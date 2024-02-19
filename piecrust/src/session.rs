// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt::{Debug, Formatter};
use std::mem;
use std::sync::{mpsc, Arc};

use bytecheck::CheckBytes;
use dusk_wasmtime::{Engine, LinearMemory, MemoryCreator, MemoryType};
use piecrust_uplink::{ContractId, Event, ARGBUF_LEN, SCRATCH_BUF_BYTES};
use rkyv::ser::serializers::{
    BufferScratch, BufferSerializer, CompositeSerializer,
};
use rkyv::ser::Serializer;
use rkyv::{
    check_archived_root, validation::validators::DefaultValidator, Archive,
    Deserialize, Infallible, Serialize,
};

use crate::call_tree::{CallTree, CallTreeElem};
use crate::contract::{ContractData, ContractMetadata, WrappedContract};
use crate::error::Error::{self, InitalizationError, PersistenceError};
use crate::instance::WrappedInstance;
use crate::store::{ContractSession, PageOpening, PAGE_SIZE};
use crate::types::StandardBufSerializer;
use crate::vm::HostQueries;

const MAX_META_SIZE: usize = ARGBUF_LEN;
pub const INIT_METHOD: &str = "init";

unsafe impl Send for Session {}
unsafe impl Sync for Session {}

/// A running mutation to a state.
///
/// `Session`s are spawned using a [`VM`] instance, and can be used to [`call`]
/// contracts with to modify their state. A sequence of these calls may then be
/// [`commit`]ed to, or discarded by simply allowing the session to drop.
///
/// New contracts are to be `deploy`ed in the context of a session.
///
/// [`VM`]: crate::VM
/// [`call`]: Session::call
/// [`commit`]: Session::commit
pub struct Session {
    engine: Engine,
    inner: &'static mut SessionInner,
    original: bool,
}

impl Debug for Session {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session")
            .field("inner", &self.inner)
            .field("original", &self.original)
            .finish()
    }
}

/// A session is created by leaking an using `Box::leak` on a `SessionInner`.
/// Therefore, the memory needs to be recovered.
impl Drop for Session {
    fn drop(&mut self) {
        if self.original {
            // ensure the stack is cleared and all instances are removed and
            // reclaimed on the drop of a session.
            self.clear_stack();

            // SAFETY: this is safe since we guarantee that there is no aliasing
            // when a session drops.
            unsafe {
                let _ = Box::from_raw(self.inner);
            }
        }
    }
}

#[derive(Debug)]
struct SessionInner {
    current: ContractId,

    call_tree: CallTree,
    debug: Vec<String>,
    data: SessionData,

    contract_session: ContractSession,
    host_queries: HostQueries,
    buffer: Vec<u8>,

    feeder: Option<mpsc::Sender<Vec<u8>>>,
    events: Vec<Event>,
}

unsafe impl MemoryCreator for Session {
    /// This new memory is created for the contract currently at the top of the
    /// call tree.
    fn new_memory(
        &self,
        _ty: MemoryType,
        minimum: usize,
        _maximum: Option<usize>,
        _reserved_size_in_bytes: Option<usize>,
        _guard_size_in_bytes: usize,
    ) -> Result<Box<dyn LinearMemory>, String> {
        let contract = self.inner.current;

        let session = self.clone();

        let contract_data =
            session.inner.contract_session.contract(contract).map_err(
                |err| format!("Failed to get contract from session: {err:?}"),
            )?;

        let mut memory = contract_data
            .expect("Contract data should exist at this point")
            .memory;

        if memory.is_new {
            memory.current_len = minimum;
        }

        Ok(Box::new(memory))
    }
}

impl Session {
    pub(crate) fn new(
        engine: Engine,
        contract_session: ContractSession,
        host_queries: HostQueries,
        data: SessionData,
    ) -> Self {
        let inner = SessionInner {
            current: ContractId::uninitialized(),
            call_tree: CallTree::new(),
            debug: vec![],
            data,
            contract_session,
            host_queries,
            buffer: vec![0; PAGE_SIZE],
            feeder: None,
            events: vec![],
        };

        // This implementation purposefully boxes and leaks the `SessionInner`.
        let inner = Box::leak(Box::new(inner));

        let mut session = Self {
            engine: engine.clone(),
            inner,
            original: true,
        };

        let mut config = engine.config().clone();
        config.with_host_memory(Arc::new(session.clone()));

        session.engine = Engine::new(&config)
            .expect("Engine configuration is set at compile time");

        session
    }

    /// Clone the given session. We explicitly **do not** implement the
    /// [`Clone`] trait here, since we don't want allow the user to clone a
    /// session.
    ///
    /// This is done to allow us to guarantee there is no aliasing of the
    /// reference to `&'static SessionInner`.
    pub(crate) fn clone(&self) -> Self {
        let inner = self.inner as *const SessionInner;
        let inner = inner as *mut SessionInner;
        // SAFETY: we explicitly allow aliasing of the session for internal
        // use.
        Self {
            engine: self.engine.clone(),
            inner: unsafe { &mut *inner },
            original: false,
        }
    }

    /// Return a reference to the engine used in this session.
    pub(crate) fn engine(&self) -> &Engine {
        &self.engine
    }

    /// Deploy a contract, returning its [`ContractId`]. The ID is computed
    /// using a `blake3` hash of the `bytecode`. Contracts using the `memory64`
    /// proposal are accepted in just the same way as 32-bit contracts, and
    /// their handling is totally transparent.
    ///
    /// Since a deployment may execute some contract initialization code, that
    /// code will be metered and executed with the given `gas_limit`.
    ///
    /// # Errors
    /// It is possible that a collision between contract IDs occurs, even for
    /// different contract IDs. This is due to the fact that all contracts have
    /// to fit into a sparse merkle tree with `2^32` positions, and as such
    /// a 256-bit number has to be mapped into a 32-bit number.
    ///
    /// If such a collision occurs, [`PersistenceError`] will be returned.
    ///
    /// [`ContractId`]: ContractId
    /// [`PersistenceError`]: PersistenceError
    pub fn deploy<'a, A, D, const N: usize>(
        &mut self,
        bytecode: &[u8],
        deploy_data: D,
        gas_limit: u64,
    ) -> Result<ContractId, Error>
    where
        A: 'a + for<'b> Serialize<StandardBufSerializer<'b>>,
        D: Into<ContractData<'a, A, N>>,
    {
        let mut deploy_data = deploy_data.into();

        match deploy_data.contract_id {
            Some(_) => (),
            _ => {
                let hash = blake3::hash(bytecode);
                deploy_data.contract_id =
                    Some(ContractId::from_bytes(hash.into()));
            }
        };

        let mut constructor_arg = None;
        if let Some(arg) = deploy_data.constructor_arg {
            let mut sbuf = [0u8; SCRATCH_BUF_BYTES];
            let scratch = BufferScratch::new(&mut sbuf);
            let ser = BufferSerializer::new(&mut self.inner.buffer[..]);
            let mut ser = CompositeSerializer::new(ser, scratch, Infallible);

            ser.serialize_value(arg)?;
            let pos = ser.pos();

            constructor_arg = Some(self.inner.buffer[0..pos].to_vec());
        }

        let contract_id = deploy_data.contract_id.unwrap();
        self.do_deploy(
            contract_id,
            bytecode,
            constructor_arg,
            deploy_data.owner.to_vec(),
            gas_limit,
        )?;

        Ok(contract_id)
    }

    fn do_deploy(
        &mut self,
        contract_id: ContractId,
        bytecode: &[u8],
        arg: Option<Vec<u8>>,
        owner: Vec<u8>,
        gas_limit: u64,
    ) -> Result<(), Error> {
        if self.inner.contract_session.contract_deployed(contract_id) {
            return Err(InitalizationError(
                "Deployed error already exists".into(),
            ));
        }

        let wrapped_contract =
            WrappedContract::new(&self.engine, bytecode, None::<&[u8]>)?;
        let contract_metadata = ContractMetadata { contract_id, owner };
        let metadata_bytes = Self::serialize_data(&contract_metadata)?;

        self.inner
            .contract_session
            .deploy(
                contract_id,
                bytecode,
                wrapped_contract.as_bytes(),
                contract_metadata,
                metadata_bytes.as_slice(),
            )
            .map_err(|err| PersistenceError(Arc::new(err)))?;

        let instantiate = || {
            let mut instance = self.new_instance(contract_id)?;

            let has_init = instance.is_function_exported(INIT_METHOD);
            if has_init && arg.is_none() {
                return Err(InitalizationError(
                    "Contract has constructor but no argument was provided"
                        .into(),
                ));
            }

            if let Some(arg) = arg {
                if !has_init {
                    return Err(InitalizationError(
                        "Argument was provided but contract has no constructor"
                            .into(),
                    ));
                }

                self.call_inner(contract_id, INIT_METHOD, arg, gas_limit)?;
            }

            Ok(())
        };

        instantiate().map_err(|err| {
            self.inner.contract_session.remove_contract(&contract_id);
            err
        })
    }

    /// Execute a call on the current state of this session.
    ///
    /// Calls are atomic, meaning that on failure their execution doesn't modify
    /// the state. They are also metered, and will execute with the given
    /// `gas_limit`. This value should never be 0.
    ///
    /// # Errors
    /// The call may error during execution for a wide array of reasons, the
    /// most common ones being running against the gas limit and a contract
    /// panic. Calling the 'init' method is not allowed except for when called
    /// from the deploy method.
    pub fn call<A, R>(
        &mut self,
        contract: ContractId,
        fn_name: &str,
        fn_arg: &A,
        gas_limit: u64,
    ) -> Result<CallReceipt<R>, Error>
    where
        A: for<'b> Serialize<StandardBufSerializer<'b>>,
        A::Archived: for<'b> CheckBytes<DefaultValidator<'b>>,
        R: Archive,
        R::Archived: Deserialize<R, Infallible>
            + for<'b> CheckBytes<DefaultValidator<'b>>,
    {
        if fn_name == INIT_METHOD {
            return Err(InitalizationError("init call not allowed".into()));
        }

        let mut sbuf = [0u8; SCRATCH_BUF_BYTES];
        let scratch = BufferScratch::new(&mut sbuf);
        let ser = BufferSerializer::new(&mut self.inner.buffer[..]);
        let mut ser = CompositeSerializer::new(ser, scratch, Infallible);

        ser.serialize_value(fn_arg)?;
        let pos = ser.pos();

        let receipt = self.call_raw(
            contract,
            fn_name,
            self.inner.buffer[..pos].to_vec(),
            gas_limit,
        )?;

        receipt.deserialize()
    }

    /// Execute a raw call on the current state of this session.
    ///
    /// Raw calls do not specify the type of the argument or of the return. The
    /// caller is responsible for serializing the argument as the target
    /// `contract` expects.
    ///
    /// For more information about calls see [`call`].
    ///
    /// [`call`]: Session::call
    pub fn call_raw<V: Into<Vec<u8>>>(
        &mut self,
        contract: ContractId,
        fn_name: &str,
        fn_arg: V,
        gas_limit: u64,
    ) -> Result<CallReceipt<Vec<u8>>, Error> {
        if fn_name == INIT_METHOD {
            return Err(InitalizationError("init call not allowed".into()));
        }

        let (data, gas_spent, call_tree) =
            self.call_inner(contract, fn_name, fn_arg.into(), gas_limit)?;
        let events = mem::take(&mut self.inner.events);

        Ok(CallReceipt {
            gas_limit,
            gas_spent,
            events,
            call_tree,
            data,
        })
    }

    /// Migrates a `contract` to a new `bytecode`, performing modifications to
    /// its state as specified by the closure.
    ///
    /// The closure takes a contract ID of where the new contract will be
    /// available during the migration, and a mutable reference to a session,
    /// allowing the caller to perform calls and other operations on the new
    /// (and old) contract.
    ///
    /// At the end of the migration, the new contract will be available at the
    /// given `contract` ID, and the old contract will be removed from the
    /// state.
    ///
    /// # Errors
    /// The migration may error during execution for a myriad of reasons. The
    /// caller is encouraged to drop the `Session` should an error occur as it
    /// will more than likely be left in an inconsistent state.
    pub fn migrate<'a, A, D, F, const N: usize>(
        mut self,
        contract: ContractId,
        bytecode: &[u8],
        deploy_data: D,
        deploy_gas_limit: u64,
        closure: F,
    ) -> Result<Self, Error>
    where
        A: 'a + for<'b> Serialize<StandardBufSerializer<'b>>,
        D: Into<ContractData<'a, A, N>>,
        F: FnOnce(ContractId, &mut Session) -> Result<(), Error>,
    {
        let new_contract =
            self.deploy(bytecode, deploy_data, deploy_gas_limit)?;
        closure(new_contract, &mut self)?;

        self.inner
            .contract_session
            .replace(contract, new_contract)
            .map_err(|err| PersistenceError(Arc::new(err)))?;

        Ok(self)
    }

    /// Execute a *feeder* call on the current state of this session.
    ///
    /// Feeder calls are used to have the contract be able to report larger
    /// amounts of data to the host via the channel included in this call.
    ///
    /// These calls are always performed with the maximum amount of gas, since
    /// the contracts may spend quite a large amount in an effort to report
    /// data.
    pub fn feeder_call<A, R>(
        &mut self,
        contract: ContractId,
        fn_name: &str,
        fn_arg: &A,
        feeder: mpsc::Sender<Vec<u8>>,
    ) -> Result<CallReceipt<R>, Error>
    where
        A: for<'b> Serialize<StandardBufSerializer<'b>>,
        A::Archived: for<'b> CheckBytes<DefaultValidator<'b>>,
        R: Archive,
        R::Archived: Deserialize<R, Infallible>
            + for<'b> CheckBytes<DefaultValidator<'b>>,
    {
        self.inner.feeder = Some(feeder);
        let r = self.call(contract, fn_name, fn_arg, u64::MAX);
        self.inner.feeder = None;
        r
    }

    /// Execute a raw *feeder* call on the current state of this session.
    ///
    /// See [`feeder_call`] and [`call_raw`] for more information of this type
    /// of call.
    ///
    /// [`feeder_call`]: [`Session::feeder_call`]
    /// [`call_raw`]: [`Session::call_raw`]
    pub fn feeder_call_raw<V: Into<Vec<u8>>>(
        &mut self,
        contract: ContractId,
        fn_name: &str,
        fn_arg: V,
        feeder: mpsc::Sender<Vec<u8>>,
    ) -> Result<CallReceipt<Vec<u8>>, Error> {
        self.inner.feeder = Some(feeder);
        let r = self.call_raw(contract, fn_name, fn_arg, u64::MAX);
        self.inner.feeder = None;
        r
    }

    /// Returns the current length of the memory of the given contract.
    ///
    /// If the contract does not exist, it will return `None`.
    pub fn memory_len(
        &mut self,
        contract_id: ContractId,
    ) -> Result<Option<usize>, Error> {
        Ok(self
            .inner
            .contract_session
            .contract(contract_id)
            .map_err(|err| Error::PersistenceError(Arc::new(err)))?
            .map(|data| data.memory.current_len))
    }

    fn clear_stack(&mut self) {
        self.inner.call_tree.clear();
    }

    /// Return the state root of the current state of the session.
    ///
    /// The state root is the root of a merkle tree whose leaves are the hashes
    /// of the state of of each contract, ordered by their contract ID.
    ///
    /// It also doubles as the ID of a commit - the commit root.
    pub fn root(&self) -> [u8; 32] {
        self.inner.contract_session.root().into()
    }

    /// Returns an iterator over the pages (and their indices) of a contract's
    /// memory, together with a proof of their inclusion in the state.
    ///
    /// The proof is a Merkle inclusion proof, and the caller is able to verify
    /// it by using [`verify`], and matching the root with the one returned by
    /// [`root`].
    ///
    /// [`verify`]: PageOpening::verify
    /// [`root`]: Session::root
    pub fn memory_pages(
        &self,
        contract: ContractId,
    ) -> Option<impl Iterator<Item = (usize, &[u8], PageOpening)>> {
        self.inner.contract_session.memory_pages(contract)
    }

    pub(crate) fn push_event(&mut self, event: Event) {
        self.inner.events.push(event);
    }

    pub(crate) fn push_feed(&mut self, data: Vec<u8>) -> Result<(), Error> {
        let feed = self.inner.feeder.as_ref().ok_or(Error::MissingFeed)?;
        feed.send(data).map_err(Error::FeedPulled)
    }

    pub(crate) fn new_instance(
        &mut self,
        contract_id: ContractId,
    ) -> Result<WrappedInstance, Error> {
        let store_data = self
            .inner
            .contract_session
            .contract(contract_id)
            .map_err(|err| PersistenceError(Arc::new(err)))?
            .ok_or(Error::ContractDoesNotExist(contract_id))?;

        let contract = WrappedContract::new(
            &self.engine,
            store_data.bytecode,
            Some(store_data.module.serialize()),
        )?;

        self.inner.current = contract_id;

        let instance = WrappedInstance::new(
            self.clone(),
            contract_id,
            &contract,
            store_data.memory,
        )?;

        Ok(instance)
    }

    pub(crate) fn host_query(
        &self,
        name: &str,
        buf: &mut [u8],
        arg_len: u32,
    ) -> Option<u32> {
        self.inner.host_queries.call(name, buf, arg_len)
    }

    pub(crate) fn nth_from_top(&self, n: usize) -> Option<CallTreeElem> {
        self.inner.call_tree.nth_parent(n)
    }

    pub(crate) fn push_callstack(
        &mut self,
        contract_id: ContractId,
        limit: u64,
        mem_len: usize,
    ) {
        self.inner.call_tree.push(CallTreeElem {
            contract_id,
            limit,
            spent: 0,
            mem_len,
        });
    }

    pub(crate) fn move_up_call_tree(&mut self, spent: u64) {
        self.inner.call_tree.move_up(spent);
    }

    pub(crate) fn move_up_prune_call_tree(&mut self) {
        self.inner.call_tree.move_up_prune();
    }

    pub(crate) fn revert_callstack(&mut self) -> Result<(), std::io::Error> {
        for elem in self.inner.call_tree.iter() {
            let mut memory = self
                .inner
                .contract_session
                .contract(elem.contract_id)?
                .expect("contract should exist")
                .memory;
            memory.revert()?;
            memory.current_len = elem.mem_len;
        }

        Ok(())
    }

    /// Commits the given session to disk, consuming the session and returning
    /// its state root.
    pub fn commit(self) -> Result<[u8; 32], Error> {
        self.inner
            .contract_session
            .commit()
            .map(Into::into)
            .map_err(|err| PersistenceError(Arc::new(err)))
    }

    #[cfg(feature = "debug")]
    pub(crate) fn register_debug<M: Into<String>>(&mut self, msg: M) {
        self.inner.debug.push(msg.into());
    }

    pub fn with_debug<C, R>(&self, c: C) -> R
    where
        C: FnOnce(&[String]) -> R,
    {
        c(&self.inner.debug)
    }

    /// Returns the value of a metadata item.
    pub fn meta(&self, name: &str) -> Option<Vec<u8>> {
        self.inner.data.get(name)
    }

    pub fn serialize_data<V>(value: &V) -> Result<Vec<u8>, Error>
    where
        V: for<'a> Serialize<StandardBufSerializer<'a>>,
    {
        let mut buf = [0u8; MAX_META_SIZE];
        let mut sbuf = [0u8; SCRATCH_BUF_BYTES];

        let ser = BufferSerializer::new(&mut buf[..]);
        let scratch = BufferScratch::new(&mut sbuf);

        let mut serializer =
            StandardBufSerializer::new(ser, scratch, Infallible);
        serializer.serialize_value(value)?;

        let pos = serializer.pos();

        Ok(buf[..pos].to_vec())
    }

    fn call_inner(
        &mut self,
        contract: ContractId,
        fname: &str,
        fdata: Vec<u8>,
        limit: u64,
    ) -> Result<(Vec<u8>, u64, CallTree), Error> {
        let mut instance = self.new_instance(contract)?;
        self.push_callstack(contract, limit, instance.mem_len());

        instance
            .snap()
            .map_err(|err| Error::MemorySnapshotFailure {
                reason: None,
                io: Arc::new(err),
            })?;

        let arg_len = instance.write_bytes_to_arg_buffer(&fdata);
        let ret_len = instance
            .call(fname, arg_len, limit)
            .map_err(|err| {
                if let Err(io_err) = self.revert_callstack() {
                    return Error::MemorySnapshotFailure {
                        reason: Some(Arc::new(err)),
                        io: Arc::new(io_err),
                    };
                }
                self.move_up_prune_call_tree();
                self.clear_stack();
                err
            })
            .map_err(Error::normalize)?;
        let ret = instance.read_bytes_from_arg_buffer(ret_len as u32);

        let spent = limit - instance.get_remaining_gas();

        for elem in self.inner.call_tree.iter() {
            let mut memory = self
                .inner
                .contract_session
                .contract(elem.contract_id)
                .map_err(|err| PersistenceError(Arc::new(err)))?
                .expect("contract should exist")
                .memory;

            memory.apply().map_err(|err| Error::MemorySnapshotFailure {
                reason: None,
                io: Arc::new(err),
            })?;
        }
        self.clear_stack();

        let mut call_tree = CallTree::new();
        mem::swap(&mut self.inner.call_tree, &mut call_tree);
        call_tree.update_spent(spent);

        Ok((ret, spent, call_tree))
    }

    pub fn contract_metadata(
        &self,
        contract_id: &ContractId,
    ) -> Option<&ContractMetadata> {
        self.inner.contract_session.contract_metadata(contract_id)
    }
}

/// The receipt given for a call execution using one of either [`call`] or
/// [`call_raw`].
///
/// [`call`]: [`Session::call`]
/// [`call_raw`]: [`Session::call_raw`]
#[derive(Debug)]
pub struct CallReceipt<T> {
    /// The amount of gas spent in the execution of the call.
    pub gas_spent: u64,
    /// The limit used in during this execution.
    pub gas_limit: u64,

    /// The events emitted during the execution of the call.
    pub events: Vec<Event>,
    /// The call tree produced during the execution.
    pub call_tree: CallTree,

    /// The data returned by the called contract.
    pub data: T,
}

impl CallReceipt<Vec<u8>> {
    /// Deserializes a `CallReceipt<Vec<u8>>` into a `CallReceipt<T>` using
    /// `rkyv`.
    fn deserialize<T>(self) -> Result<CallReceipt<T>, Error>
    where
        T: Archive,
        T::Archived: Deserialize<T, Infallible>
            + for<'b> CheckBytes<DefaultValidator<'b>>,
    {
        let ta = check_archived_root::<T>(&self.data[..])?;
        let data = ta.deserialize(&mut Infallible)?;

        Ok(CallReceipt {
            gas_spent: self.gas_spent,
            gas_limit: self.gas_limit,
            events: self.events,
            call_tree: self.call_tree,
            data,
        })
    }
}

#[derive(Debug, Default)]
pub struct SessionData {
    data: BTreeMap<Cow<'static, str>, Vec<u8>>,
    pub base: Option<[u8; 32]>,
}

impl SessionData {
    pub fn builder() -> SessionDataBuilder {
        SessionDataBuilder {
            data: BTreeMap::new(),
            base: None,
        }
    }

    fn get(&self, name: &str) -> Option<Vec<u8>> {
        self.data.get(name).cloned()
    }
}

impl From<SessionDataBuilder> for SessionData {
    fn from(builder: SessionDataBuilder) -> Self {
        builder.build()
    }
}

pub struct SessionDataBuilder {
    data: BTreeMap<Cow<'static, str>, Vec<u8>>,
    base: Option<[u8; 32]>,
}

impl SessionDataBuilder {
    pub fn insert<S, V>(mut self, name: S, value: V) -> Result<Self, Error>
    where
        S: Into<Cow<'static, str>>,
        V: for<'a> Serialize<StandardBufSerializer<'a>>,
    {
        let data = Session::serialize_data(&value)?;
        self.data.insert(name.into(), data);
        Ok(self)
    }

    pub fn base(mut self, base: [u8; 32]) -> Self {
        self.base = Some(base);
        self
    }

    fn build(&self) -> SessionData {
        SessionData {
            data: self.data.clone(),
            base: self.base,
        }
    }
}
