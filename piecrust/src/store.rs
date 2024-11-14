// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! A library for dealing with memories in trees.

mod bytecode;
mod commit;
mod memory;
mod metadata;
mod module;
mod session;
mod tree;

use std::cell::Ref;
use std::collections::btree_map::Entry::*;
use std::collections::btree_map::Keys;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Debug, Formatter};
use std::fs::create_dir_all;
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc, Mutex};
use std::{fs, io, thread};

use dusk_wasmtime::Engine;
use piecrust_uplink::ContractId;
use session::ContractDataEntry;
use tree::{Hash, NewContractIndex};

use crate::store::commit::Hulk;
use crate::store::tree::{
    position_from_contract, BaseInfo, ContractIndexElement, ContractsMerkle,
};
pub use bytecode::Bytecode;
pub use memory::{Memory, PAGE_SIZE};
pub use metadata::Metadata;
pub use module::Module;
pub use session::ContractSession;
pub use tree::PageOpening;

const BYTECODE_DIR: &str = "bytecode";
const MEMORY_DIR: &str = "memory";
const LEAF_DIR: &str = "leaf";
const BASE_FILE: &str = "base";
const ELEMENT_FILE: &str = "element";
const OBJECTCODE_EXTENSION: &str = "a";
const METADATA_EXTENSION: &str = "m";
const MAIN_DIR: &str = "main";

/// A store for all contract commits.
pub struct ContractStore {
    sync_loop: Option<thread::JoinHandle<()>>,
    engine: Engine,

    call: Option<mpsc::Sender<Call>>,
    root_dir: PathBuf,
    pub commit_store: Arc<Mutex<CommitStore>>,
}

impl Debug for ContractStore {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContractStore")
            .field("sync_loop", &self.sync_loop)
            .field("call", &self.call)
            .field("root_dir", &self.root_dir)
            .finish()
    }
}

#[derive(Debug)]
pub struct CommitStore {
    commits: BTreeMap<Hash, Commit>,
    main_index: NewContractIndex,
}

impl CommitStore {
    pub fn new() -> Self {
        Self {
            commits: BTreeMap::new(),
            main_index: NewContractIndex::new(),
        }
    }

    pub fn insert_commit(&mut self, hash: Hash, commit: Commit) {
        self.commits.insert(hash, commit);
    }

    pub fn get_commit(&self, hash: &Hash) -> Option<&Commit> {
        self.commits.get(hash)
    }

    pub fn get_element_and_base(
        &self,
        hash: &Hash,
        contract_id: &ContractId,
    ) -> (Option<*const ContractIndexElement>, Option<Hash>) {
        match self.commits.get(hash) {
            Some(commit) => {
                let e = commit.index.get(contract_id);
                (e.map(|a| a as *const ContractIndexElement), commit.base)
            }
            None => {
                let e = self.main_index.get(contract_id);
                (e.map(|a| a as *const ContractIndexElement), None)
            }
        }
    }

    pub fn get_element_and_base_mut(
        &mut self,
        hash: &Hash,
        contract_id: &ContractId,
    ) -> (Option<*mut ContractIndexElement>, Option<Hash>) {
        match self.commits.get_mut(hash) {
            Some(commit) => {
                let e = commit.index.get_mut(contract_id);
                (e.map(|a| a as *mut ContractIndexElement), commit.base)
            }
            None => {
                let e = self.main_index.get_mut(contract_id);
                (e.map(|a| a as *mut ContractIndexElement), None)
            }
        }
    }

    pub fn contains_key(&self, hash: &Hash) -> bool {
        self.commits.contains_key(hash)
    }

    pub fn keys(&self) -> Keys<'_, Hash, Commit> {
        self.commits.keys()
    }

    pub fn remove_commit(&mut self, hash: &Hash) {
        if let Some(commit) = self.commits.remove(hash) {
            commit.index.move_into(&mut self.main_index);
        }
    }

    pub fn insert_main_index(
        &mut self,
        contract_id: &ContractId,
        element: ContractIndexElement,
    ) {
        self.main_index.insert_contract_index(contract_id, element);
    }
}

impl ContractStore {
    /// Loads a new contract store from the given `dir`ectory.
    ///
    /// This also starts the synchronization loop, which is used to align
    /// [`commit`]s, [`delete`]s, and [`session spawning`] to avoid deleting
    /// commits in use by a session.
    ///
    /// [`commit`]: ContractSession::commit
    /// [`delete`]: ContractStore::delete_commit
    /// [`session spawning`]: ContractStore::session
    pub fn new<P: AsRef<Path>>(engine: Engine, dir: P) -> io::Result<Self> {
        let root_dir = dir.as_ref();

        fs::create_dir_all(root_dir)?;

        Ok(Self {
            sync_loop: None,
            engine,
            call: None,
            root_dir: root_dir.into(),
            commit_store: Arc::new(Mutex::new(CommitStore::new())),
        })
    }

    pub fn finish_new(&mut self) -> io::Result<()> {
        let loop_root_dir = self.root_dir.to_path_buf();
        let (call, calls) = mpsc::channel();
        let commit_store = self.commit_store.clone();

        tracing::trace!("before read_all_commit");
        read_all_commits(&self.engine, &self.root_dir, commit_store)?;
        tracing::trace!("after read_all_commit");

        let commit_store = self.commit_store.clone();

        // The thread is given a name to allow for easily identifying it while
        // debugging.
        let sync_loop = thread::Builder::new()
            .name(String::from("PiecrustSync"))
            .spawn(|| sync_loop(loop_root_dir, commit_store, calls))?;

        self.sync_loop = Some(sync_loop);
        self.call = Some(call);
        Ok(())
    }

    /// Create a new [`ContractSession`] with the given `base` commit.
    ///
    /// Errors if the given base commit does not exist in the store.
    pub fn session(&self, base: Hash) -> io::Result<ContractSession> {
        tracing::trace!("session creation started");
        let base_commit_hash = self
            .call_with_replier(|replier| Call::CommitHold { base, replier })
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("No such base commit: {}", hex::encode(base)),
                )
            })?;

        let r = Ok(self.session_with_base(Some(base_commit_hash)));
        tracing::trace!("session creation finished");
        r
    }

    /// Create a new [`ContractSession`] that has no base commit.
    ///
    /// For session with a base commit, please see [`session`].
    ///
    /// [`session`]: ContractStore::session
    pub fn genesis_session(&self) -> ContractSession {
        self.session_with_base(None)
    }

    /// Returns the roots of the commits that are currently in the store.
    pub fn commits(&self) -> Vec<Hash> {
        self.call_with_replier(|replier| Call::GetCommits { replier })
    }

    /// Deletes a given `commit` from the store.
    ///
    /// If a `ContractSession` is currently using the given commit as a base,
    /// the operation will be queued for completion until the last session
    /// using the commit has dropped.
    ///
    /// It will block until the operation is completed.
    pub fn delete_commit(&self, commit: Hash) -> io::Result<()> {
        self.call_with_replier(|replier| Call::CommitDelete { commit, replier })
    }

    /// Finalizes commit
    ///
    /// The commit will become a "current" commit
    pub fn finalize_commit(&self, commit: Hash) -> io::Result<()> {
        self.call_with_replier(|replier| Call::CommitFinalize {
            commit,
            replier,
        })
    }

    /// Return the handle to the thread running the store's synchronization
    /// loop.
    pub fn sync_loop(&self) -> &thread::Thread {
        self.sync_loop
            .as_ref()
            .expect("sync thread should exist")
            .thread()
    }

    /// Return the path to the VM directory.
    pub fn root_dir(&self) -> &Path {
        &self.root_dir
    }

    fn call_with_replier<T, F>(&self, closure: F) -> T
    where
        F: FnOnce(mpsc::SyncSender<T>) -> Call,
    {
        let (replier, receiver) = mpsc::sync_channel(1);

        self.call
            .as_ref()
            .expect("call should exist")
            .send(closure(replier))
            .expect(
                "The receiver should never be dropped while there are senders",
            );

        receiver
            .recv()
            .expect("The sender should never be dropped without responding")
    }

    fn session_with_base(&self, base: Option<Hash>) -> ContractSession {
        let base_commit = base.and_then(|hash| {
            self.commit_store.lock().unwrap().get_commit(&hash).cloned() //todo: clone
        });
        ContractSession::new(
            &self.root_dir,
            self.engine.clone(),
            base_commit,
            self.call.as_ref().expect("call should exist").clone(),
            self.commit_store.clone(),
        )
    }
}

fn read_all_commits<P: AsRef<Path>>(
    engine: &Engine,
    root_dir: P,
    commit_store: Arc<Mutex<CommitStore>>,
) -> io::Result<()> {
    let root_dir = root_dir.as_ref();

    let root_dir = root_dir.join(MAIN_DIR);
    fs::create_dir_all(&root_dir)?;

    for entry in fs::read_dir(root_dir)? {
        let entry = entry?;
        if entry.path().is_dir() {
            let filename = entry.file_name();
            if filename == MEMORY_DIR
                || filename == BYTECODE_DIR
                || filename == LEAF_DIR
            {
                continue;
            }
            tracing::trace!("before read_commit");
            let commit =
                read_commit(engine, entry.path(), commit_store.clone())?;
            tracing::trace!("before read_commit");
            let root = *commit.root();
            commit_store.lock().unwrap().insert_commit(root, commit);
        }
    }

    Ok(())
}

fn read_commit<P: AsRef<Path>>(
    engine: &Engine,
    commit_dir: P,
    commit_store: Arc<Mutex<CommitStore>>,
) -> io::Result<Commit> {
    let commit_dir = commit_dir.as_ref();
    let commit = commit_from_dir(engine, commit_dir, commit_store)?;
    Ok(commit)
}

fn page_path<P: AsRef<Path>>(memory_dir: P, page_index: usize) -> PathBuf {
    memory_dir.as_ref().join(format!("{page_index}"))
}

fn page_path_main<P: AsRef<Path>, S: AsRef<str>>(
    memory_dir: P,
    page_index: usize,
    commit_id: S,
) -> io::Result<PathBuf> {
    let commit_id = commit_id.as_ref();
    let dir = memory_dir.as_ref().join(commit_id);
    fs::create_dir_all(&dir)?;
    Ok(dir.join(format!("{page_index}")))
}

fn base_path_main<P: AsRef<Path>, S: AsRef<str>>(
    main_dir: P,
    commit_id: S,
) -> io::Result<PathBuf> {
    let commit_id = commit_id.as_ref();
    let dir = main_dir.as_ref().join(commit_id);
    fs::create_dir_all(&dir)?;
    Ok(dir.join(BASE_FILE))
}

fn commit_id_to_hash<S: AsRef<str>>(commit_id: S) -> Hash {
    let hash: [u8; 32] = hex::decode(commit_id.as_ref())
        .expect("Hex decoding of commit id string should succeed")
        .try_into()
        .expect("Commit id string conversion should succeed");
    Hash::from(hash)
}

fn contract_id_from_hex<S: AsRef<str>>(contract_id: S) -> ContractId {
    let bytes: [u8; 32] = hex::decode(contract_id.as_ref())
        .expect("Hex decoding of commit id string should succeed")
        .try_into()
        .expect("Commit id string conversion should succeed");
    ContractId::from_bytes(bytes)
}

fn commit_from_dir<P: AsRef<Path>>(
    engine: &Engine,
    dir: P,
    commit_store: Arc<Mutex<CommitStore>>,
) -> io::Result<Commit> {
    let dir = dir.as_ref();
    let mut commit_id: Option<String> = None;
    let main_dir = if dir
        .file_name()
        .expect("Filename or folder name should exist")
        != MAIN_DIR
    {
        commit_id = Some(
            dir.file_name()
                .expect("Filename or folder name should exist")
                .to_string_lossy()
                .to_string(),
        );
        // this means we are in a commit dir, need to back up for bytecode
        // and memory paths to work correctly
        dir.parent().expect("Parent should exist")
    } else {
        dir
    };
    let maybe_hash = commit_id.as_ref().map(commit_id_to_hash);

    // let contracts_merkle_path = dir.join(MERKLE_FILE);
    let leaf_dir = main_dir.join(LEAF_DIR);
    tracing::trace!("before index_merkle_from_path");
    let (index, contracts_merkle) = index_merkle_from_path(
        main_dir,
        leaf_dir,
        &maybe_hash,
        commit_store.clone(),
    )?;
    tracing::trace!("after index_merkle_from_path");

    let bytecode_dir = main_dir.join(BYTECODE_DIR);
    let memory_dir = main_dir.join(MEMORY_DIR);

    for (contract, contract_index) in index.iter() {
        let contract_hex = hex::encode(contract);

        // Check that all contracts in the index file have a corresponding
        // bytecode and memory pages specified.
        let bytecode_path = bytecode_dir.join(&contract_hex);
        if !bytecode_path.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Non-existing bytecode for contract: {contract_hex}"),
            ));
        }

        let module_path = bytecode_path.with_extension(OBJECTCODE_EXTENSION);

        // SAFETY it is safe to deserialize the file here, since we don't use
        // the module here. We just want to check if the file is valid.
        if Module::from_file(engine, &module_path).is_err() {
            let bytecode = Bytecode::from_file(bytecode_path)?;
            let module = Module::from_bytecode(engine, bytecode.as_ref())
                .map_err(|err| {
                    io::Error::new(io::ErrorKind::InvalidData, err)
                })?;
            fs::write(module_path, module.serialize())?;
        }

        let contract_memory_dir = memory_dir.join(&contract_hex);

        for page_index in contract_index.page_indices() {
            let main_page_path = page_path(&contract_memory_dir, *page_index);
            if !main_page_path.is_file() {
                let path = ContractSession::find_page(
                    *page_index,
                    maybe_hash,
                    &contract_memory_dir,
                    main_dir,
                );
                let found = path.map(|p| p.is_file()).unwrap_or(false);
                if !found {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "Non-existing memory for contract: {contract_hex}"
                        ),
                    ));
                }
            }
        }
    }

    let base = if let Some(hash_hex) = commit_id {
        let base_info_path = main_dir.join(hash_hex).join(BASE_FILE);
        base_from_path(base_info_path)?.maybe_base
    } else {
        None
    };

    Ok(Commit {
        index,
        contracts_merkle,
        maybe_hash,
        commit_store: Some(commit_store),
        base,
    })
}

fn index_merkle_from_path(
    main_path: impl AsRef<Path>,
    leaf_dir: impl AsRef<Path>,
    maybe_commit_id: &Option<Hash>,
    commit_store: Arc<Mutex<CommitStore>>,
) -> io::Result<(NewContractIndex, ContractsMerkle)> {
    let leaf_dir = leaf_dir.as_ref();

    let mut index: NewContractIndex = NewContractIndex::new();
    let mut merkle: ContractsMerkle = ContractsMerkle::default();

    for entry in fs::read_dir(leaf_dir)? {
        let entry = entry?;
        if entry.path().is_dir() {
            let contract_id_hex = entry.file_name();
            let contract_id =
                contract_id_from_hex(contract_id_hex.to_string_lossy());
            let contract_leaf_path = leaf_dir.join(contract_id_hex);
            let (element_path, element_depth) = ContractSession::find_element(
                *maybe_commit_id,
                &contract_leaf_path,
                &main_path,
                0,
            )
            .unwrap_or((contract_leaf_path.join(ELEMENT_FILE), 0));
            if element_path.is_file() {
                let element_bytes = fs::read(&element_path)?;
                let element: ContractIndexElement =
                    rkyv::from_bytes(&element_bytes).map_err(|err| {
                        tracing::trace!(
                            "deserializing element file failed {}",
                            err
                        );
                        io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!(
                            "Invalid element file \"{element_path:?}\": {err}"
                        ),
                        )
                    })?;
                if let Some(h) = element.hash() {
                    merkle.insert_with_int_pos(
                        position_from_contract(&contract_id),
                        element.int_pos().expect("int pos should be present"),
                        h,
                    );
                }
                if element_depth != u32::MAX {
                    index.insert_contract_index(&contract_id, element);
                } else {
                    commit_store
                        .lock()
                        .unwrap()
                        .insert_main_index(&contract_id, element);
                }
            }
        }
    }

    Ok((index, merkle))
}

fn base_from_path<P: AsRef<Path>>(path: P) -> io::Result<BaseInfo> {
    let path = path.as_ref();

    let base_info_bytes = fs::read(path)?;
    let base_info = rkyv::from_bytes(&base_info_bytes).map_err(|err| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Invalid base info file \"{path:?}\": {err}"),
        )
    })?;

    Ok(base_info)
}

#[derive(Debug, Clone)]
pub(crate) struct Commit {
    index: NewContractIndex,
    contracts_merkle: ContractsMerkle,
    maybe_hash: Option<Hash>,
    commit_store: Option<Arc<Mutex<CommitStore>>>,
    base: Option<Hash>,
}

impl Commit {
    pub fn new(
        commit_store: &Arc<Mutex<CommitStore>>,
        maybe_base: Option<Hash>,
    ) -> Self {
        Self {
            index: NewContractIndex::new(),
            contracts_merkle: ContractsMerkle::default(),
            maybe_hash: None,
            commit_store: Some(commit_store.clone()),
            base: maybe_base,
        }
    }

    #[allow(dead_code)]
    pub fn fast_clone<'a>(
        &self,
        contract_ids: impl Iterator<Item = &'a ContractId>,
    ) -> Self {
        let mut index = NewContractIndex::new();
        for contract_id in contract_ids {
            if let Some(a) = self.index.get(contract_id) {
                index.insert_contract_index(contract_id, a.clone());
            }
        }
        Self {
            index,
            contracts_merkle: self.contracts_merkle.clone(),
            maybe_hash: self.maybe_hash,
            commit_store: self.commit_store.clone(),
            base: self.base,
        }
    }

    #[allow(dead_code)]
    pub fn inclusion_proofs(
        mut self,
        contract_id: &ContractId,
    ) -> Option<impl Iterator<Item = (usize, PageOpening)>> {
        let contract = self.index.remove_contract_index(contract_id)?;

        let pos = position_from_contract(contract_id);

        let (iter, tree) = contract.page_indices_and_tree();
        Some(iter.map(move |page_index| {
            let tree_opening = self
                .contracts_merkle
                .opening(pos)
                .expect("There must be a leaf for the contract");

            let page_opening = tree
                .opening(page_index as u64)
                .expect("There must be a leaf for the page");

            (
                page_index,
                PageOpening {
                    tree: tree_opening,
                    inner: page_opening,
                },
            )
        }))
    }

    pub fn insert(&mut self, contract_id: ContractId, memory: &Memory) {
        if self.index_get(&contract_id).is_none() {
            self.index.insert_contract_index(
                &contract_id,
                ContractIndexElement::new(memory.is_64()),
            );
        }
        let (element, contracts_merkle) =
            self.element_and_merkle_mut(&contract_id);
        let element = element.unwrap();

        element.set_len(memory.current_len);

        for (dirty_page, _, page_index) in memory.dirty_pages() {
            let hash = Hash::new(dirty_page);
            element.insert_page_index_hash(
                *page_index,
                *page_index as u64,
                hash,
            );
        }

        let root = *element.tree().root();
        let pos = position_from_contract(&contract_id);
        let internal_pos = contracts_merkle.insert(pos, root);
        element.set_hash(Some(root));
        element.set_int_pos(Some(internal_pos));
    }

    pub fn remove_and_insert(&mut self, contract: ContractId, memory: &Memory) {
        self.index.remove_contract_index(&contract);
        self.insert(contract, memory);
    }

    pub fn root(&self) -> Ref<Hash> {
        tracing::trace!("calculating root started");
        let ret = self.contracts_merkle.root();
        tracing::trace!("calculating root finished");
        ret
    }

    pub fn index_get(
        &self,
        contract_id: &ContractId,
    ) -> Option<&ContractIndexElement> {
        Hulk::deep_index_get(
            &self.index,
            *contract_id,
            self.commit_store.clone(),
            self.base,
        )
        .map(|a| unsafe { &*a })
    }

    pub fn element_and_merkle_mut(
        &mut self,
        contract_id: &ContractId,
    ) -> (Option<&mut ContractIndexElement>, &mut ContractsMerkle) {
        (
            Hulk::deep_index_get_mut(
                &mut self.index,
                *contract_id,
                self.commit_store.clone(),
                self.base,
            )
            .map(|a| unsafe { &mut *a }),
            &mut self.contracts_merkle,
        )
    }
}

pub(crate) enum Call {
    Commit {
        contracts: BTreeMap<ContractId, ContractDataEntry>,
        base: Option<Commit>,
        replier: mpsc::SyncSender<io::Result<Hash>>,
    },
    GetCommits {
        replier: mpsc::SyncSender<Vec<Hash>>,
    },
    CommitDelete {
        commit: Hash,
        replier: mpsc::SyncSender<io::Result<()>>,
    },
    CommitFinalize {
        commit: Hash,
        replier: mpsc::SyncSender<io::Result<()>>,
    },
    CommitHold {
        base: Hash,
        replier: mpsc::SyncSender<Option<Hash>>,
    },
    SessionDrop(Hash),
}

fn sync_loop<P: AsRef<Path>>(
    root_dir: P,
    commit_store: Arc<Mutex<CommitStore>>,
    calls: mpsc::Receiver<Call>,
) {
    let root_dir = root_dir.as_ref();

    let mut sessions = BTreeMap::new();

    let mut delete_bag = BTreeMap::new();

    for call in calls {
        match call {
            // Writes a session to disk and adds it to the map of existing
            // commits.
            Call::Commit {
                contracts,
                base,
                replier,
            } => {
                tracing::trace!("writing commit started");
                let io_result = write_commit(
                    root_dir,
                    commit_store.clone(),
                    base,
                    contracts,
                );
                match &io_result {
                    Ok(hash) => tracing::trace!(
                        "writing commit finished: {:?}",
                        hex::encode(hash.as_bytes())
                    ),
                    Err(e) => tracing::trace!("writing commit failed {:?}", e),
                }
                let _ = replier.send(io_result);
            }
            // Copy all commits and send them back to the caller.
            Call::GetCommits { replier } => {
                tracing::trace!("get commits started");
                let _ = replier.send(
                    commit_store.lock().unwrap().keys().copied().collect(),
                );
                tracing::trace!("get commits finished");
            }
            // Delete a commit from disk. If the commit is currently in use - as
            // in it is held by at least one session using `Call::SessionHold` -
            // queue it for deletion once no session is holding it.
            Call::CommitDelete {
                commit: root,
                replier,
            } => {
                tracing::trace!("delete commit started");
                if sessions.contains_key(&root) {
                    match delete_bag.entry(root) {
                        Vacant(entry) => {
                            entry.insert(vec![replier]);
                        }
                        Occupied(mut entry) => {
                            entry.get_mut().push(replier);
                        }
                    }

                    continue;
                }

                let io_result = delete_commit_dir(root_dir, root);
                commit_store.lock().unwrap().remove_commit(&root);
                tracing::trace!("delete commit finished");
                let _ = replier.send(io_result);
            }
            // Finalize commit
            Call::CommitFinalize {
                commit: root,
                replier,
            } => {
                tracing::trace!("finalizing commit started");
                if sessions.contains_key(&root) {
                    match delete_bag.entry(root) {
                        Vacant(entry) => {
                            entry.insert(vec![replier]);
                        }
                        Occupied(mut entry) => {
                            entry.get_mut().push(replier);
                        }
                    }

                    continue;
                }

                let mut commit_store = commit_store.lock().unwrap();
                if let Some(commit) = commit_store.get_commit(&root) {
                    tracing::trace!(
                        "finalizing commit proper started {}",
                        hex::encode(root.as_bytes())
                    );
                    let io_result = finalize_commit(root, root_dir, commit);
                    match &io_result {
                        Ok(_) => tracing::trace!(
                            "finalizing commit proper finished: {:?}",
                            hex::encode(root.as_bytes())
                        ),
                        Err(e) => tracing::trace!(
                            "finalizing commit proper failed {:?}",
                            e
                        ),
                    }
                    commit_store.remove_commit(&root);
                    tracing::trace!("finalizing commit finished");
                    let _ = replier.send(io_result);
                } else {
                    tracing::trace!("finalizing commit finished");
                    let _ = replier.send(Ok(()));
                }
            }
            // Increment the hold count of a commit to prevent it from deletion
            // on a `Call::CommitDelete`.
            Call::CommitHold { base, replier } => {
                tracing::trace!("hold commit open session started");
                let mut maybe_base = None;
                if commit_store.lock().unwrap().contains_key(&base) {
                    maybe_base = Some(base);

                    match sessions.entry(base) {
                        Vacant(entry) => {
                            entry.insert(1);
                        }
                        Occupied(mut entry) => {
                            *entry.get_mut() += 1;
                        }
                    }
                }
                tracing::trace!("hold commit open session finished");

                let _ = replier.send(maybe_base);
            }
            // Signal that a session with a base commit has dropped and
            // decrements the hold count, once incremented using
            // `Call::SessionHold`. If this is the last session that held that
            // commit, and there are queued deletions, execute them.
            Call::SessionDrop(base) => {
                tracing::trace!("session drop started");
                match sessions.entry(base) {
                    Vacant(_) => unreachable!("If a session is dropped there must be a session hold entry"),
                    Occupied(mut entry) => {
                        *entry.get_mut() -= 1;

                        if *entry.get() == 0 {
                            entry.remove();

                            // Try all deletions first
                            match delete_bag.entry(base) {
                                Vacant(_) => {}
                                Occupied(entry) => {
                                    for replier in entry.remove() {
                                        let io_result =
                                            delete_commit_dir(root_dir, base);
                                        commit_store.lock().unwrap().remove_commit(&base);
                                        let _ = replier.send(io_result);
                                    }
                                }
                            }
                        }
                    }
                };
                tracing::trace!("session drop finished");
            }
        }
    }
}

fn write_commit<P: AsRef<Path>>(
    root_dir: P,
    commit_store: Arc<Mutex<CommitStore>>,
    base: Option<Commit>,
    commit_contracts: BTreeMap<ContractId, ContractDataEntry>,
) -> io::Result<Hash> {
    let root_dir = root_dir.as_ref();

    let base_info = BaseInfo {
        maybe_base: base.as_ref().map(|base| *base.root()),
        ..Default::default()
    };

    // base is already a copy, no point cloning it again

    // let index = base
    //     .as_ref()
    //     .map_or(NewContractIndex::new(), |base| base.index.clone());
    // let contracts_merkle =
    //     base.as_ref().map_or(ContractsMerkle::default(), |base| {
    //         base.contracts_merkle.clone()
    //     });
    // let mut commit = Commit {
    //     index,
    //     contracts_merkle,
    //     maybe_hash: base.as_ref().and_then(|base| base.maybe_hash),
    // };

    let mut commit =
        base.unwrap_or(Commit::new(&commit_store, base_info.maybe_base));
    for (contract_id, contract_data) in &commit_contracts {
        if contract_data.is_new {
            commit.remove_and_insert(*contract_id, &contract_data.memory);
        } else {
            commit.insert(*contract_id, &contract_data.memory);
        }
    }

    let root = *commit.root();
    let root_hex = hex::encode(root);
    commit.maybe_hash = Some(root);
    commit.base = base_info.maybe_base;

    // Don't write the commit if it already exists on disk. This may happen if
    // the same transactions on the same base commit for example.
    if commit_store.lock().unwrap().contains_key(&root) {
        return Ok(root);
    }

    write_commit_inner(root_dir, &commit, commit_contracts, root_hex, base_info)
        .map(|_| {
            commit_store.lock().unwrap().insert_commit(root, commit);
            root
        })
}

/// Writes a commit to disk.
fn write_commit_inner<P: AsRef<Path>, S: AsRef<str>>(
    root_dir: P,
    commit: &Commit,
    commit_contracts: BTreeMap<ContractId, ContractDataEntry>,
    commit_id: S,
    mut base_info: BaseInfo,
) -> io::Result<()> {
    let root_dir = root_dir.as_ref();

    struct Directories {
        main_dir: PathBuf,
        bytecode_main_dir: PathBuf,
        memory_main_dir: PathBuf,
        leaf_main_dir: PathBuf,
    }

    let directories = {
        let main_dir = root_dir.join(MAIN_DIR);
        fs::create_dir_all(&main_dir)?;

        let bytecode_main_dir = main_dir.join(BYTECODE_DIR);
        fs::create_dir_all(&bytecode_main_dir)?;

        let memory_main_dir = main_dir.join(MEMORY_DIR);
        fs::create_dir_all(&memory_main_dir)?;

        let leaf_main_dir = main_dir.join(LEAF_DIR);
        fs::create_dir_all(&leaf_main_dir)?;

        Directories {
            main_dir,
            bytecode_main_dir,
            memory_main_dir,
            leaf_main_dir,
        }
    };

    // Write the dirty pages contracts of contracts to disk.
    for (contract, contract_data) in &commit_contracts {
        let contract_hex = hex::encode(contract);

        let memory_main_dir = directories.memory_main_dir.join(&contract_hex);
        fs::create_dir_all(&memory_main_dir)?;

        let leaf_main_dir = directories.leaf_main_dir.join(&contract_hex);
        fs::create_dir_all(&leaf_main_dir)?;

        let mut pages = BTreeSet::new();

        let mut dirty = false;
        // Write dirty pages and keep track of the page indices.
        for (dirty_page, _, page_index) in contract_data.memory.dirty_pages() {
            let page_path: PathBuf =
                page_path_main(&memory_main_dir, *page_index, &commit_id)?;
            fs::write(page_path, dirty_page)?;
            pages.insert(*page_index);
            dirty = true;
        }

        let bytecode_main_path =
            directories.bytecode_main_dir.join(&contract_hex);
        let module_main_path =
            bytecode_main_path.with_extension(OBJECTCODE_EXTENSION);
        let metadata_main_path =
            bytecode_main_path.with_extension(METADATA_EXTENSION);

        // If the contract is new, we write the bytecode, module, and metadata
        // files to disk.
        if contract_data.is_new {
            // we write them to the main location
            fs::write(bytecode_main_path, &contract_data.bytecode)?;
            fs::write(module_main_path, &contract_data.module.serialize())?;
            fs::write(metadata_main_path, &contract_data.metadata)?;
            dirty = true;
        }
        if dirty {
            base_info.contract_hints.push(*contract);
        }
    }

    tracing::trace!("persisting index started");
    for (contract_id, element) in commit.index.iter() {
        if commit_contracts.contains_key(contract_id) {
            // todo: write element to disk at
            // main/leaf/{contract_id}/{commit_id}
            let element_dir_path = directories
                .leaf_main_dir
                .join(hex::encode(contract_id.as_bytes()))
                .join(commit_id.as_ref());
            let element_file_path = element_dir_path.join(ELEMENT_FILE);
            create_dir_all(element_dir_path)?;
            let element_bytes =
                rkyv::to_bytes::<_, 128>(element).map_err(|err| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("Failed serializing element file: {err}"),
                    )
                })?;
            fs::write(&element_file_path, element_bytes)?;
        }
    }
    tracing::trace!("persisting index finished");

    let base_main_path =
        base_path_main(directories.main_dir, commit_id.as_ref())?;
    let base_info_bytes =
        rkyv::to_bytes::<_, 128>(&base_info).map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Failed serializing base info file: {err}"),
            )
        })?;
    fs::write(base_main_path, base_info_bytes)?;

    Ok(())
}

/// Delete the given commit's directory.
fn delete_commit_dir<P: AsRef<Path>>(
    root_dir: P,
    root: Hash,
) -> io::Result<()> {
    let root = hex::encode(root);
    let root_main_dir = root_dir.as_ref().join(MAIN_DIR);
    let commit_dir = root_main_dir.join(&root);
    if commit_dir.exists() {
        let base_info_path = commit_dir.join(BASE_FILE);
        let base_info = base_from_path(base_info_path)?;
        for contract_hint in base_info.contract_hints {
            let contract_hex = hex::encode(contract_hint);
            let commit_mem_path = root_main_dir
                .join(MEMORY_DIR)
                .join(&contract_hex)
                .join(&root);
            fs::remove_dir_all(&commit_mem_path)?;
            let commit_leaf_path =
                root_main_dir.join(LEAF_DIR).join(&contract_hex).join(&root);
            fs::remove_dir_all(&commit_leaf_path)?;
        }
        fs::remove_dir_all(&commit_dir)?;
    }
    Ok(())
}

/// Finalize commit
fn finalize_commit<P: AsRef<Path>>(
    root: Hash,
    root_dir: P,
    _commit: &Commit,
) -> io::Result<()> {
    let main_dir = root_dir.as_ref().join(MAIN_DIR);
    let root = hex::encode(root);
    let commit_path = main_dir.join(&root);
    let base_info_path = commit_path.join(BASE_FILE);
    let base_info = base_from_path(&base_info_path)?;
    for contract_hint in base_info.contract_hints {
        let contract_hex = hex::encode(contract_hint);
        // MEMORY
        let src_path =
            main_dir.join(MEMORY_DIR).join(&contract_hex).join(&root);
        let dst_path = main_dir.join(MEMORY_DIR).join(&contract_hex);
        for entry in fs::read_dir(&src_path)? {
            let filename = entry?.file_name();
            let src_file_path = src_path.join(&filename);
            let dst_file_path = dst_path.join(&filename);
            if src_file_path.is_file() {
                fs::rename(src_file_path, dst_file_path)?;
            }
        }
        fs::remove_dir(&src_path)?;
        // LEAF
        let src_leaf_path =
            main_dir.join(LEAF_DIR).join(&contract_hex).join(&root);
        let dst_leaf_path = main_dir.join(LEAF_DIR).join(contract_hex);
        let src_leaf_file_path = src_leaf_path.join(ELEMENT_FILE);
        let dst_leaf_file_path = dst_leaf_path.join(ELEMENT_FILE);
        if src_leaf_file_path.is_file() {
            fs::rename(src_leaf_file_path, dst_leaf_file_path)?;
        }
        fs::remove_dir(src_leaf_path)?;
    }

    fs::remove_file(base_info_path)?;
    fs::remove_dir(commit_path)?;

    Ok(())
}
