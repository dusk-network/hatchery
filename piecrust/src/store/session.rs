// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use std::collections::btree_map::Entry::{Occupied, Vacant};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc};
use std::{io, mem};

use dusk_wasmtime::Engine;
use piecrust_uplink::ContractId;

use crate::contract::ContractMetadata;
use crate::store::tree::{Hash, PageOpening};
use crate::store::{
    index_from_path, Bytecode, Call, Commit, Memory, Metadata, Module,
    BYTECODE_DIR, INDEX_FILE, MAIN_DIR, MEMORY_DIR, METADATA_EXTENSION,
    OBJECTCODE_EXTENSION, PAGE_SIZE,
};
use crate::Error;

#[derive(Debug, Clone)]
pub struct ContractDataEntry {
    pub bytecode: Bytecode,
    pub module: Module,
    pub metadata: Metadata,
    pub memory: Memory,
    pub is_new: bool,
}

/// The representation of a session with a [`ContractStore`].
///
/// A session tracks modifications to the contracts' memories by keeping
/// references to the set of instantiated contracts.
///
/// The modifications are kept in memory and are only persisted to disk on a
/// call to [`commit`].
///
/// [`commit`]: ContractSession::commit
pub struct ContractSession {
    contracts: BTreeMap<ContractId, ContractDataEntry>,
    engine: Engine,

    base: Option<Commit>,
    root_dir: PathBuf,

    call: mpsc::Sender<Call>,
}

impl Debug for ContractSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContractSession")
            .field("contracts", &self.contracts)
            .field("base", &self.base)
            .field("root_dir", &self.root_dir)
            .finish()
    }
}

impl ContractSession {
    pub(crate) fn new<P: AsRef<Path>>(
        root_dir: P,
        engine: Engine,
        base: Option<Commit>,
        call: mpsc::Sender<Call>,
    ) -> Self {
        Self {
            contracts: BTreeMap::new(),
            engine,
            base,
            root_dir: root_dir.as_ref().into(),
            call,
        }
    }

    /// Returns the root that the session would have if one would decide to
    /// commit it.
    ///
    /// Keep in mind that modifications to memories obtained using [`contract`],
    /// may cause the root to be inconsistent. The caller should ensure that no
    /// instance of [`Memory`] obtained via this session is being modified when
    /// calling this function.
    ///
    /// [`contract`]: ContractSession::contract
    pub fn root(&self) -> Hash {
        let mut commit = self.base.clone().unwrap_or_default();
        for (contract, entry) in &self.contracts {
            commit.index.insert(*contract, &entry.memory);
        }
        let root = commit.index.root();

        *root
    }

    /// Returns an iterator through all the pages of a contract, together with a
    /// proof of their inclusion in the state.
    pub fn memory_pages(
        &self,
        contract: ContractId,
    ) -> Option<impl Iterator<Item = (usize, &[u8], PageOpening)>> {
        let mut commit = self.base.clone().unwrap_or_default();
        for (contract, entry) in &self.contracts {
            commit.index.insert(*contract, &entry.memory);
        }

        let contract_data = self.contracts.get(&contract)?;
        let inclusion_proofs = commit.index.inclusion_proofs(&contract)?;

        let inclusion_proofs =
            inclusion_proofs.map(move |(page_index, opening)| {
                let page_offset = page_index * PAGE_SIZE;
                let page = &contract_data.memory[page_offset..][..PAGE_SIZE];
                (page_index, page, opening)
            });

        Some(inclusion_proofs)
    }

    /// Commits the given session to disk, consuming the session and adding it
    /// to the [`ContractStore`] it was created from.
    ///
    /// Keep in mind that modifications to memories obtained using [`contract`],
    /// may cause the root to be inconsistent. The caller should ensure that no
    /// instance of [`Memory`] obtained via this session is being modified when
    /// calling this function.
    ///
    /// # Safety
    /// This method should only be called once, while immediately allowing the
    /// `ContractSession` to drop.
    ///
    /// [`contract`]: ContractSession::contract
    pub fn commit(&mut self) -> io::Result<Hash> {
        let (replier, receiver) = mpsc::sync_channel(1);

        let mut contracts = BTreeMap::new();
        let mut base = self.base.as_ref().map(|c| Commit {
            index: c.index.clone(),
        });

        mem::swap(&mut self.contracts, &mut contracts);
        mem::swap(&mut self.base, &mut base);

        self.call
            .send(Call::Commit {
                contracts,
                base,
                replier,
            })
            .expect("The receiver should never drop before sending");

        receiver
            .recv()
            .expect("The receiver should always receive a reply")
            .map(|c| *c.index.root())
    }

    fn do_find_page(
        page_index: usize,
        commit: Option<Hash>,
        memory_path: impl AsRef<Path>,
        main_path: impl AsRef<Path>,
    ) -> Option<PathBuf> {
        match commit {
            None => None,
            Some(hash) => {
                let hash_hex = hex::encode(hash.as_bytes());
                let path = memory_path
                    .as_ref()
                    .join(hash_hex.clone())
                    .join(format!("{page_index}"));
                if path.is_file() {
                    Some(path)
                } else {
                    let index_path =
                        main_path.as_ref().join(hash_hex).join(INDEX_FILE);
                    let index = index_from_path(index_path).ok()?;
                    Self::do_find_page(
                        page_index,
                        index.maybe_base,
                        memory_path.as_ref(),
                        main_path.as_ref(),
                    )
                }
            }
        }
    }

    /// Return the bytecode and memory belonging to the given `contract`, if it
    /// exists.
    ///
    /// The contract is considered to exist if either of the following
    /// conditions are met:
    ///
    /// - The contract has been [`deploy`]ed in this session
    /// - The contract was deployed to the base commit
    ///
    /// [`deploy`]: ContractSession::deploy
    pub fn contract(
        &mut self,
        contract: ContractId,
    ) -> io::Result<Option<ContractDataEntry>> {
        let commit_id = self.base.as_ref().map(|commit| *commit.index.root());
        match self.contracts.entry(contract) {
            Vacant(entry) => {
                match &self.base {
                    None => Ok(None),
                    Some(base_commit) => {
                        let _base = base_commit.index.root();

                        match base_commit.index.contains_key(&contract) {
                            true => {
                                // let base_hex = hex::encode(*base);
                                // let base_dir = self.root_dir.join(base_hex);
                                let base_dir = self.root_dir.join(MAIN_DIR);

                                let contract_hex = hex::encode(contract);

                                let bytecode_path = base_dir
                                    .join(BYTECODE_DIR)
                                    .join(&contract_hex);
                                let module_path = bytecode_path
                                    .with_extension(OBJECTCODE_EXTENSION);
                                let metadata_path = bytecode_path
                                    .with_extension(METADATA_EXTENSION);
                                let memory_path = base_dir
                                    .join(MEMORY_DIR)
                                    .join(contract_hex);

                                let bytecode =
                                    Bytecode::from_file(bytecode_path)?;
                                let module = Module::from_file(
                                    &self.engine,
                                    module_path,
                                )?;
                                let metadata =
                                    Metadata::from_file(metadata_path)?;

                                let memory = match base_commit
                                    .index
                                    .get(&contract)
                                {
                                    Some(elem) => {
                                        let page_indices =
                                            elem.page_indices.clone();
                                        let memory_path = memory_path.clone();

                                        Memory::from_files(
                                            module.is_64(),
                                            move |page_index: usize| {
                                                match page_indices
                                                    .contains(&page_index)
                                                {
                                                    true => Some(
                                                        Self::do_find_page(
                                                            page_index,
                                                            commit_id,
                                                            memory_path.clone(),
                                                            base_dir.clone(),
                                                        )
                                                        .unwrap_or(
                                                            memory_path.join(
                                                                format!(
                                                                "{page_index}"
                                                            ),
                                                            ),
                                                        ),
                                                    ),
                                                    false => None,
                                                }
                                            },
                                            elem.len,
                                        )?
                                    }
                                    None => Memory::new(module.is_64())?,
                                };

                                let contract = entry
                                    .insert(ContractDataEntry {
                                        bytecode,
                                        module,
                                        metadata,
                                        memory,
                                        is_new: false,
                                    })
                                    .clone();

                                Ok(Some(contract))
                            }
                            false => Ok(None),
                        }
                    }
                }
            }
            Occupied(entry) => Ok(Some(entry.get().clone())),
        }
    }

    /// Remove the given contract from the session.
    pub fn remove_contract(&mut self, contract: &ContractId) {
        self.contracts.remove(contract);
    }

    /// Checks if contract is deployed
    pub fn contract_deployed(&mut self, contract_id: ContractId) -> bool {
        if self.contracts.contains_key(&contract_id) {
            true
        } else if let Some(base_commit) = &self.base {
            base_commit.index.contains_key(&contract_id)
        } else {
            false
        }
    }

    /// Deploys bytecode to the contract store with the given its `contract_id`.
    ///
    /// See [`deploy`] for deploying bytecode without specifying a contract ID.
    ///
    /// [`deploy`]: ContractSession::deploy
    pub fn deploy<B: AsRef<[u8]>>(
        &mut self,
        contract_id: ContractId,
        bytecode: B,
        module: B,
        metadata: ContractMetadata,
        metadata_bytes: B,
    ) -> io::Result<()> {
        let bytecode = Bytecode::new(bytecode)?;
        let module = Module::new(&self.engine, module)?;
        let metadata = Metadata::new(metadata_bytes, metadata)?;
        let memory = Memory::new(module.is_64())?;

        // If the position is already filled in the tree, the contract cannot be
        // inserted.
        if let Some(base) = self.base.as_ref() {
            if base.index.contains_key(&contract_id) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Existing contract '{contract_id}'"),
                ));
            }
        }

        self.contracts.insert(
            contract_id,
            ContractDataEntry {
                bytecode,
                module,
                metadata,
                memory,
                is_new: true,
            },
        );

        Ok(())
    }

    /// Remove the `old_contract` and move the `new_contract` to the
    /// `old_contract`, effectively replacing the `old_contract` with
    /// `new_contract`.
    pub fn replace(
        &mut self,
        old_contract: ContractId,
        new_contract: ContractId,
    ) -> Result<(), Error> {
        let mut new_contract_data =
            self.contracts.remove(&new_contract).ok_or_else(|| {
                Error::PersistenceError(Arc::new(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Contract '{new_contract}' not found"),
                )))
            })?;

        // The new contract should have the ID of the old contract in its
        // metadata.
        new_contract_data.metadata.set_data(ContractMetadata {
            contract_id: old_contract,
            owner: new_contract_data.metadata.data().owner.clone(),
        })?;

        self.contracts.insert(old_contract, new_contract_data);

        Ok(())
    }

    /// Provides metadata of the contract with a given `contract_id`.
    pub fn contract_metadata(
        &mut self,
        contract_id: &ContractId,
    ) -> Option<&ContractMetadata> {
        let _ = self.contract(*contract_id);
        self.contracts
            .get(contract_id)
            .map(|store_data| store_data.metadata.data())
    }
}

impl Drop for ContractSession {
    fn drop(&mut self) {
        if let Some(base) = self.base.take() {
            let root = base.index.root();
            let _ = self.call.send(Call::SessionDrop(*root));
        }
    }
}
