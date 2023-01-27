// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Formatter};
use std::path::{Path, PathBuf};

use tempfile::tempdir;

use piecrust_uplink::ModuleId;

use crate::commit::{CommitId, ModuleCommitBag, ModuleCommitId, SessionCommit, SessionCommits, CommitPath};
use crate::memory_path::MemoryPath;
use crate::persistable::Persistable;
use crate::session::Session;
use crate::types::MemoryState;
use crate::util::module_id_to_name;
use crate::Error::{self, PersistenceError, SessionError};

const SESSION_COMMITS_FILENAME: &str = "commits";
// const LAST_COMMIT_POSTFIX: &str = "_last";
// const LAST_COMMIT_ID_POSTFIX: &str = "_last_id";

pub struct VM {
    host_queries: HostQueries,
    base_memory_path: PathBuf,
    session_commits: SessionCommits,
    // root: Option<[u8; 32]>,
}

impl VM {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, Error>
    where
        P: Into<PathBuf>,
    {
        let base_memory_path = path.into();
        let session_commits = SessionCommits::from(
            base_memory_path.join(SESSION_COMMITS_FILENAME),
        )?;
        Ok(Self {
            host_queries: HostQueries::default(),
            base_memory_path,
            session_commits,
            // root: None,
        })
    }

    pub fn ephemeral() -> Result<Self, Error> {
        Ok(Self {
            base_memory_path: tempdir()
                .map_err(PersistenceError)?
                .path()
                .into(),
            host_queries: HostQueries::default(),
            session_commits: SessionCommits::new(),
            // root: None,
        })
    }

    /// Registers a [`HostQuery`] with the given `name`.
    pub fn register_host_query<Q, S>(&mut self, name: S, query: Q)
    where
        Q: 'static + HostQuery,
        S: Into<Cow<'static, str>>,
    {
        self.host_queries.insert(name, query);
    }

    pub(crate) fn host_query(
        &self,
        name: &str,
        buf: &mut [u8],
        arg_len: u32,
    ) -> Option<u32> {
        self.host_queries.call(name, buf, arg_len)
    }

    pub fn session(&mut self) -> Session {
        Session::new(self)
    }

    pub(crate) fn memory_path(
        &self,
        module_id: &ModuleId,
    ) -> (MemoryPath, MemoryState) {
        Self::get_memory_path(&self.base_memory_path, module_id)
    }

    pub(crate) fn get_memory_path(
        base_path: &Path,
        module_id: &ModuleId,
    ) -> (MemoryPath, MemoryState) {
        (
            MemoryPath::new(base_path.join(module_id_to_name(*module_id))),
            MemoryState::Uninitialized,
        )
    }

    pub(crate) fn module_last_commit_path_if_present(
        &mut self,
        module_id: &ModuleId,
    ) -> (Option<CommitPath>, bool) {
        let current_session_commit = self.session_commits.get_current_session_commit();
        let csc;
        if current_session_commit.is_none(){
            return (None, false)
        } else {
            csc = current_session_commit.unwrap();
        }
        if let Some(module_commit_id) = csc.module_commit_ids().get(module_id) {
            let (memory_path, _) = self.memory_path(&module_id);
            let module_commit_id = module_commit_id.clone();
            let r = self.get_bag(module_id).restore_module_commit(module_commit_id, &memory_path, false);
            if r.is_err() {
                (None, false)
            } else {
                r.unwrap()
            }
        } else {
            (None, false)
        }
    }

    // pub(crate) fn path_to_module_last_commit_id(
    //     &self,
    //     module_id: &ModuleId,
    // ) -> MemoryPath {
    //     self.path_to_module_with_postfix(module_id, LAST_COMMIT_ID_POSTFIX)
    // }

    // fn path_to_module_with_postfix<P: AsRef<str>>(
    //     &self,
    //     module_id: &ModuleId,
    //     postfix: P,
    // ) -> MemoryPath {
    //     let mut name = module_id_to_name(*module_id);
    //     name.push_str(postfix.as_ref());
    //     let path = self.base_memory_path.join(name);
    //     MemoryPath::new(path)
    // }

    fn path_to_session_commits(&self) -> PathBuf {
        self.base_memory_path.join(SESSION_COMMITS_FILENAME)
    }

    pub(crate) fn add_session_commit(&mut self, session_commit: SessionCommit) {
        self.session_commits.add(session_commit);
    }

    // todo move it to session commits
    pub(crate) fn restore_session(
        &mut self,
        commit_id: &CommitId,
    ) -> Result<(), Error> {
        let base_path = self.base_path();

        let mut pairs = Vec::<(ModuleId, ModuleCommitId)>::new();

        {
            let r = &mut self.session_commits.get_session_commit(commit_id);
            if r.is_none() {
                return Err(SessionError("unknown session commit id".into()))
            }

            let session_commit = r.unwrap();
            for (module_id, module_commit_id) in session_commit.module_commit_ids().iter() {
                pairs.push((*module_id, *module_commit_id))
            }
        }
        self.session_commits.current = *commit_id; // todo move it to session commits

        for (module_id, module_commit_id) in pairs {
            let (memory_path, _) = Self::get_memory_path(&base_path, &module_id);
            // let module_commit = ModuleCommit::from_id_and_path(module_commit_id, memory_path.path())?;
            self.session_commits.get_bag(&module_id).restore_module_commit(module_commit_id, &memory_path, true)?;
        }

        Ok(())
    }

    pub fn persist(&self) -> Result<(), Error> {
        self.session_commits.persist(self.path_to_session_commits())
    }

    pub fn base_path(&self) -> PathBuf {
        self.base_memory_path.to_path_buf()
    }

    // todo eliminate refresh
    pub(crate) fn root(&mut self, _refresh: bool) -> Result<[u8; 32], Error> {
        let root = self.session_commits.get_current_commit().to_bytes();
        Ok(root)
    }

    pub(crate) fn get_bag(&mut self, module_id: &ModuleId) -> &mut ModuleCommitBag {
        self.session_commits.get_bag(module_id)
    }
}

#[derive(Default)]
pub struct HostQueries {
    map: BTreeMap<Cow<'static, str>, Box<dyn HostQuery>>,
}

impl Debug for HostQueries {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.map.keys()).finish()
    }
}

impl HostQueries {
    pub fn insert<Q, S>(&mut self, name: S, query: Q)
    where
        Q: 'static + HostQuery,
        S: Into<Cow<'static, str>>,
    {
        self.map.insert(name.into(), Box::new(query));
    }

    pub fn call(&self, name: &str, buf: &mut [u8], len: u32) -> Option<u32> {
        self.map.get(name).map(|host_query| host_query(buf, len))
    }
}

/// A query executable on the host.
///
/// The buffer containing the argument the module used to call the query
/// together with its length are passed as arguments to the function, and should
/// be processed first. Once this is done, the implementor should emplace the
/// return of the query in the same buffer, and return its length.
pub trait HostQuery: Send + Sync + Fn(&mut [u8], u32) -> u32 {}
impl<F> HostQuery for F where F: Send + Sync + Fn(&mut [u8], u32) -> u32 {}
