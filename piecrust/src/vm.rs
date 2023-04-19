// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Formatter};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::thread;

use tempfile::tempdir;

use crate::session::Session;
use crate::store::ModuleStore;
use crate::Error::{self, PersistenceError};

/// A handle to the piecrust virtual machine.
///
/// It is instantiated using [`new`] or [`ephemeral`], and can be used to spawn
/// multiple [`Session`]s using either [`session`] or [`genesis_session`].
///
/// These sessions are synchronized with the help of a sync loop. [`Deletions`]
/// and [`squashes`] are assured to not delete any commits used as a base for
/// sessions until these are dropped. A handle to this loop is available at
/// [`sync_thread`].
///
/// Users are encouraged to instantiate a `VM` once during the lifetime of their
/// program and spawn sessions as needed.
///
/// [`new`]: VM::new
/// [`ephemeral`]: VM::ephemeral
/// [`Session`]: Session
/// [`session`]: VM::session
/// [`genesis_session`]: VM::genesis_session
/// [`Deletions`]: VM::delete_commit
/// [`squashes`]: VM::squash_commit
/// [`sync_thread`]: VM::sync_thread
#[derive(Debug)]
pub struct VM {
    host_queries: HostQueries,
    store: ModuleStore,
}

impl VM {
    /// Creates a new `VM`, reading the given `dir`ectory for existing commits
    /// and bytecode.
    ///
    /// The directory will be used to save any future session commits made by
    /// this `VM` instance.
    ///
    /// # Errors
    /// If the directory contains unparseable or inconsistent data.
    pub fn new<P: AsRef<Path>>(root_dir: P) -> Result<Self, Error>
    where
        P: Into<PathBuf>,
    {
        let store = ModuleStore::new(root_dir)
            .map_err(|err| PersistenceError(Arc::new(err)))?;
        Ok(Self {
            host_queries: HostQueries::default(),
            store,
        })
    }

    /// Creates a new `VM` using a new temporary directory.
    ///
    /// Any session commits made by this machine should be considered discarded
    /// once this `VM` instance drops.
    ///
    /// # Errors
    /// If creating a temporary directory fails.
    pub fn ephemeral() -> Result<Self, Error> {
        let tmp = tempdir().map_err(|err| PersistenceError(Arc::new(err)))?;
        let tmp = tmp.path().to_path_buf();

        let store = ModuleStore::new(tmp)
            .map_err(|err| PersistenceError(Arc::new(err)))?;

        Ok(Self {
            host_queries: HostQueries::default(),
            store,
        })
    }

    /// Registers a [host `query`] with the given `name`.
    ///
    /// The query will be available to any session spawned *after* this was
    /// called.
    ///
    /// [host `query`]: HostQuery
    pub fn register_host_query<Q, S>(&mut self, name: S, query: Q)
    where
        Q: 'static + HostQuery,
        S: Into<Cow<'static, str>>,
    {
        self.host_queries.insert(name, query);
    }

    /// Spawn a [`Session`] with the given commit as the `base`.
    ///
    /// Sessions spawned with a commit as a base are running modifications to
    /// said commit. For sessions with no commit as base use
    /// [`genesis_session`].
    ///
    /// # Errors
    /// If the given base commit does not exist.
    ///
    /// [`Session`]: Session
    /// [`genesis_session`]: VM::genesis_session
    pub fn session(&self, base: [u8; 32]) -> Result<Session, Error> {
        let module_session = self
            .store
            .session(base)
            .map_err(|err| PersistenceError(Arc::new(err)))?;
        Ok(Session::new(module_session, self.host_queries.clone()))
    }

    /// Spawn a [`Session`] with no commit as a base.
    ///
    /// Genesis sessions are used for initial state deployment. For sessions
    /// based on previous commits use [`session`].
    ///
    /// [`Session`]: Session
    /// [`session`]: VM::session
    pub fn genesis_session(&self) -> Session {
        let module_session = self.store.genesis_session();
        Session::new(module_session, self.host_queries.clone())
    }

    /// Return all existing commits.
    pub fn commits(&self) -> Vec<[u8; 32]> {
        self.store.commits()
    }

    /// Remove the diff files from a commit by applying them to the base
    /// memories, and writing them back to disk.
    ///
    /// # Errors
    /// If this function fails, it may be due to any number of reasons:
    ///
    /// - [`remove_file`] may fail
    /// - [`write`] may fail
    ///
    /// Failing may result in a corrupted commit, and the user is encouraged to
    /// call [`delete_commit`].
    ///
    /// [`remove_file`]: std::fs::remove_file
    /// [`write`]: std::fs::write
    /// [`delete_commit`]: VM::delete_commit
    pub fn squash_commit(&self, root: [u8; 32]) -> Result<(), Error> {
        self.store
            .squash_commit(root)
            .map_err(|err| PersistenceError(Arc::new(err)))
    }

    /// Deletes the given commit from disk.
    pub fn delete_commit(&self, root: [u8; 32]) -> Result<(), Error> {
        self.store
            .delete_commit(root)
            .map_err(|err| PersistenceError(Arc::new(err)))
    }

    /// Return the root directory of the virtual machine.
    ///
    /// This is either the directory passed in by using [`new`], or the
    /// temporary directory created using [`ephemeral`].
    ///
    /// [`new`]: VM::new
    /// [`ephemeral`]: VM::ephemeral
    pub fn root_dir(&self) -> &Path {
        self.store.root_dir()
    }

    /// Returns a reference to the synchronization thread.
    pub fn sync_thread(&self) -> &thread::Thread {
        self.store.sync_loop()
    }
}

#[derive(Default, Clone)]
pub struct HostQueries {
    map: BTreeMap<Cow<'static, str>, Arc<dyn HostQuery>>,
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
        self.map.insert(name.into(), Arc::new(query));
    }

    pub fn call(&self, name: &str, buf: &mut [u8], len: u32) -> Option<u32> {
        self.map.get(name).map(|host_query| host_query(buf, len))
    }
}

/// A query executable on the host.
///
/// The buffer containing the argument the module used to call the query,
/// together with the argument's length, are passed as arguments to the
/// function, and should be processed first. Once this is done, the implementor
/// should emplace the return of the query in the same buffer, and return the
/// length written.
pub trait HostQuery: Send + Sync + Fn(&mut [u8], u32) -> u32 {}
impl<F> HostQuery for F where F: Send + Sync + Fn(&mut [u8], u32) -> u32 {}
