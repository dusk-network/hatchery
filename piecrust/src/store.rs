// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! A library for dealing with memories in trees.

mod bytecode;
mod diff;
mod memory;
mod mmap;

use std::collections::btree_map::Entry::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::{fs, io, mem, thread};

use flate2::write::DeflateEncoder;
use flate2::Compression;

pub use bytecode::Bytecode;
use diff::diff;
pub use memory::Memory;
use piecrust_uplink::ModuleId;

const ROOT_LEN: usize = 32;

const BYTECODE_DIR: &str = "bytecode";
const MEMORY_DIR: &str = "memory";
const DIFF_EXTENSION: &str = "diff";
const MERKLE_FILE: &str = "merkle";

type Root = [u8; ROOT_LEN];

/// A store for all module commits.
pub struct ModuleStore {
    sync_loop: thread::JoinHandle<()>,
    call: mpsc::Sender<Call>,
    root_dir: PathBuf,
}

impl ModuleStore {
    /// Loads a new module store from the given `dir`ectory.
    ///
    /// This also starts the synchronization loop, which is used to align
    /// [`commit`]s, [`delete`]s, and [`session spawning`] to avoid deleting
    /// commits in use by a session.
    ///
    /// [`commit`]: ModuleSession::commit
    /// [`delete`]: ModuleStore::delete_commit
    /// [`session spawning`]: ModuleStore::session
    pub fn new<P: AsRef<Path>>(dir: P) -> io::Result<Self> {
        let root_dir = dir.as_ref();

        fs::create_dir_all(root_dir)?;

        let (call, calls) = mpsc::channel();
        let commits = read_all_commits(root_dir)?;

        let loop_root_dir = root_dir.to_path_buf();
        let sync_loop =
            thread::spawn(|| sync_loop(loop_root_dir, commits, calls));

        Ok(Self {
            sync_loop,
            call,
            root_dir: root_dir.into(),
        })
    }

    /// Create a new [`ModuleSession`] with the given `base` commit.
    ///
    /// Errors if the given base commit does not exist in the store.
    pub fn session(&self, base: Root) -> io::Result<ModuleSession> {
        let base_commit = self
            .call_with_replier(|replier| Call::CommitHold { base, replier })
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("No such base commit: {}", hex::encode(base)),
                )
            })?;

        Ok(self.session_with_base(Some((base, base_commit))))
    }

    /// Create a new [`ModuleSession`] that has no base commit.
    ///
    /// For session with a base commit, please see [`session`].
    ///
    /// [`session`]: ModuleStore::session
    pub fn genesis_session(&self) -> ModuleSession {
        self.session_with_base(None)
    }

    /// Returns the roots of the commits that are currently in the store.
    pub fn commits(&self) -> Vec<Root> {
        self.call_with_replier(|replier| Call::GetCommits { replier })
    }

    /// Deletes a given `commit` from the store.
    ///
    /// If a `ModuleSession` is currently using the given commit as a base, the
    /// operation will be queued for completion until the last session using the
    /// commit has dropped.
    ///
    /// It will block until the operation is completed.
    pub fn delete_commit(&self, commit: Root) -> io::Result<()> {
        self.call_with_replier(|replier| Call::CommitDelete { commit, replier })
    }

    /// Return the handle to the thread running the store's synchronization
    /// loop.
    pub fn sync_loop(&self) -> &thread::Thread {
        self.sync_loop.thread()
    }

    /// Return the path to the VM directory.
    pub fn root_dir(&self) -> &Path {
        &self.root_dir
    }

    fn call_with_replier<T, F>(&self, closure: F) -> T
    where
        F: Fn(mpsc::SyncSender<T>) -> Call,
    {
        let (replier, receiver) = mpsc::sync_channel(1);

        self.call.send(closure(replier)).expect(
            "The receiver should never be dropped while there are senders",
        );

        receiver
            .recv()
            .expect("The sender should never be dropped without responding")
    }

    fn session_with_base(&self, base: Option<(Root, Commit)>) -> ModuleSession {
        ModuleSession {
            modules: BTreeMap::new(),
            base,
            root_dir: self.root_dir.clone(),
            call: self.call.clone(),
        }
    }
}

fn read_all_commits<P: AsRef<Path>>(
    root_dir: P,
) -> io::Result<BTreeMap<Root, Commit>> {
    let root_dir = root_dir.as_ref();
    let mut commits = BTreeMap::new();

    for entry in fs::read_dir(root_dir)? {
        let entry = entry?;
        if entry.path().is_dir() {
            let (root, commit) = read_commit(entry.path())?;
            commits.insert(root, commit);
        }
    }

    Ok(commits)
}

fn read_commit<P: AsRef<Path>>(commit_dir: P) -> io::Result<(Root, Commit)> {
    let commit_dir = commit_dir.as_ref();

    let root = root_from_dir(commit_dir)?;
    let commit = commit_from_dir(commit_dir)?;

    Ok((root, commit))
}

fn root_from_dir<P: AsRef<Path>>(dir: P) -> io::Result<Root> {
    let dir = dir.as_ref();
    let dir_name = dir.file_name().unwrap().to_str().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Directory name \"{dir:?}\" is invalid UTF-8"),
        )
    })?;

    let dir_name_bytes = hex::decode(dir_name).map_err(|err| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Directory name \"{dir_name}\" is invalid hex: {err}"),
        )
    })?;

    if dir_name_bytes.len() != ROOT_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Expected directory name \"{dir_name}\" to be of size {ROOT_LEN}, was {}", dir_name_bytes.len())
        ));
    }

    let mut root = [0u8; ROOT_LEN];
    root.copy_from_slice(&dir_name_bytes);

    Ok(root)
}

fn commit_from_dir<P: AsRef<Path>>(dir: P) -> io::Result<Commit> {
    let dir = dir.as_ref();

    let merkle_path = dir.join(MERKLE_FILE);

    let modules = merkle_from_path(merkle_path)?;
    let mut diffs = BTreeSet::new();

    let bytecode_dir = dir.join(BYTECODE_DIR);
    let memory_dir = dir.join(MEMORY_DIR);

    for module in modules.keys() {
        let module_hex = hex::encode(module);

        // Check that all modules in the merkle file have a corresponding
        // bytecode and memory.
        let bytecode_path = bytecode_dir.join(&module_hex);
        if !bytecode_path.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Non-existing bytecode for module: {module_hex}"),
            ));
        }

        let memory_path = memory_dir.join(&module_hex);
        if !memory_path.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Non-existing memory for module: {module_hex}"),
            ));
        }

        // If there is a diff file for a given module, register it in the map.
        let diff_path = memory_path.with_extension(DIFF_EXTENSION);
        if diff_path.is_file() {
            diffs.insert(*module);
        }
    }

    Ok(Commit { modules, diffs })
}

fn merkle_from_path<P: AsRef<Path>>(
    path: P,
) -> io::Result<BTreeMap<ModuleId, Root>> {
    let path = path.as_ref();

    let modules_bytes = fs::read(path)?;
    let modules = rkyv::from_bytes(&modules_bytes).map_err(|err| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Invalid merkle file \"{path:?}\": {err}"),
        )
    })?;

    Ok(modules)
}

#[derive(Clone)]
struct Commit {
    modules: BTreeMap<ModuleId, Root>,
    diffs: BTreeSet<ModuleId>,
}

enum Call {
    Commit {
        modules: BTreeMap<ModuleId, (Bytecode, Memory)>,
        base: Option<(Root, Commit)>,
        replier: mpsc::SyncSender<io::Result<(Root, Commit)>>,
    },
    GetCommits {
        replier: mpsc::SyncSender<Vec<Root>>,
    },
    CommitDelete {
        commit: Root,
        replier: mpsc::SyncSender<io::Result<()>>,
    },
    CommitHold {
        base: Root,
        replier: mpsc::SyncSender<Option<Commit>>,
    },
    SessionDrop(Root),
}

fn sync_loop<P: AsRef<Path>>(
    root_dir: P,
    commits: BTreeMap<Root, Commit>,
    calls: mpsc::Receiver<Call>,
) {
    let root_dir = root_dir.as_ref();

    let mut sessions = BTreeMap::new();
    let mut delete_bag = BTreeMap::new();
    let mut commits = commits;

    for call in calls {
        match call {
            // Writes a session to disk and adds it to the map of existing commits.
            Call::Commit {
                modules,
                base,
                replier,
            } => {
                let io_result = write_commit(root_dir, &mut commits, base, modules);
                let _ = replier.send(io_result);
            }
            Call::GetCommits {
                replier
            } => {
                let _ = replier.send(commits.keys().copied().collect());
            }
            // Delete a commit from disk. If the commit is currently in use - as
            // in it is held by at least one session using `Call::SessionHold` -
            // queue it for deletion once no session is holding it.
            Call::CommitDelete { commit: root, replier } => {
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
                commits.remove(&root);
                let _ = replier.send(io_result);
            }
            // Increment the hold count of a commit to prevent it from deletion
            // on a `Call::CommitDelete`.
            Call::CommitHold {
                base,
                replier,
            } => {
                let base_commit = commits.get(&base).cloned();

                if base_commit.is_some() {
                    match sessions.entry(base) {
                        Vacant(entry) => {
                            entry.insert(1);
                        }
                        Occupied(mut entry) => {
                            *entry.get_mut() += 1;
                        }
                    }
                }

                let _ = replier.send(base_commit);
            }
            // Signal that a session with a base commit has dropped and
            // decrements the hold count, once incremented using
            // `Call::SessionHold`. If this is the last session that held that
            // commit, and there are queued deletions, execute them.
            Call::SessionDrop(base) => match sessions.entry(base) {
                Vacant(_) => unreachable!("If a session is dropped there must be a session hold entry"),
                Occupied(mut entry) => {
                    *entry.get_mut() -= 1;

                    if *entry.get() == 0 {
                        entry.remove();

                        match delete_bag.entry(base) {
                            Vacant(_) => {}
                            Occupied(entry) => {
                                for replier in entry.remove() {
                                    let io_result =
                                        delete_commit_dir(root_dir, base);
                                    commits.remove(&base);
                                    let _ = replier.send(io_result);
                                }
                            }
                        }
                    }
                }
            },
        }
    }
}

fn write_commit<P: AsRef<Path>>(
    root_dir: P,
    commits: &mut BTreeMap<Root, Commit>,
    base: Option<(Root, Commit)>,
    commit_modules: BTreeMap<ModuleId, (Bytecode, Memory)>,
) -> io::Result<(Root, Commit)> {
    let root_dir = root_dir.as_ref();

    let (root, modules) = compute_root(&base, &commit_modules);
    let root_hex = hex::encode(root);

    let commit_dir = root_dir.join(root_hex);

    // Don't write the commit if it already exists on disk. This may happen if
    // the same transactions on the same base commit for example.
    if let Some(commit) = commits.get(&root) {
        return Ok((root, commit.clone()));
    }

    match write_commit_inner(
        root_dir,
        &commit_dir,
        base,
        modules,
        commit_modules,
    ) {
        Ok(commit) => {
            commits.insert(root, commit.clone());
            Ok((root, commit))
        }
        Err(err) => {
            let _ = fs::remove_dir_all(commit_dir);
            Err(err)
        }
    }
}

/// Writes a commit to disk.
fn write_commit_inner<P: AsRef<Path>>(
    root_dir: P,
    commit_dir: P,
    base: Option<(Root, Commit)>,
    modules: BTreeMap<ModuleId, Root>,
    commit_modules: BTreeMap<ModuleId, (Bytecode, Memory)>,
) -> io::Result<Commit> {
    let root_dir = root_dir.as_ref();
    let commit_dir = commit_dir.as_ref();

    let bytecode_dir = commit_dir.join(BYTECODE_DIR);
    fs::create_dir_all(&bytecode_dir)?;

    let memory_dir = commit_dir.join(MEMORY_DIR);
    fs::create_dir_all(&memory_dir)?;

    let mut diffs = BTreeSet::new();

    match base {
        None => {
            for (module, (bytecode, memory)) in commit_modules {
                let module_hex = hex::encode(module);

                let bytecode_path = bytecode_dir.join(&module_hex);
                let memory_path = memory_dir.join(&module_hex);

                fs::write(bytecode_path, &bytecode)?;
                fs::write(memory_path, &memory.read())?;
            }
        }
        Some((base, base_commit)) => {
            let base_hex = hex::encode(base);
            let base_dir = root_dir.join(base_hex);

            let base_bytecode_dir = base_dir.join(BYTECODE_DIR);
            let base_memory_dir = base_dir.join(MEMORY_DIR);

            for module in base_commit.modules.keys() {
                let module_hex = hex::encode(module);

                let bytecode_path = bytecode_dir.join(&module_hex);
                let memory_path = memory_dir.join(&module_hex);

                let base_bytecode_path = base_bytecode_dir.join(&module_hex);
                let base_memory_path = base_memory_dir.join(&module_hex);

                fs::hard_link(base_bytecode_path, bytecode_path)?;
                fs::hard_link(&base_memory_path, &memory_path)?;

                // If there is a diff of this memory in the base module, and it
                // hasn't been touched in this commit, link it as well.
                if base_commit.diffs.contains(module)
                    && !commit_modules.contains_key(module)
                {
                    let base_diff_path =
                        base_memory_path.with_extension(DIFF_EXTENSION);
                    let diff_path = memory_path.with_extension(DIFF_EXTENSION);

                    fs::hard_link(base_diff_path, diff_path)?;
                }
            }

            for (module, (bytecode, memory)) in commit_modules {
                let module_hex = hex::encode(module);

                match base_commit.modules.contains_key(&module) {
                    true => {
                        let base_memory_path =
                            base_memory_dir.join(&module_hex);
                        let memory_diff_path = memory_dir
                            .join(&module_hex)
                            .with_extension(DIFF_EXTENSION);

                        let base_memory = Memory::from_file(base_memory_path)?;
                        let memory_diff = File::create(memory_diff_path)?;

                        let mut encoder = DeflateEncoder::new(
                            memory_diff,
                            Compression::default(),
                        );

                        diff(
                            &base_memory.read(),
                            &memory.read(),
                            &mut encoder,
                        )?;

                        diffs.insert(module);
                    }
                    false => {
                        let bytecode_path = bytecode_dir.join(&module_hex);
                        let memory_path = memory_dir.join(&module_hex);

                        fs::write(bytecode_path, &bytecode)?;
                        fs::write(memory_path, memory.read())?;
                    }
                }
            }
        }
    }

    let merkle_path = commit_dir.join(MERKLE_FILE);
    let merkle_bytes = rkyv::to_bytes::<_, 128>(&modules)
        .map_err(|err| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Failed serializing merkle file: {err}"),
            )
        })?
        .to_vec();
    fs::write(merkle_path, merkle_bytes)?;

    Ok(Commit { modules, diffs })
}

/// Compute the root of the state.
///
/// The root is computed by arranging all existing modules in order of their
/// module ID, and computing a hash of the module ID, the bytecode, and the
/// current state of the memory. These hashes then form the leaves of the tree
/// whose root is then computed.
fn compute_root<'a, I>(
    base: &Option<(Root, Commit)>,
    modules: I,
) -> (Root, BTreeMap<ModuleId, Root>)
where
    I: IntoIterator<Item = (&'a ModuleId, &'a (Bytecode, Memory))>,
{
    let iter = modules.into_iter();

    let mut leaves_map = BTreeMap::new();

    // Compute the hashes of changed memories
    for (module, (_, memory)) in iter {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&memory.read());
        leaves_map.insert(*module, Root::from(hasher.finalize()));
    }

    // Store the hashes of *un*changed memories
    if let Some((_, base_commit)) = base {
        for (module, root) in &base_commit.modules {
            if !leaves_map.contains_key(module) {
                leaves_map.insert(*module, *root);
            }
        }
    }

    let mut leaves: Vec<Root> = leaves_map.clone().into_values().collect();

    while leaves.len() > 1 {
        leaves = leaves
            .chunks(2)
            .map(|chunk| {
                let mut hasher = blake3::Hasher::new();

                hasher.update(&chunk[0]);
                if chunk.len() > 1 {
                    hasher.update(&chunk[1]);
                }

                Root::from(hasher.finalize())
            })
            .collect();
    }

    (leaves[0], leaves_map)
}

/// Delete the given commit's directory.
fn delete_commit_dir<P: AsRef<Path>>(
    root_dir: P,
    root: Root,
) -> io::Result<()> {
    let root = hex::encode(root);
    let commit_dir = root_dir.as_ref().join(root);
    fs::remove_dir_all(commit_dir)
}

/// The representation of a session with a [`ModuleStore`].
///
/// A session tracks modifications to the modules' memories by keeping
/// references to the set of instantiated modules.
///
/// The modifications are kept in memory and are only persisted to disk on a
/// call to [`commit`].
///
/// [`commit`]: ModuleSession::commit
pub struct ModuleSession {
    modules: BTreeMap<ModuleId, (Bytecode, Memory)>,

    base: Option<(Root, Commit)>,
    root_dir: PathBuf,

    call: mpsc::Sender<Call>,
}

impl ModuleSession {
    /// Returns the root that the session would have if one would decide to
    /// commit it.
    ///
    /// Keep in mind that modifications to memories obtained using [`module`],
    /// may cause the root to be inconsistent. The caller should ensure that no
    /// instance of [`Memory`] obtained via this session is being modified when
    /// calling this function.
    ///
    /// [`module`]: ModuleSession::module
    pub fn root(&self) -> Root {
        let (root, _) = compute_root(&self.base, &self.modules);
        root
    }

    /// Commits the given session to disk, consuming the session and adding it
    /// to the [`ModuleStore`] it was created from.
    ///
    /// Keep in mind that modifications to memories obtained using [`module`],
    /// may cause the root to be inconsistent. The caller should ensure that no
    /// instance of [`Memory`] obtained via this session is being modified when
    /// calling this function.
    ///
    /// [`module`]: ModuleSession::module
    pub fn commit(self) -> io::Result<Root> {
        let mut slef = self;

        let (replier, receiver) = mpsc::sync_channel(1);

        let mut modules = BTreeMap::new();
        let mut base = slef.base.as_ref().map(|(root, _)| {
            (
                *root,
                Commit {
                    modules: BTreeMap::new(),
                    diffs: BTreeSet::new(),
                },
            )
        });

        mem::swap(&mut slef.modules, &mut modules);
        mem::swap(&mut slef.base, &mut base);

        slef.call
            .send(Call::Commit {
                modules,
                base,
                replier,
            })
            .expect("The receiver should never drop before sending");

        receiver
            .recv()
            .expect("The receiver should always receive a reply")
            .map(|p| p.0)
    }

    /// Return the bytecode and memory belonging to the given `module`, if it
    /// exists.
    ///
    /// The module is considered to exist if either of the following conditions
    /// are met:
    ///
    /// - The module has been [`deploy`]ed in this session
    /// - The module was deployed to the base commit
    ///
    /// [`deploy`]: ModuleSession::deploy
    pub fn module(
        &mut self,
        module: ModuleId,
    ) -> io::Result<Option<(Bytecode, Memory)>> {
        match self.modules.entry(module) {
            Vacant(entry) => match &self.base {
                None => Ok(None),
                Some((base, base_commit)) => {
                    match base_commit.modules.contains_key(&module) {
                        true => {
                            let base_hex = hex::encode(base);
                            let base_dir = self.root_dir.join(base_hex);

                            let module_hex = hex::encode(module);

                            let bytecode_path =
                                base_dir.join(BYTECODE_DIR).join(&module_hex);
                            let memory_path =
                                base_dir.join(MEMORY_DIR).join(module_hex);
                            let memory_diff_path =
                                memory_path.with_extension(DIFF_EXTENSION);

                            let bytecode = Bytecode::from_file(bytecode_path)?;
                            let memory =
                                match base_commit.diffs.contains(&module) {
                                    true => Memory::from_file_and_diff(
                                        memory_path,
                                        memory_diff_path,
                                    )?,
                                    false => Memory::from_file(memory_path)?,
                                };

                            let module =
                                entry.insert((bytecode, memory)).clone();

                            Ok(Some(module))
                        }
                        false => Ok(None),
                    }
                }
            },
            Occupied(entry) => Ok(Some(entry.get().clone())),
        }
    }

    /// Deploys bytecode to the module store.
    ///
    /// The module ID returned is computed using the `blake3` hash of the given
    /// bytecode. See [`deploy_with_id`] for deploying bytecode with a given
    /// module ID.
    ///
    /// [`deploy_with_id`]: ModuleSession::deploy_with_id
    pub fn deploy<B: AsRef<[u8]>>(
        &mut self,
        bytecode: B,
    ) -> io::Result<ModuleId> {
        let bytes = bytecode.as_ref();
        let hash = blake3::hash(bytes);

        let module_id = ModuleId::from_bytes(hash.into());
        self.deploy_with_id(module_id, bytes)?;

        Ok(module_id)
    }

    /// Deploys bytecode to the module store with the given its `module_id`.
    ///
    /// See [`deploy`] for deploying bytecode without specifying a module ID.
    ///
    /// [`deploy`]: ModuleSession::deploy
    pub fn deploy_with_id<B: AsRef<[u8]>>(
        &mut self,
        module_id: ModuleId,
        bytecode: B,
    ) -> io::Result<()> {
        if self.modules.contains_key(&module_id) {
            let module_hex = hex::encode(module_id);
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Failed deploying {module_hex}: already deployed"),
            ));
        }

        if let Some((base, base_commit)) = &self.base {
            if base_commit.modules.contains_key(&module_id) {
                let module_hex = hex::encode(module_id);
                let base_hex = hex::encode(base);
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Failed deploying {module_hex}: already deployed in base commit {base_hex}"),
                ));
            }
        }

        let memory = Memory::new()?;
        let bytecode = Bytecode::new(bytecode)?;

        self.modules.insert(module_id, (bytecode, memory));

        Ok(())
    }
}

impl Drop for ModuleSession {
    fn drop(&mut self) {
        if let Some((base, _)) = self.base.take() {
            let _ = self.call.send(Call::SessionDrop(base));
        }
    }
}
