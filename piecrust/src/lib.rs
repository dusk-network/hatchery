// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Piecrust VM for WASM smart contract execution.
//!
//! A [`VM`] is instantiated by calling [`VM::new`] using a directory for
//! storage of commits.
//!
//! Once instantiation has been successful, [`Session`]s can be started using
//! [`VM::session`]. A session represents the execution of a sequence of
//! [`call`]  and [`deploy`] calls, and stores mutations to the underlying state
//! as a result. This sequence of mutations may be committed - meaning written
//! to the VM's directory - using [`commit`]. After a commit, the resulting
//! state may be used by starting a new session with it as a base.
//!
//! Contract execution is metered in terms of `gas`. The limit for gas used in a
//! `call` or `deploy` is passed in their respective function signatures. If the
//! limit is exceeded during the call an error will be returned. To learn more
//! about the compiler middleware used to achieve this, please refer to the
//! relevant [runtime docs].
//!
//! # State Representation and Session/Commit Mechanism
//!
//! Smart Contracts are represented on disk by two separate files: their WASM
//! bytecode and their linear memory at a given commit. The collection of all
//! the memories of smart contracts at a given commit is referred to as the
//! *state* of said commit.
//!
//! During a session, each contract called in the sequence of
//! queries/transactions is loaded by:
//!
//! - Reading the contract's bytecode file
//! - Memory mapping the linear memory file copy-on-write (CoW)
//!
//! Using copy-on-write mappings of linear memories ensures that each commit is
//! never mutated in place by a session, with the important exception of
//! [`deletions`].
//!
//! # Session Concurrency
//!
//! Multiple sessions may be started concurrently on the same `VM`, and then
//! passed on to different threads. These sessions are then non-overlapping
//! sequences of mutations of a state and may all be committed/dropped
//! simultaneously.
//!
//! ```
//! use piecrust::{Session, VM};
//!
//! fn assert_send<T: Send>() {}
//!
//! // Both VM and Session are `Send`
//! assert_send::<VM>();
//! assert_send::<Session>();
//! ```
//!
//! This is achieved by synchronizing commit deletions, and session
//! spawns/commits using a synchronization loop started on VM instantiation.
//!
//! # Call Atomicity
//!
//! Contract calls are executed atomically, that is, they are either executed
//! completely or they are not executed at all.
//!
//! In other words, if the call succeeds, all the state mutations they produce
//! are kept, while if they produce an error (e.g. they panic), all such
//! mutations are reverted.
//!
//! If the call was made within another call (i.e., the caller was a contract),
//! we ensure all mutations are reverted by undoing the whole call stack of the
//! current transact/query execution, and re-executing it with the exception of
//! the error-producing call, which returns an error without being actually
//! executed.
//!
//! # 32 vs 64-bit
//!
//! Contracts can be compiled to either 32 or 64-bit WASM - i.e. the `memory64`
//! proposal. 32-bit contracts have a maximum memory size of 4GiB, while 64-bit
//! contracts have a maximum memory size of 4TiB.
//!
//! # Usage
//! ```
//! use piecrust::{contract_bytecode, ContractData, SessionData, VM};
//! let mut vm = VM::ephemeral().unwrap();
//!
//! const OWNER: [u8; 32] = [0u8; 32];
//! const LIMIT: u64 = 1_000_000;
//!
//! let mut session = vm.session(SessionData::builder()).unwrap();
//! let counter_id = session
//!     .deploy(
//!         contract_bytecode!("counter"),
//!         ContractData::builder().owner(OWNER),
//!         LIMIT,
//!     )
//!     .unwrap();
//!
//! assert_eq!(session.call::<_, i64>(counter_id, "read_value", &(), LIMIT).unwrap().data, 0xfc);
//! session.call::<_, ()>(counter_id, "increment", &(), LIMIT).unwrap();
//! assert_eq!(session.call::<_, i64>(counter_id, "read_value", &(), LIMIT).unwrap().data, 0xfd);
//!
//! let commit_root = session.commit().unwrap();
//! assert_eq!(commit_root, vm.commits()[0]);
//! ```
//!
//! [`VM`]: VM
//! [`VM::new`]: VM::new
//! [`Session`]: Session
//! [`VM::session`]: VM::session
//! [`call`]: Session::call
//! [`deploy`]: Session::deploy
//! [`commit`]: Session::commit
//! [runtime docs]: dusk_wasmtime::Config::consume_fuel
//! [`deletions`]: VM::delete_commit

#[macro_use]
mod bytecode_macro;
mod call_tree;
mod config;
mod contract;
mod error;
mod imports;
mod instance;
mod session;
mod store;
mod types;
mod vm;

pub use call_tree::{CallTree, CallTreeElem};
pub use contract::{ContractData, ContractDataBuilder};
pub use error::Error;
pub use session::{CallReceipt, Session, SessionData};
pub use store::PageOpening;
pub use vm::{HostQuery, VM};

// re-export the contents of the `piecrust-uplink` crate wholesale, ensuring
// this is the only crate we need to define and use a VM.
pub use piecrust_uplink::*;
