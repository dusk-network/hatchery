// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Module to get the hash value from the host.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use piecrust_uplink as uplink;
use uplink::{ModuleId, State};

/// Struct that describes the state of the host module
pub struct Hoster;

/// Module id, initialized by the host when the module is deployed
#[no_mangle]
static SELF_ID: ModuleId = ModuleId::uninitialized();

/// State of the host module
static mut STATE: State<Hoster> = State::new(Hoster);

impl Hoster {
    /// Call this same function via the host and return the bytes from its
    /// argument
    pub fn hash(&self, bytes: Vec<u8>) -> [u8; 32] {
        uplink::host_query("hash", bytes)
    }
}

/// Expose `Hoster::hash()` to the host
#[no_mangle]
unsafe fn hash(arg_len: u32) -> u32 {
    uplink::wrap_query(arg_len, |num| STATE.hash(num))
}
