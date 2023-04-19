// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Module that provides and example use of the constructor.

#![feature(arbitrary_self_types)]
#![no_std]

use piecrust_uplink as uplink;
use uplink::State;

/// Struct that describes the state of the Constructor module
pub struct Constructor {
    value: u8,
}

impl Constructor {
    pub fn init(&mut self, value: u8) {
        self.value = value;
    }
}

/// State of the Constructor module
static mut STATE: State<Constructor> = State::new(Constructor { value: 0x50 });

impl Constructor {
    /// Read the value of the constructor module state
    pub fn read_value(&self) -> u8 {
        self.value
    }
    /// Increment the value  by 1
    pub fn increment(&mut self) {
        let value = self.value + 1;
        self.value = value;
    }
}

/// Expose `Constructor::read_value()` to the host
#[no_mangle]
unsafe fn read_value(arg_len: u32) -> u32 {
    uplink::wrap_query(arg_len, |_: ()| STATE.read_value())
}

/// Expose `Constructor::increment()` to the host
#[no_mangle]
unsafe fn increment(arg_len: u32) -> u32 {
    uplink::wrap_transaction(arg_len, |_: ()| STATE.increment())
}

/// Expose `Constructor::init()` to the host
#[no_mangle]
unsafe fn init(arg_len: u32) -> u32 {
    uplink::wrap_transaction(arg_len, |arg: u8| STATE.init(arg))
}
