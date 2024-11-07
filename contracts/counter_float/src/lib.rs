// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Contract to implement a simple counter that can be read and incremented by
//! one count.

#![no_std]

use piecrust_uplink as uplink;

/// Struct that describes the state of the Counter contract
pub struct Counter {
    value: f64,
}

/// State of the Counter contract
static mut STATE: Counter = Counter { value: 0xfc as f64 };

impl Counter {
    /// Read the value of the counter
    pub fn read_value(&self) -> f64 {
        self.value
    }

    /// Increment the value of the counter by 1
    pub fn increment(&mut self) {
        let value = self.value + 1.0;
        self.value = value;
    }
}

/// Expose `Counter::read_value()` to the host
#[no_mangle]
unsafe fn read_value(arg_len: u32) -> u32 {
    uplink::wrap_call_unchecked(arg_len, |_: ()| STATE.read_value())
}

/// Expose `Counter::increment()` to the host
#[no_mangle]
unsafe fn increment(arg_len: u32) -> u32 {
    uplink::wrap_call_unchecked(arg_len, |_: ()| STATE.increment())
}
