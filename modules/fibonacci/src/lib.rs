// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Module that calculates the nth number of the Fibonacci sequence

#![feature(arbitrary_self_types)]
#![no_std]

/// Struct that describes the state of the fibonacci module
pub struct Fibonacci;

use piecrust_uplink as uplink;
use uplink::State;

#[allow(unused)]
/// State of the fibonacci module
static mut STATE: State<Fibonacci> = State::new(Fibonacci);

impl Fibonacci {
    /// Calculate the nth number in the fibonacci sequence
    fn nth(n: u32) -> u64 {
        match n {
            0 | 1 => 1,
            n => Self::nth(n - 1) + Self::nth(n - 2),
        }
    }
}

/// Expose `Fibonacci::nth()` to the host
#[no_mangle]
unsafe fn nth(arg_len: u32) -> u32 {
    uplink::wrap_query(arg_len, |n: u32| Fibonacci::nth(n))
}
