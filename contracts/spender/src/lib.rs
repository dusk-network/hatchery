// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Contract for testing the gas spending behavior.

#![no_std]

use piecrust_uplink as uplink;

/// Struct that describes the state of the spender contract
pub struct Spender;

/// State of the spender contract
static mut STATE: Spender = Spender;

impl Spender {
    /// Get the limit and spent gas before and after an inter-contract call,
    /// including the limit and spent by the called contract
    pub fn get_limit_and_spent(&self) -> (u64, u64, u64, u64, u64) {
        let self_id = uplink::self_id();

        let limit = uplink::limit();
        let spent_before = uplink::spent();

        match uplink::caller().is_none() {
            // if this contract has not been called by another contract,
            // i.e. has been called directly from the outside, call the function
            // via the host and return the limit and spent values before and
            // after the call
            true => {
                let (called_limit, called_spent, _, _, _): (
                    u64,
                    u64,
                    u64,
                    u64,
                    u64,
                ) = uplink::call(self_id, "get_limit_and_spent", &())
                    .expect("Self query should succeed");

                let spent_after = uplink::spent();
                (limit, spent_before, spent_after, called_limit, called_spent)
            }
            // if the contract has been called by another contract (we do that
            // in the above match arm) only return the limit and
            // spent at this point
            false => (limit, spent_before, 0, 0, 0),
        }
    }

    /// Spend all gas that is given to the contract.
    pub fn spend(&self) {
        panic!("I like spending");
    }
}

/// Expose `Spender::get_limit_and_spent()` to the host
#[no_mangle]
unsafe fn get_limit_and_spent(a: u32) -> u32 {
    uplink::wrap_call(a, |_: ()| STATE.get_limit_and_spent())
}

/// Expose `Spender::spend()` to the host
#[no_mangle]
unsafe fn spend(a: u32) -> u32 {
    uplink::wrap_call(a, |_: ()| STATE.spend())
}
