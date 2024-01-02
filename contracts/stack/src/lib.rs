// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

//! Contract that implements a simple nstack.

#![no_std]

use nstack::annotation::Cardinality;
use nstack::NStack;
use ranno::Annotation;

use piecrust_macros::contract;

/// Struct that describes the state of the stack contract
pub struct Stack {
    inner: NStack<i32, Cardinality>,
}

/// State of the stack contract
static mut STATE: Stack = Stack {
    inner: NStack::new(),
};

#[contract]
impl Stack {
    /// Push a new item onto the stack
    pub fn push(&mut self, elem: i32) {
        self.inner.push(elem);
    }

    /// Pop the latest item off the stack
    pub fn pop(&mut self) -> Option<i32> {
        self.inner.pop()
    }

    /// Return the length of the stack
    pub fn len(&self) -> u32 {
        *Cardinality::from_child(&self.inner) as u32
    }
}
