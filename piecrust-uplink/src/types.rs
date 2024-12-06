// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use alloc::string::String;
use alloc::vec::Vec;

use bytecheck::CheckBytes;
use rkyv::{
    ser::serializers::{BufferScratch, BufferSerializer, CompositeSerializer},
    Archive, Deserialize, Serialize,
};

use crate::SCRATCH_BUF_BYTES;

/// And event emitted by a contract.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Archive,
    Serialize,
    Deserialize,
)]
#[archive_attr(derive(CheckBytes))]
pub struct Event {
    pub source: ContractId,
    pub topic: String,
    pub data: Vec<u8>,
}

/// Type with `rkyv` serialization capabilities for specific types.
pub type StandardBufSerializer<'a> = CompositeSerializer<
    BufferSerializer<&'a mut [u8]>,
    BufferScratch<&'a mut [u8; SCRATCH_BUF_BYTES]>,
>;

/// The length of [`ContractId`] in bytes
pub const CONTRACT_ID_BYTES: usize = 32;

/// ID to identify the wasm contracts after they have been deployed
#[derive(
    PartialEq,
    Eq,
    Archive,
    Serialize,
    CheckBytes,
    Deserialize,
    PartialOrd,
    Ord,
    Hash,
    Clone,
    Copy,
)]
#[archive(as = "Self")]
#[repr(C)]
pub struct ContractId([u8; CONTRACT_ID_BYTES]);

impl ContractId {
    /// Creates a new [`ContractId`] from an array of bytes
    pub const fn from_bytes(bytes: [u8; CONTRACT_ID_BYTES]) -> Self {
        Self(bytes)
    }

    /// Returns the array of bytes that make up the [`ContractId`]
    pub const fn to_bytes(self) -> [u8; CONTRACT_ID_BYTES] {
        self.0
    }

    /// Returns a reference to the array of bytes that make up the
    /// [`ContractId`]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns a mutable reference to the array of bytes that make up the
    /// [`ContractId`]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl From<[u8; CONTRACT_ID_BYTES]> for ContractId {
    fn from(bytes: [u8; CONTRACT_ID_BYTES]) -> Self {
        Self::from_bytes(bytes)
    }
}

impl AsRef<[u8]> for ContractId {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsMut<[u8]> for ContractId {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl PartialEq<[u8; CONTRACT_ID_BYTES]> for ContractId {
    fn eq(&self, other: &[u8; CONTRACT_ID_BYTES]) -> bool {
        self.0.eq(other)
    }
}

impl core::fmt::Debug for ContractId {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

impl core::fmt::Display for ContractId {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if f.alternate() {
            write!(f, "0x")?
        }
        for byte in self.0 {
            write!(f, "{:02x}", &byte)?
        }
        Ok(())
    }
}

#[derive(
    Debug,
    Copy,
    Clone,
    Archive,
    Deserialize,
    Serialize,
    PartialOrd,
    Ord,
    PartialEq,
    Eq,
)]
#[archive_attr(derive(CheckBytes))]
pub struct CommitRoot([u8; 32]);

impl CommitRoot {
    pub fn from_bytes(a: [u8; 32]) -> Self {
        Self(a)
    }
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}
