// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use bytecheck::CheckBytes;
use rkyv::{
    ser::serializers::{
        AllocSerializer, BufferScratch, BufferSerializer, CompositeSerializer,
    },
    ser::Serializer,
    Archive, Deserialize, Infallible, Serialize,
};

use crate::SCRATCH_BUF_BYTES;

/// Type with `rkyv` buffer serialization capabilities
pub type StandardBufSerializer<'a> = CompositeSerializer<
    BufferSerializer<&'a mut [u8]>,
    BufferScratch<&'a mut [u8; SCRATCH_BUF_BYTES]>,
>;

/// The length of [`ModuleId`] in bytes
pub const MODULE_ID_BYTES: usize = 32;

/// ID to identify the wasm modules after they have been deployed
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
pub struct ModuleId([u8; MODULE_ID_BYTES]);

impl ModuleId {
    /// Creates a placeholder [`ModuleId`] until the host deploys the module
    /// and sets a real [`ModuleId`]
    pub const fn uninitialized() -> Self {
        ModuleId([0u8; MODULE_ID_BYTES])
    }

    /// Creates a new [`ModuleId`] from an array of bytes
    pub const fn from_bytes(bytes: [u8; MODULE_ID_BYTES]) -> Self {
        Self(bytes)
    }

    /// Returns the array of bytes that make up the [`ModuleId`]
    pub const fn to_bytes(self) -> [u8; MODULE_ID_BYTES] {
        self.0
    }

    /// Returns a reference to the array of bytes that make up the [`ModuleId`]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Returns a mutable reference to the array of bytes that make up the
    /// [`ModuleId`]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }

    /// Determines whether the [`ModuleId`] still is uninitialized
    pub fn is_uninitialized(&self) -> bool {
        self == &Self::uninitialized()
    }
}

impl From<[u8; MODULE_ID_BYTES]> for ModuleId {
    fn from(bytes: [u8; MODULE_ID_BYTES]) -> Self {
        Self::from_bytes(bytes)
    }
}

impl AsRef<[u8]> for ModuleId {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl AsMut<[u8]> for ModuleId {
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
}

impl core::fmt::Debug for ModuleId {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Display::fmt(self, f)
    }
}

impl core::fmt::Display for ModuleId {
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

/// A RawQuery is a host query that doesn't care about types and only operates
/// on raw data.
#[derive(Archive, Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
#[archive_attr(derive(CheckBytes))]
pub struct RawQuery {
    arg_len: u32,
    data: alloc::vec::Vec<u8>,
}

impl RawQuery {
    /// Creates a new [`RawQuery`] by serializing an argument.
    ///
    /// The name of the [`RawQuery`] is stored in its `data` field after the
    /// arguments.
    pub fn new<A>(name: &str, arg: A) -> Self
    where
        A: Serialize<AllocSerializer<64>>,
    {
        let mut ser = AllocSerializer::default();

        ser.serialize_value(&arg)
            .expect("We assume infallible serialization and allocation");

        let data = ser.into_serializer().into_inner().to_vec();
        Self::from_parts(name, data)
    }

    /// Create a new [`RawQuery`] from its parts without serializing data.
    ///
    /// This assumes the `data` given has already been correctly serialized for
    /// the module to call.
    pub fn from_parts(name: &str, data: alloc::vec::Vec<u8>) -> Self {
        let mut data = data;

        let arg_len = data.len() as u32;
        data.extend_from_slice(name.as_bytes());

        Self { arg_len, data }
    }

    /// Return a reference to the name of [`RawQuery`]
    pub fn name(&self) -> &str {
        core::str::from_utf8(self.name_bytes())
            .expect("always created from a valid &str")
    }

    /// Return a reference to the raw name of [`RawQuery`]
    pub fn name_bytes(&self) -> &[u8] {
        &self.data[self.arg_len as usize..]
    }

    /// Return a reference to the raw argument of [`RawQuery`]
    pub fn arg_bytes(&self) -> &[u8] {
        &self.data[..self.arg_len as usize]
    }
}

/// A RawTransaction is a host transaction that doesn't care about types and
/// only operates on raw data.
#[derive(Archive, Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
#[archive_attr(derive(CheckBytes))]
pub struct RawTransaction {
    arg_len: u32,
    // TODO: use AlignedVec
    data: alloc::vec::Vec<u8>,
}

impl RawTransaction {
    /// Creates a new [`RawTransaction`] by serializing an argument.
    ///
    /// The name of the [`RawTransaction`] is stored in its `data` field after
    /// the arguments.
    pub fn new<A>(name: &str, arg: A) -> Self
    where
        A: Serialize<AllocSerializer<64>>,
    {
        let mut ser = AllocSerializer::default();

        ser.serialize_value(&arg)
            .expect("We assume infallible serialization and allocation");

        let data = ser.into_serializer().into_inner().to_vec();
        Self::from_parts(name, data)
    }

    /// Create a new [`RawTransaction`] from its parts without serializing data.
    ///
    /// This assumes the `data` given has already been correctly serialized for
    /// the module to call.
    pub fn from_parts(name: &str, data: alloc::vec::Vec<u8>) -> Self {
        let mut data = data;

        let arg_len = data.len() as u32;
        data.extend_from_slice(name.as_bytes());

        Self { arg_len, data }
    }

    /// Return a reference to the name of [`RawTransaction`]
    pub fn name(&self) -> &str {
        core::str::from_utf8(self.name_bytes())
            .expect("always created from a valid &str")
    }

    /// Return a reference to the raw name of [`RawTransaction`]
    pub fn name_bytes(&self) -> &[u8] {
        &self.data[self.arg_len as usize..]
    }

    /// Return a reference to raw argument of [`RawTransaction`]
    pub fn arg_bytes(&self) -> &[u8] {
        &self.data[..self.arg_len as usize]
    }
}

#[derive(Archive, Serialize, Deserialize)]
#[archive_attr(derive(CheckBytes))]
pub struct RawResult {
    data: alloc::vec::Vec<u8>,
}

/// A RawResult is a result that doesn't care about its type and only
/// operates on raw data.
impl RawResult {
    /// Creates a new [`RawResult`] from raw data as bytes.
    pub fn new(bytes: &[u8]) -> Self {
        RawResult {
            data: alloc::vec::Vec::from(bytes),
        }
    }

    /// Casts the `data` from [`RawResult`] to the desired type by serializing
    /// and returning it
    pub fn cast<D>(&self) -> D
    where
        D: Archive,
        D::Archived: Deserialize<D, Infallible>,
    {
        // add bytecheck here.
        let archived = unsafe { rkyv::archived_root::<D>(&self.data[..]) };
        archived.deserialize(&mut Infallible).expect("Infallible")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn raw_query() {
        let q = RawQuery::new("hello", 42u128);

        assert_eq!(q.name(), "hello");
        assert_eq!(
            q.arg_bytes(),
            [
                0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00
            ]
        );
    }

    #[test]
    fn raw_transaction() {
        let q = RawQuery::new("world", 666u128);

        assert_eq!(q.name(), "world");
        assert_eq!(
            q.arg_bytes(),
            [
                0x9a, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00
            ]
        );
    }
}
