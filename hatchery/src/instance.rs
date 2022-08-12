// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use colored::*;

use dallo::{
    ModuleId, StandardBufSerializer, MODULE_ID_BYTES, SCRATCH_BUF_BYTES,
};
use rkyv::{
    archived_root,
    ser::serializers::{BufferScratch, BufferSerializer, CompositeSerializer},
    ser::Serializer,
    Archive, Deserialize, Infallible, Serialize,
};
use wasmer::NativeFunc;

use crate::error::*;
use crate::memory::MemHandler;
use crate::snapshot_bag::SnapshotBag;
use crate::world::World;

#[derive(Debug)]
pub struct Instance {
    id: ModuleId,
    instance: wasmer::Instance,
    world: World,
    mem_handler: MemHandler,
    arg_buf_ofs: i32,
    arg_buf_len: u32,
    heap_base: i32,
    self_id_ofs: i32,
    snapshot_bag: SnapshotBag,
}

impl Instance {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        id: ModuleId,
        instance: wasmer::Instance,
        world: World,
        mem_handler: MemHandler,
        arg_buf_ofs: i32,
        arg_buf_len: u32,
        heap_base: i32,
        self_id_ofs: i32,
    ) -> Self {
        Instance {
            id,
            instance,
            world,
            mem_handler,
            arg_buf_ofs,
            arg_buf_len,
            heap_base,
            self_id_ofs,
            snapshot_bag: SnapshotBag::new(),
        }
    }

    pub(crate) fn query<Arg, Ret>(
        &self,
        name: &str,
        arg: Arg,
    ) -> Result<Ret, Error>
    where
        Arg: for<'a> Serialize<StandardBufSerializer<'a>>,
        Ret: Archive,
        Ret::Archived: Deserialize<Ret, Infallible>,
    {
        let ret_len = {
            let arg_len = self.write_to_arg_buffer(arg)?;
            self.perform_query(name, arg_len)?
        };

        self.read_from_arg_buffer(ret_len)
    }

    pub(crate) fn perform_query(
        &self,
        name: &str,
        arg_len: u32,
    ) -> Result<u32, Error> {
        let fun: NativeFunc<u32, u32> =
            self.instance.exports.get_native_function(name)?;
        Ok(fun.call(arg_len)?)
    }

    pub(crate) fn transact<Arg, Ret>(
        &mut self,
        name: &str,
        arg: Arg,
    ) -> Result<Ret, Error>
    where
        Arg: for<'a> Serialize<StandardBufSerializer<'a>> + core::fmt::Debug,
        Ret: Archive,
        Ret::Archived: Deserialize<Ret, Infallible>,
    {
        let ret_len = {
            let arg_ofs = self.write_to_arg_buffer(arg)?;
            self.perform_transaction(name, arg_ofs)?
        };

        self.read_from_arg_buffer(ret_len)
    }

    pub(crate) fn perform_transaction(
        &self,
        name: &str,
        arg_len: u32,
    ) -> Result<u32, Error> {
        let fun: NativeFunc<u32, u32> =
            self.instance.exports.get_native_function(name)?;
        Ok(fun.call(arg_len)?)
    }

    pub(crate) fn with_memory<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        let mem = self
            .instance
            .exports
            .get_memory("memory")
            .expect("memory export is checked at module creation time");
        let memory_bytes = unsafe { mem.data_unchecked() };

        f(memory_bytes)
    }

    pub(crate) fn with_memory_mut<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mem =
            self.instance.exports.get_memory("memory").expect(
                "memory export should be checked at module creation time",
            );
        let memory_bytes = unsafe { mem.data_unchecked_mut() };
        f(memory_bytes)
    }

    pub(crate) fn write_self_id(&self, module_id: ModuleId) {
        let mem =
            self.instance.exports.get_memory("memory").expect(
                "memory export should be checked at module creation time",
            );

        let ofs = self.self_id_ofs as usize;

        let memory = unsafe { mem.data_unchecked_mut() };
        let self_id_buf = &mut memory[ofs..][..MODULE_ID_BYTES];

        self_id_buf.copy_from_slice(module_id.as_bytes());
    }

    pub(crate) fn write_to_arg_buffer<T>(&self, value: T) -> Result<u32, Error>
    where
        T: for<'a> Serialize<StandardBufSerializer<'a>>,
    {
        self.with_arg_buffer(|abuf| {
            let mut sbuf = [0u8; SCRATCH_BUF_BYTES];
            let scratch = BufferScratch::new(&mut sbuf);
            let ser = BufferSerializer::new(abuf);
            let mut ser =
                CompositeSerializer::new(ser, scratch, rkyv::Infallible);

            ser.serialize_value(&value)?;

            Ok(ser.pos() as u32)
        })
    }

    fn read_from_arg_buffer<T>(&self, arg_len: u32) -> Result<T, Error>
    where
        T: Archive,
        T::Archived: Deserialize<T, Infallible>,
    {
        // TODO use bytecheck here
        Ok(self.with_arg_buffer(|abuf| {
            let slice = &abuf[..arg_len as usize];
            let ta: &T::Archived = unsafe { archived_root::<T>(slice) };
            ta.deserialize(&mut Infallible).unwrap()
        }))
    }

    pub(crate) fn with_arg_buffer<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        self.with_memory_mut(|memory_bytes| {
            let a = self.arg_buf_ofs as usize;
            let b = self.arg_buf_len as usize;
            let begin = &mut memory_bytes[a..];
            let trimmed = &mut begin[..b];
            f(trimmed)
        })
    }

    pub(crate) fn alloc(&mut self, amount: usize, align: usize) -> usize {
        self.mem_handler.alloc(amount, align)
    }

    pub(crate) fn dealloc(&mut self, _addr: usize) {}

    pub fn id(&self) -> ModuleId {
        self.id
    }

    pub(crate) fn snapshot_bag(&mut self) -> &SnapshotBag {
        &self.snapshot_bag
    }
    pub(crate) fn snapshot_bag_mut(&mut self) -> &mut SnapshotBag {
        &mut self.snapshot_bag
    }
    pub(crate) fn world(&self) -> &World {
        &self.world
    }

    pub fn snap(&self) {
        let mem = self
            .instance
            .exports
            .get_memory("memory")
            .expect("memory export is checked at module creation time");

        println!("memory snapshot");

        let maybe_interesting = unsafe { mem.data_unchecked_mut() };

        const CSZ: usize = 128;
        const RSZ: usize = 16;

        for (chunk_nr, chunk) in maybe_interesting.chunks(CSZ).enumerate() {
            if chunk[..] != [0; CSZ][..] {
                for (row_nr, row) in chunk.chunks(RSZ).enumerate() {
                    let ofs = chunk_nr * CSZ + row_nr * RSZ;

                    print!("{:08x}:", ofs);

                    for (i, byte) in row.iter().enumerate() {
                        if i % 4 == 0 {
                            print!(" ");
                        }

                        let buf_start = self.arg_buf_ofs as usize;
                        let buf_end = buf_start + self.arg_buf_len as usize;
                        let heap_base = self.heap_base as usize;

                        if ofs + i >= buf_start && ofs + i < buf_end {
                            print!("{}", format!("{:02x}", byte).red());
                            print!(" ");
                        } else if ofs + i >= heap_base {
                            print!("{}", format!("{:02x} ", byte).green());
                        } else {
                            print!("{:02x} ", byte)
                        }
                    }

                    println!();
                }
            }
        }
    }
}
