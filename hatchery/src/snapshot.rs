use bsdiff::diff::diff;
use bsdiff::patch::patch;
use dallo::SnapshotId;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::mem;
use std::path::{Path, PathBuf};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::error::Error;
use crate::storage_helpers::{
    combine_module_snapshot_names, snapshot_id_to_name,
};
use crate::Error::PersistenceError;

const COMPRESSION_LEVEL: i32 = 11;

pub trait SnapshotLike {
    fn path(&self) -> &PathBuf;
    /// Load snapshot as buffer
    fn load(&self) -> Result<Vec<u8>, Error> {
        let mut f = std::fs::File::open(self.path().as_path())
            .map_err(PersistenceError)?;
        let metadata =
            std::fs::metadata(self.path().as_path()).map_err(PersistenceError)?;
        let mut buffer = vec![0; metadata.len() as usize];
        f.read(buffer.as_mut_slice()).map_err(PersistenceError)?;
        Ok(buffer)
    }
    /// Load snapshot as size and buffer
    fn load_with_size(&self) -> Result<(usize, usize, Vec<u8>), Error> {
        let mut f = std::fs::File::open(self.path().as_path())
            .map_err(PersistenceError)?;
        let metadata =
            std::fs::metadata(self.path().as_path()).map_err(PersistenceError)?;
        let mut buffer = vec![0; metadata.len() as usize - (mem::size_of::<u32>() as usize) * 2];
        let size = f.read_u32::<LittleEndian>().map_err(PersistenceError)?;
        let original_len = f.read_u32::<LittleEndian>().map_err(PersistenceError)?;
        f.read(buffer.as_mut_slice()).map_err(PersistenceError)?;
        Ok((size as usize, original_len as usize, buffer))
    }
}

pub struct MemoryEdge {
    path: PathBuf,
}

impl MemoryEdge {
    pub fn new(path: impl AsRef<Path>) -> Self {
        MemoryEdge {
            path: path.as_ref().to_path_buf(),
        }
    }
}

impl SnapshotLike for MemoryEdge {
    fn path(&self) -> &PathBuf {
        &self.path
    }
}

pub struct Snapshot {
    path: PathBuf,
}

impl Snapshot {
    pub fn new(snapshot_id: SnapshotId, memory_edge: &MemoryEdge) -> Self {
        let mut path = memory_edge.path().to_owned();
        path.set_file_name(combine_module_snapshot_names(
            path.file_name()
                .expect("filename exists")
                .to_str()
                .expect("filename is UTF8"),
            snapshot_id_to_name(snapshot_id),
        ));
        Snapshot { path }
    }

    pub fn from_edge(memory_edge: &MemoryEdge) -> Self {
        Snapshot {
            path: memory_edge.path().to_path_buf(),
        }
    }

    /// Create uncompressed snapshot
    pub fn write(&self, memory_edge: &MemoryEdge) -> Result<(), Error> {
        std::fs::copy(memory_edge.path(), self.path().as_path())
            .map_err(PersistenceError)?;
        Ok(())
    }

    /// Create compressed snapshot
    pub fn write_compressed(
        &self,
        diff1: &MemoryEdge,
        diff2: &Snapshot,
    ) -> Result<(), Error> {
        let mut compressor = zstd::block::Compressor::new();
        let mut delta: Vec<u8> = Vec::new();
        let diff1_buffer = diff1.load()?;
        let diff2_buffer = diff2.load()?;
        diff(diff2_buffer.as_slice(), diff1_buffer.as_slice(), &mut delta)
            .unwrap();
        println!("delta1={} original_len1={} original_len2={}", delta.len(), diff2_buffer.as_slice().len(), diff1_buffer.as_slice().len());
        let compressed_delta = compressor.compress(&delta, COMPRESSION_LEVEL).unwrap();
        println!("delta2={} compressed delta={}", delta.len(), compressed_delta.len());
        self.save_with_size(compressed_delta, delta.len(), diff2_buffer.as_slice().len())?;
        // self.save(compressed_delta)?;
        Ok(())
    }

    /// Save buffer into current snapshot
    pub fn save(&self, buf: Vec<u8>) -> Result<(), Error> {
        let file_path_exists = self.path().exists();
        let mut file = OpenOptions::new()
            .write(true)
            .create(!file_path_exists)
            .open(self.path())
            .map_err(PersistenceError)?;
        file.write_all(buf.as_slice()).map_err(PersistenceError)?;
        Ok(())
    }

    /// Save buffer and size into current snapshot
    pub fn save_with_size(&self, buf: Vec<u8>, size: usize, original_len: usize) -> Result<(), Error> {
        let file_path_exists = self.path().exists();
        let mut file = OpenOptions::new()
            .write(true)
            .create(!file_path_exists)
            .open(self.path())
            .map_err(PersistenceError)?;
        println!("saving to {:?}", self.path());
        println!("writesz={}", size);
        file.write_u32::<LittleEndian>(size as u32).map_err(PersistenceError)?;
        file.write_u32::<LittleEndian>(original_len as u32).map_err(PersistenceError)?;
        println!("write compressed buffer={}", buf.as_slice().len());
        file.write_all(buf.as_slice()).map_err(PersistenceError)?;
        Ok(())
    }

    /// Decompress current snapshot into the given snapshot
    pub fn decompress(
        &self,
        old_snapshot: &Snapshot,
        to_snapshot: &Snapshot,
    ) -> Result<(), Error> {
        let (original_size, old_size, compressed) = self.load_with_size()?;
        println!("about to decompress!!!! original size={} compressed_size={}", original_size, compressed.len());
        let old = old_snapshot.load()?;
        let mut decompressor = zstd::block::Decompressor::new();
        let mut patch_data = std::io::Cursor::new(
            decompressor
                .decompress(compressed.as_slice(), original_size)
                .map_err(PersistenceError)?,
        );
        println!("old len={} original_size={}", old.len(), original_size);
        let mut patched = vec![0; old_size];
        patch(old.as_slice(), &mut patch_data, patched.as_mut_slice())
            .map_err(PersistenceError)?;
        to_snapshot.save(patched)?;
        Ok(())
    }
}

impl SnapshotLike for Snapshot {
    fn path(&self) -> &PathBuf {
        &self.path
    }
}
