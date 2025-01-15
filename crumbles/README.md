# Crumbles

[![Repository](https://img.shields.io/badge/github-crumbles-blueviolet?logo=github)](https://github.com/dusk-network/piecrust/tree/main/crumbles)
![Build Status](https://github.com/dusk-network/piecrust/workflows/build/badge.svg)
[![Documentation](https://img.shields.io/badge/docs-crumbles-blue?logo=rust)](https://docs.rs/crumbles)

Crumbles is a Rust library designed for creating and managing copy-on-write memory-mapped regions. This allows for efficient memory handling by tracking changes at page level. It's particularly suitable for scenarios where memory snapshots and reverting to previous states are required.

## Usage

The core functionality of Crumbles is provided by the `Mmap` struct. This struct offers methods to manage memory regions, create snapshots and revert/apply changes.

Add `crumbles` as a dependency to your contract project:
```sh
cargo add crumbles
```

To make use of `crumbles`, import the dependency in your project. Example:
```rust
use crumbles::Mmap;
use std::io;

fn main() -> io::Result<()> {
    let mut mmap = Mmap::new(65536, 65536)?;

    // When first created, the mmap is not dirty.
    assert_eq!(mmap.dirty_pages().count(), 0);

    mmap[24] = 42;

    // After writing a single byte, the page it's on is dirty.
    assert_eq!(mmap.dirty_pages().count(), 1);

    Ok(())
}

```

## Build and Test

To build and test the crate you will need a
[Rust](https://www.rust-lang.org/tools/install) toolchain. Use the following commands to run the tests:

```sh
cargo test
```

## Release History

To see the release history for this crate, please see the [CHANGELOG](./CHANGELOG.md) file.

## License

This code is licensed under the Mozilla Public License Version 2.0 (MPL-2.0). Please see the [LICENSE](./LICENSE) for further details.

## Contribute

If you want to contribute to this project, please check the [CONTRIBUTING](https://github.com/dusk-network/.github/blob/main/.github/CONTRIBUTING.md) file.
