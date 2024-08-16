# π-crust Uplink

[![Repository](https://img.shields.io/badge/github-piecrust%20uplink-blueviolet?logo=github)](https://github.com/dusk-network/piecrust/tree/main/piecrust-uplink)
![Build Status](https://github.com/dusk-network/piecrust/workflows/build/badge.svg)
[![Documentation](https://img.shields.io/badge/docs-piecrust%20uplink-blue?logo=rust)](https://docs.rs/piecrust-uplink/)

Piecrust Uplink is the library that allows you to build smart contracts directly on top of Dusk's Piecrust virtual machine. 

## Usage

The library allows users of the contract platform to manage the interface and state with the host environment of the contracts. The example below describes a barebones contract. For more detailed examples, see the [contracts](https://github.com/dusk-network/piecrust/tree/main/contracts) folder.

Add `piecrust_uplink` as a dependency to your contract project:
```sh
cargo add piecrust_uplink
```

To make use of `uplink`, import the dependency in your project and mark it as `no_std`:
```rust
#![no_std]

use piecrust_uplink as uplink;
```

To attach state to a contract:
```rust
/// Struct that describe the state for your contract
pub struct Counter {
    value: i64,
};

/// State of the contract
static mut STATE: Counter = Counter { value: 0x1 };
```

To define logic for your contract, define an implementation:
```rust
impl Counter {
    pub fn read_value(&self) -> i64 {
        self.value
    }

    pub fn increment(&mut self) {
        let value = self.value + 1;
    }
}
```

Read and write operations need to be exposed to the host. Add the following below the implementation:
```rust
unsafe fn read_value(arg_len: u32) -> u32 {
    uplink::wrap_call(arg_len, |_: ()| STATE.read_value())
}

#[no_mangle]
unsafe fn increment(arg_len: u32) -> u32 {
    uplink::wrap_call(arg_len, |panic: bool| STATE.increment(panic))
}
```

## Release History

To see the release history for this crate, please see the [CHANGELOG](./CHANGELOG.md) file.

## License

This code is licensed under the Mozilla Public License Version 2.0 (MPL-2.0). Please see the [LICENSE](./LICENSE) for further details.

## Contribute

If you want to contribute to this project, please check the [CONTRIBUTING](https://github.com/dusk-network/.github/blob/main/.github/CONTRIBUTING.md) file.
