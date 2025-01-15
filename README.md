# π-crust

[![Repository](https://img.shields.io/badge/github-piecrust-blueviolet?logo=github)](https://github.com/dusk-network/piecrust)
![Build Status](https://github.com/dusk-network/piecrust/workflows/build/badge.svg)
[![Documentation](https://img.shields.io/badge/docs-piecrust-blue?logo=rust)](https://docs.rs/piecrust/)

`piecrust` is a Rust workspace containing two crates, `piecrust` and `piecrust-uplink`, that together form the WASM virtual machine for running, handling and creating Dusk smart contracts.

## Workspace Members

- [piecrust](piecrust/README.md): WASM virtual machine for running Dusk's smart contracts.
- [piecrust-uplink](piecrust-uplink/README.md): The library that allows you to create smart contracts directly on top of `piecrust`.

## Project Structure

The project is organized as follows:

- `contracts`: Contains a number of example smart contracts that can be run against the `piecrust` virtual machine.
- `piecrust`: Contains the source code and README for the WASM virtual machine.
- `piecrust-uplink`: Contains the source code and README for the smart contract development kit.

## Build and Test

To build and test the crate one will need a
[Rust](https://www.rust-lang.org/tools/install) toolchain, Make, and the
`wasm-tools` binary.

```sh
sudo apt install -y make # ubuntu/debian - adapt to own system
cargo install wasm-tools
make test
```

## Release History

To see the release history for this project, please see the Changelogs of each individual workspace member.

## License

This code is licensed under the Mozilla Public License Version 2.0 (MPL-2.0). Please see the [LICENSE](./LICENSE) for further details.

## Contribute

If you want to contribute to this project, please check the [CONTRIBUTING](https://github.com/dusk-network/.github/blob/main/.github/CONTRIBUTING.md) file.
