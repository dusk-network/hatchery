// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

extern crate core;

use std::path::{Path, PathBuf};
use std::{env, fs};

use piecrust::{CommitRoot, ContractData, ContractId, SessionData, VM};

const COUNTER_ID: ContractId = {
    let mut bytes = [0u8; 32];
    bytes[0] = 99;
    ContractId::from_bytes(bytes)
};
const OWNER: [u8; 32] = [0u8; 32];

fn initialize_counter<P: AsRef<Path>>(
    vm: &VM,
    commit_id_file_path: P,
) -> Result<(), piecrust::Error> {
    let mut session = vm.session(SessionData::builder())?;

    let counter_bytecode =
        include_bytes!("../../../../target/stripped/counter.wasm");

    session.deploy(
        counter_bytecode,
        ContractData::builder().owner(OWNER).contract_id(COUNTER_ID),
        u64::MAX,
    )?;
    session.call::<_, ()>(COUNTER_ID, "increment", &(), u64::MAX)?;

    let commit_root = session.commit()?;
    fs::write(commit_id_file_path, commit_root.as_bytes())
        .expect("writing commit root should succeed");

    Ok(())
}

fn confirm_counter<P: AsRef<Path>>(
    vm: &VM,
    commit_id_file_path: P,
) -> Result<(), piecrust::Error> {
    let mut commit_root = [0u8; 32];

    let commit_root_bytes = fs::read(commit_id_file_path)
        .expect("Reading commit root should succeed");
    commit_root.copy_from_slice(&commit_root_bytes);
    let root = CommitRoot::from_bytes(commit_root);

    let mut session = vm
        .session(SessionData::builder().base(root))
        .expect("Instantiating session from given root should succeed");

    assert_eq!(
        session
            .call::<_, i64>(COUNTER_ID, "read_value", &(), u64::MAX)?
            .data,
        0xfd
    );

    Ok(())
}

fn initialize<P: AsRef<str>>(vm_data_path: P) -> Result<(), piecrust::Error> {
    let commit_id_file_path =
        PathBuf::from(vm_data_path.as_ref()).join("commit_id");
    let vm = VM::new(vm_data_path.as_ref())?;
    initialize_counter(&vm, commit_id_file_path)
}

fn confirm<P: AsRef<str>>(vm_data_path: P) -> Result<(), piecrust::Error> {
    let commit_id_file_path =
        PathBuf::from(vm_data_path.as_ref()).join("commit_id");
    let vm = VM::new(vm_data_path.as_ref())?;
    confirm_counter(&vm, commit_id_file_path)
}

fn main() -> Result<(), piecrust::Error> {
    const MESSAGE: &str =
        "argument expected: <path_for_vm_data> (initialize|confirm|test_both)";
    let args: Vec<String> = env::args().collect();

    if args.len() < 3 {
        println!("{}", MESSAGE);
        return Ok(());
    }

    let vm_data_path = args[1].clone();

    match &*args[2] {
        "initialize" => initialize(&vm_data_path)?,
        "confirm" => confirm(&vm_data_path)?,
        "test_both" => {
            initialize(&vm_data_path)?;
            for _ in 0..10 {
                confirm(&vm_data_path)?;
            }
        }
        _ => {
            println!("{}", MESSAGE);
        }
    }

    Ok(())
}
