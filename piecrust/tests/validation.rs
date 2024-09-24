// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use piecrust::{contract_bytecode, ContractData, Error, SessionData, VM};

const OWNER: [u8; 32] = [0u8; 32];
const LIMIT: u64 = 1_000_000;

#[test]
fn out_of_bounds() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(None, SessionData::builder())?;

    let c_example_id = session.deploy(
        None,
        contract_bytecode!("c_example"),
        &(),
        OWNER,
        LIMIT,
    )?;

    session
        .call::<_, ()>(c_example_id, "out_of_bounds", &(), LIMIT)
        .expect_err("An out of bounds access should error");

    Ok(())
}

#[test]
fn bad_contract() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(None, SessionData::builder())?;

    let _ = session
        .deploy(None, contract_bytecode!("invalid"), &(), OWNER, LIMIT)
        .expect_err("Deploying an invalid contract should error");

    Ok(())
}
