// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use piecrust::{
    contract_bytecode, CommitRoot, ContractData, Error, Session, SessionData,
    VM,
};
use piecrust_uplink::ContractId;
use std::thread;

const OWNER: [u8; 32] = [0u8; 32];
const LIMIT: u64 = 1_000_000;

#[test]
fn read_write_session() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    {
        let mut session = vm.session(SessionData::builder())?;
        let id = session.deploy(
            contract_bytecode!("counter"),
            ContractData::builder().owner(OWNER),
            LIMIT,
        )?;

        assert_eq!(
            session.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
            0xfc
        );

        session.call::<_, ()>(id, "increment", &(), LIMIT)?;

        assert_eq!(
            session.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
            0xfd
        );
    }

    // mutable session dropped without committing.
    // old counter value still accessible.

    let mut other_session = vm.session(SessionData::builder())?;
    let id = other_session.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;

    assert_eq!(
        other_session
            .call::<_, i64>(id, "read_value", &(), LIMIT)?
            .data,
        0xfc
    );

    other_session.call::<_, ()>(id, "increment", &(), LIMIT)?;

    let _commit_id = other_session.commit()?;

    // session committed, new value accessible

    let mut session = vm.session(SessionData::builder().base(_commit_id))?;

    assert_eq!(
        session.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xfd
    );
    Ok(())
}

#[test]
fn commit_restore() -> Result<(), Error> {
    let vm = VM::ephemeral()?;
    let mut session_1 = vm.session(SessionData::builder())?;
    let id = session_1.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;
    // commit 1
    assert_eq!(
        session_1.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xfc
    );
    session_1.call::<_, ()>(id, "increment", &(), LIMIT)?;
    let commit_1 = session_1.commit()?;

    // commit 2
    let mut session_2 = vm.session(SessionData::builder().base(commit_1))?;
    assert_eq!(
        session_2.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xfd
    );
    session_2.call::<_, ()>(id, "increment", &(), LIMIT)?;
    session_2.call::<_, ()>(id, "increment", &(), LIMIT)?;
    let commit_2 = session_2.commit()?;
    let mut session_2 = vm.session(SessionData::builder().base(commit_2))?;
    assert_eq!(
        session_2.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xff
    );

    // restore commit 1
    let mut session_3 = vm.session(SessionData::builder().base(commit_1))?;
    assert_eq!(
        session_3.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xfd
    );

    // restore commit 2
    let mut session_4 = vm.session(SessionData::builder().base(commit_2))?;
    assert_eq!(
        session_4.call::<_, i64>(id, "read_value", &(), LIMIT)?.data,
        0xff
    );
    Ok(())
}

#[test]
fn commit_restore_two_contracts_session() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(SessionData::builder())?;
    let id_1 = session.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;
    let id_2 = session.deploy(
        contract_bytecode!("box"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;

    session.call::<_, ()>(id_1, "increment", &(), LIMIT)?;
    session.call::<i16, ()>(id_2, "set", &0x11, LIMIT)?;
    assert_eq!(
        session.call::<_, i64>(id_1, "read_value", &(), LIMIT)?.data,
        0xfd
    );
    assert_eq!(
        session
            .call::<_, Option<i16>>(id_2, "get", &(), LIMIT)?
            .data,
        Some(0x11)
    );

    let commit_1 = session.commit()?;

    let mut session = vm.session(SessionData::builder().base(commit_1))?;
    session.call::<_, ()>(id_1, "increment", &(), LIMIT)?;
    session.call::<i16, ()>(id_2, "set", &0x12, LIMIT)?;
    let commit_2 = session.commit()?;
    let mut session = vm.session(SessionData::builder().base(commit_2))?;
    assert_eq!(
        session.call::<_, i64>(id_1, "read_value", &(), LIMIT)?.data,
        0xfe
    );
    assert_eq!(
        session
            .call::<_, Option<i16>>(id_2, "get", &(), LIMIT)?
            .data,
        Some(0x12)
    );

    let mut session = vm.session(SessionData::builder().base(commit_1))?;

    // check if both contracts' state was restored
    assert_eq!(
        session
            .call::<(), i64>(id_1, "read_value", &(), LIMIT)?
            .data,
        0xfd
    );
    assert_eq!(
        session
            .call::<_, Option<i16>>(id_2, "get", &(), LIMIT)?
            .data,
        Some(0x11)
    );
    Ok(())
}

#[test]
fn multiple_commits() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(SessionData::builder())?;
    let id = session.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;
    // commit 1
    assert_eq!(
        session.call::<(), i64>(id, "read_value", &(), LIMIT)?.data,
        0xfc
    );
    session.call::<(), ()>(id, "increment", &(), LIMIT)?;
    let commit_1 = session.commit()?;

    // commit 2
    let mut session = vm.session(SessionData::builder().base(commit_1))?;
    assert_eq!(
        session.call::<(), i64>(id, "read_value", &(), LIMIT)?.data,
        0xfd
    );
    session.call::<(), ()>(id, "increment", &(), LIMIT)?;
    session.call::<(), ()>(id, "increment", &(), LIMIT)?;
    let commit_2 = session.commit()?;
    let mut session = vm.session(SessionData::builder().base(commit_2))?;
    assert_eq!(
        session.call::<(), i64>(id, "read_value", &(), LIMIT)?.data,
        0xff
    );

    // restore commit 1
    let mut session = vm.session(SessionData::builder().base(commit_1))?;
    assert_eq!(
        session.call::<(), i64>(id, "read_value", &(), LIMIT)?.data,
        0xfd
    );

    // restore commit 2
    let mut session = vm.session(SessionData::builder().base(commit_2))?;
    assert_eq!(
        session.call::<(), i64>(id, "read_value", &(), LIMIT)?.data,
        0xff
    );
    Ok(())
}

#[test]
fn root_equal_on_err() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(SessionData::builder())?;

    let callcenter_id = session.deploy(
        contract_bytecode!("callcenter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;
    let counter_id = session.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;

    let root = session.commit()?;

    let mut session_after = vm.session(SessionData::builder().base(root))?;
    let mut session_after_alt =
        vm.session(SessionData::builder().base(root))?;

    assert_eq!(
        session_after.root(),
        session_after_alt.root(),
        "Roots should be equal at the beginning"
    );

    session_after
        .call::<_, ()>(callcenter_id, "panik", &counter_id, LIMIT)
        .expect_err("Calling with too little gas should error");

    assert_eq!(
        session_after.root(),
        session_after_alt.root(),
        "Roots should be equal immediately after erroring call"
    );

    session_after.call::<_, ()>(
        callcenter_id,
        "increment_counter",
        &counter_id,
        LIMIT,
    )?;
    session_after_alt.call::<_, ()>(
        callcenter_id,
        "increment_counter",
        &counter_id,
        LIMIT,
    )?;

    assert_eq!(
        session_after.root(),
        session_after_alt.root(),
        "Roots should be equal after call"
    );

    Ok(())
}

fn increment_counter_and_commit(
    mut session: Session,
    id: ContractId,
    count: usize,
) -> Result<CommitRoot, Error> {
    for _ in 0..count {
        session.call::<(), ()>(id, "increment", &(), LIMIT)?;
    }
    session.commit()
}

#[test]
fn concurrent_sessions() -> Result<(), Error> {
    let vm = VM::ephemeral()?;

    let mut session = vm.session(SessionData::builder())?;
    let counter = session.deploy(
        contract_bytecode!("counter"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;

    assert_eq!(
        session
            .call::<(), i64>(counter, "read_value", &(), LIMIT)?
            .data,
        0xfc
    );

    let root = session.commit()?;

    let commits = vm.commits();
    assert_eq!(commits.len(), 1, "There should only be one commit");
    assert_eq!(commits[0], root, "The commit should be the received root");

    // spawn different threads incrementing different times and committing
    const THREAD_NUM: usize = 6;
    let mut threads = Vec::with_capacity(THREAD_NUM);
    for n in 0..THREAD_NUM {
        let session = vm.session(SessionData::builder().base(root))?;
        threads.push(thread::spawn(move || {
            increment_counter_and_commit(session, counter, n + 1)
        }));
    }

    let mut roots: Vec<CommitRoot> = threads
        .into_iter()
        .map(|handle| {
            handle.join().unwrap().expect("Committing should succeed")
        })
        .collect();

    let num_commits = roots.len();

    roots.sort();
    roots.dedup();

    assert_eq!(num_commits, roots.len(), "Commits should all be different");

    let commits = vm.commits();
    assert_eq!(
        commits.len(),
        THREAD_NUM + 1,
        "There should be the genesis commit plus the ones just made"
    );

    // start sessions with all the commits and do lots of increments just to
    // waste time
    const INCREMENTS_NUM: usize = 100;
    let mut threads = Vec::with_capacity(roots.len());
    for root in &roots {
        let session = vm.session(SessionData::builder().base(*root))?;
        threads.push(thread::spawn(move || {
            increment_counter_and_commit(session, counter, INCREMENTS_NUM)
        }));
    }

    // Try and delete all the commits while they're working
    for root in roots {
        vm.delete_commit(root)?;
    }

    let mut roots: Vec<CommitRoot> = threads
        .into_iter()
        .map(|handle| {
            handle.join().unwrap().expect("Committing should succeed")
        })
        .collect();

    let num_commits = roots.len();

    roots.sort();
    roots.dedup();

    assert_eq!(num_commits, roots.len(), "Commits should all be different");

    let commits = vm.commits();
    assert_eq!(
        commits.len(),
        THREAD_NUM + 1,
        "The deleted commits should not be returned"
    );

    Ok(())
}

fn make_session(vm: &VM) -> Result<(Session, ContractId), Error> {
    const HEIGHT: u64 = 29_000u64;
    let mut session =
        vm.session(SessionData::builder().insert("height", HEIGHT)?)?;
    let contract_id = session.deploy(
        contract_bytecode!("everest"),
        ContractData::builder().owner(OWNER),
        LIMIT,
    )?;
    Ok((session, contract_id))
}

#[test]
fn session_move() -> Result<(), Error> {
    let vm = VM::ephemeral()?;
    let (mut session, contract_id) = make_session(&vm)?;

    // This tests that a session can be moved without subsequent calls producing
    // a SIGSEGV. The pattern is very common downstream, and should be tested
    // for.
    session.call::<_, u64>(contract_id, "get_height", &(), LIMIT)?;

    Ok(())
}
