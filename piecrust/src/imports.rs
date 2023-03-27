// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use wasmer::{imports, Function, FunctionEnv, FunctionEnvMut};

use crate::Error;
use piecrust_uplink::{ModuleError, ModuleId, ARGBUF_LEN};

use crate::instance::Env;

const POINT_PASS_PCT: u64 = 93;

pub(crate) struct DefaultImports;

impl DefaultImports {
    pub fn default(store: &mut wasmer::Store, env: Env) -> wasmer::Imports {
        let fenv = FunctionEnv::new(store, env);

        imports! {
            "env" => {
                "caller" => Function::new_typed_with_env(store, &fenv, caller),
                "q" => Function::new_typed_with_env(store, &fenv, q),
                "t" => Function::new_typed_with_env(store, &fenv, t),
                "hq" => Function::new_typed_with_env(store, &fenv, hq),
                "hd" => Function::new_typed_with_env(store, &fenv, hd),
                "host_debug" => Function::new_typed_with_env(store, &fenv, host_debug),
                "emit" => Function::new_typed_with_env(store, &fenv, emit),
                "limit" => Function::new_typed_with_env(store, &fenv, limit),
                "spent" => Function::new_typed_with_env(store, &fenv, spent),
                "metadata" => Function::new_typed_with_env(store, &fenv, metadata),
            }
        }
    }
}

fn caller(env: FunctionEnvMut<Env>) {
    let env = env.data();

    let mod_id = env
        .nth_from_top(1)
        .map_or(ModuleId::uninitialized(), |elem| elem.module_id);

    env.self_instance().with_arg_buffer(|arg| {
        arg[..std::mem::size_of::<ModuleId>()]
            .copy_from_slice(mod_id.as_bytes())
    })
}

fn q(
    mut fenv: FunctionEnvMut<Env>,
    mod_id_ofs: i32,
    name_ofs: i32,
    name_len: u32,
    arg_len: u32,
) -> Result<i32, Error> {
    let env = fenv.data_mut();

    let instance = env.self_instance();
    let argbuf_ofs = instance.arg_buffer_offset();

    let caller_remaining = instance
        .get_remaining_points()
        .expect("there should be points remaining");
    let callee_limit = caller_remaining * POINT_PASS_PCT / 100;

    // If an error is returned then we are in a re-execution, and should signal
    // the module without executing the call.
    env.increment_icc_height();
    if let Some(err) = env.increment_icc_count() {
        env.decrement_icc_height();
        env.decrement_icc_count();
        // Consume all gas given to the callee on an error
        instance.set_remaining_points(caller_remaining - callee_limit);
        return Ok(ModuleError::from(err).into());
    }

    let (ret_len, callee_spent) = instance
        .with_memory_mut::<_, Result<_, Error>>(|memory| {
            let name = core::str::from_utf8(
                &memory[name_ofs as usize..][..name_len as usize],
            )
            .expect("TODO error handling");

            let arg_buf = &memory[argbuf_ofs..][..ARGBUF_LEN];

            let mut mod_id = ModuleId::uninitialized();
            mod_id.as_bytes_mut().copy_from_slice(
                &memory[mod_id_ofs as usize..]
                    [..std::mem::size_of::<ModuleId>()],
            );

            let callee_stack_element = env
                .push_callstack(mod_id, callee_limit)
                .expect("pushing to the callstack should succeed");
            let callee = env
                .instance(&callee_stack_element.module_id)
                .expect("callee instance should exist");

            let arg = &arg_buf[..arg_len as usize];

            callee.write_argument(arg);
            let ret_len = callee.query(name, arg.len() as u32, callee_limit)?;

            // copy back result
            callee.read_argument(&mut memory[argbuf_ofs..][..ret_len as usize]);

            let callee_remaining = callee
                .get_remaining_points()
                .expect("there should be points remaining");
            let callee_spent = callee_limit - callee_remaining;

            env.pop_callstack();

            Ok((ret_len, callee_spent))
        })?;

    env.decrement_icc_height();
    instance.set_remaining_points(caller_remaining - callee_spent);

    Ok(ret_len)
}

fn t(
    mut fenv: FunctionEnvMut<Env>,
    mod_id_ofs: i32,
    name_ofs: i32,
    name_len: u32,
    arg_len: u32,
) -> Result<i32, Error> {
    let env = fenv.data_mut();

    let instance = env.self_instance();
    let argbuf_ofs = instance.arg_buffer_offset();

    let caller_remaining = instance
        .get_remaining_points()
        .expect("there should be points remaining");
    let callee_limit = caller_remaining * POINT_PASS_PCT / 100;

    // If an error is returned then we are in a re-execution, and should signal
    // the module without executing the call.
    env.increment_icc_height();
    if let Some(err) = env.increment_icc_count() {
        env.decrement_icc_height();
        env.decrement_icc_count();
        // Consume all gas given to the callee on an error
        instance.set_remaining_points(caller_remaining - callee_limit);
        return Ok(ModuleError::from(err).into());
    }

    let (ret_len, callee_spent) = instance
        .with_memory_mut::<_, Result<_, Error>>(|memory| {
            let name = core::str::from_utf8(
                &memory[name_ofs as usize..][..name_len as usize],
            )
            .expect("TODO error handling");

            let arg_buf = &memory[argbuf_ofs..][..ARGBUF_LEN];

            let mut mod_id = ModuleId::uninitialized();
            mod_id.as_bytes_mut().copy_from_slice(
                &memory[mod_id_ofs as usize..]
                    [..std::mem::size_of::<ModuleId>()],
            );

            let callee_stack_element = env
                .push_callstack(mod_id, callee_limit)
                .expect("pushing to the callstack should succeed");
            let callee = env
                .instance(&callee_stack_element.module_id)
                .expect("callee instance should exist");

            let arg = &arg_buf[..arg_len as usize];

            callee.write_argument(arg);
            let ret_len = callee.query(name, arg.len() as u32, callee_limit)?;

            // copy back result
            callee.read_argument(&mut memory[argbuf_ofs..][..ret_len as usize]);

            let callee_remaining = callee
                .get_remaining_points()
                .expect("there should be points remaining");
            let callee_spent = callee_limit - callee_remaining;

            env.pop_callstack();

            Ok((ret_len, callee_spent))
        })?;

    env.decrement_icc_height();
    instance.set_remaining_points(caller_remaining - callee_spent);

    Ok(ret_len)
}

fn hq(
    mut fenv: FunctionEnvMut<Env>,
    name_ofs: i32,
    name_len: u32,
    arg_len: u32,
) -> u32 {
    let env = fenv.data_mut();

    let instance = env.self_instance();

    let name_ofs = name_ofs as usize;
    let name_len = name_len as usize;

    let name = instance.with_memory(|buf| {
        // performance: use a dedicated buffer here?
        core::str::from_utf8(&buf[name_ofs..][..name_len])
            .expect("TODO, error out cleaner")
            .to_owned()
    });

    instance
        .with_arg_buffer(|buf| env.host_query(&name, buf, arg_len))
        .expect("TODO: error handling")
}

fn hd(mut fenv: FunctionEnvMut<Env>, name_ofs: i32, name_len: u32) -> u32 {
    let env = fenv.data_mut();

    let instance = env.self_instance();

    let name_ofs = name_ofs as usize;
    let name_len = name_len as usize;

    let name = instance.with_memory(|buf| {
        // performance: use a dedicated buffer here?
        core::str::from_utf8(&buf[name_ofs..][..name_len])
            .expect("TODO, error out cleaner")
            .to_owned()
    });

    match env.meta(&name) {
        Some(data) => {
            instance.with_arg_buffer(|buf| {
                buf[..data.len()].copy_from_slice(&data);
            });

            data.len() as u32
        }
        _ => 0u32,
    }
}

fn emit(mut fenv: FunctionEnvMut<Env>, arg_len: u32) {
    let env = fenv.data_mut();
    env.emit(arg_len)
}

fn host_debug(mut fenv: FunctionEnvMut<Env>, msg_ofs: i32, msg_len: u32) {
    let env = fenv.data_mut();

    env.self_instance().with_memory(|mem| {
        let slice = &mem[msg_ofs as usize..][..msg_len as usize];

        let msg = std::str::from_utf8(slice).expect("Invalid debug string");

        env.register_debug(msg);

        println!("MODULE DEBUG {msg}")
    })
}

fn limit(fenv: FunctionEnvMut<Env>) -> u64 {
    fenv.data().limit()
}

fn spent(fenv: FunctionEnvMut<Env>) -> u64 {
    let env = fenv.data();
    let instance = env.self_instance();

    let limit = env.limit();
    let remaining = instance
        .get_remaining_points()
        .expect("there should be remaining points");

    limit - remaining
}

fn metadata(fenv: FunctionEnvMut<Env>) -> u32 {
    let env = fenv.data();
    let self_id = env.self_module_id();
    let slice = env.metadata(self_id).expect("metadata should exist");
    let len = slice.len();
    env.self_instance()
        .with_arg_buffer(|arg| arg[..len].copy_from_slice(slice));
    len as u32
}
