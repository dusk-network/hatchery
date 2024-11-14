// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::store::tree::{ContractIndexElement, Hash, NewContractIndex};
use crate::store::CommitStore;
use piecrust_uplink::ContractId;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub(crate) struct Hulk;

impl Hulk {
    pub fn deep_index_get(
        index: &NewContractIndex,
        contract_id: ContractId,
        commit_store: Option<Arc<Mutex<CommitStore>>>,
        base: Option<Hash>,
    ) -> Option<*const ContractIndexElement> {
        if let Some(e) = index.get(&contract_id) {
            return Some(e);
        }
        let mut base = base?;
        let commit_store = commit_store.clone()?;
        let commit_store = commit_store.lock().unwrap();
        loop {
            let (maybe_element, commit_base) =
                commit_store.get_element_and_base(&base, &contract_id);
            if let Some(e) = maybe_element {
                return Some(e);
            }
            base = commit_base?;
        }
    }

    pub fn deep_index_get_mut(
        index: &mut NewContractIndex,
        contract_id: ContractId,
        commit_store: Option<Arc<Mutex<CommitStore>>>,
        base: Option<Hash>,
    ) -> Option<*mut ContractIndexElement> {
        if let Some(e) = index.get_mut(&contract_id) {
            return Some(e);
        }
        let mut base = base?;
        let commit_store = commit_store.clone()?;
        let mut commit_store = commit_store.lock().unwrap();
        loop {
            let (maybe_element, commit_base) =
                commit_store.get_element_and_base_mut(&base, &contract_id);
            if let Some(e) = maybe_element {
                return Some(e);
            }
            base = commit_base?;
        }
    }
}
