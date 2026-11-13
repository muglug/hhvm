// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/deferral_tracker.ml`: whether the states a file watcher
//! defers changes for (Eden's, `Server_notifier.get_deferring_states`)
//! block new clients.
//!
//! Owned by **SRV** (plan §3.1).

use crate::hg_states;
use crate::server_local_config;
use crate::server_notifier;

/// `decision`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Ok,
    DeferredBy(Vec<String>),
}

pub fn should_block_on(local_config: &server_local_config::T, state: &str) -> bool {
    if hg_states::is_hg_state(state) {
        local_config.hg_aware
    } else {
        true
    }
}

pub fn should_accept_client_connection(
    local_config: &server_local_config::T,
    notifier: &server_notifier::T,
) -> Decision {
    if !local_config.block_client_connections_while_deferring {
        Decision::Ok
    } else {
        let asserted_states = server_notifier::get_deferring_states(notifier);
        let blocking_states: Vec<String> = asserted_states
            .into_iter()
            .filter(|s| should_block_on(local_config, s))
            .collect();
        if blocking_states.is_empty() {
            Decision::Ok
        } else {
            Decision::DeferredBy(blocking_states)
        }
    }
}
