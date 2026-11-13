// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/server_local_config_qe.ml`, the OSS stub of the QE layer
//! that `hh_client` gives `Server_config.load_with_dynamic_overrides` (QE is
//! Meta-only). See `hh/PORTING.md`.

use crate::config_file_common;

/// Does nothing.
pub fn prepare_client_startup() {}

#[derive(Clone, Debug, PartialEq)]
pub struct Fetch {
    pub start_time: f64,
    pub end_time: f64,
}

/// Returns the config it is given, and no fetch.
pub fn apply_qe_overrides(
    _silent: bool,
    config: config_file_common::T,
) -> (config_file_common::T, Vec<Fetch>) {
    (config, vec![])
}
