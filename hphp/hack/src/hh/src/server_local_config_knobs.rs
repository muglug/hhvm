// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/server_local_config_knobs.ml`, the OSS stub of the
//! JustKnobs layer of `Server_local_config_load` (JustKnobs are Meta-only).
//! See `hh/PORTING.md`.

use crate::config_file_common;

/// Returns the config it is given.
pub fn apply_justknobs_overrides(
    _silent: bool,
    config: config_file_common::T,
    _from: &str,
) -> config_file_common::T {
    config
}
