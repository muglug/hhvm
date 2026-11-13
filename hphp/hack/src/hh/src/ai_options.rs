// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/ai_options.ml`, the OSS stub (`--ai` is Meta-only). See
//! `hh/PORTING.md`.

use crate::shared_mem;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct T {
    pub analyses: Vec<String>,
}

/// Ignores its arguments: no analysis.
pub fn prepare(_server: bool, _s: &str) -> T {
    T { analyses: vec![] }
}

/// Returns the config it is given.
pub fn modify_shared_mem(_options: &T, config: &shared_mem::Config) -> shared_mem::Config {
    config.clone()
}
