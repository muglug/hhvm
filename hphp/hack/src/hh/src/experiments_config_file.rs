// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/experiments_config_file.ml`, the OSS stub (the updater of
//! the experiments config is Meta-only). See `hh/PORTING.md`.

/// Updates nothing.
pub fn update(silent: bool, file: &str, source: Option<&str>, ttl: f64) -> Result<String, String> {
    let _ = (silent, file, source, ttl);
    Ok("Experiments config update: nothing to do".to_string())
}
