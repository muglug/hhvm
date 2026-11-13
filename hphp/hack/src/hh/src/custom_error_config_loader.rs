// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error_config_loader.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use std::sync::LazyLock;

use crate::custom_error_config;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::relative_path;

pub const config_path_relative_to_repo_root: &str = "CUSTOM_ERRORS.json";

pub static repo_config_path: LazyLock<relative_path::T> =
    LazyLock::new(|| relative_path::from_root(config_path_relative_to_repo_root));

fn log_debug(msg: &str) {
    hh_logger::debug(Some("custom errors"), None, msg)
}

/// `load_and_parse ?(path = repo_config_path) ()`. A malformed config logs
/// and exits with `Config_error`.
pub fn load_and_parse(path: Option<&relative_path::T>) -> custom_error_config::T {
    let path = path.unwrap_or(&repo_config_path);
    match custom_error_config::initialize(custom_error_config::Path::Relative(path.clone())) {
        Ok(cfg) => {
            for rule in &cfg.invalid {
                log_debug(&format!("CustomErrorConfig bad rule: {}", rule.name))
            }
            cfg
        }
        Err(msg) => {
            log_debug(&format!("CustomErrorConfig: {}", msg));
            hh_logger::log_with(
                Some(hh_logger::level::T::Fatal),
                None,
                &format!("Custom errors config malformed: {}", msg),
            );
            exit::exit(None, None, None, exit_status::T::ConfigError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_file_is_empty() {
        let path = relative_path::create(
            relative_path::Prefix::Dummy,
            "/this/directory/does/not/exist/CUSTOM_ERRORS.json",
        );
        assert_eq!(load_and_parse(Some(&path)), custom_error_config::empty);
    }
}
