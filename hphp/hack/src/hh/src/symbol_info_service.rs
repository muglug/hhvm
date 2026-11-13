// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/symbol_info_service.ml`. See `hh/PORTING.md`.
//!
//! This module dumps all the symbol info(like fun-calls) in input files.
//! (`Multi_worker.call` is not used: the files are handled by `helper`.)

use crate::relative_path::Prefix;
use crate::relative_path::RelativePath;
use crate::server_command_types::symbol_info_service::Result;
use crate::server_env;
use crate::symbol_info_service_utils::format_result;
use crate::symbol_info_service_utils::helper;

/// Entry Point
pub fn go(file_list: &[String], env: &server_env::Env) -> Result {
    let filename_l: Vec<RelativePath> = file_list
        .iter()
        .filter(|f| crate::find_utils::file_filter(f))
        .map(|f| crate::relative_path::create(Prefix::Root, f))
        .collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let raw_result = helper(&ctx, vec![], &filename_l);
    format_result(raw_result)
}
