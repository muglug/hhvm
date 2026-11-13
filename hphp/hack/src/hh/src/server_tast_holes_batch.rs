// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_tast_holes_batch.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: see `server_infer_type_batch`.

use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_command_types::tast_hole::Filter;
use crate::server_env;
use crate::tast_holes_service;

fn helper(
    ctx: &provider_context::T,
    acc: Vec<tast_holes_service::T>,
    path_list: &[RelativePath],
) -> Vec<tast_holes_service::T> {
    let (ctx, tasts) = crate::server_infer_type_batch::get_tast_map(ctx, path_list);
    let mut holes: Vec<tast_holes_service::T> = vec![];
    for path in path_list {
        // `Relative_path.Map.find tasts path`
        let tast = match tasts.get(path) {
            Some(tast) => tast,
            None => panic!("Not_found"),
        };
        holes.extend(crate::server_collect_tast_holes::tast_holes(
            &ctx,
            &tast.under_normal_assumptions,
            Filter::Typing,
        ))
    }
    holes.extend(acc);
    holes
}

pub fn go(file_list: Vec<String>, env: &server_env::Env) -> tast_holes_service::Result {
    let mut file_list = file_list;
    file_list.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    file_list.dedup();
    let file_list: Vec<RelativePath> = file_list.iter().map(|f| relative_path::create_detect_prefix(f)).collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    helper(&ctx, vec![], &file_list)
}
