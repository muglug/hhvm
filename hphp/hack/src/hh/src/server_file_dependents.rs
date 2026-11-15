// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_file_dependents.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` over the files: the
//! union of the dependency sets does not depend on the buckets, so they
//! are folded on this thread.
//!
//! OCaml fact (oracle, matched): the job runs in the daemon's WORKER
//! processes, forked before the init's typecheck, whose copy of the
//! dependency graph (`DEP_GRAPH`, a Rust static of the FFI) has no in-memory
//! delta: the edges the daemon discovered are invisible there. With
//! `InMemoryMode None` (no saved state: Slack's case) the graph a worker
//! sees is empty, so the answer is the files that define the input files'
//! symbols, i.e. the input files: that is what is computed here (no graph
//! query). With a base graph (`InMemoryMode (Some _)`, `SaveToDiskMode`) a
//! worker sees the base graph and not the delta; the port has no
//! base-only query, so it queries the whole graph (deviation, saved states
//! only).

use crate::naming_table;
use crate::provider_context;
use crate::provider_utils;
use crate::relative_path;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::typing_deps;

/// Given the naming table, a list of relative paths,
///   find the list of relative paths of all dependencies
fn deps_of_paths(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    relative_paths: &[relative_path::T],
) -> Vec<relative_path::T> {
    let deps_mode = provider_context::get_deps_mode(ctx);
    let fileinfos: Vec<_> = relative_paths
        .iter()
        .filter_map(|p| naming_table::get_file_info(naming_table, p))
        .collect();
    let mut initial_deps = typing_deps::dep_set::make();
    for fileinfo in &fileinfos {
        let deps = typing_deps::deps_of_file_info(fileinfo)
            .into_iter()
            .fold(typing_deps::dep_set::make(), |s, d| typing_deps::dep_set::add(&s, d));
        initial_deps = typing_deps::dep_set::union(&initial_deps, &deps);
    }
    let all_deps = match &deps_mode {
        crate::typing_deps_mode::T::InMemoryMode(None) => initial_deps,
        _ => typing_deps::add_all_deps(&deps_mode, &initial_deps),
    };
    crate::naming_provider::get_files(ctx, &all_deps).into_iter().collect()
}

pub fn go(_genv: &Genv, env: &Env, filenames: &[String]) -> Vec<String> {
    let ctx = provider_utils::ctx_from_server_env(env);
    let naming_table = &env.naming_table;
    let paths: Vec<relative_path::T> = filenames.iter().map(|f| relative_path::create_detect_prefix(f)).collect();
    let all_deps = deps_of_paths(&ctx, naming_table, &paths);
    all_deps.iter().map(relative_path::to_absolute).collect()
}
