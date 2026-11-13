// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_file_dependents.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: the dependencies of the paths are found
//! in one job.

use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env;
use crate::typing_deps;
use crate::typing_deps::dep_set;

fn deps_of_paths(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    relative_paths: &[RelativePath],
) -> Vec<RelativePath> {
    let deps_mode = provider_context::get_deps_mode(ctx);
    let find_dependencies = |acc: dep_set::T, paths: &[RelativePath]| -> dep_set::T {
        let fileinfos = paths.iter().filter_map(|path| naming_table::get_file_info(naming_table, path));
        let initial_deps = fileinfos.fold(dep_set::make(), |acc, fileinfo| {
            let deps = dep_set::of_list(&typing_deps::deps_of_file_info(&fileinfo));
            dep_set::union(&acc, &deps)
        });
        dep_set::union(&acc, &typing_deps::add_all_deps(&deps_mode, &initial_deps))
    };
    let all_deps = find_dependencies(dep_set::make(), relative_paths);
    crate::naming_provider::get_files(ctx, &all_deps).into_iter().collect()
}

pub fn go(_genv: &server_env::Genv, env: &server_env::Env, filenames: &[String]) -> Vec<String> {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let naming_table = &env.naming_table;
    let paths: Vec<RelativePath> = filenames.iter().map(|f| relative_path::create_detect_prefix(f)).collect();
    let all_deps = deps_of_paths(&ctx, naming_table, &paths);
    all_deps.iter().map(relative_path::to_absolute).collect()
}
