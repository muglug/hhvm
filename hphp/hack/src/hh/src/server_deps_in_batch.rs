// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_deps_in_batch.ml`. See `hh/PORTING.md`.
//!
//! `Server_find_refs.go` takes the environment and returns it: it is
//! threaded through the searches (the OCaml gives each the same one).

use std::sync::Arc;

use crate::nast;
use crate::provider_context;
use crate::server_command_types::done_or_retry;
use crate::server_command_types::find_refs::ResultOrRetry;
use crate::server_deps_util::Occ;
use crate::server_deps_util::body_symbols;
use crate::server_deps_util::get_def;
use crate::server_deps_util::get_def_setup;
use crate::server_deps_util::is_target;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_find_refs;

fn references(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    genv: &Genv,
    env: Env,
    occ: &Occ,
) -> (Env, ResultOrRetry) {
    let (line, column, _) = crate::pos::info_pos(&occ.pos);
    match server_find_refs::go_from_file_ctx(
        ctx,
        entry,
        &crate::file_content::position::from_one_based(line, column),
    ) {
        None => (env, done_or_retry::T::Done(vec![])),
        Some((_, action)) => done_or_retry::map_env(
            |r| server_find_refs::to_absolute(&r),
            server_find_refs::go(ctx, &action, false, None, &[], genv, env),
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn body_references(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    genv: &Genv,
    env: Env,
    declarations: &[Occ],
    ast: &nast::Program,
    occ: &Occ,
) -> (Env, Vec<ResultOrRetry>) {
    match get_def(ctx, ast, occ) {
        None => (env, vec![done_or_retry::T::Done(vec![])]),
        Some(def) => {
            let mut symbols_to_find: Vec<&Occ> = vec![occ];
            symbols_to_find.extend(body_symbols(ctx, entry, declarations, occ, &def));
            let mut env = env;
            let mut results = vec![];
            for occ in symbols_to_find {
                let (env_, r) = references(ctx, entry, genv, env, occ);
                env = env_;
                results.push(r)
            }
            (env, results)
        }
    }
}

pub fn go(
    ctx: &provider_context::T,
    genv: &Genv,
    env: Env,
    pos_list: &[(String, isize, isize)],
) -> (Env, Vec<ResultOrRetry>) {
    let mut acc_ctx = ctx.clone();
    let mut env = env;
    let mut all = vec![];
    for (file, line, column) in pos_list {
        let (acc_ctx_out, entry, ast) = get_def_setup(&acc_ctx, file);
        // Other files can only depend on things declared in this one
        let declarations: Vec<Occ> = crate::identify_symbol_service::all_symbols_ctx(&acc_ctx_out, &entry)
            .into_iter()
            .filter(|s| s.is_declaration.is_some())
            .collect();
        for occ in declarations.iter().filter(|occ| is_target(*line, *column, occ)) {
            // (`~ctx`: the context of the command, not `acc_ctx_out`.)
            let (env_, deps) = body_references(ctx, &entry, genv, env, &declarations, &ast, occ);
            env = env_;
            all.extend(deps)
        }
        acc_ctx = acc_ctx_out;
    }
    (env, all)
}
