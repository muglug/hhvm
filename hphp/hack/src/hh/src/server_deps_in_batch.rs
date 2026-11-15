// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_deps_in_batch.ml` (the `DEPS_IN_BATCH`
//! command). See `hh/PORTING.md`.
//!
//! `Server_find_refs.go` takes the server's environment and gives it back
//! (the OCaml drops the environment it returns and goes on with the one it
//! was given; here the environment is moved, so each call gets the one the
//! previous call returned, which is given back to the caller).

use std::sync::Arc;

use crate::provider_context;
use crate::server_command_types::done_or_retry;
use crate::server_command_types::find_refs::ResultOrRetry;
use crate::server_deps_util::Occ;
use crate::server_deps_util::body_symbols;
use crate::server_deps_util::get_def_setup;
use crate::server_deps_util::is_target;
use crate::server_env::Env;
use crate::server_env::Genv;

fn references(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    genv: &Genv,
    env: Env,
    occ: &Occ,
) -> (Env, ResultOrRetry) {
    let (line, column, _) = crate::pos::info_pos(&occ.pos);
    match crate::server_find_refs::go_from_file_ctx(
        ctx,
        entry,
        &crate::file_content::position::from_one_based(line, column),
    ) {
        None => (env, done_or_retry::T::Done(vec![])),
        Some((_, action)) => done_or_retry::map_env(
            |r| crate::server_find_refs::to_absolute(&r),
            crate::server_find_refs::go(ctx, &action, false, None, &[], genv, env),
        ),
    }
}

pub fn go(
    ctx: &provider_context::T,
    genv: &Genv,
    env: Env,
    pos_list: &[(String, isize, isize)],
) -> (Env, Vec<ResultOrRetry>) {
    let mut env = env;
    let mut acc_ctx = ctx.clone();
    let mut res = vec![];
    for (file, line, column) in pos_list {
        let (acc_ctx_out, entry, ast) = get_def_setup(&acc_ctx, file);
        // Other files can only depend on things declared in this one
        let declarations: Vec<Occ> = crate::identify_symbol_service::all_symbols_ctx(&acc_ctx_out, &entry)
            .into_iter()
            .filter(|s| s.is_declaration.is_some())
            .collect();
        for occ in declarations.iter().filter(|o| is_target(*line, *column, o)) {
            // `body_references ~ctx ~entry ~genv ~env ~declarations ~get_def`
            // (`~ctx` is the context given to `go`; `get_def` uses the
            // context of the setup)
            match crate::server_symbol_definition::go(&acc_ctx_out, Some(&ast), occ) {
                None => res.push(done_or_retry::T::Done(vec![])),
                Some(def) => {
                    let mut symbols_to_find = vec![occ];
                    symbols_to_find.extend(body_symbols(ctx, &entry, &declarations, occ, &def));
                    for o in symbols_to_find {
                        let (env_, r) = references(ctx, &entry, genv, env, o);
                        env = env_;
                        res.push(r)
                    }
                }
            }
        }
        acc_ctx = acc_ctx_out;
    }
    (env, res)
}
