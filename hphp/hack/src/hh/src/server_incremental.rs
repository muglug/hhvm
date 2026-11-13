// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_incremental.ml`.
//!
//! Owned by **S1** (plan §3.1).

use std::sync::Arc;

use crate::ctx::Ctx;
use crate::decl_compare::versioned_names;
use crate::diagnostics_state;
use crate::fanout;
use crate::file_info;
use crate::hh_logger;
use crate::naming_global;
use crate::naming_provider;
use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::server_env::Env;
use crate::server_progress;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::user_diagnostic;

type RPSet = crate::relative_path::set::T;
type RPMap<A> = crate::relative_path::map::T<A>;
type Diag = crate::diagnostics_state::T;

/// Removes the names that were defined in the files from the reverse naming table
pub fn remove_defs_from_reverse_naming_table(
    ctx: &Ctx,
    nt: &naming_table::T,
    defs_per_file_parsed: &RPMap<file_info::T>,
) {
    for fn_ in defs_per_file_parsed.keys() {
        match naming_table::get_file_info(nt, fn_) {
            None => {}
            Some(file_info::T { ids, .. }) => {
                let file_info::Ids {
                    funs,
                    classes,
                    typedefs,
                    consts,
                    modules,
                } = ids;
                // we use [snd] to strip away positions
                let snd = |ids: &[file_info::Id]| -> Vec<String> {
                    ids.iter().map(|id| id.name.clone()).collect()
                };
                naming_global::remove_decls(
                    ctx,
                    &snd(&funs),
                    &snd(&classes),
                    &snd(&typedefs),
                    &snd(&consts),
                    &snd(&modules),
                )
            }
        }
    }
}

/// `get_old_and_new_defs_in_files old_naming_table new_naming_table files`
pub fn get_old_and_new_defs_in_files(
    old_naming_table: &naming_table::T,
    new_naming_table: &naming_table::T,
    files: &RPSet,
) -> RPMap<versioned_names::T> {
    let mut acc = RPMap::new();
    for path in files {
        let old_names =
            naming_table::get_file_info(old_naming_table, path).map(|i| file_info::simplify(&i));
        let new_names =
            naming_table::get_file_info(new_naming_table, path).map(|i| file_info::simplify(&i));
        match (old_names, new_names) {
            (None, None) => {}
            (old_names, new_names) => {
                acc.insert(
                    path.clone(),
                    versioned_names::T {
                        old_names: old_names.unwrap_or_else(file_info::empty_names),
                        new_names: new_names.unwrap_or_else(file_info::empty_names),
                    },
                );
            }
        }
    }
    acc
}

/// If the only things that would change about file analysis are positions,
/// we're not going to recheck it, and positions in its error list might
/// become stale. Look if any of those positions refer to files that have
/// actually changed and add them to files to recheck.
///
/// `reparsed`: Set of files that were reparsed (so their ASTs and positions
/// in them could have changed.
///
/// `diagnostics`: Current global diagnostic list
fn add_files_with_stale_errors(
    ctx: &Arc<Ctx>,
    reparsed: &RPSet,
    diagnostics: &Diag,
    files_acc: RPSet,
) -> RPSet {
    diagnostics_state::fold_errors(None, diagnostics, files_acc, |source, error, mut acc| {
        if user_diagnostic::to_list_(error).iter().any(|e| {
            reparsed.contains(naming_provider::resolve_position(ctx, &e.0).filename())
        }) {
            acc.insert(source.clone());
            acc
        } else {
            acc
        }
    })
}

/// `resolve_files ctx ~reparsed env fanout`
fn resolve_files(ctx: &Arc<Ctx>, reparsed: &RPSet, env: &Env, fanout: &fanout::T) -> RPSet {
    server_progress::with_message(None, None, "resolving files", || {
        let fanout::T {
            changed: _,
            to_recheck,
            to_recheck_if_errors,
        } = fanout;
        let deps_mode = provider_context::get_deps_mode(ctx);
        let dependent_on_files = reparsed.iter().fold(dep_set::make(), |depset, file| {
            let file_dep = dep::Variant::File(file.clone());
            let file_dependents = typing_deps::get_ideps(&deps_mode, &file_dep);
            dep_set::union(&depset, &file_dependents)
        });
        let to_recheck = dep_set::union(&dependent_on_files, to_recheck);
        let files_to_recheck = naming_provider::get_files(ctx, &to_recheck);
        let files_with_errors_to_recheck = {
            let files_with_errors: RPSet = diagnostics_state::get_failed_files(&env.diagnostics)
                .into_iter()
                .collect();
            let files_to_recheck_if_errors = naming_provider::get_files(ctx, to_recheck_if_errors);
            files_with_errors.intersection(files_to_recheck_if_errors)
        };
        let files = files_to_recheck.union(files_with_errors_to_recheck);
        hh_logger::log(&format!(
            "{}:\n{}",
            if files.len() <= 10 {
                "Files to recheck"
            } else {
                "First 10 files to recheck"
            },
            files
                .iter()
                .take(10)
                .map(relative_path::suffix)
                .collect::<Vec<_>>()
                .join("\n")
        ));
        files
    })
}

/// `get_files_to_recheck ctx env fanout ~reparsed ~diagnostics`
pub fn get_files_to_recheck(
    ctx: &Arc<Ctx>,
    env: &Env,
    fanout: &fanout::T,
    reparsed: &RPSet,
    diagnostics: &Diag,
) -> RPSet {
    let files = resolve_files(ctx, reparsed, env, fanout);
    // We want to also recheck files that have typing errors referring to files that were
    // reparsed, since positions in those errors can be now stale.
    add_files_with_stale_errors(ctx, reparsed, diagnostics, files)
}
