// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_status_single.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call_with_worker_id` is not used: the files are checked by
//! `go_sequential`, whatever their number.

use crate::diagnostics_state;
use crate::filter_diagnostics;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_command_types::FileInput;
use crate::server_command_types::Tasts;
use crate::server_env;
use crate::tast_provider;

fn file_inputs_to_cacheable_paths(file_inputs: &[FileInput]) -> Option<Vec<RelativePath>> {
    let mut acc = vec![];
    for file_input in file_inputs {
        match file_input {
            FileInput::FileName(file_name) => {
                let path = relative_path::create_detect_prefix(file_name);
                if crate::find_utils::path_filter(&path) {
                    acc.push(path)
                } else {
                    return None;
                }
            }
            FileInput::FileContent(_) => return None,
        }
    }
    Some(acc)
}

fn diagnostics_for_paths(diagnostics: &diagnostics_state::T, paths: &[RelativePath]) -> diagnostics_state::T {
    let list: Vec<_> = paths
        .iter()
        .flat_map(|path| {
            let diagnostics = diagnostics_state::get_file_diagnostics(Some(false), diagnostics, path);
            // `(path, diagnostic) :: acc`: the last diagnostic first.
            let mut acc = diagnostics_state::fold_per_file_diagnostics(&diagnostics, vec![], |mut acc, diagnostic| {
                acc.push((path.clone(), diagnostic.clone()));
                acc
            });
            acc.reverse();
            acc
        })
        .collect();
    diagnostics_state::from_file_diagnostic_list(list)
}

pub fn go_from_cached_diagnostics(
    env: &server_env::Env,
    file_inputs: &[FileInput],
    return_expanded_tast: bool,
    preexisting_warnings: bool,
    is_stale: bool,
    uses_partial_typecheck: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> Option<(diagnostics_state::T, Tasts)> {
    if return_expanded_tast
        || preexisting_warnings
        || is_stale
        || !server_env::are_diagnostics_complete(env, uses_partial_typecheck)
    {
        None
    } else {
        let paths = file_inputs_to_cacheable_paths(file_inputs)?;
        crate::hh_logger::debug(None, None, "ServerStatusSingle: using cached diagnostics");
        let tast_provider::ErrorFilter {
            error_filter,
            warnings_saved_state,
        } = error_filter;
        let diagnostics = diagnostics_for_paths(&env.diagnostics, &paths);
        let diagnostics = diagnostics_state::filter_out_mergebase_warnings(warnings_saved_state.as_ref(), diagnostics);
        let diagnostics = filter_diagnostics::filter_rel(error_filter, diagnostics);
        Some((diagnostics, Tasts::new()))
    }
}

fn process_file_input(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    file_input: &FileInput,
) -> (diagnostics_state::T, Tasts) {
    match file_input {
        FileInput::FileName(file_name) => {
            let path = relative_path::create_detect_prefix(file_name);
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let tast_provider::ComputeTastAndErrors { diagnostics, tast, .. } =
                tast_provider::compute_tast_and_errors_unquarantined(&ctx, &entry, error_filter);
            (diagnostics, std::iter::once((path, tast)).collect())
        }
        FileInput::FileContent(contents) => {
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                relative_path::default.clone(),
                contents.as_bytes().into(),
            );
            // Explicitly put the contents of `ctx` in a quarantine, since they
            // may overwrite naming table entries.
            let tast_provider::ComputeTastAndErrors { diagnostics, tast, .. } =
                crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                    tast_provider::compute_tast_and_errors_unquarantined(&ctx, &entry, error_filter)
                });
            (diagnostics, std::iter::once((relative_path::default.clone(), tast)).collect())
        }
    }
}

fn go_sequential(
    file_inputs: &[FileInput],
    ctx: &provider_context::T,
    return_expanded_tast: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> (diagnostics_state::T, Tasts) {
    let mut errors_acc = diagnostics_state::T::new();
    let mut tasts = Tasts::new();
    for file_input in file_inputs {
        let (errors, file_tast) = process_file_input(ctx, error_filter, file_input);
        errors_acc = diagnostics_state::merge(errors, errors_acc);
        if return_expanded_tast {
            // `Relative_path.Map.union tasts file_tast`: the first binding wins.
            for (path, tast) in file_tast {
                tasts.entry(path).or_insert(tast);
            }
        } else {
            tasts = Tasts::new()
        }
    }
    (errors_acc, tasts)
}

pub fn go(
    file_inputs: &[FileInput],
    ctx: &provider_context::T,
    return_expanded_tast: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> (diagnostics_state::T, Tasts) {
    go_sequential(file_inputs, ctx, return_expanded_tast, error_filter)
}
