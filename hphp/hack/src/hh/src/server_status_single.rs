// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_status_single.ml`. See `hh/PORTING.md`.
//!
//! `go_parallel` runs the buckets one after the other on this thread (the
//! diagnostics are merged, then sorted by the caller: the order of the
//! buckets cannot be seen).

use crate::diagnostics;
use crate::filter_diagnostics;
use crate::find_utils;
use crate::hh_logger;
use crate::provider_context;
use crate::provider_utils;
use crate::relative_path;
use crate::server_command_types::FileInput;
use crate::server_command_types::Tasts;
use crate::server_env;
use crate::tast_provider;

fn file_inputs_to_cacheable_paths(file_inputs: &[FileInput]) -> Option<Vec<relative_path::T>> {
    let mut acc = vec![];
    for file_input in file_inputs {
        match file_input {
            FileInput::FileName(file_name) => {
                let path = relative_path::create_detect_prefix(file_name);
                if find_utils::path_filter(&path) {
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

fn diagnostics_for_paths(diagnostics: &diagnostics::T, paths: &[relative_path::T]) -> diagnostics::T {
    diagnostics::from_file_diagnostic_list(
        paths
            .iter()
            .flat_map(|path| {
                let diagnostics = diagnostics::get_file_diagnostics(Some(false), diagnostics, path);
                let l = diagnostics::fold_per_file_diagnostics(&diagnostics, vec![], |mut acc, diagnostic| {
                    acc.insert(0, (path.clone(), diagnostic.clone()));
                    acc
                });
                l
            })
            .collect(),
    )
}

pub fn go_from_cached_diagnostics(
    env: &server_env::Env,
    file_inputs: &[FileInput],
    return_expanded_tast: bool,
    preexisting_warnings: bool,
    is_stale: bool,
    uses_partial_typecheck: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> Option<(diagnostics::T, Tasts)> {
    if return_expanded_tast
        || preexisting_warnings
        || is_stale
        || !server_env::are_diagnostics_complete(env, uses_partial_typecheck)
    {
        None
    } else {
        match file_inputs_to_cacheable_paths(file_inputs) {
            None => None,
            Some(paths) => {
                hh_logger::debug(None, None, "ServerStatusSingle: using cached diagnostics");
                let tast_provider::ErrorFilter {
                    error_filter,
                    warnings_saved_state,
                } = error_filter;
                let diagnostics = diagnostics_for_paths(&env.diagnostics, &paths);
                let diagnostics =
                    diagnostics::filter_out_mergebase_warnings(warnings_saved_state.as_ref(), diagnostics);
                let diagnostics = filter_diagnostics::filter_rel(error_filter, diagnostics);
                Some((diagnostics, Tasts::new()))
            }
        }
    }
}

/// Helper function to process a single file input
fn process_file_input(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    file_input: &FileInput,
) -> (diagnostics::T, Tasts) {
    match file_input {
        FileInput::FileName(file_name) => {
            let path = relative_path::create_detect_prefix(file_name);
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let tast_provider::ComputeTastAndErrors { diagnostics, tast, .. } =
                tast_provider::compute_tast_and_errors_unquarantined(&ctx, &entry, error_filter);
            (diagnostics, Tasts::unit(path, tast))
        }
        FileInput::FileContent(contents) => {
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                relative_path::DEFAULT,
                contents.as_str().into(),
            );
            let tast_provider::ComputeTastAndErrors { diagnostics, tast, .. } =
                // Explicitly put the contents of `ctx` in a quarantine, since they
                // may overwrite naming table entries.
                provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
                    tast_provider::compute_tast_and_errors_unquarantined(&ctx, &entry, error_filter)
                });
            (diagnostics, Tasts::unit(relative_path::DEFAULT, tast))
        }
    }
}

/// Single-threaded implementation
fn go_sequential(
    file_inputs: &[FileInput],
    ctx: &provider_context::T,
    return_expanded_tast: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> (diagnostics::T, Tasts) {
    let mut errors_acc = diagnostics::EMPTY;
    let mut tasts = Tasts::new();
    for file_input in file_inputs {
        let (errors, file_tast) = process_file_input(ctx, error_filter, file_input);
        errors_acc = diagnostics::merge(errors, errors_acc);
        tasts = if return_expanded_tast {
            crate::wrapped_map::union(None, &tasts, &file_tast)
        } else {
            Tasts::new()
        };
    }
    (errors_acc, tasts)
}

/// Multi-threaded worker job function
fn worker_job(
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
    acc: (diagnostics::T, Tasts),
    file_inputs: &[FileInput],
) -> (diagnostics::T, Tasts) {
    let (mut errors_acc, mut tasts) = acc;
    for file_input in file_inputs {
        let (errors, file_tast) = process_file_input(ctx, error_filter, file_input);
        errors_acc = diagnostics::merge(errors, errors_acc);
        tasts = crate::wrapped_map::union(None, &tasts, &file_tast);
    }
    (errors_acc, tasts)
}

/// Merge function for combining results from workers
fn merge_results(
    return_expanded_tast: bool,
    result: (diagnostics::T, Tasts),
    acc: (diagnostics::T, Tasts),
) -> (diagnostics::T, Tasts) {
    let (errors1, tasts1) = result;
    let (errors2, tasts2) = acc;
    let merged_errors = diagnostics::merge(errors1, errors2);
    let merged_tasts = if return_expanded_tast {
        crate::wrapped_map::union(None, &tasts1, &tasts2)
    } else {
        Tasts::new()
    };
    (merged_errors, merged_tasts)
}

/// Parallel implementation
fn go_parallel(
    num_workers: isize,
    file_inputs: &[FileInput],
    ctx: &provider_context::T,
    return_expanded_tast: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> (diagnostics::T, Tasts) {
    let mut next = crate::bucket::make_list(num_workers, None, None, file_inputs.to_vec());
    let mut acc = (diagnostics::EMPTY, Tasts::new());
    loop {
        let bucket = next();
        if bucket.is_empty() {
            break;
        }
        let res = worker_job(ctx, error_filter, (diagnostics::EMPTY, Tasts::new()), &bucket);
        acc = merge_results(return_expanded_tast, res, acc);
    }
    acc
}

/// Main entry point that decides whether to use parallel or sequential processing
pub fn go(
    num_workers: isize,
    file_inputs: &[FileInput],
    ctx: &provider_context::T,
    return_expanded_tast: bool,
    error_filter: &tast_provider::ErrorFilter,
) -> (diagnostics::T, Tasts) {
    let num_files = file_inputs.len();
    // Use parallel processing if there are enough files to justify the overhead
    if num_files >= 10 {
        go_parallel(num_workers, file_inputs, ctx, return_expanded_tast, error_filter)
    } else {
        go_sequential(file_inputs, ctx, return_expanded_tast, error_filter)
    }
}
