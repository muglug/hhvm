// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/symbol_info_service.ml` (the `DUMP_SYMBOL_INFO`
//! command): dumps all the symbol info (like fun-calls) in input files. See
//! `hh/PORTING.md`.

use crate::server_command_types::symbol_info_service::Result;
use crate::symbol_info_service_utils::RawResult;
use crate::symbol_info_service_utils::format_result;
use crate::symbol_info_service_utils::helper;

pub fn parallel_helper(
    workers: Option<usize>,
    filename_l: &[crate::relative_path::T],
    ctx: &crate::provider_context::T,
) -> RawResult {
    crate::multi_worker::call_service::<SymbolInfoJob, _>(
        ctx,
        (),
        filename_l,
        rev_append,
        vec![],
        || false,
        |_| parallel_helper_threads(workers, filename_l, ctx),
    )
}

/// `List.rev_append`
fn rev_append(b: RawResult, c: RawResult) -> RawResult {
    let mut r: RawResult = b.into_iter().rev().collect();
    r.extend(c);
    r
}

/// The job of [`parallel_helper`] on the workers.
pub struct SymbolInfoJob;

impl crate::multi_worker::ServiceJob for SymbolInfoJob {
    const NAME: &'static str = "Symbol_info_service.helper";
    type Params = ();
    type Item = crate::relative_path::T;
    type Output = RawResult;
    fn run(ctx: &crate::provider_context::T, (): &(), files: Vec<crate::relative_path::T>) -> RawResult {
        helper(ctx, vec![], &files)
    }
}

/// [`parallel_helper`] without workers.
fn parallel_helper_threads(
    workers: Option<usize>,
    filename_l: &[crate::relative_path::T],
    ctx: &crate::provider_context::T,
) -> RawResult {
    crate::find_refs_service::multi_worker_call(
        workers,
        filename_l,
        |acc: RawResult, files: Vec<crate::relative_path::T>| helper(ctx, acc, &files),
        Vec::new,
        // `List.rev_append`
        |b: RawResult, c: RawResult| {
            let mut r: RawResult = b.into_iter().rev().collect();
            r.extend(c);
            r
        },
        || false,
    )
}

/// Entry Point
pub fn go(workers: Option<usize>, file_list: &[String], env: &crate::server_env::Env) -> Result {
    let filename_l: Vec<crate::relative_path::T> = file_list
        .iter()
        .filter(|f| crate::find_utils::file_filter(f))
        .map(|f| crate::relative_path::create(crate::relative_path::Prefix::Root, f))
        .collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let raw_result = if filename_l.len() < 10 {
        helper(&ctx, vec![], &filename_l)
    } else {
        parallel_helper(workers, &filename_l, &ctx)
    };
    format_result(raw_result)
}
