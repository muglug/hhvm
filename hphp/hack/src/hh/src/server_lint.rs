// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_lint.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! `Multi_worker.call genv.workers ~job ~merge:List.rev_append ~neutral:[]
//! ~next`: the buckets that `next` gives are linted on the rayon pool, and
//! their results merged in the order of the buckets, as one worker would
//! (`rev_append r_n (... (rev_append r_1 []))`). `Typing_deps.trace` is off
//! while they run (see `crate::linting_main::lint`), and restored after.
//!
//! Also here: the `Lint` and `Lint_json` modes of `hh_single_type_check.ml`
//! ([`hh_single_lint`]), for the mode table of `hh single` (F0).

use std::sync::Arc;
use std::sync::atomic::Ordering;

use oxidized::pos::Pos;
use rayon::prelude::*;

use crate::ctx::Ctx;
use crate::lints_core;
use crate::relative_path as rp;
use crate::server_env::Genv;

type RP = rp::T;

/// For linting from stdin, we pass the file contents in directly because there's
/// no other way to get ahold of the contents of stdin from a worker process. But
/// when linting from disk, we want each individual worker to read the file off disk
/// by itself, so that we don't need to read all the files at the beginning and hold
/// them all in memory.
#[derive(Clone, Debug)]
pub struct LintTarget {
    pub filename: RP,
    pub contents: Option<String>,
}

pub fn lint(
    ctx: &Arc<Ctx>,
    _acc: Vec<lints_core::T<Pos>>,
    files_with_contents: &[LintTarget],
) -> Vec<lints_core::T<Pos>> {
    files_with_contents
        .iter()
        .fold(vec![], |acc, LintTarget { filename, contents }| {
            let (mut errs, ()) = lints_core::do_(|| {
                crate::diagnostics_state::ignore_(|| {
                    let contents: Vec<u8> = match contents {
                        Some(contents) => contents.as_bytes().to_vec(),
                        None => match crate::sys_utils::cat(&rp::to_absolute(filename)) {
                            Ok(contents) => contents,
                            // `Sys_error`, which nothing catches.
                            Err(e) => panic!("Sys_error {:?}", e),
                        },
                    };
                    crate::linting_main::lint(ctx, filename, &contents)
                })
            });
            // `errs @ acc`
            errs.extend(acc);
            errs
        })
}

pub fn lint_and_filter(
    ctx: &Arc<Ctx>,
    code: isize,
    acc: Vec<lints_core::T<Pos>>,
    fnl: &[LintTarget],
) -> Vec<lints_core::T<Pos>> {
    let lint_errs = lint(ctx, acc, fnl);
    lint_errs
        .into_iter()
        .filter(|err| lints_core::get_code(err) == code)
        .collect()
}

/// `Multi_worker.call workers ~job ~merge:List.rev_append ~neutral:[] ~next`
/// (see the module doc).
fn multi_worker_call(
    buckets: Vec<Vec<LintTarget>>,
    job: impl Fn(Vec<lints_core::T<Pos>>, &[LintTarget]) -> Vec<lints_core::T<Pos>> + Sync,
) -> Vec<lints_core::T<Pos>> {
    let orig_trace = crate::typing_deps::trace.swap(false, Ordering::Relaxed);
    let results: Vec<Vec<lints_core::T<Pos>>> = buckets
        .par_iter()
        .map(|bucket| job(vec![], bucket))
        .collect();
    crate::typing_deps::trace.store(orig_trace, Ordering::Relaxed);
    let mut acc: Vec<lints_core::T<Pos>> = vec![];
    for r in results {
        // `List.rev_append r acc`
        let mut merged: Vec<lints_core::T<Pos>> = r.into_iter().rev().collect();
        merged.extend(acc);
        acc = merged;
    }
    acc
}

pub fn lint_all(genv: &Genv, ctx: &Arc<Ctx>, code: isize) -> Vec<lints_core::T<crate::pos::Absolute>> {
    let tcopt = crate::provider_context::get_tcopt(ctx);
    let sample_rate = tcopt.tco_typecheck_sample_rate;
    // `genv.indexer Find_utils.is_hack`
    let mut next = match crate::server_notifier::indexer(
        &genv.notifier,
        Box::new(crate::find_utils::is_hack),
    ) {
        Ok(next) => next,
        Err(e) => panic!("{:?}", e),
    };
    // `Hack_bucket.of_list`: each list of files the indexer gives is a bucket;
    // the empty list is `Done`.
    let mut buckets = vec![];
    loop {
        let lst = next();
        let bucket: Vec<LintTarget> = lst
            .into_iter()
            .map(|fn_| LintTarget {
                filename: rp::create(rp::Prefix::Root, &fn_),
                contents: None,
            })
            .filter(|LintTarget { filename, .. }| {
                crate::find_utils::sample_filter(sample_rate, filename)
            })
            .collect();
        if bucket.is_empty() {
            break;
        }
        buckets.push(bucket);
    }
    let errs = multi_worker_call(buckets, |acc, fnl| lint_and_filter(ctx, code, acc, fnl));
    errs.into_iter().map(lints_core::to_absolute).collect()
}

fn create_rp(s: &str) -> RP {
    rp::create(rp::Prefix::Root, s)
}

fn prepare_errors_for_output(
    errs: Vec<lints_core::T<Pos>>,
) -> Vec<lints_core::T<crate::pos::Absolute>> {
    let mut errs = errs;
    // `List.sort` is stable.
    errs.sort_by(|x, y| crate::pos::compare(&lints_core::get_pos(x), &lints_core::get_pos(y)));
    errs.into_iter().map(lints_core::to_absolute).collect()
}

pub fn go(genv: &Genv, ctx: &Arc<Ctx>, fnl: &[String]) -> Vec<lints_core::T<crate::pos::Absolute>> {
    let files_with_contents: Vec<LintTarget> = fnl
        .iter()
        .map(|filename| LintTarget {
            filename: create_rp(filename),
            contents: None,
        })
        .collect();
    let errs = if files_with_contents.len() > 10 {
        // `Multi_worker.next genv.workers files_with_contents`
        let mut next = crate::bucket::make_list(
            genv.num_workers,
            None,
            None,
            files_with_contents,
        );
        let mut buckets = vec![];
        loop {
            let bucket = next();
            if bucket.is_empty() {
                break;
            }
            buckets.push(bucket);
        }
        multi_worker_call(buckets, |acc, fnl| lint(ctx, acc, fnl))
    } else {
        lint(ctx, vec![], &files_with_contents)
    };
    prepare_errors_for_output(errs)
}

pub fn go_stdin(
    ctx: &Arc<Ctx>,
    filename: &str,
    contents: &str,
) -> Vec<lints_core::T<crate::pos::Absolute>> {
    let file_with_contents = LintTarget {
        filename: create_rp(filename),
        contents: Some(contents.to_string()),
    };
    prepare_errors_for_output(lint(ctx, vec![], &[file_with_contents]))
}

/// The `Lint` (`json = false`) and `Lint_json` (`json = true`) branches of
/// `handle_mode` in `hh_single_type_check.ml`: lints `files_contents` (the
/// files of the test, in the order of `Relative_path.Map.fold`) and prints
/// the lints on `oc`. Returns the exit code: 2 when it calls `exit 2`, 0
/// otherwise.
pub fn hh_single_lint(
    ctx: &Arc<Ctx>,
    files_contents: &[(RP, Vec<u8>)],
    json: bool,
    error_format: crate::diagnostics_state::Format,
    oc: &mut dyn std::io::Write,
) -> i32 {
    // `Relative_path.Map.fold files_contents ~init:[] ~f:(fun fn content
    // lint_errors -> lint_errors @ fst (Lints_core.do_ ...))`
    let mut lint_errors: Vec<lints_core::T<Pos>> = vec![];
    for (fn_, content) in files_contents {
        lint_errors.extend(lints_core::do_(|| crate::linting_main::lint(ctx, fn_, content)).0);
    }
    if !json {
        if !lint_errors.is_empty() {
            let lint_errors = prepare_errors_for_output(lint_errors);
            crate::server_lint_types::output_text(oc, &lint_errors, error_format);
            2
        } else {
            let _ = oc.write_all(b"No lint errors\n");
            0
        }
    } else {
        let json_errors = prepare_errors_for_output(lint_errors);
        crate::server_lint_types::output_json(Some(true), Some(true), oc, &json_errors);
        2
    }
}
