// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_method_jumps_batch.ml`. See `hh/PORTING.md`.
//!
//! The parallel path runs its buckets one
//! after the other (`server_infer_type_batch::multi_worker_call_rev_append`).

use crate::decl_entry;
use crate::decl_provider;
use crate::method_jumps;
use crate::provider_context;
use crate::server_command_types::method_jumps::Filter;
use crate::server_command_types::method_jumps::Result as MjResult;

fn get_ancestors_single(ctx: &provider_context::T, class_: &str, filter: Filter) -> Option<Vec<MjResult>> {
    let class_ = method_jumps::add_ns(class_);
    let class_ = decl_entry::to_option(decl_provider::get_class(None, ctx, &class_));
    class_.map(|c| method_jumps::get_ancestor_classes_and_methods(ctx, &c, filter, vec![]))
}

fn get_ancestors_multiple(
    ctx: &provider_context::T,
    mut acc: Vec<Vec<MjResult>>,
    classes: &[String],
    filter: Filter,
) -> Vec<Vec<MjResult>> {
    let result: Vec<MjResult> = classes
        .iter()
        .filter_map(|class_| get_ancestors_single(ctx, class_, filter))
        .flatten()
        .collect();
    // `result :: acc`
    acc.insert(0, result);
    acc
}

/// Entry Point
pub fn go(ctx: &provider_context::T, num_workers: isize, classes: &[String], filter: Filter) -> Vec<MjResult> {
    // Sort and dedup identical queries
    let mut deduped = classes.to_vec();
    deduped.sort();
    deduped.dedup();
    let results = if deduped.len() < 10 {
        get_ancestors_multiple(ctx, vec![], &deduped, filter)
    } else {
        crate::server_infer_type_batch::multi_worker_call_rev_append(num_workers, deduped, |acc, classes| {
            get_ancestors_multiple(ctx, acc, &classes, filter)
        })
    };
    results.into_iter().flatten().collect()
}
