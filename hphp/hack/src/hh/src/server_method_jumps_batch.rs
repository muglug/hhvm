// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_method_jumps_batch.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: see `server_infer_type_batch`.

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
    acc.insert(0, result);
    acc
}

pub fn go(ctx: &provider_context::T, classes: Vec<String>, filter: Filter) -> Vec<MjResult> {
    // Sort and dedup identical queries
    let mut deduped = classes;
    deduped.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    deduped.dedup();
    let results = get_ancestors_multiple(ctx, vec![], &deduped, filter);
    results.into_iter().flatten().collect()
}
