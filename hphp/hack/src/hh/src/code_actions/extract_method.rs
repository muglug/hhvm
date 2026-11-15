// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_method/extract_method.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use super::code_action_types as cat;
use super::extract_method_to_refactor;
use super::extract_method_traverse;
use crate::ast_provider;
use crate::code_actions::extract_method_plugins;
use crate::pos::Pos;
use crate::provider_context;

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    if crate::pos::length(pos) > 0 {
        let source_text = ast_provider::compute_source_text(entry);
        let path = entry.path.clone();
        match extract_method_traverse::find_candidate(pos, entry, ctx) {
            Some(candidate) => {
                let mut refactors_from_plugins: Vec<cat::Refactor<'a>> =
                    extract_method_plugins::find(ctx, entry, &path, pos, &candidate);
                let refactor = extract_method_to_refactor::of_candidate(source_text, path, candidate);
                refactors_from_plugins.push(refactor);
                refactors_from_plugins
            }
            None => vec![],
        }
    } else {
        vec![]
    }
}
