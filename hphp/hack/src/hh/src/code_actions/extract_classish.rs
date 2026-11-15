// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/extract_classish/extract_classish.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use super::code_action_types as cat;
use crate::ast_provider;
use crate::pos::Pos;
use crate::provider_context;

/// Provide refactors for when the user selects class members
/// such as "Extract method"
pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    if crate::pos::length(pos) > 0 {
        let source_text = ast_provider::compute_source_text(entry);
        let path = entry.path.clone();
        match super::extract_classish_find_candidate::find_candidate(pos, entry, ctx) {
            Some(candidate) => super::extract_classish_to_refactors::to_refactors(source_text, path, candidate),
            None => vec![],
        }
    } else {
        vec![]
    }
}
