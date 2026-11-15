// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/inline_method/inline_method.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use super::code_action_types as cat;
use super::inline_method_find_candidate;
use super::inline_method_to_refactor;
use crate::ast_provider;
use crate::pos::Pos;
use crate::provider_context;

pub fn find<'a>(
    entry: &'a Arc<provider_context::Entry>,
    cursor: &Pos,
    ctx: &'a provider_context::T,
) -> Vec<cat::Refactor<'a>> {
    let source_text = ast_provider::compute_source_text(entry);
    let path = entry.path.clone();
    inline_method_find_candidate::find_candidate(cursor, entry, ctx)
        .and_then(|candidate| inline_method_to_refactor::to_refactor(source_text, path, candidate))
        .into_iter()
        .collect()
}
