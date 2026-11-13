// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/extract_method/extract_method.ml`. See
//! `hh/PORTING.md`.

use std::sync::Arc;

use super::code_action_types as cat;
use super::extract_method_to_refactor;
use super::extract_method_traverse;
use super::extract_method_types as t;
use crate::ast_provider;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;

/// `Extract_method_plugins.find` of `stubs/extract_method_plugins.ml`: the
/// open-source build has no plugin.
mod extract_method_plugins {
    use super::*;

    pub fn find<'a>(
        _ctx: &provider_context::T,
        _entry: &Arc<provider_context::Entry>,
        _path: &RelativePath,
        _pos: &Pos,
        _candidate: &t::Candidate,
    ) -> Vec<cat::Refactor<'a>> {
        vec![]
    }
}

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
