// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/custom_search_service.ml`: the open-source custom index,
//! which finds nothing. See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).

use crate::file_info::SiKind;
use crate::relative_path::RelativePath;
use crate::search_types::AutocompleteType;
use crate::search_types::SiComplete;
use crate::search_types::SiItem;
use crate::search_types::find_refs::Action;
use crate::search_utils::SiEnv;

/// Put any initialization code necessary here
pub fn initialize(sienv: SiEnv) -> SiEnv {
    sienv
}

/// If you have a way of listing namespaces, put it here
pub fn fetch_namespaces(sienv: &SiEnv) -> Vec<String> {
    let _ = sienv;
    vec![]
}

/// Use the custom search service to find symbols by autocomplete context
pub fn search_symbols(
    sienv_ref: &mut SiEnv,
    query_text: &str,
    max_results: isize,
    context: AutocompleteType,
    kind_filter: Option<SiKind>,
) -> (Vec<SiItem>, SiComplete) {
    let _ = (sienv_ref, query_text, max_results, context, kind_filter);
    (vec![], SiComplete::Complete)
}

pub fn find_refs(
    sienv_ref: &mut SiEnv,
    action: &Action,
    max_results: isize,
) -> Option<Vec<RelativePath>> {
    let _ = (sienv_ref, action, max_results);
    None
}
