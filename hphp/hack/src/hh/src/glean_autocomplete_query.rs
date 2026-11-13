// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/glean_autocomplete_query.ml`: the open-source stub (the
//! queries are empty). See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).

use crate::file_info::SiKind;
use crate::search_types::AutocompleteType;
use crate::search_types::find_refs::Action;

pub fn make_symbols_query(
    prefix: &str,
    context: AutocompleteType,
    kind_filter: Option<SiKind>,
) -> String {
    let _ = (prefix, context, kind_filter);
    String::new()
}

pub fn make_refs_query(action: &Action) -> String {
    let _ = action;
    String::new()
}
