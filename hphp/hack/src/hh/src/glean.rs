// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/glean.ml`: the open-source stub of the Glean client
//! (every function fails). See `hh/PORTING.md`.

use crate::file_info::SiKind;
use crate::relative_path::RelativePath;
use crate::search_types::AutocompleteType;
use crate::search_types::SiItem;
use crate::search_types::find_refs::Action;

/// `type handle = unit`
pub type Handle = ();

pub fn initialize(reponame: &str, prev_init_time: f64) -> Handle {
    let _ = (reponame, prev_init_time);
    panic!("not implemented")
}

pub fn query_autocomplete(
    handle: &Handle,
    query_text: &str,
    max_results: isize,
    context: AutocompleteType,
    kind_filter: Option<SiKind>,
) -> (Vec<SiItem>, bool) {
    let _ = (handle, query_text, max_results, context, kind_filter);
    panic!("not implemented")
}

pub fn query_refs(handle: &Handle, action: &Action, max_results: isize) -> Vec<RelativePath> {
    let _ = (handle, action, max_results);
    panic!("not implemented")
}
