// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/class_method_search.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).

use crate::ast_provider;
use crate::file_info::SiKind;
use crate::naming_provider;
use crate::pos;
use crate::provider_context;
use crate::search_utils;
use crate::search_utils::Term;

pub fn query_class_methods(
    ctx: &provider_context::T,
    class_name: &str,
    method_query: &str,
) -> search_utils::Result {
    // `String.lowercase`: ASCII.
    let method_query = method_query.to_ascii_lowercase();
    let matches_query = |method_name: &str| {
        if !method_query.is_empty() {
            let method_name = method_name.to_ascii_lowercase();
            method_name.contains(method_query.as_str())
        } else {
            true
        }
    };
    naming_provider::get_class_path(ctx, class_name)
        .and_then(|file| ast_provider::find_class_in_file(false, ctx, &file, class_name))
        .map(|class_| class_.methods)
        .map(|methods| {
            methods
                .into_iter()
                .filter_map(|m| {
                    let oxidized::ast::Id(pos, name) = m.name;
                    if matches_query(&name) {
                        Some(Term {
                            name,
                            pos: pos::to_absolute(&pos),
                            result_type: SiKind::SIClassMethod,
                        })
                    } else {
                        None
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}
