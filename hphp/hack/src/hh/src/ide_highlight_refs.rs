// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_highlight_refs.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F5** (plan §7.3).
//!
//! `get_target` builds a `Find_refs_service.action_internal`, and
//! `highlight_symbol` calls `Find_refs_service.find_refs_ctx` (F6's).

use std::sync::Arc;

use oxidized::pos::Pos;

use crate::file_content::position;
use crate::find_refs_service;
use crate::identify_symbol_service;
use crate::ide_api_types;
use crate::provider_context;
use crate::server_find_locals;
use crate::symbol_occurrence;
use crate::symbol_occurrence::Kind as SO;

/// `get_target symbol`
fn get_target(symbol: &symbol_occurrence::T<Pos>) -> Option<find_refs_service::ActionInternal> {
    use find_refs_service::ActionInternal::*;
    use find_refs_service::MemberClass::SubclassesOf;
    use symbol_occurrence::ReceiverClass::ClassName;
    use crate::search_types::find_refs::Member as Types;
    match &symbol.type_ {
        SO::Class(_) => Some(IClass(symbol.name.clone())),
        SO::Function => Some(IFunction(symbol.name.clone())),
        SO::Method(ClassName(class_name), member_name) => Some(IMember(
            SubclassesOf(class_name.clone()),
            Types::Method(member_name.clone()),
        )),
        SO::Property(ClassName(class_name), member_name)
        | SO::XhpLiteralAttr(class_name, member_name) => Some(IMember(
            SubclassesOf(class_name.clone()),
            Types::Property(member_name.clone()),
        )),
        SO::ClassConst(ClassName(class_name), member_name) => Some(IMember(
            SubclassesOf(class_name.clone()),
            Types::ClassConst(member_name.clone()),
        )),
        SO::Typeconst(class_name, member_name) => Some(IMember(
            SubclassesOf(class_name.clone()),
            Types::Typeconst(member_name.clone()),
        )),
        SO::GConst => Some(IGConst(symbol.name.clone())),
        _ => None,
    }
}

fn highlight_symbol(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
    symbol: &symbol_occurrence::T<Pos>,
) -> Vec<ide_api_types::Range> {
    let res: Vec<Pos> = if let Some(target) = get_target(symbol) {
        let results = find_refs_service::find_refs_ctx(ctx, entry, &target);
        results.into_iter().rev().map(|r| r.pos).collect()
    } else if symbol.type_ == SO::LocalVar {
        server_find_locals::go(ctx, entry, pos)
    } else {
        vec![]
    };
    res.iter().map(ide_api_types::pos_to_range).collect()
}

fn compare_starts(r1: &ide_api_types::Range, r2: &ide_api_types::Range) -> std::cmp::Ordering {
    position::compare(&r1.st, &r2.st).cmp(&0)
}

pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
) -> Vec<ide_api_types::Range> {
    let symbol_to_highlight = identify_symbol_service::go_quarantined(ctx, entry, pos, false);
    let mut results: Vec<ide_api_types::Range> = vec![];
    for s in &symbol_to_highlight {
        let mut stuff = highlight_symbol(ctx, entry, pos, s);
        // `List.append stuff acc`
        stuff.extend(results);
        results = stuff;
    }
    // `List.dedup_and_sort ~compare:compare_starts`: a stable sort, then of
    // each run of equal elements the last is kept (Base's
    // `remove_consecutive_duplicates`, `which_to_keep = `Last`).
    results.sort_by(compare_starts);
    let mut deduped: Vec<ide_api_types::Range> = Vec::with_capacity(results.len());
    for r in results {
        match deduped.last_mut() {
            Some(last) if compare_starts(last, &r) == std::cmp::Ordering::Equal => *last = r,
            _ => deduped.push(r),
        }
    }
    deduped
}
