// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_identify_function.ml`. See
//! `hh/PORTING.md`.
//!
//! Owned by **F1** (plan §7.3).
//!
//! `List.sort ~compare:by_nesting` is OCaml's merge sort
//! (`rt::ocaml_list::stable_sort`): `by_nesting` is not a total order, so
//! the order of the result depends on the algorithm.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::file_content;
use crate::identify_symbol_service;
use crate::pos::Absolute;
use crate::pos::Pos;
use crate::provider_context;
use crate::rt::ocaml_list;
use crate::symbol_definition;
use crate::symbol_occurrence;

/// Order symbols from innermost to outermost
fn by_nesting(x: &symbol_occurrence::T<Pos>, y: &symbol_occurrence::T<Pos>) -> Ordering {
    if crate::pos::contains(&x.pos, &y.pos) {
        if crate::pos::contains(&y.pos, &x.pos) {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    } else {
        Ordering::Less
    }
}

fn take_best_suggestions(l: Vec<symbol_occurrence::T<Pos>>) -> Vec<symbol_occurrence::T<Pos>> {
    let mut result = vec![];
    let mut rest = l.into_iter();
    while let Some(first) = rest.next() {
        // Check if we should stop finding suggestions. For example, in
        // "foo($bar)" it's not useful to look outside the local variable "$bar".
        let stop = matches!(
            first.type_,
            symbol_occurrence::Kind::LocalVar
                | symbol_occurrence::Kind::Method(..)
                | symbol_occurrence::Kind::Class(_)
        );
        if stop {
            // We're stopping here, but also include the other suggestions for
            // this span.
            let same_span: Vec<_> = rest
                .take_while(|x| by_nesting(&first, x) == Ordering::Equal)
                .collect();
            result.push(first);
            result.extend(same_span);
            return result;
        } else {
            result.push(first)
        }
    }
    result
}

/// The symbols at `pos` as `go_quarantined` chooses them, before their
/// definitions are looked up.
pub(crate) fn best_symbols(symbols: Vec<symbol_occurrence::T<Pos>>) -> Vec<symbol_occurrence::T<Pos>> {
    take_best_suggestions(ocaml_list::stable_sort(symbols, by_nesting))
}

/// Given a file and a position, return a list of symbols at that position,
/// plus information about the definition of that symbol if found.
pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Vec<(symbol_occurrence::T<Pos>, Option<symbol_definition::T<Pos>>)> {
    let symbols = identify_symbol_service::go_quarantined(ctx, entry, pos, false);
    let symbols = best_symbols(symbols);
    // TODO(ljw): shouldn't the following be quarantined also?
    symbols
        .into_iter()
        .map(|symbol| {
            let ast = crate::ast_provider::compute_ast(provider_context::get_popt(ctx), entry);
            let symbol_definition = crate::server_symbol_definition::go(ctx, Some(&ast), &symbol);
            (symbol, symbol_definition)
        })
        .collect()
}

pub fn go_quarantined_absolute(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Vec<(symbol_occurrence::T<Absolute>, Option<symbol_definition::T<Absolute>>)> {
    go_quarantined(ctx, entry, pos)
        .into_iter()
        .map(|(occurrence, definition)| {
            let occurrence = symbol_occurrence::to_absolute(&occurrence);
            let definition = definition.as_ref().map(symbol_definition::to_absolute);
            (occurrence, definition)
        })
        .collect()
}
