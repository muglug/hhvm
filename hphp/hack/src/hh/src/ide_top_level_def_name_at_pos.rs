// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_top_level_def_name_at_pos.ml`. See
//! `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::pos::Pos;

use crate::file_content::position;
use crate::identify_symbol_service;
use crate::provider_context;
use crate::symbol_occurrence;
use crate::utils;

fn first_top_level_def(symbols: &[symbol_occurrence::T<Pos>]) -> Option<String> {
    symbols.iter().fold(None, |res, symbol| match res {
        Some(_) => res,
        None => {
            if symbol_occurrence::is_top_level_definition(symbol) {
                Some(utils::strip_ns(&symbol.name).to_string())
            } else {
                None
            }
        }
    })
}

pub fn go_quarantined(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
) -> Option<String> {
    let symbols: Vec<symbol_occurrence::T<Pos>> =
        identify_symbol_service::go_quarantined(ctx, entry, pos, true);
    match first_top_level_def(&symbols) {
        Some(def) => Some(def),
        None => {
            let symbols = identify_symbol_service::all_symbols_ctx(ctx, entry);
            first_top_level_def(&symbols)
        }
    }
}
