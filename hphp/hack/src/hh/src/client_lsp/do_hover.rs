// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_hover` (and `do_hover_common`).

#![allow(unused_imports)]

use super::*;

/// `do_hover`
pub(crate) fn do_hover(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::hover::Params,
) -> Result<lsp::hover::Result, Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    let infos = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::hover(document, location),
    )?;
    Ok(do_hover_common(&infos))
}

/// `do_hover_common`
pub(crate) fn do_hover_common(infos: &crate::hover_service::Result) -> lsp::hover::Result {
    let contents = crate::hover_service::as_marked_string_list(infos);
    // We pull the position from the SymbolOccurrence.t record, so I would be
    // surprised if there were any different ones in here. Just take the first
    // non-None one.
    let range = infos
        .iter()
        .filter_map(|info| info.pos.as_ref())
        .next()
        .map(|pos| lsp_helpers::hack_pos_to_lsp_range(|a: &relative_path::T, b: &relative_path::T| a == b, pos));
    if contents.is_empty() {
        None
    } else {
        Some(lsp::hover::HoverResult { contents, range })
    }
}
