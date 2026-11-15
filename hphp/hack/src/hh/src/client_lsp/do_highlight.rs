// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_highlight` (and `hack_range_to_lsp_highlight`).

#![allow(unused_imports)]

use super::*;

/// `do_highlight`
pub(crate) fn do_highlight(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::document_highlight::Params,
) -> Result<lsp::document_highlight::Result, Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    let ranges = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::document_highlight(document, location),
    )?;
    Ok(ranges.iter().map(hack_range_to_lsp_highlight).collect())
}

/// `hack_range_to_lsp_highlight`
pub(crate) fn hack_range_to_lsp_highlight(range: &ide_api_types::Range) -> lsp::document_highlight::DocumentHighlight {
    lsp::document_highlight::DocumentHighlight {
        range: ide_range_to_lsp(range),
        kind: None,
    }
}
