// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_typeDefinition` (and
//! `hack_pos_definition_to_lsp_identifier_location`).

#![allow(unused_imports)]

use super::*;

/// `do_typeDefinition`
pub(crate) fn do_type_definition(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::type_definition::Params,
) -> Result<lsp::type_definition::Result, Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    let file = path::to_string(&document.file_path);
    let results = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::type_definition(document, location),
    )?;
    Ok(results
        .iter()
        .map(|nast_sid| super::do_definition::hack_pos_definition_to_lsp_identifier_location(nast_sid, &file))
        .collect())
}
