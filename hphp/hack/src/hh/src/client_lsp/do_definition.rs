// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_definition` (and
//! `hack_symbol_definition_to_lsp_identifier_location`).

#![allow(unused_imports)]

use super::*;

/// `do_definition`: the locations, and whether one of the occurrences is
/// an XHP literal attribute.
pub(crate) fn do_definition(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::definition::Params,
) -> Result<(lsp::definition::Result, bool), Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    let file = path::to_string(&document.file_path);
    let results = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::definition(document, location),
    )?;
    let locations = results
        .iter()
        .map(|(_, definition)| hack_symbol_definition_to_lsp_identifier_location(definition, &file))
        .collect();
    let has_xhp_attribute = results
        .iter()
        .any(|(occurrence, _)| crate::symbol_occurrence::is_xhp_literal_attr(occurrence));
    Ok((locations, has_xhp_attribute))
}

/// `hack_pos_definition_to_lsp_identifier_location`
pub(crate) fn hack_pos_definition_to_lsp_identifier_location(
    (pos, title): &(pos::Absolute, String),
    default_path: &str,
) -> lsp::definition_location::T {
    let location = hack_pos_to_lsp_location(pos, default_path);
    lsp::definition_location::T {
        location,
        title: Some(title.clone()),
    }
}

/// `hack_symbol_definition_to_lsp_identifier_location`
pub(crate) fn hack_symbol_definition_to_lsp_identifier_location(
    symbol: &crate::symbol_definition::T<pos::Absolute>,
    default_path: &str,
) -> lsp::definition_location::T {
    let location = hack_pos_to_lsp_location(&symbol.pos, default_path);
    lsp::definition_location::T {
        location,
        title: Some(crate::utils::strip_ns(&crate::symbol_definition::full_name(symbol)).to_string()),
    }
}
