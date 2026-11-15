// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_codeAction`, `do_codeAction_resolve` (and
//! `should_use_snippet_edits`, `location_of_code_action_request`).

#![allow(unused_imports)]

use super::*;

/// `do_codeAction`: the actions, the file, and the diagnostics the daemon
/// recomputed if it did (the caller then schedules a recheck of the file).
pub(crate) fn do_code_action(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::code_action_request::Params,
) -> Result<(
    lsp::code_action::Result,
    path::T,
    Option<Vec<client_ide_message::FinalizedDiagnostic>>,
), Exn> {
    let (document, range, file_path) = location_of_code_action_request(editor_open_files, params)?;
    let (actions, errors_opt) = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::code_action(document, range),
    )?;
    Ok((actions, file_path, errors_opt))
}

/// `do_codeAction_resolve`
pub(crate) fn do_code_action_resolve(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::code_action_request::Params,
    resolve_title: &str,
) -> Result<lsp::code_action_resolve::Result, Exn> {
    let (document, range, _file_path) = location_of_code_action_request(editor_open_files, params)?;
    let use_snippet_edits = should_use_snippet_edits(initialize_params().as_deref());
    ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::code_action_resolve(document, range, resolve_title.to_string(), use_snippet_edits),
    )
}

/// `should_use_snippet_edits`
pub(crate) fn should_use_snippet_edits(initialize_params: Option<&lsp::initialize::Params>) -> bool {
    initialize_params
        .map(|p| p.client_capabilities.client_experimental.snippet_text_edit)
        .unwrap_or(false)
}

/// `location_of_code_action_request`
pub(crate) fn location_of_code_action_request(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::code_action_request::Params,
) -> Result<(client_ide_message::Document, ide_api_types::Range, path::T), Exn> {
    let text_document = get_text_document_item(editor_open_files, &params.text_document.uri)?;
    let document = lsp_document_to_ide(&text_document)?;
    let file_path = document.file_path.clone();
    let range = lsp_range_to_ide(&params.range);
    Ok((document, range, file_path))
}
