// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): the formatting family: `do_formatting_common`,
//! `do_documentRangeFormatting`, `do_documentOnTypeFormatting`,
//! `do_documentFormatting`, `do_willSaveWaitUntil`.

#![allow(unused_imports)]

use super::*;

/// `do_documentRangeFormatting`
pub(crate) fn do_document_range_formatting(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::document_range_formatting::Params,
) -> Result<lsp::document_range_formatting::Result, Exn> {
    let action = crate::server_format_types::IdeAction::Range(lsp_range_to_ide(&params.range));
    do_formatting_common(&params.text_document.uri, editor_open_files, &action, &params.options)
}

/// `do_documentOnTypeFormatting`
pub(crate) fn do_document_on_type_formatting(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::document_on_type_formatting::Params,
) -> Result<lsp::document_on_type_formatting::Result, Exn> {
    // In LSP, positions do not point directly to characters, but to spaces in between characters.
    // Thus, the LSP position that the cursor points to after typing a character is the space
    // immediately after the character. (See the OCaml.) Thus, to send the position of the
    // character itself for formatting, we must subtract one.
    let position = lsp::Position {
        character: params.position.character - 1,
        ..params.position
    };
    let action = crate::server_format_types::IdeAction::Position(lsp_position_to_ide(&position));
    do_formatting_common(&params.text_document.uri, editor_open_files, &action, &params.options)
}

/// `do_documentFormatting`
pub(crate) fn do_document_formatting(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::document_formatting::Params,
) -> Result<lsp::document_formatting::Result, Exn> {
    let action = crate::server_format_types::IdeAction::Document;
    do_formatting_common(&params.text_document.uri, editor_open_files, &action, &params.options)
}

/// `do_willSaveWaitUntil`
pub(crate) fn do_will_save_wait_until(
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::will_save_wait_until::Params,
) -> Result<lsp::will_save_wait_until::Result, Exn> {
    let is_autosave = match params.reason {
        lsp::TextDocumentSaveReason::AfterDelay => true,
        lsp::TextDocumentSaveReason::Manual | lsp::TextDocumentSaveReason::FocusOut => false,
    };
    let uri = &params.text_document.uri;
    let lsp_doc = match editor_open_files.get(uri) {
        Some(doc) => doc,
        None => return Err(Exn::Other(crate::exception::wrap(NotFound))),
    };
    let content = &lsp_doc.text;
    if !is_autosave && formatting_is_formattable(content) {
        do_document_formatting(
            editor_open_files,
            &lsp::document_formatting::Params {
                text_document: params.text_document.clone(),
                options: lsp::document_formatting::FormattingOptions {
                    tab_size: 2,
                    insert_spaces: true,
                },
            },
        )
    } else {
        Ok(vec![])
    }
}

/// `Not_found`, as `Printexc.to_string` prints it (`UriMap.find` of a file
/// that is not open).
struct NotFound;

impl std::fmt::Debug for NotFound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Not_found")
    }
}

/// `Formatting.is_formattable`: the open-source stub (`stubs/formatting.ml`)
/// answers false.
fn formatting_is_formattable(_content: &str) -> bool {
    false
}

/// `do_formatting_common uri editor_open_files action options`
pub(crate) fn do_formatting_common(
    uri: &lsp::DocumentUri,
    editor_open_files: &uri_map::T<text_document_item::T>,
    action: &crate::server_format_types::IdeAction,
    options: &lsp::document_formatting::FormattingOptions,
) -> Result<Vec<lsp::text_edit::T>, Exn> {
    let filename_for_logging = lsp_uri_to_path(uri)?;
    // Following line will throw if the document isn't already open, so we'll
    // return an error code to the LSP client. The spec doesn't spell out if we
    // should be expected to handle formatting requests on unopened files.
    let lsp_doc = match editor_open_files.get(uri) {
        Some(doc) => doc,
        None => return Err(Exn::Other(crate::exception::wrap(NotFound))),
    };
    let content = &lsp_doc.text;
    let response = crate::ide_format::go_ide(&filename_for_logging, content, action, options);
    match response {
        // If LSP issues a formatting request at a given line+char, but we can't
        // calculate a better format for the file due to syntax errors in it,
        // then we should return "success and there are no edits to apply"
        // rather than "error".
        Err(message) if message == "File failed to parse without errors" => Ok(vec![]),
        Err(message) => Err(lsp_exception(error::UnknownErrorCode, &message)),
        Ok(r) => {
            let range = ide_range_to_lsp(&r.range);
            let new_text = r.new_text;
            Ok(vec![lsp::text_edit::T { range, new_text }])
        }
    }
}
