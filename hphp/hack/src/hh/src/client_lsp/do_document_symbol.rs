// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_documentSymbol` (and
//! `lsp_document_symbols_of_outline`, `document_symbol_location_of_symbol`).

#![allow(unused_imports)]

use super::*;

/// `do_documentSymbol`
pub(crate) fn do_document_symbol(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::document_symbol::Params,
) -> Result<lsp::document_symbol::Result, Exn> {
    let filename = lsp_uri_to_path(&params.text_document.uri)?;
    let text_document = get_text_document_item(editor_open_files, &params.text_document.uri)?;
    let document = lsp_document_to_ide(&text_document)?;
    let outline = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::document_symbol(document),
    )?;
    Ok(lsp_document_symbols_of_outline(&filename, vec![], None, &outline))
}

/// For LSP textDocument/documentSymbol, pos starts where the name starts,
/// skipping over stuff like user attributes.
/// This is expected behavior for IDE functionality like sticky scroll (T224080471 for more information).
/// Only classlikes/functionlikes can have long bodies and need this tweaking for sticky scroll.
/// This adaptor logic is here because FileOutline.ml (calculates symbol positions)
/// is used for all sorts of things, including "safe rename", but the logic
/// here is for outlines, sticky headers, and breadcrumbs.
pub(crate) fn document_symbol_location_of_symbol(
    symbol: &crate::symbol_definition::T<pos::Absolute>,
    default_path: &str,
) -> lsp::location::T {
    let full_pos = &symbol.span;
    // By convention, symbol.pos is the position of the name. See FileOutline.ml
    let line_with_name_pos = &symbol.pos;
    let pos = if pos::start_offset(line_with_name_pos) < pos::start_offset(&symbol.span) {
        // Rare case where another symbol is defined on the same line.
        symbol.span.clone()
    } else {
        pos::to_absolute(&pos::btw(&pos::to_relative(line_with_name_pos), &pos::to_relative(full_pos)))
    };
    hack_pos_to_lsp_location(&pos, default_path)
}

/// `lsp_document_symbols_of_outline ~filename ~accu ~container_name defs`
/// (each end of a list reverses the accumulator, as the OCaml's).
pub(crate) fn lsp_document_symbols_of_outline(
    filename: &str,
    mut accu: Vec<lsp::symbol_information::T>,
    container_name: Option<&str>,
    defs: &[crate::symbol_definition::T<pos::Absolute>],
) -> Vec<lsp::symbol_information::T> {
    use crate::symbol_definition::ClassishKind;
    use crate::symbol_definition::Kind;
    use crate::symbol_definition::MemberKind;
    use lsp::symbol_information::SymbolKind;
    let hack_to_lsp_kind = |kind: &Kind<pos::Absolute>| match kind {
        Kind::Function => SymbolKind::Function,
        Kind::Classish {
            classish_kind: ClassishKind::Class,
            ..
        } => SymbolKind::Class,
        Kind::Member { member_kind, .. } => match member_kind {
            MemberKind::Method => SymbolKind::Method,
            MemberKind::Property => SymbolKind::Property,
            MemberKind::ClassConst => SymbolKind::Constant,
            // e.g. "const type Ta = string;" -- absent from LSP
            MemberKind::TypeConst => SymbolKind::Class,
        },
        Kind::GlobalConst => SymbolKind::Constant,
        Kind::Classish {
            classish_kind: ClassishKind::Enum,
            ..
        } => SymbolKind::Enum,
        // LSP doesn't have traits, so we approximate with interface
        Kind::Classish {
            classish_kind: ClassishKind::Interface | ClassishKind::Trait,
            ..
        } => SymbolKind::Interface,
        Kind::LocalVar => SymbolKind::Variable,
        Kind::TypeVar => SymbolKind::TypeParameter,
        // e.g. top level type alias -- absent from LSP
        Kind::Typedef => SymbolKind::Class,
        // We never return a param from a document-symbol-search
        Kind::Param => SymbolKind::Variable,
        Kind::Module => SymbolKind::Module,
    };
    match defs.split_first() {
        // Flattens the recursive list of symbols
        None => {
            accu.reverse();
            accu
        }
        Some((def, defs)) => {
            let children: &[_] = match &def.kind {
                Kind::Classish { members, .. } => members,
                _ => &[],
            };
            accu.insert(
                0,
                lsp::symbol_information::T {
                    name: def.name.clone(),
                    kind: hack_to_lsp_kind(&def.kind),
                    location: document_symbol_location_of_symbol(def, filename),
                    container_name: container_name.map(|s| s.to_string()),
                    detail: def.detail.clone(),
                },
            );
            let accu = lsp_document_symbols_of_outline(filename, accu, Some(&def.name), children);
            lsp_document_symbols_of_outline(filename, accu, container_name, defs)
        }
    }
}
