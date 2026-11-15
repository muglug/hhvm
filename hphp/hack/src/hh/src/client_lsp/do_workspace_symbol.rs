// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_workspaceSymbol` (and `hack_symbol_to_lsp`).

#![allow(unused_imports)]

use super::*;

/// `do_workspaceSymbol`
pub(crate) fn do_workspace_symbol(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    params: &lsp::workspace_symbol::Params,
) -> Result<lsp::workspace_symbol::Result, Exn> {
    let query = params.query.clone();
    let results = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::workspace_symbol(query),
    )?;
    results.iter().map(hack_symbol_to_lsp).collect()
}

/// `hack_symbol_to_lsp`
pub(crate) fn hack_symbol_to_lsp(symbol: &crate::search_utils::Symbol) -> Result<lsp::symbol_information::T, Exn> {
    use crate::file_info::SiKind;
    use lsp::symbol_information::SymbolKind;
    // Hack sometimes gives us back items with an empty path, by which it
    // intends "whichever path you asked me about". That would be meaningless
    // here. If it does, then it'll pick up our default path (also empty),
    // which will throw and go into our telemetry. That's the best we can do.
    let kind = match symbol.result_type {
        SiKind::SIClass => SymbolKind::Class,
        SiKind::SIInterface => SymbolKind::Interface,
        // LSP doesn't have traits, so we approximate with interface
        SiKind::SITrait => SymbolKind::Interface,
        SiKind::SIEnum => SymbolKind::Enum,
        SiKind::SIClassMethod => SymbolKind::Method,
        SiKind::SIFunction => SymbolKind::Function,
        // LSP doesn't have typedef, so we approximate with class
        SiKind::SITypedef => SymbolKind::Class,
        SiKind::SIGlobalConstant => SymbolKind::Constant,
        SiKind::SINamespace => SymbolKind::Namespace,
        SiKind::SIMixed => SymbolKind::Variable,
        SiKind::SIXHP => SymbolKind::Class,
        SiKind::SILiteral => SymbolKind::Variable,
        SiKind::SIClassConstant => SymbolKind::Constant,
        SiKind::SIProperty => SymbolKind::Property,
        SiKind::SILocalVariable => SymbolKind::Variable,
        SiKind::SIConstructor => SymbolKind::Constructor,
        // Do these happen in practice?
        SiKind::SIKeyword | SiKind::SIUnknown => return Err(failwith("Unknown symbol kind")),
    };
    Ok(lsp::symbol_information::T {
        name: crate::utils::strip_ns(&symbol.name).to_string(),
        kind,
        location: hack_pos_to_lsp_location(&symbol.pos, ""),
        detail: None,
        container_name: None,
    })
}
