// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_resolve` (completionItem/resolve) and its helpers
//! (`docblock_to_markdown`, `docblock_with_ranking_detail`,
//! `resolve_ranking_source`).

#![allow(unused_imports)]

use super::*;

/// `do_resolve`
pub(crate) fn do_resolve(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    params: &lsp::completion_item_resolve::Params,
) -> Result<lsp::completion_item_resolve::Result, Exn> {
    if params.documentation.is_some() {
        return Ok(params.clone());
    }
    let raw_kind = params.kind;
    let kind = super::do_completion::completion_kind_to_si_kind(raw_kind);
    // [do_completion] happens to provide line+col+filename for members.
    // Since docblock resolution needs line+col+filename, and we've already computed them,
    // let's just use them!
    //
    // (The OCaml's `try` is not `try%lwt`: only what fails before the rpc,
    // i.e. reading the data, falls back to resolving by symbol.)
    let data = params.data.as_ref();
    let located: Result<_, ()> = (|| {
        if data.is_none() {
            // `raise NoLocationFound`
            return Err(());
        }
        let fullname = jget::string_exn(data, "fullname").map_err(|_| ())?;
        let filename = jget::string_exn(data, "filename").map_err(|_| ())?;
        let file_path = path::make(&filename);
        let line = jget::int_exn(data, "line").map_err(|_| ())?;
        let column = jget::int_exn(data, "char").map_err(|_| ())?;
        let ranking_detail = jget::string_opt(data, "ranking_detail");
        let ranking_source = jget::int_opt(data, "ranking_source").map_err(|_| ())?;
        if line == 0 && column == 0 {
            // `failwith "NoFileLineColumnData"`
            return Err(());
        }
        let pos = file_content::position::from_one_based(line, column);
        Ok((fullname, file_path, pos, ranking_detail, ranking_source))
    })();
    let with_documentation = |raw_docblock: client_ide_message::completion_resolve::Result,
                              documentation: Option<lsp::completion::CompletionDocumentation>| {
        match raw_docblock.signature {
            None => lsp::completion::CompletionItem {
                documentation,
                ..params.clone()
            },
            Some(signature) => lsp::completion::CompletionItem {
                documentation,
                detail: Some(signature),
                ..params.clone()
            },
        }
    };
    match located {
        Ok((fullname, file_path, pos, ranking_detail, ranking_source)) => {
            let request = client_ide_message::request::completion_resolve_location(
                file_path,
                client_ide_message::Fullname(fullname),
                pos,
                resolve_ranking_source(kind, ranking_source),
            );
            let raw_docblock = ide_rpc(ide_service, tracking_id, ref_unblocked_time, request)?;
            let documentation =
                docblock_to_markdown(&docblock_with_ranking_detail(raw_docblock.docblock.clone(), ranking_detail));
            Ok(with_documentation(raw_docblock, documentation))
        }
        // If that fails, next try using symbol
        Err(()) => {
            // Completion.data was produced by [make_ide_completion_response]
            // which in all codepaths provides a "fullname" field to data
            let fullname = match jget::string_exn(data, "fullname") {
                Ok(fullname) => fullname,
                Err(e) => return Err(Exn::Other(exception::wrap(e))),
            };
            let request = client_ide_message::request::completion_resolve(
                client_ide_message::completion_resolve::Request { fullname, kind },
            );
            let raw_docblock = ide_rpc(ide_service, tracking_id, ref_unblocked_time, request)?;
            let documentation = docblock_to_markdown(&raw_docblock.docblock);
            Ok(with_documentation(raw_docblock, documentation))
        }
    }
}

/// `docblock_to_markdown`
pub(crate) fn docblock_to_markdown(
    raw_docblock: &crate::docblock_service::Result,
) -> Option<lsp::completion::CompletionDocumentation> {
    use crate::docblock_service::DocblockElement;
    if raw_docblock.is_empty() {
        None
    } else {
        // (`List.fold ~init:[]` consing: in reverse order.)
        let mut acc = vec![];
        for elt in raw_docblock {
            acc.insert(
                0,
                match elt {
                    DocblockElement::Markdown(txt) => lsp::MarkedString::MarkedString(txt.clone()),
                    DocblockElement::HackSnippet(txt) => lsp::MarkedString::MarkedCode("hack".to_string(), txt.clone()),
                    DocblockElement::XhpSnippet(txt) => lsp::MarkedString::MarkedCode("html".to_string(), txt.clone()),
                },
            );
        }
        Some(lsp::completion::CompletionDocumentation::MarkedStringsDocumentation(acc))
    }
}

/// `docblock_with_ranking_detail`
pub(crate) fn docblock_with_ranking_detail(
    mut raw_docblock: crate::docblock_service::Result,
    ranking_detail: Option<String>,
) -> crate::docblock_service::Result {
    if let Some(detail) = ranking_detail {
        raw_docblock.push(crate::docblock_service::DocblockElement::Markdown(detail));
    }
    raw_docblock
}

/// `resolve_ranking_source`
pub(crate) fn resolve_ranking_source(
    kind: crate::file_info::SiKind,
    ranking_source: Option<isize>,
) -> crate::file_info::SiKind {
    match ranking_source {
        Some(x) => crate::search_types::int_to_kind(x),
        None => kind,
    }
}
