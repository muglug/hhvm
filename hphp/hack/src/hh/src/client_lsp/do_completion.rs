// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_completion` and its helpers
//! (`make_ide_completion_response`, `completion_kind_to_si_kind`,
//! `si_kind_to_completion_kind`).

#![allow(unused_imports)]

use super::*;

/// `do_completion`
pub(crate) fn do_completion(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::completion::Params,
) -> Result<lsp::completion::Result, Exn> {
    // Other parameters
    let (document, location) = get_document_location(editor_open_files, &params.loc)?;
    let is_manually_invoked = match &params.context {
        None => false,
        Some(c) => lsp::completion::is_invoked(c.trigger_kind),
    };
    // this is what I want to fix
    let request = client_ide_message::request::completion(
        document.clone(),
        location,
        client_ide_message::CompletionRequest { is_manually_invoked },
    );
    let infos = ide_rpc(ide_service, tracking_id, ref_unblocked_time, request)?;
    let filename = path::to_string(&document.file_path);
    make_ide_completion_response(&infos, &filename)
}

/// This conversion is imprecise.  Comments indicate potential gaps
pub(crate) fn completion_kind_to_si_kind(
    completion_kind: Option<lsp::completion::CompletionItemKind>,
) -> crate::file_info::SiKind {
    use crate::file_info::SiKind;
    use lsp::completion::CompletionItemKind as C;
    match completion_kind {
        Some(C::Class) => SiKind::SIClass,
        Some(C::Method) => SiKind::SIClassMethod,
        Some(C::Function) => SiKind::SIFunction,
        // or SI_Mixed, but that's never used
        Some(C::Variable) => SiKind::SILocalVariable,
        Some(C::Property) => SiKind::SIProperty,
        // or SI_ClassConstant
        Some(C::Constant) => SiKind::SIGlobalConstant,
        // or SI_Trait
        Some(C::Interface) => SiKind::SIInterface,
        Some(C::Enum) => SiKind::SIEnum,
        Some(C::Module) => SiKind::SINamespace,
        Some(C::Constructor) => SiKind::SIConstructor,
        Some(C::Keyword) => SiKind::SIKeyword,
        Some(C::Value) => SiKind::SILiteral,
        Some(C::TypeParameter) => SiKind::SITypedef,
        // The completion enum includes things we don't really support
        _ => SiKind::SIUnknown,
    }
}

pub(crate) fn si_kind_to_completion_kind(
    kind: crate::file_info::SiKind,
) -> Option<lsp::completion::CompletionItemKind> {
    use crate::file_info::SiKind;
    use lsp::completion::CompletionItemKind as C;
    match kind {
        SiKind::SIXHP | SiKind::SIClass => Some(C::Class),
        SiKind::SIClassMethod => Some(C::Method),
        SiKind::SIFunction => Some(C::Function),
        SiKind::SIMixed | SiKind::SILocalVariable => Some(C::Variable),
        SiKind::SIProperty => Some(C::Field),
        SiKind::SIClassConstant => Some(C::Constant),
        SiKind::SIInterface | SiKind::SITrait => Some(C::Interface),
        SiKind::SIEnum => Some(C::Enum),
        SiKind::SINamespace => Some(C::Module),
        SiKind::SIConstructor => Some(C::Constructor),
        SiKind::SIKeyword => Some(C::Keyword),
        SiKind::SILiteral => Some(C::Value),
        SiKind::SIGlobalConstant => Some(C::Constant),
        SiKind::SITypedef => Some(C::TypeParameter),
        SiKind::SIUnknown => None,
    }
}

/// `make_ide_completion_response result filename`
pub(crate) fn make_ide_completion_response(
    result: &crate::autocomplete_types::IdeResult,
    filename: &str,
) -> Result<lsp::completion::CompletionList, Exn> {
    use crate::autocomplete_types::AutocompleteItem;
    use crate::autocomplete_types::InsertText;
    use crate::yojson::safe as yojson;
    use lsp::completion::InsertTextFormat;
    let hack_to_insert = |completion: &AutocompleteItem| -> Result<
        (lsp::text_edit::T, InsertTextFormat, Vec<lsp::text_edit::T>),
        Exn,
    > {
        let additional_edits = completion
            .res_additional_edits
            .iter()
            .map(|(text, range)| lsp::text_edit::T {
                range: ide_range_to_lsp(range),
                new_text: text.clone(),
            })
            .collect();
        let range = ide_range_to_lsp(&completion.res_replace_pos);
        Ok(match &completion.res_insert_text {
            InsertText::InsertAsSnippet(crate::autocomplete_types::SnippetWithFallback { snippet, fallback }) => {
                // `Option.value_exn !initialize_params_ref`
                let initialize_params = match initialize_params() {
                    Some(p) => p,
                    None => return Err(failwith("Option.value_exn None")),
                };
                if lsp_helpers::supports_snippets(&initialize_params) {
                    (
                        lsp::text_edit::T {
                            range,
                            new_text: snippet.clone(),
                        },
                        InsertTextFormat::SnippetFormat,
                        additional_edits,
                    )
                } else {
                    (
                        lsp::text_edit::T {
                            range,
                            new_text: fallback.clone(),
                        },
                        InsertTextFormat::PlainText,
                        additional_edits,
                    )
                }
            }
            InsertText::InsertLiterally(text) => (
                lsp::text_edit::T {
                    range,
                    new_text: text.clone(),
                },
                InsertTextFormat::PlainText,
                additional_edits,
            ),
        })
    };
    let hack_completion_to_lsp = |completion: &AutocompleteItem| -> Result<lsp::completion::CompletionItem, Exn> {
        let (text_edit, insert_text_format, additional_text_edits) = hack_to_insert(completion)?;
        // `if Pos.filename completion.res_decl_pos = "" then Pos.set_file filename ...`
        let pos_filename = pos::filename(&completion.res_decl_pos);
        let filename = if pos_filename.is_empty() {
            filename.to_string()
        } else {
            pos_filename
        };
        let data = {
            let (line, start, _) = pos::info_pos(&completion.res_decl_pos);
            let base_class = match &completion.res_base_class {
                Some(base_class) => vec![("base_class".to_string(), yojson::T::String(base_class.clone()))],
                None => vec![],
            };
            // If we do not have a correct file position, skip sending that data
            if line == 0 && start == 0 {
                let mut l = vec![(
                    "fullname".to_string(),
                    yojson::T::String(completion.res_fullname.clone()),
                )];
                l.extend(base_class);
                Some(yojson::T::Assoc(l))
            } else {
                // Fullname is needed for namespaces.  We often trim namespaces to make
                // the results more readable, such as showing "ad__breaks" instead of
                // "Thrift\Packages\cf\ad__breaks".
                // Filename/line/char/base_class are used to handle class methods.
                // We could unify this with fullname in the future.
                let mut l = vec![
                    (
                        "fullname".to_string(),
                        yojson::T::String(completion.res_fullname.clone()),
                    ),
                    ("filename".to_string(), yojson::T::String(filename)),
                    ("line".to_string(), yojson::T::Int(line)),
                    ("char".to_string(), yojson::T::Int(start)),
                ];
                l.extend(base_class);
                Some(yojson::T::Assoc(l))
            }
        };
        Ok(lsp::completion::CompletionItem {
            label: completion.res_label.clone(),
            kind: si_kind_to_completion_kind(completion.res_kind),
            detail: Some(completion.res_detail.clone()),
            documentation: completion.res_documentation.as_ref().map(|s| {
                lsp::completion::CompletionDocumentation::MarkedStringsDocumentation(vec![
                    lsp::MarkedString::MarkedString(s.clone()),
                ])
            }),
            // This will be filled in by completionItem/resolve.
            sort_text: Some(crate::autocomplete_types::sort_text(completion)),
            filter_text: completion.res_filter_text.clone(),
            insert_text: None,
            insert_text_format: Some(insert_text_format),
            text_edit: Some(text_edit),
            additional_text_edits,
            command: None,
            data,
        })
    };
    Ok(lsp::completion::CompletionList {
        is_incomplete: !result.is_complete,
        items: result
            .completions
            .iter()
            .map(hack_completion_to_lsp)
            .collect::<Result<_, _>>()?,
    })
}
