// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_documentRename`, `do_documentRename2`,
//! `patch_to_workspace_edit_change`, `patches_to_workspace_edit`, and the parse
//! of the shell-out's output (`edit_of_patch`,
//! `shellout_patch_list_to_lsp_edits_exn`).

#![allow(unused_imports)]

use super::*;

/// `patch_to_workspace_edit_change`
fn patch_to_workspace_edit_change(patch: &server_rename_types::Patch) -> (DocumentUri, lsp::text_edit::T) {
    use server_rename_types::InsertPatch;
    use server_rename_types::Patch;
    let text_edit = match patch {
        Patch::Insert(insert_patch) | Patch::Replace(insert_patch) => lsp::text_edit::T {
            range: lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, &insert_patch.pos),
            new_text: insert_patch.text.clone(),
        },
        Patch::Remove(pos) => lsp::text_edit::T {
            range: lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, pos),
            new_text: String::new(),
        },
    };
    let uri_string = match patch {
        Patch::Insert(InsertPatch { pos, .. }) | Patch::Replace(InsertPatch { pos, .. }) => {
            crate::file_url::create(&pos::filename(pos))
        }
        Patch::Remove(pos) => crate::file_url::create(&pos::filename(pos)),
    };
    (lsp::document_uri::T::Uri(uri_string), text_edit)
}

/// `patches_to_workspace_edit`
pub(crate) fn patches_to_workspace_edit(patches: &[server_rename_types::Patch]) -> lsp::workspace_edit::T {
    let mut changes: lsp::document_uri::map::T<Vec<lsp::text_edit::T>> = Default::default();
    for (uri, text_edit) in patches.iter().map(patch_to_workspace_edit_change) {
        // `text_edit :: current_edits`
        let mut new_edits = vec![text_edit];
        if let Some(current_edits) = changes.get(&uri) {
            new_edits.extend(current_edits.iter().cloned());
        }
        changes.insert(uri, new_edits);
    }
    lsp::workspace_edit::T { changes }
}

/// `do_documentRename`: responds itself (or leaves the response to the
/// shell-out it kicks off), and returns the telemetry.
pub(crate) fn do_document_rename(
    state: &mut State,
    ide_service: &client_ide_service::T,
    metadata: &IncomingMetadata,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::rename::Params,
    id: &LspId,
) -> Result<ResultTelemetry, Exn> {
    let start_time_local_handle = ocaml_unix::gettimeofday();
    let document_position = rename_params_to_document_position(params);
    let (document, location) = get_document_location(editor_open_files, &document_position)?;
    let new_name = params.new_name.clone();
    let all_open_documents = get_documents_from_open_files(editor_open_files)?;
    let response = ide_rpc(
        ide_service,
        &metadata.tracking_id,
        ref_unblocked_time,
        client_ide_message::request::rename(document, location, new_name.clone(), all_open_documents),
    )?;
    match response {
        client_ide_message::RenameResult::NotRenameablePosition => {
            let message = "Tried to rename a non-renameable symbol";
            Err(lsp_exception(error::InvalidRequest, message))
        }
        client_ide_message::RenameResult::RenameSuccess { shellout: None, local } => {
            let patches = patches_to_workspace_edit(&local);
            respond_jsonrpc(PoweredBy::HhServer, id, &LspResult::RenameResult(patches));
            Ok(make_result_telemetry(None, None, local.len() as isize))
        }
        client_ide_message::RenameResult::RenameSuccess {
            shellout: Some((symbol_definition, find_refs_action)),
            local: ide_calculated_patches,
        } => {
            let shellable_type = run_env::ShellableType::Rename {
                symbol_definition,
                find_refs_action,
                new_name,
                ide_calculated_patches,
            };
            kickoff_shell_out_and_maybe_cancel(
                state,
                shellable_type,
                run_env::TriggeringRequest {
                    id: id.clone(),
                    metadata: metadata.clone(),
                    start_time_local_handle,
                    request: LspRequest::RenameRequest(params.clone()),
                },
            )
        }
    }
}

/// This is called when a shell-out to "hh --ide-rename-by-symbol" completes successfully
pub(crate) fn do_document_rename2(
    ide_calculated_patches: Vec<server_rename_types::Patch>,
    hh_edits: lsp::workspace_edit::T,
) -> Result<(LspResult, isize), Exn> {
    // The list of patches we receive from shelling out reflect the state
    // of files on disk, which is incorrect for edited files. To fix,
    //
    // 1) Filter out all changes for files that are open
    // 2) add the list of ide_calculated changes
    let hh_changes = hh_edits.changes;
    let ide_changes = patches_to_workspace_edit(&ide_calculated_patches);
    let mut changes = hh_changes;
    for (file, ide) in ide_changes.changes.into_iter() {
        changes.insert(file, ide);
    }
    let result_count: isize = changes.values().map(|c| c.len() as isize).sum();
    Ok((
        LspResult::RenameResult(lsp::workspace_edit::T { changes }),
        result_count,
    ))
}

/// `ide_refactor_patch`
struct IdeRefactorPatch {
    filename: String,
    char_start: isize,
    char_end: isize,
    line: isize,
    patch_type: String,
    replacement: String,
}

/// `edit_of_patch`
fn edit_of_patch(patch: &IdeRefactorPatch) -> Result<lsp::text_edit::T, Exn> {
    let text = match patch.patch_type.as_str() {
        "insert" | "replace" => patch.replacement.clone(),
        "remove" => String::new(),
        e => return Err(failwith(&format!("invalid patch type: {}", e))),
    };
    let loc = {
        let ide_shell_out_pos = HalfOpenOneBased {
            filename: patch.filename.clone(),
            char_start: patch.char_start,
            // This end is inclusive for range replacement
            char_end: patch.char_end + 1,
            line: patch.line,
        };
        ide_shell_out_pos_to_lsp_location(&ide_shell_out_pos)
    };
    Ok(lsp::text_edit::T {
        range: loc.range,
        new_text: text,
    })
}

/// `Yojson.Basic.Util`'s accessors, over `Yojson.Safe.to_basic` of the value
/// (an `` `Intlit`` is a `` `String`` there).
mod util {
    use super::super::do_find_references::Raised;
    use super::*;
    use crate::yojson::safe::T;

    fn typeof_(j: &T) -> &'static str {
        match j {
            T::Assoc(_) => "object",
            T::Bool(_) => "bool",
            T::Float(_) => "float",
            T::Int(_) => "int",
            T::List(_) => "array",
            T::Null => "null",
            T::String(_) | T::Intlit(_) => "string",
        }
    }

    /// `raise (Type_error (msg, json))`
    fn type_error<A>(msg: String) -> Result<A, Exn> {
        Err(Exn::Other(exception::wrap(Raised(format!(
            "Yojson.Basic.Util.Type_error({}, _)",
            crate::rt::ocaml_printf::sprintf_s(&msg)
        )))))
    }

    pub fn member<'a>(name: &str, j: &'a T) -> Result<&'a T, Exn> {
        static NULL: T = T::Null;
        match j {
            // `List.assoc name l` with a fallback to `Null: the first binding
            T::Assoc(l) => Ok(l.iter().find(|(k, _)| k == name).map(|(_, v)| v).unwrap_or(&NULL)),
            js => type_error(format!("Can't get member '{}' of non-object type {}", name, typeof_(js))),
        }
    }

    pub fn to_string(j: &T) -> Result<String, Exn> {
        match j {
            T::String(s) | T::Intlit(s) => Ok(s.clone()),
            js => type_error(format!("Expected string, got {}", typeof_(js))),
        }
    }

    pub fn to_int(j: &T) -> Result<isize, Exn> {
        match j {
            T::Int(i) => Ok(*i),
            js => type_error(format!("Expected int, got {}", typeof_(js))),
        }
    }

    pub fn to_list(j: &T) -> Result<&Vec<T>, Exn> {
        match j {
            T::List(l) => Ok(l),
            js => type_error(format!("Expected array, got {}", typeof_(js))),
        }
    }
}

/// Parses output of "hh --ide-rename-by-symbol".
/// If the output is malformed, raises an exception.
pub(crate) fn shellout_patch_list_to_lsp_edits_exn(stdout: &str) -> Result<lsp::workspace_edit::T, Exn> {
    use crate::yojson::safe::T;
    let patches: Vec<IdeRefactorPatch> = {
        let json = match crate::yojson::safe::from_string(stdout) {
            Ok(json) => json,
            Err(e) => return Err(Exn::Other(exception::wrap(super::do_find_references::Raised(e.to_string())))),
        };
        match &json {
            T::List(positions) => {
                let mut patches = vec![];
                for pos in positions {
                    let lst_json = pos;
                    let filename = util::to_string(util::member("filename", lst_json)?)?;
                    let raw_patches = util::to_list(util::member("patches", lst_json)?)?;
                    for raw_patch in raw_patches {
                        let char_start = util::to_int(util::member("col_start", raw_patch)?)?;
                        let char_end = util::to_int(util::member("col_end", raw_patch)?)?;
                        let line = util::to_int(util::member("line", raw_patch)?)?;
                        let patch_type = util::to_string(util::member("patch_type", raw_patch)?)?;
                        let replacement = util::to_string(util::member("replacement", raw_patch)?)?;
                        patches.push(IdeRefactorPatch {
                            filename: filename.clone(),
                            char_start,
                            char_end,
                            line,
                            patch_type,
                            replacement,
                        });
                    }
                }
                patches
            }
            T::Int(_) | T::Bool(_) | T::Intlit(_) | T::Null | T::Assoc(_) | T::Float(_) | T::String(_) => {
                return Err(failwith(&format!("Expected list, got json like {}", stdout)));
            }
        }
    };
    let mut changes: lsp::document_uri::map::T<Vec<lsp::text_edit::T>> = Default::default();
    for patch in &patches {
        let uri = lsp_helpers::path_string_to_lsp_uri(&patch.filename, &patch.filename);
        let edit = edit_of_patch(patch)?;
        let mut new_edits = vec![edit];
        if let Some(current_edits) = changes.get(&uri) {
            new_edits.extend(current_edits.iter().cloned());
        }
        changes.insert(uri, new_edits);
    }
    Ok(lsp::workspace_edit::T { changes })
}
