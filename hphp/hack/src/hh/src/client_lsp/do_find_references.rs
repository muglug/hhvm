// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_findReferences`, `notify_refs_file_items`,
//! `handle_refs_file_items`, `do_findReferences2` (the shell-out machinery they
//! use, `kickoff_shell_out_and_maybe_cancel` and `watch_refs_stream_file`, is
//! in `client_lsp.rs`).

#![allow(unused_imports)]

use super::*;

/// An OCaml exception that is only ever printed: its `Printexc.to_string`.
pub(crate) struct Raised(pub String);

impl std::fmt::Debug for Raised {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// `Stdlib.Filename.temp_file ~temp_dir prefix suffix`: creates the empty
/// file `temp_dir/prefix<6 hex digits>suffix` (mode 0o600, a new name on a
/// collision, up to 1000 tries) and returns its name.
fn temp_file(temp_dir: &str, prefix: &str, suffix: &str) -> Result<String, Exn> {
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    use std::os::unix::fs::OpenOptionsExt;
    let mut counter = 0;
    loop {
        let rnd = {
            let mut h = std::collections::hash_map::RandomState::new().build_hasher();
            h.write_u64(ocaml_unix::gettimeofday().to_bits());
            h.write_u32(std::process::id());
            (h.finish() & 0xFFFFFF) as u32
        };
        let name = crate::rt::ocaml_filename::concat(temp_dir, &format!("{}{:06x}{}", prefix, rnd, suffix));
        match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&name)
        {
            Ok(_) => return Ok(name),
            Err(e) => {
                counter += 1;
                if counter >= 1000 {
                    // `raise (Sys_error msg)`
                    return Err(Exn::Other(exception::wrap(SysError(format!(
                        "{}: {}",
                        name,
                        sys_error_message(&e)
                    )))));
                }
            }
        }
    }
}

/// `do_findReferences`: responds itself (or leaves the response to the
/// shell-out it kicks off), and returns the telemetry.
pub(crate) fn do_find_references(
    state: &mut State,
    ide_service: &client_ide_service::T,
    metadata: &IncomingMetadata,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::find_references::Params,
    id: &LspId,
) -> Result<ResultTelemetry, Exn> {
    let start_time_local_handle = ocaml_unix::gettimeofday();
    let (document, location) = get_document_location(editor_open_files, &params.loc)?;
    let all_open_documents = get_documents_from_open_files(editor_open_files)?;
    let response = ide_rpc(
        ide_service,
        &metadata.tracking_id,
        ref_unblocked_time,
        client_ide_message::request::find_references(document, location, all_open_documents),
    )?;
    match response {
        client_ide_message::FindRefsResult::InvalidSymbol => {
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::FindReferencesResult(vec![]),
            );
            Ok(make_result_telemetry(None, None, -1))
        }
        client_ide_message::FindRefsResult::FindRefsSuccess {
            full_name: _,
            action: None,
            hint_suffixes: _,
            open_file_results: ide_calculated_positions,
        } => {
            let positions = {
                let values = uri_map::values(&ide_calculated_positions);
                // UriMap.values returns [Pos.absolute list list] and if we're here,
                // we should only have one element - the list of positions in the file the localvar is defined.
                if values.len() == 1 {
                    values.into_iter().next().unwrap()
                } else {
                    // `assert false` (Explicitly handled in ClientIdeDaemon)
                    return Err(Exn::Other(exception::wrap(Raised(
                        "Assert_failure(\"client/client_lsp.ml\", 2730, 13)".to_string(),
                    ))));
                }
            };
            let filename = lsp_helpers::lsp_text_document_identifier_to_filename(&params.loc.text_document)?;
            let positions: Vec<lsp::location::T> = positions
                .iter()
                .map(|search_types::find_refs::Result { name: _, pos }| hack_pos_to_lsp_location(pos, &filename))
                .collect();
            let n = positions.len() as isize;
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::FindReferencesResult(positions),
            );
            Ok(make_result_telemetry(None, None, n))
        }
        client_ide_message::FindRefsResult::FindRefsSuccess {
            full_name,
            action: Some(action),
            hint_suffixes,
            open_file_results,
        } => {
            let stream_file = match &params.partial_result_token {
                None => None,
                Some(partial_result_token) => {
                    let file = temp_file(
                        &crate::server_files::get_tmp(),
                        &format!("find_refs_stream_{}_pid", ocaml_unix::getpid()),
                        ".jsonl",
                    )?;
                    let file = path::make(&file);
                    let q = watch_refs_stream_file(&file, &open_file_results);
                    Some(run_env::StreamFile {
                        file,
                        partial_result_token: partial_result_token.clone(),
                        q,
                    })
                }
            };
            // The [open_file_results] included the SymbolOccurrence text for each ref. We won't need that...
            let ide_calculated_positions: uri_map::T<Vec<pos::Absolute>> = open_file_results
                .iter()
                .map(|(uri, l)| {
                    (
                        uri.clone(),
                        l.iter()
                            .map(|search_types::find_refs::Result { name: _, pos }| pos.clone())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect();
            let shellable_type = run_env::ShellableType::FindRefs(run_env::ShelloutStandardResponse {
                symbol: full_name,
                find_refs_action: action,
                stream_file,
                hint_suffixes,
                ide_calculated_positions,
            });
            // If we reach kickoff a shell-out to hh_server, processing that response
            // also invokes respond_jsonrpc
            kickoff_shell_out_and_maybe_cancel(
                state,
                shellable_type,
                run_env::TriggeringRequest {
                    id: id.clone(),
                    metadata: metadata.clone(),
                    start_time_local_handle,
                    request: LspRequest::FindReferencesRequest(params.clone()),
                },
            )
        }
    }
}

/// Helper for sending $/progress messages for find-refs items.
fn notify_refs_file_items(
    shellout_standard_response: &run_env::ShelloutStandardResponse,
    refs: &[HalfOpenOneBased],
) {
    match &shellout_standard_response.stream_file {
        Some(run_env::StreamFile {
            partial_result_token,
            ..
        }) => {
            let notification = LspNotification::FindReferencesPartialResultNotification(
                partial_result_token.clone(),
                refs.iter().map(ide_shell_out_pos_to_lsp_location).collect(),
            );
            to_stdout(lsp_fmt::print_lsp_notification(&notification));
        }
        None => {
            log("Refs-file: notify-refs called, but no stream_file");
            crate::hack_event_logger::invariant_violation_bug(
                None,
                None,
                None,
                None,
                None,
                "refs-file: notify-refs called, but no stream file",
            );
        }
    }
}

/// This is the main handler for when the main loop detects new
/// items in the streaming-find-refs file.
pub(crate) fn handle_refs_file_items(
    state: &State,
    items: Option<Vec<HalfOpenOneBased>>,
) -> Option<ResultTelemetry> {
    use crate::hack_event_logger::invariant_violation_bug;
    match (items, state) {
        (
            Some(refs),
            State::Running(run_env::T {
                current_hh_shell:
                    Some(run_env::CurrentHhShell {
                        shellable_type: run_env::ShellableType::FindRefs(shellout_standard_response),
                        ..
                    }),
                ..
            }),
        ) => {
            notify_refs_file_items(shellout_standard_response, &refs);
            None
        }
        (
            Some(_),
            State::Running(run_env::T {
                current_hh_shell: Some(run_env::CurrentHhShell { shellable_type, .. }),
                ..
            }),
        ) => {
            let data = run_env::show_shellable_type(shellable_type);
            log(&format!("Refs-file: wrong shellable type to send refs - {}", data));
            invariant_violation_bug(
                None,
                None,
                Some(&data),
                None,
                None,
                "refs-file wrong shellale type to send refs",
            );
            None
        }
        (
            Some(_),
            State::Running(run_env::T {
                current_hh_shell: None,
                ..
            }),
        ) => {
            log("Refs-file: got items when current_hh_shell is None");
            invariant_violation_bug(
                None,
                None,
                None,
                None,
                None,
                "refs-file got items when current_hh_shell is None",
            );
            None
        }
        (Some(_), _) => {
            let data = state_to_string(state);
            log(&format!("Refs-file: unexpected items in wrong state - {}", data));
            invariant_violation_bug(
                None,
                None,
                Some(data),
                None,
                None,
                "refs-file unexpected items in wrong state",
            );
            None
        }
        (None, _) => {
            // This signals that the stream has been closed. The function [watch_refs_stream_file] only closes
            // the stream when the stream-file has been unlinked. We only unlink the file in [handle_shell_out_complete],
            // which also updates [state] to no longer be watching this file. Therefore, we should never encounter
            // a closed stream.
            log("Refs-file: unexpected end of stream");
            invariant_violation_bug(None, None, None, None, None, "refs-file unexpected end of stream");
            None
        }
    }
}

/// This is called when a shell-out to "hh --ide-find-refs-by-symbol" completes successfully
pub(crate) fn do_find_references2(
    shellout_standard_response: run_env::ShelloutStandardResponse,
    hh_locations: Vec<lsp::location::T>,
) -> Result<(LspResult, isize), Exn> {
    let run_env::ShelloutStandardResponse {
        ide_calculated_positions,
        stream_file,
        ..
    } = &shellout_standard_response;
    // lsp_locations return a file for each position. To support unsaved, edited files
    // let's discard locations for files that we previously fetched from ClientIDEDaemon.
    //
    // First: filter out locations for any where the DocumentUri.t matches a relative_path
    // in the returned map
    // Second: augment above list with values in `ide_calculated_positions`
    let hh_locations: Vec<lsp::location::T> = hh_locations
        .into_iter()
        .filter(|location| !ide_calculated_positions.contains_key(&location.uri))
        .collect();
    let ide_locations: Vec<lsp::location::T> = ide_calculated_positions
        .iter()
        .flat_map(|(lsp_uri, pos_list)| {
            let filename = lsp::string_of_uri(lsp_uri);
            pos_list
                .iter()
                .map(|pos| hack_pos_to_lsp_location(pos, &filename))
                .collect::<Vec<_>>()
        })
        .collect();
    // `List.rev_append ide_locations hh_locations`
    let all_locations: Vec<lsp::location::T> = ide_locations.into_iter().rev().chain(hh_locations).collect();
    // LSP spec explains: "If a server reports partial result via a corresponding $/progress, the whole result
    // must be reported using n $/progress notifications. The final response has to be empty in terms of result values."
    // Thus we'll give an empty response here.
    // But first, flush whatever remaining $/progress. The protocol of [watch_refs_stream_file] is that it opens an fd
    // on [file], polls the fd for changes and writes them to [q], but also polls and when [file] is unlinked then
    // it closes [q]. Thus our protocol is: unlink [file], await all items until [q] is closed, publish them
    // as $/progress, and then give an empty response.
    match stream_file {
        Some(run_env::StreamFile { file, q, .. }) => {
            let file_s = path::to_string(file);
            if let Err(e) = std::fs::remove_file(&file_s) {
                return Err(Exn::Other(exception::wrap(Raised(ocaml_unix::unix_error_to_string(
                    &e, "unlink", &file_s,
                )))));
            }
            log(&format!("Unlinked find-refs streaming file {}", file_s));
            // [Lwt_stream.to_list] awaits until the stream is closed, picking up all remaining items.
            let items_list: Vec<Vec<HalfOpenOneBased>> = lwt::yield_during(|| q.iter().collect());
            for items in &items_list {
                notify_refs_file_items(&shellout_standard_response, items);
            }
            Ok((LspResult::FindReferencesResult(vec![]), all_locations.len() as isize))
        }
        None => {
            let n = all_locations.len() as isize;
            Ok((LspResult::FindReferencesResult(all_locations), n))
        }
    }
}
