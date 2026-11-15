// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_goToImplementation` and `do_goToImplementation2`.

#![allow(unused_imports)]

use super::*;

/// `do_goToImplementation`: responds itself (or leaves the response to the
/// shell-out it kicks off), and returns the telemetry.
#[allow(clippy::too_many_arguments)]
pub(crate) fn do_go_to_implementation(
    state: &mut State,
    ide_service: &client_ide_service::T,
    metadata: &IncomingMetadata,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::implementation::Params,
    id: &LspId,
) -> Result<ResultTelemetry, Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    let all_open_documents = get_documents_from_open_files(editor_open_files)?;
    let response = ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::go_to_implementation(document, location, all_open_documents),
    )?;
    match response {
        client_ide_message::GoToImplResult::InvalidSymbolImpl => {
            respond_jsonrpc(
                PoweredBy::ServerlessIde,
                id,
                &LspResult::ImplementationResult(vec![]),
            );
            Ok(make_result_telemetry(None, None, 0))
        }
        client_ide_message::GoToImplResult::GoToImplSuccess(symbol, find_refs_action, ide_calculated_positions) => {
            let shellable_type = run_env::ShellableType::GoToImpl(run_env::ShelloutStandardResponse {
                symbol,
                find_refs_action,
                stream_file: None,
                hint_suffixes: vec![],
                ide_calculated_positions,
            });
            let start_time_local_handle = ocaml_unix::gettimeofday();
            kickoff_shell_out_and_maybe_cancel(
                state,
                shellable_type,
                run_env::TriggeringRequest {
                    id: id.clone(),
                    metadata: metadata.clone(),
                    start_time_local_handle,
                    request: LspRequest::ImplementationRequest(params.clone()),
                },
            )
        }
    }
}

/// This is called when a shellout to "hh --ide-go-to-impl" completes successfully
pub(crate) fn do_go_to_implementation2(
    ide_calculated_positions: uri_map::T<Vec<pos::Absolute>>,
    hh_locations: Vec<lsp::location::T>,
) -> Result<(LspResult, isize), Exn> {
    // reject all server-supplied locations for files that we calculated in ClientIdeDaemon, then join the lists
    let filtered_list = hh_locations
        .into_iter()
        .filter(|loc| !ide_calculated_positions.contains_key(&loc.uri))
        .collect::<Vec<_>>();
    // (`UriMap.elements`: a fold that conses, so in decreasing order of the uris.)
    let ide_supplied_positions = uri_map::elements(&ide_calculated_positions).into_iter().flat_map(|(_uri, pos_list)| {
        pos_list
            .iter()
            .map(|pos| hack_pos_to_lsp_location(pos, &pos::filename(pos)))
            .collect::<Vec<_>>()
    });
    let locations: Vec<lsp::location::T> = filtered_list.into_iter().chain(ide_supplied_positions).collect();
    let n = locations.len() as isize;
    Ok((LspResult::ImplementationResult(locations), n))
}
