// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`, in part (the module is split: see
//! `client_lsp.rs`): `do_topLevelDefNameAtPos`.

#![allow(unused_imports)]

use super::*;

/// `do_topLevelDefNameAtPos`
pub(crate) fn do_top_level_def_name_at_pos(
    ide_service: &client_ide_service::T,
    tracking_id: &str,
    ref_unblocked_time: &mut f64,
    editor_open_files: &uri_map::T<text_document_item::T>,
    params: &lsp::top_level_def_name_at_pos::Params,
) -> Result<lsp::top_level_def_name_at_pos::Result, Exn> {
    let (document, location) = get_document_location(editor_open_files, params)?;
    ide_rpc(
        ide_service,
        tracking_id,
        ref_unblocked_time,
        client_ide_message::request::top_level_def_name_at_pos(document, location),
    )
}
