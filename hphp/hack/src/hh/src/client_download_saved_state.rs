// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_download_saved_state.ml`. See `hh/PORTING.md`.
//!
//! Only `type env` is ported so far, by the `hh_client` command line (A3):
//! `Client_args` builds it for `hh_client download-saved-state`. The command
//! itself downloads from Manifold, which is Meta-only (design, section 1.1).

use crate::path;

/// `Client_download_saved_state.env`
#[derive(Clone, Debug, PartialEq)]
pub struct Env {
    pub root: path::T,
    pub from: String,
    pub saved_state_manifold_api_key: Option<String>,
    pub should_save_replay: bool,
    pub replay_token: Option<String>,
}
