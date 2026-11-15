// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `Client_rage`. See `hh/PORTING.md`.
//!
//! `client/rage/dune` links Meta's `Client_rage` when `src/facebook` exists,
//! and `stubs/client_rage.ml` otherwise: this is the stub, in full. `hh_client
//! rage` asks its questions (`Client_args.parse_rage_args`), then `main`
//! exits with `No_error` without doing anything else.

use crate::exit;
use crate::exit_status;
use crate::path;
use crate::server_local_config;

/// `Client_rage.env`
#[derive(Clone, Debug, PartialEq)]
pub struct Env {
    pub root: path::T,
    pub from: String,
    pub rageid: Option<String>,
    pub desc: String,
    pub lsp_log: Option<String>,
}

/// `let main _ _ = Exit.exit Exit_status.No_error`
pub fn main(_env: &Env, _local_config: &server_local_config::T) -> ! {
    exit::exit(None, None, None, None, exit_status::T::NoError)
}

/// Does nothing.
pub fn verify_typechecker_err_src() {}
