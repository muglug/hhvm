// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_decompress_zhhdg.ml`. See `hh/PORTING.md`.
//!
//! Only `type env` is ported so far, by the `hh_client` command line (A3):
//! `Client_args` builds it for `hh_client decompress-zhhdg`. `main` (running
//! the depgraph decompressor) belongs to the saved-state production
//! assignment (C4).

/// `Client_decompress_zhhdg.env`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Env {
    pub path: String,
    pub from: String,
}
