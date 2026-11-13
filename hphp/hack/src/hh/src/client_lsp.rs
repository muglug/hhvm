// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_lsp.ml`. See `hh/PORTING.md`.
//!
//! Only `type args` is ported so far, by the `hh_client` command line (A3):
//! `Client_args` builds it for `hh_client lsp`. The rest of the module (the
//! language server) belongs to the ClientLsp assignments (G3a, G3b).

use crate::path;

/// `Client_lsp.args`
#[derive(Clone, Debug, PartialEq)]
pub struct Args {
    /// The source where the client was spawned from, i.e. nuclide, vim, emacs, etc.
    pub from: String,
    /// --config overrides at the command-line
    pub config: Vec<(String, String)>,
    pub disable_format_on_save: bool,
    pub ignore_hh_version: bool,
    pub naming_table: Option<String>,
    pub warnings_saved_state_path: Option<path::T>,
    /// Notebook mode. The *only* thing this does is filter out error messages that are not relevant for notebooks.
    /// Important:
    /// 1. The *key* difference between notebooks and IDEs is that top-level statements are allowed
    /// 2. To preserve (1) and keep our testing surface area small: do not propagate this option outside of Client_lsp:
    ///    parsing, elab, type-checking, etc. should not know about notebooks.
    pub notebook_mode: bool,
    /// Extra logging, including logs per LSP message (voluminous!)
    pub verbose: bool,
    /// clientLsp only ever uses the root path provided to us in the initialize request.
    /// This field here isn't that! it's a record of what root was derived upon launch
    /// (well before the initialize request), either from an argument if supplied, or
    /// otherwise by searching from the CWD. We use this field solely to validate
    /// whether there's a mismatch between the project root implied by how we launched,
    /// and the project root supplied by initialize, in case we want to warn about
    /// any difference.
    pub root_from_cli: path::T,
}
