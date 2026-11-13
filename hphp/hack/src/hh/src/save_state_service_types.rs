// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/save_state_service_types.ml`. See
//! `hh/PORTING.md`.
//!
//! The module is only its types, ported in full by the client-connection
//! assignment (D1), which needs `save_naming_result` (the result of
//! `Server_command_types.SAVE_NAMING`). `Warnings_saved_state.t` is
//! `oxidized::warnings_saved_state_impl::WarningsSavedState`.

use oxidized::warnings_saved_state_impl::WarningsSavedState;
use serde::Deserialize;
use serde::Serialize;

use crate::relative_path;

/// An alias for the errors type that we marshal to and unmarshal from the saved state.
/// Keep this in sync with saved_states.rs:dump_error_files
pub type SavedStateErrors = relative_path::set::T;

#[derive(Clone, Debug)]
pub struct OldIssues {
    pub old_errors: SavedStateErrors,
    pub old_warnings: WarningsSavedState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaveStateResult {
    pub dep_table_edges_added: isize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaveNamingResult {
    pub nt_files_added: isize,
    pub nt_symbols_added: isize,
}
