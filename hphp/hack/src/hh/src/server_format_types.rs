// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_format_types.ml` (types only; the
//! module has nothing else); `ide_format` uses them.

use crate::file_content::position;
use crate::ide_api_types;

/// `action`: file contents, offset start, offset end.
pub type Action = (String, isize, isize);

/// `result`
pub type Result = std::result::Result<String, String>;

/// `ide_action`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdeAction {
    Document,
    Range(ide_api_types::Range),
    Position(position::T),
}

/// `ide_response`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdeResponse {
    pub new_text: String,
    /// what range was actually replaced?
    pub range: ide_api_types::Range,
}

/// `ide_result`
pub type IdeResult = std::result::Result<IdeResponse, String>;
