// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_rage_types.ml`. See `hh/PORTING.md`.
//!
//! The module is only its types: the result of `Server_command_types.RAGE`.

use serde::Deserialize;
use serde::Serialize;

/// To make the rage output more useful, it's broken into rageItems.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RageItem {
    pub title: String,
    pub data: String,
}

pub type Result = Vec<RageItem>;
