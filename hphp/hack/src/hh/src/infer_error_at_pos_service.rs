// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/infer_error_at_pos_service.ml`. See
//! `hh/PORTING.md`.
//!
//! The module is only its types: the result of
//! `Server_command_types.INFER_TYPE_ERROR`.

use serde::Deserialize;
use serde::Serialize;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct T {
    pub actual_ty_string: String,
    pub actual_ty_json: String,
    pub expected_ty_string: String,
    pub expected_ty_json: String,
}

pub type Result = Option<T>;
