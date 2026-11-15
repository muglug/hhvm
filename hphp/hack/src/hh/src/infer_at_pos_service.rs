// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/infer_at_pos_service.ml`. See `hh/PORTING.md`.
//!
//! The module is only its type: the result of
//! `Server_command_types.INFER_TYPE`.

/// The first string is the pretty-printed type, the second is the JSON
pub type Result = Option<(String, String)>;
