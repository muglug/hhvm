// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Marshal_tools` (`utils/marshal_tools/marshal_tools.ml`). See
//! `hh/PORTING.md`.
//!
//! Only the description of an exception that crossed a process boundary,
//! which `Jsonrpc` and `Client_lsp` exchange. The rest of the module (the
//! preambles and the marshalling of values over file descriptors) has no use
//! in the Rust process model, where threads exchange Rust values.

use crate::exception;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RemoteExceptionData {
    pub message: String,
    pub stack: String,
}

pub fn of_exception(e: &exception::T) -> RemoteExceptionData {
    RemoteExceptionData {
        message: exception::get_ctor_string(e),
        stack: exception::get_backtrace_string(e),
    }
}
