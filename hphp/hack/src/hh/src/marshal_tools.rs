// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/marshal_tools/marshal_tools.ml`. See `hh/PORTING.md`.
//!
//! The description of an exception that crossed a process boundary, which
//! `Jsonrpc` and `Client_lsp` exchange, and the preamble of a marshalled
//! value (the errors file of `Server_progress` and the handshake of the
//! monitor, `crate::rt::protocol::ocaml_frame`, have it). The rest of the
//! module (the marshalling of values over file descriptors) has no use in the
//! Rust process model, where threads exchange Rust values.

use crate::exception;

/// We want to marshal exceptions (or at least their message+stacktrace) over
/// the wire. This type ensures that no one will attempt to pattern-match on
/// the thing we marshal: 'Values of extensible variant types, for example
/// exceptions (of extensible type exn), returned by the unmarhsaller should
/// not be pattern-matched over, because unmarshalling does not preserve the
/// information required for matching their constructors.'
/// <https://caml.inria.fr/pub/docs/manual-ocaml/libref/Marshal.html>
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

/// `Marshal_tools.preamble_start_sentinel`
pub const PREAMBLE_START_SENTINEL: u8 = 0x8E;

/// `Marshal_tools.expected_preamble_size`: the sentinel and 4 bytes of size.
pub const EXPECTED_PREAMBLE_SIZE: usize = 5;

/// `Marshal_tools.make_preamble size`: the sentinel, then the size on 4
/// bytes, most significant first. (`Payload_Size_Too_Large_Exception` from
/// 2^32-1 bytes cannot happen: `server_progress::errors_file::assert_payload_size_ok`
/// stops at 4,000,000,000.)
pub fn make_preamble(size: usize) -> [u8; EXPECTED_PREAMBLE_SIZE] {
    let s = (size as u32).to_be_bytes();
    [PREAMBLE_START_SENTINEL, s[0], s[1], s[2], s[3]]
}

/// `Marshal_tools.parse_preamble`: `Malformed_Preamble_Exception` (a panic,
/// as OCaml does not catch it) if the sentinel is not there.
pub fn parse_preamble(preamble: &[u8]) -> usize {
    if preamble.len() != EXPECTED_PREAMBLE_SIZE || preamble[0] != PREAMBLE_START_SENTINEL {
        panic!("Marshal_tools.Malformed_Preamble_Exception")
    }
    preamble[1..]
        .iter()
        .fold(0usize, |acc, b| acc * 256 + *b as usize)
}
