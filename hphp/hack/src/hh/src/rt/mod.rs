// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the infrastructure of the server layer that stands in
//! for what the OCaml gets from its runtime and process model (the socket
//! protocol, the decl epoch, heap accounting, OCaml's `Marshal`, `Arg`,
//! `Unix`, `Str`...). See `hh/PORTING.md`, "The server layer".

#[cfg(feature = "port")]
pub mod decl_epoch;
#[cfg(test)]
pub mod diagnostic_fixtures;
pub mod heap_stats;
#[cfg(any(feature = "port", feature = "server"))]
pub mod finale;
// (also `port`: `hh single` parses its options with it)
pub mod ocaml_arg;
pub mod ocaml_filename;
#[cfg(feature = "port")]
pub mod ocaml_hashtbl;
pub mod ocaml_list;
#[cfg(feature = "port")]
pub mod ocaml_option;
pub mod ocaml_stdlib;
pub mod ocaml_string;
#[cfg(any(feature = "port", feature = "server"))]
pub mod ocaml_printf;
#[cfg(any(feature = "port", feature = "server"))]
pub mod ocaml_str;
#[cfg(feature = "server")]
pub mod ocaml_sys;
#[cfg(any(feature = "port", feature = "server"))]
pub mod ocaml_unix;
#[cfg(feature = "server")]
pub mod protocol;
#[cfg(any(feature = "port", feature = "server"))]
pub mod yojson_conv;

#[cfg(feature = "port")]
pub mod ocaml_marshal;
#[cfg(any(feature = "port", feature = "server"))]
pub mod exe_suffix;
#[cfg(any(feature = "port", feature = "server"))]
pub mod quiet_panic;
#[cfg(any(feature = "port", feature = "server"))]
pub mod ocaml_exn;
