// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The infrastructure of the server layer that has no OCaml counterpart: the
//! process model, the socket protocol, file-watcher backends, the emulation of
//! OCaml's `Arg`. See `hh/PORTING.md`, "The server layer".

#[cfg(feature = "server")]
pub mod client_provider;
#[cfg(feature = "server")]
pub mod daemonize;
#[cfg(feature = "port")]
pub mod decl_epoch;
#[cfg(test)]
pub mod diagnostic_fixtures;
#[cfg(any(feature = "port", feature = "server"))]
pub mod finale;
#[cfg(feature = "server")]
pub mod notifier_native;
#[cfg(feature = "server")]
pub mod notifier_watchman;
#[cfg(feature = "server")]
pub mod ocaml_arg;
pub mod ocaml_filename;
pub mod ocaml_list;
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
#[cfg(any(feature = "port", feature = "server"))]
pub mod yojson_ext;

// Registrations by assignment (as in `lib.rs`): append at the end of your own
// block, before its `end` line. Modules registered before W0b stay above.
//
//
// ---- MEMO: invalidation ----
// ---- end MEMO ----
//
//
// ---- MON: monitor ----
#[cfg(feature = "server")]
pub mod fd_passing;
// ---- end MON ----
//
//
// ---- SRV: server loop ----
// ---- end SRV ----
//
//
// ---- ERR: streaming errors ----
#[cfg(feature = "port")]
pub mod ocaml_marshal;
// ---- end ERR ----
//
//
// ---- SUFFIX: suffix of the running executable, sibling binaries ----
#[cfg(any(feature = "port", feature = "server"))]
pub mod exe_suffix;
// ---- end SUFFIX ----
