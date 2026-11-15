// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_error_utils.ml`. See `hh/PORTING.md`.
//!
//! The OCaml file is one module of 7.9k lines; here each of its parts is a
//! file, re-exported so that paths follow the OCaml module structure:
//!
//! - `common`, `eval_result`: `Common`, `Eval_result`
//! - `eval_primary`: `Eval_primary` (its nested modules, and its functions in
//!   two halves)
//! - `eval_error`: `Eval_error`, `Eval_secondary`, `Eval_callback`,
//!   `Eval_reasons_callback` and the functions after them (`add_typing_error`,
//!   ...), which are re-exported from here.

pub mod common;
pub mod eval_error;
pub mod eval_primary;
pub mod eval_result;

pub use eval_error::*;
