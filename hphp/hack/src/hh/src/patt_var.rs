// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error/patt_var.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::patt_var`'s, re-exported (`[@@deriving compare,
//! eq, sexp, show]` is its `Ord`, `Eq` and `Debug`).

pub use oxidized::patt_var::*;

/// `Patt_var.t`
pub type T = PattVar;
