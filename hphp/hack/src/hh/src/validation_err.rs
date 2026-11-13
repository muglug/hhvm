// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `validation_err.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::validation_err`'s, re-exported (`[@@deriving
//! compare, eq, sexp, show]` is its `Ord`, `Eq` and `Debug`).

pub use oxidized::validation_err::*;

/// `Validation_err.t`
pub type T = ValidationErr;
