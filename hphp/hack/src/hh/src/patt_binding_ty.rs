// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `patt_binding_ty.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::patt_binding_ty`'s, re-exported (`[@@deriving
//! compare, eq, sexp, show]` is its `Ord`, `Eq` and `Debug`).

pub use oxidized::patt_binding_ty::*;

/// `Patt_binding_ty.t`
pub type T = PattBindingTy;
