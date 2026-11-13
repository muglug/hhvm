// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `patt_locl_ty.ml`. See `hh/PORTING.md`.
//!
//! Defines pattern matches over a subset of Hack types.
//!
//! The types are `oxidized::patt_locl_ty`'s, re-exported: `t` is [`T`]
//! (`PattLoclTy`), and `params`, `prim`, `shape_fields`, `shape_field` and
//! `shape_label` are [`Params`], [`Prim`], [`ShapeFields`], [`ShapeField`]
//! and [`ShapeLabel`]. The inline records lose the prefix their fields share
//! (`Apply { patt_name; patt_params }` is `Apply { name, params }`).
//! (`[@@deriving compare, eq, sexp, show]` is their `Ord`, `Eq` and `Debug`.)

pub use oxidized::patt_locl_ty::*;

/// `Patt_locl_ty.t`
pub type T = PattLoclTy;
