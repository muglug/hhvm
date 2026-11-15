// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error/patt_name.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::patt_name`'s, re-exported: `t` is [`T`]
//! (`PattName`) and `namespace` is [`Namespace`]. (`[@@deriving compare, eq,
//! sexp, show]` is their `Ord`, `Eq` and `Debug`.)

pub use oxidized::patt_name::*;

/// `Patt_name.t`
pub type T = PattName;
