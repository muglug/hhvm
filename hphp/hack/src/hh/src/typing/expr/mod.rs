// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 2515-9032): module `Expr`
//! (`Typing.Expr`), split over three files that are one OCaml module: each
//! part starts with `use super::*;`, so that the functions of `Expr` call each
//! other unqualified, as in OCaml, and with `use crate::typing::prelude::*;`.
//! See `../mod.rs`.

mod part_a;
mod part_b;
mod part_c;

pub use part_a::*;
pub use part_b::*;
pub(crate) use part_c::*;
