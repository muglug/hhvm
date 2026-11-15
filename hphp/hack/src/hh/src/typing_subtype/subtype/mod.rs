// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 802-7656): module
//! `Subtype` (`Typing_subtype.Subtype`), split over three files that are one
//! OCaml module: each part starts with `use super::*;`, so that the functions
//! of `Subtype` call each other unqualified, as in OCaml, and with
//! `use crate::typing_subtype::prelude::*;`. See `../mod.rs`.

mod part_a;
mod part_b;
mod part_c;

pub use part_a::*;
pub use part_b::*;
pub(crate) use part_c::*;
