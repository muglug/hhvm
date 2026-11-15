// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/collections/i_map.ml`: `Wrapped_map.Make (Int_key)`.
//! See `hh/PORTING.md`.
//!
//! The map is an `im::OrdMap` (`i_map::T<A>`): the functions of
//! `Stdlib.Map` are its methods, and the ones `Wrapped_map` adds are here.
//!
//! Not here: `pp` and `show` (they need the boxes of OCaml's `Format`) and
//! `yojson_of_t`.

pub use crate::wrapped_map::*;

pub type T<A> = im::OrdMap<isize, A>;

pub type Key = isize;
