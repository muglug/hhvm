// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `S_map` (`utils/collections/s_map.ml`): `Wrapped_map.Make (String_key)`.
//! See `hh/PORTING.md`.
//!
//! The map is an `im::OrdMap` (`s_map::T<A>`): the functions of
//! `Stdlib.Map` are its methods, and the ones `Wrapped_map` adds are here.
//!
//! Not here: `pp` and `show` (they need the boxes of OCaml's `Format`),
//! `hash_fold_t` and `yojson_of_t`.

pub use crate::wrapped_map::*;

pub type T<A> = im::OrdMap<String, A>;

pub type Key = String;
