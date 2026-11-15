// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/collections/i_set.ml`: `Set.Make (Int_key)`. See
//! `hh/PORTING.md`.
//!
//! The set is an `im::OrdSet` (`i_set::T`): the functions of `Stdlib.Set`
//! are its methods.
//!
//! Not here: `pp`, `show` and `to_string` (they need the boxes of OCaml's
//! `Format`) and `yojson_of_t`.

pub type T = im::OrdSet<isize>;

pub type Elt = isize;
