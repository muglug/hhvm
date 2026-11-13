// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<d28b09746c83797e7f0dc786ca8c2f35>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

pub use error_hash_set::*;

#[allow(unused_imports)]
use crate::*;

/// A 63-bit hash (the most significant bit is erased, as OCaml ints were).
pub type ErrorHash = isize;

pub type Path = String;
