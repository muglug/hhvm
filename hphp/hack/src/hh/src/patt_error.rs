// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `patt_error.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::patt_error`'s, re-exported (`[@@deriving eq,
//! show]` is its `Eq` and `Debug`).

pub use oxidized::patt_error::*;

/// `Patt_error.t`
pub type T = PattError;
