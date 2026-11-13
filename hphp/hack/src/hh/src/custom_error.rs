// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::custom_error`'s, re-exported: `t` is [`T`]
//! (`CustomError`), `versioned_patt_error` is [`VersionedPattError`]
//! (`Error_v1` is `ErrorV1`, `Error_v2` is `ErrorV2`) and
//! `versioned_error_message` is [`VersionedErrorMessage`] (`Message_v1` is
//! `MessageV1`). (`[@@deriving eq, show]` is their `Eq` and `Debug`.)

pub use oxidized::custom_error::*;

/// `Custom_error.t`
pub type T = CustomError;
