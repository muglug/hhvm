// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error/error_message.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::error_message`'s, re-exported: `t` is [`T`]
//! (`ErrorMessage`, whose field is `message`) and `elem` is [`Elem`]
//! (`Ty_var` is `TyVar`, ...). (`[@@deriving eq, show]` is their `Eq` and
//! `Debug`.)

pub use oxidized::error_message::*;

/// `Error_message.t`
pub type T = ErrorMessage;
