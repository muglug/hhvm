// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `custom_error/patt_naming_error.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::patt_naming_error`'s, re-exported: `t` is [`T`]
//! (`PattNamingError`) and `patt_name_context` is [`PattNameContext`]. The
//! inline records lose the prefix their fields share (`Unbound_name {
//! patt_name_context; patt_name }` is `UnboundName { name_context, name }`).
//! (`[@@deriving eq, show]` is their `Eq` and `Debug`.)

pub use oxidized::patt_naming_error::*;

/// `Patt_naming_error.t`
pub type T = PattNamingError;
