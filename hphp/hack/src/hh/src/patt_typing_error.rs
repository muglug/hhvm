// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `patt_typing_error.ml`. See `hh/PORTING.md`.
//!
//! The types are `oxidized::patt_typing_error`'s, re-exported: `t` is [`T`]
//! (`PattTypingError`), and `primary`, `static_pattern`,
//! `member_kind_pattern`, `visibility_pattern`, `secondary`, `callback` and
//! `reasons_callback` are [`Primary`], [`StaticPattern`],
//! [`MemberKindPattern`], [`VisibilityPattern`], [`Secondary`], [`Callback`]
//! and [`ReasonsCallback`]. The inline records lose the prefix their fields
//! share (`Apply { patt_cb; patt_err }` is `Apply { cb, err }`,
//! `Subtyping_error { patt_ty_sub; patt_ty_sup }` is `SubtypingError { sub,
//! sup }`). (`[@@deriving eq, show]` is their `Eq` and `Debug`.)

pub use oxidized::patt_typing_error::*;

/// `Patt_typing_error.t`
pub type T = PattTypingError;
