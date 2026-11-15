// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/tast_holes_service.ml`. See `hh/PORTING.md`.
//!
//! The module is only its types: the result of
//! `Server_command_types.TAST_HOLES` and `TAST_HOLES_BATCH`. `X.t` is [`T`] (`include X`); its derived `compare`
//! is [`compare`], which orders `Set`.

use std::cmp::Ordering;

use oxidized::pos::Pos;
use serde::Deserialize;
use serde::Serialize;

/// `X.t` (`include X`)
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct T {
    pub actual_ty_string: String,
    pub actual_ty_json: String,
    pub expected_ty_string: String,
    pub expected_ty_json: String,
    pub pos: Pos,
}

/// `X.compare` (`[@@deriving ord]`): the fields in order; positions with
/// `Pos.compare`.
pub fn compare(a: &T, b: &T) -> Ordering {
    a.actual_ty_string
        .cmp(&b.actual_ty_string)
        .then_with(|| a.actual_ty_json.cmp(&b.actual_ty_json))
        .then_with(|| a.expected_ty_string.cmp(&b.expected_ty_string))
        .then_with(|| a.expected_ty_json.cmp(&b.expected_ty_json))
        .then_with(|| crate::pos::compare(&a.pos, &b.pos))
}

impl PartialOrd for T {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(compare(self, other))
    }
}

impl Ord for T {
    fn cmp(&self, other: &Self) -> Ordering {
        compare(self, other)
    }
}

/// `module Set = Set.Make (X)`
pub mod set {
    pub type T = std::collections::BTreeSet<super::T>;
}

pub type Result = Vec<T>;
