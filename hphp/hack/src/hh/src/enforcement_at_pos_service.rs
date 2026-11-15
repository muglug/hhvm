// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `enforcement_at_pos_service.ml` (types only, as the OCaml). See
//! `hh/PORTING.md`.

pub struct EnforcedType {
    pub ty_str: String,
    pub ty_json: crate::yojson::safe::T,
}

pub enum Enforcement {
    Enforced(Vec<EnforcedType>),
    Unenforced,
}

pub type Result = Option<Enforcement>;
