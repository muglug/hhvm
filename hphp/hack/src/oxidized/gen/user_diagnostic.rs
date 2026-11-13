// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<a3b5ed99c9d0b7ea1f981b17a664df39>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Eq,
    EqModuloPos,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Severity {
    Warning {
        is_trusted: bool,
    },
    Err,
}

#[derive(Clone, Debug, Deserialize, Eq, EqModuloPos, Hash, NoPosHash, PartialEq, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct UserDiagnostic<PrimPos, Pos> {
    pub severity: Severity,
    pub code: isize,
    pub claim: message::Message<PrimPos>,
    pub reasons: Vec<message::Message<Pos>>,
    pub explanation: explanation::Explanation<Pos>,
    pub quickfixes: Vec<quickfix::Quickfix<PrimPos>>,
    pub custom_msgs: Vec<String>,
    pub is_fixmed: bool,
    pub function_pos: Option<PrimPos>,
}
