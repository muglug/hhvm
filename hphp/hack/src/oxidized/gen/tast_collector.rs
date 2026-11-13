// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<b73eb81117f77fb37b140dc8179738d8>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

pub type Tast = String;

#[derive(
    Clone,
    Debug,
    Default,
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
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct ByNames {
    pub fun_tasts: s_map::SMap<Tast>,
    pub class_tasts: s_map::SMap<Tast>,
    pub typedef_tasts: s_map::SMap<Tast>,
    pub gconst_tasts: s_map::SMap<Tast>,
    pub module_tasts: s_map::SMap<Tast>,
}

pub type TastCollector = relative_path::map::Map<ByNames>;
