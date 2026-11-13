// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<1c8aacfcf98419919edbc8c488c38d87>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

pub type Hash = isize;

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
    #[serde(default)]
    pub fun_tast_hashes: s_map::SMap<Hash>,
    #[serde(default)]
    pub class_tast_hashes: s_map::SMap<Hash>,
    #[serde(default)]
    pub typedef_tast_hashes: s_map::SMap<Hash>,
    #[serde(default)]
    pub gconst_tast_hashes: s_map::SMap<Hash>,
    #[serde(default)]
    pub module_tast_hashes: s_map::SMap<Hash>,
}

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
pub struct FileInfo {
    pub tast_hashes: ByNames,
    pub error_hashes: i_set::ISet,
}

pub type TastHashes = relative_path::map::Map<FileInfo>;
