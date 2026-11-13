// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<02ff73d59e30f5c1a9032958db67ac87>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
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
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Mode {
    ForTypecheck,
    ForCodegen,
}
impl TrivialDrop for Mode {}
arena_deserializer::impl_deserialize_in_arena!(Mode);

#[derive(Clone, Debug, Deserialize, Eq, Hash, NoPosHash, Ord, PartialEq, PartialOrd, Serialize)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Env {
    pub ns_uses: s_map::SMap<String>,
    pub class_uses: s_map::SMap<String>,
    pub fun_uses: s_map::SMap<String>,
    pub const_uses: s_map::SMap<String>,
    pub name: Option<String>,
    pub mode: Mode,
    pub disable_xhp_element_mangling: bool,
}
