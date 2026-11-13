// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<29226b911573751192b6469082c7954a>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

pub type Fixmes = i_map::IMap<i_map::IMap<pos::Pos>>;

#[derive(
    Clone,
    Debug,
    Default,
    Deserialize,
    Eq,
    Hash,
    NoPosHash,
    Ord,
    PartialEq,
    PartialOrd,
    Serialize
)]
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct ScouredComments {
    pub comments: Vec<(pos::Pos, prim_defs::Comment)>,
    pub fixmes: Fixmes,
    pub ignores: Fixmes,
    pub misuses: Fixmes,
    pub error_pos: Vec<pos::Pos>,
    pub bad_ignore_pos: Vec<pos::Pos>,
}
