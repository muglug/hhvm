// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<47d7503830c471429ca0926f1e8e4e03>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
pub use pos::Pos;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

#[derive(
    Clone,
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
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum Entity {
    Class(String),
    Function(String),
}

#[derive(
    Clone,
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
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct EntityPos(pub Pos, pub Entity);

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
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum LoggedType {
    Like,
    NonLike,
    Mixed,
    SupportdynOfMixed,
    Dynamic,
    Tany,
    CapturedLike,
}
impl TrivialDrop for LoggedType {}
arena_deserializer::impl_deserialize_in_arena!(LoggedType);

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
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Category {
    Expression,
    ObjGetReceiver,
    ClassGetReceiver,
    ClassConstReceiver,
    Property,
    Parameter,
    Return,
}
impl TrivialDrop for Category {}
arena_deserializer::impl_deserialize_in_arena!(Category);

#[derive(
    Clone,
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
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Count {
    /// The position of the entity for which this count holds
    pub entity_pos: EntityPos,
    /// The type that this count is for
    pub counted_type: LoggedType,
    /// Program construct that produces this type
    pub category: Category,
    /// The actual count
    pub value: isize,
}

/// Summary for one file, only counting like types.
#[derive(
    Clone,
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
#[repr(C)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub struct Summary {
    pub like_types: isize,
    pub captured_like_types: isize,
    pub non_like_types: isize,
    pub mixed: isize,
    pub supportdyn_of_mixed: isize,
    pub dynamic: isize,
    pub dynamic_obj: isize,
    pub like_obj: isize,
    pub non_like_obj: isize,
    pub tany: isize,
}

pub type TypeCounter = relative_path::map::Map<Summary>;
