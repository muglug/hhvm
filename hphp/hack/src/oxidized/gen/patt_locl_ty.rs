// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<62ad3965e3c2979dd13f79405bed2492>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

#[allow(unused_imports)]
use crate::*;

/// Defines pattern matches over a subset of Hack types
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
pub enum PattLoclTy {
    /// Matches type-constructor like types e.g. class, vec_or_dict and newtypes
    Apply {
        name: patt_name::PattName,
        params: Box<Params>,
    },
    /// Matches Hack primitives
    Prim(Prim),
    /// Matches Hack shapes
    Shape(ShapeFields),
    /// Matches Hack optional types
    Option(Box<PattLoclTy>),
    /// Matches Hack tuples
    Tuple(Vec<PattLoclTy>),
    /// Matches dynamic
    Dynamic,
    /// Matches non-null
    Nonnull,
    /// Matches any Hack type
    Any,
    /// Matches either the first pattern or, if that does not match, the second
    Or {
        fst: Box<PattLoclTy>,
        snd: Box<PattLoclTy>,
    },
    /// Match the provided pattern and bind the result to the supplied variable name
    As {
        lbl: patt_var::PattVar,
        patt: Box<PattLoclTy>,
    },
    /// Mark invalid patterns
    Invalid(Vec<validation_err::ValidationErr>, Box<PattLoclTy>),
}

/// Defines pattern matches over list of Hack types appearing as type parameters
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
pub enum Params {
    /// Matches the empty parameter list
    Nil,
    /// Matches any parameter list
    Wildcard,
    /// Mathes a parameter list where the first element matches [patt_hd] and
    /// the remaining parameters match [patt_tl]
    Cons { hd: PattLoclTy, tl: Box<Params> },
    /// Matches a parameter list where at least one Hint matches the supplied
    /// pattern
    Exists(PattLoclTy),
}

/// Match Hack primitive types
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
pub enum Prim {
    Null,
    Void,
    Int,
    Bool,
    Float,
    String,
    Resource,
    Num,
    Arraykey,
    Noreturn,
}
impl TrivialDrop for Prim {}
arena_deserializer::impl_deserialize_in_arena!(Prim);

/// Matches the fields of a Hack shape
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
pub enum ShapeFields {
    /// Matches a shape which contains the a field matching the given [shape_field]
    /// and matches the remaining [shape_fields]
    Fld {
        fld: ShapeField,
        rest: Box<ShapeFields>,
    },
    /// Matches any shape which contains fields which have not already been matched
    Open,
    /// Matches a shape in which all other fields have already been matched
    Closed,
}

/// Matches an individual Hack shape field
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
pub struct ShapeField {
    pub lbl: ShapeLabel,
    pub optional: bool,
    pub patt: Box<PattLoclTy>,
}

/// Matches a Hack shape label
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
pub enum ShapeLabel {
    RegGroupLabel(String),
    StrLbl(String),
    CConstLbl { cls_nm: String, cnst_nm: String },
}
