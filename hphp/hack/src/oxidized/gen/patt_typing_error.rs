// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<55c1b72bbc0716f271770aef5c1aedda>>
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
pub enum PattTypingError {
    Primary(Primary),
    Apply {
        cb: Callback,
        err: Box<PattTypingError>,
    },
    ApplyReasons {
        rsns_cb: ReasonsCallback,
        secondary: Box<Secondary>,
    },
    Or {
        fst: Box<PattTypingError>,
        snd: Box<PattTypingError>,
    },
    InvalidTyping {
        errs: Vec<validation_err::ValidationErr>,
        patt: Box<PattTypingError>,
    },
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
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum Primary {
    AnyPrim,
    MemberNotFound {
        is_static: Option<StaticPattern>,
        kind: MemberKindPattern,
        class_name: patt_name::PattName,
        member_name: patt_member_name::PattMemberName,
        visibility: Option<VisibilityPattern>,
    },
    /// Matches any of the other package primary errors
    AnyPkg {
        use_file: patt_file::PattFile,
        decl_file: patt_file::PattFile,
    },
    CrossPkgAccess {
        use_file: patt_file::PattFile,
        decl_file: patt_file::PattFile,
    },
    CrossPkgAccessWithRequirepackage {
        use_file: patt_file::PattFile,
        decl_file: patt_file::PattFile,
    },
    CrossPkgAccessWithSoftrequirepackage {
        use_file: patt_file::PattFile,
        decl_file: patt_file::PattFile,
    },
    SoftIncludedAccess {
        use_file: patt_file::PattFile,
        decl_file: patt_file::PattFile,
    },
    ExpressionTreeUnsupportedOperator {
        class_name: patt_name::PattName,
        member_name: patt_member_name::PattMemberName,
    },
}

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
pub enum StaticPattern {
    StaticOnly,
    InstanceOnly,
}
impl TrivialDrop for StaticPattern {}
arena_deserializer::impl_deserialize_in_arena!(StaticPattern);

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
pub enum MemberKindPattern {
    AnyMemberKind,
    MethodOnly,
    PropertyOnly,
    ClassConstantOnly,
    ClassTypeconstOnly,
}
impl TrivialDrop for MemberKindPattern {}
arena_deserializer::impl_deserialize_in_arena!(MemberKindPattern);

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
pub enum VisibilityPattern {
    AnyVisibility,
    PublicOnly,
    PrivateOnly,
    ProtectedOnly,
    InternalOnly,
}
impl TrivialDrop for VisibilityPattern {}
arena_deserializer::impl_deserialize_in_arena!(VisibilityPattern);

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
pub enum Secondary {
    OfError(PattTypingError),
    ViolatedConstraint {
        cstr: patt_string::PattString,
        ty_sub: patt_locl_ty::PattLoclTy,
        ty_sup: patt_locl_ty::PattLoclTy,
    },
    SubtypingError {
        sub: patt_locl_ty::PattLoclTy,
        sup: patt_locl_ty::PattLoclTy,
    },
    AnySnd,
}

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
pub enum Callback {
    AnyCallback,
}
impl TrivialDrop for Callback {}
arena_deserializer::impl_deserialize_in_arena!(Callback);

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
pub enum ReasonsCallback {
    AnyReasonsCallback,
}
impl TrivialDrop for ReasonsCallback {}
arena_deserializer::impl_deserialize_in_arena!(ReasonsCallback);
