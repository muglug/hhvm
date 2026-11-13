// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<24c58490fd9f4c29128019b0c44af05a>>
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

pub type PosId = (pos_or_decl::PosOrDecl, ast_defs::Id_);

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
pub enum ArgPosition {
    Aonly,
    Afirst,
    Asecond,
}
impl TrivialDrop for ArgPosition {}
arena_deserializer::impl_deserialize_in_arena!(ArgPosition);

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
pub enum ExprDepTypeReason {
    ERexpr(isize),
    ERstatic,
    ERclass(String),
    ERparent(String),
    ERself(String),
    ERpu(String),
}

/// Reason for pessimising this return or property type
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
pub enum PessimiseReason {
    PRabstract,
    PRgenericParam,
    PRthis,
    PRgenericApply,
    PRtupleOrShape,
    PRtypeconst,
    PRcase,
    PRenum,
    PRopaque,
    PRdynamic,
    PRfun,
    PRclassptr,
    PRvoidOrNoreturn,
    PRrefinement,
    PRunionOrIntersection,
    PRxhp,
}
impl TrivialDrop for PessimiseReason {}
arena_deserializer::impl_deserialize_in_arena!(PessimiseReason);

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
pub enum BlameSource {
    BScall,
    BSlambda,
    BSassignment,
    BSoutOfScope,
}
impl TrivialDrop for BlameSource {}
arena_deserializer::impl_deserialize_in_arena!(BlameSource);

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
pub enum Blame {
    Blame(pos::Pos, BlameSource),
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
pub enum VarianceDir {
    Co,
    Contra,
}
impl TrivialDrop for VarianceDir {}
arena_deserializer::impl_deserialize_in_arena!(VarianceDir);

/// When recording the decomposition of a type during inference we want to keep
/// track of variance so we can give intuition about the direction of 'flow'.
/// In the case of invariant type parameters, we record both the fact that it was
/// invariant and the direction in which the error occurred
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
pub enum CstrVariance {
    Dir(VarianceDir),
    Inv(VarianceDir),
}

/// Shape field kinds
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
pub enum FieldKind {
    Absent,
    Optional,
    Required,
}
impl TrivialDrop for FieldKind {}
arena_deserializer::impl_deserialize_in_arena!(FieldKind);

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
pub enum CtorKind {
    CtorClass,
    CtorNewtype,
}
impl TrivialDrop for CtorKind {}
arena_deserializer::impl_deserialize_in_arena!(CtorKind);

/// Symmetric projections are those in which the same decomposition is applied
/// to both sub- and supertype during inference
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
pub enum PrjSymm {
    PrjSymmNeg,
    PrjSymmNullable,
    PrjSymmCtor(CtorKind, String, isize, CstrVariance),
    PrjSymmTuple(isize),
    PrjSymmShape(String, FieldKind, FieldKind),
    PrjSymmFnParam(isize, isize),
    PrjSymmFnParamInout(isize, isize, VarianceDir),
    PrjSymmFnRet,
    PrjSymmSupportdyn,
}

/// Asymmetric projections are those in which the same decomposition is applied
/// to only one of the sub- or supertype during inference
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
pub enum PrjAsymm {
    PrjAsymmUnion,
    PrjAsymmInter,
    PrjAsymmNeg,
    PrjAsymmNullable,
    PrjAsymmArraykey,
    PrjAsymmNum,
    PrjAsymmContains,
}
impl TrivialDrop for PrjAsymm {}
arena_deserializer::impl_deserialize_in_arena!(PrjAsymm);

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
pub enum FlowKind {
    FlowArrayGet,
    FlowAssign,
    FlowCall,
    FlowPropAccess,
    FlowConstAccess,
    FlowLocal,
    FlowFunReturn,
    FlowParamHint,
    FlowReturnExpr,
    FlowInstantiate(String),
    FlowElab,
}

/// Witness the reason for a type during decling using the position of a hint
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
pub enum WitnessDecl {
    WitnessFromDecl(pos_or_decl::PosOrDecl),
    IdxVectorFromDecl(pos_or_decl::PosOrDecl),
    IdxStringFromDecl(pos_or_decl::PosOrDecl),
    Hint(pos_or_decl::PosOrDecl),
    ClassClass(pos_or_decl::PosOrDecl, String),
    VarParamFromDecl(pos_or_decl::PosOrDecl),
    TupleFromSplat(pos_or_decl::PosOrDecl),
    VecOrDictKey(pos_or_decl::PosOrDecl),
    RetFunKindFromDecl(pos_or_decl::PosOrDecl, ast_defs::FunKind),
    InoutParam(pos_or_decl::PosOrDecl),
    TconstNoCstr(PosId),
    VarrayOrDarrayKey(pos_or_decl::PosOrDecl),
    MissingOptionalField(pos_or_decl::PosOrDecl, String),
    ImplicitUpperBound(pos_or_decl::PosOrDecl, String),
    GlobalTypeVariableGenerics(pos_or_decl::PosOrDecl, String, String),
    SolveFail(pos_or_decl::PosOrDecl),
    CstrOnGenerics(pos_or_decl::PosOrDecl, PosId),
    Enforceable(pos_or_decl::PosOrDecl),
    GlobalClassProp(pos_or_decl::PosOrDecl),
    GlobalFunParam(pos_or_decl::PosOrDecl),
    GlobalFunRet(pos_or_decl::PosOrDecl),
    DefaultCapability(pos_or_decl::PosOrDecl),
    SupportDynamicType(pos_or_decl::PosOrDecl),
    PessimisedInout(pos_or_decl::PosOrDecl),
    PessimisedReturn(pos_or_decl::PosOrDecl, PessimiseReason),
    PessimisedProp(pos_or_decl::PosOrDecl, PessimiseReason),
    PessimisedThis(pos_or_decl::PosOrDecl),
    IllegalRecursiveType(pos_or_decl::PosOrDecl, String),
    SupportDynamicTypeAssume(pos_or_decl::PosOrDecl),
    PolymorphicTypeParam(pos_or_decl::PosOrDecl, String, String, isize),
    EnforcedType(pos_or_decl::PosOrDecl),
}

/// Axioms are information about types provided by the user in class or type
/// parameter declarations. We make use of this information during subtype
/// constraint simplification
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
pub enum Axiom {
    Extends,
    UpperBound(String),
    LowerBound,
}

/// The reason why something is expected to have a certain type
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
pub enum T_ {
    /// Lift a decl-time witness into a reason
    FromWitnessDecl(WitnessDecl),
    Instantiate {
        type__: Box<T_>,
        var_name: String,
        var: Box<T_>,
    },
    NoReason,
    Invalid,
    Typeconst(
        Box<T_>,
        (pos_or_decl::PosOrDecl, String),
        lazy::Lazy<String>,
        Box<T_>,
    ),
    ExprDepType(Box<T_>, pos_or_decl::PosOrDecl, ExprDepTypeReason),
}

pub type Reason = T_;

pub type DeclT = T_;

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
pub enum Ureason {
    URnone,
    URassign,
    URassignInout,
    URhint,
    URreturn,
    URforeach,
    URthrow,
    URvector,
    URkey(String),
    URvalue(String),
    URawait,
    URdelay,
    URyield,
    /// Name of XHP class, Name of XHP attribute
    URxhp(String, String),
    URxhpSpread,
    URindex(String),
    URelement(String),
    URparam,
    URparamInout,
    URarrayValue,
    URpairValue,
    URtupleAccess,
    URtupleOOB,
    URpairAccess,
    URnewtypeCstr,
    URclassReq,
    URenum,
    URenumInclude,
    URenumCstr,
    URenumUnderlying,
    URenumIncompatibleCstr,
    URtypeconstCstr,
    URsubsumeTconstCstr,
    URsubsumeTconstAssign,
    URclone,
    URusing,
    URstrConcat,
    URstrInterp,
    URdynamicProp,
    URlabel,
    URcondition,
}
