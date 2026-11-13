// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<25c1816d0cc193d72ecd3fafb2d7c58b>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
pub use pos::Pos;
use serde::Deserialize;
use serde::Serialize;
use transform_markers::TransformMarkers;

pub use crate::shape_map;
#[allow(unused_imports)]
use crate::*;

pub type Id_ = String;

#[derive(
    Clone,
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
pub struct Id(pub Pos, pub Id_);

pub type Pstring = (Pos, String);

pub type ByteString = String;

pub type PositionedByteString = (Pos, bstr::BString);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum ShapeFieldName {
    SFlitStr(PositionedByteString),
    SFclassname(Id),
    SFclassConst(Id, Pstring),
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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Variance {
    Covariant,
    Contravariant,
    Invariant,
}
impl TrivialDrop for Variance {}
arena_deserializer::impl_deserialize_in_arena!(Variance);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum ConstraintKind {
    ConstraintAs,
    ConstraintEq,
    ConstraintSuper,
}
impl TrivialDrop for ConstraintKind {}
arena_deserializer::impl_deserialize_in_arena!(ConstraintKind);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Abstraction {
    Concrete,
    Abstract,
}
impl TrivialDrop for Abstraction {}
arena_deserializer::impl_deserialize_in_arena!(Abstraction);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum ClassishKind {
    /// Kind for `class` and `abstract class`
    Cclass(Abstraction),
    /// Kind for `interface`
    Cinterface,
    /// Kind for `trait`
    Ctrait,
    /// Kind for `enum`
    Cenum,
    /// Kind for `enum class` and `abstract enum class`.
    /// See https://docs.hhvm.com/hack/built-in-types/enum-class
    CenumClass(Abstraction),
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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum ParamKind {
    /// Contains the position for an entire `inout` annotated expression, e.g.:
    ///
    ///   foo(inout $bar);
    ///       ^^^^^^^^^^
    Pinout(Pos),
    Pnormal,
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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum ReadonlyKind {
    Readonly,
}
impl TrivialDrop for ReadonlyKind {}
arena_deserializer::impl_deserialize_in_arena!(ReadonlyKind);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum ParamNamed {
    ParamNamed,
}
impl TrivialDrop for ParamNamed {}
arena_deserializer::impl_deserialize_in_arena!(ParamNamed);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum OptionalKind {
    Optional,
}
impl TrivialDrop for OptionalKind {}
arena_deserializer::impl_deserialize_in_arena!(OptionalKind);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum SplatKind {
    Splat,
}
impl TrivialDrop for SplatKind {}
arena_deserializer::impl_deserialize_in_arena!(SplatKind);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum OperatorNullFlavor {
    Regular,
    Nullsafe,
}
impl TrivialDrop for OperatorNullFlavor {}
arena_deserializer::impl_deserialize_in_arena!(OperatorNullFlavor);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum PropOrMethod {
    IsProp,
    IsMethod,
}
impl TrivialDrop for PropOrMethod {}
arena_deserializer::impl_deserialize_in_arena!(PropOrMethod);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum FunKind {
    FSync,
    FAsync,
    FGenerator,
    FAsyncGenerator,
}
impl TrivialDrop for FunKind {}
arena_deserializer::impl_deserialize_in_arena!(FunKind);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Bop {
    /// Addition: x + y
    Plus,
    /// Subtraction: x - y
    Minus,
    /// Multiplication: x * y
    Star,
    /// Division: x / y
    Slash,
    /// Value/coercing equality: x == y
    Eqeq,
    /// Same-type-and-value equality: x === y
    Eqeqeq,
    /// Exponent: x ** y
    Starstar,
    /// Value inquality: x != y
    Diff,
    /// Not-same-type-and-value-equality: x !== y
    Diff2,
    /// Logical AND: x && y
    Ampamp,
    /// Logical OR: x || y
    Barbar,
    /// Less than: x < y
    Lt,
    /// Less than or equal to: x <= y
    Lte,
    /// Greater than: x > y
    Gt,
    /// Greater than or equal to: x >= y
    Gte,
    /// String concatenation: x . y
    Dot,
    /// Bitwise AND: x & y
    Amp,
    /// Bitwise OR: x | y
    Bar,
    /// Bitwise left shift: x << y
    Ltlt,
    /// Bitwise right shift: x >> y
    Gtgt,
    /// Modulo: x % y
    Percent,
    /// Bitwise XOR: x ^ y
    Xor,
    /// Spaceship operator: x <=> y
    Cmp,
    /// Coalesce: x ?? y
    QuestionQuestion,
}
impl TrivialDrop for Bop {}
arena_deserializer::impl_deserialize_in_arena!(Bop);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Uop {
    /// Bitwise negation: ~x
    Utild,
    /// Logical not: !b
    Unot,
    /// Unary plus: +x
    Uplus,
    /// Unary minus: -x
    Uminus,
    /// Unary increment: ++i
    Uincr,
    /// Unary decrement: --i
    Udecr,
    /// Unary postfix increment: i++
    Upincr,
    /// Unary postfix decrement: i--
    Updecr,
    /// Error control/Silence (ignore) expections: @e
    Usilence,
}
impl TrivialDrop for Uop {}
arena_deserializer::impl_deserialize_in_arena!(Uop);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Visibility {
    Private,
    Public,
    Protected,
    Internal,
    ProtectedInternal,
}
impl TrivialDrop for Visibility {}
arena_deserializer::impl_deserialize_in_arena!(Visibility);

/// Literal values that can occur in XHP enum properties.
///
/// class :my-xhp-class {
///   attribute enum {'big', 'small'} my-prop;
/// }
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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(C, u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::ToOcamlRep))]
pub enum XhpEnumValue {
    XEVInt(isize),
    XEVString(String),
}

/// Hack's primitive types (as the typechecker understands them).
///
/// Used in the AST of typehints (Aast_defs.Hprim) and in the representation of
/// types (Typing_defs.Tprim).
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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum Tprim {
    Tnull,
    Tvoid,
    Tint,
    Tbool,
    Tfloat,
    Tresource,
    Tnum,
    Tarraykey,
    Tnoreturn,
}
impl TrivialDrop for Tprim {}
arena_deserializer::impl_deserialize_in_arena!(Tprim);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum TypedefVisibility {
    Transparent,
    Opaque,
    OpaqueModule,
}
impl TrivialDrop for TypedefVisibility {}
arena_deserializer::impl_deserialize_in_arena!(TypedefVisibility);

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
    Serialize,
    TransformMarkers
)]
#[transform(opaque)]
#[repr(u8)]
#[cfg_attr(feature = "ocamlrep", derive(ocamlrep::FromOcamlRep, ocamlrep::FromOcamlRepIn, ocamlrep::ToOcamlRep))]
pub enum ReifyKind {
    Erased,
    SoftReified,
    Reified,
}
impl TrivialDrop for ReifyKind {}
arena_deserializer::impl_deserialize_in_arena!(ReifyKind);
