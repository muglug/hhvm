// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<8890579a36717deee759cc488da574e1>>
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
pub enum Visibility {
    Vprivate,
    Vpublic,
    Vinternal,
    Vprotected,
    VprotectedInternal,
}
impl TrivialDrop for Visibility {}
arena_deserializer::impl_deserialize_in_arena!(Visibility);

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
pub enum ReturnOnlyHint {
    Hvoid,
    Hnoreturn,
}
impl TrivialDrop for ReturnOnlyHint {}
arena_deserializer::impl_deserialize_in_arena!(ReturnOnlyHint);

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
pub enum UnsupportedFeature {
    FtWhereConstraints,
    FtConstraints,
    FtReification,
    FtUserAttrs,
    FtVariance,
}
impl TrivialDrop for UnsupportedFeature {}
arena_deserializer::impl_deserialize_in_arena!(UnsupportedFeature);

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
pub enum NamingError {
    UnexpectedArrow { pos: pos::Pos, cname: String },
    MissingArrow { pos: pos::Pos, cname: String },
    DisallowedXhpType { pos: pos::Pos, ty_name: String },
    NameIsReserved { pos: pos::Pos, name: String },
    DollardollarUnused(pos::Pos),
    MethodNameAlreadyBound { pos: pos::Pos, meth_name: String },
    ErrorNameAlreadyBound {
        pos: pos::Pos,
        name: String,
        prev_pos: pos::Pos,
    },
    UnboundName {
        pos: pos::Pos,
        name: String,
        kind: name_context::NameContext,
    },
    InvalidFunPointer { pos: pos::Pos, name: String },
    Undefined {
        pos: pos::Pos,
        var_name: String,
        did_you_mean: Option<(String, pos::Pos)>,
    },
    UndefinedInExprTree {
        pos: pos::Pos,
        var_name: String,
        dsl: Option<String>,
        did_you_mean: Option<(String, pos::Pos)>,
    },
    ThisReserved(pos::Pos),
    StartWithT(pos::Pos),
    AlreadyBound { pos: pos::Pos, name: String },
    UnexpectedTypedef {
        pos: pos::Pos,
        decl_pos: pos::Pos,
        expected_kind: name_context::NameContext,
    },
    FieldNameAlreadyBound(pos::Pos),
    TypedOpenShapeDisallowed(pos::Pos),
    NamedVariadicTypeDisallowed(pos::Pos),
    VariadicNamedParameterDisallowed(pos::Pos),
    TraitSelfShapeKey { pos: pos::Pos, key_name: String },
    PrimitiveTopLevel(pos::Pos),
    PrimitiveInvalidAlias {
        pos: pos::Pos,
        ty_name_used: String,
        ty_name_canon: String,
    },
    DynamicNewInStrictMode(pos::Pos),
    InvalidTypeAccessRoot { pos: pos::Pos, id: Option<String> },
    InvalidTypeAccessInWhere(pos::Pos),
    DuplicateUserAttribute {
        pos: pos::Pos,
        attr_name: String,
        prev_pos: pos::Pos,
    },
    InvalidMemoizeLabel { pos: pos::Pos, attr_name: String },
    UnboundAttributeName {
        pos: pos::Pos,
        attr_name: String,
        closest_attr_name: Option<String>,
    },
    ThisNoArgument(pos::Pos),
    ObjectCast(pos::Pos),
    ThisHintOutsideClass(pos::Pos),
    ParentOutsideClass(pos::Pos),
    SelfOutsideClass(pos::Pos),
    StaticOutsideClass(pos::Pos),
    ThisTypeForbidden {
        pos: pos::Pos,
        in_extends: bool,
        in_req_extends: bool,
    },
    NonstaticPropertyWithLsb(pos::Pos),
    ClassnameParam(pos::Pos),
    TparamAppliedToType { pos: pos::Pos, tparam_name: String },
    ShadowedTparam {
        pos: pos::Pos,
        tparam_name: String,
        prev_pos: pos::Pos,
    },
    MissingTypehint(pos::Pos),
    ExpectedVariable(pos::Pos),
    TooManyArguments(pos::Pos),
    TooFewArguments(pos::Pos),
    ExpectedCollection { pos: pos::Pos, cname: String },
    IllegalCLASS(pos::Pos),
    IllegalTRAIT(pos::Pos),
    IllegalMemberVariableClass(pos::Pos),
    IllegalMethCaller(pos::Pos),
    IllegalClassMeth(pos::Pos),
    ClassMethNonFinalSelf { pos: pos::Pos, class_name: String },
    ClassMethNonFinalCLASS {
        pos: pos::Pos,
        class_name: String,
        is_trait: bool,
    },
    ConstWithoutTypehint {
        pos: pos::Pos,
        const_name: String,
        ty_name: String,
    },
    PropWithoutTypehint {
        pos: pos::Pos,
        prop_name: String,
        vis: Visibility,
    },
    IllegalConstant(pos::Pos),
    InvalidRequireImplements(pos::Pos),
    InvalidRequireExtends(pos::Pos),
    InvalidRequireClass(pos::Pos),
    InvalidRequireConstraint(pos::Pos),
    DidYouMean {
        pos: pos::Pos,
        name: String,
        suggest_pos: pos::Pos,
        suggest_name: String,
    },
    UsingInternalClass { pos: pos::Pos, class_name: String },
    TooFewTypeArguments(pos::Pos),
    DynamicClassNameInStrictMode(pos::Pos),
    XhpOptionalRequiredAttr { pos: pos::Pos, attr_name: String },
    WildcardHintDisallowed(pos::Pos),
    WildcardTparamDisallowed(pos::Pos),
    IllegalUseOfDynamicallyCallable {
        attr_pos: pos::Pos,
        meth_pos: pos::Pos,
        vis: Visibility,
    },
    ParentInFunctionPointer {
        pos: pos::Pos,
        meth_name: String,
        parent_name: Option<String>,
    },
    SelfInNonFinalFunctionPointer {
        pos: pos::Pos,
        meth_name: String,
        class_name: Option<String>,
    },
    InvalidWildcardContext(pos::Pos),
    ReturnOnlyTypehint { pos: pos::Pos, kind: ReturnOnlyHint },
    UnexpectedTypeArguments(pos::Pos),
    TooManyTypeArguments(pos::Pos),
    ThisAsLexicalVariable(pos::Pos),
    ExplicitConsistentConstructor {
        pos: pos::Pos,
        classish_kind: ast_defs::ClassishKind,
    },
    ModuleDeclarationOutsideAllowedFiles(pos::Pos),
    InternalModuleLevelTrait(pos::Pos),
    DynamicMethodAccess(pos::Pos),
    DeprecatedUse { pos: pos::Pos, fn_name: String },
    UnnecessaryAttribute {
        pos: pos::Pos,
        attr: String,
        class_pos: pos::Pos,
        class_name: String,
        suggestion: Option<String>,
    },
    DynamicHintDisallowed(pos::Pos),
    ToplevelStatement(pos::Pos),
    AttributeOutsideAllowedFiles(pos::Pos),
    PolymorphicLambdaMissingReturnHint(pos::Pos),
    PolymorphicLambdaMissingParamHint { pos: pos::Pos, name: String },
}
