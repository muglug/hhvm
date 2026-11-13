// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.
//
// @generated SignedSource<<0530ca8f1d87a4bc381d7646717c833d>>
//
// To regenerate this file, run:
//   buck run @fbcode//mode/dev-nosan-lg fbcode//hphp/hack/src:oxidized_regen

use arena_trait::TrivialDrop;
use eq_modulo_pos::EqModuloPos;
use no_pos_hash::NoPosHash;
use serde::Deserialize;
use serde::Serialize;

pub use crate::error_codes::NastCheck as Error_code;
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
pub enum Verb {
    VreqImplement,
    Vimplement,
}
impl TrivialDrop for Verb {}
arena_deserializer::impl_deserialize_in_arena!(Verb);

/// The construct that asked whether a package is deployed. Rendered (with
/// styling) by the error constructor.
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
pub enum PackageConstruct {
    PackageExpression,
    RequirePackageAttribute(String),
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
pub enum NastCheckError {
    RepeatedRecordFieldName {
        pos: pos::Pos,
        name: String,
        prev_pos: pos_or_decl::PosOrDecl,
    },
    DynamicallyCallableReified(pos::Pos),
    NoConstructParent(pos::Pos),
    NonstaticMethodInAbstractFinalClass(pos::Pos),
    ConstructorRequired {
        pos: pos::Pos,
        class_name: String,
        prop_names: Vec<String>,
    },
    NotInitialized {
        pos: pos::Pos,
        class_name: String,
        props: Vec<(pos_or_decl::PosOrDecl, String)>,
    },
    ThisEscapesOverridableConstructor {
        pos: pos::Pos,
        class_name: String,
    },
    CallBeforeInit {
        pos: pos::Pos,
        prop_name: String,
    },
    AbstractWithBody(pos::Pos),
    NotAbstractWithoutTypeconst(pos::Pos),
    TypeconstDependsOnExternalTparam {
        pos: pos::Pos,
        ext_pos: pos::Pos,
        ext_name: String,
    },
    InterfaceWithPartialTypeconst(pos::Pos),
    PartiallyAbstractTypeconstDefinition(pos::Pos),
    RefinementInTypestruct {
        pos: pos::Pos,
        kind: String,
    },
    MultipleXhpCategory(pos::Pos),
    ReturnInFinally(pos::Pos),
    ToplevelBreak(pos::Pos),
    ToplevelContinue(pos::Pos),
    ContinueInSwitch(pos::Pos),
    AwaitInSyncFunction {
        pos: pos::Pos,
        func_pos: Option<pos::Pos>,
        keyword: String,
    },
    InterfaceUsesTrait(pos::Pos),
    Magic {
        pos: pos::Pos,
        meth_name: String,
    },
    NonInterface {
        pos: pos::Pos,
        name: String,
        verb: Verb,
    },
    ToStringReturnsString(pos::Pos),
    ToStringVisibility(pos::Pos),
    UsesNonTrait {
        pos: pos::Pos,
        name: String,
        kind: String,
    },
    RequiresNonClass {
        pos: pos::Pos,
        name: String,
        kind: String,
        is_interface: bool,
        is_req_this_as_check: bool,
    },
    RequiresFinalClass {
        pos: pos::Pos,
        name: String,
        is_req_this_as_check: bool,
    },
    AbstractBody(pos::Pos),
    InterfaceWithMemberVariable(pos::Pos),
    InterfaceWithStaticMemberVariable(pos::Pos),
    IllegalFunctionName {
        pos: pos::Pos,
        name: String,
    },
    EntrypointArguments(pos::Pos),
    EntrypointGenerics(pos::Pos),
    VariadicMemoize(pos::Pos),
    AbstractMethodMemoize(pos::Pos),
    InstancePropertyInAbstractFinalClass(pos::Pos),
    InoutParamsSpecial(pos::Pos),
    InoutParamsMemoize {
        pos: pos::Pos,
        param_pos: pos::Pos,
    },
    InoutInTransformedPseudofunction {
        pos: pos::Pos,
        fn_name: String,
    },
    NamedInTransformedPseudofunction {
        pos: pos::Pos,
        fn_name: String,
    },
    ReadingFromAppend(pos::Pos),
    ListRvalue(pos::Pos),
    PlaceholderRead(pos::Pos),
    PlaceholderInoutWrite {
        pos: pos::Pos,
        param_pos: pos::Pos,
    },
    IllegalDestructor(pos::Pos),
    IllegalContext {
        pos: pos::Pos,
        name: String,
    },
    CaseFallthrough {
        switch_pos: pos::Pos,
        case_pos: pos::Pos,
        next_pos: Option<pos::Pos>,
    },
    DefaultFallthrough(pos::Pos),
    PhpLambdaDisallowed(pos::Pos),
    InternalMethodWithInvalidVisibility {
        pos: pos::Pos,
        vis: ast_defs::Visibility,
    },
    PrivateAndFinal(pos::Pos),
    InternalMemberInsidePublicTrait {
        member_pos: pos::Pos,
        trait_pos: pos::Pos,
        is_method: bool,
    },
    AttributeConflictingMemoize {
        pos: pos::Pos,
        second_pos: pos::Pos,
    },
    SoftInternalWithoutInternal(pos::Pos),
    WrongExpressionKindBuiltinAttribute {
        pos: pos::Pos,
        attr_name: String,
        expr_kind: String,
    },
    AttributeTooManyArguments {
        pos: pos::Pos,
        name: String,
        expected: isize,
    },
    AttributeTooFewArguments {
        pos: pos::Pos,
        name: String,
        expected: isize,
    },
    AttributeNotExactNumberOfArgs {
        pos: pos::Pos,
        name: String,
        actual: isize,
        expected: isize,
    },
    AttributeParamType {
        pos: pos::Pos,
        x: String,
    },
    AttributeNoAutoDynamic(pos::Pos),
    AttributeImplementedByRestriction {
        restriction: String,
        pos: pos::Pos,
    },
    GenericAtRuntime {
        pos: pos::Pos,
        prefix: String,
    },
    GenericsNotAllowed(pos::Pos),
    LocalVariableModifiedAndUsed {
        pos: pos::Pos,
        pos_useds: Vec<pos::Pos>,
    },
    LocalVariableModifiedTwice {
        pos: pos::Pos,
        pos_modifieds: Vec<pos::Pos>,
    },
    AssignDuringCase(pos::Pos),
    ReadBeforeWrite {
        pos: pos::Pos,
        member_name: String,
    },
    LateinitWithDefault(pos::Pos),
    MissingAssign(pos::Pos),
    CloneReturnType(pos::Pos),
    ClassSealedWithTrait {
        pos: pos::Pos,
        class_name: String,
        trait_name: String,
    },
    RequirePackageStrictInclusion {
        required_pos: pos::Pos,
        required: String,
        def_pos: pos_or_decl::PosOrDecl,
        current: String,
        current_pos: pos::Pos,
        attribute_name: String,
        current_package_assignment_kind: String,
    },
    PackageExpressionStrictInclusion {
        pkg_pos: pos::Pos,
        pkg: String,
        def_pos: pos_or_decl::PosOrDecl,
        current: String,
        current_pos: pos::Pos,
        current_package_assignment_kind: String,
    },
    ObservationNotAllowedForPackage {
        pos: pos::Pos,
        pkg: String,
        def_pos: pos_or_decl::PosOrDecl,
        construct: PackageConstruct,
    },
    OverrideNotAllowedForPackage {
        pos: pos::Pos,
        pkg: String,
        def_pos: pos_or_decl::PosOrDecl,
        attr: String,
    },
    PackageOverrideTargetNotIncluded {
        override_pos: pos::Pos,
        target: String,
        path_package: String,
        path_package_pos: pos_or_decl::PosOrDecl,
    },
    RedundantPackageOverride {
        pos: pos::Pos,
        pkg: String,
        def_pos: pos_or_decl::PosOrDecl,
    },
}

/// Context for package strict inclusion errors
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
pub enum PackageStrictInclusionContext {
    CtxRequirePackage(String),
    CtxPackageExpression,
}
