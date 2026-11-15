// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the `Secondary` module of `typing/typing_error.ml`.
//!
//! The naming conventions are described in `crate::typing_error`.

use oxidized::message::Message;
use oxidized::pos_or_decl::PosOrDecl;

pub use super::InstanceOrStatic;
use super::Lazy;
pub use super::ReadOrWrite;
use super::error;
use super::primary;
use crate::typing_reason;

// -- Polymorphic variants of the fields of `T` --------------------------------
//
// `<Constructor><Field>`; see `crate::typing_error`.

/// ``kind: [ `class_constant | `class_typeconst | `class_variable | `static_method ]``
pub type SmemberNotFoundKind = primary::SmemberNotFoundKind;
/// ``hint: ([ `instance | `static ] * Pos_or_decl.t * string) option``
pub type SmemberNotFoundHint = InstanceOrStatic;
/// ``ctxt: [ `read | `write ]``
pub type NonObjectMemberCtxt = ReadOrWrite;
/// ``kind: [ `class_typeconst | `method_ | `property ]``
pub type NonObjectMemberKind = primary::NonObjectMemberKind;

/// ``kind: [ `fn | `fn_return | `param ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadonlyMismatchKind {
    /// `` `fn ``
    Fn,
    FnReturn,
    Param,
}

/// ``kind: [ `constant | `method_ | `property | `typeconst ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractConcreteOverrideKind {
    Constant,
    Method,
    Property,
    Typeconst,
}

/// ``cstr: [ `As | `Super ] * Pos_or_decl.t``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViolatedRefinementConstraintCstr {
    As,
    Super,
}
pub type AsOrSuper = ViolatedRefinementConstraintCstr;
/// Short for [`ViolatedRefinementConstraintCstr`]
pub type RefinementConstraintKind = ViolatedRefinementConstraintCstr;

/// Specific error information which needs to be given a primary position from
/// the AST being typed to be transformable into a user error.
/// This can be done via applying a `Reasons_callback.t` using
/// `apply_reasons`.
/// `Typing_error.Secondary.Shape_splat_cycle`
pub mod shape_splat_cycle {
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_defs_core::Ty;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum EdgeKind {
        DirectUpper,
        IndirectUpper,
        NestedUpper,
        NestedLower,
    }

    #[derive(Clone, Debug)]
    pub struct Edge {
        pub pos: PosOrDecl,
        pub source: Ty,
        pub target: Ty,
        pub kind: EdgeKind,
    }
}

#[derive(Clone, Debug)]
pub enum T {
    OfError(Box<error::T>),
    // == Primary and secondary ================================================
    SmemberNotFound {
        pos: PosOrDecl,
        kind: SmemberNotFoundKind,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
    },
    TypeArityMismatch {
        pos: PosOrDecl,
        actual: isize,
        decl_pos: PosOrDecl,
        expected: isize,
    },
    TypingTooManyArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    TypingTooFewArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    NonObjectMember {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
        ctxt: ReadOrWrite,
        member_name: String,
        kind: NonObjectMemberKind,
    },
    RigidTvarEscape {
        pos: PosOrDecl,
        name: String,
    },
    ConcreteConstInterfaceOverride {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        parent_origin: String,
        name: String,
    },
    InterfaceOrTraitConstMultipleDefs {
        pos: PosOrDecl,
        origin: String,
        name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    InterfaceTypeconstMultipleDefs {
        pos: PosOrDecl,
        origin: String,
        is_abstract: bool,
        name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    VisibilityExtends {
        pos: PosOrDecl,
        vis: String,
        parent_pos: PosOrDecl,
        parent_vis: String,
    },
    VisibilityOverrideInternal {
        pos: PosOrDecl,
        module_name: Option<String>,
        parent_pos: PosOrDecl,
        parent_module: String,
    },
    AbstractTconstNotAllowed {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        tconst_name: String,
    },
    MissingConstructor(PosOrDecl),
    MissingField {
        pos: PosOrDecl,
        name: String,
        decl_pos: PosOrDecl,
        reason_sub: typing_reason::T,
        reason_super: typing_reason::T,
    },
    ShapeFieldsUnknown {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    SplatMayRequireFields {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        name: Option<String>,
    },
    SplatFieldNotKnown {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        name: String,
        field: String,
    },
    UnsupportedCyclicShapeSplatBounds {
        pos: PosOrDecl,
        cycle: Vec<shape_splat_cycle::Edge>,
    },
    AcceptDisposableInvariant {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    InvalidDestructure {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
    },
    UnpackArrayRequiredArgument {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    UnpackArrayVariadicArgument {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    FunTooManyArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    FunTooFewArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    FunUnexpectedNonvariadic {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    FunVariadicityHhVsPhp56 {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    FunExtraNamedArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        extra_names: Vec<String>,
    },
    FunMissingNamedArgs {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        missing_names: Vec<String>,
    },
    FunParamRequiredButExpectedOptional {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        /// If empty, this is a positional parameter
        param_names: Vec<String>,
    },
    RequiredFieldIsOptional {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        def_pos: PosOrDecl,
        name: String,
        reason_sub: typing_reason::T,
        reason_super: typing_reason::T,
    },
    ReturnDisposableMismatch {
        pos_sub: PosOrDecl,
        is_marked_return_disposable: bool,
        pos_super: PosOrDecl,
    },
    OverridingPropConstMismatch {
        pos: PosOrDecl,
        is_const: bool,
        parent_pos: PosOrDecl,
        parent_is_const: bool,
    },
    OverrideFinal {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    OverrideTestsBypassVisibility {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    AbstractTestsBypassVisibilityMissingAttr {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    OverrideAsync {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    OverrideLsb {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    MultipleConcreteDefs {
        pos: PosOrDecl,
        name: String,
        origin: String,
        class_name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    CyclicEnumConstraint(PosOrDecl),
    InoutnessMismatch {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    BadLateinitOverride {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        parent_is_lateinit: bool,
    },
    BadMethodOverride {
        pos: PosOrDecl,
        member_name: String,
    },
    BadMemberOverrideNotSubtype {
        is_method: bool,
        class_name: String,
        parent_name: String,
        parent_type: Lazy<String>,
        member_pos: PosOrDecl,
        member_name: String,
        member_type: Lazy<String>,
        origin_name: String,
        origin_type: Lazy<String>,
        member_parent_pos: PosOrDecl,
        member_parent_type: Lazy<String>,
        member_parent_origin: String,
        member_parent_origin_type: Lazy<String>,
    },
    BadPropOverride {
        pos: PosOrDecl,
        member_name: String,
    },
    BadXhpAttrRequiredOverride {
        pos: PosOrDecl,
        tag: String,
        parent_pos: PosOrDecl,
        parent_tag: String,
    },
    CoeffectSubtyping {
        pos: PosOrDecl,
        cap: Lazy<String>,
        pos_expected: PosOrDecl,
        cap_expected: Lazy<String>,
    },
    OverrideMethodSupportDynamicType {
        pos: PosOrDecl,
        method_name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    ReadonlyMismatch {
        pos: PosOrDecl,
        kind: ReadonlyMismatchKind,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    },
    RequirePackageMismatch {
        pos: PosOrDecl,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    },
    NotSubDynamic {
        pos: PosOrDecl,
        ty_name: Lazy<String>,
        dynamic_part: Lazy<Vec<Message<PosOrDecl>>>,
    },
    SubtypingError {
        cstrs: Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>>,
        ty_sub: crate::typing_defs_constraints::InternalType,
        ty_sup: crate::typing_defs_constraints::InternalType,
        is_coeffect: bool,
    },
    MethodNotDynamicallyCallable {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    ThisFinal {
        pos_sub: PosOrDecl,
        pos_super: PosOrDecl,
        class_name: String,
    },
    TypeconstConcreteConcreteOverride {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    AbstractConcreteOverride {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        kind: AbstractConcreteOverrideKind,
    },
    OverrideNoDefaultTypeconst {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    UnsupportedRefinement(PosOrDecl),
    SplatNotAShape(PosOrDecl),
    MissingClassConstant {
        pos: PosOrDecl,
        class_name: String,
        const_name: String,
    },
    InvalidRefinedConstKind {
        pos: PosOrDecl,
        class_name: String,
        const_name: String,
        correct_kind: String,
        wrong_kind: String,
    },
    InexactTconstAccess(PosOrDecl, (PosOrDecl, String)),
    ViolatedRefinementConstraint {
        cstr: (ViolatedRefinementConstraintCstr, PosOrDecl),
    },
    UnknownLabel {
        enum_name: String,
        decl_pos: PosOrDecl,
        most_similar: Option<(String, PosOrDecl)>,
    },
    HigherRankTparamEscape {
        tvar_pos: PosOrDecl,
        pos_with_generic: PosOrDecl,
        generic_reason: typing_reason::T,
        generic_name: Option<String>,
    },
    OverrideSealed {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
}
