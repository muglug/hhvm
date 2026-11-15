// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the `Primary` module of `typing/typing_error.ml`: specific error
//! information readily transformable into a user error.
//!
//! The naming conventions are described in `crate::typing_error`.

use oxidized::ast_defs::ClassishKind;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Quickfix;
use oxidized::s_set::SSet;

pub use super::InstanceOrStatic;
use super::Lazy;
pub use super::MethOrProp;
pub use super::MethodOrProperty;
pub use super::ReadOrWrite;

/// `Typing_error.Primary.Shape`
pub mod shape {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;
    pub use crate::typing_error::NothingOrUndefined;

    /// ``reason: [ `Nothing of Pos_or_decl.t Message.t list Lazy.t | `Undefined ]``,
    /// the type of the `reason` of three constructors
    pub type Reason = NothingOrUndefined;
    /// ``reason: [ `Nothing of Pos_or_decl.t Message.t list Lazy.t | `Undefined ]``
    pub type ShapesKeyExistsAlwaysFalseReason = NothingOrUndefined;
    /// ``reason: [ `Nothing of Pos_or_decl.t Message.t list Lazy.t | `Undefined ]``
    pub type ShapesMethodAccessWithNonExistentFieldReason = NothingOrUndefined;
    /// ``reason: [ `Nothing of Pos_or_decl.t Message.t list Lazy.t | `Undefined ]``
    pub type ShapesAccessWithNonExistentFieldReason = NothingOrUndefined;

    /// ``const_kind: [ `Enum | `ClassConst ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ShapeKeyConstValueUnresolvableConstKind {
        Enum,
        ClassConst,
    }

    #[derive(Clone, Debug)]
    pub enum T {
        InvalidShapeFieldName {
            pos: Pos,
            is_empty: bool,
        },
        InvalidShapeFieldLiteral {
            pos: Pos,
            witness_pos: Pos,
        },
        InvalidShapeFieldConst {
            pos: Pos,
            witness_pos: Pos,
        },
        AbstractShapeFieldConst {
            pos: Pos,
            decl_pos: PosOrDecl,
            name: String,
        },
        ShapeFieldClassConstMissingShapeKeyAttribute {
            pos: Pos,
            decl_pos: PosOrDecl,
            class_name: String,
            const_name: String,
        },
        ShapeKeyConstValueUnresolvable {
            pos: Pos,
            reason_pos: PosOrDecl,
            class_name: String,
            const_name: String,
            const_kind: ShapeKeyConstValueUnresolvableConstKind,
        },
        ShapeKeyClassConstNameofSelfInTrait {
            pos: Pos,
            value_pos: Pos,
            class_name: String,
            const_name: String,
        },
        ShapeKeyClassConstIsAbstract {
            pos: Pos,
            decl_pos: Pos,
            class_name: String,
            const_name: String,
        },
        InvalidShapeFieldType {
            pos: Pos,
            ty_pos: PosOrDecl,
            ty_name: Lazy<String>,
            trail: Vec<PosOrDecl>,
        },
        ShapeFieldClassMismatch {
            pos: Pos,
            class_name: String,
            witness_pos: Pos,
            witness_class_name: String,
        },
        ShapeFieldTypeMismatch {
            pos: Pos,
            ty_name: Lazy<String>,
            witness_pos: Pos,
            witness_ty_name: Lazy<String>,
        },
        InvalidShapeRemoveKey(Pos),
        ShapesKeyExistsAlwaysTrue {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
        },
        ShapesKeyExistsAlwaysFalse {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
            reason: NothingOrUndefined,
        },
        ShapesMethodAccessWithNonExistentField {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
            method_name: String,
            reason: NothingOrUndefined,
        },
        ShapesAccessWithNonExistentField {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
            reason: NothingOrUndefined,
        },
    }
}

/// `Typing_error.Primary.Shape_and_tuple_destructure`
pub mod shape_and_tuple_destructure {
    use oxidized::pos::Pos;

    #[derive(Clone, Debug)]
    pub enum T {
        MissingEllipsis(Pos),
        MissingRequiredFields {
            pos: Pos,
            field_names: String,
        },
        UnknownField {
            pos: Pos,
            field_name: String,
        },
        TupleArityMismatch {
            pos: Pos,
            pat_arity: isize,
            tuple_arity: isize,
        },
        TupleArityExceeds {
            pos: Pos,
            pat_arity: isize,
            tuple_arity: isize,
        },
        TupleArityUnionConflict(Pos),
    }
}

/// `Typing_error.Primary.Switch`
pub mod switch {
    use oxidized::pos::Pos;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        SwitchNonexhaustive {
            switch_pos: Pos,
            missing: Lazy<Vec<String>>,
            scrutinee_pos: Pos,
            scrutinee_type: Lazy<String>,
        },
        SwitchNeedsDefault {
            switch_pos: Pos,
            scrutinee_pos: Pos,
            scrutinee_type: Lazy<String>,
        },
    }
}

/// `Typing_error.Primary.Enum`
pub mod enum_ {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    /// `Typing_error.Primary.Enum.Const`
    pub mod const_ {
        #[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum T {
            Null,
            Label {
                class_: String,
                /// `const`
                const_: String,
            },
            Bool(bool),
            Int(Option<String>),
            String(Option<String>),
        }

        pub fn to_user_string(t: &T) -> String {
            match t {
                T::Null => "null".to_string(),
                // you need the class field for distinguish identically named constants
                // from different classes in hash, eq, and ord but for printing, we just
                // show only const namae instead
                T::Label { class_: _, const_ } => const_.clone(),
                T::Bool(true) => "true".to_string(),
                T::Bool(false) => "false".to_string(),
                T::Int(None) => "int".to_string(),
                T::Int(Some(num)) => num.clone(),
                T::String(None) => "string".to_string(),
                T::String(Some(str)) => str.clone(),
            }
        }

        pub fn if_int<A>(lit: &T, then_: impl Fn(&str) -> A, else_: A) -> A {
            match lit {
                T::Int(Some(num)) => then_(num),
                T::Int(None) | T::Null | T::Label { .. } | T::Bool(_) | T::String(_) => else_,
            }
        }

        pub fn opt_to_user_string(t: &Option<T>) -> String {
            match t {
                None => "default".to_string(),
                Some(t) => to_user_string(t),
            }
        }
    }

    pub use self::const_ as r#const;

    #[derive(Clone, Debug)]
    pub enum T {
        EnumSwitchRedundant {
            pos: Pos,
            first_pos: Pos,
            const_name: const_::T,
        },
        EnumSwitchNonexhaustive {
            pos: Pos,
            kind: Option<String>,
            decl_pos: PosOrDecl,
            missing: Vec<Option<const_::T>>,
        },
        EnumSwitchRedundantDefault {
            pos: Pos,
            kind: String,
            decl_pos: PosOrDecl,
        },
        EnumSwitchNotConst(Pos),
        EnumSwitchWrongClass {
            pos: Pos,
            kind: String,
            expected: Lazy<String>,
            actual: Lazy<String>,
            expected_pos: Option<PosOrDecl>,
        },
        EnumSwitchInconsistentIntLiteralFormat {
            expected_pos: Pos,
            expected: String,
            actual: String,
            pos: Pos,
        },
        EnumTypeBad {
            pos: Pos,
            ty_name: Lazy<String>,
            is_enum_class: bool,
            trail: Vec<PosOrDecl>,
        },
        EnumTypeBadCaseType {
            pos: Pos,
            ty_name: Lazy<String>,
            case_type_decl_pos: PosOrDecl,
        },
        EnumConstantTypeBad {
            pos: Pos,
            ty_pos: PosOrDecl,
            ty_name: Lazy<String>,
            trail: Vec<PosOrDecl>,
        },
        EnumTypeTypedefNonnull(Pos),
        EnumClassLabelAsExpr(Pos),
        EnumClassLabelMemberMismatch {
            pos: Pos,
            label: String,
            expected_ty_msg_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        },
        IncompatibleEnumInclusionBase {
            pos: Pos,
            classish_name: String,
            src_classish_name: String,
        },
        IncompatibleEnumInclusionConstraint {
            pos: Pos,
            classish_name: String,
            src_classish_name: String,
        },
        EnumInclusionNotEnum {
            pos: Pos,
            classish_name: String,
            src_classish_name: String,
        },
    }
}

pub use self::enum_ as r#enum;

/// `Typing_error.Primary.Expr_tree`
pub mod expr_tree {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub enum T {
        ExpressionTreeNonPublicMember {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        ReifiedStaticMethodInExprTree(Pos),
        ThisVarInExprTree(Pos),
        ExperimentalExpressionTrees(Pos),
        ExpressionTreeUnsupportedOperator {
            pos: Pos,
            member_name: String,
            class_name: String,
        },
    }
}

/// `Typing_error.Primary.Readonly`
pub mod readonly {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    /// ``what: [ `arg_readonly | `arg_mut | `collection_mod | `prop_assign ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ReadonlyMismatchWhat {
        ArgReadonly,
        ArgMut,
        CollectionMod,
        PropAssign,
    }

    /// ``kind: [ `fn_call | `property | `static_property ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ExplicitReadonlyCastKind {
        FnCall,
        Property,
        StaticProperty,
    }

    /// Short for [`ReadonlyMismatchWhat`]
    pub type What = ReadonlyMismatchWhat;
    /// Short for [`ExplicitReadonlyCastKind`]
    pub type Kind = ExplicitReadonlyCastKind;

    #[derive(Clone, Debug)]
    pub enum T {
        ReadonlyModified {
            pos: Pos,
            reason_opt: Option<Lazy<Message<PosOrDecl>>>,
        },
        ReadonlyMismatch {
            pos: Pos,
            what: ReadonlyMismatchWhat,
            pos_sub: PosOrDecl,
            pos_super: PosOrDecl,
        },
        ReadonlyInvalidAsMut(Pos),
        ReadonlyException(Pos),
        ExplicitReadonlyCast {
            pos: Pos,
            decl_pos: PosOrDecl,
            kind: ExplicitReadonlyCastKind,
        },
        ReadonlyMethodCall {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        ReadonlyClosureCall {
            pos: Pos,
            decl_pos: PosOrDecl,
            suggestion: String,
        },
    }
}

/// `Typing_error.Primary.Coeffect`
pub mod coeffect {
    use oxidized::error_codes::Typing;
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        CallCoeffect {
            pos: Pos,
            available_pos: PosOrDecl,
            available_incl_unsafe: Lazy<String>,
            required_pos: PosOrDecl,
            required: Lazy<String>,
        },
        OpCoeffectError {
            pos: Pos,
            op_name: String,
            locally_available: Lazy<String>,
            available_pos: PosOrDecl,
            err_code: Typing,
            required: Lazy<String>,
            suggestion: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        },
    }
}

/// `Typing_error.Primary.Wellformedness`
pub mod wellformedness {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        MissingReturn {
            pos: Pos,
            hint_pos: Option<PosOrDecl>,
            is_async: bool,
        },
        VoidUsage {
            pos: Pos,
            reason: Lazy<Vec<Message<PosOrDecl>>>,
        },
        NoreturnUsage {
            pos: Pos,
            reason: Lazy<Vec<Message<PosOrDecl>>>,
        },
        ReturnsWithAndWithoutValue {
            pos: Pos,
            with_value_pos: Pos,
            without_value_pos_opt: Option<Pos>,
        },
        NonVoidAnnotationOnReturnVoidFunction {
            is_async: bool,
            hint_pos: Pos,
        },
        TupleSyntax(Pos),
        InvalidClassRefinement {
            pos: Pos,
        },
        RedundantShapeSplat {
            pos: Pos,
            operand_pos: Pos,
            is_dynamic: bool,
        },
    }
}

/// `Typing_error.Primary.Modules`
pub mod modules {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub enum T {
        ModuleHint {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        ModuleMismatch {
            pos: Pos,
            current_module_opt: Option<String>,
            decl_pos: PosOrDecl,
            target_module: String,
            tests_bypass_visibility_context: bool,
        },
        ModuleUnsafeTraitAccess {
            access_pos: Pos,
            trait_pos: PosOrDecl,
        },
    }
}

/// `Typing_error.Primary.Package`
pub mod package {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;
    use relative_path::RelativePath;

    #[derive(Clone, Debug)]
    pub enum TargetSymbolSpec {
        Func,
        GlobalConst,
        ClassConst,
        Class,
        Enum,
        Symbol,
        TypeConst,
        ReifiableTypeConst {
            reifiable_attr_pos: PosOrDecl,
            tconst_name: String,
        },
        TransparentTypeAlias,
        CaseType,
        ReifiedGeneric,
        Generic,
        AsExpression,
        EnforceableTypeAlias,
        EnforceableEnum,
        Attribute,
        TypeHint,
    }

    pub fn target_symbol_spec_to_string(spec: &TargetSymbolSpec) -> String {
        match spec {
            TargetSymbolSpec::Func => "function",
            TargetSymbolSpec::GlobalConst => "global constant",
            TargetSymbolSpec::ClassConst => "class constant",
            TargetSymbolSpec::Class => "class",
            TargetSymbolSpec::Enum => "enum",
            TargetSymbolSpec::Symbol => "symbol",
            TargetSymbolSpec::TypeConst => "type constant",
            TargetSymbolSpec::ReifiableTypeConst { .. } => "reifiable type constant",
            TargetSymbolSpec::TransparentTypeAlias => "transparent type alias",
            TargetSymbolSpec::CaseType => "case type",
            TargetSymbolSpec::ReifiedGeneric => "reified generic",
            TargetSymbolSpec::Generic => "generic",
            TargetSymbolSpec::AsExpression => "asserted type",
            TargetSymbolSpec::EnforceableTypeAlias => "type alias used as an enforceable type hint",
            TargetSymbolSpec::EnforceableEnum => "enum used as an enforceable type hint",
            TargetSymbolSpec::Attribute => "attribute",
            TargetSymbolSpec::TypeHint => "type",
        }
        .to_string()
    }

    #[derive(Clone, Debug)]
    pub enum T {
        CrossPkgAccess {
            pos: Pos,
            decl_pos: PosOrDecl,
            current_package: Option<oxidized::package::PosId>,
            current_package_assignment_kind: String,
            target_package: Option<oxidized::package::PosId>,
            target_package_assignment_kind: String,
            current_filename: RelativePath,
            target_filename: RelativePath,
            target_id: String,
            target_symbol_spec: TargetSymbolSpec,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        CrossPkgAccessWithRequirepackage {
            pos: Pos,
            decl_pos: PosOrDecl,
            target_package: String,
            current_package: Option<oxidized::package::PosId>,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        CrossPkgAccessWithSoftrequirepackage {
            pos: Pos,
            decl_pos: PosOrDecl,
            current_soft_package_opt: Option<(Pos, String)>,
            target_package: String,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        SoftIncludedAccess {
            pos: Pos,
            decl_pos: PosOrDecl,
            current_package: Option<oxidized::package::PosId>,
            current_package_assignment_kind: String,
            target_package: Option<oxidized::package::PosId>,
            target_package_assignment_kind: String,
            current_filename: RelativePath,
            target_filename: RelativePath,
            target_id: String,
            target_symbol_spec: TargetSymbolSpec,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        ExcludedPathAccess {
            pos: Pos,
            decl_pos: PosOrDecl,
            package: Option<oxidized::package::PosId>,
            target_filename: RelativePath,
            target_id: String,
            target_symbol_spec: TargetSymbolSpec,
        },
    }
}

/// `Typing_error.Primary.Xhp`
pub mod xhp {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        XhpRequired {
            pos: Pos,
            why_xhp: String,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        IllegalXhpChild {
            pos: Pos,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        MissingXhpRequiredAttr {
            pos: Pos,
            attr: String,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        AttributeValue {
            pos: Pos,
            attr_name: String,
            valid_values: Vec<String>,
        },
    }
}

/// `Typing_error.Primary.CaseType`
pub mod case_type {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        OverlappingVariantTypes {
            pos: Pos,
            name: String,
            why: Lazy<Vec<Message<PosOrDecl>>>,
        },
        InvalidRecursive {
            pos: Pos,
            name: String,
        },
        RecursiveWhereClause {
            pos: Pos,
            name: String,
            mentions: Vec<PosOrDecl>,
        },
    }
}

/// `Typing_error.Primary.SimpliHack`
pub mod simpli_hack {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        RunPrompt {
            pos: Pos,
        },
        RerunPrompt {
            pos: Pos,
            prompt_digest: String,
            expected_digest: String,
        },
        EvaluationError {
            pos: Pos,
            stack_trace: Lazy<Vec<Message<PosOrDecl>>>,
        },
    }
}

/// `Typing_error.Primary.Shape_splat`
pub mod shape_splat {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_defs_core::Ty;

    #[derive(Clone, Debug)]
    pub enum OverlapSourceOrigin {
        ShapeField(String),
        Description(String),
    }

    #[derive(Clone, Debug)]
    pub struct OverlapSource {
        pub pos: PosOrDecl,
        pub origin: OverlapSourceOrigin,
    }

    /// All the ways in which two shape splat elements can be non-disjoint
    #[derive(Clone, Debug)]
    pub enum DisjointnessViolation {
        OverlappingField {
            label: String,
            positions: Vec<PosOrDecl>,
        },
        PossibleOverlappingField {
            label: String,
            positions: Vec<PosOrDecl>,
            sources: Vec<OverlapSource>,
        },
        UnresolvedSources {
            sources: Vec<OverlapSource>,
        },
    }

    #[derive(Clone, Debug)]
    pub struct NonDenotableField {
        pub label: String,
        pub pos: PosOrDecl,
        pub ty: Ty,
    }

    #[derive(Clone, Debug)]
    pub enum T {
        DisjointShapeSplatViolation {
            pos: Pos,
            violations: Vec<DisjointnessViolation>,
        },
        NonDenotableShapeSplatFields {
            pos: Pos,
            fields: Vec<NonDenotableField>,
        },
    }
}

#[derive(Clone, Debug)]
pub struct ImplementsInfo {
    pub pos: PosOrDecl,
    pub instantiation: Vec<String>,
    pub via_direct_parent: (Pos, String),
}

#[derive(Clone, Debug)]
pub struct DynamicObjGetMember {
    pub member_pos: Pos,
    pub member_name_pos: Pos,
    pub member_name: String,
}

// -- Polymorphic variants of the fields of `T` --------------------------------
//
// `<Constructor><Field>`; see `crate::typing_error`.

/// ``kind: [ `method_ | `property ]``
pub type MemberNotFoundKind = MethodOrProperty;
/// ``hint: ([ `instance | `static ] * Pos_or_decl.t * string) option Lazy.t``
pub type MemberNotFoundHint = InstanceOrStatic;
/// ``ctxt: [ `read | `write ]``
pub type InvalidArraykeyCtxt = ReadOrWrite;
/// ``ctxt: [ `read | `write ]``
pub type NullMemberCtxt = ReadOrWrite;
/// ``kind: [ `method_ | `property ]``
pub type NullMemberKind = MethodOrProperty;
/// ``ctxt: [ `read | `write ]``
pub type TopMemberCtxt = ReadOrWrite;
/// ``kind: [ `method_ | `property ]``
pub type TopMemberKind = MethodOrProperty;
/// ``ctxt: [ `read | `write ]``
pub type ArrayAccessCtxt = ReadOrWrite;
/// ``elt: [ `meth | `prop ]``
pub type UnknownObjectMemberElt = MethOrProp;
/// ``elt: [ `meth | `prop ]``
pub type NonClassMemberElt = MethOrProp;
/// ``hint: ([ `instance | `static ] * Pos_or_decl.t * string) option``
pub type SmemberNotFoundHint = InstanceOrStatic;
/// ``ctxt: [ `read | `write ]``
pub type NonObjectMemberCtxt = ReadOrWrite;
/// ``kind: [ `meth | `prop ]``
pub type StaticInstanceIntersectionKind = MethOrProp;

/// ``op: [ `is | `as_ ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvalidIsAsExpressionHintOp {
    Is,
    As,
}
pub type IsOrAs = InvalidIsAsExpressionHintOp;

/// ``kind: [ `constant | `param ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvalidEnforceableTypeKind {
    Constant,
    Param,
}
pub type ConstantOrParam = InvalidEnforceableTypeKind;

/// ``kind: [ `ty | `cnstr | `super_cnstr ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReifiableAttrKind {
    Ty,
    Cnstr,
    SuperCnstr,
}

/// ``via: [ `Id | `Self | `Parent | `Static ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallNeedsConcreteVia {
    Id,
    /// `` `Self ``
    Self_,
    Parent,
    Static,
}

/// ``variance: [ `Co | `Contra ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RedundantGenericVariance {
    Co,
    Contra,
}
pub type CoOrContra = RedundantGenericVariance;

/// ``member_kind: [ `Property | `Method ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequireDynamicObjGetMemberKind {
    Property,
    Method,
}
pub type PropertyOrMethod = RequireDynamicObjGetMemberKind;

/// ``reason: [ `non_string | `embedded_expr ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RePrefixedNonStringReason {
    NonString,
    EmbeddedExpr,
}
pub type NonStringOrEmbeddedExpr = RePrefixedNonStringReason;

/// ``reason: [ `missing_delim | `empty_patt | `invalid_option | `bad_patt of string ]``
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BadRegexPatternReason {
    MissingDelim,
    EmptyPatt,
    InvalidOption,
    BadPatt(String),
}

/// ``kind: [ `void | `noreturn ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptionReturnOnlyTypehintKind {
    Void,
    Noreturn,
}
pub type VoidOrNoreturn = OptionReturnOnlyTypehintKind;

/// ``verb: [ `assigned ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IllegalDisposableVerb {
    Assigned,
}

/// ``kind: [ `static | `classname ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NewInconsistentConstructKind {
    /// `` `static ``
    Static,
    Classname,
}
pub type StaticOrClassname = NewInconsistentConstructKind;

/// ``req_constraint_kind: [ `class_ | `this_as ]`` (`Trait_not_used`)
pub type TraitNotUsedReqConstraintKind = StaticCallOnTraitRequireNonStrictReqConstraintKind;

/// ``req_constraint_kind: [ `class_ | `this_as ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StaticCallOnTraitRequireNonStrictReqConstraintKind {
    Class,
    ThisAs,
}
pub type ClassOrThisAs = StaticCallOnTraitRequireNonStrictReqConstraintKind;
/// Short for [`StaticCallOnTraitRequireNonStrictReqConstraintKind`]
pub type ReqConstraintKind = StaticCallOnTraitRequireNonStrictReqConstraintKind;

/// ``parent_kind: [ `intf | `trait | `class_ | `enum | `enum_class ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtendSealedParentKind {
    Intf,
    /// `` `trait ``
    Trait,
    Class,
    /// `` `enum ``
    Enum,
    EnumClass,
}
/// Short for [`ExtendSealedParentKind`]
pub type SealedParentKind = ExtendSealedParentKind;

/// ``verb: [ `extend | `implement | `use ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtendSealedVerb {
    Extend,
    Implement,
    /// `` `use ``
    Use,
}

/// ``kind: [ `meth | `prop | `const | `ty_const ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImplementAbstractKind {
    Meth,
    Prop,
    /// `` `const ``
    Const,
    TyConst,
}

/// ``member_kind: [ `method_ | `property | `constant | `type_constant ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractMemberInConcreteClassMemberKind {
    Method,
    Property,
    Constant,
    TypeConstant,
}
/// Short for [`AbstractMemberInConcreteClassMemberKind`]
pub type AbstractMemberKind = AbstractMemberInConcreteClassMemberKind;

/// ``kind: [ `class_constant | `class_typeconst | `class_variable | `static_method ]``
///
/// (Also the `kind` of `Secondary.Smember_not_found`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmemberNotFoundKind {
    ClassConstant,
    ClassTypeconst,
    ClassVariable,
    StaticMethod,
}
/// Short for [`SmemberNotFoundKind`]
pub type ClassMemberKind = SmemberNotFoundKind;

/// ``kind: [ `class_typeconst | `method_ | `property ]``
///
/// (Also the `kind` of `Secondary.Non_object_member`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonObjectMemberKind {
    ClassTypeconst,
    Method,
    Property,
}

/// Specific error information readily transformable into a user error
#[derive(Clone, Debug)]
pub enum T {
    // == Factorised errors ====================================================
    Coeffect(coeffect::T),
    Enum(enum_::T),
    ExprTree(expr_tree::T),
    Modules(modules::T),
    Package(package::T),
    Readonly(readonly::T),
    Shape(shape::T),
    ShapeAndTupleDestructure(shape_and_tuple_destructure::T),
    Switch(switch::T),
    Wellformedness(wellformedness::T),
    Xhp(xhp::T),
    CaseType(case_type::T),
    SimpliHack(simpli_hack::T),
    // == Primary only =========================================================
    UnresolvedTyvar(Pos),
    UnifyError {
        pos: Pos,
        msg_opt: Option<String>,
        reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    },
    GenericUnify {
        pos: Pos,
        msg: String,
    },
    UsingError {
        pos: Pos,
        has_await: bool,
    },
    BadEnumDecl(Pos),
    BadConditionalSupportDynamic {
        pos: Pos,
        child: String,
        parent: String,
        ty_name: Lazy<String>,
        self_ty_name: Lazy<String>,
    },
    BadDeclOverride {
        pos: Pos,
        name: String,
        parent_name: String,
    },
    ExplainWhereConstraint {
        pos: Pos,
        in_class: bool,
        decl_pos: PosOrDecl,
    },
    ExplainConstraint(Pos),
    RigidTvarEscape {
        pos: Pos,
        what: String,
    },
    InvalidTypeHint(Pos),
    ShapeSplat(shape_splat::T),
    GatedByFeatureFlag {
        pos: Pos,
        name: String,
        feature: String,
    },
    TestsBypassVisibilityOnMemberWithoutClass {
        pos: Pos,
        member_name: String,
        class_name: String,
    },
    UnsatisfiedReq {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    UnsatisfiedReqClass {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    UnsatisfiedReqThisAs {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    IncompatibleReqs {
        pos: Pos,
        req_name: String,
        req_class_pos: PosOrDecl,
        req_extends_pos: PosOrDecl,
    },
    TraitNotUsed {
        pos: Pos,
        trait_name: String,
        req_class_pos: PosOrDecl,
        class_pos: PosOrDecl,
        class_name: String,
        req_constraint_kind: TraitNotUsedReqConstraintKind,
    },
    InvalidEchoArgument(Pos),
    IndexTypeMismatch {
        pos: Pos,
        is_covariant_container: bool,
        msg_opt: Option<String>,
        reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    },
    MemberNotFound {
        pos: Pos,
        kind: MethodOrProperty,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Lazy<Option<(InstanceOrStatic, PosOrDecl, String)>>,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    ConstructNotInstanceMethod(Pos),
    AmbiguousInheritance {
        pos: Pos,
        class_name: String,
        origin: String,
    },
    ExpectedTparam {
        pos: Pos,
        decl_pos: PosOrDecl,
        n: isize,
    },
    TypeconstConcreteConcreteOverride {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ConstantMultipleConcreteConflict {
        pos: Pos,
        name: String,
        definitions: Vec<(PosOrDecl, Option<String>)>,
    },
    InvalidMemoizedParam {
        pos: Pos,
        ty_name: Lazy<String>,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    InvalidArraykey {
        pos: Pos,
        ctxt: ReadOrWrite,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        key_pos: PosOrDecl,
        key_ty_name: Lazy<String>,
    },
    InvalidKeysetValue {
        pos: Pos,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        value_pos: PosOrDecl,
        value_ty_name: Lazy<String>,
    },
    InvalidSetValue {
        pos: Pos,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        value_pos: PosOrDecl,
        value_ty_name: Lazy<String>,
    },
    InvalidSubstring {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    UnsetNonidxInStrict {
        pos: Pos,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    NullableCast {
        pos: Pos,
        ty_pos: PosOrDecl,
        ty_name: Lazy<String>,
    },
    HhExpect {
        pos: Pos,
        equivalent: bool,
    },
    NullMember {
        pos: Pos,
        obj_pos_opt: Option<Pos>,
        ctxt: ReadOrWrite,
        kind: MethodOrProperty,
        member_name: String,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    NullsafePropertyWriteContext(Pos),
    UninstantiableClass {
        pos: Pos,
        class_name: String,
        reason_ty_opt: Option<(Pos, Lazy<String>)>,
        decl_pos: PosOrDecl,
    },
    AbstractConstUsage {
        pos: Pos,
        decl_pos: PosOrDecl,
        name: String,
    },
    MemberNotImplemented {
        pos: Pos,
        member_name: String,
        decl_pos: PosOrDecl,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    KindMismatch {
        pos: Pos,
        decl_pos: PosOrDecl,
        tparam_name: String,
        expected_kind: String,
        actual_kind: String,
    },
    TraitParentConstructInconsistent {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    TopMember {
        pos: Pos,
        ctxt: ReadOrWrite,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
        kind: MethodOrProperty,
        name: String,
        is_nullable: bool,
        ty_reasons: Lazy<Vec<(PosOrDecl, String)>>,
    },
    UnresolvedTyvarProjection {
        pos: Pos,
        proj_pos: PosOrDecl,
        tconst_name: String,
    },
    CyclicClassConstant {
        pos: Pos,
        class_name: String,
        const_name: String,
    },
    InoutAnnotationMissing {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    InoutAnnotationUnexpected {
        pos: Pos,
        decl_pos: PosOrDecl,
        param_is_variadic: bool,
        qfx_pos: Pos,
    },
    InoutArgumentBadType {
        pos: Pos,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    },
    InvalidMethCallerInoutParameter {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    InvalidMethCallerNamedParameter {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    InvalidMethCallerReadonlyReturn {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ThisAsFunctionPointerParam {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    InvalidNewDisposable(Pos),
    InvalidReturnDisposable(Pos),
    InvalidDisposableHint {
        pos: Pos,
        class_name: String,
    },
    InvalidDisposableReturnHint {
        pos: Pos,
        class_name: String,
    },
    AmbiguousLambda {
        pos: Pos,
        uses: Lazy<Vec<Message<PosOrDecl>>>,
    },
    WrongExtendKind {
        pos: Pos,
        kind: ClassishKind,
        name: String,
        parent_pos: PosOrDecl,
        parent_kind: ClassishKind,
        parent_name: String,
    },
    WrongUseKind {
        pos: Pos,
        name: String,
        parent_pos: PosOrDecl,
        parent_name: String,
    },
    CyclicClassDef {
        pos: Pos,
        stack: SSet,
    },
    TraitReuseWithFinalMethod {
        pos: Pos,
        trait_name: String,
        parent_cls_name: Lazy<String>,
        trace: Lazy<Vec<Message<PosOrDecl>>>,
    },
    TraitReuseInsideClass {
        pos: Pos,
        class_name: String,
        trait_name: String,
        occurrences: Vec<PosOrDecl>,
    },
    InvalidIsAsExpressionHint {
        pos: Pos,
        op: InvalidIsAsExpressionHintOp,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    },
    InvalidEnforceableType {
        pos: Pos,
        ty_info: Lazy<Vec<Message<PosOrDecl>>>,
        tp_pos: PosOrDecl,
        tp_name: String,
        kind: InvalidEnforceableTypeKind,
    },
    ReifiableAttr {
        pos: Pos,
        ty_info: Lazy<Vec<Message<PosOrDecl>>>,
        attr_pos: PosOrDecl,
        kind: ReifiableAttrKind,
    },
    InvalidNewableTypeArgument {
        pos: Pos,
        tp_pos: PosOrDecl,
        tp_name: String,
    },
    InvalidNewableTyparamConstraints {
        pos: Pos,
        tp_name: String,
        constraints: Vec<String>,
    },
    OverridePerTrait {
        pos: Pos,
        class_name: String,
        meth_name: String,
        trait_name: String,
        meth_pos: PosOrDecl,
    },
    ShouldNotBeOverride {
        pos: Pos,
        class_id: String,
        id: String,
    },
    NeedsConcreteInFinalClass {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    NeedsConcreteOnInstanceMethod {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    NeedsConcreteOnConstructor {
        pos: Pos,
        class_name: String,
    },
    CallNeedsConcrete {
        pos: Pos,
        class_name: String,
        meth_name: String,
        decl_pos: PosOrDecl,
        via: CallNeedsConcreteVia,
    },
    AbstractAccessViaStatic {
        pos: Pos,
        class_name: String,
        member_name: String,
        decl_pos: PosOrDecl,
        containing_method_pos: Option<Pos>,
    },
    UninstantiableClassViaStatic {
        pos: Pos,
        class_name: String,
        decl_pos: PosOrDecl,
        containing_method_pos: Option<Pos>,
    },
    ThisRefinementInGenericClass {
        pos: Pos,
        class_name: String,
        decl_pos: PosOrDecl,
    },
    PrivateMemberVariance {
        pos: Pos,
        class_name: String,
        member_name: String,
        is_write: bool,
        tparam_name: String,
        variance: oxidized::ast_defs::Variance,
        use_pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    MemoizeErasedGenericReturn {
        pos: Pos,
        tparam_name: String,
        attr_pos: Pos,
        via_param: Option<Pos>,
    },
    NeedsConcreteOverride {
        pos: Pos,
        method_pos: PosOrDecl,
        parent_pos: PosOrDecl,
        method_name_for_method_defined_outside_class: Option<String>,
    },
    TrivialStrictEq {
        pos: Pos,
        result: bool,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
        left_trail: Vec<PosOrDecl>,
        right_trail: Vec<PosOrDecl>,
    },
    TrivialStrictNotNullableCompareNull {
        pos: Pos,
        result: bool,
        ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
    },
    EqIncompatibleTypes {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    ComparisonInvalidTypes {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    StrictEqValueIncompatibleTypes {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    DeprecatedUse {
        pos: Pos,
        decl_pos_opt: Option<PosOrDecl>,
        msg: String,
    },
    CannotDeclareConstant {
        pos: Pos,
        class_pos: Pos,
        class_name: String,
    },
    RedeclaringPromotedProperty {
        pos: Pos,
        prop_name: String,
        parent_pos: PosOrDecl,
        parent_name: String,
    },
    InvalidClassname(Pos),
    IllegalTypeStructure {
        pos: Pos,
        msg: String,
        /// `fn`
        fn_: String,
    },
    IllegalTypeconstDirectAccess(Pos),
    WrongExpressionKindAttribute {
        pos: Pos,
        attr_name: String,
        expr_kind: String,
        attr_class_pos: PosOrDecl,
        attr_class_name: String,
        intf_name: String,
    },
    AmbiguousObjectAccess {
        pos: Pos,
        name: String,
        self_pos: PosOrDecl,
        vis: String,
        subclass_pos: PosOrDecl,
        class_self: String,
        class_subclass: String,
    },
    InvalidArraykeyConstraint {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    RedundantGeneric {
        pos: Pos,
        variance: RedundantGenericVariance,
        msg: String,
        suggest: String,
    },
    MethCallerTrait {
        pos: Pos,
        trait_name: String,
    },
    DuplicateInterface {
        pos: Pos,
        name: String,
        others: Vec<PosOrDecl>,
    },
    EnumDuplicateValue {
        /// the enum definition
        pos: Pos,
        value: String,
        member_name: String,
        member_pos: PosOrDecl,
        prev_name: String,
        prev_pos: PosOrDecl,
    },
    EnumUncheckableValue {
        /// the enum definition
        pos: Pos,
        /// the enum's name
        name: String,
        /// Lazily: `(reasons, num_omitted)` -- why the enum can't be
        /// statically checked for duplicate values (capped for display) and
        /// how many further reasons were omitted. Lazy so the reason strings
        /// are only built when the error is rendered.
        reasons: Lazy<(Vec<(PosOrDecl, String)>, isize)>,
    },
    ReifiedFunctionReference(Pos),
    ReinheritingClassishConst {
        pos: Pos,
        classish_name: String,
        src_pos: Pos,
        src_classish_name: String,
        existing_const_origin: String,
        const_name: String,
    },
    RedeclaringClassishConst {
        pos: Pos,
        classish_name: String,
        redeclaration_pos: Pos,
        existing_const_origin: String,
        const_name: String,
    },
    AbstractFunctionPointer {
        pos: Pos,
        class_name: String,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    InheritedClassMemberWithDifferentCase {
        pos: Pos,
        member_type: String,
        name: String,
        name_prev: String,
        child_class: String,
        prev_class: String,
        prev_class_pos: PosOrDecl,
    },
    MultipleInheritedClassMemberWithDifferentCase {
        pos: Pos,
        child_class_name: String,
        member_type: String,
        class1_name: String,
        class1_pos: PosOrDecl,
        name1: String,
        class2_name: String,
        class2_pos: PosOrDecl,
        name2: String,
    },
    MultipleInstantiationInheritence {
        type_name: String,
        implements_or_extends: String,
        interface_name: String,
        winning_implements: ImplementsInfo,
        losing_implements: ImplementsInfo,
    },
    ParentSupportDynamicType {
        pos: Pos,
        child_name: String,
        child_kind: ClassishKind,
        parent_name: String,
        parent_kind: ClassishKind,
        child_support_dyn: bool,
    },
    PropertyIsNotEnforceable {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    PropertyIsNotDynamic {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    PrivatePropertyIsNotEnforceable {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    PrivatePropertyIsNotDynamic {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    ImmutableLocal(Pos),
    RequireDynamicObjGet {
        receiver_pos: Pos,
        receiver_ty: Lazy<String>,
        receiver_ty_pos: PosOrDecl,
        member_kind: RequireDynamicObjGetMemberKind,
        member_name: Option<DynamicObjGetMember>,
    },
    NonsenseMemberSelection {
        pos: Pos,
        kind: String,
    },
    ConsiderMethCaller {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    MethodImportViaDiamond {
        pos: Pos,
        class_name: String,
        method_pos: PosOrDecl,
        method_name: String,
        trace1: Lazy<Vec<Message<PosOrDecl>>>,
        trace2: Lazy<Vec<Message<PosOrDecl>>>,
    },
    PropertyImportViaDiamond {
        generic: bool,
        pos: Pos,
        class_name: String,
        property_pos: PosOrDecl,
        property_name: String,
        trace1: Lazy<Vec<Message<PosOrDecl>>>,
        trace2: Lazy<Vec<Message<PosOrDecl>>>,
    },
    UnificationCycle {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    MethodVariance(Pos),
    ExplainTconstWhereConstraint {
        pos: Pos,
        decl_pos: PosOrDecl,
        msgs: Lazy<Vec<Message<PosOrDecl>>>,
    },
    FormatString {
        pos: Pos,
        snippet: String,
        fmt_string: String,
        class_pos: PosOrDecl,
        fn_name: String,
        class_suggest: String,
    },
    ExpectedLiteralFormatString(Pos),
    RePrefixedNonString {
        pos: Pos,
        reason: RePrefixedNonStringReason,
    },
    BadRegexPattern {
        pos: Pos,
        reason: BadRegexPatternReason,
    },
    OptionReturnOnlyTypehint {
        pos: Pos,
        kind: OptionReturnOnlyTypehintKind,
    },
    RedeclaringMissingMethod {
        pos: Pos,
        trait_method: String,
    },
    ExpectingTypeHint(Pos),
    ExpectingTypeHintVariadic(Pos),
    ExpectingReturnTypeHint(Pos),
    DuplicateUsingVar(Pos),
    IllegalDisposable {
        pos: Pos,
        verb: IllegalDisposableVerb,
    },
    EscapingDisposable(Pos),
    EscapingDisposableParam(Pos),
    EscapingThis(Pos),
    MustExtendDisposable(Pos),
    FieldKinds {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    UnboundName {
        pos: Pos,
        name: String,
        class_exists: bool,
    },
    PreviousDefault(Pos),
    PreviousDefaultOrOptional(Pos),
    ReturnInVoid {
        pos: Pos,
        decl_pos: Pos,
    },
    ThisVarOutsideClass(Pos),
    UnboundGlobal(Pos),
    PrivateMethCaller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ProtectedMethCaller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    InternalMethCaller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ProtectedInternalMethCaller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ArrayCast(Pos),
    StringCast {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    StaticOutsideClass(Pos),
    SelfOutsideClass(Pos),
    NewInconsistentConstruct {
        pos: Pos,
        class_pos: PosOrDecl,
        class_name: String,
        kind: NewInconsistentConstructKind,
    },
    ParentOutsideClass(Pos),
    ParentAbstractCall {
        pos: Pos,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    SelfAbstractCall {
        pos: Pos,
        self_pos: Pos,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    ClassnameAbstractCall {
        pos: Pos,
        meth_name: String,
        class_name: String,
        decl_pos: PosOrDecl,
    },
    StaticSyntheticMethod {
        pos: Pos,
        meth_name: String,
        class_name: String,
        decl_pos: PosOrDecl,
    },
    StaticCallOnTraitRequireNonStrict {
        pos: Pos,
        meth_name: String,
        trait_name: String,
        req_constraint_name: String,
        req_constraint_kind: StaticCallOnTraitRequireNonStrictReqConstraintKind,
        trait_pos: PosOrDecl,
    },
    StaticPropOnTrait {
        pos: Pos,
        meth_name: String,
        trait_name: String,
        trait_pos: PosOrDecl,
    },
    IssetInStrict(Pos),
    IssetInoutArg(Pos),
    UnpackingDisallowedBuiltinFunction {
        pos: Pos,
        fn_name: String,
    },
    ArrayGetArity {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    UndefinedField {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    ArrayAccess {
        pos: Pos,
        ctxt: ReadOrWrite,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    KeysetSet {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ArrayAppend {
        pos: Pos,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    ConstMutation {
        pos: Pos,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    ExpectedClass {
        pos: Pos,
        suffix: Option<Lazy<String>>,
    },
    UnknownType {
        pos: Pos,
        expected: String,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    ParentInTrait(Pos),
    ParentUndefined {
        pos: Pos,
        trait_reqs: Option<Vec<PosOrDecl>>,
    },
    ConstructorNoArgs(Pos),
    Visibility {
        pos: Pos,
        msg: String,
        decl_pos: PosOrDecl,
        reason_msg: String,
    },
    BadCall {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    ExtendFinal {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    ExtendSealed {
        pos: Pos,
        parent_pos: PosOrDecl,
        parent_name: String,
        parent_kind: ExtendSealedParentKind,
        verb: ExtendSealedVerb,
    },
    TraitPropConstClass {
        pos: Pos,
        name: String,
    },
    ImplementAbstract {
        pos: Pos,
        is_final: bool,
        decl_pos: PosOrDecl,
        trace: Lazy<Vec<Message<PosOrDecl>>>,
        name: String,
        kind: ImplementAbstractKind,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    AbstractMemberInConcreteClass {
        pos: Pos,
        class_name_pos: Pos,
        is_final: bool,
        member_kind: AbstractMemberInConcreteClassMemberKind,
        member_name: String,
    },
    GenericStatic {
        pos: Pos,
        typaram_name: String,
    },
    ObjectString {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    ObjectStringDeprecated(Pos),
    CyclicTypedef {
        def_pos: Pos,
        use_pos: PosOrDecl,
    },
    RequireArgsReify {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    RequireGenericExplicit {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
    },
    InvalidReifiedArg {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
        arg_info: Lazy<Vec<Message<PosOrDecl>>>,
    },
    InvalidReifiedArgReifiable {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
        ty_pos: PosOrDecl,
        ty_msg: Lazy<String>,
    },
    NewClassReified {
        pos: Pos,
        class_kind: String,
        suggested_class_name: Option<String>,
    },
    ClassGetReified(Pos),
    StaticMethWithClassReifiedGeneric {
        pos: Pos,
        generic_pos: Pos,
    },
    ConsistentConstructReified(Pos),
    BadFnPtrConstruction(Pos),
    ReifiedGenericsNotAllowed(Pos),
    NewWithoutNewable {
        pos: Pos,
        name: String,
    },
    DiscardedAwaitable {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    UnknownObjectMember {
        pos: Pos,
        member_name: String,
        elt: MethOrProp,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    NonClassMember {
        pos: Pos,
        member_name: String,
        elt: MethOrProp,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    NullContainer {
        pos: Pos,
        null_witness: Lazy<Vec<Message<PosOrDecl>>>,
    },
    DeclaredCovariant {
        pos: Pos,
        param_pos: Pos,
        msgs: Lazy<Vec<Message<Pos>>>,
    },
    DeclaredContravariant {
        pos: Pos,
        param_pos: Pos,
        msgs: Lazy<Vec<Message<Pos>>>,
    },
    StaticPropTypeGenericParam {
        pos: Pos,
        var_ty_pos: PosOrDecl,
        class_pos: PosOrDecl,
    },
    ContravariantThis {
        pos: Pos,
        class_name: String,
        typaram_name: String,
    },
    CyclicTypeconst {
        pos: Pos,
        tyconst_names: Vec<String>,
    },
    ArrayGetWithOptionalField {
        recv_pos: Pos,
        field_pos: Pos,
        field_name: String,
        decl_pos: PosOrDecl,
    },
    MutatingConstProperty(Pos),
    SelfConstParentNot(Pos),
    UnexpectedTyInTast {
        pos: Pos,
        expected_ty: Lazy<String>,
        actual_ty: Lazy<String>,
    },
    CallLvalue(Pos),
    UnsafeCastAwait(Pos),
    // == Primary and secondary ================================================
    SmemberNotFound {
        pos: Pos,
        kind: SmemberNotFoundKind,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    TypeArityMismatch {
        pos: Pos,
        actual: isize,
        decl_pos: PosOrDecl,
        expected: isize,
    },
    TypingTooManyArgs {
        pos: Pos,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    TypingTooFewArgs {
        pos: Pos,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
        /// Hint for adding missing optional arguments, takes positions of
        /// declaration for optional arguments
        hint_missing_optional: Option<PosOrDecl>,
    },
    MissingNamedArgs {
        pos: Pos,
        decl_pos: PosOrDecl,
        missing_names: Vec<String>,
    },
    UnexpectedNamedArgs {
        pos: Pos,
        decl_pos: PosOrDecl,
        unexpected_names: Vec<String>,
    },
    DuplicateNamedArgs {
        pos: Pos,
        duplicate_names: Vec<String>,
    },
    NonObjectMember {
        pos: Pos,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
        ctxt: ReadOrWrite,
        member_name: String,
        kind: NonObjectMemberKind,
    },
    StaticInstanceIntersection {
        class_pos: Pos,
        instance_pos: Lazy<PosOrDecl>,
        static_pos: Lazy<PosOrDecl>,
        member_name: String,
        kind: MethOrProp,
    },
    MatchNotExhaustive {
        pos: Pos,
        ty_not_covered: Lazy<String>,
    },
    MatchOnUnsupportedType {
        pos: Pos,
        expr_ty: Lazy<String>,
        unsupported_tys: Vec<Lazy<String>>,
    },
    ClassConstToString {
        pos: Pos,
        cls_name: String,
    },
    ClassPointerToString {
        pos: Pos,
        ty: String,
    },
    StringToClassPointer {
        pos: Pos,
        cls_name: String,
        ty_pos: PosOrDecl,
    },
    OptionalParameterNotSupported(Pos),
    OptionalParameterNotAbstract(Pos),
}
