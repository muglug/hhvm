// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error.Primary`: specific error information readily transformable
//! into a user error.
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

    #[derive(Clone, Debug)]
    pub enum T {
        Invalid_shape_field_name {
            pos: Pos,
            is_empty: bool,
        },
        Invalid_shape_field_literal {
            pos: Pos,
            witness_pos: Pos,
        },
        Invalid_shape_field_const {
            pos: Pos,
            witness_pos: Pos,
        },
        Invalid_shape_field_type {
            pos: Pos,
            ty_pos: PosOrDecl,
            ty_name: Lazy<String>,
            trail: Vec<PosOrDecl>,
        },
        Shape_field_class_mismatch {
            pos: Pos,
            class_name: String,
            witness_pos: Pos,
            witness_class_name: String,
        },
        Shape_field_type_mismatch {
            pos: Pos,
            ty_name: Lazy<String>,
            witness_pos: Pos,
            witness_ty_name: Lazy<String>,
        },
        Invalid_shape_remove_key(Pos),
        Shapes_key_exists_always_true {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
        },
        Shapes_key_exists_always_false {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
            reason: NothingOrUndefined,
        },
        Shapes_method_access_with_non_existent_field {
            pos: Pos,
            field_name: String,
            decl_pos: PosOrDecl,
            method_name: String,
            reason: NothingOrUndefined,
        },
        Shapes_access_with_non_existent_field {
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
        Missing_ellipsis(Pos),
        Missing_required_fields {
            pos: Pos,
            field_names: String,
        },
        Unknown_field {
            pos: Pos,
            field_name: String,
        },
        Tuple_arity_mismatch {
            pos: Pos,
            pat_arity: isize,
            tuple_arity: isize,
        },
        Tuple_arity_exceeds {
            pos: Pos,
            pat_arity: isize,
            tuple_arity: isize,
        },
        Tuple_arity_union_conflict(Pos),
    }
}

/// `Typing_error.Primary.Switch`
pub mod switch {
    use oxidized::pos::Pos;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        Switch_nonexhaustive {
            switch_pos: Pos,
            missing: Lazy<Vec<String>>,
            scrutinee_pos: Pos,
            scrutinee_type: Lazy<String>,
        },
        Switch_needs_default {
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
        Enum_switch_redundant {
            pos: Pos,
            first_pos: Pos,
            const_name: const_::T,
        },
        Enum_switch_nonexhaustive {
            pos: Pos,
            kind: Option<String>,
            decl_pos: PosOrDecl,
            missing: Vec<Option<const_::T>>,
        },
        Enum_switch_redundant_default {
            pos: Pos,
            kind: String,
            decl_pos: PosOrDecl,
        },
        Enum_switch_not_const(Pos),
        Enum_switch_wrong_class {
            pos: Pos,
            kind: String,
            expected: Lazy<String>,
            actual: Lazy<String>,
            expected_pos: Option<PosOrDecl>,
        },
        Enum_switch_inconsistent_int_literal_format {
            expected_pos: Pos,
            expected: String,
            actual: String,
            pos: Pos,
        },
        Enum_type_bad {
            pos: Pos,
            ty_name: Lazy<String>,
            is_enum_class: bool,
            trail: Vec<PosOrDecl>,
        },
        Enum_type_bad_case_type {
            pos: Pos,
            ty_name: Lazy<String>,
            case_type_decl_pos: PosOrDecl,
        },
        Enum_constant_type_bad {
            pos: Pos,
            ty_pos: PosOrDecl,
            ty_name: Lazy<String>,
            trail: Vec<PosOrDecl>,
        },
        Enum_type_typedef_nonnull(Pos),
        Enum_class_label_as_expr(Pos),
        Enum_class_label_member_mismatch {
            pos: Pos,
            label: String,
            expected_ty_msg_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        },
        Incompatible_enum_inclusion_base {
            pos: Pos,
            classish_name: String,
            src_classish_name: String,
        },
        Incompatible_enum_inclusion_constraint {
            pos: Pos,
            classish_name: String,
            src_classish_name: String,
        },
        Enum_inclusion_not_enum {
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
        Expression_tree_non_public_member {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        Reified_static_method_in_expr_tree(Pos),
        This_var_in_expr_tree(Pos),
        Experimental_expression_trees(Pos),
        Expression_tree_unsupported_operator {
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
        arg_readonly,
        arg_mut,
        collection_mod,
        prop_assign,
    }

    /// ``kind: [ `fn_call | `property | `static_property ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ExplicitReadonlyCastKind {
        fn_call,
        property,
        static_property,
    }

    /// Short for [`ReadonlyMismatchWhat`]
    pub type What = ReadonlyMismatchWhat;
    /// Short for [`ExplicitReadonlyCastKind`]
    pub type Kind = ExplicitReadonlyCastKind;

    #[derive(Clone, Debug)]
    pub enum T {
        Readonly_modified {
            pos: Pos,
            reason_opt: Option<Lazy<Message<PosOrDecl>>>,
        },
        Readonly_mismatch {
            pos: Pos,
            what: ReadonlyMismatchWhat,
            pos_sub: PosOrDecl,
            pos_super: PosOrDecl,
        },
        Readonly_invalid_as_mut(Pos),
        Readonly_exception(Pos),
        Explicit_readonly_cast {
            pos: Pos,
            decl_pos: PosOrDecl,
            kind: ExplicitReadonlyCastKind,
        },
        Readonly_method_call {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        Readonly_closure_call {
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
        Call_coeffect {
            pos: Pos,
            available_pos: PosOrDecl,
            available_incl_unsafe: Lazy<String>,
            required_pos: PosOrDecl,
            required: Lazy<String>,
        },
        Op_coeffect_error {
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
        Missing_return {
            pos: Pos,
            hint_pos: Option<PosOrDecl>,
            is_async: bool,
        },
        Void_usage {
            pos: Pos,
            reason: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Noreturn_usage {
            pos: Pos,
            reason: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Returns_with_and_without_value {
            pos: Pos,
            with_value_pos: Pos,
            without_value_pos_opt: Option<Pos>,
        },
        Non_void_annotation_on_return_void_function {
            is_async: bool,
            hint_pos: Pos,
        },
        Tuple_syntax(Pos),
        Invalid_class_refinement {
            pos: Pos,
        },
    }
}

/// `Typing_error.Primary.Modules`
pub mod modules {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub enum T {
        Module_hint {
            pos: Pos,
            decl_pos: PosOrDecl,
        },
        Module_mismatch {
            pos: Pos,
            current_module_opt: Option<String>,
            decl_pos: PosOrDecl,
            target_module: String,
            tests_bypass_visibility_context: bool,
        },
        Module_unsafe_trait_access {
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
        Global_const,
        Class_const,
        Class,
        Enum,
        Symbol,
        Type_const,
        Reifiable_type_const {
            reifiable_attr_pos: PosOrDecl,
            tconst_name: String,
        },
        Transparent_type_alias,
        Case_type,
        Reified_generic,
        Generic,
        As_expression,
        Enforceable_type_alias,
        Enforceable_enum,
        Attribute,
        Type_hint,
    }

    pub fn target_symbol_spec_to_string(spec: &TargetSymbolSpec) -> String {
        match spec {
            TargetSymbolSpec::Func => "function",
            TargetSymbolSpec::Global_const => "global constant",
            TargetSymbolSpec::Class_const => "class constant",
            TargetSymbolSpec::Class => "class",
            TargetSymbolSpec::Enum => "enum",
            TargetSymbolSpec::Symbol => "symbol",
            TargetSymbolSpec::Type_const => "type constant",
            TargetSymbolSpec::Reifiable_type_const { .. } => "reifiable type constant",
            TargetSymbolSpec::Transparent_type_alias => "transparent type alias",
            TargetSymbolSpec::Case_type => "case type",
            TargetSymbolSpec::Reified_generic => "reified generic",
            TargetSymbolSpec::Generic => "generic",
            TargetSymbolSpec::As_expression => "asserted type",
            TargetSymbolSpec::Enforceable_type_alias => {
                "type alias used as an enforceable type hint"
            }
            TargetSymbolSpec::Enforceable_enum => "enum used as an enforceable type hint",
            TargetSymbolSpec::Attribute => "attribute",
            TargetSymbolSpec::Type_hint => "type",
        }
        .to_string()
    }

    #[derive(Clone, Debug)]
    pub enum T {
        Cross_pkg_access {
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
        Cross_pkg_access_with_requirepackage {
            pos: Pos,
            decl_pos: PosOrDecl,
            target_package: String,
            current_package: Option<oxidized::package::PosId>,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        Cross_pkg_access_with_softrequirepackage {
            pos: Pos,
            decl_pos: PosOrDecl,
            current_soft_package_opt: Option<(Pos, String)>,
            target_package: String,
            loaded_packages: Vec<oxidized::package::PosId>,
            included_packages: Vec<(String, String, Pos)>,
        },
        Soft_included_access {
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
        Excluded_path_access {
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
        Xhp_required {
            pos: Pos,
            why_xhp: String,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Illegal_xhp_child {
            pos: Pos,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Missing_xhp_required_attr {
            pos: Pos,
            attr: String,
            ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Attribute_value {
            pos: Pos,
            attr_name: String,
            valid_values: Vec<String>,
        },
    }
}

/// `Typing_error.Primary.CaseType`
pub mod casetype {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        Overlapping_variant_types {
            pos: Pos,
            name: String,
            why: Lazy<Vec<Message<PosOrDecl>>>,
        },
        Invalid_recursive {
            pos: Pos,
            name: String,
        },
        Recursive_where_clause {
            pos: Pos,
            name: String,
            mentions: Vec<PosOrDecl>,
        },
    }
}

pub use self::casetype as case_type;

/// `Typing_error.Primary.SimpliHack`
pub mod simplihack {
    use oxidized::message::Message;
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    use crate::typing_error::Lazy;

    #[derive(Clone, Debug)]
    pub enum T {
        Run_prompt {
            pos: Pos,
        },
        Rerun_prompt {
            pos: Pos,
            prompt_digest: String,
            expected_digest: String,
        },
        Evaluation_error {
            pos: Pos,
            stack_trace: Lazy<Vec<Message<PosOrDecl>>>,
        },
    }
}

pub use self::simplihack as simpli_hack;

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
    is,
    as_,
}
pub type IsOrAs = InvalidIsAsExpressionHintOp;

/// ``kind: [ `constant | `param ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvalidEnforceableTypeKind {
    constant,
    param,
}
pub type ConstantOrParam = InvalidEnforceableTypeKind;

/// ``kind: [ `ty | `cnstr | `super_cnstr ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReifiableAttrKind {
    ty,
    cnstr,
    super_cnstr,
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
    non_string,
    embedded_expr,
}
pub type NonStringOrEmbeddedExpr = RePrefixedNonStringReason;

/// ``reason: [ `missing_delim | `empty_patt | `invalid_option | `bad_patt of string ]``
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BadRegexPatternReason {
    missing_delim,
    empty_patt,
    invalid_option,
    bad_patt(String),
}

/// ``kind: [ `void | `noreturn ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptionReturnOnlyTypehintKind {
    void,
    noreturn,
}
pub type VoidOrNoreturn = OptionReturnOnlyTypehintKind;

/// ``verb: [ `assigned ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IllegalDisposableVerb {
    assigned,
}

/// ``kind: [ `static | `classname ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NewInconsistentConstructKind {
    /// `` `static ``
    static_,
    classname,
}
pub type StaticOrClassname = NewInconsistentConstructKind;

/// ``req_constraint_kind: [ `class_ | `this_as ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StaticCallOnTraitRequireNonStrictReqConstraintKind {
    class_,
    this_as,
}
pub type ClassOrThisAs = StaticCallOnTraitRequireNonStrictReqConstraintKind;
/// Short for [`StaticCallOnTraitRequireNonStrictReqConstraintKind`]
pub type ReqConstraintKind = StaticCallOnTraitRequireNonStrictReqConstraintKind;

/// ``parent_kind: [ `intf | `trait | `class_ | `enum | `enum_class ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtendSealedParentKind {
    intf,
    /// `` `trait ``
    trait_,
    class_,
    /// `` `enum ``
    enum_,
    enum_class,
}
/// Short for [`ExtendSealedParentKind`]
pub type SealedParentKind = ExtendSealedParentKind;

/// ``verb: [ `extend | `implement | `use ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtendSealedVerb {
    extend,
    implement,
    /// `` `use ``
    use_,
}

/// ``kind: [ `meth | `prop | `const | `ty_const ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImplementAbstractKind {
    meth,
    prop,
    /// `` `const ``
    const_,
    ty_const,
}

/// ``member_kind: [ `method_ | `property | `constant | `type_constant ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractMemberInConcreteClassMemberKind {
    method_,
    property,
    constant,
    type_constant,
}
/// Short for [`AbstractMemberInConcreteClassMemberKind`]
pub type AbstractMemberKind = AbstractMemberInConcreteClassMemberKind;

/// ``kind: [ `class_constant | `class_typeconst | `class_variable | `static_method ]``
///
/// (Also the `kind` of `Secondary.Smember_not_found`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmemberNotFoundKind {
    class_constant,
    class_typeconst,
    class_variable,
    static_method,
}
/// Short for [`SmemberNotFoundKind`]
pub type ClassMemberKind = SmemberNotFoundKind;

/// ``kind: [ `class_typeconst | `method_ | `property ]``
///
/// (Also the `kind` of `Secondary.Non_object_member`.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonObjectMemberKind {
    class_typeconst,
    method_,
    property,
}

/// Specific error information readily transformable into a user error
#[derive(Clone, Debug)]
pub enum T {
    // == Factorised errors ====================================================
    Coeffect(coeffect::T),
    Enum(enum_::T),
    Expr_tree(expr_tree::T),
    Modules(modules::T),
    Package(package::T),
    Readonly(readonly::T),
    Shape(shape::T),
    Shape_and_tuple_destructure(shape_and_tuple_destructure::T),
    Switch(switch::T),
    Wellformedness(wellformedness::T),
    Xhp(xhp::T),
    CaseType(casetype::T),
    SimpliHack(simplihack::T),
    // == Primary only =========================================================
    Unresolved_tyvar(Pos),
    Unify_error {
        pos: Pos,
        msg_opt: Option<String>,
        reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    },
    Generic_unify {
        pos: Pos,
        msg: String,
    },
    Using_error {
        pos: Pos,
        has_await: bool,
    },
    Bad_enum_decl(Pos),
    Bad_conditional_support_dynamic {
        pos: Pos,
        child: String,
        parent: String,
        ty_name: Lazy<String>,
        self_ty_name: Lazy<String>,
    },
    Bad_decl_override {
        pos: Pos,
        name: String,
        parent_name: String,
    },
    Explain_where_constraint {
        pos: Pos,
        in_class: bool,
        decl_pos: PosOrDecl,
    },
    Explain_constraint(Pos),
    Rigid_tvar_escape {
        pos: Pos,
        what: String,
    },
    Invalid_type_hint(Pos),
    Gated_by_feature_flag {
        pos: Pos,
        name: String,
        feature: String,
    },
    Tests_bypass_visibility_on_member_without_class {
        pos: Pos,
        member_name: String,
        class_name: String,
    },
    Unsatisfied_req {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    Unsatisfied_req_class {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    Unsatisfied_req_this_as {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
        req_name: String,
    },
    Req_class_not_final {
        pos: Pos,
        trait_pos: PosOrDecl,
        req_pos: PosOrDecl,
    },
    Incompatible_reqs {
        pos: Pos,
        req_name: String,
        req_class_pos: PosOrDecl,
        req_extends_pos: PosOrDecl,
    },
    Trait_not_used {
        pos: Pos,
        trait_name: String,
        req_class_pos: PosOrDecl,
        class_pos: PosOrDecl,
        class_name: String,
    },
    Invalid_echo_argument(Pos),
    Index_type_mismatch {
        pos: Pos,
        is_covariant_container: bool,
        msg_opt: Option<String>,
        reasons_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    },
    Member_not_found {
        pos: Pos,
        kind: MethodOrProperty,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Lazy<Option<(InstanceOrStatic, PosOrDecl, String)>>,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Construct_not_instance_method(Pos),
    Ambiguous_inheritance {
        pos: Pos,
        class_name: String,
        origin: String,
    },
    Expected_tparam {
        pos: Pos,
        decl_pos: PosOrDecl,
        n: isize,
    },
    Typeconst_concrete_concrete_override {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Constant_multiple_concrete_conflict {
        pos: Pos,
        name: String,
        definitions: Vec<(PosOrDecl, Option<String>)>,
    },
    Invalid_memoized_param {
        pos: Pos,
        ty_name: Lazy<String>,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Invalid_arraykey {
        pos: Pos,
        ctxt: ReadOrWrite,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        key_pos: PosOrDecl,
        key_ty_name: Lazy<String>,
    },
    Invalid_keyset_value {
        pos: Pos,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        value_pos: PosOrDecl,
        value_ty_name: Lazy<String>,
    },
    Invalid_set_value {
        pos: Pos,
        container_pos: PosOrDecl,
        container_ty_name: Lazy<String>,
        value_pos: PosOrDecl,
        value_ty_name: Lazy<String>,
    },
    Invalid_substring {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    Unset_nonidx_in_strict {
        pos: Pos,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Nullable_cast {
        pos: Pos,
        ty_pos: PosOrDecl,
        ty_name: Lazy<String>,
    },
    Hh_expect {
        pos: Pos,
        equivalent: bool,
    },
    Null_member {
        pos: Pos,
        obj_pos_opt: Option<Pos>,
        ctxt: ReadOrWrite,
        kind: MethodOrProperty,
        member_name: String,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Nullsafe_property_write_context(Pos),
    Uninstantiable_class {
        pos: Pos,
        class_name: String,
        reason_ty_opt: Option<(Pos, Lazy<String>)>,
        decl_pos: PosOrDecl,
    },
    Abstract_const_usage {
        pos: Pos,
        decl_pos: PosOrDecl,
        name: String,
    },
    Member_not_implemented {
        pos: Pos,
        member_name: String,
        decl_pos: PosOrDecl,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    Kind_mismatch {
        pos: Pos,
        decl_pos: PosOrDecl,
        tparam_name: String,
        expected_kind: String,
        actual_kind: String,
    },
    Trait_parent_construct_inconsistent {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Top_member {
        pos: Pos,
        ctxt: ReadOrWrite,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
        kind: MethodOrProperty,
        name: String,
        is_nullable: bool,
        ty_reasons: Lazy<Vec<(PosOrDecl, String)>>,
    },
    Unresolved_tyvar_projection {
        pos: Pos,
        proj_pos: PosOrDecl,
        tconst_name: String,
    },
    Cyclic_class_constant {
        pos: Pos,
        class_name: String,
        const_name: String,
    },
    Inout_annotation_missing {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Inout_annotation_unexpected {
        pos: Pos,
        decl_pos: PosOrDecl,
        param_is_variadic: bool,
        qfx_pos: Pos,
    },
    Inout_argument_bad_type {
        pos: Pos,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Invalid_meth_caller_inout_parameter {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Invalid_meth_caller_named_parameter {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Invalid_meth_caller_readonly_return {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    This_as_function_pointer_param {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Invalid_new_disposable(Pos),
    Invalid_return_disposable(Pos),
    Invalid_disposable_hint {
        pos: Pos,
        class_name: String,
    },
    Invalid_disposable_return_hint {
        pos: Pos,
        class_name: String,
    },
    Ambiguous_lambda {
        pos: Pos,
        uses: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Wrong_extend_kind {
        pos: Pos,
        kind: ClassishKind,
        name: String,
        parent_pos: PosOrDecl,
        parent_kind: ClassishKind,
        parent_name: String,
    },
    Wrong_use_kind {
        pos: Pos,
        name: String,
        parent_pos: PosOrDecl,
        parent_name: String,
    },
    Cyclic_class_def {
        pos: Pos,
        stack: SSet,
    },
    Trait_reuse_with_final_method {
        pos: Pos,
        trait_name: String,
        parent_cls_name: Lazy<String>,
        trace: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Trait_reuse_inside_class {
        pos: Pos,
        class_name: String,
        trait_name: String,
        occurrences: Vec<PosOrDecl>,
    },
    Invalid_is_as_expression_hint {
        pos: Pos,
        op: InvalidIsAsExpressionHintOp,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Invalid_enforceable_type {
        pos: Pos,
        ty_info: Lazy<Vec<Message<PosOrDecl>>>,
        tp_pos: PosOrDecl,
        tp_name: String,
        kind: InvalidEnforceableTypeKind,
    },
    Reifiable_attr {
        pos: Pos,
        ty_info: Lazy<Vec<Message<PosOrDecl>>>,
        attr_pos: PosOrDecl,
        kind: ReifiableAttrKind,
    },
    Invalid_newable_type_argument {
        pos: Pos,
        tp_pos: PosOrDecl,
        tp_name: String,
    },
    Invalid_newable_typaram_constraints {
        pos: Pos,
        tp_name: String,
        constraints: Vec<String>,
    },
    Override_per_trait {
        pos: Pos,
        class_name: String,
        meth_name: String,
        trait_name: String,
        meth_pos: PosOrDecl,
    },
    Should_not_be_override {
        pos: Pos,
        class_id: String,
        id: String,
    },
    Needs_concrete_in_final_class {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    Needs_concrete_on_instance_method {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    Needs_concrete_on_constructor {
        pos: Pos,
        class_name: String,
    },
    Call_needs_concrete {
        pos: Pos,
        class_name: String,
        meth_name: String,
        decl_pos: PosOrDecl,
        via: CallNeedsConcreteVia,
    },
    Abstract_access_via_static {
        pos: Pos,
        class_name: String,
        member_name: String,
        decl_pos: PosOrDecl,
        containing_method_pos: Option<Pos>,
    },
    Uninstantiable_class_via_static {
        pos: Pos,
        class_name: String,
        decl_pos: PosOrDecl,
        containing_method_pos: Option<Pos>,
    },
    Needs_concrete_override {
        pos: Pos,
        method_pos: PosOrDecl,
        parent_pos: PosOrDecl,
        method_name_for_method_defined_outside_class: Option<String>,
    },
    Trivial_strict_eq {
        pos: Pos,
        result: bool,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
        left_trail: Vec<PosOrDecl>,
        right_trail: Vec<PosOrDecl>,
    },
    Trivial_strict_not_nullable_compare_null {
        pos: Pos,
        result: bool,
        ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Eq_incompatible_types {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Comparison_invalid_types {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Strict_eq_value_incompatible_types {
        pos: Pos,
        left: Lazy<Vec<Message<PosOrDecl>>>,
        right: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Deprecated_use {
        pos: Pos,
        decl_pos_opt: Option<PosOrDecl>,
        msg: String,
    },
    Cannot_declare_constant {
        pos: Pos,
        class_pos: Pos,
        class_name: String,
    },
    Redeclaring_promoted_property {
        pos: Pos,
        prop_name: String,
        parent_pos: PosOrDecl,
        parent_name: String,
    },
    Invalid_classname(Pos),
    Illegal_type_structure {
        pos: Pos,
        msg: String,
        /// `fn`
        fn_: String,
    },
    Illegal_typeconst_direct_access(Pos),
    Wrong_expression_kind_attribute {
        pos: Pos,
        attr_name: String,
        expr_kind: String,
        attr_class_pos: PosOrDecl,
        attr_class_name: String,
        intf_name: String,
    },
    Ambiguous_object_access {
        pos: Pos,
        name: String,
        self_pos: PosOrDecl,
        vis: String,
        subclass_pos: PosOrDecl,
        class_self: String,
        class_subclass: String,
    },
    Invalid_arraykey_constraint {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    Redundant_generic {
        pos: Pos,
        variance: RedundantGenericVariance,
        msg: String,
        suggest: String,
    },
    Meth_caller_trait {
        pos: Pos,
        trait_name: String,
    },
    Duplicate_interface {
        pos: Pos,
        name: String,
        others: Vec<PosOrDecl>,
    },
    Enum_duplicate_value {
        /// the enum definition
        pos: Pos,
        value: String,
        member_name: String,
        member_pos: PosOrDecl,
        prev_name: String,
        prev_pos: PosOrDecl,
    },
    Enum_uncheckable_value {
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
    Reified_function_reference(Pos),
    Reinheriting_classish_const {
        pos: Pos,
        classish_name: String,
        src_pos: Pos,
        src_classish_name: String,
        existing_const_origin: String,
        const_name: String,
    },
    Redeclaring_classish_const {
        pos: Pos,
        classish_name: String,
        redeclaration_pos: Pos,
        existing_const_origin: String,
        const_name: String,
    },
    Abstract_function_pointer {
        pos: Pos,
        class_name: String,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    Inherited_class_member_with_different_case {
        pos: Pos,
        member_type: String,
        name: String,
        name_prev: String,
        child_class: String,
        prev_class: String,
        prev_class_pos: PosOrDecl,
    },
    Multiple_inherited_class_member_with_different_case {
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
    Multiple_instantiation_inheritence {
        type_name: String,
        implements_or_extends: String,
        interface_name: String,
        winning_implements: ImplementsInfo,
        losing_implements: ImplementsInfo,
    },
    Parent_support_dynamic_type {
        pos: Pos,
        child_name: String,
        child_kind: ClassishKind,
        parent_name: String,
        parent_kind: ClassishKind,
        child_support_dyn: bool,
    },
    Property_is_not_enforceable {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    Property_is_not_dynamic {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    Private_property_is_not_enforceable {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    Private_property_is_not_dynamic {
        pos: Pos,
        prop_name: String,
        class_name: String,
        prop_pos: PosOrDecl,
        prop_type: String,
    },
    Immutable_local(Pos),
    Require_dynamic_obj_get {
        receiver_pos: Pos,
        receiver_ty: Lazy<String>,
        receiver_ty_pos: PosOrDecl,
        member_kind: RequireDynamicObjGetMemberKind,
        member_name: Option<DynamicObjGetMember>,
    },
    Nonsense_member_selection {
        pos: Pos,
        kind: String,
    },
    Consider_meth_caller {
        pos: Pos,
        class_name: String,
        meth_name: String,
    },
    Method_import_via_diamond {
        pos: Pos,
        class_name: String,
        method_pos: PosOrDecl,
        method_name: String,
        trace1: Lazy<Vec<Message<PosOrDecl>>>,
        trace2: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Property_import_via_diamond {
        generic: bool,
        pos: Pos,
        class_name: String,
        property_pos: PosOrDecl,
        property_name: String,
        trace1: Lazy<Vec<Message<PosOrDecl>>>,
        trace2: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Unification_cycle {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    Method_variance(Pos),
    Explain_tconst_where_constraint {
        pos: Pos,
        decl_pos: PosOrDecl,
        msgs: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Format_string {
        pos: Pos,
        snippet: String,
        fmt_string: String,
        class_pos: PosOrDecl,
        fn_name: String,
        class_suggest: String,
    },
    Expected_literal_format_string(Pos),
    Re_prefixed_non_string {
        pos: Pos,
        reason: RePrefixedNonStringReason,
    },
    Bad_regex_pattern {
        pos: Pos,
        reason: BadRegexPatternReason,
    },
    Option_return_only_typehint {
        pos: Pos,
        kind: OptionReturnOnlyTypehintKind,
    },
    Redeclaring_missing_method {
        pos: Pos,
        trait_method: String,
    },
    Expecting_type_hint(Pos),
    Expecting_type_hint_variadic(Pos),
    Expecting_return_type_hint(Pos),
    Duplicate_using_var(Pos),
    Illegal_disposable {
        pos: Pos,
        verb: IllegalDisposableVerb,
    },
    Escaping_disposable(Pos),
    Escaping_disposable_param(Pos),
    Escaping_this(Pos),
    Must_extend_disposable(Pos),
    Field_kinds {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Unbound_name {
        pos: Pos,
        name: String,
        class_exists: bool,
    },
    Previous_default(Pos),
    Previous_default_or_optional(Pos),
    Return_in_void {
        pos: Pos,
        decl_pos: Pos,
    },
    This_var_outside_class(Pos),
    Unbound_global(Pos),
    Private_meth_caller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Protected_meth_caller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Internal_meth_caller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Protected_internal_meth_caller {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Array_cast(Pos),
    String_cast {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    Static_outside_class(Pos),
    Self_outside_class(Pos),
    New_inconsistent_construct {
        pos: Pos,
        class_pos: PosOrDecl,
        class_name: String,
        kind: NewInconsistentConstructKind,
    },
    Parent_outside_class(Pos),
    Parent_abstract_call {
        pos: Pos,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    Self_abstract_call {
        pos: Pos,
        self_pos: Pos,
        meth_name: String,
        decl_pos: PosOrDecl,
    },
    Classname_abstract_call {
        pos: Pos,
        meth_name: String,
        class_name: String,
        decl_pos: PosOrDecl,
    },
    Static_synthetic_method {
        pos: Pos,
        meth_name: String,
        class_name: String,
        decl_pos: PosOrDecl,
    },
    Static_call_on_trait_require_non_strict {
        pos: Pos,
        meth_name: String,
        trait_name: String,
        req_constraint_name: String,
        req_constraint_kind: StaticCallOnTraitRequireNonStrictReqConstraintKind,
        trait_pos: PosOrDecl,
    },
    Static_prop_on_trait {
        pos: Pos,
        meth_name: String,
        trait_name: String,
        trait_pos: PosOrDecl,
    },
    Isset_in_strict(Pos),
    Isset_inout_arg(Pos),
    Unpacking_disallowed_builtin_function {
        pos: Pos,
        fn_name: String,
    },
    Array_get_arity {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    Undefined_field {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    Array_access {
        pos: Pos,
        ctxt: ReadOrWrite,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    Keyset_set {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Array_append {
        pos: Pos,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    Const_mutation {
        pos: Pos,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    Expected_class {
        pos: Pos,
        suffix: Option<Lazy<String>>,
    },
    Unknown_type {
        pos: Pos,
        expected: String,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Parent_in_trait(Pos),
    Parent_undefined {
        pos: Pos,
        trait_reqs: Option<Vec<PosOrDecl>>,
    },
    Constructor_no_args(Pos),
    Visibility {
        pos: Pos,
        msg: String,
        decl_pos: PosOrDecl,
        reason_msg: String,
    },
    Bad_call {
        pos: Pos,
        ty_name: Lazy<String>,
    },
    Extend_final {
        pos: Pos,
        name: String,
        decl_pos: PosOrDecl,
    },
    Extend_sealed {
        pos: Pos,
        parent_pos: PosOrDecl,
        parent_name: String,
        parent_kind: ExtendSealedParentKind,
        verb: ExtendSealedVerb,
    },
    Trait_prop_const_class {
        pos: Pos,
        name: String,
    },
    Implement_abstract {
        pos: Pos,
        is_final: bool,
        decl_pos: PosOrDecl,
        trace: Lazy<Vec<Message<PosOrDecl>>>,
        name: String,
        kind: ImplementAbstractKind,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    Abstract_member_in_concrete_class {
        pos: Pos,
        class_name_pos: Pos,
        is_final: bool,
        member_kind: AbstractMemberInConcreteClassMemberKind,
        member_name: String,
    },
    Generic_static {
        pos: Pos,
        typaram_name: String,
    },
    Object_string {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Object_string_deprecated(Pos),
    Cyclic_typedef {
        def_pos: Pos,
        use_pos: PosOrDecl,
    },
    Require_args_reify {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Require_generic_explicit {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
    },
    Invalid_reified_arg {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
        arg_info: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Invalid_reified_arg_reifiable {
        pos: Pos,
        param_name: String,
        decl_pos: PosOrDecl,
        ty_pos: PosOrDecl,
        ty_msg: Lazy<String>,
    },
    New_class_reified {
        pos: Pos,
        class_kind: String,
        suggested_class_name: Option<String>,
    },
    Class_get_reified(Pos),
    Static_meth_with_class_reified_generic {
        pos: Pos,
        generic_pos: Pos,
    },
    Consistent_construct_reified(Pos),
    Bad_fn_ptr_construction(Pos),
    Reified_generics_not_allowed(Pos),
    New_without_newable {
        pos: Pos,
        name: String,
    },
    Discarded_awaitable {
        pos: Pos,
        decl_pos: PosOrDecl,
    },
    Unknown_object_member {
        pos: Pos,
        member_name: String,
        elt: MethOrProp,
        reason: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Non_class_member {
        pos: Pos,
        member_name: String,
        elt: MethOrProp,
        ty_name: Lazy<String>,
        decl_pos: PosOrDecl,
    },
    Null_container {
        pos: Pos,
        null_witness: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Declared_covariant {
        pos: Pos,
        param_pos: Pos,
        msgs: Lazy<Vec<Message<Pos>>>,
    },
    Declared_contravariant {
        pos: Pos,
        param_pos: Pos,
        msgs: Lazy<Vec<Message<Pos>>>,
    },
    Static_prop_type_generic_param {
        pos: Pos,
        var_ty_pos: PosOrDecl,
        class_pos: PosOrDecl,
    },
    Contravariant_this {
        pos: Pos,
        class_name: String,
        typaram_name: String,
    },
    Cyclic_typeconst {
        pos: Pos,
        tyconst_names: Vec<String>,
    },
    Array_get_with_optional_field {
        recv_pos: Pos,
        field_pos: Pos,
        field_name: String,
        decl_pos: PosOrDecl,
    },
    Mutating_const_property(Pos),
    Self_const_parent_not(Pos),
    Unexpected_ty_in_tast {
        pos: Pos,
        expected_ty: Lazy<String>,
        actual_ty: Lazy<String>,
    },
    Call_lvalue(Pos),
    Unsafe_cast_await(Pos),
    // == Primary and secondary ================================================
    Smember_not_found {
        pos: Pos,
        kind: SmemberNotFoundKind,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
        quickfixes: Vec<Quickfix<Pos>>,
    },
    Type_arity_mismatch {
        pos: Pos,
        actual: isize,
        decl_pos: PosOrDecl,
        expected: isize,
    },
    Typing_too_many_args {
        pos: Pos,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
        /// Hint for converting mandatory arguments into optional, takes
        /// positions of the argument to be converted
        hint_convert_to_optional: Option<PosOrDecl>,
    },
    Typing_too_few_args {
        pos: Pos,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
        /// Hint for adding missing optional arguments, takes positions of
        /// declaration for optional arguments
        hint_missing_optional: Option<PosOrDecl>,
    },
    Missing_named_args {
        pos: Pos,
        decl_pos: PosOrDecl,
        missing_names: Vec<String>,
    },
    Unexpected_named_args {
        pos: Pos,
        decl_pos: PosOrDecl,
        unexpected_names: Vec<String>,
    },
    Duplicate_named_args {
        pos: Pos,
        duplicate_names: Vec<String>,
    },
    Non_object_member {
        pos: Pos,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
        ctxt: ReadOrWrite,
        member_name: String,
        kind: NonObjectMemberKind,
    },
    Static_instance_intersection {
        class_pos: Pos,
        instance_pos: Lazy<PosOrDecl>,
        static_pos: Lazy<PosOrDecl>,
        member_name: String,
        kind: MethOrProp,
    },
    Match_not_exhaustive {
        pos: Pos,
        ty_not_covered: Lazy<String>,
    },
    Match_on_unsupported_type {
        pos: Pos,
        expr_ty: Lazy<String>,
        unsupported_tys: Vec<Lazy<String>>,
    },
    Class_const_to_string {
        pos: Pos,
        cls_name: String,
    },
    Class_pointer_to_string {
        pos: Pos,
        ty: String,
    },
    String_to_class_pointer {
        pos: Pos,
        cls_name: String,
        ty_pos: PosOrDecl,
    },
    Optional_parameter_not_supported(Pos),
    Optional_parameter_not_abstract(Pos),
}
