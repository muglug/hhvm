// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typing_error.Secondary`
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
    fn_,
    fn_return,
    param,
}

/// ``kind: [ `constant | `method_ | `property | `typeconst ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractConcreteOverrideKind {
    constant,
    method_,
    property,
    typeconst,
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
#[derive(Clone, Debug)]
pub enum T {
    Of_error(Box<error::T>),
    // == Primary and secondary ================================================
    Smember_not_found {
        pos: PosOrDecl,
        kind: SmemberNotFoundKind,
        class_name: String,
        class_pos: PosOrDecl,
        member_name: String,
        hint: Option<(InstanceOrStatic, PosOrDecl, String)>,
    },
    Type_arity_mismatch {
        pos: PosOrDecl,
        actual: isize,
        decl_pos: PosOrDecl,
        expected: isize,
    },
    Typing_too_many_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    Typing_too_few_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    Non_object_member {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
        ctxt: ReadOrWrite,
        member_name: String,
        kind: NonObjectMemberKind,
    },
    Rigid_tvar_escape {
        pos: PosOrDecl,
        name: String,
    },
    Concrete_const_interface_override {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        parent_origin: String,
        name: String,
    },
    Interface_or_trait_const_multiple_defs {
        pos: PosOrDecl,
        origin: String,
        name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    Interface_typeconst_multiple_defs {
        pos: PosOrDecl,
        origin: String,
        is_abstract: bool,
        name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    Visibility_extends {
        pos: PosOrDecl,
        vis: String,
        parent_pos: PosOrDecl,
        parent_vis: String,
    },
    Visibility_override_internal {
        pos: PosOrDecl,
        module_name: Option<String>,
        parent_pos: PosOrDecl,
        parent_module: String,
    },
    Abstract_tconst_not_allowed {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        tconst_name: String,
    },
    Missing_constructor(PosOrDecl),
    Missing_field {
        pos: PosOrDecl,
        name: String,
        decl_pos: PosOrDecl,
        reason_sub: typing_reason::T,
        reason_super: typing_reason::T,
    },
    Shape_fields_unknown {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Splat_may_require_fields {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        name: Option<String>,
    },
    Splat_field_not_known {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        name: String,
        field: String,
    },
    Accept_disposable_invariant {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Invalid_destructure {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        ty_name: Lazy<String>,
    },
    Unpack_array_required_argument {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Unpack_array_variadic_argument {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Fun_too_many_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    Fun_too_few_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        actual: isize,
        expected: isize,
    },
    Fun_unexpected_nonvariadic {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Fun_variadicity_hh_vs_php56 {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Fun_extra_named_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        extra_names: Vec<String>,
    },
    Fun_missing_named_args {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        missing_names: Vec<String>,
    },
    Fun_param_required_but_expected_optional {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        /// If empty, this is a positional parameter
        param_names: Vec<String>,
    },
    Required_field_is_optional {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
        def_pos: PosOrDecl,
        name: String,
        reason_sub: typing_reason::T,
        reason_super: typing_reason::T,
    },
    Return_disposable_mismatch {
        pos_sub: PosOrDecl,
        is_marked_return_disposable: bool,
        pos_super: PosOrDecl,
    },
    Overriding_prop_const_mismatch {
        pos: PosOrDecl,
        is_const: bool,
        parent_pos: PosOrDecl,
        parent_is_const: bool,
    },
    Override_final {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    Override_tests_bypass_visibility {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    Abstract_tests_bypass_visibility_missing_attr {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    Override_async {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    Override_lsb {
        pos: PosOrDecl,
        member_name: String,
        parent_pos: PosOrDecl,
    },
    Multiple_concrete_defs {
        pos: PosOrDecl,
        name: String,
        origin: String,
        class_name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    Cyclic_enum_constraint(PosOrDecl),
    Inoutness_mismatch {
        pos: PosOrDecl,
        decl_pos: PosOrDecl,
    },
    Bad_lateinit_override {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        parent_is_lateinit: bool,
    },
    Bad_method_override {
        pos: PosOrDecl,
        member_name: String,
    },
    Bad_member_override_not_subtype {
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
    Bad_prop_override {
        pos: PosOrDecl,
        member_name: String,
    },
    Bad_xhp_attr_required_override {
        pos: PosOrDecl,
        tag: String,
        parent_pos: PosOrDecl,
        parent_tag: String,
    },
    Coeffect_subtyping {
        pos: PosOrDecl,
        cap: Lazy<String>,
        pos_expected: PosOrDecl,
        cap_expected: Lazy<String>,
    },
    Override_method_support_dynamic_type {
        pos: PosOrDecl,
        method_name: String,
        parent_pos: PosOrDecl,
        parent_origin: String,
    },
    Readonly_mismatch {
        pos: PosOrDecl,
        kind: ReadonlyMismatchKind,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Require_package_mismatch {
        pos: PosOrDecl,
        reason_sub: Lazy<Vec<Message<PosOrDecl>>>,
        reason_super: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Not_sub_dynamic {
        pos: PosOrDecl,
        ty_name: Lazy<String>,
        dynamic_part: Lazy<Vec<Message<PosOrDecl>>>,
    },
    Subtyping_error {
        cstrs: Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>>,
        ty_sub: crate::typing_defs_constraints::InternalType,
        ty_sup: crate::typing_defs_constraints::InternalType,
        is_coeffect: bool,
    },
    Method_not_dynamically_callable {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    This_final {
        pos_sub: PosOrDecl,
        pos_super: PosOrDecl,
        class_name: String,
    },
    Typeconst_concrete_concrete_override {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    Abstract_concrete_override {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
        kind: AbstractConcreteOverrideKind,
    },
    Override_no_default_typeconst {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
    Unsupported_refinement(PosOrDecl),
    Splat_not_a_shape(PosOrDecl),
    Missing_class_constant {
        pos: PosOrDecl,
        class_name: String,
        const_name: String,
    },
    Invalid_refined_const_kind {
        pos: PosOrDecl,
        class_name: String,
        const_name: String,
        correct_kind: String,
        wrong_kind: String,
    },
    Inexact_tconst_access(PosOrDecl, (PosOrDecl, String)),
    Violated_refinement_constraint {
        cstr: (ViolatedRefinementConstraintCstr, PosOrDecl),
    },
    Unknown_label {
        enum_name: String,
        decl_pos: PosOrDecl,
        most_similar: Option<(String, PosOrDecl)>,
    },
    Higher_rank_tparam_escape {
        tvar_pos: PosOrDecl,
        pos_with_generic: PosOrDecl,
        generic_reason: typing_reason::T,
        generic_name: Option<String>,
    },
    Override_sealed {
        pos: PosOrDecl,
        parent_pos: PosOrDecl,
    },
}
