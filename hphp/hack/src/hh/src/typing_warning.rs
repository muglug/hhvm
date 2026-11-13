// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_warning.ml`. See `hh/PORTING.md`.
//!
//! Each OCaml submodule `Foo_bar` is the module `foo_bar` here, with its
//! record `t` as `foo_bar::T` and its constructors under their OCaml names.
//!
//! `('x, 'a) kind` is a GADT in OCaml: a constructor fixes the type of the
//! warning's data (`'x`) and whether the warning was migrated from a lint
//! (`'a`). Here it is [`Kind<X, A>`], and the constructors are associated
//! constants of the instance they belong to, so that
//! `(pos, Typing_warning.Sketchy_equality, { result; ... })` is written
//! `(pos, typing_warning::Kind::Sketchy_equality, typing_warning::sketchy_equality::T { result, .. })`
//! and only typechecks with the data that constructor has in OCaml.

#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

use std::marker::PhantomData;
use std::sync::LazyLock;

use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

/// `'a Lazy.t`: the data of a warning that is only computed if the warning is
/// reported. Build one with `Lazy::new(Box::new(move || ...))` and read it
/// with `Lazy::force(&x)`.
pub type Lazy<'a, T> = LazyLock<T, Box<dyn FnOnce() -> T + 'a>>;

/// `type warn = private Warn_tag`
#[derive(Debug)]
pub enum Warn {}

/// `type migrated = private Migrated_tag`
#[derive(Debug)]
pub enum Migrated {}

#[derive(Clone, Debug)]
pub struct Quickfix {
    pub can_be_captured: bool,
    pub original_pos: Pos,
    pub replacement_pos: Pos,
}

pub mod is_as_always {
    #[derive(Clone, Debug)]
    pub enum Kind {
        Is_is_always_true,
        Is_is_always_false,
        As_always_succeeds(super::Quickfix),
        As_always_fails { is_nullable: bool },
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub lhs_ty: String,
        pub rhs_ty: String,
    }
}

pub mod null_coalesce_always {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub enum Kind {
        Null_coalesce_always_null,
        Null_coalesce_never_null,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub lhs_pos: PosOrDecl,
        pub lhs_ty: String,
    }
}

pub mod non_disjoint_check {
    #[derive(Clone, Debug)]
    pub struct T {
        pub name: String,
        pub ty1: String,
        pub ty2: String,
        pub dynamic: bool,
    }
}

pub mod sketchy_equality {
    use super::Lazy;
    use super::Message;
    use super::PosOrDecl;

    #[derive(Debug)]
    pub struct T<'a> {
        pub result: bool,
        pub left: Lazy<'a, Vec<Message<PosOrDecl>>>,
        pub right: Lazy<'a, Vec<Message<PosOrDecl>>>,
        pub left_trail: Vec<PosOrDecl>,
        pub right_trail: Vec<PosOrDecl>,
    }
}

pub mod cast_non_primitive {
    #[derive(Clone, Debug)]
    pub struct T {
        pub cast_hint: String,
        pub ty: String,
    }
}

pub mod truthiness_test {
    #[derive(Clone, Debug)]
    pub enum SketchyKind {
        String,
        Arraykey,
        Stringish,
        Xhp_child,
        Traversable,
    }

    #[derive(Clone, Debug)]
    pub enum Kind {
        Invalid { truthy: bool },
        Sketchy(SketchyKind),
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub ty: std::string::String,
        pub expr: Option<std::string::String>,
        pub not: bool,
    }
}

pub mod equality_check {
    #[derive(Clone, Debug)]
    pub enum Kind {
        Equality(bool),
        Switch,
        Contains,
        Contains_key,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub ty1: String,
        pub ty2: String,
    }
}

pub mod duplicate_properties {
    #[derive(Clone, Debug)]
    pub struct T {
        pub class_name: String,
        pub prop_name: String,
        pub class_names: Vec<String>,
        pub initialized_with_constant: bool,
    }
}

pub mod class_pointer_to_string {
    use oxidized::pos::Pos;

    #[derive(Clone, Debug)]
    pub struct T {
        pub pos: Pos,
        pub ty: String,
    }
}

pub mod no_disjoint_union_check {
    use super::Lazy;
    use super::PosOrDecl;

    #[derive(Debug)]
    pub struct T<'a> {
        pub disjuncts: Lazy<'a, Vec<(PosOrDecl, String)>>,
        pub tparam_pos: PosOrDecl,
    }
}

pub mod switch_redundancy {
    use super::Lazy;
    use super::Pos;

    #[derive(Debug)]
    pub enum T<'a> {
        /// Primary position on the switch
        SwitchHasRedundancy {
            positions: Lazy<'a, Vec<Pos>>,
            redundancy_size: isize,
        },
        /// Primary position is on the duplicate occurrence of the case
        DuplicatedCase {
            first_occurrence: Pos,
            case: Lazy<'a, String>,
        },
        /// Primary position on the default
        RedundantDefault,
    }
}

pub mod static_call_on_trait {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub meth_name: String,
        pub trait_name: String,
        pub trait_pos: PosOrDecl,
    }
}

pub mod static_property_override {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub prop_name: String,
        pub child_prop_pos: PosOrDecl,
    }
}

pub mod string_to_class_pointer {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub cls_name: String,
        pub ty_pos: PosOrDecl,
    }
}

pub mod call_needs_concrete {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    /// ``[ `Id | `Self | `Parent | `Static ]``
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Via {
        Id,
        Self_,
        Parent,
        Static,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub call_pos: Pos,
        pub class_name: String,
        pub meth_name: String,
        pub decl_pos: PosOrDecl,
        pub via: Via,
    }
}

pub mod abstract_access_via_static {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub access_pos: Pos,
        pub class_name: String,
        pub member_name: String,
        pub decl_pos: PosOrDecl,
        pub containing_method_pos: Option<Pos>,
    }
}

pub mod uninstantiable_class_via_static {
    use oxidized::pos::Pos;
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub usage_pos: Pos,
        pub class_name: String,
        pub decl_pos: PosOrDecl,
        pub containing_method_pos: Option<Pos>,
    }
}

pub mod needs_concrete_override {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub pos: PosOrDecl,
        pub parent_pos: PosOrDecl,
        /// `Some m` iff `m` is a trait method of a trait that is used by the
        /// class. In such cases, the location for the warning will be a class
        /// name, so we need to preserve the method name to give a meaningful
        /// error message.
        /// Example:   `class Child extends Parent { use Tr; }`
        ///                   ~~~~~
        /// where trait `Tr` defines the method with the incorrect override of
        /// `Parent::m`
        pub method_name_for_method_defined_outside_class: Option<String>,
    }
}

pub mod expect_bool_for_condition {
    #[derive(Clone, Debug)]
    pub struct T {
        pub ty: String,
    }
}

pub mod redundant_nullsafe_operation {
    #[derive(Clone, Debug)]
    pub enum Kind {
        Redundant_nullsafe_member_select,
        Nullsafe_member_select_on_null,
        Redundant_nullsafe_pipe,
        Nullsafe_pipe_on_null,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub ty: String,
    }
}

pub mod unbound_name_warning {
    #[derive(Clone, Debug)]
    pub struct T {
        pub name: String,
        pub kind_str: String,
    }
}

pub mod set_or_keyset_array_get {
    use oxidized::pos::Pos;

    #[derive(Clone, Debug)]
    pub enum Kind {
        Keyset,
        ConstSet,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub ty: String,
        pub full_expr_pos: Pos,
        /// The replacement text for the quickfix, if source text was
        /// available.
        /// For keyset: `C\contains_key($arr, $idx)`
        /// For ConstSet: `$arr->contains($idx)`
        pub replacement_text: Option<String>,
    }
}

pub mod sealed_not_subtype {
    #[derive(Clone, Debug)]
    pub struct T {
        pub verb: String,
        pub parent_name: String,
        pub parent_method_name: Option<String>,
        pub child_name: String,
        pub child_kind: String,
    }
}

pub mod tany_found {
    pub type T = ();
}

pub mod consistent_construct_abstract_final {
    #[derive(Clone, Debug)]
    pub struct T {
        pub name: String,
        pub inherited_from: Option<String>,
    }
}

pub mod dynamic_call {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub enum Kind {
        Method_invocation,
        Function_call,
        Array_index,
        Array_append,
        Property_access,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub actual_type: String,
        pub dynamic_reason_pos: PosOrDecl,
        pub dynamic_reason_msg: String,
    }
}

pub mod sealed_not_override {
    #[derive(Clone, Debug)]
    pub struct T {
        pub method_name: String,
        pub method_def: String,
        pub allowlist_class_name: String,
        pub allowlist_class_kind: String,
    }
}

pub mod redundant_require_this_as {
    #[derive(Clone, Debug)]
    pub struct T {
        pub trait_name: String,
        pub class_name: String,
    }
}

/// The constructors of `kind`, without the types they are indexed by: what a
/// function that is polymorphic in `('x, 'a) kind` matches on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KindTag {
    Sketchy_equality,
    Is_as_always,
    Non_disjoint_check,
    Cast_non_primitive,
    Truthiness_test,
    Equality_check,
    Duplicate_properties,
    Class_pointer_to_string,
    No_disjoint_union_check,
    Switch_redundancy,
    Static_call_on_trait,
    Static_property_override,
    String_to_class_pointer,
    Null_coalesce_always,
    Call_needs_concrete,
    Abstract_access_via_static,
    Uninstantiable_class_via_static,
    Needs_concrete_override,
    Expect_bool_for_condition,
    Redundant_nullsafe_operation,
    Unbound_name_warning,
    Set_or_keyset_array_get,
    Sealed_not_subtype,
    Tany_found,
    Consistent_construct_abstract_final,
    Dynamic_call,
    Sealed_not_override,
    Redundant_require_this_as,
}

/// `('x, 'a) kind`. The only values are the constants below, one for each
/// OCaml constructor (`Kind::Sketchy_equality`, ...).
pub struct Kind<X, A> {
    tag: KindTag,
    marker: PhantomData<fn() -> (X, A)>,
}

impl<X, A> Kind<X, A> {
    const fn new(tag: KindTag) -> Self {
        Kind {
            tag,
            marker: PhantomData,
        }
    }

    /// Which constructor this is.
    pub fn tag(&self) -> KindTag {
        self.tag
    }
}

impl<X, A> Clone for Kind<X, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<X, A> Copy for Kind<X, A> {}

impl<X, A> std::fmt::Debug for Kind<X, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.tag.fmt(f)
    }
}

impl<'a> Kind<sketchy_equality::T<'a>, Warn> {
    pub const Sketchy_equality: Self = Self::new(KindTag::Sketchy_equality);
}

impl Kind<is_as_always::T, Migrated> {
    pub const Is_as_always: Self = Self::new(KindTag::Is_as_always);
}

impl Kind<non_disjoint_check::T, Migrated> {
    pub const Non_disjoint_check: Self = Self::new(KindTag::Non_disjoint_check);
}

impl Kind<cast_non_primitive::T, Migrated> {
    pub const Cast_non_primitive: Self = Self::new(KindTag::Cast_non_primitive);
}

impl Kind<truthiness_test::T, Migrated> {
    pub const Truthiness_test: Self = Self::new(KindTag::Truthiness_test);
}

impl Kind<equality_check::T, Migrated> {
    pub const Equality_check: Self = Self::new(KindTag::Equality_check);
}

impl Kind<duplicate_properties::T, Migrated> {
    pub const Duplicate_properties: Self = Self::new(KindTag::Duplicate_properties);
}

impl Kind<class_pointer_to_string::T, Warn> {
    pub const Class_pointer_to_string: Self = Self::new(KindTag::Class_pointer_to_string);
}

impl<'a> Kind<no_disjoint_union_check::T<'a>, Warn> {
    pub const No_disjoint_union_check: Self = Self::new(KindTag::No_disjoint_union_check);
}

impl<'a> Kind<switch_redundancy::T<'a>, Warn> {
    pub const Switch_redundancy: Self = Self::new(KindTag::Switch_redundancy);
}

impl Kind<static_call_on_trait::T, Warn> {
    pub const Static_call_on_trait: Self = Self::new(KindTag::Static_call_on_trait);
}

impl Kind<static_property_override::T, Warn> {
    pub const Static_property_override: Self = Self::new(KindTag::Static_property_override);
}

impl Kind<string_to_class_pointer::T, Warn> {
    pub const String_to_class_pointer: Self = Self::new(KindTag::String_to_class_pointer);
}

impl Kind<null_coalesce_always::T, Warn> {
    pub const Null_coalesce_always: Self = Self::new(KindTag::Null_coalesce_always);
}

impl Kind<call_needs_concrete::T, Warn> {
    pub const Call_needs_concrete: Self = Self::new(KindTag::Call_needs_concrete);
}

impl Kind<abstract_access_via_static::T, Warn> {
    pub const Abstract_access_via_static: Self = Self::new(KindTag::Abstract_access_via_static);
}

impl Kind<uninstantiable_class_via_static::T, Warn> {
    pub const Uninstantiable_class_via_static: Self =
        Self::new(KindTag::Uninstantiable_class_via_static);
}

impl Kind<needs_concrete_override::T, Warn> {
    pub const Needs_concrete_override: Self = Self::new(KindTag::Needs_concrete_override);
}

impl Kind<expect_bool_for_condition::T, Warn> {
    pub const Expect_bool_for_condition: Self = Self::new(KindTag::Expect_bool_for_condition);
}

impl Kind<redundant_nullsafe_operation::T, Warn> {
    pub const Redundant_nullsafe_operation: Self =
        Self::new(KindTag::Redundant_nullsafe_operation);
}

impl Kind<unbound_name_warning::T, Warn> {
    pub const Unbound_name_warning: Self = Self::new(KindTag::Unbound_name_warning);
}

impl Kind<set_or_keyset_array_get::T, Warn> {
    pub const Set_or_keyset_array_get: Self = Self::new(KindTag::Set_or_keyset_array_get);
}

impl Kind<sealed_not_subtype::T, Warn> {
    pub const Sealed_not_subtype: Self = Self::new(KindTag::Sealed_not_subtype);
}

impl Kind<tany_found::T, Warn> {
    pub const Tany_found: Self = Self::new(KindTag::Tany_found);
}

impl Kind<consistent_construct_abstract_final::T, Warn> {
    pub const Consistent_construct_abstract_final: Self =
        Self::new(KindTag::Consistent_construct_abstract_final);
}

impl Kind<dynamic_call::T, Warn> {
    pub const Dynamic_call: Self = Self::new(KindTag::Dynamic_call);
}

impl Kind<sealed_not_override::T, Warn> {
    pub const Sealed_not_override: Self = Self::new(KindTag::Sealed_not_override);
}

impl Kind<redundant_require_this_as::T, Warn> {
    pub const Redundant_require_this_as: Self = Self::new(KindTag::Redundant_require_this_as);
}

/// `type ('x, 'a) t = Pos.t * ('x, 'a) kind * 'x`
pub type T<X, A> = (Pos, Kind<X, A>, X);
