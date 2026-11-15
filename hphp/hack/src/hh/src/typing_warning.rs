// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_warning.ml`. See `hh/PORTING.md`.
//!
//! Each OCaml submodule `Foo_bar` is the module `foo_bar` here, with its
//! record `t` as `foo_bar::T` and its constructors in the UpperCamelCase of
//! their OCaml names (`Is_is_always_true` is `IsIsAlwaysTrue`).
//!
//! `('x, 'a) kind` is a GADT in OCaml: a constructor fixes the type of the
//! warning's data (`'x`) and whether the warning was migrated from a lint
//! (`'a`). Here it is [`Kind<X, A>`], and the constructors are associated
//! constants of the instance they belong to, so that
//! `(pos, Typing_warning.Sketchy_equality, { result; ... })` is written
//! `(pos, typing_warning::Kind::Sketchy_equality, typing_warning::sketchy_equality::T { result, .. })`
//! and only typechecks with the data that constructor has in OCaml.

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
        IsIsAlwaysTrue,
        IsIsAlwaysFalse,
        AsAlwaysSucceeds(super::Quickfix),
        AsAlwaysFails { is_nullable: bool },
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
        NullCoalesceAlwaysNull,
        NullCoalesceNeverNull,
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
        XhpChild,
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
        ContainsKey,
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

pub mod readonly_property_override {
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

pub mod expect_bool_for_condition {
    #[derive(Clone, Debug)]
    pub struct T {
        pub ty: String,
    }
}

pub mod redundant_nullsafe_operation {
    #[derive(Clone, Debug)]
    pub enum Kind {
        RedundantNullsafeMemberSelect,
        NullsafeMemberSelectOnNull,
        RedundantNullsafePipe,
        NullsafePipeOnNull,
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
        MethodInvocation,
        FunctionCall,
        ArrayIndex,
        ArrayAppend,
        PropertyAccess,
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub kind: Kind,
        pub actual_type: String,
        pub dynamic_reason_pos: PosOrDecl,
        pub dynamic_reason_msg: String,
    }
}

pub mod dynamic_return {
    use oxidized::pos_or_decl::PosOrDecl;

    #[derive(Clone, Debug)]
    pub struct T {
        pub return_type: String,
        pub return_type_pos: PosOrDecl,
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

pub mod redundant_concurrent {
    /// `unit` in OCaml; a type of its own here, because the renderer of a
    /// warning is chosen by the type of its data (`tany_found::T` is `()`).
    #[derive(Clone, Debug)]
    pub struct T;
}

/// The constructors of `kind`, without the types they are indexed by: what a
/// function that is polymorphic in `('x, 'a) kind` matches on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KindTag {
    SketchyEquality,
    IsAsAlways,
    NonDisjointCheck,
    CastNonPrimitive,
    TruthinessTest,
    EqualityCheck,
    DuplicateProperties,
    ClassPointerToString,
    NoDisjointUnionCheck,
    SwitchRedundancy,
    StaticCallOnTrait,
    StaticPropertyOverride,
    ReadonlyPropertyOverride,
    StringToClassPointer,
    NullCoalesceAlways,
    CallNeedsConcrete,
    ExpectBoolForCondition,
    RedundantNullsafeOperation,
    UnboundNameWarning,
    SetOrKeysetArrayGet,
    SealedNotSubtype,
    TanyFound,
    ConsistentConstructAbstractFinal,
    DynamicCall,
    DynamicReturn,
    SealedNotOverride,
    RedundantRequireThisAs,
    RedundantConcurrent,
}

/// `('x, 'a) kind`. The only values are the constants below, one for each
/// OCaml constructor (`Kind::SKETCHY_EQUALITY`, ...).
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
    pub const SKETCHY_EQUALITY: Self = Self::new(KindTag::SketchyEquality);
}

impl Kind<is_as_always::T, Migrated> {
    pub const IS_AS_ALWAYS: Self = Self::new(KindTag::IsAsAlways);
}

impl Kind<non_disjoint_check::T, Migrated> {
    pub const NON_DISJOINT_CHECK: Self = Self::new(KindTag::NonDisjointCheck);
}

impl Kind<cast_non_primitive::T, Migrated> {
    pub const CAST_NON_PRIMITIVE: Self = Self::new(KindTag::CastNonPrimitive);
}

impl Kind<truthiness_test::T, Migrated> {
    pub const TRUTHINESS_TEST: Self = Self::new(KindTag::TruthinessTest);
}

impl Kind<equality_check::T, Migrated> {
    pub const EQUALITY_CHECK: Self = Self::new(KindTag::EqualityCheck);
}

impl Kind<duplicate_properties::T, Migrated> {
    pub const DUPLICATE_PROPERTIES: Self = Self::new(KindTag::DuplicateProperties);
}

impl Kind<class_pointer_to_string::T, Warn> {
    pub const CLASS_POINTER_TO_STRING: Self = Self::new(KindTag::ClassPointerToString);
}

impl<'a> Kind<no_disjoint_union_check::T<'a>, Warn> {
    pub const NO_DISJOINT_UNION_CHECK: Self = Self::new(KindTag::NoDisjointUnionCheck);
}

impl<'a> Kind<switch_redundancy::T<'a>, Warn> {
    pub const SWITCH_REDUNDANCY: Self = Self::new(KindTag::SwitchRedundancy);
}

impl Kind<static_call_on_trait::T, Warn> {
    pub const STATIC_CALL_ON_TRAIT: Self = Self::new(KindTag::StaticCallOnTrait);
}

impl Kind<static_property_override::T, Warn> {
    pub const STATIC_PROPERTY_OVERRIDE: Self = Self::new(KindTag::StaticPropertyOverride);
}

impl Kind<readonly_property_override::T, Warn> {
    pub const READONLY_PROPERTY_OVERRIDE: Self = Self::new(KindTag::ReadonlyPropertyOverride);
}

impl Kind<string_to_class_pointer::T, Warn> {
    pub const STRING_TO_CLASS_POINTER: Self = Self::new(KindTag::StringToClassPointer);
}

impl Kind<null_coalesce_always::T, Warn> {
    pub const NULL_COALESCE_ALWAYS: Self = Self::new(KindTag::NullCoalesceAlways);
}

impl Kind<call_needs_concrete::T, Warn> {
    pub const CALL_NEEDS_CONCRETE: Self = Self::new(KindTag::CallNeedsConcrete);
}

impl Kind<expect_bool_for_condition::T, Warn> {
    pub const EXPECT_BOOL_FOR_CONDITION: Self = Self::new(KindTag::ExpectBoolForCondition);
}

impl Kind<redundant_nullsafe_operation::T, Warn> {
    pub const REDUNDANT_NULLSAFE_OPERATION: Self =
        Self::new(KindTag::RedundantNullsafeOperation);
}

impl Kind<unbound_name_warning::T, Warn> {
    pub const UNBOUND_NAME_WARNING: Self = Self::new(KindTag::UnboundNameWarning);
}

impl Kind<set_or_keyset_array_get::T, Warn> {
    pub const SET_OR_KEYSET_ARRAY_GET: Self = Self::new(KindTag::SetOrKeysetArrayGet);
}

impl Kind<sealed_not_subtype::T, Warn> {
    pub const SEALED_NOT_SUBTYPE: Self = Self::new(KindTag::SealedNotSubtype);
}

impl Kind<tany_found::T, Warn> {
    pub const TANY_FOUND: Self = Self::new(KindTag::TanyFound);
}

impl Kind<consistent_construct_abstract_final::T, Warn> {
    pub const CONSISTENT_CONSTRUCT_ABSTRACT_FINAL: Self =
        Self::new(KindTag::ConsistentConstructAbstractFinal);
}

impl Kind<dynamic_call::T, Warn> {
    pub const DYNAMIC_CALL: Self = Self::new(KindTag::DynamicCall);
}

impl Kind<dynamic_return::T, Warn> {
    pub const DYNAMIC_RETURN: Self = Self::new(KindTag::DynamicReturn);
}

impl Kind<sealed_not_override::T, Warn> {
    pub const SEALED_NOT_OVERRIDE: Self = Self::new(KindTag::SealedNotOverride);
}

impl Kind<redundant_require_this_as::T, Warn> {
    pub const REDUNDANT_REQUIRE_THIS_AS: Self = Self::new(KindTag::RedundantRequireThisAs);
}

impl Kind<redundant_concurrent::T, Warn> {
    pub const REDUNDANT_CONCURRENT: Self = Self::new(KindTag::RedundantConcurrent);
}

/// `type ('x, 'a) t = Pos.t * ('x, 'a) kind * 'x`
pub type T<X, A> = (Pos, Kind<X, A>, X);
