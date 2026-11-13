// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_warning_utils.ml`. See `hh/PORTING.md`.
//!
//! In OCaml each kind of warning has a module (`Sketchy_equality`,
//! `Is_as_always`, ...) of signature `Warning` or `Lint`, and `module_of`
//! picks the module of a `Typing_warning.kind`. Here the two signatures are
//! the traits [`Warning`] and [`Lint`], implemented by the data of each kind
//! (`typing_warning::sketchy_equality::T`, ...): the kind of a warning
//! determines the type of its data, which is what `module_of` and
//! `module_of_migrated` compute.

use bstr::BString;
use naming_special_names_rust as sn;
use oxidized::error_codes::Warning as Codes;
use oxidized::explanation::Explanation;
use oxidized::global_options::GlobalOptions;
use oxidized::global_options::NoneOrAllExcept;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Edits;
use oxidized::quickfix::Quickfix;
use oxidized::typechecker_options::TypecheckerOptions;
use oxidized::user_diagnostic::Severity;
use oxidized::user_diagnostic::UserDiagnostic;

use crate::typing_env_types::Env;
// `Markdown_lite.md_codify`
use crate::typing_reason::md_codify;
use crate::typing_warning;
use crate::typing_warning::KindTag;
use crate::typing_warning::Lazy;

/// `Utils.strip_ns`
fn utils_strip_ns(s: &str) -> &str {
    crate::typing_reason::utils_strip_ns(s)
}

/// `Render.strip_ns`
fn render_strip_ns(s: &str) -> &str {
    crate::typing_reason::strip_ns(s)
}

fn message(pos: PosOrDecl, msg: impl Into<BString>) -> Message<PosOrDecl> {
    Message(pos, msg.into())
}

/// `module type Warning`
pub trait Warning {
    fn claim(&self) -> String;

    fn code(&self) -> Codes;

    fn codes() -> Vec<Codes>;

    fn reasons(&self) -> Vec<Message<PosOrDecl>>;

    fn quickfixes(&self) -> Vec<Quickfix<Pos>>;
}

/// `module type Lint`
pub trait Lint: Warning {
    fn lint_code(&self) -> isize;

    fn lint_severity(&self) -> crate::lints_core::Severity;

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix>;
}

// module Sketchy_equality
impl Warning for typing_warning::sketchy_equality::T<'_> {
    fn code(&self) -> Codes {
        Codes::SketchyEquality
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::SketchyEquality]
    }

    fn claim(&self) -> String {
        let b = md_codify(if self.result { "true" } else { "false" });
        format!("This expression is likely always {}", b)
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        let left = Lazy::force(&self.left);
        let right = Lazy::force(&self.right);
        let typedef_trail_entry =
            |pos: &PosOrDecl| message(pos.clone(), "Typedef definition comes from here");
        let left_trail = self.left_trail.iter().map(typedef_trail_entry);
        let right_trail = self.right_trail.iter().map(typedef_trail_entry);
        let mut reasons = left.clone();
        reasons.extend(left_trail);
        reasons.extend(right.iter().cloned());
        reasons.extend(right_trail);
        reasons
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Is_as_always
impl Warning for typing_warning::is_as_always::T {
    fn code(&self) -> Codes {
        use typing_warning::is_as_always::Kind;
        match &self.kind {
            Kind::Is_is_always_true => Codes::IsIsAlwaysTrue,
            Kind::Is_is_always_false => Codes::IsIsAlwaysFalse,
            Kind::As_always_succeeds(_) => Codes::AsAlwaysSucceeds,
            Kind::As_always_fails { .. } => Codes::AsAlwaysFails,
        }
    }

    fn codes() -> Vec<Codes> {
        vec![
            Codes::IsIsAlwaysTrue,
            Codes::IsIsAlwaysFalse,
            Codes::AsAlwaysSucceeds,
            Codes::AsAlwaysFails,
        ]
    }

    fn claim(&self) -> String {
        use typing_warning::is_as_always::Kind;
        let lhs_ty = md_codify(&self.lhs_ty);
        let rhs_ty = md_codify(&self.rhs_ty);
        match &self.kind {
            Kind::Is_is_always_true => format!(
                "This `is` check is always `true`. The expression on the left has type {} which is a subtype of {}.",
                lhs_ty, rhs_ty
            ),
            Kind::Is_is_always_false => format!(
                "This `is` check is always `false`. The expression on the left has type {} which shares no values with {}.",
                lhs_ty, rhs_ty
            ),
            Kind::As_always_succeeds(_) => format!(
                "This `as` assertion will always succeed and hence is redundant. The expression on the left has a type {} which is a subtype of {}.",
                lhs_ty, rhs_ty
            ),
            Kind::As_always_fails { is_nullable } => {
                let consequence = if *is_nullable {
                    "a `null` value"
                } else {
                    "an exception at runtime"
                };
                format!(
                    "This `as` assertion will always fail and lead to {}. The expression on the left has type {} which shares no values with {}.",
                    consequence, lhs_ty, rhs_ty
                )
            }
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::is_as_always::T {
    fn lint_severity(&self) -> crate::lints_core::Severity {
        crate::lints_core::Severity::Lint_warning
    }

    fn lint_code(&self) -> isize {
        use typing_warning::is_as_always::Kind;
        match &self.kind {
            Kind::Is_is_always_true => crate::lints_codes::codes::is_always_true,
            Kind::Is_is_always_false => crate::lints_codes::codes::is_always_false,
            Kind::As_always_succeeds(_) => crate::lints_codes::codes::as_always_succeeds,
            Kind::As_always_fails { .. } => crate::lints_codes::codes::as_always_fails,
        }
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        use typing_warning::is_as_always::Kind;
        match &self.kind {
            Kind::Is_is_always_true | Kind::Is_is_always_false | Kind::As_always_fails { .. } => {
                None
            }
            Kind::As_always_succeeds(quickfix) => Some(quickfix.clone()),
        }
    }
}

// module Null_coalesce_always
impl Warning for typing_warning::null_coalesce_always::T {
    fn code(&self) -> Codes {
        Codes::NullCoalesceAlways
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::NullCoalesceAlways]
    }

    fn claim(&self) -> String {
        use typing_warning::null_coalesce_always::Kind;
        let side = match &self.kind {
            Kind::Null_coalesce_always_null => "right",
            Kind::Null_coalesce_never_null => "left",
        };
        format!(
            "This null coalesce will always evaluate to its {}-hand side.",
            side
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        use typing_warning::null_coalesce_always::Kind;
        let sub = match &self.kind {
            Kind::Null_coalesce_always_null => "is always",
            Kind::Null_coalesce_never_null => "can never be",
        };
        vec![message(
            self.lhs_pos.clone(),
            format!(
                "The expression on the left has type {} which {} `null`.",
                md_codify(&self.lhs_ty),
                sub
            ),
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Non_disjoint_check
impl Warning for typing_warning::non_disjoint_check::T {
    fn code(&self) -> Codes {
        Codes::NonDisjointCheck
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::NonDisjointCheck]
    }

    fn claim(&self) -> String {
        format!(
            "{} to '{}' will always return the same value, because type {} is disjoint from type {}.",
            if self.dynamic {
                "Non-dynamic calls"
            } else {
                "This call"
            },
            self.name,
            self.ty1,
            self.ty2
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::non_disjoint_check::T {
    fn lint_code(&self) -> isize {
        crate::lints_codes::codes::invalid_disjointness_check
    }

    fn lint_severity(&self) -> crate::lints_core::Severity {
        crate::lints_core::Severity::Lint_warning
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        None
    }
}

// module Cast_non_primitive
impl Warning for typing_warning::cast_non_primitive::T {
    fn code(&self) -> Codes {
        Codes::CastNonPrimitive
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::CastNonPrimitive]
    }

    fn claim(&self) -> String {
        format!(
            "Casting {} to {}: casting a non-primitive type to a primitive rarely yields a useful value. Did you mean to extract a value from this object before casting it, or to do a null-check?",
            self.ty, self.cast_hint
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::cast_non_primitive::T {
    fn lint_code(&self) -> isize {
        crate::lints_codes::codes::cast_non_primitive
    }

    fn lint_severity(&self) -> crate::lints_core::Severity {
        crate::lints_core::Severity::Lint_error
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        None
    }
}

// module Truthiness_test
impl Warning for typing_warning::truthiness_test::T {
    fn code(&self) -> Codes {
        Codes::TruthinessTest
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::TruthinessTest]
    }

    fn claim(&self) -> String {
        use typing_warning::truthiness_test::Kind;
        use typing_warning::truthiness_test::SketchyKind;
        let not = self.not;
        match &self.kind {
            Kind::Invalid { truthy } => format!(
                "Invalid condition: a value of type {} will always be {}",
                md_codify(&self.ty),
                if *truthy { "truthy" } else { "falsy" }
            ),
            Kind::Sketchy(sketchy) => format!(
                "{}ketchy condition: testing the {} of {} may not behave as expected.\n{}",
                match &self.expr {
                    None => "S".to_string(),
                    Some(e) => format!("`{}{}` is a s", if not { "!" } else { "" }, e),
                },
                if not { "falsiness" } else { "truthiness" },
                self.ty,
                match sketchy {
                    SketchyKind::String => format!(
                        "The values `\"\"` and `\"0\"` are both considered falsy. To check for {}emptiness, use `{}Str\\is_empty{}`.",
                        if not { "" } else { "non-" },
                        if not { "" } else { "!" },
                        match &self.expr {
                            None => "".to_string(),
                            Some(e) => format!("({})", e),
                        }
                    ),
                    SketchyKind::Arraykey => {
                        "The values `0`, `\"\"`, and `\"0\"` are all considered falsy. Test for them explicitly.".to_string()
                    }
                    SketchyKind::Stringish => concat!(
                        "The values `\"\"` and `\"0\"` are both considered falsy, but objects will be truthy even if their `__toString` returns `\"\"` or `\"0\"`.\n",
                        "To check for emptiness, convert to a string and use `Str\\is_empty`."
                    )
                    .to_string(),
                    SketchyKind::Xhp_child => {
                        "The values `\"\"` and `\"0\"` are both considered falsy, but objects (including XHP elements) will be truthy even if their `__toString` returns `\"\"` or `\"0\"`.".to_string()
                    }
                    SketchyKind::Traversable => concat!(
                        "A value of this type may be truthy even when empty.\n",
                        "Hack collections and arrays are falsy when empty, but user-defined Traversables will always be truthy, even when empty.\n",
                        "If you would like to only allow containers which are falsy when empty, use the `Container` or `KeyedContainer` interfaces."
                    )
                    .to_string(),
                }
            ),
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::truthiness_test::T {
    fn lint_code(&self) -> isize {
        use typing_warning::truthiness_test::Kind;
        match &self.kind {
            Kind::Invalid { .. } => crate::lints_codes::codes::invalid_truthiness_test,
            Kind::Sketchy(_) => crate::lints_codes::codes::sketchy_truthiness_test,
        }
    }

    fn lint_severity(&self) -> crate::lints_core::Severity {
        crate::lints_core::Severity::Lint_warning
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        None
    }
}

// module Equality_check
impl Warning for typing_warning::equality_check::T {
    fn code(&self) -> Codes {
        Codes::EqualityCheck
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::EqualityCheck]
    }

    fn claim(&self) -> String {
        use typing_warning::equality_check::Kind;
        match &self.kind {
            Kind::Equality(b) => format!(
                "Invalid comparison: This expression will always return {}.\nA value of type {} can never be equal to a value of type {}",
                md_codify(if *b { "true" } else { "false" }),
                md_codify(&self.ty1),
                md_codify(&self.ty2)
            ),
            Kind::Switch => format!(
                "Invalid case: This case will never match.\nA value of type {} can never be equal to a value of type {}",
                md_codify(&self.ty1),
                md_codify(&self.ty2)
            ),
            Kind::Contains => format!(
                "Invalid `C\\contains` check: This call will always return `false`.\nA `Traversable<{}>` cannot contain a value of type {}",
                self.ty1,
                md_codify(&self.ty2)
            ),
            Kind::Contains_key => format!(
                "Invalid `C\\contains_key` check: This call will always return `false`.\nA `KeyedTraversable<{}, ...>` cannot contain a key of type {}",
                self.ty1,
                md_codify(&self.ty2)
            ),
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::equality_check::T {
    fn lint_code(&self) -> isize {
        use typing_warning::equality_check::Kind;
        match &self.kind {
            Kind::Equality(_) | Kind::Switch => crate::lints_codes::codes::non_equatable_comparison,
            Kind::Contains | Kind::Contains_key => {
                crate::lints_codes::codes::invalid_contains_check
            }
        }
    }

    fn lint_severity(&self) -> crate::lints_core::Severity {
        crate::lints_core::Severity::Lint_warning
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        None
    }
}

// module Duplicated_properties

/// `Duplicated_properties.prettify_class_list`
fn prettify_class_list(names: &[String]) -> String {
    match names {
        [] => "".to_string(),
        [c] => c.clone(),
        [c1, c2] => format!("{} and {}", c1, c2),
        [h, t @ ..] => format!("{}, {}", h, prettify_class_list(t)),
    }
}

impl Warning for typing_warning::duplicate_properties::T {
    fn code(&self) -> Codes {
        Codes::DuplicateProperties
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::DuplicateProperties]
    }

    fn claim(&self) -> String {
        if self.initialized_with_constant {
            let class_names: Vec<String> = self
                .class_names
                .iter()
                .map(|n| utils_strip_ns(n).to_string())
                .collect();
            format!(
                "Property {}, defined in {}, is inherited multiple times by class {} and one of its instances is initialised with a class or enum constant",
                md_codify(utils_strip_ns(&self.prop_name)),
                prettify_class_list(&class_names),
                md_codify(utils_strip_ns(&self.class_name))
            )
        } else {
            let class_names: Vec<String> = self
                .class_names
                .iter()
                .map(|n| md_codify(utils_strip_ns(n)))
                .collect();
            format!(
                "Duplicated property {} in {} (defined in {}): all instances will be aliased at runtime",
                md_codify(utils_strip_ns(&self.prop_name)),
                md_codify(utils_strip_ns(&self.class_name)),
                prettify_class_list(&class_names)
            )
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

impl Lint for typing_warning::duplicate_properties::T {
    fn lint_code(&self) -> isize {
        if self.initialized_with_constant {
            crate::lints_codes::codes::duplicate_property_enum_init
        } else {
            crate::lints_codes::codes::duplicate_property
        }
    }

    fn lint_severity(&self) -> crate::lints_core::Severity {
        if self.initialized_with_constant {
            crate::lints_core::Severity::Lint_error
        } else {
            crate::lints_core::Severity::Lint_warning
        }
    }

    fn lint_quickfix(&self) -> Option<typing_warning::Quickfix> {
        None
    }
}

// module Class_pointer_to_string
impl Warning for typing_warning::class_pointer_to_string::T {
    fn code(&self) -> Codes {
        Codes::ClassPointerToString
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::ClassPointerToString]
    }

    fn claim(&self) -> String {
        format!(
            "Using {} in this position will trigger an implicit runtime conversion to string. You may use {} to get the class name as a string.",
            self.ty,
            md_codify("HH\\class_to_classname")
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module No_disjoint_union_check
impl Warning for typing_warning::no_disjoint_union_check::T<'_> {
    fn code(&self) -> Codes {
        Codes::NoDisjointUnion
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::NoDisjointUnion]
    }

    fn claim(&self) -> String {
        "Invalid type argument due to disjoint types in a union".to_string()
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        let disjuncts = Lazy::force(&self.disjuncts);
        let mut reasons: Vec<Message<PosOrDecl>> = disjuncts
            .iter()
            .map(|(pos, ty)| {
                message(
                    pos.clone(),
                    format!("{} is one of the disjoint types", md_codify(ty)),
                )
            })
            .collect();
        reasons.push(message(
            self.tparam_pos.clone(),
            format!(
                "This type parameter is marked with {} to indicate that disjoint unions are errors",
                md_codify(sn::user_attributes::NO_DISJOINT_UNION)
            ),
        ));
        reasons
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Switch_redundancy
impl Warning for typing_warning::switch_redundancy::T<'_> {
    fn code(&self) -> Codes {
        Codes::SwitchRedundancy
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::SwitchRedundancy]
    }

    fn claim(&self) -> String {
        use typing_warning::switch_redundancy::T;
        match self {
            T::SwitchHasRedundancy {
                redundancy_size, ..
            } => format!(
                "This switch statement contains redundant cases. There are {} redundant cases.",
                redundancy_size
            ),
            T::DuplicatedCase { case, .. } => format!(
                "This switch case, {}, occurred before. It will never be matched.",
                md_codify(Lazy::force(case).as_str())
            ),
            T::RedundantDefault => {
                "All cases are already covered. Redundant `default` cases prevent detection of future errors.".to_string()
            }
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        use typing_warning::switch_redundancy::T;
        match self {
            T::SwitchHasRedundancy { positions, .. } => Lazy::force(positions)
                .iter()
                .map(|p| message(p.clone(), "The case is redundant."))
                .collect(),
            T::DuplicatedCase {
                first_occurrence, ..
            } => vec![message(
                first_occurrence.clone(),
                "This is the original occurrence of the case.",
            )],
            T::RedundantDefault => vec![],
        }
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Static_call_on_trait
impl Warning for typing_warning::static_call_on_trait::T {
    fn code(&self) -> Codes {
        Codes::StaticCallOnTrait
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::StaticCallOnTrait]
    }

    fn claim(&self) -> String {
        let trait_call = md_codify(&format!(
            "{}::{}",
            utils_strip_ns(&self.trait_name),
            self.meth_name
        ));
        format!("Static method call on a trait: {}", trait_call)
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        let trait_name = utils_strip_ns(&self.trait_name);
        vec![message(
            self.trait_pos.clone(),
            format!("{} is defined here", md_codify(trait_name)),
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Static_property_override
impl Warning for typing_warning::static_property_override::T {
    fn code(&self) -> Codes {
        Codes::StaticPropertyOverride
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::StaticPropertyOverride]
    }

    fn claim(&self) -> String {
        format!(
            "Static property is overridden: {}",
            md_codify(&self.prop_name)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(
            self.child_prop_pos.clone(),
            "Overriding static property is here",
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Readonly_property_override
impl Warning for typing_warning::readonly_property_override::T {
    fn code(&self) -> Codes {
        Codes::ReadonlyPropertyOverride
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::ReadonlyPropertyOverride]
    }

    fn claim(&self) -> String {
        format!(
            "The readonly-ness of property {} is changed by this override",
            md_codify(&self.prop_name)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(
            self.child_prop_pos.clone(),
            "Overriding property is here",
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module String_to_class_pointer
impl Warning for typing_warning::string_to_class_pointer::T {
    fn code(&self) -> Codes {
        Codes::StringToClassPointer
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::StringToClassPointer]
    }

    fn claim(&self) -> String {
        let name = utils_strip_ns(&self.cls_name);
        format!(
            "It is no longer allowed to use a `classname<{}>` in this position. Please use a `class<{}>` instead.",
            name, name
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(self.ty_pos.clone(), "Definition is here")]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Call_needs_concrete
impl Warning for typing_warning::call_needs_concrete::T {
    fn code(&self) -> Codes {
        Codes::CallNeedsConcrete
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::CallNeedsConcrete]
    }

    fn claim(&self) -> String {
        use typing_warning::call_needs_concrete::Via;
        let strip_ns_class_name = utils_strip_ns(&self.class_name);
        let member = md_codify(&format!("{}::{}", strip_ns_class_name, self.meth_name));
        match self.via {
            Via::Id => format!(
                "Dangerous call to {} (a `<<__NeedsConcrete>>` method). It is expecting a concrete receiver but {} is not concrete.",
                member,
                md_codify(strip_ns_class_name)
            ),
            Via::Static => format!(
                "Dangerous call to {} (a `<<__NeedsConcrete>>` method) via `static`. It requires `static` to refer to a concrete class but `static` may not be concrete.",
                member
            ),
            Via::Self_ | Via::Parent => {
                let via_str = match self.via {
                    Via::Self_ => "`self`",
                    _ => "`parent`",
                };
                format!(
                    "Dangerous call to {} (a `<<__NeedsConcrete>>` method) via {}. It requires `static` to refer to a concrete class, but {} sets `static` to a class that may not be concrete.",
                    member, via_str, via_str
                )
            }
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(self.decl_pos.clone(), "Declaration is here")]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Expect_bool_for_condition
impl Warning for typing_warning::expect_bool_for_condition::T {
    fn code(&self) -> Codes {
        Codes::ExpectBoolForCondition
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::ExpectBoolForCondition]
    }

    fn claim(&self) -> String {
        format!(
            "Only bool values can be used as a condition. Use a type-specific test instead. This is {}",
            self.ty
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Redundant_nullsafe_operation
impl Warning for typing_warning::redundant_nullsafe_operation::T {
    fn code(&self) -> Codes {
        use typing_warning::redundant_nullsafe_operation::Kind;
        match &self.kind {
            Kind::Redundant_nullsafe_member_select => Codes::RedundantNullsafeMemberSelect,
            Kind::Nullsafe_member_select_on_null => Codes::NullsafeMemberSelectOnNull,
            Kind::Redundant_nullsafe_pipe => Codes::RedundantNullsafePipe,
            Kind::Nullsafe_pipe_on_null => Codes::NullsafePipeOnNull,
        }
    }

    fn codes() -> Vec<Codes> {
        vec![
            Codes::RedundantNullsafeMemberSelect,
            Codes::NullsafeMemberSelectOnNull,
            Codes::RedundantNullsafePipe,
            Codes::NullsafePipeOnNull,
        ]
    }

    fn claim(&self) -> String {
        use typing_warning::redundant_nullsafe_operation::Kind;
        match &self.kind {
            Kind::Redundant_nullsafe_member_select => format!(
                "You are using the {} operator but this object is of type {} which cannot be null. You can use the {} operator instead.",
                md_codify("?->"),
                self.ty,
                md_codify("->")
            ),
            Kind::Nullsafe_member_select_on_null => format!(
                "You are using the {} operator but this value is always null. It's likely you did not intend this value to be always null.",
                md_codify("?->")
            ),
            Kind::Redundant_nullsafe_pipe => format!(
                "You are using the {} operator but this expression is of type {} which cannot be null. You can use the {} operator instead.",
                md_codify("|?>"),
                self.ty,
                md_codify("|>")
            ),
            Kind::Nullsafe_pipe_on_null => format!(
                "You are using the {} operator but this expression is always null. It's likely you did not intend this value to be always null.",
                md_codify("|?>")
            ),
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Unbound_name_warning
impl Warning for typing_warning::unbound_name_warning::T {
    fn code(&self) -> Codes {
        Codes::UnboundNameWarning
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::UnboundNameWarning]
    }

    fn claim(&self) -> String {
        format!(
            "Unbound name: {}{}",
            md_codify(render_strip_ns(&self.name)),
            self.kind_str
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Set_or_keyset_array_get
impl Warning for typing_warning::set_or_keyset_array_get::T {
    fn code(&self) -> Codes {
        Codes::SetOrKeysetArrayGet
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::SetOrKeysetArrayGet]
    }

    fn claim(&self) -> String {
        use typing_warning::set_or_keyset_array_get::Kind;
        let suggestion = match &self.kind {
            Kind::Keyset => "`C\\contains_key`",
            Kind::ConstSet => "the `contains` method",
        };
        format!(
            "Array access on type {} returns the key (if present) or throws an exception. Consider using {} to check for membership instead.",
            md_codify(&self.ty),
            suggestion
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        use typing_warning::set_or_keyset_array_get::Kind;
        match &self.replacement_text {
            None => vec![],
            Some(new_text) => {
                let title = match &self.kind {
                    Kind::Keyset => "Replace with `C\\contains_key`",
                    Kind::ConstSet => "Replace with `->contains`",
                };
                // `Quickfix.make_eager_default_hint_style`
                vec![Quickfix {
                    title: title.to_string(),
                    edits: Edits::Eager(vec![(new_text.clone(), self.full_expr_pos.clone())]),
                    hint_styles: vec![],
                }]
            }
        }
    }
}

// module Sealed_not_subtype
impl Warning for typing_warning::sealed_not_subtype::T {
    fn code(&self) -> Codes {
        Codes::SealedNotSubtype
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::SealedNotSubtype]
    }

    fn claim(&self) -> String {
        let parent_name = utils_strip_ns(&self.parent_name);
        let child_name = utils_strip_ns(&self.child_name);
        format!(
            "{} {} in sealed allowlist for {}{}, but does not {} {}",
            self.child_kind,
            md_codify(child_name),
            match &self.parent_method_name {
                Some(method_name) => format!("method {} in ", md_codify(method_name)),
                None => "".to_string(),
            },
            md_codify(parent_name),
            self.verb,
            md_codify(parent_name)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Tany_found
impl Warning for typing_warning::tany_found::T {
    fn code(&self) -> Codes {
        Codes::TanyFound
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::TanyFound]
    }

    fn claim(&self) -> String {
        "This expression has an unresolved type due to a limitation of the typechecker. It is silently compatible with every type, so it can be passed to or returned from any function without triggering a type error, potentially hiding bugs. Please post in the support group for further guidance.".to_string()
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Dynamic_call_warning
impl Warning for typing_warning::dynamic_call::T {
    fn codes() -> Vec<Codes> {
        vec![
            Codes::DynamicMethodCall,
            Codes::DynamicFunctionCall,
            Codes::DynamicArrayAccess,
            Codes::DynamicPropertyAccess,
        ]
    }

    fn code(&self) -> Codes {
        use typing_warning::dynamic_call::Kind;
        match &self.kind {
            Kind::Method_invocation => Codes::DynamicMethodCall,
            Kind::Function_call => Codes::DynamicFunctionCall,
            Kind::Array_index => Codes::DynamicArrayAccess,
            Kind::Array_append => Codes::DynamicArrayAccess,
            Kind::Property_access => Codes::DynamicPropertyAccess,
        }
    }

    fn claim(&self) -> String {
        use typing_warning::dynamic_call::Kind;
        let ty_str = md_codify(&self.actual_type);
        match &self.kind {
            Kind::Method_invocation => format!("Method invoked on a value of type {}", ty_str),
            Kind::Function_call => format!("Value of type {} called as a function", ty_str),
            Kind::Array_index => format!("Indexing into a value of type {}", ty_str),
            Kind::Array_append => format!("Appending to a value of type {}", ty_str),
            Kind::Property_access => format!("Property accessed on a value of type {}", ty_str),
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(
            self.dynamic_reason_pos.clone(),
            self.dynamic_reason_msg.as_str(),
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Dynamic_return
impl Warning for typing_warning::dynamic_return::T {
    fn code(&self) -> Codes {
        Codes::DynamicReturn
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::DynamicReturn]
    }

    fn claim(&self) -> String {
        format!(
            "Returning a value of type `dynamic` through a non-fully-enforced return type {}",
            md_codify(&self.return_type)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![message(
            self.return_type_pos.clone(),
            "This return type is not fully enforced at runtime",
        )]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Consistent_construct_abstract_final
impl Warning for typing_warning::consistent_construct_abstract_final::T {
    fn code(&self) -> Codes {
        Codes::ConsistentConstructAbstractFinal
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::ConsistentConstructAbstractFinal]
    }

    fn claim(&self) -> String {
        let name = render_strip_ns(&self.name);
        match &self.inherited_from {
            Some(ancestor) => format!(
                "An `abstract final` class cannot be `__ConsistentConstruct`. Class {} inherits `__ConsistentConstruct` from {}.",
                md_codify(name),
                md_codify(render_strip_ns(ancestor))
            ),
            None => format!(
                "An `abstract final` class cannot be `__ConsistentConstruct`. {} is `__ConsistentConstruct`.",
                md_codify(name)
            ),
        }
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Sealed_not_override
impl Warning for typing_warning::sealed_not_override::T {
    fn code(&self) -> Codes {
        Codes::SealedNotOverride
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::SealedNotOverride]
    }

    fn claim(&self) -> String {
        let method_name = utils_strip_ns(&self.method_name);
        let method_def = utils_strip_ns(&self.method_def);
        let allowlist_class_name = utils_strip_ns(&self.allowlist_class_name);
        format!(
            "{} {} in sealed allowlist for method {} in {}, but does not override method {}",
            self.allowlist_class_kind,
            md_codify(allowlist_class_name),
            md_codify(method_name),
            md_codify(method_def),
            md_codify(method_name)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Redundant_require_this_as
impl Warning for typing_warning::redundant_require_this_as::T {
    fn code(&self) -> Codes {
        Codes::RedundantRequireThisAs
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::RedundantRequireThisAs]
    }

    fn claim(&self) -> String {
        let trait_name = utils_strip_ns(&self.trait_name);
        let class_name = utils_strip_ns(&self.class_name);
        format!(
            "Trait {} has `require this as {}` constraint but class {} does not use this trait. Replace `require this as` with `require extends`",
            md_codify(trait_name),
            md_codify(class_name),
            md_codify(class_name)
        )
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

// module Redundant_concurrent
impl Warning for typing_warning::redundant_concurrent::T {
    fn code(&self) -> Codes {
        Codes::RedundantConcurrent
    }

    fn codes() -> Vec<Codes> {
        vec![Codes::RedundantConcurrent]
    }

    fn claim(&self) -> String {
        "A `concurrent` block containing a single statement is redundant. Concurrency within a statement is already implied by `await`.".to_string()
    }

    fn reasons(&self) -> Vec<Message<PosOrDecl>> {
        vec![]
    }

    fn quickfixes(&self) -> Vec<Quickfix<Pos>> {
        vec![]
    }
}

/// A type-dependent warning is one that does depends on type precision and
/// therefore can be invalidated by dynamic. Warnings which do not depend on
/// type can always trusted.
fn is_type_dependent<X, A>(kind: &typing_warning::Kind<X, A>) -> bool {
    match kind.tag() {
        // Structural: don't depend on type information that could be
        // invalidated by dynamic
        KindTag::Static_call_on_trait => false,
        KindTag::Static_property_override => false,
        KindTag::Readonly_property_override => false,
        KindTag::Duplicate_properties => false,
        KindTag::Class_pointer_to_string => false,
        KindTag::String_to_class_pointer => false,
        KindTag::Call_needs_concrete => false,
        KindTag::Unbound_name_warning => false,
        KindTag::Sealed_not_subtype => false,
        KindTag::Sealed_not_override => false,
        KindTag::Consistent_construct_abstract_final => false,
        KindTag::Redundant_require_this_as => false,
        KindTag::Redundant_concurrent => false,
        // Type-dependent: rely on type precision that could differ under
        // dynamic
        KindTag::Is_as_always => true,
        KindTag::Non_disjoint_check => true,
        KindTag::Cast_non_primitive => true,
        KindTag::Truthiness_test => true,
        KindTag::Equality_check => true,
        KindTag::Sketchy_equality => true,
        KindTag::Null_coalesce_always => true,
        KindTag::Switch_redundancy => true,
        KindTag::No_disjoint_union_check => true,
        KindTag::Expect_bool_for_condition => true,
        KindTag::Redundant_nullsafe_operation => true,
        KindTag::Set_or_keyset_array_get => true,
        KindTag::Dynamic_call => true,
        KindTag::Dynamic_return => true,
        KindTag::Tany_found => true,
    }
}

pub fn code_is_enabled(tcopt: &GlobalOptions, code: Codes) -> bool {
    // `Typechecker_options.hack_warnings tcopt`
    match &tcopt.hack_warnings {
        NoneOrAllExcept::NNone => false,
        NoneOrAllExcept::AllExcept(disabled_codes) => !disabled_codes.contains(&(code as isize)),
    }
}

pub fn add_<X: Warning, A>(
    tcopt: &TypecheckerOptions,
    (pos, kind, warning): typing_warning::T<X, A>,
) {
    if code_is_enabled(tcopt, warning.code()) {
        let severity = Severity::Warning {
            is_trusted: !is_type_dependent(&kind),
        };
        crate::diagnostics_state::add_diagnostic(UserDiagnostic {
            severity,
            code: warning.code() as isize,
            claim: Message(pos, BString::from(warning.claim())),
            reasons: warning.reasons(),
            explanation: Explanation::Empty,
            quickfixes: warning.quickfixes(),
            custom_msgs: vec![],
            is_fixmed: false,
            function_pos: None,
        })
    }
}

pub fn add_for_migration<X: Lint>(
    tcopt: &GlobalOptions,
    as_lint: Option<Option<crate::tast::CheckStatus>>,
    warning: typing_warning::T<X, typing_warning::Migrated>,
) {
    match as_lint {
        None => add_(tcopt, warning),
        Some(check_status) => {
            let (pos, _kind, warning) = warning;
            crate::lints_core::add(
                Some(check_status),
                None,
                Some(
                    warning
                        .lint_quickfix()
                        .map(|quickfix| crate::lints_diagnostics::quickfix(&quickfix)),
                ),
                warning.lint_code(),
                warning.lint_severity(),
                pos,
                warning.claim(),
            )
        }
    }
}

pub fn add<X: Warning, A>(env: &Env, warning: typing_warning::T<X, A>) {
    add_(&crate::typing_env::get_tcopt(env), warning)
}

pub fn codes<X: Warning, A>(_kind: &typing_warning::Kind<X, A>) -> Vec<Codes> {
    X::codes()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::diagnostics_state;
    use crate::diagnostics_state::Diagnostic;
    use crate::typing_warning::Kind;

    fn pos(line: usize, cols: std::ops::Range<usize>) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        let bol = line * 100;
        Pos::from_lnum_bol_offset(
            file,
            (line, bol, bol + cols.start),
            (line, bol, bol + cols.end),
        )
    }

    fn tcopt(hack_warnings: NoneOrAllExcept<isize>) -> TypecheckerOptions {
        TypecheckerOptions {
            hack_warnings,
            ..Default::default()
        }
    }

    fn all_warnings() -> TypecheckerOptions {
        tcopt(NoneOrAllExcept::AllExcept(vec![]))
    }

    /// The diagnostics that `f` adds.
    fn added(f: impl FnOnce()) -> Vec<Diagnostic> {
        let (errors, ()) = diagnostics_state::do_(Some(false), f);
        diagnostics_state::get_diagnostic_list(Some(false), errors)
    }

    fn static_call_on_trait() -> typing_warning::static_call_on_trait::T {
        typing_warning::static_call_on_trait::T {
            meth_name: "f".to_string(),
            trait_name: "\\NS\\Tr".to_string(),
            trait_pos: pos(1, 6..8),
        }
    }

    #[test]
    fn a_warning_that_does_not_depend_on_types_is_trusted() {
        let tcopt = all_warnings();
        let diags = added(|| {
            add_(
                &tcopt,
                (
                    pos(5, 2..9),
                    Kind::Static_call_on_trait,
                    static_call_on_trait(),
                ),
            )
        });
        assert_eq!(diags.len(), 1);
        let d = &diags[0];
        assert_eq!(d.severity, Severity::Warning { is_trusted: true });
        assert_eq!(d.code, 12020);
        assert_eq!(
            d.claim,
            Message(
                pos(5, 2..9),
                "Static method call on a trait: `NS\\Tr::f`".into()
            )
        );
        assert_eq!(
            d.reasons,
            vec![Message(pos(1, 6..8), "`NS\\Tr` is defined here".into())]
        );
        assert!(d.quickfixes.is_empty());
        assert!(!d.is_fixmed);
    }

    #[test]
    fn a_warning_that_depends_on_types_is_not_trusted() {
        let tcopt = all_warnings();
        let warning = |kind| typing_warning::is_as_always::T {
            kind,
            lhs_ty: "int".to_string(),
            rhs_ty: "num".to_string(),
        };
        use typing_warning::is_as_always::Kind as K;
        let diags = added(|| {
            add_(
                &tcopt,
                (pos(1, 0..4), Kind::Is_as_always, warning(K::Is_is_always_true)),
            );
            add_(
                &tcopt,
                (
                    pos(2, 0..4),
                    Kind::Is_as_always,
                    warning(K::As_always_fails { is_nullable: true }),
                ),
            );
            add_(
                &tcopt,
                (
                    pos(3, 0..4),
                    Kind::Is_as_always,
                    warning(K::As_always_fails { is_nullable: false }),
                ),
            );
        });
        assert_eq!(
            diags
                .iter()
                .map(|d| (d.severity, d.code, d.claim.1.to_string()))
                .collect::<Vec<_>>(),
            vec![
                (
                    Severity::Warning { is_trusted: false },
                    12009,
                    "This `is` check is always `true`. The expression on the left has type `int` which is a subtype of `num`.".to_string()
                ),
                (
                    Severity::Warning { is_trusted: false },
                    12012,
                    "This `as` assertion will always fail and lead to a `null` value. The expression on the left has type `int` which shares no values with `num`.".to_string()
                ),
                (
                    Severity::Warning { is_trusted: false },
                    12012,
                    "This `as` assertion will always fail and lead to an exception at runtime. The expression on the left has type `int` which shares no values with `num`.".to_string()
                ),
            ]
        );
    }

    #[test]
    fn nothing_is_added_when_the_code_is_disabled() {
        let none = tcopt(NoneOrAllExcept::NNone);
        let except = tcopt(NoneOrAllExcept::AllExcept(vec![12020]));
        let diags = added(|| {
            add_(
                &none,
                (
                    pos(5, 2..9),
                    Kind::Static_call_on_trait,
                    static_call_on_trait(),
                ),
            );
            add_(
                &except,
                (
                    pos(5, 2..9),
                    Kind::Static_call_on_trait,
                    static_call_on_trait(),
                ),
            );
        });
        assert!(diags.is_empty());
        assert!(!code_is_enabled(&none, Codes::TanyFound));
        assert!(!code_is_enabled(&except, Codes::StaticCallOnTrait));
        assert!(code_is_enabled(&except, Codes::TanyFound));
    }

    #[test]
    fn lazy_data_is_only_computed_for_a_warning_that_is_reported() {
        let forced = std::cell::Cell::new(0);
        let warning = || typing_warning::sketchy_equality::T {
            result: false,
            left: Lazy::new(Box::new(|| {
                forced.set(forced.get() + 1);
                vec![Message(pos(1, 0..1), "This is an int".into())]
            })),
            right: Lazy::new(Box::new(|| {
                forced.set(forced.get() + 1);
                vec![Message(pos(2, 0..1), "This is a string".into())]
            })),
            left_trail: vec![pos(3, 0..1)],
            right_trail: vec![pos(4, 0..1), pos(5, 0..1)],
        };
        let none = tcopt(NoneOrAllExcept::NNone);
        let diags = added(|| add_(&none, (pos(9, 0..5), Kind::Sketchy_equality, warning())));
        assert!(diags.is_empty());
        assert_eq!(forced.get(), 0);

        let all = all_warnings();
        let diags = added(|| add_(&all, (pos(9, 0..5), Kind::Sketchy_equality, warning())));
        assert_eq!(forced.get(), 2);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, 12001);
        assert_eq!(diags[0].severity, Severity::Warning { is_trusted: false });
        assert_eq!(
            diags[0].claim.1.to_string(),
            "This expression is likely always `false`"
        );
        let typedef = "Typedef definition comes from here";
        assert_eq!(
            diags[0].reasons,
            vec![
                Message(pos(1, 0..1), "This is an int".into()),
                Message(pos(3, 0..1), typedef.into()),
                Message(pos(2, 0..1), "This is a string".into()),
                Message(pos(4, 0..1), typedef.into()),
                Message(pos(5, 0..1), typedef.into()),
            ]
        );
    }

    #[test]
    fn truthiness_test_claims() {
        use typing_warning::truthiness_test::Kind as K;
        use typing_warning::truthiness_test::SketchyKind;
        use typing_warning::truthiness_test::T;
        let claim = |kind, expr: Option<&str>, not| {
            T {
                kind,
                ty: "string".to_string(),
                expr: expr.map(|e| e.to_string()),
                not,
            }
            .claim()
        };
        assert_eq!(
            claim(K::Invalid { truthy: true }, None, false),
            "Invalid condition: a value of type `string` will always be truthy"
        );
        assert_eq!(
            claim(K::Sketchy(SketchyKind::String), None, false),
            "Sketchy condition: testing the truthiness of string may not behave as expected.\nThe values `\"\"` and `\"0\"` are both considered falsy. To check for non-emptiness, use `!Str\\is_empty`."
        );
        assert_eq!(
            claim(K::Sketchy(SketchyKind::String), Some("$x"), true),
            "`!$x` is a sketchy condition: testing the falsiness of string may not behave as expected.\nThe values `\"\"` and `\"0\"` are both considered falsy. To check for emptiness, use `Str\\is_empty($x)`."
        );
        assert_eq!(
            claim(K::Sketchy(SketchyKind::Arraykey), Some("$x"), false),
            "`$x` is a sketchy condition: testing the truthiness of string may not behave as expected.\nThe values `0`, `\"\"`, and `\"0\"` are all considered falsy. Test for them explicitly."
        );
    }

    #[test]
    fn duplicate_properties_claims() {
        use typing_warning::duplicate_properties::T;
        let warning = |class_names: &[&str], initialized_with_constant| T {
            class_name: "\\C".to_string(),
            prop_name: "p".to_string(),
            class_names: class_names.iter().map(|c| c.to_string()).collect(),
            initialized_with_constant,
        };
        assert_eq!(
            warning(&["\\T1", "\\T2", "\\T3"], false).claim(),
            "Duplicated property `p` in `C` (defined in `T1`, `T2` and `T3`): all instances will be aliased at runtime"
        );
        assert_eq!(
            warning(&["\\T1", "\\T2"], true).claim(),
            "Property `p`, defined in T1 and T2, is inherited multiple times by class `C` and one of its instances is initialised with a class or enum constant"
        );
        assert_eq!(prettify_class_list(&[]), "");
        assert_eq!(prettify_class_list(&["A".to_string()]), "A");
    }

    #[test]
    fn the_codes_of_a_kind() {
        assert_eq!(codes(&Kind::Tany_found), vec![Codes::TanyFound]);
        assert_eq!(
            codes(&Kind::Is_as_always),
            vec![
                Codes::IsIsAlwaysTrue,
                Codes::IsIsAlwaysFalse,
                Codes::AsAlwaysSucceeds,
                Codes::AsAlwaysFails,
            ]
        );
        assert_eq!(
            codes(&Kind::Dynamic_call),
            vec![
                Codes::DynamicMethodCall,
                Codes::DynamicFunctionCall,
                Codes::DynamicArrayAccess,
                Codes::DynamicPropertyAccess,
            ]
        );
    }

    #[test]
    fn a_warning_is_suppressed_by_hh_ignore() {
        use oxidized::scoured_comments::ScouredComments;
        let file = RelativePath::make(Prefix::Root, "a.php".into());
        let mut sc = ScouredComments::new();
        sc.add_to_ignores(5, 12020, pos(4, 0..20));
        diagnostics_state::fixme_provider::provide_scoured_comments(&file, &sc, false);
        let tcopt = all_warnings();
        let diags = added(|| {
            add_(
                &tcopt,
                (
                    pos(5, 2..9),
                    Kind::Static_call_on_trait,
                    static_call_on_trait(),
                ),
            )
        });
        assert_eq!(diags.len(), 1);
        assert!(diags[0].is_fixmed);
    }
}
