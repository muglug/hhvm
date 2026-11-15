// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_data_type.ml`. See `hh/PORTING.md`.
//!
//! # Modules
//!
//! - `Tag` is [`tag`] (it re-exports `crate::typing_tag_defs`),
//!   `DataTypeReason` [`data_type_reason`], `TagWithReason`
//!   [`tag_with_reason`], `ApproxTagSet` [`approx_tag_set`] and `DataType`
//!   [`data_type`] (`DataType.Set` is `data_type::set`, `DataType.Class`
//!   `data_type::class`).
//! - The module type `SET` is the trait [`SET`], implemented by the set type
//!   (as the module types of `crate::approx_set_intf`): `ApproxTagSet.t` is
//!   `approx_set::Make<tag_with_reason::T>` (`approx_tag_set::T`), and
//!   `tag_with_reason::T` is its domain (`Approx_set.Make (TagWithReason)`).
//! - The functor `Make (S : SET)` is the module [`make`], whose functions are
//!   generic in `S: SET`; `DataType` is `include Make (ApproxTagSet)` with the
//!   functions that take a trail applied to an empty one.
//!
//! # Shadowed definitions
//!
//! `Make.Class` defines `to_datatypes` twice (the recursive one, then the one
//! that adds the tags of the special interfaces), and `Make` defines `fromTy`
//! twice (the recursive one, which takes a `context`, then the one of the
//! signature). The first ones are in the private modules
//! `make::class::without_special_interfaces` and `make::with_context`.
//!
//! # The forward reference
//!
//! `Tag.derive_generic_relation_ref` is set when the module is initialised,
//! once `DataType` is defined. As in `crate::typing_utils`, the reference here
//! starts with the function the initialisation puts in it
//! ([`derive_generic_relation`]).

use crate::hh_autoimport;
use crate::naming_special_names::classes::C_CLOSURE;
use crate::naming_special_names::classes::C_STRING;
use crate::typing_env_types::Env;
use crate::utils;

fn strip_ns(id: &str) -> String {
    hh_autoimport::strip_hh_namespace_if_autoimport(utils::strip_ns(id)).to_string()
}

/// Not in the OCaml: forget what this thread derived from declarations (see
/// `crate::rt::decl_epoch`).
pub fn forget_thread_memos() {
    make::class::forget_special_interface_cache();
    make::class::release_special_interface_cache()
}

/// `module Tag`
pub mod tag {
    use super::C_CLOSURE;
    use super::strip_ns;
    use crate::decl_entry;
    use crate::folded_class as cls;
    use crate::set_relation;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::TypeTagGeneric;
    use crate::typing_defs_core::get_node;
    use crate::typing_env;
    use crate::typing_env_types::Env;
    use crate::typing_print;
    pub use crate::typing_tag_defs::*;
    use crate::typing_utils;

    pub type Ctx = Env;

    /// Forward ref for; set after [DataType] is defined
    pub(super) static DERIVE_GENERIC_RELATION_REF: fn(&Env, &str, &T) -> set_relation::T =
        super::derive_generic_relation;

    fn is_fresh_generic(ty: &Ty) -> bool {
        match get_node(ty) {
            Ty_::Tgeneric(name) => typing_env::is_fresh_generic_parameter(name),
            _ => false,
        }
    }

    fn generics_for_class_and_ty_opt_l(
        env: &Env,
        cls: &str,
        ty_opt_l: &[Option<Ty>],
    ) -> Vec<Generic> {
        match typing_env::get_class(env, cls) {
            decl_entry::T::Found(class_info) => {
                let tparams = cls::tparams(&class_info);
                fn zip(
                    tparams: &[crate::typing_defs_core::DeclTparam],
                    ty_opt_l: &[Option<Ty>],
                ) -> Vec<Generic> {
                    match (tparams, ty_opt_l) {
                        ([], _) => vec![],
                        ([tparam, tparams @ ..], [Some(ty), ty_opt_l @ ..])
                            if matches!(
                                tparam.reified,
                                oxidized::aast_defs::ReifyKind::SoftReified
                                    | oxidized::aast_defs::ReifyKind::Reified
                            ) && !is_fresh_generic(ty) =>
                        {
                            let mut res = vec![Generic::Reified(ty.clone())];
                            res.extend(zip(tparams, ty_opt_l));
                            res
                        }
                        ([_, tparams @ ..], [_, ty_opt_l @ ..])
                        | ([_, tparams @ ..], ty_opt_l @ []) => {
                            let mut res = vec![Generic::Erased];
                            res.extend(zip(tparams, ty_opt_l));
                            res
                        }
                    }
                }
                zip(&tparams, ty_opt_l)
            }
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                ty_opt_l.iter().map(|_| Generic::Erased).collect()
            }
        }
    }

    pub fn generics_for_class_and_tyl(env: &Env, cls: &str, args: &[Ty]) -> Vec<Generic> {
        let ty_opt_l: Vec<Option<Ty>> = args.iter().map(|ty| Some(ty.clone())).collect();
        generics_for_class_and_ty_opt_l(env, cls, &ty_opt_l)
    }

    pub fn generics_for_class_and_tag_generic_l(
        env: &Env,
        cls: &str,
        generic_l: &[TypeTagGeneric],
    ) -> Vec<Generic> {
        let ty_opt_l: Vec<Option<Ty>> = generic_l
            .iter()
            .map(|g| match g {
                TypeTagGeneric::Filled(ty) => Some(ty.clone()),
                TypeTagGeneric::Wildcard(_) => None,
            })
            .collect();
        generics_for_class_and_ty_opt_l(env, cls, &ty_opt_l)
    }

    fn describe_generics(env: &Env, generics: &[Generic]) -> String {
        match generics {
            [_, ..] if generics.iter().any(|g| !equal_generic(g, &Generic::Erased)) => {
                "<".to_string()
                    + &generics
                        .iter()
                        .map(|g| match g {
                            Generic::Erased => "_".to_string(),
                            Generic::Reified(ty) => typing_print::full_strip_ns(true, env, ty),
                        })
                        .collect::<Vec<String>>()
                        .join(", ")
                    + ">"
            }
            _ => "".to_string(),
        }
    }

    pub fn describe(env: &Env, t: &T) -> String {
        match t {
            T::DictData => "dicts".to_string(),
            T::VecData => "vecs".to_string(),
            T::TupleData => "tuples".to_string(),
            T::ShapeData => "shapes".to_string(),
            T::KeysetData => "keysets".to_string(),
            T::StringData => "strings".to_string(),
            T::ResourceData => "resources".to_string(),
            T::BoolData => "booleans".to_string(),
            T::IntData => "ints".to_string(),
            T::FloatData => "floats".to_string(),
            T::NullData => "the value null".to_string(),
            T::ObjectData => "objects".to_string(),
            T::InstanceOf {
                name,
                kind: ClassKind::FinalClass(generics),
            } => {
                let generics = describe_generics(env, generics);
                format!(
                    "instances of the final class {}{}",
                    strip_ns(name),
                    generics
                )
            }
            T::InstanceOf {
                name,
                kind: ClassKind::Class(generics),
            } => {
                let generics = describe_generics(env, generics);
                format!("instances of the class {}{}", strip_ns(name), generics)
            }
            T::InstanceOf {
                name,
                kind: ClassKind::Interface,
            } => format!("instances of the interface {}", strip_ns(name)),
            T::ClassData => "class pointers".to_string(),
            T::LabelData => "enum class labels".to_string(),
            T::BuiltInData => "built-in values".to_string(),
            T::EnumData(name) => format!("values of the enum {}", strip_ns(name)),
            T::GenericData(name) => format!("values of the generic {}", name),
        }
    }

    /// Given [(T1a, T1b), (T2a, T2b)...],
    /// what is the relationship between Foo<T1a, T2a, ...> and Foo<T1b, T2b, ...>
    fn relation_generics(env: &Env, generic_pairs: &[(Generic, Generic)]) -> set_relation::T {
        match generic_pairs {
            [] => set_relation::EQUIVALENT,
            [(Generic::Erased, Generic::Erased), generic_pairs @ ..] => {
                relation_generics(env, generic_pairs)
            }
            [(_, Generic::Erased), generic_pairs @ ..] => {
                let rel = relation_generics(env, generic_pairs);
                set_relation::inter(&set_relation::SUBSET, &rel)
            }
            [(Generic::Erased, Generic::Reified(_)), ..] => set_relation::NONE,
            [
                (Generic::Reified(left), Generic::Reified(right)),
                generic_pairs @ ..,
            ] => {
                let is_sub_left_right =
                    typing_utils::is_sub_type_opt_ignore_generic_params(env, left, right);
                let is_sub_right_left =
                    typing_utils::is_sub_type_opt_ignore_generic_params(env, right, left);
                match (is_sub_left_right, is_sub_right_left) {
                    (Some(true), Some(true)) => relation_generics(env, generic_pairs),
                    (Some(false), _) | (_, Some(false)) => set_relation::DISJOINT,
                    _ => set_relation::NONE,
                }
            }
        }
    }

    pub fn relation(tag1: &T, env: &Ctx, tag2: &T) -> set_relation::T {
        use T::*;
        match (tag1, tag2) {
            // Built-in data can be any value made exclusively by the runtime.
            // It includes some tags that aren't able to be tested for within the surface language.
            // Since this can include multiple data types at runtime, we should consider their,
            // relationship to each other to be unknown
            (BuiltInData, BuiltInData)
            // Built-in data includes objects that are used as part of certain features that aren't
            // exposed to the surface language. An example of this is MethCallerHelper, which is a
            // the instance produce for calls to meth_caller(). This means there is some overlap
            // between the set of values that are built-in and objects
            | (BuiltInData, ObjectData)
            | (ObjectData, BuiltInData) => set_relation::NONE,
            // Shapes are represented imprecisely so do not consider them as equal
            (ShapeData, ShapeData) | (DictData, ShapeData) | (ShapeData, DictData) => {
                set_relation::NONE
            }
            // Tuples are represented imprecisely so do not consider them as equal
            (TupleData, TupleData) | (VecData, TupleData) | (TupleData, VecData) => {
                set_relation::NONE
            }
            // Enums share runtime representation with arraykeys; same-name enums are
            // equivalent, different enums may share values and so are uncertain.
            (EnumData(e1), EnumData(e2)) if e1 == e2 => set_relation::EQUIVALENT,
            (EnumData(_), EnumData(_)) => set_relation::NONE,
            (EnumData(_), IntData | StringData) | (IntData | StringData, EnumData(_)) => {
                set_relation::NONE
            }
            (EnumData(_), _) | (_, EnumData(_)) => set_relation::DISJOINT,
            (GenericData(g1), GenericData(g2)) if g1 == g2 => set_relation::EQUIVALENT,
            (GenericData(g), other) => {
                let f = DERIVE_GENERIC_RELATION_REF;
                f(env, g, other)
            }
            (other, GenericData(g)) => {
                let f = DERIVE_GENERIC_RELATION_REF;
                set_relation::flip(&f(env, g, other))
            }
            (tag1, tag2) if equal(tag1, tag2) => set_relation::EQUIVALENT,
            (ObjectData, InstanceOf { .. }) => set_relation::SUPERSET,
            (InstanceOf { .. }, ObjectData) => set_relation::SUBSET,
            (
                InstanceOf {
                    name: cls1,
                    kind: kind1,
                },
                InstanceOf {
                    name: cls2,
                    kind: kind2,
                },
            ) => {
                let is_instance_of = |sub: &str, sup: &str| -> Option<bool> {
                    let cls = decl_entry::to_option(typing_env::get_class(env, sub))?;
                    Some(cls::has_ancestor(&cls, sup))
                };
                let is_instance_of_closure = |cls: &str| cls == C_CLOSURE;

                let rel = (|| -> Option<set_relation::T> {
                    let cls1_instance_of_cls2 = is_instance_of(cls1, cls2)?;
                    if cls1_instance_of_cls2 {
                        if has_reified(kind2) {
                            // TODO(T221435654)
                            // if cls2 has reified generics and cls1 inherits cls2 but
                            // cls1 != cls2, we would need to know *how* cls1 inherits from
                            // cls2, i.e. what are the generics provided to cls2 in the
                            // inheritting declaration(s)
                            Some(set_relation::NONE)
                        } else {
                            Some(set_relation::SUBSET)
                        }
                    } else {
                        let cls2_instance_of_cls1 = is_instance_of(cls2, cls1)?;
                        if cls2_instance_of_cls1 {
                            if has_reified(kind1) {
                                // TODO(T221435654) see comment above
                                Some(set_relation::NONE)
                            } else {
                                Some(set_relation::SUPERSET)
                            }
                        } else if cls1 == cls2 {
                            Some(relation_generics(
                                env,
                                &zip_generics(
                                    &get_generics_from_kind(kind1),
                                    &get_generics_from_kind(kind2),
                                ),
                            ))
                        } else {
                            match (kind1, kind2) {
                                (ClassKind::FinalClass(_), _) | (_, ClassKind::FinalClass(_)) => {
                                    Some(set_relation::DISJOINT)
                                }
                                (ClassKind::Interface, _) | (_, ClassKind::Interface) => {
                                    // Closures cannot be implemented in user-land so we assume
                                    // it is disjoint from any user specified interface
                                    if is_instance_of_closure(cls1) || is_instance_of_closure(cls2) {
                                        Some(set_relation::DISJOINT)
                                    } else {
                                        Some(set_relation::NONE)
                                    }
                                }
                                (ClassKind::Class(_), ClassKind::Class(_)) => {
                                    Some(set_relation::DISJOINT)
                                }
                            }
                        }
                    }
                })();
                rel.unwrap_or(set_relation::NONE)
            }
            _ => set_relation::DISJOINT,
        }
    }
}

/// Tracks the reason why a particular tag is assumed to be a part of the
/// data type of a type. Tracking is optional, depending on if an origin
/// type is provided or not.
pub mod data_type_reason {
    use crate::type_expansions;
    use crate::typing_defs_core::Ty;
    use crate::typing_reason;
    use crate::typing_reason::T as Reason;

    /// More information about where a particular tag comes from.
    /// For example, for tag DictData, subreasons might be Shapes or NoSubreason
    #[derive(Clone, Debug)]
    pub enum Subreason {
        NoSubreason,
        Shapes,
        Tuples,
        Nullable,
        Nums,
        Arraykeys,
        EnumForCaseTypeAsArraykey,
        SpecialInterface(String),
        Cyclic,
    }

    #[derive(Clone, Debug)]
    pub enum TrailKind {
        VariantOfCaseType(String),
        GenericUpperbound(String),
        UpperboundOfNewType(String),
        UpperboundOfEnum(String),
        SealedInterface(String),
        Requirement(String),
        ExpansionOfTypeConstant { root_ty: Ty, name: String },
    }

    /// `instances` is in the order of the OCaml list: the most recent first.
    #[derive(Clone, Debug)]
    pub struct Trail {
        pub instances: Vec<(TrailKind, Reason)>,
        pub expansions: type_expansions::T,
    }

    pub type T = (Subreason, Trail);

    fn append(trail: &Trail, reason: Reason, kind: TrailKind) -> Result<Trail, Trail> {
        match &kind {
            TrailKind::VariantOfCaseType(name)
            | TrailKind::GenericUpperbound(name)
            | TrailKind::UpperboundOfNewType(name)
            | TrailKind::UpperboundOfEnum(name)
            | TrailKind::SealedInterface(name)
            | TrailKind::Requirement(name) => {
                let expansion = type_expansions::Expansion {
                    name: type_expansions::expandable::T::TypeAlias(name.clone()),
                    use_pos: typing_reason::to_pos(&reason),
                    def_pos: None,
                };
                match type_expansions::add_and_check_cycles(&trail.expansions, expansion) {
                    Ok(expansions) => {
                        let mut instances = Vec::with_capacity(trail.instances.len() + 1);
                        instances.push((kind, reason));
                        instances.extend(trail.instances.iter().cloned());
                        Ok(Trail {
                            instances,
                            expansions,
                        })
                    }
                    Err(_cycle) => Err(trail.clone()),
                }
            }
            TrailKind::ExpansionOfTypeConstant { .. } => {
                let mut instances = Vec::with_capacity(trail.instances.len() + 1);
                instances.push((kind, reason));
                instances.extend(trail.instances.iter().cloned());
                Ok(Trail {
                    instances,
                    ..trail.clone()
                })
            }
        }
    }

    pub fn case_type(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(
            trail,
            reason,
            TrailKind::VariantOfCaseType(name.to_string()),
        )
    }

    pub fn generic(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(
            trail,
            reason,
            TrailKind::GenericUpperbound(name.to_string()),
        )
    }

    pub fn newtype(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(
            trail,
            reason,
            TrailKind::UpperboundOfNewType(name.to_string()),
        )
    }

    pub fn enum_(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(trail, reason, TrailKind::UpperboundOfEnum(name.to_string()))
    }

    pub fn type_constant(
        trail: &Trail,
        reason: Reason,
        root_ty: Ty,
        name: &str,
    ) -> Result<Trail, Trail> {
        append(
            trail,
            reason,
            TrailKind::ExpansionOfTypeConstant {
                root_ty,
                name: name.to_string(),
            },
        )
    }

    pub fn sealed_interface(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(trail, reason, TrailKind::SealedInterface(name.to_string()))
    }

    pub fn requirement(trail: &Trail, reason: Reason, name: &str) -> Result<Trail, Trail> {
        append(trail, reason, TrailKind::Requirement(name.to_string()))
    }

    pub fn make(subreason: Subreason, trail: Trail) -> T {
        (subreason, trail)
    }

    /// `val make_trail : trail`
    pub fn make_trail() -> Trail {
        Trail {
            instances: vec![],
            expansions: type_expansions::empty(),
        }
    }
}

/// `module TagWithReason`
pub mod tag_with_reason {
    use oxidized::pos_or_decl::PosOrDecl;
    use pos::ToOxidized;

    use super::data_type_reason;
    use super::data_type_reason::Subreason;
    use super::data_type_reason::Trail;
    use super::data_type_reason::TrailKind;
    use super::strip_ns;
    use super::tag;
    use crate::approx_set_intf::DomainType;
    use crate::decl_utils;
    use crate::markdown_lite;
    use crate::set_relation;
    use crate::typing_defs_core::DeclTy;
    use crate::typing_env_types::Env;
    use crate::typing_print;
    use crate::typing_reason;

    pub type Ctx = tag::Ctx;

    #[derive(Clone, Debug)]
    pub struct T {
        pub subreason: Subreason,
        pub trail: Trail,
        pub tag: tag::T,
    }

    pub fn relation(t1: &T, ctx: &Ctx, t2: &T) -> set_relation::T {
        let T { tag: tag1, .. } = t1;
        let T { tag: tag2, .. } = t2;
        tag::relation(tag1, ctx, tag2)
    }

    pub fn make((subreason, trail): data_type_reason::T, tag: tag::T) -> T {
        T {
            subreason,
            trail,
            tag,
        }
    }

    pub fn to_message(
        env: &Env,
        f: impl Fn(&str) -> String,
        (origin, t): &(DeclTy, T),
    ) -> Vec<(PosOrDecl, String)> {
        let T {
            subreason,
            trail,
            tag,
        } = t;
        let ty_str =
            typing_print::full_strip_ns_decl(None, false, env, &origin.clone().to_oxidized());
        // `Reason.to_pos (get_reason origin)`
        let pos = PosOrDecl::from(decl_utils::get_pos(origin));
        let prefix = f(&ty_str);
        let tag_str = tag::describe(env, tag);
        let subreason_str = match subreason {
            Subreason::NoSubreason => "".to_string(),
            Subreason::Shapes => " because shapes are dicts at runtime".to_string(),
            Subreason::Tuples => " because tuples are vecs at runtime".to_string(),
            Subreason::Nullable => " because it is a nullable type".to_string(),
            Subreason::Nums => " because nums are ints or floats".to_string(),
            Subreason::Arraykeys => " because arraykeys are ints or strings".to_string(),
            Subreason::EnumForCaseTypeAsArraykey => {
                " because enums are approximated as `arraykey` for case type variant disjointness"
                    .to_string()
                    + " — an `is` test on an enum cannot rule out other ints or strings"
            }
            Subreason::Cyclic => " because it is a cyclic type".to_string(),
            Subreason::SpecialInterface(name) => format!(
                " because `{}` is a special interface that includes non-object values",
                strip_ns(name)
            ),
        };
        let msg = prefix + &markdown_lite::md_bold(&tag_str) + &subreason_str;

        let trail_kind_msg = |kind: &TrailKind| match kind {
            TrailKind::VariantOfCaseType(name) => {
                format!("  via this variant of the case type `{}`", strip_ns(name))
            }
            TrailKind::GenericUpperbound(name) => {
                format!("  via this constraint on the generic `{}`", name)
            }
            TrailKind::UpperboundOfNewType(name) => {
                format!("  via the constraint on the newtype `{}`", strip_ns(name))
            }
            TrailKind::UpperboundOfEnum(name) => {
                format!("  via the constraint on the enum `{}`", strip_ns(name))
            }
            TrailKind::SealedInterface(name) => {
                format!("  via the sealed interface `{}`", strip_ns(name))
            }
            TrailKind::Requirement(name) => {
                format!("  via this requirement on `{}`", strip_ns(name))
            }
            TrailKind::ExpansionOfTypeConstant { root_ty, name } => {
                let name = format!(
                    "{}::{}",
                    typing_print::full_strip_ns(true, env, root_ty),
                    name
                );
                format!("  via the expansion of the type constant `{}`", name)
            }
        };
        // `List.fold trail.instances ~init:[] ~f:(fun acc (kind, reason) ->
        //   Reason.to_string (trail_kind_msg kind) reason @ acc)`
        let mut trail_result: Vec<(PosOrDecl, String)> = vec![];
        for (kind, reason) in &trail.instances {
            let mut l = typing_reason::to_string(&trail_kind_msg(kind), reason);
            l.extend(trail_result);
            trail_result = l;
        }
        let mut res = vec![(pos, msg)];
        res.extend(trail_result);
        res
    }

    /// `TagWithReason` as the domain of `Approx_set.Make (TagWithReason)`.
    impl DomainType for T {
        type T = Self;
        type Ctx = Env;

        fn relation(t1: &Self, ctx: &Env, t2: &Self) -> set_relation::T {
            relation(t1, ctx, t2)
        }
    }
}

/// `module type SET`, implemented by the set type.
pub trait SET: Sized {
    fn empty() -> Self;

    fn singleton(reason: data_type_reason::T, tag: crate::typing_tag_defs::T) -> Self;

    fn of_list(reason: data_type_reason::T, tags: Vec<crate::typing_tag_defs::T>) -> Self;

    fn union(s1: &Self, s2: &Self) -> Self;

    fn inter(s1: &Self, s2: &Self) -> Self;

    fn diff(s1: &Self, s2: &Self) -> Self;

    fn are_disjoint(env: &Env, s1: &Self, s2: &Self) -> bool;

    fn is_subset(env: &Env, s1: &Self, s2: &Self) -> bool;
}

/// `module ApproxTagSet`: `include Approx_set.Make (TagWithReason)`, with
/// `singleton` and `of_list` taking a reason.
pub mod approx_tag_set {
    use super::data_type_reason;
    use super::tag;
    use super::tag_with_reason;
    use crate::approx_set;
    use crate::typing_env_types::Env;

    /// `ApproxTagSet.t`
    pub type T = approx_set::Make<tag_with_reason::T>;

    /// `ApproxTagSet.disjoint`: `Sat | Unsat { left; relation; right }`
    pub type Disjoint = approx_set::Disjoint<tag_with_reason::T>;

    pub fn empty() -> T {
        T::empty()
    }

    pub fn singleton(reason: data_type_reason::T, tag: tag::T) -> T {
        T::singleton(tag_with_reason::make(reason, tag))
    }

    pub fn of_list(reason: data_type_reason::T, tags: Vec<tag::T>) -> T {
        T::of_list(
            tags.into_iter()
                .map(|tag| tag_with_reason::make(reason.clone(), tag))
                .collect(),
        )
    }

    pub fn union(s1: &T, s2: &T) -> T {
        T::union(s1, s2)
    }

    pub fn inter(s1: &T, s2: &T) -> T {
        T::inter(s1, s2)
    }

    pub fn diff(s1: &T, s2: &T) -> T {
        T::diff(s1, s2)
    }

    pub fn are_disjoint(env: &Env, s1: &T, s2: &T) -> bool {
        T::are_disjoint(env, s1, s2)
    }

    pub fn is_subset(env: &Env, s1: &T, s2: &T) -> bool {
        T::is_subset(env, s1, s2)
    }

    pub fn disjoint(ctx: &Env, s1: &T, s2: &T) -> Disjoint {
        T::disjoint(ctx, s1, s2)
    }
}

impl SET for approx_tag_set::T {
    fn empty() -> Self {
        approx_tag_set::empty()
    }

    fn singleton(reason: data_type_reason::T, tag: crate::typing_tag_defs::T) -> Self {
        approx_tag_set::singleton(reason, tag)
    }

    fn of_list(reason: data_type_reason::T, tags: Vec<crate::typing_tag_defs::T>) -> Self {
        approx_tag_set::of_list(reason, tags)
    }

    fn union(s1: &Self, s2: &Self) -> Self {
        approx_tag_set::union(s1, s2)
    }

    fn inter(s1: &Self, s2: &Self) -> Self {
        approx_tag_set::inter(s1, s2)
    }

    fn diff(s1: &Self, s2: &Self) -> Self {
        approx_tag_set::diff(s1, s2)
    }

    fn are_disjoint(env: &Env, s1: &Self, s2: &Self) -> bool {
        approx_tag_set::are_disjoint(env, s1, s2)
    }

    fn is_subset(env: &Env, s1: &Self, s2: &Self) -> bool {
        approx_tag_set::is_subset(env, s1, s2)
    }
}

/// `module Make (Set : SET)`: the functions are generic in the set.
pub mod make {
    use oxidized::aast;
    use oxidized::ast_defs::Tprim;

    use super::C_CLOSURE;
    use super::C_STRING;
    use super::SET;
    use super::data_type_reason;
    use super::data_type_reason::Subreason;
    use super::data_type_reason::Trail;
    use super::tag;
    use super::tag::ClassKind;
    use crate::decl_hint;
    use crate::typing_defs_core::DeclTy;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::TypePredicate;
    use crate::typing_defs_core::TypePredicate_;
    use crate::typing_defs_core::TypeTag;
    use crate::typing_env_types::Env;
    use crate::typing_utils;

    /// `type t = Set.t`
    pub type T<S> = S;

    /// `mixed` should cover all possible data types.
    /// Update [Tag.all_tags] if additional tags are added to [Tag.t]
    pub fn mixed<S: SET>(reason: data_type_reason::T) -> S {
        S::of_list(reason, tag::all_tags())
    }

    /// Check [trail] for a cycle. If [trail] is an [Error], then
    /// a cycle has been detected and this will produce an error and return
    /// the result of [default]. If not, it will just call [f env trail]
    ///
    /// (`~env ~f ~default ~trail`. In OCaml the result of `default` includes
    /// the environment when the result does, and in `fromTy` that is an
    /// environment it captured earlier; here the environment is changed in
    /// place, so `default` is given it, to put the captured one back.)
    pub(super) fn cycle_handler<E, Res>(
        env: E,
        f: impl FnOnce(E, Trail) -> Res,
        default: impl FnOnce(E, data_type_reason::T) -> Res,
        trail: Result<Trail, Trail>,
    ) -> Res {
        match trail {
            Ok(trail) => f(env, trail),
            Err(trail) => default(env, data_type_reason::make(Subreason::Cyclic, trail)),
        }
    }

    pub fn prim_to_datatypes<S: SET>(trail: &Trail, prim: Tprim) -> S {
        use tag::T::*;
        let reason = data_type_reason::make(Subreason::NoSubreason, trail.clone());
        match prim {
            Tprim::Tint => S::singleton(reason, IntData),
            Tprim::Tnull => S::singleton(reason, NullData),
            Tprim::Tvoid => S::singleton(reason, NullData),
            Tprim::Tbool => S::singleton(reason, BoolData),
            Tprim::Tfloat => S::singleton(reason, FloatData),
            Tprim::Tresource => S::singleton(reason, ResourceData),
            Tprim::Tnum => S::of_list(
                data_type_reason::make(Subreason::Nums, trail.clone()),
                vec![IntData, FloatData],
            ),
            Tprim::Tarraykey => S::of_list(
                data_type_reason::make(Subreason::Arraykeys, trail.clone()),
                vec![IntData, StringData],
            ),
            Tprim::Tnoreturn => S::empty(),
        }
    }

    /// There are three ways values that are compatible with a function type can
    /// be introduce:
    ///   1. Via a lambda expression (i.e. `() ==> {}` or `function () {}`)
    ///   2. Via a meth_caller() expression
    ///   3. Via a function reference expression (i.e. `f<>` or `Cls:meth<>`)
    /// Each can produce values of the following kind:
    ///   1. Lambdas will be an instance of the special `Closure` class
    ///   2. meth_caller() will be an instance of MethCallerHelper
    ///   3. Function references have a dedicated datatype at runtime
    /// Out of these three possible kinds of value only `Closure` is denotable
    /// in the surface language, so the remaining two we represent as
    /// [Tag.BuiltinData].
    pub fn fun_to_datatypes<S: SET>(trail: &Trail) -> S {
        S::of_list(
            data_type_reason::make(Subreason::NoSubreason, trail.clone()),
            vec![
                tag::T::BuiltInData,
                tag::T::InstanceOf {
                    name: C_CLOSURE.to_string(),
                    kind: ClassKind::Class(vec![]),
                },
            ],
        )
    }

    pub fn nonnull_to_datatypes<S: SET>(trail: &Trail) -> S {
        S::of_list(
            data_type_reason::make(Subreason::NoSubreason, trail.clone()),
            tag::all_nonnull_tags(),
        )
    }

    pub fn tuple_to_datatypes<S: SET>(trail: &Trail) -> S {
        S::singleton(
            data_type_reason::make(Subreason::Tuples, trail.clone()),
            tag::T::TupleData,
        )
    }

    pub fn shape_to_datatypes<S: SET>(trail: &Trail) -> S {
        S::singleton(
            data_type_reason::make(Subreason::Shapes, trail.clone()),
            tag::T::ShapeData,
        )
    }

    pub fn label_to_datatypes<S: SET>(trail: &Trail) -> S {
        S::singleton(
            data_type_reason::make(Subreason::NoSubreason, trail.clone()),
            tag::T::LabelData,
        )
    }

    pub fn enum_to_datatypes<S: SET>(trail: &Trail, name: &str) -> S {
        S::singleton(
            data_type_reason::make(Subreason::NoSubreason, trail.clone()),
            tag::T::EnumData(name.to_string()),
        )
    }

    pub fn generic_to_datatypes<S: SET>(trail: &Trail, name: &str) -> S {
        S::singleton(
            data_type_reason::make(Subreason::NoSubreason, trail.clone()),
            tag::T::GenericData(name.to_string()),
        )
    }

    /// `module Class`
    pub mod class {
        use std::cell::RefCell;
        use std::collections::HashMap;

        use naming_special_names_rust as sn;
        use oxidized::pos::Pos;

        use super::super::C_STRING;
        use super::super::SET;
        use super::super::data_type_reason;
        use super::super::data_type_reason::Subreason;
        use super::super::data_type_reason::Trail;
        use super::super::tag;
        use super::super::tag::Generic;
        use crate::typing_env;
        use crate::typing_env_types::Env;
        use crate::typing_make_type;
        use crate::typing_reason;
        use crate::typing_utils;

        /// Set of interfaces that contain non-object members
        fn special_interfaces() -> &'static [&'static str] {
            &[
                sn::classes::STRINGISH,
                sn::classes::XHP_CHILD,
                C_STRING,
                sn::collections::TRAVERSABLE,
                sn::collections::KEYED_TRAVERSABLE,
                sn::collections::CONTAINER,
                sn::collections::KEYED_CONTAINER,
            ]
        }

        /// The [special_interfaces] contain additional data type tags beside
        /// [ObjectData]. These special interfaces are handled in [Typing_subtype].
        /// To avoid duplicating the logic, we check if a certain tag should be included
        /// by doing a subtype test against the interface type. If the type
        /// corresponding to a tag is a subtype then it will be included in the list.
        fn special_interface_to_datatypes(env: &mut Env, interface: &str) -> Vec<tag::T> {
            use tag::T::*;
            use typing_make_type as mk_ty;
            let r = typing_reason::none;
            let tag_to_type = vec![
                (
                    DictData,
                    mk_ty::dict(r(), mk_ty::nothing(r()), mk_ty::nothing(r())),
                ),
                (VecData, mk_ty::vec(r(), mk_ty::nothing(r()))),
                (KeysetData, mk_ty::keyset(r(), mk_ty::nothing(r()))),
                (StringData, mk_ty::string(r())),
                (ResourceData, mk_ty::resource(r())),
                (BoolData, mk_ty::bool(r())),
                (IntData, mk_ty::int(r())),
                (FloatData, mk_ty::float(r())),
                (NullData, mk_ty::null(r())),
            ];
            let interface_ty = match interface {
                name if name == sn::collections::TRAVERSABLE
                    || name == sn::collections::CONTAINER =>
                {
                    let targ = typing_env::fresh_type(env, Pos::NONE);
                    typing_make_type::class_type(
                        typing_reason::none(),
                        name.to_string(),
                        vec![targ],
                    )
                }
                name if name == sn::collections::KEYED_TRAVERSABLE
                    || name == sn::collections::KEYED_CONTAINER =>
                {
                    let targ1 = typing_env::fresh_type(env, Pos::NONE);
                    let targ2 = typing_env::fresh_type(env, Pos::NONE);
                    typing_make_type::class_type(
                        typing_reason::none(),
                        name.to_string(),
                        vec![targ1, targ2],
                    )
                }
                name if name == sn::classes::STRINGISH || name == sn::classes::XHP_CHILD => {
                    typing_make_type::class_type(typing_reason::none(), name.to_string(), vec![])
                }
                name if name == C_STRING => typing_make_type::string(typing_reason::none()),
                name => panic!(
                    "Unexpected special interface `{}` when determining data types",
                    name
                ),
            };
            // `List.fold` consing the tags: the last one first.
            let mut tags = vec![];
            for (tag, tag_ty) in tag_to_type {
                if typing_utils::can_sub_type(env, &tag_ty, &interface_ty) {
                    tags.insert(0, tag);
                }
            }
            tags
        }

        thread_local! {
            /// `special_interface_cache : Tag.t list String.Table.t`. OCaml
            /// has one table per process (a worker checks many files); here
            /// one per thread.
            static SPECIAL_INTERFACE_CACHE: RefCell<HashMap<String, Vec<tag::T>>> =
                RefCell::new(HashMap::new());
        }

        /// Not in the OCaml: empty `special_interface_cache` (an OCaml
        /// worker starts each job with an empty one: see
        /// `crate::rt::decl_epoch`).
        pub(crate) fn forget_special_interface_cache() {
            SPECIAL_INTERFACE_CACHE.with(|cache| cache.borrow_mut().clear())
        }

        /// Also frees the table's memory (see `crate::rt::decl_epoch`).
        pub(crate) fn release_special_interface_cache() {
            SPECIAL_INTERFACE_CACHE.with(|cache| *cache.borrow_mut() = Default::default())
        }

        /// Access to `special_interface_cache` (the table is borrowed only
        /// for the time of `f`).
        fn special_interface_cache<A>(f: impl FnOnce(&mut HashMap<String, Vec<tag::T>>) -> A) -> A {
            SPECIAL_INTERFACE_CACHE.with(|cache| f(&mut cache.borrow_mut()))
        }

        /// The first `to_datatypes` of `Make.Class`, which the second one
        /// shadows.
        mod without_special_interfaces {
            use naming_special_names_rust as sn;
            use oxidized::ast_defs::ClassishKind;
            use oxidized::pos_or_decl::PosOrDecl;
            use pos::ToOxidized;

            use super::super::super::C_STRING;
            use super::super::super::SET;
            use super::super::super::data_type_reason;
            use super::super::super::data_type_reason::Subreason;
            use super::super::super::data_type_reason::Trail;
            use super::super::super::tag::ClassKind;
            use super::super::super::tag::Generic;
            use super::super::super::tag::T::*;
            use super::super::cycle_handler;
            use crate::ast_defs;
            use crate::decl_entry;
            use crate::folded_class as cls;
            use crate::typing_env;
            use crate::typing_env_types::Env;
            use crate::typing_reason;
            use crate::typing_utils;

            pub(super) fn to_datatypes<S: SET>(
                safe_for_are_disjoint: bool,
                trail: &Trail,
                env: &Env,
                cls: &str,
                generics: &[Generic],
            ) -> S {
                let reason = data_type_reason::make(Subreason::NoSubreason, trail.clone());
                let handle_sealed_whitelist = |trail: &Trail,
                                               name: &str,
                                               pos: PosOrDecl,
                                               default: &dyn Fn(data_type_reason::T) -> S,
                                               whitelist: &im::OrdSet<String>|
                 -> S {
                    let trail = data_type_reason::sealed_interface(
                        trail,
                        typing_reason::witness_from_decl(pos),
                        name,
                    );
                    // `S_set.fold`: in increasing order. On a cycle the
                    // accumulator is replaced by `default`.
                    let mut acc = S::empty();
                    for whitelist_cls in whitelist.iter() {
                        acc = cycle_handler(
                            env,
                            |env, trail| {
                                S::union(
                                    &acc,
                                    &to_datatypes::<S>(
                                        safe_for_are_disjoint,
                                        &trail,
                                        env,
                                        whitelist_cls,
                                        // You cannot provide generics when sealing
                                        &[],
                                    ),
                                )
                            },
                            |_env, reason| default(reason),
                            trail.clone(),
                        );
                    }
                    S::inter(&default(reason.clone()), &acc)
                };
                if cls == C_STRING {
                    S::singleton(reason, StringData)
                } else if cls == sn::collections::DICT {
                    S::singleton(reason, DictData)
                } else if cls == sn::collections::KEYSET {
                    S::singleton(reason, KeysetData)
                } else if cls == sn::collections::VEC {
                    S::singleton(reason, VecData)
                } else if cls == sn::collections::ANY_ARRAY {
                    S::of_list(reason, vec![DictData, KeysetData, VecData])
                } else {
                    let name = cls;
                    // `Decl_entry.map_or ~default:(Set.singleton ~reason ObjectData) ~f`
                    match typing_env::get_class(env, name) {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                            S::singleton(reason, ObjectData)
                        }
                        decl_entry::T::Found(cls) => match cls::kind(&cls) {
                            ClassishKind::Cclass(_) if cls::final_(&cls) => S::singleton(
                                reason,
                                InstanceOf {
                                    name: name.to_string(),
                                    kind: ClassKind::FinalClass(generics.to_vec()),
                                },
                            ),
                            ClassishKind::Cclass(_) => {
                                let default = |reason: data_type_reason::T| {
                                    S::singleton(
                                        reason,
                                        InstanceOf {
                                            name: name.to_string(),
                                            kind: ClassKind::Class(generics.to_vec()),
                                        },
                                    )
                                };
                                match cls::sealed_whitelist(&cls) {
                                    None => default(reason.clone()),
                                    Some(whitelist) => handle_sealed_whitelist(
                                        trail,
                                        name,
                                        cls::pos(&cls),
                                        &default,
                                        &whitelist,
                                    ),
                                }
                            }
                            ClassishKind::Ctrait | ClassishKind::Cinterface => {
                                let default = |reason: data_type_reason::T| {
                                    if ast_defs::is_c_trait(cls::kind(&cls)) {
                                        S::singleton(reason, ObjectData)
                                    } else {
                                        S::singleton(
                                            reason,
                                            InstanceOf {
                                                name: name.to_string(),
                                                kind: ClassKind::Interface,
                                            },
                                        )
                                    }
                                };
                                match cls::sealed_whitelist(&cls) {
                                    None => {
                                        let reqs = cls::all_ancestor_reqs(&cls);
                                        if safe_for_are_disjoint || reqs.is_empty() {
                                            default(reason.clone())
                                        } else {
                                            let mut acc = default(reason.clone());
                                            for req in &reqs {
                                                let required_ty = &req.ty;
                                                match typing_utils::try_unwrap_class_type(
                                                    required_ty,
                                                ) {
                                                    None => {}
                                                    Some((r, req_cls, _paraml)) => {
                                                        let req_cls = req_cls.id_ref().as_str();
                                                        let trail = data_type_reason::requirement(
                                                            trail,
                                                            typing_reason::localize(
                                                                &r.clone().to_oxidized(),
                                                            ),
                                                            name,
                                                        );
                                                        acc = cycle_handler(
                                                            env,
                                                            |env, trail| {
                                                                S::inter(
                                                                    &acc,
                                                                    &to_datatypes::<S>(
                                                                        safe_for_are_disjoint,
                                                                        &trail,
                                                                        env,
                                                                        req_cls,
                                                                        // TODO(T221435654)
                                                                        // you can require a specific generic class,
                                                                        // but for now, [] (all Erased) is sound but
                                                                        // incomplete
                                                                        &[],
                                                                    ),
                                                                )
                                                            },
                                                            |_env, reason| default(reason),
                                                            trail,
                                                        );
                                                    }
                                                }
                                            }
                                            acc
                                        }
                                    }
                                    Some(whitelist) => handle_sealed_whitelist(
                                        trail,
                                        name,
                                        cls::pos(&cls),
                                        &default,
                                        &whitelist,
                                    ),
                                }
                            }
                            ClassishKind::Cenum | ClassishKind::CenumClass(_) => {
                                S::singleton(reason, ObjectData)
                            }
                        },
                    }
                }
            }
        }

        pub fn to_datatypes<S: SET>(
            safe_for_are_disjoint: bool,
            trail: &Trail,
            env: &mut Env,
            cls: &str,
            args: &[Generic],
        ) -> S {
            if special_interfaces().contains(&cls) {
                let tags = match special_interface_cache(|cache| cache.get(cls).cloned()) {
                    Some(tags) => tags,
                    None => {
                        let tags = special_interface_to_datatypes(env, cls);
                        // `Hashtbl.add` (Core): `Duplicate` leaves the table
                        // as it is.
                        special_interface_cache(|cache| {
                            cache.entry(cls.to_string()).or_insert_with(|| tags.clone());
                        });
                        tags
                    }
                };
                let set1 = S::of_list(
                    data_type_reason::make(
                        Subreason::SpecialInterface(cls.to_string()),
                        trail.clone(),
                    ),
                    tags,
                );
                let set2 = without_special_interfaces::to_datatypes::<S>(
                    safe_for_are_disjoint,
                    trail,
                    env,
                    cls,
                    args,
                );
                S::union(&set1, &set2)
            } else {
                without_special_interfaces::to_datatypes(
                    safe_for_are_disjoint,
                    trail,
                    env,
                    cls,
                    args,
                )
            }
        }
    }

    fn from_predicate<S: SET>(
        safe_for_are_disjoint: bool,
        trail: &Trail,
        env: &mut Env,
        predicate: &TypePredicate,
    ) -> S {
        use tag::T::*;
        let reason = data_type_reason::make(Subreason::NoSubreason, trail.clone());
        let from_tag = |env: &mut Env, tag: &TypeTag| -> S {
            match tag {
                TypeTag::BoolTag => S::singleton(reason.clone(), BoolData),
                TypeTag::IntTag => S::singleton(reason.clone(), IntData),
                TypeTag::ArraykeyTag => S::of_list(reason.clone(), vec![IntData, StringData]),
                TypeTag::FloatTag => S::singleton(reason.clone(), FloatData),
                TypeTag::NumTag => S::of_list(reason.clone(), vec![IntData, FloatData]),
                TypeTag::ResourceTag => S::singleton(reason.clone(), ResourceData),
                TypeTag::NullTag => S::singleton(reason.clone(), NullData),
                TypeTag::ClassTag(id, _) if id == C_STRING => {
                    S::singleton(reason.clone(), StringData)
                }
                TypeTag::ClassTag(id, args) => {
                    let generics = tag::generics_for_class_and_tag_generic_l(env, id, args);
                    class::to_datatypes(safe_for_are_disjoint, trail, env, id, &generics)
                }
                TypeTag::EnumTag(id) => {
                    // The enum's runtime representation is captured by [Tag.EnumData id],
                    // which relates as "uncertain" with arraykey tags via [Tag.relation].
                    // Because [EnumData] is excluded from [all_tags], [complement] of the
                    // result yields [mixed] — the safe over-approximation needed by the
                    // [Tneg]-based [fromTy] path.
                    enum_to_datatypes(trail, id)
                }
                TypeTag::GenericTag { name, from_like: _ } => {
                    // Same imprecise-tag treatment as [EnumData]: relates as [none] with
                    // everything, complement yields [mixed].
                    generic_to_datatypes(trail, name)
                }
            }
        };
        match &predicate.1 {
            TypePredicate_::IsTag(tag) => from_tag(env, tag),
            TypePredicate_::IsTupleOf(_) => S::singleton(reason.clone(), VecData),
            TypePredicate_::IsShapeOf(_) => S::singleton(reason.clone(), DictData),
            TypePredicate_::IsUnionOf(predicates) => {
                let sets: Vec<S> = predicates
                    .iter()
                    .map(|pred| from_predicate::<S>(safe_for_are_disjoint, trail, env, pred))
                    .collect();
                let mut acc = S::empty();
                for set in &sets {
                    acc = S::union(&acc, set);
                }
                acc
            }
            TypePredicate_::IsNot(inner) => {
                let inner_set = from_predicate::<S>(safe_for_are_disjoint, trail, env, inner);
                S::diff(&mixed::<S>(reason.clone()), &inner_set)
            }
        }
    }

    /// `type context`
    #[derive(Clone)]
    struct Context {
        safe_for_are_disjoint: bool,
        trail: Trail,
    }

    /// The first `fromTy` of `Make`, which the second one shadows.
    mod with_context {
        use naming_special_names_rust as sn;

        use super::super::C_STRING;
        use super::super::SET;
        use super::super::data_type_reason;
        use super::super::data_type_reason::Subreason;
        use super::super::data_type_reason::Trail;
        use super::super::tag;
        use super::Context;
        use super::class;
        use super::cycle_handler;
        use super::from_predicate;
        use super::fun_to_datatypes;
        use super::label_to_datatypes;
        use super::mixed;
        use super::nonnull_to_datatypes;
        use super::prim_to_datatypes;
        use super::shape_to_datatypes;
        use super::tuple_to_datatypes;
        use crate::decl_entry;
        use crate::folded_class as cls;
        use crate::typing_defs::ExpandEnv;
        use crate::typing_defs::TypedefTypeAssignment;
        use crate::typing_defs::empty_expand_env;
        use crate::typing_defs_core::ShapeType;
        use crate::typing_defs_core::TaccessType;
        use crate::typing_defs_core::Ty;
        use crate::typing_defs_core::Ty_;
        use crate::typing_defs_core::get_node;
        use crate::typing_defs_core::get_reason;
        use crate::typing_env;
        use crate::typing_env_types::Env;
        use crate::typing_reason;
        use crate::typing_set;
        use crate::typing_utils;

        pub(super) fn from_ty<S: SET>(ctx: &Context, env: &mut Env, ty: &Ty) -> S {
            let (_, ty) = typing_utils::strip_supportdyn(env, ty.clone());
            let ty = typing_env::expand_type(env, ty);
            let trail = &ctx.trail;
            let reason = data_type_reason::make(Subreason::NoSubreason, trail.clone());
            // `cycle_handler ty ~env ~trail`: on a cycle, the result is the
            // environment as it is here (`env_here`), with `mixed`.
            let cycle_handler_ty =
                |env_here: &Env, env: &mut Env, trail: Result<Trail, Trail>, ty: &Ty| -> S {
                    cycle_handler(
                        env,
                        |env, trail| {
                            from_ty::<S>(
                                &Context {
                                    trail,
                                    ..ctx.clone()
                                },
                                env,
                                ty,
                            )
                        },
                        |env, reason| {
                            *env = env_here.clone();
                            mixed::<S>(reason)
                        },
                        trail,
                    )
                };
            match get_node(&ty) {
                Ty_::Tprim(prim) => prim_to_datatypes(trail, *prim),
                Ty_::Tnonnull => nonnull_to_datatypes(trail),
                Ty_::Tdynamic(_) => mixed(reason),
                Ty_::Tany(_) => mixed(reason),
                Ty_::Toption(ty) => {
                    let data_types = from_ty::<S>(ctx, env, ty);
                    S::union(
                        &data_types,
                        &S::singleton(
                            data_type_reason::make(Subreason::Nullable, trail.clone()),
                            tag::T::NullData,
                        ),
                    )
                }
                // For now say it has the same tags as `nonnull`.
                // We should be able to be more precise, but need to
                // validate what are all the data types that are valid callables
                Ty_::Tfun(_) => fun_to_datatypes(trail),
                Ty_::Ttuple(_) => tuple_to_datatypes(trail),
                Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_)) => {
                    shape_to_datatypes(trail)
                }
                Ty_::Tlabel(_) => label_to_datatypes(trail),
                Ty_::Tvar(_) => mixed(reason),
                Ty_::Tgeneric(name) => {
                    let env_here = env.clone();
                    let upper_bounds =
                        typing_set::elements(&typing_env::get_upper_bounds(env, name));
                    let sets: Vec<S> = upper_bounds
                        .iter()
                        .map(|upper_bound_ty| {
                            let trail = data_type_reason::generic(
                                trail,
                                get_reason(upper_bound_ty).clone(),
                                name,
                            );
                            cycle_handler_ty(&env_here, env, trail, upper_bound_ty)
                        })
                        .collect();
                    // `List.reduce ~f:Set.inter sets`
                    let result_opt = sets.into_iter().reduce(|acc, set| S::inter(&acc, &set));
                    result_opt.unwrap_or_else(|| mixed(reason))
                }
                Ty_::Tunion(tyl) => {
                    let mut acc = S::empty();
                    for ty in tyl {
                        let dty = from_ty::<S>(ctx, env, ty);
                        acc = S::union(&acc, &dty);
                    }
                    acc
                }
                Ty_::Tintersection(tyl) => {
                    let sets: Vec<S> = tyl.iter().map(|ty| from_ty::<S>(ctx, env, ty)).collect();
                    let result_opt = sets.into_iter().reduce(|acc, set| S::inter(&acc, &set));
                    result_opt.unwrap_or_else(|| mixed(reason))
                }
                Ty_::TvecOrDict(_, _) => {
                    S::of_list(reason, vec![tag::T::VecData, tag::T::DictData])
                }
                Ty_::Taccess(TaccessType(root_ty, id)) => {
                    let env_here = env.clone();
                    let ety_env = empty_expand_env();
                    let (_, _cycles, ty) = typing_utils::expand_typeconst(
                        &ety_env,
                        env,
                        None,
                        None,
                        root_ty.clone(),
                        id.clone(),
                        true,
                    );
                    let trail = data_type_reason::type_constant(
                        trail,
                        get_reason(&ty).clone(),
                        root_ty.clone(),
                        &id.1,
                    );
                    cycle_handler_ty(&env_here, env, trail, &ty)
                }
                Ty_::Tdependent(_, ty) => from_ty::<S>(ctx, env, ty),
                Ty_::Tnewtype(name, _, _) if name == sn::classes::ENUM_CLASS_LABEL => {
                    label_to_datatypes(trail)
                }
                Ty_::Tnewtype(name, _, _)
                    if name == sn::classes::CLASS_NAME
                        || name == sn::classes::CLASS_OR_CLASSNAME =>
                {
                    S::of_list(reason, vec![tag::T::ClassData, tag::T::StringData])
                }
                // RepresentableAs<T> has the same runtime data type as T
                Ty_::Tnewtype(name, ty_args, _)
                    if ty_args.len() == 1 && name == sn::classes::REPRESENTABLE_AS =>
                {
                    let env_here = env.clone();
                    let ty_arg = &ty_args[0];
                    let trail = data_type_reason::newtype(trail, get_reason(ty_arg).clone(), name);
                    cycle_handler_ty(&env_here, env, trail, ty_arg)
                }
                Ty_::Tnewtype(name, ty_args, _) => {
                    // A Tnewtype is either an opaque alias (defined with keyword `newtype`)
                    // or a case type.
                    // For opaque type aliases, we look at the upper bound, but for case types,
                    // we expand.
                    let env_here = env.clone();
                    // `Decl_entry.Found { td_type_assignment = CaseType (variant, variants);
                    //   td_tparams; _ }`
                    let case_type = match typing_env::get_typedef(env, name) {
                        decl_entry::T::Found(td) => match &td.type_assignment {
                            TypedefTypeAssignment::CaseType(variant, variants) => {
                                Some((variant.clone(), variants.to_vec(), td.tparams.to_vec()))
                            }
                            TypedefTypeAssignment::SimpleTypeDef(..) => None,
                        },
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
                    };
                    match case_type {
                        Some((variant, variants, td_tparams)) => {
                            let td_tparams = &td_tparams;
                            // Here we should expand the case type instead of looking at the upper bound.
                            // If we do not expand, then we will over approximate the datatype.
                            // Consider:
                            //
                            //  case type Type1 = bool | int;
                            //  case type Type2 = Type1 | string;
                            //
                            // If we do not expand we will reject the definition of `Type2`
                            // because we will believe the datatype for `Type1` contains `string`.
                            // By expanding we can allow this definition.
                            let localize = |env: &mut Env, ty: &crate::typing_defs_core::DeclTy| {
                                typing_utils::localize(
                                    // The this_ty does not need to be set because case types cannot
                                    // appear within classes thus cannot use the this type.
                                    // If we ever change that this could need to be changed
                                    &ExpandEnv {
                                        substs: crate::decl_subst::make_locl(td_tparams, ty_args),
                                        ..empty_expand_env()
                                    },
                                    env,
                                    ty,
                                )
                            };
                            // Ignore case type where clauses for now.
                            // This will over-approximate the datatype because it will include all
                            // the variants' types regardless of satisfaction of the where clause.
                            // Over-approximation is safe, but incomplete: e.g. the following is OK
                            // but results in an error if where clauses are ignored.
                            //   case type Type1<T> = bool where T as arraykey | int;
                            //   case type Type2 = bool | Type1<float>;
                            // We can revisit should there be a use case for this.
                            let tyl: Vec<&crate::typing_defs_core::DeclTy> =
                                std::iter::once(&variant)
                                    .chain(variants.iter())
                                    .map(|v| &v.hint)
                                    .collect();
                            let mut acc = S::empty();
                            for variant in tyl {
                                let (_ty_err_opt, variant) = localize(env, variant);
                                let trail = data_type_reason::case_type(
                                    trail,
                                    get_reason(&variant).clone(),
                                    name,
                                );
                                let dty = cycle_handler_ty(&env_here, env, trail, &variant);
                                acc = S::union(&acc, &dty);
                            }
                            acc
                        }
                        None => {
                            if typing_env::is_enum(env, name) {
                                // Enums are approximated as `arraykey` for case type variant
                                // disjointness, regardless of their declared base type. An
                                // `is IntEnum` test does not narrow which arraykey tag the
                                // value may carry, so e.g. `IntEnum | string` is not a valid
                                // case type. We emit the {IntData, StringData} set directly
                                // with a subreason that surfaces this case-type-specific
                                // approximation, instead of recursing through a synthesized
                                // `arraykey` type (which would render the misleading
                                // "arising from an implicit `as arraykey` constraint"
                                // text).
                                let pos = match typing_env::get_enum(env, name) {
                                    decl_entry::T::Found(tc) => cls::pos(&tc),
                                    _ => typing_reason::to_pos(get_reason(&ty)),
                                };
                                let trail = match data_type_reason::enum_(
                                    trail,
                                    typing_reason::witness_from_decl(pos),
                                    name,
                                ) {
                                    Ok(trail) => trail,
                                    Err(trail) => trail,
                                };
                                S::of_list(
                                    data_type_reason::make(
                                        Subreason::EnumForCaseTypeAsArraykey,
                                        trail,
                                    ),
                                    vec![tag::T::IntData, tag::T::StringData],
                                )
                            } else {
                                let as_ty = typing_utils::get_newtype_super(
                                    env,
                                    get_reason(&ty).clone(),
                                    name,
                                    ty_args,
                                );
                                let trail = if typing_env::is_enum_class(env, name) {
                                    data_type_reason::enum_(trail, get_reason(&as_ty).clone(), name)
                                } else {
                                    data_type_reason::newtype(
                                        trail,
                                        get_reason(&as_ty).clone(),
                                        name,
                                    )
                                };
                                cycle_handler_ty(&env_here, env, trail, &as_ty)
                            }
                        }
                    }
                }
                Ty_::Tclass((_, cls), _, _) if cls == C_STRING => {
                    let reason = data_type_reason::make(Subreason::NoSubreason, trail.clone());
                    S::singleton(reason, tag::T::StringData)
                }
                Ty_::Tclass((_, cls), _, args) => {
                    let generics = tag::generics_for_class_and_tyl(env, cls, args);
                    class::to_datatypes(ctx.safe_for_are_disjoint, trail, env, cls, &generics)
                }
                Ty_::Tneg(predicate) => {
                    let right =
                        from_predicate::<S>(ctx.safe_for_are_disjoint, trail, env, predicate);
                    S::diff(&mixed::<S>(reason), &right)
                }
                Ty_::TclassPtr(_) => {
                    // StringData: during the migration a class<T> value can still be a string
                    // at runtime. The inner type is dropped: the runtime doesn't enforce it,
                    // so distinct class<_> are indistinguishable. See T199606542.
                    S::of_list(reason, vec![tag::T::ClassData, tag::T::StringData])
                }
            }
        }
    }

    pub fn from_hint<S: SET>(
        safe_for_are_disjoint: bool,
        env: &mut Env,
        hint: &aast::Hint,
    ) -> (DeclTy, S) {
        let decl_ty = decl_hint::hint(&env.decl_env, hint);
        let (_, ty) = typing_utils::localize_no_subst(env, true, &decl_ty);
        let trail = data_type_reason::make_trail();
        let dt = with_context::from_ty::<S>(
            &Context {
                safe_for_are_disjoint,
                trail,
            },
            env,
            &ty,
        );
        (decl_ty, dt)
    }

    pub fn from_ty<S: SET>(safe_for_are_disjoint: bool, env: &mut Env, ty: &Ty) -> S {
        let trail = data_type_reason::make_trail();
        with_context::from_ty::<S>(
            &Context {
                safe_for_are_disjoint,
                trail,
            },
            env,
            ty,
        )
    }
}

/// `module DataType`: `include Make (ApproxTagSet)`, with the functions that
/// take a trail applied to an empty one.
pub mod data_type {
    use oxidized::aast;
    use oxidized::ast_defs::Tprim;

    pub use super::approx_tag_set as set;
    use super::approx_tag_set;
    use super::data_type_reason;
    use super::data_type_reason::Subreason;
    use super::data_type_reason::Trail;
    use super::make;
    use crate::typing_defs_core::DeclTy;
    use crate::typing_defs_core::Ty;
    use crate::typing_env_types::Env;

    pub type T = approx_tag_set::T;

    /// `let trail = DataTypeReason.make_trail`
    fn trail() -> Trail {
        data_type_reason::make_trail()
    }

    /// The values of the module (`val mixed : Set.t`...), which the OCaml
    /// computes once: here once per thread (the sets are `Rc`s), instead of at
    /// every call (-1.0% of a check on the sample).
    macro_rules! value {
        ($name:ident, $e:expr) => {{
            thread_local! {
                static $name: T = $e;
            }
            $name.with(T::clone)
        }};
    }

    pub fn from_hint(safe_for_are_disjoint: bool, env: &mut Env, hint: &aast::Hint) -> (DeclTy, T) {
        make::from_hint::<T>(safe_for_are_disjoint, env, hint)
    }

    pub fn from_ty(safe_for_are_disjoint: bool, env: &mut Env, ty: &Ty) -> T {
        make::from_ty::<T>(safe_for_are_disjoint, env, ty)
    }

    pub fn prim_to_datatypes(prim: Tprim) -> T {
        make::prim_to_datatypes(&trail(), prim)
    }

    /// `val fun_to_datatypes : t`
    pub fn fun_to_datatypes() -> T {
        value!(VALUE, make::fun_to_datatypes(&trail()))
    }

    /// `val nonnull_to_datatypes : t`
    pub fn nonnull_to_datatypes() -> T {
        value!(VALUE, make::nonnull_to_datatypes(&trail()))
    }

    /// `val tuple_to_datatypes : t`
    pub fn tuple_to_datatypes() -> T {
        value!(VALUE, make::tuple_to_datatypes(&trail()))
    }

    /// `val shape_to_datatypes : t`
    pub fn shape_to_datatypes() -> T {
        value!(VALUE, make::shape_to_datatypes(&trail()))
    }

    /// `val label_to_datatypes : t`
    pub fn label_to_datatypes() -> T {
        value!(VALUE, make::label_to_datatypes(&trail()))
    }

    pub fn enum_to_datatypes(name: &str) -> T {
        make::enum_to_datatypes(&trail(), name)
    }

    pub fn generic_to_datatypes(name: &str) -> T {
        make::generic_to_datatypes(&trail(), name)
    }

    /// `val mixed : Set.t`
    pub fn mixed() -> T {
        value!(
            VALUE,
            make::mixed(data_type_reason::make(Subreason::NoSubreason, trail()))
        )
    }

    /// `module Class`
    pub mod class {
        use super::super::make;
        use super::super::tag::Generic;
        use super::T;
        use super::trail;
        use crate::typing_env_types::Env;

        pub fn to_datatypes(
            safe_for_are_disjoint: bool,
            env: &mut Env,
            cls: &str,
            generics: &[Generic],
        ) -> T {
            make::class::to_datatypes(safe_for_are_disjoint, &trail(), env, cls, generics)
        }
    }
}

/// Wire up the [GenericData] relation derivation, now that [DataType] is in
/// scope. The rule: convert the generic's upper bound into a data-type set
/// via [DataType.fromTy], then ask the set algebra whether that
/// upper-bound set is disjoint from / a subset of [{other_tag}]. Anything
/// else stays uncertain ([SetRelation.none]).
///
/// (What `let () = Tag.derive_generic_relation_ref := ...` puts in the
/// reference.)
fn derive_generic_relation(env: &Env, g: &str, other: &tag::T) -> crate::set_relation::T {
    use crate::set_relation;
    let g_ty = crate::typing_make_type::generic(crate::typing_reason::none(), g.to_string());
    let g_dt = data_type::from_ty(true, &mut env.clone(), &g_ty);
    let other_dt = data_type::set::singleton(
        data_type_reason::make(
            data_type_reason::Subreason::NoSubreason,
            data_type_reason::make_trail(),
        ),
        other.clone(),
    );
    if data_type::set::are_disjoint(env, &g_dt, &other_dt) {
        set_relation::DISJOINT
    } else if data_type::set::is_subset(env, &g_dt, &other_dt) {
        set_relation::SUBSET
    } else {
        set_relation::NONE
    }
}

#[cfg(test)]
mod tests {
    use super::data_type_reason;
    use super::data_type_reason::TrailKind;
    use super::tag;
    use super::tag_with_reason;
    use crate::typing_make_type as make_type;
    use crate::typing_reason;

    #[test]
    fn trails_record_the_most_recent_instance_first_and_detect_cycles() {
        let trail = data_type_reason::make_trail();
        let t1 = data_type_reason::generic(&trail, typing_reason::none(), "T")
            .ok()
            .unwrap();
        assert_eq!(t1.instances.len(), 1);
        let t2 = data_type_reason::newtype(&t1, typing_reason::none(), "\\N")
            .ok()
            .unwrap();
        assert_eq!(t2.instances.len(), 2);
        assert!(matches!(
            t2.instances[0].0,
            TrailKind::UpperboundOfNewType(_)
        ));
        assert!(matches!(t2.instances[1].0, TrailKind::GenericUpperbound(_)));
        // Expanding `T` again is a cycle: the trail is given back unchanged.
        match data_type_reason::case_type(&t2, typing_reason::none(), "T") {
            Err(t) => assert_eq!(t.instances.len(), 2),
            Ok(_) => panic!("expected a cycle"),
        }
        // Expansions of type constants are not checked for cycles.
        let root = make_type::int(typing_reason::none());
        let t3 = data_type_reason::type_constant(&t2, typing_reason::none(), root.clone(), "TC")
            .ok()
            .unwrap();
        assert!(data_type_reason::type_constant(&t3, typing_reason::none(), root, "TC").is_ok());
    }

    #[test]
    fn tags_with_reasons_keep_the_reason() {
        let reason = data_type_reason::make(
            data_type_reason::Subreason::Nums,
            data_type_reason::make_trail(),
        );
        let t = tag_with_reason::make(reason, tag::T::IntData);
        assert!(matches!(t.subreason, data_type_reason::Subreason::Nums));
        assert!(matches!(t.tag, tag::T::IntData));
        assert!(t.trail.instances.is_empty());
    }
}
