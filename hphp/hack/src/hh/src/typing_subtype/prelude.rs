// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 1-801): everything before `module rec Subtype`.
//! See `hh/PORTING.md`.
//!
//! | OCaml | Rust |
//! |---|---|
//! | `VisitedGoalsFunctor (Tset)` | [`visited_goals_functor`], generic in the element type of the sets (both instances are `Stdlib.Set`s: `crate::typing_set::stdlib_set`) |
//! | `VisitedGoals`, `VisitedGoalsInternal` | [`visited_goals`], [`visited_goals_internal`] |
//! | `Pretty`, `Subtype_env`, `Logging`, `Subtype_negation`, `Sd` | [`pretty`], [`subtype_env`], [`logging`], [`subtype_negation`], [`sd`] |
//! | `type lhs` | [`Lhs`] |
//! | `module type Constraint_handler` | the trait [`ConstraintHandler`] |
//!
//! # Signatures shared by the whole of `typing_subtype/`
//!
//! The `simplify` of every constraint handler (the `val simplify` of
//! `Constraint_handler`) is, as the rules of PORTING.md give it:
//!
//! ```ignore
//! fn simplify(
//!     subtype_env: &subtype_env::T,
//!     this_ty: Option<&Ty>,
//!     lhs: Lhs,
//!     rhs: Rhs,
//!     env: &mut Env,
//! ) -> typing_logic::SubtypeProp
//! ```
//!
//! The functions of `Subtype_env` that return an updated record
//! (`map_on_error`, `set_visited`, `possibly_add_violated_constraint`, ...)
//! take it by value, as they return it; the others take it by reference.

use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::markdown_lite;
use crate::pos_or_decl;
use crate::subtype_recursion_tracker;
use crate::tast;
use crate::tvid;
use crate::typing_coeffects;
use crate::typing_defs;
use crate::typing_defs_constraints;
use crate::typing_defs_constraints::CanTraverse;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_constraints::is_locl_type;
use crate::typing_defs_constraints::is_tyvar_i;
use crate::typing_defs_core;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::deref;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::is_nonexact;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_log;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

// We maintain a "visited" set for subtype goals. We do this only
// for goals of the form T <: t or t <: T where T is a generic parameter,
// as this is the more common case.
// T83096774: work out how to do this *efficiently* for all subtype goals.
//
// Here's a non-trivial example (assuming a contravariant type Contra).
// Under assumption T <: Contra<Contra<T>> show T <: Contra<T>.
// This leads to cycle of implications
//    T <: Contra<T> =>
//    Contra<Contra<T>> <: Contra<T> =>
//    T <: Contra<T>
// at which point we are back at the original goal.
//
// Note that it's not enough to just keep a set of visited generic parameters,
// else we would reject good code e.g. consider
//   class C extends B implements Contra<B>
// Now under assumption T <: C show T <: Contra<T>
// This leads to cycle of implications
//   T <: Contra<T> =>
//   C <: Contra<T> =>
//   Contra<B> <: Contra<T> =>
//   T <: B =>     // DO NOT REJECT here just because we've visited T before!
//   C <: B => done.
//
// We represent the visited set as a map from generic parameters
// to pairs of sets of types, such that an entry T := ({t1,...,tm},{u1,...,un})
// represents a set of goals
//   T <: u1, ..., t <: un , t1 <: T, ..., tn <: T

/// `VisitedGoalsFunctor (Tset : Stdlib.Set.S)`. Both instances apply it to a
/// `Stdlib.Set` (`Typing_set`, `Internal_type_set`), whose Rust port is
/// `crate::typing_set::stdlib_set`: the functor is generic in the element
/// type of those sets.
pub mod visited_goals_functor {
    use crate::typing_set::stdlib_set;
    use crate::typing_set::stdlib_set::OrderedType;

    type Map<Elt> = im::OrdMap<String, (stdlib_set::Set<Elt>, stdlib_set::Set<Elt>)>;

    /// `type t = (Tset.t * Tset.t) S_map.t` (abstract in the signature).
    ///
    /// `None` is the empty map: `im::OrdMap::new` allocates (and fills) a
    /// whole tree node, and a subtyping environment with two empty maps is
    /// created for every subtype query, almost all of which never add a goal.
    pub struct T<Elt>(Option<Map<Elt>>);

    impl<Elt> Clone for T<Elt> {
        fn clone(&self) -> Self {
            T(self.0.clone())
        }
    }

    pub fn empty<Elt>() -> T<Elt> {
        T(None)
    }

    impl<Elt> T<Elt> {
        /// No goal was added.
        pub fn is_empty(&self) -> bool {
            self.0.is_none()
        }
    }

    impl<Elt> T<Elt>
    where
        stdlib_set::Set<Elt>: Clone,
    {
        fn get(&self, name: &str) -> Option<&(stdlib_set::Set<Elt>, stdlib_set::Set<Elt>)> {
            self.0.as_ref().and_then(|map| map.get(name))
        }

        /// `S_map.add name x v`
        fn update(&self, name: String, x: (stdlib_set::Set<Elt>, stdlib_set::Set<Elt>)) -> T<Elt> {
            T(Some(match &self.0 {
                None => im::OrdMap::unit(name, x),
                Some(map) => map.update(name, x),
            }))
        }
    }

    /// Return None if (name <: ty) is already present, otherwise return Some v'
    /// where v' has the pair added
    pub fn try_add_visited_generic_sub<Elt: OrderedType>(
        v: &T<Elt>,
        name: &str,
        ty: Elt,
    ) -> Option<T<Elt>> {
        match v.get(name) {
            None => Some(v.update(
                name.to_string(),
                (stdlib_set::empty(), stdlib_set::singleton(ty)),
            )),
            Some((lower, upper)) => {
                if stdlib_set::mem(&ty, upper) {
                    None
                } else {
                    Some(v.update(
                        name.to_string(),
                        (lower.clone(), stdlib_set::add(ty, upper)),
                    ))
                }
            }
        }
    }

    /// Return None if (ty <: name) is already present, otherwise return Some v'
    /// where v' has the pair added
    pub fn try_add_visited_generic_super<Elt: OrderedType>(
        v: &T<Elt>,
        ty: Elt,
        name: &str,
    ) -> Option<T<Elt>> {
        match v.get(name) {
            None => Some(v.update(
                name.to_string(),
                (stdlib_set::singleton(ty), stdlib_set::empty()),
            )),
            Some((lower, upper)) => {
                if stdlib_set::mem(&ty, lower) {
                    None
                } else {
                    Some(v.update(
                        name.to_string(),
                        (stdlib_set::add(ty, lower), upper.clone()),
                    ))
                }
            }
        }
    }
}

/// `module VisitedGoals = VisitedGoalsFunctor (Typing_set)`
pub mod visited_goals {
    use super::visited_goals_functor;
    use crate::typing_defs_core::Ty;

    pub type T = visited_goals_functor::T<Ty>;

    pub fn empty() -> T {
        visited_goals_functor::empty()
    }

    pub fn try_add_visited_generic_sub(v: &T, name: &str, ty: Ty) -> Option<T> {
        visited_goals_functor::try_add_visited_generic_sub(v, name, ty)
    }

    pub fn try_add_visited_generic_super(v: &T, ty: Ty, name: &str) -> Option<T> {
        visited_goals_functor::try_add_visited_generic_super(v, ty, name)
    }
}

/// `module VisitedGoalsInternal = VisitedGoalsFunctor (Internal_type_set)`
pub mod visited_goals_internal {
    use super::visited_goals_functor;
    use crate::typing_defs_constraints::InternalType;

    pub type T = visited_goals_functor::T<InternalType>;

    pub fn empty() -> T {
        visited_goals_functor::empty()
    }

    pub fn try_add_visited_generic_sub(v: &T, name: &str, ty: InternalType) -> Option<T> {
        visited_goals_functor::try_add_visited_generic_sub(v, name, ty)
    }

    pub fn try_add_visited_generic_super(v: &T, ty: InternalType, name: &str) -> Option<T> {
        visited_goals_functor::try_add_visited_generic_super(v, ty, name)
    }
}

/// `module Pretty`
pub mod pretty {
    use super::*;

    pub fn describe_ty_default(env: &Env, ty: &InternalType) -> String {
        typing_print::full_strip_ns_i(true, env, ty)
    }

    /// The OCaml returns a function specialised on `is_coeffect`
    /// ("Optimization: specialize on partial application ... will check the
    /// flag only once"); here the flag is the first parameter.
    pub(crate) fn describe_ty(is_coeffect: bool, env: &Env, ty: &InternalType) -> String {
        if !is_coeffect {
            describe_ty_default(env, ty)
        } else {
            match ty {
                InternalType::LoclType(ty) => typing_coeffects::pretty(env, ty).force().clone(),
                ty => describe_ty_default(env, ty),
            }
        }
    }

    pub fn describe_ty_super(is_coeffect: bool, env: &Env, ty: &InternalType) -> String {
        // `print` and `default` are made before the match: they use the
        // environment and the type that the function is called with, not the
        // ones that shadow them below.
        let print = |ty: &InternalType| describe_ty(is_coeffect, env, ty);
        let default = || print(ty);
        match ty {
            InternalType::LoclType(lty) => {
                // `Env.expand_type` returns a new environment, which is the
                // one used from here on but is not returned: a copy.
                let mut expanded_env = env.clone();
                let lty = env::expand_type(&mut expanded_env, lty.clone());
                let env = &expanded_env;
                match get_node(&lty) {
                    Ty_::Tvar(v) => {
                        let upper_bounds = ity_set::elements(&env::get_tyvar_upper_bounds(env, *v));
                        // The constraint graph is transitively closed so we can filter tyvars.
                        let upper_bounds: Vec<InternalType> = upper_bounds
                            .into_iter()
                            .filter(|t| !is_tyvar_i(t))
                            .collect();
                        match upper_bounds.as_slice() {
                            [] => "some type not known yet".to_string(),
                            _ => {
                                let tyl = upper_bounds;
                                let (locl_tyl, cstr_tyl): (Vec<InternalType>, Vec<InternalType>) =
                                    tyl.into_iter().partition(is_locl_type);
                                let sep = match (locl_tyl.as_slice(), cstr_tyl.as_slice()) {
                                    ([_, ..], [_, ..]) => " and ",
                                    _ => "",
                                };
                                let locl_descr = match locl_tyl.as_slice() {
                                    [] => String::new(),
                                    tyl => {
                                        "of type ".to_string()
                                            + &markdown_lite::md_codify(
                                                &tyl.iter()
                                                    .map(|ty| print(ty))
                                                    .collect::<Vec<String>>()
                                                    .join(" & "),
                                            )
                                    }
                                };
                                let cstr_descr = cstr_tyl
                                    .iter()
                                    .map(|ty| describe_ty_super(is_coeffect, env, ty))
                                    .collect::<Vec<String>>()
                                    .join(" and ");
                                "something ".to_string() + &locl_descr + sep + &cstr_descr
                            }
                        }
                    }
                    Ty_::Toption(ty) if typing_defs::is_tyvar(ty) => {
                        "`null` or ".to_string()
                            + &describe_ty_super(
                                is_coeffect,
                                env,
                                &InternalType::LoclType(ty.clone()),
                            )
                    }
                    _ => markdown_lite::md_codify(&default()),
                }
            }
            InternalType::ConstraintType(ty) => match deref_constraint_type(ty) {
                (_, ConstraintType_::ThasMember(hm)) => {
                    let typing_defs_constraints::HasMember {
                        name: oxidized::ast_defs::Id(_, name),
                        type_: _,
                        class_id: _,
                        method: method_info,
                    } = hm;
                    match method_info {
                        None => format!("an object with property `{}`", name),
                        Some(_) => format!("an object with method `{}`", name),
                    }
                }
                (_, ConstraintType_::ThasTypeMember(htm)) => {
                    let typing_defs_constraints::HasTypeMember {
                        id,
                        lower: lo,
                        upper: up,
                    } = htm;
                    // `lo` and `up` are clones of the bounds, which share
                    // their nodes: `phys_equal` on them is `phys_equal` on
                    // the bounds.
                    if typing_defs_core::phys_equal(&lo, &up) {
                        // We use physical equality as a heuristic to generate
                        // slightly more readable descriptions.
                        format!(
                            "a class with `{{type {} = {}}}`",
                            id,
                            describe_ty(false, env, &InternalType::LoclType(lo))
                        )
                    } else {
                        let bound_desc = |prefix: &str,
                                          is_trivial: fn(&Env, &Ty) -> bool,
                                          bnd: &Ty| {
                            if is_trivial(env, bnd) {
                                String::new()
                            } else {
                                prefix.to_string()
                                    + &describe_ty(false, env, &InternalType::LoclType(bnd.clone()))
                            }
                        };
                        // The arguments of `Printf.sprintf` are evaluated
                        // right to left, and `TUtils.is_mixed` runs subtyping.
                        let up_desc = bound_desc(" as ", t_utils::is_mixed, &up);
                        let lo_desc = bound_desc(" super ", t_utils::is_nothing, &lo);
                        format!("a class with `{{type {}{}{}}}`", id, lo_desc, up_desc)
                    }
                }
                (_, ConstraintType_::TcanTraverse(_)) => {
                    "an array that can be traversed with foreach".to_string()
                }
                (_, ConstraintType_::TcanIndex(_)) => "an array that can be indexed".to_string(),
                (_, ConstraintType_::TcanIndexAssign(_)) => {
                    "an array that can be updated".to_string()
                }
                (_, ConstraintType_::ThasConst { name, ty: _ }) => {
                    format!("a class with a member `{}`", name)
                }
                (_, ConstraintType_::TtypeSwitch { .. })
                | (_, ConstraintType_::Tdestructure(_)) => {
                    markdown_lite::md_codify(&typing_print::full_strip_ns_i(
                        true,
                        env,
                        &InternalType::ConstraintType(ty.clone()),
                    ))
                }
            },
        }
    }
}

/// `module Subtype_env`
pub mod subtype_env {
    use super::*;

    /// `tparam_constraint_candidate = { r_sub; r_super }` (the common prefix
    /// `r_` of the fields is dropped, as for the records that `oxidized`
    /// and `hackrs` mirror).
    #[derive(Clone, Debug)]
    pub struct TparamConstraintCandidate {
        pub sub: Reason,
        pub super_: Reason,
        /// Not in OCaml: the `Rcstr_on_generics` reason the candidate
        /// resolves to in [`resolve_tparam_constraints`], when that is known
        /// without following the solutions of `Solved` reasons (`None`: not
        /// known). See [`candidate_to_add`].
        pub witness: Option<Reason>,
    }

    #[derive(Clone)]
    pub struct T {
        /// If set, requires the simplification of subtype constraints to be sound,
        /// meaning that the simplified constraint must imply the original one.
        pub require_soundness: bool,
        /// If set, requires the simplification of subtype constraints to be complete,
        /// meaning that the original constraint must imply the simplified one.
        /// If set, we also finish as soon as we see a goal of the form T <: t or
        /// t <: T for generic parameter T
        pub require_completeness: bool,
        /// If set, do not apply readonly subtyping through function types i.e. the
        /// readonly qualifier on function types and the readonly qualifier on
        /// function parameters. This flag is triggered by the <<__IgnoreReadonlyError>>
        /// on parameters.
        pub ignore_readonly: bool,
        /// If require_completeness is not set, maintain a visited goal set
        pub visited: visited_goals::T,
        pub visited_internal: visited_goals_internal::T,
        pub no_top_bottom: bool,
        /// is_dynamic_aware indicates whether subtyping should allow
        /// types that implement dynamic are considered sub-types of dynamic.
        pub is_dynamic_aware: bool,
        pub on_error: Option<reasons_callback::T>,
        pub report_ambiguous_shape_splat: bool,
        pub has_member_arg_posl: Option<Vec<Pos>>,
        /// The reason pairs along this subtype path. They are inspected only
        /// if an error is evaluated.
        ///
        /// The OCaml list (the most recent candidate first), persistent as
        /// in OCaml: the record is copied for every step of subtyping.
        pub tparam_constraint_candidates: crate::plist::List<TparamConstraintCandidate>,
        /// A flag which, if set, indicates that coeffects are being subtyped.
        /// Note: this is a short-term solution to provide coeffects.pretty-printing of
        /// `locl_ty`s that represent coeffects, since there is no good way to
        /// tell apart coeffects from regular types
        pub is_coeffect: bool,
        /// Which level the recursive calls to simplify_subtype should be logged at
        pub log_level: isize,
        /// This is a subtype check from within transitive closure
        /// e.g. string <: #1 <: int doing string <: int
        pub in_transitive_closure: bool,
        /// We're ignoring likes because we had a goal of the form `t <: ~u`
        /// for t <:D dynamic
        pub ignore_likes: bool,
        /// When enabled, allow rewriting of class<T> <: U to classname<T> <: U
        /// for a subset of U types. This is normally controlled by the
        /// class_sub_classname typechecker option, but it is unconditionally
        /// false for type well-formedness checks.
        pub class_sub_classname: bool,
        pub recursion_tracker: subtype_recursion_tracker::T,
    }

    /// Callback presence is fixed by [`create`]. Descendants may only contextualize
    /// an existing callback.
    pub fn map_on_error(t: T, f: impl FnOnce(reasons_callback::T) -> reasons_callback::T) -> T {
        match t.on_error {
            None => t,
            Some(on_error) => {
                let on_error = Some(f(on_error));
                T { on_error, ..t }
            }
        }
    }

    pub fn set_visited(t: T, visited: visited_goals::T) -> T {
        T { visited, ..t }
    }

    pub fn set_visited_internal(t: T, visited_internal: visited_goals_internal::T) -> T {
        T {
            visited_internal,
            ..t
        }
    }

    pub fn set_is_dynamic_aware(t: T, is_dynamic_aware: bool) -> T {
        T {
            is_dynamic_aware,
            ..t
        }
    }

    /// The optional arguments are `Option`s (`None` for the default); the
    /// default of `has_member_arg_posl` is `None`, so it is an
    /// `Option<Option<..>>`.
    #[allow(clippy::too_many_arguments)]
    pub fn create(
        require_soundness: Option<bool>,
        require_completeness: Option<bool>,
        ignore_readonly: Option<bool>,
        no_top_bottom: Option<bool>,
        is_dynamic_aware: Option<bool>,
        is_coeffect: Option<bool>,
        in_transitive_closure: Option<bool>,
        ignore_likes: Option<bool>,
        has_member_arg_posl: Option<Option<Vec<Pos>>>,
        report_ambiguous_shape_splat: Option<bool>,
        class_sub_classname: bool,
        log_level: isize,
        on_error: Option<reasons_callback::T>,
    ) -> T {
        let require_soundness = require_soundness.unwrap_or(true);
        let require_completeness = require_completeness.unwrap_or(false);
        let ignore_readonly = ignore_readonly.unwrap_or(false);
        let no_top_bottom = no_top_bottom.unwrap_or(false);
        let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
        let is_coeffect = is_coeffect.unwrap_or(false);
        let in_transitive_closure = in_transitive_closure.unwrap_or(false);
        let ignore_likes = ignore_likes.unwrap_or(false);
        let has_member_arg_posl = has_member_arg_posl.unwrap_or(None);
        let report_ambiguous_shape_splat = report_ambiguous_shape_splat.unwrap_or(false);
        T {
            require_soundness,
            require_completeness,
            ignore_readonly,
            visited: visited_goals::empty(),
            visited_internal: visited_goals_internal::empty(),
            no_top_bottom,
            is_dynamic_aware,
            is_coeffect,
            on_error: on_error.clone(),
            report_ambiguous_shape_splat,
            has_member_arg_posl,
            tparam_constraint_candidates: crate::plist::List::new(),
            log_level,
            in_transitive_closure,
            ignore_likes,
            class_sub_classname,
            recursion_tracker: subtype_recursion_tracker::empty(),
        }
    }

    /// What `Reason.Predicates.unpack_cstr_on_generics_opt r` gives, found
    /// without allocating when it can be.
    enum Unpack<'a> {
        /// `None`.
        No,
        /// `Some` of the payload of this `Rcstr_on_generics` reason.
        Yes(&'a Reason),
        /// Not known: a `Solved` reason is on the way, whose solutions
        /// `on_outermost` follows.
        Unknown,
    }

    /// The outermost reason, through the flows and projections, as
    /// `on_outermost` (which, until it meets a `Solved` reason, has no
    /// solution to follow).
    #[inline]
    fn unpack_cstr_on_generics_quick(r: &Reason) -> Unpack<'_> {
        use crate::typing_reason::T_;
        let mut r: &Reason = r;
        loop {
            match &**r {
                T_::Flow { from: t, .. }
                | T_::LowerBound { bound: t, .. }
                | T_::Axiom { next: t, .. }
                | T_::PrjBoth { sub_prj: t, .. }
                | T_::PrjOne { part: t, .. }
                | T_::Def(_, t) => r = t,
                T_::Solved { .. } => return Unpack::Unknown,
                T_::FromWitnessDecl(reason::WitnessDecl::CstrOnGenerics(..)) => {
                    return Unpack::Yes(r);
                }
                _ => return Unpack::No,
            }
        }
    }

    /// Whether two `Rcstr_on_generics` reasons give constraints that
    /// [`resolve_tparam_constraints`] takes as the same (its test on the
    /// previous constraint).
    fn same_cstr_on_generics(r1: &Reason, r2: &Reason) -> bool {
        use crate::typing_reason::T_;
        Rc::ptr_eq(r1, r2)
            || match (&**r1, &**r2) {
                (
                    T_::FromWitnessDecl(reason::WitnessDecl::CstrOnGenerics(p1, tparam1)),
                    T_::FromWitnessDecl(reason::WitnessDecl::CstrOnGenerics(p2, tparam2)),
                ) => {
                    pos_or_decl::equal(p1, p2)
                        && pos_or_decl::equal(&tparam1.0, &tparam2.0)
                        && tparam1.1 == tparam2.1
                }
                _ => false,
            }
    }

    /// Whether `possibly_add_violated_constraint` adds the candidate
    /// (`Some`, with its `witness`), or gives back the environment (`None`).
    ///
    /// Not in OCaml, which adds every pair, and copies the record, at each
    /// step of subtyping. The candidates are only read by
    /// [`resolve_tparam_constraints`] (when an error is built), so a
    /// candidate is added only if it can change what that gives:
    /// - only with an error callback (callback presence is fixed by
    ///   [`create`], and descendants only transform an existing callback
    ///   through [`map_on_error`]);
    /// - not when neither reason unpacks to a constraint on generics (it
    ///   skips those);
    /// - not when it unpacks to the same constraint as the latest candidate
    ///   (it skips a constraint equal to the previous one, and the latest
    ///   candidate's, when known, is the previous one).
    ///
    /// On the benchmark sample, about 9 million steps had a callback; 7% of
    /// the pairs unpack to a constraint, and most of those to the one of the
    /// latest candidate.
    #[inline]
    fn candidate_to_add(t: &T, r_sub: &Reason, r_super: &Reason) -> Option<Option<Reason>> {
        if t.on_error.is_none() {
            return None;
        }
        // `match unpack r_super with Some _ as c -> c | None -> unpack r_sub`
        let unpacked = match unpack_cstr_on_generics_quick(r_super) {
            Unpack::No => unpack_cstr_on_generics_quick(r_sub),
            unpacked => unpacked,
        };
        match unpacked {
            Unpack::No => None,
            Unpack::Unknown => Some(None),
            Unpack::Yes(witness) => match t.tparam_constraint_candidates.front() {
                Some(TparamConstraintCandidate {
                    witness: Some(latest),
                    ..
                }) if same_cstr_on_generics(latest, witness) => None,
                _ => Some(Some(witness.clone())),
            },
        }
    }

    fn add_tparam_constraint_candidate(t: T, r_sub: Reason, r_super: Reason, witness: Option<Reason>) -> T {
        let mut tparam_constraint_candidates = t.tparam_constraint_candidates;
        tparam_constraint_candidates.push_front(TparamConstraintCandidate {
            sub: r_sub,
            super_: r_super,
            witness,
        });
        T {
            tparam_constraint_candidates,
            ..t
        }
    }

    pub fn possibly_add_violated_constraint(subtype_env: T, r_sub: Reason, r_super: Reason) -> T {
        match candidate_to_add(&subtype_env, &r_sub, &r_super) {
            Some(witness) => add_tparam_constraint_candidate(subtype_env, r_sub, r_super, witness),
            None => subtype_env,
        }
    }

    /// `possibly_add_violated_constraint subtype_env r_sub r_super` on a
    /// borrowed environment: `None` when that gives back the same
    /// environment (then it is not copied).
    #[inline]
    pub fn possibly_add_violated_constraint_opt(subtype_env: &T, r_sub: &Reason, r_super: &Reason) -> Option<T> {
        candidate_to_add(subtype_env, r_sub, r_super)
            .map(|witness| add_tparam_constraint_candidate(subtype_env.clone(), r_sub.clone(), r_super.clone(), witness))
    }

    /// The result is in the order of the OCaml list.
    pub fn resolve_tparam_constraints(
        candidates: &[TparamConstraintCandidate],
    ) -> Vec<(PosOrDecl, reason::PosId)> {
        // `constraints` is built by adding at the head of the OCaml list:
        // here at the end of the vector, which is reversed at the end.
        fn add_candidate(
            mut constraints: Vec<(PosOrDecl, reason::PosId)>,
            TparamConstraintCandidate {
                sub: r_sub,
                super_: r_super,
                witness: _,
            }: &TparamConstraintCandidate,
        ) -> Vec<(PosOrDecl, reason::PosId)> {
            let candidate = match reason::predicates::unpack_cstr_on_generics_opt(r_super) {
                Some(candidate) => Some(candidate),
                None => reason::predicates::unpack_cstr_on_generics_opt(r_sub),
            };
            match candidate {
                None => constraints,
                Some(candidate) => {
                    let (p, tparam) = &candidate;
                    match constraints.last() {
                        Some((p_prev, tparam_prev))
                            if pos_or_decl::equal(p, p_prev)
                                // `Typing_defs.equal_pos_id`
                                && pos_or_decl::equal(&tparam.0, &tparam_prev.0)
                                && tparam.1 == tparam_prev.1 =>
                        {
                            constraints
                        }
                        _ => {
                            constraints.push(candidate);
                            constraints
                        }
                    }
                }
            }
        }
        let mut constraints = candidates.iter().rev().fold(vec![], add_candidate);
        constraints.reverse();
        constraints
    }

    /// `cstrs` of `Typing_error.Secondary.Subtyping_error` is a
    /// `(Pos_or_decl.t * Pos_or_decl.t Message.t) list Lazy.t`, which in OCaml
    /// is the type of the result of `resolve_tparam_constraints` (a `pos_id`
    /// is a `Pos_or_decl.t Message.t`); in Rust the two types differ, and the
    /// constraints are converted here.
    pub fn lazy_tparam_constraints(t: &T) -> Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>> {
        lazy_tparam_constraints_of(&t.tparam_constraint_candidates)
    }

    fn lazy_tparam_constraints_of(
        candidates: &crate::plist::List<TparamConstraintCandidate>,
    ) -> Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>> {
        let tparam_constraint_candidates = candidates.clone();
        Lazy::new(move || {
            let tparam_constraint_candidates: Vec<TparamConstraintCandidate> =
                tparam_constraint_candidates.iter().cloned().collect();
            resolve_tparam_constraints(&tparam_constraint_candidates)
                .into_iter()
                .map(|(p, (tparam_pos, tparam_name))| (p, Message(tparam_pos, tparam_name.into())))
                .collect()
        })
    }

    pub fn choose_on_error(
        cstrs: &Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>>,
        on_error: reasons_callback::T,
    ) -> reasons_callback::T {
        let has_constraints = cstrs.map(|cstrs| !cstrs.is_empty());
        let if_false = reasons_callback::retain_code(on_error.clone());
        reasons_callback::choose(has_constraints, on_error, if_false)
    }

    pub fn mk_secondary_error(
        cstrs: Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>>,
        t: &T,
        ty_sub: InternalType,
        ty_super: InternalType,
    ) -> secondary::T {
        secondary::T::SubtypingError {
            cstrs,
            ty_sub,
            ty_sup: ty_super,
            is_coeffect: t.is_coeffect,
        }
    }

    /// `choose_on_error cstrs on_error` for the callback of `t`.
    fn choose_on_error_of_env(
        cstrs: &Lazy<Vec<(PosOrDecl, Message<PosOrDecl>)>>,
        t: &T,
    ) -> Option<reasons_callback::T> {
        t.on_error
            .as_ref()
            .map(|on_error| choose_on_error(cstrs, on_error.clone()))
    }

    pub fn fail_with_secondary_error(
        t: &T,
        secondary_error: secondary::T,
    ) -> Option<typing_error::T> {
        t.on_error.as_ref().map(|_| {
            let cstrs = lazy_tparam_constraints(t);
            let on_error = choose_on_error_of_env(&cstrs, t).unwrap();
            typing_error::apply_reasons(secondary_error, on_error)
        })
    }

    /// Not built until needed, as [`fail_deferred`] (whose comment says why
    /// building it later gives the same error).
    pub fn fail(t: &T, ty_sub: InternalType, ty_super: InternalType) -> Option<typing_error::T> {
        t.on_error.as_ref().map(|_| {
            typing_error::T::Deferred(Rc::new(DeferredFail::new(t, ty_sub, ty_super)))
        })
    }

    /// `fail subtype_env ty_sub ty_super` on two locl types, as a value that
    /// builds the error only if it is needed.
    ///
    /// In OCaml the error is built at once (it is a few small blocks); here
    /// it is several allocations, needed at every step of subtyping that has
    /// an error callback, and almost never reported (on the benchmark sample,
    /// 2.8 million built, 212 reported). What `fail` builds depends only on
    /// the callback, the constraint candidates and `is_coeffect` of the
    /// subtype environment and on the two types, all immutable values, and
    /// building it has no effect: so it is built later, from copies of them,
    /// and gives the same error. A [`Fail`] borrows them; [`Fail::get`]
    /// copies them into a [`typing_error::T::Deferred`] error.
    pub fn fail_deferred<'a>(t: &'a T, ty_sub: &'a Ty, ty_super: &'a Ty) -> Fail<'a> {
        match &t.on_error {
            Some(_) => Fail(FailRepr::Of(FailOf {
                env: t,
                ty_sub,
                ty_super,
            })),
            None => Fail(FailRepr::Ready(None)),
        }
    }

    /// The error of a failing step of subtyping (`Typing_error.t option`),
    /// not built: see [`fail_deferred`]. `None` without a callback.
    #[derive(Clone)]
    pub struct Fail<'a>(FailRepr<'a>);

    #[derive(Clone)]
    enum FailRepr<'a> {
        /// (Behind an `Rc`, so that a `Fail`, which is copied at many
        /// steps, is small.)
        Ready(Option<Rc<typing_error::T>>),
        Of(FailOf<'a>),
    }

    #[derive(Clone, Copy)]
    struct FailOf<'a> {
        env: &'a T,
        ty_sub: &'a Ty,
        ty_super: &'a Ty,
    }

    struct DeferredFail {
        error: std::cell::OnceCell<typing_error::T>,
        candidates: crate::plist::List<TparamConstraintCandidate>,
        is_coeffect: bool,
        on_error: reasons_callback::T,
        ty_sub: InternalType,
        ty_super: InternalType,
    }

    impl DeferredFail {
        fn new(t: &T, ty_sub: InternalType, ty_super: InternalType) -> Self {
            DeferredFail {
                error: std::cell::OnceCell::new(),
                candidates: t.tparam_constraint_candidates.clone(),
                is_coeffect: t.is_coeffect,
                // `Some`: there is an error only with a callback.
                on_error: t.on_error.clone().unwrap(),
                ty_sub,
                ty_super,
            }
        }
    }

    impl typing_error::Deferred for DeferredFail {
        fn force(&self) -> &typing_error::T {
            self.error.get_or_init(|| {
                // The body of `fail`.
                let cstrs = lazy_tparam_constraints_of(&self.candidates);
                let secondary_error = secondary::T::SubtypingError {
                    cstrs: cstrs.clone(),
                    ty_sub: self.ty_sub.clone(),
                    ty_sup: self.ty_super.clone(),
                    is_coeffect: self.is_coeffect,
                };
                let on_error = choose_on_error(&cstrs, self.on_error.clone());
                typing_error::apply_reasons(secondary_error, on_error)
            })
        }
    }

    impl Fail<'_> {
        /// The error (`None` without a callback), as a
        /// [`typing_error::T::Deferred`].
        pub fn get(&self) -> Option<typing_error::T> {
            match &self.0 {
                FailRepr::Ready(err) => err.as_deref().cloned(),
                FailRepr::Of(f) => Some(typing_error::T::Deferred(Rc::new(DeferredFail::new(
                    f.env,
                    InternalType::LoclType(f.ty_sub.clone()),
                    InternalType::LoclType(f.ty_super.clone()),
                )))),
            }
        }
    }

    impl From<Option<typing_error::T>> for Fail<'_> {
        fn from(err: Option<typing_error::T>) -> Self {
            Fail(FailRepr::Ready(err.map(Rc::new)))
        }
    }

    impl From<Fail<'_>> for Option<typing_error::T> {
        fn from(fail: Fail<'_>) -> Self {
            fail.get()
        }
    }

    pub fn fail_with_suffix(
        t: &T,
        ty_sub: InternalType,
        ty_super: InternalType,
        suffix: secondary::T,
    ) -> Option<typing_error::T> {
        t.on_error.as_ref().map(|_| {
            let cstrs = lazy_tparam_constraints(t);
            let secondary_error = mk_secondary_error(cstrs.clone(), t, ty_sub, ty_super);
            let on_error = choose_on_error_of_env(&cstrs, t).unwrap();
            typing_error::apply_reasons(
                suffix,
                reasons_callback::prepend_on_apply(on_error, secondary_error),
            )
        })
    }

    pub fn check_infinite_recursion(
        subtype_env: T,
        op: subtype_recursion_tracker::subtype_op::T,
    ) -> Result<T, subtype_recursion_tracker::subtype_op::T> {
        subtype_recursion_tracker::add_op_and_check_infinite_recursion(
            subtype_env.recursion_tracker.clone(),
            op,
        )
        .map(|recursion_tracker| T {
            recursion_tracker,
            ..subtype_env
        })
    }
}

/// `module Logging`
///
/// - `log_subtype_i` and `log_subtype` read the environment (`&Env`) and
///   take the continuation `unit -> 'a` as `FnOnce() -> A`, as PORTING.md
///   gives them. A caller whose continuation changes the environment prints
///   with a copy of it: `let log_env = env.clone(); log_subtype_i(..,
///   &log_env, .., || f(env))`.
/// - The continuation of `log_subtype_prop` returns the environment
///   (`unit -> env * TL.subtype_prop`): it is `FnOnce(&mut Env) ->
///   SubtypeProp`, called with the environment that `log_subtype_prop` is
///   given. The arguments are printed in that environment as it was before
///   the call, the result in the environment the continuation leaves, as in
///   OCaml.
pub mod logging {
    use super::*;

    // Given a pair of types `ty_sub` and `ty_super` attempt to apply simplifications
    // and add to the accumulated constraints in `constraints` any necessary and
    // sufficient [(t1,ck1,u1);...;(tn,ckn,un)] such that
    //   ty_sub <: ty_super iff t1 ck1 u1, ..., tn ckn un
    // where ck is `as` or `=`. Essentially we are making solution-preserving
    // simplifications to the subtype assertion, for now, also generating equalities
    // as well as subtype assertions, for backwards compatibility with use of
    // unification.
    //
    // If `constraints = []` is returned then the subtype assertion is valid.
    //
    // If the subtype assertion is unsatisfiable then return `failed = Some f`
    // where `f` is a `unit-> unit` function that records an error message.
    // (Sometimes we don't want to call this function e.g. when just checking if
    //  a subtype holds)
    //
    // Elide singleton unions, treat invariant generics as both-ways
    // subtypes, and actually chase hierarchy for extends and implements.
    //
    // Annoyingly, we need to pass env back too, because Typing_phase.localize
    // expands type constants. (TODO: work out a better way of handling this)
    //
    // Special cases:
    //   If assertion is valid (e.g. string <: arraykey) then
    //     result can be the empty list (i.e. nothing is added to the result)
    //   If assertion is unsatisfiable (e.g. arraykey <: string) then
    //     we record this in the failed field of the result.

    pub(crate) fn log_subtype_i_<A>(
        this_ty: Option<&Ty>,
        function_name: &str,
        result: impl FnOnce(&A) -> Option<String>,
        env: &Env,
        ty_sub: &InternalType,
        ty_super: &InternalType,
        f: impl FnOnce() -> A,
    ) -> A {
        typing_log::log_function(
            &reason::to_pos(typing_defs_constraints::reason(ty_sub)),
            function_name,
            &[
                ("ty_sub".to_string(), typing_print::debug_i(env, ty_sub)),
                ("ty_super".to_string(), typing_print::debug_i(env, ty_super)),
                (
                    "this_ty".to_string(),
                    match this_ty {
                        None => "None".to_string(),
                        Some(ty) => typing_print::debug(env, ty),
                    },
                ),
            ],
            result,
            f,
        )
    }

    /// The OCaml `f` returns `(env, prop)`, and `~result` prints `prop` in
    /// that `env`: here `f` changes `env`, and the `'a` of `log_subtype_i_`
    /// is the environment with the proposition. The arguments are printed in
    /// the environment as it is before `f` (a copy).
    pub(crate) fn log_subtype_i_prop(
        this_ty: Option<&Ty>,
        function_name: &str,
        env: &mut Env,
        ty_sub: &InternalType,
        ty_super: &InternalType,
        f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
    ) -> tl::SubtypeProp {
        let env_before = env.clone();
        let (_env, prop) = log_subtype_i_(
            this_ty,
            function_name,
            |(env, prop): &(&mut Env, tl::SubtypeProp)| {
                Some(tl::print(|ty| typing_print::debug_i(&**env, ty), prop))
            },
            &env_before,
            ty_sub,
            ty_super,
            move || {
                let prop = f(env);
                (env, prop)
            },
        );
        prop
    }

    pub fn log_subtype_prop(
        env: &mut Env,
        ty_sub: &Ty,
        ty_super: &Ty,
        this_ty: Option<&Ty>,
        function_name: &str,
        f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
    ) -> tl::SubtypeProp {
        log_subtype_i_prop(
            this_ty,
            function_name,
            env,
            &InternalType::LoclType(ty_sub.clone()),
            &InternalType::LoclType(ty_super.clone()),
            f,
        )
    }

    pub fn should_log_subtype_i(
        env: &Env,
        level: isize,
        ty_sub: &InternalType,
        ty_super: &InternalType,
    ) -> bool {
        if !typing_log::should_log(env, "sub", level) {
            false
        } else {
            let level = if (t_utils::is_capability_i(ty_sub) || t_utils::is_capability_i(ty_super))
                && level < 3
            {
                3
            } else {
                level
            };
            typing_log::should_log(env, "sub", level)
        }
    }

    pub fn log_subtype_i<A>(
        this_ty: Option<&Ty>,
        function_name: &str,
        env: &Env,
        ty_sub: &InternalType,
        ty_super: &InternalType,
        f: impl FnOnce() -> A,
    ) -> A {
        log_subtype_i_(this_ty, function_name, |_| None, env, ty_sub, ty_super, f)
    }

    pub fn should_log_subtype(env: &Env, level: isize, ty_sub: &Ty, ty_super: &Ty) -> bool {
        // (The same short cut as in `should_log_subtype_i`, before the types
        // are copied into internal types.)
        typing_env_types::get_log_level(env, "sub") >= level
            && should_log_subtype_i(
            env,
            level,
            &InternalType::LoclType(ty_sub.clone()),
            &InternalType::LoclType(ty_super.clone()),
        )
    }

    pub fn log_subtype<A>(
        this_ty: Option<&Ty>,
        function_name: &str,
        env: &Env,
        ty_sub: &Ty,
        ty_super: &Ty,
        f: impl FnOnce() -> A,
    ) -> A {
        log_subtype_i(
            this_ty,
            function_name,
            env,
            &InternalType::LoclType(ty_sub.clone()),
            &InternalType::LoclType(ty_super.clone()),
            f,
        )
    }
}

/// `module Subtype_negation`
pub mod subtype_negation {
    use super::*;

    pub fn is_tprim_disjoint(tp1: Tprim, tp2: Tprim) -> bool {
        let one_side = |tp1: Tprim, tp2: Tprim| match (tp1, tp2) {
            (Tprim::Tnum, Tprim::Tint)
            | (Tprim::Tnum, Tprim::Tfloat)
            | (Tprim::Tarraykey, Tprim::Tint)
            | (Tprim::Tarraykey, Tprim::Tnum) => false,
            (
                _,
                Tprim::Tnum
                | Tprim::Tint
                | Tprim::Tvoid
                | Tprim::Tbool
                | Tprim::Tarraykey
                | Tprim::Tfloat
                | Tprim::Tnull
                | Tprim::Tresource
                | Tprim::Tnoreturn,
            ) => true,
        };
        tp1 != tp2 && one_side(tp1, tp2) && one_side(tp2, tp1)
    }

    /// Two classes c1 and c2 are disjoint iff there exists no c3 such that
    /// c3 <: c1 and c3 <: c2.
    pub fn is_class_disjoint(env: &Env, c1: &str, ex1: &Exact, c2: &str, ex2: &Exact) -> bool {
        let is_interface_or_trait = |c_def: &cls::T| match cls::kind(c_def) {
            ClassishKind::Cinterface | ClassishKind::Ctrait => true,
            ClassishKind::Cclass(_) | ClassishKind::CenumClass(_) | ClassishKind::Cenum => false,
        };
        if c1 == c2 {
            false
        } else if c1 == C_STRING || c2 == C_STRING {
            // Strings are disjoint from other classes, except for stringish
            !((c1 == sn::classes::STRINGISH && is_nonexact(ex1))
                || (c2 == sn::classes::STRINGISH && is_nonexact(ex2)))
        } else {
            // The components of the tuple are evaluated right to left: `c2`
            // is looked up (and its dependency recorded) first.
            let c2_def = env::get_class(env, c2);
            let c1_def = env::get_class(env, c1);
            match (c1_def, c2_def) {
                (decl_entry::T::Found(c1_def), decl_entry::T::Found(c2_def)) => {
                    if cls::final_(&c1_def) {
                        // if c1 is final, then c3 would have to be equal to c1
                        !cls::has_ancestor(&c1_def, c2)
                    } else if cls::final_(&c2_def) {
                        // if c2 is final, then c3 would have to be equal to c2
                        !cls::has_ancestor(&c2_def, c1)
                    } else {
                        // Given two non-final classes, if either is an interface or trait, then
                        // there could be a c3, and so we consider the classes to not be disjoint.
                        // However, if they are both classes, then c3 must be either c1 or c2 since
                        // we don't have multiple inheritance.
                        (!is_interface_or_trait(&c1_def))
                            && (!is_interface_or_trait(&c2_def))
                            && (!cls::has_ancestor(&c2_def, c1))
                            && !cls::has_ancestor(&c1_def, c2)
                    }
                }
                _ => {
                    // This is a decl error that should have already been caught
                    false
                }
            }
        }
    }

    /// [negate_ak_null_type env r ty] performs type negation similar to
    /// TUtils.negate_type, but restricted to arraykey and null (and their
    /// negations).
    pub fn negate_ak_null_type(env: &mut Env, r: Reason, ty: Ty) -> Option<Ty> {
        let ty = env::expand_type(env, ty);
        let neg_ty = match get_node(&ty) {
            Ty_::Tprim(Tprim::Tnull) => Some(make_type::nonnull(r)),
            Ty_::Tprim(Tprim::Tarraykey) => Some(make_type::neg(
                r.clone(),
                TypePredicate(r, TypePredicate_::IsTag(TypeTag::ArraykeyTag)),
            )),
            Ty_::Tneg(TypePredicate(r, TypePredicate_::IsTag(TypeTag::ArraykeyTag))) => {
                Some(make_type::prim_type(r.clone(), Tprim::Tarraykey))
            }
            Ty_::Tneg(TypePredicate(r, TypePredicate_::IsTag(TypeTag::NullTag))) => {
                Some(make_type::null(r.clone()))
            }
            Ty_::Tnonnull => Some(make_type::null(r)),
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ClassTag(id, _))))
                if C_STRING != id =>
            {
                None
            }
            Ty_::Tneg(predicate) => {
                // negate_ak_null_type is ultimately used in simplifcations of the form
                //   A & !B <: C iff A <: C | B
                // However, if we overapproximate (C | B) which we do for shape unions,
                // this transform is unsound.
                // For this reason, we exclude predicates containing IsShapeOf from this
                // calculus.
                // Another (better) solution would be to add a flag to Typing_union
                // functions forbidding overapproximation.
                // We also overapproximate unions of tuples, but I don't think we can
                // contrive/observe the same unsoundness since we atomicize tuples
                // during type splitting
                fn has_isshape(predicate: &TypePredicate) -> bool {
                    let TypePredicate(_, predicate_) = predicate;
                    match predicate_ {
                        TypePredicate_::IsTag(_) => false,
                        TypePredicate_::IsUnionOf(preds)
                        | TypePredicate_::IsTupleOf(typing_defs_core::TuplePredicate {
                            required: preds,
                        }) => preds.iter().any(has_isshape),
                        TypePredicate_::IsShapeOf(_) => true,
                        TypePredicate_::IsNot(inner) => has_isshape(inner),
                    }
                }
                if has_isshape(predicate) {
                    None
                } else {
                    typing_refinement::ty_predicate::to_ty_without_instantiation_opt(env, predicate)
                }
            }
            _ => None,
        };
        neg_ty
    }

    /// False only if `negate_ak_null_type` is `None` for `ty`, whatever the
    /// environment: a type that is not a type variable, `null`, `arraykey`,
    /// `nonnull` or a negation (`expand_type` gives it back as it is, without
    /// changing the environment, and no other arm applies to it).
    fn may_have_exact_negation(ty: &Ty) -> bool {
        matches!(
            get_node(ty),
            Ty_::Tvar(_)
                | Ty_::Tprim(Tprim::Tnull | Tprim::Tarraykey)
                | Ty_::Tnonnull
                | Ty_::Tneg(_)
        )
    }

    /// What the callers of `find_type_with_exact_negation` do with it, for an
    /// intersection on the left: `Some (non_ty, tyl)` with the environment
    /// the search returns, or `None` with the environment as it was before
    /// the search (the OCaml matches the second case without binding the
    /// environment of the search). Not in the OCaml: when no element can
    /// have an exact negation, the answer is `None` without searching (and so
    /// without copying the environment and the list).
    pub fn find_type_with_exact_negation_opt(env: &mut Env, tyl: &[Ty]) -> Option<(Ty, Vec<Ty>)> {
        if !tyl.iter().any(may_have_exact_negation) {
            return None;
        }
        let env_before = env.clone();
        match find_type_with_exact_negation(env, tyl.to_vec()) {
            (Some(non_ty), tyl) => Some((non_ty, tyl)),
            (None, _) => {
                *env = env_before;
                None
            }
        }
    }

    /// Whether `find_type_with_exact_negation` finds a type, in a copy of the
    /// environment (which is dropped).
    pub fn has_type_with_exact_negation(env: &Env, tyl: &[Ty]) -> bool {
        tyl.iter().any(may_have_exact_negation)
            && find_type_with_exact_negation(&mut env.clone(), tyl.to_vec()).0.is_some()
    }

    /// The OCaml returns `(env, neg_ty, tyl)`.
    pub fn find_type_with_exact_negation(env: &mut Env, tyl: Vec<Ty>) -> (Option<Ty>, Vec<Ty>) {
        // Prefer to negate [Tneg _] components first. Negating a [Tneg P]
        // gives the predicate-as-type [P]; the resulting union [C | P] is much
        // more useful for closing out the subtype check than the [C | Tneg X]
        // we'd get from negating, e.g., an [arraykey] component.

        // `acc_tyl` is the OCaml list, which is built by adding at its head:
        // here at the end of the vector, which is reversed when it is
        // returned.
        fn find(env: &mut Env, tyl: Vec<Ty>, mut acc_tyl: Vec<Ty>) -> (Option<Ty>, Vec<Ty>) {
            let mut tyl = tyl.into_iter();
            loop {
                match tyl.next() {
                    None => {
                        acc_tyl.reverse();
                        return (None, acc_tyl);
                    }
                    Some(ty) => {
                        let neg_ty = negate_ak_null_type(env, get_reason(&ty).clone(), ty.clone());
                        match neg_ty {
                            None => acc_tyl.push(ty),
                            Some(neg_ty) => {
                                // `tyl' @ acc_tyl`
                                acc_tyl.reverse();
                                let mut res: Vec<Ty> = tyl.collect();
                                res.extend(acc_tyl);
                                return (Some(neg_ty), res);
                            }
                        }
                    }
                }
            }
        }
        let (tneg_tys, other_tys): (Vec<Ty>, Vec<Ty>) =
            tyl.into_iter().partition(typing_defs::is_neg);
        let mut tys = tneg_tys;
        tys.extend(other_tys);
        find(env, tys, vec![])
    }
}

/// `ty_equal ty (MakeType.mixed _)`: `ty_compare` ignores reasons and
/// compares nodes of different constructors as different, so the type equal to
/// `?nonnull` is `?nonnull`.
pub fn is_mixed_node(ty: &Ty) -> bool {
    matches!(get_node(ty), Ty_::Toption(inner) if matches!(get_node(inner), Ty_::Tnonnull))
}

pub fn get_tyvar_opt(t: &InternalType) -> Option<tvid::T> {
    match t {
        InternalType::LoclType(lt) => match get_node(lt) {
            Ty_::Tvar(var) => Some(*var),
            _ => None,
        },
        _ => None,
    }
}

/// build the interface corresponding to the can_traverse constraint
pub fn can_traverse_to_iface(ct: &CanTraverse) -> Ty {
    match (&ct.key, ct.is_await) {
        (None, false) => make_type::traversable(ct.reason.clone(), ct.val.clone()),
        (None, true) => make_type::async_iterator(ct.reason.clone(), ct.val.clone()),
        (Some(ct_key), false) => {
            make_type::keyed_traversable(ct.reason.clone(), ct_key.clone(), ct.val.clone())
        }
        (Some(ct_key), true) => {
            make_type::async_keyed_iterator(ct.reason.clone(), ct_key.clone(), ct.val.clone())
        }
    }
}

/// `module Sd`
pub mod sd {
    use super::*;

    pub fn liken(super_like: bool, env: &Env, ty: Ty) -> Ty {
        if super_like {
            t_utils::make_like(None, env, ty)
        } else {
            ty
        }
    }

    /// At present, we don't distinguish between coercions (<:D) and subtyping (<:) in the
    /// type variable and type parameter environments. When closing the environment we use subtyping (<:).
    /// To mitigate against this, when adding a dynamic upper bound wrt coercion,
    /// transform it first into supportdyn<mixed>,
    /// as t <:D dynamic iff t <: supportdyn<mixed>.
    pub fn transform_dynamic_upper_bound(is_dynamic_aware: bool, env: &Env, ty: Ty) -> Ty {
        if tast::is_under_dynamic_assumptions(env.checked) {
            ty
        } else {
            match (is_dynamic_aware, get_node(&ty)) {
                (true, Ty_::Tdynamic(_)) => {
                    let r = get_reason(&ty).clone();
                    make_type::supportdyn_mixed(r)
                }
                (true, _) => ty,
                _ => ty,
            }
        }
    }
}

pub fn mk_issubtype_prop(
    sub_supportdyn: Option<&Reason>,
    is_dynamic_aware: bool,
    env: &mut Env,
    ty1: InternalType,
    ty2: InternalType,
) -> tl::SubtypeProp {
    let ty1 = match sub_supportdyn {
        None => ty1,
        Some(r) => {
            let ty1 = env::expand_internal_type(env, ty1);
            match ty1 {
                InternalType::LoclType(ty) => {
                    if typing_defs::is_tyvar(&ty) {
                        InternalType::LoclType(ty)
                    } else {
                        let ty = make_type::supportdyn(r.clone(), ty);
                        InternalType::LoclType(ty)
                    }
                }
                _ => ty1,
            }
        }
    };
    match ty2 {
        InternalType::LoclType(ty2) => {
            // TODO akenn: somehow we lose this environment
            let (is_dynamic_aware, ty2) =
                // If we are in dynamic-aware subtyping mode, that fact will be lost when ty2
                // ends up on the upper bound of a type variable. Here we find if ty2 contains
                // dynamic and replace it with supportdyn<mixed> which is equivalent, but does not
                // require dynamic-aware subtyping mode to be a supertype of types that support dynamic.
                match is_dynamic_aware {
                    true => {
                        let ty_opt =
                            typing_dynamic_utils::try_strip_dynamic(None, Some(true), env, &ty2);
                        match ty_opt {
                            Some(non_dyn_ty) => {
                                let r = get_reason(&ty2).clone();
                                (
                                    false,
                                    make_type::union(
                                        r.clone(),
                                        vec![non_dyn_ty, make_type::supportdyn_mixed(r)],
                                    ),
                                )
                            }
                            None => (is_dynamic_aware, ty2),
                        }
                    }
                    _ => (is_dynamic_aware, ty2),
                };
            tl::SubtypeProp::IsSubtype(is_dynamic_aware, ty1, InternalType::LoclType(ty2))
        }
        _ => tl::SubtypeProp::IsSubtype(is_dynamic_aware, ty1, ty2),
    }
}

/// All of our constraints have a type with additional context to support <:D
///
/// The OCaml record holds pointers to the reason and the type; here it
/// borrows them (`Copy`), so that building one for each step of subtyping
/// changes no reference counts: a type that is built for the step is bound
/// first and borrowed (`&mk(..)` in an argument lives until the call
/// returns).
#[derive(Clone, Copy, Debug)]
pub struct Lhs<'a> {
    pub sub_supportdyn: Option<&'a Reason>,
    pub ty_sub: &'a Ty,
}

/// Just some shorthand
pub fn should_cls_sub_cn(env: &Env) -> bool {
    env.genv.tcopt.class_sub_classname
}

/// Find the first generic occurring in [ty] with a rank higher than [rank]
pub fn check_rank(env: &Env, ty: &Ty, rank: isize) -> Option<(Reason, Option<String>)> {
    // To avoid this potentially expensive check we record when the sub- or
    // supertype _may_ contain a higher rank type parameter.
    if typing_env_types::should_check_rank(env) {
        let p = |ty: &Ty| match get_node(ty) {
            Ty_::Tgeneric(name) => env::rank_of_tparam(env, name) > rank,
            Ty_::Tvar(tv) => env::rank_of_tvar(env, *tv) > rank,
            _ => false,
        };
        let ty_opt = typing_defs_core::find_locl_ty(ty, &p);
        ty_opt.map(|ty| match deref(&ty) {
            (r, Ty_::Tgeneric(name)) => (r, Some(name)),
            (r, Ty_::Tvar(_)) => (r, None),
            _ => {
                // We are guaranteed that if the result if [Some(...)] then the type
                // is a [Tgeneric] so something is seriously wrong here
                panic!("check_rank: unexpected type")
            }
        })
    } else {
        None
    }
}

/// `module type Constraint_handler`: the modules of the recursive group that
/// handle a kind of constraint (`Subtype`, `Can_index`, `Has_member`, ...)
/// each have a function `simplify` of this signature, with their own `rhs`.
/// They are modules, not types: this trait states the signature and is not
/// implemented.
pub trait ConstraintHandler {
    type Rhs;

    fn simplify(
        subtype_env: &subtype_env::T,
        this_ty: Option<&Ty>,
        lhs: Lhs,
        rhs: Self::Rhs,
        env: &mut Env,
    ) -> tl::SubtypeProp;
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::mk;

    fn prim(p: Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    #[test]
    fn is_tprim_disjoint_() {
        use subtype_negation::is_tprim_disjoint;
        assert!(!is_tprim_disjoint(Tprim::Tint, Tprim::Tint));
        // Overlapping primitives, in both orders
        for (tp1, tp2) in [
            (Tprim::Tnum, Tprim::Tint),
            (Tprim::Tnum, Tprim::Tfloat),
            (Tprim::Tarraykey, Tprim::Tint),
            (Tprim::Tarraykey, Tprim::Tnum),
        ] {
            assert!(!is_tprim_disjoint(tp1, tp2));
            assert!(!is_tprim_disjoint(tp2, tp1));
        }
        assert!(is_tprim_disjoint(Tprim::Tint, Tprim::Tfloat));
        assert!(is_tprim_disjoint(Tprim::Tfloat, Tprim::Tarraykey));
        assert!(is_tprim_disjoint(Tprim::Tnull, Tprim::Tvoid));
    }

    #[test]
    fn visited_goals_() {
        let v = visited_goals::empty();
        let v = visited_goals::try_add_visited_generic_sub(&v, "T", prim(Tprim::Tint)).unwrap();
        // `T <: int` again
        assert!(visited_goals::try_add_visited_generic_sub(&v, "T", prim(Tprim::Tint)).is_none());
        // `int <: T` is another goal
        let v = visited_goals::try_add_visited_generic_super(&v, prim(Tprim::Tint), "T").unwrap();
        assert!(visited_goals::try_add_visited_generic_super(&v, prim(Tprim::Tint), "T").is_none());
        assert!(visited_goals::try_add_visited_generic_sub(&v, "T", prim(Tprim::Tint)).is_none());
        // Other parameters and other types are other goals
        assert!(visited_goals::try_add_visited_generic_sub(&v, "U", prim(Tprim::Tint)).is_some());
        assert!(visited_goals::try_add_visited_generic_sub(&v, "T", prim(Tprim::Tfloat)).is_some());
        // Types are compared without their reasons
        let int = mk((
            reason::witness_from_decl(PosOrDecl::NONE),
            Ty_::Tprim(Tprim::Tint),
        ));
        assert!(visited_goals::try_add_visited_generic_sub(&v, "T", int).is_none());
    }

    #[test]
    fn resolve_tparam_constraints_() {
        use subtype_env::TparamConstraintCandidate;
        let cstr = |name: &str| {
            reason::cstr_on_generics((PosOrDecl::NONE, (PosOrDecl::NONE, name.to_string())))
        };
        let c = |sub: Reason, super_: Reason| TparamConstraintCandidate {
            sub,
            super_,
            witness: None,
        };
        // The most recent candidate first, as in the OCaml list.
        let candidates = vec![
            // the supertype's constraint is preferred
            c(cstr("U"), cstr("T")),
            c(reason::none(), reason::none()),
            c(cstr("U"), reason::none()),
            // the same as the one before: dropped
            c(cstr("T"), reason::none()),
            c(reason::none(), cstr("T")),
        ];
        let names: Vec<String> = subtype_env::resolve_tparam_constraints(&candidates)
            .into_iter()
            .map(|(_, (_, name))| name)
            .collect();
        assert_eq!(names, vec!["T", "U", "T"]);
        assert!(subtype_env::resolve_tparam_constraints(&[]).is_empty());
    }

    #[test]
    fn possibly_add_violated_constraint_() {
        use subtype_env::TparamConstraintCandidate;
        let cstr = |name: &str| {
            reason::cstr_on_generics((PosOrDecl::NONE, (PosOrDecl::NONE, name.to_string())))
        };
        let names = |candidates: &[TparamConstraintCandidate]| -> Vec<String> {
            subtype_env::resolve_tparam_constraints(candidates)
                .into_iter()
                .map(|(_, (_, name))| name)
                .collect()
        };
        let t_cstr = cstr("T");
        // Pairs in the order they are added.
        let pairs = vec![
            (reason::none(), cstr("T")),
            (reason::none(), reason::none()),
            (t_cstr.clone(), reason::none()),
            (reason::flow_local(t_cstr.clone(), reason::none()), reason::none()),
            (cstr("U"), cstr("T")),
            (cstr("U"), reason::none()),
            (reason::none(), reason::none()),
            (cstr("U"), reason::none()),
            (cstr("T"), reason::none()),
        ];
        let mut t = subtype_env::create(
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            false,
            2,
            Some(crate::typing_error::reasons_callback::unify_error_at(
                oxidized::pos::Pos::NONE,
            )),
        );
        let mut all = vec![];
        for (r_sub, r_super) in pairs {
            t = subtype_env::possibly_add_violated_constraint(t, r_sub.clone(), r_super.clone());
            all.insert(0, TparamConstraintCandidate {
                sub: r_sub,
                super_: r_super,
                witness: None,
            });
        }
        let kept: Vec<TparamConstraintCandidate> =
            t.tparam_constraint_candidates.iter().cloned().collect();
        // What the OCaml keeps (every pair) and what is kept resolve the same.
        assert_eq!(names(&kept), names(&all));
        assert_eq!(names(&kept), vec!["T", "U", "T"]);
        assert_eq!(kept.len(), 3);
    }
}
