// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 10517-11226): module `Common`.
//! See `hh/PORTING.md`.
//!
//! # Signatures
//!
//! The arguments are in the order of the OCaml signature, the environment
//! last:
//!
//! - `~subtype_env` is `&subtype_env::T`, `~this_ty` is `Option<&Ty>`,
//!   `~fail` is `Option<typing_error::T>` by value.
//! - `~mk_prop` is `impl Fn(&subtype_env::T, Option<&Ty>, Lhs, R,
//!   &mut Env) -> tl::SubtypeProp` (the shape of the `simplify` of every
//!   constraint handler, so that `simplify` itself can be passed), where `R`
//!   is the `'rhs` of the OCaml. [`simplify_newtype_l`] and
//!   [`simplify_dependent_l`] call it once and return what it returns (the
//!   OCaml `'res`): there it is `impl FnOnce(..) -> Res`.
//! - `~update_reason` is `impl Fn(&Env, Ty) -> Ty`, `~lift_rhs` is
//!   `impl Fn(R) -> ConstraintType`.
//! - The tuples are passed by value, with `sub_supportdyn` borrowed (as in
//!   [`Lhs`]): `(Option<&Reason>, &[Ty])` for `simplify_union_l` and
//!   `simplify_intersection_l`, `(Option<&Reason>, Reason, String)` for
//!   `simplify_generic_l`, `(Option<&Reason>, Reason, String, Ty)` for
//!   `simplify_newtype_l`, `(Option<&Reason>, Reason, DependentType, Ty)`
//!   for `simplify_dependent_l`, and `(Option<&Reason>, &Ty)` and `(Reason,
//!   subtype::Rhs, R)` for `simplify_disj_r`.
//!
//! The `rhs` of the other constraint handlers, which [`dispatch_constraint`]
//! builds, are named as the rules give them: `destructure::Rhs {
//! reason_super, destructure }`, `can_index::Rhs { reason_super, can_index }`,
//! `can_index_assign::Rhs { reason_super, can_index_assign }`.

use naming_special_names_rust as sn;
use oxidized::pos::Pos;

/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::typing_defs;
use crate::typing_defs::dependent_kind;
use crate::typing_defs_constraints;
use crate::typing_defs_constraints::ConstraintType;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_core::DependentType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::secondary;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::if_unsat;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::or;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;
use crate::typing_subtype::can_index;
use crate::typing_subtype::can_index_assign;
use crate::typing_subtype::can_traverse;
use crate::typing_subtype::destructure;
use crate::typing_subtype::has_const;
use crate::typing_subtype::has_member;
use crate::typing_subtype::has_type_member;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_subtype::type_switch;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// Helper function which returns true if a type is dynamic or a (nested)
/// intersection of types where any type in the intersection is dynamic. Used
/// to delay generation disjunctions in the c-union-l case.
pub fn contains_dynamic_through_intersection(ty: &Ty) -> bool {
    typing_defs::is_dynamic(ty)
        || match get_node(ty) {
            Ty_::Tintersection(tyl) => tyl.iter().any(contains_dynamic_through_intersection),
            _ => false,
        }
}

pub fn simplify_union_l<R: Clone>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    mk_prop: impl Fn(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> tl::SubtypeProp,
    update_reason: impl Fn(&Env, Ty) -> Ty,
    (sub_supportdyn, ty_subs): (Option<&Reason>, &[Ty]),
    rhs: R,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `f` gives `update_reason` the environment that `simplify_union_l` is
    // given (the folds thread theirs in `res`). Here it is given the current
    // one: every `update_reason` passed here is `Env.update_reason`, which
    // does not look at the environment (keeping a copy of it would make the
    // first write in the loop copy the environment).
    let f = |env: &mut Env, res: tl::SubtypeProp, ty_sub: Ty| {
        let ty_sub = update_reason(env, ty_sub);
        and(env, res, |env| {
            mk_prop(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                rhs.clone(),
                env,
            )
        })
    };
    // Prioritize types that aren't dynamic or intersections with dynamic
    // to get better error messages
    let (last_tyl, first_tyl) =
        typing_dynamic_utils::partition_union(&contains_dynamic_through_intersection, env, ty_subs);
    let mut init = tl::valid();
    for ty_sub in first_tyl {
        init = f(env, init, ty_sub);
    }
    let mut res = init;
    for ty_sub in last_tyl {
        res = f(env, res, ty_sub);
    }
    res
}

/// It's sound to reduce t1 & t2 <: t to (t1 <: t) || (t2 <: t), but
/// not complete.
/// TODO(T120921930): Don't do this if require_completeness is set.
#[allow(clippy::too_many_arguments)]
pub fn simplify_intersection_l<R: Clone>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    fail: subtype_env::Fail,
    mk_prop: impl Fn(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> tl::SubtypeProp,
    update_reason: impl Fn(&Env, Ty) -> Ty,
    (sub_supportdyn, tys_sub): (Option<&Reason>, &[Ty]),
    rhs: R,
    env: &mut Env,
) -> tl::SubtypeProp {
    // If we have an intersection containing a type variable e.g. #0 & dict<string,mixed>
    // and the type variable has a supportdyn or dynamic upper bound, then it's sound (and desirable)
    // to preserve supportdyn when making incomplete simplification of the intersection. In this
    // case we add supportdyn to the other conjuncts to preserve the "supports dynamic" property.
    //
    // `is_dynamic_or_supportdyn` and `add_supportdyn` expand in the
    // environment given to `simplify_intersection_l` and drop the
    // environment the expansion returns: they expand in a copy.
    fn is_dynamic_or_supportdyn(env: &Env, ty: &Ty) -> bool {
        // (`expand_type` gives back any other type than a type variable.)
        let expanded;
        let ty = match get_node(ty) {
            Ty_::Tvar(_) => {
                expanded = env::expand_type(&mut env.clone(), ty.clone());
                &expanded
            }
            _ => ty,
        };
        match get_node(ty) {
            Ty_::Tnewtype(name_sub, tyl, _)
                if tyl.len() == 1 && name_sub == sn::classes::SUPPORT_DYN =>
            {
                true
            }
            Ty_::Tdynamic(_) | Ty_::Tprim(_) => true,
            Ty_::Tclass((_, id), _, _) if C_STRING == id => true,
            Ty_::Toption(ty) => is_dynamic_or_supportdyn(env, ty),
            Ty_::Tunion(tyl) => tyl.iter().all(|ty| is_dynamic_or_supportdyn(env, ty)),
            Ty_::Tintersection(tyl) => tyl.iter().any(|ty| is_dynamic_or_supportdyn(env, ty)),
            _ => false,
        }
    }
    let add_supportdyn = {
        let env: &Env = env;
        tys_sub.iter().any(|ty_sub| {
            // (Only a type variable can expand to one.)
            if !matches!(get_node(ty_sub), Ty_::Tvar(_)) {
                return false;
            }
            let ty_sub = env::expand_type(&mut env.clone(), ty_sub.clone());
            match get_node(&ty_sub) {
                Ty_::Tvar(v) => {
                    let upper_bounds = env::get_tyvar_upper_bounds(env, *v);
                    ity_set::exists(
                        |ity| match ity {
                            InternalType::LoclType(ty) => is_dynamic_or_supportdyn(env, ty),
                            _ => false,
                        },
                        &upper_bounds,
                    )
                }
                _ => false,
            }
        })
    };
    // `aux tys_sub ~env ~errs:[fail] ~props:[]`, as a loop. `errs` and
    // `props` are the OCaml lists, which `aux` builds by adding at their
    // head: here at the end of the vectors, which are reversed at the end.
    // (`fail` is the first error of the list, the last of the vector once
    // reversed; it is added only when the disjunction is built, so that it is
    // not built when a conjunct is valid: see `subtype_env::fail_deferred`.
    // The vector is not allocated until a conjunct fails. The OCaml's `fail`
    // is already built; building the error of a failing step is the costly
    // part and almost all of them are dropped: 2.8M built, 212 reported on
    // the benchmark sample.)
    let mut errs: Vec<Option<typing_error::T>> = Vec::new();
    let mut props: Vec<tl::SubtypeProp> = vec![];
    for ty_sub in tys_sub {
        let ty_sub = update_reason(env, ty_sub.clone());
        let ty_sub = if add_supportdyn {
            t_utils::make_supportdyn(get_reason(&ty_sub).clone(), env, ty_sub)
        } else {
            ty_sub
        };
        let prop = mk_prop(
            subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            rhs.clone(),
            env,
        );
        if tl::is_valid(&prop) {
            return prop;
        } else {
            match tl::get_error_if_unsat(&prop) {
                Some(err) => errs.push(err),
                _ => props.push(prop),
            }
        }
    }
    errs.reverse();
    errs.push(fail.get());
    props.reverse();
    tl::SubtypeProp::Disj(
        typing_error::intersect_opt(errs.into_iter().flatten().collect()),
        props,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn simplify_generic_l<R: Clone>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    fail: subtype_env::Fail,
    mk_prop: impl Fn(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> tl::SubtypeProp,
    (sub_supportdyn, reason_generic, generic_nm): (Option<&Reason>, Reason, String),
    rhs: R,
    rhs_for_mixed: R,
    env: &mut Env,
) -> tl::SubtypeProp {
    let lty_sub = mk((reason_generic.clone(), Ty_::Tgeneric(generic_nm.clone())));
    let prop = {
        // If the generic is actually an expression dependent type,
        // we need to update this_ty
        let this_ty = if dependent_kind::is_generic_dep_ty(&generic_nm) && this_ty.is_none() {
            Some(&lty_sub)
        } else {
            this_ty
        };

        // Otherwise, we collect all the upper bounds ("as" constraints) on
        // the generic parameter, and check each of these in turn against
        // ty_super until one of them succeeds
        //
        // `errs` and `props` are the OCaml lists, built by adding at their
        // head: here at the end of the vectors, so that `List.rev errs` and
        // `List.rev props` are the vectors as they are.
        type Accumulated = (Vec<Option<typing_error::T>>, Vec<tl::SubtypeProp>);
        let accumulate = |prop: tl::SubtypeProp,
                          mut errs: Vec<Option<typing_error::T>>,
                          mut props: Vec<tl::SubtypeProp>|
         -> Result<tl::SubtypeProp, Accumulated> {
            if tl::is_valid(&prop) {
                Ok(prop)
            } else {
                match tl::get_error_if_unsat(&prop) {
                    Some(err) => {
                        errs.push(err);
                        Err((errs, props))
                    }
                    None => {
                        props.push(prop);
                        Err((errs, props))
                    }
                }
            }
        };
        // `aux`, as a loop.
        let aux = |upper_bounds: Vec<Ty>,
                   env: &mut Env,
                   mut errs: Vec<Option<typing_error::T>>,
                   mut props: Vec<tl::SubtypeProp>|
         -> tl::SubtypeProp {
            for upper_bound in upper_bounds {
                let ty_sub = env::update_reason(env, upper_bound, |bound| {
                    reason::axiom_upper_bound(bound, reason_generic.clone(), generic_nm.clone())
                });
                let prop = mk_prop(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    rhs.clone(),
                    env,
                );
                match accumulate(prop, errs, props) {
                    Ok(prop) => return prop,
                    Err((errs_, props_)) => {
                        errs = errs_;
                        props = props_;
                    }
                }
            }
            // (`fail`, the first error: see the call of `aux`. The OCaml's
            // `aux ~errs:[fail]` starts from the built error; here it is
            // built only now that the disjunction is needed, as in
            // `simplify_union_l`.)
            errs[0] = fail.get();
            let err = typing_error::intersect_opt(errs.into_iter().flatten().collect());
            tl::SubtypeProp::Disj(err, props)
        };

        let upper_bounds = typing_set::elements(&env::get_upper_bounds(env, &generic_nm));
        // TODO(mjt) We reverse bounds here to match the evaluation order
        // of older code; not doing so triggers errors due to incompleteness
        let mut upper_bounds = upper_bounds;
        upper_bounds.reverse();
        match upper_bounds.as_slice() {
            [] => {
                // Try an implicit mixed = ?nonnull bound before giving up.
                // This can be useful when checking T <: t, where type t is
                // equivalent to but syntactically different from ?nonnull.
                // E.g., if t is a generic type parameter T with nonnull as
                // a lower bound.
                let r = reason::implicit_upper_bound((get_pos(&lty_sub), "mixed".to_string()));
                let tmixed = make_type::mixed(r);
                let ty_sub = env::update_reason(env, tmixed, |bound| {
                    reason::axiom_upper_bound(bound, reason_generic.clone(), generic_nm.clone())
                });
                let prop = mk_prop(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    rhs_for_mixed,
                    env,
                );
                if tl::is_valid(&prop) {
                    prop
                } else {
                    let (err, props) = match tl::get_error_if_unsat(&prop) {
                        Some(err) => (
                            typing_error::intersect_opt(
                                vec![fail.get(), err].into_iter().flatten().collect(),
                            ),
                            vec![],
                        ),
                        _ => (fail.get(), vec![prop]),
                    };
                    tl::SubtypeProp::Disj(err, props)
                }
            }
            // (`[fail]`: `fail` is put first when the disjunction is built, so
            // that it is not built when a bound gives a valid proposition.)
            _ => aux(upper_bounds, env, vec![None], vec![]),
        }
    };
    prop
}

pub fn simplify_newtype_l<R, Res>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    mk_prop: impl FnOnce(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> Res,
    (sub_supportdyn, reason_newtype, newtype_nm, newtype_ty): (Option<&Reason>, Reason, String, Ty),
    rhs: R,
    env: &mut Env,
) -> Res {
    let sub_supportdyn = match sub_supportdyn {
        None => {
            if newtype_nm == sn::classes::SUPPORT_DYN {
                Some(&reason_newtype)
            } else {
                None
            }
        }
        _ => sub_supportdyn,
    };
    let ty_sub = env::update_reason(env, newtype_ty, |bound| {
        reason::axiom_upper_bound(bound, reason_newtype.clone(), newtype_nm)
    });

    mk_prop(
        subtype_env,
        this_ty,
        Lhs {
            sub_supportdyn,
            ty_sub: &ty_sub,
        },
        rhs,
        env,
    )
}

pub fn simplify_dependent_l<R, Res>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    mk_prop: impl FnOnce(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> Res,
    (sub_supportdyn, reason_dep, dep_ty, ty_inner_sub): (Option<&Reason>, Reason, DependentType, Ty),
    rhs: R,
    env: &mut Env,
) -> Res {
    let dependent_ty = mk((reason_dep, Ty_::Tdependent(dep_ty, ty_inner_sub.clone())));
    // `Option.first_some this_ty (Some ...)`
    let this_ty = this_ty.or(Some(&dependent_ty));
    let lhs = Lhs {
        sub_supportdyn,
        ty_sub: &ty_inner_sub,
    };

    mk_prop(subtype_env, this_ty, lhs, rhs, env)
}

/// `let rec simplify_disj_r`. The recursion, which passes `mk_prop` and
/// `lift_rhs` on to itself through closures, is made with them as trait
/// objects (an `impl Fn` would make a new type at each level).
#[allow(clippy::too_many_arguments)]
pub fn simplify_disj_r<R: Clone>(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    fail: Option<typing_error::T>,
    mk_prop: impl Fn(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> tl::SubtypeProp,
    lift_rhs: impl Fn(R) -> ConstraintType,
    lhs: (Option<&Reason>, &Ty),
    rhs: (Reason, subtype::Rhs, R),
    env: &mut Env,
) -> tl::SubtypeProp {
    #[allow(clippy::too_many_arguments)]
    fn simplify_disj_r_inner<R: Clone>(
        subtype_env: &subtype_env::T,
        this_ty: Option<&Ty>,
        fail: Option<typing_error::T>,
        mk_prop: &dyn Fn(&subtype_env::T, Option<&Ty>, Lhs, R, &mut Env) -> tl::SubtypeProp,
        lift_rhs: &dyn Fn(R) -> ConstraintType,
        (sub_supportdyn, ty_sub): (Option<&Reason>, &Ty),
        rhs: (Reason, subtype::Rhs, R),
        env: &mut Env,
    ) -> tl::SubtypeProp {
        // `((reason_super, rhs_subtype, rhs_other) as rhs)`: the components are
        // taken apart in the cases that use them.
        let ty_sub = &env::expand_type(env, ty_sub.clone());

        match get_node(&ty_sub) {
            Ty_::Toption(ty) => {
                let r = get_reason(&ty_sub).clone();
                let ty_null = make_type::null(r.clone());
                let ty = env::update_reason(env, ty.clone(), |r_sub_prj| {
                    reason::prj_nullable_sub(r, r_sub_prj)
                });
                let prop = |env: &mut Env| {
                    let p = simplify_disj_r_inner(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        lift_rhs,
                        (sub_supportdyn, &ty_null),
                        rhs.clone(),
                        env,
                    );
                    and(env, p, |env| {
                        simplify_disj_r_inner(
                            subtype_env,
                            this_ty,
                            fail.clone(),
                            mk_prop,
                            lift_rhs,
                            (sub_supportdyn, &ty),
                            rhs,
                            env,
                        )
                    })
                };
                let p = prop(env);
                if_unsat(|env| invalid(fail, env), env, p)
            }
            Ty_::Tintersection(ty_subs) => {
                let r_sub = get_reason(&ty_sub).clone();
                let mk_prop_intersection = |subtype_env: &subtype_env::T,
                                            this_ty: Option<&Ty>,
                                            Lhs {
                                                sub_supportdyn,
                                                ty_sub,
                                            }: Lhs,
                                            rhs: (Reason, subtype::Rhs, R),
                                            env: &mut Env| {
                    simplify_disj_r_inner(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        lift_rhs,
                        (sub_supportdyn, ty_sub),
                        rhs,
                        env,
                    )
                };
                simplify_intersection_l(
                    subtype_env,
                    this_ty,
                    fail.clone().into(),
                    mk_prop_intersection,
                    |env: &Env, ty: Ty| {
                        env::update_reason(env, ty, |r_sub_prj| {
                            reason::prj_inter_sub(r_sub.clone(), r_sub_prj)
                        })
                    },
                    (sub_supportdyn, ty_subs),
                    rhs,
                    env,
                )
            }
            Ty_::Tunion(ty_subs) => {
                let r_sub = get_reason(&ty_sub).clone();
                let mk_prop_union = |subtype_env: &subtype_env::T,
                                     this_ty: Option<&Ty>,
                                     Lhs {
                                         sub_supportdyn,
                                         ty_sub,
                                     }: Lhs,
                                     rhs: (Reason, subtype::Rhs, R),
                                     env: &mut Env| {
                    simplify_disj_r_inner(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        lift_rhs,
                        (sub_supportdyn, ty_sub),
                        rhs,
                        env,
                    )
                };
                simplify_union_l(
                    subtype_env,
                    this_ty,
                    mk_prop_union,
                    |env: &Env, ty: Ty| {
                        env::update_reason(env, ty, |r_sub_prj| {
                            reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                        })
                    },
                    (sub_supportdyn, ty_subs),
                    rhs,
                    env,
                )
            }
            Ty_::Tvar(_) => {
                let (reason_super, rhs_subtype, rhs_other) = rhs;
                let ty_fresh = env::fresh_type(env, Pos::NONE);
                let mk_cstr_prop = |env: &mut Env| {
                    mk_prop(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &ty_fresh,
                        },
                        rhs_other,
                        env,
                    )
                };
                let mk_subty_prop = |env: &mut Env| {
                    subtype::simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub,
                        },
                        subtype::Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &make_type::union(
                                reason_super,
                                vec![rhs_subtype.ty_super.clone(), ty_fresh.clone()],
                            ),
                        },
                        env,
                    )
                };
                let p = mk_subty_prop(env);
                and(env, p, mk_cstr_prop)
            }
            Ty_::Tgeneric(nm) => {
                let r_generic = get_reason(&ty_sub).clone();
                let rhs_subtype = &rhs.1;
                match get_node(&rhs_subtype.ty_super) {
                    // Before using the upper bounds of the generic in a call to
                    // [simplify_generic_l] we need to check if the super type is a type
                    // variable and, if so, ensure the two have compatible ranks
                    Ty_::Tvar(tv_sup)
                        if env::rank_of_tparam(env, nm) > env::rank_of_tvar(env, *tv_sup) =>
                    {
                        let r_super = get_reason(&rhs_subtype.ty_super);
                        let error = secondary::T::HigherRankTparamEscape {
                            tvar_pos: reason::to_pos(r_super),
                            pos_with_generic: reason::to_pos(&r_generic),
                            generic_reason: r_generic.clone(),
                            generic_name: Some(nm.clone()),
                        };
                        let fail = subtype_env::fail_with_secondary_error(subtype_env, error);
                        invalid(fail, env)
                    }
                    _ => {
                        let mk_prop_generic = |subtype_env: &subtype_env::T,
                                               this_ty: Option<&Ty>,
                                               Lhs {
                                                   sub_supportdyn,
                                                   ty_sub,
                                               }: Lhs,
                                               rhs: (Reason, subtype::Rhs, R),
                                               env: &mut Env| {
                            simplify_disj_r_inner(
                                subtype_env,
                                this_ty,
                                fail.clone(),
                                mk_prop,
                                lift_rhs,
                                (sub_supportdyn, ty_sub),
                                rhs,
                                env,
                            )
                        };
                        simplify_generic_l(
                            subtype_env,
                            this_ty,
                            fail.clone().into(),
                            mk_prop_generic,
                            (sub_supportdyn, r_generic, nm.clone()),
                            rhs.clone(),
                            rhs,
                            env,
                        )
                    }
                }
            }
            Ty_::Tdependent(dep_ty, ty_sub_inner) => {
                let r_dep = get_reason(&ty_sub).clone();
                let mk_prop_dependent = |subtype_env: &subtype_env::T,
                                         this_ty: Option<&Ty>,
                                         Lhs {
                                             sub_supportdyn,
                                             ty_sub,
                                         }: Lhs,
                                         rhs: (Reason, subtype::Rhs, R),
                                         env: &mut Env| {
                    simplify_disj_r_inner(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        lift_rhs,
                        (sub_supportdyn, ty_sub),
                        rhs,
                        env,
                    )
                };
                simplify_dependent_l(
                    subtype_env,
                    this_ty,
                    mk_prop_dependent,
                    (sub_supportdyn, r_dep, dep_ty.clone(), ty_sub_inner.clone()),
                    rhs,
                    env,
                )
            }
            Ty_::Tnewtype(nm, tyl, _) => {
                let r_newtype = get_reason(&ty_sub).clone();
                let ty_newtype = t_utils::get_newtype_super(env, r_newtype.clone(), nm, tyl);
                let mk_prop_newtype = |subtype_env: &subtype_env::T,
                                       this_ty: Option<&Ty>,
                                       Lhs {
                                           sub_supportdyn,
                                           ty_sub,
                                       }: Lhs,
                                       rhs: (Reason, subtype::Rhs, R),
                                       env: &mut Env| {
                    simplify_disj_r_inner(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        lift_rhs,
                        (sub_supportdyn, ty_sub),
                        rhs,
                        env,
                    )
                };
                let (_, rhs_subtype, rhs_other) = &rhs;
                // `( ||| ) = ( ||| ) ~fail`; `a ||| b ||| c` is `(a ||| b) ||| c`.
                let p = mk_prop(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn,
                        ty_sub,
                    },
                    rhs_other.clone(),
                    env,
                );
                let p = or(fail.clone(), env, p, |env| {
                    subtype::simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub,
                        },
                        *rhs_subtype,
                        env,
                    )
                });
                or(fail.clone(), env, p, |env| {
                    simplify_newtype_l(
                        subtype_env,
                        this_ty,
                        mk_prop_newtype,
                        (sub_supportdyn, r_newtype, nm.clone(), ty_newtype),
                        rhs,
                        env,
                    )
                })
            }
            Ty_::Tany(_)
            | Ty_::Tdynamic(_)
            | Ty_::Tprim(_)
            | Ty_::Tneg(_)
            | Ty_::Tnonnull
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::Tclass(..)
            | Ty_::Tlabel(_)
            | Ty_::TclassPtr(_) => {
                let (_, rhs_subtype, rhs_other) = rhs;
                // `( ||| ) = ( ||| ) ~fail`
                let p = mk_prop(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn,
                        ty_sub,
                    },
                    rhs_other,
                    env,
                );
                or(fail, env, p, |env| {
                    subtype::simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub,
                        },
                        rhs_subtype,
                        env,
                    )
                })
            }
        }
    }
    simplify_disj_r_inner(subtype_env, this_ty, fail, &mk_prop, &lift_rhs, lhs, rhs, env)
}

pub fn dispatch_constraint(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    sub_supportdyn: Option<Reason>,
    ity_sub: InternalType,
    ity_super: InternalType,
    env: &mut Env,
) -> tl::SubtypeProp {
    // Dynamic inference: record constraint-type upper bounds on shadow type
    // variables so they accumulate structural use-type information.
    // Skip Thas_member — it has a dedicated shadow-aware handler in
    // typing_object_get.ml that creates a fresh shadow for the member type.
    // Recording the raw constraint here would produce a duplicate without
    // proper shadow linkage.
    match &ity_sub {
        InternalType::LoclType(ty_sub) => match get_node(ty_sub) {
            Ty_::Tdynamic(Some(shadow_v)) => {
                let dominated_by_shadow_handler = match &ity_super {
                    InternalType::ConstraintType(cty) => {
                        // `snd (deref_constraint_type cty)`
                        match &*cty.1 {
                            ConstraintType_::ThasMember(_) => true,
                            _ => false,
                        }
                    }
                    _ => false,
                };
                if dominated_by_shadow_handler {
                } else {
                    env::add_tyvar_upper_bound(None, env, *shadow_v, ity_super.clone())
                }
            }
            _ => {}
        },
        _ => {}
    }
    match (&ity_sub, &ity_super) {
        (InternalType::LoclType(ty_sub), InternalType::LoclType(ty_super)) => subtype::simplify(
            subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn: sub_supportdyn.as_ref(),
                ty_sub,
            },
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super,
            },
            env,
        ),
        (InternalType::LoclType(ty_sub), InternalType::ConstraintType(cstr)) => {
            let lhs = Lhs {
                sub_supportdyn: sub_supportdyn.as_ref(),
                ty_sub,
            };
            match deref_constraint_type(cstr) {
                (r_super, ConstraintType_::Tdestructure(destructure)) => destructure::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    destructure::Rhs {
                        reason_super: r_super,
                        destructure,
                    },
                    env,
                ),
                (r, ConstraintType_::TcanIndex(can_index)) => can_index::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    can_index::Rhs {
                        reason_super: r,
                        can_index,
                    },
                    env,
                ),
                (r, ConstraintType_::TcanIndexAssign(can_index_assign)) => {
                    can_index_assign::simplify(
                        subtype_env,
                        this_ty,
                        lhs,
                        can_index_assign::Rhs {
                            reason_super: r,
                            can_index_assign,
                        },
                        env,
                    )
                }
                (r, ConstraintType_::TcanTraverse(can_traverse)) => can_traverse::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    can_traverse::Rhs {
                        reason_super: r,
                        can_traverse,
                    },
                    env,
                ),
                (r, ConstraintType_::ThasMember(has_member)) => has_member::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    has_member::Rhs {
                        reason_super: r,
                        has_member,
                    },
                    env,
                ),
                (r, ConstraintType_::ThasTypeMember(has_type_member)) => has_type_member::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    has_type_member::Rhs {
                        reason_super: r,
                        has_type_member,
                    },
                    env,
                ),
                (reason_super, ConstraintType_::ThasConst { name, ty }) => has_const::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    has_const::Rhs {
                        reason_super,
                        name,
                        ty,
                    },
                    env,
                ),
                (
                    reason_super,
                    ConstraintType_::TtypeSwitch {
                        predicate,
                        ty_true,
                        ty_false,
                    },
                ) => type_switch::simplify(
                    subtype_env,
                    this_ty,
                    lhs,
                    type_switch::Rhs {
                        reason_super,
                        predicate,
                        ty_true,
                        ty_false,
                        super_like: false,
                    },
                    env,
                ),
            }
        }
        (
            InternalType::ConstraintType(_),
            InternalType::LoclType(_) | InternalType::ConstraintType(_),
        ) => {
            let subtype_env = subtype_env::possibly_add_violated_constraint(
                subtype_env.clone(),
                typing_defs_constraints::reason(&ity_sub).clone(),
                typing_defs_constraints::reason(&ity_super).clone(),
            );
            let fail = subtype_env::fail(&subtype_env, ity_sub.clone(), ity_super.clone());
            invalid(fail, env)
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;

    fn ty(ty_: Ty_) -> Ty {
        mk((reason::none(), ty_))
    }

    #[test]
    fn contains_dynamic_through_intersection_() {
        let dynamic = ty(Ty_::Tdynamic(None));
        let int = ty(Ty_::Tprim(Tprim::Tint));
        assert!(contains_dynamic_through_intersection(&dynamic));
        assert!(!contains_dynamic_through_intersection(&int));
        // Through nested intersections
        let inter = ty(Ty_::Tintersection(vec![
            int.clone(),
            ty(Ty_::Tintersection(vec![int.clone(), dynamic.clone()])),
        ]));
        assert!(contains_dynamic_through_intersection(&inter));
        assert!(!contains_dynamic_through_intersection(&ty(
            Ty_::Tintersection(vec![int.clone(), int.clone()])
        )));
        // Not through unions or options
        assert!(!contains_dynamic_through_intersection(&ty(Ty_::Tunion(
            vec![dynamic.clone(), int.clone()]
        ))));
        assert!(!contains_dynamic_through_intersection(&ty(Ty_::Toption(
            dynamic
        ))));
    }
}
