// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 11452-12235): module `Subtype_trans`.
//! See `hh/PORTING.md`.
//!
//! - The OCaml threads pairs `(env, prop)` through the closure functions:
//!   here the environment is `&mut Env` and the proposition is passed and
//!   returned by value (`f ~is_dynamic_aware (env, prop) (r, v) ty on_error`
//!   is `f(is_dynamic_aware, env, prop, (r, v), ty, on_error)`).
//! - `tell` and friends return `(env, ty_err_opt, props)`: here
//!   `(ty_err_opt, props)`, with the environment updated in place.
//! - The functions of the module that the signature hides take the error
//!   callback by reference (`&Option<Reasons_callback.t>`): they hand it to
//!   several calls. `prop_to_env` and `prop_to_env_against_expected_type`
//!   take it by value.
//! - Lists that the OCaml builds by consing and reverses at the end are kept
//!   in the OCaml order (head first) so that the reversals are the OCaml ones.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;

use crate::internal_type_set as ity_set;
use crate::tvid;
use crate::typing_class_pointers;
use crate::typing_defs_constraints::ConstraintType;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::get_reason_i;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::equal_locl_ty;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_log;
use crate::typing_logic as tl;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::valid;
use crate::typing_make_type as make_type;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_subtype::subtype_ask;
use crate::typing_subtype::subtype_simplify;
use crate::typing_subtype_tconst;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// The result of [`tell`] and its friends: `(env, ty_err_opt, props)` in
/// OCaml, the environment being updated in place.
type TellResult = (Option<typing_error::T>, Vec<tl::SubtypeProp>);

pub(crate) fn add_non_subtype_constraint(
    is_dynamic_aware: bool,
    env: &mut Env,
    prop: tl::SubtypeProp,
    (r_sub, var_sub): (Reason, tvid::T),
    cty_super: ConstraintType,
    on_error: &Option<reasons_callback::T>,
) -> tl::SubtypeProp {
    let ty_super = InternalType::ConstraintType(cty_super);
    let upper_bounds_before = env::get_tyvar_upper_bounds(env, var_sub);
    {
        // `~intersect` closes over the environment before the bound is added.
        let intersect_env = env.clone();
        let mut intersect = |ty: InternalType, tyl: &[InternalType]| {
            subtype_simplify::try_intersect_i(Some(true), &intersect_env, ty, tyl)
        };
        env::add_tyvar_upper_bound_and_update_variances(
            Some(&mut intersect),
            env,
            var_sub,
            ty_super,
        );
    }
    let upper_bounds_after = env::get_tyvar_upper_bounds(env, var_sub);
    // Because of [try_intersect_i], the changed upper bounds may include
    // [locl_ty]s
    let added_upper_bounds = ity_set::diff(&upper_bounds_after, &upper_bounds_before);
    // We have the invariant that the lower bound must always be a [locl_ty]
    let lower_bounds: Vec<Ty> = ity_set::elements(&env::get_tyvar_lower_bounds(env, var_sub))
        .into_iter()
        .filter_map(|ty| match ty {
            InternalType::LoclType(ty) => Some(ty),
            _ => panic!("constraint_type in lowerbounds"),
        })
        .collect();
    let subtype_env = subtype_env::create(
        None,                   // require_soundness
        None,                   // require_completeness
        None,                   // ignore_readonly
        None,                   // no_top_bottom
        Some(is_dynamic_aware), // is_dynamic_aware
        None,                   // is_coeffect
        Some(true),             // in_transitive_closure
        None,                   // ignore_likes
        None,                   // has_member_arg_posl
        None,                   // report_ambiguous_shape_splat
        should_cls_sub_cn(env), // class_sub_classname
        2,                      // log_level
        on_error.clone(),
    );
    ity_set::fold(
        |upper_bound: &InternalType, prop: tl::SubtypeProp| {
            let ty_err_opt = typing_subtype_tconst::make_all_type_consts_equal(
                env,
                var_sub,
                upper_bound,
                on_error.clone(),
                true, // as_tyvar_with_cnstr
            );
            let mut prop = match ty_err_opt {
                None => prop,
                Some(ty_err) => invalid(Some(ty_err), env),
            };
            for lower_bound in &lower_bounds {
                let lower_bound = env::update_reason(env, lower_bound.clone(), |bound| {
                    typing_reason::trans_lower_bound(bound, r_sub.clone())
                });
                // Since we can have either the rhs of a subtype constraint or
                // the rhs of any other constraint in the upper bounds we
                // have to inspect the upper bound and dispatch to the
                // appropriate top-level handler
                let prop2 = common::dispatch_constraint(
                    &subtype_env,
                    None, // this_ty
                    None, // sub_supportdyn
                    InternalType::LoclType(lower_bound),
                    upper_bound.clone(),
                    env,
                );
                prop = tl::conj(prop, prop2);
            }
            prop
        },
        &added_upper_bounds,
        prop,
    )
}

pub(crate) fn is_stringish_upper_bound(env: &mut Env, ty: &Ty) -> bool {
    let ty = env::expand_type(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tclass((_, name), _, tyargs) if tyargs.is_empty() && name == C_STRING => true,
        Ty_::Tprim(Tprim::Tarraykey) => true,
        Ty_::Tclass((_, name), _, tyargs)
            if tyargs.is_empty()
                && (name == sn::classes::STRINGISH || name == sn::classes::XHP_CHILD) =>
        {
            true
        }
        Ty_::Toption(ty) => is_stringish_upper_bound(env, ty),
        Ty_::Tunion(tyl) => {
            let mut found = false;
            for ty in tyl {
                if !found {
                    found = is_stringish_upper_bound(env, ty);
                }
            }
            found
        }
        _ => false,
    }
}

pub(crate) fn maybe_widen_class_pointer_bound(env: &mut Env, var: tvid::T, ty_sub: Ty) -> Ty {
    let upper_bounds = env::get_tyvar_upper_bounds(env, var);
    let widen = ity_set::fold(
        |upper_bound: &InternalType, found: bool| {
            if found {
                true
            } else {
                match upper_bound {
                    InternalType::LoclType(ty) => is_stringish_upper_bound(env, ty),
                    InternalType::ConstraintType(_) => false,
                }
            }
        },
        &upper_bounds,
        false,
    );
    if widen {
        typing_class_pointers::coerce_to_name(env, ty_sub)
    } else {
        ty_sub
    }
}

pub(crate) fn maybe_widen_lower_bounds_for_stringish(
    is_dynamic_aware: bool,
    env: &mut Env,
    prop: tl::SubtypeProp,
    (r_sup, var): (Reason, tvid::T),
    ty_super: &Ty,
    on_error: &Option<reasons_callback::T>,
) -> tl::SubtypeProp {
    let widen = is_stringish_upper_bound(env, ty_super);
    if !widen {
        prop
    } else {
        let lower_bounds = env::get_tyvar_lower_bounds(env, var);
        ity_set::fold(
            |lower_bound: &InternalType, prop: tl::SubtypeProp| match lower_bound {
                InternalType::LoclType(ty) => {
                    let widened_ty = typing_class_pointers::coerce_to_name(env, ty.clone());
                    if equal_locl_ty(ty, &widened_ty) {
                        prop
                    } else {
                        add_tyvar_lower_bound_and_close(
                            is_dynamic_aware,
                            env,
                            prop,
                            (r_sup.clone(), var),
                            widened_ty,
                            on_error,
                        )
                    }
                }
                InternalType::ConstraintType(_) => prop,
            },
            &lower_bounds,
            prop,
        )
    }
}

/// Add a new upper bound ty on var.  Apply transitivity of sutyping,
/// so if we already have tyl <: var, then check that for each ty_sub
/// in tyl we have ty_sub <: ty.
pub(crate) fn add_tyvar_upper_bound_and_close(
    is_dynamic_aware: bool,
    env: &mut Env,
    prop: tl::SubtypeProp,
    (r_sub, var): (Reason, tvid::T),
    ty_super: Ty,
    on_error: &Option<reasons_callback::T>,
) -> tl::SubtypeProp {
    let ty_super = sd::transform_dynamic_upper_bound(is_dynamic_aware, env, ty_super);
    let upper_bounds_before = env::get_tyvar_upper_bounds(env, var);
    // If the type is already in the upper bounds of the type variable,
    // then we already know that this subtype assertion is valid
    if ity_set::mem(
        &InternalType::LoclType(ty_super.clone()),
        &upper_bounds_before,
    ) {
        valid(env)
    } else {
        let prop = maybe_widen_lower_bounds_for_stringish(
            is_dynamic_aware,
            env,
            prop,
            (r_sub.clone(), var),
            &ty_super,
            on_error,
        );
        {
            // `~intersect` closes over the environment before the bound is
            // added.
            let intersect_env = env.clone();
            let mut intersect = |ty: InternalType, tyl: &[InternalType]| {
                subtype_simplify::try_intersect_i(Some(true), &intersect_env, ty, tyl)
            };
            env::add_tyvar_upper_bound_and_update_variances(
                Some(&mut intersect),
                env,
                var,
                InternalType::LoclType(ty_super),
            );
        }
        let upper_bounds_after = env::get_tyvar_upper_bounds(env, var);
        let added_upper_bounds: Vec<Ty> =
            ity_set::elements(&ity_set::diff(&upper_bounds_after, &upper_bounds_before))
                .into_iter()
                .filter_map(|ty| match ty {
                    InternalType::LoclType(ty) => Some(ty),
                    _ => panic!("constraint_type in added upperbounds"),
                })
                .collect();
        let lower_bounds: Vec<Ty> = ity_set::elements(&env::get_tyvar_lower_bounds(env, var))
            .into_iter()
            .filter_map(|ty| match ty {
                InternalType::LoclType(ty) => Some(ty),
                _ => panic!("constraint_type in lowerbound"),
            })
            .collect();
        let subtype_env = subtype_env::create(
            None,                   // require_soundness
            None,                   // require_completeness
            None,                   // ignore_readonly
            None,                   // no_top_bottom
            Some(is_dynamic_aware), // is_dynamic_aware
            None,                   // is_coeffect
            Some(true),             // in_transitive_closure
            None,                   // ignore_likes
            None,                   // has_member_arg_posl
            None,                   // report_ambiguous_shape_splat
            should_cls_sub_cn(env), // class_sub_classname
            2,                      // log_level
            on_error.clone(),
        );
        let mut prop = prop;
        for upper_bound in added_upper_bounds {
            let ty_err_opt = typing_subtype_tconst::make_all_type_consts_equal(
                env,
                var,
                &InternalType::LoclType(upper_bound.clone()),
                on_error.clone(),
                true, // as_tyvar_with_cnstr
            );
            prop = match ty_err_opt {
                None => prop,
                Some(ty_err) => invalid(Some(ty_err), env),
            };
            for lower_bound in &lower_bounds {
                let ty_sub = env::update_reason(env, lower_bound.clone(), |bound| {
                    typing_reason::trans_lower_bound(bound, r_sub.clone())
                });
                let prop2 = subtype::simplify(
                    &subtype_env,
                    None, // this_ty
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_sub,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &upper_bound,
                    },
                    env,
                );
                prop = tl::conj(prop, prop2);
            }
        }
        prop
    }
}

/// Add a new lower bound ty on var.  Apply transitivity of subtyping
/// (so if var <: ty1,...,tyn then assert ty <: tyi for each tyi), using
/// simplify_subtype to produce a subtype proposition.
pub(crate) fn add_tyvar_lower_bound_and_close(
    is_dynamic_aware: bool,
    env: &mut Env,
    prop: tl::SubtypeProp,
    (r_sup, var): (Reason, tvid::T),
    ty_sub: Ty,
    on_error: &Option<reasons_callback::T>,
) -> tl::SubtypeProp {
    let ty_sub = maybe_widen_class_pointer_bound(env, var, ty_sub);
    let lower_bounds_before = env::get_tyvar_lower_bounds(env, var);
    // If the type is already in the lower bounds of the type variable, then we
    // already know that this subtype assertion is valid.
    if ity_set::mem(
        &InternalType::LoclType(ty_sub.clone()),
        &lower_bounds_before,
    ) {
        valid(env)
    } else {
        let ty_sub = env::update_reason(env, ty_sub, |bound| {
            typing_reason::trans_lower_bound(bound, r_sup.clone())
        });
        {
            // `~union` closes over the environment before the bound is added.
            let union_env = env.clone();
            let mut union = |ty: InternalType, tyl: &[InternalType]| {
                subtype_simplify::try_union_i(&union_env, ty, tyl)
            };
            env::add_tyvar_lower_bound_and_update_variances(
                Some(&mut union),
                env,
                var,
                InternalType::LoclType(ty_sub),
            );
        }
        let lower_bounds_after = env::get_tyvar_lower_bounds(env, var);
        // We have the invariant that lower bounds _must_ be the lhs of a constraint
        // and this is always a [LoclType]
        let added_lower_bounds: Vec<Ty> =
            ity_set::elements(&ity_set::diff(&lower_bounds_after, &lower_bounds_before))
                .into_iter()
                .filter_map(|ty| match ty {
                    InternalType::LoclType(ty) => Some(ty),
                    _ => panic!("constraint_type in added lowerbounds"),
                })
                .collect();
        let upper_bounds = env::get_tyvar_upper_bounds(env, var);
        let subtype_env = subtype_env::create(
            None,                   // require_soundness
            None,                   // require_completeness
            None,                   // ignore_readonly
            None,                   // no_top_bottom
            Some(is_dynamic_aware), // is_dynamic_aware
            None,                   // is_coeffect
            Some(true),             // in_transitive_closure
            None,                   // ignore_likes
            None,                   // has_member_arg_posl
            None,                   // report_ambiguous_shape_splat
            should_cls_sub_cn(env), // class_sub_classname
            2,                      // log_level
            on_error.clone(),
        );
        let mut prop = prop;
        for lower_bound in added_lower_bounds {
            let ty_err_opt = typing_subtype_tconst::make_all_type_consts_equal(
                env,
                var,
                &InternalType::LoclType(lower_bound.clone()),
                on_error.clone(),
                false, // as_tyvar_with_cnstr
            );
            prop = match ty_err_opt {
                None => prop,
                Some(err) => invalid(Some(err), env),
            };
            prop = ity_set::fold(
                |upper_bound: &InternalType, prop1: tl::SubtypeProp| {
                    // Since we can have either the rhs of a subtype constraint or
                    // the rhs of any other constraint in the upper bounds we
                    // have to inspect the upper bound and dispatch to the
                    // appropriate top-level handler
                    let prop2 = common::dispatch_constraint(
                        &subtype_env,
                        None, // this_ty
                        None, // sub_supportdyn
                        InternalType::LoclType(lower_bound.clone()),
                        upper_bound.clone(),
                        env,
                    );
                    tl::conj(prop1, prop2)
                },
                &upper_bounds,
                prop,
            );
        }
        prop
    }
}

/// A bound in the table of [`simplify_disj`]: whether it is a lower bound,
/// the bound, and the constraint it comes from.
type Bound = (bool, InternalType, tl::SubtypeProp);

/// Traverse a list of disjuncts and remove obviously redundant ones.
///   t1 <: #1 is considered redundant if t2 <: #1 is also a disjunct and t2 <: t1.
/// Dually,
///   #1 <: t1 is considered redundant if #1 <: t2 is also a disjunct and t1 <: t2.
/// It does not preserve the ordering.
pub(crate) fn simplify_disj(env: &Env, disj: Vec<tl::SubtypeProp>) -> Vec<tl::SubtypeProp> {
    // even if sub_ty is not a supertype of super_ty, still consider super_ty redunant
    fn additional_heuristic(
        is_dynamic_aware: bool,
        env: &Env,
        _sub_ty: &InternalType,
        super_ty: &InternalType,
    ) -> bool {
        let nonnull = make_type::supportdyn_nonnull(typing_reason::none());
        subtype_ask::is_sub_type_for_union_i(
            env,
            Some(is_dynamic_aware),
            &InternalType::LoclType(nonnull),
            super_ty,
        )
    }
    // `b :: bounds`
    fn cons(b: Bound, mut bounds: Vec<Bound>) -> Vec<Bound> {
        bounds.insert(0, b);
        bounds
    }
    fn add_new_bound(
        env: &Env,
        is_lower: bool,
        is_dynamic_aware: bool,
        constr: tl::SubtypeProp,
        ty: InternalType,
        mut bounds: Vec<Bound>,
    ) -> Vec<Bound> {
        if bounds.is_empty() {
            return vec![(is_lower, ty, constr)];
        }
        let b = bounds.remove(0);
        let (is_lower_, bound_ty) = (b.0, b.1.clone());
        if is_lower && is_lower_ {
            if subtype_ask::is_sub_type_for_union_i(env, Some(is_dynamic_aware), &bound_ty, &ty) {
                cons(b, bounds)
            } else if subtype_ask::is_sub_type_for_union_i(
                env,
                Some(is_dynamic_aware),
                &ty,
                &bound_ty,
            ) {
                add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds)
            } else if additional_heuristic(is_dynamic_aware, env, &bound_ty, &ty) {
                cons(b, bounds)
            } else if additional_heuristic(is_dynamic_aware, env, &ty, &bound_ty) {
                add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds)
            } else {
                let bounds = add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds);
                cons(b, bounds)
            }
        } else if !is_lower
            && !is_lower_
            && subtype_ask::is_sub_type_for_union_i(env, Some(is_dynamic_aware), &ty, &bound_ty)
        {
            cons(b, bounds)
        } else if !is_lower
            && !is_lower_
            && subtype_ask::is_sub_type_for_union_i(env, Some(is_dynamic_aware), &bound_ty, &ty)
        {
            add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds)
        } else {
            let bounds = add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds);
            cons(b, bounds)
        }
    }
    // Map a type variable to a list of lower and upper bound types. For any two types
    // t1 and t2 both lower or upper in the list, it is not the case that t1 <: t2 or t2 <: t1.
    let mut bound_map: tvid::map::T<Vec<Bound>> = tvid::map::T::new();
    let mut process_bound = |is_lower: bool,
                             is_dynamic_aware: bool,
                             constr: tl::SubtypeProp,
                             ty: InternalType,
                             var: tvid::T| {
        let ty = match ty {
            InternalType::LoclType(ty) if !is_lower => {
                InternalType::LoclType(sd::transform_dynamic_upper_bound(is_dynamic_aware, env, ty))
            }
            ty => ty,
        };
        match bound_map.remove(&var) {
            None => {
                bound_map.insert(var, vec![(is_lower, ty, constr)]);
            }
            Some(bounds) => {
                let new_bounds = add_new_bound(env, is_lower, is_dynamic_aware, constr, ty, bounds);
                bound_map.insert(var, new_bounds);
            }
        }
    };
    /// The OCaml recursion (`Disj (_, props)` goes on with `props @ disj`,
    /// the others keep `d` in front of the result for the rest), as a walk
    /// of the nested lists in the same order, with the kept propositions
    /// pushed in order.
    fn fill_bound_map(
        disj: &[tl::SubtypeProp],
        process_bound: &mut dyn FnMut(bool, bool, tl::SubtypeProp, InternalType, tvid::T),
    ) -> Vec<tl::SubtypeProp> {
        let mut remaining = vec![];
        let mut stack: Vec<std::slice::Iter<'_, tl::SubtypeProp>> = vec![disj.iter()];
        while let Some(top) = stack.last_mut() {
            let Some(d) = top.next() else {
                stack.pop();
                continue;
            };
            match d {
                tl::SubtypeProp::Conj(_) | tl::SubtypeProp::AmbiguousShapeSplat(_) => {
                    remaining.push(d.clone())
                }
                tl::SubtypeProp::Disj(_, props) => stack.push(props.iter()),
                tl::SubtypeProp::IsSubtype(is_dynamic_aware, ty_sub, ty_super) => {
                    match get_tyvar_opt(ty_super) {
                        Some(var_super) => process_bound(
                            true, // is_lower
                            *is_dynamic_aware,
                            d.clone(),
                            ty_sub.clone(),
                            var_super,
                        ),
                        None => match get_tyvar_opt(ty_sub) {
                            Some(var_sub) => process_bound(
                                false, // is_lower
                                *is_dynamic_aware,
                                d.clone(),
                                ty_super.clone(),
                                var_sub,
                            ),
                            None => remaining.push(d.clone()),
                        },
                    }
                }
            }
        }
        remaining
    }
    // Get the constraints from the table that were not removed, and add them to
    // the remaining constraints that were not of the form we were looking for.
    fn rebuild_disj(
        remaining: Vec<tl::SubtypeProp>,
        to_process: Vec<(tvid::T, Vec<Bound>)>,
    ) -> Vec<tl::SubtypeProp> {
        let mut res = vec![];
        for (_, bounds) in to_process {
            res.extend(bounds.into_iter().map(|(_, _, c)| c));
        }
        res.extend(remaining);
        res
    }
    let remaining = fill_bound_map(&disj, &mut process_bound);
    // `Tvid.Map.elements` is `Wrapped_map.elements`, `fold (fun k v acc ->
    // (k, v) :: acc) m []`: in decreasing order of the keys, so the bounds of
    // the largest variable come first (and `tell_exists` tries them first).
    let bounds: Vec<(tvid::T, Vec<Bound>)> = bound_map.into_iter().rev().collect();
    rebuild_disj(remaining, bounds)
}

pub(crate) fn log_non_singleton_disj(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &Env,
    msg: &str,
    disj_prop: &tl::SubtypeProp,
    props: &[tl::SubtypeProp],
) {
    fn aux(
        ty_sub: &InternalType,
        ty_super: &InternalType,
        env: &Env,
        msg: &str,
        disj_prop: &tl::SubtypeProp,
        props: &[tl::SubtypeProp],
    ) {
        match props {
            [] => {}
            [tl::SubtypeProp::Disj(_, props)] => aux(ty_sub, ty_super, env, msg, disj_prop, props),
            [_] => {}
            // The OCaml builds the message before `log_prop` looks at the log
            // level. Printing the types has no effect (it reads copies of
            // the environment), so nothing is built when nothing is logged:
            // the level `log_prop` checks, of the category "prop".
            _ if !typing_log::should_log(env, "prop", 1) => {}
            _ => {
                // (OCaml's `^` evaluates its right operand first.)
                let ty_super_str = typing_print::debug_i(env, ty_super);
                let ty_sub_str = typing_print::debug_i(env, ty_sub);
                let message = format!(
                    "non-singleton disjunction {} of {} <: {}",
                    msg, ty_sub_str, ty_super_str
                );
                typing_log::log_prop(
                    1,
                    &typing_reason::to_pos(get_reason_i(ty_sub)),
                    &message,
                    env,
                    disj_prop,
                )
            }
        }
    }
    aux(ty_sub, ty_super, env, msg, disj_prop, props)
}

pub(crate) fn partition_ambiguous_shape_splat_vars(
    props: Vec<tl::SubtypeProp>,
) -> (tvid::set::T, Vec<tl::SubtypeProp>) {
    let mut vars = tvid::set::T::new();
    // The OCaml conses the other propositions and reverses the result: they
    // stay in their order.
    let mut other_props = vec![];
    for prop in props {
        match prop {
            tl::SubtypeProp::AmbiguousShapeSplat(new_vars) => {
                for var in new_vars {
                    vars.insert(var);
                }
            }
            prop => other_props.push(prop),
        }
    }
    (vars, other_props)
}

pub(crate) fn tell(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &mut Env,
    prop: tl::SubtypeProp,
    on_error: &Option<reasons_callback::T>,
) -> TellResult {
    match prop {
        tl::SubtypeProp::Conj(props) => {
            tell_all(ty_sub, ty_super, env, vec![], vec![], props, on_error)
        }
        // Encodes the invalid proposition with an accompanying error
        tl::SubtypeProp::Disj(inf_err_opt, props) if props.is_empty() => (inf_err_opt, vec![]),
        tl::SubtypeProp::Disj(inf_err_opt, props) => {
            // The logging prints the whole proposition. It does nothing below
            // the level of the category "prop" that it checks: the copy of
            // the proposition is only made when it can log.
            let props = if typing_log::should_log(env, "prop", 1) {
                let disj_prop = tl::SubtypeProp::Disj(inf_err_opt.clone(), props.clone());
                log_non_singleton_disj(
                    ty_sub,
                    ty_super,
                    env,
                    "before simplification",
                    &disj_prop,
                    &props,
                );
                let props = simplify_disj(env, props);
                log_non_singleton_disj(
                    ty_sub,
                    ty_super,
                    env,
                    "after simplification",
                    &disj_prop,
                    &props,
                );
                props
            } else {
                simplify_disj(env, props)
            };
            let ty_errs: Vec<typing_error::T> = inf_err_opt.into_iter().collect();
            tell_exists(
                ty_sub,
                ty_super,
                env,
                ty_errs,
                vec![],
                tvid::set::T::new(),
                props,
                on_error,
            )
        }
        tl::SubtypeProp::IsSubtype(coerce, ty_sub, ty_super) => {
            tell_cstr(env, (coerce, ty_sub, ty_super), on_error)
        }
        tl::SubtypeProp::AmbiguousShapeSplat(vars) => {
            (None, vec![tl::SubtypeProp::AmbiguousShapeSplat(vars)])
        }
    }
}

pub(crate) fn tell_cstr(
    env: &mut Env,
    (is_dynamic_aware, ty_sub, ty_super): (bool, InternalType, InternalType),
    on_error: &Option<reasons_callback::T>,
) -> TellResult {
    let ty_sub = env::expand_internal_type(env, ty_sub);
    let ty_super = env::expand_internal_type(env, ty_super);

    match (&ty_sub, &ty_super) {
        (InternalType::LoclType(lty_sub), InternalType::LoclType(lty_super)) => {
            match (get_node(lty_sub), get_node(lty_super)) {
                // var-l-r
                (Ty_::Tvar(var_sub), Ty_::Tvar(var_super))
                    if env::rank_of_tvar(env, *var_sub) != env::rank_of_tvar(env, *var_super) =>
                {
                    let tvar_pos = typing_reason::to_pos(get_reason(lty_sub));
                    let generic_reason = get_reason(lty_super).clone();
                    let pos_with_generic = typing_reason::to_pos(&generic_reason);
                    let generic_name = None;
                    let error = secondary::T::HigherRankTparamEscape {
                        tvar_pos,
                        pos_with_generic,
                        generic_reason,
                        generic_name,
                    };
                    let fail = on_error
                        .clone()
                        .map(|on_error| typing_error::apply_reasons(error, on_error));
                    (fail, vec![])
                }
                (Ty_::Tvar(var_sub), Ty_::Tvar(var_super)) => {
                    let prop = valid(env);
                    let prop1 = add_tyvar_upper_bound_and_close(
                        is_dynamic_aware,
                        env,
                        prop,
                        (get_reason(lty_sub).clone(), *var_sub),
                        lty_super.clone(),
                        on_error,
                    );
                    let prop = valid(env);
                    let prop2 = add_tyvar_lower_bound_and_close(
                        is_dynamic_aware,
                        env,
                        prop,
                        (get_reason(lty_super).clone(), *var_super),
                        lty_sub.clone(),
                        on_error,
                    );
                    tell_all(
                        &ty_sub,
                        &ty_super,
                        env,
                        vec![],
                        vec![],
                        vec![prop1, prop2],
                        on_error,
                    )
                }
                // var-l
                (Ty_::Tvar(var), _) => {
                    let tvar_rank = env::rank_of_tvar(env, *var);
                    match check_rank(env, lty_super, tvar_rank) {
                        Some((generic_reason, generic_name)) => {
                            let error = secondary::T::HigherRankTparamEscape {
                                tvar_pos: typing_reason::to_pos(get_reason(lty_sub)),
                                pos_with_generic: typing_reason::to_pos(get_reason(lty_super)),
                                generic_reason,
                                generic_name,
                            };
                            let fail = on_error
                                .clone()
                                .map(|on_error| typing_error::apply_reasons(error, on_error));
                            (fail, vec![])
                        }
                        _ => {
                            let prop = valid(env);
                            let prop = add_tyvar_upper_bound_and_close(
                                is_dynamic_aware,
                                env,
                                prop,
                                (get_reason(lty_sub).clone(), *var),
                                lty_super.clone(),
                                on_error,
                            );
                            tell(&ty_sub, &ty_super, env, prop, on_error)
                        }
                    }
                }
                (_, Ty_::Tvar(var)) => {
                    let tvar_rank = env::rank_of_tvar(env, *var);
                    match check_rank(env, lty_sub, tvar_rank) {
                        Some((generic_reason, generic_name)) => {
                            let error = secondary::T::HigherRankTparamEscape {
                                tvar_pos: typing_reason::to_pos(get_reason(lty_super)),
                                pos_with_generic: typing_reason::to_pos(get_reason(lty_sub)),
                                generic_reason,
                                generic_name,
                            };
                            let fail = on_error
                                .clone()
                                .map(|on_error| typing_error::apply_reasons(error, on_error));
                            (fail, vec![])
                        }
                        _ => {
                            let prop = valid(env);
                            let prop = add_tyvar_lower_bound_and_close(
                                is_dynamic_aware,
                                env,
                                prop,
                                (get_reason(lty_super).clone(), *var),
                                lty_sub.clone(),
                                on_error,
                            );
                            tell(&ty_sub, &ty_super, env, prop, on_error)
                        }
                    }
                }
                _ => (
                    None,
                    vec![tl::SubtypeProp::IsSubtype(
                        is_dynamic_aware,
                        ty_sub.clone(),
                        ty_super.clone(),
                    )],
                ),
            }
        }
        // [constraint_type]s are only valid on the rhs
        (InternalType::LoclType(lty_sub), InternalType::ConstraintType(cstr)) => {
            match get_node(lty_sub) {
                Ty_::Tvar(var) => {
                    let prop = valid(env);
                    let prop = add_non_subtype_constraint(
                        is_dynamic_aware,
                        env,
                        prop,
                        (get_reason(lty_sub).clone(), *var),
                        cstr.clone(),
                        on_error,
                    );
                    tell(&ty_sub, &ty_super, env, prop, on_error)
                }
                _ => (
                    None,
                    vec![tl::SubtypeProp::IsSubtype(
                        is_dynamic_aware,
                        ty_sub.clone(),
                        ty_super.clone(),
                    )],
                ),
            }
        }
        (
            InternalType::ConstraintType(_),
            InternalType::LoclType(_) | InternalType::ConstraintType(_),
        ) => (
            None,
            vec![tl::SubtypeProp::IsSubtype(
                is_dynamic_aware,
                ty_sub.clone(),
                ty_super.clone(),
            )],
        ),
    }
}

/// `ty_errs` and `remain` are in the order of the OCaml lists (head first).
/// The OCaml recursion on `props` is a tail call: here a loop.
pub(crate) fn tell_all(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &mut Env,
    ty_errs: Vec<typing_error::T>,
    remain: Vec<tl::SubtypeProp>,
    props: Vec<tl::SubtypeProp>,
    on_error: &Option<reasons_callback::T>,
) -> TellResult {
    let mut ty_errs = ty_errs;
    let mut remain = remain;
    for prop in props {
        let (inf_err_opt, prop_remain) = tell(ty_sub, ty_super, env, prop, on_error);
        // `prop_remain @ remain`
        let mut new_remain = prop_remain;
        new_remain.extend(remain);
        remain = new_remain;
        if let Some(ty_err) = inf_err_opt {
            ty_errs.insert(0, ty_err);
        }
    }
    ty_errs.reverse();
    let ty_err_opt = typing_error::multiple_opt(ty_errs);
    remain.reverse();
    (ty_err_opt, remain)
}

/// `ty_errs` and `remain` are in the order of the OCaml lists (head first).
/// The OCaml recursion on `props` is a tail call: here a loop.
pub(crate) fn tell_exists(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &mut Env,
    ty_errs: Vec<typing_error::T>,
    remain: Vec<tl::SubtypeProp>,
    ambiguous_shape_splat_vars: tvid::set::T,
    props: Vec<tl::SubtypeProp>,
    on_error: &Option<reasons_callback::T>,
) -> TellResult {
    let mut ty_errs = ty_errs;
    let mut remain = remain;
    let mut ambiguous_shape_splat_vars = ambiguous_shape_splat_vars;
    let mut props = props.into_iter();
    // For now, just find the first prop in the disjunction that works
    loop {
        match props.next() {
            None if ambiguous_shape_splat_vars.is_empty() => {
                let inf_err_opt = typing_error::intersect_opt(ty_errs);
                remain.reverse();
                return (inf_err_opt, remain);
            }
            None => {
                remain.reverse();
                let mut props = vec![tl::SubtypeProp::AmbiguousShapeSplat(
                    ambiguous_shape_splat_vars.into_iter().collect(),
                )];
                props.extend(remain);
                return (None, props);
            }
            Some(prop) => {
                // Each disjunct is tried in the environment the disjunction
                // started with: `tell` returns `prop_env`, which is kept only
                // if the disjunct succeeds.
                let env_before = env.clone();
                let (prop_inf_err, prop_remain) = tell(ty_sub, ty_super, env, prop, on_error);
                let (prop_ambiguous_shape_splat_vars, prop_remain) =
                    partition_ambiguous_shape_splat_vars(prop_remain);
                match prop_inf_err {
                    Some(ty_err) => {
                        *env = env_before;
                        ty_errs.insert(0, ty_err);
                        // `prop_remain @ remain`
                        let mut new_remain = prop_remain;
                        new_remain.extend(remain);
                        remain = new_remain;
                    }
                    None if !prop_ambiguous_shape_splat_vars.is_empty() => {
                        *env = env_before;
                        ambiguous_shape_splat_vars.extend(prop_ambiguous_shape_splat_vars);
                    }
                    None => {
                        // `env` is `prop_env`.
                        remain.reverse();
                        return (None, remain);
                    }
                }
            }
        }
    }
}

/// Given a subtype proposition, resolve conjunctions of subtype assertions
/// of the form #v <: t or t <: #v by adding bounds to #v in env. Close env
/// wrt transitivity i.e. if t <: #v and #v <: u then resolve t <: u which
/// may in turn produce more bounds in env.
/// For disjunctions, arbitrarily pick the first disjunct that is not
/// unsatisfiable. If any unsatisfiable disjunct remains, return it.
pub fn prop_to_env(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &mut Env,
    prop: tl::SubtypeProp,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let (ty_err_opt, _props_) = tell(ty_sub, ty_super, env, prop, &on_error);
    ty_err_opt
}

pub fn prop_to_env_against_expected_type(
    ty_sub: &InternalType,
    ty_super: &InternalType,
    env: &mut Env,
    prop: tl::SubtypeProp,
    on_error: Option<reasons_callback::T>,
) -> (Option<typing_error::T>, tvid::set::T) {
    let (ty_err_opt, props) = tell(ty_sub, ty_super, env, prop, &on_error);
    let (ambiguous_shape_splat_vars, _) = partition_ambiguous_shape_splat_vars(props);
    (ty_err_opt, ambiguous_shape_splat_vars)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partition_ambiguous_shape_splat_vars_unions_the_vars_and_keeps_the_order() {
        let props = vec![
            tl::SubtypeProp::Conj(vec![]),
            tl::SubtypeProp::AmbiguousShapeSplat(vec![3, 1]),
            tl::SubtypeProp::Disj(None, vec![]),
            tl::SubtypeProp::AmbiguousShapeSplat(vec![2, 3]),
        ];
        let (vars, props) = partition_ambiguous_shape_splat_vars(props);
        assert_eq!(vars.into_iter().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(props.len(), 2);
        assert!(tl::is_valid(&props[0]));
        assert!(tl::is_unsat(&props[1]));
    }

    #[test]
    fn partition_ambiguous_shape_splat_vars_of_nothing() {
        let (vars, props) = partition_ambiguous_shape_splat_vars(vec![]);
        assert!(vars.is_empty());
        assert!(props.is_empty());
    }
}
