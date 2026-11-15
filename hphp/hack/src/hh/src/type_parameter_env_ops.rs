// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/type_parameter_env_ops.ml`. See `hh/PORTING.md`.

use oxidized::ast_defs;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ctx::R;
use crate::type_parameter_env as tp_env;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::locl_subst;
use crate::typing_defs_core::mk;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_intersection;
use crate::typing_kinding_defs as k_defs;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_set as ty_set;
use crate::typing_union;

/// `'a Typing_defs.tparam`. The callers have declared type parameters, which
/// are `ty::decl::Tparam<R, ty::decl::Ty<R>>`; that definition is generic in
/// the type of the constraints.
type Tparam<TY> = ty::decl::Tparam<R, TY>;

/// `S_map.t`
type SMap<V> = im::OrdMap<String, V>;

/// `TySet.elements`
fn elements(tys: &ty_set::T) -> Vec<Ty> {
    tys.iter().cloned().collect()
}

/// `TySet.singleton`
fn singleton(ty: Ty) -> ty_set::T {
    std::iter::once(ty).collect()
}

fn intersect_upper_bounds(env: &mut Env, r: Reason, ul: &ty_set::T) -> Ty {
    typing_intersection::intersect_list(env, r, &elements(ul))
}

fn union_lower_bounds(env: &mut Env, r: Reason, ll: &ty_set::T) -> Ty {
    typing_union::union_list(env, None, r, &elements(ll))
}

fn join_lower_bounds(env: &mut Env, l1: ty_set::T, l2: ty_set::T) -> ty_set::T {
    // Special case: subset inclusion. Return subset
    // (e.g. if t|u <: T or t <: T then t <: T )
    if l1.is_subset(&l2) {
        l1
    } else if l2.is_subset(&l1) {
        l2
    } else {
        // Convert upper bounds to equivalent union
        let union1 = union_lower_bounds(env, typing_reason::none(), &l1);
        let union2 = union_lower_bounds(env, typing_reason::none(), &l2);
        let new_lower = typing_intersection::intersect(env, typing_reason::none(), union1, union2);
        singleton(new_lower)
    }
}

fn join_upper_bounds(env: &mut Env, u1: ty_set::T, u2: ty_set::T) -> ty_set::T {
    // Special case: subset inclusion. Return subset
    // (e.g. if T <: t & u, or T <: t, then T <: t)
    if u1.is_subset(&u2) {
        u1
    } else if u2.is_subset(&u1) {
        u2
    } else {
        // Convert upper bounds to equivalent intersection
        let inter1 = intersect_upper_bounds(env, typing_reason::none(), &u1);
        let inter2 = intersect_upper_bounds(env, typing_reason::none(), &u2);
        let new_upper = typing_union::union(env, None, None, inter1, inter2);
        singleton(new_upper)
    }
}

/// Merge two type parameter environments. Given tpenv1 and tpenv2 we want
/// to compute a "merged" environment tpenv such that
///     tpenv1 |- tpenv
/// and tpenv2 |- tpenv
///
/// A type parameter defined on only one input is kept: it may be a fresh generic
/// the other input never had. One in the global tpenv (a type constant) is
/// dropped, leaving its global bounds.
/// If it appears in both, supposing we have
///     l1 <: T <: u1 in tpenv1
/// and l2 <: T <: u2 in tpenv2
/// with multiple lower bounds reduced to a union, and multiple upper bounds
/// reduced to an intersection, then the resulting tpenv will have
///     l1&l2 <: T <: u1|u2
pub fn join(env: &mut Env, tpenv1: &tp_env::T, tpenv2: &tp_env::T) -> tp_env::T {
    let merge_pos = |p1: &PosOrDecl, p2: &PosOrDecl| {
        if crate::pos::equal_none(p1) { p2.clone() } else { p1.clone() }
    };
    let global_tpenv = crate::typing_env::get_global_tpenv(env);
    let merged = tp_env::merge_env(
        env,
        tpenv1,
        tpenv2,
        |env: &mut Env, tparam, info1, info2| match (info1, info2) {
            (Some((pos1, info1)), Some((pos2, info2))) => {
                // When both bounds of the first are subsets of those of the
                // second (always so for the binding that both maps share),
                // the join is the binding of the first, and nothing else
                // happens: the merge keeps it. The OCaml (`join`) rebuilds the
                // binding even then, with the same bounds and position;
                // keeping the first map's entry is the same result without
                // the copy, and lets `merge_env` skip the shared bindings.
                let (l1, u1) = (&info1.lower_bounds, &info1.upper_bounds);
                let (l2, u2) = (&info2.lower_bounds, &info2.upper_bounds);
                let lower_is_l1 = l1.is_subset(l2);
                let upper_is_u1 = u1.is_subset(u2);
                if lower_is_l1
                    && upper_is_u1
                    && (!crate::pos::equal_none(pos1) || crate::pos::equal_none(pos2))
                {
                    return tp_env::Merged::First;
                }
                let lower_bounds = if lower_is_l1 {
                    l1.clone()
                } else {
                    join_lower_bounds(env, l1.clone(), l2.clone())
                };
                let upper_bounds = if upper_is_u1 {
                    u1.clone()
                } else {
                    join_upper_bounds(env, u1.clone(), u2.clone())
                };
                let pos = merge_pos(pos1, pos2);
                tp_env::Merged::New((
                    pos,
                    k_defs::Kind {
                        lower_bounds,
                        upper_bounds,
                        ..info1.clone()
                    },
                ))
            }
            (Some(_), None) | (None, Some(_)) if tp_env::mem(tparam, &global_tpenv) => {
                tp_env::Merged::Neither
            }
            (Some(_), _) => tp_env::Merged::First,
            (_, Some(_)) => tp_env::Merged::Second,
            (_, _) => tp_env::Merged::Neither,
        },
    );
    // (`merge_env` does not pass the bindings that only the first has.)
    tp_env::forget_first_only(merged, tpenv1, tpenv2, |tparam| {
        tp_env::mem(tparam, &global_tpenv)
    })
}

fn get_tpenv_equal_bounds(env: &tp_env::T, name: &str) -> ty_set::T {
    let lower = tp_env::get_lower_bounds(env, name);
    let upper = tp_env::get_upper_bounds(env, name);
    ty_set::inter(&lower, &upper)
}

/// Given a list of type parameter names, attempt to simplify away those
/// type parameters by looking for a type to which they are equal in the tpenv.
/// If such a type exists, remove the type parameter from the tpenv.
/// Returns a set of substitutions mapping each type parameter name to the type
/// to which it is equal if found, otherwise to itself.
pub fn simplify_tpenv<TY>(
    env: &mut Env,
    tparams: &[(Option<(Tparam<TY>, String)>, Ty)],
    r: Reason,
) -> SMap<Ty> {
    // The OCaml keeps the environment it was given, for `log_env_change`.
    let old_env = env.clone();
    let mut tpenv = env_::get_tpenv(env);
    // For each tparam, "solve" it if it falls in any of those categories:
    //   - there exists a type ty to which it is equal
    //   - it is covariant and has upper bound ty (or mixed if absent)
    //   - it is contravariant and lower bound ty (or nothing if absent).
    // In which case remove tparam from tpenv and add substitution
    // (tparam -> ty) to substs.
    let mut substs: SMap<Ty> = SMap::new();
    for (p_opt, ty) in tparams {
        let reason = get_reason(ty).clone();
        match p_opt {
            None => {}
            Some((tp, tparam_name)) => {
                let equal_bounds = get_tpenv_equal_bounds(&tpenv, tparam_name);
                let lower_bounds = tp_env::get_lower_bounds(&tpenv, tparam_name);
                let upper_bounds = tp_env::get_upper_bounds(&tpenv, tparam_name);
                let lower_bound = union_lower_bounds(env, reason.clone(), &lower_bounds);
                let upper_bound = intersect_upper_bounds(env, reason, &upper_bounds);
                // remove tparam_name from tpenv, and in any lower/upper bound set
                // where it occurs.
                // We don't need to do any merging of lower/upper bounds,
                // because all its lower/upper bounds
                // are already lower/upper bounds of `bound` (and other bounds)
                // thanks to the transitive closure we've done in
                // Typing_subtype.add_constraint.
                //
                // `TySet.choose_opt` is `min_elt_opt`.
                match (&tp.variance, equal_bounds.iter().next()) {
                    (_, Some(bound)) => {
                        tp_env::remove(&mut tpenv, tparam_name);
                        substs.insert(tparam_name.clone(), bound.clone());
                    }
                    (ast_defs::Variance::Covariant, _) => {
                        tp_env::remove(&mut tpenv, tparam_name);
                        substs.insert(tparam_name.clone(), upper_bound);
                    }
                    (ast_defs::Variance::Contravariant, _) => {
                        tp_env::remove(&mut tpenv, tparam_name);
                        substs.insert(tparam_name.clone(), lower_bound);
                    }
                    _ => {
                        // TODO see comment at beginning of function
                        let tparam_ty = mk((r.clone(), Ty_::Tgeneric(tparam_name.clone())));
                        substs.insert(tparam_name.clone(), tparam_ty);
                    }
                }
            }
        }
    }
    env_::env_with_tpenv(env, tpenv.clone());
    // reduce the set of substitutions. For example, for a set of substitutions
    // like
    //   Ta -> Tb
    //   Tb -> int
    // simplify to:
    //   Ta -> int
    //   Tb -> int
    fn reduce(substs: &mut SMap<Ty>, tparam: &str) -> Option<Ty> {
        match substs.get(tparam).cloned() {
            None => None,
            Some(subst) => match get_node(&subst) {
                Ty_::Tgeneric(tparam_) if tparam_ != tparam => {
                    // TODO see comment at beginning of function
                    let new_subst_opt = reduce(substs, tparam_);
                    match new_subst_opt {
                        None => Some(subst),
                        Some(new_subst) => {
                            substs.insert(tparam.to_string(), new_subst.clone());
                            Some(new_subst)
                        }
                    }
                }
                _ => Some(subst),
            },
        }
    }
    for (p_opt, _) in tparams {
        match p_opt {
            None => {}
            Some((_, name)) => {
                reduce(&mut substs, name);
            }
        }
    }
    // Apply substitution to bounds on type parameters that remain
    let combine_reasons = |_src: Reason, dest: Reason| dest;
    tp_env::map(
        |ty| locl_subst::apply(ty.clone(), &substs, &combine_reasons),
        &mut tpenv,
    );
    env_::env_with_tpenv(env, tpenv);
    env_::log_env_change("simplify_tpenv", None, &old_env, env);
    substs
}
