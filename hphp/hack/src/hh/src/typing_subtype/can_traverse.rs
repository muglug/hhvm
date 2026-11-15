// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 9376-9612): module `Can_traverse`.
//! See `hh/PORTING.md`.
//!
//! `simplify` has the signature of the prelude's `ConstraintHandler`; the
//! functions of `Common` are called as `common.rs` documents.

/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::tast;
use crate::typing_defs_constraints::CanTraverse;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub can_traverse: CanTraverse,
}

pub(crate) fn subtype_with_dynamic(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs,
    CanTraverse {
        key: ct_key,
        val: ct_val,
        ..
    }: &CanTraverse,
    env: &mut Env,
) -> tl::SubtypeProp {
    let subty_prop_val = |env: &mut Env| {
        subtype::simplify(
            subtype_env,
            this_ty,
            lhs.clone(),
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ct_val,
            },
            env,
        )
    };
    let subty_prop_key = |env: &mut Env| match ct_key {
        None => valid(env),
        Some(ct_key) => subtype::simplify(
            subtype_env,
            this_ty,
            lhs.clone(),
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ct_key,
            },
            env,
        ),
    };
    let prop = subty_prop_val(env);
    and(env, prop, subty_prop_key)
}

pub fn simplify(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Lhs {
        sub_supportdyn: _,
        ty_sub,
    } = lhs;
    let Rhs {
        reason_super,
        can_traverse,
    } = &rhs;
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        reason_super.clone(),
        ConstraintType_::TcanTraverse(can_traverse.clone()),
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // `log_subtype_i` prints in the environment it is given, which the
        // continuation changes: a copy.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Can_traverse.simplify",
            &log_env,
            &ty_sub,
            &ty_super,
            || simplify_(subtype_env, this_ty, lhs, rhs, env),
        )
    } else {
        simplify_(subtype_env, this_ty, lhs, rhs, env)
    }
}

pub(crate) fn simplify_(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    Lhs {
        sub_supportdyn,
        ty_sub: lty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `~rhs:({ reason_super = r; can_traverse = ct } as rhs)`
    let r = rhs.reason_super.clone();
    let ct = rhs.can_traverse.clone();
    let lty_sub = env::expand_type(env, lty_sub.clone());
    let subtype_env = subtype_env::possibly_add_violated_constraint(
        subtype_env.clone(),
        get_reason(&lty_sub).clone(),
        r.clone(),
    );
    let fail = subtype_env::fail(
        &subtype_env,
        InternalType::LoclType(lty_sub.clone()),
        InternalType::ConstraintType(mk_constraint_type((
            r.clone(),
            ConstraintType_::TcanTraverse(ct.clone()),
        ))),
    );
    if t_utils::is_tyvar_error(env, &lty_sub) {
        let trav_ty = can_traverse_to_iface(&ct);
        subtype::simplify(
            &subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn,
                ty_sub: &lty_sub,
            },
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &trav_ty,
            },
            env,
        )
    } else {
        // `let mk_prop ~subtype_env ~this_ty ~lhs ~rhs = simplify ~subtype_env ~this_ty ~lhs ~rhs`
        let mk_prop = simplify;
        match get_node(&lty_sub) {
            Ty_::Tdynamic(_) => subtype_with_dynamic(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &lty_sub,
                },
                &ct,
                env,
            ),
            _ if sub_supportdyn.is_some() && tast::is_under_dynamic_assumptions(env.checked) => {
                subtype_with_dynamic(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &lty_sub,
                    },
                    &ct,
                    env,
                )
            }
            Ty_::Tclass(..) | Ty_::TvecOrDict(..) | Ty_::Tany(_) => {
                let trav_ty = can_traverse_to_iface(&ct);
                subtype::simplify(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &lty_sub,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &trav_ty,
                    },
                    env,
                )
            }
            Ty_::Tunion(ty_subs) => {
                let r_sub = get_reason(&lty_sub).clone();
                common::simplify_union_l(
                    &subtype_env,
                    this_ty,
                    mk_prop,
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
            Ty_::Tvar(id) => {
                // If the type is already in the upper bounds of the type variable,
                // then we already know that this subtype assertion is valid
                let cty = InternalType::ConstraintType(mk_constraint_type((
                    r.clone(),
                    ConstraintType_::TcanTraverse(ct.clone()),
                )));
                if ity_set::mem(&cty, &env::get_tyvar_upper_bounds(env, *id)) {
                    valid(env)
                } else {
                    mk_issubtype_prop(
                        sub_supportdyn,
                        subtype_env.is_dynamic_aware,
                        env,
                        InternalType::LoclType(lty_sub.clone()),
                        InternalType::ConstraintType(mk_constraint_type((
                            r,
                            ConstraintType_::TcanTraverse(ct),
                        ))),
                    )
                }
            }
            Ty_::Tintersection(ty_subs) => {
                let r_sub = get_reason(&lty_sub).clone();
                // A & B <: C iif A <: C | !B
                //
                // The second case matches without binding the environment
                // that `find_type_with_exact_negation` returns: it goes on
                // with the environment from before.
                match subtype_negation::find_type_with_exact_negation_opt(env, ty_subs) {
                    Some((non_ty, tyl)) => {
                        let ty_sub = make_type::intersection(r_sub, tyl);

                        let mk_prop = simplify;
                        let lift_rhs = |Rhs {
                                            reason_super,
                                            can_traverse,
                                        }: Rhs| {
                            mk_constraint_type((
                                reason_super,
                                ConstraintType_::TcanTraverse(can_traverse),
                            ))
                        };
                        let lhs = (sub_supportdyn, &ty_sub);
                        let rhs_subtype = subtype::Rhs {
                            super_supportdyn: false,
                            super_like: false,
                            ty_super: &non_ty,
                        };
                        let rhs_can_traverse = Rhs {
                            reason_super: r.clone(),
                            can_traverse: ct,
                        };
                        let rhs = (r, rhs_subtype, rhs_can_traverse);
                        common::simplify_disj_r(
                            &subtype_env,
                            this_ty,
                            fail,
                            mk_prop,
                            lift_rhs,
                            lhs,
                            rhs,
                            env,
                        )
                    }
                    None => {
                        common::simplify_intersection_l(
                            &subtype_env,
                            this_ty,
                            fail.into(),
                            mk_prop,
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
                }
            }
            Ty_::Tgeneric(generic_nm) => {
                let r_sub = get_reason(&lty_sub).clone();
                common::simplify_generic_l(
                    &subtype_env,
                    this_ty,
                    fail.into(),
                    mk_prop,
                    (sub_supportdyn, r_sub, generic_nm.clone()),
                    rhs.clone(),
                    rhs,
                    env,
                )
            }
            Ty_::Tnewtype(alias_name, tyl, _) => {
                let r_sub = get_reason(&lty_sub).clone();
                let ty_newtype = t_utils::get_newtype_super(env, r_sub.clone(), alias_name, tyl);
                common::simplify_newtype_l(
                    &subtype_env,
                    this_ty,
                    mk_prop,
                    (sub_supportdyn, r_sub, alias_name.clone(), ty_newtype),
                    rhs,
                    env,
                )
            }
            Ty_::Tdependent(dep_ty, ty_inner) => {
                let r_sub = get_reason(&lty_sub).clone();
                common::simplify_dependent_l(
                    &subtype_env,
                    this_ty,
                    mk_prop,
                    (sub_supportdyn, r_sub, dep_ty.clone(), ty_inner.clone()),
                    rhs,
                    env,
                )
            }
            Ty_::Toption(_)
            | Ty_::Tprim(_)
            | Ty_::Tnonnull
            | Ty_::Tneg(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(_)
            | Ty_::Taccess(_)
            | Ty_::Tlabel(_) => invalid(fail, env),
            Ty_::TclassPtr(_) => {
                // TODO(T199606542) confirm CanTraverse behavior for class pointers
                invalid(fail, env)
            }
        }
    }
}
