// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 10415-10515): module `Type_switch`.
//! See `hh/PORTING.md`.
//!
//! `simplify` has the signature of the prelude's `ConstraintHandler`; the
//! functions of `Common` are called as `common.rs` documents.

use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_intersection;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;

#[derive(Clone, Debug)]
pub struct Rhs {
    pub super_like: bool,
    pub reason_super: Reason,
    pub predicate: TypePredicate,
    pub ty_true: Ty,
    pub ty_false: Ty,
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
        super_like: _,
        reason_super,
        predicate,
        ty_true,
        ty_false,
    } = &rhs;
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        reason_super.clone(),
        ConstraintType_::TtypeSwitch {
            predicate: predicate.clone(),
            ty_true: ty_true.clone(),
            ty_false: ty_false.clone(),
        },
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // `log_subtype_i` prints in the environment it is given, which the
        // continuation changes: a copy.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Type_switch.simplify",
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
        ty_sub,
        sub_supportdyn,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `~rhs:({ super_like; reason_super; predicate; ty_true; ty_false } as rhs)`
    let Rhs {
        super_like,
        reason_super,
        predicate,
        ty_true,
        ty_false,
    } = rhs.clone();
    let cty = mk_constraint_type((
        reason_super.clone(),
        ConstraintType_::TtypeSwitch {
            predicate: predicate.clone(),
            ty_true: ty_true.clone(),
            ty_false: ty_false.clone(),
        },
    ));
    let ty_super = InternalType::ConstraintType(cty);
    let ty_sub = env::expand_type(env, ty_sub.clone());
    match get_node(&ty_sub) {
        Ty_::Tvar(_) => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            ty_super,
        ),
        Ty_::Tunion(ty_subs) => {
            let r_sub = get_reason(&ty_sub).clone();
            common::simplify_union_l(
                subtype_env,
                this_ty,
                simplify,
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
        _ => {
            let partition = typing_refinement::partition_ty(env, &ty_sub, &predicate);
            let intersect = |env: &mut Env, tyl: &[Ty]| {
                typing_intersection::intersect_list(env, reason_super.clone(), tyl)
            };
            let simplify_subtype = |f: &dyn Fn(&mut Env, &[Ty]) -> Ty,
                                    tyl: &[Ty],
                                    ty_super: Ty,
                                    env: &mut Env| {
                let ty_sub = f(env, tyl);
                subtype::simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    subtype::Rhs {
                        super_supportdyn: false,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                )
            };
            // `tys : Typing_refinement.dnf_ty`; `~init:(env, props)` is
            // `env` with `init`.
            let simplify_split =
                |env: &mut Env, init: tl::SubtypeProp, tys: Vec<Vec<Ty>>, ty_sup: &Ty| {
                    let mut res = init;
                    for tyl in tys {
                        res = and(env, res, |env| {
                            simplify_subtype(&intersect, &tyl, ty_sup.clone(), env)
                        });
                    }
                    res
                };
            let left = partition.left;
            let span = partition.span;
            let right = partition.right;
            // `left @ span` and `right @ span`
            let left_span: Vec<Vec<Ty>> = left.iter().chain(span.iter()).cloned().collect();
            let right_span: Vec<Vec<Ty>> = right.iter().chain(span.iter()).cloned().collect();
            let props = simplify_split(env, tl::valid(), left_span, &ty_true);
            simplify_split(env, props, right_span, &ty_false)
        }
    }
}
