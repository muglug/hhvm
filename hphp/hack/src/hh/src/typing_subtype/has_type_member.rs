// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 9614-9857): module `Has_type_member`.
//! See `hh/PORTING.md`.
//!
//! `simplify` has the signature of the prelude's `ConstraintHandler`; the
//! functions of `Common` are called as `common.rs` documents.
//!
//! The polymorphic variant `` [ `As | `Super ] `` of the local
//! `simplify_subtype_bound` is `secondary::RefinementConstraintKind`, the
//! type of the `cstr` of `Secondary.Violated_refinement_constraint` that it
//! is put in.

use naming_special_names_rust as sn;

use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::HasTypeMember;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core;
use crate::typing_defs_core::DependentType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_error::secondary::RefinementConstraintKind;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::or;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_type_member;
use crate::typing_type_member::TypeMember;
use crate::typing_type_member::UnknownConcreteClassKind;

#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub has_type_member: HasTypeMember,
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
        has_type_member,
    } = &rhs;
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        reason_super.clone(),
        ConstraintType_::ThasTypeMember(has_type_member.clone()),
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // `log_subtype_i` prints in the environment it is given, which the
        // continuation changes: a copy.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Has_type_member.simplify",
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
        ty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `~rhs:({ reason_super = r; has_type_member = htm } as rhs)`
    let r = rhs.reason_super.clone();
    let htm = rhs.has_type_member.clone();
    let HasTypeMember {
        id: memid,
        lower: memloty,
        upper: memupty,
    } = htm.clone();
    let htmty = InternalType::ConstraintType(mk_constraint_type((
        r.clone(),
        ConstraintType_::ThasTypeMember(htm.clone()),
    )));
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let subtype_env = subtype_env::possibly_add_violated_constraint(
        subtype_env.clone(),
        get_reason(&ty_sub).clone(),
        r.clone(),
    );
    let fail = subtype_env::fail(
        &subtype_env,
        InternalType::LoclType(ty_sub.clone()),
        htmty.clone(),
    );

    let ity_super = InternalType::ConstraintType(mk_constraint_type((
        r.clone(),
        ConstraintType_::ThasTypeMember(htm),
    )));
    let ity_sub = InternalType::LoclType(ty_sub.clone());
    let cstrs = subtype_env::lazy_tparam_constraints(&subtype_env);
    let secondary_error = subtype_env::mk_secondary_error(cstrs, &subtype_env, ity_sub, ity_super);
    // Contextualize errors that may be generated when
    // checking refinement bounds.
    let subtype_env = subtype_env::map_on_error(subtype_env, |on_error| {
        reasons_callback::prepend_on_apply(on_error, secondary_error)
    });

    let simplify_subtype_bound =
        |kind: RefinementConstraintKind, bound: Ty, ty: Ty, env: &mut Env| -> tl::SubtypeProp {
            let subtype_env = subtype_env::map_on_error(subtype_env.clone(), |on_error| {
                let pos = reason::to_pos(get_reason(&bound));
                reasons_callback::prepend_on_apply(
                    on_error,
                    secondary::T::Violated_refinement_constraint { cstr: (kind, pos) },
                )
            });
            let this_ty = None;
            match kind {
                RefinementConstraintKind::As => subtype::simplify(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &bound,
                    },
                    env,
                ),
                RefinementConstraintKind::Super => subtype::simplify(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &bound,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty,
                    },
                    env,
                ),
            }
        };

    let concrete_rigid_tvar_access =
        |env: &mut Env, ucckind: UnknownConcreteClassKind, bndtys: Vec<Ty>| -> tl::SubtypeProp {
            // First, we try to discharge the subtype query on the bound; if
            // that fails, we mint a fresh rigid type variable to represent
            // the concrete type constant and try to solve the query using it
            let bndty = make_type::intersection(get_reason(&ty_sub).clone(), bndtys.clone());
            // `let ( ||| ) = ( ||| ) ~fail`
            let p = simplify(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &bndty,
                },
                rhs.clone(),
                env,
            );
            or(fail.clone(), env, p, |env| {
                // TODO(refinements): The treatment of `this_ty` below is
                // no good; see below.
                let dtmemty = typing_type_member::make_type_member(
                    env,
                    subtype_env.on_error.clone(),
                    this_ty.cloned().unwrap_or_else(|| ty_sub.clone()),
                    ucckind,
                    &bndtys,
                    &(reason::to_pos(&r), memid.clone()),
                );
                let p = simplify_subtype_bound(
                    RefinementConstraintKind::As,
                    memupty.clone(),
                    dtmemty.clone(),
                    env,
                );
                and(env, p, |env| {
                    simplify_subtype_bound(
                        RefinementConstraintKind::Super,
                        memloty.clone(),
                        dtmemty,
                        env,
                    )
                })
            })
        };

    match get_node(&ty_sub) {
        Ty_::Tclass(x_sub, exact_sub, _tyl_sub) => {
            // TODO(refinements): The treatment of `this_ty` below is
            // no good; we should not default to `ty_sub`. `this_ty`
            // will be used when a type constant refers to another
            // constant either in its def or in its bounds.
            // See related FIXME(T59448452) above.
            let type_member = typing_type_member::lookup_class_type_member(
                env,
                subtype_env.on_error.clone(),
                this_ty.cloned().unwrap_or_else(|| ty_sub.clone()),
                (x_sub, exact_sub),
                &(reason::to_pos(&r), memid.clone()),
            );
            match type_member {
                TypeMember::NotYetAvailable => panic!("TODO(hverr): propagate decl_entry"),
                TypeMember::Error(err) => invalid(err, env),
                TypeMember::Exact(ty) => {
                    let p = simplify_subtype_bound(
                        RefinementConstraintKind::As,
                        memupty.clone(),
                        ty.clone(),
                        env,
                    );
                    and(env, p, |env| {
                        simplify_subtype_bound(
                            RefinementConstraintKind::Super,
                            memloty.clone(),
                            ty,
                            env,
                        )
                    })
                }
                TypeMember::Abstract {
                    name,
                    lower: loty,
                    upper: upty,
                } => {
                    let r_bnd = reason::tconst_no_cstr(name);
                    let loty = loty.unwrap_or_else(|| make_type::nothing(r_bnd.clone()));
                    let upty = upty.unwrap_or_else(|| make_type::mixed(r_bnd));
                    // In case the refinement is exact we check that upty <: loty;
                    // doing the check early gives us a better chance at generating
                    // good error messages. The unification errors we get when
                    // doing this check are usually unhelpful, so we drop them.
                    let is_exact = typing_defs_core::phys_equal(&memloty, &memupty);
                    let p = if is_exact {
                        let subtype_env = subtype_env::map_on_error(
                            subtype_env.clone(),
                            reasons_callback::drop_reasons_on_apply,
                        );
                        subtype::simplify(
                            &subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn: None,
                                ty_sub: &upty,
                            },
                            subtype::Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &loty,
                            },
                            env,
                        )
                    } else {
                        valid(env)
                    };
                    let p = and(env, p, |env| {
                        simplify_subtype_bound(
                            RefinementConstraintKind::As,
                            memupty.clone(),
                            upty,
                            env,
                        )
                    });
                    and(env, p, |env| {
                        simplify_subtype_bound(
                            RefinementConstraintKind::Super,
                            memloty.clone(),
                            loty,
                            env,
                        )
                    })
                }
            }
        }
        Ty_::Tdependent(DependentType::DTexpr(eid), bndty) => concrete_rigid_tvar_access(
            env,
            UnknownConcreteClassKind::EDT(*eid),
            vec![bndty.clone()],
        ),
        Ty_::Tgeneric(s) if s == sn::typehints::THIS => {
            let bnd_tys = typing_set::elements(&env::get_upper_bounds(env, s));
            concrete_rigid_tvar_access(env, UnknownConcreteClassKind::This, bnd_tys)
        }
        Ty_::Tvar(_) => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            htmty,
        ),
        Ty_::Tunion(ty_subs) => {
            let r_sub = get_reason(&ty_sub).clone();
            // Remove this_ty if it equal to the subtype; this avoids a loop. Note
            // that `ty_equal` already uses physical equality to short circuit
            // structural equality so this should be cheap in practice
            let this_ty =
                this_ty.filter(|this_ty| !typing_defs_core::ty_equal(None, this_ty, &ty_sub));
            common::simplify_union_l(
                &subtype_env,
                this_ty,
                simplify,
                |env: &Env, ty: Ty| {
                    env::update_reason(env, ty, |r_sub_prj| {
                        reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                    })
                },
                (sub_supportdyn, ty_subs),
                rhs.clone(),
                env,
            )
        }
        Ty_::Tintersection(ty_subs) => {
            let r_sub = get_reason(&ty_sub).clone();
            // (The OCaml projects the reasons with `prj_union_sub` here.)
            common::simplify_intersection_l(
                &subtype_env,
                this_ty,
                fail.clone().into(),
                simplify,
                |env: &Env, ty: Ty| {
                    env::update_reason(env, ty, |r_sub_prj| {
                        reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                    })
                },
                (sub_supportdyn, ty_subs),
                rhs.clone(),
                env,
            )
        }
        Ty_::Tgeneric(generic_nm) => {
            let r_generic = get_reason(&ty_sub).clone();
            match visited_goals_internal::try_add_visited_generic_sub(
                &subtype_env.visited_internal,
                generic_nm,
                htmty,
            ) {
                None => invalid(fail.clone(), env),
                Some(new_visited) => {
                    let subtype_env =
                        subtype_env::set_visited_internal(subtype_env.clone(), new_visited);
                    common::simplify_generic_l(
                        &subtype_env,
                        this_ty,
                        fail.clone().into(),
                        simplify,
                        (sub_supportdyn, r_generic, generic_nm.clone()),
                        rhs.clone(),
                        rhs.clone(),
                        env,
                    )
                }
            }
        }
        Ty_::Tany(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tnonnull
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tneg(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::TvecOrDict(..)
        | Ty_::Taccess(_)
        | Ty_::Tnewtype(..)
        | Ty_::Tlabel(_) => invalid(fail.clone(), env),
        Ty_::TclassPtr(_) => {
            // TODO(T199606542) Confirm if class pointers appear in HasTypeMember positions
            invalid(fail.clone(), env)
        }
    }
}
