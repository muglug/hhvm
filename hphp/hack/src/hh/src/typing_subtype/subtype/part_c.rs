// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 4773-7656): module `Subtype`.
//! See `hh/PORTING.md`.
//!
//! This part is `simplify_`, the main case analysis of subtyping: one
//! function with one `match` on the expanded subtype and supertype, in the
//! order of the OCaml arms. The bodies of the large arms are the private
//! functions after it; they get the variables that the OCaml arms see in
//! their scope in a [`Scope`], and the local functions of the OCaml arms
//! (`subtype_args`, `simplify_elems_req`, `simplify_elems_opt`, ...) are
//! private functions of the same names.
//!
//! - `lhs` and `rhs` stay as `simplify_` gets them: the OCaml uses them
//!   (`lhs.ty_sub`, `{ lhs with ty_sub }`, `rhs` given to `Common`) with the
//!   types before expansion, while `ty_sub` and `ty_super` are the expanded
//!   ones.
//! - `( &&& )` is `typing_logic_helpers::and`, `( ||| ) ~fail` is
//!   `typing_logic_helpers::or(fail, ..)`; their right operand, a partial
//!   application in OCaml, is the closure given to them (building it has no
//!   effect in OCaml: reason updates, records, `mk`).
//! - Literal list patterns (`Tunion [t]`, `Tnewtype (n, [t], _)`) are length
//!   guards before the other conditions of the arm; they have no effect.

use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::pos::Pos;
use ty::decl::WhereConstraint;

#[allow(unused_imports)]
use super::*;
use crate::class_refinement;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::naming_special_names::classes::C_CLOSURE;
use crate::pos_or_decl;
use crate::subtype_recursion_tracker::subtype_op;
use crate::tast;
use crate::tvid;
use crate::type_expansions;
use crate::typing_case_type_utils;
use crate::typing_defs;
use crate::typing_corners;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::TypedefCaseTypeVariant;
use crate::typing_defs::TypedefTypeAssignment;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_constraints::HasTypeMember;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::ClassRefinement;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclWhereConstraint;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::PosString;
use crate::typing_defs_core::RefinedConstBound;
use crate::typing_defs_core::RefinedConstBounds;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::get_ft_support_dynamic_type;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::is_nonexact;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_defs_core::same_type_origin;
use crate::typing_defs_core::ty_equal;
use crate::typing_dynamic;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::secondary;
/// `module Inter = Typing_intersection`
use crate::typing_intersection as inter;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::if_unsat;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::or;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
use crate::typing_set;
use crate::typing_solver_utils;
use crate::typing_subtype::common;
use crate::typing_subtype::has_const;
use crate::typing_subtype::has_type_member;
use crate::typing_subtype::instantiate;
use crate::typing_subtype::prelude::*;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// The variables of `simplify_` in the scope of its `match`, which the
/// private functions below (the bodies of its large arms) use as the OCaml
/// arms do.
#[derive(Clone, Copy)]
struct Scope<'a> {
    /// After `Subtype_env.possibly_add_violated_constraint`.
    subtype_env: &'a subtype_env::T,
    this_ty: Option<&'a Ty>,
    /// `~lhs` and `~rhs` as `simplify_` gets them (not expanded).
    lhs: Lhs<'a>,
    rhs: Rhs<'a>,
    sub_supportdyn: Option<&'a Reason>,
    super_like: bool,
    /// Expanded, and with likes stripped under `ignore_likes`.
    ty_sub: &'a Ty,
    /// Expanded.
    ty_super: &'a Ty,
    /// Built when first needed (`subtype_env::fail_deferred`).
    fail: &'a subtype_env::Fail<'a>,
}

pub(crate) fn simplify_(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs<'_>,
    rhs: Rhs<'_>,
    env: &mut Env,
) -> tl::SubtypeProp {
    // The fields of `~lhs` and `~rhs` (borrowed), and the types once
    // expanded, are borrowed (copied where they are given away below):
    // `Env.expand_type` gives back the type it is given unless it is a type
    // variable.
    let Lhs {
        sub_supportdyn,
        ty_sub,
    } = lhs;
    let Rhs {
        super_supportdyn,
        super_like,
        ty_super,
    } = rhs;
    // `simplify_subtype_by_physical_equality`, before and after the
    // expansion: the option it tests is read once.
    let by_physical_equality = !env.genv.tcopt.tco_disable_physical_equality;
    if by_physical_equality && crate::typing_defs_core::phys_equal(ty_sub, ty_super) {
        return tl::valid();
    }
    {
        let ty_super_expanded;
        let ty_super: &Ty = match get_node(ty_super) {
            Ty_::Tvar(_) => {
                ty_super_expanded = env::expand_type(env, ty_super.clone());
                &ty_super_expanded
            }
            _ => ty_super,
        };
        let ty_sub_expanded;
        let ty_sub: &Ty = match get_node(ty_sub) {
            Ty_::Tvar(_) => {
                ty_sub_expanded = env::expand_type(env, ty_sub.clone());
                &ty_sub_expanded
            }
            _ => ty_sub,
        };
        if by_physical_equality && crate::typing_defs_core::phys_equal(ty_sub, ty_super) {
            return tl::valid();
        }
        {
            // `possibly_add_violated_constraint` returns the environment it is
            // given when it adds no candidate: then it is not copied.
            let subtype_env_with_candidate;
            let subtype_env = match subtype_env::possibly_add_violated_constraint_opt(
                subtype_env,
                get_reason(ty_sub),
                get_reason(ty_super),
            ) {
                None => subtype_env,
                Some(env_with_candidate) => {
                    subtype_env_with_candidate = env_with_candidate;
                    &subtype_env_with_candidate
                }
            };
            let fail = subtype_env::fail_deferred(subtype_env, &ty_sub, &ty_super);
            fn simplify_splat_vec(env: &mut Env, ty: Ty) -> Ty {
                let ty = env::expand_type(env, ty);
                match get_node(&ty) {
                    Ty_::Tclass((_, n), _, tys) if tys.len() == 1 && n == sn::collections::VEC => {
                        let r = get_reason(&ty).clone();
                        mk((
                            r,
                            Ty_::Ttuple(TupleType {
                                required: vec![],
                                optional: vec![],
                                extra: TupleExtra::Tvariadic(tys[0].clone()),
                            }),
                        ))
                    }
                    _ => ty,
                }
            }
            let ty_sub_stripped;
            let ty_sub: &Ty = if subtype_env.ignore_likes {
                let ty_opt = typing_dynamic_utils::try_strip_dynamic(
                    Some(true), // accept_intersections
                    Some(true), // do_not_solve_likes
                    env,
                    ty_sub,
                );
                match ty_opt {
                    Some(ty) => {
                        ty_sub_stripped = ty;
                        &ty_sub_stripped
                    }
                    None => ty_sub,
                }
            } else {
                ty_sub
            };
            // Dynamic inference: when the subtype is a dynamic with a shadow type
            // variable, record the supertype as an upper bound on the shadow. This is
            // the core mechanism — every [dynamic <: T] check contributes T to the
            // shadow's constraint set, building a use-type profile of the dynamic
            // expression.
            match get_node(&ty_sub) {
                Ty_::Tdynamic(Some(shadow_v)) => env::add_tyvar_upper_bound(
                    None,
                    env,
                    *shadow_v,
                    InternalType::LoclType(ty_super.clone()),
                ),
                _ => {}
            }
            let s = Scope {
                subtype_env,
                this_ty,
                lhs,
                rhs,
                sub_supportdyn,
                super_like,
                ty_sub: &ty_sub,
                ty_super: &ty_super,
                fail: &fail,
            };
            match (get_node(&ty_sub), get_node(&ty_super)) {
                // (...t) <: t
                (
                    Ty_::Ttuple(TupleType {
                        required,
                        optional,
                        extra: TupleExtra::Tsplat(ty_sub_splat),
                    }),
                    _,
                ) if required.is_empty() && optional.is_empty() => {
                    let ty_sub = simplify_splat_vec(env, ty_sub_splat.clone());
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                }
                // t <: (...t)
                (
                    _,
                    Ty_::Ttuple(TupleType {
                        required,
                        optional,
                        extra: TupleExtra::Tsplat(ty_super_splat),
                    }),
                ) if required.is_empty() && optional.is_empty() => {
                    let ty_sub = simplify_splat_vec(env, ty_sub.clone());
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn,
                            ty_super: &ty_super_splat,
                        },
                        env,
                    )
                }
                // First come all the rewrites.
                // By "rewrite", we mean stuff like A <: ?B ---> A & nonnull <: B
                // -- Rewrite: x <: Tunion[t] ---> x <: t
                (_, Ty_::Tunion(tys)) if tys.len() == 1 => {
                    let ty_super_prime = &tys[0];
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &ty_super_prime,
                        },
                        env,
                    )
                }
                // -- Rewrite:
                //    t <: #1 | arraykey => t & !arraykey <: #1
                //    or t <: #1 | !arraykey => t & arraykey <: #1
                // TODO(mjt) this is awkward because we need to expand and dereference types
                // in a nested position. This would be easier if we didn't have the
                // implmentation abstract within constraint solving and we had a function
                // (or set of functions) for expansion to a given depth
                (_, Ty_::Tunion(tys))
                    if tys.len() == 2 && expands_to_var_and_arraykey(&tys[0], &tys[1], env) =>
                {
                    let (tvar_ty, ak_ty) = var_and_arraykey_exn(&tys[0], &tys[1], env);

                    // `mk ak_ty`, which the OCaml builds twice (for the
                    // reason and for the type): the two are the same type.
                    let ak = mk(ak_ty);
                    let neg_ty = inter::negate_type(
                        env,
                        get_reason(&ak).clone(),
                        &ak,
                        t_utils::Approx::ApproxDown,
                    );
                    let inter_ty = inter::intersect(
                        env,
                        get_reason(&lhs.ty_sub).clone(),
                        neg_ty,
                        lhs.ty_sub.clone(),
                    );
                    let lhs = Lhs {
                        ty_sub: &inter_ty,
                        ..lhs
                    };
                    let rhs = Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &mk(tvar_ty),
                    };
                    simplify(subtype_env, this_ty, lhs, rhs, env)
                }
                // -- Rewrite: x <: ?supportdyn<t> ---> x <: supportdyn<?t>
                (
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::Toption(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tunion(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tvar(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Toption(ty_inner),
                ) if expands_to_supportdyn(ty_inner, env) => {
                    let r_super = get_reason(&ty_super).clone();
                    let ty_inner = env::expand_type(env, ty_inner.clone());
                    // Since we have guarded on [ty_inner] being a supportdyn new type,
                    // the following calls will not generate exceptions
                    let (_, tyargs, _) = newtype_exn(&ty_inner, env);
                    // `List.hd_exn`
                    let tyarg = tyargs[0].clone();
                    let tyarg = make_type::nullable(r_super.clone(), tyarg);
                    let ty_super = make_type::supportdyn(r_super, tyarg);
                    let lhs = Lhs {
                        ty_sub: &ty_sub,
                        ..lhs
                    };
                    let rhs = Rhs {
                        super_like: rhs.super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    };
                    simplify(subtype_env, this_ty, lhs, rhs, env)
                }
                // -- Rewrite:
                //    supportdyn<t> <: ?u
                //    ---> nonnull & supportdyn<t> <: u
                //    ---> supportdyn<nonnull & t> <: u
                (Ty_::Tnewtype(name, tyargs, _), Ty_::Toption(lty_inner))
                    if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN =>
                {
                    let r = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    let tyarg1 = &tyargs[0];
                    // TODO(mjt) add 'rewrite' reason including both r & r_super?
                    let ty_sub_prime = inter::intersect(
                        env,
                        r_super.clone(),
                        tyarg1.clone(),
                        make_type::nonnull(r_super.clone()),
                    );
                    let lty_inner = env::update_reason(env, lty_inner.clone(), |r_super_prj| {
                        reason::prj_nullable_super(r_super.clone(), r_super_prj)
                    });
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: Some(&r),
                            ty_sub: &ty_sub_prime,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &lty_inner,
                        },
                        env,
                    )
                }
                // -- Rewrite: _ & ...  & _ <: ?t ---> _ & .. & _ & nonnull <: t
                // but only when the intersection does not contain any type with an exact
                // negation (we apply a rewrite in the other direction for those cases)
                (Ty_::Tintersection(ty_subs), Ty_::Toption(ty_inner_super))
                    if expands_to_var_or_intersection(ty_inner_super, env)
                        // The environment that the negation returns is dropped.
                        && !subtype_negation::has_type_with_exact_negation(env, ty_subs) =>
                {
                    let r_super = get_reason(&ty_super).clone();
                    let ty_sub = inter::intersect(
                        env,
                        r_super.clone(),
                        ty_sub.clone(),
                        make_type::nonnull(r_super.clone()),
                    );
                    let ty_inner_super =
                        env::update_reason(env, ty_inner_super.clone(), |r_super_prj| {
                            reason::prj_nullable_super(r_super.clone(), r_super_prj)
                        });
                    let lhs = Lhs {
                        ty_sub: &ty_sub,
                        ..lhs
                    };
                    let rhs = Rhs {
                        super_supportdyn: false,
                        ty_super: &ty_inner_super,
                        ..rhs.clone()
                    };
                    simplify(subtype_env, this_ty, lhs, rhs, env)
                }
                // -- C-Var-R -----------------------------------------------------------
                (Ty_::Tunion(_), Ty_::Tvar(_)) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // We want to treat nullable as a union with the same rule as above.
                // This is only needed for Tvar on right; other cases are dealt with specially as
                // derived rules.
                (Ty_::Toption(t), Ty_::Tvar(_var_super)) => {
                    let r = get_reason(&ty_sub).clone();
                    let t = env::expand_type(env, t.clone());
                    match get_node(&t) {
                        // We special case on `mixed <: Tvar _`, adding the entire `mixed` type
                        // as a lower bound. This enables clearer error messages when upper bounds
                        // are added to the type variable: transitive closure picks up the
                        // entire `mixed` type, and not separately consider `null` and `nonnull`
                        Ty_::Tnonnull => mk_issubtype_prop(
                            sub_supportdyn,
                            subtype_env.is_dynamic_aware,
                            env,
                            InternalType::LoclType(ty_sub.clone()),
                            InternalType::LoclType(ty_super.clone()),
                        ),
                        _ => {
                            let ty_null = make_type::null(r.clone());
                            let t = env::update_reason(env, t.clone(), |r_sub_prj| {
                                reason::prj_nullable_sub(r.clone(), r_sub_prj)
                            });
                            let p = simplify(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &t,
                                },
                                Rhs {
                                    super_like,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                env,
                            );
                            and(env, p, |env| {
                                simplify(
                                    subtype_env,
                                    this_ty,
                                    Lhs {
                                        sub_supportdyn,
                                        ty_sub: &ty_null,
                                    },
                                    Rhs {
                                        super_like: false,
                                        super_supportdyn: false,
                                        ty_super: &ty_super,
                                    },
                                    env,
                                )
                            })
                        }
                    }
                }
                (Ty_::Tvar(var_sub), Ty_::Tvar(var_super)) if tvid::equal(*var_sub, *var_super) => {
                    valid(env)
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tintersection(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tvar(var_super_id),
                ) => simplify_c_var_r(&s, *var_super_id, env),
                // -- C-Inter-R ---------------------------------------------------------
                (Ty_::Tunion(ty_subs), Ty_::Tintersection(_)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let mk_prop = |subtype_env: &subtype_env::T,
                                   _this_ty: Option<&Ty>,
                                   lhs: Lhs,
                                   rhs: Rhs,
                                   env: &mut Env| {
                        simplify(subtype_env, None, lhs, rhs, env)
                    };
                    common::simplify_union_l(
                        subtype_env,
                        this_ty,
                        mk_prop,
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
                (
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::Toption(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tintersection(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tintersection(tyl),
                ) => {
                    let r_super = get_reason(&ty_super).clone();
                    // t <: (t1 & ... & tn)
                    //   if and only if
                    // t <: t1 /\  ... /\ t <: tn
                    let mut res = tl::valid();
                    for ty_super in tyl {
                        let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
                            reason::prj_inter_super(r_super.clone(), r_super_prj)
                        });
                        res = and(env, res, |env| {
                            simplify(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &ty_sub,
                                },
                                Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                env,
                            )
                        });
                    }
                    res
                }
                // -- C-Bot-R -----------------------------------------------------------
                // Empty union encodes the bottom type nothing
                (Ty_::Tunion(tyl_sub), Ty_::Tunion(tyl_super))
                    if tyl_sub.is_empty() && tyl_super.is_empty() =>
                {
                    tl::valid()
                }
                (Ty_::Tunion(tyl), Ty_::Tunion(tys)) if tys.is_empty() => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let mk_prop = |subtype_env: &subtype_env::T,
                                   _this_ty: Option<&Ty>,
                                   lhs: Lhs,
                                   rhs: Rhs,
                                   env: &mut Env| {
                        simplify(subtype_env, None, lhs, rhs, env)
                    };
                    common::simplify_union_l(
                        subtype_env,
                        this_ty,
                        mk_prop,
                        |env: &Env, ty: Ty| {
                            env::update_reason(env, ty, |r_sub_prj| {
                                reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                            })
                        },
                        (sub_supportdyn, tyl),
                        rhs.clone(),
                        env,
                    )
                }
                (Ty_::Tintersection(tyl), Ty_::Tunion(tys)) if tys.is_empty() => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let mk_prop = |subtype_env: &subtype_env::T,
                                   _this_ty: Option<&Ty>,
                                   lhs: Lhs,
                                   rhs: Rhs,
                                   env: &mut Env| {
                        simplify(subtype_env, None, lhs, rhs, env)
                    };
                    // Otherwise use the incomplete common case which doesn't require inspection of the rhs
                    common::simplify_intersection_l(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        mk_prop,
                        |env: &Env, ty: Ty| {
                            env::update_reason(env, ty, |r_sub_prj| {
                                reason::prj_inter_sub(r_sub.clone(), r_sub_prj)
                            })
                        },
                        (sub_supportdyn, tyl),
                        rhs.clone(),
                        env,
                    )
                }
                (Ty_::Tnewtype(n, tyl, _), Ty_::Tunion(tys)) if tys.is_empty() => {
                    let r = get_reason(&ty_sub).clone();
                    let ty = t_utils::get_newtype_super(env, r.clone(), n, tyl);
                    let mk_prop = |subtype_env: &subtype_env::T,
                                   this_ty: Option<&Ty>,
                                   lhs: Lhs,
                                   rhs: Rhs,
                                   env: &mut Env| {
                        simplify(subtype_env, this_ty, lhs, rhs, env)
                    };
                    common::simplify_newtype_l(
                        subtype_env,
                        this_ty,
                        mk_prop,
                        (sub_supportdyn, r, n.clone(), ty),
                        rhs.clone(),
                        env,
                    )
                }
                (Ty_::Tgeneric(_), Ty_::Tunion(tys))
                    if tys.is_empty() && subtype_env.require_completeness =>
                {
                    mk_issubtype_prop(
                        sub_supportdyn,
                        subtype_env.is_dynamic_aware,
                        env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::LoclType(ty_super.clone()),
                    )
                }
                (Ty_::Tgeneric(name_sub), Ty_::Tunion(tys)) if tys.is_empty() => {
                    let r_generic = get_reason(&ty_sub).clone();
                    match visited_goals::try_add_visited_generic_sub(
                        &subtype_env.visited,
                        name_sub,
                        ty_super.clone(),
                    ) {
                        None => {
                            // If we've seen this type parameter before then we must have gone
                            // round a cycle so we fail
                            invalid(fail.clone(), env)
                        }
                        Some(new_visited) => {
                            let subtype_env =
                                subtype_env::set_visited(subtype_env.clone(), new_visited);

                            let mk_prop = |subtype_env: &subtype_env::T,
                                           this_ty: Option<&Ty>,
                                           lhs: Lhs,
                                           rhs: Rhs,
                                           env: &mut Env| {
                                simplify(subtype_env, this_ty, lhs, rhs, env)
                            };
                            common::simplify_generic_l(
                                &subtype_env,
                                this_ty,
                                fail.clone(),
                                mk_prop,
                                (sub_supportdyn, r_generic, name_sub.clone()),
                                Rhs {
                                    super_like,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                env,
                            )
                        }
                    }
                }
                (Ty_::Tdependent(dep_ty, ty), Ty_::Tunion(tys)) if tys.is_empty() => {
                    let r = get_reason(&ty_sub).clone();
                    let mk_prop = |subtype_env: &subtype_env::T,
                                   this_ty: Option<&Ty>,
                                   lhs: Lhs,
                                   rhs: Rhs,
                                   env: &mut Env| {
                        simplify(subtype_env, this_ty, lhs, rhs, env)
                    };
                    common::simplify_dependent_l(
                        subtype_env,
                        this_ty,
                        mk_prop,
                        (sub_supportdyn, r, *dep_ty, ty.clone()),
                        rhs.clone(),
                        env,
                    )
                }
                (Ty_::Tany(_), Ty_::Tunion(tys)) if tys.is_empty() && subtype_env.no_top_bottom => {
                    mk_issubtype_prop(
                        sub_supportdyn,
                        subtype_env.is_dynamic_aware,
                        env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::LoclType(ty_super.clone()),
                    )
                }
                (Ty_::Tany(_), Ty_::Tunion(tys)) if tys.is_empty() => valid(env),
                (Ty_::Tvar(_), Ty_::Tunion(tys)) if tys.is_empty() => mk_issubtype_prop(
                    sub_supportdyn,
                    subtype_env.is_dynamic_aware,
                    env,
                    InternalType::LoclType(ty_sub.clone()),
                    InternalType::LoclType(ty_super.clone()),
                ),
                (
                    Ty_::Tnonnull
                    | Ty_::Toption(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_),
                    Ty_::Tunion(tys),
                ) if tys.is_empty() => invalid(fail.clone(), env),
                // -- C-Union-R ---------------------------------------------------------
                (_, Ty_::Tunion(lty_supers)) => simplify_c_union_r(&s, lty_supers, env),
                // -- C-Top-R -----------------------------------------------------------
                // `Toption(Tnonnull)` encodes mixed, which is our top type
                (
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::Toption(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tunion(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tvar(_),
                    Ty_::Toption(ty_inner),
                ) if expands_to_nonnull(ty_inner, env) => valid(env),
                // -- C-Option-R --------------------------------------------------------
                // null is the type of null and is a subtype of any option type.
                (Ty_::Tprim(Tprim::Tnull), Ty_::Toption(_)) => valid(env),
                // ?ty_sub' <: ?ty_super' iff ty_sub' <: ?ty_super'. Reasoning:
                // If ?ty_sub' <: ?ty_super', then from ty_sub' <: ?ty_sub' (widening) and transitivity
                // of <: it follows that ty_sub' <: ?ty_super'.  Conversely, if ty_sub' <: ?ty_super', then
                // by covariance and idempotence of ?, we have ?ty_sub' <: ??ty_sub' <: ?ty_super'.
                // Therefore, this step preserves the set of solutions.
                (Ty_::Toption(ty_sub_prime), Ty_::Toption(lty_inner)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    let ty_sub_prime = env::update_reason(env, ty_sub_prime.clone(), |r_sub_prj| {
                        reason::prj_nullable_sub(r_sub, r_sub_prj)
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub_prime,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &mk((r_super, Ty_::Toption(lty_inner.clone()))),
                        },
                        env,
                    )
                }
                // If ty_sub <: ?ty_super' and ty_sub does not contain null then we
                // must also have ty_sub <: ty_super'.  The converse follows by
                // widening and transitivity.  Therefore, this step preserves the set
                // of solutions.
                (Ty_::Tintersection(_) | Ty_::Tunion(_), Ty_::Toption(lty_inner))
                    if t_utils::is_type_disjoint(env, &ty_sub, &make_type::null(reason::none())) =>
                {
                    let r_super = get_reason(&ty_super).clone();
                    let lty_inner = env::update_reason(env, lty_inner.clone(), |r_super_prj| {
                        reason::prj_nullable_super(r_super, r_super_prj)
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &lty_inner,
                        },
                        env,
                    )
                }
                // We do not want to decompose Toption for these cases
                (
                    Ty_::Tvar(_) | Ty_::Tunion(_) | Ty_::Tintersection(_),
                    Ty_::Toption(lty_inner),
                ) => {
                    let r_super = get_reason(&ty_super).clone();
                    default_subtype(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &mk((r_super, Ty_::Toption(lty_inner.clone()))),
                        },
                        env,
                    )
                }
                (Ty_::Tgeneric(_), Ty_::Toption(lty_inner))
                    if subtype_env.require_completeness =>
                {
                    let r_super = get_reason(&ty_super).clone();
                    // TODO(T69551141) handle type arguments ?
                    default_subtype(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &mk((r_super, Ty_::Toption(lty_inner.clone()))),
                        },
                        env,
                    )
                }
                // If t1 <: ?t2 and t1 is an abstract type constrained as t1',
                // then t1 <: t2 or t1' <: ?t2.  The converse is obviously
                // true as well.  We can fold the case where t1 is unconstrained
                // into the case analysis below.
                //
                // In the case where it's easy to determine that null isn't in t1,
                // we need only check t1 <: t2.
                (
                    Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tprim(Tprim::Tvoid),
                    Ty_::Toption(lty_inner),
                ) => {
                    let r_super = get_reason(&ty_super).clone();
                    let lty_inner = env::update_reason(env, lty_inner.clone(), |r_super_prj| {
                        reason::prj_nullable_super(r_super, r_super_prj)
                    });
                    // TODO(T69551141) handle type arguments?
                    if null_not_subtype(env, &ty_sub) {
                        simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_like,
                                super_supportdyn: false,
                                ty_super: &lty_inner,
                            },
                            env,
                        )
                    } else {
                        let p = simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_like,
                                super_supportdyn: false,
                                ty_super: &lty_inner,
                            },
                            env,
                        );
                        or(fail.clone(), env, p, |env| {
                            default_subtype(
                                subtype_env,
                                this_ty,
                                fail.clone(),
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &ty_sub,
                                },
                                Rhs {
                                    super_like,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                env,
                            )
                        })
                    }
                }
                (
                    Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Tany(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Toption(lty_inner),
                ) => {
                    let r_super = get_reason(&ty_super).clone();
                    let lty_inner = env::update_reason(env, lty_inner.clone(), |r_super_prj| {
                        reason::prj_nullable_super(r_super, r_super_prj)
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &lty_inner,
                        },
                        env,
                    )
                }
                // This is treating the option as a union, and using the sound, but incomplete,
                // t <: t1 | t2 to (t <: t1) || (t <: t2) reduction
                // TODO(T120921930): Don't do this if require_completeness is set.
                (Ty_::Tneg(_), Ty_::Toption(lty_inner)) => {
                    let r_super = get_reason(&ty_super).clone();
                    let lty_inner = env::update_reason(env, lty_inner.clone(), |r_super_prj| {
                        reason::prj_nullable_super(r_super, r_super_prj)
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &lty_inner,
                        },
                        env,
                    )
                }
                // -- C-Dep-R -----------------------------------------------------------
                (Ty_::Tdependent(d_sub, bound_sub), Ty_::Tdependent(d_sup, bound_sup))
                    if d_sub == d_sup =>
                {
                    simplify(
                        subtype_env,
                        this_ty.or(Some(&ty_sub)),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &bound_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &bound_sup,
                        },
                        env,
                    )
                }
                (Ty_::Tdependent(_, bound_sub), Ty_::Tdependent(..)) => simplify(
                    subtype_env,
                    this_ty.or(Some(&ty_sub)),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &bound_sub,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                (Ty_::Tclass((_, y), _, _), Ty_::Tdependent(_, bound_sup))
                    if expands_to_class(bound_sup, env) =>
                {
                    let r_sub = get_reason(&ty_sub).clone();
                    let id = class_id_exn(bound_sup, env);
                    let x = &id.1;

                    if is_final_and_invariant(env, x) {
                        // For final class C, there is no difference between `this as X` and `X`,
                        // and `expr<#n> as X` and `X`. But we need to take care with variant
                        // classes, since we can't statically guarantee their runtime type.
                        simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &bound_sup,
                            },
                            env,
                        )
                    } else {
                        let fail = if x == y {
                            let p = reason::to_pos(&r_sub);
                            let (pos_super, class_name) = id.clone();
                            subtype_env::fail_with_suffix(
                                subtype_env,
                                InternalType::LoclType(ty_sub.clone()),
                                InternalType::LoclType(ty_super.clone()),
                                secondary::T::ThisFinal {
                                    pos_super,
                                    class_name,
                                    pos_sub: p,
                                },
                            )
                        } else {
                            subtype_env::fail(
                                subtype_env,
                                InternalType::LoclType(ty_sub.clone()),
                                InternalType::LoclType(ty_super.clone()),
                            )
                        };
                        invalid(fail, env)
                    }
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tdependent(..),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Access-R --------------------------------------------------------
                (_, Ty_::Taccess(_)) => invalid(fail.clone(), env),
                // -- C-Generic-R -------------------------------------------------------
                (Ty_::Tgeneric(name_sub), Ty_::Tgeneric(name_super)) if name_sub == name_super => {
                    valid(env)
                }
                (Ty_::Tgeneric(name_sub), Ty_::Tgeneric(_))
                    if {
                        let (generic_lower_bounds, _other_lower_bounds) =
                            generic_lower_bounds(env, &ty_super);
                        generic_lower_bounds.contains(name_sub)
                    } =>
                {
                    valid(env)
                }
                // Ensure that higher-ranked type parameters don't escape their scope
                (Ty_::Tvar(tv_sub), Ty_::Tgeneric(tp_sup))
                    if env::rank_of_tparam(env, tp_sup) > env::rank_of_tvar(env, *tv_sub) =>
                {
                    let r_sub = get_reason(&ty_sub);
                    let r_super = get_reason(&ty_super);
                    let error = secondary::T::HigherRankTparamEscape {
                        tvar_pos: reason::to_pos(r_sub),
                        pos_with_generic: reason::to_pos(r_super),
                        generic_reason: r_super.clone(),
                        generic_name: Some(tp_sup.clone()),
                    };
                    let fail = subtype_env::fail_with_secondary_error(subtype_env, error);
                    invalid(fail, env)
                }
                // When decomposing subtypes for the purpose of adding bounds on generic
                // parameters to the context, (so seen_generic_params = None), leave
                // subtype so that the bounds get added
                (Ty_::Tvar(_) | Ty_::Tunion(_), Ty_::Tgeneric(_)) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                (
                    Ty_::Tany(_)
                    | Ty_::Toption(_)
                    | Ty_::Tnonnull
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tintersection(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tgeneric(_),
                ) if subtype_env.require_completeness => mk_issubtype_prop(
                    sub_supportdyn,
                    subtype_env.is_dynamic_aware,
                    env,
                    InternalType::LoclType(ty_sub.clone()),
                    InternalType::LoclType(ty_super.clone()),
                ),
                // When we have a shape splat <: an opaque type we lift that type into a
                // singleton shape splat so that any assignment of a type parameter is
                // consistent on both sides of the subtype proposition
                (Ty_::Tshape(shape_sub @ ShapeType::ShapeSplat(_)), Ty_::Tgeneric(_)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    simplify_subtype_shape_splat(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        (sub_supportdyn.is_some(), r_sub, shape_sub.clone()),
                        (
                            false,
                            r_super,
                            ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: vec![ty_super.clone()],
                            }),
                        ),
                    )
                }
                (Ty_::Tshape(shape_sub @ ShapeType::ShapeSplat(_)), Ty_::Tnewtype(n, _, _))
                    // [supportdyn] is itself a [Tnewtype] and has its own handling.
                    if n != sn::classes::SUPPORT_DYN && n != sn::classes::REPRESENTABLE_AS =>
                {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    simplify_subtype_shape_splat(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        (sub_supportdyn.is_some(), r_sub, shape_sub.clone()),
                        (
                            false,
                            r_super,
                            ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: vec![ty_super.clone()],
                            }),
                        ),
                    )
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Toption(_)
                    | Ty_::Tnonnull
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tintersection(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tgeneric(name_super),
                ) => simplify_c_generic_r(&s, name_super, env),
                (
                    Ty_::Tprim(
                        Tprim::Tint
                        | Tprim::Tbool
                        | Tprim::Tfloat
                        | Tprim::Tresource
                        | Tprim::Tnum
                        | Tprim::Tarraykey
                        | Tprim::Tnoreturn,
                    )
                    | Ty_::Tnonnull
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tnonnull,
                ) => valid(env),
                // supportdyn<t> <: nonnull iff t <: nonnull
                (Ty_::Tnewtype(name, tyargs, _), Ty_::Tnonnull)
                    if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN =>
                {
                    let r = get_reason(&ty_sub).clone();
                    let r_nonnull = get_reason(&ty_super).clone();
                    let upper_bound = &tyargs[0];
                    // TODO(mjt) update to be an asymm projection
                    let ty_sub = env::update_reason(env, upper_bound.clone(), |bound| {
                        reason::axiom_upper_bound(bound, r.clone(), name.clone())
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: Some(&r),
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &mk((r_nonnull, Ty_::Tnonnull)),
                        },
                        env,
                    )
                }
                // negations always contain null
                (Ty_::Tneg(_), Ty_::Tnonnull) => invalid(fail.clone(), env),
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tprim(Tprim::Tvoid | Tprim::Tnull)
                    | Ty_::Tvar(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..),
                    Ty_::Tnonnull,
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Dynamic-R -------------------------------------------------------
                (_, Ty_::Tdynamic(_))
                    if subtype_env.is_dynamic_aware
                        || tast::is_under_dynamic_assumptions(env.checked) =>
                {
                    simplify_c_dynamic_r(&s, env)
                }
                (_, Ty_::Tdynamic(_)) if typing_defs::is_dynamic(&ty_sub) => valid(env),
                (_, Ty_::Tdynamic(_)) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_supportdyn,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Prim-R ----------------------------------------------------------
                (Ty_::Tprim(Tprim::Tint | Tprim::Tfloat), Ty_::Tprim(Tprim::Tnum)) => valid(env),
                // class<T> <: string because of typename's bound
                (Ty_::TclassPtr(_), Ty_::Tprim(Tprim::Tarraykey))
                    if subtype_env.class_sub_classname =>
                {
                    valid(env)
                }
                (Ty_::TclassPtr(_), Ty_::Tclass((_, id), _, _))
                    if subtype_env.class_sub_classname && C_STRING == id =>
                {
                    valid(env)
                }
                (Ty_::Tprim(Tprim::Tint), Ty_::Tprim(Tprim::Tarraykey)) => valid(env),
                (Ty_::Tclass((_, id), _, _), Ty_::Tprim(Tprim::Tarraykey)) if C_STRING == id => {
                    valid(env)
                }
                (Ty_::Tprim(prim_sub), Ty_::Tprim(prim_sup)) if prim_sub == prim_sup => valid(env),
                (Ty_::Tprim(_), Ty_::Tprim(_)) => invalid(fail.clone(), env),
                (Ty_::Toption(arg_ty_sub), Ty_::Tprim(Tprim::Tnull)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let arg_ty_sub = env::update_reason(env, arg_ty_sub.clone(), |r_sub_prj| {
                        reason::prj_nullable_sub(r_sub, r_sub_prj)
                    });
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &arg_ty_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnonnull
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tprim(_),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Any-R -----------------------------------------------------------
                (Ty_::Tany(_), Ty_::Tany(_)) => valid(env),
                (Ty_::Tunion(_) | Ty_::Tintersection(_) | Ty_::Tvar(_), Ty_::Tany(_)) => {
                    default_subtype(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_supportdyn,
                            super_like,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                }
                (_, Ty_::Tany(_)) if subtype_env.no_top_bottom => mk_issubtype_prop(
                    sub_supportdyn,
                    subtype_env.is_dynamic_aware,
                    env,
                    InternalType::LoclType(ty_sub.clone()),
                    InternalType::LoclType(ty_super.clone()),
                ),
                (_, Ty_::Tany(_)) => valid(env),
                // -- C-Fun -------------------------------------------------------------
                (Ty_::Tfun(ft_sub), Ty_::Tfun(ft_super)) => {
                    simplify_c_fun(&s, ft_sub, ft_super, env)
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tfun(_),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_supportdyn,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // Tuple against tuple.
                (Ty_::Ttuple(t_sub), Ty_::Ttuple(t_super)) => {
                    let r_sub = get_reason(&ty_sub);
                    let r_super = get_reason(&ty_super);
                    // First test the required components of the tuples, pointwise
                    simplify_elems_req(
                        &s,
                        (r_sub, t_sub),
                        (r_super, t_super),
                        &t_sub.required,
                        &t_super.required,
                        env,
                    )
                }
                (_, Ty_::Ttuple(_)) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_supportdyn,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // Keep this before the shape-splat case below: constraint decomposition must
                // retain [T <: shape(...)] so [T]'s declared upper bound is recorded.
                (Ty_::Tgeneric(_), Ty_::Tshape(ShapeType::ShapeSplat(_)))
                    if subtype_env.require_completeness =>
                {
                    mk_issubtype_prop(
                        sub_supportdyn,
                        subtype_env.is_dynamic_aware,
                        env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::LoclType(ty_super.clone()),
                    )
                }
                // As above, wrap a opaque types in a singleton splat when subtyping
                // against a shape splat to ensure all assignments of type parameters
                // are consistent
                (
                    Ty_::Tgeneric(_) | Ty_::Tnewtype(..),
                    Ty_::Tshape(shape_super @ ShapeType::ShapeSplat(_)),
                ) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    simplify_subtype_shape_splat(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        (
                            sub_supportdyn.is_some(),
                            r_sub,
                            ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: vec![ty_sub.clone()],
                            }),
                        ),
                        (super_supportdyn, r_super, shape_super.clone()),
                    )
                }
                // -- C-Shape-R ---------------------------------------------------------
                (Ty_::Tnewtype(name_sub, tyl, _), Ty_::Tshape(_)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let ty_bound_sub =
                        t_utils::get_newtype_super(env, r_sub.clone(), name_sub, tyl);
                    common::simplify_newtype_l(
                        subtype_env,
                        this_ty,
                        simplify,
                        (sub_supportdyn, r_sub, name_sub.clone(), ty_bound_sub),
                        rhs.clone(),
                        env,
                    )
                }
                (
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: origin_sub,
                        unknown_value: shape_kind_sub,
                        fields: fdm_sub,
                    })),
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: origin_super,
                        unknown_value: shape_kind_super,
                        fields: fdm_super,
                    })),
                ) => {
                    if same_type_origin(origin_super, origin_sub) {
                        // Fast path for shape types: if they have the same origin,
                        // they are equal type.
                        valid(env)
                    } else {
                        let r_sub = get_reason(&ty_sub).clone();
                        let r_super = get_reason(&ty_super).clone();
                        let sub_supportdyn = sub_supportdyn.is_some();
                        simplify_subtype_shape(
                            subtype_env,
                            env,
                            this_ty,
                            super_like,
                            (sub_supportdyn, r_sub, shape_kind_sub.clone(), fdm_sub),
                            (super_supportdyn, r_super, shape_kind_super.clone(), fdm_super),
                        )
                    }
                }
                (Ty_::Tshape(shape_sub), Ty_::Tshape(shape_super)) => {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_super = get_reason(&ty_super).clone();
                    let sub_supportdyn = sub_supportdyn.is_some();
                    simplify_subtype_shape_splat(
                        subtype_env,
                        env,
                        this_ty,
                        super_like,
                        (sub_supportdyn, r_sub, shape_sub.clone()),
                        (super_supportdyn, r_super, shape_super.clone()),
                    )
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Ttuple(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tshape(_),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_supportdyn,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Vec-or-Dict-R ---------------------------------------------------
                (
                    Ty_::TvecOrDict(lty_key_sub, lty_val_sub),
                    Ty_::TvecOrDict(lty_key_sup, lty_val_sup),
                ) => {
                    let lty_val_sup = sd::liken(super_like, env, lty_val_sup.clone());
                    let lty_key_sup = sd::liken(super_like, env, lty_key_sup.clone());
                    let p = simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &lty_key_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &lty_key_sup,
                        },
                        env,
                    );
                    and(env, p, |env| {
                        simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &lty_val_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &lty_val_sup,
                            },
                            env,
                        )
                    })
                }
                (Ty_::Tclass((_, n), _, tys), Ty_::TvecOrDict(lty_key_sup, lty_val_sup))
                    if tys.len() == 2 && n == sn::collections::DICT =>
                {
                    let (lty_key_sub, lty_val_sub) = (&tys[0], &tys[1]);
                    let lty_val_sup = sd::liken(super_like, env, lty_val_sup.clone());
                    let lty_key_sup = sd::liken(super_like, env, lty_key_sup.clone());
                    let p = simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &lty_key_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &lty_key_sup,
                        },
                        env,
                    );
                    and(env, p, |env| {
                        simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &lty_val_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &lty_val_sup,
                            },
                            env,
                        )
                    })
                }
                (Ty_::Tclass((_, n), _, tys), Ty_::TvecOrDict(lty_key_sup, lty_val_sup))
                    if tys.len() == 1 && n == sn::collections::VEC =>
                {
                    let lty_val_sub = &tys[0];
                    let pos = get_pos(&ty_sub);
                    let lty_key_sub = make_type::int(reason::idx_vector_from_decl(pos));
                    let lty_val_sup = sd::liken(super_like, env, lty_val_sup.clone());
                    let lty_key_sup = sd::liken(super_like, env, lty_key_sup.clone());
                    let p = simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &lty_key_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &lty_key_sup,
                        },
                        env,
                    );
                    and(env, p, |env| {
                        simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &lty_val_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &lty_val_sup,
                            },
                            env,
                        )
                    })
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tclass(..)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                    Ty_::TvecOrDict(..),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-Newtype-R -------------------------------------------------------
                // x <: supportdyn<u>
                (_, Ty_::Tnewtype(name_super, tys, bound_super))
                    if tys.len() == 1 && name_super == sn::classes::SUPPORT_DYN =>
                {
                    simplify_c_newtype_r_supportdyn(&s, &tys[0], bound_super, env)
                }
                // -- C-RepresentableAs-R -------------------------------------------------
                // x <: RepresentableAs<u>
                (_, Ty_::Tnewtype(name_super, tys, _bound_super))
                    if tys.len() == 1 && name_super == sn::classes::REPRESENTABLE_AS =>
                {
                    simplify_c_representable_as_r(&s, &tys[0], env)
                }
                // #A <: \\HH\\EnumClass\\Label<u, v>
                (Ty_::Tlabel(name), Ty_::Tnewtype(label_kind, tys, _))
                    if tys.len() == 2 && label_kind == sn::classes::ENUM_CLASS_LABEL =>
                {
                    let r_sub = get_reason(&ty_sub).clone();
                    let r_sup = get_reason(&ty_super).clone();
                    let (ty_from, ty_to) = (&tys[0], &tys[1]);
                    let ty = sd::liken(
                        super_like,
                        env,
                        mk((
                            r_sup,
                            Ty_::Tnewtype(
                                sn::classes::MEMBER_OF.to_string(),
                                vec![ty_from.clone(), ty_to.clone()],
                                ty_to.clone(),
                            ),
                        )),
                    );
                    has_const::simplify(
                        subtype_env,
                        Some(ty_from),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_from,
                        },
                        has_const::Rhs {
                            reason_super: r_sub,
                            name: name.clone(),
                            ty,
                        },
                        env,
                    )
                }
                // When flag enabled, class<T> <: classname<T>, which is bounded by
                // typename<T>
                (Ty_::TclassPtr(ty_sub_inner), Ty_::Tnewtype(name, tys, _))
                    if tys.len() == 1
                        && subtype_env.class_sub_classname
                        && (name == sn::classes::CLASS_NAME || name == sn::classes::TYPE_NAME) =>
                {
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &ty_sub_inner,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &tys[0],
                        },
                        env,
                    )
                }
                (Ty_::TclassPtr(ty_sub_inner), Ty_::Tnewtype(name, tys, _))
                    if tys.len() == 1 && name == sn::classes::CLASS_OR_CLASSNAME =>
                {
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &ty_sub_inner,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &tys[0],
                        },
                        env,
                    )
                }
                (Ty_::Tnewtype(name_sub, tys_sub, _), Ty_::Tnewtype(name_super, tys_super, _))
                    if tys_sub.len() == 1
                        && tys_super.len() == 1
                        && name_super == sn::classes::CLASS_OR_CLASSNAME
                        && name_sub == sn::classes::CLASS_NAME =>
                {
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &tys_sub[0],
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &tys_super[0],
                        },
                        env,
                    )
                }
                (_, Ty_::Tnewtype(name_super, lty_supers, _bound_super)) => {
                    simplify_c_newtype_r(&s, name_super, lty_supers, env)
                }
                // -- C-Neg-R -----------------------------------------------------------
                (
                    _,
                    Ty_::Tneg(TypePredicate(
                        r_pred,
                        TypePredicate_::IsTag(TypeTag::ClassTag(c_super, c_super_args)),
                    )),
                ) => {
                    let r_super = get_reason(&ty_super).clone();
                    match get_node(&ty_sub) {
                        Ty_::Tneg(TypePredicate(
                            _,
                            TypePredicate_::IsTag(TypeTag::ClassTag(c_sub, c_sub_args)),
                        )) if c_sub_args.is_empty() => {
                            if t_utils::is_sub_class_refl(env, c_super, c_sub) {
                                valid(env)
                            } else {
                                invalid(fail.clone(), env)
                            }
                        }
                        Ty_::Tclass((_, c_sub), ex, _) => {
                            if subtype_negation::is_class_disjoint(
                                env,
                                c_sub,
                                ex,
                                c_super,
                                &nonexact(),
                            ) {
                                valid(env)
                            } else {
                                invalid(fail.clone(), env)
                            }
                        }
                        // Functions can be instances of the Closure class
                        Ty_::Tfun(_) if C_CLOSURE == c_super => invalid(fail.clone(), env),
                        Ty_::Tprim(Tprim::Tarraykey) if C_STRING == c_super => {
                            invalid(fail.clone(), env)
                        }
                        // All of these are definitely disjoint from class types
                        Ty_::Tfun(_) | Ty_::Ttuple(_) | Ty_::Tshape(_) | Ty_::Tprim(_) => {
                            valid(env)
                        }
                        _ => default_subtype(
                            subtype_env,
                            this_ty,
                            fail.clone(),
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_like,
                                super_supportdyn: false,
                                ty_super: &mk((
                                    r_super,
                                    Ty_::Tneg(TypePredicate(
                                        r_pred.clone(),
                                        TypePredicate_::IsTag(TypeTag::ClassTag(
                                            c_super.clone(),
                                            c_super_args.clone(),
                                        )),
                                    )),
                                )),
                            },
                            env,
                        ),
                    }
                }
                (_, Ty_::Tneg(predicate)) => {
                    let reason_super = get_reason(&ty_super).clone();
                    match get_node(&ty_sub) {
                        Ty_::Tvar(_) => mk_issubtype_prop(
                            sub_supportdyn,
                            subtype_env.is_dynamic_aware,
                            env,
                            InternalType::LoclType(ty_sub.clone()),
                            InternalType::LoclType(ty_super.clone()),
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
                                rhs.clone(),
                                env,
                            )
                        }
                        _ => {
                            // T < !P iff left < nothing and span & P < nothing
                            // However, just do span < nothing since we know that
                            // if span is not nothing, it isn't known to be disjoint from P.
                            // This also avoids the need to do special handling of dynamic
                            // in the union case above to avoid dynamic & P
                            let partition =
                                typing_refinement::partition_ty(env, &ty_sub, predicate);
                            let simplify_subtype = |tyl: &[Ty], ty_super: Ty, env: &mut Env| {
                                simplify(
                                    subtype_env,
                                    this_ty,
                                    Lhs {
                                        sub_supportdyn,
                                        ty_sub: &make_type::intersection(
                                            reason_super.clone(),
                                            tyl.to_vec(),
                                        ),
                                    },
                                    Rhs {
                                        super_supportdyn: false,
                                        super_like,
                                        ty_super: &ty_super,
                                    },
                                    env,
                                )
                            };
                            let nothing = make_type::nothing(reason_super.clone());
                            // `partition.left @ partition.span`
                            let mut res = tl::valid();
                            for tyl in partition.left.iter().chain(partition.span.iter()) {
                                res = and(env, res, |env| {
                                    simplify_subtype(tyl, nothing.clone(), env)
                                });
                            }
                            res
                        }
                    }
                }
                // -- C-Class-R ---------------------------------------------------------
                // class refinement
                //   x <: A with type T = y <=> x <: A && x <: has_type_member(T, y)
                (_, Ty_::Tclass(class_id_super, Exact::Nonexact(cr_super), tyargs_super))
                    if (!class_refinement::is_empty(cr_super))
                        && (subtype_env.require_soundness
                            // To deal with refinements, the code below generates a
                            // constraint type. That is currently not supported when
                            // require_soundness is not set (see below in the function
                            // decompose_subtype_add_prop). Consequently, if soundness
                            // is not required, we treat the refinement information
                            // only if we know for sure that we can discharge it on
                            // the spot; e.g., when ety_sub is a class-ish. This
                            // limits the information lost by skipping refinements.
                            || t_utils::is_class(&ty_sub)) =>
                {
                    simplify_c_class_r_refinement(&s, class_id_super, cr_super, tyargs_super, env)
                }
                (
                    _,
                    Ty_::Tclass(
                        (_pos_super, class_nm_super),
                        exact_super,
                        tyargs_super,
                    ),
                ) => simplify_c_class_r(&s, class_nm_super, exact_super, tyargs_super, env),
                // -- C-Label-R ----------------------------------------------------------
                (Ty_::Tlabel(sub_name), Ty_::Tlabel(sup_name)) => {
                    if sub_name == sup_name {
                        valid(env)
                    } else {
                        invalid(fail.clone(), env)
                    }
                }
                (
                    Ty_::Tany(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Taccess(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnonnull
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Tclass(..)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tneg(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tvar(_)
                    | Ty_::TclassPtr(_),
                    Ty_::Tlabel(_),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
                // -- C-ClassPtr-R -----------------------------------------------------
                (Ty_::TclassPtr(ty_sub_inner), Ty_::TclassPtr(ty_super_inner)) => simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_sub_inner,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super_inner,
                    },
                    env,
                ),
                (
                    Ty_::Tany(_)
                    | Ty_::Tunion(_)
                    | Ty_::Toption(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tprim(_)
                    | Ty_::Tnonnull
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::Ttuple(_)
                    | Ty_::Tshape(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tdependent(..)
                    | Ty_::Tvar(_)
                    | Ty_::Tlabel(_)
                    | Ty_::Tfun(_),
                    Ty_::TclassPtr(_),
                ) => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_supportdyn,
                        super_like,
                        ty_super: &ty_super,
                    },
                    env,
                ),
            }
        }
    }
}

/// `simplify_`, arm `(_, (r_super, Tvar var_super_id))` (C-Var-R) for the
/// subtypes that are not unions or options.
fn simplify_c_var_r(s: &Scope<'_>, var_super_id: tvid::T, env: &mut Env) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        ..
    } = *s;
    let r_sub = get_reason(ty_sub);
    let r_super = get_reason(ty_super);
    // Ensure that higher-ranked type parameters don't escape their scope
    let tvar_rank = env::rank_of_tvar(env, var_super_id);
    match check_rank(env, ty_sub, tvar_rank) {
        Some((generic_reason, generic_name)) => {
            let error = secondary::T::HigherRankTparamEscape {
                tvar_pos: reason::to_pos(r_super),
                pos_with_generic: reason::to_pos(r_sub),
                generic_reason,
                generic_name,
            };
            let fail = subtype_env::fail_with_secondary_error(subtype_env, error);
            invalid(fail, env)
        }
        _ => {
            let simplified_sub_ty = typing_solver_utils::remove_tyvar_from_lower_bound(
                env,
                var_super_id,
                InternalType::LoclType(ty_sub.clone()),
            );
            match simplified_sub_ty {
                InternalType::LoclType(ref simplified_sub_ty)
                // Better than checking nothing like this might be to change
                // remove_tyvar_from_lower_bound to return an Option to distinguish
                // whether a simplification was actually done.
                // And then we can recursively do a subtype check to check this.
                    if ty_equal(None, simplified_sub_ty, &make_type::nothing(reason::none())) =>
                {
                    valid(env)
                }
                _ => match subtype_env.is_dynamic_aware {
                    true => mk_issubtype_prop(
                        sub_supportdyn,
                        true,
                        env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::LoclType(ty_super.clone()),
                    ),
                    false => {
                        if super_like {
                            let ty_sub = typing_dynamic::strip_covariant_like(env, ty_sub.clone());
                            simplify(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &ty_sub,
                                },
                                Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &ty_super,
                                },
                                env,
                            )
                        } else {
                            mk_issubtype_prop(
                                sub_supportdyn,
                                subtype_env.is_dynamic_aware,
                                env,
                                InternalType::LoclType(ty_sub.clone()),
                                InternalType::LoclType(ty_super.clone()),
                            )
                        }
                    }
                },
            }
        }
    }
}

/// `simplify_`, arm `(_, (r_super, Tunion lty_supers))` (C-Union-R).
fn simplify_c_union_r(s: &Scope<'_>, lty_supers: &[Ty], env: &mut Env) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        lhs,
        rhs,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    let r_super = get_reason(ty_super).clone();
    match get_node(ty_sub) {
        Ty_::Tunion(ty_subs) => {
            let r_sub = get_reason(ty_sub).clone();
            let mk_prop =
                |subtype_env: &subtype_env::T,
                 _this_ty: Option<&Ty>,
                 lhs: Lhs,
                 rhs: Rhs,
                 env: &mut Env| { simplify(subtype_env, None, lhs, rhs, env) };
            common::simplify_union_l(
                subtype_env,
                this_ty,
                mk_prop,
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
        Ty_::Tvar(_) if subtype_env.is_dynamic_aware => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            InternalType::LoclType(ty_super.clone()),
        ),
        Ty_::Tvar(id) => {
            let id = *id;
            // For subtyping queries of the form
            //
            //   Tvar #id <: (Tvar #id | ...)
            //
            // `remove_tyvar_from_upper_bound` simplifies the union to
            // `mixed`. This indicates that the query is discharged. If we find
            // any other upper bound, we leave the subtyping query as it is.
            let simplified_super_ty = typing_solver_utils::remove_tyvar_from_upper_bound(
                env,
                id,
                InternalType::LoclType(ty_super.clone()),
            );
            // If the type is already in the upper bounds of the type variable,
            // then we already know that this subtype assertion is valid
            if ity_set::mem(&simplified_super_ty, &env::get_tyvar_upper_bounds(env, id)) {
                valid(env)
            } else {
                // `ty_equal simplified_super_ty (MakeType.mixed Reason.none)`, which
                // holds for `?nonnull` alone (see `is_mixed_node`), without building it.
                match simplified_super_ty {
                    InternalType::LoclType(ref simplified_super_ty)
                        if is_mixed_node(simplified_super_ty) =>
                    {
                        valid(env)
                    }
                    _ => mk_issubtype_prop(
                        sub_supportdyn,
                        subtype_env.is_dynamic_aware,
                        env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::LoclType(ty_super.clone()),
                    ),
                }
            }
        }
        Ty_::Tgeneric(_) if subtype_env.require_completeness => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            InternalType::LoclType(ty_super.clone()),
        ),
        // Num is not atomic: it is equivalent to int|float. The rule below relies
        // on ty_sub not being a union e.g. consider num <: arraykey | float, so
        // we break out num first.
        Ty_::Tprim(Tprim::Tnum) => {
            let r = get_reason(ty_sub).clone();
            let r = reason::prj_num_sub(r.clone(), r);
            let ty_float = make_type::float(r.clone());
            let ty_int = make_type::int(r);
            let p = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &ty_float,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            and(env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_int,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            })
        }
        // Likewise, reduce nullable on left to a union
        Ty_::Toption(ty) => {
            let r = get_reason(ty_sub).clone();
            let r = reason::prj_nullable_sub(r.clone(), r);
            let ty_null = make_type::null(r.clone());
            let prop_null = |env: &mut Env| {
                let prop = simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_null,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                );
                if_unsat(|env| invalid(fail.clone(), env), env, prop)
            };
            let ty = env::update_reason(env, ty.clone(), |r_sub_prj| {
                reason::prj_nullable_sub(r.clone(), r_sub_prj)
            });
            let p = prop_null(env);
            and(env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            })
        }
        Ty_::Tintersection(tyl) => {
            let r_sub = get_reason(ty_sub).clone();
            // First try to rewrite
            //   _ & ... & !t & _ <: _ | ... | _ => _ & ... & _ <: _ | ... | t | _
            //
            // The second branch matches without binding the environment that
            // `find_type_with_exact_negation` returns: it goes on with the
            // environment from before (and the original `tyl`).
            match subtype_negation::find_type_with_exact_negation_opt(env, tyl) {
                Some((non_ty, tyl)) => {
                    let ty_super = t_utils::union(env, None, None, ty_super.clone(), non_ty);
                    let ty_sub = make_type::intersection(r_sub, tyl);
                    let lhs = Lhs {
                        ty_sub: &ty_sub,
                        ..lhs
                    };
                    let rhs = Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    };
                    simplify(subtype_env, this_ty, lhs, rhs, env)
                }
                None => {
                    // `let ( ||| ) = ( ||| ) ~fail`
                    let simplify_super_intersection =
                        |env: &mut Env, tyl_sub: &[Ty], ty_super: Ty| {
                            // It's sound to reduce t1 & t2 <: t to (t1 <: t) || (t2 <: t), but
                            // not complete.
                            // TODO(T120921930): Don't do this if require_completeness is set.
                            let mut res = tl::invalid(fail.get());
                            for ty_sub in tyl_sub {
                                res = or(fail.clone(), env, res, |env| {
                                    simplify(
                                        subtype_env,
                                        this_ty,
                                        Lhs {
                                            sub_supportdyn,
                                            ty_sub: &ty_sub,
                                        },
                                        Rhs {
                                            super_like: false,
                                            super_supportdyn: false,
                                            ty_super: &ty_super,
                                        },
                                        env,
                                    )
                                });
                            }
                            res
                        };
                    // Heuristicky logic to decide whether to "break" the intersection
                    // or the union first, based on observing that the following cases often occur:
                    //   - A & B <: (A & B) | C
                    //     In which case we want to "break" the union on the right first
                    //     in order to have the following recursive calls :
                    //         A & B <: A & B
                    //         A & B <: C
                    //   - A & (B | C) <: B | C
                    //     In which case we want to "break" the intersection on the left first
                    //     in order to have the following recursive calls:
                    //         A <: B | C
                    //         B | C <: B | C
                    // If there is a type variable in the union, then generally it's helpful to
                    // break the union apart.
                    if lty_supers.iter().any(|t| {
                        t_utils::is_tintersection(env, t)
                            || t_utils::is_opt_tyvar(env, t)
                            || t_utils::is_tyvar(env, t)
                    }) {
                        simplify_sub_union(
                            subtype_env,
                            sub_supportdyn,
                            this_ty,
                            super_like,
                            fail.clone(),
                            &ty_sub,
                            (r_super, lty_supers),
                            env,
                        )
                    } else if tyl.iter().any(|t| t_utils::is_tunion(env, t)) {
                        simplify_super_intersection(
                            env,
                            tyl,
                            mk((r_super, Ty_::Tunion(lty_supers.to_vec()))),
                        )
                    } else {
                        simplify_sub_union(
                            subtype_env,
                            sub_supportdyn,
                            this_ty,
                            super_like,
                            fail.clone(),
                            &ty_sub,
                            (r_super, lty_supers),
                            env,
                        )
                    }
                }
            }
        }
        Ty_::Tany(_)
        | Ty_::Tprim(_)
        | Ty_::Tnonnull
        | Ty_::Tdynamic(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tgeneric(_)
        | Ty_::TvecOrDict(..)
        | Ty_::Taccess(_)
        | Ty_::Tnewtype(..)
        | Ty_::Tdependent(..)
        | Ty_::Tclass(..)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_)
        | Ty_::TclassPtr(_) => simplify_sub_union(
            subtype_env,
            sub_supportdyn,
            this_ty,
            super_like,
            fail.clone(),
            &ty_sub,
            (r_super, lty_supers),
            env,
        ),
    }
}

/// `simplify_`, arm `(_, (r_super, Tgeneric name_super))` (C-Generic-R) once
/// the other cases with a generic supertype are excluded.
fn simplify_c_generic_r(s: &Scope<'_>, name_super: &str, env: &mut Env) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    let r_super = get_reason(ty_super).clone();
    // If we've seen this type parameter before then we must have gone
    // round a cycle so we fail
    match visited_goals::try_add_visited_generic_super(
        &subtype_env.visited,
        ty_sub.clone(),
        name_super,
    ) {
        None => invalid(fail.clone(), env),
        Some(new_visited) => {
            let (_generic_lower_bounds, other_lower_bounds) = generic_lower_bounds(env, ty_super);
            let subtype_env = &subtype_env::set_visited(subtype_env.clone(), new_visited);

            // Collect all the lower bounds ("super" constraints) on the
            // generic parameter, and check ty_sub against each of them in turn
            // until one of them succeeds
            //
            // `let rec aux lower_bounds ~env ~errs ~props`, as a loop. `errs`
            // and `props` are OCaml lists built by consing: here they are
            // built at the end of the vectors, which are reversed at the end.
            let aux = |lower_bounds: Vec<Ty>,
                       env: &mut Env,
                       mut errs: Vec<Option<typing_error::T>>,
                       mut props: Vec<tl::SubtypeProp>| {
                for lower_bound in lower_bounds {
                    let lower_bound = env::update_reason(env, lower_bound, |bound| {
                        reason::axiom_lower_bound(bound, r_super.clone())
                    });
                    let prop = simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &lower_bound,
                        },
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
                // `[]`
                let prop = default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                );
                if tl::is_valid(&prop) {
                    prop
                } else {
                    match tl::get_error_if_unsat(&prop) {
                        Some(err) => errs.push(err),
                        _ => props.push(prop),
                    }
                    // (`fail`, the first error: see the call of `aux`.)
                    errs[0] = fail.get();
                    errs.reverse();
                    props.reverse();
                    let err = typing_error::intersect_opt(errs.into_iter().flatten().collect());
                    tl::SubtypeProp::Disj(err, props)
                }
            };

            // Turn error into a generic error about the type parameter
            // (`[fail]`: `fail` is put first when the disjunction is built,
            // so that it is not built when a bound gives a valid proposition.)
            let lower_bounds = typing_set::elements(&other_lower_bounds);
            aux(lower_bounds, env, vec![None], vec![])
        }
    }
}

/// `simplify_`, arm `(_, (r_dynamic, Tdynamic _)) when
/// subtype_env.is_dynamic_aware || Tast.is_under_dynamic_assumptions
/// env.checked` (C-Dynamic-R).
fn simplify_c_dynamic_r(s: &Scope<'_>, env: &mut Env) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    // Not in the OCaml (typing_subtype.ml, C-Dynamic-R of `simplify_`), which
    // simplifies `t <: dynamic` every time: a shape (alias origin) or closed
    // class type found to be a subtype of `dynamic` before, in the same
    // context, is answered from `dynamic_memo` (its module doc says why the
    // answer cannot change). `dynamic` with a type variable collects bounds,
    // so it is not answered from memory.
    let memo = if sub_supportdyn.is_none() && matches!(get_node(ty_super), Ty_::Tdynamic(None)) {
        crate::typing_subtype::dynamic_memo::query(subtype_env, this_ty, env, ty_sub)
    } else {
        crate::typing_subtype::dynamic_memo::Query::No
    };
    let memo = match memo {
        crate::typing_subtype::dynamic_memo::Query::Valid => return valid(env),
        crate::typing_subtype::dynamic_memo::Query::No => None,
        crate::typing_subtype::dynamic_memo::Query::Unknown(recorder) => Some(recorder),
    };
    let r_dynamic = get_reason(ty_super).clone();
    // The OCaml builds `dyn_`, `dynamic_part` and `ty_name` (lazy values,
    // without effects until forced) and `postprocess_fail` before the match.
    // The error is needed only if the proposition is unsatisfiable (5% of
    // the calls on the benchmark sample) and there is a callback: it is
    // built then, from the same values. The lazy values print in the
    // environment of this point, which is kept for them (a copy of the
    // handle, shared by the two); the position comes from the reason, which
    // does not change.
    let lazy_env = subtype_env.on_error.as_ref().map(|_| env.clone());
    let postprocess_fail = |lazy_env: Option<Env>| {
        lazy_env.map(|lazy_env| {
            let on_error = subtype_env.on_error.clone().unwrap();
            let pos = reason::to_pos(get_reason(ty_sub));
            let lazy_env = Rc::new(lazy_env);
            let dyn_ = {
                let env = Rc::clone(&lazy_env);
                let ty_super = ty_super.clone();
                Lazy::new(move || {
                    pretty::describe_ty_super(false, &env, &InternalType::LoclType(ty_super))
                })
            };
            let dynamic_part = {
                let r_dynamic = r_dynamic.clone();
                dyn_.map(move |dyn_: &String| {
                    reason::to_string(&("Expected ".to_string() + dyn_), &r_dynamic)
                        .into_iter()
                        .map(|(p, s)| Message(p, s.into()))
                        .collect::<Vec<Message<_>>>()
                })
            };
            let ty_name = {
                let env = Rc::clone(&lazy_env);
                let ty_sub = ty_sub.clone();
                Lazy::new(move || {
                    pretty::describe_ty_default(&env, &InternalType::LoclType(ty_sub))
                })
            };
            typing_error::apply_reasons(
                secondary::T::NotSubDynamic {
                    pos,
                    ty_name,
                    dynamic_part,
                },
                on_error,
            )
        })
    };
    let prop = if sub_supportdyn.is_some() {
        valid(env)
    } else {
        match get_node(ty_sub) {
            Ty_::Tlabel(_)
            | Ty_::Tany(_)
            | Ty_::Tprim(
                Tprim::Tint
                | Tprim::Tbool
                | Tprim::Tfloat
                | Tprim::Tnum
                | Tprim::Tarraykey
                | Tprim::Tvoid
                | Tprim::Tnoreturn
                | Tprim::Tresource,
            ) => valid(env),
            Ty_::Tnewtype(name_sub, tyargs, _)
                if tyargs.len() == 1 && name_sub == sn::classes::SUPPORT_DYN =>
            {
                valid(env)
            }
            Ty_::Tnewtype(name_sub, _, _) if name_sub == sn::classes::ENUM_CLASS_LABEL => {
                valid(env)
            }
            // class_or_classname<T> <D: dynamic, mirroring class<T>: valid by
            // exposure to string when class_sub_classname is set, otherwise valid
            // when the type argument is itself <D: dynamic. Without an explicit arm
            // it falls through to the generic Tnewtype case below, which uses the
            // `as nonnull` bound and so fails.
            Ty_::Tnewtype(name_sub, _, _)
                if name_sub == sn::classes::CLASS_OR_CLASSNAME
                    && subtype_env.class_sub_classname =>
            {
                valid(env)
            }
            Ty_::Tnewtype(name_sub, tys, _)
                if tys.len() == 1 && name_sub == sn::classes::CLASS_OR_CLASSNAME =>
            {
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &tys[0],
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            }
            Ty_::Toption(ty) => match get_node(ty) {
                // Special case mixed <: dynamic for better error message
                Ty_::Tnonnull => invalid(fail.clone(), env),
                _ => {
                    let r_sub = get_reason(ty_sub).clone();
                    let ty = env::update_reason(env, ty.clone(), |r_sub_prj| {
                        reason::prj_nullable_sub(r_sub, r_sub_prj)
                    });
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                }
            },
            Ty_::Tdynamic(_) | Ty_::Tprim(Tprim::Tnull) => valid(env),
            Ty_::Tnonnull
            | Ty_::Tvar(_)
            | Ty_::Tnewtype(..)
            | Ty_::Tdependent(..)
            | Ty_::Taccess(_)
            | Ty_::Tunion(_)
            | Ty_::Tintersection(_)
            | Ty_::Tgeneric(_)
            | Ty_::Tneg(_) => default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            ),
            Ty_::TvecOrDict(_, ty) => simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            ),
            Ty_::Tfun(ft_sub) => {
                let r_sub = get_reason(ty_sub).clone();
                if get_ft_support_dynamic_type(ft_sub) {
                    valid(env)
                } else {
                    // Special case of function type subtype dynamic.
                    //   (function(ty1,...,tyn):ty <: supportdyn<nonnull>)
                    //   iff
                    //   dynamic <D: ty1 & ... & dynamic <D: tyn & ty <D: dynamic
                    //
                    // Contravariant subtyping on parameters: `param_props`,
                    // applied to the environment below.
                    //
                    // Finally do covariant subtyping on return type
                    let ret_ty_sub = env::update_reason(env, ft_sub.ret.clone(), |r_sub_prj| {
                        reason::prj_fn_ret(r_sub.clone(), r_sub_prj, r_dynamic.clone())
                    });
                    let param_props = simplify_supertype_params_with_variadic(
                        subtype_env,
                        (r_sub.clone(), 0, &ft_sub.params),
                        (r_dynamic.clone(), 0, ty_super.clone()),
                        env,
                    );
                    and(env, param_props, |env| {
                        simplify(
                            subtype_env,
                            None,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ret_ty_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &ty_super,
                            },
                            env,
                        )
                    })
                }
            }
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            }) => {
                let extras: Vec<Ty> = match t_extra {
                    TupleExtra::Tvariadic(t_variadic) => std::iter::once(t_variadic.clone())
                        .chain(t_optional.iter().cloned())
                        .collect(),
                    TupleExtra::Tsplat(t_splat) => vec![t_splat.clone()],
                };
                // `extras @ t_required`
                let mut res = tl::valid();
                for ty_sub in extras.iter().chain(t_required.iter()) {
                    res = and(env, res, |env| {
                        simplify(
                            subtype_env,
                            None,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &ty_sub,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &ty_super,
                            },
                            env,
                        )
                    });
                }
                res
            }
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: unknown_fields_type,
                fields: sftl,
            })) => {
                // `TShapeMap.values sftl` is `Wrapped_map.values`, `fold (fun _ v
                // acc -> v :: acc) m []`: in decreasing order of the keys.
                let mut res = tl::valid();
                for sft in sftl.values().rev() {
                    res = and(env, res, |env| {
                        simplify(
                            subtype_env,
                            None,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &sft.ty,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &ty_super,
                            },
                            env,
                        )
                    });
                }
                and(env, res, |env| {
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &unknown_fields_type,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                })
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                // Each element of the splat must be <: dynamic
                let mut res = valid(env);
                for elem_ty in ss_elems {
                    res = and(env, res, |env| {
                        simplify(
                            subtype_env,
                            None,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &elem_ty,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &ty_super,
                            },
                            env,
                        )
                    });
                }
                res
            }
            // class<T> <D: dynamic by exposure to string
            Ty_::TclassPtr(_) if subtype_env.class_sub_classname => valid(env),
            // class<T> <D: dynamic if T <D: dynamic (class is SDT)
            Ty_::TclassPtr(ty) => simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &ty,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            ),
            Ty_::Tclass((_, class_id), _exact, tyargs) => {
                let class_def_sub = env::get_class(env, class_id);
                match class_def_sub {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        // This should have been caught already in the naming phase
                        valid(env)
                    }
                    decl_entry::T::Found(class_sub) => {
                        if cls::get_support_dynamic_type(&class_sub) || env::is_enum(env, class_id)
                        {
                            // If a class has the __SupportDynamicType annotation, then
                            // a type formed from it is a dynamic-aware subtype of dynamic if
                            // the type arguments are correctly supplied, which depends on the
                            // variance of the parameter, and whether the __RequireDynamic
                            // is on the parameter.
                            subtype_args(s, &r_dynamic, cls::tparams_ref(&class_sub), tyargs, env)
                        } else {
                            match cls::kind(&class_sub) {
                                ClassishKind::CenumClass(_) => match cls::enum_type(&class_sub) {
                                    Some(enum_type) => {
                                        let (_ty_err_opt, subtype) =
                                            t_utils::localize_no_subst(env, true, &enum_type.base);
                                        simplify(
                                            subtype_env,
                                            None,
                                            Lhs {
                                                sub_supportdyn: None,
                                                ty_sub: &subtype,
                                            },
                                            Rhs {
                                                super_like: false,
                                                super_supportdyn: false,
                                                ty_super: &ty_super,
                                            },
                                            env,
                                        )
                                    }
                                    None => default_subtype(
                                        subtype_env,
                                        this_ty,
                                        fail.clone(),
                                        Lhs {
                                            sub_supportdyn,
                                            ty_sub: &ty_sub,
                                        },
                                        Rhs {
                                            super_like,
                                            super_supportdyn: false,
                                            ty_super: &ty_super,
                                        },
                                        env,
                                    ),
                                },
                                _ => default_subtype(
                                    subtype_env,
                                    this_ty,
                                    fail.clone(),
                                    Lhs {
                                        sub_supportdyn,
                                        ty_sub: &ty_sub,
                                    },
                                    Rhs {
                                        super_like,
                                        super_supportdyn: false,
                                        ty_super: &ty_super,
                                    },
                                    env,
                                ),
                            }
                        }
                    }
                }
            }
        }
    };
    if let Some(recorder) = memo {
        recorder.record(env, ty_sub, &prop);
    }
    // `postprocess`
    if_unsat(|env| invalid(postprocess_fail(lazy_env), env), env, prop)
}

/// The local `subtype_args` of the arm C-Dynamic-R of `simplify_`, for a
/// class with `__SupportDynamicType` (or an enum).
fn subtype_args(
    s: &Scope<'_>,
    r_dynamic: &Reason,
    tparams: &[DeclTparam],
    tyargs: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        ty_super,
        fail,
        ..
    } = *s;
    match (tparams, tyargs) {
        ([], _) => valid(env),
        (_, []) => {
            // If there are missing type arguments, we don't know that they are subtypes of dynamic, unless the bounds enforce that
            invalid(fail.clone(), env)
        }
        ([tp, tparams @ ..], [tyarg, tyargs @ ..]) => {
            // `Attributes.mem SN.UserAttributes.uaRequireDynamic
            // tp.tp_user_attributes`, comparing the interned names (equal
            // exactly when the strings are) rather than the strings.
            static REQUIRE_DYNAMIC: std::sync::LazyLock<pos::TypeName> =
                std::sync::LazyLock::new(|| pos::TypeName::new(sn::user_attributes::REQUIRE_DYNAMIC));
            let has_require_dynamic = tp
                .user_attributes
                .iter()
                .any(|ua| *ua.name.id_ref() == *REQUIRE_DYNAMIC);
            let prop = if has_require_dynamic
                // Implicit pessimisation should ignore the RequireDynamic attribute
                // because everything should be pessimised enough that it isn't necessary.
                && !env.genv.tcopt.po.everything_sdt
            {
                // If the class is marked <<__SupportDynamicType>> then for any
                // type parameters marked <<__RequireDynamic>> then the class does not
                // unconditionally implement dynamic, but rather we must check that
                // it is a subtype of the same type whose corresponding type arguments
                // are replaced by dynamic, intersected with the parameter's upper bounds.
                //
                // For example, to check dict<int,float> <: supportdyn<nonnull>
                // we check dict<int,float> <D: dict<arraykey,dynamic>
                // which in turn requires int <D: arraykey and float <D: dynamic.
                //
                // (The environment that localization returns is dropped.)
                let upper_bounds: Vec<Ty> = tp
                    .constraints
                    .iter()
                    .filter_map(|(c, ty)| match c {
                        ast_defs::ConstraintKind::ConstraintAs => {
                            let (_, ty) = phase::localize_no_subst(&mut env.clone(), true, ty);
                            Some(ty)
                        }
                        _ => None,
                    })
                    .collect();
                let super_ = make_type::intersection(
                    r_dynamic.clone(),
                    std::iter::once(ty_super.clone())
                        .chain(upper_bounds)
                        .collect(),
                );
                match tp.variance {
                    ast_defs::Variance::Covariant => simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &tyarg,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &super_,
                        },
                        env,
                    ),
                    ast_defs::Variance::Contravariant => simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &super_,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &tyarg,
                        },
                        env,
                    ),
                    ast_defs::Variance::Invariant => {
                        let p = simplify(
                            subtype_env,
                            None,
                            Lhs {
                                sub_supportdyn: None,
                                ty_sub: &tyarg,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &super_,
                            },
                            env,
                        );
                        and(env, p, |env| {
                            simplify(
                                subtype_env,
                                None,
                                Lhs {
                                    sub_supportdyn: None,
                                    ty_sub: &super_,
                                },
                                Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &tyarg,
                                },
                                env,
                            )
                        })
                    }
                }
            } else {
                // If the class is marked <<__SupportDynamicType>> then for any
                // type parameters not marked <<__RequireDynamic>> then the class is a
                // subtype of dynamic only when the arguments are also subtypes of dynamic.
                match tp.variance {
                    ast_defs::Variance::Covariant | ast_defs::Variance::Invariant => simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn: None,
                            ty_sub: &tyarg,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    ),
                    ast_defs::Variance::Contravariant => {
                        // If the parameter is contra-variant, then we only need to
                        // check that the lower bounds (if present) are subtypes of
                        // dynamic. For example, given <<__SDT>> class C<-T> {...},
                        // then for any t, C<t> <: C<nothing>, and since
                        // `nothing <D: dynamic`, `C<nothing> <D: dynamic` and so
                        // `C<t> <D: dynamic`. If there are lower bounds, we can't
                        // push the argument below them. It suffices to check only
                        // them because if one of them is not <D: dynamic, then
                        // none of their supertypes are either.
                        //
                        // (The environment that localization returns is dropped.)
                        let lower_bounds: Vec<Ty> = tp
                            .constraints
                            .iter()
                            .filter_map(|(c, ty)| match c {
                                ast_defs::ConstraintKind::ConstraintSuper => {
                                    let (_, ty) =
                                        phase::localize_no_subst(&mut env.clone(), true, ty);
                                    Some(ty)
                                }
                                _ => None,
                            })
                            .collect();
                        match lower_bounds.as_slice() {
                            [] => valid(env),
                            _ => {
                                let sub = make_type::union(r_dynamic.clone(), lower_bounds);
                                simplify(
                                    subtype_env,
                                    None,
                                    Lhs {
                                        sub_supportdyn: None,
                                        ty_sub: &sub,
                                    },
                                    Rhs {
                                        super_like: false,
                                        super_supportdyn: false,
                                        ty_super: &ty_super,
                                    },
                                    env,
                                )
                            }
                        }
                    }
                }
            };
            and(env, prop, |env| {
                subtype_args(s, r_dynamic, tparams, tyargs, env)
            })
        }
    }
}

/// `simplify_`, arm `((r_sub, Tfun ft_sub), (r_super, Tfun ft_super))` (C-Fun).
fn simplify_c_fun(
    s: &Scope<'_>,
    ft_sub: &FunType,
    ft_super: &FunType,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        super_like,
        ty_sub,
        ty_super,
        ..
    } = *s;
    let r_sub = get_reason(ty_sub).clone();
    let r_super = get_reason(ty_super).clone();
    // If function type in supertype position is polymorphic we will move
    // through a binder. In doing so we need to ensure that any type parameters
    // bound at this higher-rank do not escape into the bounds of any
    // lower ranked type variables. To do this we increase the current rank
    // before binding the type parameters and instantiating the subtype (if
    // it is polymorphic). We then decrease the rank again before returning.
    //
    // If only the subtype is polymorphic we don't change ranks because we
    // aren't going though a binder - we are just instantiating.
    let increase_rank = !ft_super.instantiated;
    if increase_rank {
        typing_env_types::increment_rank(env)
    }
    let rank = typing_env_types::get_rank(env);
    // (The instantiated function types are borrowed.)
    let ft_sub_instantiated;
    let ft_super_freshened;
    let (err_opt, ft_sub): (_, &FunType) = if ft_sub.instantiated {
        (None, ft_sub)
    } else {
        let pos = pos_or_decl::unsafe_to_raw_pos(reason::to_pos(&r_sub));
        // Replace all quantifiers with fresh type variables adding any declared
        // bounds
        let (err_opt, ft) = instantiate::instantiate_fun_type(
            subtype_env.on_error.clone(),
            pos,
            ft_sub.clone(),
            rank,
            env,
        );
        ft_sub_instantiated = ft;
        (err_opt, &ft_sub_instantiated)
    };
    // Handle any error - we can fail to instantiate if the function type has
    // unsatisfiable bounds
    if err_opt.is_some() {
        tl::invalid(err_opt)
    } else {
        let ft_super: &FunType = if ft_super.instantiated {
            ft_super
        } else {
            // Freshen all type parameters wrt to the enclosing context then
            // bind them
            ft_super_freshened = instantiate::freshen_and_bind_fun_type_quantifiers(
                r_super.clone(),
                ft_super.clone(),
                rank,
                env,
            );
            &ft_super_freshened
        };
        // Simplify the subtype proposition between the instantiated subtype
        // and the the supertype in the modified context
        let prop = simplify_funs(
            subtype_env,
            true,  // check_return
            false, // for_override
            super_like,
            (r_sub, ft_sub),
            (r_super, ft_super),
            env,
        );
        // If we incremented the rank during the instantiation of polymorphic
        // function types we need to decrement it here
        if increase_rank {
            typing_env_types::decrement_rank(env)
        }
        prop
    }
}

/// The local `simplify_elems_req` of the arm "Tuple against tuple" of
/// `simplify_`: `ty_subs` and `ty_supers` are what is left of the required
/// components of the two tuples, whose other components it reads.
fn simplify_elems_req(
    s: &Scope<'_>,
    (r_sub, t_sub): (&Reason, &TupleType),
    (r_super, t_super): (&Reason, &TupleType),
    ty_subs: &[Ty],
    ty_supers: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        sub_supportdyn,
        super_like,
        fail,
        ..
    } = *s;
    let TupleType {
        optional: t_optional_sub,
        extra: t_extra_sub,
        ..
    } = t_sub;
    let TupleType {
        optional: t_optional_super,
        extra: t_extra_super,
        ..
    } = t_super;
    match (ty_subs, ty_supers) {
        // We have required elements in the supertype that can't be satisfied by the subtype
        ([], [_, ..]) => match t_extra_sub {
            TupleExtra::Tsplat(t_splat_sub) => {
                let tuple_super_ty = mk((
                    r_super.clone(),
                    Ty_::Ttuple(TupleType {
                        required: ty_supers.to_vec(),
                        optional: t_optional_super.clone(),
                        extra: t_extra_super.clone(),
                    }),
                ));
                let ty_super = sd::liken(super_like, env, tuple_super_ty);
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &t_splat_sub,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            }
            TupleExtra::Tvariadic(_) => invalid(fail.clone(), env),
        },
        // Pointwise compare sub and super
        ([ty_sub, ty_subs @ ..], [ty_super, ty_supers @ ..]) => {
            let ty_super = sd::liken(super_like, env, ty_super.clone());
            let p = simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            and(env, p, |env| {
                simplify_elems_req(
                    s,
                    (r_sub, t_sub),
                    (r_super, t_super),
                    ty_subs,
                    ty_supers,
                    env,
                )
            })
        }
        // We've run out of required elements in the supertype
        (_, []) => match t_extra_super {
            // But we can match the rest of the subtype against a splat in the supertype
            // i.e. (ty_subs, optional t_optional_sub, tvariadic_sub...) <: t_splat_super
            TupleExtra::Tsplat(t_splat_super) => {
                let tuple_sub_ty = mk((
                    r_sub.clone(),
                    Ty_::Ttuple(TupleType {
                        required: ty_subs.to_vec(),
                        optional: t_optional_sub.clone(),
                        extra: t_extra_sub.clone(),
                    }),
                ));
                let ty_super = sd::liken(super_like, env, t_splat_super.clone());
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &tuple_sub_ty,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            }
            TupleExtra::Tvariadic(t_variadic_super) => {
                // Shortcut so that error refers to whole tuple
                if ty_subs.len() + t_optional_sub.len() > t_optional_super.len()
                    && typing_defs::is_nothing(t_variadic_super)
                {
                    invalid(fail.clone(), env)
                } else {
                    // `ty_subs @ t_optional_sub`
                    let ty_subs: Vec<Ty> = ty_subs
                        .iter()
                        .chain(t_optional_sub.iter())
                        .cloned()
                        .collect();
                    simplify_elems_opt(
                        s,
                        r_super,
                        t_extra_sub,
                        t_variadic_super,
                        &ty_subs,
                        t_optional_super,
                        env,
                    )
                }
            }
        },
    }
}

/// The local `simplify_elems_opt` of the arm "Tuple against tuple" of
/// `simplify_`, once the required components of the supertype are matched:
/// the rest of the subtype against the optional and variadic components of
/// the supertype.
fn simplify_elems_opt(
    s: &Scope<'_>,
    r_super: &Reason,
    t_extra_sub: &TupleExtra,
    t_variadic_super: &Ty,
    ty_subs: &[Ty],
    ty_supers: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        sub_supportdyn,
        super_like,
        ..
    } = *s;
    match (ty_subs, ty_supers) {
        ([ty_sub, ty_subs @ ..], []) => {
            let ty_super = sd::liken(super_like, env, t_variadic_super.clone());
            let p = simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            and(env, p, |env| {
                simplify_elems_opt(
                    s,
                    r_super,
                    t_extra_sub,
                    t_variadic_super,
                    ty_subs,
                    ty_supers,
                    env,
                )
            })
        }
        // We've run out of elements in the subtype
        ([], _) => match t_extra_sub {
            TupleExtra::Tsplat(t_splat_sub) => {
                let tuple_super_ty = mk((
                    r_super.clone(),
                    Ty_::Ttuple(TupleType {
                        required: vec![],
                        optional: ty_supers.to_vec(),
                        extra: TupleExtra::Tvariadic(t_variadic_super.clone()),
                    }),
                ));
                let ty_super = sd::liken(super_like, env, tuple_super_ty);
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &t_splat_sub,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            }
            TupleExtra::Tvariadic(t_variadic_sub) => match ty_supers {
                [] => {
                    let ty_super = sd::liken(super_like, env, t_variadic_super.clone());
                    simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &t_variadic_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                }
                [ty_super, ty_supers @ ..] => {
                    let ty_super = sd::liken(super_like, env, ty_super.clone());
                    let p = simplify(
                        subtype_env,
                        None,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &t_variadic_sub,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    );
                    and(env, p, |env| {
                        simplify_elems_opt(
                            s,
                            r_super,
                            t_extra_sub,
                            t_variadic_super,
                            &[],
                            ty_supers,
                            env,
                        )
                    })
                }
            },
        },
        ([ty_sub, ty_subs @ ..], [ty_super, ty_supers @ ..]) => {
            let ty_super = sd::liken(super_like, env, ty_super.clone());
            let p = simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            and(env, p, |env| {
                simplify_elems_opt(
                    s,
                    r_super,
                    t_extra_sub,
                    t_variadic_super,
                    ty_subs,
                    ty_supers,
                    env,
                )
            })
        }
    }
}

/// `simplify_`, arm `(_, (r_supportdyn, Tnewtype (name_super, [lty_inner],
/// bound_super))) when String.equal name_super SN.Classes.cSupportDyn`
/// (C-Newtype-R, `x <: supportdyn<u>`).
fn simplify_c_newtype_r_supportdyn(
    s: &Scope<'_>,
    lty_inner: &Ty,
    bound_super: &Ty,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        fail,
        ty_super,
        ..
    } = *s;
    let r_supportdyn = get_reason(ty_super).clone();
    match get_node(ty_sub) {
        // supportdyn<t> <: supportdyn<u>
        Ty_::Tnewtype(name_sub, tyargs_sub, _)
            if tyargs_sub.len() == 1 && name_sub == sn::classes::SUPPORT_DYN =>
        {
            let r = get_reason(ty_sub).clone();
            let tyarg_sub = &tyargs_sub[0];
            let ty_sub = env::update_reason(env, tyarg_sub.clone(), |r_sub_prj| {
                reason::prj_supportdyn(r.clone(), r_sub_prj, r_supportdyn.clone())
            });
            let ty_super = lty_inner.clone();
            simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: Some(&r),
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: true,
                    ty_super: &ty_super,
                },
                env,
            )
        }
        Ty_::Tvar(_) => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &mk((
                    r_supportdyn,
                    Ty_::Tnewtype(
                        sn::classes::SUPPORT_DYN.to_string(),
                        vec![lty_inner.clone()],
                        bound_super.clone(),
                    ),
                )),
            },
            env,
        ),
        _ => {
            let ty_dyn = make_type::dynamic(r_supportdyn);
            let p = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: true,
                    ty_super: &lty_inner,
                },
                env,
            );
            and(env, p, |env| {
                simplify(
                    &subtype_env::set_is_dynamic_aware(subtype_env.clone(), true),
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_dyn,
                    },
                    env,
                )
            })
        }
    }
}

/// `simplify_`, arm `(_, (_r_representable_as, Tnewtype (name_super,
/// [lty_inner], _bound_super))) when String.equal name_super
/// SN.Classes.cRepresentableAs` (C-RepresentableAs-R).
fn simplify_c_representable_as_r(s: &Scope<'_>, lty_inner: &Ty, env: &mut Env) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    match get_node(ty_sub) {
        // RepresentableAs<t> <: RepresentableAs<u> ==> t <: u (covariance)
        Ty_::Tnewtype(name_sub, tyargs_sub, _)
            if tyargs_sub.len() == 1 && name_sub == sn::classes::REPRESENTABLE_AS =>
        {
            simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &tyargs_sub[0],
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &lty_inner,
                },
                env,
            )
        }
        Ty_::Tvar(_) => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
        Ty_::Tprim(Tprim::Tvoid) => {
            let r_sub = get_reason(ty_sub).clone();
            // void <: RepresentableAs<U> when null <: U OR void <: U
            let p = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &make_type::null(r_sub),
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &lty_inner,
                },
                env,
            );
            or(fail.clone(), env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &lty_inner,
                    },
                    env,
                )
            })
        }
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => {
            let r_sub = get_reason(ty_sub).clone();
            // (T1, T2, ...Tn) <: RepresentableAs<U>
            // when vec<T1 | T2 | ... | Tn> <: U OR (T1, T2, ...Tn) <: U
            let elem_tys: Vec<Ty> = t_required
                .iter()
                .chain(t_optional.iter())
                .chain(match t_extra {
                    TupleExtra::Tvariadic(ty) | TupleExtra::Tsplat(ty) => std::iter::once(ty),
                })
                .cloned()
                .collect();
            let union_ty = make_type::union(r_sub.clone(), elem_tys);
            let vec_ty = make_type::vec(r_sub, union_ty);
            let p = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &vec_ty,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &lty_inner,
                },
                env,
            );
            or(fail.clone(), env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &lty_inner,
                    },
                    env,
                )
            })
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            let r_sub = get_reason(ty_sub).clone();
            let result = typing_corners::resolve_for_read(env, r_sub, ss_elems);
            match result {
                Err(missing) => missing_shape_splat_assignment(
                    subtype_env,
                    env,
                    &missing,
                    InternalType::LoclType(ty_sub.clone()),
                    InternalType::LoclType(ty_super.clone()),
                ),
                Ok(ty_sub) => simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super,
                    },
                    env,
                ),
            }
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            fields: s_fields,
            unknown_value: s_unknown_value,
            ..
        })) => {
            let r_sub = get_reason(ty_sub).clone();
            // shape('a' => T1, 'b' => T2, ...) <: RepresentableAs<U>
            // when dict<key, V1 | V2 | ... | Vn> <: U
            // OR   shape('a' => T1, 'b' => T2, ...) <: U
            // For closed shapes, the key type is the union of the per-field key
            // types: TSFlit_str => string, TSFregex_group => int,
            // TSFclass_const => looked up from the class constant's declared type.
            // For open shapes, key = arraykey.
            // For open shapes, s_unknown_value is included in the value union.
            // If s_unknown_value is mixed, the value union is just mixed.
            let is_closed = t_utils::is_nothing(env, s_unknown_value);
            let key_ty = if !is_closed {
                make_type::arraykey(r_sub.clone())
            } else {
                // `TShapeMap.fold`: in the order of the keys
                let mut key_tys = typing_set::empty();
                for key in s_fields.keys() {
                    key_tys = match &key.0 {
                        TshapeFieldName::TSFlitStr(_) => {
                            typing_set::add(make_type::string(r_sub.clone()), &key_tys)
                        }
                        TshapeFieldName::TSFregexGroup(_) => {
                            typing_set::add(make_type::int(r_sub.clone()), &key_tys)
                        }
                        TshapeFieldName::TSFclassConst((_, cid), PosString(_, mid)) => {
                            match env::get_class(env, cid) {
                                decl_entry::T::Found(cls) => match env::get_const(env, &cls, mid) {
                                    Some(const_) => {
                                        let (_ty_err_opt, lty) =
                                            phase::localize_no_subst(env, true, &const_.ty);
                                        typing_set::add(lty, &key_tys)
                                    }
                                    None => typing_set::add(
                                        make_type::arraykey(r_sub.clone()),
                                        &key_tys,
                                    ),
                                },
                                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                                    typing_set::add(make_type::arraykey(r_sub.clone()), &key_tys)
                                }
                            }
                        }
                    };
                }
                make_type::union(r_sub.clone(), typing_set::elements(&key_tys))
            };
            let value_union = if t_utils::is_mixed(env, s_unknown_value) {
                s_unknown_value.clone()
            } else {
                // `TShapeMap.fold` conses the field types onto the initial
                // list, in the order of the keys: the result has them in the
                // reverse order, followed by the initial list.
                let value_tys: Vec<Ty> = s_fields
                    .values()
                    .rev()
                    .map(|sft| sft.ty.clone())
                    .chain(if is_closed {
                        None
                    } else {
                        Some(s_unknown_value.clone())
                    })
                    .collect();
                make_type::union(r_sub.clone(), value_tys)
            };
            let dict_ty = make_type::dict(r_sub, key_ty, value_union);
            let p = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &dict_ty,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &lty_inner,
                },
                env,
            );
            or(fail.clone(), env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &lty_inner,
                    },
                    env,
                )
            })
        }
        Ty_::Tgeneric(_) if subtype_env.require_completeness => {
            // In completeness mode (decompose_subtype), preserve the
            // constraint shape `T <: RepresentableAs<U>` so it is stored
            // as T's upper bound. The iff-U reduction would strip the RA
            // wrapper, and `simplify ||| default_subtype` would produce a
            // Disj that decompose_subtype_add_prop drops. default_subtype
            // already defers Tgeneric in completeness mode via
            // mk_issubtype_prop.
            default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            )
        }
        Ty_::Tnewtype(..) | Ty_::Tgeneric(_) | Ty_::Tdependent(..) => {
            let p = default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            or(fail.clone(), env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &lty_inner,
                    },
                    env,
                )
            })
        }
        _ => {
            // T <: RepresentableAs<U> iff T <: U
            simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &lty_inner,
                },
                env,
            )
        }
    }
}

/// `simplify_`, arm `(_, (r_super, Tnewtype (name_super, lty_supers,
/// _bound_super)))` (C-Newtype-R) once the special newtypes are excluded.
fn simplify_c_newtype_r(
    s: &Scope<'_>,
    name_super: &str,
    lty_supers: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    let r_super = get_reason(ty_super).clone();
    match get_node(ty_sub) {
        Ty_::Tclass((_, name_sub), _, _)
            if name_sub == name_super && env::is_enum(env, name_super) =>
        {
            valid(env)
        }
        Ty_::Tnewtype(name_sub, lty_subs, _) if name_sub == name_super => {
            let r_sub = get_reason(ty_sub).clone();
            if lty_subs.is_empty() {
                valid(env)
            } else if env::is_enum(env, name_super) && env::is_enum(env, name_sub) {
                valid(env)
            } else {
                let td = env::get_typedef(env, name_super);
                match td {
                    decl_entry::T::Found(td) => {
                        let variance_reifiedl: Vec<_> =
                            td.tparams.iter().map(|t| (t.variance, t.reified)).collect();
                        simplify_subtype_variance_for_non_injective(
                            subtype_env,
                            sub_supportdyn,
                            super_like,
                            name_sub,
                            None,
                            &variance_reifiedl,
                            (r_sub, lty_subs),
                            (r_super, lty_supers),
                            ty_sub.clone(),
                            ty_super.clone(),
                            env,
                        )
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        // TODO(hverr): decl_entry propagate
                        invalid(fail.clone(), env)
                    }
                }
            }
        }
        // ?t <: A <=> null <: A && t <: A
        Ty_::Toption(ty_sub_inner) => {
            let r = get_reason(ty_sub).clone();
            let r = reason::prj_nullable_sub(r.clone(), r);
            let ty_null = make_type::null(r.clone());
            // Errors due to `null` should refer to full option type
            let prop_null = |env: &mut Env| {
                let prop = simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_null,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                );
                if_unsat(|env| invalid(fail.clone(), env), env, prop)
            };
            let ty_sub_inner = env::update_reason(env, ty_sub_inner.clone(), |r_sub_prj| {
                reason::prj_nullable_sub(r.clone(), r_sub_prj)
            });
            let p = prop_null(env);
            and(env, p, |env| {
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub_inner,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                )
            })
        }
        Ty_::Tprim(Tprim::Tarraykey) => {
            let r = get_reason(ty_sub).clone();
            let r = reason::prj_arraykey_sub(r.clone(), r);
            let ty_string = make_type::string(r.clone());
            let ty_int = make_type::int(r);
            let prop = |env: &mut Env| {
                let p = simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_string,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                );
                and(env, p, |env| {
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_int,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                })
            };
            // Use `if_unsat` so we report arraykey in the error
            let p = prop(env);
            if_unsat(|env| invalid(fail.clone(), env), env, p)
        }
        Ty_::Tprim(Tprim::Tnum) => {
            let r = get_reason(ty_sub).clone();
            let r = reason::prj_num_sub(r.clone(), r);
            let ty_float = make_type::float(r.clone());
            let ty_int = make_type::int(r);
            let prop = |env: &mut Env| {
                let p = simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_float,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                );
                and(env, p, |env| {
                    simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_int,
                        },
                        Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    )
                })
            };
            // Use `if_unsat` so we report num in the error
            let p = prop(env);
            if_unsat(|env| invalid(fail.clone(), env), env, p)
        }
        Ty_::Tgeneric(_) if subtype_env.require_completeness => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
        Ty_::Tvar(_) | Ty_::Tunion(_) => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
        Ty_::Tany(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tintersection(_)
        | Ty_::Tdependent(..)
        | Ty_::Taccess(_)
        | Ty_::Tgeneric(_)
        | Ty_::Tnonnull
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::TvecOrDict(..)
        | Ty_::Tclass(..)
        | Ty_::Tnewtype(..)
        | Ty_::Tneg(_)
        | Ty_::Tprim(
            Tprim::Tnull
            | Tprim::Tvoid
            | Tprim::Tint
            | Tprim::Tbool
            | Tprim::Tfloat
            | Tprim::Tresource
            | Tprim::Tnoreturn,
        )
        | Ty_::Tlabel(_)
        | Ty_::TclassPtr(_) => {
            let subtype_env = match get_node(ty_sub) {
                Ty_::Tnewtype(..) => Ok(subtype_env.clone()),
                _ => subtype_env::check_infinite_recursion(
                    subtype_env.clone(),
                    subtype_op::T {
                        sub: ty_sub.clone(),
                        super_: ty_super.clone(),
                    },
                ),
            };
            match subtype_env {
                Err(_) => {
                    // We've essentially proven by recursion that this subypting relationship holds.
                    // For details, see Figure 21-4 p. 395 of Pierce's Types and Programming Languages.
                    // The subtyping relationship would only fail to hold if the recursive types are not
                    // contractive.
                    // We're checking for contractiveness in check_invalid_recursive_case_type
                    valid(env)
                }
                Ok(subtype_env) => {
                    simplify_c_newtype_r_case_type(s, &subtype_env, name_super, lty_supers, env)
                }
            }
        }
    }
}

/// The end of the arm C-Newtype-R of `simplify_` (`x <: case_type`), with
/// the `subtype_env` that records the operation for the recursion check.
fn simplify_c_newtype_r_case_type(
    s: &Scope<'_>,
    subtype_env: &subtype_env::T,
    name_super: &str,
    lty_supers: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    let localize = |td_tparams: &[DeclTparam], hint: &DeclTy, env: &mut Env| -> Ty {
        let ety_env = ExpandEnv {
            // The this_ty cannot does not need to be set because newtypes
            // & case types cannot appear within classes thus cannot us
            // the this type. If we ever change that this could needs to
            // be changed
            //
            // Subtyping can be called when localizing
            // a union type, since we attempt to simplify it.
            // Since case types are encoded as union types,
            // a cyclic reference to the same case type will
            // lead to infinite looping. The chain is:
            //   localize -> simplify_union -> sub_type -> localize
            //
            // The expand environment is not threaded through the
            // whole way, so we won't be able to tell we entered a cycle.
            //
            // For this reason we want to report cycles on the
            // case type we are currently expanding. If a cycle
            // occurs we say the proposition is invalid, but
            // don't report an error, since that will be done
            // during well-formedness checks on type defs
            type_expansions: type_expansions::empty_w_cycle_report(Some((
                Pos::NONE,
                type_expansions::expandable::T::TypeAlias(name_super.to_string()),
            ))),
            substs: if lty_supers.is_empty() {
                crate::pmap::Map::new()
            } else {
                // `Decl_subst.make_locl`
                crate::decl_subst::make_locl(td_tparams, lty_supers)
            },
            ..empty_expand_env()
        };
        let (_err, ty) = phase::localize(&ety_env, env, hint);
        ty
    };
    let simplify_ = |ty_sub: Ty, ty_super: Ty, env: &mut Env| {
        simplify(
            subtype_env,
            None,
            Lhs {
                sub_supportdyn: None,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        )
    };
    // x <: case_type
    let td = env::get_typedef(env, name_super);
    let td = match &td {
        decl_entry::T::Found(td) => Some((td, &td.type_assignment, &td.super_constraint)),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    };
    match td {
        Some((td, TypedefTypeAssignment::CaseType(variant, variants), _)) => {
            let td_tparams: &[DeclTparam] = &td.tparams;
            let check_where_constraint =
                |wc: &DeclWhereConstraint, env: &mut Env| -> tl::SubtypeProp {
                    let WhereConstraint(left, ck, right) = wc;
                    let local_left = localize(td_tparams, left, env);
                    let local_right = localize(td_tparams, right, env);
                    match ck {
                        ast_defs::ConstraintKind::ConstraintAs => {
                            simplify_(local_left, local_right, env)
                        }
                        ast_defs::ConstraintKind::ConstraintSuper => {
                            simplify_(local_right, local_left, env)
                        }
                        ast_defs::ConstraintKind::ConstraintEq => {
                            let p = simplify_(local_left.clone(), local_right.clone(), env);
                            and(env, p, |env| simplify_(local_right, local_left, env))
                        }
                    }
                };
            // For
            // CT<T1, ... Tn> =
            // | U1 where [constraints_1] | ... | Um where [constraints_m]
            // Then T < CT<t1, ... tn> iff
            // for any k in [1..m]:
            // T < Vk[t1/T1, ...] &&& constraints_k[t1/T1, ...]
            //
            // (`let ( ||| ) = ( ||| ) ~fail`)
            let try_variant = |variant: &TypedefCaseTypeVariant, env: &mut Env| {
                let hint = &variant.hint;
                let wcs = &variant.where_constraints;
                let hint_ty = localize(td_tparams, hint, env);
                let valid = |ty: &DeclTy| {
                    !typing_case_type_utils::decl_ty_mentions_name_via_typedef(env, name_super, ty)
                };
                let wcs: Vec<&DeclWhereConstraint> = wcs
                    .iter()
                    .filter(|wc| {
                        let WhereConstraint(left, _ck, right) = wc;
                        valid(left) && valid(right)
                    })
                    .collect();
                let mut acc = simplify_(ty_sub.clone(), hint_ty, env);
                for wc in wcs {
                    acc = and(env, acc, |env| check_where_constraint(wc, env));
                }
                acc
            };
            let mut acc = default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            // `variant :: variants`
            for variant in std::iter::once(variant).chain(variants.iter()) {
                acc = or(fail.clone(), env, acc, |env| try_variant(variant, env));
            }
            acc
        }
        Some((td, TypedefTypeAssignment::SimpleTypeDef(..), Some(lower))) => {
            let p = default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            );
            or(fail.clone(), env, p, |env| {
                let lower_ty = localize(&td.tparams, lower, env);
                simplify_(ty_sub.clone(), lower_ty, env)
            })
        }
        _ => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
    }
}

/// `simplify_`, arm `(_, (r_super, Tclass (class_id_super, Nonexact
/// cr_super, tyargs_super))) when ...` (C-Class-R, class refinement):
/// `x <: A with type T = y <=> x <: A && x <: has_type_member(T, y)`.
fn simplify_c_class_r_refinement(
    s: &Scope<'_>,
    class_id_super: &PosId,
    cr_super: &ClassRefinement,
    tyargs_super: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        ..
    } = *s;
    let r_super = get_reason(ty_super).clone();
    // We discharge class refinements before anything
    // else ...
    let init = valid(env);
    let prop = class_refinement::fold_refined_consts(cr_super, init, |type_id, rc, prop| {
        and(env, prop, |env| {
            let (htm_lower, htm_upper) = match &rc.bound {
                RefinedConstBound::TRexact(ty) => (ty.clone(), ty.clone()),
                RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: tr_lower,
                    upper: tr_upper,
                }) => {
                    let loty = make_type::union(r_super.clone(), tr_lower.clone());
                    let upty = make_type::intersection(r_super.clone(), tr_upper.clone());
                    (loty, upty)
                }
            };
            let htm = HasTypeMember {
                id: type_id.to_string(),
                lower: htm_lower,
                upper: htm_upper,
            };
            let lhs = Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            };
            let rhs = has_type_member::Rhs {
                reason_super: r_super.clone(),
                has_type_member: htm,
            };
            let subtype_env = subtype_env::possibly_add_violated_constraint(
                subtype_env.clone(),
                get_reason(ty_sub).clone(),
                r_super.clone(),
            );
            has_type_member::simplify(&subtype_env, this_ty, lhs, rhs, env)
        })
    });
    and(env, prop, |env| {
        // then recursively check the class with all the
        // refinements dropped.
        let ty_super = mk((
            r_super.clone(),
            Ty_::Tclass(class_id_super.clone(), nonexact(), tyargs_super.to_vec()),
        ));

        simplify(
            subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        )
    })
}

/// `simplify_`, arm `(_, (_r_super, Tclass ((_pos_super, class_nm_super),
/// exact_super, tyargs_super)))` (C-Class-R).
fn simplify_c_class_r(
    s: &Scope<'_>,
    class_nm_super: &str,
    exact_super: &Exact,
    tyargs_super: &[Ty],
    env: &mut Env,
) -> tl::SubtypeProp {
    let Scope {
        subtype_env,
        this_ty,
        sub_supportdyn,
        super_like,
        ty_sub,
        ty_super,
        fail,
        ..
    } = *s;
    match get_node(ty_sub) {
        // Enums...
        Ty_::Tnewtype(enum_name, _, _)
            if enum_name == class_nm_super
                && is_nonexact(exact_super)
                && env::is_enum(env, enum_name) =>
        {
            valid(env)
        }
        // E <: \HH\BuiltinEnum<t>
        Ty_::Tnewtype(cid, _, _)
            if class_nm_super == sn::classes::HH_BUILTIN_ENUM && env::is_enum(env, cid) =>
        {
            match tyargs_super {
                [lty_super_prime] => simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &lty_super_prime,
                    },
                    env,
                ),
                _ => default_subtype(
                    subtype_env,
                    this_ty,
                    fail.clone(),
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
                    },
                    env,
                ),
            }
        }
        Ty_::Tnewtype(enum_name, _, _)
            if enum_name == class_nm_super && env::is_enum(env, enum_name) =>
        {
            valid(env)
        }
        Ty_::Tnewtype(enum_name, _, _)
            if env::is_enum(env, enum_name) && class_nm_super == sn::classes::XHP_CHILD =>
        {
            valid(env)
        }
        // t_prim <: XHPChild
        Ty_::Tprim(Tprim::Tarraykey | Tprim::Tint | Tprim::Tfloat | Tprim::Tnum)
            if class_nm_super == sn::classes::XHP_CHILD && is_nonexact(exact_super) =>
        {
            valid(env)
        }
        Ty_::Tclass((_, id), _, _)
            if id == C_STRING
                && class_nm_super == sn::classes::XHP_CHILD
                && is_nonexact(exact_super) =>
        {
            valid(env)
        }
        // string <: Stringish
        Ty_::Tclass((_, id), _, _)
            if class_nm_super == sn::classes::STRINGISH
                && is_nonexact(exact_super)
                && id == C_STRING =>
        {
            valid(env)
        }
        // same as prior two cases by typename's string bound
        Ty_::TclassPtr(_)
            if subtype_env.class_sub_classname
                && is_nonexact(exact_super)
                && (class_nm_super == sn::classes::XHP_CHILD
                    || class_nm_super == sn::classes::STRINGISH) =>
        {
            valid(env)
        }
        // Match what's done in unify for non-strict code
        Ty_::Tclass(class_id_sub, exact_sub, tyl_sub) => {
            let r_sub = get_reason(ty_sub).clone();
            match get_node(ty_super) {
                Ty_::Tclass(class_id_super, exact_super, tyl_super) => {
                    let r_super = get_reason(ty_super).clone();
                    simplify_subtype_classes(
                        fail.clone(),
                        subtype_env,
                        sub_supportdyn,
                        this_ty,
                        super_like,
                        (r_sub, (class_id_sub, exact_sub, tyl_sub)),
                        (r_super, (class_id_super, exact_super, tyl_super)),
                        env,
                    )
                }
                _ => invalid(fail.clone(), env),
            }
        }
        Ty_::TvecOrDict(_, tv) => match (exact_super, tyargs_super) {
            (Exact::Nonexact(_), [tv_super])
                if class_nm_super == sn::collections::TRAVERSABLE
                    || class_nm_super == sn::collections::CONTAINER =>
            {
                // vec<tv> <: Traversable<tv_super>
                // iff tv <: tv_super
                // Likewise for vec<tv> <: Container<tv_super>
                //          and map<_,tv> <: Traversable<tv_super>
                //          and map<_,tv> <: Container<tv_super>
                simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: &tv,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &tv_super,
                    },
                    env,
                )
            }
            (Exact::Nonexact(_), [tk_super, tv_super])
                if class_nm_super == sn::collections::KEYED_TRAVERSABLE
                    || class_nm_super == sn::collections::KEYED_CONTAINER
                    || class_nm_super == sn::collections::ANY_ARRAY =>
            {
                match get_node(ty_sub) {
                    Ty_::TvecOrDict(tk, _) => {
                        let p = simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn,
                                ty_sub: &tk,
                            },
                            Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &tk_super,
                            },
                            env,
                        );
                        and(env, p, |env| {
                            simplify(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &tv,
                                },
                                Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &tv_super,
                                },
                                env,
                            )
                        })
                    }
                    _ => default_subtype(
                        subtype_env,
                        this_ty,
                        fail.clone(),
                        Lhs {
                            sub_supportdyn,
                            ty_sub: &ty_sub,
                        },
                        Rhs {
                            super_like,
                            super_supportdyn: false,
                            ty_super: &ty_super,
                        },
                        env,
                    ),
                }
            }
            (Exact::Nonexact(_), [])
                if class_nm_super == sn::collections::KEYED_TRAVERSABLE
                    || class_nm_super == sn::collections::KEYED_CONTAINER
                    || class_nm_super == sn::collections::ANY_ARRAY =>
            {
                // All arrays are subtypes of the untyped KeyedContainer / Traversables
                valid(env)
            }
            (_, _) => default_subtype(
                subtype_env,
                this_ty,
                fail.clone(),
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn: false,
                    ty_super: &ty_super,
                },
                env,
            ),
        },
        _ => default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::ast_defs::Tprim;
    use oxidized::pos_or_decl::PosOrDecl;
    use oxidized::tany_sentinel::TanySentinel;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::typing_defs_core::TaccessType;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    fn subtype_env() -> subtype_env::T {
        subtype_env::create(
            None, None, None, None, None, None, None, None, None, None, false, 0, None,
        )
    }

    fn prim(p: Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    /// `ty_sub <: ty_super`, without `on_error` (the failures carry no error).
    fn sub(ty_sub: Ty, ty_super: Ty) -> tl::SubtypeProp {
        let mut env = env();
        simplify_(
            &subtype_env(),
            None,
            Lhs {
                sub_supportdyn: None,
                ty_sub: &ty_sub,
            },
            Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            &mut env,
        )
    }

    #[test]
    fn primitives() {
        // C-Prim-R
        assert!(tl::is_valid(&sub(prim(Tprim::Tint), prim(Tprim::Tnum))));
        assert!(tl::is_valid(&sub(prim(Tprim::Tfloat), prim(Tprim::Tnum))));
        assert!(tl::is_valid(&sub(
            prim(Tprim::Tint),
            prim(Tprim::Tarraykey)
        )));
        assert!(tl::is_valid(&sub(prim(Tprim::Tbool), prim(Tprim::Tbool))));
        assert!(tl::is_unsat(&sub(prim(Tprim::Tint), prim(Tprim::Tbool))));
        assert!(tl::is_unsat(&sub(
            prim(Tprim::Tfloat),
            prim(Tprim::Tarraykey)
        )));
        assert!(tl::is_unsat(&sub(prim(Tprim::Tnum), prim(Tprim::Tint))));
    }

    #[test]
    fn physical_equality() {
        let access = || {
            mk((
                reason::none(),
                Ty_::Taccess(TaccessType(
                    mk((reason::none(), Ty_::Tgeneric("T".to_string()))),
                    (PosOrDecl::NONE, "C".to_string()),
                )),
            ))
        };
        // The same type: valid before the case analysis.
        let ty = access();
        assert!(tl::is_valid(&sub(ty.clone(), ty)));
        // Built twice, it is another type, and `_ <: T::C` is invalid
        // (C-Access-R).
        assert!(tl::is_unsat(&sub(access(), access())));
    }

    #[test]
    fn top_and_bottom() {
        let int = || prim(Tprim::Tint);
        let nothing = || make_type::nothing(reason::none());
        // C-Top-R: mixed is ?nonnull
        assert!(tl::is_valid(&sub(int(), make_type::mixed(reason::none()))));
        // C-Option-R: null <: ?int
        assert!(tl::is_valid(&sub(
            prim(Tprim::Tnull),
            make_type::nullable(reason::none(), int())
        )));
        // C-Bot-R
        assert!(tl::is_valid(&sub(nothing(), nothing())));
        assert!(tl::is_unsat(&sub(int(), nothing())));
        // `no_top_bottom` is not set
        assert!(tl::is_valid(&sub(
            mk((reason::none(), Ty_::Tany(TanySentinel))),
            nothing()
        )));
    }

    #[test]
    fn labels() {
        let label = |n: &str| mk((reason::none(), Ty_::Tlabel(n.to_string())));
        assert!(tl::is_valid(&sub(label("A"), label("A"))));
        assert!(tl::is_unsat(&sub(label("A"), label("B"))));
    }
}
