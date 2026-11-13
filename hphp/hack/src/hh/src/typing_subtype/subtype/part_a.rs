// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 802-2522): module `Subtype`.
//! See `hh/PORTING.md`.
//!
//! This part has the signature of `Subtype` (the type [`Rhs`]; `simplify` and
//! `simplify_funs` are in `part_b.rs`) and its functions from the start of the
//! structure up to and including `simplify_subtype_named_variadic`.
//!
//! The signature documents `simplify` (`include Constraint_handler with type
//! rhs := rhs`):
//!
//! > Given types ty_sub and ty_super, attempt to
//! > reduce the subtyping proposition ty_sub <: ty_super to
//! > a logical proposition whose primitive assertions are of the form v <: t or t <: v
//! > where v is a type variable.
//! >
//! > If super_like=true, then we have already reduced ty_sub <: ~ty_super to ty_sub <: ty_super
//! > with ty_super known to support dynamic (i.e. ty_super <: supportdyn<mixed>). In this case,
//! > when "going under" a constructor (for example, we had C<t> <: ~C<u>),
//! > we can apply "like pushing" on the components (in this example, t <: ~u).
//! > The parameter defaults to false to guard against incorrectly propagating the option. When
//! > simplifying ty_sub only (e.g. reducing t|u <: v to t<:v && u<:v) it is correct to
//! > propagate it.
//! >
//! > The logical relationship between the original and returned proposition
//! > depends on the flags require_soundness and require_completeness.
//! > Fail with Unsat error_function if
//! > the assertion is unsatisfiable. Some examples:
//! >   string <: arraykey  ==>  True    (represented as Conj [])
//! > (For covariant C and a type variable v)
//! >   C<string> <: C<v>   ==>  string <: v
//! > (Assuming that C does *not* implement interface J)
//! >   C <: J              ==>  Unsat _
//! > (Assuming we have T <: D in tpenv, and class D implements I)
//! >   vec<T> <: vec<I>    ==>  True
//! > This last one would be left as T <: I if subtype_env.require_completeness=true
//!
//! # Signatures
//!
//! - `~subtype_env` is `&subtype_env::T`, `~this_ty` is `Option<&Ty>`,
//!   `~lhs` and `~rhs` are [`Lhs`] and [`Rhs`] by value, `~fail` is
//!   `Option<typing_error::T>` by value, and the environment is the last
//!   parameter, as in OCaml (`simplify(subtype_env, this_ty, lhs, rhs,
//!   env)`).
//! - A function that OCaml applies partially and passes to `&&&` (the
//!   environment missing) takes the environment as its last parameter here,
//!   and is called inside the closure given to
//!   `crate::typing_logic_helpers::and`.
//! - Functions that return the environment they are given without using it
//!   (`simplify_param_modes`, ...) take `&Env`, as
//!   `crate::typing_logic_helpers::valid` does; a `&mut Env` can be passed.
//! - The helpers whose OCaml takes `~env` last (`expands_to ty ~p ~env`) take
//!   it last. Those that drop the environment they get back (`let (_, ty) =
//!   Env.expand_type env ty`) take `&Env` and expand in a copy.
//! - `Common`'s functions take the `~mk_prop` callback as `impl Fn(&subtype_env::T,
//!   Option<&Ty>, Lhs, Rhs, &mut Env) -> SubtypeProp` and `~update_reason` as
//!   `impl Fn(&Env, Ty) -> Ty`, with the tuple arguments by value
//!   (`(Option<Reason>, Vec<Ty>)`, ...).

use std::collections::BTreeMap;

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::s_set::SSet;

#[allow(unused_imports)]
use super::*;
use crate::decl_entry;
use crate::internal_type_set as ity_set;
use crate::pos_or_decl;
use crate::typechecker_options;
use crate::typing_coeffects;
use crate::typing_defs;
use crate::typing_defs::named_params;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core;
use crate::typing_defs_core::Capability;
use crate::typing_defs_core::FunImplicitParams;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ParamMode;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::deref;
use crate::typing_defs_core::get_fp_accept_disposable;
use crate::typing_defs_core::get_fp_ignore_readonly_error;
use crate::typing_defs_core::get_fp_is_named;
use crate::typing_defs_core::get_fp_is_optional;
use crate::typing_defs_core::get_fp_mode;
use crate::typing_defs_core::get_fp_readonly;
use crate::typing_defs_core::get_fp_splat;
use crate::typing_defs_core::get_ft_readonly_this;
use crate::typing_defs_core::get_ft_return_disposable;
use crate::typing_defs_core::get_ft_returns_readonly;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_dynamic;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_log;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::if_unsat;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::or;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_named_params;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;
use crate::typing_solver_utils;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype_ask;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `type rhs` of the signature of `Subtype` (the structure defines it again,
/// the same). It borrows the type, as [`Lhs`].
#[derive(Clone, Copy, Debug)]
pub struct Rhs<'a> {
    pub super_supportdyn: bool,
    pub super_like: bool,
    pub ty_super: &'a Ty,
}

/// `module Log`
pub(crate) mod log {
    use super::*;

    pub(crate) fn level(subtype_env: &subtype_env::T, ty_sub: &Ty, ty_super: &Ty) -> isize {
        let level = subtype_env.log_level;
        if (t_utils::is_capability(ty_sub) || t_utils::is_capability(ty_super)) && level < 3 {
            3
        } else {
            level
        }
    }

    /// (The usual case, no level set and a positive `subtype_env.log_level`,
    /// is answered here, without a call: it is asked at every step.)
    #[inline]
    pub(crate) fn should_log(
        env: &Env,
        subtype_env: &subtype_env::T,
        lhs: &Lhs,
        rhs: &Rhs,
    ) -> bool {
        if subtype_env.log_level > 0 && env.log_levels.is_empty() {
            false
        } else {
            should_log_levels(env, subtype_env, lhs, rhs)
        }
    }

    #[inline(never)]
    fn should_log_levels(
        env: &Env,
        subtype_env: &subtype_env::T,
        lhs: &Lhs,
        rhs: &Rhs,
    ) -> bool {
        // `Typing_log.should_log env ~category:"sub" ~level:(level ...)`.
        // `level` is never below `subtype_env.log_level`: when the level
        // configured for "sub" is, the answer is no whatever the types are,
        // and `level` (which looks at both types, for every subtype step)
        // need not be computed.
        // (No level is set, as a rule: then it is 0 without a lookup.)
        let configured = if env.log_levels.is_empty() {
            0
        } else {
            crate::typing_env_types::get_log_level(env, "sub")
        };
        configured >= subtype_env.log_level
            && typing_log::should_log(env, "sub", level(subtype_env, &lhs.ty_sub, &rhs.ty_super))
    }

    pub(crate) fn function_name(
        subtype_env: &subtype_env::T,
        sub_supportdyn: Option<&Reason>,
        super_like: bool,
        super_supportdyn: bool,
    ) -> String {
        let flag = |s: &str, b: bool| match b {
            true => s.to_string(),
            false => String::new(),
        };
        "Typing_subtype.Subtype.simplify".to_string()
            + match subtype_env.is_dynamic_aware {
                false => "",
                true => " <:D",
            }
            + &(flag(" sub_supportdyn", sub_supportdyn.is_some())
                + &flag(" super_supportdyn", super_supportdyn)
                + &flag(" super_like", super_like)
                + &flag(" ignore_likes", subtype_env.ignore_likes)
                + &flag(" require_soundness", subtype_env.require_soundness)
                + &flag(" require_completeness", subtype_env.require_completeness)
                + &flag(" ignore_readonly", subtype_env.ignore_readonly)
                + &flag(" in_transitive_closure", subtype_env.in_transitive_closure))
    }

    /// The OCaml returns `Logging.log_subtype_prop` applied to everything but
    /// the continuation, which the caller then gives (`Log.log env
    /// subtype_env ~this_ty ~lhs ~rhs @@ fun () -> ...`): here the
    /// continuation is the last parameter.
    pub(crate) fn log(
        env: &mut Env,
        subtype_env: &subtype_env::T,
        this_ty: Option<&Ty>,
        lhs: &Lhs,
        rhs: &Rhs,
        f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
    ) -> tl::SubtypeProp {
        let Lhs {
            sub_supportdyn,
            ty_sub,
        } = lhs;
        let Rhs {
            super_like,
            super_supportdyn,
            ty_super,
        } = rhs;
        logging::log_subtype_prop(
            env,
            ty_sub,
            ty_super,
            this_ty,
            &function_name(
                subtype_env,
                *sub_supportdyn,
                *super_like,
                *super_supportdyn,
            ),
            f,
        )
    }
}

pub(crate) fn is_final_and_invariant(env: &Env, id: &str) -> bool {
    let class_def = env::get_class(env, id);
    match class_def {
        decl_entry::T::Found(class_ty) => t_utils::class_is_final_and_invariant(&class_ty),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// The environment the expansion returns is dropped: the expansion is made
/// in a copy.
pub(crate) fn expands_to(ty: &Ty, p: impl FnOnce(&Ty) -> bool, env: &Env) -> bool {
    let ty = env::expand_type(&mut env.clone(), ty.clone());
    p(&ty)
}

pub(crate) fn expands_to_nonnull(ty: &Ty, env: &Env) -> bool {
    expands_to(ty, typing_defs::is_nonnull, env)
}

pub(crate) fn expands_to_supportdyn(ty: &Ty, env: &Env) -> bool {
    expands_to(
        ty,
        |ty| match get_node(ty) {
            Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 => name == sn::classes::SUPPORT_DYN,
            _ => false,
        },
        env,
    )
}

pub(crate) fn expands_to_var_or_intersection(ty: &Ty, env: &Env) -> bool {
    expands_to(
        ty,
        |ty| match get_node(ty) {
            Ty_::Tvar(_) | Ty_::Tintersection(_) => true,
            _ => false,
        },
        env,
    )
}

/// Helper function for inspecting types occuring inside a union from a top-level
/// pattern match
///
/// The pair is the type variable and the arraykey type, each as `deref` gives
/// it (`Reason.t * locl_ty_`, which the caller rebuilds with `mk`).
pub(crate) fn var_and_arraykey_opt(
    ty1: &Ty,
    ty2: &Ty,
    env: &mut Env,
) -> Option<((Reason, Ty_), (Reason, Ty_))> {
    let ty1 = env::expand_type(env, ty1.clone());
    let ty2 = env::expand_type(env, ty2.clone());
    // `match (deref ty1, deref ty2) with ((_, Tvar _) as tv, (_, (Tprim
    // Tarraykey | Tneg ..)) as ak) | (ak, tv) -> Some (tv, ak) | _ -> None`:
    // the nodes are looked at in place, and copied (`deref`) only when they
    // match.
    let is_tv = |ty: &Ty| matches!(get_node(ty), Ty_::Tvar(_));
    let is_ak = |ty: &Ty| {
        matches!(
            get_node(ty),
            Ty_::Tprim(Tprim::Tarraykey)
                | Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ArraykeyTag)))
        )
    };
    if is_tv(&ty1) && is_ak(&ty2) {
        Some((deref(&ty1), deref(&ty2)))
    } else if is_ak(&ty1) && is_tv(&ty2) {
        Some((deref(&ty2), deref(&ty1)))
    } else {
        None
    }
}

pub(crate) fn var_and_arraykey_exn(
    ty1: &Ty,
    ty2: &Ty,
    env: &mut Env,
) -> ((Reason, Ty_), (Reason, Ty_)) {
    match var_and_arraykey_opt(ty1, ty2, env) {
        Some((tv, ak)) => (tv, ak),
        _ => panic!(
            "Expected a pair of types, one of which a [Tvar] and the other [Tprim Tarraykey] or [Tneg (IsTag ArraykeyTag)]"
        ),
    }
}

pub(crate) fn expands_to_var_and_arraykey(ty1: &Ty, ty2: &Ty, env: &Env) -> bool {
    match var_and_arraykey_opt(ty1, ty2, &mut env.clone()) {
        Some(_) => true,
        _ => false,
    }
}

pub(crate) fn expands_to_class(ty: &Ty, env: &Env) -> bool {
    expands_to(
        ty,
        |ty| match get_node(ty) {
            Ty_::Tclass(..) => true,
            _ => false,
        },
        env,
    )
}

pub(crate) fn class_id_exn(ty: &Ty, env: &mut Env) -> PosId {
    let ty = env::expand_type(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tclass(id, _, _) => id.clone(),
        _ => panic!("This type is not a Tclass"),
    }
}

pub(crate) fn newtype_exn(ty: &Ty, env: &mut Env) -> (String, Vec<Ty>, Ty) {
    let ty = env::expand_type(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, bound) => (name.clone(), tyargs.clone(), bound.clone()),
        _ => panic!("This type is not a Tnewtype"),
    }
}

/// The OCaml returns an `S_set.t` and a `Typing_set.t`.
pub(crate) fn generic_lower_bounds(env: &Env, ty_super: &Ty) -> (SSet, typing_set::T) {
    fn fixpoint(env: &Env, new_set: typing_set::T, bounds_set: typing_set::T) -> typing_set::T {
        if typing_set::is_empty(&new_set) {
            bounds_set
        } else {
            let add_set = typing_set::fold(
                |ty, add_set| match get_node(ty) {
                    Ty_::Tgeneric(name) => {
                        let gen_bounds = env::get_lower_bounds(env, name);
                        typing_set::union(&add_set, &gen_bounds)
                    }
                    _ => add_set,
                },
                &new_set,
                typing_set::empty(),
            );
            let bounds_set = typing_set::union(&new_set, &bounds_set);
            let new_set = typing_set::diff(&add_set, &bounds_set);
            fixpoint(env, new_set, bounds_set)
        }
    }
    let lower_bounds = fixpoint(
        env,
        typing_set::singleton(ty_super.clone()),
        typing_set::empty(),
    );
    typing_set::fold(
        |bound_ty, (mut g_set, o_set): (SSet, typing_set::T)| match get_node(bound_ty) {
            Ty_::Tgeneric(name) => {
                g_set.insert(name.clone());
                (g_set, o_set)
            }
            _ => (g_set, typing_set::add(bound_ty.clone(), &o_set)),
        },
        &lower_bounds,
        (SSet::new(), typing_set::empty()),
    )
}

/// If it's clear from the syntax of the type that null isn't in ty, return true.
pub(crate) fn null_not_subtype(env: &Env, ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tprim(Tprim::Tnull | Tprim::Tvoid)
        | Ty_::Tgeneric(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tany(_)
        | Ty_::Toption(_)
        | Ty_::Tvar(_)
        | Ty_::Taccess(_)
        | Ty_::Tneg(_)
        | Ty_::Tintersection(_) => false,
        Ty_::Tunion(tys) => tys.iter().all(|ty| null_not_subtype(env, ty)),
        Ty_::Tclass(..)
        | Ty_::Tprim(_)
        | Ty_::Tnonnull
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tlabel(_)
        | Ty_::TvecOrDict(..)
        | Ty_::TclassPtr(_) => true,
        Ty_::Tnewtype(id, tyargs, _) => {
            // The environment is threaded through the rest of the check and
            // then dropped.
            let mut env = env.clone();
            let bound = t_utils::get_newtype_super(&mut env, get_reason(ty).clone(), id, tyargs);
            null_not_subtype(&env, &bound)
        }
        Ty_::Tdependent(_, bound) => null_not_subtype(env, bound),
    }
}

/// The OCaml continuation `simplify : unit -> env * TL.subtype_prop` closes
/// over the environment: here it is given it.
///
/// (`simplify_`, its only caller, has its body inlined, reading the option
/// once for its two calls.)
#[allow(dead_code)]
pub(crate) fn simplify_subtype_by_physical_equality(
    env: &mut Env,
    ty_sub: &Ty,
    ty_super: &Ty,
    simplify: impl FnOnce(&mut Env) -> tl::SubtypeProp,
) -> tl::SubtypeProp {
    if !env.genv.tcopt.tco_disable_physical_equality
        && typing_defs_core::phys_equal(ty_sub, ty_super)
    {
        tl::valid()
    } else {
        simplify(env)
    }
}

pub(crate) fn default_subtype(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    fail: subtype_env::Fail,
    Lhs {
        sub_supportdyn,
        ty_sub,
    }: Lhs,
    Rhs {
        super_like,
        ty_super,
        super_supportdyn,
    }: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // (`Env.expand_type` gives back any other type than a type variable:
    // the types are borrowed then.)
    let ty_super_expanded;
    let ty_super = match get_node(ty_super) {
        Ty_::Tvar(_) => {
            ty_super_expanded = env::expand_type(env, ty_super.clone());
            &ty_super_expanded
        }
        _ => ty_super,
    };
    let ty_sub_expanded;
    let ty_sub = match get_node(ty_sub) {
        Ty_::Tvar(_) => {
            ty_sub_expanded = env::expand_type(env, ty_sub.clone());
            &ty_sub_expanded
        }
        _ => ty_sub,
    };
    match get_node(ty_sub) {
        Ty_::Tvar(_) => match (subtype_env.is_dynamic_aware, get_node(ty_super)) {
            (true, Ty_::Tdynamic(_)) => {
                let r = get_reason(ty_super).clone();
                let ty_super = make_type::supportdyn_mixed(r);
                default_subtype_inner(
                    subtype_env,
                    this_ty,
                    fail,
                    Lhs {
                        sub_supportdyn,
                        ty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn,
                        ty_super: &ty_super,
                    },
                    env,
                )
            }
            (true, _) => mk_issubtype_prop(
                sub_supportdyn,
                true,
                env,
                InternalType::LoclType(ty_sub.clone()),
                InternalType::LoclType(ty_super.clone()),
            ),
            (false, _) => default_subtype_inner(
                subtype_env,
                this_ty,
                fail,
                Lhs {
                    sub_supportdyn,
                    ty_sub,
                },
                Rhs {
                    super_like,
                    super_supportdyn,
                    ty_super,
                },
                env,
            ),
        },
        Ty_::Tprim(Tprim::Tvoid) => {
            let r_sub = get_reason(ty_sub);
            let r = reason::implicit_upper_bound((reason::to_pos(r_sub), "mixed".to_string()));
            let prop = simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &make_type::mixed(r),
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super,
                },
                env,
            );
            if_unsat(|env| invalid(fail, env), env, prop)
        }
        Ty_::Tany(_) => {
            if subtype_env.no_top_bottom {
                mk_issubtype_prop(
                    sub_supportdyn,
                    subtype_env.is_dynamic_aware,
                    env,
                    InternalType::LoclType(ty_sub.clone()),
                    InternalType::LoclType(ty_super.clone()),
                )
            } else {
                valid(env)
            }
        }
        _ => default_subtype_inner(
            subtype_env,
            this_ty,
            fail,
            Lhs {
                sub_supportdyn,
                ty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn,
                ty_super,
            },
            env,
        ),
    }
}

pub(crate) fn default_subtype_inner(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    fail: subtype_env::Fail,
    Lhs {
        sub_supportdyn,
        ty_sub: lty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `~rhs:({ super_like; ty_super; _ } as rhs)`
    let super_like = rhs.super_like;
    let ty_super = rhs.ty_super;
    match get_node(&lty_sub) {
        Ty_::Tunion(tyl) => {
            let r_sub = get_reason(&lty_sub).clone();
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
                (sub_supportdyn, tyl),
                rhs,
                env,
            )
        }
        Ty_::Tvar(id) => {
            let id = *id;
            let r_sub = get_reason(&lty_sub);
            // Ensure that higher-ranked type parameters don't escape their scope
            let tvar_rank = env::rank_of_tvar(env, id);
            match check_rank(env, &ty_super, tvar_rank) {
                Some((generic_reason, generic_name)) => {
                    let error = secondary::T::Higher_rank_tparam_escape {
                        tvar_pos: reason::to_pos(r_sub),
                        pos_with_generic: reason::to_pos(get_reason(&ty_super)),
                        generic_reason,
                        generic_name,
                    };
                    let fail = subtype_env::fail_with_secondary_error(subtype_env, error);
                    invalid(fail, env)
                }
                _ => {
                    // For subtyping queries of the form
                    //
                    //   Tvar #id <: (Tvar #id | ...)
                    //
                    // `remove_tyvar_from_upper_bound` simplifies the union to
                    // `mixed`. This indicates that the query is discharged. If we find
                    // any other upper bound, we leave the subtyping query as it is.
                    let simplified_super_ty: InternalType =
                        typing_solver_utils::remove_tyvar_from_upper_bound(
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
                                InternalType::LoclType(lty_sub.clone()),
                                InternalType::LoclType(ty_super.clone()),
                            ),
                        }
                    }
                }
            }
        }
        Ty_::Tintersection(tyl) => {
            let r_sub = get_reason(&lty_sub).clone();
            // A & B <: C iif A <: C | !B
            //
            // The second branch matches without binding the environment that
            // `find_type_with_exact_negation` returns: it goes on with the
            // environment from before.
            match subtype_negation::find_type_with_exact_negation_opt(env, tyl) {
                Some((non_ty, tyl)) => {
                    let ty_super = t_utils::union(env, None, None, ty_super.clone(), non_ty);
                    let ty_sub = make_type::intersection(r_sub, tyl);
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
                }
                None => {
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
                        fail,
                        mk_prop,
                        |env: &Env, ty: Ty| {
                            env::update_reason(env, ty, |r_sub_prj| {
                                reason::prj_inter_sub(r_sub.clone(), r_sub_prj)
                            })
                        },
                        (sub_supportdyn, tyl),
                        rhs,
                        env,
                    )
                }
            }
        }
        Ty_::Tgeneric(_) if subtype_env.require_completeness => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(lty_sub.clone()),
            InternalType::LoclType(ty_super.clone()),
        ),
        Ty_::Tgeneric(name_sub) => {
            let r_generic = get_reason(&lty_sub).clone();
            match get_node(&ty_super) {
                Ty_::Tvar(id)
                    if env::rank_of_tparam(env, name_sub) > env::rank_of_tvar(env, *id) =>
                {
                    let r_super = get_reason(&ty_super);
                    let error = secondary::T::Higher_rank_tparam_escape {
                        tvar_pos: reason::to_pos(r_super),
                        pos_with_generic: reason::to_pos(&r_generic),
                        generic_reason: r_generic.clone(),
                        generic_name: Some(name_sub.clone()),
                    };
                    let fail = subtype_env::fail_with_secondary_error(subtype_env, error);
                    invalid(fail, env)
                }
                _ => {
                    match visited_goals::try_add_visited_generic_sub(
                        &subtype_env.visited,
                        name_sub,
                        ty_super.clone(),
                    ) {
                        None => {
                            // If we've seen this type parameter before then we must have gone
                            // round a cycle so we fail
                            invalid(fail, env)
                        }
                        Some(new_visited) => {
                            let subtype_env =
                                subtype_env::set_visited(subtype_env.clone(), new_visited);

                            let mk_prop =
                                |subtype_env: &subtype_env::T,
                                 this_ty: Option<&Ty>,
                                 lhs: Lhs,
                                 rhs: Rhs,
                                 env: &mut Env| {
                                    simplify(subtype_env, this_ty, lhs, rhs, env)
                                };
                            common::simplify_generic_l(
                                &subtype_env,
                                this_ty,
                                fail,
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
                                    ty_super,
                                },
                                env,
                            )
                        }
                    }
                }
            }
        }
        Ty_::Taccess(_) => invalid(fail, env),
        Ty_::Tnewtype(n, _tyl, ty) => {
            let r = get_reason(&lty_sub).clone();
            let mk_prop =
                |subtype_env: &subtype_env::T,
                 this_ty: Option<&Ty>,
                 lhs: Lhs,
                 rhs: Rhs,
                 env: &mut Env| { simplify(subtype_env, this_ty, lhs, rhs, env) };
            common::simplify_newtype_l(
                subtype_env,
                this_ty,
                mk_prop,
                (sub_supportdyn, r, n.clone(), ty.clone()),
                rhs,
                env,
            )
        }
        Ty_::Tdependent(dep_ty, ty) => {
            let r = get_reason(&lty_sub).clone();
            let mk_prop =
                |subtype_env: &subtype_env::T,
                 this_ty: Option<&Ty>,
                 lhs: Lhs,
                 rhs: Rhs,
                 env: &mut Env| { simplify(subtype_env, this_ty, lhs, rhs, env) };
            common::simplify_dependent_l(
                subtype_env,
                this_ty,
                mk_prop,
                (sub_supportdyn, r, dep_ty.clone(), ty.clone()),
                rhs,
                env,
            )
        }
        _ => invalid(fail, env),
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn simplify_sub_union(
    subtype_env: &subtype_env::T,
    sub_supportdyn: Option<&Reason>,
    this_ty: Option<&Ty>,
    super_like: bool,
    fail: subtype_env::Fail,
    lty_sub: &Ty,
    (r_super, lty_supers): (Reason, &[Ty]),
    env: &mut Env,
) -> tl::SubtypeProp {
    // We *know* that the assertion is unsatisfiable
    let invalid_env = |env: &mut Env| invalid(fail.clone(), env);
    let default_subtype_help = |env: &mut Env| {
        default_subtype(
            subtype_env,
            this_ty,
            fail.clone(),
            Lhs {
                sub_supportdyn,
                ty_sub: lty_sub,
            },
            Rhs {
                super_like,
                super_supportdyn: false,
                ty_super: &mk((r_super.clone(), Ty_::Tunion(lty_supers.to_vec()))),
            },
            env,
        )
    };
    // Identify cases heuristically where we just want to reduce t <: ~u to
    // t <: u with super-like set, and not also try t <: dynamic or run finish
    let avoid_disjunctions = |env: &mut Env, ty: &Ty| -> bool {
        let ty = env::expand_type(env, ty.clone());
        match (get_node(lty_sub), get_node(&ty)) {
            (Ty_::Tnewtype(n1, _, _), Ty_::Tnewtype(n2, _, _))
                if n1 == n2 && n1 != sn::classes::SUPPORT_DYN =>
            {
                true
            }
            _ => false,
        }
    };
    let finish = |env: &mut Env| match get_node(lty_sub) {
        Ty_::Tnewtype(..) | Ty_::Tdependent(..) | Ty_::Tgeneric(_) => default_subtype_help(env),
        _ => invalid_env(env),
    };
    let simplify_subtype_of_dynamic = |env: &mut Env| {
        simplify(
            subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn,
                ty_sub: lty_sub,
            },
            Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &make_type::dynamic(r_super.clone()),
            },
            env,
        )
    };
    let dyn_finish = |ty: &Ty, env: &mut Env| {
        let avoid = avoid_disjunctions(env, ty);
        if avoid {
            invalid_env(env)
        } else {
            // `let ( ||| ) = ( ||| ) ~fail in simplify_subtype_of_dynamic env ||| finish`
            let p1 = simplify_subtype_of_dynamic(env);
            or(fail.clone(), env, p1, finish)
        }
    };
    let stripped_dynamic =
        typing_dynamic_utils::try_strip_dynamic_from_union(None, env, lty_supers);
    match stripped_dynamic {
        Some((ty_dynamic, tyl)) => {
            // If subtype is literally `dynamic` then we're done
            if typing_defs::is_dynamic(lty_sub) {
                valid(env)
            } else {
                let ty = make_type::union(r_super.clone(), tyl);
                let ty = env::expand_type(env, ty);
                let delay_push = subtype_ask::is_sub_type_for_union_i(
                    env,
                    None,
                    &InternalType::LoclType(ty.clone()),
                    &InternalType::LoclType(make_type::supportdyn_mixed(r_super.clone())),
                );
                // This is Typing_logic_helpers.( ||| ) except with a bias towards p1
                //
                // (It shadows `( ||| )` from here on; `dyn_finish`, defined
                // above, uses the one of `Typing_logic_helpers`.)
                fn or_biased(
                    fail: &subtype_env::Fail,
                    env: &mut Env,
                    p1: tl::SubtypeProp,
                    f: impl FnOnce(&mut Env) -> tl::SubtypeProp,
                ) -> tl::SubtypeProp {
                    if tl::is_valid(&p1) {
                        p1
                    } else {
                        let p2 = f(env);
                        if tl::is_unsat(&p2) {
                            p1
                        } else if tl::is_unsat(&p1) {
                            p2
                        } else {
                            tl::disj(fail.get(), p1, p2)
                        }
                    }
                }
                // Implement the declarative subtyping rule C<~t1,...,~tn> <: ~C<t1,...,tn>
                // for a type C<t1,...,tn> that supports dynamic. Algorithmically,
                //   t <: ~C<t1,...,tn> iff
                //   t <: C<~t1,...,~tn> /\ C<~t1,...,~tn> <:D dynamic.
                // An SDT class C generalizes to other SDT constructors such as tuples and shapes.
                let try_push = |env: &mut Env| -> tl::SubtypeProp {
                    if delay_push {
                        dyn_finish(&ty, env)
                    } else {
                        // "Solve" type variables that are bounded from above and below by the same type.
                        // Push this through nullables. This addresses common completeness issues that
                        // bedevil like-pushing because of the disjunction that is generated.
                        fn solve_eq_tyvar(env: &mut Env, ty: Ty) -> Ty {
                            let ty = env::expand_type(env, ty);
                            match get_node(&ty) {
                                Ty_::Tvar(v) => {
                                    let v = *v;
                                    let lower_bounds = env::get_tyvar_lower_bounds(env, v);
                                    let (nulls, nonnulls) = ity_set::partition(
                                        |ty| match ty {
                                            InternalType::LoclType(t) => {
                                                typing_defs::is_prim(Tprim::Tnull, t)
                                            }
                                            _ => false,
                                        },
                                        &lower_bounds,
                                    );
                                    // Make sure that lower bounds [null;t] intersects with ?t upper bound
                                    let lower_bounds = if ity_set::is_empty(&nulls) {
                                        nonnulls
                                    } else {
                                        ity_set::map(
                                            |ity| match ity {
                                                InternalType::LoclType(t) => {
                                                    InternalType::LoclType(make_type::nullable(
                                                        reason::none(),
                                                        t.clone(),
                                                    ))
                                                }
                                                InternalType::ConstraintType(t) => {
                                                    InternalType::ConstraintType(t.clone())
                                                }
                                            },
                                            &nonnulls,
                                        )
                                    };
                                    let upper_bounds = env::get_tyvar_upper_bounds(env, v);
                                    let bounds = ity_set::inter(&lower_bounds, &upper_bounds);
                                    let bounds_list = ity_set::elements(&bounds);
                                    match bounds_list.as_slice() {
                                        [InternalType::LoclType(lty)] => lty.clone(),
                                        _ => ty,
                                    }
                                }
                                Ty_::Toption(ty1) => {
                                    let ty1 = solve_eq_tyvar(env, ty1.clone());
                                    mk((get_reason(&ty).clone(), Ty_::Toption(ty1)))
                                }
                                _ => ty,
                            }
                        }
                        let ty = solve_eq_tyvar(env, ty.clone());
                        // For generic parameters with lower bounds, try like-pushing wrt
                        // these lower bounds. For example, we want
                        // vec<~int> <: ~T if vec<int> <: T
                        let ty = match get_node(&ty) {
                            Ty_::Tgeneric(name) => {
                                let bounds = env::get_lower_bounds(env, name);
                                make_type::union(
                                    get_reason(&ty).clone(),
                                    typing_set::elements(&bounds),
                                )
                            }
                            _ => ty,
                        };
                        let opt_ty: Option<Ty> = typing_dynamic::try_push_like(env, &ty);
                        match opt_ty {
                            None => {
                                let istyvar = match get_node(&ty) {
                                    Ty_::Tvar(_) => true,
                                    Ty_::Toption(ty) => {
                                        let ty = env::expand_type(&mut env.clone(), ty.clone());
                                        typing_defs::is_tyvar(&ty)
                                    }
                                    _ => false,
                                };
                                if istyvar {
                                    let p1 = simplify(
                                        subtype_env,
                                        this_ty,
                                        Lhs {
                                            sub_supportdyn,
                                            ty_sub: lty_sub,
                                        },
                                        Rhs {
                                            super_like: true,
                                            super_supportdyn: false,
                                            ty_super: &ty,
                                        },
                                        env,
                                    );
                                    or_biased(&fail, env, p1, |env| dyn_finish(&ty, env))
                                } else {
                                    dyn_finish(&ty, env)
                                }
                            }
                            Some(ty) => {
                                let ty: Ty = ty;
                                let simplify_pushed_like = |env: &mut Env| {
                                    let p = simplify(
                                        &subtype_env::set_is_dynamic_aware(
                                            subtype_env.clone(),
                                            true,
                                        ),
                                        this_ty,
                                        Lhs {
                                            sub_supportdyn: None,
                                            ty_sub: &ty,
                                        },
                                        Rhs {
                                            super_like: false,
                                            super_supportdyn: false,
                                            ty_super: &ty_dynamic,
                                        },
                                        env,
                                    );
                                    and(env, p, |env| {
                                        simplify(
                                            &subtype_env::T {
                                                ignore_likes: true,
                                                ..subtype_env.clone()
                                            },
                                            this_ty,
                                            Lhs {
                                                sub_supportdyn,
                                                ty_sub: lty_sub,
                                            },
                                            Rhs {
                                                super_like: false,
                                                super_supportdyn: false,
                                                ty_super: &ty,
                                            },
                                            env,
                                        )
                                    })
                                };

                                // `env |> simplify_pushed_like ||| dyn_finish ty`
                                let p1 = simplify_pushed_like(env);
                                or_biased(&fail, env, p1, |env| dyn_finish(&ty, env))
                            }
                        }
                    }
                };
                let p1 = simplify(
                    &subtype_env::T {
                        ignore_likes: delay_push,
                        ..subtype_env.clone()
                    },
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: lty_sub,
                    },
                    Rhs {
                        super_like: delay_push,
                        super_supportdyn: false,
                        ty_super: &ty,
                    },
                    env,
                );
                or_biased(&fail, env, p1, try_push)
            }
        }
        _ => {
            // It's sound to reduce t <: t1 | t2 to (t <: t1) || (t <: t2). But
            // not complete e.g. consider (t1 | t3) <: (t1 | t2) | (t2 | t3).
            // But we deal with unions on the left first (see case above), so this
            // particular situation won't arise.
            // TODO: identify under what circumstances this reduction is complete.
            // TODO(T120921930): Don't do this if require_completeness is set.
            //
            // `errs` is the OCaml list, which is built by adding at its head:
            // here at the end of the vector, which is reversed at the end.
            // `props` is in the order of `List.rev props`.
            // (`fail` is the first error of the list, the last of the vector
            // once reversed; it is added only when the disjunction is built,
            // so that it is not built when a disjunct is valid: see
            // `subtype_env::fail_deferred`. The vector is not allocated until
            // a disjunct fails.)
            let mut errs: Vec<Option<typing_error::T>> = Vec::new();
            let mut props: Vec<tl::SubtypeProp> = vec![];
            for ty_super in lty_supers.iter() {
                let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
                    reason::prj_union_super(r_super.clone(), r_super_prj)
                });

                let prop = simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn,
                        ty_sub: lty_sub,
                    },
                    Rhs {
                        super_like,
                        super_supportdyn: false,
                        ty_super: &ty_super,
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
            tl::SubtypeProp::Disj(
                typing_error::intersect_opt(
                    errs.into_iter()
                        .rev()
                        .chain(std::iter::once(fail.get()))
                        .flatten()
                        .collect(),
                ),
                props,
            )
        }
    }
}

// == Function subtyping ==================================================

pub(crate) fn simplify_subtype_params_with_variadic(
    subtype_env: &subtype_env::T,
    (r_super, idx_super, fn_param_supers): (Reason, isize, &[FunParam]),
    (r_sub, idx_sub, ty_sub): (Reason, isize, Ty),
    env: &mut Env,
) -> tl::SubtypeProp {
    match fn_param_supers {
        [] => valid(env),
        [
            FunParam {
                type_: ty_super, ..
            },
            fn_param_supers @ ..,
        ] => {
            let param_prop = {
                let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
                    reason::prj_fn_param(
                        r_sub.clone(),
                        r_super.clone(),
                        r_super_prj,
                        idx_sub,
                        idx_super,
                    )
                });
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_super,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_sub,
                    },
                    env,
                )
            };
            and(env, param_prop, |env| {
                simplify_subtype_params_with_variadic(
                    subtype_env,
                    (r_super, idx_super + 1, fn_param_supers),
                    (r_sub, idx_sub, ty_sub),
                    env,
                )
            })
        }
    }
}

pub(crate) fn simplify_subtype_implicit_params(
    subtype_env: &subtype_env::T,
    FunImplicitParams {
        capability: sub_cap,
    }: &FunImplicitParams,
    FunImplicitParams {
        capability: super_cap,
    }: &FunImplicitParams,
    env: &mut Env,
) -> tl::SubtypeProp {
    if typechecker_options::any_coeffects(&env::get_tcopt(env)) {
        let expected = typing_coeffects::get_type(sub_cap);
        let got = typing_coeffects::get_type(super_cap);
        let reasons = secondary::T::Coeffect_subtyping {
            pos: get_pos(&got),
            cap: typing_coeffects::pretty(env, &got),
            pos_expected: get_pos(&expected),
            cap_expected: typing_coeffects::pretty(env, &expected),
        };
        let subtype_env = subtype_env::map_on_error(subtype_env.clone(), |on_error| {
            let err = typing_error::apply_reasons(reasons, on_error);
            reasons_callback::always(err)
        });
        match (sub_cap, super_cap) {
            (Capability::CapTy(sub), Capability::CapTy(super_)) => simplify(
                &subtype_env,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &super_,
                },
                env,
            ),
            (Capability::CapTy(sub), Capability::CapDefaults(_p)) => simplify(
                &subtype_env,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &sub,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &got,
                },
                env,
            ),
            (Capability::CapDefaults(_p), Capability::CapTy(super_)) => simplify(
                &subtype_env,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &expected,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &super_,
                },
                env,
            ),
            (Capability::CapDefaults(_p1), Capability::CapDefaults(_p2)) => valid(env),
        }
    } else {
        valid(env)
    }
}

pub(crate) fn simplify_supertype_params_with_variadic(
    subtype_env: &subtype_env::T,
    (r_sub, idx_sub, fn_param_subs): (Reason, isize, &[FunParam]),
    (r_super, idx_super, ty_super): (Reason, isize, Ty),
    env: &mut Env,
) -> tl::SubtypeProp {
    match fn_param_subs {
        [] => valid(env),
        [FunParam { type_: ty_sub, .. }, fn_param_subs @ ..] => {
            let param_prop = {
                let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
                    reason::prj_fn_param(
                        r_sub.clone(),
                        r_super.clone(),
                        r_super_prj,
                        idx_sub,
                        idx_super,
                    )
                });
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_super,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_sub,
                    },
                    env,
                )
            };
            and(env, param_prop, |env| {
                simplify_supertype_params_with_variadic(
                    subtype_env,
                    (r_sub, idx_sub + 1, fn_param_subs),
                    (r_super, idx_super, ty_super),
                    env,
                )
            })
        }
    }
}

pub(crate) fn simplify_param_modes(
    subtype_env: &subtype_env::T,
    fn_param_sub: &FunParam,
    fn_param_super: &FunParam,
    env: &Env,
) -> tl::SubtypeProp {
    let FunParam {
        pos: pos1,
        name: name1,
        ..
    } = fn_param_super;
    let FunParam {
        pos: pos2,
        name: name2,
        ..
    } = fn_param_sub;
    // Usually an arity check covers this case, except in the case that a splat parameter is preceded by an optional parameter
    if get_fp_is_optional(fn_param_super)
        && (!get_fp_is_optional(fn_param_sub))
        && name1.is_none()
        && name2.is_none()
    {
        invalid(
            subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Fun_param_required_but_expected_optional {
                        pos: pos2.clone(),
                        decl_pos: pos1.clone(),
                        param_names: vec![],
                    },
                    on_error,
                )
            }),
            env,
        )
    } else {
        match (get_fp_mode(fn_param_super), get_fp_mode(fn_param_sub)) {
            (ParamMode::FPnormal, ParamMode::FPnormal)
            | (ParamMode::FPinout, ParamMode::FPinout) => valid(env),
            (ParamMode::FPnormal, ParamMode::FPinout) => invalid(
                subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::Inoutness_mismatch {
                            pos: pos2.clone(),
                            decl_pos: pos1.clone(),
                        },
                        on_error,
                    )
                }),
                env,
            ),
            (ParamMode::FPinout, ParamMode::FPnormal) => invalid(
                subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::Inoutness_mismatch {
                            pos: pos1.clone(),
                            decl_pos: pos2.clone(),
                        },
                        on_error,
                    )
                }),
                env,
            ),
        }
    }
}

pub(crate) fn simplify_param_accept_disposable(
    subtype_env: &subtype_env::T,
    fn_param_sub: &FunParam,
    fn_param_super: &FunParam,
    env: &Env,
) -> tl::SubtypeProp {
    let FunParam { pos: pos1, .. } = fn_param_super;
    let FunParam { pos: pos2, .. } = fn_param_sub;
    match (
        get_fp_accept_disposable(fn_param_super),
        get_fp_accept_disposable(fn_param_sub),
    ) {
        (true, false) => invalid(
            subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Accept_disposable_invariant {
                        pos: pos1.clone(),
                        decl_pos: pos2.clone(),
                    },
                    on_error,
                )
            }),
            env,
        ),
        (false, true) => invalid(
            subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Accept_disposable_invariant {
                        pos: pos2.clone(),
                        decl_pos: pos1.clone(),
                    },
                    on_error,
                )
            }),
            env,
        ),
        (_, _) => valid(env),
    }
}

pub(crate) fn readonly_subtype(r_sub: bool, r_super: bool) -> bool {
    match (r_sub, r_super) {
        (true, false) => {
            false // A readonly value is a supertype of a mutable one
        }
        _ => true,
    }
}

pub(crate) fn simplify_param_readonly(
    subtype_env: &subtype_env::T,
    fn_param_sub: &FunParam,
    fn_param_super: &FunParam,
    env: &Env,
) -> tl::SubtypeProp {
    let FunParam { pos: pos1, .. } = fn_param_super;
    let FunParam { pos: pos2, .. } = fn_param_sub;
    if (!subtype_env.ignore_readonly)
        && (!get_fp_ignore_readonly_error(fn_param_sub))
        && (!get_fp_ignore_readonly_error(fn_param_super))
        && !readonly_subtype(
            get_fp_readonly(fn_param_super),
            get_fp_readonly(fn_param_sub),
        )
    {
        invalid(
            subtype_env.on_error.clone().map(|on_error| {
                let pos1_ = pos1.clone();
                let pos2_ = pos2.clone();
                typing_error::apply_reasons(
                    secondary::T::Readonly_mismatch {
                        pos: pos1.clone(),
                        kind: secondary::ReadonlyMismatchKind::param,
                        reason_sub: Lazy::new(move || {
                            vec![Message(pos2_, "This parameter is mutable".into())]
                        }),
                        reason_super: Lazy::new(move || {
                            vec![Message(pos1_, "But this parameter is readonly".into())]
                        }),
                    },
                    on_error,
                )
            }),
            env,
        )
    } else {
        valid(env)
    }
}

/// Helper function for subtyping on function types: performs all checks that
/// don't involve actual types:
///   <<__ReturnDisposable>> attribute
///   variadic arity
///  <<__Policied>> attribute
///  Readonlyness
///
/// The OCaml takes no environment and returns a proposition.
pub(crate) fn simplify_subtype_funs_attributes(
    subtype_env: &subtype_env::T,
    (r_sub, ft_sub): (&Reason, &FunType),
    (r_super, ft_super): (&Reason, &FunType),
) -> tl::SubtypeProp {
    let p_sub = reason::to_pos(r_sub);
    let p_super = reason::to_pos(r_super);
    let splat_super = match ft_super.params.last() {
        Some(fp) => get_fp_splat(fp),
        None => false,
    };
    // The six results are made by one `let ... and ...`; making them has no
    // effect.
    //
    // Readonly this is contravariant, so check ft_super_ro <: ft_sub_ro
    let readonly_this_err: Result<(), Option<typing_error::T>> = if (!subtype_env.ignore_readonly)
        && !readonly_subtype(get_ft_readonly_this(ft_super), get_ft_readonly_this(ft_sub))
    {
        Err(subtype_env.on_error.clone().map(|on_error| {
            let p_sub_ = p_sub.clone();
            let p_super_ = p_super.clone();
            typing_error::apply_reasons(
                secondary::T::Readonly_mismatch {
                    pos: p_sub.clone(),
                    kind: secondary::ReadonlyMismatchKind::fn_,
                    reason_sub: Lazy::new(move || {
                        vec![Message(
                            p_sub_,
                            "This function is not marked readonly".into(),
                        )]
                    }),
                    reason_super: Lazy::new(move || {
                        vec![Message(p_super_, "This function is marked readonly".into())]
                    }),
                },
                on_error,
            )
        }))
    } else {
        Ok(())
    };
    // Readonly return is covariant, so check ft_sub <: ft_super
    let readonly_ret_err: Result<(), Option<typing_error::T>> = if (!subtype_env.ignore_readonly)
        && !readonly_subtype(
            get_ft_returns_readonly(ft_sub),
            get_ft_returns_readonly(ft_super),
        ) {
        Err(subtype_env.on_error.clone().map(|on_error| {
            let p_sub_ = p_sub.clone();
            let p_super_ = p_super.clone();
            typing_error::apply_reasons(
                secondary::T::Readonly_mismatch {
                    pos: p_sub.clone(),
                    kind: secondary::ReadonlyMismatchKind::fn_return,
                    reason_sub: Lazy::new(move || {
                        vec![Message(
                            p_sub_,
                            "This function returns a readonly value".into(),
                        )]
                    }),
                    reason_super: Lazy::new(move || {
                        vec![Message(
                            p_super_,
                            "This function does not return a readonly value".into(),
                        )]
                    }),
                },
                on_error,
            )
        }))
    } else {
        Ok(())
    };
    let return_disposable_err: Result<(), Option<typing_error::T>> =
        if get_ft_return_disposable(ft_sub) != get_ft_return_disposable(ft_super) {
            Err(subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Return_disposable_mismatch {
                        pos_super: p_super.clone(),
                        pos_sub: p_sub.clone(),
                        is_marked_return_disposable: get_ft_return_disposable(ft_super),
                    },
                    on_error,
                )
            }))
        } else {
            Ok(())
        };
    let arity_required_err: Result<(), Option<typing_error::T>> = {
        let (arity_required_sub, _sub_required_named_params) =
            typing_defs::arity_and_names_required(ft_sub);
        let (arity_required_super, _super_required_named_params) =
            typing_defs::arity_and_names_required(ft_super);
        if (!splat_super) && !(arity_required_sub <= arity_required_super) {
            Err(subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Fun_too_many_args {
                        expected: arity_required_super,
                        actual: arity_required_sub,
                        pos: p_sub.clone(),
                        decl_pos: p_super.clone(),
                    },
                    on_error,
                )
            }))
        } else {
            Ok(())
        }
    };
    let named_params_err: Result<(), Option<typing_error::T>> = {
        let typing_named_params::Mismatch {
            extra_names,
            missing_names,
            too_optional_names,
            missing_named_variadic,
        } = typing_named_params::find_names_mismatch(ft_sub, ft_super);
        // If the expected type has a named-variadic parameter but the actual
        // does not, surface it as a "missing named argument: ..." error
        // (matching the naming convention used by decl_hint.ml when it lowers
        // the named-variadic to a param with fp_name = Some "...").
        let missing_names = if missing_named_variadic {
            let mut names = vec!["...".to_string()];
            names.extend(missing_names);
            names
        } else {
            missing_names
        };
        if !(extra_names.is_empty() && missing_names.is_empty() && too_optional_names.is_empty()) {
            Err(subtype_env.on_error.clone().map(|on_error| {
                let apply_if_nonempty =
                    |names: &[String], f: &dyn Fn() -> secondary::T| -> Vec<typing_error::T> {
                        if names.is_empty() {
                            vec![]
                        } else {
                            vec![typing_error::apply_reasons(f(), on_error.clone())]
                        }
                    };
                // `multiple (l1 @ l2 @ l3)`: making the three lists has no
                // effect.
                let mut errs =
                    apply_if_nonempty(&extra_names, &|| secondary::T::Fun_extra_named_args {
                        extra_names: extra_names.clone(),
                        pos: p_sub.clone(),
                        decl_pos: p_super.clone(),
                    });
                errs.extend(apply_if_nonempty(&missing_names, &|| {
                    secondary::T::Fun_missing_named_args {
                        missing_names: missing_names.clone(),
                        pos: p_sub.clone(),
                        decl_pos: p_super.clone(),
                    }
                }));
                errs.extend(apply_if_nonempty(&too_optional_names, &|| {
                    secondary::T::Fun_param_required_but_expected_optional {
                        param_names: too_optional_names.clone(),
                        pos: p_sub.clone(),
                        decl_pos: p_super.clone(),
                    }
                }));
                typing_error::multiple(errs)
            }))
        } else {
            Ok(())
        }
    };
    let variadic_err: Result<(), Option<typing_error::T>> = {
        fn positional_variadic_of(ft: &FunType) -> Option<&FunParam> {
            if typing_defs::ft_has_positional_variadic(ft) {
                typing_defs::ft_params_without_named_variadic(ft).last()
            } else {
                None
            }
        }
        let ft_sub_variadic = positional_variadic_of(ft_sub);
        let ft_super_variadic = positional_variadic_of(ft_super);

        match (ft_sub_variadic, ft_super_variadic) {
            (Some(FunParam { name: None, .. }), Some(FunParam { name: Some(_), .. })) => {
                // The HHVM runtime ignores "..." entirely, but knows about
                // "...$args"; for contexts for which the runtime enforces method
                // compatibility (currently, inheritance from abstract/interface
                // methods), letting "..." override "...$args" would result in method
                // compatibility errors at runtime.
                Err(subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::Fun_variadicity_hh_vs_php56 {
                            pos: p_sub.clone(),
                            decl_pos: p_super.clone(),
                        },
                        on_error,
                    )
                }))
            }
            (None, None) if !splat_super => {
                let count_positional_params = |ft: &FunType| {
                    ft.params.iter().filter(|fp| !get_fp_is_named(fp)).count() as isize
                };
                let sub_max = count_positional_params(ft_sub);
                let super_max = count_positional_params(ft_super);
                if sub_max < super_max {
                    Err(subtype_env.on_error.clone().map(|on_error| {
                        typing_error::apply_reasons(
                            secondary::T::Fun_too_few_args {
                                pos: p_sub.clone(),
                                decl_pos: p_super.clone(),
                                expected: super_max,
                                actual: sub_max,
                            },
                            on_error,
                        )
                    }))
                } else {
                    Ok(())
                }
            }
            (None, Some(_)) => Err(subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::Fun_unexpected_nonvariadic {
                        pos: p_sub.clone(),
                        decl_pos: p_super.clone(),
                    },
                    on_error,
                )
            })),
            (_, _) => Ok(()),
        }
    };
    // Collect attribute errors
    let errs: Vec<Option<typing_error::T>> = vec![
        readonly_this_err,
        readonly_ret_err,
        return_disposable_err,
        arity_required_err,
        named_params_err,
        variadic_err,
    ]
    .into_iter()
    .filter_map(|res| res.err())
    .collect();
    // If we have no errors, return valid
    if errs.is_empty() {
        tl::valid()
    } else {
        // Otherwise, combine the errors and return invalid
        tl::invalid(typing_error::multiple_opt(
            errs.into_iter().flatten().collect(),
        ))
    }
}

/// Construct a tuple type from the parameters in a function type.
/// This is used for subtyping function types at least one of which contains
/// a splat parameter e.g. consider
///
///   (function(t1', _, tm', ...T):r') <:
///   (function(t1, _, tm, u1, _, un, optional v1, _, vk, w...):r <:
///
/// (Here ...T is a splat parameter and w... is a variadic).
///
/// We need to subtype t1<:t1', _, tm<:tm' and r'<:r as normal but
/// splat parameter T is compared a tuple of the remaining parameters in the supertype
/// i.e. (u1, _, un, optional v1, _, optional vk, w...) <: T
///
/// If there is a splat parameter on both sides, e.g.
///   (function(t1',_,tm', ...T'):r') <:
///   (function(t1, _, tm, u1, _, un, ...T):r)
///
/// then we use splat in a tuple:
///
///   (u1, _, un, ...T) <: T'
pub(crate) fn params_to_tuple(
    fun_type_pos: PosOrDecl,
    is_variadic: bool,
    fn_params: &[FunParam],
) -> Ty {
    // We construct a position that spans all the parameters that we are gathering.
    // If there are no parameters, just use the position from the function type
    let acc_pos = match fn_params {
        [] => fun_type_pos.clone(),
        [
            FunParam {
                pos: fp_pos,
                type_: fp_type,
                ..
            },
            ..,
        ] => pos_or_decl::merge(&get_pos(fp_type), fp_pos),
    };
    // `acc_required` and `acc_optional` are the OCaml lists, which are built
    // by adding at their head and reversed at the end: here they are built
    // in their final order.
    fn aux(
        is_variadic: bool,
        fn_params: &[FunParam],
        acc_pos: PosOrDecl,
        mut acc_required: Vec<Ty>,
        mut acc_optional: Vec<Ty>,
        acc_variadic: Ty,
        acc_splat: Option<Ty>,
    ) -> Ty {
        match fn_params {
            [] => mk((
                reason::tuple_from_splat(acc_pos),
                Ty_::Ttuple(TupleType {
                    required: acc_required,
                    optional: acc_optional,
                    extra: match acc_splat {
                        None => TupleExtra::Tvariadic(acc_variadic),
                        Some(t) => TupleExtra::Tsplat(t),
                    },
                }),
            )),
            [
                fn_param @ FunParam {
                    type_: fp_type,
                    pos: fp_pos,
                    ..
                },
                fn_params @ ..,
            ] => {
                let acc_pos = if fn_params.is_empty() {
                    pos_or_decl::merge(&acc_pos, fp_pos)
                } else {
                    acc_pos
                };
                let (acc_variadic, acc_splat) = if fn_params.is_empty() && is_variadic {
                    (fp_type.clone(), acc_splat)
                } else if fn_params.is_empty() && get_fp_splat(fn_param) {
                    (acc_variadic, Some(fp_type.clone()))
                } else if get_fp_is_optional(fn_param) {
                    acc_optional.push(fp_type.clone());
                    (acc_variadic, acc_splat)
                } else {
                    acc_required.push(fp_type.clone());
                    (acc_variadic, acc_splat)
                };
                aux(
                    is_variadic,
                    fn_params,
                    acc_pos,
                    acc_required,
                    acc_optional,
                    acc_variadic,
                    acc_splat,
                )
            }
        }
    }
    aux(
        is_variadic,
        fn_params,
        acc_pos,
        vec![],
        vec![],
        make_type::nothing(reason::witness_from_decl(fun_type_pos)),
        None,
    )
}

pub(crate) fn simplify_subtype_params(
    subtype_env: &subtype_env::T,
    arg_posl: Option<Vec<Pos>>,
    for_override: bool,
    (r_sub, idx_sub, all_params_sub, variadic_sub_ty): (Reason, isize, &[FunParam], bool),
    (r_super, idx_super, all_params_super, variadic_super_ty): (Reason, isize, &[FunParam], bool),
    env: &mut Env,
) -> tl::SubtypeProp {
    // We use this for matching parameters fn_param_sub and fn_param_super
    // Below we match using two separate strategies: by name (for named params) and by position
    let simplify_subtype_for_matching_parameters = |arg_pos: Option<Pos>,
                                                    subtype_env: &subtype_env::T,
                                                    fn_param_sub: &FunParam,
                                                    fn_param_super: &FunParam,
                                                    env: &mut Env|
     -> tl::SubtypeProp {
        let FunParam { type_: ty_sub, .. } = fn_param_sub;
        let FunParam {
            type_: ty_super, ..
        } = fn_param_super;
        // Construct the subtype proposition for the two parameters; function
        // paramaters are contravariant unless they are marked with `inout`
        // in which case they are typed as invariant
        let subtype_env_for_param = {
            // When overriding in Sound Dynamic, we treat any dynamic-aware subtype of dynamic as a
            // subtype of the dynamic type itself
            let subtype_env_for_param = match get_node(ty_sub) {
                Ty_::Tdynamic(_) if for_override => {
                    subtype_env::set_is_dynamic_aware(subtype_env.clone(), true)
                }
                _ => subtype_env.clone(),
            };
            let subtype_env_for_param = match arg_pos {
                Some(pos) => subtype_env::map_on_error(subtype_env_for_param, |on_error| {
                    reasons_callback::T::With_claim(
                        std::rc::Rc::new(on_error),
                        Lazy::new(move || Message(pos, "Invalid argument".into())),
                    )
                }),
                None => subtype_env_for_param,
            };
            if get_fp_ignore_readonly_error(fn_param_sub)
                || get_fp_ignore_readonly_error(fn_param_super)
            {
                subtype_env::T {
                    ignore_readonly: true,
                    ..subtype_env_for_param
                }
            } else {
                subtype_env_for_param
            }
        };
        let subtype_env_for_param = &subtype_env_for_param;
        // Construct the contravariant subtype proposition
        let subty_prop_contra = |is_inout: bool, env: &mut Env| {
            // Update the provenance on the super type:
            //  i) Reverse the direction of flow for the containing function-type reasons
            //  ii) Record the projection into the ith function arg, treated as contravariant, of that function-type
            //  iii) Record the flow from the supertype into that arg
            let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
                if is_inout {
                    reason::prj_fn_param_inout_contra(
                        r_sub.clone(),
                        r_super.clone(),
                        r_super_prj,
                        idx_sub,
                        idx_super,
                    )
                } else {
                    reason::prj_fn_param(
                        r_sub.clone(),
                        r_super.clone(),
                        r_super_prj,
                        idx_sub,
                        idx_super,
                    )
                }
            });
            simplify(
                subtype_env_for_param,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &ty_super,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_sub,
                },
                env,
            )
        };
        // For parameters with the `inout` calling convention also construct
        // the covariant subtype proposition
        //
        // (The OCaml builds `subty_prop_co` before the checks of the calling
        // conventions below: updating a reason and applying `simplify`
        // partially have no effect, so it is built when it is used.)
        let subty_prop =
            |env: &mut Env| match (get_fp_mode(fn_param_sub), get_fp_mode(fn_param_super)) {
                (ParamMode::FPinout, ParamMode::FPinout) => {
                    let subty_prop_co = {
                        // Update the provenance for the subtype:
                        //  i) Record the flow from the parent function types
                        //  ii) Record the projection in the ith arg, treated as covariant, of that function
                        //  iii) Record the flow from the subtype into that arg
                        let ty_sub = env::update_reason(env, ty_sub.clone(), |r_sub_prj| {
                            reason::prj_fn_param_inout_co(
                                r_sub.clone(),
                                r_sub_prj,
                                r_super.clone(),
                                idx_sub,
                                idx_super,
                            )
                        });
                        move |env: &mut Env| {
                            simplify(
                                subtype_env_for_param,
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
                                env,
                            )
                        }
                    };
                    let p = subty_prop_contra(true, env);
                    and(env, p, subty_prop_co)
                }
                _ => subty_prop_contra(false, env),
            };
        // Check that the calling conventions of the params are compatible.
        let p = simplify_param_modes(subtype_env, fn_param_sub, fn_param_super, env);
        let p = and(env, p, |env| {
            simplify_param_readonly(subtype_env, fn_param_sub, fn_param_super, env)
        });
        let p = and(env, p, |env| {
            simplify_param_accept_disposable(subtype_env, fn_param_sub, fn_param_super, env)
        });
        and(env, p, subty_prop)
    };
    let partition_by_namedness = |fps: &[FunParam]| -> (Vec<FunParam>, Vec<FunParam>) {
        fps.iter()
            .cloned()
            .partition(|fp| named_params::name_of_named_param(fp).is_some())
    };
    let (named_params_sub, positional_params_sub) = partition_by_namedness(all_params_sub);
    let (named_params_super, positional_params_super) = partition_by_namedness(all_params_super);
    // Handle named parameters
    let prop = {
        let mut name_to_named_param_super: BTreeMap<String, &FunParam> = BTreeMap::new();
        for fp in named_params_super.iter() {
            match named_params::name_of_named_param(fp) {
                Some(name) => {
                    // `Duplicate -> acc`: the first parameter of a name is kept.
                    name_to_named_param_super.entry(name).or_insert(fp);
                }
                None => {}
            }
        }
        let mut prop = tl::valid();
        for fp_sub in named_params_sub.iter() {
            // `Option.value ~default:(env, prop) @@ let* ... let+ ...`
            if let Some(name) = named_params::name_of_named_param(fp_sub) {
                if let Some(fp_super) = name_to_named_param_super.get(&name) {
                    // we can safely ignore when no matching named parameter is found, since arity checks happen elsewhere
                    prop = and(env, prop, |env| {
                        simplify_subtype_for_matching_parameters(
                            None,
                            subtype_env,
                            fp_sub,
                            fp_super,
                            env,
                        )
                    });
                }
            }
        }
        prop
    };
    and(env, prop, |env| {
        match (
            positional_params_sub.as_slice(),
            positional_params_super.as_slice(),
        ) {
            // When either list runs out, we still have to typecheck that
            // the remaining portion sub/super types with the other's variadic.
            // For example, if
            // ChildClass {
            //   public function a(int $x = 0, string ... $args) // superl = [int], super_var = string
            // }
            // overrides
            // ParentClass {
            //   public function a(string ... $args) // subl = [], sub_var = string
            // }
            // , there should be an error because the first argument will be checked against
            // int, not string that is, ChildClass::a("hello") would crash,
            // but ParentClass::a("hello") wouldn't.
            //
            // Similarly, if th{ subtype_env with Subtype_env.ignore_likes = delay_push }e other list is longer, aka
            // ChildClass  extends ParentClass {
            //   public function a(mixed ... $args) // superl = [], super_var = mixed
            // }
            // overrides
            // ParentClass {
            //   //subl = [string], sub_var = string
            //   public function a(string $x = 0, string ... $args)
            // }
            // It should also check that string is a subtype of mixed.
            ([FunParam { type_: ty_sub, .. }], _) if variadic_sub_ty => {
                simplify_subtype_params_with_variadic(
                    subtype_env,
                    (r_super.clone(), idx_super, &positional_params_super),
                    (r_sub.clone(), idx_sub, ty_sub.clone()),
                    env,
                )
            }
            (
                _,
                [
                    FunParam {
                        type_: ty_super, ..
                    },
                ],
            ) if variadic_super_ty => simplify_supertype_params_with_variadic(
                subtype_env,
                (r_sub.clone(), idx_sub, &positional_params_sub),
                (r_super.clone(), idx_super, ty_super.clone()),
                env,
            ),
            // Two splat parameters are just compared directly
            (
                [fn_param_sub @ FunParam { type_: ty_sub, .. }],
                [
                    fn_param_super @ FunParam {
                        type_: ty_super, ..
                    },
                ],
            ) if get_fp_splat(fn_param_sub) && get_fp_splat(fn_param_super) => simplify(
                subtype_env,
                None,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &ty_super,
                },
                Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_sub,
                },
                env,
            ),
            // If supertype is a splat parameter then package up remaining parameters in subtype as
            // a tuple and compare that
            (
                _,
                [
                    fn_param_super @ FunParam {
                        type_: ty_super, ..
                    },
                ],
            ) if get_fp_splat(fn_param_super) => {
                let tuple_ty_sub = params_to_tuple(
                    reason::to_pos(&r_sub),
                    variadic_sub_ty,
                    &positional_params_sub,
                );
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &ty_super,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &tuple_ty_sub,
                    },
                    env,
                )
            }
            // If subtype is a splat parameter then package up remaining parameters in supertype as
            // a tuple and compare that
            ([fn_param_sub @ FunParam { type_: ty_sub, .. }], _) if get_fp_splat(fn_param_sub) => {
                let tuple_ty = params_to_tuple(
                    reason::to_pos(&r_super),
                    variadic_super_ty,
                    &positional_params_super,
                );
                simplify(
                    subtype_env,
                    None,
                    Lhs {
                        sub_supportdyn: None,
                        ty_sub: &tuple_ty,
                    },
                    Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_sub,
                    },
                    env,
                )
            }
            // We've run out of parameters
            ([], [_, ..]) => {
                let splat_super = match positional_params_super.last() {
                    Some(fp) => get_fp_splat(fp),
                    None => false,
                };
                if splat_super {
                    let fail = subtype_env.on_error.clone().map(|on_error| {
                        typing_error::apply_reasons(
                            secondary::T::Fun_too_few_args {
                                pos: reason::to_pos(&r_sub),
                                decl_pos: reason::to_pos(&r_super),
                                actual: idx_sub,
                                expected: positional_params_super.len() as isize,
                            },
                            on_error,
                        )
                    });
                    invalid(fail, env)
                } else {
                    valid(env)
                }
            }
            (_, []) => valid(env),
            (
                [fn_param_sub, positional_params_sub @ ..],
                [fn_param_super, positional_params_super @ ..],
            ) => {
                let (arg_pos, arg_posl) = match &arg_posl {
                    None => (None, None),
                    Some(ps) => match ps.split_first() {
                        None => (None, None),
                        Some((p, ps)) => (Some(p.clone()), Some(ps.to_vec())),
                    },
                };
                let p = simplify_subtype_for_matching_parameters(
                    arg_pos,
                    subtype_env,
                    fn_param_sub,
                    fn_param_super,
                    env,
                );
                and(env, p, |env| {
                    simplify_subtype_params(
                        subtype_env,
                        arg_posl,
                        for_override,
                        (
                            r_sub.clone(),
                            idx_sub + 1,
                            positional_params_sub,
                            variadic_sub_ty,
                        ),
                        (
                            r_super.clone(),
                            idx_super + 1,
                            positional_params_super,
                            variadic_super_ty,
                        ),
                        env,
                    )
                })
            }
        }
    })
}

/// Contravariant element-type subtyping for named-variadic parameters
/// between two function types. Two obligations:
///
/// 1. If the actual (sub) function has a named-variadic and the expected
///    (super) function declares required named parameters that the sub
///    does not declare by name, the sub's variadic absorbs them — but
///    the super's declared param type must be a subtype of the sub's
///    variadic element type (contravariance).
///
/// 2. If both sides have a named-variadic, their element types must
///    subtype contravariantly (super's element <: sub's element).
///
/// 3. If the expected function has a named-variadic and the actual function
///    has an optional named parameter not declared by the expected function,
///    the expected variadic's element type must be a subtype of that explicit
///    parameter's type. The explicit parameter shadows the actual function's
///    variadic for that name.
///
/// The "missing named-variadic on sub" and "extra required name on sub"
/// cases are handled in [simplify_subtype_funs_attributes] via
/// [Typing_named_params.find_names_mismatch].
pub(crate) fn simplify_subtype_named_variadic(
    subtype_env: &subtype_env::T,
    (r_sub, ft_sub): (Reason, &FunType),
    (r_super, ft_super): (Reason, &FunType),
    env: &mut Env,
) -> tl::SubtypeProp {
    let sub_var = typing_defs::ft_named_variadic_param(ft_sub);
    let super_var = typing_defs::ft_named_variadic_param(ft_super);
    let names_of = |ft: &FunType| -> SSet {
        let mut acc = SSet::new();
        for fp in typing_defs::ft_params_without_named_variadic(ft) {
            match named_params::name_of_named_param(fp) {
                Some(name) => {
                    acc.insert(name);
                }
                None => {}
            }
        }
        acc
    };
    let sub_named_names = names_of(ft_sub);
    let super_named_names = names_of(ft_super);
    let contra = |ty_super: &Ty, ty_sub: &Ty, env: &mut Env| {
        let ty_super = env::update_reason(env, ty_super.clone(), |r_super_prj| {
            reason::prj_fn_param(r_sub.clone(), r_super.clone(), r_super_prj, 0, 0)
        });
        simplify(
            subtype_env,
            None,
            Lhs {
                sub_supportdyn: None,
                ty_sub: &ty_super,
            },
            Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ty_sub,
            },
            env,
        )
    };
    // Each super-declared named param not matched by name in sub is
    // absorbed by sub's variadic (if sub has one). Check element-type
    // compatibility for each such absorption.
    let prop = match sub_var {
        None => valid(env),
        Some(FunParam {
            type_: ty_sub_var, ..
        }) => {
            let mut prop = valid(env);
            for super_fp in typing_defs::ft_params_without_named_variadic(ft_super) {
                match named_params::name_of_named_param(super_fp) {
                    Some(name) if !sub_named_names.contains(&name) => {
                        prop = and(env, prop, |env| contra(&super_fp.type_, ty_sub_var, env));
                    }
                    _ => {}
                }
            }
            prop
        }
    };
    // An explicit optional parameter in the sub shadows its named variadic.
    // If the super only accepts that name through its variadic, check against
    // the explicit parameter's type instead of the sub's variadic type.
    let prop = match (sub_var, super_var) {
        (
            Some(_),
            Some(FunParam {
                type_: ty_super_var,
                ..
            }),
        ) => {
            let mut prop = prop;
            for sub_fp in typing_defs::ft_params_without_named_variadic(ft_sub) {
                match named_params::name_of_named_param(sub_fp) {
                    Some(name)
                        if get_fp_is_optional(sub_fp) && !super_named_names.contains(&name) =>
                    {
                        prop = and(env, prop, |env| contra(ty_super_var, &sub_fp.type_, env));
                    }
                    _ => {}
                }
            }
            prop
        }
        _ => prop,
    };
    and(env, prop, |env| match (sub_var, super_var) {
        (
            Some(FunParam {
                type_: ty_sub_var, ..
            }),
            Some(FunParam {
                type_: ty_super_var,
                ..
            }),
        ) => contra(ty_super_var, ty_sub_var, env),
        _ => valid(env),
    })
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::path::Path;
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    fn prim(p: Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    fn generic(name: &str) -> Ty {
        mk((reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    fn param(ty: Ty, is_optional: bool, splat: bool) -> FunParam {
        FunParam {
            pos: PosOrDecl::NONE,
            name: None,
            type_: ty,
            flags: typing_defs_core::make_fp_flags(
                ParamMode::FPnormal,
                false,
                is_optional,
                false,
                false,
                splat,
                false,
            ),
            def_value: None,
        }
    }

    #[test]
    fn readonly_subtype_() {
        assert!(readonly_subtype(false, false));
        assert!(readonly_subtype(false, true));
        assert!(readonly_subtype(true, true));
        // A readonly value is a supertype of a mutable one
        assert!(!readonly_subtype(true, false));
    }

    #[test]
    fn params_to_tuple_() {
        // (int, optional float, num...)
        let ty = params_to_tuple(
            PosOrDecl::NONE,
            true,
            &[
                param(prim(Tprim::Tint), false, false),
                param(prim(Tprim::Tfloat), true, false),
                param(prim(Tprim::Tnum), false, false),
            ],
        );
        match get_node(&ty) {
            Ty_::Ttuple(TupleType {
                required,
                optional,
                extra: TupleExtra::Tvariadic(variadic),
            }) => {
                assert!(matches!(required.as_slice(), [t] if typing_defs::is_prim(Tprim::Tint, t)));
                assert!(
                    matches!(optional.as_slice(), [t] if typing_defs::is_prim(Tprim::Tfloat, t))
                );
                assert!(typing_defs::is_prim(Tprim::Tnum, variadic));
            }
            _ => panic!("expected a tuple with a variadic"),
        }
        // (int, ...T)
        let ty = params_to_tuple(
            PosOrDecl::NONE,
            false,
            &[
                param(prim(Tprim::Tint), false, false),
                param(generic("T"), false, true),
            ],
        );
        match get_node(&ty) {
            Ty_::Ttuple(TupleType {
                required,
                optional,
                extra: TupleExtra::Tsplat(splat),
            }) => {
                assert_eq!(required.len(), 1);
                assert!(optional.is_empty());
                assert!(typing_defs::is_generic(splat));
            }
            _ => panic!("expected a tuple with a splat"),
        }
        // No parameters: (nothing...)
        let ty = params_to_tuple(PosOrDecl::NONE, false, &[]);
        match get_node(&ty) {
            Ty_::Ttuple(TupleType {
                required,
                optional,
                extra: TupleExtra::Tvariadic(variadic),
            }) => {
                assert!(required.is_empty() && optional.is_empty());
                assert!(typing_defs::is_nothing(variadic));
            }
            _ => panic!("expected an empty tuple"),
        }
    }

    #[test]
    fn log_function_name() {
        let subtype_env = subtype_env::create(
            None,
            None,
            None,
            None,
            Some(true),
            None,
            None,
            None,
            None,
            None,
            false,
            2,
            None,
        );
        assert_eq!(
            log::function_name(&subtype_env, Some(&reason::none()), false, true),
            "Typing_subtype.Subtype.simplify <:D sub_supportdyn super_supportdyn require_soundness"
        );
        let subtype_env = subtype_env::create(
            Some(false),
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
            None,
        );
        assert_eq!(
            log::function_name(&subtype_env, None, true, false),
            "Typing_subtype.Subtype.simplify super_like"
        );
    }

    #[test]
    fn null_not_subtype_() {
        let env = env();
        assert!(null_not_subtype(&env, &prim(Tprim::Tint)));
        assert!(!null_not_subtype(&env, &prim(Tprim::Tnull)));
        assert!(!null_not_subtype(&env, &prim(Tprim::Tvoid)));
        assert!(!null_not_subtype(&env, &generic("T")));
        let union = |tyl| mk((reason::none(), Ty_::Tunion(tyl)));
        assert!(null_not_subtype(
            &env,
            &union(vec![prim(Tprim::Tint), prim(Tprim::Tfloat)])
        ));
        assert!(!null_not_subtype(
            &env,
            &union(vec![prim(Tprim::Tint), prim(Tprim::Tnull)])
        ));
    }

    #[test]
    fn generic_lower_bounds_without_bounds() {
        let env = env();
        let (g_set, o_set) = generic_lower_bounds(&env, &generic("T"));
        assert_eq!(g_set.into_iter().collect::<Vec<_>>(), vec!["T".to_string()]);
        assert!(typing_set::is_empty(&o_set));
        let (g_set, o_set) = generic_lower_bounds(&env, &prim(Tprim::Tint));
        assert!(g_set.is_empty());
        assert_eq!(typing_set::cardinal(&o_set), 1);
    }

    #[test]
    fn simplify_subtype_by_physical_equality_() {
        let mut env = env();
        let calls = Cell::new(0);
        // `?int`: a node with a component (the nodes of `mk` without
        // components, such as `int`, are shared, so two of them with the same
        // reason are the same node).
        let opt_int = || mk((reason::none(), Ty_::Toption(prim(Tprim::Tint))));
        let ty = opt_int();
        // The same type (a clone shares its node): valid, without simplifying.
        let p = simplify_subtype_by_physical_equality(&mut env, &ty, &ty.clone(), |_| {
            calls.set(calls.get() + 1);
            tl::invalid(None)
        });
        assert!(tl::is_valid(&p));
        assert_eq!(calls.get(), 0);
        // An equal type built separately: simplified.
        let p = simplify_subtype_by_physical_equality(&mut env, &ty, &opt_int(), |_| {
            calls.set(calls.get() + 1);
            tl::invalid(None)
        });
        assert!(tl::is_unsat(&p));
        assert_eq!(calls.get(), 1);
    }
}
