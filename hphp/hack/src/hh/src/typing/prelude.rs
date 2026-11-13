// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 1-2514): everything before `module rec Expr`.
//! See `hh/PORTING.md`.
//!
//! The submodules `Log`, `Env_help`, `Fun_id`, `TraitMostConcreteParent` and
//! `Valkind` of `typing.ml` are [`log`], [`env_help`], [`fun_id`],
//! [`trait_most_concrete_parent`] and [`valkind`]; the top-level functions are
//! the functions of this module, in the order of `typing.ml`.
//!
//! # Types
//!
//! - `expected_type_check` is [`ExpectedTypeCheck`]. `(env, env) result`, in
//!   which both sides are the environment the check returns, is
//!   `Result<(), ()>`: the environment is the one the check mutated, as for
//!   every other function that returns an environment. When the check is
//!   ambiguous (`Expected_ambiguous_shape_splat`), OCaml returns no
//!   environment and the caller goes on with the one it had before the
//!   check: the functions here leave `*env` as it was before the check in
//!   that case.
//! - `newable_class_info` is [`NewableClassInfo`], without the environment;
//!   its polymorphic variant `` [ `Class of ... | `Dynamic ] `` is
//!   [`ClassOrDynamic`].
//! - `type_split_info` is [`TypeSplitInfo`]: its fields that are functions of
//!   the environment are boxed closures that take `&mut Env` and return what
//!   the OCaml returns besides the environment.
//! - The result of [`get_variadic_or_splat_param`],
//!   `` [ `Splat of 'a fun_param | `Variadic of 'a fun_param ] ``, is
//!   [`SplatOrVariadic`].
//!
//! # Closures that OCaml lets capture the environment
//!
//! Where OCaml passes a closure that uses the environment it captured
//! (`check : unit -> expected_type_check`, `localize_with`), the Rust closure
//! takes the environment as its first argument instead.
//!
//! # `with_type`
//!
//! [`with_type`] is OCaml's `Aast.map` with `on_'ex` and `on_'en` constant:
//! it rebuilds the expression with every annotation replaced. That map,
//! which changes the type of the annotations, is [`aast_map`] (`oxidized`
//! only has visitors that work in place).

#![allow(non_upper_case_globals)]

use std::cell::RefCell;
use std::fmt::Write as _;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ParamKind;
use oxidized::local_id::LocalId;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;
use ty::reason::Reason as _;

use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
// module Cls = Folded_class
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::hh_logger;
use crate::pos_or_decl;
use crate::tast;
// module TCO = Typechecker_options
use crate::typechecker_options as tco;
// module C = Typing_continuations
use crate::typing_continuations as c;
// open Typing_defs (with Typing_defs_core)
use crate::typing_defs::*;
// open Typing_defs_constraints
use crate::typing_defs_constraints::*;
// module ExprDepTy = Typing_dependent_type.ExprDepTy
use crate::typing_dependent_type::expr_dep_ty;
// module Env = Typing_env
use crate::typing_env as env;
// open Typing_env_types
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
// module Fake = Typing_fake_members
use crate::typing_fake_members as fake;
// module TFTerm = Typing_func_terminality
use crate::typing_func_terminality as tfterm;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module TOG = Typing_object_get
use crate::typing_object_get as tog;
// module Phase = Typing_phase
use crate::typing_phase as phase;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;
use crate::typing_warning;
use crate::typing_warning_utils;

/// The names of `Naming_special_names` that `naming_special_names_rust` does
/// not have, with the OCaml values.
mod missing_special_names {
    /// `PseudoFunctions.hh_time`
    pub const HH_TIME: &str = "\\hh_time";
    /// `Capabilities.io`
    pub const CAPABILITIES_IO: &str = "\\HH\\Capabilities\\IO";
}

/// `newable_class_info`, without the environment.
pub(crate) type NewableClassInfo = (Vec<tast::Targ>, tast::ClassId, Vec<ClassOrDynamic>);

/// `` [ `Class of pos_id * Cls.t * locl_ty | `Dynamic ] ``
#[derive(Clone, Debug)]
pub(crate) enum ClassOrDynamic {
    Class(PosId, cls::T, Ty),
    Dynamic,
}

/// `expected_type_check`
#[derive(Clone, Debug)]
pub enum ExpectedTypeCheck {
    /// `Expected_checked of (env, env) result`: the environment is the one the
    /// check mutated.
    ExpectedChecked(Result<(), ()>),
    /// No environment: `*env` is the one from before the check.
    ExpectedAmbiguousShapeSplat(crate::tvid::set::T),
}

pub mod log {
    use super::*;

    pub fn should_log_check_expected_ty(env: &Env) -> bool {
        crate::typing_log::should_log(env, "typing", 1)
    }

    /// The OCaml is applied to the check (`unit -> expected_type_check`) last,
    /// which takes the environment here.
    pub fn log_check_expected_ty(
        env: &mut Env,
        p: &Pos,
        message: &str,
        inferred_ty: &Ty,
        ty: &Ty,
        check: impl FnOnce(&mut Env) -> ExpectedTypeCheck,
    ) -> ExpectedTypeCheck {
        let function_name = format!("Typing.check_expected_ty_res {}", message);
        let arguments = vec![
            (
                "inferred_ty".to_string(),
                typing_print::debug(&*env, inferred_ty),
            ),
            ("expected_ty".to_string(), typing_print::debug(&*env, ty)),
        ];
        crate::typing_log::log_function(
            &pos_or_decl::of_raw_pos(p.clone()),
            &function_name,
            &arguments,
            |res: &ExpectedTypeCheck| match res {
                ExpectedTypeCheck::ExpectedChecked(Ok(_)) => Some("ok".to_string()),
                ExpectedTypeCheck::ExpectedChecked(Err(_)) => Some("error".to_string()),
                ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(_) => {
                    Some("ambiguous_shape_splat".to_string())
                }
            },
            move || check(env),
        )
    }
}

// ---------------------------------------------------------------------------
// Debugging
// ---------------------------------------------------------------------------

thread_local! {
    /// A guess as to the last position we were typechecking, for use in debugging,
    /// such as figuring out what a runaway hh_server thread is doing. Updated
    /// only best-effort -- it's an approximation to point debugging in the right
    /// direction, nothing more.
    ///
    /// `debug_last_pos := p` is `debug_last_pos.with(|r| *r.borrow_mut() = p)`.
    pub static debug_last_pos: RefCell<Pos> = const { RefCell::new(Pos::NONE) };
}

pub fn debug_print_last_pos<A>(_: A) {
    let last_pos = debug_last_pos.with(|r| r.borrow().clone());
    hh_logger::info(
        None,
        None,
        &format!(
            "Last typecheck pos: {}",
            crate::pos::string(&crate::pos::to_absolute(&last_pos))
        ),
    )
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

pub(crate) fn log_iteration_count(env: &Env, pos: &Pos, n: isize) {
    let should_log_iteration_count = env::get_tcopt(env)
        .log_levels
        .get("loop_iteration_count")
        .is_some();
    if should_log_iteration_count {
        // `Format.asprintf "Loop iteration count %s:%a: %d\n" ... Pos.pp pos n`
        let mut msg = String::new();
        let _ = write!(
            msg,
            "Loop iteration count {}:",
            crate::pos::filename(&crate::pos::to_absolute(pos))
        );
        let _ = crate::pos::pp(&mut msg, pos);
        let _ = write!(msg, ": {}\n", n);
        hh_logger::log(&msg)
    }
}

pub(crate) fn mk_ty_mismatch_opt<A, B, E>(
    ty_have: A,
    ty_expect: B,
    err: Option<&E>,
) -> Option<(A, B)> {
    match err {
        Some(_) => Some((ty_have, ty_expect)),
        _ => None,
    }
}

pub(crate) fn mk_ty_mismatch_res<A, B, E>(
    ty_have: A,
    ty_expect: B,
    err: Option<&E>,
) -> Result<A, (A, B)> {
    match err {
        Some(_) => Err((ty_have, ty_expect)),
        _ => Ok(ty_have),
    }
}

pub(crate) fn mk_hole(
    source: Option<aast::HoleSource>,
    expr: tast::Expr,
    ty_have: Ty,
    ty_expect: Ty,
) -> tast::Expr {
    let source = source.unwrap_or(aast::HoleSource::Typing);
    if equal_locl_ty(&ty_have, &ty_expect) {
        expr
    } else {
        // if the hole is generated from typing, we leave the type unchanged,
        // if it is a call to `[unsafe|enforced]_cast`, we give it the expected type
        let ty_hole = match &source {
            aast::HoleSource::Typing => ty_have.clone(),
            aast::HoleSource::UnsafeCast(_)
            | aast::HoleSource::UnsafeNonnullCast
            | aast::HoleSource::EnforcedCast(_) => ty_expect.clone(),
        };
        let pos = expr.1.clone();
        tast::make_typed_expr(
            pos,
            ty_hole,
            aast::Expr_::Hole(Box::new((expr, ty_have, ty_expect, source))),
        )
    }
}

pub(crate) fn hole_on_ty_mismatch(te: tast::Expr, ty_mismatch_opt: Option<(Ty, Ty)>) -> tast::Expr {
    match ty_mismatch_opt {
        None => te,
        Some((ty_have, ty_expect)) => mk_hole(None, te, ty_have, ty_expect),
    }
}

/// When recording subtyping or coercion errors for union and intersection types
/// we need to look at the error for each element and then reconstruct any
/// errors into a union or intersection. If there were no errors for any
/// element, the result if also `Ok`; if there was an error for at least
/// on element we have `Error` with list of actual and expected types
pub(crate) fn fold_coercion_errs<A: Clone>(
    errs: Vec<Result<A, (A, A)>>,
) -> Result<Vec<A>, (Vec<A>, Vec<A>)> {
    // OCaml conses each element onto the front of the lists: they are kept
    // reversed here (`x :: xs` is a push) and turned around at the end.
    let mut acc: Result<Vec<A>, (Vec<A>, Vec<A>)> = Ok(vec![]);
    for err in errs {
        acc = match (acc, err) {
            (Ok(mut xs), Ok(x)) => {
                xs.push(x);
                Ok(xs)
            }
            (Ok(xs), Err((x, y))) => {
                let mut ys = xs.clone();
                let mut xs = xs;
                xs.push(x);
                ys.push(y);
                Err((xs, ys))
            }
            (Err((mut xs, mut ys)), Ok(x)) => {
                xs.push(x.clone());
                ys.push(x);
                Err((xs, ys))
            }
            (Err((mut xs, mut ys)), Err((x, y))) => {
                xs.push(x);
                ys.push(y);
                Err((xs, ys))
            }
        }
    }
    match acc {
        Ok(mut xs) => {
            xs.reverse();
            Ok(xs)
        }
        Err((mut xs, mut ys)) => {
            xs.reverse();
            ys.reverse();
            Err((xs, ys))
        }
    }
}

pub(crate) fn union_coercion_errs(errs: Vec<Result<Ty, (Ty, Ty)>>) -> Result<Ty, (Ty, Ty)> {
    match fold_coercion_errs(errs) {
        Ok(tys) => Ok(make_type::union(reason::none(), tys)),
        Err((acts, exps)) => Err((
            make_type::union(reason::none(), acts),
            make_type::union(reason::none(), exps),
        )),
    }
}

pub(crate) fn intersect_coercion_errs(errs: Vec<Result<Ty, (Ty, Ty)>>) -> Result<Ty, (Ty, Ty)> {
    match fold_coercion_errs(errs) {
        Ok(tys) => Ok(make_type::intersection(reason::none(), tys)),
        Err((acts, exps)) => Err((
            make_type::intersection(reason::none(), acts),
            make_type::intersection(reason::none(), exps),
        )),
    }
}

/// Given the type of an argument that has been unpacked and typed against
/// positional and variadic function parameter types, apply the subtyping /
/// coercion errors back to the original packed type.
pub(crate) fn pack_errs(
    pos: &Pos,
    ty: &Ty,
    subtyping_errs: &(Vec<Option<(Ty, Ty)>>, Option<(Ty, Ty)>),
) -> Ty {
    let nothing = make_type::nothing(reason::solve_fail(pos_or_decl::of_raw_pos(pos.clone())));
    // `aux ~k`, whose continuation only rebuilds the list in order.
    fn aux(errs: &[Option<(Ty, Ty)>], var_opt: &Option<(Ty, Ty)>, tys: &[Ty]) -> Vec<Ty> {
        let mut out = vec![];
        let mut errs = errs;
        let mut tys = tys;
        loop {
            match ((errs, var_opt), tys) {
                // Case 1: we have a type error at this positional parameter so
                // replace the type parameter which caused it with the expected type
                (([Some((_, ty)), rest @ ..], _), [_, tys_rest @ ..])
                // Case 2: there was no type error here so retain the original type
                // parameter
                | (([None, rest @ ..], _), [ty, tys_rest @ ..]) => {
                    // recurse for any remaining positional parameters and add the
                    // corrected (case 1) or original (case 2) type to the front of the
                    // list of type parameters in the continuation
                    out.push(ty.clone());
                    errs = rest;
                    tys = tys_rest;
                }
                // Case 3: we have a type error at the variadic parameter so replace
                // the type parameter which cased it with the expected type
                ((_, Some((_, ty))), [_, tys_rest @ ..]) => {
                    // recurse with the variadic parameter error and add the
                    // corrected type to the front of the list of type parameters in the
                    // continuation
                    out.push(ty.clone());
                    errs = &[];
                    tys = tys_rest;
                }
                // Case 4: we have a variadic parameter but no error - we're done so
                // pass the remaining unchanged type parameters into the contination
                // to rebuild corrected type params in the right order
                ((_, None), tys) => {
                    out.extend(tys.iter().cloned());
                    return out;
                }
                // Case 5: no more type parameters - again we're done so pass empty
                // list to continuation and rebuild corrected type params in the right
                // order
                (_, []) => return out,
            }
        }
    }
    let (errs, var_opt) = subtyping_errs;
    // The only types that _can_ be upacked are tuples and pairs; match on the
    // type to get the type parameters, pass them to our recursive function
    // aux to subsitute the expected type where we have a type error
    // then reconstruct the type in the continuation
    let r = get_reason(ty);
    match get_node(ty) {
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: TupleExtra::Tvariadic(t_variadic),
        }) => {
            let t_required = aux(errs, var_opt, t_required);
            let t_optional = aux(errs, var_opt, t_optional);
            mk((
                r.clone(),
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: TupleExtra::Tvariadic(t_variadic.clone()),
                }),
            ))
        }
        Ty_::Tclass(pos_id, exact, tys) => {
            let tys = aux(errs, var_opt, tys);
            mk((r.clone(), Ty_::Tclass(pos_id.clone(), exact.clone(), tys)))
        }
        _ => nothing,
    }
}

/// `(env, te, ty)` is `(te, ty)` here, as `(env, (te, ty))` is.
pub fn triple_to_pair<A, B>(x: (A, B)) -> (A, B) {
    x
}

pub mod env_help {
    //! Caller will be looking for a particular form of expected type
    //! e.g. a function type (when checking lambdas) or tuple type (when checking
    //! tuples). First expand the expected type and elide single union; also
    //! strip nullables, so ?t becomes t, as context will always accept a t if a ?t
    //! is expected.

    use super::*;

    pub(crate) fn unbox(
        strip_supportdyn: bool,
        pessimisable_builtin: bool,
        env: &mut Env,
        ty: Ty,
    ) -> Option<(Ty, bool)> {
        fn aux(
            strip_supportdyn: bool,
            pessimisable_builtin: bool,
            under_supportdyn: bool,
            env: &mut Env,
            ty: Ty,
        ) -> Option<(Ty, bool)> {
            let (sd, ty) = tutils::strip_supportdyn(env, ty);
            if sd {
                let result = aux(strip_supportdyn, pessimisable_builtin, true, env, ty);
                match result {
                    None => None,
                    Some((ty, _)) => Some((ty, true)),
                }
            } else {
                let ty_opt = crate::typing_dynamic_utils::try_strip_dynamic(None, None, env, &ty);
                match ty_opt {
                    Some(stripped_ty) => {
                        // We've got a type ty = ~stripped_ty so under Sound Dynamic we need to
                        // account for like-pushing: the rule (shown here for vec)
                        //     t <:D dynamic
                        //     ----------------------
                        //     vec<~t> <: ~vec<t>
                        // So if expected type is ~vec<t> then we can actually ask for vec<~t>
                        // which is more generous.
                        let opt_ty = if !strip_supportdyn && pessimisable_builtin {
                            None
                        } else {
                            crate::typing_dynamic::try_push_like(env, &stripped_ty)
                        };
                        match opt_ty {
                            None => aux(
                                strip_supportdyn,
                                pessimisable_builtin,
                                under_supportdyn,
                                env,
                                stripped_ty,
                            ),
                            Some(rty) => {
                                // We can only apply like-pushing if the type actually supports dynamic.
                                // We know this if we've gone under a supportdyn, *OR* if the type is
                                // known to be a dynamic-aware subtype of dynamic.
                                if under_supportdyn || tutils::is_supportdyn(env, &rty) {
                                    aux(strip_supportdyn, pessimisable_builtin, true, env, rty)
                                } else {
                                    None
                                }
                            }
                        }
                    }
                    None => match get_node(&ty) {
                        Ty_::Tunion(tyl) if tyl.len() == 1 => {
                            let ty = tyl[0].clone();
                            aux(
                                strip_supportdyn,
                                pessimisable_builtin,
                                under_supportdyn,
                                env,
                                ty,
                            )
                        }
                        Ty_::Toption(ty) => {
                            let ty = ty.clone();
                            aux(
                                strip_supportdyn,
                                pessimisable_builtin,
                                under_supportdyn,
                                env,
                                ty,
                            )
                        }
                        _ => Some((ty, false)),
                    },
                }
            }
        }
        aux(strip_supportdyn, pessimisable_builtin, false, env, ty)
    }

    pub(crate) fn expand_expected_and_get_node(
        strip_supportdyn: bool,
        pessimisable_builtin: bool,
        env: &mut Env,
        expected_ty: &expected_ty::T,
    ) -> Option<(Pos, Ureason, bool, Ty, Ty_, bool)> {
        let expected_ty::T {
            pos: p,
            reason: ur,
            ty,
            ignore_readonly,
            ..
        } = expected_ty;
        let res = unbox(strip_supportdyn, pessimisable_builtin, env, ty.clone());
        match res {
            None => None,
            Some((uty, supportdyn)) => {
                if supportdyn && !strip_supportdyn {
                    None
                } else {
                    let node = get_node(&uty).clone();
                    Some((
                        p.clone(),
                        ur.clone(),
                        supportdyn,
                        uty,
                        node,
                        *ignore_readonly,
                    ))
                }
            }
        }
    }

    /// Caller will be looking for a particular form of expected type
    /// e.g. a function type (when checking lambdas) or tuple type (when checking
    /// tuples). First expand the expected type and elide single union; also
    /// strip nullables, so ?t becomes t, as context will always accept a t if a ?t
    /// is expected.
    ///
    /// If strip_supportdyn is true, then we are expecting a function or shape type for the expected type,
    /// and we should decompose supportdyn<t>, and like-push, and return true to
    /// indicate that the type supports dynamic.
    ///
    /// Note: we currently do not generally expand ?t into (null | t), so ~?t is (dynamic | Toption t).
    pub fn expand_expected_opt(
        strip_supportdyn: bool,
        pessimisable_builtin: bool,
        env: &mut Env,
        expected_ty_opt: Option<&expected_ty::T>,
    ) -> Option<(Pos, Ureason, bool, Ty, Ty_, bool)> {
        match expected_ty_opt {
            None => None,
            Some(expected_ty) => expand_expected_and_get_node(
                strip_supportdyn,
                pessimisable_builtin,
                env,
                expected_ty,
            ),
        }
    }
}

pub fn with_special_coeffects<A>(
    env: &mut Env,
    cap_ty: Ty,
    unsafe_cap_ty: Ty,
    f: impl FnOnce(&mut Env) -> A,
) -> A {
    let init = env::next_cont_opt(env).map(|next_cont| {
        let initial_locals = next_cont.local_types;
        let tpenv = env::get_tpenv(env);
        (initial_locals, tpenv)
    });
    let conts = env::all_continuations(env);
    lenv::stash_and_do(env, &conts, move |env| {
        match init {
            None => {}
            Some((initial_locals, tpenv)) => {
                env::reinitialize_locals(env);
                env::set_locals(env, &initial_locals);
                env::env_with_tpenv(env, tpenv);
            }
        }
        let _ty = crate::typing_coeffects::register_capabilities(env, cap_ty, unsafe_cap_ty);
        f(env)
    })
}

/// Set all the types in an expression to the given type.
///
/// `env` is the `'en` annotation (a saved environment), not the typing
/// environment.
pub(crate) fn with_type(ty: Ty, env: tast::SavedEnv, e: &nast::Expr) -> tast::Expr {
    let mut on_ex = |_: &()| ty.clone();
    let mut on_en = |_: &()| env.clone();
    let mut visitor = aast_map::Map {
        on_ex: &mut on_ex,
        on_en: &mut on_en,
    };
    visitor.on_expr(e)
}

pub(crate) fn expr_error(env: &mut Env, p: Pos, e: &nast::Expr) -> (tast::Expr, Ty) {
    let ty = env::fresh_type_error(env, p);
    (with_type(ty.clone(), tast::dummy_saved_env(), e), ty)
}

pub(crate) fn unbound_name(env: &mut Env, id: &nast::Sid, e: &nast::Expr) -> (tast::Expr, Ty) {
    let ast_defs::Id(pos, name) = id;
    if tast::is_under_dynamic_assumptions(env.checked) {
        expr_error(env, pos.clone(), e)
    } else {
        let class_exists = {
            let decl = env::get_class(env, name);
            match decl {
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => false,
                decl_entry::T::Found(dc) => is_c_class(cls::kind(&dc)),
            }
        };
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Unbound_name {
                pos: pos.clone(),
                name: name.clone(),
                class_exists,
            }),
            env,
        );
        expr_error(env, pos.clone(), e)
    }
}

/// `Ast_defs.is_c_class`, which `crate::ast_defs` does not have.
fn is_c_class(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(_) => true,
        ClassishKind::Cenum
        | ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface => false,
    }
}

/// Is this type Traversable<vty> or Container<vty> for some vty?
pub(crate) fn get_value_collection_inst(
    env: &mut Env,
    p: &Pos,
    vc_kind: aast::VcKind,
    ty: &Ty,
) -> Option<Ty> {
    let arraykey_on = |env: &mut Env, ty: Ty| match vc_kind {
        aast::VcKind::Set | aast::VcKind::ImmSet | aast::VcKind::Keyset => {
            let reason = reason::idx_set_element(p.clone());
            let arraykey = make_type::arraykey(reason.clone());
            let ty = inter::intersect(env, reason, arraykey, ty);
            Some(ty)
        }
        aast::VcKind::Vector | aast::VcKind::ImmVector | aast::VcKind::Vec => Some(ty),
    };
    match get_node(ty) {
        Ty_::Tclass((_, c), _, tyl)
            if tyl.len() == 1
                && (c == sn::collections::TRAVERSABLE || c == sn::collections::CONTAINER) =>
        {
            arraykey_on(env, tyl[0].clone())
        }
        // If we're expecting a mixed or a nonnull then we can just assume
        // that the element type is mixed if it is a vec-like type and arraykey if it
        // is a set-like one.
        Ty_::Tnonnull => arraykey_on(env, make_type::mixed(get_reason(ty).clone())),
        Ty_::Tany(_) => Some(ty.clone()),
        Ty_::Tdynamic(_) if tast::is_under_dynamic_assumptions(env.checked) => {
            // interpret dynamic as Traversable<dynamic> or keyset<arraykey>
            arraykey_on(env, ty.clone())
        }
        _ => None,
    }
}

/// Is this type KeyedTraversable<kty,vty>
///           or KeyedContainer<kty,vty>
/// for some kty, vty?
pub(crate) fn get_key_value_collection_inst(env: &mut Env, p: &Pos, ty: &Ty) -> Option<(Ty, Ty)> {
    match get_node(ty) {
        Ty_::Tclass((_, c), _, tyl)
            if tyl.len() == 2
                && (c == sn::collections::KEYED_TRAVERSABLE
                    || c == sn::collections::KEYED_CONTAINER) =>
        {
            let (kty, vty) = (tyl[0].clone(), tyl[1].clone());
            let reason = reason::key_value_collection_key(p.clone());
            let arraykey = make_type::arraykey(reason.clone());
            let kty = inter::intersect(env, reason, kty, arraykey);
            Some((kty, vty))
        }
        // If we're expecting a mixed or a nonnull then we can just assume
        // that the key type is arraykey and the value type is mixed
        Ty_::Tnonnull => {
            let arraykey = make_type::arraykey(reason::key_value_collection_key(p.clone()));
            let mixed = make_type::mixed(reason::witness(p.clone()));
            Some((arraykey, mixed))
        }
        Ty_::Tany(_) => Some((ty.clone(), ty.clone())),
        Ty_::Tdynamic(_) if tast::is_under_dynamic_assumptions(env.checked) => {
            // interpret dynamic as KeyedTraversable<arraykey, dynamic>
            let arraykey = make_type::arraykey(reason::key_value_collection_key(p.clone()));
            Some((arraykey, ty.clone()))
        }
        _ => None,
    }
}

/// Is this type varray<vty> or a supertype for some vty?
pub(crate) fn vc_kind_to_supers(kind: aast::VcKind) -> Vec<&'static str> {
    match kind {
        aast::VcKind::Vector => vec![sn::collections::VECTOR, sn::collections::MUTABLE_VECTOR],
        aast::VcKind::ImmVector => {
            vec![sn::collections::IMM_VECTOR, sn::collections::CONST_VECTOR]
        }
        aast::VcKind::Vec => vec![sn::collections::VEC],
        aast::VcKind::Set => vec![sn::collections::SET, sn::collections::MUTABLE_SET],
        aast::VcKind::ImmSet => vec![sn::collections::IMM_SET, sn::collections::CONST_SET],
        aast::VcKind::Keyset => vec![sn::collections::KEYSET],
    }
}

pub(crate) fn kvc_kind_to_supers(kind: aast::KvcKind) -> Vec<&'static str> {
    match kind {
        aast::KvcKind::Map => vec![sn::collections::MAP, sn::collections::MUTABLE_MAP],
        aast::KvcKind::ImmMap => vec![sn::collections::IMM_MAP, sn::collections::CONST_MAP],
        aast::KvcKind::Dict => vec![sn::collections::DICT],
    }
}

/// Is this type one of the value collection types with element type vty?
pub(crate) fn get_vc_inst(env: &mut Env, p: &Pos, vc_kind: aast::VcKind, ty: &Ty) -> Option<Ty> {
    let classnames = vc_kind_to_supers(vc_kind);
    match get_node(ty) {
        Ty_::Tclass((_, c), _, tyl) if tyl.len() == 1 && classnames.iter().any(|n| n == c) => {
            Some(tyl[0].clone())
        }
        _ => get_value_collection_inst(env, p, vc_kind, ty),
    }
}

/// Is this type one of the three key-value collection types
/// e.g. dict<kty,vty> or a supertype for some kty and vty?
pub(crate) fn get_kvc_inst(
    env: &mut Env,
    p: &Pos,
    kvc_kind: aast::KvcKind,
    ty: &Ty,
) -> Option<(Ty, Ty)> {
    let classnames = kvc_kind_to_supers(kvc_kind);
    match get_node(ty) {
        Ty_::Tclass((_, c), _, tyl) if tyl.len() == 2 && classnames.iter().any(|n| n == c) => {
            Some((tyl[0].clone(), tyl[1].clone()))
        }
        _ => get_key_value_collection_inst(env, p, ty),
    }
}

/// Check whether this is a function type that (a) either returns a disposable
/// or (b) has the <<__ReturnDisposable>> attribute
///
/// The OCaml returns no environment: the one it threads is a copy.
pub(crate) fn is_return_disposable_fun_type(env: &Env, ty: &Ty) -> bool {
    let mut env = env.clone();
    let env = &mut env;
    let ty = crate::typing_dynamic_utils::strip_dynamic(env, ty.clone());
    let opt_ft = tutils::get_underlying_function_type(env, ty);
    match opt_ft {
        None => false,
        Some((_, ft)) => {
            get_ft_return_disposable(&ft)
                || crate::typing_disposable::is_disposable_type(env, &ft.ret).is_some()
        }
    }
}

/// `checked_env` is the environment of the check, which the caller goes on
/// with.
pub(crate) fn finish_expected_ty_check(
    checked_env: &Env,
    ty_err_opt: Option<typing_error::T>,
) -> ExpectedTypeCheck {
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, checked_env)
    }
    ExpectedTypeCheck::ExpectedChecked(match ty_err_opt {
        None => Ok(()),
        Some(_) => Err(()),
    })
}

/// The OCaml's `check : unit -> Typing_utils.expected_subtyping_result`
/// takes the environment here.
pub(crate) fn check_expected_ty_res_with(
    message: &str,
    env: &mut Env,
    inferred_ty: &Ty,
    expected_ty: &expected_ty::T,
    check: impl FnOnce(&mut Env) -> tutils::ExpectedSubtypingResult,
) -> ExpectedTypeCheck {
    let expected_ty::T { pos: p, ty, .. } = expected_ty;
    // On an ambiguous shape splat the OCaml returns no environment: the
    // caller goes on with the one it had before the check.
    let env_before_check = env.clone();
    let check = move |env: &mut Env| match check(env) {
        tutils::ExpectedSubtypingResult::AmbiguousShapeSplat(vars) => {
            ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(vars)
        }
        tutils::ExpectedSubtypingResult::SubtypingResult(ty_err_opt) => {
            finish_expected_ty_check(env, ty_err_opt)
        }
    };
    let res = if log::should_log_check_expected_ty(env) {
        log::log_check_expected_ty(env, p, message, inferred_ty, ty, check)
    } else {
        check(env)
    };
    if let ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(_) = res {
        *env = env_before_check;
    }
    res
}

pub(crate) fn check_expected_ty_res(
    coerce_for_op: bool,
    message: &str,
    env: &mut Env,
    inferred_ty: &Ty,
    expected_ty: &expected_ty::T,
) -> Result<(), ()> {
    let expected_ty::T {
        pos: p,
        reason: ur,
        ty,
        is_dynamic_aware,
        ignore_readonly,
    } = expected_ty;
    match check_expected_ty_res_with(message, env, inferred_ty, expected_ty, |env| {
        let ty_err_opt = crate::typing_coercion::coerce_type(
            Some(coerce_for_op),
            Some(*is_dynamic_aware),
            Some(*ignore_readonly),
            p.clone(),
            ur.clone(),
            env,
            inferred_ty.clone(),
            ty.clone(),
            Enforcement::Enforced, // TODO AKENN: flow this in
            callback::unify_error(),
        );
        tutils::ExpectedSubtypingResult::SubtypingResult(ty_err_opt)
    }) {
        ExpectedTypeCheck::ExpectedChecked(result) => result,
        ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(_) => {
            panic!("Unexpected ambiguous shape splat")
        }
    }
}

/// Do a subtype check of inferred type against expected type.
/// The optional coerce_for_op parameter controls whether any arguments of type
/// dynamic can be coerced to enforceable types because they are arguments to a
/// built-in operator.
pub(crate) fn check_expected_ty_opt_res(
    coerce_for_op: bool,
    message: &str,
    env: &mut Env,
    inferred_ty: &Ty,
    expected: Option<&expected_ty::T>,
) -> Result<(), ()> {
    match expected {
        None => Ok(()),
        Some(expected_ty) => {
            check_expected_ty_res(coerce_for_op, message, env, inferred_ty, expected_ty)
        }
    }
}

/// `Result.fold ~ok:Fn.id ~error:Fn.id`: the environment of the check either
/// way.
pub(crate) fn check_expected_ty(
    message: &str,
    env: &mut Env,
    inferred_ty: &Ty,
    expected: Option<&expected_ty::T>,
) {
    let _ = check_expected_ty_opt_res(false, message, env, inferred_ty, expected);
}

pub(crate) fn check_call_result_against_expected_type(
    message: &str,
    env: &mut Env,
    inferred_ty: &Ty,
    expected: Option<&expected_ty::T>,
) -> ExpectedTypeCheck {
    match expected {
        None => ExpectedTypeCheck::ExpectedChecked(Ok(())),
        Some(expected_ty) => {
            let expected_ty::T {
                pos: p,
                reason: ur,
                ty,
                is_dynamic_aware,
                ignore_readonly,
            } = expected_ty;
            check_expected_ty_res_with(message, env, inferred_ty, expected_ty, |env| {
                crate::typing_coercion::coerce_type_against_expected_type(
                    Some(false),
                    Some(*is_dynamic_aware),
                    Some(*ignore_readonly),
                    p.clone(),
                    ur.clone(),
                    env,
                    inferred_ty.clone(),
                    ty.clone(),
                    Enforcement::Enforced,
                    callback::unify_error(),
                )
            })
        }
    }
}

/// Set a local; must not be already assigned if it is a using variable
pub(crate) fn set_local(is_using_clause: Option<bool>, env: &mut Env, lid: aast::Lid, ty: Ty) {
    let is_using_clause = is_using_clause.unwrap_or(false);
    let aast::Lid(pos, x) = lid;
    if env::is_using_var(env, &x) {
        typing_error_utils::add_typing_error(
            &typing_error::primary(if is_using_clause {
                primary::T::Duplicate_using_var(pos.clone())
            } else {
                primary::T::Illegal_disposable {
                    pos: pos.clone(),
                    verb: primary::IllegalDisposableVerb::assigned,
                }
            }),
            env,
        )
    }
    env::set_local(None, None, env, x.clone(), ty, pos);
    if is_using_clause {
        env::set_using_var(env, x)
    }
}

/// Require a new construct with disposable
pub(crate) fn enforce_return_disposable<Ex, En>(env: &Env, e: &aast::Expr<Ex, En>) {
    match e {
        aast::Expr(_, _, aast::Expr_::New(_)) => {}
        aast::Expr(_, _, aast::Expr_::Call(_)) => {}
        aast::Expr(_, _, aast::Expr_::Await(e))
            if matches!(&**e, aast::Expr(_, _, aast::Expr_::Call(_))) => {}
        aast::Expr(_, _, aast::Expr_::Hole(h)) => enforce_return_disposable(env, &h.0),
        aast::Expr(_, p, _) => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Invalid_return_disposable(p.clone())),
            env,
        ),
    }
}

/// Wrappers around the function with the same name in LEnv, which only
/// performs the move/save and merge operation if we are in a try block or in a
/// function with return type 'noreturn'.
/// This enables significant perf improvement, because this is called at every
/// function of method call, when most calls are outside of a try block.
pub(crate) fn move_and_merge_next_in_catch(join_pos: &Pos, env: &mut Env) {
    if env.in_try || tfterm::is_noreturn(env) {
        lenv::move_and_merge_next_in_cont(env, join_pos, c::T::Catch)
    } else {
        lenv::drop_cont(env, c::T::Next)
    }
}

pub(crate) fn save_and_merge_next_in_catch(join_pos: &Pos, env: &mut Env) {
    if env.in_try || tfterm::is_noreturn(env) {
        lenv::save_and_merge_next_in_cont(env, join_pos, c::T::Catch)
    }
}

/// `let might_throw env = save_and_merge_next_in_catch env`: the callers
/// write `might_throw ~join_pos env`, and the arguments are in that order.
pub(crate) fn might_throw(join_pos: &Pos, env: &mut Env) {
    save_and_merge_next_in_catch(join_pos, env)
}

pub(crate) fn branch<Res>(
    join_pos: &Pos,
    env: &mut Env,
    branch1: impl FnOnce(&mut Env) -> Res,
    branch2: impl FnOnce(&mut Env) -> Res,
) -> (Res, Res) {
    let parent_lenv = env.lenv.clone();
    let tbr1 = branch1(env);
    // `let env = { env with lenv = parent_lenv }`: the rest of the
    // environment that `branch1` returned is kept.
    let lenv1 = std::mem::replace(&mut env.lenv, parent_lenv.clone());
    let tbr2 = branch2(env);
    let lenv2 = env.lenv.clone();
    lenv::union_lenvs(env, join_pos, &parent_lenv, &lenv1, &lenv2);
    (tbr1, tbr2)
}

/// The OCaml returns `((env, ty_err_opt), tk, tv, ty_mismatch_opt)`, where
/// the error is the one of `Typing_solver.close_tyvars_and_solve`.
pub(crate) fn as_expr(
    env: &mut Env,
    ty1: &Ty,
    pe: &Pos,
    e: &nast::AsExpr,
) -> (Option<typing_error::T>, Ty, Ty, Option<(Ty, Ty)>) {
    env::open_tyvars(env, pe.clone());
    let tv = if tutils::is_tyvar_error(env, ty1) {
        env::fresh_type_error(env, pe.clone())
    } else {
        env::fresh_type(env, pe.clone())
    };
    // Dynamic inference: if the collection has a shadow type variable, create
    // fresh shadows for the iteration value (and key) types. This ensures the
    // loop variable gets its own shadow rather than sharing the collection's,
    // so constraints from using the loop variable are attributed to it, not
    // the collection.
    let has_shadow = env::get_tcopt(env).tco_dynamic_inference && {
        let ty_check = match get_node(ty1) {
            Ty_::Toption(ty) => ty,
            _ => ty1,
        };
        match get_node(ty_check) {
            Ty_::Tdynamic(Some(_)) => true,
            _ => false,
        }
    };
    let shadow_val = if has_shadow {
        let v = env::fresh_shadow_tyvar(env, pe.clone());
        Some(v)
    } else {
        None
    };
    let shadow_tv = match shadow_val {
        Some(v) => mk((get_reason(&tv).clone(), Ty_::Tdynamic(Some(v)))),
        None => tv,
    };
    let ct = match e {
        aast::AsExpr::AsV(_) => CanTraverse {
            key: None,
            val: shadow_tv.clone(),
            is_await: false,
            reason: reason::foreach(pe.clone()),
        },
        aast::AsExpr::AsKv(_, _) => {
            let tk = env::fresh_type(env, pe.clone());
            let shadow_key = if has_shadow {
                let v = env::fresh_shadow_tyvar(env, pe.clone());
                mk((get_reason(&tk).clone(), Ty_::Tdynamic(Some(v))))
            } else {
                tk
            };
            CanTraverse {
                key: Some(shadow_key),
                val: shadow_tv.clone(),
                is_await: false,
                reason: reason::foreach(pe.clone()),
            }
        }
        aast::AsExpr::AwaitAsV(_, _) => CanTraverse {
            key: None,
            val: shadow_tv.clone(),
            is_await: true,
            reason: reason::asyncforeach(pe.clone()),
        },
        aast::AsExpr::AwaitAsKv(_, _, _) => {
            let tk = env::fresh_type(env, pe.clone());
            let shadow_key = if has_shadow {
                let v = env::fresh_shadow_tyvar(env, pe.clone());
                mk((get_reason(&tk).clone(), Ty_::Tdynamic(Some(v))))
            } else {
                tk
            };
            CanTraverse {
                key: Some(shadow_key),
                val: shadow_tv.clone(),
                is_await: true,
                reason: reason::asyncforeach(pe.clone()),
            }
        }
    };
    let expected_ty = InternalType::ConstraintType(mk_constraint_type((
        reason::foreach(pe.clone()),
        ConstraintType_::TcanTraverse(ct.clone()),
    )));
    let (ty_actual, is_option) = match get_node(ty1) {
        Ty_::Toption(ty_actual) => (ty_actual.clone(), true),
        _ => (ty1.clone(), false),
    };
    let ty_err_opt1 = crate::typing_ops::sub_type_i(
        None,
        pe.clone(),
        Ureason::URforeach,
        env,
        InternalType::LoclType(ty_actual.clone()),
        expected_ty.clone(),
        callback::unify_error(),
    );
    // Handle the case where we have a nullable type where the inner type does
    // support `Tcan_traverse`
    let (ty_mismatch_opt, ty_err_opt2) = match &ty_err_opt1 {
        None if is_option => {
            let ty_str: Lazy<String> = {
                let env = env.clone();
                let ty1 = ty1.clone();
                Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty1))
            };
            let ty_ct = sub_type::can_traverse_to_iface(&ct);
            let ct_str: Lazy<String> = {
                let env = env.clone();
                Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty_ct))
            };
            let reasons_opt = Some({
                let ct_reason = ct.reason.clone();
                let pe = pe.clone();
                // `Lazy.(ty_str >>= fun ty_str -> map ct_str ~f:(fun ct_str -> ...))`
                ty_str.bind(move |ty_str: &String| {
                    let ty_str = ty_str.clone();
                    ct_str.map(move |ct_str: &String| {
                        let msg = format!("Expected `{}` ", ct_str);
                        let mut reasons: Vec<Message<PosOrDecl>> =
                            reason::to_string(&msg, &ct_reason)
                                .into_iter()
                                .map(|(p, s)| Message(p, s.into()))
                                .collect();
                        reasons.push(Message(
                            pos_or_decl::of_raw_pos(pe.clone()),
                            format!("But got `?{}`", ty_str).into(),
                        ));
                        reasons
                    })
                })
            });
            // We actually failed so generate the error we should
            // have seen
            let ty_err = typing_error::primary(primary::T::Unify_error {
                pos: pe.clone(),
                msg_opt: None,
                reasons_opt,
            });
            (Some((ty1.clone(), ty_actual.clone())), Some(ty_err))
        }
        Some(_) => {
            let ty_mismatch =
                match mk_ty_mismatch_res(ty1.clone(), expected_ty.clone(), ty_err_opt1.as_ref()) {
                    Ok(_) => None,
                    Err((act, InternalType::LoclType(exp))) => Some((act, exp)),
                    Err((act, InternalType::ConstraintType(_))) => {
                        Some((act, sub_type::can_traverse_to_iface(&ct)))
                    }
                };
            (ty_mismatch, None)
        }
        None => (None, None),
    };
    let ty_err_opt = option_merge(ty_err_opt1, ty_err_opt2, typing_error::both);
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    env::set_tyvar_variance_i(env, None, None, &expected_ty);
    let tk = match ct.key {
        None => make_type::mixed(reason::none()),
        Some(tk) => tk,
    };
    (
        crate::typing_solver::close_tyvars_and_solve(env),
        tk,
        shadow_tv,
        ty_mismatch_opt,
    )
}

/// `Option.merge`
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, b) => b,
        (a, None) => a,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// These functions invoke special printing functions for Typing_env. They do not
/// appear in user code, but we still check top level function calls against their
/// names.
/// (An Fx hash set: it is only asked for membership, at every call of a named function.)
pub(crate) static typing_env_pseudofunctions: LazyLock<hash::HashSet<String>> = LazyLock::new(|| {
    [
        sn::pseudo_functions::HH_SHOW,
        sn::pseudo_functions::HH_EXPECT,
        sn::pseudo_functions::HH_EXPECT_EQUIVALENT,
        sn::pseudo_functions::HH_SHOW_ENV,
        sn::pseudo_functions::HH_LOG_LEVEL,
        sn::pseudo_functions::HH_FORCE_SOLVE,
        sn::pseudo_functions::HH_LOOP_FOREVER,
        sn::pseudo_functions::HH_SLEEP,
        missing_special_names::HH_TIME,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
});

pub(crate) fn do_hh_expect(
    equivalent: bool,
    env: &mut Env,
    use_pos: &Pos,
    explicit_targs: &[nast::Targ],
    p: &Pos,
    tys: &[Ty],
) {
    match explicit_targs {
        [targ] => {
            let (ty_err_opt, aast::Targ(expected_ty, _)) =
                phase::localize_targ(None, true, env, &targ.1);
            if let Some(ty_err) = &ty_err_opt {
                typing_error_utils::add_typing_error(ty_err, env)
            }
            let right_expected_ty = make_type::locl_like(
                reason::enforceable(get_pos(&expected_ty)),
                expected_ty.clone(),
            );
            match tys {
                [expr_ty] => {
                    let res = sub_type::sub_type(
                        env,
                        None,
                        None,
                        None,
                        None,
                        expr_ty.clone(),
                        right_expected_ty,
                        Some(reasons_callback::of_primary_error(primary::T::Hh_expect {
                            pos: p.clone(),
                            equivalent,
                        })),
                    );
                    let ty_err_opt = match res {
                        None => {
                            if equivalent {
                                sub_type::sub_type(
                                    env,
                                    None,
                                    None,
                                    None,
                                    None,
                                    expected_ty,
                                    expr_ty.clone(),
                                    Some(reasons_callback::of_primary_error(
                                        primary::T::Hh_expect {
                                            pos: p.clone(),
                                            equivalent,
                                        },
                                    )),
                                )
                            } else {
                                None
                            }
                        }
                        env_err => env_err,
                    };
                    if let Some(ty_err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(ty_err, env)
                    }
                }
                _ => {}
            }
        }
        _ => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Expected_tparam {
                pos: use_pos.clone(),
                decl_pos: pos_or_decl::none,
                n: 1,
            }),
            env,
        ),
    }
}

pub(crate) fn loop_forever(env: &Env) -> ! {
    // forever = up to 10 minutes, to avoid accidentally stuck processes
    for _i in 1..=600 {
        // Look up things in shared memory occasionally to have a chance to be
        // interrupted
        match env::get_class(env, "FOR_TEST_ONLY") {
            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => unix_sleep(1),
            decl_entry::T::Found(_) => panic!("assert false"),
        }
    }
    crate::utils::assert_false_log_backtrace(Some(
        "hh_loop_forever was looping for more than 10 minutes",
    ))
}

/// `Unix.sleep`: nothing for a negative duration.
fn unix_sleep(seconds: isize) {
    if seconds > 0 {
        std::thread::sleep(std::time::Duration::from_secs(seconds as u64))
    }
}

/// `Unix.gettimeofday`
fn unix_gettimeofday() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |d| d.as_secs_f64())
}

/// `int_of_string`: an OCaml integer literal (an optional sign, then `0x`,
/// `0o`, `0b` or `0u` and digits, or decimal digits, and `_` after the first
/// digit), within the range of an OCaml `int`. Raises `Failure
/// "int_of_string"` otherwise.
fn int_of_string(s: &str) -> isize {
    const MAX: i128 = (1 << 62) - 1;
    let fail = || -> ! { panic!("int_of_string") };
    let (negative, s) = match s.strip_prefix('-') {
        Some(s) => (true, s),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let lower = s.to_ascii_lowercase();
    let (radix, digits, decimal) = if let Some(d) = lower.strip_prefix("0x") {
        (16, d, false)
    } else if let Some(d) = lower.strip_prefix("0o") {
        (8, d, false)
    } else if let Some(d) = lower.strip_prefix("0b") {
        (2, d, false)
    } else if let Some(d) = lower.strip_prefix("0u") {
        (10, d, false)
    } else {
        (10, lower.as_str(), true)
    };
    match digits.chars().next() {
        Some(c) if c.is_digit(radix) => {}
        _ => fail(),
    }
    let mut n: i128 = 0;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        let d = match c.to_digit(radix) {
            Some(d) => d,
            None => fail(),
        };
        n = n * radix as i128 + d as i128;
        // Unsigned literals can use all the 63 bits; they wrap around.
        if n > 2 * MAX + 1 {
            fail()
        }
    }
    if decimal {
        // Decimal literals are signed: up to `max_int`, or `-min_int`.
        if n > MAX + (negative as i128) {
            fail()
        }
    } else if n > MAX {
        n -= 2 * (MAX + 1);
    }
    (if negative { -n } else { n }) as isize
}

pub(crate) fn do_hh_sleep<Ex, En>(args: &[aast::Argument<Ex, En>]) {
    let exprs: Vec<&aast::Expr<Ex, En>> = args
        .iter()
        .take(1)
        .map(crate::aast_utils::arg_to_expr)
        .collect();
    match exprs.as_slice() {
        [aast::Expr(_, _, aast::Expr_::Int(seconds_str))] => unix_sleep(int_of_string(seconds_str)),
        _ => {}
    }
}

thread_local! {
    /// `hh_time_start_times`: the keys are the tags, which are Hack strings.
    pub(crate) static hh_time_start_times: RefCell<im::OrdMap<bstr::BString, f64>> =
        RefCell::new(im::OrdMap::new());
}

/// Wrap the code you'd like to profile with `hh_time` annotations, e.g.,
///
///      hh_time('start');
///      // Expensive to typecheck code
///      hh_time('stop');
///
///    `hh_time` admits an optional tag parameter to allow for multiple timings in
///    the same file.
///
///      hh_time('start', 'Timing 1');
///      // Expensive to typecheck code
///      hh_time('stop', 'Timinig 1');
///
///      hh_time('start', 'Timing 2');
///      // Some more expensive to typecheck code
///      hh_time('stop', 'Timinig 2');
///
///    Limitation: Timings are not scoped, so multiple uses of the same tag
///    with `hh_time('start', tag)` will overwrite the beginning time of the
///    previous timing.
pub(crate) fn do_hh_time<Ex, En>(el: &[aast::Argument<Ex, En>]) {
    fn go<Ex, En>(command: &aast::Expr_<Ex, En>, tag: &[u8]) {
        match command {
            aast::Expr_::String(s) if s.as_slice() == b"start" => {
                let start_time = unix_gettimeofday();
                hh_time_start_times.with(|m| {
                    m.borrow_mut().insert(bstr::BString::from(tag), start_time);
                })
            }
            aast::Expr_::String(s) if s.as_slice() == b"stop" => {
                let stop_time = unix_gettimeofday();
                let start_time = hh_time_start_times.with(|m| m.borrow().get(tag).copied());
                match start_time {
                    Some(start_time) => {
                        let elapsed_time_ms = (stop_time - start_time) * 1000.;
                        // `Printf.printf "%s: %0.2fms\n" tag elapsed_time_ms`
                        use std::io::Write as _;
                        let mut out = std::io::stdout().lock();
                        let _ = out.write_all(tag);
                        let _ = write!(out, ": {:.2}ms\n", elapsed_time_ms);
                    }
                    None => {}
                }
            }
            _ => {}
        }
    }
    let exprs: Vec<&aast::Expr<Ex, En>> = el
        .iter()
        .take(2)
        .map(crate::aast_utils::arg_to_expr)
        .collect();
    match exprs.as_slice() {
        [aast::Expr(_, _, command)] => go(command, b"_"),
        [
            aast::Expr(_, _, command),
            aast::Expr(_, _, aast::Expr_::String(tag)),
        ] => go(command, tag.as_slice()),
        _ => {}
    }
}

pub(crate) fn is_parameter(env: &Env, x: &LocalId) -> bool {
    env::get_params(env).contains_key(x)
}

pub(crate) fn check_escaping_var(env: &Env, lid: &aast::Lid) {
    let aast::Lid(pos, x) = lid;
    let err_opt = if env::is_using_var(env, x) {
        Some(if crate::local_id::equal(x, &this()) {
            primary::T::Escaping_this(pos.clone())
        } else if is_parameter(env, x) {
            primary::T::Escaping_disposable_param(pos.clone())
        } else {
            primary::T::Escaping_disposable(pos.clone())
        })
    } else {
        None
    };
    if let Some(err) = err_opt {
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

pub(crate) fn make_result(env: &mut Env, p: Pos, te: tast::Expr_, ty: Ty) -> (tast::Expr, Ty) {
    // Set the variance of any type variables that were generated according
    // to how they appear in the expression type
    env::set_tyvar_variance(env, None, None, &ty);
    let te = crate::typing_helpers::make_simplify_typed_expr(env, p, ty.clone(), te);
    (te, ty)
}

/// The OCaml returns `((env, ty_err_opt), targ, expected)`.
pub(crate) fn localize_targ(
    env: &mut Env,
    ta: &aast::Hint,
) -> (Option<typing_error::T>, tast::Targ, expected_ty::T) {
    let pos = ta.0.clone();
    let (ty_err_opt, targ) = phase::localize_targ(None, true, env, ta);
    let expected = expected_ty::make(None, None, pos, Ureason::URhint, targ.0.clone());
    (ty_err_opt, targ, expected)
}

/// Set the function type to be capturing readonly values only
pub(crate) fn set_capture_only_readonly(env: &mut Env, ty: Ty) -> Ty {
    tutils::map_supportdyn(env, ty, |_env: &mut Env, ty: Ty| match get_node(&ty) {
        Ty_::Tfun(ft) => {
            let ft = set_ft_readonly_this(FunType::clone(&ft), true);
            mk((get_reason(&ty).clone(), Ty_::Tfun(std::rc::Rc::new(ft))))
        }
        _ => ty,
    })
}

/// `attr` is `((name_pos, name), (value_pos, value_ty))`.
pub(crate) fn xhp_attribute_decl_ty(
    env: &mut Env,
    sid: &nast::Sid,
    obj: Ty,
    attr: &(aast::Pstring, (Pos, Ty)),
) -> (Ty, Option<(Ty, Ty)>) {
    let (namepstr, valpty) = attr;
    let (valp, valty) = valpty;
    let (e1, (declty, _tal)) = tog::obj_get(
        sid.0.clone(),
        false,
        None,
        None,
        &[],
        &aast::ClassId_::CI(sid.clone()),
        &ast_defs::Id(namepstr.0.clone(), namepstr.1.clone()),
        callback::unify_error(),
        None,
        env,
        obj,
    );
    let ureason = Ureason::URxhp(sid.1.clone(), namepstr.1.clone());
    let e2 = crate::typing_coercion::coerce_type(
        None,
        None,
        None,
        valp.clone(),
        ureason,
        env,
        valty.clone(),
        declty.clone(),
        Enforcement::Unenforced,
        callback::xhp_attribute_does_not_match_hint(),
    );
    let ty_mismatch_opt = mk_ty_mismatch_opt(valty.clone(), declty.clone(), e2.as_ref());
    if let Some(ty_err) = option_merge(e1, e2, typing_error::both) {
        typing_error_utils::add_typing_error(&ty_err, env)
    }
    (declty, ty_mismatch_opt)
}

pub(crate) fn stash_conts_for_closure<A>(
    env: &mut Env,
    p: &Pos,
    should_invalidate_fakes: bool,
    is_expr_tree_virtual_expr: bool,
    is_anon: bool,
    captured: &[aast::CaptureLid<crate::typing_local_types::Local>],
    f: impl FnOnce(&mut Env) -> A,
) -> A {
    let with_ty_for_lid = |env: &Env, lid: aast::Lid| {
        let local = env::get_local(env, &lid.1);
        aast::CaptureLid(local, lid)
    };
    let captured: Vec<aast::CaptureLid<crate::typing_local_types::Local>> =
        if is_anon && tco::any_coeffects(&env::get_tcopt(env)) {
            // The elements of a list literal are evaluated from right to left.
            let capability = with_ty_for_lid(
                env,
                aast::Lid(Pos::NONE, crate::typing_coeffects::capability_id()),
            );
            let local_capability = with_ty_for_lid(
                env,
                aast::Lid(Pos::NONE, crate::typing_coeffects::local_capability_id()),
            );
            let mut l = vec![local_capability, capability];
            l.extend(captured.iter().cloned());
            l
        } else {
            captured.to_vec()
        };
    let captured = if env::is_local_defined(env, &this()) && !env::is_in_expr_tree(env) {
        let mut l = vec![with_ty_for_lid(env, aast::Lid(Pos::NONE, this()))];
        l.extend(captured);
        l
    } else {
        captured
    };
    let init = env::next_cont_opt(env).map(|next_cont| {
        let extended_env = match &env.in_macro_splice {
            Some(macro_splice_vars) if is_expr_tree_virtual_expr => {
                let mut extended_env = env.clone();
                env::set_locals(&mut extended_env, macro_splice_vars);
                Some(extended_env)
            }
            _ => None,
        };
        let extended_env: &Env = match &extended_env {
            Some(extended_env) => extended_env,
            None => env,
        };
        let initial_locals = if is_anon {
            env::get_locals(None, extended_env, &captured)
        } else {
            next_cont.local_types.clone()
        };
        let initial_fakes = if should_invalidate_fakes {
            fake::forget(
                env::get_fake_members(env),
                reason::Blame::Blame(p.clone(), reason::BlameSource::BSlambda),
            )
        } else {
            env::get_fake_members(env)
        };
        let tpenv = env::get_tpenv(env);
        let initial_loaded_packages = next_cont.loaded_packages;
        (
            initial_locals,
            initial_fakes,
            tpenv,
            initial_loaded_packages,
        )
    });
    let conts = env::all_continuations(env);
    lenv::stash_and_do(env, &conts, move |env| {
        match init {
            None => {}
            Some((initial_locals, initial_fakes, tpenv, initial_loaded_packages)) => {
                env::reinitialize_locals(env);
                env::set_locals(env, &initial_locals);
                env::set_fake_members(env, initial_fakes);
                env::env_with_tpenv(env, tpenv);
                env::set_loaded_packages(env, initial_loaded_packages);
            }
        }
        f(env)
    })
}

pub(crate) fn requires_consistent_construct<Ex, En>(cid: &aast::ClassId_<Ex, En>) -> bool {
    match cid {
        aast::ClassId_::CIstatic => true,
        aast::ClassId_::CIexpr(_) => true,
        aast::ClassId_::CIreified(_) => false,
        aast::ClassId_::CIparent => false,
        aast::ClassId_::CIself => false,
        aast::ClassId_::CI(_) => false,
    }
}

pub(crate) fn uninstantiable_error<Ex, En>(
    env: &Env,
    reason_pos: &Pos,
    cid: &aast::ClassId_<Ex, En>,
    c_tc_pos: &PosOrDecl,
    c_name: &str,
    c_usage_pos: &Pos,
    c_ty: &Ty,
) {
    let reason_ty_opt = match cid {
        aast::ClassId_::CIexpr(_) => {
            let env = env.clone();
            let c_ty = c_ty.clone();
            Some((
                reason_pos.clone(),
                Lazy::new(move || typing_print::error(None, &env, &c_ty)),
            ))
        }
        _ => None,
    };
    let err = typing_error::primary(primary::T::Uninstantiable_class {
        pos: c_usage_pos.clone(),
        class_name: c_name.to_string(),
        reason_ty_opt,
        decl_pos: c_tc_pos.clone(),
    });
    typing_error_utils::add_typing_error(&err, env)
}

pub(crate) fn coerce_to_throwable(pos: &Pos, env: &mut Env, exn_ty: Ty) -> Option<typing_error::T> {
    let throwable_ty = make_type::throwable(reason::throw(pos.clone()));
    crate::typing_coercion::coerce_type(
        Some(true),
        None,
        None,
        pos.clone(),
        Ureason::URthrow,
        env,
        exn_ty,
        throwable_ty,
        Enforcement::Enforced,
        callback::unify_error(),
    )
}

/// Bind lvar to ty and, if a hint is supplied, ty must be a subtype of it.
pub(crate) fn set_valid_rvalue(
    is_using_clause: Option<bool>,
    p: Pos,
    env: &mut Env,
    lvar: LocalId,
    _hint_ty: Option<Ty>,
    ty: Ty,
) {
    set_local(is_using_clause, env, aast::Lid(p, lvar.clone()), ty);
    // We are assigning a new value to the local variable, so we need to
    // generate a new expression id
    let new_eid = env::make_expression_id(env);
    match env::set_local_expr_id(env, &lvar, new_eid) {
        Ok(()) => {}
        Err(err) => typing_error_utils::add_typing_error(&err, env),
    }
}

/// The OCaml returns no environment.
pub(crate) fn is_hack_collection(env: &Env, ty: &Ty) -> (bool, Option<typing_error::T>) {
    // TODO(like types) This fails if a collection is used as a parameter under
    // pessimization, because ~Vector<int> </: ConstCollection<mixed>. This is the
    // test we use to see whether to update the expression id for expressions
    // $vector[0] = $x and $vector[] = $x. If this is false, the receiver is assumed
    // to be a Hack array which are COW. This approximation breaks down in the presence
    // of dynamic. It is unclear whether we should change an expression id if the
    // receiver is dynamic.
    match get_node(ty) {
        Ty_::Tvar(_) if tutils::is_tyvar_error(env, ty) => (true, None),
        _ => crate::typing_solver::is_sub_type(
            env,
            ty,
            &make_type::const_collection(reason::none(), make_type::mixed(reason::none())),
        ),
    }
}

/// `(_, _cid_pos, e)` is the class id.
pub(crate) fn check_class_get<Ex, En>(
    env: &Env,
    p: &Pos,
    def_pos: &PosOrDecl,
    cid: &str,
    mid: &str,
    ce: &ClassElt,
    class_id: &aast::ClassId<Ex, En>,
    function_pointer: bool,
    is_method: bool,
) {
    let aast::ClassId(_, cid_pos, e) = class_id;
    crate::typing_needs_concrete::check_class_get(env, p, def_pos, cid, mid, ce, e, is_method);
    match e {
        aast::ClassId_::CIself if get_ce_abstract(ce) => {
            match env::get_self_id(env) {
                Some(self_) => {
                    // at runtime, self:: in a trait is a call to whatever
                    // self:: is in the context of the non-trait "use"-ing
                    // the trait's code
                    match env::get_class(env, &self_) {
                        decl_entry::T::Found(cls) if ast_defs::is_c_trait(cls::kind(&cls)) => {
                            // Ban self::some_abstract_method() in a trait, if the
                            // method is also defined in a trait.
                            //
                            // Abstract methods from interfaces are fine: we'll check
                            // in the child class that we actually have an
                            // implementation.
                            match env::get_class(env, &ce.ce_origin) {
                                decl_entry::T::Found(meth_cls)
                                    if ast_defs::is_c_trait(cls::kind(&meth_cls)) =>
                                {
                                    typing_error_utils::add_typing_error(
                                        &typing_error::primary(primary::T::Self_abstract_call {
                                            meth_name: mid.to_string(),
                                            self_pos: cid_pos.clone(),
                                            pos: p.clone(),
                                            decl_pos: def_pos.clone(),
                                        }),
                                        env,
                                    )
                                }
                                _ => {}
                            }
                        }
                        _ => {
                            // Ban self::some_abstract_method() in a class. This will
                            //  always error.
                            typing_error_utils::add_typing_error(
                                &typing_error::primary(primary::T::Self_abstract_call {
                                    meth_name: mid.to_string(),
                                    self_pos: cid_pos.clone(),
                                    pos: p.clone(),
                                    decl_pos: def_pos.clone(),
                                }),
                                env,
                            )
                        }
                    }
                }
                None => {}
            }
        }
        aast::ClassId_::CIparent if get_ce_abstract(ce) => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Parent_abstract_call {
                meth_name: mid.to_string(),
                pos: p.clone(),
                decl_pos: def_pos.clone(),
            }),
            env,
        ),
        aast::ClassId_::CIreified(_) | aast::ClassId_::CI(_)
            if get_ce_abstract(ce) && function_pointer =>
        {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Abstract_function_pointer {
                    class_name: cid.to_string(),
                    meth_name: mid.to_string(),
                    pos: p.clone(),
                    decl_pos: def_pos.clone(),
                }),
                env,
            )
        }
        aast::ClassId_::CI(_) if get_ce_abstract(ce) => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Classname_abstract_call {
                class_name: cid.to_string(),
                meth_name: mid.to_string(),
                pos: p.clone(),
                decl_pos: def_pos.clone(),
            }),
            env,
        ),
        aast::ClassId_::CIreified(ast_defs::Id(_, name)) if get_ce_abstract(ce) => {
            let is_newable = env::get_newable(env, name);
            if is_newable {
                // If T is newable, any concrete implementation will have all static methods implemented.
            } else {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Classname_abstract_call {
                        class_name: cid.to_string(),
                        meth_name: mid.to_string(),
                        pos: p.clone(),
                        decl_pos: def_pos.clone(),
                    }),
                    env,
                )
            }
        }
        aast::ClassId_::CI(ast_defs::Id(_, class_name)) if get_ce_synthesized(ce) => {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Static_synthetic_method {
                    class_name: class_name.clone(),
                    meth_name: mid.to_string(),
                    pos: p.clone(),
                    decl_pos: def_pos.clone(),
                }),
                env,
            )
        }
        aast::ClassId_::CI(ast_defs::Id(_, class_name)) => match env::get_class(env, class_name) {
            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {}
            decl_entry::T::Found(cd) => {
                if ast_defs::is_c_trait(cls::kind(&cd)) {
                    if is_method {
                        let req_non_strict = cls::all_ancestor_req_constraints_requirements(&cd);
                        if !req_non_strict.is_empty() {
                            let elab = |ty: &DeclTy| match tutils::try_unwrap_class_type(ty) {
                                None => None,
                                Some((_r, req_name, _paraml)) => {
                                    Some(req_name.id_ref().as_str().to_string())
                                }
                            };
                            let ty_kind = match req_non_strict.first() {
                                Some(ty::decl::folded::ConstraintRequirement::CREqual(req)) => {
                                    (elab(&req.ty), primary::ReqConstraintKind::class_)
                                }
                                Some(ty::decl::folded::ConstraintRequirement::CRSubtype(req)) => {
                                    (elab(&req.ty), primary::ReqConstraintKind::this_as)
                                }
                                None => {
                                    // cannot happen
                                    (None, primary::ReqConstraintKind::class_)
                                }
                            };
                            match ty_kind {
                                (Some(req_constraint_name), req_constraint_kind) => {
                                    typing_error_utils::add_typing_error(
                                        &typing_error::primary(
                                            primary::T::Static_call_on_trait_require_non_strict {
                                                trait_name: class_name.clone(),
                                                meth_name: mid.to_string(),
                                                req_constraint_name,
                                                req_constraint_kind,
                                                pos: p.clone(),
                                                trait_pos: cls::pos(&cd),
                                            },
                                        ),
                                        env,
                                    )
                                }
                                _ => {}
                            }
                        } else {
                            typing_warning_utils::add(
                                env,
                                (
                                    p.clone(),
                                    typing_warning::Kind::Static_call_on_trait,
                                    typing_warning::static_call_on_trait::T {
                                        trait_name: class_name.clone(),
                                        meth_name: mid.to_string(),
                                        trait_pos: cls::pos(&cd),
                                    },
                                ),
                            )
                        }
                    } else {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Static_prop_on_trait {
                                trait_name: class_name.clone(),
                                meth_name: mid.to_string(),
                                pos: p.clone(),
                                trait_pos: cls::pos(&cd),
                            }),
                            env,
                        )
                    }
                }
            }
        },
        aast::ClassId_::CIself
        | aast::ClassId_::CIparent
        | aast::ClassId_::CIstatic
        | aast::ClassId_::CIreified(_)
        | aast::ClassId_::CIexpr(_) => {}
    }
}

pub mod fun_id {
    //! The function types of the declarations are `hackrs` types
    //! ([`DeclFunType`]); the localized ones are [`FunType`].

    use super::*;

    /// The decl position of a function, as `Pos_or_decl.t`.
    fn decl_pos(p: &pos::BPos) -> PosOrDecl {
        p.clone().to_oxidized()
    }

    pub(crate) fn validate((use_pos, name): (&Pos, &str), decl_entry: &FunElt, env: &Env) {
        let FunElt {
            pos: def_pos,
            deprecated: fe_deprecated,
            module: fe_module,
            internal: fe_internal,
            package: fe_package,
            package_requirement: fe_package_requirement,
            gated_by_feature_flag: fe_gated_by_feature_flag,
            ..
        } = decl_entry;
        let def_pos = decl_pos(def_pos);
        let other_errs: Vec<typing_error::T> = {
            // The elements of a list literal are evaluated from right to left.
            let cross_package = tvis::check_cross_package(
                use_pos.clone(),
                &def_pos,
                env,
                Some(fe_package_requirement.clone()),
            );
            let deprecated = tvis::check_deprecated(
                use_pos.clone(),
                def_pos.clone(),
                env,
                // `fe_deprecated` is a string in OCaml.
                fe_deprecated
                    .as_ref()
                    .map(|s| String::from_utf8_lossy(s.as_bytes()).into_owned()),
            );
            [deprecated, cross_package].into_iter().flatten().collect()
        };
        let (access_errs, access_linter_errors) = tvis::check_top_level_access(
            crate::typing_packages::CheckReason::Yes(primary::package::TargetSymbolSpec::Func),
            false,
            use_pos.clone(),
            def_pos.clone(),
            false,
            false,
            env,
            *fe_internal,
            fe_module.as_ref().map(|m| m.id_ref().as_str().to_string()),
            fe_package.as_ref(),
            name.to_string(),
        );
        for (pos, w) in access_linter_errors {
            let crate::typing_packages::PackageWarningInfo {
                current_package,
                current_package_before_override,
                caller_has_package_override,
                target_package,
                target_package_before_override,
                callee_has_package_override,
                classptr_reference_warning,
            } = w;
            crate::lints_diagnostics::crosspackage_linter(
                pos,
                current_package.as_ref(),
                current_package_before_override.as_deref(),
                caller_has_package_override,
                target_package.as_ref(),
                target_package_before_override.as_deref(),
                callee_has_package_override,
                classptr_reference_warning,
            )
        }
        let errs: Vec<typing_error::T> = other_errs.into_iter().chain(access_errs).collect();
        if let Some(err) = typing_error::multiple_opt(errs) {
            typing_error_utils::add_typing_error(&err, env)
        }
        // Check feature flag gating
        if let Some(feature_name) = fe_gated_by_feature_flag {
            let tcopt = env::get_tcopt(env);
            if !tco::is_unstable_feature_enabled(&tcopt, feature_name) {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Gated_by_feature_flag {
                        pos: use_pos.clone(),
                        name: name.to_string(),
                        feature: feature_name.clone(),
                    }),
                    env,
                )
            }
        }
    }

    pub(crate) fn validate_polymorphic(ft_tparams: &[DeclTparam], use_pos: &Pos, env: &Env) {
        let explicit_errs: Vec<typing_error::T> = {
            let is_explicit = |ua: &ty::decl::UserAttribute<pos::BPos>| {
                ua.name.id_ref().as_str() == sn::user_attributes::EXPLICIT
            };
            ft_tparams
                .iter()
                .filter_map(|tp| {
                    if tp.user_attributes.iter().any(is_explicit) {
                        Some(typing_error::primary(
                            primary::T::Require_generic_explicit {
                                decl_pos: decl_pos(tp.name.pos()),
                                param_name: tp.name.id_ref().as_str().to_string(),
                                pos: use_pos.clone(),
                            },
                        ))
                    } else {
                        None
                    }
                })
                .collect()
        };
        if let Some(err) = typing_error::multiple_opt(explicit_errs) {
            typing_error_utils::add_typing_error(&err, env)
        }
    }

    pub(crate) fn localize_polymorphic(
        fun_ty: DeclFunType,
        (use_pos, _fun_name): (&Pos, &str),
        def_pos: &PosOrDecl,
        env: &mut Env,
    ) -> FunType {
        // Raise errors for each parameter which is marked as explicit
        validate_polymorphic(&fun_ty.tparams, use_pos, env);
        let ty = DeclTy::new(R::none(), ty::decl::Ty_::Tfun(Box::new(fun_ty)));
        let (err_opt, ty) = phase::localize_no_subst(env, false, &ty);
        if let Some(err) = &err_opt {
            typing_error_utils::add_typing_error(err, env)
        }
        match get_node(&ty) {
            Ty_::Tfun(fun_ty) => {
                // We need simplify any where constraints so that we can modify the
                // bounds of any type parameters with the implied constraints
                // Once applied we are free to remove the where constraints
                let (ft_tparams, err_opt_cstr) = sub_type::apply_where_constraints(
                    use_pos,
                    def_pos,
                    &fun_ty.tparams,
                    &fun_ty.where_constraints,
                    env,
                );
                if let Some(err) = &err_opt_cstr {
                    typing_error_utils::add_typing_error(err, env)
                }
                // If this is not a polymorphic function type, mark as instantiated
                let ft_instantiated = fun_ty.tparams.is_empty();
                FunType {
                    tparams: ft_tparams,
                    where_constraints: vec![],
                    instantiated: ft_instantiated,
                    ..FunType::clone(&fun_ty)
                }
            }
            _ => panic!("Expected function type"),
        }
    }

    pub(crate) fn localize_instantiated(
        fun_ty: DeclFunType,
        ty_args: &[nast::Targ],
        (use_pos, fun_name): (&Pos, &str),
        def_pos: &PosOrDecl,
        env: &mut Env,
    ) -> (FunType, Vec<tast::Targ>) {
        let ety_env = empty_expand_env();
        let hints: Vec<aast::Hint> = ty_args.iter().map(|aast::Targ(_, h)| h.clone()).collect();
        let (tyargs_err_opt, ty_args) = phase::localize_targs(
            true,
            true,
            def_pos.clone(),
            use_pos.clone(),
            crate::utils::strip_ns(fun_name).to_string(),
            None,
            env,
            &fun_ty.tparams,
            hints,
        );
        if let Some(err) = &tyargs_err_opt {
            typing_error_utils::add_typing_error(err, env)
        }
        let (ty_err_opt, fun_ty) = phase::localize_ft(
            Some(phase::MethodInstantiation {
                use_name: crate::utils::strip_ns(fun_name).to_string(),
                use_pos: use_pos.clone(),
                explicit_targs: ty_args.clone(),
            }),
            &ety_env,
            def_pos.clone(),
            env,
            &fun_ty,
        );
        if let Some(err) = &ty_err_opt {
            typing_error_utils::add_typing_error(err, env)
        }
        (fun_ty, ty_args)
    }

    /// Localize the function type; if there are no type arguments, we
    /// 'localize' as though the function is polymorphic (i.e. we don't eliminate
    /// type parameters).
    pub(crate) fn localize(
        fun_ty: DeclFunType,
        ty_args: &[nast::Targ],
        fun_id: (&Pos, &str),
        def_pos: &PosOrDecl,
        env: &mut Env,
    ) -> (FunType, Vec<tast::Targ>) {
        if ty_args.is_empty() {
            let fun_ty = localize_polymorphic(fun_ty, fun_id, def_pos, env);
            (fun_ty, vec![])
        } else {
            localize_instantiated(fun_ty, ty_args, fun_id, def_pos, env)
        }
    }

    /// Replace default coeffect by [io] for type of echo (we don't want to make
    /// io generally available through hhi) and mark varargs parameter as readonly
    /// ; this is normally rejected by the parser.
    pub(crate) fn set_echo_capabilities(fun_ty: FunType, def_pos: &PosOrDecl) -> FunType {
        let FunType {
            params: ft_params, ..
        } = &fun_ty;
        let params = ft_params
            .iter()
            .map(|fp| FunParam {
                flags: crate::typing_defs_flags::fun_param::set_readonly(true, fp.flags),
                ..fp.clone()
            })
            .collect();
        FunType {
            implicit_params: FunImplicitParams {
                capability: Capability::CapTy(make_type::capability(
                    reason::witness_from_decl(def_pos.clone()),
                    missing_special_names::CAPABILITIES_IO.to_string(),
                )),
            },
            params,
            ..fun_ty
        }
    }

    /// `localize_with` is [`localize`] or [`localize_instantiated`].
    pub(crate) fn synth_help(
        localize_with: impl FnOnce(
            DeclFunType,
            &[nast::Targ],
            (&Pos, &str),
            &PosOrDecl,
            &mut Env,
        ) -> (FunType, Vec<tast::Targ>),
        reason: &R,
        fun_ty: DeclFunType,
        ty_args: &[nast::Targ],
        fun_id: &nast::Sid,
        decl_entry: &FunElt,
        env: &mut Env,
    ) -> (Ty, Vec<tast::Targ>) {
        let ast_defs::Id(fun_id_pos, fun_id_name) = fun_id;
        validate((fun_id_pos, fun_id_name), decl_entry, env);
        let FunElt {
            pos: fe_pos,
            support_dynamic_type: fe_support_dynamic_type,
            ..
        } = decl_entry;
        let fe_pos = decl_pos(fe_pos);
        let fun_ty = crate::typing_enforceability::compute_enforced_and_pessimize_fun_type(
            None, env, fun_ty,
        );
        let (fun_ty, ty_args) =
            localize_with(fun_ty, ty_args, (fun_id_pos, fun_id_name), &fe_pos, env);
        let fun_ty = if fun_id_name == sn::pre_namespaced_functions::ECHO {
            set_echo_capabilities(fun_ty, &fe_pos)
        } else {
            fun_ty
        };
        let reason = {
            let def = reason::localize(&reason.clone().to_oxidized());
            let use_ = reason::witness(fun_id_pos.clone());
            reason::flow_call(def, use_)
        };
        let ty = crate::typing_dynamic::maybe_wrap_with_supportdyn(
            *fe_support_dynamic_type,
            reason,
            fun_ty,
        );
        (ty, ty_args)
    }

    /// Synthesize the type of a function identifier. If no type arguments are
    /// provided but some are expected, a polymorphic function type will be
    /// generated.
    pub fn synth(
        fun_id: &nast::Sid,
        ty_args: &[nast::Targ],
        env: &mut Env,
    ) -> (Ty, Vec<tast::Targ>) {
        let lookup_id = {
            let ast_defs::Id(_, name) = fun_id;
            if name == sn::pre_namespaced_functions::ECHO {
                sn::pseudo_functions::ECHO
            } else {
                name.as_str()
            }
        };
        match env::get_fun(env, lookup_id) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                let (_, ty) =
                    unbound_name(env, fun_id, &aast::Expr((), Pos::NONE, aast::Expr_::Null));
                (ty, vec![])
            }
            decl_entry::T::Found(decl_entry) => match decl_entry.ty.node_ref() {
                ty::decl::Ty_::Tfun(fun_ty) => synth_help(
                    localize,
                    decl_entry.ty.reason(),
                    (**fun_ty).clone(),
                    ty_args,
                    fun_id,
                    &decl_entry,
                    env,
                ),
                _ => panic!("Expected function type"),
            },
        }
    }

    /// Transform the special function `idx` according to the number
    /// of arguments actually passed to the function
    ///
    /// The idx function has two signatures, depending on number of arguments
    /// actually passed:
    ///
    /// idx<Tk as arraykey, Tv>(?KeyedContainer<Tk, Tv> $collection, ?Tk $index): ?Tv
    /// idx<Tk as arraykey, Tv>(?KeyedContainer<Tk, Tv> $collection, ?Tk $index, Tv $default): Tv
    ///
    /// In the hhi file, it has signature
    ///
    /// function idx<Tk as arraykey, Tv>
    ///   (?KeyedContainer<Tk, Tv> $collection, ?Tk $index, $default = null)
    ///
    /// so this needs to be munged into the above.
    pub(crate) fn transform_idx_fun_ty(
        fun_ty: DeclFunType,
        nargs: isize,
        pessimise: bool,
    ) -> DeclFunType {
        let (param1, param2, param3) = match &*fun_ty.params {
            [param1, param2, param3] => (param1.clone(), param2.clone(), param3.clone()),
            _ => panic!("Expected 3 parameters for idx in hhi file"),
        };
        let rret = fun_ty.ret.reason().clone();
        let (ft_params, ft_ret) = match nargs {
            2 => {
                // Return type should be ?Tv
                let ret = {
                    let ty = decl_nullable(rret.clone(), decl_generic(rret, "Tv"));
                    if pessimise {
                        make_type::like(decl_enforceable(ty.pos().clone()), ty)
                    } else {
                        ty
                    }
                };
                (vec![param1, param2], ret)
            }
            3 => {
                // Third parameter should have type Tv
                let param3 = {
                    let r3 = param1.ty.reason().clone();
                    DeclFunParam {
                        ty: decl_generic(r3, "Tv"),
                        ..param3
                    }
                };
                // Return type should be Tv
                let ret = {
                    let ty = decl_generic(rret, "Tv");
                    if pessimise {
                        make_type::like(decl_enforceable(ty.pos().clone()), ty)
                    } else {
                        ty
                    }
                };
                (vec![param1, param2, param3], ret)
            }
            // Shouldn't happen!
            _ => (fun_ty.params.to_vec(), fun_ty.ret.clone()),
        };
        DeclFunType {
            params: ft_params.into_boxed_slice(),
            ret: ft_ret,
            ..fun_ty
        }
    }

    /// Synthesize a function type for the given function identifier. When
    /// generating the type of a function identifier for a function call we will
    /// always instantiate: if no type arguments are provided fresh type variables
    /// will be generated during localisation.
    ///
    /// In addition,typing the special function `idx` requires the number of
    /// arguments actually passed to the function so this information must be
    /// provided.
    pub fn synth_for_call(
        fun_id: &nast::Sid,
        ty_args: &[nast::Targ],
        nargs: isize,
        env: &mut Env,
    ) -> (Ty, Vec<tast::Targ>) {
        let lookup_id = {
            let ast_defs::Id(_, name) = fun_id;
            if name == sn::pre_namespaced_functions::ECHO {
                sn::pseudo_functions::ECHO
            } else {
                name.as_str()
            }
        };
        match env::get_fun(env, lookup_id) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                let (_, ty) =
                    unbound_name(env, fun_id, &aast::Expr((), Pos::NONE, aast::Expr_::Null));
                (ty, vec![])
            }
            decl_entry::T::Found(decl_entry) => match decl_entry.ty.node_ref() {
                ty::decl::Ty_::Tfun(fun_ty) => {
                    let fun_ty = (**fun_ty).clone();
                    let fun_ty = if fun_id.1 == sn::fb::IDX || fun_id.1 == sn::readonly::IDX {
                        let pessimise = tco_pessimise_builtins(&env::get_tcopt(env));
                        transform_idx_fun_ty(fun_ty, nargs, pessimise)
                    } else {
                        fun_ty
                    };
                    synth_help(
                        localize_instantiated,
                        decl_entry.ty.reason(),
                        fun_ty,
                        ty_args,
                        fun_id,
                        &decl_entry,
                        env,
                    )
                }
                _ => panic!("Expected function type"),
            },
        }
    }

    /// `MakeType.generic r name` on a decl type.
    fn decl_generic(r: R, name: &str) -> DeclTy {
        DeclTy::generic(r, pos::TypeName::new(name))
    }

    /// `MakeType.nullable r ty` on a decl type.
    fn decl_nullable(r: R, ty: DeclTy) -> DeclTy {
        // Cheap avoidance of double nullable
        match ty.node_ref() {
            ty::decl::Ty_::Toption(_) => DeclTy::new(r, ty.node_ref().clone()),
            ty::decl::Ty_::Tunion(tyl) if tyl.is_empty() => {
                // `MakeType.null r`
                DeclTy::prim(r, aast::Tprim::Tnull)
            }
            _ => DeclTy::new(r, ty::decl::Ty_::Toption(ty)),
        }
    }

    /// `Reason.enforceable p` on a decl position.
    fn decl_enforceable(p: pos::BPos) -> R {
        R::mk(|| ty::reason::ReasonImpl::FromWitnessDecl(ty::reason::WitnessDecl::Enforceable(p)))
    }

    /// `TCO.pessimise_builtins`, which `crate::typechecker_options` does not
    /// have.
    fn tco_pessimise_builtins(t: &tco::T) -> bool {
        // `everything_sdt t || t.tco_pessimise_builtins`
        t.po.everything_sdt || t.tco_pessimise_builtins
    }
}

/// Checks if a class (given by cty) contains a given static method.
///
/// We could refactor this + class_get
pub(crate) fn class_contains_smethod(env: &Env, cty: &Ty, (_pos, mid): &aast::Pstring) -> bool {
    let lookup_member = |ty: &Ty| match get_class_type(ty) {
        Some(((_, c), _, _)) => match env::get_class(env, &c) {
            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => false,
            decl_entry::T::Found(class_) => {
                env::get_static_member(true, env, &class_, mid).is_some()
            }
        },
        None => false,
    };
    // The environment that `get_concrete_supertypes` returns is dropped.
    let tyl =
        tutils::get_concrete_supertypes(None, None, None, true, &mut env.clone(), cty.clone());
    tyl.iter().any(lookup_member)
}

/// It the trait has a require class constraint, parent:: must resolve to the parent
/// of the required class, if it exists.  If a trait has `require extends` constraints
/// then parent:: can be approximated with the most precise of the required classes: this
/// must be unique because in a valid trait declaration all `require extends` must be
/// belong to the same inheritance hierarchy.  A similar reasoning applies to
/// `require this as` constraint, except that parent:: must be approximated with the most
/// precise parent of all the required classes, if it exists (if exists it is unique).
pub mod trait_most_concrete_parent {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum T {
        Found(cls::T, DeclTy),
        NotFound,
    }
}

pub(crate) fn trait_most_concrete_parent(
    trait_: &cls::T,
    env: &Env,
) -> Option<trait_most_concrete_parent::T> {
    use trait_most_concrete_parent::T::Found;
    use trait_most_concrete_parent::T::NotFound;
    let return_ancestor_list = |ty: &DeclTy| -> Vec<DeclTy> {
        let (_r, name, _paraml) = tutils::unwrap_class_type(ty);
        match env::get_class(env, name.id_ref().as_str()) {
            decl_entry::T::Found(required_class) => cls::all_ancestors(&required_class)
                .into_iter()
                .map(|(_, ty)| ty)
                .collect(),
            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => vec![],
        }
    };
    let ancestors_class = cls::all_ancestor_req_class_requirements(trait_);
    let ancestors_this_as = cls::all_ancestor_req_this_as_requirements(trait_);
    let ancestors_reqs = cls::all_ancestor_reqs(trait_);
    let ancestors: Vec<DeclTy> = match ancestors_class.first() {
        Some(req) => return_ancestor_list(&req.ty),
        None => {
            let ancestors_of_req_this: Vec<DeclTy> = ancestors_this_as
                .iter()
                .map(|r| return_ancestor_list(&r.ty))
                .collect::<Vec<_>>()
                .into_iter()
                .flatten()
                .collect();
            ancestors_of_req_this
                .into_iter()
                .chain(ancestors_reqs.iter().map(|r| r.ty.clone()))
                .collect()
        }
    };
    let ancestors_without_interfaces: Vec<(String, cls::T, DeclTy)> = ancestors
        .into_iter()
        .filter_map(|ty| {
            let (_r, name, _param) = tutils::unwrap_class_type(&ty);
            let name = name.id_ref().as_str().to_string();
            let class_ = env::get_class(env, &name);
            match class_ {
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => None,
                decl_entry::T::Found(c) if ast_defs::is_c_interface(cls::kind(&c)) => None,
                decl_entry::T::Found(c) if ast_defs::is_c_trait(cls::kind(&c)) => {
                    // this is an error case for which Typing_type_wellformedness spits out
                    // an error, but does *not* currently remove the offending
                    // 'require extends' or 'require implements'
                    None
                }
                decl_entry::T::Found(c) => Some((name, c, ty)),
            }
        })
        .collect();
    // if a trait has no constraints, then parent:: cannot be approximated; decls
    // do not store trait requirements directly, so the following checks if a trait has
    // require extends, require class, or require this as constraints from the ancestors
    // they pull in; the only subtlety is that `require implements` must not be taken
    // into account.
    if ancestors_without_interfaces.is_empty()
        && ancestors_class.is_empty()
        && ancestors_this_as.is_empty()
    {
        None
    } else {
        // return the most precise ancestor.
        Some(
            ancestors_without_interfaces
                .into_iter()
                .fold(NotFound, |acc, (name, c, ty)| {
                    let keep = match &acc {
                        Found(acc_c, _ty) => cls::has_ancestor(acc_c, &name),
                        NotFound => false,
                    };
                    if keep { acc } else { Found(c, ty) }
                }),
        )
    }
}

/// `List.hd_exn` and `List.last_exn` of the positions of `params`, merged.
fn merge_first_last_pos(params: &[&FunParam]) -> PosOrDecl {
    let first_pos = &params.first().expect("List.hd_exn").pos;
    let last_pos = &params.last().expect("List.last").pos;
    pos_or_decl::merge(first_pos, last_pos)
}

pub(crate) fn check_arity_and_names(
    did_unpack: Option<bool>,
    is_variadic_or_splat: bool,
    env: &Env,
    pos: &Pos,
    pos_def: &PosOrDecl,
    ft: &FunType,
    arity: isize,
    arg_names: &im::OrdSet<String>,
) {
    let did_unpack = did_unpack.unwrap_or(false);
    let (exp_min, required_names) = arity_and_names_required(ft);
    let positional_params: Vec<&FunParam> =
        ft.params.iter().filter(|fp| !get_fp_is_named(fp)).collect();
    let optional_params: Vec<&FunParam> = ft
        .params
        .iter()
        .filter(|fp| get_fp_is_optional(fp))
        .collect();
    let check_arity = || {
        if arity < exp_min {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Typing_too_few_args {
                    expected: exp_min,
                    actual: arity,
                    pos: pos.clone(),
                    decl_pos: pos_def.clone(),
                    // It's fine to not provide optional arguments here, don't provide any hints
                    hint_missing_optional: None,
                }),
                env,
            )
        }
        if !is_variadic_or_splat {
            let exp_max = positional_params.len() as isize;
            let arity = if did_unpack { arity + 1 } else { arity };
            if arity > exp_max {
                let should_show_hint_for_convert_to_optional =
                    // If the function has optional parameters, and the optional
                    // paramaters are provided as if they are mandatory, provide a hint
                    arity == exp_min + optional_params.len() as isize;
                let hint_convert_to_optional = if should_show_hint_for_convert_to_optional {
                    let last_args: Vec<&FunParam> =
                        ft.params.iter().skip(exp_min.max(0) as usize).collect();
                    Some(merge_first_last_pos(&last_args))
                } else {
                    None
                };
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Typing_too_many_args {
                        expected: exp_max,
                        actual: arity,
                        pos: pos.clone(),
                        decl_pos: pos_def.clone(),
                        hint_convert_to_optional,
                    }),
                    env,
                )
            }
        }
    };
    let check_names = || {
        // `S_set.diff` (which is its first argument when either set is
        // empty: most calls have no named arguments).
        let missing_names = if required_names.is_empty() || arg_names.is_empty() {
            required_names.clone()
        } else {
            required_names
                .clone()
                .relative_complement(arg_names.clone())
        };
        // When the callee has a named-variadic parameter, any name the caller
        // passes is legal — the variadic absorbs it (with element-type checking
        // done separately on each argument).
        let extra_names = if ft_named_variadic_param(ft).is_some() {
            crate::im_empty::ord_set()
        } else if arg_names.is_empty() {
            // `S_set.diff arg_names all_names` is empty.
            crate::im_empty::ord_set()
        } else {
            let all_names: im::OrdSet<String> = ft_params_without_named_variadic(ft)
                .iter()
                .filter_map(named_params::name_of_named_param)
                .collect();
            arg_names.clone().relative_complement(all_names)
        };
        if !missing_names.is_empty() {
            let missing_names: Vec<String> = missing_names.into_iter().collect();
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Missing_named_args {
                    missing_names,
                    pos: pos.clone(),
                    decl_pos: pos_def.clone(),
                }),
                env,
            )
        }
        if !extra_names.is_empty() {
            let unexpected_names: Vec<String> = extra_names.into_iter().collect();
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Unexpected_named_args {
                    unexpected_names,
                    pos: pos.clone(),
                    decl_pos: pos_def.clone(),
                }),
                env,
            )
        }
    };
    check_arity();
    check_names()
}

/// `` [ `Splat of 'a fun_param | `Variadic of 'a fun_param ] ``
#[derive(Clone, Debug)]
pub(crate) enum SplatOrVariadic {
    Splat(FunParam),
    Variadic(FunParam),
}

/// The last parameter of a function can be
///    variadic (written t...), meaning any number of t's
/// or
///    splat (written ...t), meaning further parameters corresponding to the elements of tuple type t
pub(crate) fn get_variadic_or_splat_param(
    ft: &FunType,
) -> (Vec<FunParam>, Option<SplatOrVariadic>) {
    match ft.params.last() {
        Some(fp) if get_fp_splat(fp) => (
            // `List.drop_last_exn`
            ft.params[..ft.params.len() - 1].to_vec(),
            Some(SplatOrVariadic::Splat(fp.clone())),
        ),
        _ if get_ft_variadic(ft) => {
            let (named, positional): (Vec<FunParam>, Vec<FunParam>) =
                ft.params.iter().cloned().partition(get_fp_is_named);
            match positional.last() {
                Some(variadic) => {
                    let variadic = variadic.clone();
                    let mut params = positional[..positional.len() - 1].to_vec();
                    params.extend(named);
                    (params, Some(SplatOrVariadic::Variadic(variadic)))
                }
                None => (ft.params.clone(), None),
            }
        }
        _ => (ft.params.clone(), None),
    }
}

pub(crate) fn check_lambda_arity(
    env: &Env,
    lambda_pos: &Pos,
    def_pos: &PosOrDecl,
    lambda_ft: &FunType,
    expected_ft: &FunType,
) -> bool {
    match (
        get_variadic_or_splat_param(lambda_ft),
        get_variadic_or_splat_param(expected_ft),
    ) {
        ((_, None), (_, None)) => {
            // what's the fewest arguments this type can take
            let (expected_min, _) = arity_and_names_required(expected_ft);
            let (actual_min, _) = arity_and_names_required(lambda_ft);
            let positional_params_of = |ft: &FunType| -> Vec<FunParam> {
                ft.params
                    .iter()
                    .filter(|fp| !get_fp_is_named(fp))
                    .cloned()
                    .collect()
            };
            let optional_params_of = |ft: &FunType| -> Vec<FunParam> {
                ft.params
                    .iter()
                    .filter(|fp| get_fp_is_optional(fp))
                    .cloned()
                    .collect()
            };
            let optional_params = optional_params_of(expected_ft);
            // what's the most arguments this type can take (assuming no splat or variadics)
            let expected_max = positional_params_of(expected_ft).len() as isize;
            let actual_max = positional_params_of(lambda_ft).len() as isize;
            // actual must be able to take at least as many args as expected expects
            // and require no more than expected requires
            let too_few = actual_max < expected_max;
            let too_many = actual_min > expected_min;
            if too_few {
                // If all the required arguments are provided, but not the optional ones,
                // provide a more specific hint
                let should_show_hint_for_missing_optional = !optional_params.is_empty()
                    && actual_max + optional_params.len() as isize == expected_max;
                let hint_missing_optional = if should_show_hint_for_missing_optional {
                    let optional_params: Vec<&FunParam> = optional_params.iter().collect();
                    Some(merge_first_last_pos(&optional_params))
                } else {
                    None
                };
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Typing_too_few_args {
                        expected: expected_max,
                        actual: actual_max,
                        pos: lambda_pos.clone(),
                        decl_pos: def_pos.clone(),
                        hint_missing_optional,
                    }),
                    env,
                )
            }
            if too_many {
                let should_show_hint_for_convert_to_optional =
                    // If the function has optional parameters, and the optional
                    // paramaters are provided as if they are mandatory, provide a hint
                    actual_min == expected_min + optional_params.len() as isize;
                let hint_convert_to_optional = if should_show_hint_for_convert_to_optional {
                    let last_args: Vec<&FunParam> = lambda_ft
                        .params
                        .iter()
                        .skip(expected_min.max(0) as usize)
                        .collect();
                    Some(merge_first_last_pos(&last_args))
                } else {
                    None
                };
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Typing_too_many_args {
                        expected: expected_min,
                        actual: actual_min,
                        pos: lambda_pos.clone(),
                        decl_pos: def_pos.clone(),
                        hint_convert_to_optional,
                    }),
                    env,
                )
            }
            !(too_few || too_many)
            // Diagnostics.typing_too_many_args expected_min lambda_min lambda_pos def_pos
        }
        (_, _) => true,
    }
}

pub(crate) fn param_modes<Ex, En>(
    is_variadic: Option<bool>,
    fp: &FunParam,
    e: &aast::Expr<Ex, En>,
    param_kind: &ParamKind,
    env: &Env,
) {
    let is_variadic = is_variadic.unwrap_or(false);
    let fp_pos = &fp.pos;
    let aast::Expr(_, pos, _) = e;
    let err_opt = match (get_fp_mode(fp), param_kind) {
        (ParamMode::FPnormal, ParamKind::Pnormal) => None,
        (ParamMode::FPinout, ParamKind::Pinout(_)) => None,
        (ParamMode::FPnormal, ParamKind::Pinout(p)) => {
            Some(primary::T::Inout_annotation_unexpected {
                pos: crate::pos::merge(p, pos),
                decl_pos: fp_pos.clone(),
                param_is_variadic: is_variadic,
                qfx_pos: p.clone(),
            })
        }
        (ParamMode::FPinout, ParamKind::Pnormal) => Some(primary::T::Inout_annotation_missing {
            pos: pos.clone(),
            decl_pos: fp_pos.clone(),
        }),
    };
    if let Some(err) = err_opt {
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

/// The elements of the lists are `(index, parameter)`: OCaml only looks at the
/// parameter.
pub(crate) fn split_remaining_params_required_optional<A: Clone>(
    positional_params: &[(A, FunParam)],
    remaining_positional_params: &[(A, FunParam)],
) -> (isize, Vec<(A, FunParam)>, Vec<(A, FunParam)>) {
    // Both lists exclude variadic and type-splat parameters.
    // remaining_positional_params is a suffix of positional_params, whose required
    // parameters precede optional ones.
    // For example:
    //    function f(
    //      int $i, named int $n = 0, string $j, float $k = 3.14, mixed ...$m,
    //    ): void {}
    //    function g((string, float, bool) $t): void {
    //      f(3, ...$t);
    //    }
    //
    //    positional_params contains [i, j, k] and remaining_positional_params contains
    //    [j, k]. min_arity is 2 and consumed is 1, so j is required and k is optional.
    //    The named parameter n contributes to neither count; the variadic parameter m
    //    handles the remaining bool separately.
    let min_arity = positional_params
        .iter()
        .filter(|(_, fp)| !get_fp_is_optional(fp))
        .count() as isize;
    let consumed = positional_params.len() as isize - remaining_positional_params.len() as isize;
    let required_remaining = std::cmp::max(min_arity - consumed, 0);
    // `List.split_n`
    let n = std::cmp::min(
        required_remaining as usize,
        remaining_positional_params.len(),
    );
    let (required_params, optional_params) = remaining_positional_params.split_at(n);
    (consumed, required_params.to_vec(), optional_params.to_vec())
}

/// The OCaml returns `(env, (d_required, d_optional, d_variadic))`.
pub(crate) fn generate_splat_type_vars<A, B>(
    env: &mut Env,
    p: &Pos,
    required_params: &[A],
    optional_params: &[A],
    variadic_or_splat_param: &Option<B>,
) -> (Vec<Ty>, Vec<Ty>, Option<Ty>) {
    let d_required: Vec<Ty> = required_params
        .iter()
        .map(|_| env::fresh_type(env, p.clone()))
        .collect();
    let d_optional: Vec<Ty> = optional_params
        .iter()
        .map(|_| env::fresh_type(env, p.clone()))
        .collect();
    let d_variadic = if variadic_or_splat_param.is_none() {
        None
    } else {
        let ty = env::fresh_type(env, p.clone());
        Some(ty)
    };
    (d_required, d_optional, d_variadic)
}

pub(crate) fn check_argument_type_against_parameter(
    is_single_argument: Option<bool>,
    dynamic_func: Option<crate::typing_argument::DynFuncKind>,
    env: &mut Env,
    param: &FunParam,
    param_kind: &ParamKind,
    (e, arg_ty): (&nast::Expr, Ty),
    is_variadic: bool,
) -> (Option<(Ty, Ty)>, Option<(PosOrDecl, Ty)>) {
    let is_single_argument = is_single_argument.unwrap_or(false);
    let aast::Expr(_, pos, expr_) = e;
    param_modes(Some(is_variadic), param, e, param_kind, env);
    // When checking params, the type 'x' may be expression dependent. Since
    // we store the expression id in the local env for Lvar, we want to apply
    // it in this case.
    let dep_ty = match expr_ {
        aast::Expr_::Hole(h) if matches!(&h.0, aast::Expr(_, _, aast::Expr_::Lvar(_))) => {
            expr_dep_ty::make(env, &aast::ClassId_::CIexpr(e.clone()), arg_ty)
        }
        aast::Expr_::Lvar(_) => expr_dep_ty::make(env, &aast::ClassId_::CIexpr(e.clone()), arg_ty),
        _ => arg_ty,
    };
    let pos = match param_kind {
        ParamKind::Pnormal => pos.clone(),
        ParamKind::Pinout(pk_pos) => crate::pos::merge(pk_pos, pos),
    };
    let ignore_readonly = get_fp_ignore_readonly_error(param);
    let (ty_err_opt, used_dynamic) =
        crate::typing_argument::check_argument_type_against_parameter_type(
            Some(is_single_argument),
            None,
            dynamic_func,
            ignore_readonly,
            env,
            // param.fp_pos
            param.type_.clone(),
            pos,
            dep_ty.clone(),
        );
    (
        ty_err_opt,
        if used_dynamic {
            Some((param.pos.clone(), dep_ty))
        } else {
            None
        },
    )
}

pub(crate) fn bad_call(env: &Env, p: &Pos, ty: &Ty) {
    if !tutils::is_tyvar_error(env, ty) {
        let ty_name = {
            let env = env.clone();
            let ty = ty.clone();
            Lazy::new(move || typing_print::error(None, &env, &ty))
        };
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Bad_call {
                pos: p.clone(),
                ty_name,
            }),
            env,
        )
    }
}

pub(crate) fn make_a_local_of(
    include_this: bool,
    env: &mut Env,
    e: &nast::Expr,
) -> Option<aast::Lid> {
    match e {
        aast::Expr(_, p, aast::Expr_::ClassGet(cg)) => {
            let (aast::ClassId(_, _, cname), (_, member_name), _) = &**cg;
            let local = env::fake_members::make_static(env, cname, member_name, p.clone());
            Some(aast::Lid(p.clone(), local))
        }
        aast::Expr(_, p, aast::Expr_::ObjGet(og))
            if matches!(
                &og.0,
                aast::Expr(_, _, aast::Expr_::This) | aast::Expr(_, _, aast::Expr_::Lvar(_))
            ) && matches!(&og.1, aast::Expr(_, _, aast::Expr_::Id(_))) =>
        {
            let (obj, member, _, _) = &**og;
            let member_name = match member {
                aast::Expr(_, _, aast::Expr_::Id(id)) => &id.1,
                _ => unreachable!(),
            };
            let local = env::fake_members::make(env, obj, member_name, p.clone());
            Some(aast::Lid(p.clone(), local))
        }
        aast::Expr(_, _, aast::Expr_::Lvar(x)) | aast::Expr(_, _, aast::Expr_::Dollardollar(x)) => {
            Some((**x).clone())
        }
        aast::Expr(_, p, aast::Expr_::This) if include_this => Some(aast::Lid(p.clone(), this())),
        aast::Expr(_, _, aast::Expr_::Hole(h)) => make_a_local_of(include_this, env, &h.0),
        aast::Expr(_, _, aast::Expr_::ReadonlyExpr(e)) => make_a_local_of(include_this, env, e),
        _ => None,
    }
}

/// `make_a_local_of include_this env (Tast.to_nast_expr te)`, without
/// converting (copying) the whole expression. `Tast.to_nast_expr` replaces
/// each hole by its expression, with the position of the hole (`Typing`
/// holes), or by a call (the casts), inner holes first: what
/// `make_a_local_of` sees of an expression is its position and the first
/// expression under its `Typing` holes, and it never sees a hole.
pub(crate) fn make_a_local_of_tast(
    include_this: bool,
    env: &mut Env,
    te: &tast::Expr,
) -> Option<aast::Lid> {
    /// What `Tast.to_nast_expr` makes of `e` (under its position); `None`
    /// for a call (a cast).
    fn converted(e: &tast::Expr) -> Option<&tast::Expr_> {
        let mut e_ = &e.2;
        loop {
            match e_ {
                aast::Expr_::Hole(h) => match &h.3 {
                    aast::HoleSource::Typing => e_ = &h.0.2,
                    aast::HoleSource::UnsafeCast(_)
                    | aast::HoleSource::UnsafeNonnullCast
                    | aast::HoleSource::EnforcedCast(_) => return None,
                },
                _ => return Some(e_),
            }
        }
    }
    let p = &te.1;
    match converted(te)? {
        aast::Expr_::ClassGet(cg) => {
            let (aast::ClassId(_, _, cname), (_, member_name), _) = &**cg;
            let cname = tast::to_nast_class_id_(cname.clone());
            let local = env::fake_members::make_static(env, &cname, member_name, p.clone());
            Some(aast::Lid(p.clone(), local))
        }
        aast::Expr_::ObjGet(og) => {
            let (obj, member, _, _) = &**og;
            // (`Typing_fake_members.make_id` reads only the kind of `obj`
            // and the name of a local.)
            let obj = match converted(obj)? {
                aast::Expr_::This => nast::Expr((), obj.1.clone(), aast::Expr_::This),
                aast::Expr_::Lvar(x) => nast::Expr((), obj.1.clone(), aast::Expr_::Lvar(x.clone())),
                _ => return None,
            };
            let member_name = match converted(member)? {
                aast::Expr_::Id(id) => &id.1,
                _ => return None,
            };
            let local = env::fake_members::make(env, &obj, member_name, p.clone());
            Some(aast::Lid(p.clone(), local))
        }
        aast::Expr_::Lvar(x) | aast::Expr_::Dollardollar(x) => Some((**x).clone()),
        aast::Expr_::This if include_this => Some(aast::Lid(p.clone(), this())),
        aast::Expr_::ReadonlyExpr(e) => make_a_local_of_tast(include_this, env, e),
        _ => None,
    }
}

pub(crate) fn make_function_ref(contains_generics: bool, p: &Pos, ty: Ty) -> Ty {
    if !contains_generics {
        make_type::function_ref(reason::witness(p.clone()), ty)
    } else {
        ty
    }
}

/// This function captures the common bits of logic behind refinement
/// of the type of a local variable or a class member variable as a
/// result of a dynamic check (e.g., nullity check, simple type check
/// using functions like is_int, is_string, is_array etc.).  The
/// argument refine is a function that takes the type of the variable
/// and returns a refined type (making necessary changes to the
/// environment, which is threaded through).
pub(crate) fn refine_lvalue_type(
    env: &mut Env,
    te: &tast::Expr,
    refine: impl FnOnce(&mut Env, Ty) -> Ty,
) {
    let aast::Expr(ty, _, _) = te;
    // (`make_a_local_of false env (Tast.to_nast_expr te)`)
    let localopt = make_a_local_of_tast(false, env, te);
    // TODO TAST: generate an assignment to the fake local in the TAST
    match localopt {
        Some(lid) => {
            let ty = refine(env, ty.clone());
            set_local(None, env, lid, ty)
        }
        None => {}
    }
}

/// If we are dealing with a refinement like
///      $x is MyClass<A, B>
///    then class_info is the class info of MyClass and hint_tyl corresponds
///    to A, B.
pub(crate) fn generate_fresh_tparams(
    env: &mut Env,
    class_info: &cls::T,
    p: &Pos,
    reason: &Reason,
    hint_tyl: &[Ty],
) -> (Vec<Option<(DeclTparam, String)>>, Vec<Ty>) {
    let tparams_len = cls::tparams(class_info).len();
    let hint_tyl: Vec<Option<Ty>> = hint_tyl
        .iter()
        .take(tparams_len)
        .cloned()
        .map(Some)
        .collect();
    let pad_len = tparams_len - hint_tyl.len();
    let hint_tyl: Vec<Option<Ty>> = hint_tyl
        .into_iter()
        .chain(std::iter::repeat_n(None, pad_len))
        .collect();
    let replace_wildcard = |env: &mut Env, hint_ty: Option<Ty>, tp: DeclTparam| {
        let tparam_name = tp.name.id_ref().as_str().to_string();
        let reified = tp.reified.clone();
        let enforceable = attributes::mem(sn::user_attributes::ENFORCEABLE, &tp.user_attributes);
        let newable = attributes::mem(sn::user_attributes::NEWABLE, &tp.user_attributes);
        match hint_ty {
            Some(ty) => match get_node(&ty) {
                Ty_::Tgeneric(name) if env::is_fresh_generic_parameter(name) => {
                    let name = name.clone();
                    (
                        Some((tp, name.clone())),
                        make_type::generic(reason.clone(), name),
                    )
                }
                _ => (None, ty),
            },
            None => {
                let new_name = env::add_fresh_generic_parameter(
                    env,
                    pos_or_decl::of_raw_pos(p.clone()),
                    &tparam_name,
                    reified,
                    enforceable,
                    newable,
                );
                // TODO(T69551141) handle type arguments for Tgeneric
                (
                    Some((tp, new_name.clone())),
                    make_type::generic(reason.clone(), new_name),
                )
            }
        }
    };
    // `List.map2_env`
    let tparams_and_tyl: Vec<(Option<(DeclTparam, String)>, Ty)> = hint_tyl
        .into_iter()
        .zip(cls::tparams(class_info))
        .map(|(hint_ty, tp)| replace_wildcard(env, hint_ty, tp))
        .collect();
    let (tparams_with_new_names, tyl_fresh) = tparams_and_tyl.into_iter().unzip();
    (tparams_with_new_names, tyl_fresh)
}

/// `List.zip_exn`
fn zip_exn<A, B>(l1: Vec<A>, l2: Vec<B>) -> Vec<(A, B)> {
    if l1.len() != l2.len() {
        panic!("length mismatch in zip_exn: {} <> {}", l1.len(), l2.len())
    }
    l1.into_iter().zip(l2).collect()
}

pub(crate) fn safely_refine_class_type(
    env: &mut Env,
    p: &Pos,
    class_name: &PosId,
    class_info: &cls::T,
    ivar_ty: &Ty,
    obj_ty: &Ty,
    reason: &Reason,
    tparams_with_new_names: Vec<Option<(DeclTparam, String)>>,
    tyl_fresh: Vec<Ty>,
) -> Ty {
    // Type of variable in block will be class name
    // with fresh type parameters
    let obj_ty = mk((
        get_reason(obj_ty).clone(),
        Ty_::Tclass(class_name.clone(), nonexact(), tyl_fresh.clone()),
    ));
    let tparams = cls::tparams(class_info);
    // Add in constraints as assumptions on those type parameters
    let ety_env = ExpandEnv {
        // `Subst.make_locl`: `crate::decl_subst::make_locl` takes the types of
        // the declared phase of `oxidized`.
        substs: phase::decl_subst_make_locl(&tparams, &tyl_fresh),
        this_ty: obj_ty.clone(),
        ..empty_expand_env()
    };
    let add_bounds = |env: &mut Env, (t, ty_fresh): (DeclTparam, Ty)| {
        for (ck, ty) in t.constraints.iter() {
            // Substitute fresh type parameters for
            // original formals in constraint
            let (ty_err_opt, ty) = phase::localize(&ety_env, env, ty);
            if let Some(ty_err) = &ty_err_opt {
                typing_error_utils::add_typing_error(ty_err, env)
            }
            sub_type::add_constraint(
                env,
                *ck,
                ty_fresh.clone(),
                ty,
                Some(reasons_callback::unify_error_at(p.clone())),
            )
        }
    };
    for tp_ty in zip_exn(tparams, tyl_fresh.clone()) {
        add_bounds(env, tp_ty)
    }
    // Finally, if we have a class-test on something with static classish type,
    // then we can chase the hierarchy and decompose the types to deduce
    // further assumptions on type parameters. For example, we might have
    //   class B<Tb> { ... }
    //   class C extends B<int>
    // and have obj_ty = C and x_ty = B<T> for a generic parameter Aast.
    // Then SubType.add_constraint will deduce that T=int and add int as
    // both lower and upper bound on T in env.lenv.tpenv
    //
    // We only wish to do this if the types are in a possible subtype relationship.
    let supertypes =
        tutils::get_concrete_supertypes(None, None, Some(true), true, env, ivar_ty.clone());
    // The OCaml returns no environment: the ones it threads are copies.
    fn might_be_supertype(env: &Env, class_info: &cls::T, obj_ty: &Ty, ty: &Ty) -> bool {
        let ty = env::expand_type(&mut env.clone(), ty.clone());
        match get_node(&ty) {
            Ty_::Tclass((_, name), _, _)
                if *name == cls::name(class_info)
                    || cls::has_ancestor(class_info, name)
                    || cls::requires_ancestor(class_info, name) =>
            {
                true
            }
            Ty_::Tnewtype(name, tyl, _) => {
                // For case types we want to open the union, filtering it to only the
                // variant types that share the same data type as [obj_ty]
                let mut env = env.clone();
                let variants_opt =
                    crate::typing_case_type_variant::get_variant_tys(&mut env, name, tyl);
                match variants_opt {
                    Some(variants) => {
                        let ty = crate::typing_case_type_variant::filter_variants_using_datatype(
                            false,
                            &mut env,
                            get_reason(&ty).clone(),
                            &variants,
                            obj_ty,
                        );
                        might_be_supertype(&env, class_info, obj_ty, &ty)
                    }
                    None => false,
                }
            }
            Ty_::Toption(ty) => might_be_supertype(env, class_info, obj_ty, ty),
            Ty_::Tunion(tyl) => tyl
                .iter()
                .all(|ty| might_be_supertype(env, class_info, obj_ty, ty)),
            _ => false,
        }
    }
    for ty in supertypes {
        if might_be_supertype(env, class_info, &obj_ty, &ty) {
            sub_type::add_constraint(
                env,
                ast_defs::ConstraintKind::ConstraintAs,
                obj_ty.clone(),
                ty,
                Some(reasons_callback::unify_error_at(p.clone())),
            )
        }
    }
    // It's often the case that the fresh name isn't necessary. For
    // example, if C<T> extends B<T>, and we have $x:B<t> for some type t
    // then $x is C should refine to $x:C<t>.
    // We take a simple approach:
    //    For a fresh type parameter T#1, if
    //      - There is an eqality constraint T#1 = t,
    //      - T#1 is covariant, and T#1 has upper bound t (or mixed if absent)
    //      - T#1 is contravariant, and T#1 has lower bound t (or nothing if absent)
    //    then replace T#1 with t.
    // This is done in Type_parameter_env_ops.simplify_tpenv
    let tparam_substs = crate::type_parameter_env_ops::simplify_tpenv(
        env,
        &zip_exn(tparams_with_new_names.clone(), tyl_fresh.clone()),
        reason.clone(),
    );
    // `List.map2_exn`
    let tyl_fresh: Vec<Ty> = zip_exn(tyl_fresh, tparams_with_new_names)
        .into_iter()
        .map(|(orig_ty, tparam_opt)| match tparam_opt {
            None => orig_ty,
            Some((_tp, name)) => match tparam_substs.get(&name) {
                Some(ty) => ty.clone(),
                None => panic!("Not_found"),
            },
        })
        .collect();
    mk((
        get_reason(&obj_ty).clone(),
        Ty_::Tclass(class_name.clone(), nonexact(), tyl_fresh),
    ))
}

/// Transform a hint like `A<_>` to a localized type like `A<T#1>` for refinement of
/// an instance variable. ivar_ty is the previous type of that instance variable. Return
/// the intersection of the hint and variable. Returns the env, refined type, and a boolean
/// true if ivar_ty was a class or tuple containing a class and false otherwise.
pub(crate) fn class_for_refinement(
    env: &mut Env,
    p: &Pos,
    reason: &Reason,
    ivar_pos: &Pos,
    ivar_ty: &Ty,
    hint_ty: Ty,
) -> (Ty, bool) {
    let hint_ty = env::expand_type(env, hint_ty);
    match (get_node(ivar_ty), get_node(&hint_ty)) {
        (_, Ty_::Tclass(c, _, tyl)) => {
            let (_, cid) = c;
            match env::get_class(env, cid) {
                decl_entry::T::Found(class_info) => {
                    let (tparams_with_new_names, tyl_fresh) =
                        generate_fresh_tparams(env, &class_info, p, reason, tyl);
                    let ty = safely_refine_class_type(
                        env,
                        p,
                        c,
                        &class_info,
                        ivar_ty,
                        &hint_ty,
                        reason,
                        tparams_with_new_names,
                        tyl_fresh,
                    );
                    (ty, true)
                }
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => (
                    make_type::nothing(reason::missing_class(ivar_pos.clone())),
                    true,
                ),
            }
        }
        // TODO optional and variadic fields T201398626 T201398652
        (
            Ty_::Ttuple(TupleType {
                required: ivar_tyl, ..
            }),
            Ty_::Ttuple(TupleType {
                required: hint_tyl, ..
            }),
        ) if ivar_tyl.len() == hint_tyl.len() => {
            // `List.map2_env`
            let tyl: Vec<(Ty, bool)> = ivar_tyl
                .iter()
                .zip(hint_tyl.iter())
                .map(|(ivar_ty, hint_ty)| {
                    class_for_refinement(env, p, reason, ivar_pos, ivar_ty, hint_ty.clone())
                })
                .collect();
            let is_class = tyl.iter().any(|(_, b)| *b);
            (
                make_type::tuple(reason.clone(), tyl.into_iter().map(|(ty, _)| ty).collect()),
                is_class,
            )
        }
        _ => (hint_ty.clone(), false),
    }
}

/// [refine_and_simplify_intersection env p reason ivar_pos ty hint_ty]
///   intersects [ty] and [hint_ty], possibly making [hint_ty] support dynamic
///   first if [ty] also supports dynamic.
///   Then if the result has some like types in which prevent simplification
///   of the intersection, it'll distribute any '&' at the top of the type tree
///   in order to have a union at hand.
///   This is because the resulting type will likely end up on the LHS of a subtyping
///   call down the line, and unions on the LHS behave better than intersections,
///   which result in incomplete typing.
///
///   Parameters:
///   * [reason]          The reason for the result types and other intermediate types.
///   * [p], [ivar_pos]   Only used if hint_ty is a class
pub(crate) fn refine_and_simplify_intersection(
    env: &mut Env,
    p: &Pos,
    reason: &Reason,
    ivar_pos: &Pos,
    ty: Ty,
    hint_ty: Ty,
) -> Ty {
    let (hint_ty, is_class) = {
        let stripped_ty_opt = crate::typing_dynamic_utils::try_strip_dynamic(None, None, env, &ty);
        let stripped_ty = match stripped_ty_opt {
            Some(ty) => ty,
            _ => ty.clone(),
        };
        class_for_refinement(env, p, reason, ivar_pos, &stripped_ty, hint_ty)
    };
    crate::typing_helpers::refine_and_simplify_intersection(
        env,
        is_class,
        None,
        reason.clone(),
        ty,
        hint_ty,
    )
}

/// Set report_errors to false if you've already localized the hint previously
/// e.g. as is the case for `is`
pub(crate) fn refine_for_hint(
    expr_pos: &Pos,
    refinement_reason: &Reason,
    report_errors: bool,
    env: &mut Env,
    tparamet: bool,
    ty: Ty,
    hint: &aast::Hint,
) -> Ty {
    let (ty_err_opt, hint_ty) = phase::localize_hint_for_refinement(env, hint);
    if report_errors {
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env)
        }
    }
    let (_, hint_ty) = tutils::strip_supportdyn(env, hint_ty);
    let hint_ty = if !tparamet {
        inter::negate_type(
            env,
            refinement_reason.clone(),
            &hint_ty,
            tutils::Approx::ApproxUp,
        )
    } else {
        hint_ty
    };
    refine_and_simplify_intersection(env, &hint.0, refinement_reason, expr_pos, ty, hint_ty)
}

pub(crate) fn refine_for_pattern(
    expr_pos: &Pos,
    env: &mut Env,
    tparamet: bool,
    ty: Ty,
    pattern: &aast::Pattern,
) -> Option<Ty> {
    match pattern {
        aast::Pattern::PVar(pv) => {
            let aast::PatVar { pos: p, id: _ } = &**pv;
            if tparamet {
                None
            } else {
                Some(make_type::nothing(reason::pattern(p.clone())))
            }
        }
        aast::Pattern::PRefinement(pr) => {
            let aast::PatRefinement {
                pos: p,
                id: _,
                hint: h,
            } = &**pr;
            let refined_ty = refine_for_hint(
                expr_pos,
                &reason::pattern(p.clone()),
                true,
                env,
                tparamet,
                ty,
                h,
            );
            Some(refined_ty)
        }
    }
}

pub(crate) fn refine_for_equality(pos: &Pos, env: &mut Env, te: &tast::Expr, ty: Ty) {
    let locl = make_a_local_of_tast(true, env, te);
    let var_type = &te.0;
    match locl {
        Some(locl_ivar) if !is_dynamic(var_type) => {
            let refined_ty = refine_and_simplify_intersection(
                env,
                pos,
                &reason::equal(pos.clone()),
                &locl_ivar.0,
                var_type.clone(),
                ty,
            );
            set_local(None, env, locl_ivar, refined_ty)
        }
        _ => {}
    }
}

pub(crate) fn key_exists(
    env: &mut Env,
    tparamet: bool,
    pos: &Pos,
    shape: &tast::Expr,
    field: &tast::Expr,
) {
    let field = tast::to_nast_expr(field.clone());
    refine_lvalue_type(env, shape, |env, shape_ty| {
        // `do_with_field_expr` reads the environment (it reports a bad field
        // name in it); `~with_error:(env, shape_ty)` and the callback go on
        // with the same environment.
        let env_for_field = env.clone();
        crate::typing_shapes::do_with_field_expr(
            &env_for_field,
            &field,
            shape_ty.clone(),
            |field_name: TshapeFieldName| {
                let field_name = t_shape_map::TShapeField(field_name);
                if tparamet {
                    crate::typing_shapes::refine_key_exists(field_name, pos.clone(), env, shape_ty)
                } else {
                    crate::typing_shapes::refine_not_key_exists(
                        field_name,
                        pos.clone(),
                        env,
                        shape_ty,
                    )
                }
            },
        )
    })
}

pub mod valkind {
    /// `[@@deriving show]`
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum T {
        Lvalue,
        LvalueSubexpr,
        Other,
    }

    /// `[@@deriving show]`: the constructor qualified by the module path.
    pub fn show(t: &T) -> String {
        match t {
            T::Lvalue => "Typing.Valkind.Lvalue",
            T::LvalueSubexpr => "Typing.Valkind.Lvalue_subexpr",
            T::Other => "Typing.Valkind.Other",
        }
        .to_string()
    }

    pub fn pp(fmt: &mut dyn std::fmt::Write, t: &T) -> std::fmt::Result {
        fmt.write_str(&show(t))
    }
}

pub(crate) fn check_bool_for_condition(env: &mut Env, pos: &Pos, ty_have: Ty) {
    let reason = reason::witness(pos.clone());
    let like_bool = make_type::locl_like(reason.clone(), make_type::bool(reason));
    let claim = {
        let pos = pos.clone();
        Lazy::new(move || Message(pos, reason::string_of_ureason(&Ureason::URcondition).into()))
    };
    let ty_err_opt = tutils::sub_type(
        env,
        None,
        None,
        None,
        None,
        ty_have,
        like_bool,
        Some(reasons_callback::with_claim(
            callback::expect_bool_for_condition(),
            claim,
        )),
    );
    match ty_err_opt {
        Some(ty_err) => typing_error_utils::add_typing_error(&ty_err, env),
        None => {}
    }
}

/// This represents a partially-processed result of type partitioning.
///    ty_trues and ty_falses take envs because they do intersections where you
///    want the updated environment.
pub(crate) struct TypeSplitInfo {
    /// Given the instantiated predicate type and the current env, get the parts of the union for the true branch
    pub ty_trues: Box<dyn Fn(Ty, &mut Env) -> Vec<Ty>>,
    /// Given the current env, get the parts of the union for the false branch
    pub ty_falses: Box<dyn Fn(&mut Env) -> Vec<Ty>>,
    /// A proposition that is to be assumed in the true branch
    pub true_assumptions: crate::typing_refinement::uninstantiated_typing_logic::SubtypeProp,
    /// A proposition that is to be assumed in the false branch
    pub false_assumptions: crate::typing_refinement::uninstantiated_typing_logic::SubtypeProp,
}

/// `Aast.map` (the `map` visitor that `[@@deriving visitors]` generates for
/// `aast_defs.ml`), restricted to what an expression can contain, for a
/// change of the annotations: `on_ex` is `on_'ex`, `on_en` is `on_'en`, and
/// everything else is copied. `oxidized::aast_visitor` cannot do this, as it
/// only visits an AST in place, without changing the type of its annotations.
///
/// The children are visited from left to right, as the generated visitor
/// does.
pub(crate) mod aast_map {
    use oxidized::aast::*;

    pub(crate) struct Map<'a, Ex, En, Ex2, En2> {
        pub on_ex: &'a mut dyn FnMut(&Ex) -> Ex2,
        pub on_en: &'a mut dyn FnMut(&En) -> En2,
    }

    impl<'a, Ex, En, Ex2, En2> Map<'a, Ex, En, Ex2, En2> {
        fn on_ex(&mut self, ex: &Ex) -> Ex2 {
            (self.on_ex)(ex)
        }

        fn on_en(&mut self, en: &En) -> En2 {
            (self.on_en)(en)
        }

        fn on_exprs(&mut self, el: &[Expr<Ex, En>]) -> Vec<Expr<Ex2, En2>> {
            el.iter().map(|e| self.on_expr(e)).collect()
        }

        fn on_expr_opt(&mut self, e: &Option<Expr<Ex, En>>) -> Option<Expr<Ex2, En2>> {
            e.as_ref().map(|e| self.on_expr(e))
        }

        pub(crate) fn on_expr(&mut self, e: &Expr<Ex, En>) -> Expr<Ex2, En2> {
            let Expr(ex, pos, e_) = e;
            let ex = self.on_ex(ex);
            Expr(ex, pos.clone(), self.on_expr_(e_))
        }

        pub(crate) fn on_expr_(&mut self, e: &Expr_<Ex, En>) -> Expr_<Ex2, En2> {
            match e {
                Expr_::Null => Expr_::Null,
                Expr_::True => Expr_::True,
                Expr_::False => Expr_::False,
                Expr_::Shape(fields) => Expr_::Shape(
                    fields
                        .iter()
                        .map(|(name, e)| (name.clone(), self.on_expr(e)))
                        .collect(),
                ),
                Expr_::ValCollection(x) => {
                    let (kind, targ, el) = &**x;
                    let targ = targ.as_ref().map(|t| self.on_targ(t));
                    Expr_::ValCollection(Box::new((kind.clone(), targ, self.on_exprs(el))))
                }
                Expr_::KeyValCollection(x) => {
                    let (kind, targs, fields) = &**x;
                    let targs = targs
                        .as_ref()
                        .map(|(t1, t2)| (self.on_targ(t1), self.on_targ(t2)));
                    let fields = fields.iter().map(|f| self.on_field(f)).collect();
                    Expr_::KeyValCollection(Box::new((kind.clone(), targs, fields)))
                }
                Expr_::This => Expr_::This,
                Expr_::Omitted => Expr_::Omitted,
                Expr_::Invalid(e) => Expr_::Invalid(Box::new(self.on_expr_opt(e))),
                Expr_::Id(id) => Expr_::Id(id.clone()),
                Expr_::Lvar(lid) => Expr_::Lvar(lid.clone()),
                Expr_::Dollardollar(lid) => Expr_::Dollardollar(lid.clone()),
                Expr_::Clone(e) => Expr_::Clone(Box::new(self.on_expr(e))),
                Expr_::ArrayGet(x) => {
                    let (e1, e2) = &**x;
                    let e1 = self.on_expr(e1);
                    Expr_::ArrayGet(Box::new((e1, self.on_expr_opt(e2))))
                }
                Expr_::ObjGet(x) => {
                    let (e1, e2, nf, pm) = &**x;
                    let e1 = self.on_expr(e1);
                    let e2 = self.on_expr(e2);
                    Expr_::ObjGet(Box::new((e1, e2, nf.clone(), pm.clone())))
                }
                Expr_::ClassGet(x) => {
                    let (cid, name, pm) = &**x;
                    let cid = self.on_class_id(cid);
                    Expr_::ClassGet(Box::new((cid, name.clone(), pm.clone())))
                }
                Expr_::ClassConst(x) => {
                    let (cid, name) = &**x;
                    let cid = self.on_class_id(cid);
                    Expr_::ClassConst(Box::new((cid, name.clone())))
                }
                Expr_::Call(c) => Expr_::Call(Box::new(self.on_call_expr(c))),
                Expr_::FunctionPointer(x) => {
                    let (id, targs, source) = &**x;
                    let id = self.on_function_ptr_id(id);
                    let targs = self.on_targs(targs);
                    Expr_::FunctionPointer(Box::new((id, targs, source.clone())))
                }
                Expr_::Int(s) => Expr_::Int(s.clone()),
                Expr_::Float(s) => Expr_::Float(s.clone()),
                Expr_::String(s) => Expr_::String(s.clone()),
                Expr_::String2(el) => Expr_::String2(self.on_exprs(el)),
                Expr_::PrefixedString(x) => {
                    let (prefix, e) = &**x;
                    Expr_::PrefixedString(Box::new((prefix.clone(), self.on_expr(e))))
                }
                Expr_::Yield(af) => Expr_::Yield(Box::new(self.on_afield(af))),
                Expr_::Await(e) => Expr_::Await(Box::new(self.on_expr(e))),
                Expr_::Delay(e) => Expr_::Delay(Box::new(self.on_expr(e))),
                Expr_::ReadonlyExpr(e) => Expr_::ReadonlyExpr(Box::new(self.on_expr(e))),
                Expr_::Tuple(el) => Expr_::Tuple(self.on_exprs(el)),
                Expr_::List(el) => Expr_::List(self.on_exprs(el)),
                Expr_::DestructureShape(ds) => {
                    Expr_::DestructureShape(Box::new(self.on_destructure_shape(ds)))
                }
                Expr_::DestructureTuple(dt) => {
                    Expr_::DestructureTuple(Box::new(self.on_destructure_tuple(dt)))
                }
                Expr_::Cast(x) => {
                    let (hint, e) = &**x;
                    Expr_::Cast(Box::new((hint.clone(), self.on_expr(e))))
                }
                Expr_::Unop(x) => {
                    let (uop, e) = &**x;
                    Expr_::Unop(Box::new((uop.clone(), self.on_expr(e))))
                }
                Expr_::Binop(b) => {
                    let Binop { bop, lhs, rhs } = &**b;
                    let lhs = self.on_expr(lhs);
                    let rhs = self.on_expr(rhs);
                    Expr_::Binop(Box::new(Binop {
                        bop: bop.clone(),
                        lhs,
                        rhs,
                    }))
                }
                Expr_::Assign(x) => {
                    let (e1, bop, e2) = &**x;
                    let e1 = self.on_expr(e1);
                    let e2 = self.on_expr(e2);
                    Expr_::Assign(Box::new((e1, bop.clone(), e2)))
                }
                Expr_::Pipe(x) => {
                    let (lid, e1, e2, nf) = &**x;
                    let e1 = self.on_expr(e1);
                    let e2 = self.on_expr(e2);
                    Expr_::Pipe(Box::new((lid.clone(), e1, e2, nf.clone())))
                }
                Expr_::Eif(x) => {
                    let (e1, e2, e3) = &**x;
                    let e1 = self.on_expr(e1);
                    let e2 = self.on_expr_opt(e2);
                    let e3 = self.on_expr(e3);
                    Expr_::Eif(Box::new((e1, e2, e3)))
                }
                Expr_::Is(x) => {
                    let (e, hint) = &**x;
                    Expr_::Is(Box::new((self.on_expr(e), hint.clone())))
                }
                Expr_::As(x) => {
                    let As_ {
                        expr,
                        hint,
                        is_nullable,
                        enforce_deep,
                    } = &**x;
                    Expr_::As(Box::new(As_ {
                        expr: self.on_expr(expr),
                        hint: hint.clone(),
                        is_nullable: *is_nullable,
                        enforce_deep: *enforce_deep,
                    }))
                }
                Expr_::Upcast(x) => {
                    let (e, hint) = &**x;
                    Expr_::Upcast(Box::new((self.on_expr(e), hint.clone())))
                }
                Expr_::New(x) => {
                    let (cid, targs, args, unpacked, ex) = &**x;
                    let cid = self.on_class_id(cid);
                    let targs = self.on_targs(targs);
                    let args = args.iter().map(|a| self.on_argument(a)).collect();
                    let unpacked = self.on_expr_opt(unpacked);
                    let ex = self.on_ex(ex);
                    Expr_::New(Box::new((cid, targs, args, unpacked, ex)))
                }
                Expr_::Efun(ef) => Expr_::Efun(Box::new(self.on_efun(ef))),
                Expr_::Lfun(x) => {
                    let (f, captures) = &**x;
                    let f = self.on_fun_(f);
                    let captures = captures.iter().map(|c| self.on_capture_lid(c)).collect();
                    Expr_::Lfun(Box::new((f, captures)))
                }
                Expr_::Xml(x) => {
                    let (name, attrs, el) = &**x;
                    let attrs = attrs.iter().map(|a| self.on_xhp_attribute(a)).collect();
                    let el = self.on_exprs(el);
                    Expr_::Xml(Box::new((name.clone(), attrs, el)))
                }
                Expr_::Import(x) => {
                    let (flavor, e) = &**x;
                    Expr_::Import(Box::new((flavor.clone(), self.on_expr(e))))
                }
                Expr_::Collection(x) => {
                    let (name, targ, afields) = &**x;
                    let targ = targ.as_ref().map(|t| self.on_collection_targ(t));
                    let afields = afields.iter().map(|af| self.on_afield(af)).collect();
                    Expr_::Collection(Box::new((name.clone(), targ, afields)))
                }
                Expr_::ExpressionTree(et) => {
                    let ExpressionTree {
                        class,
                        runtime_expr,
                        free_vars,
                    } = &**et;
                    Expr_::ExpressionTree(Box::new(ExpressionTree {
                        class: class.clone(),
                        runtime_expr: self.on_expr(runtime_expr),
                        free_vars: free_vars.clone(),
                    }))
                }
                Expr_::Lplaceholder(p) => Expr_::Lplaceholder(p.clone()),
                Expr_::MethodCaller(x) => Expr_::MethodCaller(x.clone()),
                Expr_::Pair(x) => {
                    let (targs, e1, e2) = &**x;
                    let targs = targs
                        .as_ref()
                        .map(|(t1, t2)| (self.on_targ(t1), self.on_targ(t2)));
                    let e1 = self.on_expr(e1);
                    let e2 = self.on_expr(e2);
                    Expr_::Pair(Box::new((targs, e1, e2)))
                }
                Expr_::ETSplice(s) => {
                    let EtSplice {
                        extract_client_type,
                        contains_await,
                        macro_variables,
                        temp_lid,
                        spliced_expr,
                    } = &**s;
                    Expr_::ETSplice(Box::new(EtSplice {
                        extract_client_type: *extract_client_type,
                        contains_await: *contains_await,
                        macro_variables: macro_variables.clone(),
                        temp_lid: temp_lid.clone(),
                        spliced_expr: self.on_expr(spliced_expr),
                    }))
                }
                Expr_::EnumClassLabel(x) => Expr_::EnumClassLabel(x.clone()),
                Expr_::Hole(x) => {
                    let (e, ex1, ex2, source) = &**x;
                    let e = self.on_expr(e);
                    let ex1 = self.on_ex(ex1);
                    let ex2 = self.on_ex(ex2);
                    Expr_::Hole(Box::new((e, ex1, ex2, source.clone())))
                }
                Expr_::Package(id) => Expr_::Package(id.clone()),
                Expr_::Nameof(cid) => Expr_::Nameof(Box::new(self.on_class_id(cid))),
            }
        }

        pub(crate) fn on_class_id(&mut self, cid: &ClassId<Ex, En>) -> ClassId<Ex2, En2> {
            let ClassId(ex, pos, cid_) = cid;
            let ex = self.on_ex(ex);
            ClassId(ex, pos.clone(), self.on_class_id_(cid_))
        }

        pub(crate) fn on_class_id_(&mut self, cid: &ClassId_<Ex, En>) -> ClassId_<Ex2, En2> {
            match cid {
                ClassId_::CIparent => ClassId_::CIparent,
                ClassId_::CIself => ClassId_::CIself,
                ClassId_::CIstatic => ClassId_::CIstatic,
                ClassId_::CIexpr(e) => ClassId_::CIexpr(self.on_expr(e)),
                ClassId_::CIreified(id) => ClassId_::CIreified(id.clone()),
                ClassId_::CI(id) => ClassId_::CI(id.clone()),
            }
        }

        fn on_targ(&mut self, targ: &Targ<Ex>) -> Targ<Ex2> {
            let Targ(ex, hint) = targ;
            Targ(self.on_ex(ex), hint.clone())
        }

        fn on_targs(&mut self, targs: &[Targ<Ex>]) -> Vec<Targ<Ex2>> {
            targs.iter().map(|t| self.on_targ(t)).collect()
        }

        fn on_type_hint(&mut self, th: &TypeHint<Ex>) -> TypeHint<Ex2> {
            let TypeHint(ex, hint) = th;
            TypeHint(self.on_ex(ex), hint.clone())
        }

        fn on_collection_targ(&mut self, ct: &CollectionTarg<Ex>) -> CollectionTarg<Ex2> {
            match ct {
                CollectionTarg::CollectionTV(t) => CollectionTarg::CollectionTV(self.on_targ(t)),
                CollectionTarg::CollectionTKV(t1, t2) => {
                    let t1 = self.on_targ(t1);
                    CollectionTarg::CollectionTKV(t1, self.on_targ(t2))
                }
            }
        }

        fn on_function_ptr_id(&mut self, id: &FunctionPtrId<Ex, En>) -> FunctionPtrId<Ex2, En2> {
            match id {
                FunctionPtrId::FPId(sid) => FunctionPtrId::FPId(sid.clone()),
                FunctionPtrId::FPClassConst(cid, name) => {
                    FunctionPtrId::FPClassConst(self.on_class_id(cid), name.clone())
                }
            }
        }

        fn on_field(&mut self, f: &Field<Ex, En>) -> Field<Ex2, En2> {
            let Field(e1, e2) = f;
            let e1 = self.on_expr(e1);
            Field(e1, self.on_expr(e2))
        }

        fn on_afield(&mut self, af: &Afield<Ex, En>) -> Afield<Ex2, En2> {
            match af {
                Afield::AFvalue(e) => Afield::AFvalue(self.on_expr(e)),
                Afield::AFkvalue(e1, e2) => {
                    let e1 = self.on_expr(e1);
                    Afield::AFkvalue(e1, self.on_expr(e2))
                }
            }
        }

        fn on_xhp_attribute(&mut self, a: &XhpAttribute<Ex, En>) -> XhpAttribute<Ex2, En2> {
            match a {
                XhpAttribute::XhpSimple(XhpSimple { name, type_, expr }) => {
                    let type_ = self.on_ex(type_);
                    XhpAttribute::XhpSimple(XhpSimple {
                        name: name.clone(),
                        type_,
                        expr: self.on_expr(expr),
                    })
                }
                XhpAttribute::XhpSpread(e) => XhpAttribute::XhpSpread(self.on_expr(e)),
            }
        }

        fn on_call_expr(&mut self, c: &CallExpr<Ex, En>) -> CallExpr<Ex2, En2> {
            let CallExpr {
                func,
                targs,
                args,
                unpacked_arg,
            } = c;
            let func = self.on_expr(func);
            let targs = self.on_targs(targs);
            let args = args.iter().map(|a| self.on_argument(a)).collect();
            let unpacked_arg = self.on_expr_opt(unpacked_arg);
            CallExpr {
                func,
                targs,
                args,
                unpacked_arg,
            }
        }

        fn on_argument(&mut self, a: &Argument<Ex, En>) -> Argument<Ex2, En2> {
            match a {
                Argument::Ainout(p, e) => Argument::Ainout(p.clone(), self.on_expr(e)),
                Argument::Anormal(e) => Argument::Anormal(self.on_expr(e)),
                Argument::Anamed(id, e) => Argument::Anamed(id.clone(), self.on_expr(e)),
            }
        }

        fn on_capture_lid(&mut self, c: &CaptureLid<Ex>) -> CaptureLid<Ex2> {
            let CaptureLid(ex, lid) = c;
            CaptureLid(self.on_ex(ex), lid.clone())
        }

        fn on_efun(&mut self, ef: &Efun<Ex, En>) -> Efun<Ex2, En2> {
            let Efun {
                fun,
                use_,
                closure_class_name,
                is_expr_tree_virtual_expr,
            } = ef;
            let fun = self.on_fun_(fun);
            let use_ = use_.iter().map(|c| self.on_capture_lid(c)).collect();
            Efun {
                fun,
                use_,
                closure_class_name: closure_class_name.clone(),
                is_expr_tree_virtual_expr: *is_expr_tree_virtual_expr,
            }
        }

        fn on_fun_(&mut self, f: &Fun_<Ex, En>) -> Fun_<Ex2, En2> {
            let Fun_ {
                span,
                readonly_this,
                annotation,
                readonly_ret,
                tparams,
                ret,
                params,
                ctxs,
                unsafe_ctxs,
                body,
                fun_kind,
                user_attributes,
                external,
                hidden,
                doc_comment,
            } = f;
            let annotation = self.on_en(annotation);
            let ret = self.on_type_hint(ret);
            let params = params.iter().map(|p| self.on_fun_param(p)).collect();
            let body = self.on_func_body(body);
            let user_attributes = self.on_user_attributes(user_attributes);
            Fun_ {
                span: span.clone(),
                readonly_this: readonly_this.clone(),
                annotation,
                readonly_ret: readonly_ret.clone(),
                tparams: tparams.clone(),
                ret,
                params,
                ctxs: ctxs.clone(),
                unsafe_ctxs: unsafe_ctxs.clone(),
                body,
                fun_kind: fun_kind.clone(),
                user_attributes,
                external: *external,
                hidden: *hidden,
                doc_comment: doc_comment.clone(),
            }
        }

        fn on_fun_param(&mut self, p: &FunParam<Ex, En>) -> FunParam<Ex2, En2> {
            let FunParam {
                annotation,
                type_hint,
                pos,
                name,
                info,
                readonly,
                splat,
                callconv,
                named,
                user_attributes,
                visibility,
            } = p;
            let annotation = self.on_ex(annotation);
            let type_hint = self.on_type_hint(type_hint);
            let info = match info {
                FunParamInfo::ParamOptional(e) => FunParamInfo::ParamOptional(self.on_expr_opt(e)),
                FunParamInfo::ParamRequired => FunParamInfo::ParamRequired,
                FunParamInfo::ParamVariadic => FunParamInfo::ParamVariadic,
            };
            let user_attributes = self.on_user_attributes(user_attributes);
            FunParam {
                annotation,
                type_hint,
                pos: pos.clone(),
                name: name.clone(),
                info,
                readonly: readonly.clone(),
                splat: splat.clone(),
                callconv: callconv.clone(),
                named: named.clone(),
                user_attributes,
                visibility: visibility.clone(),
            }
        }

        fn on_user_attributes(&mut self, uas: &UserAttributes<Ex, En>) -> UserAttributes<Ex2, En2> {
            let UserAttributes(uas) = uas;
            UserAttributes(
                uas.iter()
                    .map(|UserAttribute { name, params }| UserAttribute {
                        name: name.clone(),
                        params: self.on_exprs(params),
                    })
                    .collect(),
            )
        }

        fn on_func_body(&mut self, fb: &FuncBody<Ex, En>) -> FuncBody<Ex2, En2> {
            let FuncBody { fb_ast } = fb;
            FuncBody {
                fb_ast: self.on_block(fb_ast),
            }
        }

        fn on_block(&mut self, b: &Block<Ex, En>) -> Block<Ex2, En2> {
            let Block(stmts) = b;
            Block(stmts.iter().map(|s| self.on_stmt(s)).collect())
        }

        fn on_stmt(&mut self, s: &Stmt<Ex, En>) -> Stmt<Ex2, En2> {
            let Stmt(pos, s_) = s;
            Stmt(pos.clone(), self.on_stmt_(s_))
        }

        fn on_loop_cond(&mut self, lc: &LoopCond<Ex, En>) -> LoopCond<Ex2, En2> {
            let LoopCond(lids, block, e) = lc;
            let block = block.as_ref().map(|b| self.on_block(b));
            LoopCond(lids.clone(), block, self.on_expr(e))
        }

        fn on_loop_iter(&mut self, li: &LoopIter<Ex, En>) -> LoopIter<Ex2, En2> {
            let LoopIter(lids, block, el) = li;
            let block = block.as_ref().map(|b| self.on_block(b));
            LoopIter(lids.clone(), block, self.on_exprs(el))
        }

        fn on_stmt_(&mut self, s: &Stmt_<Ex, En>) -> Stmt_<Ex2, En2> {
            match s {
                Stmt_::Noop => Stmt_::Noop,
                Stmt_::Fallthrough => Stmt_::Fallthrough,
                Stmt_::Expr(e) => Stmt_::Expr(Box::new(self.on_expr(e))),
                Stmt_::Break => Stmt_::Break,
                Stmt_::Continue => Stmt_::Continue,
                Stmt_::Throw(e) => Stmt_::Throw(Box::new(self.on_expr(e))),
                Stmt_::Return(e) => Stmt_::Return(Box::new(self.on_expr_opt(e))),
                Stmt_::YieldBreak => Stmt_::YieldBreak,
                Stmt_::Awaitall(x) => {
                    let (assigns, block) = &**x;
                    let assigns = assigns
                        .iter()
                        .map(|(lid, e)| (lid.clone(), self.on_expr(e)))
                        .collect();
                    Stmt_::Awaitall(Box::new((assigns, self.on_block(block))))
                }
                Stmt_::Concurrent(b) => Stmt_::Concurrent(self.on_block(b)),
                Stmt_::If(x) => {
                    let (e, b1, b2) = &**x;
                    let e = self.on_expr(e);
                    let b1 = self.on_block(b1);
                    let b2 = self.on_block(b2);
                    Stmt_::If(Box::new((e, b1, b2)))
                }
                Stmt_::Do(x) => {
                    let (b, lc) = &**x;
                    let b = self.on_block(b);
                    Stmt_::Do(Box::new((b, self.on_loop_cond(lc))))
                }
                Stmt_::While(x) => {
                    let (lc, b) = &**x;
                    let lc = self.on_loop_cond(lc);
                    Stmt_::While(Box::new((lc, self.on_block(b))))
                }
                Stmt_::Using(u) => {
                    let UsingStmt {
                        is_block_scoped,
                        has_await,
                        exprs: (p, el),
                        block,
                    } = &**u;
                    let el = self.on_exprs(el);
                    Stmt_::Using(Box::new(UsingStmt {
                        is_block_scoped: *is_block_scoped,
                        has_await: *has_await,
                        exprs: (p.clone(), el),
                        block: self.on_block(block),
                    }))
                }
                Stmt_::For(x) => {
                    let (inits, cond, iter, b) = &**x;
                    let inits = self.on_exprs(inits);
                    let cond = cond.as_ref().map(|lc| self.on_loop_cond(lc));
                    let iter = self.on_loop_iter(iter);
                    let b = self.on_block(b);
                    Stmt_::For(Box::new((inits, cond, iter, b)))
                }
                Stmt_::Switch(x) => {
                    let (e, cases, default) = &**x;
                    let e = self.on_expr(e);
                    let cases = cases
                        .iter()
                        .map(|Case(e, b)| {
                            let e = self.on_expr(e);
                            Case(e, self.on_block(b))
                        })
                        .collect();
                    let default = default
                        .as_ref()
                        .map(|DefaultCase(p, b)| DefaultCase(p.clone(), self.on_block(b)));
                    Stmt_::Switch(Box::new((e, cases, default)))
                }
                Stmt_::Match(m) => {
                    let StmtMatch { expr, arms } = &**m;
                    let expr = self.on_expr(expr);
                    let arms = arms
                        .iter()
                        .map(|StmtMatchArm { pat, body }| StmtMatchArm {
                            pat: pat.clone(),
                            body: self.on_block(body),
                        })
                        .collect();
                    Stmt_::Match(Box::new(StmtMatch { expr, arms }))
                }
                Stmt_::Foreach(x) => {
                    let (e, as_e, b) = &**x;
                    let e = self.on_expr(e);
                    let as_e = self.on_as_expr(as_e);
                    let b = self.on_block(b);
                    Stmt_::Foreach(Box::new((e, as_e, b)))
                }
                Stmt_::Try(x) => {
                    let (b, catches, FinallyBlock(fb)) = &**x;
                    let b = self.on_block(b);
                    let catches = catches
                        .iter()
                        .map(|Catch(name, lid, b)| {
                            Catch(name.clone(), lid.clone(), self.on_block(b))
                        })
                        .collect();
                    let fb = FinallyBlock(fb.iter().map(|s| self.on_stmt(s)).collect());
                    Stmt_::Try(Box::new((b, catches, fb)))
                }
                Stmt_::Block(x) => {
                    let (lids, b) = &**x;
                    Stmt_::Block(Box::new((lids.clone(), self.on_block(b))))
                }
                Stmt_::Markup(s) => Stmt_::Markup(s.clone()),
            }
        }

        fn on_as_expr(&mut self, a: &AsExpr<Ex, En>) -> AsExpr<Ex2, En2> {
            match a {
                AsExpr::AsV(e) => AsExpr::AsV(self.on_expr(e)),
                AsExpr::AsKv(e1, e2) => {
                    let e1 = self.on_expr(e1);
                    AsExpr::AsKv(e1, self.on_expr(e2))
                }
                AsExpr::AwaitAsV(p, e) => AsExpr::AwaitAsV(p.clone(), self.on_expr(e)),
                AsExpr::AwaitAsKv(p, e1, e2) => {
                    let e1 = self.on_expr(e1);
                    AsExpr::AwaitAsKv(p.clone(), e1, self.on_expr(e2))
                }
            }
        }

        fn on_destructure_shape(
            &mut self,
            ds: &DestructureShape<Ex, En>,
        ) -> DestructureShape<Ex2, En2> {
            let DestructureShape {
                pos,
                fields,
                ellipsis,
            } = ds;
            DestructureShape {
                pos: pos.clone(),
                fields: fields
                    .iter()
                    .map(
                        |DestructureShapeField {
                             optional,
                             name,
                             target,
                         }| DestructureShapeField {
                            optional: *optional,
                            name: name.clone(),
                            target: self.on_destructure_target(target),
                        },
                    )
                    .collect(),
                ellipsis: *ellipsis,
            }
        }

        fn on_destructure_tuple(
            &mut self,
            dt: &DestructureTuple<Ex, En>,
        ) -> DestructureTuple<Ex2, En2> {
            let DestructureTuple {
                pos,
                entries,
                ellipsis,
            } = dt;
            DestructureTuple {
                pos: pos.clone(),
                entries: entries
                    .iter()
                    .map(
                        |DestructureTupleEntry { optional, target }| DestructureTupleEntry {
                            optional: *optional,
                            target: self.on_destructure_target(target),
                        },
                    )
                    .collect(),
                ellipsis: *ellipsis,
            }
        }

        fn on_destructure_target(
            &mut self,
            t: &DestructureTarget<Ex, En>,
        ) -> DestructureTarget<Ex2, En2> {
            let DestructureTarget(ex, en, t_) = t;
            let ex = self.on_ex(ex);
            let en = self.on_en(en);
            let t_ = match t_ {
                DestructureTarget_::DtLvar(lid) => DestructureTarget_::DtLvar(lid.clone()),
                DestructureTarget_::DtWildcard(p) => DestructureTarget_::DtWildcard(p.clone()),
                DestructureTarget_::DtShape(ds) => {
                    DestructureTarget_::DtShape(self.on_destructure_shape(ds))
                }
                DestructureTarget_::DtTuple(dt) => {
                    DestructureTarget_::DtTuple(self.on_destructure_tuple(dt))
                }
            };
            DestructureTarget(ex, en, t_)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fold_coercion_errs_conses_onto_the_front() {
        // `[Ok 1; Error (2, 3); Ok 4]`: `Error ([4; 2; 1], [4; 3; 1])`
        assert_eq!(
            fold_coercion_errs(vec![Ok(1), Err((2, 3)), Ok(4)]),
            Err((vec![4, 2, 1], vec![4, 3, 1]))
        );
        assert_eq!(fold_coercion_errs(vec![Ok(1), Ok(2)]), Ok(vec![2, 1]));
        assert_eq!(
            fold_coercion_errs(vec![Err((1, 2)), Err((3, 4))]),
            Err((vec![3, 1], vec![4, 2]))
        );
        assert_eq!(fold_coercion_errs::<i32>(vec![]), Ok(vec![]));
    }

    #[test]
    fn mismatches() {
        let none: Option<&()> = None;
        assert_eq!(mk_ty_mismatch_opt(1, 2, Some(&())), Some((1, 2)));
        assert_eq!(mk_ty_mismatch_opt(1, 2, none), None);
        assert_eq!(mk_ty_mismatch_res(1, 2, Some(&())), Err((1, 2)));
        assert_eq!(mk_ty_mismatch_res(1, 2, none), Ok(1));
    }

    #[test]
    fn ocaml_int_of_string() {
        assert_eq!(int_of_string("12"), 12);
        assert_eq!(int_of_string("-5"), -5);
        assert_eq!(int_of_string("+5"), 5);
        assert_eq!(int_of_string("1_000"), 1000);
        assert_eq!(int_of_string("0x1f"), 31);
        assert_eq!(int_of_string("0X1F"), 31);
        assert_eq!(int_of_string("0o17"), 15);
        assert_eq!(int_of_string("0b101"), 5);
        // Not octal in OCaml.
        assert_eq!(int_of_string("017"), 17);
        assert_eq!(int_of_string("4611686018427387903"), 4611686018427387903);
        assert_eq!(int_of_string("-4611686018427387904"), -4611686018427387904);
    }

    #[test]
    #[should_panic(expected = "int_of_string")]
    fn ocaml_int_of_string_fails_on_garbage() {
        int_of_string("_1");
    }

    #[test]
    #[should_panic(expected = "int_of_string")]
    fn ocaml_int_of_string_fails_out_of_range() {
        int_of_string("4611686018427387904");
    }

    #[test]
    fn supers() {
        assert_eq!(
            vc_kind_to_supers(aast::VcKind::Vector),
            vec!["\\HH\\Vector", "\\MutableVector"]
        );
        assert_eq!(
            vc_kind_to_supers(aast::VcKind::Keyset),
            vec!["\\HH\\keyset"]
        );
        assert_eq!(
            kvc_kind_to_supers(aast::KvcKind::ImmMap),
            vec!["\\HH\\ImmMap", "\\ConstMap"]
        );
    }

    #[test]
    fn valkind_show() {
        assert_eq!(valkind::show(&valkind::T::Lvalue), "Typing.Valkind.Lvalue");
        assert_eq!(
            valkind::show(&valkind::T::LvalueSubexpr),
            "Typing.Valkind.Lvalue_subexpr"
        );
        assert_eq!(valkind::show(&valkind::T::Other), "Typing.Valkind.Other");
    }

    #[test]
    fn consistent_construct() {
        let e: nast::Expr = aast::Expr((), Pos::NONE, aast::Expr_::Null);
        assert!(requires_consistent_construct::<(), ()>(
            &aast::ClassId_::CIstatic
        ));
        assert!(requires_consistent_construct(&aast::ClassId_::CIexpr(e)));
        assert!(!requires_consistent_construct::<(), ()>(
            &aast::ClassId_::CIself
        ));
        assert!(!requires_consistent_construct::<(), ()>(
            &aast::ClassId_::CIparent
        ));
        assert!(!requires_consistent_construct::<(), ()>(
            &aast::ClassId_::CI(ast_defs::Id(Pos::NONE, "\\C".to_string()))
        ));
    }

    fn prim(p: aast::Tprim) -> Ty {
        mk((reason::none(), Ty_::Tprim(p)))
    }

    fn class(tyl: Vec<Ty>) -> Ty {
        mk((
            reason::none(),
            Ty_::Tclass((Pos::NONE, "\\C".to_string()), nonexact(), tyl),
        ))
    }

    #[test]
    fn pack_errs_substitutes_the_expected_types() {
        let (int, arraykey, float, bool, num) = (
            prim(aast::Tprim::Tint),
            prim(aast::Tprim::Tarraykey),
            prim(aast::Tprim::Tfloat),
            prim(aast::Tprim::Tbool),
            prim(aast::Tprim::Tnum),
        );
        let ty = class(vec![int.clone(), arraykey.clone(), float.clone()]);
        // An error at the first position and at the variadic one.
        let errs = (
            vec![Some((int.clone(), bool.clone())), None],
            Some((float.clone(), num.clone())),
        );
        let expected = class(vec![bool.clone(), arraykey.clone(), num.clone()]);
        assert!(equal_locl_ty(&pack_errs(&Pos::NONE, &ty, &errs), &expected));
        // No variadic error: the rest is kept.
        let errs = (vec![None, Some((arraykey.clone(), bool.clone()))], None);
        let expected = class(vec![int.clone(), bool.clone(), float.clone()]);
        assert!(equal_locl_ty(&pack_errs(&Pos::NONE, &ty, &errs), &expected));
        // Neither a tuple nor a class.
        let packed = pack_errs(&Pos::NONE, &int, &(vec![], None));
        assert!(is_nothing(&packed));
    }

    #[test]
    fn with_type_sets_every_annotation() {
        let ty = make_type::int(reason::none());
        let lvar = |x: &str| -> nast::Expr {
            aast::Expr(
                (),
                Pos::NONE,
                aast::Expr_::Lvar(Box::new(aast::Lid(
                    Pos::NONE,
                    oxidized::local_id::make_unscoped(x),
                ))),
            )
        };
        let hint = aast::Hint(Pos::NONE, Box::new(aast::Hint_::Hmixed));
        let call: nast::Expr = aast::Expr(
            (),
            Pos::NONE,
            aast::Expr_::Call(Box::new(aast::CallExpr {
                func: aast::Expr(
                    (),
                    Pos::NONE,
                    aast::Expr_::Id(Box::new(ast_defs::Id(Pos::NONE, "\\f".to_string()))),
                ),
                targs: vec![aast::Targ((), hint)],
                args: vec![aast::Argument::Anormal(aast::Expr(
                    (),
                    Pos::NONE,
                    aast::Expr_::Hole(Box::new((lvar("$x"), (), (), aast::HoleSource::Typing))),
                ))],
                unpacked_arg: Some(lvar("$y")),
            })),
        );
        let te = with_type(ty.clone(), tast::dummy_saved_env(), &call);
        let is_ty = |t: &Ty| equal_locl_ty(t, &ty);
        assert!(is_ty(&te.0));
        match &te.2 {
            aast::Expr_::Call(c) => {
                assert!(is_ty(&c.func.0));
                assert!(is_ty(&c.targs[0].0));
                match &c.args[..] {
                    [aast::Argument::Anormal(aast::Expr(t, _, aast::Expr_::Hole(h)))] => {
                        assert!(is_ty(t));
                        let (e, t1, t2, _) = &**h;
                        assert!(is_ty(&e.0) && is_ty(t1) && is_ty(t2));
                    }
                    _ => panic!("the argument is a hole"),
                }
                assert!(is_ty(&c.unpacked_arg.as_ref().unwrap().0));
            }
            _ => panic!("the expression is a call"),
        }
    }
}
