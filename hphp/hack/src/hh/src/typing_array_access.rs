// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_array_access.ml`. See `hh/PORTING.md`.
//!
//! The callbacks given to `Typing_generic_rules` return, for each part of the
//! container type, the OCaml `(locl_ty, locl_ty * locl_ty) result`
//! ([`TyMismatchRes`]); the generic rules turn them into the
//! `(locl_ty * locl_ty) option` of the signatures of [`assign_array_append`]
//! and [`assign_array_get`].

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::pos_or_decl;
use crate::tast;
use crate::typechecker_options;
use crate::typing_class_pointers;
use crate::typing_coercion;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_defs_core::t_shape_map;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::ReadOrWrite;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_generic_rules as generic_rules;
use crate::typing_intersection;
use crate::typing_log;
use crate::typing_make_type as make_type;
use crate::typing_ops;
use crate::typing_print;
use crate::typing_reason as reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_shape_normalize;
use crate::typing_shapes;
use crate::typing_solver;
use crate::typing_union;
use crate::typing_utils as t_utils;

/// `Naming_special_names.Classes.cString` (`naming_special_names_rust` does
/// not have it).
const C_STRING: &str = "\\HH\\string";

/// `(locl_ty, locl_ty * locl_ty) result`: the type, or the actual and the
/// expected types of a mismatch.
pub type TyMismatchRes = std::result::Result<Ty, (Ty, Ty)>;

/// `Option.merge e1 e2 ~f`
fn option_merge<A>(e1: Option<A>, e2: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(f(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// `lazy (Typing_print.error env ty)`
fn lazy_print_error(env: &Env, ty: &Ty) -> Lazy<String> {
    let env = env.clone();
    let ty = ty.clone();
    Lazy::new(move || typing_print::error(None, &env, &ty))
}

/// `Typing_log.(log_with_level env "typing" ~level:1 (fun () -> log_types
/// (Pos_or_decl.of_raw_pos p) env [Log_head (head, [Log_type (name, ty); ...])]))`
fn log_types_at_level_1(env: &Env, p: &Pos, head: &str, tys: &[(&str, &Ty)]) {
    typing_log::log_with_level(env, "typing", 1, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(p.clone()),
            env,
            &[typing_log::LogStructure::LogHead(
                head.to_string(),
                tys.iter()
                    .map(|(name, ty)| {
                        typing_log::LogStructure::LogType(name.to_string(), (*ty).clone())
                    })
                    .collect(),
            )],
        )
    })
}

fn mk_ty_mismatch_res(
    ty_have: Ty,
    ty_expect: Ty,
    ty_err_opt: &Option<typing_error::T>,
) -> TyMismatchRes {
    match ty_err_opt {
        None => Ok(ty_have),
        Some(_) => Err((ty_have, ty_expect)),
    }
}

fn err_witness(env: &mut Env, p: &Pos) -> Ty {
    env_::fresh_type_error(env, p.clone())
}

fn error_assign_array_append(env: &mut Env, p: &Pos, ty: Ty) -> Ty {
    if !t_utils::is_tyvar_error(env, &ty) {
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Array_append {
                pos: p.clone(),
                decl_pos: get_pos(&ty),
                ty_name: lazy_print_error(env, &ty),
            }),
            env,
        );
    }
    ty
}

fn maybe_make_supportdyn(r: Reason, env: &mut Env, supportdyn: bool, ty: Ty) -> Ty {
    if supportdyn {
        let ty: Ty = t_utils::make_supportdyn(r, env, ty);
        ty
    } else {
        ty
    }
}

/// Check that an index to a map-like collection passes the basic test of
/// being a subtype of arraykey
fn check_arraykey_index(
    error: impl FnOnce(Pos, (PosOrDecl, Lazy<String>), (PosOrDecl, Lazy<String>)) -> primary::T,
    env: &mut Env,
    pos: &Pos,
    container_ty: Ty,
    index_ty: Ty,
) -> TyMismatchRes {
    let container_ty = env_::expand_type(env, container_ty);
    let reason = match get_node(&container_ty) {
        Ty_::Tclass((_, cn), _, _) => reason::index_class(cn),
        _ => reason::index_array(),
    };
    let info_of_type = |ty: &Ty| (get_pos(ty), lazy_print_error(env, ty));
    let container_info = info_of_type(&container_ty);
    let index_info = info_of_type(&index_ty);
    let ty_arraykey = make_type::arraykey(reason::idx_dict(pos.clone()));
    // If we have an error in coercion here, we will add a `Hole` indicating the
    // actual and expected type. The `Hole` may then be used in a codemod to
    // add a call to `UNSAFE_CAST` so we need to consider what type we expect.
    // There is a somewhat common pattern in older parts of www to do something like:
    //
    // ```
    // function keyset_issue(?string $x): keyset<string> {
    //   $xs = keyset<string>[];
    //   ...
    //   /* HH_FIXME[4435] keyset values must be arraykeys */
    //   $xs[] = $x;
    //   return Keyset\filter_nulls($xs);
    // }
    // ```
    // (even though it is impossible for keysets to contain nulls).
    //
    // If we were to add an expected type of 'arraykey' here it would be
    // correct but adding an `UNSAFE_CAST<?string,arraykey>($x)` means we
    // get cascading errors; here, we now have the wrong return type.
    //
    // To try and prevent this, if this is an optional type where the nonnull
    // part can be coerced to arraykey, we prefer that type as our expected type.
    let base_error = error(pos.clone(), container_info, index_info);
    let (ty_actual, is_option) = match get_node(&index_ty) {
        Ty_::Toption(inner_ty) => (inner_ty.clone(), true),
        _ => (index_ty.clone(), false),
    };
    let e1: Option<typing_error::T> = typing_coercion::coerce_type(
        Some(true), // coerce_for_op
        None,       // is_dynamic_aware
        None,       // ignore_readonly
        pos.clone(),
        reason,
        env,
        ty_actual.clone(),
        ty_arraykey.clone(),
        Enforcement::Enforced,
        callback::always(base_error.clone()),
    );
    let (ty_mismatch, e2) = match e1 {
        None if is_option => (
            Err((index_ty, ty_actual)),
            Some(typing_error::primary(base_error)),
        ),
        None => (Ok(index_ty), None),
        Some(_) => (Err((index_ty, ty_arraykey)), None),
    };
    if let Some(e) = option_merge(e1, e2, typing_error::both) {
        typing_error_utils::add_typing_error(&e, env)
    }
    ty_mismatch
}

fn check_arraykey_index_write(
    env: &mut Env,
    pos: &Pos,
    container_ty: Ty,
    index_ty: Ty,
) -> TyMismatchRes {
    let mk_err = |pos, (container_pos, container_ty_name), (key_pos, key_ty_name)| {
        primary::T::Invalid_arraykey {
            pos,
            ctxt: ReadOrWrite::write,
            container_pos,
            container_ty_name,
            key_pos,
            key_ty_name,
        }
    };
    check_arraykey_index(mk_err, env, pos, container_ty, index_ty)
}

fn check_keyset_value(env: &mut Env, pos: &Pos, container_ty: Ty, index_ty: Ty) -> TyMismatchRes {
    let mk_err = |pos, (container_pos, container_ty_name), (value_pos, value_ty_name)| {
        primary::T::Invalid_keyset_value {
            pos,
            container_pos,
            container_ty_name,
            value_pos,
            value_ty_name,
        }
    };
    check_arraykey_index(mk_err, env, pos, container_ty, index_ty)
}

fn check_set_value(env: &mut Env, pos: &Pos, container_ty: Ty, index_ty: Ty) -> TyMismatchRes {
    let mk_err = |pos, (container_pos, container_ty_name), (value_pos, value_ty_name)| {
        primary::T::Invalid_set_value {
            pos,
            container_pos,
            container_ty_name,
            value_pos,
            value_ty_name,
        }
    };
    check_arraykey_index(mk_err, env, pos, container_ty, index_ty)
}

pub fn pessimise_type(env: &mut Env, ty: Ty) -> Ty {
    let dynamic = make_type::dynamic(get_reason(&ty).clone());
    typing_union::union(env, None, None, ty, dynamic)
}

pub fn maybe_pessimise_type(env: &mut Env, ty: Ty) -> Ty {
    // `Typechecker_options.pessimise_builtins`, which `crate::typechecker_options`
    // does not have: `everything_sdt t || t.tco_pessimise_builtins`.
    let pessimise_builtins =
        |t: &typechecker_options::T| t.po.everything_sdt || t.tco_pessimise_builtins;
    if pessimise_builtins(&env_::get_tcopt(env)) {
        pessimise_type(env, ty)
    } else {
        ty
    }
}

fn type_index(
    read: bool,
    env: &mut Env,
    p: &Pos,
    ty_have: Ty,
    ty_expect: Ty,
    enforced: Enforcement,
    reason: Ureason,
) -> (Option<typing_error::T>, TyMismatchRes) {
    let log_name = if read {
        "array_get/type_index"
    } else {
        "assign_array_set/type_index"
    };
    log_types_at_level_1(
        env,
        p,
        log_name,
        &[("ty_have", &ty_have), ("ty_expect", &ty_expect)],
    );
    let ty_err_opt: Option<typing_error::T> = typing_coercion::coerce_type(
        Some(true), // coerce_for_op
        None,       // is_dynamic_aware
        None,       // ignore_readonly
        p.clone(),
        reason,
        env,
        ty_have.clone(),
        ty_expect.clone(),
        enforced,
        callback::index_type_mismatch(),
    );
    let ty_mismatch = mk_ty_mismatch_res(ty_have, ty_expect, &ty_err_opt);
    (ty_err_opt, ty_mismatch)
}

/// Given a type `ty` known to be a lower bound on the type of the array operand
/// to an array append operation, compute the largest upper bound on that type
/// that validates the get operation. For example, if `vec<string>` is a lower
/// bound, then `vec<#1>` is a suitable upper bound.`
fn widen_for_assign_array_append(expr_pos: &Pos, env: &mut Env, ty: Ty) -> Option<Ty> {
    match get_node(&ty) {
        // dynamic is valid for array append
        Ty_::Tdynamic(_) => Some(ty),
        Ty_::Tclass(id, _, tyl)
            if id.1 == sn::collections::VEC
                || id.1 == sn::collections::KEYSET
                || id.1 == sn::collections::VECTOR
                || id.1 == sn::collections::MAP =>
        {
            let params: Vec<Ty> = tyl
                .iter()
                .map(|_ty| env_::fresh_type_invariant(env, expr_pos.clone()))
                .collect();
            let ty = mk((
                get_reason(&ty).clone(),
                Ty_::Tclass(id.clone(), nonexact(), params),
            ));
            Some(ty)
        }
        _ => None,
    }
}

/// Check an array append expression returning the modified typing environment,
/// the resulting type of the lhs expression, an optional subtyping errors for
/// the lhs expression and an optional subtyping error for the expression to be
/// appended
pub fn assign_array_append(
    array_pos: Pos,
    expr_pos: Pos,
    ur: Ureason,
    env: &mut Env,
    ty1: Ty,
    ty2: Ty,
) -> (Ty, Option<(Ty, Ty)>, Option<(Ty, Ty)>) {
    let (array_pos, expr_pos) = (&array_pos, &expr_pos);
    let coerce_set_value =
        |env: &mut Env, ty: Ty| typing_class_pointers::coerce_to_name(env, ty);
    let (ty_err1, ty1): (Option<typing_error::T>, Ty) = typing_solver::expand_type_and_narrow(
        env,
        None, // default
        None, // allow_nothing
        None, // force_solve
        "an array or collection",
        |env: &mut Env, ty: Ty| widen_for_assign_array_append(expr_pos, env, ty),
        array_pos.clone(),
        ty1,
    );
    if let Some(e) = &ty_err1 {
        typing_error_utils::add_typing_error(e, env)
    }
    generic_rules::apply_rules_with_index_value_ty_mismatches(
        None,  // ignore_type_structure
        false, // preserve_supportdyn
        env,
        ty1,
        |env: &mut Env, supportdyn: bool, ty1: Ty| -> (Ty, TyMismatchRes, TyMismatchRes) {
            // In dynamic mode strip off nullable because we can always upcast to dynamic
            let ty1 = match get_node(&ty1) {
                Ty_::Toption(ty) if tast::is_under_dynamic_assumptions(env.checked) => ty.clone(),
                _ => ty1,
            };
            let got_dynamic = |env: &mut Env| -> (Ty, TyMismatchRes, TyMismatchRes) {
                // Dynamic inference: propagate shadow type variables through array
                // append. If the container carries a shadow type variable, create one
                // for the element to track its inferred element type.
                let result_shadow = match get_node(&ty1) {
                    Ty_::Tdynamic(Some(shadow_v)) => {
                        let container_ty =
                            make_type::container(get_reason(&ty1).clone(), ty2.clone());
                        env_::add_tyvar_upper_bound(
                            None,
                            env,
                            *shadow_v,
                            InternalType::LoclType(container_ty),
                        );
                        Some(*shadow_v)
                    }
                    _ => None,
                };
                let tv = mk((get_reason(&ty1).clone(), Ty_::Tdynamic(result_shadow)));
                let val_ty_err_opt: Option<typing_error::T> = t_utils::supports_dynamic(
                    env,
                    ty2.clone(),
                    Some(reasons_callback::unify_error_at(expr_pos.clone())),
                );
                if let Some(e) = &val_ty_err_opt {
                    typing_error_utils::add_typing_error(e, env)
                }
                let val_err_res = mk_ty_mismatch_res(ty2.clone(), tv.clone(), &val_ty_err_opt);
                (tv.clone(), Ok(tv), val_err_res)
            };
            let r = get_reason(&ty1).clone();
            match get_node(&ty1) {
                Ty_::Tany(_) => (ty1.clone(), Ok(ty1.clone()), Ok(ty2.clone())),
                Ty_::Tclass((_, n), _, tyl) if tyl.len() == 1 && n == sn::collections::VECTOR => {
                    let tv = tyl[0].clone();
                    let tv = maybe_make_supportdyn(r, env, supportdyn, tv);
                    let tv = maybe_pessimise_type(env, tv);
                    let val_ty_err_opt: Option<typing_error::T> = typing_ops::sub_type(None, 
                        expr_pos.clone(),
                        ur.clone(),
                        env,
                        ty2.clone(),
                        tv.clone(),
                        callback::unify_error(),
                    );
                    if let Some(e) = &val_ty_err_opt {
                        typing_error_utils::add_typing_error(e, env)
                    }
                    let val_err_res = mk_ty_mismatch_res(ty2.clone(), tv, &val_ty_err_opt);
                    (ty1.clone(), Ok(ty1.clone()), val_err_res)
                }
                // Handle the case where Vector or Set was used as a typehint
                // without type parameters
                Ty_::Tclass((_, n), _, tyl) if tyl.is_empty() && n == sn::collections::VECTOR => {
                    (ty1.clone(), Ok(ty1.clone()), Ok(ty2.clone()))
                }
                Ty_::Tclass(id, e, tyl)
                    if tyl.is_empty()
                        && (id.1 == sn::collections::KEYSET || id.1 == sn::collections::SET) =>
                {
                    let n = &id.1;
                    let ty2 = coerce_set_value(env, ty2.clone());
                    let val_err_res = if n == sn::collections::KEYSET {
                        check_keyset_value(env, expr_pos, ty1.clone(), ty2.clone())
                    } else {
                        check_set_value(env, expr_pos, ty1.clone(), ty2.clone())
                    };
                    let ty = mk((r, Ty_::Tclass(id.clone(), e.clone(), vec![ty2])));
                    (ty.clone(), Ok(ty), val_err_res)
                }
                Ty_::Tclass(id, e, tyl) if tyl.len() == 1 && id.1 == sn::collections::VEC => {
                    let tv = tyl[0].clone();
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv);
                    let tv_ = typing_union::union(env, None, None, tv, ty2.clone());
                    let ty = mk((r, Ty_::Tclass(id.clone(), e.clone(), vec![tv_])));
                    (ty.clone(), Ok(ty), Ok(ty2.clone()))
                }
                Ty_::Tclass(id, e, tyl) if tyl.len() == 1 && id.1 == sn::collections::KEYSET => {
                    let tv = tyl[0].clone();
                    let ty2 = coerce_set_value(env, ty2.clone());
                    let err_res = check_keyset_value(env, expr_pos, ty1.clone(), ty2.clone());
                    let tk_ = {
                        let r = reason::key_value_collection_key(expr_pos.clone());
                        let ak_t = make_type::arraykey(r.clone());
                        let ty2 = typing_intersection::intersect(env, r, ak_t, ty2);
                        typing_union::union(env, None, None, tv, ty2)
                    };
                    let ty = mk((r, Ty_::Tclass(id.clone(), e.clone(), vec![tk_])));
                    (ty.clone(), Ok(ty), err_res)
                }
                Ty_::Tclass((_, n), _, tyl) if tyl.len() == 1 && n == sn::collections::SET => {
                    let tv = tyl[0].clone();
                    let ty2 = coerce_set_value(env, ty2.clone());
                    let err_res = {
                        // `match check_set_value env expr_pos ty1 ty2 with
                        //  | (_, Error _) as err_res -> err_res | (env, _) -> ...`
                        match check_set_value(env, expr_pos, ty1.clone(), ty2.clone()) {
                            err_res @ Err(_) => err_res,
                            Ok(_) => {
                                let (tv_, enforced) = {
                                    let ak_t =
                                        make_type::arraykey(reason::idx_vector(expr_pos.clone()));
                                    let tv = maybe_pessimise_type(env, tv.clone());
                                    if t_utils::is_sub_type_for_union(env, &ak_t, &tv) {
                                        // hhvm will enforce that the key is an arraykey, so if
                                        // $x : Set<arraykey>, then it should be allowed to
                                        // set $x[] = e where $d : dynamic.
                                        (tv, Enforcement::Enforced)
                                    } else {
                                        // It is unsound to allow $x[] = e if $x : Set<string>
                                        // since the dynamic $d might be an int and hhvm wouldn't
                                        // complain.
                                        (tv, Enforcement::Unenforced)
                                    }
                                };
                                let ty_err_opt: Option<typing_error::T> =
                                    typing_coercion::coerce_type(
                                        Some(true), // coerce_for_op
                                        None,       // is_dynamic_aware
                                        None,       // ignore_readonly
                                        expr_pos.clone(),
                                        ur.clone(),
                                        env,
                                        ty2.clone(),
                                        tv_,
                                        enforced,
                                        callback::unify_error(),
                                    );
                                if let Some(e) = &ty_err_opt {
                                    typing_error_utils::add_typing_error(e, env)
                                }
                                mk_ty_mismatch_res(ty2.clone(), tv, &ty_err_opt)
                            }
                        }
                    };
                    (ty1.clone(), Ok(ty1.clone()), err_res)
                }
                Ty_::Tdynamic(_) => got_dynamic(env),
                Ty_::Tprim(Tprim::Tnull) if tast::is_under_dynamic_assumptions(env.checked) => {
                    got_dynamic(env)
                }
                Ty_::Tnewtype(cid, _, _bound) if cid == sn::classes::SUPPORT_DYN => {
                    // We must be under_dynamic_assumptions because
                    // apply_rules_with_index_value_ty_mismatches otherwise descends into the newtype.
                    // In this case we just accept the assignment because it's as though
                    // we applied an implicit upcast to dynamic
                    got_dynamic(env)
                }
                Ty_::Tnonnull
                | Ty_::TvecOrDict(_, _)
                | Ty_::Toption(_)
                | Ty_::Tprim(_)
                | Ty_::Tvar(_)
                | Ty_::Tfun(_)
                | Ty_::Tclass(_, _, _)
                | Ty_::Ttuple(_)
                | Ty_::Tshape(_)
                | Ty_::Tunion(_)
                | Ty_::Tintersection(_)
                | Ty_::Tlabel(_)
                | Ty_::Tgeneric(_)
                | Ty_::Tnewtype(_, _, _)
                | Ty_::Tdependent(_, _)
                | Ty_::Taccess(_)
                | Ty_::Tneg(_)
                | Ty_::TclassPtr(_) => {
                    let ty = error_assign_array_append(env, expr_pos, ty1.clone());
                    let ty = maybe_make_supportdyn(r, env, supportdyn, ty);
                    let ty_nothing = make_type::nothing(reason::none());
                    (
                        ty.clone(),
                        Err((ty, ty_nothing.clone())),
                        Err((ty2.clone(), ty_nothing)),
                    )
                }
            }
        },
    )
}

fn widen_for_assign_array_get(
    expr_pos: &Pos,
    index_expr: &nast::Expr,
    env: &mut Env,
    ty: Ty,
) -> Option<Ty> {
    log_types_at_level_1(env, expr_pos, "widen_for_assign_array_get", &[("ty", &ty)]);
    match get_node(&ty) {
        // dynamic is valid for assign array get
        Ty_::Tdynamic(_) => Some(ty),
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: TupleExtra::Tvariadic(t_variadic),
        }) => {
            // requires integer literal
            match index_expr {
                // Should freshen type variables
                nast::Expr(_, _, nast::Expr_::Int(_)) => {
                    let t_required: Vec<Ty> = t_required
                        .iter()
                        .map(|_ty| env_::fresh_type_invariant(env, expr_pos.clone()))
                        .collect();
                    let t_optional: Vec<Ty> = t_optional
                        .iter()
                        .map(|_ty| env_::fresh_type_invariant(env, expr_pos.clone()))
                        .collect();
                    Some(mk((
                        get_reason(&ty).clone(),
                        Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: t_optional,
                            extra: TupleExtra::Tvariadic(t_variadic.clone()),
                        }),
                    )))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// `int_of_string_opt`: an OCaml integer literal (a sign, `0x`, `0o`, `0b`
/// or `0u`, digits and `_`), within the range of an OCaml `int` (63 bits).
fn int_of_string_opt(s: &str) -> Option<isize> {
    const MAX: i128 = (1 << 62) - 1;
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
    // The first character is a digit; `_` can follow.
    if !digits.chars().next()?.is_digit(radix) {
        return None;
    }
    let mut n: i128 = 0;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        n = n * radix as i128 + c.to_digit(radix)? as i128;
        // Unsigned literals can use all the 63 bits; they wrap around.
        if n > 2 * MAX + 1 {
            return None;
        }
    }
    if decimal {
        // Decimal literals are signed: up to `max_int`, or `-min_int`.
        if n > MAX + (negative as i128) {
            return None;
        }
    } else if n > MAX {
        n -= 2 * (MAX + 1);
    }
    Some((if negative { -n } else { n }) as isize)
}

/// `List.split_n l n`: the first `n` elements and the rest (all of `l` and
/// nothing if `n` is larger than its length, nothing and all of `l` if `n` is
/// negative).
fn split_n(l: &[Ty], n: isize) -> (&[Ty], &[Ty]) {
    let n = n.clamp(0, l.len() as isize) as usize;
    l.split_at(n)
}

/// Check an array append expression returning the modified typing environment,
/// the resulting type of the lhs expression, an optional subtyping errors for
/// the indexed expression, an optional subtyping error for the indexing expression
/// , and an optional subtyping error for the rhs expression
///
/// Used for typing an assignment e1[key] = e2
/// where e1 has type ty1, key has type tkey and e2 has type ty2.
/// Return the new array type
pub fn assign_array_get(
    array_pos: Pos,
    expr_pos: Pos,
    ur: Ureason,
    env: &mut Env,
    ty1: Ty,
    key: &nast::Expr,
    tkey: Ty,
    ty2: Ty,
) -> (Ty, Option<(Ty, Ty)>, Option<(Ty, Ty)>, Option<(Ty, Ty)>) {
    let (array_pos, expr_pos) = (&array_pos, &expr_pos);
    log_types_at_level_1(
        env,
        expr_pos,
        "assign_array_get",
        &[("ty1", &ty1), ("ty2", &ty2)],
    );
    let (ty_err1, ety1): (Option<typing_error::T>, Ty) = typing_solver::expand_type_and_narrow(
        env,
        None, // default
        None, // allow_nothing
        None, // force_solve
        "an array or collection",
        |env: &mut Env, ty: Ty| widen_for_assign_array_get(expr_pos, key, env, ty),
        array_pos.clone(),
        ty1,
    );
    if let Some(e) = &ty_err1 {
        typing_error_utils::add_typing_error(e, env)
    }
    generic_rules::apply_rules_with_array_index_value_ty_mismatches(
        None,        // ignore_type_structure
        Some(false), // preserve_supportdyn
        env,
        ety1,
        |env: &mut Env,
         supportdyn: bool,
         ety1: Ty|
         -> (Ty, TyMismatchRes, TyMismatchRes, TyMismatchRes) {
            let (r, ety1_) = match get_node(&ety1) {
                Ty_::Toption(ty) if tast::is_under_dynamic_assumptions(env.checked) => {
                    // If we're under dynamic assumptions just check that the target supports dynamic
                    (get_reason(ty).clone(), ty.clone())
                }
                _ => (get_reason(&ety1).clone(), ety1.clone()),
            };
            // `arity_error` reports in the environment the callback was given
            // (OCaml's closure captures it), whatever the case has done to the
            // environment before calling it.
            let env_at_start = env.clone();
            let arity_error = |(_, name): &(PosOrDecl, String)| {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Array_get_arity {
                        pos: expr_pos.clone(),
                        name: name.clone(),
                        decl_pos: reason::to_pos(&r),
                    }),
                    &env_at_start,
                )
            };
            let got_dynamic = |env: &mut Env| -> (Ty, TyMismatchRes, TyMismatchRes, TyMismatchRes) {
                // Dynamic inference: propagate shadow type variables through array
                // assignment. Create a shadow for the value type and record a
                // KeyedContainer upper bound on the container's shadow, capturing the
                // key type used at this access.
                let result_shadow = match get_node(&ety1_) {
                    Ty_::Tdynamic(Some(shadow_v)) => {
                        let container_ty =
                            make_type::keyed_container(r.clone(), tkey.clone(), ty2.clone());
                        env_::add_tyvar_upper_bound(
                            None,
                            env,
                            *shadow_v,
                            InternalType::LoclType(container_ty),
                        );
                        Some(*shadow_v)
                    }
                    _ => None,
                };
                let tv = mk((r.clone(), Ty_::Tdynamic(result_shadow)));
                let ty_err1: Option<typing_error::T> = t_utils::supports_dynamic(
                    env,
                    tkey.clone(),
                    Some(reasons_callback::unify_error_at(expr_pos.clone())),
                );
                let idx_err_res = mk_ty_mismatch_res(tkey.clone(), tv.clone(), &ty_err1);
                let ty_err2: Option<typing_error::T> = t_utils::supports_dynamic(
                    env,
                    ty2.clone(),
                    Some(reasons_callback::unify_error_at(expr_pos.clone())),
                );
                let val_err_res = mk_ty_mismatch_res(tkey.clone(), tv.clone(), &ty_err2);
                if let Some(e) = option_merge(ty_err1, ty_err2, typing_error::both) {
                    typing_error_utils::add_typing_error(&e, env)
                }
                (tv.clone(), Ok(tv), idx_err_res, val_err_res)
            };
            match get_node(&ety1_) {
                Ty_::Tclass(id, _, argl) if id.1 == sn::collections::VECTOR => {
                    let cn = &id.1;
                    let tv = match &argl[..] {
                        [tv] => maybe_pessimise_type(env, tv.clone()),
                        _ => {
                            arity_error(id);
                            err_witness(env, expr_pos)
                        }
                    };
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv);
                    let nast::Expr(_, p, _) = key;
                    let tk = make_type::int(reason::idx_vector(p.clone()));
                    let (ty_err1, idx_err) = type_index(
                        false, // read
                        env,
                        expr_pos,
                        tkey.clone(),
                        tk,
                        Enforcement::Enforced,
                        reason::index_class(cn),
                    );
                    let ty_err2: Option<typing_error::T> = typing_ops::sub_type(None, 
                        expr_pos.clone(),
                        ur.clone(),
                        env,
                        ty2.clone(),
                        tv.clone(),
                        callback::unify_error(),
                    );
                    let err_res = mk_ty_mismatch_res(ty2.clone(), tv, &ty_err2);
                    if let Some(e) = option_merge(ty_err1, ty_err2, typing_error::both) {
                        typing_error_utils::add_typing_error(&e, env)
                    }
                    (ety1.clone(), Ok(ety1.clone()), idx_err, err_res)
                }
                Ty_::Tclass(id, e, argl) if id.1 == sn::collections::VEC => {
                    let cn = &id.1;
                    let tv = match &argl[..] {
                        [tv] => tv.clone(),
                        _ => {
                            arity_error(id);
                            err_witness(env, expr_pos)
                        }
                    };
                    let nast::Expr(_, p, _) = key;
                    let tk = make_type::int(reason::idx_vector(p.clone()));
                    let (ty_err1, idx_err) = type_index(
                        false, // read
                        env,
                        expr_pos,
                        tkey.clone(),
                        tk,
                        Enforcement::Enforced,
                        reason::index_class(cn),
                    );
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv);
                    let tv_ = typing_union::union(env, None, None, tv, ty2.clone());
                    let ty = mk((r.clone(), Ty_::Tclass(id.clone(), e.clone(), vec![tv_])));
                    if let Some(e) = &ty_err1 {
                        typing_error_utils::add_typing_error(e, env)
                    }
                    (ty.clone(), Ok(ty), idx_err, Ok(ty2.clone()))
                }
                Ty_::Tclass(id, _, argl) if id.1 == sn::collections::MAP => {
                    let cn = &id.1;
                    let idx_err1 =
                        check_arraykey_index_write(env, expr_pos, ety1.clone(), tkey.clone());
                    let (tk, tv) = match &argl[..] {
                        [tk, tv] => (tk.clone(), maybe_pessimise_type(env, tv.clone())),
                        _ => {
                            arity_error(id);
                            let ty = err_witness(env, expr_pos);
                            (ty.clone(), ty)
                        }
                    };
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv);
                    let (enforced, tk) = {
                        let nast::Expr(_, p, _) = key;
                        let ak_t = make_type::arraykey(reason::idx_vector(p.clone()));
                        let tk = maybe_pessimise_type(env, tk);
                        if t_utils::is_sub_type_for_union(env, &ak_t, &tk) {
                            // hhvm will enforce that the key is an arraykey, so if
                            // $x : Map<arraykey, t>, then it should be allowed to
                            // set $x[$d] = e where $d : dynamic. NB above, we don't need
                            // to check that tk <: arraykey, because the Map ensures that.
                            (Enforcement::Enforced, tk)
                        } else {
                            // It is unsound to allow $x[$d] = e if $x : Map<string, t>
                            // since the dynamic $d might be an int and hhvm wouldn't
                            // complain.
                            (Enforcement::Unenforced, tk)
                        }
                    };
                    let (ty_err1, idx_err2) = type_index(
                        false, // read
                        env,
                        expr_pos,
                        tkey.clone(),
                        tk,
                        enforced,
                        reason::index_class(cn),
                    );
                    let idx_err = match (&idx_err1, &idx_err2) {
                        (Err(_), _) => idx_err1,
                        _ => idx_err2,
                    };
                    let ty_err2: Option<typing_error::T> = typing_ops::sub_type(None, 
                        expr_pos.clone(),
                        ur.clone(),
                        env,
                        ty2.clone(),
                        tv.clone(),
                        callback::unify_error(),
                    );
                    let err_res = mk_ty_mismatch_res(ty2.clone(), tv, &ty_err2);
                    if let Some(e) = option_merge(ty_err1, ty_err2, typing_error::both) {
                        typing_error_utils::add_typing_error(&e, env)
                    }
                    (ety1.clone(), Ok(ety1.clone()), idx_err, err_res)
                }
                Ty_::Tclass(id, e, argl) if id.1 == sn::collections::DICT => {
                    let idx_err =
                        check_arraykey_index_write(env, expr_pos, ety1.clone(), tkey.clone());
                    let (tk, tv) = match &argl[..] {
                        [tk, tv] => (tk.clone(), tv.clone()),
                        _ => {
                            arity_error(id);
                            // `let (_env, ty) = err_witness env expr_pos`: the
                            // environment is dropped.
                            let ty = err_witness(&mut env.clone(), expr_pos);
                            (ty.clone(), ty)
                        }
                    };
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv);
                    let tk_ = {
                        let nast::Expr(_, p, _) = key;
                        let ak_t = make_type::arraykey(reason::idx_dict(p.clone()));
                        match idx_err {
                            Ok(_) => {
                                let tkey_new = typing_intersection::intersect(
                                    env,
                                    reason::idx_dict(p.clone()),
                                    tkey.clone(),
                                    ak_t,
                                );
                                typing_union::union(env, None, None, tk, tkey_new)
                            }
                            _ => typing_union::union(env, None, None, tk, tkey.clone()),
                        }
                    };
                    let tv_ = typing_union::union(env, None, None, tv, ty2.clone());
                    let ty = mk((
                        r.clone(),
                        Ty_::Tclass(id.clone(), e.clone(), vec![tk_, tv_]),
                    ));
                    (ty.clone(), Ok(ty), idx_err, Ok(ty2.clone()))
                }
                Ty_::Tclass((_, cn), _, _) if cn == sn::collections::KEYSET => {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Keyset_set {
                            pos: expr_pos.clone(),
                            decl_pos: reason::to_pos(&r),
                        }),
                        env,
                    );
                    (
                        ety1.clone(),
                        Err((ety1.clone(), make_type::nothing(reason::none()))),
                        Ok(tkey.clone()),
                        Ok(ty2.clone()),
                    )
                }
                Ty_::Tclass((_, cn), _, tys)
                    if cn == sn::collections::CONST_MAP || cn == sn::collections::IMM_MAP =>
                {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Const_mutation {
                            pos: expr_pos.clone(),
                            decl_pos: reason::to_pos(&r),
                            ty_name: lazy_print_error(env, &ety1),
                        }),
                        env,
                    );
                    let ty_expect = make_type::class_type(
                        reason::none(),
                        sn::collections::MAP.to_string(),
                        tys.clone(),
                    );
                    (
                        ety1.clone(),
                        Err((ety1.clone(), ty_expect)),
                        Ok(tkey.clone()),
                        Ok(ty2.clone()),
                    )
                }
                Ty_::Tclass((_, cn), _, tys)
                    if cn == sn::collections::CONST_VECTOR || cn == sn::collections::IMM_VECTOR =>
                {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Const_mutation {
                            pos: expr_pos.clone(),
                            decl_pos: reason::to_pos(&r),
                            ty_name: lazy_print_error(env, &ety1),
                        }),
                        env,
                    );
                    let ty_expect = make_type::class_type(
                        reason::none(),
                        sn::collections::VECTOR.to_string(),
                        tys.clone(),
                    );
                    let ety1 = maybe_make_supportdyn(r.clone(), env, supportdyn, ety1.clone());
                    (
                        ety1.clone(),
                        Err((ety1, ty_expect)),
                        Ok(tkey.clone()),
                        Ok(ty2.clone()),
                    )
                }
                Ty_::Tclass((_, cn), _, _)
                    if cn == sn::collections::ANY_ARRAY
                        && tast::is_under_dynamic_assumptions(env.checked) =>
                {
                    got_dynamic(env)
                }
                Ty_::Tclass((_, cn), _, _)
                    if cn == sn::collections::KEYED_CONTAINER
                        || cn == sn::collections::ANY_ARRAY
                        || cn == sn::collections::PAIR =>
                {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Const_mutation {
                            pos: expr_pos.clone(),
                            decl_pos: reason::to_pos(&r),
                            ty_name: lazy_print_error(env, &ety1),
                        }),
                        env,
                    );
                    let ty_expect = make_type::nothing(reason::none());
                    let ety1 = maybe_make_supportdyn(r.clone(), env, supportdyn, ety1.clone());
                    (
                        ety1.clone(),
                        Err((ety1, ty_expect)),
                        Ok(tkey.clone()),
                        Ok(ty2.clone()),
                    )
                }
                Ty_::TvecOrDict(tk, tv) => {
                    let idx_err =
                        check_arraykey_index_write(env, expr_pos, ety1.clone(), tkey.clone());
                    let tk_ = typing_union::union(env, None, None, tk.clone(), tkey.clone());
                    let tv = maybe_make_supportdyn(r.clone(), env, supportdyn, tv.clone());
                    let tv_ = typing_union::union(env, None, None, tv, ty2.clone());
                    let ty = mk((r.clone(), Ty_::TvecOrDict(tk_, tv_)));
                    (ty.clone(), Ok(ty), idx_err, Ok(ty2.clone()))
                }
                Ty_::Tvar(_) if t_utils::is_tyvar_error(env, &ety1) => {
                    let ty = env_::fresh_type_error(env, expr_pos.clone());
                    let ty = maybe_make_supportdyn(r.clone(), env, supportdyn, ty);
                    (ty.clone(), Ok(ty), Ok(tkey.clone()), Ok(ty2.clone()))
                }
                Ty_::Tdynamic(_) => got_dynamic(env),
                Ty_::Tany(_) => (
                    ety1.clone(),
                    Ok(ety1.clone()),
                    Ok(tkey.clone()),
                    Ok(ty2.clone()),
                ),
                Ty_::Tprim(Tprim::Tnull) if tast::is_under_dynamic_assumptions(env.checked) => {
                    got_dynamic(env)
                }
                Ty_::Tclass((_, id), _, _) if id == C_STRING => {
                    let nast::Expr(_, p, _) = key;
                    let tk = make_type::int(reason::idx((p.clone(), r.clone())));
                    let tv = make_type::string(reason::witness(expr_pos.clone()));
                    let (ty_err1, idx_err) = type_index(
                        false, // read
                        env,
                        expr_pos,
                        tkey.clone(),
                        tk,
                        Enforcement::Enforced,
                        reason::index_array(),
                    );
                    let tv_ = maybe_pessimise_type(env, tv.clone());
                    let ty_err2: Option<typing_error::T> = typing_ops::sub_type(None, 
                        expr_pos.clone(),
                        ur.clone(),
                        env,
                        ty2.clone(),
                        tv_,
                        callback::unify_error(),
                    );
                    let err_res = mk_ty_mismatch_res(ty2.clone(), tv, &ty_err2);
                    if let Some(e) = option_merge(ty_err1, ty_err2, typing_error::both) {
                        typing_error_utils::add_typing_error(&e, env)
                    }
                    (ety1.clone(), Ok(ety1.clone()), idx_err, err_res)
                }
                // TODO T201398626 T201398652
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: TupleExtra::Tvariadic(_),
                }) if t_optional.is_empty() => {
                    let fail = |env: &Env, key_err: TyMismatchRes, reason: Ureason| {
                        let nast::Expr(_, p, _) = key;
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Generic_unify {
                                pos: p.clone(),
                                msg: reason::string_of_ureason(&reason),
                            }),
                            env,
                        );
                        (ety1.clone(), Ok(ety1.clone()), key_err, Ok(ty2.clone()))
                    };
                    match key {
                        nast::Expr(_, _, nast::Expr_::Int(n)) => {
                            let idx = int_of_string_opt(n);
                            match idx.map(|idx| split_n(t_required, idx)) {
                                Some((tyl_, [_, tyl__ @ ..])) => {
                                    let mut tyl = tyl_.to_vec();
                                    tyl.push(ty2.clone());
                                    tyl.extend(tyl__.iter().cloned());
                                    let ty = make_type::tuple(r.clone(), tyl);
                                    let ty = maybe_make_supportdyn(r.clone(), env, supportdyn, ty);
                                    (ty, Ok(ety1.clone()), Ok(tkey.clone()), Ok(ty2.clone()))
                                }
                                _ => fail(env, Ok(tkey.clone()), reason::index_tuple()),
                            }
                        }
                        _ => fail(
                            env,
                            Err((tkey.clone(), make_type::int(reason::none()))),
                            Ureason::URtupleAccess,
                        ),
                    }
                }
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: shape_kind,
                    fields: fdm,
                })) => {
                    // OCaml computes `~with_error` (and the environment it
                    // gives) before the call; the callback goes on with the
                    // environment of before, which is also the one that
                    // `do_with_field_expr` reports a bad field name in.
                    let saved = env.clone();
                    let with_error = {
                        let ety1 = maybe_make_supportdyn(r.clone(), env, supportdyn, ety1.clone());
                        (
                            Some(env.clone()),
                            (ety1.clone(), Ok(ety1), Ok(tkey.clone()), Ok(ty2.clone())),
                        )
                    };
                    *env = saved;
                    let env_for_field = env.clone();
                    let (env_opt, res) = typing_shapes::do_with_field_expr(
                        &env_for_field,
                        key,
                        with_error,
                        |field: TshapeFieldName| {
                            let fdm = if supportdyn {
                                let f =
                                    |env: &mut Env,
                                     _name: &t_shape_map::Key,
                                     ShapeFieldType {
                                         optional: sft_optional,
                                         ty: sft_ty,
                                     }: ShapeFieldType| {
                                        let sft_ty: Ty =
                                            t_utils::make_supportdyn(r.clone(), env, sft_ty);
                                        ShapeFieldType {
                                            optional: sft_optional,
                                            ty: sft_ty,
                                        }
                                    };
                                t_shape_map::map_env(f, env, fdm.clone())
                            } else {
                                fdm.clone()
                            };
                            // `TShapeMap.add field ... fdm`: the binding, key
                            // included (its position), replaces any other one
                            // for the same field (`BTreeMap::insert` would keep
                            // the old key).
                            let mut fdm_ = fdm;
                            let field = t_shape_map::TShapeField(field);
                            fdm_.remove(&field);
                            fdm_.insert(
                                field,
                                ShapeFieldType {
                                    optional: false,
                                    ty: ty2.clone(),
                                },
                            );
                            let ty = mk((
                                r.clone(),
                                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                                    origin: TypeOrigin::MissingOrigin,
                                    unknown_value: shape_kind.clone(),
                                    fields: fdm_,
                                })),
                            ));
                            (
                                None,
                                (ty.clone(), Ok(ty), Ok(tkey.clone()), Ok(ty2.clone())),
                            )
                        },
                    );
                    if let Some(env_) = env_opt {
                        *env = env_
                    }
                    res
                }
                Ty_::Tnewtype(cid, _, _bound) if cid == sn::classes::SUPPORT_DYN => {
                    // We must be under_dynamic_assumptions because
                    // apply_rules_with_index_value_ty_mismatches otherwise descends into the newtype.
                    // In this case we just accept the assignment because it's as though
                    // we applied an implicit upcast to dynamic
                    (
                        ety1.clone(),
                        Ok(ety1.clone()),
                        Ok(tkey.clone()),
                        Ok(ty2.clone()),
                    )
                }
                Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                    // If a type parameter may also provide this field, the write still
                    // refines the local value: the new rightmost field shadows the parameter's
                    // field. We do not require the written type to be compatible with every
                    // instantiation of the parameter here. If the refined value is later used
                    // where the original splat type is expected, shape-splat subtyping performs
                    // that check and reports any incompatibility.
                    //
                    // (`~with_error` as in the case of a simple shape.)
                    let saved = env.clone();
                    let with_error = {
                        let ety1 = maybe_make_supportdyn(r.clone(), env, supportdyn, ety1.clone());
                        (
                            Some(env.clone()),
                            (ety1.clone(), Ok(ety1), Ok(tkey.clone()), Ok(ty2.clone())),
                        )
                    };
                    *env = saved;
                    let env_for_field = env.clone();
                    let (env_opt, res) = typing_shapes::do_with_field_expr(
                        &env_for_field,
                        key,
                        with_error,
                        |field: TshapeFieldName| {
                            let (_err, ty): (Option<typing_error::T>, Ty) =
                                typing_shape_normalize::set_rightmost_field(
                                    ss_elems,
                                    field,
                                    ShapeFieldType {
                                        optional: false,
                                        ty: ty2.clone(),
                                    },
                                    supportdyn, // pessimize_existing
                                    r.clone(),  // reason
                                    env,
                                );
                            (
                                None,
                                (ty.clone(), Ok(ty), Ok(tkey.clone()), Ok(ty2.clone())),
                            )
                        },
                    );
                    if let Some(env_) = env_opt {
                        *env = env_
                    }
                    res
                }
                Ty_::Toption(_)
                | Ty_::Tnonnull
                | Ty_::Tprim(_)
                | Ty_::Tunion(_)
                | Ty_::Tintersection(_)
                | Ty_::Tgeneric(_)
                | Ty_::Tnewtype(_, _, _)
                | Ty_::Tdependent(_, _)
                | Ty_::Tvar(_)
                | Ty_::Tfun(_)
                | Ty_::Tclass(_, _, _)
                | Ty_::Taccess(_)
                | Ty_::Tlabel(_)
                | Ty_::Ttuple(_)
                | Ty_::Tneg(_)
                | Ty_::TclassPtr(_) => {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Array_access {
                            ctxt: ReadOrWrite::write,
                            pos: expr_pos.clone(),
                            decl_pos: reason::to_pos(&r),
                            ty_name: lazy_print_error(env, &ety1),
                        }),
                        env,
                    );
                    let ty_nothing = make_type::nothing(reason::none());
                    let ety1 = maybe_make_supportdyn(r.clone(), env, supportdyn, ety1.clone());
                    (
                        ety1.clone(),
                        Err((ety1, ty_nothing.clone())),
                        Ok(tkey.clone()),
                        Err((ty2.clone(), ty_nothing)),
                    )
                } // The OCaml match is on the node of `ety1` minus the
                  // constructors above; `Tany` and `Tdynamic` are handled above.
            }
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_of_string_opt_is_ocamls() {
        assert_eq!(int_of_string_opt("0"), Some(0));
        assert_eq!(int_of_string_opt("12"), Some(12));
        assert_eq!(int_of_string_opt("-1"), Some(-1));
        // Leading zeros are decimal, not octal as in Hack.
        assert_eq!(int_of_string_opt("017"), Some(17));
        assert_eq!(int_of_string_opt("0x1F"), Some(31));
        assert_eq!(int_of_string_opt("0b101"), Some(5));
        assert_eq!(int_of_string_opt("0o17"), Some(15));
        assert_eq!(int_of_string_opt("1_000"), Some(1000));
        assert_eq!(int_of_string_opt(""), None);
        assert_eq!(int_of_string_opt("1.5"), None);
        assert_eq!(int_of_string_opt("4611686018427387904"), None);
    }

    #[test]
    fn split_n_is_cores() {
        let ty = |p| mk((reason::none(), Ty_::Tprim(p)));
        let l = vec![ty(Tprim::Tint), ty(Tprim::Tbool), ty(Tprim::Tfloat)];
        assert_eq!(split_n(&l, 1).0.len(), 1);
        assert_eq!(split_n(&l, 1).1.len(), 2);
        // A negative index splits before the first element
        assert_eq!(split_n(&l, -1).0.len(), 0);
        assert_eq!(split_n(&l, -1).1.len(), 3);
        // An index past the end keeps everything on the left
        assert_eq!(split_n(&l, 5).0.len(), 3);
        assert_eq!(split_n(&l, 5).1.len(), 0);
    }
}
