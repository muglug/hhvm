// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 13101-13573): module `Assign`.
//! See `hh/PORTING.md`.
//!
//! The functions return `(te, ty, ty_mismatch_opt)` where OCaml returns
//! `(env, te, ty, ty_mismatch_opt)`. `?expr_for_string_check` is the first
//! parameter, `Option<&nast::Expr>`.

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::pos_or_decl;
use crate::tast;
use crate::typing::class_get_expr;
use crate::typing::class_id;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_array_access;
use crate::typing_class_pointers;
use crate::typing_coercion;
use crate::typing_defs::*;
use crate::typing_defs_constraints::*;
use crate::typing_destructure;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::callback;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_helpers;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module Type = Typing_ops
use crate::typing_ops;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::Blame;
use crate::typing_reason::BlameSource;
use crate::typing_reason::Ureason;
use crate::typing_solver;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;

/// `Option.merge` (Core)
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, None) => None,
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

fn add_typing_error_opt(ty_err_opt: &Option<typing_error::T>, env: &Env) {
    if let Some(err) = ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}

pub(crate) fn assign_simple(
    pos: &Pos,
    ur: Ureason,
    env: &mut Env,
    e1: &nast::Expr,
    ty2: Ty,
) -> (tast::Expr, Ty, Option<(Ty, Ty)>) {
    let (te1, ty1) = expr::lvalue(env, e1);
    // Since we return the typed expression _and_ the type, we have to first
    // modify the types reason if extended-reasons is set and do the same
    // with typed expression's annotation since these types are not necessarily
    // the same for certain special functions
    let ty1 = env::update_reason(env, ty1, |lval| {
        reason::flow_assign(get_reason(&ty2).clone(), lval)
    });
    let te1 = {
        let aast::Expr(ty, pos, e) = te1;
        let ty = env::update_reason(env, ty, |lval| {
            reason::flow_assign(get_reason(&ty2).clone(), lval)
        });
        aast::Expr(ty, pos, e)
    };
    let ty_err_opt = typing_coercion::coerce_type(
        None,
        None,
        None,
        pos.clone(),
        ur,
        env,
        ty2.clone(),
        ty1.clone(),
        Enforcement::Unenforced,
        callback::unify_error(),
    );
    add_typing_error_opt(&ty_err_opt, env);
    let ty_mismatch = mk_ty_mismatch_opt(ty2.clone(), ty1, ty_err_opt.as_ref());
    (te1, ty2, ty_mismatch)
}

pub(crate) fn assign_with_subtype_err_(
    expr_for_string_check: Option<&nast::Expr>,
    p: &Pos,
    ur: Ureason,
    env: &mut Env,
    e1: &nast::Expr,
    pos2: &Pos,
    ty2: Ty,
) -> (tast::Expr, Ty, Option<(Ty, Ty)>) {
    match e1 {
        aast::Expr(_, _, aast::Expr_::Hole(hole)) => {
            let (e, _, _, _) = &**hole;
            assign_with_subtype_err_(None, p, ur, env, e, pos2, ty2)
        }
        _ => {
            match e1 {
                aast::Expr(_, _, aast::Expr_::Lvar(lid)) => {
                    let aast::Lid(_, x) = &**lid;
                    env::forget_prefixed_members(
                        env,
                        x,
                        Blame::Blame(p.clone(), BlameSource::BSassignment),
                    )
                }
                // If we ever extend fake members from $x->a to more complicated lvalues
                // such as $x->a->b, we would need to call forget_prefixed_members on
                // other lvalues as well.
                aast::Expr(_, _, aast::Expr_::ObjGet(og))
                    if matches!(&og.1, aast::Expr(_, _, aast::Expr_::Id(_))) =>
                {
                    let property = match &og.1 {
                        aast::Expr(_, _, aast::Expr_::Id(id)) => &id.1,
                        _ => unreachable!(),
                    };
                    env::forget_suffixed_members(
                        env,
                        property,
                        Blame::Blame(p.clone(), BlameSource::BSassignment),
                    )
                }
                _ => {}
            }
            match e1 {
                aast::Expr(_, p1, aast::Expr_::Lvar(id)) => {
                    let aast::Lid(_, x) = &**id;
                    // Since the lvar will be given the type [ty2] we need to update it
                    // to indicate it flows _into_ an local
                    let ty = env::update_reason(env, ty2, |rhs| {
                        reason::flow_assign(rhs, reason::witness(p1.clone()))
                    });
                    set_valid_rvalue(None, p.clone(), env, x.clone(), None, ty.clone());
                    let (te, ty) =
                        make_result(env, p1.clone(), aast::Expr_::Lvar(id.clone()), ty);
                    (te, ty, None)
                }
                aast::Expr(_, p1, aast::Expr_::Lplaceholder(id)) => {
                    let placeholder_ty = {
                        let ty = make_type::void(reason::placeholder(p.clone()));
                        env::update_reason(env, ty, |lval| {
                            reason::flow_assign(get_reason(&ty2).clone(), lval)
                        })
                    };
                    let (te, ty) = make_result(
                        env,
                        p1.clone(),
                        aast::Expr_::Lplaceholder(id.clone()),
                        placeholder_ty,
                    );
                    (te, ty, None)
                }
                aast::Expr(_, p1, aast::Expr_::List(el)) => {
                    // Generate fresh types for each lhs list element, then subtype against
                    // rhs type. If original type was generated from an error, propagate this to
                    // avoid cascading errors.
                    let is_error_type = tutils::is_tyvar_error(env, &ty2);
                    env::open_tyvars(env, p.clone());
                    let tyl: Vec<Ty> = el
                        .iter()
                        .map(|aast::Expr(_, p, _e)| {
                            if is_error_type {
                                env::fresh_type_error(env, p.clone())
                            } else {
                                env::fresh_type(env, p.clone())
                            }
                        })
                        .collect();
                    let tyl: Vec<Ty> = tyl
                        .into_iter()
                        .map(|ty| {
                            env::update_reason(env, ty, |lval| {
                                reason::flow_assign(get_reason(&ty2).clone(), lval)
                            })
                        })
                        .collect();
                    let destructure_ty =
                        make_type::list_destructure(reason::destructure(p1.clone()), tyl.clone());
                    env::set_tyvar_variance_i(env, None, None, &destructure_ty);
                    let lty2 = InternalType::LoclType(ty2.clone());
                    let assign_accumulate =
                        |env: &mut Env,
                         (tel, errs): &mut (Vec<tast::Expr>, Vec<Option<(Ty, Ty)>>),
                         lvalue: &nast::Expr,
                         ty2: Ty| {
                            let (te, _, err_opt) = assign(None, p, env, lvalue, pos2, ty2);
                            // `te :: tel` and `err_opt :: errs`: kept in order
                            // here, so nothing is reversed afterwards.
                            tel.push(te);
                            errs.push(err_opt);
                        };
                    let type_list_elem = |env: &mut Env| {
                        // `List.fold2_exn el tyl`: the lists have the same
                        // length by construction.
                        let mut acc = (vec![], vec![]);
                        for (lvalue, ty2) in el.iter().zip(tyl.iter()) {
                            assign_accumulate(env, &mut acc, lvalue, ty2.clone());
                        }
                        let (tel, subtype_errs) = acc;
                        let (te, ty) =
                            make_result(env, p1.clone(), aast::Expr_::List(tel), ty2.clone());
                        (te, ty, subtype_errs)
                    };

                    // Here we attempt to unify the type of the rhs we assigning with
                    // a number of fresh tyvars corresponding to the arity of the lhs `list`
                    //
                    // if we have a failure in subtyping the fresh tyvars in `destructure_ty`,
                    // we have a rhs which cannot be destructured to the variables on the lhs;
                    // e.g. `list($x,$y) = 2`  or `list($x,$y) = tuple (1,2,3)`
                    //
                    // in the error case, we add a `Hole` with expected type `nothing` since
                    // there is no type we can suggest was expected
                    //
                    // in the ok case were the destrucutring succeeded, the fresh vars
                    // now have types so we can subtype each element, accumulate the errors
                    // and pack back into the rhs structure as our expected type
                    let ty_err1 = typing_ops::sub_type_i(
                        None,
                        p.clone(),
                        ur.clone(),
                        env,
                        lty2,
                        destructure_ty,
                        callback::unify_error(),
                    );
                    let ty_err2 = typing_solver::close_tyvars_and_solve(env);
                    let ty_err_opt = option_merge(ty_err1, ty_err2, typing_error::both);
                    add_typing_error_opt(&ty_err_opt, env);
                    match ty_err_opt {
                        None => {
                            let (te, ty, subty_errs) = type_list_elem(env);
                            let err_opt = if subty_errs.iter().all(Option::is_none) {
                                None
                            } else {
                                Some((ty2.clone(), pack_errs(pos2, &ty2, &(subty_errs, None))))
                            };
                            (te, ty, err_opt)
                        }
                        Some(_) => {
                            let (te, ty, _) = type_list_elem(env);
                            let nothing = make_type::nothing(reason::solve_fail(
                                pos_or_decl::of_raw_pos(pos2.clone()),
                            ));
                            (te, ty, Some((ty2, nothing)))
                        }
                    }
                }
                aast::Expr(_, pobj, aast::Expr_::ObjGet(og))
                    if matches!(&og.1, aast::Expr(_, _, aast::Expr_::Id(_))) =>
                {
                    let (obj, member, nullflavor, prop_or_method) = &**og;
                    let (pm, m) = match member {
                        aast::Expr(_, pm, aast::Expr_::Id(m)) => (pm, &**m),
                        _ => unreachable!(),
                    };
                    let member_name = &m.1;
                    let lenv = env.lenv.clone();
                    let nullsafe = match nullflavor {
                        aast::OperatorNullFlavor::Regular => None,
                        aast::OperatorNullFlavor::Nullsafe => Some(pobj.clone()),
                    };
                    let (tobj, obj_ty) = expr::expr(
                        None,
                        &expr::context::T {
                            accept_using_var: true,
                            ..expr::context::default()
                        },
                        env,
                        obj,
                    );
                    might_throw(p, env);
                    let aast::Expr(_, p1, _) = obj;
                    let (
                        ty_err_opt,
                        (declared_ty, _tal),
                        lval_ty_mismatch_opt,
                        rval_ty_mismatch_opt,
                    ) = crate::typing_object_get::obj_get_with_mismatches(
                        p1.clone(),
                        false,
                        nullsafe,
                        Some((pos2.clone(), ur.clone(), ty2.clone())),
                        &[],
                        &aast::ClassId_::CIexpr(e1.clone()),
                        m,
                        callback::unify_error(),
                        None,
                        env,
                        obj_ty,
                    );
                    add_typing_error_opt(&ty_err_opt, env);
                    if let Some(e) = expr_for_string_check {
                        typing_class_pointers::check_string_coercion_point(env, e, &declared_ty)
                    }
                    let inner_te = typing_helpers::make_simplify_typed_expr(
                        env,
                        pm.clone(),
                        declared_ty.clone(),
                        aast::Expr_::Id(Box::new(m.clone())),
                    );
                    let te1 = typing_helpers::make_simplify_typed_expr(
                        env,
                        pobj.clone(),
                        declared_ty.clone(),
                        aast::Expr_::ObjGet(Box::new((
                            hole_on_ty_mismatch(tobj, lval_ty_mismatch_opt),
                            inner_te,
                            *nullflavor,
                            *prop_or_method,
                        ))),
                    );
                    env.lenv = lenv;
                    match obj {
                        aast::Expr(_, _, aast::Expr_::This)
                        | aast::Expr(_, _, aast::Expr_::Lvar(_)) => {
                            let local = env::fake_members::make(env, obj, member_name, p.clone());
                            let refined_ty = inter::intersect(
                                env,
                                reason::witness(p.clone()),
                                declared_ty,
                                ty2.clone(),
                            );
                            set_valid_rvalue(None, p.clone(), env, local, None, refined_ty);
                            (te1, ty2, rval_ty_mismatch_opt)
                        }
                        _ => (te1, ty2, rval_ty_mismatch_opt),
                    }
                }
                aast::Expr(_, _, aast::Expr_::ClassGet(cg)) => {
                    let (cid, pstr, _) = &**cg;
                    let aast::ClassId(_, _, x) = cid;
                    let (_pos_member, y) = pstr;
                    let lenv = env.lenv.clone();
                    // `let no_fakes = LEnv.env_with_empty_fakes env`
                    lenv::env_with_empty_fakes(env);
                    let (te1, _) = expr::lvalue(env, e1);
                    env.lenv = lenv;
                    let ety2 = env::expand_type(env, ty2.clone());
                    // This defers the coercion check to class_get, which looks up the appropriate target type
                    let (_tal, _, cty) = class_id::class_expr(
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        env,
                        &[],
                        cid,
                    );
                    might_throw(p, env);
                    let ((declared_ty, _), rval_err_opt) = class_get_expr::class_get_err(
                        false,
                        false,
                        None,
                        Some((p.clone(), ur.clone(), ety2)),
                        None,
                        None,
                        None,
                        env,
                        cty,
                        pstr,
                        cid,
                    );
                    let local = env::fake_members::make_static(env, x, y, p.clone());
                    let refined_ty = inter::intersect(
                        env,
                        reason::witness(p.clone()),
                        declared_ty,
                        ty2.clone(),
                    );
                    set_valid_rvalue(None, p.clone(), env, local, None, refined_ty);
                    (te1, ty2, rval_err_opt)
                }
                aast::Expr(_, _, aast::Expr_::ObjGet(_)) => {
                    let lenv = env.lenv.clone();
                    // `let no_fakes = LEnv.env_with_empty_fakes env`
                    lenv::env_with_empty_fakes(env);
                    let (te1, real_type) = expr::lvalue(env, e1);
                    let exp_real_type = env::expand_type(env, real_type);
                    env.lenv = lenv;
                    let ty_err_opt = typing_coercion::coerce_type(
                        None,
                        None,
                        None,
                        p.clone(),
                        ur,
                        env,
                        ty2.clone(),
                        exp_real_type.clone(),
                        Enforcement::Unenforced,
                        callback::unify_error(),
                    );
                    add_typing_error_opt(&ty_err_opt, env);
                    let ty_mismatch =
                        mk_ty_mismatch_opt(ty2.clone(), exp_real_type, ty_err_opt.as_ref());
                    (te1, ty2, ty_mismatch)
                }
                aast::Expr(_, pos, aast::Expr_::ArrayGet(ag)) if ag.1.is_none() => {
                    let (e1, _) = &**ag;
                    let parent_lenv = env.lenv.clone();
                    let (te1, ty1) =
                        expr::update_array_type(false, pos, env, e1, valkind::T::Lvalue);
                    let aast::Expr(_, p1, _) = e1;
                    let (ty1_, arr_ty_mismatch_opt, val_ty_mismatch_opt) =
                        typing_array_access::assign_array_append(
                            p1.clone(),
                            p.clone(),
                            ur.clone(),
                            env,
                            ty1.clone(),
                            ty2.clone(),
                        );
                    let (ty1_is_hack_collection, ty_err_opt) = is_hack_collection(env, &ty1);
                    let te1 = if ty1_is_hack_collection {
                        hole_on_ty_mismatch(te1, arr_ty_mismatch_opt)
                    } else {
                        env.lenv = parent_lenv;
                        might_throw(p, env);
                        let (te1, ty, _) =
                            assign_with_subtype_err_(None, p, ur, env, e1, pos2, ty1_);
                        // Update the actual type to that after assignment
                        let arr_ty_mismatch_opt =
                            arr_ty_mismatch_opt.map(|(_, ty_expect)| (ty, ty_expect));
                        hole_on_ty_mismatch(te1, arr_ty_mismatch_opt)
                    };
                    let (te, ty) =
                        make_result(env, pos.clone(), aast::Expr_::ArrayGet(Box::new((te1, None))), ty2);
                    add_typing_error_opt(&ty_err_opt, env);
                    (te, ty, val_ty_mismatch_opt)
                }
                aast::Expr(_, pos, aast::Expr_::ArrayGet(ag)) => {
                    let (e1, Some(e)) = &**ag else {
                        unreachable!("`Array_get (e1, None)` is the case above")
                    };
                    let (te, ty) = expr::expr(None, &expr::context::default(), env, e);
                    let ty = typing_class_pointers::coerce_to_name(
                        env.genv.tcopt.tco_class_pointer_array_write_keys,
                        env,
                        ty,
                    );
                    let parent_lenv = env.lenv.clone();
                    let (te1, ty1) =
                        expr::update_array_type(false, pos, env, e1, valkind::T::Lvalue);
                    might_throw(p, env);
                    let aast::Expr(_, p1, _) = e1;
                    let aast::Expr(_, index_pos, _) = e;
                    let (ty1_, arr_ty_mismatch_opt, key_ty_mismatch_opt, val_ty_mismatch_opt) =
                        if env.genv.tcopt.tco_constraint_array_index_assign {
                            let val_ty = env::fresh_type_invariant(env, p.clone());
                            let ty_err_opt = sub_type::sub_type_i(
                                env,
                                None,
                                InternalType::LoclType(ty1.clone()),
                                InternalType::ConstraintType(mk_constraint_type((
                                    reason::witness(p.clone()),
                                    ConstraintType_::TcanIndexAssign(CanIndexAssign {
                                        key: ty.clone(),
                                        write: ty2.clone(),
                                        val: val_ty.clone(),
                                        index_expr: e.clone(),
                                        expr_pos: p.clone(),
                                        array_pos: p1.clone(),
                                        index_pos: index_pos.clone(),
                                        write_pos: pos2.clone(),
                                    }),
                                ))),
                                Some(reasons_callback::unify_error_at(p.clone())),
                            );
                            add_typing_error_opt(&ty_err_opt, env);
                            (
                                if ty_err_opt.is_none() {
                                    val_ty
                                } else {
                                    ty1.clone()
                                },
                                None,
                                None,
                                None,
                            )
                        } else {
                            typing_array_access::assign_array_get(
                                p1.clone(),
                                p.clone(),
                                ur.clone(),
                                env,
                                ty1.clone(),
                                e,
                                ty,
                                ty2.clone(),
                            )
                        };
                    let (ty1_is_hack_collection, ty_err_opt) = is_hack_collection(env, &ty1);
                    let te1 = if ty1_is_hack_collection {
                        hole_on_ty_mismatch(te1, arr_ty_mismatch_opt)
                    } else {
                        env.lenv = parent_lenv;
                        might_throw(p, env);
                        let (te1, ty, _) =
                            assign_with_subtype_err_(None, p, ur, env, e1, pos2, ty1_);
                        // Update the actual type to that after assignment
                        let arr_ty_mismatch_opt =
                            arr_ty_mismatch_opt.map(|(_, ty_expect)| (ty, ty_expect));
                        hole_on_ty_mismatch(te1, arr_ty_mismatch_opt)
                    };
                    add_typing_error_opt(&ty_err_opt, env);
                    (
                        aast::Expr(
                            ty2.clone(),
                            pos.clone(),
                            aast::Expr_::ArrayGet(Box::new((
                                te1,
                                Some(hole_on_ty_mismatch(te, key_ty_mismatch_opt)),
                            ))),
                        ),
                        ty2,
                        val_ty_mismatch_opt,
                    )
                }
                aast::Expr(_, pos, aast::Expr_::ReadonlyExpr(e)) => {
                    let (te1, ty, err) = assign_with_subtype_err_(None, pos, ur, env, e, pos2, ty2);
                    (
                        aast::Expr(ty.clone(), pos.clone(), aast::Expr_::ReadonlyExpr(Box::new(te1))),
                        ty,
                        err,
                    )
                }
                aast::Expr(_, pos1, aast::Expr_::DestructureShape(ds)) => {
                    let (te, ty) =
                        typing_destructure::shape(p.clone(), pos1.clone(), env, ds, ty2);
                    (te, ty, None)
                }
                aast::Expr(_, pos1, aast::Expr_::DestructureTuple(dt)) => {
                    let (te, ty) =
                        typing_destructure::tuple(p.clone(), pos1.clone(), env, dt, ty2);
                    (te, ty, None)
                }
                _ => assign_simple(p, ur, env, e1, ty2),
            }
        }
    }
}

/// Deal with assignment of a value of type ty2 to lvalue e1
pub fn assign(
    expr_for_string_check: Option<&nast::Expr>,
    p: &Pos,
    env: &mut Env,
    e1: &nast::Expr,
    pos2: &Pos,
    ty2: Ty,
) -> (tast::Expr, Ty, Option<(Ty, Ty)>) {
    assign_with_subtype_err_(
        expr_for_string_check,
        p,
        Ureason::URassign,
        env,
        e1,
        pos2,
        ty2,
    )
}

pub fn assign_(
    expr_for_string_check: Option<&nast::Expr>,
    p: &Pos,
    ur: Ureason,
    env: &mut Env,
    e1: &nast::Expr,
    pos2: &Pos,
    ty2: Ty,
) -> (tast::Expr, Ty) {
    let (te, ty, _err) =
        assign_with_subtype_err_(expr_for_string_check, p, ur, env, e1, pos2, ty2);
    (te, ty)
}
