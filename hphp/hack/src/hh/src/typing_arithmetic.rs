// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_arithmetic.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Uop;
use oxidized::error_codes::Typing as ErrorCode;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::naming_special_names as sn;
use crate::tast;
use crate::typing_argument;
use crate::typing_coercion;
use crate::typing_defs;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
use crate::typing_expand;
use crate::typing_helpers;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::ArgPosition;
use crate::typing_reason::Ureason;
use crate::typing_solver;
use crate::typing_subtype;
use crate::typing_union;
use crate::typing_utils;

/// `Reason.to_string` gives the `(Pos_or_decl.t * string) list` that is a
/// `Pos_or_decl.t Message.t list`.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

fn is_float(env: &Env, t: &Ty) -> bool {
    let (r, e) = typing_solver::is_sub_type(env, t, &make_type::float(reason::none()));
    if let Some(e) = &e {
        typing_error_utils::add_typing_error(e, env)
    }
    r
}

fn is_int(env: &Env, t: &Ty) -> bool {
    let (r, e) = typing_solver::is_sub_type(env, t, &make_type::int(reason::none()));
    if let Some(e) = &e {
        typing_error_utils::add_typing_error(e, env)
    }
    r
}

/// [check_like_num p_exp p env ty] ensures that [ty] is a subtype of num or ~num.
/// In the former case, it returns false and the type, in the latter, it returns
/// true, and the type with the ~ removed. If it is not a subtype of either, the
/// error generated refers to the attempt to make [ty] <: num. If there were errors
/// in both cases, we return the errors from the non ~ case.
fn check_like_num(
    err: Option<typing_error::callback::T>,
    p_exp: Pos,
    p: Pos,
    env: &mut Env,
    ty: Ty,
) -> (Option<(Ty, Ty)>, bool, Ty) {
    let err = match err {
        None => typing_error::callback::math_invalid_argument(),
        Some(err) => err,
    };
    let num_ty = make_type::num(reason::arith(p_exp));
    typing_coercion::coerce_type_like_strip(p, Ureason::URnone, env, ty, num_ty, err)
}

/// [expand_type_and_narrow_to_numeric ~allow_nothing env p ty] forces the
/// solving of [ty] to a numeric type, based on its lower bounds. If allow_nothing
/// is set, then it is allowed to return nothing when [ty] doesn't have numeric.
/// Otherwise the default type of int will be solved to.
fn expand_type_and_narrow_to_numeric(
    allow_nothing: bool,
    env: &mut Env,
    p: Pos,
    ty: Ty,
) -> (Option<typing_error::T>, Ty) {
    let widen_for_arithmetic = |_env: &mut Env, ty: Ty| match get_node(&ty) {
        Ty_::Tprim(Tprim::Tnum) | Ty_::Tprim(Tprim::Tfloat) | Ty_::Tprim(Tprim::Tint) => {
            Some(ty)
        }
        _ => None,
    };
    let default = make_type::int(reason::arith(p.clone()));
    typing_solver::expand_type_and_narrow(
        env,
        Some(default),
        Some(allow_nothing),
        Some(true),
        "a number",
        widen_for_arithmetic,
        p,
        ty,
    )
}

/// [expand_type_and_try_narrow_to_float env p ty] tries to solve [ty] to
/// float, based on its lower bounds. If it isn't solved to float, no narrowing
/// is done.
fn expand_type_and_try_narrow_to_float(
    env: &mut Env,
    p: Pos,
    ty: Ty,
) -> (Option<typing_error::T>, Ty) {
    let widen_for_arithmetic = |env: &mut Env, ty: Ty| match get_node(&ty) {
        Ty_::Tprim(Tprim::Tfloat) => Some(ty),
        Ty_::Tgeneric(_) => {
            let float = make_type::float(get_reason(&ty).clone());
            if typing_subtype::is_sub_type(env, &ty, &float) {
                Some(float)
            } else {
                None
            }
        }
        _ => None,
    };
    typing_solver::expand_type_and_narrow(
        env,
        None,
        Some(false),
        Some(false),
        "a number",
        widen_for_arithmetic,
        p,
        ty,
    )
}

/// [expand_type_and_try_narrow_to_nothing env p ty] tries to solve [ty] to
/// nothing, based on its lower bounds. If it isn't solved to nothing, no narrowing
/// is done.
fn expand_type_and_try_narrow_to_nothing(
    env: &mut Env,
    p: Pos,
    ty: Ty,
) -> (Option<typing_error::T>, Ty) {
    let widen_for_arithmetic = |_env: &mut Env, _ty: Ty| -> Option<Ty> { None };
    typing_solver::expand_type_and_narrow(
        env,
        None,
        Some(true),
        Some(false),
        "a number",
        widen_for_arithmetic,
        p,
        ty,
    )
}

fn hole_on_err(expr: tast::Expr, err_opt: Option<(Ty, Ty)>) -> tast::Expr {
    match err_opt {
        None => expr,
        Some((ty_have, ty_expect)) => {
            let pos = expr.1.clone();
            tast::make_typed_expr(
                pos,
                ty_have.clone(),
                aast::Expr_::Hole(Box::new((expr, ty_have, ty_expect, aast::HoleSource::Typing))),
            )
        }
    }
}

/// [check_for_float_result p env p1 ty1 p2 ty2] Tries to narrow ty1 or ty2 to float,
/// and if one can narrow, then the result is float. However, we don't want to do early
/// solving otherwise, before we've detected the other cases that don't require full solving.
fn check_for_float_result(
    p: &Pos,
    env: &mut Env,
    p1: &Pos,
    ty1: &Ty,
    p2: &Pos,
    ty2: &Ty,
) -> Option<Ty> {
    // The reasons are those of the types as they are given, not narrowed.
    let make_float_type = |use_ty1_reason: bool| {
        Some(make_type::float(if use_ty1_reason {
            reason::arith_ret_float((p.clone(), get_reason(ty1).clone(), ArgPosition::Afirst))
        } else {
            reason::arith_ret_float((p.clone(), get_reason(ty2).clone(), ArgPosition::Asecond))
        }))
    };
    let float_no_reason = make_type::float(reason::none());
    let (ty_err_opt, ty1) = expand_type_and_try_narrow_to_float(env, p1.clone(), ty1.clone());
    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    if typing_subtype::is_sub_type(env, &ty1, &float_no_reason) {
        make_float_type(true)
    } else {
        let (ty_err_opt, ty2) = expand_type_and_try_narrow_to_float(env, p2.clone(), ty2.clone());
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env)
        }
        if typing_subtype::is_sub_type(env, &ty2, &float_no_reason) {
            make_float_type(false)
        } else {
            None
        }
    }
}

pub fn binop(
    p: Pos,
    env: &mut Env,
    bop: Bop,
    p1: Pos,
    te1: tast::Expr,
    ty1: Ty,
    p2: Pos,
    te2: tast::Expr,
    ty2: Ty,
) -> (tast::Expr, Ty) {
    let make_result = |is_like: bool,
                       env: &mut Env,
                       te1: tast::Expr,
                       err_opt1: Option<(Ty, Ty)>,
                       te2: tast::Expr,
                       err_opt2: Option<(Ty, Ty)>,
                       ty: Ty| {
        let ty = if is_like {
            typing_union::union(env, None, None, ty, make_type::dynamic(reason::witness(p.clone())))
        } else {
            ty
        };
        let hte1 = hole_on_err(te1, err_opt1);
        let hte2 = hole_on_err(te2, err_opt2);
        let te = typing_helpers::make_simplify_typed_expr(
            env,
            p.clone(),
            ty.clone(),
            aast::Expr_::Binop(Box::new(aast::Binop {
                bop,
                lhs: hte1,
                rhs: hte2,
            })),
        );
        (te, ty)
    };
    let int_no_reason = make_type::int(reason::none());
    let num_no_reason = make_type::num(reason::none());
    let nothing_no_reason = make_type::nothing(reason::none());
    // The reasons are those of the types as they are given (the branches below
    // shadow `ty1` and `ty2`).
    let make_nothing_type = |use_ty1_reason: bool| {
        make_type::nothing(if use_ty1_reason {
            get_reason(&ty1).clone()
        } else {
            get_reason(&ty2).clone()
        })
    };
    // `let is_any = Typing_utils.is_any env`: with the environment as it is now.
    let env0 = env.clone();
    let is_any = |ty: &Ty| typing_utils::is_any(&env0, ty);
    let contains_any = is_any(&ty1) || is_any(&ty2);
    match bop {
        // Type of addition, subtraction and multiplication is essentially
        //    (int,int):int
        //  & (float,num):float
        //  & (num,float):float
        //  & (num,num):num
        Bop::Plus | Bop::Minus | Bop::Star if !contains_any => {
            let make_int_type = || make_type::int(reason::arith_ret_int(p.clone()));
            let make_num_type = |use_ty1_reason: bool| {
                let (r, apos) = if use_ty1_reason {
                    (get_reason(&ty1).clone(), ArgPosition::Afirst)
                } else {
                    (get_reason(&ty2).clone(), ArgPosition::Asecond)
                };
                make_type::num(reason::arith_ret_num((p.clone(), r, apos)))
            };
            let ty1_ = env::expand_type(env, ty1.clone());
            let ty2_ = env::expand_type(env, ty2.clone());
            let (ty1, ty2) = (ty1_, ty2_);
            let is_dynamic1 = typing_defs::is_dynamic(&ty1);
            let is_dynamic2 = typing_defs::is_dynamic(&ty2);
            let (ty_mismatch1, is_like1, ty1) = check_like_num(None, p.clone(), p1.clone(), env, ty1);
            let (ty_mismatch2, is_like2, ty2) = check_like_num(None, p.clone(), p2.clone(), env, ty2);
            // We'll compute the type ignoring whether one of the arguments was a like-type,
            // but we'll add the like type to the result type in the end if one was.
            let is_like = is_like1 || is_like2;
            let result_ty = match check_for_float_result(&p, env, &p1, &ty1, &p2, &ty2) {
                Some(ty) => ty,
                None => {
                    let is_int1 = typing_subtype::is_sub_type(env, &ty1, &int_no_reason);
                    let is_int2 = typing_subtype::is_sub_type(env, &ty2, &int_no_reason);
                    // If both of the arguments is definitely subtypes of int,
                    // then the return is int
                    if is_int1 && is_int2 {
                        make_int_type()
                    } else {
                        let is_num1 = typing_subtype::is_sub_type(env, &num_no_reason, &ty1);
                        let is_num2 = typing_subtype::is_sub_type(env, &num_no_reason, &ty2);
                        // If one argument is exactly num, then the return is num.
                        if is_num1 || is_num2 {
                            make_num_type(is_num1)
                        } else {
                            // Otherwise, at least one of the arguments is unsolved, and we need
                            // to take care to not solve too eagerly.
                            // Put the first one to try in ty1,
                            // and the second, if any in ty2. Keep the result of the previous
                            // check whether the second type was an int.
                            let ((ty1, p1, is_dynamic1), (ty2, p2, is_int2, is_dynamic2), swapped) =
                                if is_int1 {
                                    (
                                        (ty2, p2.clone(), is_dynamic2),
                                        (ty1, p1.clone(), is_int1, is_dynamic1),
                                        true,
                                    )
                                } else {
                                    (
                                        (ty1, p1.clone(), is_dynamic1),
                                        (ty2, p2.clone(), is_int2, is_dynamic2),
                                        false,
                                    )
                                };
                            let (ty_err_opt, ty1) =
                                expand_type_and_narrow_to_numeric(is_dynamic1, env, p1, ty1);
                            if let Some(ty_err) = &ty_err_opt {
                                typing_error_utils::add_typing_error(ty_err, env)
                            }
                            // If the first type solved a subtype of int, and the second was
                            // already int, then it is sound to return int.
                            let is_int1 = typing_subtype::is_sub_type(env, &ty1, &int_no_reason);
                            if is_int1 && is_int2 {
                                make_int_type()
                            } else {
                                // If the first type solved to exactly num, then we can just return that
                                let is_num1 =
                                    typing_subtype::is_sub_type(env, &num_no_reason, &ty1);
                                if is_num1 {
                                    make_num_type(swapped)
                                } else {
                                    // The second type needs solving too
                                    let (ty_err_opt, ty2) =
                                        expand_type_and_narrow_to_numeric(is_dynamic2, env, p2, ty2);
                                    if let Some(ty_err) = &ty_err_opt {
                                        typing_error_utils::add_typing_error(ty_err, env)
                                    }
                                    if typing_subtype::is_sub_type(env, &ty1, &nothing_no_reason)
                                        && typing_subtype::is_sub_type(
                                            env,
                                            &ty2,
                                            &nothing_no_reason,
                                        )
                                    {
                                        make_nothing_type(swapped)
                                    } else if is_int1
                                        && typing_subtype::is_sub_type(env, &ty2, &int_no_reason)
                                    {
                                        make_int_type()
                                    } else {
                                        make_num_type(!swapped)
                                    }
                                }
                            }
                        }
                    }
                }
            };
            make_result(is_like, env, te1, ty_mismatch1, te2, ty_mismatch2, result_ty)
        }
        // Type of division and exponentiation is essentially
        //    (float,num):float
        //  & (num,float):float
        //  & (num,num):num
        Bop::Slash | Bop::Starstar if !contains_any => {
            let make_num_type = || match bop {
                Bop::Slash => make_type::num(reason::ret_div(p.clone())),
                _ => make_type::num(reason::arith_ret(p.clone())),
            };
            let (ty_mismatch1, is_like1, ty1) =
                check_like_num(None, p.clone(), p1.clone(), env, ty1.clone());
            let (ty_mismatch2, is_like2, ty2) =
                check_like_num(None, p.clone(), p2.clone(), env, ty2.clone());
            // We'll compute the type ignoring whether one of the arguments was a like-type,
            // but we'll add the like type to the result type in the end if one was.
            let is_like = is_like1 || is_like2;
            let result_ty = match check_for_float_result(&p, env, &p1, &ty1, &p2, &ty2) {
                Some(ty) => ty,
                None => {
                    // We return num, unless both ty1 and ty2 will solve to nothing. This
                    // would happen for dynamic / dynamic, and in that case we want to
                    // return nothing, in order to get back dynamic in the end. For that to happen,
                    // we would have to have detected like types on both arguments.
                    if !(is_like1 && is_like2) {
                        make_num_type()
                    } else {
                        let (ty_err_opt, ty1) =
                            expand_type_and_try_narrow_to_nothing(env, p1.clone(), ty1);
                        if let Some(ty_err) = &ty_err_opt {
                            typing_error_utils::add_typing_error(ty_err, env)
                        }
                        let (ty_err_opt, ty2) =
                            expand_type_and_try_narrow_to_nothing(env, p2.clone(), ty2);
                        if let Some(ty_err) = &ty_err_opt {
                            typing_error_utils::add_typing_error(ty_err, env)
                        }
                        if typing_subtype::is_sub_type(env, &ty1, &nothing_no_reason)
                            && typing_subtype::is_sub_type(env, &ty2, &nothing_no_reason)
                        {
                            make_nothing_type(true)
                        } else {
                            make_num_type()
                        }
                    }
                }
            };
            make_result(is_like, env, te1, ty_mismatch1, te2, ty_mismatch2, result_ty)
        }
        Bop::Percent | Bop::Ltlt | Bop::Gtgt if !contains_any => {
            let (err_opt1, _used_dynamic1) =
                typing_argument::check_argument_type_against_parameter_type(
                    None,
                    None,
                    Some(typing_argument::DynFuncKind::SupportdynFunction),
                    false,
                    env,
                    make_type::int(reason::arith(p1.clone())),
                    p1.clone(),
                    ty1.clone(),
                );
            let (err_opt2, _used_dynamic2) =
                typing_argument::check_argument_type_against_parameter_type(
                    None,
                    None,
                    Some(typing_argument::DynFuncKind::SupportdynFunction),
                    false,
                    env,
                    make_type::int(reason::arith(p2.clone())),
                    p2.clone(),
                    ty2.clone(),
                );
            let r = match bop {
                Bop::Percent => reason::arith_ret_int(p.clone()),
                _ => reason::bitwise_ret(p.clone()),
            };
            // Result is int regardless of whether the arguments are int or ~int
            make_result(false, env, te1, err_opt1, te2, err_opt2, make_type::int(r))
        }
        Bop::Xor | Bop::Amp | Bop::Bar if !contains_any => {
            // Type-check a bitwise operation as if it's a call to a function of type
            //   <<__SupportDynamicType>> function bitwise_math(int $x, int $y): int
            // With one samll improvement: if checking of *either* argument succeeds against int
            // rather than ~int, then return int, because we know that it will simply throw if
            // the other argument is not int at runtime.
            let (err_opt1, used_dynamic1) =
                typing_argument::check_argument_type_against_parameter_type(
                    None,
                    None,
                    Some(typing_argument::DynFuncKind::SupportdynFunction),
                    false,
                    env,
                    make_type::int(reason::bitwise(p1.clone())),
                    p1.clone(),
                    ty1.clone(),
                );
            let (err_opt2, used_dynamic2) =
                typing_argument::check_argument_type_against_parameter_type(
                    None,
                    None,
                    Some(typing_argument::DynFuncKind::SupportdynFunction),
                    false,
                    env,
                    make_type::int(reason::bitwise(p2.clone())),
                    p2.clone(),
                    ty2.clone(),
                );
            make_result(
                used_dynamic1 && used_dynamic2,
                env,
                te1,
                err_opt1,
                te2,
                err_opt2,
                make_type::int(reason::bitwise_ret(p.clone())),
            )
        }
        Bop::Eqeq | Bop::Diff => make_result(
            false,
            env,
            te1,
            None,
            te2,
            None,
            make_type::bool(reason::comp(p.clone())),
        ),
        Bop::Eqeqeq | Bop::Diff2 => make_result(
            false,
            env,
            te1,
            None,
            te2,
            None,
            make_type::bool(reason::comp(p.clone())),
        ),
        Bop::Lt | Bop::Lte | Bop::Gt | Bop::Gte | Bop::Cmp => {
            let ty_num = make_type::num(reason::comp(p.clone()));
            let ty_int = make_type::int(reason::comp(p.clone()));
            let ty_bool = make_type::bool(reason::comp(p.clone()));
            let ty_result = match bop {
                Bop::Cmp => ty_int,
                _ => ty_bool,
            };
            let ty_string = make_type::string(reason::comp(p.clone()));
            let ty_datetime = make_type::datetime(reason::comp(p.clone()));
            let ty_datetimeimmutable = make_type::datetime_immutable(reason::comp(p.clone()));
            let ty_dynamic = make_type::dynamic(reason::comp(p.clone()));
            let ty_all = make_type::union(
                reason::comp(p.clone()),
                vec![
                    ty_num.clone(),
                    ty_string.clone(),
                    ty_datetime.clone(),
                    ty_datetimeimmutable.clone(),
                    ty_dynamic.clone(),
                ],
            );
            let both_sub = |env: &Env, ty: &Ty| {
                typing_subtype::can_sub_type(env, &ty1, ty)
                    && typing_subtype::can_sub_type(env, &ty2, ty)
            };
            // Comparison here is allowed when both args are num, both string, or both
            // DateTime | DateTimeImmutable. Alternatively, either or both args can be
            // dynamic. We use both_sub to check that both arguments subtype a type.
            //
            // This actually does not properly handle union types. For instance,
            // DateTime | DateTimeImmutable is neither a subtype of DateTime nor
            // DateTimeImmutable, but it will be the type of an element coming out
            // of a vector containing both. Further, dynamic could be comparable to
            // num | string | DateTime | DateTimeImmutable | dynamic. Better union
            // handling would be an improvement.
            if !contains_any
                && !(both_sub(
                    env,
                    &make_type::union(
                        reason::comp(p.clone()),
                        vec![ty_num.clone(), ty_dynamic.clone()],
                    ),
                ) || both_sub(
                    env,
                    &make_type::union(
                        reason::comp(p.clone()),
                        vec![ty_string.clone(), ty_dynamic.clone()],
                    ),
                ) || both_sub(
                    env,
                    &make_type::union(
                        reason::comp(p.clone()),
                        vec![
                            ty_datetime.clone(),
                            ty_datetimeimmutable.clone(),
                            ty_dynamic.clone(),
                        ],
                    ),
                ))
            {
                // There is definitely an error if we get here
                let lazy_fully_expanded = |ty: &Ty| {
                    let env = env.clone();
                    let ty = ty.clone();
                    Lazy::new(move || {
                        let ty = typing_expand::fully_expand(&env, ty);
                        let tys = typing_print::error(None, &env, &ty);
                        (ty, tys)
                    })
                };
                // `let ty1 = lazy (fully_expand env ty1) ... in let tys1 = Lazy.map ty1 ...`
                let tys1 = lazy_fully_expanded(&ty1);
                let tys2 = lazy_fully_expanded(&ty2);
                typing_error_utils::add_typing_error(
                    &typing_error::primary(typing_error::primary::T::ComparisonInvalidTypes {
                        pos: p.clone(),
                        left: tys1.map(|(ty1, tys1)| {
                            messages(reason::to_string(
                                &("This is ".to_string() + tys1),
                                get_reason(ty1),
                            ))
                        }),
                        right: tys2.map(|(ty2, tys2)| {
                            messages(reason::to_string(
                                &("This is ".to_string() + tys2),
                                get_reason(ty2),
                            ))
                        }),
                    }),
                    env,
                )
            } else {
                // If we get here, there might be an error that was obscured by can_subtype returning
                // true on an unresolved type variables. Insist that each type is separately allowed.
                // This leaves the potential of letting two acceptable, but incompatible types through.
                //
                // The environments of these two `sub_type`s are local to this
                // branch of the OCaml: the result is made with the environment
                // from before them.
                let saved_env = env.clone();
                let err1 = typing_subtype::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    ty1.clone(),
                    ty_all.clone(),
                    Some(typing_error::reasons_callback::with_code(
                        typing_error::reasons_callback::unify_error_at(p.clone()),
                        ErrorCode::ComparisonInvalidTypes,
                    )),
                );
                if let Some(e) = &err1 {
                    typing_error_utils::add_typing_error(e, env)
                }
                let err2 = typing_subtype::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    ty2.clone(),
                    ty_all.clone(),
                    Some(typing_error::reasons_callback::with_code(
                        typing_error::reasons_callback::unify_error_at(p.clone()),
                        ErrorCode::ComparisonInvalidTypes,
                    )),
                );
                if let Some(e) = &err2 {
                    typing_error_utils::add_typing_error(e, env)
                }
                *env = saved_env;
            }
            make_result(false, env, te1, None, te2, None, ty_result)
        }
        Bop::Dot => {
            let sub_arraykey = |env: &mut Env, p: &Pos, ty: &Ty| {
                let expected_ty = make_type::arraykey(reason::concat_operand(p.clone()));
                let (ty_mismatch, _used_dynamic) =
                    typing_argument::check_argument_type_against_parameter_type(
                        None,
                        Some(Ureason::URstrConcat),
                        Some(typing_argument::DynFuncKind::SupportdynFunction),
                        false,
                        env,
                        expected_ty,
                        p.clone(),
                        ty.clone(),
                    );
                ty_mismatch
            };
            let err_opt1 = sub_arraykey(env, &p1, &ty1);
            let err_opt2 = sub_arraykey(env, &p2, &ty2);
            let r = reason::concat_ret(p.clone());
            let ty = {
                // Special case for TypedFormatString operands.
                // If  e1 has type TypedFormatString<I,(t1,...,tn)>
                // and e2 has type TypedFormatString<I,(u1,...,um)>
                // then e1 . e2 has type TypedFormatString<I,(t1,...,tn,u1,...,um)>
                match (get_node(&ty1), get_node(&ty2)) {
                    (Ty_::Tnewtype(fs1, tyl1, _), Ty_::Tnewtype(fs2, tyl2, bound))
                        if tyl1.len() == 2
                            && tyl2.len() == 2
                            && sn::classes::is_typed_format_string(fs1)
                            && sn::classes::is_typed_format_string(fs2)
                            && typing_defs::equal_locl_ty(&tyl1[0], &tyl2[0]) =>
                    {
                        let (ty1, tuple1) = (&tyl1[0], &tyl1[1]);
                        let tuple2 = &tyl2[1];
                        match (get_node(tuple1), get_node(tuple2)) {
                            (
                                Ty_::Ttuple(TupleType {
                                    required: req1,
                                    optional: opt1,
                                    extra: _,
                                }),
                                Ty_::Ttuple(TupleType {
                                    required: req2,
                                    optional: opt2,
                                    extra: _,
                                }),
                            ) if opt1.is_empty() && opt2.is_empty() => {
                                let mut req = req1.clone();
                                req.extend(req2.iter().cloned());
                                mk((
                                    r.clone(),
                                    Ty_::Tnewtype(
                                        fs1.clone(),
                                        vec![ty1.clone(), make_type::tuple(r.clone(), req)],
                                        bound.clone(),
                                    ),
                                ))
                            }
                            _ => make_type::string(r.clone()),
                        }
                    }
                    _ => make_type::string(r.clone()),
                }
            };
            make_result(false, env, te1, err_opt1, te2, err_opt2, ty)
        }
        Bop::Barbar | Bop::Ampamp => make_result(
            false,
            env,
            te1,
            None,
            te2,
            None,
            make_type::bool(reason::logic_ret(p.clone())),
        ),
        Bop::QuestionQuestion if !contains_any => panic!("assert false"),
        _ => {
            assert!(contains_any);
            if is_any(&ty1) {
                make_result(false, env, te1, None, te2, None, ty1.clone())
            } else {
                make_result(false, env, te1, None, te2, None, ty2.clone())
            }
        }
    }
}

pub fn unop(p: Pos, env: &mut Env, uop: Uop, te: tast::Expr, ty: Ty) -> (tast::Expr, Ty) {
    let make_result = |is_like: bool,
                       env: &mut Env,
                       te: tast::Expr,
                       err_opt: Option<(Ty, Ty)>,
                       ty: Ty| {
        let ty = if is_like {
            typing_union::union(env, None, None, ty, make_type::dynamic(reason::witness(p.clone())))
        } else {
            ty
        };

        let hte = hole_on_err(te, err_opt);
        let te = typing_helpers::make_simplify_typed_expr(
            env,
            p.clone(),
            ty.clone(),
            aast::Expr_::Unop(Box::new((uop, hte))),
        );
        (te, ty)
    };
    // `let is_any = Typing_utils.is_any env`: with the environment as it is now.
    let env0 = env.clone();
    let is_any = |ty: &Ty| typing_utils::is_any(&env0, ty);
    match uop {
        Uop::Unot => {
            if is_any(&ty) {
                make_result(false, env, te, None, ty)
            } else {
                // args isn't any or a variant thereof so can actually do stuff
                // !$x (logical not) works with any type, so we just return Tbool
                make_result(false, env, te, None, make_type::bool(reason::logic_ret(p.clone())))
            }
        }
        Uop::Utild => {
            if is_any(&ty) {
                make_result(false, env, te, None, ty)
            } else {
                let (err_opt, used_dynamic) =
                    typing_argument::check_argument_type_against_parameter_type(
                        None,
                        None,
                        Some(typing_argument::DynFuncKind::SupportdynFunction),
                        false,
                        env,
                        make_type::int(reason::bitwise(p.clone())),
                        p.clone(),
                        ty,
                    );
                make_result(
                    used_dynamic,
                    env,
                    te,
                    err_opt,
                    make_type::int(reason::bitwise_ret(p.clone())),
                )
            }
        }
        Uop::Uplus | Uop::Uminus | Uop::Uincr | Uop::Upincr | Uop::Udecr | Uop::Updecr => {
            if is_any(&ty) {
                make_result(false, env, te, None, ty)
            } else {
                let allow_nothing = typing_defs::is_dynamic(&ty);
                let (ty_mismatch, is_like, ty) = check_like_num(
                    match uop {
                        Uop::Uincr | Uop::Upincr | Uop::Udecr | Uop::Updecr => {
                            Some(typing_error::callback::inc_dec_invalid_argument())
                        }
                        _ => None,
                    },
                    p.clone(),
                    p.clone(),
                    env,
                    ty,
                );
                let (ty_err_opt, ty): (_, Ty) =
                    expand_type_and_narrow_to_numeric(allow_nothing, env, p.clone(), ty);
                if let Some(ty_err) = &ty_err_opt {
                    typing_error_utils::add_typing_error(ty_err, env)
                }
                let result_ty =
                    if typing_subtype::is_sub_type(env, &ty, &make_type::nothing(reason::none())) {
                        make_type::nothing(get_reason(&ty).clone())
                    } else if is_float(env, &ty) {
                        make_type::float(reason::arith_ret_float((
                            p.clone(),
                            get_reason(&ty).clone(),
                            ArgPosition::Aonly,
                        )))
                    } else if is_int(env, &ty) {
                        make_type::int(reason::arith_ret_int(p.clone()))
                    } else {
                        make_type::num(reason::arith_ret_num((
                            p.clone(),
                            get_reason(&ty).clone(),
                            ArgPosition::Aonly,
                        )))
                    };
                let result_ty = if is_like {
                    let dynamic = make_type::dynamic(get_reason(&result_ty).clone());
                    typing_union::union(env, None, None, result_ty, dynamic)
                } else {
                    result_ty
                };
                make_result(false, env, te, ty_mismatch, result_ty)
            }
        }
        Uop::Usilence => {
            // Silencing does not change the type
            // any check omitted because would return the same anyway
            make_result(false, env, te, None, ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hole_on_err_wraps_the_expression_in_a_typing_hole() {
        let int = make_type::int(reason::none());
        let num = make_type::num(reason::none());
        let e = tast::make_typed_expr(Pos::NONE, int.clone(), aast::Expr_::Int("1".to_string()));
        match hole_on_err(e.clone(), None) {
            aast::Expr(ty, _, aast::Expr_::Int(i)) => {
                assert!(crate::typing_defs_core::phys_equal(&ty, &int));
                assert_eq!(i, "1")
            }
            _ => panic!("expected the expression unchanged"),
        }
        match hole_on_err(e, Some((int.clone(), num.clone()))) {
            aast::Expr(ty, _, aast::Expr_::Hole(b)) => {
                assert!(crate::typing_defs_core::phys_equal(&ty, &int));
                let (inner, ty_have, ty_expect, source) = *b;
                assert!(matches!(inner.2, aast::Expr_::Int(_)));
                assert!(crate::typing_defs_core::phys_equal(&ty_have, &int));
                assert!(crate::typing_defs_core::phys_equal(&ty_expect, &num));
                assert!(matches!(source, aast::HoleSource::Typing));
            }
            _ => panic!("expected a hole"),
        }
    }
}
