// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 12509-12799): module `Binop`.
//! See `hh/PORTING.md`.
//!
//! `(Nast.expr, Tast.expr * locl_ty) Either.t` is
//! `Either<&nast::Expr, (tast::Expr, Ty)>` (`itertools::Either`: `First` is
//! `Left`, `Second` is `Right`).

use itertools::Either;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::diagnostics_state;
use crate::naming_special_names as sn;
use crate::tast;
use crate::typing::assign;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_arithmetic;
use crate::typing_class_pointers;
use crate::typing_defs::*;
use crate::typing_defs_constraints::InternalType;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
use crate::typing_local_ops;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module Reason = Typing_reason
use crate::typing_reason as reason;
// module Union = Typing_union
use crate::typing_union as union;

/// `check_e2` of `check_assign` and `check_binop`: the right operand is
/// either still to be checked, or already checked.
fn check_e2(
    checker: impl FnOnce(&mut Env, &nast::Expr) -> (tast::Expr, Ty),
    env: &mut Env,
    e2: Either<&nast::Expr, (tast::Expr, Ty)>,
) -> (tast::Expr, Ty) {
    match e2 {
        Either::Left(expr) => checker(env, expr),
        Either::Right((te, ty)) => (te, ty),
    }
}

/// When typing compound assignments we generate a 'fake' expression which
/// desugars it to the operation on the rhs of the assignment. If there
/// was a subtyping error, we end up with the Hole on the fake rhs
/// rather than the original rhs. This function rewrites the
/// desugared expression with the Hole in the correct place
pub(crate) fn resugar_binop(expr: tast::Expr) -> Option<tast::Expr> {
    let aast::Expr(topt, p, e) = expr;
    match e {
        aast::Expr_::Assign(assign) => {
            let (te1, _, rhs) = *assign;
            match rhs {
                aast::Expr(_, _, aast::Expr_::Hole(hole)) => {
                    let (inner, ty_have, ty_expect, source) = *hole;
                    match inner {
                        aast::Expr(_, _, aast::Expr_::Binop(binop)) => {
                            let aast::Binop {
                                bop: op,
                                lhs: _,
                                rhs: te2,
                            } = *binop;
                            let hte2 = mk_hole(Some(source), te2, ty_have, ty_expect);
                            let te = aast::Expr_::Assign(Box::new((te1, Some(op), hte2)));
                            Some(aast::Expr(topt, p, te))
                        }
                        // The second case needs a `Binop` on the right, not a
                        // `Hole`.
                        _ => None,
                    }
                }
                aast::Expr(_, _, aast::Expr_::Binop(binop)) => {
                    let aast::Binop {
                        bop: op,
                        lhs: _,
                        rhs: te2,
                    } = *binop;
                    let te = aast::Expr_::Assign(Box::new((te1, Some(op), te2)));
                    Some(aast::Expr(topt, p, te))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn check_assign(
    check_defined: bool,
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    outer: &nast::Expr,
    p: &Pos,
    op_opt: Option<Bop>,
    e1: &nast::Expr,
    e2: Either<&nast::Expr, (tast::Expr, Ty)>,
) -> (tast::Expr, Ty) {
    fn make_result(env: &mut Env, p: Pos, te: tast::Expr_, ty: Ty) -> (tast::Expr, Ty) {
        let (te, ty) = crate::typing::prelude::make_result(env, p, te, ty);
        typing_local_ops::check_assignment(env, &te);
        (te, ty)
    }
    match op_opt {
        // For example, e1 += e2. This is typed and translated as if
        // written e1 = e1 + e2.
        // TODO TAST: is this right? e1 will get evaluated more than once
        Some(op) => {
            let aast::Expr(_, _, lval_) = e1;
            match (op, lval_) {
                (Bop::QuestionQuestion, aast::Expr_::ClassGet(_)) => {
                    diagnostics_state::experimental_feature(
                        p.clone(),
                        "null coalesce assignment operator with static properties",
                    );
                    expr_error(env, p.clone(), outer)
                }
                _ => {
                    let (te, ty) = check_binop(check_defined, expected, env, p, op, e1, e2);
                    let (te2, ty2) = check_assign(
                        check_defined,
                        expected,
                        env,
                        outer,
                        p,
                        None,
                        e1,
                        Either::Right((te, ty)),
                    );
                    let te_opt = resugar_binop(te2);
                    match te_opt {
                        Some(aast::Expr(_, _, te)) => make_result(env, p.clone(), te, ty2),
                        _ => panic!("assert false"),
                    }
                }
            }
        }
        None => {
            // Read before `e2` is consumed (this has no effect).
            let expr_for_string_check = match &e2 {
                Either::Left(e) => Some(*e),
                Either::Right(_) => None,
            };
            let ctxt = expr::context::T {
                check_defined,
                ..expr::context::default()
            };
            let (te2, ty2) = check_e2(|env, e| expr::expr(None, &ctxt, env, e), env, e2);
            let pos2 = te2.1.clone();
            let (te1, ty, ty_mismatch_opt) =
                assign::assign(expr_for_string_check, p, env, e1, &pos2, ty2);
            let te = aast::Expr_::Assign(Box::new((
                te1,
                None,
                hole_on_ty_mismatch(te2, ty_mismatch_opt),
            )));
            make_result(env, p.clone(), te, ty)
        }
    }
}

/// Type check a binop, where e1 is the lhs and e2 is the rhs sub-exression.
/// In case we've already checked e2, allow it to be passed in as it's TAST and type
pub fn check_binop(
    check_defined: bool,
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    p: &Pos,
    bop: Bop,
    e1: &nast::Expr,
    e2: Either<&nast::Expr, (tast::Expr, Ty)>,
) -> (tast::Expr, Ty) {
    match bop {
        Bop::QuestionQuestion => {
            let (te1, ty1) = expr::expr(
                None,
                &expr::context::T {
                    lhs_of_null_coalesce: true,
                    check_defined,
                    ..expr::context::default()
                },
                env,
                e1,
            );
            let parent_lenv = env.lenv.clone();
            let lenv1 = env.lenv.clone();
            let ctxt = expr::context::T {
                check_defined,
                ..expr::context::default()
            };
            let (te2, ty2) = check_e2(|env, e| expr::expr(expected, &ctxt, env, e), env, e2);
            let lenv2 = env.lenv.clone();
            lenv::union_lenvs(env, p, &parent_lenv, &lenv1, &lenv2);
            // Dynamic inference: when $lhs ?? $rhs and $lhs is dynamic with a
            // shadow tyvar, the RHS type constrains what the dynamic value must be
            // when non-null. Add ty2 as an upper bound on the shadow.
            if env::get_tcopt(env).tco_dynamic_inference {
                match get_node(&ty1) {
                    Ty_::Tdynamic(Some(v)) => {
                        let v = *v;
                        env::add_tyvar_upper_bound(None, env, v, InternalType::LoclType(ty2.clone()))
                    }
                    _ => {}
                }
            }
            // There are two cases: either the left argument was null in which case we
            // evaluate the second argument which gets as ty2, or that ty1 wasn't null.
            // The following intersection adds the nonnull information.
            let ty1 = inter::intersect(env, reason::none(), ty1, make_type::nonnull(reason::none()));
            let ty = union::union(env, None, Some(true), ty1, ty2);
            make_result(
                env,
                p.clone(),
                aast::Expr_::Binop(Box::new(aast::Binop {
                    bop: Bop::QuestionQuestion,
                    lhs: te1,
                    rhs: te2,
                })),
                ty,
            )
        }
        Bop::Ampamp | Bop::Barbar => {
            let c = bop == Bop::Ampamp;
            let ctxt = expr::context::T {
                check_defined,
                ..expr::context::default()
            };
            let (te1, _) = expr::expr(None, &ctxt, env, e1);
            let aast::Expr(cond_ty, cond_pos, _) = &te1;
            check_bool_for_condition(env, cond_pos, cond_ty.clone());
            let lenv = env.lenv.clone();
            expr::condition(env, c, &te1);
            let (te2, _) = check_e2(|env, e| expr::expr(None, &ctxt, env, e), env, e2);
            let aast::Expr(cond_ty, cond_pos, _) = &te2;
            check_bool_for_condition(env, cond_pos, cond_ty.clone());
            env.lenv = lenv;
            make_result(
                env,
                p.clone(),
                aast::Expr_::Binop(Box::new(aast::Binop {
                    bop,
                    lhs: te1,
                    rhs: te2,
                })),
                make_type::bool(reason::logic_ret(p.clone())),
            )
        }
        _ => {
            let expected = match bop {
                Bop::Dot => env_help::expand_expected_opt(false, false, env, expected),
                _ => None,
            };
            let expected: Option<expected_ty::T> = match expected {
                Some((pos, ur, _, _, Ty_::Tnewtype(fs, tyargs, bound), _))
                    if tyargs.len() == 2 && sn::classes::is_typed_format_string(&fs) =>
                {
                    let ty = tyargs[0].clone();
                    let fresh_ty = env::fresh_type(env, p.clone());
                    let expected = expected_ty::make(
                        None,
                        None,
                        pos,
                        ur,
                        mk((
                            reason::concat_operand(p.clone()),
                            Ty_::Tnewtype(fs, vec![ty, fresh_ty], bound),
                        )),
                    );
                    Some(expected)
                }
                _ => None,
            };
            let ctxt = expr::context::T {
                check_defined,
                ..expr::context::default()
            };
            let (te1, ty1) = expr::expr(expected.as_ref(), &ctxt, env, e1);
            // Read before `e2` is consumed (this has no effect).
            let p2 = match &e2 {
                Either::Left(aast::Expr(_, p, _)) | Either::Right((aast::Expr(_, p, _), _)) => {
                    p.clone()
                }
            };
            let e2_first = match &e2 {
                Either::Left(e2) => Some(*e2),
                Either::Right(_) => None,
            };
            let (te2, ty2) =
                check_e2(|env, e| expr::expr(expected.as_ref(), &ctxt, env, e), env, e2);
            match bop {
                // TODO: This could be less conservative: we only need to account for
                // the possibility of exception if the operator is `/` or `/=`.
                Bop::Eqeqeq | Bop::Diff2 => {}
                _ => might_throw(p, env),
            }
            match bop {
                Bop::Dot => {
                    typing_class_pointers::check_string_coercion_point(
                        env,
                        e1,
                        &make_type::string(reason::none()),
                    );
                    match e2_first {
                        Some(e2) => typing_class_pointers::check_string_coercion_point(
                            env,
                            e2,
                            &make_type::string(reason::none()),
                        ),
                        None => {}
                    }
                }
                _ => {}
            }
            typing_arithmetic::binop(
                p.clone(),
                env,
                bop,
                crate::aast_utils::get_expr_pos(e1),
                te1,
                ty1,
                p2,
                te2,
                ty2,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_expr(n: &str, ty: &Ty) -> tast::Expr {
        aast::Expr(ty.clone(), Pos::NONE, aast::Expr_::Int(n.to_string()))
    }

    fn assign_of(lhs: tast::Expr, rhs: tast::Expr, ty: &Ty) -> tast::Expr {
        aast::Expr(
            ty.clone(),
            Pos::NONE,
            aast::Expr_::Assign(Box::new((lhs, None, rhs))),
        )
    }

    fn plus(lhs: tast::Expr, rhs: tast::Expr, ty: &Ty) -> tast::Expr {
        aast::Expr(
            ty.clone(),
            Pos::NONE,
            aast::Expr_::Binop(Box::new(aast::Binop {
                bop: Bop::Plus,
                lhs,
                rhs,
            })),
        )
    }

    #[test]
    fn resugar_binop_moves_the_operator_back() {
        let int = make_type::int(reason::none());
        let e = assign_of(
            int_expr("1", &int),
            plus(int_expr("1", &int), int_expr("2", &int), &int),
            &int,
        );
        match resugar_binop(e) {
            Some(aast::Expr(_, _, aast::Expr_::Assign(a))) => {
                let (l, op, r) = *a;
                assert_eq!(op, Some(Bop::Plus));
                assert!(matches!(l.2, aast::Expr_::Int(ref s) if s == "1"));
                assert!(matches!(r.2, aast::Expr_::Int(ref s) if s == "2"));
            }
            _ => panic!("expected an assignment"),
        }
    }

    #[test]
    fn resugar_binop_keeps_the_hole_on_the_rhs() {
        let int = make_type::int(reason::none());
        let string = make_type::string(reason::none());
        let hole = aast::Expr(
            int.clone(),
            Pos::NONE,
            aast::Expr_::Hole(Box::new((
                plus(int_expr("1", &int), int_expr("2", &int), &int),
                int.clone(),
                string.clone(),
                aast::HoleSource::Typing,
            ))),
        );
        let e = assign_of(int_expr("1", &int), hole, &int);
        match resugar_binop(e) {
            Some(aast::Expr(_, _, aast::Expr_::Assign(a))) => {
                let (_, op, r) = *a;
                assert_eq!(op, Some(Bop::Plus));
                match r.2 {
                    aast::Expr_::Hole(h) => {
                        let (inner, _, _, source) = *h;
                        assert!(matches!(inner.2, aast::Expr_::Int(ref s) if s == "2"));
                        assert!(matches!(source, aast::HoleSource::Typing));
                    }
                    _ => panic!("expected a hole"),
                }
            }
            _ => panic!("expected an assignment"),
        }
    }

    #[test]
    fn resugar_binop_needs_a_binop() {
        let int = make_type::int(reason::none());
        let string = make_type::string(reason::none());
        assert!(resugar_binop(assign_of(int_expr("1", &int), int_expr("2", &int), &int)).is_none());
        let hole = aast::Expr(
            int.clone(),
            Pos::NONE,
            aast::Expr_::Hole(Box::new((
                int_expr("2", &int),
                int.clone(),
                string,
                aast::HoleSource::Typing,
            ))),
        );
        assert!(resugar_binop(assign_of(int_expr("1", &int), hole, &int)).is_none());
        assert!(resugar_binop(int_expr("1", &int)).is_none());
    }
}
