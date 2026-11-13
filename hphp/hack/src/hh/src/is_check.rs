// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `is_check.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::ast_defs::Bop;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::error_codes;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_defs::mk;
use crate::typing_env;
use crate::typing_error;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_solver;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning::Migrated;
use crate::typing_warning_utils;

const warning_kind: typing_warning::Kind<typing_warning::is_as_always::T, Migrated> =
    typing_warning::Kind::Is_as_always;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

fn nothing_ty() -> Ty {
    typing_make_type::nothing(typing_reason::none())
}

// Tany indicates missing type information (e.g. unresolved generics). Subtype
// checks involving Tany are unreliable since Tany <: T for all T. The nothing
// guard below catches bare Tany (Tany <: nothing), but not ?Tany or
// supportdyn<Tany> since null is not <: nothing. This helper catches those.
fn has_tany(env: &Env, ty: &Ty) -> bool {
    // The environment is dropped.
    let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tany(_) => true,
        Ty_::Toption(inner) => has_tany(env, inner),
        Ty_::Tunion(tys) | Ty_::Tintersection(tys) => tys.iter().any(|ty| has_tany(env, ty)),
        Ty_::Tnewtype(_, tys, _) => tys.iter().any(|ty| has_tany(env, ty)),
        _ => false,
    }
}

// To handle typechecking against placeholder, e.g., `... as C<_>`, we convert
// the generic the placeholder is elaborated to into a type variable so that
// the subtyping query can be discharged.
fn replace_placeholders_with_tvars(env: &mut Env, pos: &Pos, ty: Ty) -> Ty {
    let replace_placeholder = |env: &mut Env, ty: &Ty| match get_node(ty) {
        Ty_::Tgeneric(name) if name.contains('#') => typing_env::fresh_type(env, pos.clone()),
        _ => ty.clone(),
    };
    match get_node(&ty) {
        Ty_::Tclass(id, exact, targs) => {
            // `List.fold_map ~init:env`: left to right
            let targs = targs
                .iter()
                .map(|ty| replace_placeholder(env, ty))
                .collect();
            mk((
                typing_reason::none(),
                Ty_::Tclass(id.clone(), exact.clone(), targs),
            ))
        }
        _ => ty,
    }
}

fn is_like_null(env: &Env, ty: &Ty) -> bool {
    tast_env::is_sub_type(
        env,
        ty,
        &typing_make_type::locl_like(
            typing_reason::none(),
            typing_make_type::null(typing_reason::none()),
        ),
    )
}

fn is_as_warning(
    as_lint: Option<Option<tast::CheckStatus>>,
    kind: typing_warning::is_as_always::Kind,
    pos: Pos,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
    env: &Env,
) {
    // The fields of the record are evaluated right to left, as in OCaml.
    let rhs_ty = tast_env::print_ty(env, rhs_ty);
    let lhs_ty = tast_env::print_ty(env, lhs_ty);
    typing_warning_utils::add_for_migration(
        &tast_env::get_tcopt(env),
        as_lint,
        (
            pos,
            typing_warning::Kind::Is_as_always,
            typing_warning::is_as_always::T {
                kind,
                lhs_ty,
                rhs_ty,
            },
        ),
    )
}

fn coalesce_warning(
    kind: typing_warning::null_coalesce_always::Kind,
    pos: Pos,
    lhs_ty: &Ty,
    _rhs_ty: &Ty,
    env: &Env,
) {
    // The fields of the record are evaluated right to left, as in OCaml.
    let lhs_ty_str = tast_env::print_ty(env, lhs_ty);
    let lhs_pos = typing_reason::to_pos(get_reason(lhs_ty));
    tast_env::add_warning(
        env,
        (
            pos,
            typing_warning::Kind::Null_coalesce_always,
            typing_warning::null_coalesce_always::T {
                kind,
                lhs_pos,
                lhs_ty: lhs_ty_str,
            },
        ),
    )
}

fn trivial_check(
    pos: &Pos,
    env: &Env,
    lhs_ty: &Ty,
    rhs_ty: &Ty,
    always: impl FnOnce(Pos, &Ty, &Ty, &Env),
    never: impl FnOnce(Pos, &Ty, &Ty, &Env),
) {
    if tast_env::is_sub_type(env, lhs_ty, &nothing_ty())
        || has_tany(env, lhs_ty)
        || has_tany(env, rhs_ty)
    {
        // If we have a nothing or Tany in our hands, there was a bigger problem
        // originating from earlier in the program. Don't flag it here, as it is
        // merely a symptom.
    } else {
        let lhs_ty = {
            // Don't strip the like if LHS is ~null because this commonly leads to
            // false positives.
            if is_like_null(env, lhs_ty) {
                lhs_ty.clone()
            } else {
                tast_env::strip_dynamic(env, lhs_ty.clone())
            }
        };
        let mut env = env.clone();
        let lhs_ty = tast_env::expand_type(&mut env, lhs_ty);
        match tast_env::is_disjoint(false, &env, &lhs_ty, rhs_ty) {
            tast_env::IsDisjointResult::Disjoint => never(pos.clone(), &lhs_ty, rhs_ty, &env),
            tast_env::IsDisjointResult::DisjointIgnoringDynamic(lhs_ty, rhs_ty) => {
                never(pos.clone(), &lhs_ty, &rhs_ty, &env)
            }
            tast_env::IsDisjointResult::NonDisjoint => {
                // We can't just use the `is_subtype` API which will discharge the
                // propositions with the fresh type variables. Instead, we use `sub_type`
                // which feedback the propositions against unconstrained type variables as
                // assumptions.
                let (_, lhs_ty) = typing_solver::expand_type_and_solve(
                    &mut env,
                    None,
                    "a value",
                    pos.clone(),
                    lhs_ty,
                );
                let restore_pos = typing_env::set_inference_env_pos(&mut env, Some(pos.clone()));
                typing_env::open_tyvars(&mut env, pos.clone());
                let rhs_ty = replace_placeholders_with_tvars(&mut env, pos, rhs_ty.clone());
                let callback = typing_error::reasons_callback::unify_error_at(pos.clone());
                let err_opt1 = typing_utils::sub_type(
                    &mut env,
                    None,
                    None,
                    None,
                    None,
                    lhs_ty.clone(),
                    rhs_ty.clone(),
                    Some(callback),
                );
                let err_opt2 = typing_solver::close_tyvars_and_solve(&mut env);
                // `Option.merge err_opt1 err_opt2 ~f:Typing_error.both`
                let err_opt = match (err_opt1, err_opt2) {
                    (None, None) => None,
                    (Some(e), None) | (None, Some(e)) => Some(e),
                    (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
                };
                restore_pos(&mut env);
                if err_opt.is_none() {
                    always(pos.clone(), &lhs_ty, &rhs_ty, &env)
                }
            }
        }
    }
}

/// `handler ~as_lint`
struct Handler {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, expr: &'a tast::Expr) {
        let as_lint = if self.as_lint {
            Some(Some(tast_env::get_check_status(env)))
        } else {
            None
        };
        match expr {
            Expr(_, p, Expr_::Is(is)) => {
                let (Expr(lhs_ty, _, _), hint) = &**is;
                let mut env = env.clone();
                let hint_ty = tast_env::localize_hint_for_refinement(&mut env, hint);
                use typing_warning::is_as_always::Kind::*;
                trivial_check(
                    p,
                    &env,
                    lhs_ty,
                    &hint_ty,
                    |pos, lhs_ty, rhs_ty, env| {
                        is_as_warning(as_lint, Is_is_always_true, pos, lhs_ty, rhs_ty, env)
                    },
                    |pos, lhs_ty, rhs_ty, env| {
                        is_as_warning(as_lint, Is_is_always_false, pos, lhs_ty, rhs_ty, env)
                    },
                )
            }
            Expr(_, p, Expr_::As(as_)) => {
                let oxidized::aast::As_ {
                    expr: Expr(lhs_ty, lhs_pos, lhs_expr),
                    hint,
                    is_nullable,
                    enforce_deep: _,
                } = &**as_;
                let mut env = env.clone();
                let hint_ty = tast_env::localize_hint_for_refinement(&mut env, hint);
                use typing_warning::is_as_always::Kind::*;
                let is_nullable = *is_nullable;
                trivial_check(
                    p,
                    &env,
                    lhs_ty,
                    &hint_ty,
                    |pos, lhs_ty, rhs_ty, env| {
                        is_as_warning(
                            as_lint,
                            As_always_succeeds(typing_warning::Quickfix {
                                can_be_captured: aast_utils::can_be_captured(lhs_expr),
                                original_pos: p.clone(),
                                replacement_pos: lhs_pos.clone(),
                            }),
                            pos,
                            lhs_ty,
                            rhs_ty,
                            env,
                        )
                    },
                    |pos, lhs_ty, rhs_ty, env| {
                        is_as_warning(
                            as_lint,
                            As_always_fails { is_nullable },
                            pos,
                            lhs_ty,
                            rhs_ty,
                            env,
                        )
                    },
                )
            }
            Expr(_, p, Expr_::Binop(b)) if matches!(b.bop, Bop::QuestionQuestion) => {
                let Expr(lhs_ty, _, lhs_expr) = &b.lhs;
                use typing_warning::null_coalesce_always::Kind::*;
                match lhs_expr {
                    Expr_::ArrayGet(_) => {}
                    _ => trivial_check(
                        p,
                        env,
                        lhs_ty,
                        &typing_make_type::null(typing_reason::witness(p.clone())),
                        |pos, lhs_ty, rhs_ty, env| {
                            coalesce_warning(Null_coalesce_always_null, pos, lhs_ty, rhs_ty, env)
                        },
                        |pos, lhs_ty, rhs_ty, env| {
                            coalesce_warning(Null_coalesce_never_null, pos, lhs_ty, rhs_ty, env)
                        },
                    ),
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler { as_lint })
}
