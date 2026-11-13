// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 9776-10649): module `Stmt`.
//! See `hh/PORTING.md`.
//!
//! The signature of the OCaml module exports [`stmt`] and [`block`]; the
//! other functions are `pub(crate)` (see `typing/mod.rs`).
//!
//! - A `Nast.stmt list` (a block) is a slice of statements, and a
//!   `Tast.stmt list` a `Vec`; the TAST nodes wrap them in `aast::Block` /
//!   `aast::FinallyBlock` as `oxidized` declares them.
//! - `infer_loop`, which OCaml defines inside `stmt_` and which reads the
//!   position and the statement being checked, takes them as arguments.
//! - `Expr.condition_dual` returns its two environment transformers as
//!   closures that take the environment.

use itertools::Either;
use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::FunKind;
use oxidized::local_id::LocalId;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::decl_counters;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
// module C = Typing_continuations
use crate::typing_continuations as c;
// open Typing_defs (with Typing_defs_core)
use crate::typing_defs::*;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_env_types::LocalEnv;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
use crate::typing_per_cont_env;
use crate::typing_per_cont_env::PerContEntry;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
use crate::wrapped_map;

/// `Expr.Context.default`
fn ctxt_default() -> expr::context::T {
    expr::context::default()
}

pub fn block(env: &mut Env, stl: &[nast::Stmt]) -> Vec<tast::Stmt> {
    env::with_origin(env, decl_counters::Origin::Body, |env| {
        // We keep the AST `Block`-free here.
        //
        // OCaml accumulates the statements in reverse order and reverses the
        // list at the end: the statements of a `Block` are spliced in their
        // order.
        let mut res: Vec<tast::Stmt> = vec![];
        for st in stl {
            let st = stmt(env, st);
            match st {
                aast::Stmt(_, aast::Stmt_::Block(b)) => {
                    let (_, stl_) = *b;
                    res.extend(stl_.0)
                }
                _ => res.push(st),
            }
        }
        res
    })
}

pub fn stmt(env: &mut Env, aast::Stmt(pos, st): &nast::Stmt) -> tast::Stmt {
    let st = stmt_(env, pos, st);
    crate::typing_debug::log_env_if_too_big(pos, env);
    aast::Stmt(pos.clone(), st)
}

/// Whether the continuations after one more iteration of a loop are
/// subsumed by the ones before it (`continuations_converge`, local to
/// `infer_loop`).
fn continuations_converge(
    env: &Env,
    old_conts: &typing_per_cont_env::T,
    new_conts: &typing_per_cont_env::T,
) -> bool {
    wrapped_map::for_all2(
        |_, old_cont_entry: Option<&PerContEntry>, new_cont_entry: Option<&PerContEntry>| {
            crate::typing_per_cont_ops::is_sub_opt_entry(
                sub_type::is_sub_type,
                env,
                new_cont_entry,
                old_cont_entry,
            )
        },
        old_conts,
        new_conts,
    )
}

/// Type check a loop. f env = (env, result) checks the body of the loop.
/// We iterate over the loop until the "next" continuation environment is
/// stable. alias_depth is supposed to be an upper bound on this; but in
/// certain cases this fails (e.g. a generic type grows unboundedly). TODO:
/// fix this.
///
/// Local to `stmt_` in OCaml: `pos` and `st` are the statement being
/// checked.
pub(crate) fn infer_loop<R>(
    env: &mut Env,
    pos: &Pos,
    st: &nast::Stmt_,
    mut f: impl FnMut(&mut Env) -> R,
) -> R {
    let in_loop_outer = env.in_loop;
    let alias_depth = if in_loop_outer {
        1
    } else {
        // `Typing_alias.get_depth (pos, st)`
        crate::typing_alias::get_depth(&aast::Stmt(pos.clone(), st.clone()))
    };
    let max_number_of_iterations = env::get_tcopt(env)
        .tco_loop_iteration_upper_bound
        .unwrap_or(alias_depth);
    env.in_loop = true;
    // `let rec loop env n`
    let mut n: isize = 1;
    loop {
        // Remember the old environment
        let old_conts = env.lenv.per_cont_env.clone();
        let result = f(env);
        let new_conts = env.lenv.per_cont_env.clone();
        // Finish if we reach the bound, or if the environments match
        if n == max_number_of_iterations || continuations_converge(env, &old_conts, &new_conts) {
            log_iteration_count(env, pos, n);
            env.in_loop = in_loop_outer;
            return result;
        } else {
            n += 1
        }
    }
}

pub(crate) fn stmt_(env: &mut Env, pos: &Pos, st: &nast::Stmt_) -> tast::Stmt_ {
    env::open_tyvars(env, pos.clone());
    let res = match st {
        aast::Stmt_::Fallthrough => {
            lenv::move_and_merge_next_in_cont(env, pos, c::T::Fallthrough);
            aast::Stmt_::Fallthrough
        }
        aast::Stmt_::Noop => aast::Stmt_::Noop,
        aast::Stmt_::YieldBreak => {
            lenv::move_and_merge_next_in_cont(env, pos, c::T::Exit);
            aast::Stmt_::YieldBreak
        }
        aast::Stmt_::Expr(e) => {
            let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
            if crate::typing_func_terminality::typed_expression_exits(&te) {
                lenv::move_and_merge_next_in_cont(env, pos, c::T::Exit)
            }
            aast::Stmt_::Expr(Box::new(te))
        }
        aast::Stmt_::If(if_) => {
            let (e, b1, b2) = &**if_;
            let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
            let aast::Expr(cond_ty, cond_pos, _) = &te;
            check_bool_for_condition(env, cond_pos, cond_ty.clone());
            let (condition_true, condition_false) = expr::condition_dual(env, &te);
            let (tb1, tb2) = branch(
                pos,
                env,
                move |env: &mut Env| {
                    condition_true(env);
                    block(env, &b1.0)
                },
                move |env: &mut Env| {
                    condition_false(env);
                    block(env, &b2.0)
                },
            );
            // TODO TAST: annotate with joined types
            aast::Stmt_::If(Box::new((te, aast::Block(tb1), aast::Block(tb2))))
        }
        aast::Stmt_::Return(e) => match &**e {
            None => {
                crate::typing_return::check_inout_return(pos.clone(), env);
                let rty = make_type::void(reason::witness(pos.clone()));
                let crate::typing_env_return_info::T {
                    return_type: expected_return,
                    ..
                } = env::get_return(env);
                let expected_return = crate::typing_return::strip_awaitable(
                    env::get_fn_kind(env),
                    env,
                    expected_return,
                );
                match env::get_fn_kind(env) {
                    FunKind::FGenerator | FunKind::FAsyncGenerator => {}
                    _ => crate::typing_return::implicit_return(
                        env,
                        pos.clone(),
                        expected_return,
                        rty,
                        None,
                        false,
                    ),
                }
                if env.in_lambda || env.in_try {
                    lenv::move_and_merge_next_in_cont(env, pos, c::T::Exit)
                } else {
                    lenv::drop_cont(env, c::T::Next)
                }
                aast::Stmt_::Return(Box::new(None))
            }
            Some(e) => {
                crate::typing_return::check_inout_return(pos.clone(), env);
                let crate::typing_env_return_info::T {
                    return_type,
                    return_disposable,
                    return_ignore_readonly,
                } = env::get_return(env);
                let return_type =
                    crate::typing_return::strip_awaitable(env::get_fn_kind(env), env, return_type);
                crate::typing_class_pointers::check_string_coercion_point(env, e, &return_type);
                let expected = Some(expected_ty::make(
                    None,
                    Some(return_ignore_readonly),
                    aast_utils::get_expr_pos(e),
                    Ureason::URreturn,
                    return_type.clone(),
                ));
                if return_disposable {
                    enforce_return_disposable(env, e)
                }
                let (te, rty): (tast::Expr, Ty) = expr::expr(
                    expected.as_ref(),
                    &expr::context::T {
                        is_using_clause: return_disposable,
                        ..ctxt_default()
                    },
                    env,
                    e,
                );
                let rty = env::update_reason(env, rty, |expr| {
                    reason::flow_return_expr(expr, reason::witness(pos.clone()))
                });
                let te = {
                    // `pos` is the position of the expression here.
                    let aast::Expr(ty, pos, e) = te;
                    let ty = env::update_reason(env, ty, |expr| {
                        reason::flow_return_expr(expr, reason::witness(pos.clone()))
                    });
                    aast::Expr(ty, pos, e)
                };
                // This is a unify_error rather than a return_type_mismatch because the return
                // statement is the problem, not the return type itself.
                let ty_err_opt = crate::typing_coercion::coerce_type(
                    None,
                    None,
                    Some(return_ignore_readonly),
                    aast_utils::get_expr_pos(e),
                    Ureason::URreturn,
                    env,
                    rty.clone(),
                    return_type.clone(),
                    Enforcement::Enforced, // TODO akenn: flow in
                    callback::unify_error(),
                );
                if let Some(err) = &ty_err_opt {
                    typing_error_utils::add_typing_error(err, env)
                }
                let ty_mismatch_opt = mk_ty_mismatch_opt(rty, return_type, ty_err_opt.as_ref());
                if env.in_lambda || env.in_try {
                    lenv::move_and_merge_next_in_cont(env, pos, c::T::Exit)
                } else {
                    lenv::drop_cont(env, c::T::Next)
                }
                aast::Stmt_::Return(Box::new(Some(hole_on_ty_mismatch(te, ty_mismatch_opt))))
            }
        },
        aast::Stmt_::Do(do_) => {
            let (b, aast::LoopCond(_, _, e)) = &**do_;
            // NOTE: leaks scope as currently implemented; this matches
            // the behavior in naming (cf. `do_stmt` in naming/naming.ml).
            let (tb, te) = lenv::stash_and_do(
                env,
                &[c::T::Continue, c::T::Break, c::T::Do],
                |env: &mut Env| {
                    lenv::save_and_merge_next_in_cont(env, pos, c::T::Do);
                    let _ = block(env, &b.0);
                    // saving the locals in continue here even if there is no continue
                    // statement because they must be merged at the end of the loop, in
                    // case there is no iteration
                    lenv::save_and_merge_next_in_cont(env, pos, c::T::Continue);
                    let tb = infer_loop(env, pos, st, |env: &mut Env| {
                        lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                        // The following is necessary in case there is an assignment in the
                        // expression
                        let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
                        expr::condition(env, true, &te);
                        lenv::update_next_from_conts(env, pos, &[c::T::Do, c::T::Next]);
                        let tb = block(env, &b.0);
                        tb
                    });
                    lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                    let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
                    let aast::Expr(cond_ty, cond_pos, _) = &te;
                    check_bool_for_condition(env, cond_pos, cond_ty.clone());
                    expr::condition(env, false, &te);
                    lenv::update_next_from_conts(env, pos, &[c::T::Break, c::T::Next]);
                    (tb, te)
                },
            );
            aast::Stmt_::Do(Box::new((aast::Block(tb), aast::LoopCond(None, None, te))))
        }
        aast::Stmt_::While(while_) => {
            let (aast::LoopCond(_, _, e), b) = &**while_;
            let (te, tb) =
                lenv::stash_and_do(env, &[c::T::Continue, c::T::Break], |env: &mut Env| {
                    lenv::save_and_merge_next_in_cont(env, pos, c::T::Continue);
                    let tb = infer_loop(env, pos, st, |env: &mut Env| {
                        lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                        // The following is necessary in case there is an assignment in the
                        // expression
                        let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
                        expr::condition(env, true, &te);
                        // TODO TAST: avoid repeated generation of block
                        block(env, &b.0)
                    });
                    lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                    let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
                    let aast::Expr(cond_ty, cond_pos, _) = &te;
                    check_bool_for_condition(env, cond_pos, cond_ty.clone());
                    expr::condition(env, false, &te);
                    lenv::update_next_from_conts(env, pos, &[c::T::Break, c::T::Next]);
                    (te, tb)
                });
            aast::Stmt_::While(Box::new((aast::LoopCond(None, None, te), aast::Block(tb))))
        }
        aast::Stmt_::Using(using) => {
            let aast::UsingStmt {
                has_await,
                exprs: (loc, using_clause),
                block: using_block,
                is_block_scoped: us_is_block_scoped,
            } = &**using;
            let (typed_using_clause, using_vars): (Vec<tast::Expr>, Vec<LocalId>) =
                crate::typing::using_stmt::check_using_clause(env, *has_await, using_clause);
            let typed_using_block = block(env, &using_block.0);
            // Remove any using variables from the environment, as they should not
            // be in scope outside the block
            for using_var in &using_vars {
                env::unset_local(env, using_var)
            }
            aast::Stmt_::Using(Box::new(aast::UsingStmt {
                has_await: *has_await,
                exprs: (loc.clone(), typed_using_clause),
                block: aast::Block(typed_using_block),
                is_block_scoped: *us_is_block_scoped,
            }))
        }
        aast::Stmt_::For(for_) => {
            let (e1, e2, aast::LoopIter(_, _, e3), b) = &**for_;
            let e2_true;
            let e2: &nast::Expr = match e2 {
                Some(aast::LoopCond(_, _, e2)) => e2,
                None => {
                    e2_true = aast::Expr((), Pos::NONE, aast::Expr_::True);
                    &e2_true
                }
            };
            let (te1, te2, te3, tb) =
                lenv::stash_and_do(env, &[c::T::Continue, c::T::Break], |env: &mut Env| {
                    // For loops leak their initializer, but nothing that's defined in the
                    // body
                    let (te1, _): (Vec<tast::Expr>, Vec<Ty>) =
                        expr::infer_exprs(e1, &ctxt_default(), env);
                    // initializer
                    lenv::save_and_merge_next_in_cont(env, pos, c::T::Continue);
                    let (tb, te3) = infer_loop(env, pos, st, |env: &mut Env| {
                        // The following is necessary in case there is an assignment in the
                        // expression
                        let (te2, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e2);
                        expr::condition(env, true, &te2);
                        // Env.with_packages env pkgs @@ fun env ->
                        let tb = block(env, &b.0);
                        lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                        let (te3, _): (Vec<tast::Expr>, Vec<Ty>) =
                            expr::infer_exprs(e3, &ctxt_default(), env);
                        (tb, te3)
                    });
                    lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                    let (te2, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e2);
                    let aast::Expr(cond_ty, cond_pos, _) = &te2;
                    check_bool_for_condition(env, cond_pos, cond_ty.clone());
                    expr::condition(env, false, &te2);
                    lenv::update_next_from_conts(env, pos, &[c::T::Break, c::T::Next]);
                    (te1, te2, te3, tb)
                });
            aast::Stmt_::For(Box::new((
                te1,
                Some(aast::LoopCond(None, None, te2)),
                aast::LoopIter(None, None, te3),
                aast::Block(tb),
            )))
        }
        aast::Stmt_::Switch(switch) => {
            let (e, cl, dfl) = &**switch;
            // `Switch (((_, pos, _) as e), cl, dfl)`: from here on `pos` is the
            // position of the expression switched on.
            let pos = &e.1;
            let (te, ty): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
            // NB: A 'continue' inside a 'switch' block is equivalent to a 'break'.
            // See the note in
            // http://php.net/manual/en/control-structures.continue.php
            let (te, tcl, tdfl) =
                lenv::stash_and_do(env, &[c::T::Continue, c::T::Break], |env: &mut Env| {
                    let parent_locals = lenv::get_all_locals(env);
                    let (tcl, tdfl) = case_list(&parent_locals, ty, env, pos, cl, dfl.as_ref());
                    lenv::update_next_from_conts(
                        env,
                        pos,
                        &[c::T::Continue, c::T::Break, c::T::Next],
                    );
                    (te, tcl, tdfl)
                });
            aast::Stmt_::Switch(Box::new((te, tcl, tdfl)))
        }
        aast::Stmt_::Match(match_) => {
            let aast::StmtMatch {
                expr: sm_expr,
                arms: sm_arms,
            } = &**match_;
            let (te, ty): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, sm_expr);
            let local_opt = make_a_local_of(true, env, sm_expr);
            let tal = {
                let match_arms = |env: &mut Env, lid: &aast::Lid| {
                    stmt_match_arm_list(pos, lid, ty.clone(), env, sm_arms)
                };
                match local_opt {
                    None => {
                        // If we are matching on an expr that isn't a local, we create a temporary local
                        let local_id = crate::local_id::tmp();
                        let aast::Expr(_, pos, _) = sm_expr;
                        env::set_local(None, None, env, local_id.clone(), ty.clone(), pos.clone());
                        let tal = match_arms(env, &aast::Lid(sm_expr.1.clone(), local_id.clone()));
                        env::unset_local(env, &local_id);
                        tal
                    }
                    Some(lid) => {
                        let tal = match_arms(env, &lid);
                        let local = env::get_local(env, &lid.1);
                        let new_ty = env::expand_type(env, local.ty.clone());
                        // TODO: remove this dirty hack after D50270756 lands
                        if is_union(&new_ty) {
                            set_local(None, env, lid, ty.clone())
                        }
                        tal
                    }
                }
            };
            aast::Stmt_::Match(Box::new(aast::StmtMatch {
                expr: te,
                arms: tal,
            }))
        }
        aast::Stmt_::Foreach(foreach) => {
            let (e1, e2, b) = &**foreach;
            // It's safe to do foreach over a disposable, as no leaking is possible
            let (te1, ty1): (tast::Expr, Ty) = expr::expr(
                None,
                &expr::context::T {
                    accept_using_var: true,
                    ..ctxt_default()
                },
                env,
                e1,
            );
            let (te1, te2, tb) =
                lenv::stash_and_do(env, &[c::T::Continue, c::T::Break], |env: &mut Env| {
                    lenv::save_and_merge_next_in_cont(env, pos, c::T::Continue);
                    let p1 = &e1.1;
                    let (ty_err_opt, tk, tv, ty_mismatch_opt) = as_expr(env, &ty1, p1, e2);
                    if let Some(err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    let (te2, tb) = infer_loop(env, pos, st, |env: &mut Env| {
                        lenv::update_next_from_conts(env, pos, &[c::T::Continue, c::T::Next]);
                        let te2 = crate::typing::as_expr::bind_as_expr(env, p1, &tk, &tv, e2);
                        let tb = block(env, &b.0);
                        (te2, tb)
                    });
                    lenv::update_next_from_conts(
                        env,
                        pos,
                        &[c::T::Continue, c::T::Break, c::T::Next],
                    );
                    (hole_on_ty_mismatch(te1, ty_mismatch_opt), te2, tb)
                });
            aast::Stmt_::Foreach(Box::new((te1, te2, aast::Block(tb))))
        }
        aast::Stmt_::Try(try_) => {
            let (tb, cl, fb) = &**try_;
            let (ttb, tcl, tfb) = try_catch(pos, env, &tb.0, cl, &fb.0);
            aast::Stmt_::Try(Box::new((aast::Block(ttb), tcl, aast::FinallyBlock(tfb))))
        }
        aast::Stmt_::Concurrent(b) => {
            let check_expr_rhs = |env: &mut Env, s: &nast::Stmt| -> Option<(tast::Expr, Ty)> {
                // `(_pos, (Expr ((), _, Assign (_, _, e)) | Expr (((), _, _) as e)))`
                match s {
                    aast::Stmt(_pos, aast::Stmt_::Expr(e)) => {
                        let e: &nast::Expr = match &**e {
                            aast::Expr((), _, aast::Expr_::Assign(assign)) => &assign.2,
                            e => e,
                        };
                        let (te, ty): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
                        Some((te, ty))
                    }
                    _ => None,
                }
            };
            let check_assign =
                |env: &mut Env, (s, te_ty_opt): (&nast::Stmt, Option<(tast::Expr, Ty)>)| {
                    let aast::Stmt(pos, s_) = s;
                    match s_ {
                        aast::Stmt_::Expr(outer) => match &**outer {
                            aast::Expr((), _, aast::Expr_::Assign(assign)) => {
                                let (lhs, op, _) = &**assign;
                                match te_ty_opt {
                                    Some((te, ty)) => {
                                        let (te, _ty): (tast::Expr, Ty) =
                                            crate::typing::binop::check_assign(
                                                true,
                                                None,
                                                env,
                                                outer,
                                                pos,
                                                *op,
                                                lhs,
                                                Either::Right((te, ty)),
                                            );
                                        aast::Stmt(pos.clone(), aast::Stmt_::Expr(Box::new(te)))
                                    }
                                    None => {
                                        diagnostics_state::internal_error(
                                            pos.clone(),
                                            "Missing type while checking Concurrent",
                                        );
                                        stmt(env, s)
                                    }
                                }
                            }
                            _e => match te_ty_opt {
                                Some((te, _ty)) => {
                                    aast::Stmt(pos.clone(), aast::Stmt_::Expr(Box::new(te)))
                                }
                                None => {
                                    diagnostics_state::internal_error(
                                        pos.clone(),
                                        "Missing type while checking Concurrent",
                                    );
                                    stmt(env, s)
                                }
                            },
                        },
                        _ => stmt(env, s),
                    }
                };
            might_throw(pos, env);
            let te_tyl: Vec<Option<(tast::Expr, Ty)>> =
                b.0.iter().map(|s| check_expr_rhs(env, s)).collect();
            // `List.zip_exn b te_tyl`: both have one element per statement.
            let b: Vec<tast::Stmt> =
                b.0.iter()
                    .zip(te_tyl)
                    .map(|s_te_ty_opt| check_assign(env, s_te_ty_opt))
                    .collect();
            aast::Stmt_::Concurrent(aast::Block(b))
        }
        aast::Stmt_::Throw(e) => {
            let aast::Expr(_, p, _) = &**e;
            let (te, ty): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
            let ty_err_opt = coerce_to_throwable(p, env, ty);
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
            move_and_merge_next_in_catch(pos, env);
            aast::Stmt_::Throw(Box::new(te))
        }
        aast::Stmt_::Continue => {
            lenv::move_and_merge_next_in_cont(env, pos, c::T::Continue);
            aast::Stmt_::Continue
        }
        aast::Stmt_::Break => {
            lenv::move_and_merge_next_in_cont(env, pos, c::T::Break);
            aast::Stmt_::Break
        }
        aast::Stmt_::Awaitall(_) | aast::Stmt_::Block(_) | aast::Stmt_::Markup(_) => {
            let msg = "Unexpected nodes in AST. These nodes should have been removed in naming. "
                .to_string()
                + &crate::pos::string_no_file(pos);
            panic!("{}", msg)
        }
    };
    let ty_err_opt = crate::typing_solver::close_tyvars_and_solve(env);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    res
}

/// The locals of all the continuations after checking the finally block
/// `fb` against continuation `ctx` alone.
pub(crate) fn finally_w_cont(
    fb: &[nast::Stmt],
    env: &mut Env,
    ctx: PerContEntry,
) -> typing_per_cont_env::T {
    // The only locals in scope are the ones from the current continuation
    env::env_with_locals(env, typing_per_cont_env::T::unit(c::T::Next, ctx));
    let _tfb = block(env, fb);
    lenv::get_all_locals(env)
}

pub(crate) fn finally(join_pos: &Pos, env: &mut Env, fb: &[nast::Stmt]) -> Vec<tast::Stmt> {
    match fb {
        [] => {
            lenv::update_next_from_conts(env, join_pos, &[c::T::Next, c::T::Finally]);
            vec![]
        }
        _ => {
            let initial_locals = lenv::get_all_locals(env);
            // First typecheck the finally block against all relevant continuations merged
            // together. The relevant continuations are those corresponding to statements
            // which will cause control flow to jump to the finally block, e.g. `break`.
            // During this phase, record errors found in the finally block, but discard
            // the resulting environment.
            lenv::update_next_from_conts(
                env,
                join_pos,
                &typing_per_cont_env::continuations_for_finally(),
            );
            let tfb = block(env, fb);
            env::env_with_locals(env, initial_locals.clone());
            // Second, typecheck the finally block once against each continuation. This
            // helps be more clever about what each continuation will be after the
            // finally block.
            // We don't want to record errors during this phase, because certain types
            // of errors will fire wrongly. For example, if $x is nullable in some
            // continuations but not in others, then we must use `?->` on $x, but an
            // error will fire when typechecking the finally block againts continuations
            // where $x is non-null.
            let locals_map = diagnostics_state::ignore_(|| {
                wrapped_map::map_env(
                    |env: &mut Env, _key: &c::T, ctx: &PerContEntry| {
                        finally_w_cont(fb, env, ctx.clone())
                    },
                    env,
                    &initial_locals,
                )
            });
            let union = |env: &mut Env,
                         _key: c::T,
                         ctxopt1: Option<PerContEntry>,
                         ctxopt2: Option<PerContEntry>| {
                lenv::union_contextopts(join_pos, env, ctxopt1, ctxopt2)
            };
            let locals = crate::typing_try::finally_merge(union, env, &locals_map);
            env::env_with_locals(env, locals);
            tfb
        }
    }
}

pub(crate) fn try_catch(
    join_pos: &Pos,
    env: &mut Env,
    tb: &[nast::Stmt],
    cl: &[nast::Catch],
    fb: &[nast::Stmt],
) -> (
    Vec<tast::Stmt>,
    Vec<aast::Catch<Ty, tast::SavedEnv>>,
    Vec<tast::Stmt>,
) {
    let parent_locals = lenv::get_all_locals(env);
    // If any `break`, `continue`, `exit`, etc. happens directly inside the `try`
    // block, they will cause control flow to go to the `finally` block first.
    // I.o.w. the `finally` block is typechecked with the corresponding continuations.
    // Therefore we need to stash the corresponding pre-existing continuations
    // so that we don't typecheck the finally block with those.
    lenv::drop_conts(env, &typing_per_cont_env::continuations_for_finally());
    let (ttb, tcb) = env::in_try(env, |env: &mut Env| {
        let ttb = block(env, tb);
        lenv::move_and_merge_next_in_cont(env, join_pos, c::T::Finally);
        let catchctx = lenv::get_cont_option(env, c::T::Catch);
        let lenvtcblist: Vec<(LocalEnv, aast::Catch<Ty, tast::SavedEnv>)> =
            cl.iter().map(|c| catch(catchctx.clone(), env, c)).collect();
        let (lenvl, tcb): (Vec<LocalEnv>, Vec<aast::Catch<Ty, tast::SavedEnv>>) =
            lenvtcblist.into_iter().unzip();
        let parent_lenv = env.lenv.clone();
        lenv::union_lenv_list(env, join_pos, &parent_lenv, &lenvl);
        lenv::move_and_merge_next_in_cont(env, join_pos, c::T::Finally);
        (ttb, tcb)
    });
    let tfb = finally(join_pos, env, fb);
    lenv::update_next_from_conts(env, join_pos, &[c::T::Finally]);
    lenv::drop_cont(env, c::T::Finally);
    lenv::restore_and_merge_conts_from(
        env,
        join_pos,
        &parent_locals,
        &typing_per_cont_env::continuations_for_finally(),
    );
    (ttb, tcb, tfb)
}

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::NastCheck(err))
    {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

pub(crate) fn case_list(
    parent_locals: &typing_per_cont_env::T,
    ty: Ty,
    env: &mut Env,
    switch_pos: &Pos,
    cl: &[nast::Case],
    dfl: Option<&nast::DefaultCase>,
) -> (
    Vec<aast::Case<Ty, tast::SavedEnv>>,
    Option<aast::DefaultCase<Ty, tast::SavedEnv>>,
) {
    let initialize_next_cont = |env: &mut Env| {
        lenv::restore_conts_from(env, parent_locals, &[c::T::Next]);
        lenv::update_next_from_conts(env, switch_pos, &[c::T::Next, c::T::Fallthrough]);
        lenv::drop_cont(env, c::T::Fallthrough)
    };
    let check_fallthrough = |env: &Env,
                             switch_pos: &Pos,
                             case_pos: &Pos,
                             next_pos: Option<Pos>,
                             block: &[nast::Stmt],
                             last: bool,
                             is_default: bool| {
        if !block.is_empty() && !last {
            match lenv::get_cont_option(env, c::T::Next) {
                Some(_) => add_nast_check_error(if is_default {
                    NastCheckError::DefaultFallthrough(switch_pos.clone())
                } else {
                    NastCheckError::CaseFallthrough {
                        switch_pos: switch_pos.clone(),
                        case_pos: case_pos.clone(),
                        next_pos,
                    }
                }),
                None => {}
            }
        }
    };
    {
        // below, we try to find out if the switch is exhaustive
        let has_default = dfl.is_some();
        let (ty_err_opt, ty) =
            // If it hasn't got a default clause then we need to solve type variables
            // in order to check for an enum
            if has_default {
                let ty = env::expand_type(env, ty);
                (None, ty)
            } else {
                crate::typing_solver::expand_type_and_solve(
                    env,
                    None,
                    "a value",
                    switch_pos.clone(),
                    ty,
                )
            };
        if let Some(err) = &ty_err_opt {
            typing_error_utils::add_typing_error(err, env)
        }
        // leverage that enums are checked for exhaustivity
        let is_enum = {
            let top_type = make_type::class_type(
                reason::none(),
                sn::classes::HH_BUILTIN_ENUM.to_string(),
                vec![make_type::mixed(reason::none())],
            );
            sub_type::is_sub_type_for_union(env, &ty, &top_type)
        };
        // register that the runtime may throw in case we cannot prove
        // that the switch is exhaustive
        if !(has_default || is_enum) {
            might_throw(switch_pos, env)
        }
    }
    let tcl = {
        // `let rec case_list env = function ...`
        let mut tcl: Vec<aast::Case<Ty, tast::SavedEnv>> = vec![];
        for (i, aast::Case(e, b)) in cl.iter().enumerate() {
            let rl = &cl[i + 1..];
            let aast::Expr(_, pos, _) = e;
            initialize_next_cont(env);
            let (te, _): (tast::Expr, Ty) = expr::expr(None, &ctxt_default(), env, e);
            let tb = block(env, &b.0);
            let last = rl.is_empty() && dfl.is_none();
            let next_pos = match rl {
                [aast::Case(aast::Expr(_, next_pos, _), _), ..] => Some(next_pos.clone()),
                [] => None,
            };
            check_fallthrough(env, switch_pos, pos, next_pos, &b.0, last, false);
            tcl.push(aast::Case(te, aast::Block(tb)))
        }
        tcl
    };
    let tdfl = match dfl {
        None => None,
        Some(aast::DefaultCase(pos, b)) => {
            initialize_next_cont(env);
            let tb = block(env, &b.0);
            check_fallthrough(env, switch_pos, pos, None, &b.0, true, true);
            Some(aast::DefaultCase(pos.clone(), aast::Block(tb)))
        }
    };
    (tcl, tdfl)
}

/// The types that `match` does not support in `ty`, consed onto `acc` as
/// the OCaml does (`find_unsupported_tys`, local to `stmt_match_arm_list`):
/// `acc` holds the OCaml list in reverse (its head last).
fn find_unsupported_tys(env: &mut Env, mut acc: Vec<Ty>, ty: Ty) -> Vec<Ty> {
    let ty = env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tprim(
            aast::Tprim::Tnull
            | aast::Tprim::Tbool
            | aast::Tprim::Tint
            | aast::Tprim::Tfloat
            | aast::Tprim::Tnum
            | aast::Tprim::Tarraykey,
        ) => acc,
        Ty_::Tdynamic(_) => acc,
        // `SN.Classes.cString`
        Ty_::Tclass((_, id), _, _) if id == sn::typehints::HH_STRING => acc,
        Ty_::Tunion(tyl) => {
            for ty in tyl {
                acc = find_unsupported_tys(env, acc, ty.clone())
            }
            acc
        }
        Ty_::Tnewtype(name, _, _) => match env::get_typedef(env, name) {
            // `Decl_entry.Found { td_type_assignment = CaseType (variant, variants); _ }`
            decl_entry::T::Found(td) => match &td.type_assignment {
                ty::decl::ty::TypedefTypeAssignment::CaseType(variant, variants) => {
                    // Conservatively ban case types with where clauses for now;
                    // implement handling later
                    if std::iter::once(variant)
                        .chain(variants.iter())
                        .all(|v| v.where_constraints.is_empty())
                    {
                        acc
                    } else {
                        acc.push(ty.clone());
                        acc
                    }
                }
                ty::decl::ty::TypedefTypeAssignment::SimpleTypeDef(_, _) => {
                    acc.push(ty.clone());
                    acc
                }
            },
            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
                acc.push(ty.clone());
                acc
            }
        },
        _ => {
            acc.push(ty.clone());
            acc
        }
    }
}

/// `refine_for_prev_patterns`, local to `stmt_match_arm_list`: `expr_ty`
/// refined by the negation of each previous pattern. `prev_patterns` is the
/// OCaml list, the most recent pattern first.
fn refine_for_prev_patterns(
    env: &mut Env,
    locl_var: &aast::Lid,
    expr_ty: &Ty,
    prev_patterns: &[&aast::Pattern],
) -> Ty {
    // `List.fold_left_env env prev_patterns ~init:expr_ty`
    let mut ty = expr_ty.clone();
    for pattern in prev_patterns {
        // `refine_for_pattern ~expr_pos:(fst locl_var)`
        let refined_ty = refine_for_pattern(&locl_var.0, env, false, ty.clone(), pattern);
        ty = refined_ty.unwrap_or(ty)
    }
    ty
}

/// `arm_condition`, local to `stmt_match_arm_list`: refines the matched
/// local for the arm with pattern `pat`, and returns the previous patterns
/// for the next arm (the OCaml list, the most recent first).
fn arm_condition<'a>(
    env: &mut Env,
    locl_var: &aast::Lid,
    expr_ty: &Ty,
    prev_patterns: Vec<&'a aast::Pattern>,
    pat: &'a aast::Pattern,
) -> Vec<&'a aast::Pattern> {
    let (refined_ty, next_patterns) = match pat {
        aast::Pattern::PVar(_) => {
            let refined_ty = refine_for_prev_patterns(env, locl_var, expr_ty, &prev_patterns);
            (
                if phys_equal(expr_ty, &refined_ty) {
                    None
                } else {
                    Some(refined_ty)
                },
                // Since we consumed the previous patterns we don't need to include them
                vec![pat],
            )
        }
        _ => {
            // `refine_for_pattern ~expr_pos:(fst locl_var)`
            let refined_ty = refine_for_pattern(&locl_var.0, env, true, expr_ty.clone(), pat);
            // `pat :: prev_patterns`
            let mut next_patterns = vec![pat];
            next_patterns.extend(prev_patterns);
            (refined_ty, next_patterns)
        }
    };
    match refined_ty {
        None => {}
        Some(ty) => set_local(None, env, locl_var.clone(), ty),
    }
    next_patterns
}

pub(crate) fn stmt_match_arm_list(
    pos: &Pos,
    locl_var: &aast::Lid,
    expr_ty: Ty,
    env: &mut Env,
    al: &[nast::StmtMatchArm],
) -> Vec<aast::StmtMatchArm<Ty, tast::SavedEnv>> {
    let has_wildcard = al
        .iter()
        .any(|aast::StmtMatchArm { pat: sma_pat, .. }| match sma_pat {
            aast::Pattern::PVar(_) => true,
            _ => false,
        });
    // We need to solve type variables in order to ensure that the type is one
    // we support in match
    let (ty_err_opt, expr_ty) = if has_wildcard {
        (None, expr_ty)
    } else {
        crate::typing_solver::expand_type_and_solve(env, None, "a value", pos.clone(), expr_ty)
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    // Error if the type is one we don't support. We currently support case types,
    // null, bool, int, float, string, dynamic, and unions thereof.
    let unsupported_tys = {
        let mut unsupported_tys = find_unsupported_tys(env, vec![], expr_ty.clone());
        // The OCaml list: the type found last first.
        unsupported_tys.reverse();
        unsupported_tys
    };
    let ty_was_allowed = unsupported_tys.is_empty();
    if !ty_was_allowed {
        let printing_env = std::rc::Rc::new(env.clone());
        let expr_ty = {
            let env = printing_env.clone();
            let expr_ty = expr_ty.clone();
            Lazy::new(move || typing_print::full_strip_ns(true, &*env, &expr_ty))
        };
        let unsupported_tys: Vec<Lazy<String>> = unsupported_tys
            .into_iter()
            .map(|ty| {
                let env = printing_env.clone();
                Lazy::new(move || typing_print::full_strip_ns(true, &*env, &ty))
            })
            .collect();
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Match_on_unsupported_type {
                pos: pos.clone(),
                expr_ty,
                unsupported_tys,
            }),
            env,
        )
    }
    // `refine_for_pattern ~expr_pos:(fst locl_var)` is applied by the two
    // helpers below, which take `locl_var`.
    let parent_lenv = env.lenv.clone();
    // `let rec branch_arms env ~prev_patterns ~lenvs = function ...`: the arms
    // in order, then the end of the list.
    let mut prev_patterns: Vec<&aast::Pattern> = vec![];
    // `env.lenv :: lenvs`: in the order of the arms here, reversed below.
    let mut lenvs: Vec<LocalEnv> = vec![];
    let mut acc: Vec<aast::StmtMatchArm<Ty, tast::SavedEnv>> = vec![];
    for aast::StmtMatchArm {
        pat: sma_pat,
        body: sma_body,
    } in al
    {
        env.lenv = parent_lenv.clone();
        prev_patterns = arm_condition(env, locl_var, &expr_ty, prev_patterns, sma_pat);
        let sma_body = block(env, &sma_body.0);
        lenvs.push(env.lenv.clone());
        acc.push(aast::StmtMatchArm {
            pat: sma_pat.clone(),
            body: aast::Block(sma_body),
        })
    }
    {
        let ty = refine_for_prev_patterns(env, locl_var, &expr_ty, &prev_patterns);
        // If the type is not one we support in match, we can't usefully check for
        // exhaustiveness and we've already emitted an error, so don't check for
        // exhaustiveness.
        if ty_was_allowed {
            let lnothing = make_type::locl_like(reason::none(), make_type::nothing(reason::none()));
            let ty_not_covered = {
                let env = env.clone();
                let ty = ty.clone();
                Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty))
            };
            let err_opt = sub_type::sub_type_or_fail(
                env,
                ty,
                lnothing,
                Some(typing_error::primary(primary::T::Match_not_exhaustive {
                    pos: pos.clone(),
                    ty_not_covered,
                })),
            );
            if let Some(err) = &err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
        }
        lenvs.reverse();
        lenv::union_lenv_list(env, pos, &parent_lenv, &lenvs);
    }
    acc
}

pub(crate) fn catch(
    catchctx: Option<PerContEntry>,
    env: &mut Env,
    aast::Catch(sid, exn_lvar, b): &nast::Catch,
) -> (LocalEnv, aast::Catch<Ty, tast::SavedEnv>) {
    lenv::replace_cont(env, c::T::Next, catchctx);
    let cid: nast::ClassId_ = aast::ClassId_::CI(sid.clone());
    let ety_p = &sid.0;
    let _: NewableClassInfo =
        crate::typing::class_id::instantiable_cid(None, None, Some(true), ety_p, env, &cid, &[]);
    let (_tal, _te, ety): (Vec<tast::Targ>, tast::ClassId, Ty) =
        crate::typing::class_id::class_expr(
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            Some(true),
            None,
            env,
            &[],
            &aast::ClassId((), ety_p.clone(), cid.clone()),
        );
    let ty_err_opt = coerce_to_throwable(ety_p, env, ety.clone());
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    let aast::Lid(p, x) = exn_lvar;
    set_valid_rvalue(None, p.clone(), env, x.clone(), None, ety);
    let tb = block(env, &b.0);
    (
        env.lenv.clone(),
        aast::Catch(sid.clone(), exn_lvar.clone(), aast::Block(tb)),
    )
}
