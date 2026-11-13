// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `truthiness_test.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Uop;
use oxidized::pos::Pos;

use crate::error_codes;
use crate::local_id;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_utils;
use crate::tast_visitor;
use crate::typing_defs_core::get_reason;
use crate::typing_make_type as make_type;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_warning;
use crate::typing_warning::truthiness_test::Kind;
use crate::typing_warning::truthiness_test::SketchyKind;
use crate::typing_warning_utils;
use crate::utils;

#[allow(non_upper_case_globals)]
pub const warning_kind: typing_warning::Kind<
    typing_warning::truthiness_test::T,
    typing_warning::Migrated,
> = typing_warning::Kind::Truthiness_test;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

pub fn get_lvar_name(e: &tast::Expr_) -> Option<String> {
    match e {
        aast::Expr_::Lvar(lid) => {
            let aast::Lid(_, id) = &**lid;
            Some(local_id::get_name(id).to_string())
        }
        _ => None,
    }
}

pub fn add_warning(
    env: &Env,
    as_lint: bool,
    pos: &Pos,
    kind: Kind,
    ty: String,
    e: &tast::Expr_,
    not: bool,
) {
    typing_warning_utils::add_for_migration(
        &tast_env::get_tcopt(env),
        if as_lint { Some(None) } else { None },
        (
            pos.clone(),
            typing_warning::Kind::Truthiness_test,
            typing_warning::truthiness_test::T {
                kind,
                ty,
                expr: get_lvar_name(e),
                not,
            },
        ),
    )
}

pub fn is_like_null(env: &Env, ty: &tast::Ty) -> bool {
    tast_env::is_sub_type(
        env,
        ty,
        &make_type::locl_like(
            typing_reason::none(),
            make_type::null(typing_reason::none()),
        ),
    )
}

pub fn truthiness_test(env: &Env, as_lint: bool, te: &tast::Expr, not: bool) {
    let aast::Expr(ty, p, e) = te;
    let prim_to_string = |prim| {
        tast_env::print_error_ty(
            None,
            env,
            &make_type::prim_type(get_reason(ty).clone(), prim),
        )
    };
    let ty = {
        // We don't strip the like if is ~null because this leads to false positives
        // in the truthiness warning. Specifically like null frequently arises through
        // calling `idx` on `dynamic` typed data.
        if is_like_null(env, ty) {
            ty.clone()
        } else {
            tast_env::strip_dynamic(env, ty.clone())
        }
    };
    for sketchy in tast_utils::find_sketchy_types(env, &ty) {
        match sketchy {
            tast_utils::SketchyTypeKind::String => {
                let tystr = typing_print::strip_ns(C_STRING);
                add_warning(
                    env,
                    as_lint,
                    p,
                    Kind::Sketchy(SketchyKind::String),
                    "a ".to_string() + &tystr,
                    e,
                    not,
                )
            }
            tast_utils::SketchyTypeKind::Arraykey => {
                let tystr = prim_to_string(aast::Tprim::Tarraykey);
                add_warning(
                    env,
                    as_lint,
                    p,
                    Kind::Sketchy(SketchyKind::Arraykey),
                    tystr,
                    e,
                    not,
                )
            }
            tast_utils::SketchyTypeKind::Stringish => {
                let tystr = utils::strip_ns(sn::classes::STRINGISH);
                add_warning(
                    env,
                    as_lint,
                    p,
                    Kind::Sketchy(SketchyKind::Stringish),
                    tystr.to_string(),
                    e,
                    not,
                )
            }
            tast_utils::SketchyTypeKind::XHPChild => {
                let tystr = utils::strip_ns(sn::classes::XHP_CHILD);
                add_warning(
                    env,
                    as_lint,
                    p,
                    Kind::Sketchy(SketchyKind::Xhp_child),
                    tystr.to_string(),
                    e,
                    not,
                )
            }
            tast_utils::SketchyTypeKind::TraversableInterface(tystr) => add_warning(
                env,
                as_lint,
                p,
                Kind::Sketchy(SketchyKind::Traversable),
                tystr,
                e,
                not,
            ),
        }
    }
    match tast_utils::truthiness(env, &ty) {
        tast_utils::Truthiness::AlwaysTruthy => add_warning(
            env,
            as_lint,
            p,
            Kind::Invalid { truthy: true },
            tast_env::print_ty(env, &ty),
            e,
            not,
        ),
        tast_utils::Truthiness::AlwaysFalsy => add_warning(
            env,
            as_lint,
            p,
            Kind::Invalid { truthy: false },
            tast_env::print_ty(env, &ty),
            e,
            not,
        ),
        tast_utils::Truthiness::PossiblyFalsy | tast_utils::Truthiness::Unknown => {}
    }
}

/// `SN.Classes.cString`
const C_STRING: &str = "\\HH\\string";

struct Handler {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let as_lint = self.as_lint;
        let aast::Expr(_, _, x) = e;
        match x {
            aast::Expr_::Unop(unop) if matches!(unop.0, Uop::Unot) => {
                truthiness_test(env, as_lint, &unop.1, true)
            }
            aast::Expr_::Eif(eif) => truthiness_test(env, as_lint, &eif.0, false),
            aast::Expr_::Binop(binop) if matches!(binop.bop, Bop::Ampamp | Bop::Barbar) => {
                let aast::Binop { lhs: e1, rhs: e2, .. } = &**binop;
                truthiness_test(env, as_lint, e1, false);
                truthiness_test(env, as_lint, e2, false)
            }
            _ => {}
        }
    }

    fn at_stmt(&mut self, env: &Env, x: &'a tast::Stmt) {
        let as_lint = self.as_lint;
        match &x.1 {
            aast::Stmt_::If(if_) => truthiness_test(env, as_lint, &if_.0, false),
            aast::Stmt_::Do(do_) => {
                let (_, aast::LoopCond(_, _, e)) = &**do_;
                truthiness_test(env, as_lint, e, false)
            }
            aast::Stmt_::While(while_) => {
                let (aast::LoopCond(_, _, e), _) = &**while_;
                truthiness_test(env, as_lint, e, false)
            }
            aast::Stmt_::For(for_) => match &for_.1 {
                Some(aast::LoopCond(_, _, e)) => truthiness_test(env, as_lint, e, false),
                None => {}
            },
            _ => {}
        }
    }
}

pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler { as_lint })
}
