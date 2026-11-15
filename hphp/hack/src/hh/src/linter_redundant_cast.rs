// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_redundant_cast.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::Tprim;

use crate::naming_special_names::classes::C_STRING;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
/// `module T = Typing_defs`
use crate::typing_defs as t;

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match &e.2 {
            aast::Expr_::Cast(cast) => {
                let pos = e.1;
                let (hint, aast::Expr(expr_ty, expr_pos, expr)) = &**cast;
                // This check is implemented with pattern matching rather than
                // subtyping because I don't want to accidentally error on unlawfully
                // typed code (e.g., on TAnys). Luckily there are only four
                // combinations to consider.
                let mut env = env.clone();
                let expr_ty = tast_env::expand_type(&mut env, expr_ty.clone());
                let env = &env;
                let check = || {
                    let cast = format!(
                        "({})",
                        crate::typing_print::full(true, tast_env::eq_typing_env(env), &expr_ty)
                    );
                    let check_status = tast_env::get_check_status(env);
                    let can_be_captured = crate::aast_utils::can_be_captured(expr);
                    crate::lints_diagnostics::redundant_cast(
                        can_be_captured,
                        check_status,
                        &cast,
                        pos,
                        *expr_pos,
                    )
                };
                match (t::get_node(&expr_ty), &*hint.1) {
                    (t::Ty_::Tprim(expr_prim), aast::Hint_::Hprim(hint_prim)) => {
                        match (expr_prim, hint_prim) {
                            (Tprim::Tint, Tprim::Tint)
                            | (Tprim::Tbool, Tprim::Tbool)
                            | (Tprim::Tfloat, Tprim::Tfloat) => check(),
                            _ => {}
                        }
                    }
                    (t::Ty_::Tclass(id1, _, _), aast::Hint_::Happly(id2, _))
                        if C_STRING == id1.1 && C_STRING == id2.1 =>
                    {
                        check()
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
