// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_infer_type_error.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::infer_error_at_pos_service;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::yojson::safe as yojson;

fn starts_at(pos: &Pos, line: isize, char_start: isize) -> bool {
    let (l, c, _) = crate::pos::info_pos(pos);
    line == l && char_start == c
}

type Acc = Option<(Pos, Env, tast::Ty, tast::Ty)>;

struct Visitor {
    line: isize,
    char: isize,
}

impl<'a> Reducer<'a, IterParams, Acc> for Visitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        None
    }
    /// A node with position P is not always a parent of every other node with
    /// a position contained by P. Some desugaring can cause nodes to be
    /// rearranged so that this is no longer the case (e.g., `invariant`).
    ///
    /// Since we are finding `Hole`s based on their exact starting position,
    /// we _shouldn't_ encounter the case of two simultaneous `Hole`s with
    /// different parents but the logic to handle this is retained - we simply
    /// take the smaller node.
    fn plus(&mut self, lhs: Acc, rhs: Acc) -> Acc {
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                if crate::pos::length(&lhs.0) <= crate::pos::length(&rhs.0) {
                    Some(lhs)
                } else {
                    Some(rhs)
                }
            }
            (lhs, None) => lhs,
            (None, rhs) => rhs,
        }
    }
    aast_reduce::tast::tast_methods!('a, Acc; fun_, method_, class_var, expression_tree);

    /// Find the the `Hole` which exactly starts at the provided position;
    /// if the current hole does not, call method on supertype to continue
    /// recursion
    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Acc {
        if let aast::Expr_::Hole(hole) = expr_ {
            let (aast::Expr(_, pos, _), from_ty, to_ty, hole_source) = &**hole;
            if matches!(hole_source, aast::HoleSource::Typing) && starts_at(pos, self.line, self.char) {
                return Some((pos.clone(), env.clone(), from_ty.clone(), to_ty.clone()));
            }
        }
        aast_reduce::tast::on_expr_(self, env, expr_)
    }
}

pub fn type_error_at_pos(
    ctx: &provider_context::T,
    tast: &[tast::Def],
    line: isize,
    char: isize,
) -> Option<(Env, tast::Ty, tast::Ty)> {
    let mut visitor = Visitor { line, char };
    aast_reduce::tast::go(&mut visitor, ctx, tast).map(|(_, env, actual_ty, expected_ty)| (env, actual_ty, expected_ty))
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    line: isize,
    column: isize,
) -> infer_error_at_pos_service::Result {
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    type_error_at_pos(ctx, &tast.under_normal_assumptions, line, column).map(|(env, from_ty, to_ty)| {
        infer_error_at_pos_service::T {
            actual_ty_string: tast_env::print_ty(&env, &from_ty),
            actual_ty_json: yojson::to_string(&tast_env::ty_to_json(&env, None, &from_ty)),
            expected_ty_string: tast_env::print_ty(&env, &to_ty),
            expected_ty_json: yojson::to_string(&tast_env::ty_to_json(&env, None, &to_ty)),
        }
    })
}
