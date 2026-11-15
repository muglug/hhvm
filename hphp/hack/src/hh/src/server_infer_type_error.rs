// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_infer_type_error.ml`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::infer_error_at_pos_service;
use crate::pos as pos_;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::yojson;

fn starts_at(pos: &Pos, line: isize, char_start: isize) -> bool {
    let (l, c, _) = pos_::info_pos(pos);
    line == l && char_start == c
}

type Found = Option<(Pos, Env, tast::Ty, tast::Ty)>;

struct Visitor {
    line: isize,
    char: isize,
    acc: Found,
}

impl<'a> Reduce<'a> for Visitor {
    type Acc = Found;

    fn zero(&self) -> Found {
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
    fn plus(&self, lhs: Found, rhs: Found) -> Found {
        match (lhs, rhs) {
            (Some(lhs), Some(rhs)) => {
                if pos_::length(&lhs.0) <= pos_::length(&rhs.0) {
                    Some(lhs)
                } else {
                    Some(rhs)
                }
            }
            (Some(x), None) | (None, Some(x)) => Some(x),
            (None, None) => None,
        }
    }

    fn acc(&mut self) -> &mut Found {
        &mut self.acc
    }
}

impl<'a> aast_visitor::Visitor<'a> for Visitor {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; fun_, method_, class_var, expression_tree);

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            // Find the the `Hole` which exactly starts at the provided position;
            // if the current hole does not, call method on supertype to continue
            // recursion
            aast::Expr_::Hole(h) => {
                let (expr, from_ty, to_ty, hole_source) = &**h;
                match (expr, hole_source) {
                    (aast::Expr(_, pos, _), aast::HoleSource::Typing) if starts_at(pos, self.line, self.char) => {
                        let r = Some((pos.clone(), env.clone(), from_ty.clone(), to_ty.clone()));
                        reduce::add(self, r);
                        Ok(())
                    }
                    _ => tast_visitor::reduce::on_expr_(self, env, expr_),
                }
            }
            _ => tast_visitor::reduce::on_expr_(self, env, expr_),
        }
    }
}

pub fn type_error_at_pos(
    ctx: &Arc<Ctx>,
    tast: &tast::Program,
    line: isize,
    char: isize,
) -> Option<(Env, tast::Ty, tast::Ty)> {
    let mut v = Visitor {
        line,
        char,
        acc: None,
    };
    reduce::go(&mut v, ctx, tast).map(|(_, env, actual_ty, expected_ty)| (env, actual_ty, expected_ty))
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    line: isize,
    column: isize,
) -> infer_error_at_pos_service::Result {
    let tast_provider::ComputeTast { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    type_error_at_pos(ctx, &tast.under_normal_assumptions, line, column).map(|(env, from_ty, to_ty)| {
        infer_error_at_pos_service::T {
            actual_ty_string: tast_env::print_ty(&env, &from_ty),
            actual_ty_json: yojson::safe::to_string(&tast_env::ty_to_json(&env, None, &from_ty)),
            expected_ty_string: tast_env::print_ty(&env, &to_ty),
            expected_ty_json: yojson::safe::to_string(&tast_env::ty_to_json(&env, None, &to_ty)),
        }
    })
}
