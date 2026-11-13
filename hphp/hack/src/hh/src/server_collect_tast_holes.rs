// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_collect_tast_holes.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::pos::Pos;
use crate::provider_context;
use crate::server_command_types::tast_hole::Filter;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_holes_service;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::yojson::safe as yojson;

type Set = tast_holes_service::set::T;

fn mk_result(env: &Env, pos: &Pos, ty_actual: &tast::Ty, ty_expected: &tast::Ty) -> Set {
    Set::from([tast_holes_service::T {
        actual_ty_string: tast_env::print_ty(env, ty_actual),
        actual_ty_json: yojson::to_string(&tast_env::ty_to_json(env, Some(true), ty_actual)),
        expected_ty_string: tast_env::print_ty(env, ty_expected),
        expected_ty_json: yojson::to_string(&tast_env::ty_to_json(env, Some(true), ty_expected)),
        pos: pos.clone(),
    }])
}

fn filter_source(hole_filter: Filter, src: &aast::HoleSource) -> bool {
    match (hole_filter, src) {
        (Filter::Any, _) => true,
        (Filter::Typing, aast::HoleSource::Typing) => true,
        (Filter::Cast, aast::HoleSource::UnsafeCast(_) | aast::HoleSource::EnforcedCast(_)) => true,
        _ => false,
    }
}

struct Visitor {
    hole_filter: Filter,
}

impl<'a> Reducer<'a, IterParams, Set> for Visitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Set> {
        self
    }
    fn zero(&mut self) -> Set {
        Set::new()
    }
    fn plus(&mut self, mut t1: Set, t2: Set) -> Set {
        t1.extend(t2);
        t1
    }
    aast_reduce::tast::tast_methods!('a, Set; fun_, method_, class_var, expression_tree);

    /// `on_Hole` (and the `on_expr_` of `Tast_visitor.reduce`)
    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Set {
        let acc = aast_reduce::tast::on_expr_(self, env, expr_);
        match expr_ {
            aast::Expr_::Hole(hole) => {
                let (aast::Expr(_, pos, _), from_ty, to_ty, src) = &**hole;
                if filter_source(self.hole_filter, src) {
                    let r = mk_result(env, pos, from_ty, to_ty);
                    self.plus(acc, r)
                } else {
                    acc
                }
            }
            _ => acc,
        }
    }
}

pub fn tast_holes(ctx: &provider_context::T, tast: &[tast::Def], hole_src_opt: Filter) -> Vec<tast_holes_service::T> {
    let mut visitor = Visitor {
        hole_filter: hole_src_opt,
    };
    aast_reduce::tast::go(&mut visitor, ctx, tast).into_iter().collect()
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    hole_filter: Filter,
) -> tast_holes_service::Result {
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    tast_holes(ctx, &tast.under_normal_assumptions, hole_filter)
}
