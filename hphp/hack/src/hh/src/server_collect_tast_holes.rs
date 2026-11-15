// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_collect_tast_holes.ml` (the `TAST_HOLES`
//! command). See `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor;

use crate::provider_context;
use crate::server_command_types::tast_hole::Filter;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_holes_service;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;

fn mk_result(env: &Env, pos: &oxidized::pos::Pos, ty_actual: &tast::Ty, ty_expected: &tast::Ty) -> tast_holes_service::set::T {
    let mut s = tast_holes_service::set::T::new();
    s.insert(tast_holes_service::T {
        actual_ty_string: tast_env::print_ty(env, ty_actual),
        actual_ty_json: crate::yojson::safe::to_string(&tast_env::ty_to_json(env, Some(true), ty_actual)),
        expected_ty_string: tast_env::print_ty(env, ty_expected),
        expected_ty_json: crate::yojson::safe::to_string(&tast_env::ty_to_json(env, Some(true), ty_expected)),
        pos: pos.clone(),
    });
    s
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
    acc: tast_holes_service::set::T,
}

impl<'a> Reduce<'a> for Visitor {
    type Acc = tast_holes_service::set::T;

    fn zero(&self) -> Self::Acc {
        Default::default()
    }

    fn plus(&self, mut a: Self::Acc, b: Self::Acc) -> Self::Acc {
        a.extend(b);
        a
    }

    fn acc(&mut self) -> &mut Self::Acc {
        &mut self.acc
    }
}

impl<'a> aast_visitor::Visitor<'a> for Visitor {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; fun_, method_, class_var, expression_tree);

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            aast::Expr_::Hole(h) => {
                reduce::on_expr_(self, env, expr_)?;
                let (aast::Expr(_, pos, _), from_ty, to_ty, src) = &**h;
                if filter_source(self.hole_filter, src) {
                    let r = mk_result(env, pos, from_ty, to_ty);
                    reduce::add(self, r)
                }
                Ok(())
            }
            _ => reduce::on_expr_(self, env, expr_),
        }
    }
}

pub fn tast_holes(ctx: &provider_context::T, tast: &[tast::Def], hole_filter: Filter) -> tast_holes_service::Result {
    let mut v = Visitor {
        hole_filter,
        acc: Default::default(),
    };
    reduce::go(&mut v, ctx, tast).into_iter().collect()
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    hole_filter: Filter,
) -> tast_holes_service::Result {
    let crate::tast_provider::ComputeTast { tast, .. } =
        crate::tast_provider::compute_tast_quarantined(ctx, entry);
    tast_holes(ctx, &tast.under_normal_assumptions, hole_filter)
}
