// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tany_check.ml`. See `hh/PORTING.md`.

use crate::error_codes;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_warning;
use crate::typing_warning_utils;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&typing_warning::Kind::Tany_found)
}

/// Returns `true` when `ty` contains a `Tany` member (possibly inside a union
/// or intersection).
pub fn has_genuine_tany(env: &Env, ty: &Ty) -> bool {
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Tany(_) => true,
        Ty_::Tunion(tyl) if tyl.is_empty() => false,
        Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
            tyl.iter().any(|ty| has_genuine_tany(&env, ty))
        }
        _ => false,
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let tast::Expr(ty, pos, _expr_) = e;
        let mut env = env.clone();
        let ty = tast_env::expand_type(&mut env, ty.clone());
        if has_genuine_tany(&env, &ty) {
            tast_env::add_warning(&env, (pos.clone(), typing_warning::Kind::Tany_found, ()))
        }
    }
}

/// `handler ~as_lint:_`
pub fn handler<'a>(_as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
