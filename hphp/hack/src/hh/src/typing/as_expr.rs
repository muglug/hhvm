// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 12968-12998): module `As_expr`.
//! See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::tast;
use crate::typing::assign;
use crate::typing_defs::Ty;
use crate::typing_env_types::Env;

pub(crate) fn bind_foreach_target(
    env: &mut Env,
    _p: &Pos,
    ty: Ty,
    expr: &nast::Expr,
) -> tast::Expr {
    let aast::Expr(_, ep, _) = expr;
    let (te, _, _) = assign::assign(None, ep, env, expr, ep, ty);
    te
}

pub fn bind_as_expr(
    env: &mut Env,
    p: &Pos,
    ty1: &Ty,
    ty2: &Ty,
    aexpr: &nast::AsExpr,
) -> aast::AsExpr<Ty, tast::SavedEnv> {
    match aexpr {
        aast::AsExpr::AsV(ev) => {
            let te = bind_foreach_target(env, p, ty2.clone(), ev);
            aast::AsExpr::AsV(te)
        }
        aast::AsExpr::AwaitAsV(p, ev) => {
            let te = bind_foreach_target(env, p, ty2.clone(), ev);
            aast::AsExpr::AwaitAsV(p.clone(), te)
        }
        aast::AsExpr::AsKv(ek, ev) => {
            let tk = bind_foreach_target(env, p, ty1.clone(), ek);
            let te = bind_foreach_target(env, p, ty2.clone(), ev);
            aast::AsExpr::AsKv(tk, te)
        }
        aast::AsExpr::AwaitAsKv(await_pos, ek, ev) => {
            let tk = bind_foreach_target(env, p, ty1.clone(), ek);
            let te = bind_foreach_target(env, p, ty2.clone(), ev);
            aast::AsExpr::AwaitAsKv(await_pos.clone(), tk, te)
        }
    }
}
