// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 12850-12966): module `Xhp_attribute`.
//! See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::OperatorNullFlavor;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::folded_class as cls;
use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_defs::Ty;
use crate::typing_env_types::Env;
use crate::typing_error_utils;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_xhp;

pub fn xhp_check_get_attribute(
    pos: &Pos,
    env: &mut Env,
    base_expr: &nast::Expr,
    prop: &str,
    null_flavour: OperatorNullFlavor,
) {
    // All and only attributes start with `:` when represented as properties.
    if prop.starts_with(":") {
        let base_lenv = env.lenv.clone();
        let call_get_attr = typing_xhp::rewrite_attribute_access_into_call(
            pos.clone(),
            base_expr.clone(),
            null_flavour,
        );
        let (_, _) = expr::expr(None, &expr::context::default(), env, &call_get_attr);
        // Snap the local env back to avoid manipualting refinements twice.
        env.lenv = base_lenv;
    }
}

/// Process a spread operator by computing the intersection of XHP attributes
/// between the spread expression and the XHP constructor onto which we're
/// spreading.
pub(crate) fn xhp_spread_attribute(
    env: &mut Env,
    c_onto: Option<&cls::T>,
    valexpr: &nast::Expr,
    sid: &nast::Sid,
    obj: &Ty,
) -> aast::XhpAttribute<Ty, tast::SavedEnv> {
    let aast::Expr(_, p, _) = valexpr;
    let (te, valty) = expr::expr(None, &expr::context::default(), env, valexpr);
    let (xhp_req_err_opt, attr_ptys) = match c_onto {
        None => (None, vec![]),
        Some(class_info) => typing_xhp::get_spread_attributes(env, p, class_info, &valty),
    };
    if let Some(err) = &xhp_req_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    let mut has_ty_mismatch = false;
    for attr in &attr_ptys {
        let (_, err_opt) = xhp_attribute_decl_ty(env, sid, obj.clone(), attr);
        has_ty_mismatch = has_ty_mismatch || err_opt.is_some();
    }
    // If we have a subtyping error for any attribute, the best we can do here
    // is give an expected type of nothing
    let ty_mismatch_opt = if has_ty_mismatch {
        Some((valty, make_type::nothing(reason::none())))
    } else {
        None
    };
    // Build the typed attribute node
    aast::XhpAttribute::XhpSpread(hole_on_ty_mismatch(te, ty_mismatch_opt))
}

/// Simple XHP attributes (attr={expr} form) are simply interpreted as a member
/// variable prefixed with a colon.
pub(crate) fn xhp_simple_attribute(
    env: &mut Env,
    id: &aast::Pstring,
    valexpr: &nast::Expr,
    sid: &nast::Sid,
    obj: &Ty,
) -> aast::XhpAttribute<Ty, tast::SavedEnv> {
    let aast::Expr(_, p, _) = valexpr;
    let (te, valty) = expr::expr(None, &expr::context::default(), env, valexpr);
    // This converts the attribute name to a member name.
    let name = format!(":{}", id.1);
    let attr_pty = ((id.0.clone(), name), (p.clone(), valty));
    let (decl_ty, ty_mismatch_opt) = xhp_attribute_decl_ty(env, sid, obj.clone(), &attr_pty);
    aast::XhpAttribute::XhpSimple(aast::XhpSimple {
        name: id.clone(),
        type_: decl_ty,
        expr: hole_on_ty_mismatch(te, ty_mismatch_opt),
    })
}

/// Typecheck the attribute expressions - this just checks that the expressions are
/// valid, not that they match the declared type for the attribute and,
/// in case of spreads, makes sure they are XHP.
pub fn xhp_attribute_exprs(
    env: &mut Env,
    cls_decl: Option<&cls::T>,
    attrl: &[nast::XhpAttribute],
    sid: &nast::Sid,
    obj: &Ty,
) -> Vec<aast::XhpAttribute<Ty, tast::SavedEnv>> {
    // `handle_attr`, folded from the left; the list is consed and reversed at
    // the end in OCaml, so pushing keeps the same order.
    let mut typed_attrl = vec![];
    for attr in attrl {
        let typed_attr = match attr {
            aast::XhpAttribute::XhpSimple(aast::XhpSimple {
                name: id,
                expr: valexpr,
                ..
            }) => xhp_simple_attribute(env, id, valexpr, sid, obj),
            aast::XhpAttribute::XhpSpread(valexpr) => {
                xhp_spread_attribute(env, cls_decl, valexpr, sid, obj)
            }
        };
        typed_attrl.push(typed_attr);
    }
    typed_attrl
}
