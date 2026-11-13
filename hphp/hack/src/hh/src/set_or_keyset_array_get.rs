// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `set_or_keyset_array_get.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::pos::Pos;

use crate::aast_utils;
use crate::error_codes;
use crate::full_fidelity_source_text;
use crate::pos;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::IterWithState;
use crate::typing_defs::*;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_warning;
use crate::typing_warning::Warn;
use crate::typing_warning::set_or_keyset_array_get as sokag;
use crate::typing_warning_utils;

const warning_kind: typing_warning::Kind<sokag::T, Warn> =
    typing_warning::Kind::Set_or_keyset_array_get;

/// `val error_codes : Error_codes.Warning.t list`
pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

fn is_keyset(env: &Env, ty: &Ty) -> bool {
    let r = typing_reason::none();
    tast_env::is_sub_type(
        env,
        ty,
        &typing_make_type::keyset(r.clone(), typing_make_type::arraykey(r)),
    )
}

fn is_nothing(env: &Env, ty: &Ty) -> bool {
    let r = typing_reason::none();
    tast_env::is_sub_type(env, ty, &typing_make_type::nothing(r))
}

fn is_const_set(env: &Env, ty: &Ty) -> bool {
    let r = typing_reason::none();
    tast_env::is_sub_type(
        env,
        ty,
        &typing_make_type::class_type(
            r.clone(),
            sn::collections::CONST_SET.to_string(),
            vec![typing_make_type::arraykey(r)],
        ),
    )
}

/// (OCaml's text is bytes; the text of the quickfix is a `String`, so bytes
/// that are not UTF-8 are replaced.)
fn get_text_at_pos(source_text: &full_fidelity_source_text::T, pos: &Pos) -> Option<String> {
    let (start_offset, end_offset) = pos::info_raw(pos);
    if start_offset >= 0 && end_offset > start_offset {
        Some(
            full_fidelity_source_text::sub(source_text, start_offset, end_offset - start_offset)
                .to_string(),
        )
    } else {
        None
    }
}

fn compute_replacement_text(
    env: &Env,
    kind: &sokag::Kind,
    arr_pos: &Pos,
    idx_pos: &Pos,
) -> Option<String> {
    let ctx = tast_env::get_ctx(env);
    let file = tast_env::get_file(env);
    let entries = &ctx.entries;
    let entry = entries.get(&*file)?;
    let source_text = entry.source_text.lock().unwrap().clone()?;
    let arr_text = get_text_at_pos(&source_text, arr_pos)?;
    let idx_text = get_text_at_pos(&source_text, idx_pos)?;
    let replacement = match kind {
        sokag::Kind::Keyset => format!("C\\contains_key({}, {})", arr_text, idx_text),
        sokag::Kind::ConstSet => format!("{}->contains({})", arr_text, idx_text),
    };
    Some(replacement)
}

fn check_array_get(
    env: &Env,
    pos: &Pos,
    full_expr_pos: &Pos,
    arr_pos: &Pos,
    idx_pos: &Pos,
    ty: &Ty,
) {
    let mut env = env.clone();
    let expanded_ty = tast_env::expand_type(&mut env, ty.clone());
    let expanded_ty = tast_env::strip_dynamic(&env, expanded_ty);
    match get_node(&expanded_ty) {
        Ty_::Tunion(tyl) => tyl
            .iter()
            .for_each(|ty| check_array_get(&env, pos, full_expr_pos, arr_pos, idx_pos, ty)),
        Ty_::Toption(inner_ty) => {
            check_array_get(&env, pos, full_expr_pos, arr_pos, idx_pos, inner_ty)
        }
        _ => {
            // Use subtype checking to detect keyset or ConstSet subtypes
            let kind_opt = if !is_nothing(&env, &expanded_ty) {
                if is_keyset(&env, &expanded_ty) {
                    Some(sokag::Kind::Keyset)
                } else if is_const_set(&env, &expanded_ty) {
                    Some(sokag::Kind::ConstSet)
                } else {
                    None
                }
            } else {
                None
            };
            match kind_opt {
                Some(kind) => {
                    let replacement_text = compute_replacement_text(&env, &kind, arr_pos, idx_pos);
                    tast_env::add_warning(
                        &env,
                        (
                            pos.clone(),
                            typing_warning::Kind::Set_or_keyset_array_get,
                            sokag::T {
                                kind,
                                ty: tast_env::print_ty(&env, &expanded_ty),
                                full_expr_pos: full_expr_pos.clone(),
                                replacement_text,
                            },
                        ),
                    )
                }
                None => {}
            }
        }
    }
}

/// Use a stateful visitor to track when we're inside an unset() call.
/// We skip the warning for Array_get inside unset() since that's a valid
/// way to remove elements from a keyset/set.
///
/// (`let visitor = object inherit [_] Tast_visitor.iter_with_state ... end`:
/// the state is `in_unset_or_assign`.)
struct UnsetVisitor;

fn visitor() -> UnsetVisitor {
    UnsetVisitor
}

type Res = Result<(), ()>;

/// `this#on_expr (env, in_unset_or_assign) e`: the environment is the same,
/// with another state.
fn on_expr_with_state<'a>(
    v: &mut UnsetVisitor,
    c: &mut (Env, bool),
    in_unset_or_assign: bool,
    e: &'a tast::Expr,
) -> Res {
    let saved = std::mem::replace(&mut c.1, in_unset_or_assign);
    let res = v.visit_expr(c, e);
    c.1 = saved;
    res
}

impl<'a> Visitor<'a> for UnsetVisitor {
    type Params = tast_visitor::StateParams<bool>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::iter_with_state_methods!('a);

    fn visit_expr(&mut self, c: &mut (Env, bool), e: &'a tast::Expr) -> Res {
        let in_unset_or_assign = c.1;
        let aast::Expr(_, p, expr) = e;
        match expr {
            // Detect unset($arr[key]) - mark children as in_unset context
            aast::Expr_::Call(call)
                if matches!(&call.func.2, aast::Expr_::Id(id)
                    if id.1 == sn::pseudo_functions::UNSET
                        || id.1 == sn::pseudo_functions::ISSET) =>
            {
                for arg in call.args.iter() {
                    on_expr_with_state(self, c, true, aast_utils::arg_to_expr(arg))?;
                }
                Ok(())
            }
            aast::Expr_::Assign(a) => {
                let (e1, _op, e2) = &**a;
                on_expr_with_state(self, c, true, e1)?;
                on_expr_with_state(self, c, false, e2)
            }
            // Check Array_get only when NOT in unset context
            aast::Expr_::ArrayGet(ag) if ag.1.is_some() => {
                let (arr, idx) = &**ag;
                let idx = idx.as_ref().unwrap();
                let aast::Expr(ty, arr_p, _) = arr;
                let aast::Expr(_, idx_p, _) = idx;
                if !in_unset_or_assign {
                    check_array_get(&c.0, p, p, arr_p, idx_p, ty)
                }
                on_expr_with_state(self, c, false, arr)?;
                on_expr_with_state(self, c, false, idx)
            }
            _ => {
                // super#on_expr (env, false) e
                let saved = std::mem::replace(&mut c.1, false);
                let res = e.recurse(c, self);
                c.1 = saved;
                res
            }
        }
    }
}

impl<'a> IterWithState<'a, bool> for UnsetVisitor {}

/// `handler ~as_lint` (`as_lint` is unused, as in OCaml)
struct Handler {
    #[allow(dead_code)]
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        let _ = visitor().visit_fun_def(&mut (env.clone(), false), fd);
    }

    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        let _ = visitor().visit_method_(&mut (env.clone(), false), m);
    }
}

/// `val handler : as_lint:bool -> Tast_visitor.handler`
pub fn handler(as_lint: bool) -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler { as_lint })
}
