// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Argument;
use nast::CallExpr;
use nast::ClassId;
use nast::ClassId_;
use nast::Expr;
use nast::Expr_;
use nast::Id;

use crate::prelude::*;

/// Port of `Naming_elab_call`: elaborate special function calls to their
/// canonical representation, if any.
///
/// The OCaml top-down pass only records the current class, which nothing
/// reads; the bottom-up pass is this one.
#[derive(Clone, Copy, Default)]
pub struct ElabCallPass;

enum Res {
    Unchanged,
    MethodCaller,
    Invalid,
}

impl Pass for ElabCallPass {
    fn on_ty_expr_bottom_up(&mut self, env: &Env, elem: &mut Expr) -> ControlFlow<()> {
        let Expr(_, _, expr_) = elem;
        let mut errs = vec![];
        let res = match expr_ {
            Expr_::Call(box CallExpr {
                func: Expr(_, _, Expr_::Id(box Id(_, fn_name))),
                unpacked_arg,
                ..
            }) if fn_name == sn::pre_namespaced_functions::ECHO => {
                if let Some(Expr(_, pos, _)) = unpacked_arg {
                    errs.push(NamingError::TooFewArguments(pos.clone()))
                }
                Res::Unchanged
            }
            Expr_::Call(box CallExpr {
                func: Expr(_, fn_expr_pos, Expr_::Id(box Id(_, fn_name))),
                args,
                unpacked_arg,
                ..
            }) if fn_name == sn::autoimported_functions::METH_CALLER => {
                // TODO[mjt] targs is ignored entirely here - shouldn't we generate
                // and error to say they are invalid for this function?
                let unpacked_err = unpacked_arg
                    .as_ref()
                    .map(|Expr(_, pos, _)| NamingError::TooFewArguments(pos.clone()));
                let res = match args.as_slice() {
                    [] | [_] => {
                        errs.push(NamingError::TooFewArguments(fn_expr_pos.clone()));
                        Res::Invalid
                    }
                    [Argument::Anormal(e1), Argument::Anormal(e2)] => match (e1, e2) {
                        (
                            Expr(
                                _,
                                _,
                                Expr_::ClassConst(box (ClassId(_, _, ClassId_::CI(_)), (_, mem))),
                            ),
                            Expr(_, _, Expr_::String(_)),
                        ) if mem == sn::members::M_CLASS => Res::MethodCaller,
                        (Expr(_, p, _), _) => {
                            errs.push(NamingError::IllegalMethCaller(p.clone()));
                            Res::Invalid
                        }
                    },
                    [Argument::Ainout(..), _] | [_, Argument::Ainout(..)] => {
                        errs.push(NamingError::IllegalMethCaller(fn_expr_pos.clone()));
                        Res::Invalid
                    }
                    _ => {
                        errs.push(NamingError::TooManyArguments(fn_expr_pos.clone()));
                        Res::Invalid
                    }
                };
                errs.extend(unpacked_err);
                res
            }
            _ => Res::Unchanged,
        };
        errs.into_iter().for_each(|err| env.emit_error(err));
        match res {
            Res::Unchanged => Continue(()),
            Res::MethodCaller => {
                if let Expr_::Call(box CallExpr { args, .. }) = expr_ {
                    let e2 = args.pop();
                    let e1 = args.pop();
                    if let (
                        Some(Argument::Anormal(Expr(
                            _,
                            _,
                            Expr_::ClassConst(box (ClassId(_, _, ClassId_::CI(cl)), _)),
                        ))),
                        Some(Argument::Anormal(Expr(_, pm, Expr_::String(meth)))),
                    ) = (e1, e2)
                    {
                        *expr_ = Expr_::MethodCaller(Box::new((cl, (pm, meth.to_string()))));
                    }
                }
                Continue(())
            }
            Res::Invalid => {
                let inner_expr = std::mem::replace(elem, elab_utils::expr::null());
                *elem = elab_utils::expr::invalid(inner_expr);
                Break(())
            }
        }
    }
}
