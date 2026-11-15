// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use nast::Argument;
use nast::Block;
use nast::CallExpr;
use nast::Expr;
use nast::Expr_;
use nast::Id;
use nast::Pos;
use nast::Stmt;
use nast::Stmt_;
use nast::Uop;

use crate::prelude::*;

/// Port of `Naming_elab_invariant`: elaborate `invariant` calls to their
/// canonical representation.
#[derive(Clone, Copy, Default)]
pub struct ElabExprCallHhInvariantPass;

impl Pass for ElabExprCallHhInvariantPass {
    // We are elaborating a `Call` `Expr` into a `Stmt` so the transformation
    // is defined on `Stmt`
    fn on_ty_stmt_bottom_up(&mut self, env: &Env, elem: &mut Stmt) -> ControlFlow<()> {
        let Stmt(_, stmt_) = elem;
        let (fn_expr_pos, args) = match stmt_ {
            Stmt_::Expr(box Expr(
                _,
                _,
                Expr_::Call(box CallExpr {
                    func: Expr(_, fn_expr_pos, Expr_::Id(box Id(_, fn_name))),
                    args,
                    ..
                }),
            )) if fn_name == sn::autoimported_functions::INVARIANT => (fn_expr_pos, args),
            _ => return Continue(()),
        };

        // With fewer than two arguments the call is replaced by an invalid
        // expression marker, whatever the kind of the argument.
        if args.len() < 2 {
            env.emit_error(NamingError::TooFewArguments(fn_expr_pos.clone()));
            let fn_expr_pos = fn_expr_pos.clone();
            let invalid = match args.pop() {
                None => Expr((), fn_expr_pos, Expr_::Invalid(Box::new(None))),
                Some(Argument::Anormal(expr))
                | Some(Argument::Ainout(_, expr))
                | Some(Argument::Anamed(_, expr)) => elab_utils::expr::invalid(expr),
            };
            *stmt_ = Stmt_::Expr(Box::new(invalid));
            return Break(());
        }

        // An `inout` or named condition is an error, but the call is
        // elaborated all the same.
        let err_opt = match &args[0] {
            Argument::Anormal(_) => None,
            Argument::Ainout(pk_p, _) => Some(NastCheckError::InoutInTransformedPseudofunction {
                pos: Pos::merge(pk_p, fn_expr_pos).unwrap_or_else(|_| pk_p.clone()),
                fn_name: "invariant".to_string(),
            }),
            Argument::Anamed(Id(name_pos, _), _) => {
                Some(NastCheckError::NamedInTransformedPseudofunction {
                    pos: Pos::merge(name_pos, fn_expr_pos).unwrap_or_else(|_| name_pos.clone()),
                    fn_name: "invariant".to_string(),
                })
            }
        };

        let old_stmt_ = std::mem::replace(stmt_, Stmt_::Noop);
        if let Stmt_::Expr(box Expr(
            annot,
            expr_pos,
            Expr_::Call(box CallExpr {
                func: Expr(fn_annot, fn_expr_pos, Expr_::Id(box Id(fn_name_pos, _))),
                targs,
                mut args,
                unpacked_arg,
            }),
        )) = old_stmt_
        {
            let Expr(cond_annot, cond_pos, cond) = match args.remove(0) {
                Argument::Anormal(expr)
                | Argument::Ainout(_, expr)
                | Argument::Anamed(_, expr) => expr,
            };
            // Construct a call to `invariant_violation` for the false case
            let id_expr = Expr_::Id(Box::new(Id(
                fn_name_pos,
                sn::autoimported_functions::INVARIANT_VIOLATION.into(),
            )));
            let fn_expr = Expr(fn_annot, fn_expr_pos, id_expr);
            let violation = Expr(
                annot,
                expr_pos.clone(),
                Expr_::Call(Box::new(CallExpr {
                    func: fn_expr,
                    targs,
                    args,
                    unpacked_arg,
                })),
            );
            *stmt_ = match cond {
                // a false <condition> means unconditional invariant_violation
                Expr_::False => Stmt_::Expr(Box::new(violation)),
                _ => {
                    let b1 = Block(vec![Stmt(expr_pos, Stmt_::Expr(Box::new(violation)))]);
                    let b2 = Block(vec![Stmt(elab_utils::pos::null(), Stmt_::Noop)]);
                    let cond = Expr(
                        cond_annot,
                        cond_pos.clone(),
                        Expr_::Unop(Box::new((Uop::Unot, Expr(cond_annot, cond_pos, cond)))),
                    );
                    Stmt_::If(Box::new((cond, b1, b2)))
                }
            };
        }
        if let Some(err) = err_opt {
            env.emit_error(err)
        }
        Continue(())
    }
}
