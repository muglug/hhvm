// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `Naming_validate_await`: nested or piped `await` expressions cannot
//! be used alongside other concurrent awaits.
//!
//! (`lift_await` does the equivalent work for codegen, where the awaits are
//! also lifted; the typechecker only validates, and with different errors.)

use nast::Afield;
use nast::ClassId_;
use nast::Expr;
use nast::Expr_;
use nast::Pos;
use nast::Stmt;
use nast::Stmt_;
use nast::XhpAttribute;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::parsing_error::ParsingError;

use crate::Env;

enum AwaitUsage {
    NoAwait,
    ContainsAwait,
    ConcurrentAwait,
    Sequential,
    Error(Option<Pos>),
}
use AwaitUsage::*;

fn combine_con(await1: AwaitUsage, await2: AwaitUsage) -> AwaitUsage {
    match (await1, await2) {
        (Sequential, NoAwait) | (NoAwait, Sequential) => Sequential,
        (Error(Some(pos)), _) => Error(Some(pos)),
        (_, Error(Some(pos))) => Error(Some(pos)),
        (Error(None), _) | (_, Error(None)) => Error(None),
        (Sequential, _) | (_, Sequential) => Error(None),
        (ConcurrentAwait, _) | (_, ConcurrentAwait) | (ContainsAwait, ContainsAwait) => {
            ConcurrentAwait
        }
        (NoAwait, ContainsAwait) | (ContainsAwait, NoAwait) => ContainsAwait,
        (NoAwait, NoAwait) => NoAwait,
    }
}

/// `List.fold_right exprs ~init ~f:await_fold`
fn fold_right<'a>(
    exprs: impl DoubleEndedIterator<Item = &'a Expr>,
    init: AwaitUsage,
) -> AwaitUsage {
    exprs
        .rev()
        .fold(init, |acc, expr| combine_con(check_await_usage(expr), acc))
}

fn check_await_usage(expr: &Expr) -> AwaitUsage {
    let Expr((), pos, e) = expr;
    let await_usage = match e {
        // Expressions with no sub-expressions that we can lift an await out of
        Expr_::Dollardollar(_)
        | Expr_::Null
        | Expr_::This
        | Expr_::True
        | Expr_::False
        | Expr_::Omitted
        | Expr_::Id(_)
        | Expr_::Lvar(_)
        | Expr_::Int(_)
        | Expr_::Float(_)
        | Expr_::String(_)
        | Expr_::Efun(_)
        | Expr_::Lfun(_)
        | Expr_::Lplaceholder(_)
        | Expr_::MethodCaller(_)
        | Expr_::Invalid(box None)
        | Expr_::EnumClassLabel(_)
        | Expr_::ClassConst(_)
        | Expr_::Nameof(_)
        | Expr_::FunctionPointer(_)
        | Expr_::ClassGet(_)
        | Expr_::Package(_) => NoAwait,

        // Expressions with exactly one sub-expression that we can lift an await out of
        Expr_::Invalid(box Some(expr))
        | Expr_::Clone(box expr)
        | Expr_::PrefixedString(box (_, expr))
        | Expr_::ReadonlyExpr(box expr)
        | Expr_::Cast(box (_, expr))
        | Expr_::Is(box (expr, _))
        | Expr_::As(box nast::As_ { expr, .. })
        | Expr_::Upcast(box (expr, _))
        | Expr_::Import(box (_, expr))
        | Expr_::Hole(box (expr, _, _, _))
        | Expr_::Yield(box Afield::AFvalue(expr))
        | Expr_::ETSplice(box nast::EtSplice {
            spliced_expr: expr, ..
        })
        | Expr_::Unop(box (_, expr))
        | Expr_::ArrayGet(box (expr, None)) => check_await_usage(expr),

        // Expressions with exactly two sub-expressions that we can lift an await out of
        // and run concurrently
        Expr_::ArrayGet(box (expr1, Some(expr2)))
        | Expr_::Pair(box (_, expr1, expr2))
        | Expr_::ObjGet(box (expr1, expr2, _, _))
        | Expr_::Yield(box Afield::AFkvalue(expr1, expr2))
        | Expr_::Binop(box nast::Binop {
            bop: _, // Can't have await in || or && (parse error)
            lhs: expr1,
            rhs: expr2,
        })
        | Expr_::Assign(box (expr1, _, expr2)) => {
            combine_con(check_await_usage(expr1), check_await_usage(expr2))
        }

        // Expressions with lists of sub-expressions that we can lift an await out of
        // and run concurrently
        Expr_::KeyValCollection(box (_, _, args)) => {
            args.iter()
                .rev()
                .fold(NoAwait, |await1, nast::Field(arg_k, arg_v)| {
                    let await2 = combine_con(check_await_usage(arg_k), check_await_usage(arg_v));
                    combine_con(await1, await2)
                })
        }
        Expr_::Tuple(args) | Expr_::String2(args) | Expr_::ValCollection(box (_, _, args)) => {
            fold_right(args.iter(), NoAwait)
        }
        Expr_::Shape(fields) => fold_right(
            fields.iter().map(|field| match field {
                nast::ShapeExprField::SFField(_, expr) | nast::ShapeExprField::SFSplat(expr) => expr,
            }),
            NoAwait,
        ),
        Expr_::Call(box nast::CallExpr {
            func,
            targs: _,
            args,
            unpacked_arg,
        }) => {
            let res = fold_right(
                args.iter().map(|arg| arg.to_expr_ref()),
                check_await_usage(func),
            );
            match unpacked_arg {
                None => res,
                Some(arg) => combine_con(check_await_usage(arg), res),
            }
        }
        Expr_::New(box (nast::ClassId(_, _, cid), _, args, unpacked_arg, _)) => {
            let res = match cid {
                ClassId_::CIexpr(expr) => check_await_usage(expr),
                ClassId_::CIparent
                | ClassId_::CIself
                | ClassId_::CIstatic
                | ClassId_::CI(_)
                | ClassId_::CIreified(_) => NoAwait,
            };
            let res = fold_right(args.iter().map(|arg| arg.to_expr_ref()), res);
            match unpacked_arg {
                None => res,
                Some(arg) => combine_con(check_await_usage(arg), res),
            }
        }
        Expr_::Xml(box (_, attrs, exprs)) => {
            let res = fold_right(
                attrs.iter().map(|attr| match attr {
                    XhpAttribute::XhpSpread(expr)
                    | XhpAttribute::XhpSimple(nast::XhpSimple { expr, .. }) => expr,
                }),
                NoAwait,
            );
            fold_right(exprs.iter(), res)
        }
        Expr_::Collection(box (_, _, afields)) => {
            afields.iter().rev().fold(NoAwait, |await_, afield| {
                let await1 = match afield {
                    Afield::AFvalue(expr) => check_await_usage(expr),
                    Afield::AFkvalue(expr1, expr2) => {
                        combine_con(check_await_usage(expr1), check_await_usage(expr2))
                    }
                };
                combine_con(await1, await_)
            })
        }
        Expr_::Await(box expr1) => match check_await_usage(expr1) {
            NoAwait => ContainsAwait,
            ContainsAwait | Sequential | ConcurrentAwait => Sequential,
            Error(p) => Error(p),
        },
        Expr_::Delay(_) => NoAwait,
        Expr_::Pipe(box (_, expr1, expr2, _)) => {
            match check_await_usage(expr2) {
                Error(p) => Error(p),
                // If the rhs contains an await, then we need to finish the lhs
                // prior to doing the await
                ContainsAwait | ConcurrentAwait | Sequential => Sequential,
                NoAwait => check_await_usage(expr1),
            }
        }
        // Can't have await in the branches (parse error)
        Expr_::Eif(box (cond, _, _)) => check_await_usage(cond),
        Expr_::ExpressionTree(box nast::ExpressionTree {
            class: _,
            runtime_expr,
            free_vars: _,
        }) => check_await_usage(runtime_expr),
        // lvalues: shouldn't contain await or $$
        Expr_::List(_) | Expr_::DestructureShape(_) | Expr_::DestructureTuple(_) => NoAwait,
    };
    match await_usage {
        Error(None) => Error(Some(pos.clone())),
        _ => await_usage,
    }
}

struct ValidateAwait<'a> {
    env: &'a Env,
}

impl ValidateAwait<'_> {
    fn error(&self, pos: Pos, msg: &str) {
        self.env
            .emit_error(NamingPhaseError::Parsing(ParsingError::ParsingError {
                pos,
                msg: msg.into(),
                quickfixes: vec![],
            }))
    }

    fn check_expr(&self, expr: &Expr) {
        match check_await_usage(expr) {
            Error(p) => self.error(
                p.unwrap_or_else(|| expr.1.clone()),
                "Nested or piped `await` expressions cannot be used alongside other concurrent awaits",
            ),
            NoAwait | ContainsAwait | ConcurrentAwait | Sequential => {}
        }
    }

    /// Visit the expression, then check it.
    fn expr<'ast>(&mut self, expr: &'ast Expr) -> Result<(), ()> {
        self.visit_expr(&mut (), expr)?;
        self.check_expr(expr);
        Ok(())
    }
}

impl<'ast> Visitor<'ast> for ValidateAwait<'_> {
    type Params = AstParams<(), ()>;

    fn object(&mut self) -> &mut dyn Visitor<'ast, Params = Self::Params> {
        self
    }

    fn visit_stmt(&mut self, c: &mut (), stmt: &'ast Stmt) -> Result<(), ()> {
        const IN_CONCURRENT: &str =
            "Nested or piped `await` expressions cannot be used in concurrent block";
        let Stmt(_, stmt_) = stmt;
        match stmt_ {
            Stmt_::Expr(box expr) | Stmt_::Return(box Some(expr)) | Stmt_::Throw(box expr) => {
                self.expr(expr)
            }
            Stmt_::Return(box None) => Ok(()),
            Stmt_::Using(box nast::UsingStmt {
                is_block_scoped: _,
                has_await: _,
                exprs: (_, exprs),
                block,
            }) => {
                for expr in exprs {
                    self.expr(expr)?;
                }
                self.visit_block(c, block)
            }
            Stmt_::If(box (expr, b1, b2)) => {
                self.expr(expr)?;
                self.visit_block(c, b1)?;
                self.visit_block(c, b2)
            }
            Stmt_::For(box (init_exprs, test, nast::LoopIter(_, _, update), block)) => {
                for expr in init_exprs {
                    self.expr(expr)?;
                }
                // No await in the test or update positions (parse error)
                if let Some(nast::LoopCond(_, _, e)) = test {
                    self.visit_expr(c, e)?;
                }
                for expr in update {
                    self.visit_expr(c, expr)?;
                }
                self.visit_block(c, block)
            }
            Stmt_::Switch(box (case, block, default)) => {
                // No await in the case expression positions (parse error)
                self.expr(case)?;
                for case in block {
                    self.visit_case(c, case)?;
                }
                if let Some(default) = default {
                    self.visit_default_case(c, default)?;
                }
                Ok(())
            }
            Stmt_::Foreach(box (expr, as_expr, block)) => {
                self.expr(expr)?;
                self.visit_as_expr(c, as_expr)?;
                self.visit_block(c, block)
            }
            // await cannot appear in expression in do or while (parse error)
            Stmt_::Do(_)
            | Stmt_::While(_)
            | Stmt_::Block(_)
            | Stmt_::Try(_)
            | Stmt_::Match(_)
            | Stmt_::Awaitall(_) => stmt.recurse(c, self.object()),
            Stmt_::Noop
            | Stmt_::Fallthrough
            | Stmt_::Break
            | Stmt_::Continue
            | Stmt_::YieldBreak
            | Stmt_::Markup(_) => Ok(()),
            Stmt_::Concurrent(stmts) => {
                for stmt in stmts.iter() {
                    // The rest is handled by parser
                    if let Stmt(_, Stmt_::Expr(box expr)) = stmt {
                        self.visit_expr(c, expr)?;
                        match check_await_usage(expr) {
                            Sequential | Error(None) => self.error(expr.1.clone(), IN_CONCURRENT),
                            Error(Some(pos)) => self.error(pos, IN_CONCURRENT),
                            NoAwait | ContainsAwait | ConcurrentAwait => {}
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

#[allow(dead_code)]
pub fn validate_program(env: &Env, program: &nast::Program) {
    let _ = ValidateAwait { env }.visit_program(&mut (), program);
}

pub fn validate_fun_def(env: &Env, fd: &nast::FunDef) {
    let _ = ValidateAwait { env }.visit_fun_def(&mut (), fd);
}

pub fn validate_class_(env: &Env, c: &nast::Class_) {
    let _ = ValidateAwait { env }.visit_class_(&mut (), c);
}

pub fn validate_stmt(env: &Env, stmt: &nast::Stmt) {
    let _ = ValidateAwait { env }.visit_stmt(&mut (), stmt);
}
