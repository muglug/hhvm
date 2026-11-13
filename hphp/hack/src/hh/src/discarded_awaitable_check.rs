// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `discarded_awaitable_check.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Uop;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_pos;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_reason;

pub fn is_awaitable(env: &Env, ty: &Ty) -> bool {
    let mixed = make_type::mixed(typing_reason::none());
    let awaitable_of_mixed = make_type::awaitable(typing_reason::none(), mixed);
    tast_env::can_subtype(env, ty, &awaitable_of_mixed)
}

pub fn can_be_null(env: &Env, ty: &Ty) -> bool {
    let null = make_type::null(typing_reason::none());
    tast_env::can_subtype(env, &null, ty)
}

pub fn enforce_not_awaitable(env: &Env, p: &Pos, ty: &Ty) {
    let ety = tast_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ety) {
        Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
            for ty in tyl {
                enforce_not_awaitable(env, p, ty)
            }
        }
        Ty_::Tclass((_, awaitable), _, _) if awaitable == sn::classes::AWAITABLE => {
            typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::Discarded_awaitable {
                    pos: p.clone(),
                    decl_pos: get_pos(&ety),
                }),
                env,
            )
        }
        Ty_::Toption(ty_) => {
            if tast_env::get_tcopt(env).tco_disallow_discarded_nullable_awaitables {
                enforce_not_awaitable(env, p, ty_)
            }
        }
        Ty_::Tany(_)
        | Ty_::Tnonnull
        | Ty_::TvecOrDict(_, _)
        | Ty_::Tprim(_)
        | Ty_::Tvar(_)
        | Ty_::Tfun(_)
        | Ty_::Tgeneric(_)
        | Ty_::Tnewtype(_, _, _)
        | Ty_::Tdependent(_, _)
        | Ty_::Tclass(_, _, _)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tdynamic(_)
        | Ty_::Taccess(_)
        | Ty_::Tlabel(_)
        | Ty_::Tneg(_)
        | Ty_::TclassPtr(_) => {}
    }
}

/// `ctx`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ctx {
    /// Is a supertype of ?Awaitable<t> allowed in a given
    /// context?
    ///
    /// E.g.: If true, ?Awaitable<t> is disallowed, but Awaitable<t> is allowed.
    pub nullable_awaitable_disallowed: bool,
    /// Is a non-nullable supertype of Awaitable<t> disallowed in a given
    /// context?
    ///
    /// E.g.: If true, Awaitable<t> is disallowed, but ?Awaitable<t> and any
    /// union containing Awaitable<t> and an nullable type are allowed.
    pub non_nullable_awaitable_disallowed: bool,
}

pub const allow_awaitable: Ctx = Ctx {
    nullable_awaitable_disallowed: false,
    non_nullable_awaitable_disallowed: false,
};

pub const disallow_awaitable: Ctx = Ctx {
    nullable_awaitable_disallowed: true,
    non_nullable_awaitable_disallowed: true,
};

pub fn disallow_due_to_cast(ctx: Ctx, env: &Env) -> Ctx {
    if tast_env::get_tcopt(env).tco_disallow_discarded_nullable_awaitables {
        Ctx {
            nullable_awaitable_disallowed: true,
            non_nullable_awaitable_disallowed: true,
        }
    } else {
        Ctx {
            non_nullable_awaitable_disallowed: true,
            ..ctx
        }
    }
}

pub const disallow_due_to_cast_with_explicit_nullcheck: Ctx = Ctx {
    nullable_awaitable_disallowed: false,
    non_nullable_awaitable_disallowed: true,
};

pub fn disallow_due_to_cast_with_explicit_nullcheck_and_return_nonnull(ctx: Ctx) -> Ctx {
    Ctx {
        nullable_awaitable_disallowed: ctx.nullable_awaitable_disallowed
            && ctx.non_nullable_awaitable_disallowed,
        non_nullable_awaitable_disallowed: true,
    }
}

type Res = tast_visitor::Res;

/// The object `visitor` (which inherits from `Tast_visitor.iter_with_state`,
/// its state being a [`Ctx`]).
pub struct AwaitableVisitor;

pub fn visitor() -> AwaitableVisitor {
    AwaitableVisitor
}

impl AwaitableVisitor {
    /// Visit with `(env, ctx)` where the context has `env`: the state is
    /// `ctx` while `f` runs.
    fn with_ctx(
        &mut self,
        c: &mut (Env, Ctx),
        ctx: Ctx,
        f: impl FnOnce(&mut Self, &mut (Env, Ctx)) -> Res,
    ) -> Res {
        let saved = std::mem::replace(&mut c.1, ctx);
        let res = f(self, c);
        c.1 = saved;
        res
    }

    /// The expression of the alternatives `Unop (Ast_defs.Unot, e)`,
    /// `Binop { bop = Eqeqeq; lhs = e; rhs = Null }`, `Binop { bop = Eqeqeq;
    /// lhs = Null; rhs = e }`, `Binop { bop = Diff2; lhs = e; rhs = Null }`
    /// and `Binop { bop = Diff2; lhs = Null; rhs = e }`, the first that
    /// matches.
    fn explicit_nullcheck(e: &tast::Expr_) -> Option<&tast::Expr> {
        let is_null = |e: &tast::Expr| matches!(&e.2, aast::Expr_::Null);
        match e {
            aast::Expr_::Unop(unop) if matches!(unop.0, Uop::Unot) => Some(&unop.1),
            aast::Expr_::Binop(binop) if matches!(binop.bop, Bop::Eqeqeq | Bop::Diff2) => {
                if is_null(&binop.rhs) {
                    Some(&binop.lhs)
                } else if is_null(&binop.lhs) {
                    Some(&binop.rhs)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl<'a> Visitor<'a> for AwaitableVisitor {
    type Params = tast_visitor::StateParams<Ctx>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::iter_with_state_methods!('a);

    /// `on_expr`
    fn visit_expr(&mut self, c: &mut (Env, Ctx), te: &'a tast::Expr) -> Res {
        let aast::Expr(ty, p, e) = te;
        let ctx = c.1;
        if let aast::Expr_::Await(e) = e {
            return self.with_ctx(c, allow_awaitable, |this, c| this.visit_expr(c, e));
        }
        if let Some(e) = Self::explicit_nullcheck(e) {
            return self.with_ctx(
                c,
                disallow_due_to_cast_with_explicit_nullcheck,
                |this, c| this.visit_expr(c, e),
            );
        }
        match e {
            aast::Expr_::Binop(binop)
                if matches!(
                    binop.bop,
                    Bop::Eqeq | Bop::Eqeqeq | Bop::Diff | Bop::Diff2 | Bop::Barbar | Bop::Ampamp
                ) =>
            {
                let aast::Binop { lhs, rhs, .. } = &**binop;
                let ctx_lhs = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx_lhs, |this, c| this.visit_expr(c, lhs))?;
                let ctx_rhs = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx_rhs, |this, c| this.visit_expr(c, rhs))
            }
            aast::Expr_::Binop(binop) if matches!(binop.bop, Bop::QuestionQuestion) => {
                let aast::Binop { lhs, rhs, .. } = &**binop;
                self.with_ctx(
                    c,
                    disallow_due_to_cast_with_explicit_nullcheck_and_return_nonnull(ctx),
                    |this, c| this.visit_expr(c, lhs),
                )?;
                self.with_ctx(c, ctx, |this, c| this.visit_expr(c, rhs))
            }
            aast::Expr_::Eif(eif) => {
                let (e1, e2, e3) = &**eif;
                let ctx1 = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx1, |this, c| this.visit_expr(c, e1))?;
                if let Some(e2) = e2 {
                    self.with_ctx(c, ctx, |this, c| this.visit_expr(c, e2))?;
                }
                self.with_ctx(c, ctx, |this, c| this.visit_expr(c, e3))
            }
            aast::Expr_::Cast(cast) => {
                let (hint, e) = &**cast;
                self.with_ctx(c, ctx, |this, c| this.visit_hint(c, hint))?;
                self.with_ctx(c, disallow_awaitable, |this, c| this.visit_expr(c, e))
            }
            aast::Expr_::Is(is)
                if matches!(
                    &*is.1.1,
                    aast::Hint_::Hnonnull | aast::Hint_::Hprim(Tprim::Tnull)
                ) =>
            {
                let (e, _) = &**is;
                self.with_ctx(
                    c,
                    disallow_due_to_cast_with_explicit_nullcheck,
                    |this, c| this.visit_expr(c, e),
                )
            }
            aast::Expr_::Is(_) | aast::Expr_::As(_) => {
                let (e, hint) = match e {
                    aast::Expr_::Is(is) => (&is.0, &is.1),
                    aast::Expr_::As(as_) => (&as_.expr, &as_.hint),
                    _ => unreachable!(),
                };
                let hint_ty = tast_env::hint_to_ty(&c.0, hint);
                let saved_env = c.0.clone();
                let hint_ty = tast_env::localize_no_subst(&mut c.0, true, &hint_ty);
                let ctx_ = if is_awaitable(&c.0, &hint_ty) {
                    allow_awaitable
                } else {
                    disallow_due_to_cast(ctx, &c.0)
                };
                let res = self.with_ctx(c, ctx_, |this, c| this.visit_expr(c, e));
                c.0 = saved_env;
                res
            }
            _ => {
                if ctx.nullable_awaitable_disallowed || ctx.non_nullable_awaitable_disallowed {
                    // (When the two flags agree the answer of `can_be_null`, a
                    // query that changes nothing, does not matter: skipped,
                    // unless the dependency edges its lookups record are.)
                    if if ctx.nullable_awaitable_disallowed
                        == ctx.non_nullable_awaitable_disallowed
                        && !crate::typing_env::deps::records_dependency_edges(&c.0)
                    {
                        ctx.nullable_awaitable_disallowed
                    } else if can_be_null(&c.0, ty) {
                        ctx.nullable_awaitable_disallowed
                    } else {
                        ctx.non_nullable_awaitable_disallowed
                    } {
                        enforce_not_awaitable(&c.0, p, ty)
                    }
                }
                // super#on_expr
                self.with_ctx(c, allow_awaitable, |this, c| te.recurse(c, this))
            }
        }
    }

    /// `on_stmt`
    fn visit_stmt(&mut self, c: &mut (Env, Ctx), stmt: &'a tast::Stmt) -> Res {
        let ctx = c.1;
        match &stmt.1 {
            aast::Stmt_::Expr(e) if matches!(&e.2, aast::Expr_::Assign(_)) => {
                self.with_ctx(c, allow_awaitable, |this, c| this.visit_expr(c, e))
            }
            aast::Stmt_::Expr(e) => {
                self.with_ctx(c, disallow_awaitable, |this, c| this.visit_expr(c, e))
            }
            aast::Stmt_::If(if_) => {
                let (e, b1, b2) = &**if_;
                let ctx_e = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx_e, |this, c| this.visit_expr(c, e))?;
                self.with_ctx(c, ctx, |this, c| this.visit_block(c, b1))?;
                self.with_ctx(c, ctx, |this, c| this.visit_block(c, b2))
            }
            aast::Stmt_::Do(do_) => {
                let (b, aast::LoopCond(_, _, e)) = &**do_;
                self.with_ctx(c, ctx, |this, c| this.visit_block(c, b))?;
                let ctx_e = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx_e, |this, c| this.visit_expr(c, e))
            }
            aast::Stmt_::While(while_) => {
                let (aast::LoopCond(_, _, e), b) = &**while_;
                let ctx_e = disallow_due_to_cast(ctx, &c.0);
                self.with_ctx(c, ctx_e, |this, c| this.visit_expr(c, e))?;
                self.with_ctx(c, ctx, |this, c| this.visit_block(c, b))
            }
            aast::Stmt_::For(for_) => {
                let (e1, e2, aast::LoopIter(_, _, e3), b) = &**for_;
                for e in e1 {
                    self.with_ctx(c, ctx, |this, c| this.visit_expr(c, e))?;
                }
                if let Some(aast::LoopCond(_, _, e)) = e2 {
                    let ctx_e = disallow_due_to_cast(ctx, &c.0);
                    self.with_ctx(c, ctx_e, |this, c| this.visit_expr(c, e))?;
                }
                for e in e3 {
                    self.with_ctx(c, ctx, |this, c| this.visit_expr(c, e))?;
                }
                self.with_ctx(c, ctx, |this, c| this.visit_block(c, b))
            }
            aast::Stmt_::Switch(switch) => {
                let (e, casel, dfl) = &**switch;
                self.with_ctx(c, disallow_awaitable, |this, c| this.visit_expr(c, e))?;
                for case in casel {
                    self.with_ctx(c, ctx, |this, c| this.visit_case(c, case))?;
                }
                if let Some(dfl) = dfl {
                    self.with_ctx(c, ctx, |this, c| this.visit_default_case(c, dfl))?;
                }
                Ok(())
            }
            // super#on_stmt
            _ => self.with_ctx(c, allow_awaitable, |this, c| stmt.recurse(c, this)),
        }
    }

    /// `on_block`
    fn visit_block(&mut self, c: &mut (Env, Ctx), block: &'a tast::Block) -> Res {
        // super#on_block
        self.with_ctx(c, allow_awaitable, |this, c| block.recurse(c, this))
    }
}

impl<'a> tast_visitor::IterWithState<'a, Ctx> for AwaitableVisitor {}

/// The object `handler`.
struct DiscardedAwaitableCheck;

impl<'a> tast_visitor::Handler<'a> for DiscardedAwaitableCheck {
    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        let _ = visitor().visit_fun_def(&mut (env.clone(), allow_awaitable), fd);
    }

    fn at_method_(&mut self, env: &Env, m: &'a tast::Method_) {
        let _ = visitor().visit_method_(&mut (env.clone(), allow_awaitable), m);
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(DiscardedAwaitableCheck)
}
