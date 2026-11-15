// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_visitor.ml`. See `hh/PORTING.md`.
//!
//! # The visitor classes
//!
//! `Aast.iter` (and `reduce`) is `oxidized::aast_visitor::Visitor`;
//! `Aast.endo` (and `map`, whose `on_'ex` and `on_'en` are the identity here)
//! is `oxidized::aast_visitor::VisitorMut`, which changes the AST in place.
//! The parameters of these visitors over a TAST are [`Params`]: the context
//! (`env` in OCaml) is the [`Env`] (`(env, state)` for
//! [`iter_with_state`]), and visiting cannot fail (`Error = ()`).
//!
//! A class that inherits from `Aast.iter` and overrides some methods is a
//! Rust type implementing `Visitor` and overriding the same `visit_` methods.
//! The classes of this module override some methods of `Aast.iter`; a
//! visitor that inherits from one of them must have these overrides too.
//! Each class is a module of functions, one for each method it defines
//! (`iter::on_method_` is `Tast_visitor.iter#on_method_`), and a macro that
//! writes the `visit_` methods which call them, to put in the `impl Visitor`
//! (or `impl VisitorMut`) of the inheriting visitor:
//!
//! ```ignore
//! impl<'a> Visitor<'a> for MyVisitor {
//!     type Params = tast_visitor::IterParams;
//!     fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
//!         self
//!     }
//!     crate::tast_visitor::iter_methods!('a);
//!     // the methods MyVisitor overrides, as in OCaml
//! }
//! ```
//!
//! A visitor that overrides one of these methods itself names the others
//! (`iter_methods!('a; expr_, method_, class_var, expression_tree)`), and
//! calls the function of the class where OCaml calls `super#on_fun_`
//! (`tast_visitor::iter::on_fun_(self, env, x)`). Where OCaml calls `super`
//! on a method that the class does not override, it is the default of
//! `Visitor`: `x.recurse(env, self)`.
//!
//! The overrides that OCaml writes for one constructor of `expr_`
//! (`on_Assign`, `on_Is`, `on_As`, `on_ET_Splice`) are made by `on_expr_`,
//! which calls the function of the constructor (`iter::on_assign`, ...):
//! `oxidized` has no method for a constructor.
//!
//! In OCaml the environment is a value, and a method that changes it for the
//! children of a node does not change it for the rest of the traversal.
//! Here the context is mutated in place: the functions that change it
//! restore it once the children are visited.
//!
//! `reduce` returns the value of each visit; here the visitor keeps an
//! accumulator (see [`Reduce`]), to which each visit adds its value. With a
//! monoid (`zero` a unit of `plus`, `plus` associative), adding the values of
//! the nodes in the order of the traversal gives what OCaml computes; where
//! OCaml combines values in another order than it visits them (`on_Assign`),
//! the values are computed apart and combined as in OCaml.

use std::marker::PhantomData;
use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::NodeMut;
use oxidized::aast_visitor::Visitor;
use oxidized::aast_visitor::VisitorMut;
use oxidized::ast_defs;

use crate::ctx::Ctx;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::typing_defs::ValKind;

/// The parameters of a visitor over a TAST, whose context is `C`.
pub struct Params<C>(PhantomData<C>);

impl<C> oxidized::aast_visitor::Params for Params<C> {
    type Context = C;
    type Error = ();
    type Ex = tast::Ty;
    type En = tast::SavedEnv;
}

/// The parameters of [`iter`], [`reduce`], [`map`] and [`endo`]: the context
/// is the environment.
pub type IterParams = Params<Env>;

/// The parameters of [`iter_with_state`]: the context is `(env, state)`.
pub type StateParams<S> = Params<(Env, S)>;

/// What every visit returns.
pub type Res = Result<(), ()>;

/// `Aast.expression_tree` of a TAST.
pub type ExpressionTree = aast::ExpressionTree<tast::Ty, tast::SavedEnv>;

fn is_construct(m: &tast::Method_) -> bool {
    m.name.1 == sn::members::__CONSTRUCT
}

/// `class virtual iter`
pub mod iter {
    use super::*;

    type V<'v, 'a> = dyn Visitor<'a, Params = IterParams> + 'v;

    /// Entry point
    pub fn go<'a>(v: &mut V<'_, 'a>, ctx: &Arc<Ctx>, program: &'a [tast::Def]) {
        for x in program {
            go_def(v, ctx, x)
        }
    }

    pub fn go_def<'a>(v: &mut V<'_, 'a>, ctx: &Arc<Ctx>, x: &'a tast::Def) {
        let mut env = tast_env::def_env(ctx, x);
        let _ = v.visit_def(&mut env, x);
    }

    pub fn on_expr_<'a>(v: &mut V<'_, 'a>, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            aast::Expr_::Invalid(_) => Ok(()),
            aast::Expr_::Assign(a) => {
                let (lhs, bop, rhs) = &**a;
                on_assign(v, env, lhs, bop.as_ref(), rhs)
            }
            aast::Expr_::Is(a) => {
                let (e, h) = &**a;
                on_is(v, env, e, h)
            }
            aast::Expr_::As(e) => on_as(v, env, e),
            aast::Expr_::ETSplice(e) => on_et_splice(v, env, e),
            _ => expr_.recurse(env, v),
        }
    }

    pub fn on_fun_<'a>(v: &mut V<'_, 'a>, env: &mut Env, x: &'a tast::Fun_) -> Res {
        let saved = env.clone();
        tast_env::restore_fun_env(env, x);
        let res = x.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_method_<'a>(v: &mut V<'_, 'a>, env: &mut Env, x: &'a tast::Method_) -> Res {
        let saved = env.clone();
        if is_construct(x) {
            tast_env::set_inside_constructor(env)
        } else if x.static_ {
            tast_env::set_static(env)
        }
        tast_env::restore_method_env(env, x);
        let res = x.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_class_var<'a>(v: &mut V<'_, 'a>, env: &mut Env, cv: &'a tast::ClassVar) -> Res {
        let saved = env.clone();
        if cv.is_static {
            tast_env::set_static(env)
        }
        let res = cv.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_assign<'a>(
        v: &mut V<'_, 'a>,
        env: &mut Env,
        lhs: &'a tast::Expr,
        bop: Option<&'a ast_defs::Bop>,
        rhs: &'a tast::Expr,
    ) -> Res {
        if let Some(bop) = bop {
            v.visit_bop(env, bop)?;
        }
        // `self#on_expr (Env.set_val_kind env Lval) lhs`. The visits leave
        // the environment as they find it (each change is undone), so
        // setting the field back gives the environment of before, without
        // keeping a copy (with a copy kept, the write copies the shared
        // records of the environment at every assignment).
        let val_kind = tast_env::get_val_kind(env);
        tast_env::set_val_kind(env, ValKind::Lval);
        let res = v.visit_expr(env, lhs);
        tast_env::set_val_kind(env, val_kind);
        res?;
        v.visit_expr(env, rhs)
    }

    pub fn on_is<'a>(v: &mut V<'_, 'a>, env: &mut Env, e: &'a tast::Expr, h: &'a tast::Hint) -> Res {
        let saved = env.clone();
        tast_env::set_allow_wildcards(env);
        // super#on_Is
        let res = match v.visit_expr(env, e) {
            Ok(()) => v.visit_hint(env, h),
            Err(err) => Err(err),
        };
        *env = saved;
        res
    }

    pub fn on_as<'a>(
        v: &mut V<'_, 'a>,
        env: &mut Env,
        e: &'a aast::As_<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = env.clone();
        tast_env::set_allow_wildcards(env);
        let res = v.visit_as_(env, e);
        *env = saved;
        res
    }

    pub fn on_expression_tree<'a>(
        v: &mut V<'_, 'a>,
        env: &mut Env,
        et: &'a ExpressionTree,
    ) -> Res {
        let aast::ExpressionTree {
            class: et_class,
            runtime_expr: et_runtime_expr,
            free_vars: _,
        } = et;
        v.visit_id(env, et_class)?;
        let saved = env.clone();
        tast_env::inside_expr_tree(env, et_class.clone());
        let res = v.visit_expr(env, et_runtime_expr);
        *env = saved;
        res
    }

    pub fn on_et_splice<'a>(
        v: &mut V<'_, 'a>,
        env: &mut Env,
        e: &'a aast::EtSplice<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = env.clone();
        tast_env::outside_expr_tree(env);
        let res = v.visit_et_splice(env, e);
        *env = saved;
        res
    }
}

/// The `visit_` methods of a visitor that inherits from [`iter`] (all of
/// them, or the ones named after the lifetime).
#[allow(unused_macros)]
macro_rules! iter_methods {
    ($lt:lifetime) => {
        $crate::tast_visitor::iter_methods!($lt; expr_, fun_, method_, class_var, expression_tree);
    };
    ($lt:lifetime; $($m:ident),* $(,)?) => {
        $( $crate::tast_visitor::iter_methods!(@one $lt, $m); )*
    };
    (@one $lt:lifetime, expr_) => {
        fn visit_expr_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Expr_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter::on_expr_(self, env, x)
        }
    };
    (@one $lt:lifetime, fun_) => {
        fn visit_fun_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Fun_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter::on_fun_(self, env, x)
        }
    };
    (@one $lt:lifetime, method_) => {
        fn visit_method_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Method_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter::on_method_(self, env, x)
        }
    };
    (@one $lt:lifetime, class_var) => {
        fn visit_class_var(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::ClassVar,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter::on_class_var(self, env, x)
        }
    };
    (@one $lt:lifetime, expression_tree) => {
        fn visit_expression_tree(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast_visitor::ExpressionTree,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter::on_expression_tree(self, env, x)
        }
    };
}
#[allow(unused_imports)]
pub(crate) use iter_methods;

/// `class virtual ['state] iter_with_state`: the methods that a visitor
/// inheriting from it can override, besides those of `Visitor`.
pub trait IterWithState<'a, S>: Visitor<'a, Params = StateParams<S>> {
    fn on_fun_with_env(&mut self, c: &mut (Env, S), x: &'a tast::Fun_) -> Res {
        // super#on_fun_
        x.recurse(c, self.object())
    }

    fn on_method_with_env(&mut self, c: &mut (Env, S), x: &'a tast::Method_) -> Res {
        // super#on_method_
        x.recurse(c, self.object())
    }

    fn on_class_var_with_env(&mut self, c: &mut (Env, S), cv: &'a tast::ClassVar) -> Res {
        // super#on_class_var
        cv.recurse(c, self.object())
    }
}

/// `class virtual ['state] iter_with_state`
pub mod iter_with_state {
    use super::*;

    /// Entry point
    pub fn go<'a, S: Clone, V: IterWithState<'a, S>>(
        v: &mut V,
        state: S,
        ctx: &Arc<Ctx>,
        program: &'a [tast::Def],
    ) {
        for x in program {
            go_def(v, ctx, state.clone(), x)
        }
    }

    pub fn go_def<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        ctx: &Arc<Ctx>,
        state: S,
        x: &'a tast::Def,
    ) {
        let mut c = (tast_env::def_env(ctx, x), state);
        let _ = v.visit_def(&mut c, x);
    }

    pub fn on_expr_<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        expr_: &'a tast::Expr_,
    ) -> Res {
        match expr_ {
            aast::Expr_::Invalid(_) => Ok(()),
            aast::Expr_::Assign(a) => {
                let (lhs, bop, rhs) = &**a;
                on_assign(v, c, lhs, bop.as_ref(), rhs)
            }
            aast::Expr_::Is(a) => {
                let (e, h) = &**a;
                on_is(v, c, e, h)
            }
            aast::Expr_::As(e) => on_as(v, c, e),
            aast::Expr_::ETSplice(e) => on_et_splice(v, c, e),
            _ => expr_.recurse(c, v),
        }
    }

    /// `on_fun_with_env` is [`IterWithState::on_fun_with_env`].
    pub fn on_fun_<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        x: &'a tast::Fun_,
    ) -> Res {
        let saved = c.0.clone();
        tast_env::restore_fun_env(&mut c.0, x);
        let res = v.on_fun_with_env(c, x);
        c.0 = saved;
        res
    }

    /// `on_method_with_env` is [`IterWithState::on_method_with_env`].
    pub fn on_method_<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        x: &'a tast::Method_,
    ) -> Res {
        let saved = c.0.clone();
        let env = &mut c.0;
        if is_construct(x) {
            tast_env::set_inside_constructor(env)
        } else if x.static_ {
            tast_env::set_static(env)
        }
        tast_env::restore_method_env(env, x);
        let res = v.on_method_with_env(c, x);
        c.0 = saved;
        res
    }

    /// `on_class_var_with_env` is [`IterWithState::on_class_var_with_env`].
    pub fn on_class_var<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        cv: &'a tast::ClassVar,
    ) -> Res {
        let saved = c.0.clone();
        if cv.is_static {
            tast_env::set_static(&mut c.0)
        }
        let res = v.on_class_var_with_env(c, cv);
        c.0 = saved;
        res
    }

    pub fn on_assign<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        lhs: &'a tast::Expr,
        bop: Option<&'a ast_defs::Bop>,
        rhs: &'a tast::Expr,
    ) -> Res {
        if let Some(bop) = bop {
            v.visit_bop(c, bop)?;
        }
        // (As `iter::on_assign`: the visitors that inherit this class leave
        // the environment as they find it.)
        let val_kind = tast_env::get_val_kind(&c.0);
        tast_env::set_val_kind(&mut c.0, ValKind::Lval);
        let res = v.visit_expr(c, lhs);
        tast_env::set_val_kind(&mut c.0, val_kind);
        res?;
        v.visit_expr(c, rhs)
    }

    pub fn on_is<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        e: &'a tast::Expr,
        h: &'a tast::Hint,
    ) -> Res {
        let saved = c.0.clone();
        tast_env::set_allow_wildcards(&mut c.0);
        // super#on_Is
        let res = match v.visit_expr(c, e) {
            Ok(()) => v.visit_hint(c, h),
            Err(err) => Err(err),
        };
        c.0 = saved;
        res
    }

    pub fn on_as<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        e: &'a aast::As_<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = c.0.clone();
        tast_env::set_allow_wildcards(&mut c.0);
        let res = v.visit_as_(c, e);
        c.0 = saved;
        res
    }

    pub fn on_expression_tree<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        et: &'a ExpressionTree,
    ) -> Res {
        let aast::ExpressionTree {
            class: et_class,
            runtime_expr: et_runtime_expr,
            free_vars: _,
        } = et;
        v.visit_id(c, et_class)?;
        let saved = c.0.clone();
        tast_env::inside_expr_tree(&mut c.0, et_class.clone());
        let res = v.visit_expr(c, et_runtime_expr);
        c.0 = saved;
        res
    }

    pub fn on_et_splice<'a, S, V: IterWithState<'a, S>>(
        v: &mut V,
        c: &mut (Env, S),
        e: &'a aast::EtSplice<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = c.0.clone();
        tast_env::outside_expr_tree(&mut c.0);
        let res = v.visit_et_splice(c, e);
        c.0 = saved;
        res
    }
}

/// The `visit_` methods of a visitor that inherits from [`iter_with_state`]
/// (all of them, or the ones named after the lifetime). The visitor also
/// implements [`IterWithState`].
#[allow(unused_macros)]
macro_rules! iter_with_state_methods {
    ($lt:lifetime) => {
        $crate::tast_visitor::iter_with_state_methods!(
            $lt; expr_, fun_, method_, class_var, expression_tree
        );
    };
    ($lt:lifetime; $($m:ident),* $(,)?) => {
        $( $crate::tast_visitor::iter_with_state_methods!(@one $lt, $m); )*
    };
    (@one $lt:lifetime, expr_) => {
        fn visit_expr_(
            &mut self,
            c: &mut <Self::Params as ::oxidized::aast_visitor::Params>::Context,
            x: &$lt $crate::tast::Expr_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter_with_state::on_expr_(self, c, x)
        }
    };
    (@one $lt:lifetime, fun_) => {
        fn visit_fun_(
            &mut self,
            c: &mut <Self::Params as ::oxidized::aast_visitor::Params>::Context,
            x: &$lt $crate::tast::Fun_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter_with_state::on_fun_(self, c, x)
        }
    };
    (@one $lt:lifetime, method_) => {
        fn visit_method_(
            &mut self,
            c: &mut <Self::Params as ::oxidized::aast_visitor::Params>::Context,
            x: &$lt $crate::tast::Method_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter_with_state::on_method_(self, c, x)
        }
    };
    (@one $lt:lifetime, class_var) => {
        fn visit_class_var(
            &mut self,
            c: &mut <Self::Params as ::oxidized::aast_visitor::Params>::Context,
            x: &$lt $crate::tast::ClassVar,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter_with_state::on_class_var(self, c, x)
        }
    };
    (@one $lt:lifetime, expression_tree) => {
        fn visit_expression_tree(
            &mut self,
            c: &mut <Self::Params as ::oxidized::aast_visitor::Params>::Context,
            x: &$lt $crate::tast_visitor::ExpressionTree,
        ) -> Result<(), ()> {
            $crate::tast_visitor::iter_with_state::on_expression_tree(self, c, x)
        }
    };
}
#[allow(unused_imports)]
pub(crate) use iter_with_state_methods;

/// `class virtual ['a] reduce`: `zero` and `plus` are the virtual methods of
/// OCaml; the result of each visit is added to the accumulator ([`acc`]),
/// which [`reduce::go`] and [`reduce::go_def`] (and [`reduce::result`]) start
/// at `zero`.
///
/// [`acc`]: Reduce::acc
pub trait Reduce<'a>: Visitor<'a, Params = IterParams> {
    /// The `'a` of `['a] reduce`.
    type Acc;

    fn zero(&self) -> Self::Acc;

    fn plus(&self, a: Self::Acc, b: Self::Acc) -> Self::Acc;

    /// The accumulator to which every visit adds its result.
    fn acc(&mut self) -> &mut Self::Acc;
}

/// `class virtual ['a] reduce`
pub mod reduce {
    use super::*;

    /// The result of the visits that `f` makes (what they add to the
    /// accumulator, from `zero`), leaving the accumulator as it was.
    pub fn result<'a, V: Reduce<'a>>(v: &mut V, f: impl FnOnce(&mut V) -> Res) -> (Res, V::Acc) {
        let zero = v.zero();
        let outer = std::mem::replace(v.acc(), zero);
        let res = f(v);
        let r = std::mem::replace(v.acc(), outer);
        (res, r)
    }

    /// Add the result `r` of a visit to the accumulator.
    pub fn add<'a, V: Reduce<'a>>(v: &mut V, r: V::Acc) {
        let zero = v.zero();
        let acc = std::mem::replace(v.acc(), zero);
        let acc = v.plus(acc, r);
        *v.acc() = acc;
    }

    /// Entry point
    pub fn go<'a, V: Reduce<'a>>(v: &mut V, ctx: &Arc<Ctx>, program: &'a [tast::Def]) -> V::Acc {
        // `self#on_list`: `List.fold_left (fun s x -> self#plus s (f x)) self#zero`
        let mut s = v.zero();
        for x in program {
            let r = go_def(v, ctx, x);
            s = v.plus(s, r);
        }
        s
    }

    pub fn go_def<'a, V: Reduce<'a>>(v: &mut V, ctx: &Arc<Ctx>, x: &'a tast::Def) -> V::Acc {
        let mut env = tast_env::def_env(ctx, x);
        let (_, r) = result(v, |v| v.visit_def(&mut env, x));
        r
    }

    pub fn on_expr_<'a, V: Reduce<'a>>(v: &mut V, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        match expr_ {
            // self#zero
            aast::Expr_::Invalid(_) => Ok(()),
            aast::Expr_::Assign(a) => {
                let (lhs, bop, rhs) = &**a;
                on_assign(v, env, lhs, bop.as_ref(), rhs)
            }
            aast::Expr_::Is(a) => {
                let (e, h) = &**a;
                on_is(v, env, e, h)
            }
            aast::Expr_::As(e) => on_as(v, env, e),
            aast::Expr_::ETSplice(e) => on_et_splice(v, env, e),
            _ => expr_.recurse(env, v),
        }
    }

    pub fn on_fun_<'a, V: Reduce<'a>>(v: &mut V, env: &mut Env, x: &'a tast::Fun_) -> Res {
        let saved = env.clone();
        tast_env::restore_fun_env(env, x);
        let res = x.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_method_<'a, V: Reduce<'a>>(v: &mut V, env: &mut Env, x: &'a tast::Method_) -> Res {
        let saved = env.clone();
        if is_construct(x) {
            tast_env::set_inside_constructor(env)
        } else if x.static_ {
            tast_env::set_static(env)
        }
        tast_env::restore_method_env(env, x);
        let res = x.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_class_var<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        cv: &'a tast::ClassVar,
    ) -> Res {
        let saved = env.clone();
        if cv.is_static {
            tast_env::set_static(env)
        }
        let res = cv.recurse(env, v);
        *env = saved;
        res
    }

    pub fn on_assign<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        lhs: &'a tast::Expr,
        bop: Option<&'a ast_defs::Bop>,
        rhs: &'a tast::Expr,
    ) -> Res {
        let op = match bop {
            None => None,
            Some(bop) => {
                let (res, op) = result(v, |v| v.visit_bop(env, bop));
                res?;
                Some(op)
            }
        };
        let (res, e1) = result(v, |v| {
            let saved = env.clone();
            tast_env::set_val_kind(env, ValKind::Lval);
            let res = v.visit_expr(env, lhs);
            *env = saved;
            res
        });
        res?;
        let (res, e2) = result(v, |v| v.visit_expr(env, rhs));
        res?;
        let r = match op {
            Some(op) => {
                let op_e2 = v.plus(op, e2);
                v.plus(e1, op_e2)
            }
            None => v.plus(e1, e2),
        };
        add(v, r);
        Ok(())
    }

    pub fn on_is<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        e: &'a tast::Expr,
        h: &'a tast::Hint,
    ) -> Res {
        let saved = env.clone();
        tast_env::set_allow_wildcards(env);
        // super#on_Is
        let res = match v.visit_expr(env, e) {
            Ok(()) => v.visit_hint(env, h),
            Err(err) => Err(err),
        };
        *env = saved;
        res
    }

    pub fn on_as<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        e: &'a aast::As_<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = env.clone();
        tast_env::set_allow_wildcards(env);
        let res = v.visit_as_(env, e);
        *env = saved;
        res
    }

    pub fn on_expression_tree<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        et: &'a ExpressionTree,
    ) -> Res {
        let aast::ExpressionTree {
            class: cls,
            runtime_expr: et_runtime_expr,
            free_vars: _,
        } = et;
        // `self#plus et_class et_runtime_expr`, in the order of the visits.
        v.visit_id(env, cls)?;
        let saved = env.clone();
        tast_env::inside_expr_tree(env, cls.clone());
        let res = v.visit_expr(env, et_runtime_expr);
        *env = saved;
        res
    }

    pub fn on_et_splice<'a, V: Reduce<'a>>(
        v: &mut V,
        env: &mut Env,
        e: &'a aast::EtSplice<tast::Ty, tast::SavedEnv>,
    ) -> Res {
        let saved = env.clone();
        tast_env::outside_expr_tree(env);
        let res = v.visit_et_splice(env, e);
        *env = saved;
        res
    }
}

/// The `visit_` methods of a visitor that inherits from [`reduce`] (all of
/// them, or the ones named after the lifetime). The visitor also implements
/// [`Reduce`].
#[allow(unused_macros)]
macro_rules! reduce_methods {
    ($lt:lifetime) => {
        $crate::tast_visitor::reduce_methods!($lt; expr_, fun_, method_, class_var, expression_tree);
    };
    ($lt:lifetime; $($m:ident),* $(,)?) => {
        $( $crate::tast_visitor::reduce_methods!(@one $lt, $m); )*
    };
    (@one $lt:lifetime, expr_) => {
        fn visit_expr_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Expr_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::reduce::on_expr_(self, env, x)
        }
    };
    (@one $lt:lifetime, fun_) => {
        fn visit_fun_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Fun_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::reduce::on_fun_(self, env, x)
        }
    };
    (@one $lt:lifetime, method_) => {
        fn visit_method_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::Method_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::reduce::on_method_(self, env, x)
        }
    };
    (@one $lt:lifetime, class_var) => {
        fn visit_class_var(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast::ClassVar,
        ) -> Result<(), ()> {
            $crate::tast_visitor::reduce::on_class_var(self, env, x)
        }
    };
    (@one $lt:lifetime, expression_tree) => {
        fn visit_expression_tree(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt $crate::tast_visitor::ExpressionTree,
        ) -> Result<(), ()> {
            $crate::tast_visitor::reduce::on_expression_tree(self, env, x)
        }
    };
}
#[allow(unused_imports)]
pub(crate) use reduce_methods;

/// The functions of `map` and `endo`, which differ only in the order in
/// which `on_Assign` visits its children.
macro_rules! map_like {
    ($on_assign_body:item) => {
        use super::*;

        type V<'v, 'a> = dyn VisitorMut<'a, Params = IterParams> + 'v;

        // method on_'ex _ ex = ex
        // method on_'en _ en = en
        // (the defaults of `VisitorMut`, which leave them as they are)

        /// Entry point
        pub fn go<'a>(v: &mut V<'_, 'a>, ctx: &Arc<Ctx>, program: &'a mut [tast::Def]) {
            for x in program {
                go_def(v, ctx, x)
            }
        }

        pub fn go_def<'a>(v: &mut V<'_, 'a>, ctx: &Arc<Ctx>, x: &'a mut tast::Def) {
            let mut env = tast_env::def_env(ctx, x);
            let _ = v.visit_def(&mut env, x);
        }

        pub fn on_expr_<'a>(v: &mut V<'_, 'a>, env: &mut Env, expr_: &'a mut tast::Expr_) -> Res {
            match expr_ {
                aast::Expr_::Invalid(_) => Ok(()),
                aast::Expr_::Assign(a) => {
                    let (lhs, bop, rhs) = &mut **a;
                    on_assign(v, env, lhs, bop.as_mut(), rhs)
                }
                aast::Expr_::Is(a) => {
                    let (e, h) = &mut **a;
                    on_is(v, env, e, h)
                }
                aast::Expr_::As(e) => on_as(v, env, e),
                aast::Expr_::ETSplice(e) => on_et_splice(v, env, e),
                _ => expr_.recurse(env, v),
            }
        }

        pub fn on_fun_<'a>(v: &mut V<'_, 'a>, env: &mut Env, x: &'a mut tast::Fun_) -> Res {
            let saved = env.clone();
            tast_env::restore_fun_env(env, x);
            let res = x.recurse(env, v);
            *env = saved;
            res
        }

        pub fn on_method_<'a>(v: &mut V<'_, 'a>, env: &mut Env, x: &'a mut tast::Method_) -> Res {
            let saved = env.clone();
            if is_construct(x) {
                tast_env::set_inside_constructor(env)
            } else if x.static_ {
                tast_env::set_static(env)
            }
            tast_env::restore_method_env(env, x);
            let res = x.recurse(env, v);
            *env = saved;
            res
        }

        pub fn on_class_var<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            cv: &'a mut tast::ClassVar,
        ) -> Res {
            let saved = env.clone();
            if cv.is_static {
                tast_env::set_static(env)
            }
            let res = cv.recurse(env, v);
            *env = saved;
            res
        }

        $on_assign_body

        pub fn on_is<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            e: &'a mut tast::Expr,
            h: &'a mut tast::Hint,
        ) -> Res {
            let saved = env.clone();
            tast_env::set_allow_wildcards(env);
            // super#on_Is
            let res = match v.visit_expr(env, e) {
                Ok(()) => v.visit_hint(env, h),
                Err(err) => Err(err),
            };
            *env = saved;
            res
        }

        pub fn on_as<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            e: &'a mut aast::As_<tast::Ty, tast::SavedEnv>,
        ) -> Res {
            let saved = env.clone();
            tast_env::set_allow_wildcards(env);
            let res = v.visit_as_(env, e);
            *env = saved;
            res
        }

        pub fn on_expression_tree<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            et: &'a mut ExpressionTree,
        ) -> Res {
            let aast::ExpressionTree {
                class: et_class,
                runtime_expr: et_runtime_expr,
                free_vars: _,
            } = et;
            // OCaml calls `Env.inside_expr_tree` with the `et_class` that
            // `self#on_id` returns. A node visited in place cannot be read
            // again here (`VisitorMut` borrows it for the whole traversal):
            // this is the `et_class` before the visit, which is the same unless
            // the visitor rewrites identifiers (`on_id` is the identity in
            // `Tast_visitor` and in every visitor that inherits from it).
            let et_class_ = et_class.clone();
            v.visit_id(env, et_class)?;
            let saved = env.clone();
            tast_env::inside_expr_tree(env, et_class_);
            let res = v.visit_expr(env, et_runtime_expr);
            *env = saved;
            res
        }

        pub fn on_et_splice<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            e: &'a mut aast::EtSplice<tast::Ty, tast::SavedEnv>,
        ) -> Res {
            let saved = env.clone();
            tast_env::outside_expr_tree(env);
            let res = v.visit_et_splice(env, e);
            *env = saved;
            res
        }
    };
}

/// `class virtual map`. `Aast.map` builds a new AST; here the AST is changed
/// in place, as by [`endo`] (`on_'ex` and `on_'en` are the identity, so the
/// AST keeps its type).
pub mod map {
    map_like! {
        pub fn on_assign<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            lhs: &'a mut tast::Expr,
            bop: Option<&'a mut ast_defs::Bop>,
            rhs: &'a mut tast::Expr,
        ) -> Res {
            v.visit_expr(env, rhs)?;
            let saved = env.clone();
            tast_env::set_val_kind(env, ValKind::Lval);
            let res = v.visit_expr(env, lhs);
            *env = saved;
            res?;
            match bop {
                Some(bop) => v.visit_bop(env, bop),
                None => Ok(()),
            }
        }
    }
}

/// `class virtual endo`
pub mod endo {
    map_like! {
        pub fn on_assign<'a>(
            v: &mut V<'_, 'a>,
            env: &mut Env,
            e1: &'a mut tast::Expr,
            bop: Option<&'a mut ast_defs::Bop>,
            e2: &'a mut tast::Expr,
        ) -> Res {
            if let Some(bop) = bop {
                v.visit_bop(env, bop)?;
            }
            let saved = env.clone();
            tast_env::set_val_kind(env, ValKind::Lval);
            let res = v.visit_expr(env, e1);
            *env = saved;
            res?;
            v.visit_expr(env, e2)
        }
    }
}

/// The `visit_` methods of a `VisitorMut` that inherits from [`map`] or
/// [`endo`] (`map_methods!(map, 'a)`, `map_methods!(endo, 'a)`; all of them,
/// or the ones named after the lifetime).
#[allow(unused_macros)]
macro_rules! map_methods {
    ($class:ident, $lt:lifetime) => {
        $crate::tast_visitor::map_methods!(
            $class, $lt; expr_, fun_, method_, class_var, expression_tree
        );
    };
    ($class:ident, $lt:lifetime; $($m:ident),* $(,)?) => {
        $( $crate::tast_visitor::map_methods!(@one $class, $lt, $m); )*
    };
    (@one $class:ident, $lt:lifetime, expr_) => {
        fn visit_expr_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt mut $crate::tast::Expr_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::$class::on_expr_(self, env, x)
        }
    };
    (@one $class:ident, $lt:lifetime, fun_) => {
        fn visit_fun_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt mut $crate::tast::Fun_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::$class::on_fun_(self, env, x)
        }
    };
    (@one $class:ident, $lt:lifetime, method_) => {
        fn visit_method_(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt mut $crate::tast::Method_,
        ) -> Result<(), ()> {
            $crate::tast_visitor::$class::on_method_(self, env, x)
        }
    };
    (@one $class:ident, $lt:lifetime, class_var) => {
        fn visit_class_var(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt mut $crate::tast::ClassVar,
        ) -> Result<(), ()> {
            $crate::tast_visitor::$class::on_class_var(self, env, x)
        }
    };
    (@one $class:ident, $lt:lifetime, expression_tree) => {
        fn visit_expression_tree(
            &mut self,
            env: &mut $crate::tast_env::Env,
            x: &$lt mut $crate::tast_visitor::ExpressionTree,
        ) -> Result<(), ()> {
            $crate::tast_visitor::$class::on_expression_tree(self, env, x)
        }
    };
}
#[allow(unused_imports)]
pub(crate) use map_methods;

/// `class type handler`: an [`iter`] visitor which is not in control of the
/// iteration (and thus cannot change the order of the iteration or choose not
/// to visit some subtrees).
///
/// Intended to be used with [`iter_with`] to aggregate many checks into a
/// single pass over a TAST.
///
/// The default methods do nothing: a handler that implements only some of
/// them is OCaml's `inherit Tast_visitor.handler_base` ([`HandlerBase`]).
/// A handler is given the environment of the traversal, which it cannot
/// change (OCaml's is a value): to call a function that takes `&mut Env`,
/// clone it.
#[allow(unused_variables)]
pub trait Handler<'a> {
    fn at_class_(&mut self, env: &Env, x: &'a tast::Class_) {}

    fn at_typedef(&mut self, env: &Env, x: &'a tast::Typedef) {}

    fn at_gconst(&mut self, env: &Env, x: &'a tast::Gconst) {}

    fn at_fun_def(&mut self, env: &Env, x: &'a tast::FunDef) {}

    fn at_module_def(&mut self, env: &Env, x: &'a tast::ModuleDef) {}

    fn at_method_(&mut self, env: &Env, x: &'a tast::Method_) {}

    fn at_expr(&mut self, env: &Env, x: &'a tast::Expr) {}

    fn at_stmt(&mut self, env: &Env, x: &'a tast::Stmt) {}

    fn at_fun_(&mut self, env: &Env, x: &'a tast::Fun_) {}

    fn at_call(&mut self, env: &Env, x: &'a tast::CallExpr) {}

    fn at_hint(&mut self, env: &Env, x: &'a tast::Hint) {}

    fn at_tparam(&mut self, env: &Env, x: &'a tast::Tparam) {}

    fn at_user_attribute(&mut self, env: &Env, x: &'a tast::UserAttribute) {}

    fn at_class_const(&mut self, env: &Env, x: &'a tast::ClassConst) {}

    fn at_class_typeconst_def(&mut self, env: &Env, x: &'a tast::ClassTypeconstDef) {}

    fn at_xhp_child(&mut self, env: &Env, x: &'a tast::XhpChild) {}
}

/// `class virtual handler_base`: a [`Handler`] which does not need to make use
/// of every visitation method implements only those it needs (the others are
/// the no-ops of the trait). This is the handler that does nothing.
pub struct HandlerBase;

impl<'a> Handler<'a> for HandlerBase {}

/// The visitor that [`iter_with`] returns (it inherits from [`iter`]).
pub struct IterWith<'a> {
    catch_handler_exceptions: bool,
    handlers: Vec<Box<dyn Handler<'a> + 'a>>,
    /// The handlers `handlers[start..end]` are warning checks, whose
    /// warnings are recorded (see [`iter_with_recording_warnings`]).
    warning_handlers: Option<(usize, usize)>,
}

/// Return an [`iter`] visitor which invokes all of the given handlers upon
/// visiting each node.
///
/// When `catch_handler_exceptions` is true, each handler invocation is wrapped
/// in a try/catch so that an exception in one handler does not prevent other
/// handlers from running or the traversal from continuing. This is used when
/// running checks on the dynamic TAST where the inference env may reference
/// type variables that no longer exist. (An OCaml exception is a panic here;
/// the panic hook still prints it.)
pub fn iter_with<'a>(
    catch_handler_exceptions: Option<bool>,
    handlers: Vec<Box<dyn Handler<'a> + 'a>>,
) -> IterWith<'a> {
    let catch_handler_exceptions = catch_handler_exceptions.unwrap_or(false);
    IterWith {
        catch_handler_exceptions,
        handlers,
        warning_handlers: None,
    }
}

/// [`iter_with`], where `handlers[warning_handlers]` are the warning checks:
/// they run with `diagnostics::set_recording_warning_check` on (see
/// `diagnostics::start_recording_warning_keys`). No OCaml counterpart.
pub fn iter_with_recording_warnings<'a>(
    catch_handler_exceptions: Option<bool>,
    handlers: Vec<Box<dyn Handler<'a> + 'a>>,
    warning_handlers: std::ops::Range<usize>,
) -> IterWith<'a> {
    IterWith {
        warning_handlers: Some((warning_handlers.start, warning_handlers.end)),
        ..iter_with(catch_handler_exceptions, handlers)
    }
}

/// `invoke`
fn invoke(catch_handler_exceptions: bool, f: impl FnOnce()) {
    if catch_handler_exceptions {
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    } else {
        f()
    }
}

impl<'a> IterWith<'a> {
    /// Entry point (`go` of [`iter`])
    pub fn go(&mut self, ctx: &Arc<Ctx>, program: &'a [tast::Def]) {
        iter::go(self, ctx, program)
    }

    /// `go_def` of [`iter`]
    pub fn go_def(&mut self, ctx: &Arc<Ctx>, x: &'a tast::Def) {
        iter::go_def(self, ctx, x)
    }
}

/// `List.iter handlers ~f:(fun v -> invoke (fun () -> v#at_x env x))`
macro_rules! handlers {
    ($self:ident, $at:ident, $env:expr, $x:expr) => {
        match $self.warning_handlers {
            None => {
                for v in $self.handlers.iter_mut() {
                    invoke($self.catch_handler_exceptions, || v.$at($env, $x));
                }
            }
            Some((start, end)) => {
                let catch = $self.catch_handler_exceptions;
                for (i, v) in $self.handlers.iter_mut().enumerate() {
                    if i == start {
                        crate::diagnostics::set_recording_warning_check(true)
                    }
                    if i == end {
                        crate::diagnostics::set_recording_warning_check(false)
                    }
                    invoke(catch, || v.$at($env, $x));
                }
                if end == $self.handlers.len() {
                    crate::diagnostics::set_recording_warning_check(false)
                }
            }
        }
    };
}

impl<'a> Visitor<'a> for IterWith<'a> {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    iter_methods!('a; expr_, class_var, expression_tree);

    fn visit_class_(&mut self, env: &mut Env, x: &'a tast::Class_) -> Res {
        handlers!(self, at_class_, env, x);
        x.recurse(env, self)
    }

    fn visit_typedef(&mut self, env: &mut Env, x: &'a tast::Typedef) -> Res {
        handlers!(self, at_typedef, env, x);
        x.recurse(env, self)
    }

    fn visit_gconst(&mut self, env: &mut Env, x: &'a tast::Gconst) -> Res {
        handlers!(self, at_gconst, env, x);
        x.recurse(env, self)
    }

    fn visit_fun_def(&mut self, env: &mut Env, x: &'a tast::FunDef) -> Res {
        handlers!(self, at_fun_def, env, x);
        x.recurse(env, self)
    }

    fn visit_module_def(&mut self, env: &mut Env, x: &'a tast::ModuleDef) -> Res {
        handlers!(self, at_module_def, env, x);
        x.recurse(env, self)
    }

    fn visit_method_(&mut self, env: &mut Env, x: &'a tast::Method_) -> Res {
        handlers!(self, at_method_, env, x);
        iter::on_method_(self, env, x)
    }

    fn visit_expr(&mut self, env: &mut Env, x: &'a tast::Expr) -> Res {
        handlers!(self, at_expr, env, x);
        x.recurse(env, self)
    }

    fn visit_stmt(&mut self, env: &mut Env, x: &'a tast::Stmt) -> Res {
        handlers!(self, at_stmt, env, x);
        x.recurse(env, self)
    }

    fn visit_fun_(&mut self, env: &mut Env, x: &'a tast::Fun_) -> Res {
        handlers!(self, at_fun_, env, x);
        iter::on_fun_(self, env, x)
    }

    /// `on_Call` (`call_expr` is only found under `Call`)
    fn visit_call_expr(&mut self, env: &mut Env, call_expr: &'a tast::CallExpr) -> Res {
        handlers!(self, at_call, env, call_expr);
        call_expr.recurse(env, self)
    }

    fn visit_hint(&mut self, env: &mut Env, h: &'a tast::Hint) -> Res {
        handlers!(self, at_hint, env, h);
        h.recurse(env, self)
    }

    fn visit_tparam(&mut self, env: &mut Env, h: &'a tast::Tparam) -> Res {
        handlers!(self, at_tparam, env, h);
        h.recurse(env, self)
    }

    fn visit_user_attribute(&mut self, env: &mut Env, ua: &'a tast::UserAttribute) -> Res {
        handlers!(self, at_user_attribute, env, ua);
        ua.recurse(env, self)
    }

    fn visit_class_const(&mut self, env: &mut Env, tc: &'a tast::ClassConst) -> Res {
        handlers!(self, at_class_const, env, tc);
        tc.recurse(env, self)
    }

    fn visit_class_typeconst_def(&mut self, env: &mut Env, tc: &'a tast::ClassTypeconstDef) -> Res {
        handlers!(self, at_class_typeconst_def, env, tc);
        tc.recurse(env, self)
    }

    fn visit_xhp_child(&mut self, env: &mut Env, c: &'a tast::XhpChild) -> Res {
        handlers!(self, at_xhp_child, env, c);
        c.recurse(env, self)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use oxidized::aast::Expr;
    use oxidized::aast::Expr_;
    use oxidized::aast::Lid;
    use oxidized::aast::Stmt;
    use oxidized::aast::Stmt_;
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;
    use oxidized::typechecker_options::TypecheckerOptions;

    use super::*;

    fn ctx() -> Arc<Ctx> {
        Arc::new(Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap())
    }

    fn ty() -> tast::Ty {
        crate::typing_make_type::mixed(crate::typing_reason::none())
    }

    fn lvar(name: &str) -> tast::Expr {
        Expr(
            ty(),
            Pos::NONE,
            Expr_::Lvar(Box::new(Lid(
                Pos::NONE,
                oxidized::local_id::make_unscoped(name),
            ))),
        )
    }

    fn expr(e: tast::Expr_) -> tast::Expr {
        Expr(ty(), Pos::NONE, e)
    }

    /// `$x = ($y is int)` (with `bop` for `$x op= ...`), then `Invalid($z)`,
    /// as top-level statements.
    fn program(bop: Option<ast_defs::Bop>) -> Vec<tast::Def> {
        let is = expr(Expr_::Is(Box::new((
            lvar("$y"),
            tast::Hint(Pos::NONE, Box::new(tast::Hint_::Hprim(Tprim::Tint))),
        ))));
        let assign = expr(Expr_::Assign(Box::new((lvar("$x"), bop, is))));
        let invalid = expr(Expr_::Invalid(Box::new(Some(lvar("$z")))));
        vec![
            aast::Def::Stmt(Box::new(Stmt(Pos::NONE, Stmt_::Expr(Box::new(assign))))),
            aast::Def::Stmt(Box::new(Stmt(Pos::NONE, Stmt_::Expr(Box::new(invalid))))),
        ]
    }

    fn lvar_name(e: &tast::Expr) -> Option<String> {
        match &e.2 {
            Expr_::Lvar(lid) => Some(lid.1.1.clone()),
            _ => None,
        }
    }

    /// The local variables, with the value kind and `allow_wildcards` of the
    /// environment they are visited in.
    struct Recorder(Vec<(String, bool, bool)>);

    impl<'a> Visitor<'a> for Recorder {
        type Params = IterParams;

        fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
            self
        }

        iter_methods!('a);

        fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> Res {
            if let Some(name) = lvar_name(e) {
                let lval = matches!(tast_env::get_val_kind(env), ValKind::Lval);
                self.0.push((name, lval, tast_env::get_allow_wildcards(env)));
            }
            e.recurse(env, self)
        }
    }

    #[test]
    fn iter_environment_of_children() {
        let program = program(None);
        let mut v = Recorder(vec![]);
        iter::go(&mut v, &ctx(), &program);
        assert_eq!(
            v.0,
            vec![
                ("$x".to_string(), true, false),
                ("$y".to_string(), false, true),
            ]
        );
    }

    /// The local variables as a list: `plus` is `@`.
    struct Names {
        acc: Vec<String>,
        visited: Vec<String>,
    }

    impl<'a> Reduce<'a> for Names {
        type Acc = Vec<String>;

        fn zero(&self) -> Vec<String> {
            vec![]
        }

        fn plus(&self, mut a: Vec<String>, b: Vec<String>) -> Vec<String> {
            a.extend(b);
            a
        }

        fn acc(&mut self) -> &mut Vec<String> {
            &mut self.acc
        }
    }

    impl<'a> Visitor<'a> for Names {
        type Params = IterParams;

        fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
            self
        }

        reduce_methods!('a);

        fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> Res {
            if let Some(name) = lvar_name(e) {
                self.visited.push(name.clone());
                reduce::add(self, vec![name]);
            }
            e.recurse(env, self)
        }

        fn visit_bop(&mut self, _env: &mut Env, _bop: &'a ast_defs::Bop) -> Res {
            self.visited.push("op".to_string());
            reduce::add(self, vec!["op".to_string()]);
            Ok(())
        }
    }

    #[test]
    fn reduce_combines_as_ocaml() {
        let program = program(Some(ast_defs::Bop::Plus));
        let mut v = Names {
            acc: vec![],
            visited: vec![],
        };
        let r = reduce::go(&mut v, &ctx(), &program);
        // `self#plus e1 (self#plus op e2)`, visited in the order op, e1, e2
        assert_eq!(r, vec!["$x", "op", "$y"]);
        assert_eq!(v.visited, vec!["op", "$x", "$y"]);
        assert!(v.acc.is_empty());
    }

    /// Records the order of the visits and renames the local variables.
    struct Renamer(Vec<String>);

    impl Renamer {
        fn visit(&mut self, e: &mut tast::Expr) {
            if let Expr_::Lvar(lid) = &mut e.2 {
                self.0.push(lid.1.1.clone());
                lid.1.1.push('!');
            }
        }
    }

    struct EndoRenamer(Renamer);

    impl<'a> VisitorMut<'a> for EndoRenamer {
        type Params = IterParams;

        fn object(&mut self) -> &mut dyn VisitorMut<'a, Params = Self::Params> {
            self
        }

        map_methods!(endo, 'a);

        fn visit_expr(&mut self, env: &mut Env, e: &'a mut tast::Expr) -> Res {
            self.0.visit(e);
            e.recurse(env, self)
        }

        fn visit_bop(&mut self, _env: &mut Env, _bop: &'a mut ast_defs::Bop) -> Res {
            self.0.0.push("op".to_string());
            Ok(())
        }
    }

    struct MapRenamer(Renamer);

    impl<'a> VisitorMut<'a> for MapRenamer {
        type Params = IterParams;

        fn object(&mut self) -> &mut dyn VisitorMut<'a, Params = Self::Params> {
            self
        }

        map_methods!(map, 'a);

        fn visit_expr(&mut self, env: &mut Env, e: &'a mut tast::Expr) -> Res {
            self.0.visit(e);
            e.recurse(env, self)
        }

        fn visit_bop(&mut self, _env: &mut Env, _bop: &'a mut ast_defs::Bop) -> Res {
            self.0.0.push("op".to_string());
            Ok(())
        }
    }

    #[test]
    fn endo_and_map_order() {
        let mut program1 = program(Some(ast_defs::Bop::Plus));
        let mut v = EndoRenamer(Renamer(vec![]));
        endo::go(&mut v, &ctx(), &mut program1);
        assert_eq!(v.0.0, vec!["op", "$x", "$y"]);
        let mut program2 = program(Some(ast_defs::Bop::Plus));
        let mut v = MapRenamer(Renamer(vec![]));
        map::go(&mut v, &ctx(), &mut program2);
        assert_eq!(v.0.0, vec!["$y", "$x", "op"]);
        // The variables are renamed in place, but not under `Invalid`.
        let mut v = Recorder(vec![]);
        iter::go(&mut v, &ctx(), &program2);
        let names: Vec<&str> = v.0.iter().map(|(n, _, _)| n.as_str()).collect();
        assert_eq!(names, vec!["$x!", "$y!"]);
        match &program2[1] {
            aast::Def::Stmt(s) => match &s.1 {
                Stmt_::Expr(e) => match &e.2 {
                    Expr_::Invalid(e) => {
                        assert_eq!(lvar_name(e.as_ref().as_ref().unwrap()).unwrap(), "$z")
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            },
            _ => panic!(),
        }
    }

    struct CountExprs<'c>(&'c std::cell::Cell<usize>);

    impl<'a> Handler<'a> for CountExprs<'_> {
        fn at_expr(&mut self, _env: &Env, _e: &'a tast::Expr) {
            self.0.set(self.0.get() + 1)
        }
    }

    struct Panics;

    impl<'a> Handler<'a> for Panics {
        fn at_expr(&mut self, _env: &Env, _e: &'a tast::Expr) {
            panic!("handler failure")
        }
    }

    #[test]
    fn iter_with_handlers() {
        let program = program(None);
        let count = std::cell::Cell::new(0);
        {
            let mut v = iter_with(None, vec![Box::new(HandlerBase), Box::new(CountExprs(&count))]);
            v.go(&ctx(), &program);
        }
        // the assignment, `$x`, the `is`, `$y` and the invalid expression
        assert_eq!(count.get(), 5);
        count.set(0);
        {
            let mut v = iter_with(
                Some(true),
                vec![Box::new(Panics), Box::new(CountExprs(&count))],
            );
            v.go(&ctx(), &program);
        }
        assert_eq!(count.get(), 5);
    }
}
