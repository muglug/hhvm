// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linting_visitors.ml`. See `hh/PORTING.md`.
//!
//! # The functors
//!
//! In OCaml a linter of function bodies is a functor `VisitorFunctor
//! (Parent : BodyVisitorModule) : BodyVisitorModule`, whose class inherits
//! `Parent.visitor` and overrides some methods of
//! `Nast.Visitor_DEPRECATED.visitor`, calling `parent#on_x` to go on.
//! [`add_visitor`] stacks the functors of every linter on the
//! `GenericBodyVisitor`, so that all of them run in one pass: the last one
//! added is the outermost class, and a method call on the object (`this#on_x`)
//! runs the override of the outermost linter that has one, which calls its
//! parent's, and so on down to the generic visitor.
//!
//! Here a [`BodyVisitorFunctor`] makes a [`BodyVisitorModule`] (the object
//! part of one linter, its fields and its overrides) from the `lint_env`; the
//! object is a [`BodyVisitor`]: the stack of layers, innermost first. Each
//! overridable method `on_x` of the object has an `on_x_at(depth, ..)`, which
//! runs the method of the class at that depth of the stack (0 is the generic
//! visitor): `this#on_x` is `on_x_at(layers.len(), ..)`, and a layer at index
//! `i` calls `parent#on_x` as `this.on_x_at(i, ..)` (the `depth` it is given).
//! The layers keep their fields in `Cell`s/`RefCell`s, as the methods take the
//! whole object (`this`) mutably.
//!
//! The overridable methods are the ones the linters of the open-source build
//! override (`on_block`, `on_stmt`, `on_expr`, `on_foreach`, `on_as_expr`,
//! `on_catch`, `on_clone`, `on_if`); a linter that overrides another method
//! adds it here.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::nast::visitor_deprecated;
use crate::nast::visitor_deprecated::Visitor;
use crate::parser_return;
use crate::relative_path::RelativePath;

/// `type lint_env`
pub struct LintEnv<'a> {
    pub ctx: &'a Arc<Ctx>,
    /// The file we are currently in
    pub cfile: &'a RelativePath,
    /// The class we are currently in
    pub cclass: Option<&'a nast::Class_>,
    /// The method we are currently in
    pub cmethod: Option<&'a nast::Method_>,
    /// The function we are currently in
    pub cfun: Option<&'a nast::FunDef>,
}

fn default_env<'a>(ctx: &'a Arc<Ctx>, cfile: &'a RelativePath) -> LintEnv<'a> {
    LintEnv {
        ctx,
        cfile,
        cclass: None,
        cmethod: None,
        cfun: None,
    }
}

/// The overrides of one linter's class (see the module doc). Every method
/// defaults to `parent#on_x`; `depth` is the depth of the parent.
#[allow(unused_variables)]
pub trait BodyVisitorModule {
    fn on_block(&self, this: &mut BodyVisitor<'_>, depth: usize, b: &[nast::Stmt]) {
        this.on_block_at(depth, b)
    }

    fn on_stmt(&self, this: &mut BodyVisitor<'_>, depth: usize, s: &nast::Stmt) {
        this.on_stmt_at(depth, s)
    }

    fn on_expr(&self, this: &mut BodyVisitor<'_>, depth: usize, e: &nast::Expr) {
        this.on_expr_at(depth, e)
    }

    fn on_foreach(
        &self,
        this: &mut BodyVisitor<'_>,
        depth: usize,
        e: &nast::Expr,
        ae: &nast::AsExpr,
        b: &[nast::Stmt],
    ) {
        this.on_foreach_at(depth, e, ae, b)
    }

    fn on_as_expr(&self, this: &mut BodyVisitor<'_>, depth: usize, ae: &nast::AsExpr) {
        this.on_as_expr_at(depth, ae)
    }

    fn on_catch(&self, this: &mut BodyVisitor<'_>, depth: usize, c: &nast::Catch) {
        this.on_catch_at(depth, c)
    }

    fn on_clone(&self, this: &mut BodyVisitor<'_>, depth: usize, e: &nast::Expr) {
        this.on_clone_at(depth, e)
    }

    fn on_if(
        &self,
        this: &mut BodyVisitor<'_>,
        depth: usize,
        e: &nast::Expr,
        b1: &[nast::Stmt],
        b2: &[nast::Stmt],
    ) {
        this.on_if_at(depth, e, b1, b2)
    }
}

/// `module type BodyVisitorFunctor`: the class a linter makes from its
/// parent's, here the layer it puts on top of the parent's
/// (`class visitor env`).
pub type BodyVisitorFunctor = for<'e> fn(&LintEnv<'e>) -> Rc<dyn BodyVisitorModule>;

/// An object of the class of a `BodyVisitorModule`: `new Visitor.visitor env`.
pub struct BodyVisitor<'e> {
    pub env: LintEnv<'e>,
    /// Innermost first; the generic visitor is below `layers[0]`.
    layers: Vec<Rc<dyn BodyVisitorModule>>,
}

macro_rules! dispatch {
    ($self:ident, $depth:ident, $method:ident, $default:expr, $($arg:ident),*) => {
        if $depth == 0 {
            $default
        } else {
            let layer = Rc::clone(&$self.layers[$depth - 1]);
            layer.$method($self, $depth - 1, $($arg),*)
        }
    };
}

impl<'e> BodyVisitor<'e> {
    fn top(&self) -> usize {
        self.layers.len()
    }

    pub fn on_block_at(&mut self, depth: usize, b: &[nast::Stmt]) {
        dispatch!(self, depth, on_block, visitor_deprecated::on_block(self, (), b), b)
    }

    pub fn on_stmt_at(&mut self, depth: usize, s: &nast::Stmt) {
        dispatch!(self, depth, on_stmt, visitor_deprecated::on_stmt(self, (), s), s)
    }

    pub fn on_expr_at(&mut self, depth: usize, e: &nast::Expr) {
        dispatch!(self, depth, on_expr, visitor_deprecated::on_expr(self, (), e), e)
    }

    pub fn on_foreach_at(
        &mut self,
        depth: usize,
        e: &nast::Expr,
        ae: &nast::AsExpr,
        b: &[nast::Stmt],
    ) {
        dispatch!(
            self,
            depth,
            on_foreach,
            visitor_deprecated::on_foreach(self, (), e, ae, b),
            e,
            ae,
            b
        )
    }

    pub fn on_as_expr_at(&mut self, depth: usize, ae: &nast::AsExpr) {
        dispatch!(
            self,
            depth,
            on_as_expr,
            visitor_deprecated::on_as_expr(self, (), ae),
            ae
        )
    }

    pub fn on_catch_at(&mut self, depth: usize, c: &nast::Catch) {
        dispatch!(self, depth, on_catch, visitor_deprecated::on_catch(self, (), c), c)
    }

    pub fn on_clone_at(&mut self, depth: usize, e: &nast::Expr) {
        dispatch!(self, depth, on_clone, visitor_deprecated::on_clone(self, (), e), e)
    }

    pub fn on_if_at(&mut self, depth: usize, e: &nast::Expr, b1: &[nast::Stmt], b2: &[nast::Stmt]) {
        dispatch!(
            self,
            depth,
            on_if,
            visitor_deprecated::on_if(self, (), e, b1, b2),
            e,
            b1,
            b2
        )
    }

    /// This allows lint rules to distinguish between the top-level block (which
    /// is the function / method body) and the inner if-else / loop blocks
    /// (`method on_body = this#on_block`)
    pub fn on_body(&mut self, b: &[nast::Stmt]) {
        Visitor::on_block(self, (), b)
    }
}

/// `class body_visitor`: `Nast.Visitor_DEPRECATED.visitor` with the overrides
/// of the layers.
impl<'e> Visitor<()> for BodyVisitor<'e> {
    fn on_block(&mut self, (): (), b: &[nast::Stmt]) {
        self.on_block_at(self.top(), b)
    }

    fn on_stmt(&mut self, (): (), s: &nast::Stmt) {
        self.on_stmt_at(self.top(), s)
    }

    fn on_expr(&mut self, (): (), e: &nast::Expr) {
        self.on_expr_at(self.top(), e)
    }

    fn on_foreach(&mut self, (): (), e: &nast::Expr, ae: &nast::AsExpr, b: &[nast::Stmt]) {
        self.on_foreach_at(self.top(), e, ae, b)
    }

    fn on_as_expr(&mut self, (): (), ae: &nast::AsExpr) {
        self.on_as_expr_at(self.top(), ae)
    }

    fn on_catch(&mut self, (): (), c: &nast::Catch) {
        self.on_catch_at(self.top(), c)
    }

    fn on_clone(&mut self, (): (), e: &nast::Expr) {
        self.on_clone_at(self.top(), e)
    }

    fn on_if(&mut self, (): (), e: &nast::Expr, b1: &[nast::Stmt], b2: &[nast::Stmt]) {
        self.on_if_at(self.top(), e, b1, b2)
    }
}

thread_local! {
    /// `body_visitors`: a mapping of lint rule visitors to functions and
    /// methods, using the position of the function / method as the map key.
    /// The various file_visitors will add to this mapping. Once that's done,
    /// body_visitor_invoker is used for running all the lint rules, and it
    /// will do so in one pass over the named AST. A module is the list of the
    /// functors applied to `GenericBodyVisitor`, the first applied first.
    /// (Global state in OCaml, where a worker is a process; here the thread's.)
    static BODY_VISITORS: RefCell<HashMap<Pos, Vec<BodyVisitorFunctor>>> =
        RefCell::new(HashMap::new());
}

/// Call this before any using add_visitor
pub fn reset() {
    BODY_VISITORS.with_borrow_mut(|m| m.clear())
}

pub fn add_visitor(sid: &aast::Sid, v: BodyVisitorFunctor) {
    let p = &sid.0;
    BODY_VISITORS.with_borrow_mut(|m| match m.get_mut(p) {
        // `VisitorFunctor (GenericBodyVisitor)`
        None => {
            m.insert(*p, vec![v]);
        }
        // `VisitorFunctor (M')`
        Some(v_) => v_.push(v),
    })
}

/// `new Visitor.visitor env` for the module at `p` (`Hashtbl.find`).
fn find_visitor<'e>(p: &Pos, env: LintEnv<'e>) -> BodyVisitor<'e> {
    let functors = BODY_VISITORS.with_borrow(|m| match m.get(p) {
        Some(functors) => functors.clone(),
        None => panic!("Not_found"),
    });
    let layers = functors.iter().map(|f| f(&env)).collect();
    BodyVisitor { env, layers }
}

/// `class virtual ['a] abstract_file_visitor` (and `class type ['a]
/// file_visitor`)
pub trait FileVisitor<A> {
    fn on_file(
        &mut self,
        context: A,
        ctx: &Arc<Ctx>,
        fn_: &RelativePath,
        pr: &parser_return::T,
    ) -> A {
        let ast = &pr.ast;
        let env = default_env(ctx, fn_);
        let mut context = context;
        for def in &ast.0 {
            context = match def {
                aast::Def::Fun(f) => {
                    let f = crate::diagnostics::ignore_(|| {
                        crate::naming::fun_def(ctx, (**f).clone())
                    });
                    self.on_fun_def(context, &env, &f)
                }
                aast::Def::Class(c) => {
                    let c = crate::diagnostics::ignore_(|| {
                        crate::naming::class_(ctx, (**c).clone())
                    });
                    self.on_class(context, &env, &c)
                }
                _ => context,
            }
        }
        context
    }

    fn on_class(&mut self, context: A, env: &LintEnv<'_>, class_: &nast::Class_) -> A {
        let mut context = context;
        for meth in &class_.methods {
            context = self.on_method(context, env, class_, meth)
        }
        context
    }

    fn on_fun_def(&mut self, context: A, _env: &LintEnv<'_>, _fun: &nast::FunDef) -> A {
        context
    }

    fn on_method(
        &mut self,
        context: A,
        _env: &LintEnv<'_>,
        _class: &nast::Class_,
        _method: &nast::Method_,
    ) -> A {
        context
    }
}

/// `class body_visitor_adder`
pub struct BodyVisitorAdder(pub BodyVisitorFunctor);

impl FileVisitor<()> for BodyVisitorAdder {
    fn on_fun_def(&mut self, (): (), _env: &LintEnv<'_>, fd: &nast::FunDef) {
        add_visitor(&fd.name, self.0)
    }

    fn on_method(
        &mut self,
        (): (),
        _env: &LintEnv<'_>,
        _class: &nast::Class_,
        meth: &nast::Method_,
    ) {
        add_visitor(&meth.name, self.0)
    }
}

/// `body_visitor_invoker`
pub struct BodyVisitorInvoker;

impl FileVisitor<()> for BodyVisitorInvoker {
    fn on_fun_def(&mut self, (): (), env: &LintEnv<'_>, fd: &nast::FunDef) {
        let fun_ = &fd.fun;
        let nb = &fun_.body;
        let env = LintEnv {
            cfun: Some(fd),
            ..*env
        };
        find_visitor(&fd.name.0, env).on_body(&nb.fb_ast.0)
    }

    fn on_method(
        &mut self,
        (): (),
        env: &LintEnv<'_>,
        class_: &nast::Class_,
        meth: &nast::Method_,
    ) {
        let nb = &meth.body;
        let env = LintEnv {
            cclass: Some(class_),
            cmethod: Some(meth),
            ..*env
        };
        find_visitor(&meth.name.0, env).on_body(&nb.fb_ast.0)
    }
}

pub fn body_visitor_invoker() -> BodyVisitorInvoker {
    BodyVisitorInvoker
}

/// `lint_all_bodies m`: `(new body_visitor_adder m)#on_file ()`
pub fn lint_all_bodies(
    m: BodyVisitorFunctor,
    ctx: &Arc<Ctx>,
    fn_: &RelativePath,
    pr: &parser_return::T,
) {
    BodyVisitorAdder(m).on_file((), ctx, fn_, pr)
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    thread_local! {
        static TRACE: RefCell<Vec<&'static str>> = const { RefCell::new(vec![]) };
    }

    fn expr(e: nast::Expr_) -> nast::Expr {
        aast::Expr((), Pos::NONE, e)
    }

    struct Named(&'static str);

    impl BodyVisitorModule for Named {
        fn on_clone(&self, this: &mut BodyVisitor<'_>, depth: usize, e: &nast::Expr) {
            TRACE.with_borrow_mut(|t| t.push(self.0));
            this.on_clone_at(depth, e)
        }
    }

    fn first(_env: &LintEnv<'_>) -> Rc<dyn BodyVisitorModule> {
        Rc::new(Named("first"))
    }

    fn second(_env: &LintEnv<'_>) -> Rc<dyn BodyVisitorModule> {
        Rc::new(Named("second"))
    }

    /// The functor added last is the outermost class: its override runs
    /// first, then its parent's; a nested `clone` goes through the stack
    /// again (late binding of `this#on_expr`).
    #[test]
    fn layers_run_outermost_first() {
        let p = Pos::NONE;
        reset();
        add_visitor(&oxidized::ast_defs::Id(p, "f".to_string()), first);
        add_visitor(&oxidized::ast_defs::Id(p, "f".to_string()), second);
        let ctx = Arc::new(
            Ctx::new(
                std::path::Path::new("/"),
                oxidized::global_options::GlobalOptions::default(),
            )
            .unwrap(),
        );
        let file = RelativePath::make(relative_path::Prefix::Dummy, "a.php".into());
        let env = default_env(&ctx, &file);
        let mut v = find_visitor(&p, env);
        let inner = expr(aast::Expr_::Clone(Box::new(expr(aast::Expr_::Null))));
        let outer = expr(aast::Expr_::Clone(Box::new(inner)));
        let body = vec![aast::Stmt(p, aast::Stmt_::Expr(Box::new(outer)))];
        TRACE.with_borrow_mut(|t| t.clear());
        v.on_body(&body);
        assert_eq!(
            TRACE.with_borrow(|t| t.clone()),
            vec!["second", "first", "second", "first"]
        );
        reset();
    }
}
