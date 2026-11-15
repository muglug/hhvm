// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: a placeholder for typing, used by the default build
//! until the port of `typing.ml` and the modules it needs (`crate::typing` and
//! friends, behind the `port` feature) can check a file end to end. It reports an error only
//! when both types involved are fully understood; anything else has the type
//! `Unknown`, which is compatible with everything. It is deleted once the
//! port runs.

use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::FunKind;
use oxidized::ast_defs::ParamKind;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Uop;
use oxidized::diagnostics::Diagnostic;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::scoured_comments::ScouredComments;
use oxidized::typing_defs_flags::FunParamFlags;
use pos::FunName;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::diagnostics_helpers;

/// "Invalid return type", "Invalid argument" and the other subtyping errors.
const UNIFY_ERROR: isize = 4110;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty_ {
    /// Not modelled. Compatible with everything.
    Unknown,
    Prim(Tprim),
    Nonnull,
    Dynamic,
    Option(Ty),
    Class(TypeName, Vec<Ty>),
}

/// A type, and the position that explains where it comes from.
#[derive(Clone, Debug)]
pub struct Ty {
    pub pos: Pos,
    pub node: Arc<Ty_>,
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}
impl Eq for Ty {}

impl Ty {
    fn new(pos: Pos, node: Ty_) -> Self {
        Self {
            pos,
            node: Arc::new(node),
        }
    }

    fn unknown() -> Self {
        Self::new(Pos::NONE, Ty_::Unknown)
    }

    fn prim(pos: &Pos, prim: Tprim) -> Self {
        Self::new(pos.clone(), Ty_::Prim(prim))
    }

    /// Whether the type has no `Unknown` part.
    fn is_known(&self) -> bool {
        match &*self.node {
            Ty_::Unknown => false,
            Ty_::Prim(_) | Ty_::Nonnull | Ty_::Dynamic => true,
            Ty_::Option(ty) => ty.is_known(),
            Ty_::Class(_, args) => args.iter().all(Ty::is_known),
        }
    }
}

/// A type as it is written in error messages.
fn print_ty(ty: &Ty) -> String {
    match &*ty.node {
        Ty_::Unknown => "_".into(),
        Ty_::Prim(prim) => match prim {
            Tprim::Tnull => "null",
            Tprim::Tvoid => "void",
            Tprim::Tint => "int",
            Tprim::Tbool => "bool",
            Tprim::Tfloat => "float",
            Tprim::Tresource => "resource",
            Tprim::Tnum => "num",
            Tprim::Tarraykey => "arraykey",
            Tprim::Tnoreturn => "noreturn",
        }
        .into(),
        Ty_::Nonnull => "nonnull".into(),
        Ty_::Dynamic => "dynamic".into(),
        Ty_::Option(inner) if matches!(&*inner.node, Ty_::Nonnull) => "mixed".into(),
        Ty_::Option(inner) => format!("?{}", print_ty(inner)),
        Ty_::Class(name, args) => {
            let name = name.as_str();
            let name = name.strip_prefix('\\').unwrap_or(name);
            // Names that are imported from `HH\` automatically are printed
            // without it.
            let name = match name.strip_prefix("HH\\") {
                Some(short) if hh_autoimport::is_hh_autoimport(short) => short,
                _ => name,
            };
            if args.is_empty() {
                name.to_string()
            } else {
                let args: Vec<String> = args.iter().map(print_ty).collect();
                format!("{}<{}>", name, args.join(", "))
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Answer {
    Yes,
    No,
    Unknown,
}

impl Answer {
    fn and(self, other: impl FnOnce() -> Answer) -> Answer {
        match self {
            Answer::Yes => other(),
            Answer::No => Answer::No,
            Answer::Unknown => match other() {
                Answer::No => Answer::No,
                _ => Answer::Unknown,
            },
        }
    }
}

const AWAITABLE: &str = "\\HH\\Awaitable";
const STRING: &str = "\\HH\\string";

/// Interfaces that types other than their implementors are subtypes of.
const MAGIC_INTERFACES: &[&str] = &["\\Stringish", "\\XHPChild", "\\HH\\XHPChild"];

/// Positions of `HH_FIXME` comments: line, then error code.
type Fixmes = oxidized::i_map::IMap<oxidized::i_map::IMap<Pos>>;

struct Checker<'a> {
    ctx: &'a Ctx,
    fixmes: &'a Fixmes,
    out: &'a mut Vec<Diagnostic>,
}

impl Checker<'_> {
    /// The type that a declared type stands for in a body.
    fn localize(&self, ty: &decl::Ty<R>) -> Ty {
        // Reasons other than "this is what the hint says" add to the message
        // of an error, which is not modelled.
        if !matches!(
            ty.reason().as_impl(),
            ReasonImpl::FromWitnessDecl(WitnessDecl::Hint(_) | WitnessDecl::WitnessFromDecl(_))
        ) {
            return Ty::unknown();
        }
        let pos = ty.pos().clone().to_oxidized();
        let node = match ty.node_ref() {
            // `void` is special wherever it meets `mixed` and nullable types.
            decl::Ty_::Tprim(Tprim::Tvoid) => Ty_::Unknown,
            decl::Ty_::Tprim(prim) => Ty_::Prim(*prim),
            decl::Ty_::Tmixed => Ty_::Option(Ty::new(pos.clone(), Ty_::Nonnull)),
            decl::Ty_::Tnonnull => Ty_::Nonnull,
            decl::Ty_::Tdynamic => Ty_::Dynamic,
            decl::Ty_::Toption(inner) => Ty_::Option(self.localize(inner)),
            decl::Ty_::Tapply(id_and_args) => {
                let (id, args) = &**id_and_args;
                match self.class_kind(id.id()) {
                    Some(ClassishKind::Cclass(_) | ClassishKind::Cinterface)
                        if !MAGIC_INTERFACES.contains(&id.id().as_str()) =>
                    {
                        Ty_::Class(id.id(), args.iter().map(|ty| self.localize(ty)).collect())
                    }
                    // Type aliases, enums and traits.
                    _ => Ty_::Unknown,
                }
            }
            _ => Ty_::Unknown,
        };
        Ty::new(pos, node)
    }

    fn class_kind(&self, name: TypeName) -> Option<ClassishKind> {
        match self.ctx.shallow_decls.get_class(name) {
            Ok(Some(class)) => Some(class.kind),
            _ => None,
        }
    }

    fn is_subtype(&self, sub: &Ty, sup: &Ty) -> Answer {
        use Answer::*;
        match (&*sub.node, &*sup.node) {
            (Ty_::Unknown, _) | (_, Ty_::Unknown) => Unknown,
            // `dynamic` takes part in coercions that are not modelled.
            (Ty_::Dynamic, _) | (_, Ty_::Dynamic) => Unknown,
            (Ty_::Prim(Tprim::Tnoreturn), _) => Yes,
            (Ty_::Option(sub), Ty_::Option(sup)) => self.is_subtype(sub, sup),
            (Ty_::Prim(Tprim::Tnull), Ty_::Option(_)) => Yes,
            (_, Ty_::Option(sup)) => self.is_subtype(sub, sup),
            (Ty_::Option(_), _) => No,
            (Ty_::Prim(Tprim::Tnull | Tprim::Tvoid), Ty_::Nonnull) => No,
            (_, Ty_::Nonnull) => Yes,
            (Ty_::Nonnull, _) => No,
            (Ty_::Prim(sub), Ty_::Prim(sup)) => {
                let ok = sub == sup
                    || matches!(
                        (sub, sup),
                        (Tprim::Tint | Tprim::Tfloat, Tprim::Tnum)
                            | (Tprim::Tint, Tprim::Tarraykey)
                    );
                if ok { Yes } else { No }
            }
            // `string` is a class.
            (Ty_::Class(name, _), Ty_::Prim(Tprim::Tarraykey)) if name.as_str() == STRING => Yes,
            (Ty_::Prim(_), Ty_::Class(..)) | (Ty_::Class(..), Ty_::Prim(_)) => No,
            (Ty_::Class(sub_name, sub_args), Ty_::Class(sup_name, sup_args)) => {
                if sub_name == sup_name {
                    // Without variance, equal arguments are the only sure case.
                    if sub_args.len() != sup_args.len() {
                        return Unknown;
                    }
                    return sub_args
                        .iter()
                        .zip(sup_args.iter())
                        .fold(Yes, |answer, (sub, sup)| {
                            answer.and(|| {
                                if !sub.is_known() || !sup.is_known() || sub != sup {
                                    Unknown
                                } else {
                                    Yes
                                }
                            })
                        });
                }
                match self.ctx.folded_decls.get_class(*sub_name) {
                    Ok(Some(class)) => {
                        if !class.ancestors.contains_key(sup_name) {
                            // Requirements (`require extends`) and the like
                            // can still make this hold.
                            if class.req_ancestors.is_empty()
                                && class.kind != ClassishKind::Cinterface
                                || self.class_kind(*sup_name)
                                    == Some(ClassishKind::Cclass(
                                        oxidized::ast_defs::Abstraction::Concrete,
                                    ))
                                    && class.req_ancestors.is_empty()
                            {
                                No
                            } else {
                                Unknown
                            }
                        } else if sup_args.is_empty() {
                            Yes
                        } else {
                            Unknown
                        }
                    }
                    _ => Unknown,
                }
            }
        }
    }

    fn is_fixmed(&self, pos: &Pos, code: isize) -> bool {
        crate::diagnostics_helpers::is_fixmed(self.fixmes, pos, code)
    }

    /// Report `claim` at `pos` unless `actual` is, or may be, a subtype of
    /// `expected`.
    fn check_subtype(&mut self, pos: &Pos, claim: &str, actual: &Ty, expected: &Ty) {
        if self.is_subtype(actual, expected) != Answer::No {
            return;
        }
        if !actual.is_known() || !expected.is_known() {
            return;
        }
        if self.is_fixmed(pos, UNIFY_ERROR) {
            return;
        }
        self.out.push(diagnostics_helpers::error_with_reasons(
            UNIFY_ERROR,
            pos.clone(),
            claim,
            vec![
                (
                    expected.pos.clone(),
                    format!("Expected `{}`", print_ty(expected)),
                ),
                (actual.pos.clone(), format!("But got `{}`", print_ty(actual))),
            ],
        ));
    }
}

/// The local variables an expression or statement may give a new type to:
/// those it assigns, and those whose type it may refine.
#[derive(Default)]
struct TouchedLocals {
    names: HashSet<String>,
}

impl TouchedLocals {
    fn of_expr(expr: &nast::Expr) -> HashSet<String> {
        let mut v = Self::default();
        let _ = v.visit_expr(&mut (), expr);
        v.names
    }

    /// Every local in `expr`.
    fn add_all(&mut self, expr: &nast::Expr) {
        struct All<'a>(&'a mut HashSet<String>);
        impl<'ast> Visitor<'ast> for All<'_> {
            type Params = AstParams<(), ()>;
            fn object(&mut self) -> &mut dyn Visitor<'ast, Params = Self::Params> {
                self
            }
            fn visit_lid(&mut self, _: &mut (), lid: &'ast nast::Lid) -> Result<(), ()> {
                self.0.insert(lid.1.1.clone());
                Ok(())
            }
        }
        let _ = All(&mut self.names).visit_expr(&mut (), expr);
    }
}

impl<'ast> Visitor<'ast> for TouchedLocals {
    type Params = AstParams<(), ()>;

    fn object(&mut self) -> &mut dyn Visitor<'ast, Params = Self::Params> {
        self
    }

    fn visit_expr(&mut self, c: &mut (), expr: &'ast nast::Expr) -> Result<(), ()> {
        match &expr.2 {
            // An assignment, to a local or to something inside one.
            nast::Expr_::Assign(assign) => self.add_all(&assign.0),
            nast::Expr_::Unop(unop)
                if matches!(
                    unop.0,
                    Uop::Uincr | Uop::Udecr | Uop::Upincr | Uop::Updecr
                ) =>
            {
                self.add_all(&unop.1)
            }
            // Tests and conditions refine what they mention.
            nast::Expr_::Is(is) => self.add_all(&is.0),
            nast::Expr_::As(as_) => self.add_all(&as_.expr),
            nast::Expr_::Eif(eif) => self.add_all(&eif.0),
            nast::Expr_::Binop(binop)
                if matches!(
                    binop.bop,
                    Bop::Ampamp | Bop::Barbar | Bop::QuestionQuestion
                ) =>
            {
                self.add_all(&binop.lhs)
            }
            nast::Expr_::Call(call) => {
                for arg in &call.args {
                    if let nast::Argument::Ainout(_, expr) = arg {
                        self.add_all(expr);
                    }
                }
                // `invariant(cond, ...)` and friends refine like a condition.
                if let nast::Expr_::Id(id) = &call.func.2 {
                    if id.1.to_ascii_lowercase().contains("invariant") {
                        for arg in &call.args {
                            self.add_all(arg.to_expr_ref());
                        }
                    }
                }
            }
            // The body of a lambda does not change the locals around it, but
            // it is simpler to stay away from what it mentions.
            nast::Expr_::Lfun(_) | nast::Expr_::Efun(_) => {
                self.add_all(expr);
                return Ok(());
            }
            _ => {}
        }
        expr.recurse(c, self.object())
    }

    fn visit_stmt(&mut self, c: &mut (), stmt: &'ast nast::Stmt) -> Result<(), ()> {
        match &stmt.1 {
            nast::Stmt_::If(if_) => self.add_all(&if_.0),
            nast::Stmt_::While(while_) => self.add_all(&while_.0.2),
            nast::Stmt_::Do(do_) => self.add_all(&do_.1.2),
            nast::Stmt_::For(for_) => {
                if let Some(cond) = &for_.1 {
                    self.add_all(&cond.2);
                }
            }
            nast::Stmt_::Switch(switch) => self.add_all(&switch.0),
            _ => {}
        }
        stmt.recurse(c, self.object())
    }

    fn visit_as_expr(&mut self, c: &mut (), as_expr: &'ast nast::AsExpr) -> Result<(), ()> {
        // The bindings of a `foreach`.
        match as_expr {
            nast::AsExpr::AsV(e) | nast::AsExpr::AwaitAsV(_, e) => self.add_all(e),
            nast::AsExpr::AsKv(k, v) | nast::AsExpr::AwaitAsKv(_, k, v) => {
                self.add_all(k);
                self.add_all(v);
            }
        }
        as_expr.recurse(c, self.object())
    }

    fn visit_catch(&mut self, c: &mut (), catch: &'ast nast::Catch) -> Result<(), ()> {
        self.names.insert(catch.1.1.1.clone());
        catch.recurse(c, self.object())
    }
}

struct Body<'a, 'c> {
    checker: &'a mut Checker<'c>,
    locals: HashMap<String, Ty>,
    /// The type `return` expects, if it is to be checked.
    ret: Option<Ty>,
}

impl Body<'_, '_> {
    fn forget(&mut self, names: HashSet<String>) {
        for name in names {
            self.locals.insert(name, Ty::unknown());
        }
    }

    fn block(&mut self, block: &nast::Block) {
        self.stmts(&block.0)
    }

    fn stmts(&mut self, stmts: &[nast::Stmt]) {
        for stmt in stmts {
            self.stmt(stmt);
        }
    }

    fn stmt(&mut self, stmt: &nast::Stmt) {
        match &stmt.1 {
            nast::Stmt_::Expr(expr) => {
                self.expr(expr);
            }
            nast::Stmt_::Throw(expr) => {
                self.expr(expr);
            }
            nast::Stmt_::Return(ret) => {
                if let Some(expr) = &**ret {
                    let actual = self.expr(expr);
                    if let Some(expected) = self.ret.clone() {
                        self.checker.check_subtype(
                            &expr.1,
                            "Invalid return type",
                            &actual,
                            &expected,
                        );
                    }
                }
            }
            nast::Stmt_::Block(block) => self.block(&block.1),
            nast::Stmt_::If(if_) => {
                let (cond, then, else_) = &**if_;
                self.expr(cond);
                let mut touched = TouchedLocals::default();
                touched.add_all(cond);
                self.forget(touched.names);
                // Each branch starts from the same locals; afterwards a local
                // keeps its type only if both branches agree on it.
                // A branch that a literal condition rules out is not checked.
                let before = self.locals.clone();
                if !matches!(cond.2, nast::Expr_::False) {
                    self.block(then);
                }
                let after_then = std::mem::replace(&mut self.locals, before);
                if !matches!(cond.2, nast::Expr_::True) {
                    self.block(else_);
                }
                let mut merged = HashMap::new();
                for (name, ty) in std::mem::take(&mut self.locals) {
                    let ty = match after_then.get(&name) {
                        Some(other) if *other == ty => ty,
                        _ => Ty::unknown(),
                    };
                    merged.insert(name, ty);
                }
                for name in after_then.into_keys() {
                    merged.entry(name).or_insert_with(Ty::unknown);
                }
                self.locals = merged;
            }
            // Loops and the rest of control flow: nothing that they may assign
            // or refine is trusted, inside or after them.
            _ => {
                let mut touched = TouchedLocals::default();
                let _ = touched.visit_stmt(&mut (), stmt);
                let names = touched.names;
                self.forget(names.clone());
                self.nested_blocks(stmt, &names);
                self.forget(names);
            }
        }
    }

    /// Check the blocks of a statement that is not interpreted itself. They
    /// are alternatives or repetitions, so none of them may rely on what
    /// another did to `touched`.
    fn nested_blocks(&mut self, stmt: &nast::Stmt, touched: &HashSet<String>) {
        let blocks: Vec<&[nast::Stmt]> = match &stmt.1 {
            nast::Stmt_::While(while_) => vec![&while_.1.0],
            nast::Stmt_::Do(do_) => vec![&do_.0.0],
            nast::Stmt_::For(for_) => vec![&for_.3.0],
            nast::Stmt_::Foreach(foreach) => vec![&foreach.2.0],
            nast::Stmt_::Switch(switch) => switch
                .1
                .iter()
                .map(|case| &case.1.0[..])
                .chain(switch.2.iter().map(|default| &default.1.0[..]))
                .collect(),
            nast::Stmt_::Try(try_) => std::iter::once(&try_.0.0[..])
                .chain(try_.1.iter().map(|catch| &catch.2.0[..]))
                .chain(std::iter::once(&try_.2.0[..]))
                .collect(),
            nast::Stmt_::Using(using) => vec![&using.block.0],
            nast::Stmt_::Concurrent(block) => vec![&block.0],
            nast::Stmt_::Awaitall(awaitall) => vec![&awaitall.1.0],
            _ => vec![],
        };
        for block in blocks {
            self.forget(touched.clone());
            self.stmts(block);
        }
    }

    fn expr(&mut self, expr: &nast::Expr) -> Ty {
        let pos = &expr.1;
        match &expr.2 {
            nast::Expr_::Int(_) => Ty::prim(pos, Tprim::Tint),
            nast::Expr_::Float(_) => Ty::prim(pos, Tprim::Tfloat),
            nast::Expr_::String(_) => Ty::new(pos.clone(), Ty_::Class(TypeName::new(STRING), vec![])),
            nast::Expr_::True | nast::Expr_::False => Ty::prim(pos, Tprim::Tbool),
            nast::Expr_::Null => Ty::prim(pos, Tprim::Tnull),
            nast::Expr_::Lvar(lid) => self
                .locals
                .get(&lid.1.1)
                .cloned()
                .unwrap_or_else(Ty::unknown),
            nast::Expr_::Assign(assign) => {
                let (lhs, op, rhs) = &**assign;
                let ty = self.expr(rhs);
                match (&lhs.2, op) {
                    (nast::Expr_::Lvar(lid), None) => {
                        self.locals.insert(lid.1.1.clone(), ty.clone());
                        ty
                    }
                    _ => {
                        self.forget(TouchedLocals::of_expr(expr));
                        Ty::unknown()
                    }
                }
            }
            nast::Expr_::Call(call) => self.call(call),
            nast::Expr_::New(new) => {
                let (class_id, targs, args, unpacked, _) = &**new;
                for arg in args {
                    self.expr(arg.to_expr_ref());
                }
                if let Some(unpacked) = unpacked {
                    self.expr(unpacked);
                }
                match &class_id.2 {
                    nast::ClassId_::CI(id) if targs.is_empty() => {
                        let name = TypeName::new(&id.1);
                        match self.checker.ctx.shallow_decls.get_class(name) {
                            Ok(Some(class))
                                if class.tparams.is_empty()
                                    && matches!(class.kind, ClassishKind::Cclass(_)) =>
                            {
                                // The reason is the class named, not the
                                // whole expression.
                                Ty::new(class_id.1.clone(), Ty_::Class(name, vec![]))
                            }
                            _ => Ty::unknown(),
                        }
                    }
                    _ => Ty::unknown(),
                }
            }
            nast::Expr_::Await(awaited) => {
                let ty = self.expr(awaited);
                match &*ty.node {
                    Ty_::Class(name, args) if name.as_str() == AWAITABLE && args.len() == 1 => {
                        args[0].clone()
                    }
                    _ => Ty::unknown(),
                }
            }
            // Not interpreted: only what it does to the locals matters.
            _ => {
                self.forget(TouchedLocals::of_expr(expr));
                Ty::unknown()
            }
        }
    }

    fn call(&mut self, call: &nast::CallExpr) -> Ty {
        let arg_tys: Vec<Ty> = call
            .args
            .iter()
            .map(|arg| self.expr(arg.to_expr_ref()))
            .collect();
        if let Some(unpacked) = &call.unpacked_arg {
            self.expr(unpacked);
        }
        // Whatever the callee is, `inout` arguments and the like change.
        for arg in &call.args {
            if let nast::Argument::Ainout(_, expr) = arg {
                self.forget(TouchedLocals::of_expr(expr));
                let mut touched = TouchedLocals::default();
                touched.add_all(expr);
                self.forget(touched.names);
            }
        }
        let nast::Expr_::Id(id) = &call.func.2 else {
            self.forget(TouchedLocals::of_expr(&call.func));
            return Ty::unknown();
        };
        if id.1.to_ascii_lowercase().contains("invariant") {
            let mut touched = TouchedLocals::default();
            for arg in &call.args {
                touched.add_all(arg.to_expr_ref());
            }
            self.forget(touched.names);
            return Ty::unknown();
        }
        let Ok(Some(decl)) = self.checker.ctx.shallow_decls.get_fun(FunName::new(&id.1)) else {
            return Ty::unknown();
        };
        let decl::Ty_::Tfun(fun_ty) = decl.ty.node_ref() else {
            return Ty::unknown();
        };
        // Generic functions need inference.
        if !fun_ty.tparams.is_empty() || !call.targs.is_empty() {
            return Ty::unknown();
        }
        // Named and splatted parameters do not line up with the arguments.
        let positional = fun_ty.params.iter().all(|param| {
            !param
                .flags
                .intersects(FunParamFlags::NAMED | FunParamFlags::SPLAT | FunParamFlags::INOUT)
        });
        if !positional {
            return self.checker.localize(&fun_ty.ret);
        }
        // The last parameter of a variadic function takes the remaining arguments.
        let fixed = fun_ty.params.len() - usize::from(fun_ty.flags.variadic());
        for ((arg, arg_ty), param) in call
            .args
            .iter()
            .zip(&arg_tys)
            .zip(fun_ty.params.iter().take(fixed))
        {
            if !matches!(arg, nast::Argument::Anormal(_)) {
                break;
            }
            let expected = self.checker.localize(&param.ty);
            self.checker.check_subtype(
                &arg.to_expr_ref().1,
                "Invalid argument",
                arg_ty,
                &expected,
            );
        }
        self.checker.localize(&fun_ty.ret)
    }
}

impl Checker<'_> {
    fn check_body(
        &mut self,
        fun_ty: &decl::FunType<R, decl::Ty<R>>,
        params: &[nast::FunParam],
        kind: FunKind,
        body: &nast::FuncBody,
    ) {
        let mut locals = HashMap::new();
        let generic = !fun_ty.tparams.is_empty();
        for (i, param) in params.iter().enumerate() {
            let ty = match fun_ty.params.get(i) {
                Some(decl_param)
                    if !generic
                        && !(fun_ty.flags.variadic() && i + 1 == fun_ty.params.len())
                        && param.callconv == ParamKind::Pnormal =>
                {
                    self.localize(&decl_param.ty)
                }
                _ => Ty::unknown(),
            };
            locals.insert(param.name.clone(), ty);
        }
        let declared_ret = self.localize(&fun_ty.ret);
        let ret = match kind {
            _ if generic => None,
            FunKind::FSync => Some(declared_ret),
            FunKind::FAsync => match &*declared_ret.node {
                Ty_::Class(name, args) if name.as_str() == AWAITABLE && args.len() == 1 => {
                    Some(args[0].clone())
                }
                _ => None,
            },
            FunKind::FGenerator | FunKind::FAsyncGenerator => None,
        };
        // `return` in a function that returns nothing is another check.
        let ret = ret.filter(|ty| {
            !matches!(
                &*ty.node,
                Ty_::Prim(Tprim::Tvoid | Tprim::Tnoreturn) | Ty_::Unknown
            )
        });
        let mut body_checker = Body {
            checker: self,
            locals,
            ret,
        };
        body_checker.block(&body.fb_ast);
    }

    fn check_fun(&mut self, fun: &nast::FunDef) {
        let Ok(Some(decl)) = self.ctx.shallow_decls.get_fun(FunName::new(&fun.name.1)) else {
            return;
        };
        if let decl::Ty_::Tfun(fun_ty) = decl.ty.node_ref() {
            self.check_body(fun_ty, &fun.fun.params, fun.fun.fun_kind, &fun.fun.body);
        }
    }

    fn check_class(&mut self, class: &nast::Class_) {
        let Ok(Some(decl)) = self
            .ctx
            .shallow_decls
            .get_class(TypeName::new(&class.name.1))
        else {
            return;
        };
        // The type parameters of the class are in scope in its methods.
        if !decl.tparams.is_empty() {
            return;
        }
        for method in &class.methods {
            let decls = if method.static_ {
                &decl.static_methods
            } else {
                &decl.methods
            };
            let Some(method_decl) = decls
                .iter()
                .find(|m| m.name.id().as_str() == method.name.1)
            else {
                continue;
            };
            if let decl::Ty_::Tfun(fun_ty) = method_decl.ty.node_ref() {
                self.check_body(fun_ty, &method.params, method.fun_kind, &method.body);
            }
        }
    }

    fn check_defs(&mut self, defs: &[nast::Def]) {
        for def in defs {
            match def {
                nast::Def::Fun(fun) => self.check_fun(fun),
                nast::Def::Class(class) => self.check_class(class),
                nast::Def::Namespace(ns) => self.check_defs(&ns.1),
                _ => {}
            }
        }
    }
}

/// Typecheck the definitions of a named file.
pub fn check_program(
    ctx: &Ctx,
    program: &nast::Program,
    comments: &ScouredComments,
    out: &mut Vec<Diagnostic>,
) {
    let mut checker = Checker {
        ctx,
        fixmes: &comments.fixmes,
        out,
    };
    checker.check_defs(&program.0);
}
