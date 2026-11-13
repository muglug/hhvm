// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `simplihack/simplihack_interpreter.ml`. See `hh/PORTING.md`.
//!
//! SimpliHack Interpreter
//!
//! This module implements an interpreter for the SimpliHack DSL, a simplified subset
//! of Hack used for code generation and metaprogramming tasks. The interpreter
//! evaluates expressions in user attributes and produces string outputs that can be
//! used as prompts or code snippets.
//!
//! Key components:
//! - Value: Represents runtime values (strings, unit)
//! - Context: Maintains interpreter state during evaluation
//! - ControlFlow: Handles statement execution flow
//! - Expr/Stmt/Block: Handle evaluation of different language constructs
//! - ClassId/Call/Binop: Support specific language features
//!
//! The interpreter follows a recursive descent pattern where each language
//! construct is handled by a dedicated module.
//!
//! The exception `EvalError` is the error of a `Result` returned through the
//! evaluation functions and handled in `eval`. The modules are generic over
//! the annotations of the AST (`(_, _) Aast.expr`): the attribute is a TAST,
//! the bodies of the functions it calls are NASTs. OCaml strings are bytes:
//! the values are `BString`s.

use bstr::BString;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::ast_provider;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::local_id;
use crate::naming;
use crate::naming_provider;
use crate::pos_or_decl;
use crate::provider_context;
use crate::simplihack_intf::LanguageServiceProvider;
use crate::tast;
use crate::tast_env;
use crate::typing_deps;
use crate::typing_deps::dep::Variant as Dep;
use crate::typing_env;
use crate::typing_error;
use crate::typing_error::primary::simplihack;
use crate::utils;

/// StackFrame module represents a single frame in the call stack
pub mod stack_frame {
    use oxidized::pos::Pos;

    #[derive(Clone, Debug)]
    pub struct T {
        /// Name of the function or method
        pub name: String,
        /// Source location of the call, if available
        pub location: Pos,
    }
}

/// `exception EvalError`
#[derive(Clone, Debug)]
pub struct EvalError {
    pub msg: String,
    pub pos: Pos,
    pub stack_trace: Vec<stack_frame::T>,
}

/// Value module represents the different types of values that can be produced during interpretation
pub mod value {
    pub use crate::simplihack_intf::Value as T;
}

use value::T as Value;

/// Context module maintains the interpreter's state during evaluation
pub mod context {
    use super::*;

    #[derive(Clone)]
    pub struct T<'a> {
        pub env: &'a tast_env::Env,
        /// Map of local variables to their values
        pub locals: im::OrdMap<local_id::T, Value>,
        /// The current call stack trace (the innermost frame first)
        pub stack_trace: Vec<stack_frame::T>,
    }

    /// [init provider dependent_root] creates a new context with the given provider, dependent_root, and empty locals map
    pub fn init(env: &tast_env::Env) -> T<'_> {
        T {
            env,
            locals: im::OrdMap::new(),
            stack_trace: vec![],
        }
    }

    pub fn env<'a>(ctx: &T<'a>) -> &'a tast_env::Env {
        ctx.env
    }

    pub fn provider<'a>(ctx: &T<'a>) -> &'a std::sync::Arc<crate::ctx::Ctx> {
        &tast_env::get_decl_env(ctx.env).ctx
    }

    pub fn dependent_root<'a>(ctx: &T<'a>) -> &'a Option<Dep> {
        &tast_env::get_decl_env(ctx.env).droot
    }

    /// Helper for raising evaluation errors
    pub fn eval_error<A>(ctx: &T<'_>, pos: &Pos, msg: String) -> Result<A, EvalError> {
        Err(EvalError {
            msg,
            pos: pos.clone(),
            stack_trace: ctx.stack_trace.clone(),
        })
    }

    /// [store ~ctx local value] returns a new context with [value] stored at [local] in the locals map
    pub fn store<'a>(ctx: T<'a>, local: local_id::T, value: Value) -> T<'a> {
        let mut ctx = ctx;
        ctx.locals.insert(local, value);
        ctx
    }

    /// [load ~ctx local] looks up the value associated with [local] in the context's locals map
    /// Raises [EvalError] if the local is not found
    pub fn load(ctx: &T<'_>, (pos, local): (&Pos, &local_id::T)) -> Result<Value, EvalError> {
        match ctx.locals.get(local) {
            Some(value) => Ok(value.clone()),
            None => eval_error(
                ctx,
                pos,
                format!("The local `{}` is not defined", local_id::get_name(local)),
            ),
        }
    }

    /// [fresh ctx] creates a new context with the same provider, dependent_root, and stack_trace but empty locals
    pub fn fresh(ctx: T<'_>) -> T<'_> {
        T {
            locals: im::OrdMap::new(),
            ..ctx
        }
    }

    /// [push_stack_frame ~ctx name pos] returns a new context with a new stack frame with a fresh set of locals
    pub fn push_stack_frame<'a>(ctx: &T<'a>, name: &str, location: &Pos) -> T<'a> {
        let frame = stack_frame::T {
            name: name.to_string(),
            location: location.clone(),
        };
        let mut stack_trace = Vec::with_capacity(ctx.stack_trace.len() + 1);
        stack_trace.push(frame);
        stack_trace.extend(ctx.stack_trace.iter().cloned());
        fresh(T {
            stack_trace,
            ..ctx.clone()
        })
    }

    pub fn add_dep(ctx: &T<'_>, dep: Dep) {
        match dependent_root(ctx) {
            None => {}
            Some(root) => {
                let mode = provider_context::get_deps_mode(provider(ctx));
                typing_deps::add_idep(&mode, root, &dep)
            }
        }
    }

    pub fn add_file_dep(ctx: &T<'_>, path: &crate::relative_path::T) {
        add_dep(ctx, Dep::File(path.clone()))
    }

    /// [find_class ~ctx name] looks up a class definition by name using the context's provider
    /// Raises [EvalError] if the class is not found
    pub fn find_class(
        ctx: &T<'_>,
        ast_defs::Id(pos, name): &aast::ClassName,
    ) -> Result<nast::Class_, EvalError> {
        add_dep(ctx, Dep::Type(name.clone()));
        let cls = (|| {
            let provider = provider(ctx);
            let path = naming_provider::get_class_path(provider, name)?;
            add_file_dep(ctx, &path);
            let class_ = ast_provider::find_class_in_file(true, provider, &path, name)?;
            Some(naming::class_(provider, class_))
        })();
        match cls {
            Some(cls) => Ok(cls),
            None => eval_error(
                ctx,
                pos,
                format!("The type `{}` is not defined", utils::strip_ns(name)),
            ),
        }
    }

    /// [find_static_method ~ctx class_ name] finds a method with [name] in [class_]
    /// Raises [EvalError] if the method is not found
    ///
    /// Note: This will only find static methods declared directly on the class
    /// and not inherited methods. If we wanted to support inherited methods we
    /// would need to use [Folded_class.t] to look up the method.
    ///
    /// For now this is an intentional choice to avoid absorbing too many Hack
    /// specific concepts into the SimpliHack DSL.
    pub fn find_static_method<'c>(
        ctx: &T<'_>,
        class_: &'c nast::Class_,
        (pos, name): &ast_defs::Pstring,
    ) -> Result<&'c nast::Method_, EvalError> {
        add_dep(ctx, Dep::SMethod(class_.name.1.clone(), name.clone()));
        match class_.methods.iter().find(|meth| meth.name.1 == *name) {
            Some(meth) => Ok(meth),
            None => eval_error(
                ctx,
                pos,
                format!(
                    "The method `{}` is not defined in `{}`",
                    name,
                    utils::strip_ns(&class_.name.1)
                ),
            ),
        }
    }

    /// [find_function ~ctx name] looks up a function definition by name using the context's provider
    /// Raises [EvalError] if the function is not found
    pub fn find_function(
        ctx: &T<'_>,
        ast_defs::Id(pos, name): &aast::Sid,
    ) -> Result<nast::FunDef, EvalError> {
        add_dep(ctx, Dep::Fun(name.clone()));
        let func = (|| {
            let provider = provider(ctx);
            let path = naming_provider::get_fun_path(provider, name)?;
            add_file_dep(ctx, &path);
            let fun_def = ast_provider::find_fun_in_file(true, provider, &path, name)?;
            Some(naming::fun_def(provider, fun_def))
        })();
        match func {
            Some(func) => Ok(func),
            None => eval_error(
                ctx,
                pos,
                format!("Function `{}` not found", utils::strip_ns(name)),
            ),
        }
    }

    /// `Context.Class`
    pub mod class {
        use super::*;

        pub type T<'a> = (super::T<'a>, cls::T);

        pub fn find<'a>(
            ctx: &super::T<'a>,
            ast_defs::Id(pos, name): &aast::ClassName,
        ) -> Result<T<'a>, EvalError> {
            add_dep(ctx, Dep::Type(name.clone()));
            let cls = decl_entry::to_option(tast_env::get_class(ctx.env, name));
            match cls {
                Some(cls) => Ok((ctx.clone(), cls)),
                None => eval_error(
                    ctx,
                    pos,
                    format!("The type `{}` is not defined", utils::strip_ns(name)),
                ),
            }
        }

        pub fn constructor((ctx, cls): &T<'_>) -> Option<ClassElt> {
            add_dep(ctx, Dep::Constructor(cls::name(cls)));
            let env = tast_env::eq_typing_env(ctx.env);
            let (constructor, _) = typing_env::get_construct(env, cls);
            constructor
        }

        pub fn methods((ctx, cls): &T<'_>) -> Vec<(String, ClassElt)> {
            add_dep(ctx, Dep::AllMembers(cls::name(cls)));
            cls::methods(cls)
        }

        pub fn static_methods((ctx, cls): &T<'_>) -> Vec<(String, ClassElt)> {
            add_dep(ctx, Dep::AllMembers(cls::name(cls)));
            cls::smethods(cls)
        }

        pub fn fields((ctx, cls): &T<'_>) -> Vec<(String, ClassElt)> {
            add_dep(ctx, Dep::AllMembers(cls::name(cls)));
            cls::props(cls)
        }

        pub fn static_fields((ctx, cls): &T<'_>) -> Vec<(String, ClassElt)> {
            add_dep(ctx, Dep::AllMembers(cls::name(cls)));
            cls::sprops(cls)
        }
    }
}

use context::T as Context;

/// `Context` as a `Simplihack_intf.LanguageServiceProvider` (the argument of
/// `Simplihack_prompt_context_provider.Make`).
impl<'a> LanguageServiceProvider for Context<'a> {
    type Error = EvalError;

    type Class = context::class::T<'a>;

    fn env(&self) -> &tast_env::Env {
        context::env(self)
    }

    fn find_class(&self, name: &aast::ClassName) -> Result<nast::Class_, EvalError> {
        context::find_class(self, name)
    }

    fn find_static_method<'c>(
        &self,
        class_: &'c nast::Class_,
        name: &ast_defs::Pstring,
    ) -> Result<&'c nast::Method_, EvalError> {
        context::find_static_method(self, class_, name)
    }

    fn find_function(&self, name: &aast::Sid) -> Result<nast::FunDef, EvalError> {
        context::find_function(self, name)
    }

    fn class_find(&self, name: &aast::ClassName) -> Result<Self::Class, EvalError> {
        context::class::find(self, name)
    }

    fn class_constructor(cls: &Self::Class) -> Option<ClassElt> {
        context::class::constructor(cls)
    }

    fn class_methods(cls: &Self::Class) -> Vec<(String, ClassElt)> {
        context::class::methods(cls)
    }

    fn class_static_methods(cls: &Self::Class) -> Vec<(String, ClassElt)> {
        context::class::static_methods(cls)
    }

    fn class_fields(cls: &Self::Class) -> Vec<(String, ClassElt)> {
        context::class::fields(cls)
    }

    fn class_static_fields(cls: &Self::Class) -> Vec<(String, ClassElt)> {
        context::class::static_fields(cls)
    }
}

/// `module PromptCtx = Simplihack_prompt_context_provider.Make (Context)`
use crate::simplihack_prompt_context_provider as prompt_ctx;

/// ControlFlow module represents the possible outcomes of statement evaluation
pub mod control_flow {
    pub enum T<'a> {
        /// Return with a value
        Return(super::Value),
        /// Continue to next statement with updated context
        Next(super::Context<'a>),
    }
}

use control_flow::T as ControlFlow;

// Note on mutual recursion:
// The following modules (Expr, Stmt, Block, ClassId, Call, Binop) are mutually
// recursive.
//
// Evaluation flow:
// - Expr.eval: Evaluates expressions (may call Call.eval for function calls)
// - Call.eval: Evaluates function calls (may call Block.eval for function bodies)
// - Block.eval: Evaluates blocks of statements (calls Stmt.eval for each statement)
// - Stmt.eval: Evaluates statements (may call Expr.eval for expressions)

/// Expr module handles expression evaluation
pub mod expr {
    use super::*;

    /// Main expression evaluation function
    fn expr<Ex, En>(
        ctx: &Context<'_>,
        pos: &Pos,
        e: &aast::Expr_<Ex, En>,
    ) -> Result<Value, EvalError> {
        let str_expr_ = |ctx: &Context<'_>, aast::Expr(_, pos, e): &aast::Expr<Ex, En>| {
            str_expr(ctx, pos, e)
        };
        match e {
            aast::Expr_::String(str) => {
                // Evaluates a string literal
                Ok(Value::Str(str.clone()))
            }
            aast::Expr_::String2(exprs) => {
                let mut value = BString::default();
                for e in exprs {
                    let rhs = str_expr_(ctx, e)?;
                    value.extend_from_slice(&rhs);
                }
                Ok(Value::Str(value))
            }
            aast::Expr_::Nameof(cid) if matches!(&cid.2, aast::ClassId_::CI(_)) => {
                let aast::ClassId_::CI(ast_defs::Id(_, name)) = &cid.2 else {
                    unreachable!()
                };
                Ok(Value::Str(BString::from(name.as_str())))
            }
            aast::Expr_::Lvar(name) => {
                // Looks up value of a local variable
                let aast::Lid(pos, lid) = &**name;
                context::load(ctx, (pos, lid))
            }
            aast::Expr_::Call(call) if call.unpacked_arg.is_none() => {
                // Evaluates a function/method call
                let aast::CallExpr {
                    func,
                    targs: _,
                    args,
                    unpacked_arg: _,
                } = &**call;
                call::eval(ctx, pos, func, args)
            }
            aast::Expr_::Binop(binop) => {
                // Handles binary operations
                let aast::Binop { bop, lhs, rhs } = &**binop;
                binop::eval(ctx, pos, bop, lhs, rhs)
            }
            _ => context::eval_error(ctx, pos, "Unsupported expression".to_string()),
        }
    }

    // Helper functions to safely extract values from the Value.t type.
    // These functions are primarily used during evaluation to safely assert
    // that a value is of an expected type (e.g., when evaluating a string
    // concatenation, we need to assert both operands are strings).
    // Returns None if the value is not of the expected type.

    fn str_expr<Ex, En>(
        ctx: &Context<'_>,
        pos: &Pos,
        e: &aast::Expr_<Ex, En>,
    ) -> Result<BString, EvalError> {
        match expr(ctx, pos, e)? {
            Value::Str(s) => Ok(s),
            Value::Unit => context::eval_error(
                ctx,
                pos,
                "Expected string value but got no value".to_string(),
            ),
        }
    }

    pub fn eval<Ex, En>(
        ctx: &Context<'_>,
        aast::Expr(_, pos, e): &aast::Expr<Ex, En>,
    ) -> Result<Value, EvalError> {
        expr(ctx, pos, e)
    }

    pub fn eval_str<Ex, En>(
        ctx: &Context<'_>,
        aast::Expr(_, pos, e): &aast::Expr<Ex, En>,
    ) -> Result<BString, EvalError> {
        str_expr(ctx, pos, e)
    }
}

/// Stmt module handles statement evaluation
pub mod stmt {
    use super::*;

    fn stmt<'a, Ex, En>(
        ctx: Context<'a>,
        pos: &Pos,
        s: &aast::Stmt_<Ex, En>,
    ) -> Result<ControlFlow<'a>, EvalError> {
        match s {
            aast::Stmt_::Return(e) if e.is_some() => {
                // Return statement
                let result = expr::eval(&ctx, e.as_ref().as_ref().unwrap())?;
                Ok(ControlFlow::Return(result))
            }
            aast::Stmt_::Return(_) => Ok(ControlFlow::Return(Value::Unit)),
            // No-op statement
            aast::Stmt_::Noop => Ok(ControlFlow::Next(ctx)),
            aast::Stmt_::Expr(e) => match &e.2 {
                aast::Expr_::Assign(assign)
                    if matches!(&**assign, (aast::Expr(_, _, aast::Expr_::Lvar(_)), None, _)) =>
                {
                    // Assignment
                    let (aast::Expr(_, _, aast::Expr_::Lvar(lid)), _, e) = &**assign else {
                        unreachable!()
                    };
                    let v = expr::eval(&ctx, e)?;
                    let ctx = context::store(ctx, lid.1.clone(), v);
                    Ok(ControlFlow::Next(ctx))
                }
                _ => {
                    // Expression statement
                    let _ = expr::eval(&ctx, e)?;
                    Ok(ControlFlow::Next(ctx))
                }
            },
            _ => context::eval_error(&ctx, pos, "Unsupported statement".to_string()),
        }
    }

    pub fn eval<'a, Ex, En>(
        ctx: Context<'a>,
        aast::Stmt(pos, s): &aast::Stmt<Ex, En>,
    ) -> Result<ControlFlow<'a>, EvalError> {
        stmt(ctx, pos, s)
    }
}

/// Block module handles evaluation of statement blocks
pub mod block {
    use super::*;

    /// Recursively evaluate statements in a block
    fn block<Ex, En>(ctx: Context<'_>, b: &[aast::Stmt<Ex, En>]) -> Result<Value, EvalError> {
        match b {
            [] => Ok(Value::Unit),
            [statement, rest @ ..] => match stmt::eval(ctx, statement)? {
                // Continue with next statement
                ControlFlow::Next(ctx) => block(ctx, rest),
                // Return from block
                ControlFlow::Return(value) => Ok(value),
            },
        }
    }

    pub fn eval<Ex, En>(ctx: Context<'_>, b: &aast::Block<Ex, En>) -> Result<Value, EvalError> {
        block(ctx, &b.0)
    }
}

/// ClassId module handles class identifier evaluation
pub mod class_id {
    use super::*;

    fn class_id<Ex, En>(
        ctx: &Context<'_>,
        pos: &Pos,
        cid: &aast::ClassId_<Ex, En>,
    ) -> Result<nast::Class_, EvalError> {
        match cid {
            aast::ClassId_::CIparent
            | aast::ClassId_::CIself
            | aast::ClassId_::CIstatic
            | aast::ClassId_::CIexpr(_)
            | aast::ClassId_::CIreified(_) => {
                // Special class refs not supported
                context::eval_error(ctx, pos, "Unsupported class reference".to_string())
            }
            // Named class
            aast::ClassId_::CI(name) => context::find_class(ctx, name),
        }
    }

    pub fn eval<Ex, En>(
        ctx: &Context<'_>,
        aast::ClassId(_, pos, cid): &aast::ClassId<Ex, En>,
    ) -> Result<nast::Class_, EvalError> {
        class_id(ctx, pos, cid)
    }
}

/// Call module handles function/method calls
pub mod call {
    use super::*;

    /// Build new context for function call with arguments
    fn build_ctx<'a, Ex, En, PEx, PEn>(
        ctx: &Context<'a>,
        name: &str,
        pos: &Pos,
        params: &[aast::FunParam<PEx, PEn>],
        args: &[aast::Argument<Ex, En>],
    ) -> Result<Context<'a>, EvalError> {
        let eval = |arg| expr::eval(ctx, arg);
        let mut new_ctx = context::push_stack_frame(ctx, name, pos);
        let mut named_params: std::collections::BTreeMap<&str, &String> =
            std::collections::BTreeMap::new();
        for param in params {
            match (&param.named, &param.info) {
                (Some(_), aast::FunParamInfo::ParamVariadic) => {}
                (Some(_), _) => {
                    // `String.chop_prefix_if_exists ~prefix:"$" param_name`
                    let key = param.name.strip_prefix('$').unwrap_or(&param.name);
                    named_params.insert(key, &param.name);
                }
                (None, _) => {}
            }
        }
        let mut positional_params = params.iter().filter(|param| param.named.is_none());
        // `let rec go args positional_params ctx = ...`
        for arg in args {
            match arg {
                aast::Argument::Anormal(arg) | aast::Argument::Ainout(_, arg) => {
                    match positional_params.next() {
                        Some(aast::FunParam {
                            name: param_name, ..
                        }) => {
                            let v = eval(arg)?;
                            new_ctx =
                                context::store(new_ctx, local_id::make_unscoped(param_name), v);
                        }
                        None => {
                            let _ = eval(arg)?;
                        }
                    }
                }
                aast::Argument::Anamed(ast_defs::Id(_, name), arg) => {
                    match named_params.get(name.as_str()) {
                        Some(param_name) => {
                            let v = eval(arg)?;
                            new_ctx = context::store(
                                new_ctx,
                                local_id::make_unscoped(param_name.as_str()),
                                v,
                            );
                        }
                        None => {
                            let _ = eval(arg)?;
                        }
                    }
                }
            }
        }
        Ok(new_ctx)
    }

    fn invoke<'a, Ex, En, PEx, PEn>(
        ctx: &Context<'a>,
        name: &str,
        pos: &Pos,
        (params, body): (&[aast::FunParam<PEx, PEn>], &aast::FuncBody<PEx, PEn>),
        args: &[aast::Argument<Ex, En>],
    ) -> Result<Value, EvalError> {
        let ctx = build_ctx(ctx, name, pos, params, args)?;
        let aast::FuncBody { fb_ast } = body;
        let result = block::eval(ctx, fb_ast)?;
        Ok(result)
    }

    /// `[Aast.Anormal arg]`
    fn single_normal<Ex, En>(args: &[aast::Argument<Ex, En>]) -> Option<&aast::Expr<Ex, En>> {
        match args {
            [aast::Argument::Anormal(arg)] => Some(arg),
            _ => None,
        }
    }

    /// The class name argument of the `PromptCtx.Class` functions:
    /// `(snd3 arg, classname)`.
    fn class_name_arg<Ex, En>(
        ctx: &Context<'_>,
        arg: &aast::Expr<Ex, En>,
    ) -> Result<aast::ClassName, EvalError> {
        let classname = expr::eval_str(ctx, arg)?;
        Ok(ast_defs::Id(arg.1.clone(), classname.to_string()))
    }

    /// Evaluate function call
    pub fn eval<Ex, En>(
        ctx: &Context<'_>,
        pos: &Pos,
        func: &aast::Expr<Ex, En>,
        args: &[aast::Argument<Ex, En>],
    ) -> Result<Value, EvalError> {
        use crate::naming_special_names::simpli_hack;
        let aast::Expr(_, _, func) = func;
        match func {
            aast::Expr_::Id(id) if id.1 == simpli_hack::file && single_normal(args).is_some() => {
                let arg = single_normal(args).unwrap();
                let path = expr::eval_str(ctx, arg)?;
                let path = crate::relative_path::from_root(&path.to_string());
                context::add_file_dep(ctx, &path);
                let contents = match crate::file_provider::rust_provider_backend::file::get_contents(context::provider(ctx), &path) {
                    Some(contents) => contents,
                    None => {
                        return context::eval_error(
                            ctx,
                            pos,
                            format!(
                                "Could not read {}",
                                crate::relative_path::to_absolute(&path)
                            ),
                        );
                    }
                };
                Ok(Value::Str(contents))
            }
            aast::Expr_::Id(id)
                if id.1 == simpli_hack::constructor && single_normal(args).is_some() =>
            {
                let name = class_name_arg(ctx, single_normal(args).unwrap())?;
                let data = prompt_ctx::class::constructor(ctx, &name)?;
                Ok(Value::Str(data.into()))
            }
            aast::Expr_::Id(id) if id.1 == simpli_hack::methods && single_normal(args).is_some() => {
                let name = class_name_arg(ctx, single_normal(args).unwrap())?;
                let data = prompt_ctx::class::methods(ctx, &name)?;
                Ok(Value::Str(data.into()))
            }
            aast::Expr_::Id(id)
                if id.1 == simpli_hack::static_methods && single_normal(args).is_some() =>
            {
                let name = class_name_arg(ctx, single_normal(args).unwrap())?;
                let data = prompt_ctx::class::static_methods(ctx, &name)?;
                Ok(Value::Str(data.into()))
            }
            aast::Expr_::Id(id) if id.1 == simpli_hack::fields && single_normal(args).is_some() => {
                let name = class_name_arg(ctx, single_normal(args).unwrap())?;
                let data = prompt_ctx::class::fields(ctx, &name)?;
                Ok(Value::Str(data.into()))
            }
            aast::Expr_::Id(id)
                if id.1 == simpli_hack::static_fields && single_normal(args).is_some() =>
            {
                let name = class_name_arg(ctx, single_normal(args).unwrap())?;
                let data = prompt_ctx::class::static_fields(ctx, &name)?;
                Ok(Value::Str(data.into()))
            }
            aast::Expr_::Id(name) => {
                let fd = context::find_function(ctx, name)?;
                let aast::Fun_ { params, body, .. } = &fd.fun;
                invoke(ctx, &name.1, pos, (params, body), args)
            }
            aast::Expr_::ClassConst(cc) => {
                let (cid, name) = &**cc;
                let class_ = class_id::eval(ctx, cid)?;
                let class_name = &class_.name.1;
                let method_name = format!("{}::{}", class_name, name.1);
                let aast::Method_ { params, body, .. } =
                    context::find_static_method(ctx, &class_, name)?;
                invoke(ctx, &method_name, pos, (params, body), args)
            }
            _ => context::eval_error(ctx, pos, "Unsupported call".to_string()),
        }
    }
}

/// Binop module handles binary operations
pub mod binop {
    use super::*;

    pub fn eval<Ex, En>(
        ctx: &Context<'_>,
        pos: &Pos,
        bop: &ast_defs::Bop,
        lhs_expr: &aast::Expr<Ex, En>,
        rhs_expr: &aast::Expr<Ex, En>,
    ) -> Result<Value, EvalError> {
        match bop {
            ast_defs::Bop::Dot => {
                let mut lhs_str = expr::eval_str(ctx, lhs_expr)?;
                let rhs_str = expr::eval_str(ctx, rhs_expr)?;
                lhs_str.extend_from_slice(&rhs_str);
                Ok(Value::Str(lhs_str))
            }
            _ => context::eval_error(ctx, pos, "Unsupported binary operation".to_string()),
        }
    }
}

/// Top-level evaluation function for user attributes
pub fn eval(env: &tast_env::Env, e: &tast::Expr) -> Result<BString, simplihack::T> {
    let ctx = context::init(env);
    match expr::eval_str(&ctx, e) {
        Ok(s) => Ok(s),
        Err(EvalError {
            msg,
            pos,
            stack_trace,
        }) => {
            let f = |stack_frame::T { name, location }: stack_frame::T| {
                oxidized::message::Message(
                    pos_or_decl::of_raw_pos(location),
                    BString::from(format!("via {}(...)", utils::strip_ns(&name))),
                )
            };
            Err(simplihack::T::Evaluation_error {
                pos: tast::get_position(e).clone(),
                stack_trace: typing_error::Lazy::new(move || {
                    let mut l = vec![oxidized::message::Message(
                        pos_or_decl::of_raw_pos(pos),
                        BString::from(msg),
                    )];
                    l.extend(stack_trace.into_iter().map(f));
                    l
                }),
            })
        }
    }
}
