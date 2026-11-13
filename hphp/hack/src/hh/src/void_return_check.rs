// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `void_return_check.ml`. See `hh/PORTING.md`.
//!
//! This check enforces 3 properties related to return statements and
//! functions' return types:
//!
//! Property 1: A function annotated with return type void must not contain a
//! return statement with a value.
//!
//! Property 2: A function containing a return statement without a value (or
//! returning implicitly) can only be annotated with a return type if that
//! return type is void (or <Awaitable<void>, for async functions).
//!
//! Property 3: A function must not mix return statements with and without a
//! value, even if such a function could be given a sufficiently general type.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::ast_defs::FunKind;
use oxidized::file_info;
use oxidized::pos::Pos;

use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::map_ty;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_make_type as make_type;
use crate::typing_native;
use crate::typing_reason as reason;

#[derive(Clone, Debug)]
pub struct State {
    /// Position of the currently active function
    pub fun_def_pos: Pos,
    /// Return type that the active function is annotated with.
    /// None if no annotation present.
    pub return_type: Option<aast::Hint>,
    /// Some if the active function can return without a value.
    /// If we only know that the function implicitly returns somewhere,
    /// the position is empty
    /// If we have seen an explicit return;, we store the location here
    pub prev_no_value_return: Option<Option<Pos>>,
    /// Some if we have seen a return foo; in the active function.
    /// In that case we store the location here.
    pub prev_value_return: Option<Pos>,
    /// Indicates whether the state has already been used to traverse a function.
    pub active: bool,
}

pub fn initial_dummy_state() -> State {
    State {
        return_type: None,
        prev_no_value_return: None,
        prev_value_return: None,
        fun_def_pos: Pos::NONE,
        active: false,
    }
}

/// An error that is reported only if it is forced (`unit Lazy.t`).
type LazyError<'e> = Box<dyn FnOnce() + 'e>;

pub fn validate_state(fun_span: &Pos, fun_kind: FunKind, env: &Env, s: &State) {
    // FIXME: Move as two functions to Ast_defs?
    let (is_generator, is_async) = match fun_kind {
        FunKind::FGenerator => (true, false),
        FunKind::FAsyncGenerator => (true, true),
        FunKind::FSync => (false, false),
        FunKind::FAsync => (false, true),
    };
    // The OCaml localizes the hint here, in a copy of the environment that it
    // drops, with errors ignored; only property 2 reads the result. It is
    // computed there, when that property is checked (nothing else reads or
    // changes the environment in between).
    let ret_type_hint_locl_opt = || -> Option<Ty> {
        s.return_type.as_ref().map(|ty_hint| {
            let dty = tast_env::hint_to_ty(env, ty_hint);
            tast_env::localize_no_subst(&mut env.clone(), true, &dty)
        })
    };
    let is_bad_supertype = |sub: &Ty, sup: &Ty| -> bool {
        let sup = map_ty(sup.clone(), |ty_| match ty_ {
            Ty_::Tclass(cid, ex, tys) if tys.len() == 1 && cid.1 == sn::classes::AWAITABLE => {
                let ty = tys.into_iter().next().unwrap();
                Ty_::Tclass(cid, ex, vec![tast_env::strip_dynamic(env, ty)])
            }
            x => x,
        });

        // returns false if sup is TAny, which implements the special behavior for
        // functions annotated with variations of TAny
        tast_env::is_sub_type(env, sub, &sup) && !tast_env::is_sub_type(env, &sup, sub)
    };
    let check_ret_type = |ret_type_hint_locl: &Ty| -> (bool, LazyError<'_>) {
        // Fixme: Should we use more precise logic to determine the expected
        // return type hint by factoring it into a function in Typing_return?
        let void = make_type::void(reason::none());
        let aw_void = make_type::awaitable(reason::none(), void.clone());
        let is_void_super_ty = is_bad_supertype(&void, ret_type_hint_locl);
        let is_awaitable_void_super_ty = is_bad_supertype(&aw_void, ret_type_hint_locl);
        if is_void_super_ty || is_awaitable_void_super_ty {
            let hint_loc = match &s.return_type {
                None => fun_span.clone(),
                Some(aast::Hint(hint_loc, _)) => hint_loc.clone(),
            };
            (
                false,
                Box::new(move || {
                    typing_error_utils::add_typing_error(
                        &typing_error::wellformedness(
                            primary::wellformedness::T::Non_void_annotation_on_return_void_function {
                                is_async,
                                hint_pos: hint_loc,
                            },
                        ),
                        env,
                    )
                }),
            )
        } else {
            (true, Box::new(|| ()))
        }
    };

    // Property 2  There are several exceptions:
    // - We do not complain if the function is annotated with Tany or Awaitable<Tany>
    //   (e.g., using one of its aliases in using one of its aliases in HH_FIXME)
    // - We only actually report an error if the return type hint of the function is a
    //   proper supertype of void (other than Tany, see first exception). Otherwise you get a normal
    //   type error already anyway.
    let (property_2_ok, raise_error_2): (bool, LazyError<'_>) =
        match (&s.prev_no_value_return, s.return_type.is_some(), is_generator) {
            (Some(_), true, false) => match ret_type_hint_locl_opt() {
                Some(ret_type_hint_locl) => check_ret_type(&ret_type_hint_locl),
                None => (true, Box::new(|| ())),
            },
            _ => (true, Box::new(|| ())),
        };

    // Property 3: Again, there are several exceptions:
    // - If the function is async, it is allowed to have a (implicit or explicit) no-value return and
    //   also a "return foo;", where the type of foo is void-typed (e.g., a call to a void-returning
    //   function or an wait of an Awaitable<void>).
    // - If the function is annotated with return type TAny (e.g., using one of its aliases in
    //   HH_FIXME), we do not complain.
    // - return await foo.
    let (property_3_ok, raise_error_3): (bool, LazyError<'_>) =
        // We must accommodate the slightly inconsistent rule that "return await foo;" is allowed in an
        // async function of type Awaitable<void> if foo's type is Awaitable<void>.
        // The test below currently lets the following corner case slip through:
        // An async lambda without a return type annotation can combine returning with and
        // without a value if we can otherwise type the lambda with an sufficiently general type like
        // Awaitable<mixed>
        match (&s.prev_no_value_return, &s.prev_value_return, is_async) {
            (Some(without_value_pos_opt), Some(with_value_pos), false) => {
                let fun_pos = s.fun_def_pos.clone();
                let with_value_pos = with_value_pos.clone();
                let without_value_pos_opt = without_value_pos_opt.clone();
                (
                    false,
                    Box::new(move || {
                        typing_error_utils::add_typing_error(
                            &typing_error::wellformedness(
                                primary::wellformedness::T::Returns_with_and_without_value {
                                    pos: fun_pos,
                                    with_value_pos,
                                    without_value_pos_opt,
                                },
                            ),
                            env,
                        )
                    }),
                )
            }
            _ => (true, Box::new(|| ())),
        };
    // Don't report violations of property 2 if prop 3 is also violated
    match (property_2_ok, property_3_ok) {
        (_, false) => raise_error_3(),
        (false, _) => raise_error_2(),
        _ => {}
    }
}

/// The object `visitor` (it inherits `Aast.iter`).
///
/// The state is only ever updated when entering a new function/method/lambda body
/// Additionally, the prev_return_form part of the state may be updated by on_return_form
/// while traversing a function body when we see a return statement.
pub struct Visitor {
    state: State,
}

/// `let visitor = object ... end`: the value, with its initial state.
pub fn visitor() -> Visitor {
    Visitor {
        state: initial_dummy_state(),
    }
}

impl Visitor {
    pub fn traverse_fun_body(
        &mut self,
        fun_span: &Pos,
        new_return_type: Option<aast::Hint>,
        new_fun_pos: Pos,
        fun_kind: FunKind,
        has_implicit_return: bool,
        env: &mut Env,
        traversal: impl FnOnce(&mut Self, &mut Env) -> tast_visitor::Res,
    ) -> tast_visitor::Res {
        let initial_no_value_return = if has_implicit_return {
            // There is an implicit return but we don't know where
            Some(None)
        } else {
            None
        };
        if self.state.active {
            // We are in a function/method already.
            // We do not descend into the nested function/method at this point. The handler
            // (defined below) will always traverse any nested functions/methods. Thus, if we
            // traversed the nested function/method here, the handler would *also* traverse it later
            // and we would report the same errors multiple times
            Ok(())
        } else {
            let new_state = State {
                return_type: new_return_type,
                prev_no_value_return: initial_no_value_return,
                prev_value_return: None,
                fun_def_pos: new_fun_pos,
                active: true,
            };
            self.state = new_state;
            let result = traversal(self, env);
            validate_state(fun_span, fun_kind, env, &self.state);
            result
        }
    }

    pub fn reset(&mut self) {
        self.state = initial_dummy_state()
    }

    pub fn update_seen_return_stmts(&mut self, with_value: bool, return_pos: &Pos) {
        if with_value {
            self.state.prev_value_return = Some(return_pos.clone())
        } else {
            self.state.prev_no_value_return = Some(Some(return_pos.clone()))
        }
    }
}

impl<'a> oxidized::aast_visitor::Visitor<'a> for Visitor {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn oxidized::aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    /// `on_expr_`
    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> tast_visitor::Res {
        match expr_ {
            aast::Expr_::Invalid(_) => Ok(()),
            _ => expr_.recurse(env, self),
        }
    }

    /// `on_fun_`
    fn visit_fun_(&mut self, env: &mut Env, fun_: &'a tast::Fun_) -> tast_visitor::Res {
        let decl_env_mode = tast_env::get_decl_env(env).mode;
        let has_impl_ret = tast_env::fun_has_implicit_return(env);
        if !(matches!(decl_env_mode, file_info::Mode::Mhhi)
            || typing_native::is_native_fun(env, fun_))
        {
            self.traverse_fun_body(
                &fun_.span,
                crate::aast::hint_of_type_hint(&fun_.ret).clone(),
                fun_.span.clone(),
                fun_.fun_kind,
                has_impl_ret,
                env,
                |this, env| fun_.recurse(env, this),
            )
        } else {
            Ok(())
        }
    }

    /// `on_method_`
    fn visit_method_(&mut self, env: &mut Env, method_: &'a tast::Method_) -> tast_visitor::Res {
        let has_impl_ret = tast_env::fun_has_implicit_return(env);
        let decl_env_mode = tast_env::get_decl_env(env).mode;
        if !(method_.abstract_
            || matches!(decl_env_mode, file_info::Mode::Mhhi)
            || typing_native::is_native_meth(env, method_))
        {
            self.traverse_fun_body(
                &method_.span,
                crate::aast::hint_of_type_hint(&method_.ret).clone(),
                method_.name.0.clone(),
                method_.fun_kind,
                has_impl_ret,
                env,
                |this, env| method_.recurse(env, this),
            )
        } else {
            Ok(())
        }
    }

    /// `on_stmt`
    fn visit_stmt(&mut self, env: &mut Env, st: &'a tast::Stmt) -> tast_visitor::Res {
        // Always call super to make sure the expressions in return statements are traversed
        let result = st.recurse(env, self);
        match st {
            aast::Stmt(return_pos, aast::Stmt_::Return(e)) if e.is_some() => {
                self.update_seen_return_stmts(true, return_pos);
                match &self.state.return_type {
                    Some(aast::Hint(pos2, h)) if matches!(&**h, aast::Hint_::Hprim(aast::Tprim::Tvoid)) => {
                        // Property 1
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Return_in_void {
                                pos: return_pos.clone(),
                                decl_pos: pos2.clone(),
                            }),
                            env,
                        )
                    }
                    _ => {}
                }
            }
            aast::Stmt(return_pos, aast::Stmt_::Return(_)) => {
                self.update_seen_return_stmts(false, return_pos)
            }
            _ => {}
        }
        result
    }

    /// `on_expr`
    fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> tast_visitor::Res {
        match e {
            aast::Expr(_, _, aast::Expr_::Invalid(_)) => Ok(()),
            _ => e.recurse(env, self),
        }
    }
}

struct Handler {
    visitor: Visitor,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_method_(&mut self, env: &Env, x: &'a tast::Method_) {
        let mut env = env.clone();
        tast_env::restore_method_env(&mut env, x);
        self.visitor.reset();
        let _ = oxidized::aast_visitor::Visitor::visit_method_(&mut self.visitor, &mut env, x);
    }

    fn at_fun_(&mut self, env: &Env, x: &'a tast::Fun_) {
        let mut env = env.clone();
        tast_env::restore_fun_env(&mut env, x);
        self.visitor.reset();
        let _ = oxidized::aast_visitor::Visitor::visit_fun_(&mut self.visitor, &mut env, x);
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler { visitor: visitor() })
}
