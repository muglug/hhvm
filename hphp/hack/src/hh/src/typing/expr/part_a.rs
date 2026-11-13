// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 2515-5016): module `Expr`.
//! See `hh/PORTING.md`.
//!
//! This part has the signature of `Expr` (the types it declares:
//! [`AttributeCheckPolicy`] and [`context::T`]), its `Log` submodule
//! ([`log`]) and its functions up to and including [`expr_`], the match on
//! expression kinds. The bodies of the large arms of that match are the
//! private functions `expr_<constructor>` below it.
//!
//! # Signatures
//!
//! The functions that type an expression return what the OCaml returns
//! besides the environment: `(tast::Expr, Ty)` for `env * Tast.expr *
//! locl_ty`, `(Vec<tast::Expr>, Vec<Ty>)` for lists.
//!
//! - `~expected:ExpectedTy.t option` is `Option<&expected_ty::T>`.
//! - `~ctxt:Context.t` is `&context::T`; `Context.default` is
//!   [`context::default`]`()`, and `Context.{ default with f = v }` is
//!   `context::T { f: v, ..context::default() }`.
//! - `attribute_check_policy` is [`AttributeCheckPolicy`] (`CheckAll`,
//!   `SkipPackage`, `SkipAllAccess`).
//! - Positions are `&Pos`.
//! - The arguments are in the order of the signature, labelled ones
//!   included: [`expr`] is `expr(expected, ctxt, env, e)` for `expr
//!   ~expected ~ctxt env e`, [`infer_exprs`] is `infer_exprs(el, ctxt, env)`.
//! - [`argument_list_exprs`] takes the partial application `expr ~expected
//!   ~ctxt` as a closure `FnMut(&mut Env, &nast::Expr) -> (tast::Expr, Ty)`.
//!
//! # Exceptions
//!
//! `Typing_inference_env.InconsistentTypeVarState` is a panic whose payload
//! is [`InconsistentTypeVarState`]; [`expr_handle_inconsistent_type_var_state`]
//! catches it where the OCaml has its `try ... with`, and goes on with the
//! environment from before the attempt, as the OCaml does.

use itertools::Either;
use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Variance;
use oxidized::local_id::LocalId;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::BPos;
use pos::Positioned;
use pos::ToOxidized;
use pos::TypeName;
use ty::reason::Reason as _;

#[allow(unused_imports)]
use super::*;
use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::exception;
// module Cls = Folded_class
use crate::folded_class as cls;
use crate::format;
use crate::hack_event_logger;
use crate::local_id;
use crate::pos_or_decl;
use crate::tast;
use crate::telemetry;
// module TCO = Typechecker_options
use crate::typechecker_options as tco;
use crate::tvid;
use crate::typing::afield;
use crate::typing::binop;
use crate::typing::class_get_expr;
use crate::typing::class_id;
use crate::typing::expression_tree;
use crate::typing::function_pointer;
use crate::typing::lambda;
use crate::typing::method_caller;
use crate::typing::prelude::*;
use crate::typing::xhp_attribute;
// module C = Typing_continuations
use crate::typing_continuations as c;
// open Typing_defs (with Typing_defs_core)
use crate::typing_defs::*;
// open Typing_defs_constraints
use crate::typing_defs_constraints::*;
use crate::typing_defs_flags;
// module Env = Typing_env
use crate::typing_env as env;
// open Typing_env_types
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
use crate::typing_inference_env::InconsistentTypeVarState;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
use crate::typing_local_types::Local;
use crate::typing_log;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module TOG = Typing_object_get
use crate::typing_object_get as tog;
// module Phase = Typing_phase
use crate::typing_phase as phase;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::Blame;
use crate::typing_reason::BlameSource;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
// module Union = Typing_union
use crate::typing_union as union;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;
use crate::utils::strip_ns;

/// The names of `Naming_special_names` that `naming_special_names_rust` does
/// not have, with the OCaml values.
mod missing_special_names {
    /// `Classes.cHHTypedFormatString`
    pub const C_HH_TYPED_FORMAT_STRING: &str = "\\HH\\TypedFormatString";
    /// `PseudoFunctions.hh_time`
    pub const HH_TIME: &str = "\\hh_time";
}

/// `SN.Classes.is_typed_format_string`
fn is_typed_format_string(x: &str) -> bool {
    x == missing_special_names::C_HH_TYPED_FORMAT_STRING
}

/// `TCO.pessimise_builtins`, which `crate::typechecker_options` does not
/// have.
fn tco_pessimise_builtins(t: &tco::T) -> bool {
    // `everything_sdt t || t.tco_pessimise_builtins`
    t.po.everything_sdt || t.tco_pessimise_builtins
}

/// `Option.iter ~f:(Typing_error_utils.add_typing_error ~env) ty_err_opt`
fn add_typing_error_opt(env: &Env, ty_err_opt: &Option<typing_error::T>) {
    if let Some(ty_err) = ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
}

/// `int_of_string`: an OCaml integer literal (an optional sign, then `0x`,
/// `0o`, `0b` or `0u` and digits, or decimal digits, and `_` after the first
/// digit), within the range of an OCaml `int`. Raises `Failure
/// "int_of_string"` otherwise.
fn int_of_string(s: &str) -> isize {
    const MAX: i128 = (1 << 62) - 1;
    let fail = || -> ! { panic!("int_of_string") };
    let (negative, s) = match s.strip_prefix('-') {
        Some(s) => (true, s),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let lower = s.to_ascii_lowercase();
    let (radix, digits, decimal) = if let Some(d) = lower.strip_prefix("0x") {
        (16, d, false)
    } else if let Some(d) = lower.strip_prefix("0o") {
        (8, d, false)
    } else if let Some(d) = lower.strip_prefix("0b") {
        (2, d, false)
    } else if let Some(d) = lower.strip_prefix("0u") {
        (10, d, false)
    } else {
        (10, lower.as_str(), true)
    };
    match digits.chars().next() {
        Some(c) if c.is_digit(radix) => {}
        _ => fail(),
    }
    let mut n: i128 = 0;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        let d = match c.to_digit(radix) {
            Some(d) => d,
            None => fail(),
        };
        n = n * radix as i128 + d as i128;
        // Unsigned literals can use all the 63 bits; they wrap around.
        if n > 2 * MAX + 1 {
            fail()
        }
    }
    if decimal {
        // Decimal literals are signed: up to `max_int`, or `-min_int`.
        if n > MAX + (negative as i128) {
            fail()
        }
    } else if n > MAX {
        n -= 2 * (MAX + 1);
    }
    (if negative { -n } else { n }) as isize
}

/// `Pos.show_absolute (Pos.to_absolute p)`, for the logger. (`Pos.show_absolute`
/// is the printer that `[@@deriving show]` makes, which is not ported: this is
/// the `Debug` form of the same record. The logger is a stub that ignores it.)
fn show_absolute_pos(p: &Pos) -> String {
    format!("{:?}", crate::pos::to_absolute(p))
}

// ---------------------------------------------------------------------------
// The signature of `Expr`
// ---------------------------------------------------------------------------

/// Controls which access checks are performed when typing expressions
/// inside attribute contexts.
/// - [Check_all]: default — run all visibility, module, and package checks.
/// - [Skip_package]: skip package boundary checks only, keep module/internal
///   and private/protected checks. Used for first-pass attribute constructor
///   arg typing where [is_attribute] suppresses package lint.
/// - [Skip_all_access]: skip all top-level access and class-member visibility
///   checks. Used for the second-pass [user_attribute] re-typing for TAST
///   construction, where checks were already performed in the first pass.
///
/// `attribute_check_policy`: `Check_all` is [`AttributeCheckPolicy::CheckAll`],
/// `Skip_package` is [`AttributeCheckPolicy::SkipPackage`], `Skip_all_access`
/// is [`AttributeCheckPolicy::SkipAllAccess`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttributeCheckPolicy {
    CheckAll,
    SkipPackage,
    SkipAllAccess,
}

/// `pp_attribute_check_policy` (`[@@deriving show]`): the constructor
/// qualified by the module path.
pub fn pp_attribute_check_policy(fmt: &mut format::Formatter, x: &AttributeCheckPolicy) {
    format::pp_print_string(
        fmt,
        match x {
            AttributeCheckPolicy::CheckAll => "Typing.Expr.Check_all",
            AttributeCheckPolicy::SkipPackage => "Typing.Expr.Skip_package",
            AttributeCheckPolicy::SkipAllAccess => "Typing.Expr.Skip_all_access",
        },
    )
}

/// `show_attribute_check_policy` (`[@@deriving show]`)
pub fn show_attribute_check_policy(x: &AttributeCheckPolicy) -> String {
    format::asprintf(|fmt| pp_attribute_check_policy(fmt, x))
}

/// `Expr.Context`
pub mod context {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct T {
        /// Set to [true] when the subexpression we are typing occurs inside a [using_stmt].
        pub is_using_clause: bool,
        /// Indicates whether the subexpression we are typing appears in lvalue top-level, lvalue subexpression or another position
        pub valkind: valkind::T,
        /// Controls which access checks are skipped when typing attribute parameters.
        pub attribute_check_policy: AttributeCheckPolicy,
        /// Set to [Some] when the subexpression we are typing occurs inside an [Await] expression.
        pub in_await: Option<Reason>,
        /// Set to [true] when the subexpression we are typing occurs on the
        /// left-hand-side of a [binop] with the [QuestionQuestion] (coalesce)
        /// binary operator
        pub lhs_of_null_coalesce: bool,
        /// Set to [true] when the subexpression we are typing is either a function/method argument, the receiver of a property access or instance method invocation or the scrutinee in a [foreach] statment. When set, [This] and [Lvar] expressions will be checked against in-scope using vars to ensure they don't escape
        pub accept_using_var: bool,
        /// Set to [false] when the subexpression is a lvalue we are defining. When true, we raise an error if [Lvar] or [This] expressions are not bound in the environment.
        pub check_defined: bool,
        /// Set to [true] when checking a lambda expression that is immediately called
        pub immediately_called_lambda: bool,
        /// Set to [true] when the subexpression we are typing occurs inside an [ReadonlyExpr] expression.
        pub support_readonly_return: bool,
    }

    /// `Context.default`
    pub fn default() -> T {
        T {
            is_using_clause: false,
            valkind: valkind::T::Other,
            attribute_check_policy: AttributeCheckPolicy::CheckAll,
            in_await: None,
            lhs_of_null_coalesce: false,
            accept_using_var: false,
            check_defined: true,
            immediately_called_lambda: false,
            support_readonly_return: false,
        }
    }

    impl Default for T {
        fn default() -> T {
            default()
        }
    }

    /// `pp` (`[@@deriving show]`): the calls that the printer of
    /// `ppx_deriving.show` makes for a record (`"@[<2>{ "`, then for each field
    /// `"@[%s =@ "`, the value and `"@]"`, separated by `";@ "`, then
    /// `"@ }@]"`), the first field qualified by the module path. `in_await`
    /// is `[@opaque]`.
    pub fn pp(fmt: &mut format::Formatter, x: &T) {
        let T {
            is_using_clause,
            valkind,
            attribute_check_policy,
            in_await: _,
            lhs_of_null_coalesce,
            accept_using_var,
            check_defined,
            immediately_called_lambda,
            support_readonly_return,
        } = x;
        fn field(fmt: &mut format::Formatter, name: &str, value: impl FnOnce(&mut format::Formatter)) {
            // `"@[%s =@ "`
            format::pp_open_box(fmt, 0);
            format::pp_print_string(fmt, name);
            format::pp_print_string(fmt, " =");
            format::pp_print_space(fmt);
            value(fmt);
            // `"@]"`
            format::pp_close_box(fmt)
        }
        fn sep(fmt: &mut format::Formatter) {
            // `";@ "`
            format::pp_print_char(fmt, ';');
            format::pp_print_space(fmt)
        }
        // `"%B"`
        fn pp_bool(fmt: &mut format::Formatter, b: bool) {
            format::pp_print_string(fmt, if b { "true" } else { "false" })
        }
        // `"@[<2>{ "`
        format::pp_open_box(fmt, 2);
        format::pp_print_string(fmt, "{ ");
        field(fmt, "Typing.Expr.Context.is_using_clause", |fmt| {
            pp_bool(fmt, *is_using_clause)
        });
        sep(fmt);
        field(fmt, "valkind", |fmt| {
            format::pp_print_string(fmt, &valkind::show(valkind))
        });
        sep(fmt);
        field(fmt, "attribute_check_policy", |fmt| {
            pp_attribute_check_policy(fmt, attribute_check_policy)
        });
        sep(fmt);
        field(fmt, "in_await", |fmt| format::pp_print_string(fmt, "<opaque>"));
        sep(fmt);
        field(fmt, "lhs_of_null_coalesce", |fmt| {
            pp_bool(fmt, *lhs_of_null_coalesce)
        });
        sep(fmt);
        field(fmt, "accept_using_var", |fmt| pp_bool(fmt, *accept_using_var));
        sep(fmt);
        field(fmt, "check_defined", |fmt| pp_bool(fmt, *check_defined));
        sep(fmt);
        field(fmt, "immediately_called_lambda", |fmt| {
            pp_bool(fmt, *immediately_called_lambda)
        });
        sep(fmt);
        field(fmt, "support_readonly_return", |fmt| {
            pp_bool(fmt, *support_readonly_return)
        });
        // `"@ }@]"`
        format::pp_print_space(fmt);
        format::pp_print_char(fmt, '}');
        format::pp_close_box(fmt)
    }

    /// `show` (`[@@deriving show]`): `Format.asprintf "%a" pp x`.
    pub fn show(x: &T) -> String {
        format::asprintf(|fmt| pp(fmt, x))
    }
}

/// `Expr.Log`
pub mod log {
    use super::*;

    pub fn should_log_expr(env: &Env) -> bool {
        typing_log::should_log(env, "typing", 1)
    }

    /// The OCaml is applied to the thunk that types the expression last
    /// (`Log.log_expr env expected ctxt p @@ fun () -> ...`); the thunk takes
    /// the environment here. The `result` printer of the OCaml prints the type
    /// with the environment the thunk returned: it is computed right after
    /// the thunk, which is the same (printing has no effect).
    pub fn log_expr(
        env: &mut Env,
        expected: Option<&expected_ty::T>,
        ctxt: &context::T,
        p: &Pos,
        f: impl FnOnce(&mut Env) -> (tast::Expr, Ty),
    ) -> (tast::Expr, Ty) {
        let (ureason_string, expected_ty_log) = match expected {
            None => ("".to_string(), vec![]),
            Some(expected_ty::T { reason: r, ty, .. }) => (
                format!(" {}", reason::string_of_ureason(r)),
                vec![("expected_ty".to_string(), typing_print::debug(&*env, ty))],
            ),
        };
        let mut arguments = vec![("ctxt".to_string(), context::show(ctxt))];
        arguments.extend(expected_ty_log);
        let function_name = format!("{}{}", "Typing.expr ", ureason_string);
        let (res, _) = typing_log::log_function(
            &pos_or_decl::of_raw_pos(p.clone()),
            &function_name,
            &arguments,
            |(_, result): &((tast::Expr, Ty), String)| Some(result.clone()),
            || {
                let res = f(env);
                let result = typing_print::debug(&*env, &res.1);
                (res, result)
            },
        );
        res
    }
}

// ---------------------------------------------------------------------------
// The functions of `Expr`, up to `expr_`
// ---------------------------------------------------------------------------

/// Compute an expected type for a lambda that is being called with the
/// given args. Where the type of the argument isn't obvious (without actual
/// type checking, just use a fresh tyvar
pub fn lambda_expected(
    p: &Pos,
    env: &mut Env,
    fun_: &nast::Fun_,
    args: &[nast::Argument],
) -> Ty {
    let get_arg_params = |env: &mut Env, arg: &nast::Argument| -> FunParam {
        let fresh = |env: &mut Env, p: &Pos| -> Ty {
            env::fresh_type_reason(Some(Variance::Contravariant), env, p.clone(), |v| {
                reason::type_variable(p.clone(), v)
            })
        };
        let (exp_opt, fp_name, is_named) = match arg {
            aast::Argument::Ainout(_, _) => (None, None, false),
            aast::Argument::Anamed(name, exp) => {
                let aast::Expr((), p, exp_) = exp;
                (Some((p, exp_)), Some(name.1.clone()), true)
            }
            aast::Argument::Anormal(exp) => {
                let aast::Expr((), p, exp_) = exp;
                (Some((p, exp_)), None, false)
            }
        };
        let fp_type = match exp_opt {
            None => env::fresh_type_reason(Some(Variance::Invariant), env, p.clone(), |v| {
                reason::type_variable(p.clone(), v)
            }),
            Some((p, exp_)) => match exp_ {
                aast::Expr_::Null => make_type::null(reason::witness(p.clone())),
                aast::Expr_::True | aast::Expr_::False => {
                    make_type::bool(reason::witness(p.clone()))
                }
                aast::Expr_::Int(_) => make_type::int(reason::witness(p.clone())),
                aast::Expr_::Float(_) => make_type::float(reason::witness(p.clone())),
                aast::Expr_::String(_) => make_type::string(reason::witness(p.clone())),
                aast::Expr_::Lvar(lid) if env::is_local_defined(env, &lid.1) => {
                    let locl = env::get_local(env, &lid.1);
                    locl.ty
                }
                aast::Expr_::Dollardollar(_) => {
                    let dd_var = local_id::make_unscoped(sn::special_idents::DOLLAR_DOLLAR);
                    if env::is_local_defined(env, &dd_var) {
                        let locl = env::get_local(env, &dd_var);
                        locl.ty
                    } else {
                        fresh(env, p)
                    }
                }
                _ => fresh(env, p),
            },
        };
        let fp_flags = typing_defs_flags::fun_param::set_named(
            is_named,
            typing_defs_flags::fun_param::default(),
        );
        FunParam {
            pos: pos_or_decl::of_raw_pos(p.clone()),
            name: fp_name,
            type_: fp_type,
            flags: fp_flags,
            def_value: None,
        }
    };
    let mut ft_params = vec![];
    for arg in args {
        ft_params.push(get_arg_params(env, arg));
    }
    let ft_flags = crate::decl_nast::lambda_flags(fun_);
    let ft_ret = env::fresh_type_reason(Some(Variance::Covariant), env, p.clone(), |v| {
        reason::type_variable(p.clone(), v)
    });
    mk((
        reason::witness(p.clone()),
        Ty_::Tfun(std::rc::Rc::new(FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: ft_params,
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(pos_or_decl::of_raw_pos(p.clone())),
            },
            ret: ft_ret,
            flags: ft_flags,
            instantiated: true,
        })),
    ))
}

/// The OCaml returns `(env1, err1, false)` or `(env2, err2, true)`, where
/// `env2` comes from the environment the function was given, not from
/// `env1`: the second coercion starts from the environment as it was before
/// the first.
pub fn coerce_nonlike_and_like(
    coerce_for_op: bool,
    is_dynamic_aware: bool,
    env: &mut Env,
    pos: &Pos,
    reason: &Ureason,
    ty: &Ty,
    ety: &Ty,
    ety_like: &Ty,
) -> (Option<typing_error::T>, bool) {
    let env0 = env.clone();
    let err1 = crate::typing_coercion::coerce_type(
        Some(coerce_for_op),
        Some(is_dynamic_aware),
        None,
        pos.clone(),
        reason.clone(),
        env,
        ty.clone(),
        ety.clone(),
        Enforcement::Enforced,
        callback::unify_error(),
    );
    match err1 {
        None => (None, false),
        Some(_) => {
            // Now check against the pessimised type
            *env = env0;
            let err2 = crate::typing_coercion::coerce_type(
                Some(coerce_for_op),
                Some(is_dynamic_aware),
                None,
                pos.clone(),
                reason.clone(),
                env,
                ty.clone(),
                ety_like.clone(),
                Enforcement::Enforced,
                callback::unify_error(),
            );
            (err2, true)
        }
    }
}

/// `result` is applied to the environment and the type, as in OCaml, and
/// gives the result.
pub fn typename_expr(
    env: &mut Env,
    pcid: &Pos,
    sid: &aast::Sid,
    outer: &nast::Expr,
    result: impl FnOnce(&mut Env, Ty) -> (tast::Expr, Ty),
) -> (tast::Expr, Ty) {
    match env::get_typedef(env, &sid.1) {
        decl_entry::T::Found(td) => {
            let tparaml = &td.tparams;
            // Typedef type parameters cannot have constraints
            let params: Vec<DeclTy> = tparaml
                .iter()
                .map(|tp| {
                    // TODO(T69551141) handle type arguments for Tgeneric
                    // `MakeType.generic (Reason.witness_from_decl p) x`
                    DeclTy::generic(R::witness_from_decl(tp.name.pos().clone()), tp.name.id())
                })
                .collect();
            let p_ = pos_or_decl::of_raw_pos(pcid.clone());
            let tdef = DeclTy::apply(
                R::witness_from_decl(BPos::from(&p_)),
                // `Positioned.of_raw_positioned sid`
                Positioned::new(BPos::from(&sid.0), TypeName::new(&sid.1)),
                params.into_boxed_slice(),
            );
            let typename = DeclTy::apply(
                R::witness_from_decl(BPos::from(&p_)),
                Positioned::new(BPos::from(&p_), TypeName::new(sn::classes::TYPE_NAME)),
                Box::new([tdef]),
            );
            let mut tparams = vec![];
            for _tp in tparaml.iter() {
                tparams.push(env::fresh_type(env, pcid.clone()));
            }
            let ety_env = ExpandEnv {
                substs: phase::decl_subst_make_locl(&tparaml[..], &tparams),
                ..empty_expand_env_with_on_error(
                    env::invalid_type_hint_assert_primary_pos_in_current_decl(env),
                )
            };
            let ty_err_opt1 =
                phase::check_tparams_constraints(pcid.clone(), &ety_env, env, &tparaml[..]);
            add_typing_error_opt(env, &ty_err_opt1);
            let (ty_err_opt2, ty) = phase::localize(&ety_env, env, &typename);
            add_typing_error_opt(env, &ty_err_opt2);
            result(env, ty)
        }
        decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
            // Should not expect None as we've checked whether the sid is a typedef
            expr_error(env, pcid.clone(), outer)
        }
    }
}

pub fn expr(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    e: &nast::Expr,
) -> (tast::Expr, Ty) {
    let aast::Expr(_, p, _) = e;
    if log::should_log_expr(env) {
        log::log_expr(env, expected, ctxt, p, |env| {
            expr_handle_inconsistent_type_var_state(expected, ctxt, env, e)
        })
    } else {
        expr_handle_inconsistent_type_var_state(expected, ctxt, env, e)
    }
}

/// Not in the OCaml: how [`expr_handle_inconsistent_type_var_state`] keeps
/// the environment it may have to restore. See [`check_without_snapshots`].
pub mod snapshots {
    use std::cell::Cell;
    use std::sync::LazyLock;

    use crate::typing_inference_env::InconsistentTypeVarState;

    thread_local! {
        /// Whether each expression keeps a copy of the environment it was
        /// given (the OCaml behaviour; `false` inside
        /// [`check_without_snapshots`]).
        pub(super) static ON: Cell<bool> = const { Cell::new(true) };
        /// Whether an `InconsistentTypeVarState` reached an expression while
        /// `ON` was `false`.
        pub(super) static MISSED: Cell<bool> = const { Cell::new(false) };
        /// The expressions typed since [`reset_fake_exceptions`].
        static COUNT: Cell<u64> = const { Cell::new(0) };
    }

    /// A test hook: with `HH_FAKE_ITVS=N`, every N-th expression typed
    /// (counted from [`reset_fake_exceptions`]) raises an
    /// `InconsistentTypeVarState` before it is typed, to check that
    /// [`check_without_snapshots`] gives what the OCaml way gives
    /// (`HH_EXPR_SNAPSHOTS=1` keeps the OCaml way everywhere).
    static FAKE_EVERY: LazyLock<Option<u64>> = LazyLock::new(|| {
        std::env::var("HH_FAKE_ITVS")
            .ok()
            .and_then(|s| s.parse().ok())
            .filter(|n| *n > 0)
    });

    static ALWAYS_ON: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("HH_EXPR_SNAPSHOTS").is_some());

    pub fn reset_fake_exceptions() {
        COUNT.set(0)
    }

    pub(super) fn maybe_raise_fake() {
        if let Some(n) = *FAKE_EVERY {
            let c = COUNT.get() + 1;
            COUNT.set(c);
            if c % n == 0 {
                std::panic::panic_any(InconsistentTypeVarState("fake (HH_FAKE_ITVS)".to_string()))
            }
        }
    }

    /// Runs `f` (the check of one file, from its start) with the expressions
    /// keeping no copy of the environment, and returns its result and
    /// whether an `InconsistentTypeVarState` reached an expression (then the
    /// result is not what the OCaml computes: the caller checks the file
    /// again from its start in the OCaml way, `f` outside of this).
    ///
    /// The copy that each expression keeps makes the next write of the
    /// environment copy the whole record, at every expression, for an
    /// exception that does not happen in practice.
    pub fn check_without_snapshots<R>(f: impl FnOnce() -> R) -> (R, bool) {
        if *ALWAYS_ON {
            return (f(), false);
        }
        struct Restore;
        impl Drop for Restore {
            fn drop(&mut self) {
                ON.set(true)
            }
        }
        ON.set(false);
        MISSED.set(false);
        let restore = Restore;
        let res = f();
        drop(restore);
        (res, MISSED.replace(false))
    }
}

/// On `InconsistentTypeVarState`, the OCaml goes on with the environment it
/// was given (the attempt only produced a new one): it is saved before the
/// attempt and restored on that path. (Unless the snapshots are off: see
/// [`snapshots::check_without_snapshots`].)
pub fn expr_handle_inconsistent_type_var_state(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    e: &nast::Expr,
) -> (tast::Expr, Ty) {
    let aast::Expr(_, p, _) = e;
    debug_last_pos.with(|r| *r.borrow_mut() = p.clone());
    if !snapshots::ON.get() {
        if snapshots::MISSED.get() {
            // The result is thrown away: stop typing the file soon.
            std::panic::resume_unwind(Box::new(InconsistentTypeVarState(
                "(the file is checked again)".to_string(),
            )))
        }
        return match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            snapshots::maybe_raise_fake();
            expr_(expected, ctxt, env, e)
        })) {
            Ok(res) => res,
            Err(payload) => {
                if payload.is::<InconsistentTypeVarState>() {
                    snapshots::MISSED.set(true)
                }
                std::panic::resume_unwind(payload)
            }
        };
    }
    let env0 = env.clone();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        snapshots::maybe_raise_fake();
        expr_(expected, ctxt, env, e)
    })) {
        Ok(res) => res,
        Err(payload) => match payload.downcast::<InconsistentTypeVarState>() {
            Ok(exn) => {
                // we don't want to catch unwanted exceptions here, eg Timeouts
                diagnostics_state::exception_occurred(p.clone(), &exception::wrap(*exn));
                *env = env0;
                expr_error(env, p.clone(), e)
            }
            Err(payload) => std::panic::resume_unwind(payload),
        },
    }
}

/// Some (legacy) special functions are allowed in initializers,
/// therefore treat them as pure and insert the matching capabilities.
pub fn expr_with_pure_coeffects(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    e: &nast::Expr,
) -> (tast::Expr, Ty) {
    let aast::Expr(_, p, _) = e;
    let pure = make_type::mixed(reason::witness(p.clone()));
    let (te, ty) = with_special_coeffects(env, pure.clone(), pure, |env| {
        triple_to_pair(expr(expected, &context::default(), env, e))
    });
    (te, ty)
}

pub fn lvalue(env: &mut Env, e: &nast::Expr) -> (tast::Expr, Ty) {
    expr_(
        None,
        &context::T {
            valkind: valkind::T::Lvalue,
            check_defined: false,
            accept_using_var: false,
            ..context::default()
        },
        env,
        e,
    )
}

/// The OCaml recursion, from the first element to the last.
pub fn lvalues(env: &mut Env, el: &[nast::Expr]) -> (Vec<tast::Expr>, Vec<Ty>) {
    let mut tel = vec![];
    let mut tyl = vec![];
    for e in el {
        let (te, ty) = lvalue(env, e);
        tel.push(te);
        tyl.push(ty);
    }
    (tel, tyl)
}

/// $x ?? 0 is handled similarly to $x ?: 0.
/// TODO TAST: type refinement should be made explicit in the typed AST
pub fn eif(
    env: &mut Env,
    expected: Option<&expected_ty::T>,
    in_await: Option<Reason>,
    p: &Pos,
    c: &nast::Expr,
    e1: Option<&nast::Expr>,
    e2: &nast::Expr,
) -> (tast::Expr, Ty) {
    let (tc, tyc) = expr(None, &context::default(), env, c);
    let aast::Expr(cond_ty, cond_pos, _) = &tc;
    check_bool_for_condition(env, cond_pos, cond_ty.clone());
    let parent_lenv = env.lenv.clone();
    super::condition(env, true, &tc);
    let (te1, ty1) = match e1 {
        None => {
            let ty = inter::intersect_with_nonnull(env, pos_or_decl::of_raw_pos(p.clone()), tyc);
            (None, ty)
        }
        Some(e1) => {
            let (te1, ty1) = expr(
                expected,
                &context::T {
                    in_await: in_await.clone(),
                    ..context::default()
                },
                env,
                e1,
            );
            (Some(te1), ty1)
        }
    };
    // `let env = { env with lenv = parent_lenv }`
    let lenv1 = std::mem::replace(&mut env.lenv, parent_lenv.clone());
    super::condition(env, false, &tc);
    let (te2, ty2) = expr(
        expected,
        &context::T {
            in_await,
            ..context::default()
        },
        env,
        e2,
    );
    let lenv2 = env.lenv.clone();
    lenv::union_lenvs(env, p, &parent_lenv, &lenv1, &lenv2);
    let ty = union::union(env, None, Some(true), ty1, ty2);
    make_result(
        env,
        p.clone(),
        aast::Expr_::Eif(Box::new((tc, te1, te2))),
        ty,
    )
}

/// The OCaml recursion, from the first element to the last.
pub fn infer_exprs(
    el: &[nast::Expr],
    ctxt: &context::T,
    env: &mut Env,
) -> (Vec<tast::Expr>, Vec<Ty>) {
    let mut tel = vec![];
    let mut tyl = vec![];
    for e in el {
        let (te, ty) = expr(None, ctxt, env, e);
        tel.push(te);
        tyl.push(ty);
    }
    (tel, tyl)
}

/// The OCaml recursion, from the first element to the last: when the
/// expected types run out, the remaining elements are inferred with
/// `Context.default` (not `ctxt`).
pub fn check_exprs(
    el: &[nast::Expr],
    ctxt: &context::T,
    env: &mut Env,
    expected_tys: &[expected_ty::T],
) -> (Vec<tast::Expr>, Vec<Ty>) {
    let mut tel = vec![];
    let mut tyl = vec![];
    let mut el = el;
    let mut expected_tys = expected_tys;
    loop {
        match (el, expected_tys) {
            ([], _) => break,
            ([e, el_rest @ ..], [expected_ty, expected_tys_rest @ ..]) => {
                let (te, ty) = expr(Some(expected_ty), ctxt, env, e);
                tel.push(te);
                tyl.push(ty);
                el = el_rest;
                expected_tys = expected_tys_rest;
            }
            (el, []) => {
                let (tel_rest, tyl_rest) = infer_exprs(el, &context::default(), env);
                tel.extend(tel_rest);
                tyl.extend(tyl_rest);
                break;
            }
        }
    }
    (tel, tyl)
}

/// `expr_cb` is the partial application the OCaml passes (`expr ~expected
/// ~ctxt`). The OCaml recursion, from the first argument to the last.
pub fn argument_list_exprs(
    mut expr_cb: impl FnMut(&mut Env, &nast::Expr) -> (tast::Expr, Ty),
    env: &mut Env,
    el: &[nast::Argument],
) -> (Vec<tast::Argument>, Vec<Ty>) {
    let mut argument = |env: &mut Env, a: &nast::Argument| -> (tast::Argument, Ty) {
        match a {
            aast::Argument::Anormal(e) => {
                let (te, ty) = expr_cb(env, e);
                (aast::Argument::Anormal(te), ty)
            }
            aast::Argument::Ainout(pos, e) => {
                let (te, ty) = expr_cb(env, e);
                (aast::Argument::Ainout(pos.clone(), te), ty)
            }
            aast::Argument::Anamed(name, e) => {
                let (te, ty) = expr_cb(env, e);
                (aast::Argument::Anamed(name.clone(), te), ty)
            }
        }
    };
    let mut tel = vec![];
    let mut tyl = vec![];
    for e in el {
        let (te, ty) = argument(env, e);
        tel.push(te);
        tyl.push(ty);
    }
    (tel, tyl)
}

// ---------------------------------------------------------------------------
// `expr_` and the functions local to it
// ---------------------------------------------------------------------------

/// The `infer_element_type_for_collection` of `expr_`, which captures the
/// position `p` of the expression (first argument here).
///
/// Given an expected type for elements (as extracted from a parameter or return hint,
/// or explicit type argument), a list of expressions, and a function that infers
/// the type of an element, infer an element type for the whole collection.
///
/// explicit is true if the expected type is just the explicit type argument
/// can_pessimise is true if this is a pessimisable builtin (e.g. Vector)
/// bound is the bound on the type parameter if present (only ever arraykey)
pub fn infer_element_type_for_collection(
    p: &Pos,
    expected: Option<&expected_ty::T>,
    explicit: bool,
    reason: Ureason,
    can_pessimise: bool,
    bound: Option<Ty>,
    use_pos: &Pos,
    r: impl FnOnce(tvid::T) -> Reason,
    env: &mut Env,
    exprs: &[&nast::Expr],
    mut expr_infer: impl FnMut(Option<&expected_ty::T>, &mut Env, &nast::Expr) -> (tast::Expr, Ty),
) -> (Vec<tast::Expr>, Ty) {
    // Is this a pessimisable builtin constructor *and* the flag is set?
    let do_pessimise_builtin = can_pessimise && tco_pessimise_builtins(&env::get_tcopt(env));
    // Under Sound Dynamic, for pessimisable builtins we add a like to the expected type
    // that is used to check the element expressions.
    //
    // For non-pessimised builtins we also do this if the type is explicit
    // but if an element actually has a like type then this must be reflected
    // in the inferred type argument.
    // e.g. contrast Vector<int>{ $li }  which has type Vector<int>
    //      and      Pair<int,string> { $li, "A" } which has type Pair<~int,string>
    let non_pessimised_builtin_explicit =
        tco_pessimise_builtins(&env::get_tcopt(env)) && explicit && !do_pessimise_builtin;
    // The supertype is the type argument of the result.
    // If there is an expected type then it's just this, but we might have to
    // add a like to it if it's the explicit type argument and we have a non-pessimised builtin.
    // Otherwise, we generate a fresh type variable and generate constraints against it.
    let (expected_with_implicit_like, supertype) = match expected {
        Some(expected_ty::T {
            pos,
            ty: ety,
            reason,
            ..
        }) => {
            // We add an implicit like type to the expected type of elements if
            //   There is an explicit type argument on the collection constructor, or
            //   This is a pessimised builtin (e.g. Vector), or
            //   There is a runtime-enforced bound (because it does no harm to allow dynamic)
            let like_ty = if explicit || do_pessimise_builtin || bound.is_some() {
                crate::typing_array_access::pessimise_type(env, ety.clone())
            } else {
                ety.clone()
            };
            let expected_with_implicit_like = Some(expected_ty::make(
                None,
                None,
                pos.clone(),
                reason.clone(),
                like_ty,
            ));
            let supertype = if explicit {
                ety.clone()
            } else {
                let ety = crate::typing_dynamic_utils::recompose_like_type(env, ety.clone());
                // Extract the underlying type from the expected type.
                // If it's an intersection, pick up the type under the like
                // e.g. For ~int & arraykey we want to pick up int
                // Otherwise, just strip the like.
                match get_node(&ety) {
                    Ty_::Tintersection(tyl) => {
                        let mut had_dynamic = false;
                        let mut stripped_tyl = vec![];
                        for ty in tyl {
                            match crate::typing_dynamic_utils::try_strip_dynamic(None, None, env, ty)
                            {
                                None => stripped_tyl.push(ty.clone()),
                                Some(ty) => {
                                    had_dynamic = true;
                                    stripped_tyl.push(ty)
                                }
                            }
                        }
                        if had_dynamic {
                            // Put the intersection back together without the dynamic
                            inter::simplify_intersections(
                                env,
                                None,
                                mk((get_reason(&ety).clone(), Ty_::Tintersection(stripped_tyl))),
                            )
                        } else {
                            ety.clone()
                        }
                    }
                    _ => crate::typing_dynamic_utils::strip_dynamic(env, ety.clone()),
                }
            };
            (expected_with_implicit_like, supertype)
        }
        None => {
            let ty = env::fresh_type_reason(None, env, use_pos.clone(), r);
            let ty_err_opt = if do_pessimise_builtin {
                sub_type::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    ty.clone(),
                    make_type::supportdyn_mixed(get_reason(&ty).clone()),
                    Some(reasons_callback::unify_error_at(p.clone())),
                )
            } else {
                None
            };
            add_typing_error_opt(env, &ty_err_opt);
            (None, ty)
        }
    };
    // Actually type the elements, given the expected element type
    let mut exprs_ = vec![];
    let mut tys = vec![];
    for x in exprs {
        let (te, ty) = expr_infer(expected_with_implicit_like.as_ref(), env, x);
        exprs_.push(te);
        tys.push(ty);
    }
    let coerce_for_op = bound.is_some() && !tco_pessimise_builtins(&env::get_tcopt(env));
    // Take the inferred type ty of each value and assert that it's a subtype
    // of the (optionally with like type added) result type argument.
    let subtype_value = |env: &mut Env, ty: &Ty| -> (Option<typing_error::T>, bool) {
        let (ty_err_opt, used_dynamic) = if non_pessimised_builtin_explicit {
            // We have an explicit type argument for a non-pessimised builtin.
            // We try first to check the value type against the non-pessimised type argument.
            // If that fails, we try it against a pessimised type argument.
            match &expected_with_implicit_like {
                Some(expected_ty::T {
                    pos,
                    reason,
                    ty: ety_like,
                    is_dynamic_aware,
                    ..
                }) => coerce_nonlike_and_like(
                    coerce_for_op,
                    *is_dynamic_aware,
                    env,
                    pos,
                    reason,
                    ty,
                    &supertype,
                    ety_like,
                ),
                // Shouldn't happen
                _ => (None, false),
            }
        } else {
            let (ety, et_enforced) = if coerce_for_op {
                (supertype.clone(), Enforcement::Enforced)
            } else {
                match &expected_with_implicit_like {
                    None => {
                        let supertype = if can_pessimise {
                            crate::typing_array_access::maybe_pessimise_type(env, supertype.clone())
                        } else {
                            supertype.clone()
                        };
                        (supertype, Enforcement::Unenforced)
                    }
                    Some(e) => (e.ty.clone(), Enforcement::Enforced), // TODO akenn: flow in
                }
            };
            let ty_err_opt = crate::typing_coercion::coerce_type(
                Some(coerce_for_op),
                Some(false),
                None,
                use_pos.clone(),
                reason.clone(),
                env,
                ty.clone(),
                ety,
                et_enforced,
                callback::unify_error(),
            );
            (ty_err_opt, false)
        };
        add_typing_error_opt(env, &ty_err_opt);
        (ty_err_opt, used_dynamic)
    };
    // `List.fold_left` consing onto `rev_ty_err_opts`, reversed below: the
    // vector is built in order.
    let mut ty_err_opts: Vec<Option<(Ty, Ty)>> = vec![];
    let mut used_dynamic = false;
    for ty in &tys {
        let (ty_err_opt, u) = subtype_value(env, ty);
        match ty_err_opt {
            None => ty_err_opts.push(None),
            Some(_) => ty_err_opts.push(Some((ty.clone(), supertype.clone()))),
        }
        used_dynamic = u || used_dynamic;
    }
    // used_dynamic is set if we had an explicit type argument t that is not
    // a like type, but one of the inferred element types is of the form ~u.
    // In this case we infer ~t as the element type for the whole collection.
    let result_type = if used_dynamic {
        crate::typing_array_access::pessimise_type(env, supertype.clone())
    } else {
        supertype.clone()
    };
    let result_type = match &bound {
        Some(ty) => inter::intersect(env, get_reason(ty).clone(), ty.clone(), result_type),
        None => result_type,
    };
    // `List.map2_exn`: both lists have an element per value.
    let exprs = exprs_
        .into_iter()
        .zip(ty_err_opts)
        .map(|(te, ty_mismatch_opt)| match &te {
            aast::Expr(_, _, aast::Expr_::Hole(_)) => te,
            _ => hole_on_ty_mismatch(te, ty_mismatch_opt),
        })
        .collect();
    (exprs, result_type)
}

/// The `check_collection_tparams` of `expr_`, which captures the position `p`
/// of the expression (first argument here).
pub fn check_collection_tparams(p: &Pos, env: &mut Env, name: &str, tys: &[Ty]) {
    // varrays and darrays are not classes but they share the same
    // constraints with vec and dict respectively
    let name = if name == sn::typehints::VARRAY {
        sn::collections::VEC
    } else if name == sn::typehints::DARRAY {
        sn::collections::DICT
    } else {
        name
    };
    // Class retrieval always succeeds because we're fetching a
    // collection decl from an HHI file.
    match env::get_class(env, name) {
        decl_entry::T::Found(class_) => {
            let ety_env = ExpandEnv {
                substs: tutils::make_locl_subst_for_class_tparams(&class_, tys),
                ..empty_expand_env_with_on_error(
                    env::invalid_type_hint_assert_primary_pos_in_current_decl(env),
                )
            };
            let ty_err_opt =
                phase::check_tparams_constraints(p.clone(), &ety_env, env, &cls::tparams(&class_));
            add_typing_error_opt(env, &ty_err_opt);
        }
        decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
            let desc = "Missing collection decl during type parameter check";
            let telemetry = telemetry::string_(None, "class name", name, telemetry::create());
            diagnostics_state::invariant_violation(p.clone(), telemetry, desc, false);
            // Continue typechecking without performing the check on a best effort
            // basis.
        }
    }
}

/// `Context.{ default with attribute_check_policy = ctxt.attribute_check_policy;
/// accept_using_var; check_defined = ctxt.check_defined }`, which most arms of
/// `expr_` give their subexpressions.
fn sub_ctxt(ctxt: &context::T, accept_using_var: bool) -> context::T {
    context::T {
        attribute_check_policy: ctxt.attribute_check_policy,
        accept_using_var,
        check_defined: ctxt.check_defined,
        ..context::default()
    }
}

pub fn expr_(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    outer: &nast::Expr,
) -> (tast::Expr, Ty) {
    let aast::Expr(_, p, e) = outer;
    env::open_tyvars(env, p.clone());
    let (te, ty) = {
        // `infer_element_type_for_collection` and `check_collection_tparams`
        // are the functions of the same names above.
        for err in crate::typing_type_wellformedness::expr(env, outer) {
            typing_error_utils::add_typing_error(&err, env)
        }
        match e {
            aast::Expr_::Import(_) | aast::Expr_::Collection(_) => {
                panic!("AST should not contain these nodes")
            }
            aast::Expr_::Hole(h) => {
                let (e, _, _, _) = &**h;
                expr_(
                    expected,
                    &context::T {
                        attribute_check_policy: AttributeCheckPolicy::CheckAll,
                        ..ctxt.clone()
                    },
                    env,
                    e,
                )
            }
            aast::Expr_::Invalid(expr_opt) => {
                let ty = make_type::nothing(reason::invalid());
                // `Aast.map_expr (fun _ -> ty) (fun _ -> Tast.dummy_saved_env)`
                let expr_opt = (**expr_opt).as_ref().map(|e| {
                    let mut on_ex = |_: &()| ty.clone();
                    let mut on_en = |_: &()| tast::dummy_saved_env();
                    aast_map::Map {
                        on_ex: &mut on_ex,
                        on_en: &mut on_en,
                    }
                    .on_expr(e)
                });
                let expr_ = aast::Expr_::Invalid(Box::new(expr_opt));
                make_result(env, p.clone(), expr_, ty)
            }
            aast::Expr_::Omitted => {
                // If an expression is omitted in an lvalue position, currently only
                // possible in a list destructuring construct such as `list(,$x) = $y;`,
                // we want to assign anything *to* the index of the omitted expression,
                // so give it type `mixed`. If an expression is omitted in an rvalue position,
                // currently only constant declarations (e.g. in hhi files), then we want
                // to be to assign *from* the expression, so give it type `nothing`.
                let ty = match ctxt.valkind {
                    valkind::T::Lvalue | valkind::T::LvalueSubexpr => {
                        make_type::mixed(reason::witness(p.clone()))
                    }
                    valkind::T::Other => make_type::nothing(reason::witness(p.clone())),
                };
                make_result(env, p.clone(), aast::Expr_::Omitted, ty)
            }
            aast::Expr_::ValCollection(vc) => expr_val_collection(expected, env, p, vc),
            aast::Expr_::KeyValCollection(kvc) => expr_key_val_collection(expected, env, p, kvc),
            aast::Expr_::Clone(e) => expr_clone(ctxt, env, p, e),
            aast::Expr_::This => expr_this(ctxt, env, p),
            aast::Expr_::True => make_result(
                env,
                p.clone(),
                aast::Expr_::True,
                make_type::bool(reason::witness(p.clone())),
            ),
            aast::Expr_::False => make_result(
                env,
                p.clone(),
                aast::Expr_::False,
                make_type::bool(reason::witness(p.clone())),
            ),
            // TODO TAST: consider checking that the integer is in range. Right now
            // it's possible for HHVM to fail on well-typed Hack code
            aast::Expr_::Int(s) => make_result(
                env,
                p.clone(),
                aast::Expr_::Int(s.clone()),
                make_type::int(reason::witness(p.clone())),
            ),
            aast::Expr_::Float(s) => make_result(
                env,
                p.clone(),
                aast::Expr_::Float(s.clone()),
                make_type::float(reason::witness(p.clone())),
            ),
            // TODO TAST: consider introducing a "null" type, and defining ?t to
            // be null | t
            aast::Expr_::Null => make_result(
                env,
                p.clone(),
                aast::Expr_::Null,
                make_type::null(reason::witness(p.clone())),
            ),
            aast::Expr_::String(s) => expr_string(expected, env, p, s),
            aast::Expr_::String2(idl) => {
                let tel = super::string2(env, idl);
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::String2(tel),
                    make_type::string(reason::witness(p.clone())),
                )
            }
            aast::Expr_::PrefixedString(ps) => expr_prefixed_string(ctxt, env, p, outer, ps),
            aast::Expr_::Id(id) => expr_id(env, p, id),
            aast::Expr_::MethodCaller(mc) => {
                // `(class_name, method_name)`
                method_caller::synth_function_ref_type(p, &**mc, env)
            }
            aast::Expr_::FunctionPointer(fp) => {
                // `(fp_id, targs, source)`
                function_pointer::synth(p, &**fp, env)
            }
            aast::Expr_::Lplaceholder(p) => {
                let r = reason::placeholder((**p).clone());
                let ty = make_type::void(r);
                make_result(env, (**p).clone(), aast::Expr_::Lplaceholder(p.clone()), ty)
            }
            aast::Expr_::Dollardollar(id) => {
                let ty = env::get_local_check_defined(env, id);
                might_throw(p, env);
                make_result(env, p.clone(), aast::Expr_::Dollardollar(id.clone()), ty.ty)
            }
            aast::Expr_::Lvar(id) => {
                let aast::Lid(_, x) = &**id;
                if !ctxt.accept_using_var {
                    check_escaping_var(env, id)
                }
                let Local { ty, .. } = if ctxt.check_defined {
                    env::get_local_check_defined(env, id)
                } else {
                    env::get_local(env, x)
                };
                let ty = env::update_reason(env, ty, |def| {
                    reason::flow_local(def, reason::witness(p.clone()))
                });
                make_result(env, p.clone(), aast::Expr_::Lvar(id.clone()), ty)
            }
            aast::Expr_::Tuple(el) => expr_tuple(expected, ctxt, env, p, el),
            aast::Expr_::List(el) => expr_list(expected, ctxt, env, p, el),
            aast::Expr_::Pair(pair) => expr_pair(expected, env, p, pair),
            aast::Expr_::ArrayGet(ag) if ag.1.is_none() => {
                let (e, _) = &**ag;
                let (te, _) = super::update_array_type(false, p, env, e, ctxt.valkind);
                might_throw(p, env);
                // NAST check reports an error if [] is used for reading in an
                // lvalue context.
                let ty = env::fresh_type_error(env, p.clone());
                make_result(env, p.clone(), aast::Expr_::ArrayGet(Box::new((te, None))), ty)
            }
            aast::Expr_::ArrayGet(ag) => {
                let (e1, e2) = &**ag;
                let e2 = e2.as_ref().expect("Array_get (e1, Some e2)");
                expr_array_get(ctxt, env, p, e1, e2)
            }
            aast::Expr_::Call(call)
                if matches!(
                    &**call,
                    aast::CallExpr {
                        func: aast::Expr(_, _, aast::Expr_::Id(id)),
                        unpacked_arg: None,
                        ..
                    } if typing_env_pseudofunctions.contains(id.1.as_str())
                ) =>
            {
                expr_call_pseudo_function(expected, ctxt, env, p, call)
            }
            aast::Expr_::Call(call) => {
                let aast::CallExpr {
                    func,
                    targs,
                    args,
                    unpacked_arg,
                } = &**call;
                might_throw(p, env);
                let ((te, ty), should_forget_fakes) = super::dispatch_call(
                    None,
                    expected,
                    ctxt,
                    p,
                    env,
                    func,
                    targs,
                    args,
                    unpacked_arg.as_ref(),
                );
                if should_forget_fakes {
                    env::forget_members(env, Blame::Blame(p.clone(), BlameSource::BScall))
                }
                (te, ty)
            }
            aast::Expr_::Binop(bo) => {
                let aast::Binop {
                    bop,
                    lhs: e1,
                    rhs: e2,
                } = &**bo;
                binop::check_binop(ctxt.check_defined, expected, env, p, *bop, e1, Either::Left(e2))
            }
            aast::Expr_::Assign(assign)
                if matches!(
                    &**assign,
                    (
                        aast::Expr(_, _, aast::Expr_::Lvar(_)),
                        None,
                        aast::Expr(_, _, aast::Expr_::ETSplice(splice)),
                    ) if !splice.extract_client_type && splice.macro_variables.is_some()
                ) =>
            {
                expr_assign_et_splice(expected, ctxt, env, p, outer, assign)
            }
            aast::Expr_::Assign(assign) => {
                let (e1, bop, e2) = &**assign;
                binop::check_assign(
                    ctxt.check_defined,
                    expected,
                    env,
                    outer,
                    p,
                    *bop,
                    e1,
                    Either::Left(e2),
                )
            }
            aast::Expr_::Pipe(pipe) => expr_pipe(ctxt, env, p, pipe),
            aast::Expr_::Unop(unop) => expr_unop(ctxt, env, p, unop),
            aast::Expr_::Eif(eif_) => {
                let (c, e1, e2) = &**eif_;
                eif(env, expected, ctxt.in_await.clone(), p, c, e1.as_ref(), e2)
            }
            aast::Expr_::ClassConst(cc)
                if matches!(
                    &**cc,
                    (aast::ClassId(_, _, aast::ClassId_::CI(sid)), (_, pstr))
                        if pstr == "class" && env::is_typedef(env, &sid.1)
                ) =>
            {
                let (aast::ClassId(_, pcid, cid_), pstr) = &**cc;
                let sid = match cid_ {
                    aast::ClassId_::CI(sid) => sid,
                    _ => unreachable!(),
                };
                typename_expr(env, pcid, sid, outer, |env, ty| {
                    let ty = map_reason(ty, |def| {
                        let use_ = reason::class_const_access(p.clone());
                        reason::flow_const_access(def, use_)
                    });
                    make_result(
                        env,
                        p.clone(),
                        aast::Expr_::ClassConst(Box::new((
                            aast::ClassId(ty.clone(), pcid.clone(), aast::ClassId_::CI(sid.clone())),
                            pstr.clone(),
                        ))),
                        ty,
                    )
                })
            }
            aast::Expr_::ClassConst(cc) => {
                let (cid, mid) = &**cc;
                super::class_const(
                    false,
                    Some(ctxt.attribute_check_policy),
                    None,
                    Some(class_id::ClassnameExprError::Error),
                    env,
                    p,
                    (cid, mid),
                )
            }
            aast::Expr_::ClassGet(cg)
                if cg.2 == aast::PropOrMethod::IsProp
                    && env::fake_members::is_valid_static(env, &cg.0.2, &cg.1.1) =>
            {
                expr_class_get_fake_member(ctxt, env, p, cg)
            }
            // Statically-known static property access e.g. Foo::$x
            aast::Expr_::ClassGet(cg) => expr_class_get(env, p, cg),
            // Fake member property access. For example:
            //   if ($x->f !== null) { ...$x->f... }
            aast::Expr_::ObjGet(og)
                if matches!(
                    &**og,
                    (e, aast::Expr(_, _, aast::Expr_::Id(id)), _, _)
                        if env::fake_members::is_valid(env, e, &id.1)
                ) =>
            {
                expr_obj_get_fake_member(ctxt, env, p, og)
            }
            // Statically-known instance property access e.g. $x->f
            aast::Expr_::ObjGet(og) if matches!(&og.1, aast::Expr(_, _, aast::Expr_::Id(_))) => {
                expr_obj_get_static(ctxt, env, p, og)
            }
            // Dynamic instance property access e.g. $x->$f
            aast::Expr_::ObjGet(og) => expr_obj_get_dynamic(ctxt, env, p, og),
            aast::Expr_::Yield(af) => expr_yield(env, p, af),
            aast::Expr_::Await(e) => expr_await(ctxt, env, p, e),
            aast::Expr_::Delay(e) => {
                let (te, rty) = expr(None, &sub_ctxt(ctxt, false), env, e);
                let r = reason::witness(p.clone());
                let mixed = make_type::mixed(r.clone());
                let expected_type = make_type::awaitable(r, mixed);
                let ty_err_opt = crate::typing_ops::sub_type(
                    p.clone(),
                    Ureason::URdelay,
                    env,
                    rty.clone(),
                    expected_type,
                    callback::unify_error(),
                );
                add_typing_error_opt(env, &ty_err_opt);
                make_result(env, p.clone(), aast::Expr_::Delay(Box::new(te)), rty)
            }
            aast::Expr_::ReadonlyExpr(e) => {
                env::set_readonly(env, true);
                let (te, rty) = expr(
                    None,
                    &context::T {
                        attribute_check_policy: ctxt.attribute_check_policy,
                        is_using_clause: ctxt.is_using_clause,
                        accept_using_var: false,
                        check_defined: ctxt.check_defined,
                        support_readonly_return: true,
                        ..context::default()
                    },
                    env,
                    e,
                );
                make_result(env, p.clone(), aast::Expr_::ReadonlyExpr(Box::new(te)), rty)
            }
            aast::Expr_::New(new) => expr_new(expected, ctxt, env, p, new),
            aast::Expr_::Cast(cast) => expr_cast(ctxt, env, p, cast),
            aast::Expr_::ExpressionTree(et) => expression_tree::expression_tree(env, p, et),
            aast::Expr_::Is(is) => {
                let (e, hint) = &**is;
                let (te, _) = expr(None, &sub_ctxt(ctxt, false), env, e);
                let (ty_err_opt, _hint_ty) = phase::localize_hint_for_refinement(env, hint);
                add_typing_error_opt(env, &ty_err_opt);
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::Is(Box::new((te, hint.clone()))),
                    make_type::bool(reason::witness(p.clone())),
                )
            }
            aast::Expr_::As(as_) => expr_as(ctxt, env, p, as_),
            aast::Expr_::Upcast(upcast) => {
                let (e, hint) = &**upcast;
                let (te, expr_ty) = expr(None, &sub_ctxt(ctxt, false), env, e);
                let (ty_err_opt, hint_ty) = phase::localize_hint_no_subst(env, false, hint);
                add_typing_error_opt(env, &ty_err_opt);
                super::upcast(env, p, expr_ty, hint_ty.clone());
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::Upcast(Box::new((te, hint.clone()))),
                    hint_ty,
                )
            }
            aast::Expr_::Efun(efun) => {
                let aast::Efun {
                    fun: f,
                    use_: idl,
                    closure_class_name,
                    is_expr_tree_virtual_expr,
                } = &**efun;
                lambda::lambda(
                    !ctxt.immediately_called_lambda,
                    true,
                    closure_class_name.clone(),
                    *is_expr_tree_virtual_expr,
                    expected,
                    p,
                    env,
                    f,
                    idl,
                )
            }
            aast::Expr_::Lfun(lfun) => {
                let (f, idl) = &**lfun;
                lambda::lambda(
                    !ctxt.immediately_called_lambda,
                    false,
                    None,
                    false,
                    expected,
                    p,
                    env,
                    f,
                    idl,
                )
            }
            aast::Expr_::Xml(xml) => expr_xml(expected, ctxt, env, p, xml),
            aast::Expr_::Shape(fdm) => expr_shape(expected, ctxt, env, p, fdm),
            aast::Expr_::ETSplice(splice) => {
                let (te, ty, _) = super::check_et_splice(env, p, splice);
                (te, ty)
            }
            aast::Expr_::EnumClassLabel(ecl) if ecl.0.is_none() => {
                let (_, name) = &**ecl;
                let label_ty = mk((reason::witness(p.clone()), Ty_::Tlabel(name.clone())));
                check_expected_ty("Label", env, &label_ty, expected);
                let ty = match expected {
                    // If there is an expected type, use that as the type recorded in the
                    // TAST
                    None => label_ty,
                    Some(expected_ty::T { ty, .. }) => {
                        // `mk (Reason.witness p, get_node ty)`
                        with_reason(ty.clone(), reason::witness(p.clone()))
                    }
                };
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::EnumClassLabel(Box::new((None, name.clone()))),
                    ty,
                )
            }
            aast::Expr_::EnumClassLabel(ecl) => expr_enum_class_label(env, p, ecl),
            aast::Expr_::Package(id) => {
                let ast_defs::Id(p, _) = &**id;
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::Package(id.clone()),
                    make_type::bool(reason::witness(p.clone())),
                )
            }
            aast::Expr_::Nameof(cid)
                if matches!(
                    &**cid,
                    aast::ClassId(_, _, aast::ClassId_::CI(sid)) if env::is_typedef(env, &sid.1)
                ) =>
            {
                let aast::ClassId(_, pcid, cid_) = &**cid;
                let sid = match cid_ {
                    aast::ClassId_::CI(sid) => sid,
                    _ => unreachable!(),
                };
                typename_expr(env, pcid, sid, outer, |env, ty| {
                    make_result(
                        env,
                        p.clone(),
                        aast::Expr_::Nameof(Box::new(aast::ClassId(
                            ty.clone(),
                            pcid.clone(),
                            aast::ClassId_::CI(sid.clone()),
                        ))),
                        ty,
                    )
                })
            }
            aast::Expr_::Nameof(cid) => {
                let (_tal, ce, cty) = class_id::class_expr(
                    None,
                    None,
                    Some(Exact::Exact), // emulate C::class
                    None,
                    Some(true),
                    None,
                    None,
                    None,
                    None,
                    None,
                    env,
                    &[],
                    cid,
                );
                make_result(
                    env,
                    p.clone(),
                    aast::Expr_::Nameof(Box::new(ce)),
                    make_type::classname(reason::witness(p.clone()), vec![cty]),
                )
            }
            aast::Expr_::DestructureShape(_) | aast::Expr_::DestructureTuple(_) => {
                // Unreachable: the lowerer only produces DestructureShape/DestructureTuple
                // in LvaluePosition (LHS of assignment, foreach value). See ExprLocation
                // in lowerer.rs.
                hack_event_logger::invariant_violation_bug(
                    None,
                    Some(&show_absolute_pos(p)),
                    None,
                    None,
                    None,
                    "DestructureShape/DestructureTuple reached rvalue typing",
                );
                let ty = env::fresh_type_error(env, p.clone());
                make_result(env, p.clone(), aast::Expr_::Omitted, ty)
            }
        }
    };
    let ty_err_opt = crate::typing_solver::close_tyvars_and_solve(env);
    add_typing_error_opt(env, &ty_err_opt);
    (te, ty)
}

// ---------------------------------------------------------------------------
// The large arms of `expr_`
// ---------------------------------------------------------------------------

/// The `expr_infer` argument of [`infer_element_type_for_collection`], when
/// the arms of a match choose it.
type SubtypeVal<'a> =
    Box<dyn Fn(Option<&expected_ty::T>, &mut Env, &nast::Expr) -> (tast::Expr, Ty) + 'a>;

/// `ValCollection ((kind_pos, kind), th, el)`
#[inline(never)]
fn expr_val_collection(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    p: &Pos,
    vc: &((Pos, aast::VcKind), Option<nast::Targ>, Vec<nast::Expr>),
) -> (tast::Expr, Ty) {
    let ((kind_pos, kind), th, el) = vc;
    let kind = *kind;
    // `get_expected_kind` is `get_vc_inst env p kind`, applied to the
    // environment of this point; `name`, `make_expr` and `make_ty` are used
    // directly below.
    let class_name = crate::nast::vc_kind_to_name(&kind);
    // `arraykey_value p class_name true` and `array_value`, partially applied.
    let arraykey_value_set: SubtypeVal<'_> = {
        let class_name = class_name.clone();
        Box::new(
            move |expected: Option<&expected_ty::T>, env: &mut Env, x: &nast::Expr| {
                super::arraykey_value(p, &class_name, true, expected, env, x)
            },
        )
    };
    let array_value: SubtypeVal<'_> = Box::new(
        |expected: Option<&expected_ty::T>, env: &mut Env, x: &nast::Expr| {
            super::array_value(expected, env, x)
        },
    );
    let (subtype_val, key_bound, pessimisable_builtin): (SubtypeVal<'_>, Option<Ty>, bool) =
        match kind {
            aast::VcKind::Set | aast::VcKind::ImmSet => (
                arraykey_value_set,
                Some(make_type::arraykey(reason::witness(p.clone()))),
                true,
            ),
            aast::VcKind::Keyset => (
                arraykey_value_set,
                Some(make_type::arraykey(reason::witness(p.clone()))),
                false,
            ),
            aast::VcKind::Vector | aast::VcKind::ImmVector => (array_value, None, true),
            aast::VcKind::Vec => (array_value, None, false),
        };
    // Use expected type to determine expected element type
    let (elem_expected, th) = match th {
        Some(aast::Targ(_, tv)) => {
            let (ty_err_opt, tv, tv_expected) = localize_targ(env, tv);
            add_typing_error_opt(env, &ty_err_opt);
            check_collection_tparams(p, env, &class_name, &[tv.0.clone()]);
            (Some(tv_expected), Some(tv))
        }
        None => {
            // The environment `get_expected_kind` was applied to, which is
            // also the one the OCaml goes on with when there is no expected
            // type (`| _ -> (env, None, None)`).
            let env0 = env.clone();
            match env_help::expand_expected_opt(false, pessimisable_builtin, env, expected) {
                Some((pos, ur, _, ety, _, _)) => {
                    let mut env_k = env0;
                    match get_vc_inst(&mut env_k, p, kind, &ety) {
                        Some(vty) => {
                            *env = env_k;
                            (Some(expected_ty::make(None, None, pos, ur, vty)), None)
                        }
                        None => (None, None),
                    }
                }
                None => {
                    *env = env0;
                    (None, None)
                }
            }
        }
    };
    let el: Vec<&nast::Expr> = el.iter().collect();
    let r = {
        let p = p.clone();
        let n = strip_ns(&class_name).to_string();
        move |v| reason::type_variable_generics((p, "T".to_string(), n), v)
    };
    let (tel, elem_ty) = infer_element_type_for_collection(
        p,
        elem_expected.as_ref(),
        th.is_some(),
        Ureason::URvector,
        pessimisable_builtin,
        key_bound,
        p,
        r,
        env,
        &el,
        subtype_val,
    );
    // `make_ty elem_ty`
    let ty = make_type::class_type(reason::witness(p.clone()), class_name, vec![elem_ty]);
    // `make_expr th tel`
    let te = aast::Expr_::ValCollection(Box::new(((kind_pos.clone(), kind), th, tel)));
    make_result(env, p.clone(), te, ty)
}

/// `KeyValCollection ((kind_pos, kind), th, l)`
#[inline(never)]
fn expr_key_val_collection(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    p: &Pos,
    kvc: &(
        (Pos, aast::KvcKind),
        Option<(nast::Targ, nast::Targ)>,
        Vec<nast::Field>,
    ),
) -> (tast::Expr, Ty) {
    let ((kind_pos, kind), th, l) = kvc;
    let kind = *kind;
    // `get_expected_kind` is `get_kvc_inst env p kind`, applied to the
    // environment of this point; `name`, `make_expr` and `make_ty` are used
    // directly below.
    let class_name = crate::nast::kvc_kind_to_name(&kind);
    let pessimisable_builtin = match kind {
        aast::KvcKind::Dict => false,
        _ => true,
    };
    // Use expected type to determine expected key and value types
    let (kexpected, vexpected, th) = match th {
        Some((aast::Targ(_, tk), aast::Targ(_, tv))) => {
            let (ty_err_opt1, tk, tk_expected) = localize_targ(env, tk);
            add_typing_error_opt(env, &ty_err_opt1);
            let (ty_err_opt2, tv, tv_expected) = localize_targ(env, tv);
            add_typing_error_opt(env, &ty_err_opt2);
            check_collection_tparams(p, env, &class_name, &[tk.0.clone(), tv.0.clone()]);
            (Some(tk_expected), Some(tv_expected), Some((tk, tv)))
        }
        None => {
            // no explicit typehint, fallback to supplied expect
            //
            // The environment `get_expected_kind` was applied to, which is
            // also the one the OCaml goes on with in its last case
            // (`| _ -> (env, None, None, None)`).
            let env0 = env.clone();
            match env_help::expand_expected_opt(false, pessimisable_builtin, env, expected) {
                Some((pos, reason, _, ety, _, _)) if !l.is_empty() => {
                    let mut env_k = env0;
                    match get_kvc_inst(&mut env_k, p, kind, &ety) {
                        Some((kty, vty)) => {
                            *env = env_k;
                            let k_expected =
                                expected_ty::make(None, None, pos.clone(), reason.clone(), kty);
                            let v_expected = expected_ty::make(None, None, pos, reason, vty);
                            (Some(k_expected), Some(v_expected), None)
                        }
                        None => (None, None, None),
                    }
                }
                _ => {
                    *env = env0;
                    (None, None, None)
                }
            }
        }
    };
    let (kl, vl): (Vec<&nast::Expr>, Vec<&nast::Expr>) =
        l.iter().map(|aast::Field(k, v)| (k, v)).unzip();
    let r = {
        let p = p.clone();
        let n = strip_ns(&class_name).to_string();
        move |v| reason::type_variable_generics((p, "Tk".to_string(), n), v)
    };
    let (tkl, k) = infer_element_type_for_collection(
        p,
        kexpected.as_ref(),
        th.is_some(),
        Ureason::URkey(class_name.clone()),
        pessimisable_builtin,
        Some(make_type::arraykey(reason::witness(p.clone()))),
        p,
        r,
        env,
        &kl,
        |expected, env, x| super::arraykey_value(p, &class_name, false, expected, env, x),
    );
    let r = {
        let p = p.clone();
        let n = strip_ns(&class_name).to_string();
        move |v| reason::type_variable_generics((p, "Tv".to_string(), n), v)
    };
    let (tvl, v) = infer_element_type_for_collection(
        p,
        vexpected.as_ref(),
        th.is_some(),
        Ureason::URvalue(class_name.clone()),
        pessimisable_builtin,
        None,
        p,
        r,
        env,
        &vl,
        |expected, env, x| super::array_value(expected, env, x),
    );
    // `List.zip_exn tkl tvl`: both lists have an element per pair.
    let pairs: Vec<aast::Field<Ty, tast::SavedEnv>> = tkl
        .into_iter()
        .zip(tvl)
        .map(|(tk, tv)| aast::Field(tk, tv))
        .collect();
    // `make_ty k v`
    let ty = make_type::class_type(reason::witness(p.clone()), class_name, vec![k, v]);
    // `make_expr th pairs`
    let te = aast::Expr_::KeyValCollection(Box::new(((kind_pos.clone(), kind), th, pairs)));
    make_result(env, p.clone(), te, ty)
}

/// `Clone e`
#[inline(never)]
fn expr_clone(ctxt: &context::T, env: &mut Env, p: &Pos, e: &nast::Expr) -> (tast::Expr, Ty) {
    let (te, ty) = expr(None, &sub_ctxt(ctxt, false), env, e);
    // Clone only works on objects; anything else fatals at runtime.
    // Constructing a call `e`->__clone() checks that `e` is an object and
    // checks coeffects on __clone
    let aast::Expr(_, pe, _) = e;
    let (ty_err_opt, (tfty, _tal)) = tog::obj_get(
        pe.clone(),
        true,
        None,
        None,
        &[],
        &aast::ClassId_::CIexpr(e.clone()),
        &ast_defs::Id(p.clone(), sn::members::__CLONE.to_string()),
        callback::unify_error(),
        None,
        env,
        ty.clone(),
    );
    add_typing_error_opt(env, &ty_err_opt);
    let (_tel, _typed_unpack_element, _ty, _should_forget_fakes) =
        super::call(None, None, None, None, None, p, p, p, env, tfty, &[], None);
    make_result(env, p.clone(), aast::Expr_::Clone(Box::new(te)), ty)
}

/// `This`
#[inline(never)]
fn expr_this(ctxt: &context::T, env: &mut Env, p: &Pos) -> (tast::Expr, Ty) {
    if env::get_self_ty(env).is_none() {
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::This_var_outside_class(p.clone())),
            env,
        )
    }
    if env::is_in_expr_tree(env) {
        typing_error_utils::add_typing_error(
            &typing_error::expr_tree(primary::expr_tree::T::This_var_in_expr_tree(p.clone())),
            env,
        )
    }
    if !ctxt.accept_using_var {
        check_escaping_var(env, &aast::Lid(p.clone(), this()))
    }
    let ty = if ctxt.check_defined {
        env::get_local_check_defined(env, &aast::Lid(p.clone(), this()))
    } else {
        env::get_local(env, &this())
    };
    let r = reason::witness(p.clone());
    // $this isn't a typed local and so has no bound
    // `mk (r, get_node ty.Typing_local_types.ty)`
    let ty = with_reason(ty.ty, r);
    make_result(env, p.clone(), aast::Expr_::This, ty)
}

/// `String s`
#[inline(never)]
fn expr_string(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    p: &Pos,
    s: &bstr::BString,
) -> (tast::Expr, Ty) {
    let expected = env_help::expand_expected_opt(false, false, env, expected);
    match &expected {
        Some((_pos, _ur, _, _, Ty_::Tnewtype(fs, tys, _), _))
            if tys.len() == 2 && is_typed_format_string(fs) =>
        {
            let ty = &tys[0];
            // `Typing_exts.parse_printf_string env s p ty`: the string is bytes.
            let fpl = crate::typing_exts::parse_printf_string(env, s.as_ref(), p.clone(), ty.clone());
            let tuple_ty = make_type::tuple(
                reason::witness(p.clone()),
                fpl.iter().map(|fp| fp.type_.clone()).collect(),
            );
            let string_ty = mk((
                reason::witness(p.clone()),
                Ty_::Tnewtype(
                    fs.clone(),
                    vec![ty.clone(), tuple_ty],
                    make_type::string(reason::witness(p.clone())),
                ),
            ));
            make_result(env, p.clone(), aast::Expr_::String(s.clone()), string_ty)
        }
        _ => make_result(
            env,
            p.clone(),
            aast::Expr_::String(s.clone()),
            make_type::string(reason::witness(p.clone())),
        ),
    }
}

/// `PrefixedString (n, e)`
#[inline(never)]
fn expr_prefixed_string(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    outer: &nast::Expr,
    ps: &(String, nast::Expr),
) -> (tast::Expr, Ty) {
    let (n, e) = ps;
    if n != "re" {
        diagnostics_state::experimental_feature(
            p.clone(),
            "String prefixes other than `re` are not yet supported.",
        );
        expr_error(env, p.clone(), outer)
    } else {
        let (te, ty) = expr(None, &sub_ctxt(ctxt, false), env, e);
        let aast::Expr(_, pe, expr_) = e;
        crate::typing_substring::sub_string(pe.clone(), env, ty);
        match expr_ {
            aast::Expr_::String(_) => {
                // `try ... with`: the exceptions of `Typing_regex.type_pattern`
                // (and `Pcre.Error (Pcre.BadPattern _)`) are the errors of its
                // `Result`.
                match crate::typing_regex::type_pattern(e) {
                    Ok(ty) => make_result(
                        env,
                        p.clone(),
                        aast::Expr_::PrefixedString(Box::new((n.clone(), te))),
                        ty,
                    ),
                    Err(crate::typing_regex::Error::BadPattern(s, i)) => {
                        let reason = primary::BadRegexPatternReason::bad_patt(format!(
                            "{}{}{}{}",
                            s, " [", i, "]"
                        ));
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Bad_regex_pattern {
                                pos: pe.clone(),
                                reason,
                            }),
                            env,
                        );
                        expr_error(env, pe.clone(), e)
                    }
                    Err(crate::typing_regex::Error::EmptyRegexPattern) => {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Bad_regex_pattern {
                                pos: pe.clone(),
                                reason: primary::BadRegexPatternReason::empty_patt,
                            }),
                            env,
                        );
                        expr_error(env, pe.clone(), e)
                    }
                    Err(crate::typing_regex::Error::MissingDelimiter) => {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Bad_regex_pattern {
                                pos: pe.clone(),
                                reason: primary::BadRegexPatternReason::missing_delim,
                            }),
                            env,
                        );
                        expr_error(env, pe.clone(), e)
                    }
                    Err(crate::typing_regex::Error::InvalidGlobalOption) => {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Bad_regex_pattern {
                                pos: pe.clone(),
                                reason: primary::BadRegexPatternReason::invalid_option,
                            }),
                            env,
                        );
                        expr_error(env, pe.clone(), e)
                    }
                }
            }
            aast::Expr_::String2(_) => {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Re_prefixed_non_string {
                        pos: pe.clone(),
                        reason: primary::RePrefixedNonStringReason::embedded_expr,
                    }),
                    env,
                );
                expr_error(env, pe.clone(), e)
            }
            _ => {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Re_prefixed_non_string {
                        pos: pe.clone(),
                        reason: primary::RePrefixedNonStringReason::non_string,
                    }),
                    env,
                );
                expr_error(env, pe.clone(), e)
            }
        }
    }
}

/// `Id ((cst_pos, cst_name) as id)`
#[inline(never)]
fn expr_id(env: &mut Env, p: &Pos, id: &aast::Sid) -> (tast::Expr, Ty) {
    let ast_defs::Id(cst_pos, cst_name) = id;
    match env::get_gconst(env, cst_name) {
        None => {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Unbound_global(cst_pos.clone())),
                env,
            );
            let ty = env::fresh_type_error(env, cst_pos.clone());
            make_result(env, cst_pos.clone(), aast::Expr_::Id(Box::new(id.clone())), ty)
        }
        Some(const_) => {
            match tvis::check_package_access(
                crate::typing_packages::CheckReason::Yes(
                    primary::package::TargetSymbolSpec::Global_const,
                ),
                cst_pos.clone(),
                const_.pos.clone().to_oxidized(),
                env,
                const_.package.as_ref(),
                cst_name.clone(),
            ) {
                tvis::PackageAccessResult::PackageAccessError(err) => {
                    typing_error_utils::add_typing_error(&err, env)
                }
                tvis::PackageAccessResult::PackageAccessLinterError((pos, w)) => {
                    let crate::typing_packages::PackageWarningInfo {
                        current_package,
                        current_package_before_override,
                        caller_has_package_override,
                        target_package,
                        target_package_before_override,
                        callee_has_package_override,
                        classptr_reference_warning,
                    } = w;
                    crate::lints_diagnostics::crosspackage_linter(
                        pos,
                        current_package.as_ref(),
                        current_package_before_override.as_deref(),
                        caller_has_package_override,
                        target_package.as_ref(),
                        target_package_before_override.as_deref(),
                        callee_has_package_override,
                        classptr_reference_warning,
                    )
                }
                tvis::PackageAccessResult::PackageAccessOk => {}
            }
            let (ty_err_opt, ty) = phase::localize_no_subst(env, true, &const_.ty);
            add_typing_error_opt(env, &ty_err_opt);
            make_result(env, p.clone(), aast::Expr_::Id(Box::new(id.clone())), ty)
        }
    }
}

/// `Tuple el`
#[inline(never)]
fn expr_tuple(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    el: &[nast::Expr],
) -> (tast::Expr, Ty) {
    let expected = env_help::expand_expected_opt(false, false, env, expected);
    let (tel, tyl) = match expected {
        // TODO: optional and variadic fields T201398626 T201398652
        Some((
            pos,
            ur,
            _,
            _,
            Ty_::Ttuple(TupleType {
                required: expected_tyl,
                ..
            }),
            _,
        )) => {
            let expected_tys: Vec<expected_ty::T> = expected_tyl
                .into_iter()
                .map(|ty| expected_ty::make(None, None, pos.clone(), ur.clone(), ty))
                .collect();
            check_exprs(el, ctxt, env, &expected_tys)
        }
        _ => infer_exprs(el, &sub_ctxt(ctxt, false), env),
    };
    let ty = make_type::tuple(reason::witness(p.clone()), tyl);
    make_result(env, p.clone(), aast::Expr_::Tuple(tel), ty)
}

/// `List el`
#[inline(never)]
fn expr_list(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    el: &[nast::Expr],
) -> (tast::Expr, Ty) {
    let (tel, tyl) = match ctxt.valkind {
        valkind::T::Lvalue | valkind::T::LvalueSubexpr => lvalues(env, el),
        valkind::T::Other => {
            let expected = env_help::expand_expected_opt(false, true, env, expected);
            match expected {
                Some((
                    pos,
                    ur,
                    _,
                    _,
                    Ty_::Ttuple(TupleType {
                        required: expected_tyl,
                        ..
                    }),
                    _,
                )) => {
                    let expected_tys: Vec<expected_ty::T> = expected_tyl
                        .into_iter()
                        .map(|ty| expected_ty::make(None, None, pos.clone(), ur.clone(), ty))
                        .collect();
                    check_exprs(el, ctxt, env, &expected_tys)
                }
                _ => infer_exprs(el, &sub_ctxt(ctxt, false), env),
            }
        }
    };
    let ty = make_type::tuple(reason::witness(p.clone()), tyl);
    make_result(env, p.clone(), aast::Expr_::List(tel), ty)
}

/// `Pair (th, e1, e2)`
#[inline(never)]
fn expr_pair(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    p: &Pos,
    pair: &(Option<(nast::Targ, nast::Targ)>, nast::Expr, nast::Expr),
) -> (tast::Expr, Ty) {
    let (th, e1, e2) = pair;
    let (expected1, expected2, th) = match th {
        Some((aast::Targ(_, t1), aast::Targ(_, t2))) => {
            let (ty_err_opt1, t1, t1_expected) = localize_targ(env, t1);
            add_typing_error_opt(env, &ty_err_opt1);
            let (ty_err_opt2, t2, t2_expected) = localize_targ(env, t2);
            add_typing_error_opt(env, &ty_err_opt2);
            (Some(t1_expected), Some(t2_expected), Some((t1, t2)))
        }
        None => {
            // Use expected type to determine expected element types
            //
            // The OCaml goes on with the environment from before the
            // expansion in its last case (`| _ -> (env, None, None, None)`).
            let env0 = env.clone();
            match env_help::expand_expected_opt(false, false, env, expected) {
                Some((pos, reason, _, _ty, Ty_::Tclass((_, k), _, tys), _))
                    if tys.len() == 2 && k == sn::collections::PAIR =>
                {
                    let (ty1, ty2) = (tys[0].clone(), tys[1].clone());
                    let ty1_expected = expected_ty::make(None, None, pos.clone(), reason.clone(), ty1);
                    let ty2_expected = expected_ty::make(None, None, pos, reason, ty2);
                    (Some(ty1_expected), Some(ty2_expected), None)
                }
                _ => {
                    *env = env0;
                    (None, None, None)
                }
            }
        }
    };
    let aast::Expr(_, p1, _) = e1;
    let aast::Expr(_, p2, _) = e2;
    let r1 = {
        let p1 = p1.clone();
        move |v| reason::type_variable_generics((p1, "T1".to_string(), "Pair".to_string()), v)
    };
    let (tel1, ty1) = infer_element_type_for_collection(
        p,
        expected1.as_ref(),
        th.is_some(),
        Ureason::URpairValue,
        false,
        None,
        p1,
        r1,
        env,
        &[e1],
        |expected, env, x| super::array_value(expected, env, x),
    );
    let r2 = {
        let p2 = p2.clone();
        move |v| reason::type_variable_generics((p2, "T2".to_string(), "Pair".to_string()), v)
    };
    let (tel2, ty2) = infer_element_type_for_collection(
        p,
        expected2.as_ref(),
        th.is_some(),
        Ureason::URpairValue,
        false,
        None,
        p2,
        r2,
        env,
        &[e2],
        |expected, env, x| super::array_value(expected, env, x),
    );
    let ty = make_type::pair(reason::witness(p.clone()), ty1, ty2);
    let te1 = tel1.into_iter().next().expect("List.hd_exn");
    let te2 = tel2.into_iter().next().expect("List.hd_exn");
    make_result(env, p.clone(), aast::Expr_::Pair(Box::new((th, te1, te2))), ty)
}

/// `Array_get (e1, Some e2)`
#[inline(never)]
fn expr_array_get(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    e1: &nast::Expr,
    e2: &nast::Expr,
) -> (tast::Expr, Ty) {
    let context::T {
        attribute_check_policy,
        lhs_of_null_coalesce,
        valkind,
        ..
    } = ctxt;
    let (te1, ty1) = super::update_array_type(*lhs_of_null_coalesce, p, env, e1, *valkind);
    let (te2, ty2) = expr(
        None,
        &context::T {
            attribute_check_policy: *attribute_check_policy,
            accept_using_var: false,
            check_defined: ctxt.check_defined,
            ..context::default()
        },
        env,
        e2,
    );
    might_throw(p, env);
    let aast::Expr(_, p1, _) = e1;
    let aast::Expr(_, p2, _) = e2;
    let key_ty = env::fresh_type_invariant(env, p2.clone());
    let key_ty = env::update_reason(env, key_ty, |_| get_reason(&ty2).clone());
    let ty_err_opt = sub_type::sub_type_i(
        env,
        None,
        InternalType::LoclType(ty2.clone()),
        InternalType::LoclType(key_ty.clone()),
        Some(reasons_callback::unify_error_at(p.clone())),
    );
    add_typing_error_opt(env, &ty_err_opt);
    let val_ty = env::fresh_type(env, p.clone());
    // Dynamic inference: if the array expression carries a shadow type
    // variable, create a fresh shadow for the element type and emit a
    // can_index constraint on the array's shadow. This records "$d['key']"
    // as: shadow($d) <: can_index(key, val=shadow).
    let shadow_val_opt = match get_node(&ty1) {
        Ty_::Tdynamic(Some(_)) => {
            let v_val = env::fresh_shadow_tyvar(env, p.clone());
            Some(v_val)
        }
        _ => None,
    };
    let ci_val = match shadow_val_opt {
        Some(v_val) => mk((get_reason(&val_ty).clone(), Ty_::Tdynamic(Some(v_val)))),
        None => val_ty.clone(),
    };
    let ty_err_opt = sub_type::sub_type_i(
        env,
        None,
        InternalType::LoclType(ty1.clone()),
        InternalType::ConstraintType(mk_constraint_type((
            reason::witness(p.clone()),
            ConstraintType_::TcanIndex(CanIndex {
                key: key_ty,
                val: ci_val,
                index_expr: e2.clone(),
                access_kind: if *lhs_of_null_coalesce {
                    CiAccessKind::CiLhsOfNullCoalesce
                } else {
                    CiAccessKind::CiNormal
                },
                expr_pos: p.clone(),
                array_pos: p1.clone(),
                index_pos: p2.clone(),
            }),
        ))),
        Some(reasons_callback::unify_error_at(p.clone())),
    );
    add_typing_error_opt(env, &ty_err_opt);
    let val_ty = match shadow_val_opt {
        Some(v_val) => mk((get_reason(&val_ty).clone(), Ty_::Tdynamic(Some(v_val)))),
        None => env::update_reason(env, val_ty, |def| {
            reason::flow_array_get(def, reason::witness(p.clone()))
        }),
    };
    make_result(
        env,
        p.clone(),
        aast::Expr_::ArrayGet(Box::new((te1, Some(te2)))),
        val_ty,
    )
}

/// `Call { func = (_, pos_id, Id (_, s)) as e; targs; args; unpacked_arg = None }
/// when Hash_set.mem typing_env_pseudofunctions s`
#[inline(never)]
fn expr_call_pseudo_function(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    call: &nast::CallExpr,
) -> (tast::Expr, Ty) {
    let aast::CallExpr {
        func: e, targs, args, ..
    } = call;
    let (pos_id, s) = match e {
        aast::Expr(_, pos_id, aast::Expr_::Id(id)) => (pos_id, id.1.as_str()),
        _ => unreachable!(),
    };
    let expr_ctxt = sub_ctxt(ctxt, true);
    let (_tel, tys) = argument_list_exprs(|env, e| expr(None, &expr_ctxt, env, e), env, args);
    if s == sn::pseudo_functions::HH_EXPECT {
        do_hh_expect(false, env, pos_id, targs, p, &tys)
    } else if s == sn::pseudo_functions::HH_EXPECT_EQUIVALENT {
        do_hh_expect(true, env, pos_id, targs, p, &tys)
    } else if !targs.is_empty() {
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Expected_tparam {
                decl_pos: pos_or_decl::none,
                pos: pos_id.clone(),
                n: 0,
            }),
            env,
        );
    } else if s == sn::pseudo_functions::HH_SHOW {
        for ty in &tys {
            typing_log::hh_show(p, env, ty)
        }
    } else if s == sn::pseudo_functions::HH_SHOW_ENV {
        typing_log::hh_show_env(None, p, env);
    } else if s == sn::pseudo_functions::HH_LOG_LEVEL {
        match args.as_slice() {
            [
                aast::Argument::Anormal(aast::Expr(_, _, aast::Expr_::String(key_str))),
                aast::Argument::Anormal(aast::Expr(_, _, aast::Expr_::Int(level_str))),
            ] => {
                let level = int_of_string(level_str);
                env::set_log_level(env, &String::from_utf8_lossy(key_str), level)
            }
            _ => {}
        }
    } else if s == sn::pseudo_functions::HH_FORCE_SOLVE {
        let ty_err_opt = crate::typing_solver::solve_all_unsolved_tyvars(env);
        add_typing_error_opt(env, &ty_err_opt);
    } else if s == sn::pseudo_functions::HH_LOOP_FOREVER {
        loop_forever(env)
    } else if s == sn::pseudo_functions::HH_SLEEP {
        do_hh_sleep(args);
    } else if s == missing_special_names::HH_TIME {
        do_hh_time(args);
    }
    // Discard the environment and whether fake members should be forgotten to
    // make sure that pseudo functions don't change the typechecker behaviour.
    let env_after_pseudo_function = env.clone();
    let ((te, ty), _should_forget_fakes) = {
        might_throw(p, env);
        super::dispatch_call(None, expected, ctxt, p, env, e, targs, args, None)
    };
    *env = env_after_pseudo_function;
    (te, ty)
}

/// `Assign (((_, _, Lvar (_, v)) as e1), None, (_, _, ET_Splice splice))
/// when (not splice.extract_client_type) && Option.is_some splice.macro_variables`
#[inline(never)]
fn expr_assign_et_splice(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    outer: &nast::Expr,
    assign: &(nast::Expr, Option<ast_defs::Bop>, nast::Expr),
) -> (tast::Expr, Ty) {
    let (e1, _, e2) = assign;
    let v = match e1 {
        aast::Expr(_, _, aast::Expr_::Lvar(lid)) => &lid.1,
        _ => unreachable!(),
    };
    let splice = match e2 {
        aast::Expr(_, _, aast::Expr_::ETSplice(splice)) => &**splice,
        _ => unreachable!(),
    };
    let (expr, ty, macro_splice_vars) = super::check_et_splice(env, p, splice);
    let (te, ty) = binop::check_assign(
        ctxt.check_defined,
        expected,
        env,
        outer,
        p,
        None,
        e1,
        Either::Right((expr, ty)),
    );
    let local = env::get_local(env, v);
    env::set_local_(
        env,
        v.clone(),
        Local {
            macro_splice_vars,
            ..local
        },
    );
    (te, ty)
}

/// `Pipe (e0, e1, e2, null_flavor)`
#[inline(never)]
fn expr_pipe(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    pipe: &(aast::Lid, nast::Expr, nast::Expr, ast_defs::OperatorNullFlavor),
) -> (tast::Expr, Ty) {
    let (e0, e1, e2, null_flavor) = pipe;
    // If it weren't for local variable assignment or refinement the pipe
    // expression e1 |> e2 could be typed using this rule (E is environment with
    // types for locals):
    //
    //    E |- e1 : ty1    E[$$:ty1] |- e2 : ty2
    //    --------------------------------------
    //                E |- e1|>e2 : ty2
    //
    // Null-safe version e1 |?> e2 could be typed using following rule:
    //
    //    E |- e1 : ty1    E[$$: ty1 & nonnull] |- e2 : ty2
    //    -------------------------------------------------
    //              E |- e1|>e2 : ty2 | null
    //
    // The possibility of e2 changing the types of locals in E means that E
    // can evolve, and so we need to restore $$ to its original state.
    let is_nullsafe = match null_flavor {
        ast_defs::OperatorNullFlavor::Nullsafe => true,
        _ => false,
    };
    let r = reason::nullsafe_pipe_op(p.clone());
    let ty_null = make_type::null(r.clone());
    let ty_nonnull = make_type::nonnull(r.clone());
    let (te1, ty1) = expr(None, &sub_ctxt(ctxt, false), env, e1);
    let ty1 = if is_nullsafe {
        inter::intersect(env, r, ty1, ty_nonnull)
    } else {
        ty1
    };
    let dd_var: LocalId = local_id::make_unscoped(sn::special_idents::DOLLAR_DOLLAR);
    let dd_old_ty = if env::is_local_defined(env, &dd_var) {
        Some(env::get_local(env, &dd_var))
    } else {
        None
    };
    env::set_local(None, None, env, dd_var.clone(), ty1, Pos::NONE);
    let (te2, ty2) = expr(None, &sub_ctxt(ctxt, false), env, e2);
    let ty2 = if is_nullsafe {
        union::union(env, None, None, ty2, ty_null)
    } else {
        ty2
    };
    match dd_old_ty {
        None => env::unset_local(env, &dd_var),
        Some(local) => env::set_local(None, None, env, dd_var, local.ty, local.pos),
    }
    let (te, ty) = make_result(
        env,
        p.clone(),
        aast::Expr_::Pipe(Box::new((e0.clone(), te1, te2, *null_flavor))),
        ty2,
    );
    (te, ty)
}

/// `Unop (uop, e)`
#[inline(never)]
fn expr_unop(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    unop: &(ast_defs::Uop, nast::Expr),
) -> (tast::Expr, Ty) {
    let (uop, e) = unop;
    let (te, ty) = expr(None, &sub_ctxt(ctxt, false), env, e);
    // might be appropriate to move this into Typing_arithmetic later,
    // but easier here while check_bool_for_condition is in typing.ml
    match uop {
        ast_defs::Uop::Unot => {
            let aast::Expr(cond_ty, cond_pos, _) = &te;
            check_bool_for_condition(env, cond_pos, cond_ty.clone())
        }
        _ => {}
    }
    might_throw(p, env);
    let (tuop, ty) = crate::typing_arithmetic::unop(p.clone(), env, *uop, te.clone(), ty);
    crate::typing_local_ops::check_assignment(env, &te);
    (tuop, ty)
}

/// `Class_get (((_, _, cid_) as cid), mid, Is_prop)
/// when Env.FakeMembers.is_valid_static env cid_ (snd mid)`
#[inline(never)]
fn expr_class_get_fake_member(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    cg: &(nast::ClassId, aast::Pstring, aast::PropOrMethod),
) -> (tast::Expr, Ty) {
    let (cid, mid, _) = cg;
    let aast::ClassId(_, _, cid_) = cid;
    let local = env::fake_members::make_static(env, cid_, &mid.1, p.clone());
    let local: nast::Expr = aast::Expr(
        (),
        p.clone(),
        aast::Expr_::Lvar(Box::new(aast::Lid(p.clone(), local))),
    );
    let (_, ty) = expr(None, &sub_ctxt(ctxt, false), env, &local);
    let ty = map_reason(ty, |def| {
        let use_ = reason::class_const_access(p.clone());
        reason::flow_const_access(def, use_)
    });
    let (_tal, te, _) = class_id::class_expr(
        None, None, None, None, None, None, None, None, None, None, env, &[], cid,
    );
    make_result(
        env,
        p.clone(),
        aast::Expr_::ClassGet(Box::new((te, mid.clone(), aast::PropOrMethod::IsProp))),
        ty,
    )
}

/// `Class_get (((_, _, cid_) as cid), mid, prop_or_method)`: statically-known
/// static property access e.g. Foo::$x
#[inline(never)]
fn expr_class_get(
    env: &mut Env,
    p: &Pos,
    cg: &(nast::ClassId, aast::Pstring, aast::PropOrMethod),
) -> (tast::Expr, Ty) {
    let (cid, mid, prop_or_method) = cg;
    let aast::ClassId(_, _, cid_) = cid;
    let (_tal, te, cty) = class_id::class_expr(
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        Some(class_id::ClassnameExprError::Error),
        env,
        &[],
        cid,
    );
    might_throw(p, env);
    let (ty, _tal) = class_get_expr::class_get(
        *prop_or_method == aast::PropOrMethod::IsMethod,
        false,
        None,
        None,
        None,
        None,
        None,
        None,
        env,
        cty,
        mid,
        cid,
    );
    let ty = env::fake_members::check_static_invalid(env, cid_, &mid.1, ty);
    let ty = map_reason(ty, |def| {
        let use_ = reason::static_prop_access(p.clone());
        reason::flow_prop_access(def, use_)
    });
    make_result(
        env,
        p.clone(),
        aast::Expr_::ClassGet(Box::new((te, mid.clone(), *prop_or_method))),
        ty,
    )
}

/// `Obj_get (e, (_, pid, Id (py, y)), nf, is_prop)
/// when Env.FakeMembers.is_valid env e y`: fake member property access
#[inline(never)]
fn expr_obj_get_fake_member(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    og: &(nast::Expr, nast::Expr, ast_defs::OperatorNullFlavor, aast::PropOrMethod),
) -> (tast::Expr, Ty) {
    let (e, member, nf, is_prop) = og;
    let (pid, py, y) = match member {
        aast::Expr(_, pid, aast::Expr_::Id(id)) => (pid, &id.0, &id.1),
        _ => unreachable!(),
    };
    might_throw(p, env);
    let local = env::fake_members::make(env, e, y, p.clone());
    let local: nast::Expr = aast::Expr(
        (),
        p.clone(),
        aast::Expr_::Lvar(Box::new(aast::Lid(p.clone(), local))),
    );
    let (_, ty) = expr(None, &sub_ctxt(ctxt, false), env, &local);
    xhp_attribute::xhp_check_get_attribute(p, env, e, y, *nf);
    let (t_lhs, _) = expr(None, &sub_ctxt(ctxt, true), env, e);
    let t_rhs = crate::typing_helpers::make_simplify_typed_expr(
        env,
        pid.clone(),
        ty.clone(),
        aast::Expr_::Id(Box::new(ast_defs::Id(py.clone(), y.clone()))),
    );
    make_result(
        env,
        p.clone(),
        aast::Expr_::ObjGet(Box::new((t_lhs, t_rhs, *nf, *is_prop))),
        ty,
    )
}

/// `Obj_get (e1, (_, pm, Id m), nullflavor, prop_or_method)`: statically-known
/// instance property access e.g. $x->f
#[inline(never)]
fn expr_obj_get_static(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    og: &(nast::Expr, nast::Expr, ast_defs::OperatorNullFlavor, aast::PropOrMethod),
) -> (tast::Expr, Ty) {
    let (e1, member, nullflavor, prop_or_method) = og;
    let (pm, m) = match member {
        aast::Expr(_, pm, aast::Expr_::Id(m)) => (pm, &**m),
        _ => unreachable!(),
    };
    xhp_attribute::xhp_check_get_attribute(p, env, e1, &m.1, *nullflavor);
    let (te1, ty1) = expr(None, &sub_ctxt(ctxt, true), env, e1);
    might_throw(p, env);
    // We typecheck Obj_get by checking whether it is a subtype of
    // Thas_member(m, #1) where #1 is a fresh type variable.
    let mem_ty = env::fresh_type(env, p.clone());
    let aast::Expr(_, p1, _) = e1;
    let r = reason::witness(p1.clone());
    let has_member_ty = make_type::has_member(
        r,
        m.clone(),
        mem_ty.clone(),
        aast::ClassId_::CIexpr(e1.clone()),
        None,
    );
    let (ty_err_opt, result_ty, ty_mismatch_opt) = match nullflavor {
        ast_defs::OperatorNullFlavor::Regular => {
            let ty_err_opt = crate::typing_ops::sub_type_i(
                None,
                p1.clone(),
                Ureason::URnone,
                env,
                InternalType::LoclType(ty1.clone()),
                has_member_ty,
                callback::unify_error(),
            );
            let ty_mismatch = mk_ty_mismatch_opt(
                ty1.clone(),
                make_type::nothing(reason::none()),
                ty_err_opt.as_ref(),
            );
            (ty_err_opt, mem_ty, ty_mismatch)
        }
        ast_defs::OperatorNullFlavor::Nullsafe => {
            // A nullsafe access is equivalent to an `if` where the receiver is
            // refined to `nonnull` (`null`) in the true (false) branches
            let r = reason::nullsafe_op(p.clone());
            let ty_null = make_type::null(r.clone());
            let ty_nonnull = make_type::nonnull(r.clone());
            // For the true case, we need to intersect the receiver type with
            // `nonnull` and assert the `has_member` constraint
            let ty_err_opt = crate::typing_ops::sub_type_i(
                None,
                p1.clone(),
                Ureason::URnone,
                env,
                InternalType::LoclType(make_type::intersection(
                    r.clone(),
                    vec![ty1.clone(), ty_nonnull],
                )),
                has_member_ty,
                callback::unify_error(),
            );
            let ty_mismatch = mk_ty_mismatch_opt(
                ty1.clone(),
                make_type::nothing(reason::none()),
                ty_err_opt.as_ref(),
            );
            // For the false case, if the receiver was nullable then the
            // member type should be made nullable. We do this by taking the
            // intersection of the receiver type with `null` and then
            // taking the union with the member type
            let null_or_nothing_ty = inter::intersect(env, r, ty_null, ty1.clone());
            let result_ty = union::union(env, None, None, null_or_nothing_ty, mem_ty);
            (ty_err_opt, result_ty, ty_mismatch)
        }
    };
    let result_ty = env::fake_members::check_instance_invalid(env, e1, &m.1, result_ty);
    let result_ty = env::update_reason(env, result_ty, |def| {
        reason::flow_prop_access(def, reason::witness(p.clone()))
    });
    add_typing_error_opt(env, &ty_err_opt);
    let inner_te = crate::typing_helpers::make_simplify_typed_expr(
        env,
        pm.clone(),
        result_ty.clone(),
        aast::Expr_::Id(Box::new(m.clone())),
    );
    make_result(
        env,
        p.clone(),
        aast::Expr_::ObjGet(Box::new((
            hole_on_ty_mismatch(te1, ty_mismatch_opt),
            inner_te,
            *nullflavor,
            *prop_or_method,
        ))),
        result_ty,
    )
}

/// `Obj_get (e1, e2, nullflavor, prop_or_method)`: dynamic instance property
/// access e.g. $x->$f
#[inline(never)]
fn expr_obj_get_dynamic(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    og: &(nast::Expr, nast::Expr, ast_defs::OperatorNullFlavor, aast::PropOrMethod),
) -> (tast::Expr, Ty) {
    let (e1, e2, nullflavor, prop_or_method) = og;
    let (te1, ty1) = expr(None, &sub_ctxt(ctxt, true), env, e1);
    let aast::Expr(_, receiver_pos, _) = e1;
    let receiver_ty = match nullflavor {
        ast_defs::OperatorNullFlavor::Regular => ty1.clone(),
        ast_defs::OperatorNullFlavor::Nullsafe => {
            let r = reason::nullsafe_op(p.clone());
            make_type::intersection(r.clone(), vec![ty1.clone(), make_type::nonnull(r)])
        }
    };
    let member_kind = match prop_or_method {
        aast::PropOrMethod::IsProp => primary::RequireDynamicObjGetMemberKind::Property,
        aast::PropOrMethod::IsMethod => primary::RequireDynamicObjGetMemberKind::Method,
    };
    let member_name = match e2 {
        aast::Expr(_, member_pos, aast::Expr_::Lvar(lid)) => {
            let aast::Lid(member_name_pos, member_name) = &**lid;
            Some(primary::DynamicObjGetMember {
                member_pos: member_pos.clone(),
                member_name_pos: member_name_pos.clone(),
                member_name: local_id::get_name(member_name).clone(),
            })
        }
        _ => None,
    };
    let dynamic_ty = make_type::dynamic(reason::witness(p.clone()));
    // Use ordinary subtyping to require the receiver to be explicitly
    // dynamic, rather than merely compatible under dynamic-aware subtyping.
    let receiver_ty_str: Lazy<String> = {
        let env = env.clone();
        let ty1 = ty1.clone();
        Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty1))
    };
    let ty_err_opt = sub_type::sub_type_or_fail(
        env,
        receiver_ty,
        dynamic_ty,
        Some(typing_error::primary(primary::T::Require_dynamic_obj_get {
            receiver_pos: receiver_pos.clone(),
            receiver_ty: receiver_ty_str,
            receiver_ty_pos: get_pos(&ty1),
            member_kind,
            member_name,
        })),
    );
    add_typing_error_opt(env, &ty_err_opt);
    let (te2, _) = expr(None, &sub_ctxt(ctxt, false), env, e2);
    let ty = make_type::dynamic(reason::dynamic_prop(p.clone()));
    let aast::Expr(_, pos, te2) = te2;
    might_throw(p, env);
    let te2 = crate::typing_helpers::make_simplify_typed_expr(env, pos, ty.clone(), te2);
    make_result(
        env,
        p.clone(),
        aast::Expr_::ObjGet(Box::new((te1, te2, *nullflavor, *prop_or_method))),
        ty,
    )
}

/// `Yield af`
#[inline(never)]
fn expr_yield(env: &mut Env, p: &Pos, af: &nast::Afield) -> (tast::Expr, Ty) {
    let (taf, opt_key, value) = afield::array_field(env, af);
    let expected_return = env::get_return(env).return_type;
    let send = match get_node(&expected_return) {
        Ty_::Tclass(_, _, tys) if tys.len() >= 3 => tys[2].clone(),
        Ty_::Tdynamic(_) if tast::is_under_dynamic_assumptions(env.checked) => {
            expected_return.clone()
        }
        _ => {
            diagnostics_state::internal_error(p.clone(), "Return type is not a generator");
            make_type::union(reason::yield_send(p.clone()), vec![])
        }
    };
    let is_async = match env::get_fn_kind(env) {
        ast_defs::FunKind::FGenerator => false,
        // This could also catch sync/async non-generators, but an error would
        // have already been generated elsewhere
        _ => true,
    };
    let key = match (af, opt_key) {
        (aast::Afield::AFvalue(aast::Expr(_, p, _)), None) => {
            if is_async {
                let ty = env::fresh_type(env, p.clone());
                make_type::nullable(reason::yield_asyncnull(p.clone()), ty)
            } else {
                make_type::int(reason::witness(p.clone()))
            }
        }
        (_, Some(x)) => x,
        (_, _) => panic!("assert false"),
    };
    let rty = if is_async {
        make_type::async_generator(reason::yield_asyncgen(p.clone()), key, value, send.clone())
    } else {
        make_type::generator(reason::yield_gen(p.clone()), key, value, send.clone())
    };
    let expected_return = env::get_return(env).return_type;
    let ty_err_opt = crate::typing_coercion::coerce_type(
        None,
        None,
        None,
        p.clone(),
        Ureason::URyield,
        env,
        rty,
        expected_return,
        Enforcement::Enforced, // TODO akenn: flow in
        callback::unify_error(),
    );
    add_typing_error_opt(env, &ty_err_opt);
    env::forget_members(env, Blame::Blame(p.clone(), BlameSource::BScall));
    lenv::save_and_merge_next_in_cont(env, p, c::T::Exit);
    make_result(
        env,
        p.clone(),
        aast::Expr_::Yield(Box::new(taf)),
        make_type::nullable(reason::yield_send(p.clone()), send),
    )
}

/// `Await e`
#[inline(never)]
fn expr_await(ctxt: &context::T, env: &mut Env, p: &Pos, e: &nast::Expr) -> (tast::Expr, Ty) {
    match e {
        aast::Expr(_, p, aast::Expr_::Call(call))
            if matches!(
                &call.func,
                aast::Expr(_, _, aast::Expr_::Id(f))
                    if f.1 == sn::pseudo_functions::UNSAFE_CAST
                        || f.1 == sn::pseudo_functions::UNSAFE_NONNULL_CAST
            ) =>
        {
            typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Unsafe_cast_await(p.clone())),
                env,
            )
        }
        _ => {}
    }
    might_throw(p, env);
    let (ty, te) = crate::typing_escape::with_expr_dep_cleanup(env, |env| {
        let (te, rty) = expr(
            None,
            &context::T {
                attribute_check_policy: ctxt.attribute_check_policy,
                is_using_clause: ctxt.is_using_clause,
                in_await: Some(reason::witness(p.clone())),
                accept_using_var: false,
                check_defined: ctxt.check_defined,
                ..context::default()
            },
            env,
            e,
        );
        let ty = crate::typing_async::overload_extract_from_awaitable(env, p.clone(), rty);
        (ty, te)
    });
    make_result(env, p.clone(), aast::Expr_::Await(Box::new(te)), ty)
}

/// `New (((_, pos, _) as cid), explicit_targs, el, unpacked_element, ())`
#[inline(never)]
fn expr_new(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    new: &(
        nast::ClassId,
        Vec<nast::Targ>,
        Vec<nast::Argument>,
        Option<nast::Expr>,
        (),
    ),
) -> (tast::Expr, Ty) {
    let (cid, explicit_targs, el, unpacked_element, ()) = new;
    let aast::ClassId(_, pos, _) = cid;
    might_throw(p, env);
    let (tc, tal, tel, typed_unpack_element, ty, ctor_fty, should_forget_fakes) =
        super::new_object(
            expected,
            true,
            ctxt.is_using_clause,
            false,
            pos,
            env,
            cid,
            explicit_targs,
            el,
            unpacked_element.as_ref(),
        );
    if should_forget_fakes {
        env::forget_members(env, Blame::Blame(p.clone(), BlameSource::BScall))
    }
    make_result(
        env,
        p.clone(),
        aast::Expr_::New(Box::new((tc, tal, tel, typed_unpack_element, ctor_fty))),
        ty,
    )
}

/// `Cast (hint, e)`
#[inline(never)]
fn expr_cast(
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    cast: &(aast::Hint, nast::Expr),
) -> (tast::Expr, Ty) {
    let (hint, e) = cast;
    let (te, ty2) = expr(
        None,
        &context::T {
            attribute_check_policy: ctxt.attribute_check_policy,
            in_await: ctxt.in_await.clone(),
            accept_using_var: false,
            check_defined: ctxt.check_defined,
            ..context::default()
        },
        env,
        e,
    );
    might_throw(p, env);
    let (ty_err_opt, ty) = phase::localize_hint_no_subst(env, false, hint);
    add_typing_error_opt(env, &ty_err_opt);
    if env::get_tcopt(env).tco_dynamic_inference {
        match get_node(&ty2) {
            Ty_::Tdynamic(Some(v)) => {
                env::add_tyvar_upper_bound(None, env, *v, InternalType::LoclType(ty.clone()))
            }
            _ => {}
        }
    }
    make_result(
        env,
        p.clone(),
        aast::Expr_::Cast(Box::new((hint.clone(), te))),
        ty,
    )
}

/// `As { expr = e; hint; is_nullable; enforce_deep }`
#[inline(never)]
fn expr_as(ctxt: &context::T, env: &mut Env, p: &Pos, as_: &nast::As_) -> (tast::Expr, Ty) {
    let aast::As_ {
        expr: e,
        hint,
        is_nullable,
        enforce_deep,
    } = as_;
    let refine_type = |env: &mut Env, lpos: &Pos, lty: Ty, rty: Ty| -> Ty {
        let reason = reason::as_refinement(lpos.clone());
        let rty = env::expand_type(env, rty);
        refine_and_simplify_intersection(env, p, &reason, lpos, lty, rty)
    };
    let (te, expr_ty) = expr(None, &sub_ctxt(ctxt, false), env, e);
    might_throw(p, env);
    let should_check_package_boundary = if *is_nullable {
        crate::typing_packages::CheckReason::No
    } else if env::package_allow_as_expression_violations(env) {
        crate::typing_packages::CheckReason::LintOnly
    } else {
        crate::typing_packages::CheckReason::Yes(
            primary::package::TargetSymbolSpec::As_expression,
        )
    };
    crate::typing_type_integrity::check_hint_integrity(
        false,
        should_check_package_boundary,
        env,
        hint,
    );
    let (ty_err_opt1, hint_ty) = phase::localize_hint_for_refinement(env, hint);
    add_typing_error_opt(env, &ty_err_opt1);
    let (_, hint_ty) = tutils::strip_supportdyn(env, hint_ty);
    let (ty_err_opt2, hint_ty) = if is_dynamic(&hint_ty) {
        let ty_err_opt = tutils::supports_dynamic(
            env,
            expr_ty,
            Some(reasons_callback::unify_error_at(p.clone())),
        );
        let locl = make_a_local_of(true, env, e);
        match locl {
            Some(ivar) => set_local(None, env, ivar, hint_ty.clone()),
            None => {}
        }
        (ty_err_opt, hint_ty)
    } else if *is_nullable {
        let aast::Expr(_, e_p, _) = e;
        let hint_ty = refine_type(env, e_p, expr_ty, hint_ty);
        (None, make_type::nullable(reason::witness(p.clone()), hint_ty))
    } else {
        let locl = make_a_local_of(true, env, e);
        match locl {
            Some(ivar) => {
                let ivar_pos = ivar.0.clone();
                let hint_ty = refine_type(env, &ivar_pos, expr_ty, hint_ty);
                set_local(None, env, ivar, hint_ty.clone());
                (None, hint_ty)
            }
            None => {
                let aast::Expr(_, e_p, _) = e;
                let ty = refine_type(env, e_p, expr_ty, hint_ty);
                (None, ty)
            }
        }
    };
    add_typing_error_opt(env, &ty_err_opt2);
    make_result(
        env,
        p.clone(),
        aast::Expr_::As(Box::new(aast::As_ {
            expr: te,
            hint: hint.clone(),
            is_nullable: *is_nullable,
            enforce_deep: *enforce_deep,
        })),
        hint_ty,
    )
}

/// `Xml (sid, attrl, el)`
#[inline(never)]
fn expr_xml(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    xml: &(aast::ClassName, Vec<nast::XhpAttribute>, Vec<nast::Expr>),
) -> (tast::Expr, Ty) {
    let (sid, attrl, el) = xml;
    let cid: nast::ClassId_ = aast::ClassId_::CI(sid.clone());
    let (_tal, _te, classes) =
        class_id::class_id_for_new(nonexact(), false, false, p, env, &cid, &[]);
    // OK to ignore rest of list; class_info only used for errors, and
    // cid = CI sid cannot produce a union of classes anyhow
    let class_info: Option<cls::T> = classes.into_iter().find_map(|c| match c {
        ClassOrDynamic::Dynamic => None,
        ClassOrDynamic::Class(_, class_info, _) => Some(class_info),
    });
    let before_new_lenv = env.lenv.clone();
    let (te, obj) = {
        // New statements derived from Xml literals are of the following form:
        //
        //   __construct(
        //     darray<string,mixed> $attributes,
        //     varray<mixed> $children,
        //     string $file,
        //     int $line
        //   );
        let new_exp = crate::typing_xhp::rewrite_xml_into_new(
            p.clone(),
            sid.clone(),
            attrl.clone(),
            el.clone(),
        );
        expr(expected, &sub_ctxt(ctxt, false), env, &new_exp)
    };
    let tchildren = match &te {
        aast::Expr(_, _, aast::Expr_::New(new)) => match &new.2[..] {
            [
                _,
                aast::Argument::Anormal(aast::Expr(_, _, aast::Expr_::ValCollection(vc))),
                _,
                _,
            ] if vc.0.1 == aast::VcKind::Vec => {
                // Typing_xhp.rewrite_xml_into_new generates an AST node for a `varray[]` literal, which is interpreted as a vec[]
                vc.2.clone()
            }
            _ => vec![],
        },
        _ => {
            // We end up in this case when the cosntructed new expression does
            // not typecheck.
            vec![]
        }
    };
    // We restored the local environment to the state prior to typechecking the
    // XHP literal as a constructor call. Otherwise, refinement and their
    // invalidations will be executed twice.
    //
    // This works specifically because when XHP literals are desugared,
    // attributes are the first argument. If children were typechecked first,
    // they could have caused legitimate invalidation of fake members making
    // restoration of environment unsound.
    let after_new_lenv = std::mem::replace(&mut env.lenv, before_new_lenv);
    let typed_attrs =
        xhp_attribute::xhp_attribute_exprs(env, class_info.as_ref(), attrl, sid, &obj);
    env.lenv = after_new_lenv;
    let txml = aast::Expr_::Xml(Box::new((sid.clone(), typed_attrs, tchildren)));
    match class_info {
        None => {
            let ty = make_type::nothing(reason::missing_class(p.clone()));
            make_result(env, p.clone(), txml, ty)
        }
        Some(_) => make_result(env, p.clone(), txml, obj),
    }
}

/// `Shape fdm`
#[inline(never)]
fn expr_shape(
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    env: &mut Env,
    p: &Pos,
    fdm: &[(ast_defs::ShapeFieldName, nast::Expr)],
) -> (tast::Expr, Ty) {
    let expr_helper = |expected: Option<&expected_ty::T>,
                       env: &mut Env,
                       (k, e): &(ast_defs::ShapeFieldName, nast::Expr)|
     -> (ast_defs::ShapeFieldName, tast::Expr, Ty) {
        let (et, ty) = expr(expected, &sub_ctxt(ctxt, false), env, e);
        (k.clone(), et, ty)
    };
    // The OCaml goes on with the environment from before the expansion in its
    // last case (`| _ -> List.map_env env ~f:expr_helper fdm`).
    let env0 = env.clone();
    let mut tfdm = vec![];
    match env_help::expand_expected_opt(true, false, env, expected) {
        Some((
            pos,
            ur,
            _,
            _,
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: expected_fdm,
                ..
            })),
            _,
        )) => {
            for ke in fdm {
                let (k, _) = ke;
                let tk = t_shape_map::TShapeField(t_shape_field::of_ast(
                    |p| pos_or_decl::of_raw_pos(p.clone()),
                    k,
                ));
                match expected_fdm.get(&tk) {
                    None => tfdm.push(expr_helper(None, env, ke)),
                    Some(sft) => {
                        let expected =
                            expected_ty::make(None, None, pos.clone(), ur.clone(), sft.ty.clone());
                        tfdm.push(expr_helper(Some(&expected), env, ke))
                    }
                }
            }
        }
        _ => {
            *env = env0;
            for ke in fdm {
                tfdm.push(expr_helper(None, env, ke))
            }
        }
    }
    let mut fdm_ty: t_shape_map::T<ShapeFieldType> = t_shape_map::T::new();
    for (k, _, ty) in &tfdm {
        let tk = t_shape_map::TShapeField(t_shape_field::of_ast(
            |p| pos_or_decl::of_raw_pos(p.clone()),
            k,
        ));
        // `TShapeMap.add` replaces the binding, key included (`insert` would
        // keep the key, whose position may differ).
        fdm_ty.remove(&tk);
        fdm_ty.insert(
            tk,
            ShapeFieldType {
                optional: false,
                ty: ty.clone(),
            },
        );
    }
    let keys: Vec<ast_defs::ShapeFieldName> = tfdm.iter().map(|(k, _, _)| k.clone()).collect();
    let errors = crate::typing_shapes::check_shape_keys_validity(env, &keys);
    for err in &errors {
        typing_error_utils::add_typing_error(err, env)
    }
    // Fields are fully known, because this shape is constructed
    // using shape keyword and we know exactly what fields are set.
    make_result(
        env,
        p.clone(),
        aast::Expr_::Shape(tfdm.into_iter().map(|(k, te, _)| (k, te)).collect()),
        make_type::closed_shape(reason::shape_literal(p.clone()), fdm_ty),
    )
}

/// `EnumClassLabel (Some enum_name, name)`
#[inline(never)]
fn expr_enum_class_label(
    env: &mut Env,
    p: &Pos,
    ecl: &(Option<aast::ClassName>, String),
) -> (tast::Expr, Ty) {
    let (enum_name, name) = ecl;
    let enum_name = enum_name
        .as_ref()
        .expect("EnumClassLabel (Some enum_name, name)");
    let ty_cls = make_type::class_type(reason::witness(enum_name.0.clone()), enum_name.1.clone(), vec![]);
    let label_pos = {
        let (_, end_column) = crate::pos::end_line_column(p);
        crate::pos::set_col_start(end_column - (name.len() as isize + 1), p)
    };
    env::open_tyvars(env, p.clone());
    let ty_in = env::fresh_type(env, p.clone());
    let ty_out = env::fresh_type(env, p.clone());
    let has_const = InternalType::ConstraintType(mk_constraint_type((
        reason::witness(label_pos),
        ConstraintType_::ThasConst {
            name: name.clone(),
            ty: mk((
                reason::witness(p.clone()),
                Ty_::Tnewtype(
                    sn::classes::MEMBER_OF.to_string(),
                    vec![ty_in.clone(), ty_out.clone()],
                    ty_out.clone(),
                ),
            )),
        },
    )));
    env::set_tyvar_variance_i(env, None, None, &has_const);
    let err = crate::typing_ops::sub_type_i(
        None,
        p.clone(),
        Ureason::URlabel,
        env,
        InternalType::LoclType(ty_cls),
        has_const,
        callback::unify_error(),
    );
    let ty_err = crate::typing_solver::close_tyvars_and_solve(env);
    // `Option.merge err ty_err ~f:Typing_error.both`
    let errs = match (err, ty_err) {
        (Some(err), Some(ty_err)) => Some(typing_error::both(err, ty_err)),
        (Some(err), None) => Some(err),
        (None, ty_err) => ty_err,
    };
    add_typing_error_opt(env, &errs);
    let r = reason::witness(p.clone());
    let ty = mk((
        r.clone(),
        Ty_::Tnewtype(
            sn::classes::ENUM_CLASS_LABEL.to_string(),
            vec![ty_in, ty_out],
            make_type::mixed(r),
        ),
    ));
    make_result(
        env,
        p.clone(),
        aast::Expr_::EnumClassLabel(Box::new((Some(enum_name.clone()), name.clone()))),
        ty,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn context_default() {
        let d = context::default();
        assert!(!d.is_using_clause);
        assert_eq!(d.valkind, valkind::T::Other);
        assert_eq!(d.attribute_check_policy, AttributeCheckPolicy::CheckAll);
        assert!(d.in_await.is_none());
        assert!(!d.lhs_of_null_coalesce);
        assert!(!d.accept_using_var);
        assert!(d.check_defined);
        assert!(!d.immediately_called_lambda);
        assert!(!d.support_readonly_return);
    }

    #[test]
    fn show_attribute_check_policy_is_qualified() {
        assert_eq!(
            show_attribute_check_policy(&AttributeCheckPolicy::CheckAll),
            "Typing.Expr.Check_all"
        );
        assert_eq!(
            show_attribute_check_policy(&AttributeCheckPolicy::SkipPackage),
            "Typing.Expr.Skip_package"
        );
        assert_eq!(
            show_attribute_check_policy(&AttributeCheckPolicy::SkipAllAccess),
            "Typing.Expr.Skip_all_access"
        );
    }

    /// `Context.show Context.default` as `ppx_deriving.show` prints it: the
    /// record does not fit in the margin of 78, so the boxes break after
    /// fields that end a line.
    #[test]
    fn show_context_default() {
        let s = context::show(&context::default());
        // The text, without the line breaks and indentation the margin adds.
        let flat: String = s.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(
            flat,
            "{ Typing.Expr.Context.is_using_clause = false; \
             valkind = Typing.Valkind.Other; \
             attribute_check_policy = Typing.Expr.Check_all; \
             in_await = <opaque>; lhs_of_null_coalesce = false; \
             accept_using_var = false; check_defined = true; \
             immediately_called_lambda = false; \
             support_readonly_return = false }"
        );
        // Every line fits in the margin.
        assert!(s.lines().all(|l| l.len() <= 78));
        // Continuation lines are indented by the box of the record.
        assert!(s.lines().skip(1).all(|l| l.starts_with("  ")));
    }

    #[test]
    fn int_of_string_literals() {
        assert_eq!(int_of_string("0"), 0);
        assert_eq!(int_of_string("42"), 42);
        assert_eq!(int_of_string("-7"), -7);
        assert_eq!(int_of_string("1_000"), 1000);
        assert_eq!(int_of_string("0x1F"), 31);
        assert_eq!(int_of_string("0o17"), 15);
        assert_eq!(int_of_string("0b101"), 5);
        assert_eq!(int_of_string("4611686018427387903"), 4611686018427387903);
        assert!(std::panic::catch_unwind(|| int_of_string("4611686018427387904")).is_err());
        assert!(std::panic::catch_unwind(|| int_of_string("")).is_err());
        assert!(std::panic::catch_unwind(|| int_of_string("_1")).is_err());
        assert!(std::panic::catch_unwind(|| int_of_string("12a")).is_err());
    }

    #[test]
    fn typed_format_string() {
        assert!(is_typed_format_string("\\HH\\TypedFormatString"));
        assert!(!is_typed_format_string("\\HH\\FormatString"));
    }
}
