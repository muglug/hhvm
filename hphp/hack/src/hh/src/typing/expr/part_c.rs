// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 6893-9032): module `Expr`, last part.
//! See `hh/PORTING.md`.
//!
//! The functions, in the order of `typing.ml`: [`call`],
//! [`call_untyped_unpack`], [`upcast`], [`type_switch`], [`condition`],
//! [`condition_dual`], [`condition_single`], [`string2`],
//! [`overload_function`] and [`update_array_type`].
//!
//! # Signatures
//!
//! - `expected : ExpectedTy.t option` is `Option<&expected_ty::T>`, as in the
//!   prelude (`check_expected_ty`); `ctxt : Context.t` is `&context::T`.
//! - `call`'s `?(nullsafe : Pos.t option = None)` is an optional argument
//!   whose type is an option: `Option<Option<Pos>>`, `None` being the
//!   default (which is `None`).
//! - `env -> env` (the two branches that `condition_dual` and `type_switch`
//!   return) is [`EnvTransformer`], `Rc<dyn Fn(&mut Env)>`: OCaml may apply
//!   them several times, and `condition_dual` shares one between two
//!   closures.
//! - `overload_function make_call ... f`: `make_call` returns what OCaml's
//!   returns besides the environment (the callers' `make_call` is
//!   `make_result`, which gives `(Tast.expr, locl_ty)`), and `f env fty res el
//!   tel` returns the type.
//!
//! # Environments that OCaml drops
//!
//! - `call`'s local `is_fun_type` reads the environment `call` was given (it
//!   is defined before any other): it gets a copy of that one.
//! - Where OCaml discards the environment of a test (`snd
//!   (Typing_dynamic_utils.try_strip_dynamic env ...)`,
//!   `TUtils.strip_supportdyn` in `is_fun_type`), the test runs on a copy.
//! - `type_switch` returns no environment when the expression is not a local
//!   (`let*`), or goes on with the one from before `get_partitions` when the
//!   type cannot be partitioned: `*env` is put back in both cases.
//! - In `type_switch`, the closure that instantiates the assumptions
//!   (`instantiate_prop env ...`) reads the environment from before
//!   `instantiate_predicate_with_assumptions`: it gets a copy of it.

use std::cell::RefCell;
use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::FunKind;
use oxidized::ast_defs::Id;
use oxidized::ast_defs::ParamKind;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Uop;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use super::*;
use crate::aast_utils;
use crate::i_map;
use crate::internal_type_set;
use crate::pos_or_decl;
use crate::tast;
use crate::tvid;
use crate::type_parameter_env_ops;
use crate::typing::assign;
use crate::typing::class_get_expr;
use crate::typing::class_id;
use crate::typing::prelude::*;
use crate::typing_argument;
use crate::typing_argument::DynFuncKind;
use crate::typing_array_access;
use crate::typing_class_pointers;
use crate::typing_coeffects;
// module C = Typing_continuations
use crate::typing_continuations as c;
// open Typing_defs (with Typing_defs_core)
use crate::typing_defs::*;
// open Typing_defs_constraints
use crate::typing_defs_constraints::*;
use crate::typing_defs_flags;
use crate::typing_dynamic_utils;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_exts;
use crate::typing_helpers;
// module ExpectedTy = Typing_helpers.ExpectedTy
use crate::typing_helpers::expected_ty;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
use crate::typing_local_packages;
use crate::typing_log;
use crate::typing_logic;
use crate::typing_logic::SubtypeProp;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module Type = Typing_ops
use crate::typing_ops;
// module Phase = Typing_phase
use crate::typing_phase as phase;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_refinement;
use crate::typing_shapes;
use crate::typing_solver;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
// module Union = Typing_union
use crate::typing_union;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;

/// The names of `Naming_special_names` that `naming_special_names_rust` does
/// not have, with the OCaml values.
mod missing_special_names {
    /// `Capabilities`
    pub mod capabilities {
        /// `Capabilities.writeProperty`
        pub const WRITE_PROPERTY: &str = "\\HH\\Capabilities\\WriteProperty";
    }
}

/// `env -> env`: what `condition_dual` and `type_switch` return for each
/// branch.
pub(crate) type EnvTransformer = Rc<dyn Fn(&mut Env)>;

/// `Tvid.Set.t`
type TvidSet = tvid::set::T;

/// `(int * locl_ty fun_param) S_map.t`
type NamedParams = im::OrdMap<String, (isize, FunParam)>;

thread_local! {
    /// Empty maps and sets that `call` copies (a reference count bump):
    /// `im`'s `new` allocates and fills a node, and most calls keep them
    /// empty. (A lookup in `crate::im_empty` costs more than the copy here.)
    static EMPTY_NAMED_PARAMS: NamedParams = NamedParams::new();
    static EMPTY_NAME_SET: im::OrdSet<String> = im::OrdSet::new();
}

/// `Option.merge`
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, None) => None,
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// `List.map_env_ty_err_opt` (of `Common.List`): `f` is applied to the
/// elements from left to right, and `combine_ty_errs` gets the errors in the
/// order the OCaml builds them: the elements are taken five at a time, the
/// errors of each group in order and the groups from the last to the first
/// (after 1001 groups, the errors of the rest of the elements from the last
/// to the first, before the groups). (The same as the private one of
/// `typing_phase`.)
fn list_map_env_ty_err_opt<E: ?Sized, X, Y, Err, Errs>(
    env: &mut E,
    xs: &[X],
    mut f: impl FnMut(&mut E, &X) -> (Option<Err>, Y),
    combine_ty_errs: impl FnOnce(Vec<Err>) -> Errs,
) -> (Errs, Vec<Y>) {
    // The OCaml list of errors, last element first.
    let mut rev_errs: Vec<Err> = Vec::new();
    let mut ys = Vec::with_capacity(xs.len());
    let mut rest = xs;
    let mut counter = 0;
    loop {
        if rest.is_empty() {
            break;
        }
        let (group, tail) = rest.split_at(std::cmp::min(5, rest.len()));
        let errs: Vec<Option<Err>> = group
            .iter()
            .map(|x| {
                let (err, y) = f(env, x);
                ys.push(y);
                err
            })
            .collect();
        // `ty_err_opt1 :: ... :: ty_err_opt5 :: ty_err_opts`
        rev_errs.extend(errs.into_iter().rev().flatten());
        if tail.is_empty() {
            break;
        }
        if counter > 1000 {
            // `rev_map_env_ty_err_opt env ys ~f ~err:(...)`
            for x in tail {
                let (err, y) = f(env, x);
                ys.push(y);
                rev_errs.extend(err);
            }
            break;
        }
        counter += 1;
        rest = tail;
    }
    rev_errs.reverse();
    (combine_ty_errs(rev_errs), ys)
}

/// `List.zip_exn`
fn zip_exn<A: Clone, B: Clone>(l1: &[A], l2: &[B]) -> Vec<(A, B)> {
    if l1.len() != l2.len() {
        panic!("length mismatch in zip_exn: {} <> {}", l1.len(), l2.len())
    }
    l1.iter().cloned().zip(l2.iter().cloned()).collect()
}

/// The check of `List.fold2_exn`
fn check_fold2_exn_lengths<A, B>(l1: &[A], l2: &[B]) {
    if l1.len() != l2.len() {
        panic!(
            "length mismatch in fold2_exn: {} <> {}",
            l1.len(),
            l2.len()
        )
    }
}

fn add_typing_error_opt(err: Option<&typing_error::T>, env: &Env) {
    if let Some(err) = err {
        typing_error_utils::add_typing_error(err, env)
    }
}

// ---------------------------------------------------------------------------
// call
// ---------------------------------------------------------------------------

/// see .mli
///
/// - `expr_pos`: span of whole call expression e.g. `$x->meth($y)`
/// - `recv_pos`: span of object receiver expression or expression of
///   function type e.g. `$x` in `$x->meth($y)` or `$f` in `$f(3)`
/// - `id_pos`: span of function/method id e.g. `meth` in `$x->meth($y)` or
///   `C::f` in `C::f(5)`
///
/// The OCaml returns `env * (Tast.argument list * Tast.expr option * locl_ty
/// * bool)`.
pub(crate) fn call(
    expected: Option<&expected_ty::T>,
    nullsafe: Option<Option<Pos>>,
    attribute_check_policy: Option<AttributeCheckPolicy>,
    in_await: Option<Reason>,
    dynamic_func: Option<DynFuncKind>,
    expr_pos: &Pos,
    recv_pos: &Pos,
    id_pos: &Pos,
    env: &mut Env,
    fty: Ty,
    el: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
) -> (Vec<tast::Argument>, Option<tast::Expr>, Ty, bool) {
    let nullsafe: Option<Pos> = nullsafe.unwrap_or(None);
    let attribute_check_policy = attribute_check_policy.unwrap_or(AttributeCheckPolicy::CheckAll);
    {
        let env: &Env = env;
        typing_log::log_with_level(env, "typing", 1, || {
            typing_log::log_types(
                &pos_or_decl::of_raw_pos(expr_pos.clone()),
                env,
                &[typing_log::LogStructure::LogHead(
                    format!(
                        "Typing.call {}",
                        match dynamic_func {
                            None => "None",
                            Some(DynFuncKind::SupportdynFunction) => "sd",
                            Some(DynFuncKind::LikeFunction) => "~",
                        }
                    ),
                    vec![typing_log::LogStructure::LogType(
                        "fty".to_string(),
                        fty.clone(),
                    )],
                )],
            )
        });
    }

    // `is_fun_type` reads the environment `call` was given.
    let env_of_call = env.clone();
    let is_fun_type = |ty: &Ty| -> bool {
        let (_, ty) = tutils::strip_supportdyn(&mut env_of_call.clone(), ty.clone());
        match get_node(&ty) {
            Ty_::Tfun(_) => true,
            _ => false,
        }
    };
    // When we enter a like function, it is safe to ignore the like type if we are
    // already in a supportdyn function.
    // Semantically, dyn & (dyn | (t1 -> t2)) = dyn | (dyn & (t1 -> t2) = dyn, and
    // doing this lets us keep like-stripping the arguments
    let to_like_function = |dynamic_func: Option<DynFuncKind>| -> Option<DynFuncKind> {
        match dynamic_func {
            Some(_) => dynamic_func,
            None => Some(DynFuncKind::LikeFunction),
        }
    };
    let tyl = tutils::get_concrete_supertypes(None, Some(false), None, true, env, fty.clone());
    if tyl.is_empty() {
        bad_call(env, expr_pos, &fty);
        let ty_err_opt = call_untyped_unpack(env, get_pos(&fty), unpacked_element);
        let should_forget_fakes = true;
        add_typing_error_opt(ty_err_opt.as_ref(), env);
        let ty = env::fresh_type_error(env, expr_pos.clone());
        (vec![], None, ty, should_forget_fakes)
    } else {
        let fty = inter::intersect_list(env, get_reason(&fty).clone(), &tyl);
        let (ty_err_opt, efty) = typing_solver::expand_type_and_solve(
            env,
            None,
            "a function value",
            expr_pos.clone(),
            fty.clone(),
        );
        add_typing_error_opt(ty_err_opt.as_ref(), env);
        let efty_opt = typing_dynamic_utils::try_strip_dynamic(None, None, env, &efty);
        match efty_opt {
            Some(ty) if is_fun_type(&ty) => call(
                expected,
                Some(nullsafe.clone()),
                Some(attribute_check_policy.clone()),
                in_await.clone(),
                to_like_function(dynamic_func),
                expr_pos,
                recv_pos,
                id_pos,
                env,
                // Preserve the reason off the like type
                with_reason(ty, get_reason(&efty).clone()),
                el,
                unpacked_element,
            ),
            _ => {
                let r = get_reason(&efty).clone();
                match get_node(&efty) {
                    Ty_::Tdynamic(shadow_v_opt) => {
                        let shadow_v_opt: Option<tvid::T> = *shadow_v_opt;
                        // Dynamic inference: calling a dynamic value — create a fresh shadow
                        // type variable for the return type, and record a function-type upper
                        // bound on the callee's shadow. The bound captures the argument types
                        // actually passed:
                        // shadow($d) <: (function(arg_tys...): shadow_ret).
                        let v_ret_opt = match shadow_v_opt {
                            Some(_) => {
                                let v_ret = env::fresh_shadow_tyvar(env, expr_pos.clone());
                                Some(v_ret)
                            }
                            None => None,
                        };
                        let ty = mk((reason::dynamic_call(expr_pos.clone()), Ty_::Tdynamic(v_ret_opt)));
                        let el: Vec<nast::Argument> =
                            // Need to check that the type of the unpacked_element can be,
                            // coerced to dynamic, just like all of the other arguments, in addition
                            // to the check below in call_untyped_unpack, that it is unpackable.
                            // We don't need to unpack and check each type because a tuple is
                            // coercible iff it's constituent types are.
                            match unpacked_element {
                                Some(u) => {
                                    let mut el = el.to_vec();
                                    el.push(aast::Argument::Anormal(u.clone()));
                                    el
                                }
                                None => el.to_vec(),
                            };
                        let expected_arg_ty = expected_ty::make(
                            Some(true),
                            None,
                            expr_pos.clone(),
                            Ureason::URparam,
                            ty.clone(),
                        );
                        let ctxt = context::T {
                            attribute_check_policy: attribute_check_policy.clone(),
                            ..context::default()
                        };
                        let (e1, tel): (Option<typing_error::T>, Vec<tast::Argument>) =
                            list_map_env_ty_err_opt(
                                env,
                                &el,
                                |env: &mut Env, arg: &nast::Argument| {
                                    let (f, te, e_ty): (
                                        Box<dyn FnOnce(tast::Expr) -> tast::Argument>,
                                        tast::Expr,
                                        Ty,
                                    ) = match arg {
                                        aast::Argument::Anormal(elt) => {
                                            let (te, ty) =
                                                expr(Some(&expected_arg_ty), &ctxt, env, elt);
                                            (Box::new(aast::Argument::Anormal), te, ty)
                                        }
                                        aast::Argument::Ainout(iopos, elt) => {
                                            let (te, ty) =
                                                expr(Some(&expected_arg_ty), &ctxt, env, elt);
                                            let aast::Expr(_, pos, _) = elt;
                                            let (_te, _ty) = assign::assign_(
                                                None,
                                                pos,
                                                Ureason::URparamInout,
                                                env,
                                                elt,
                                                pos,
                                                efty.clone(),
                                            );
                                            let iopos = iopos.clone();
                                            (
                                                Box::new(move |e| aast::Argument::Ainout(iopos, e)),
                                                te,
                                                ty,
                                            )
                                        }
                                        aast::Argument::Anamed(name, elt) => {
                                            let (te, ty) =
                                                expr(Some(&expected_arg_ty), &ctxt, env, elt);
                                            let name = name.clone();
                                            (
                                                Box::new(move |e| aast::Argument::Anamed(name, e)),
                                                te,
                                                ty,
                                            )
                                        }
                                    };
                                    let ty_err_opt = sub_type::sub_type(
                                        env,
                                        Some(true),
                                        None,
                                        None,
                                        None,
                                        e_ty.clone(),
                                        ty.clone(),
                                        Some(reasons_callback::unify_error_at(expr_pos.clone())),
                                    );
                                    let ty_mismatch_opt =
                                        mk_ty_mismatch_opt(e_ty, ty.clone(), ty_err_opt.as_ref());
                                    (ty_err_opt, f(hole_on_ty_mismatch(te, ty_mismatch_opt)))
                                },
                                typing_error::multiple_opt,
                            );
                        let e2 = call_untyped_unpack(env, reason::to_pos(&r), unpacked_element);
                        let should_forget_fakes = true;
                        let ty_err_opt = option_merge(e1, e2, typing_error::both);
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                        // Dynamic inference: record the function-type upper bound on the
                        // callee's shadow type variable, capturing the actual arg types.
                        match (shadow_v_opt, v_ret_opt) {
                            (Some(shadow_v), Some(v_ret)) => {
                                let params: Vec<FunParam> = tel
                                    .iter()
                                    .filter_map(|arg| {
                                        let (name_opt, arg_ty) = match arg {
                                            aast::Argument::Anormal(aast::Expr(ty, _, _)) => {
                                                (None, ty.clone())
                                            }
                                            aast::Argument::Ainout(_, aast::Expr(ty, _, _)) => {
                                                (None, ty.clone())
                                            }
                                            aast::Argument::Anamed(
                                                Id(_, name),
                                                aast::Expr(ty, _, _),
                                            ) => (Some(format!("${}", name)), ty.clone()),
                                        };
                                        let named = name_opt.is_some();
                                        Some(FunParam {
                                            pos: PosOrDecl::NONE,
                                            name: name_opt,
                                            type_: arg_ty,
                                            flags: typing_defs_flags::fun_param::make(
                                                false, // inout
                                                false, // accept_disposable
                                                false, // is_optional
                                                false, // readonly
                                                false, // ignore_readonly_error
                                                false, // splat
                                                named,
                                            ),
                                            def_value: None,
                                        })
                                    })
                                    .collect();
                                let ft = FunType {
                                    tparams: vec![],
                                    where_constraints: vec![],
                                    params,
                                    implicit_params: FunImplicitParams {
                                        capability: Capability::CapDefaults(PosOrDecl::NONE),
                                    },
                                    ret: mk((r.clone(), Ty_::Tdynamic(Some(v_ret)))),
                                    flags: typing_defs_flags::fun::make(
                                        FunKind::FSync,
                                        false, // return_disposable
                                        false, // returns_readonly
                                        false, // readonly_this
                                        false, // support_dynamic_type
                                        false, // is_memoized
                                        false, // variadic
                                        false, // named_variadic
                                    ),
                                    instantiated: false,
                                };
                                env::add_tyvar_upper_bound(
                                    None,
                                    env,
                                    shadow_v,
                                    InternalType::LoclType(mk((r.clone(), Ty_::Tfun(std::rc::Rc::new(ft))))),
                                )
                            }
                            _ => {}
                        }
                        (tel, None, ty, should_forget_fakes)
                    }
                    // `(r, ((Tprim Tnull | Tany _ | Tunion [] | Tvar _) as ty))` with its
                    // guard
                    ty_ if match ty_ {
                        Ty_::Tprim(Tprim::Tnull) => nullsafe.is_some(),
                        Ty_::Tvar(_) => tutils::is_tyvar_error(env, &efty),
                        Ty_::Tany(_) => true,
                        Ty_::Tunion(tyl) => tyl.is_empty(),
                        _ => false,
                    } =>
                    {
                        let el: Vec<nast::Argument> = match unpacked_element {
                            Some(u) => {
                                let mut el = el.to_vec();
                                el.push(aast::Argument::Anormal(u.clone()));
                                el
                            }
                            None => el.to_vec(),
                        };
                        let ctxt = context::T {
                            attribute_check_policy: attribute_check_policy.clone(),
                            ..context::default()
                        };
                        let tel: Vec<tast::Argument> = el
                            .iter()
                            .map(|arg| {
                                let (te, _ty) = match arg {
                                    aast::Argument::Anormal(elt) => {
                                        let (te, ty) = expr(None, &ctxt, env, elt);
                                        (aast::Argument::Anormal(te), ty)
                                    }
                                    aast::Argument::Ainout(iopos, elt) => {
                                        let (te, ty) = expr(None, &ctxt, env, elt);
                                        let aast::Expr(_, pos, _) = elt;
                                        let (_te, _ty) = assign::assign_(
                                            None,
                                            pos,
                                            Ureason::URparamInout,
                                            env,
                                            elt,
                                            pos,
                                            efty.clone(),
                                        );
                                        (aast::Argument::Ainout(iopos.clone(), te), ty)
                                    }
                                    aast::Argument::Anamed(name, elt) => {
                                        let (te, ty) = expr(None, &ctxt, env, elt);
                                        (aast::Argument::Anamed(name.clone(), te), ty)
                                    }
                                };
                                te
                            })
                            .collect();
                        let ty_err_opt =
                            call_untyped_unpack(env, reason::to_pos(&r), unpacked_element);
                        let ty = match ty_ {
                            Ty_::Tprim(Tprim::Tnull) => mk((r.clone(), Ty_::Tprim(Tprim::Tnull))),
                            Ty_::Tdynamic(shadow_v_opt) => {
                                // Dynamic inference: same as the Tdynamic call case above — record
                                // a function-type upper bound capturing arg types and return shadow.
                                let result_shadow = match shadow_v_opt {
                                    Some(shadow_v) => {
                                        let shadow_v: tvid::T = *shadow_v;
                                        let v_ret = env::fresh_shadow_tyvar(env, expr_pos.clone());
                                        let params: Vec<FunParam> = tel
                                            .iter()
                                            .filter_map(|arg| {
                                                let (name_opt, arg_ty) = match arg {
                                                    aast::Argument::Anormal(aast::Expr(
                                                        ty,
                                                        _,
                                                        _,
                                                    )) => (None, ty.clone()),
                                                    aast::Argument::Ainout(
                                                        _,
                                                        aast::Expr(ty, _, _),
                                                    ) => (None, ty.clone()),
                                                    aast::Argument::Anamed(
                                                        Id(_, name),
                                                        aast::Expr(ty, _, _),
                                                    ) => (Some(format!("${}", name)), ty.clone()),
                                                };
                                                let named = name_opt.is_some();
                                                Some(FunParam {
                                                    pos: PosOrDecl::NONE,
                                                    name: name_opt,
                                                    type_: arg_ty,
                                                    flags: typing_defs_flags::fun_param::make(
                                                        false, // inout
                                                        false, // accept_disposable
                                                        false, // is_optional
                                                        false, // readonly
                                                        false, // ignore_readonly_error
                                                        false, // splat
                                                        named,
                                                    ),
                                                    def_value: None,
                                                })
                                            })
                                            .collect();
                                        let ft = FunType {
                                            tparams: vec![],
                                            where_constraints: vec![],
                                            params,
                                            implicit_params: FunImplicitParams {
                                                capability: Capability::CapDefaults(
                                                    PosOrDecl::NONE,
                                                ),
                                            },
                                            ret: mk((r.clone(), Ty_::Tdynamic(Some(v_ret)))),
                                            flags: typing_defs_flags::fun::make(
                                                FunKind::FSync,
                                                false, // return_disposable
                                                false, // returns_readonly
                                                false, // readonly_this
                                                false, // support_dynamic_type
                                                false, // is_memoized
                                                false, // variadic
                                                false, // named_variadic
                                            ),
                                            instantiated: false,
                                        };
                                        env::add_tyvar_upper_bound(
                                            None,
                                            env,
                                            shadow_v,
                                            InternalType::LoclType(mk((
                                                r.clone(),
                                                Ty_::Tfun(std::rc::Rc::new(ft)),
                                            ))),
                                        );
                                        Some(v_ret)
                                    }
                                    None => None,
                                };
                                mk((
                                    reason::dynamic_call(expr_pos.clone()),
                                    Ty_::Tdynamic(result_shadow),
                                ))
                            }
                            Ty_::Tvar(_) if tutils::is_tyvar_error(env, &efty) => {
                                env::fresh_type_error(env, expr_pos.clone())
                            }
                            // `Tunion []` and `_` (should not happen!)
                            _ => mk((r.clone(), Ty_::Tunion(vec![]))),
                        };
                        let should_forget_fakes = true;
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                        (tel, None, ty, should_forget_fakes)
                    }
                    Ty_::Tunion(tyl) if tyl.len() == 1 => call(
                        expected,
                        Some(nullsafe.clone()),
                        Some(attribute_check_policy.clone()),
                        in_await.clone(),
                        dynamic_func,
                        expr_pos,
                        recv_pos,
                        id_pos,
                        env,
                        tyl[0].clone(),
                        el,
                        unpacked_element,
                    ),
                    Ty_::Tunion(tyl) => {
                        let saved_locals = env.lenv.per_cont_env.clone();
                        let resl: Vec<(Vec<tast::Argument>, Option<tast::Expr>, Ty, bool)> = tyl
                            .iter()
                            .map(|ty| {
                                env::env_with_locals(env, saved_locals.clone());
                                call(
                                    expected,
                                    Some(nullsafe.clone()),
                                    Some(attribute_check_policy.clone()),
                                    in_await.clone(),
                                    dynamic_func,
                                    expr_pos,
                                    recv_pos,
                                    id_pos,
                                    env,
                                    ty.clone(),
                                    el,
                                    unpacked_element,
                                )
                            })
                            .collect();
                        let should_forget_fakes = resl.iter().any(|(_, _, _, forget)| *forget);
                        let retl: Vec<Ty> = resl.iter().map(|(_, _, x, _)| x.clone()).collect();
                        let ty = typing_union::union_list(env, None, r.clone(), &retl);
                        // We shouldn't be picking arbitrarily for the TAST here, as TAST checks
                        // depend on the types inferred. Here's we're preserving legacy behaviour
                        // by picking the last one.
                        // TODO: don't do this, instead use subtyping to push unions
                        // through function types
                        let (tel, typed_unpack_element, _, _) =
                            resl.into_iter().last().expect("List.hd_exn");
                        (tel, typed_unpack_element, ty, should_forget_fakes)
                    }
                    Ty_::Tintersection(tyl) => {
                        let resl: Vec<(Vec<tast::Argument>, Option<tast::Expr>, Ty, bool)> =
                            tutils::run_on_intersection(
                                env,
                                |env: &mut Env, ty: &Ty| {
                                    call(
                                        expected,
                                        Some(nullsafe.clone()),
                                        Some(attribute_check_policy.clone()),
                                        in_await.clone(),
                                        dynamic_func,
                                        expr_pos,
                                        recv_pos,
                                        id_pos,
                                        env,
                                        ty.clone(),
                                        el,
                                        unpacked_element,
                                    )
                                },
                                tyl,
                            );
                        let should_forget_fakes = resl.iter().all(|(_, _, _, forget)| *forget);
                        let retl: Vec<Ty> = resl.iter().map(|(_, _, x, _)| x.clone()).collect();
                        let ty = inter::intersect_list(env, r.clone(), &retl);
                        // We shouldn't be picking arbitrarily for the TAST here, as TAST checks
                        // depend on the types inferred. Here we're preserving legacy behaviour
                        // by picking the last one.
                        // TODO: don't do this, instead use subtyping to push intersections
                        // through function types
                        let (tel, typed_unpack_element, _, _) =
                            resl.into_iter().last().expect("List.hd_exn");
                        (tel, typed_unpack_element, ty, should_forget_fakes)
                    }
                    Ty_::Tfun(ft) => {
                        let r2 = r.clone();
                        let ft: FunType = FunType::clone(&ft);
                        // Instantiate polymorphic function types
                        let ft = if ft.instantiated {
                            ft
                        } else {
                            let (err_opt, ft) =
                                sub_type::instantiate_fun_type(expr_pos.clone(), ft, env);
                            add_typing_error_opt(err_opt.as_ref(), env);
                            ft
                        };

                        // Typing of format string functions. It is dependent on the arguments (el)
                        // so it cannot be done earlier.
                        let pos_def = reason::to_pos(&r2);
                        let ft = typing_exts::retype_magic_func(env, ft, el);
                        let (positive_return_vars, negative_return_vars) =
                            env::get_tyvars(env, &ft.ret);
                        // (`covariant_return_vars`, `Tvid.Set.diff positive negative`,
                        // and the set of `current_call_vars` are only read by
                        // `relevant_ambiguous_shape_splat_vars`, in the rare
                        // ambiguous case: it tests membership in them instead.)
                        let current_call_vars: Vec<tvid::T> = env::get_current_tyvars(env);
                        // Split off the named-variadic (if any) so it doesn't get treated
                        // as either a positional variadic or a required named parameter.
                        // Unmatched named arguments will fall through to it below.
                        let named_variadic_param: Option<FunParam> =
                            ft_named_variadic_param(&ft).cloned();
                        // (Without a named variadic it is `ft` itself: borrowed.)
                        let ft_without_named_variadic_owned;
                        let ft_without_named_variadic: &FunType = match &named_variadic_param {
                            Some(_) => {
                                ft_without_named_variadic_owned = FunType {
                                    params: ft_params_without_named_variadic(&ft).to_vec(),
                                    ..ft.clone()
                                };
                                &ft_without_named_variadic_owned
                            }
                            None => &ft,
                        };
                        let (non_variadic_non_splat_params, variadic_or_splat_param) =
                            get_variadic_or_splat_param(ft_without_named_variadic);

                        // (`indexed_non_variadic_non_splat_params` is not built: the
                        // two below are taken from the parameters with their index.)
                        let indexed_non_variadic_non_splat_params = || {
                            non_variadic_non_splat_params
                                .iter()
                                .enumerate()
                                .map(|(idx, param)| (idx as isize, param))
                        };
                        let positional_non_variadic_non_splat_params: Vec<(isize, FunParam)> =
                            indexed_non_variadic_non_splat_params()
                                .filter(|(_, param)| {
                                    !typing_defs_flags::fun_param::named(param.flags)
                                })
                                .map(|(idx, param)| (idx, param.clone()))
                                .collect();
                        let named_params: NamedParams = {
                            // (A copy of the shared empty map: most calls have no
                            // named parameter, and `new` allocates a node.)
                            let mut named_params: NamedParams = EMPTY_NAMED_PARAMS.with(Clone::clone);
                            for (idx, fp) in indexed_non_variadic_non_splat_params() {
                                match named_params::name_of_named_param(fp) {
                                    Some(name) => {
                                        named_params.insert(name, (idx, fp.clone()));
                                    }
                                    None => {}
                                }
                            }
                            named_params
                        };
                        let relevant_ambiguous_shape_splat_vars = |vars: &TvidSet| -> TvidSet {
                            // `vars ∩ ((positive \ negative) ∩ current_call_vars)`
                            vars.iter()
                                .filter(|v| {
                                    positive_return_vars.contains(v)
                                        && !negative_return_vars.contains(v)
                                        && current_call_vars.contains(v)
                                })
                                .cloned()
                                .collect()
                        };
                        // Our use of bidirectional typing can interact badly with functions
                        // returning shape splats involving multiple type variables causing
                        // incompleteness. To avoid this we detect ambiguous cases and
                        // defer propagating expected type information inwards
                        let initial_deferred_spread_vars: Option<TvidSet> = {
                            let check_result = check_call_result_against_expected_type(
                                "Call result",
                                env,
                                &ft.ret,
                                expected,
                            );
                            match check_result {
                                // `Result.fold result ~ok:Fn.id ~error:Fn.id`: the
                                // environment of the check either way.
                                ExpectedTypeCheck::ExpectedChecked(_result) => None,
                                ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(vars) => {
                                    let vars = relevant_ambiguous_shape_splat_vars(&vars);
                                    if vars.is_empty() {
                                        check_expected_ty("Call result", env, &ft.ret, expected);
                                        None
                                    } else {
                                        Some(vars)
                                    }
                                }
                            }
                        };
                        env::set_tyvar_variance(env, None, None, &ft.ret);
                        let deferred_spread_vars: RefCell<Option<TvidSet>> =
                            RefCell::new(initial_deferred_spread_vars);
                        let solve_deferred_spread_vars =
                            |final_: bool, env: &mut Env, spread_vars: &TvidSet| {
                                // `Tvid.Set.fold`, in increasing order; the errors are
                                // consed (`err :: errs`).
                                let mut ty_err_opts: Vec<Option<typing_error::T>> = vec![];
                                for var in spread_vars.iter() {
                                    let var: tvid::T = *var;
                                    let lower_bounds = env::get_tyvar_lower_bounds(env, var);
                                    if internal_type_set::is_empty(&lower_bounds) {
                                    } else {
                                        let var_pos = env::get_tyvar_pos(env, var);
                                        let var_reason = reason::witness(var_pos.clone());
                                        let err = if final_ {
                                            let (err, _) = typing_solver::expand_type_and_solve(
                                                env,
                                                Some(false),
                                                "a shape spread inferred from call arguments",
                                                var_pos,
                                                mk((var_reason, Ty_::Tvar(var))),
                                            );
                                            err
                                        } else {
                                            typing_solver::solve_to_equal_bound_or_wrt_variance(
                                                env, var_reason, var,
                                            )
                                        };
                                        ty_err_opts.push(err);
                                    }
                                }
                                ty_err_opts.reverse();
                                add_typing_error_opt(
                                    typing_error::multiple_opt(
                                        ty_err_opts.into_iter().flatten().collect(),
                                    )
                                    .as_ref(),
                                    env,
                                );
                            };
                        let check_deferred_expected = |final_: bool, env: &mut Env| {
                            let spread_vars_opt: Option<TvidSet> =
                                deferred_spread_vars.borrow().clone();
                            match spread_vars_opt {
                                None => {}
                                Some(spread_vars) => {
                                    solve_deferred_spread_vars(final_, env, &spread_vars);
                                    if final_ {
                                        *deferred_spread_vars.borrow_mut() = None;
                                        check_expected_ty("Call result", env, &ft.ret, expected)
                                    } else {
                                        // A pass-2 lambda may make the next probe unambiguous.
                                        let check_result = check_call_result_against_expected_type(
                                            "Call result",
                                            env,
                                            &ft.ret,
                                            expected,
                                        );
                                        match check_result {
                                            ExpectedTypeCheck::ExpectedChecked(_result) => {
                                                *deferred_spread_vars.borrow_mut() = None;
                                            }
                                            ExpectedTypeCheck::ExpectedAmbiguousShapeSplat(
                                                vars,
                                            ) => {
                                                let vars =
                                                    relevant_ambiguous_shape_splat_vars(&vars);
                                                if vars.is_empty() {
                                                    *deferred_spread_vars.borrow_mut() = None;
                                                    check_expected_ty(
                                                        "Call result",
                                                        env,
                                                        &ft.ret,
                                                        expected,
                                                    )
                                                } else {
                                                    *deferred_spread_vars.borrow_mut() =
                                                        Some(vars);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        };
                        fn set_tyvar_variance_from_lambda_param(
                            env: &mut Env,
                            opt_param: Option<&FunParam>,
                        ) {
                            match opt_param {
                                Some(param) => {
                                    fn set_params_variance(env: &mut Env, ty: Ty) {
                                        let ty = typing_dynamic_utils::strip_dynamic(env, ty);
                                        let (_, ty) = tutils::strip_supportdyn(env, ty);
                                        let ty = env::expand_type(env, ty);
                                        match get_node(&ty) {
                                            Ty_::Tunion(tyl) if tyl.len() == 1 => {
                                                set_params_variance(env, tyl[0].clone())
                                            }
                                            Ty_::Toption(ty) => set_params_variance(env, ty.clone()),
                                            Ty_::Tfun(ft) => {
                                                for param in &ft.params {
                                                    env::set_tyvar_variance(
                                                        env,
                                                        None,
                                                        None,
                                                        &param.type_,
                                                    )
                                                }
                                                env::set_tyvar_variance(
                                                    env,
                                                    Some(true),
                                                    None,
                                                    &ft.ret,
                                                )
                                            }
                                            _ => {}
                                        }
                                    }
                                    set_params_variance(env, param.type_.clone())
                                }
                                None => {}
                            }
                        }
                        // Simply checking argument expressions from left-to-right produces poor
                        // results from inference, with too many programs rejected because unknown
                        // types can not be determined or are not solved with enough precision.
                        // So instead we traverse the arguments in three passes.
                        //
                        // Pass 0. We first check lambda expression arguments for which all lambda parameters
                        // have an explicit type hint. If we don't do this then Hack sometimes infers
                        // a like-type for a generic parameter where a non-like-type would be better.
                        //
                        // Pass 1. Next, we check all non-lambda arguments, in order to get as much information
                        // about generic type parameters that might appear in the types of
                        // lambda arguments.
                        //
                        // Pass 2. Finally, we check the remaining lambda arguments.
                        fn check_pass_and_set_tyvar_variance(
                            pass: isize,
                            env: &mut Env,
                            arg: &nast::Argument,
                            opt_param: Option<&FunParam>,
                        ) -> bool {
                            match arg {
                                aast::Argument::Anormal(aast::Expr(_, _, e))
                                | aast::Argument::Anamed(_, aast::Expr(_, _, e)) => {
                                    let lambda_params: Option<&[nast::FunParam]> = match e {
                                        aast::Expr_::Efun(efun) => Some(&efun.fun.params),
                                        aast::Expr_::Lfun(lfun) => Some(&lfun.0.params),
                                        _ => None,
                                    };
                                    match lambda_params {
                                        // We first check lambdas that have fully explicit parameters
                                        Some(f_params)
                                            if f_params
                                                .iter()
                                                .all(|param| param.type_hint.1.is_some()) =>
                                        {
                                            pass == 0
                                        }
                                        // Lastly we check lambdas that have some parameters whose types must be inferred
                                        Some(_) => {
                                            // On the first pass we need to set the type variable variance
                                            if pass == 0 {
                                                set_tyvar_variance_from_lambda_param(env, opt_param);
                                                false
                                            } else {
                                                pass == 2
                                            }
                                        }
                                        // Second we check non-lambdas
                                        None => pass == 1,
                                    }
                                }
                                aast::Argument::Ainout(_, _) => pass == 1,
                            }
                        }
                        let is_single_argument = el.len() == 1;
                        /// The OCaml returns `(idx, (is_variadic, opt_param,
                        /// named_params_remaining,
                        /// remaining_positional_non_variadic_non_splat_params))`;
                        /// the remaining positional parameters are a suffix of
                        /// the positional ones.
                        fn get_next_positional_param_info<'a>(
                            non_variadic_non_splat_params: &[FunParam],
                            variadic_or_splat_param: &Option<SplatOrVariadic>,
                            named_params_remaining: NamedParams,
                            remaining_positional_non_variadic_non_splat_params: &'a [(
                                isize,
                                FunParam,
                            )],
                        ) -> (
                            isize,
                            (
                                bool,
                                Option<FunParam>,
                                NamedParams,
                                &'a [(isize, FunParam)],
                            ),
                        ) {
                            match remaining_positional_non_variadic_non_splat_params {
                                [
                                    (idx, param),
                                    remaining_positional_non_variadic_non_splat_params @ ..,
                                ] => (
                                    *idx,
                                    (
                                        false,
                                        Some(param.clone()),
                                        named_params_remaining,
                                        remaining_positional_non_variadic_non_splat_params,
                                    ),
                                ),
                                [] => match variadic_or_splat_param {
                                    Some(SplatOrVariadic::Variadic(param)) => (
                                        non_variadic_non_splat_params.len() as isize,
                                        (
                                            true,
                                            Some(param.clone()),
                                            named_params_remaining,
                                            remaining_positional_non_variadic_non_splat_params,
                                        ),
                                    ),
                                    Some(SplatOrVariadic::Splat(_)) | None => (
                                        -1,
                                        (
                                            true,
                                            None,
                                            named_params_remaining,
                                            remaining_positional_non_variadic_non_splat_params,
                                        ),
                                    ),
                                },
                            }
                        }
                        fn get_next_named_param_info<'a>(
                            non_variadic_non_splat_params: &[FunParam],
                            variadic_or_splat_param: &Option<SplatOrVariadic>,
                            named_variadic_param: &Option<FunParam>,
                            name: &str,
                            named_params_remaining: NamedParams,
                            remaining_positional_non_variadic_non_splat_params: &'a [(
                                isize,
                                FunParam,
                            )],
                        ) -> (
                            isize,
                            (
                                bool,
                                Option<FunParam>,
                                NamedParams,
                                &'a [(isize, FunParam)],
                            ),
                        ) {
                            match named_params_remaining.get(name).cloned() {
                                Some((idx, param)) => (
                                    idx,
                                    (
                                        false,
                                        Some(param),
                                        named_params_remaining.without(name),
                                        remaining_positional_non_variadic_non_splat_params,
                                    ),
                                ),
                                None => {
                                    // No matching declared name — if the callee has a named
                                    // variadic, use it so the argument's type is still checked
                                    // against the variadic's element type.
                                    match named_variadic_param {
                                        Some(param) => (
                                            non_variadic_non_splat_params.len() as isize
                                                + match variadic_or_splat_param {
                                                    Some(_) => 1,
                                                    None => 0,
                                                },
                                            (
                                                true,
                                                Some(param.clone()),
                                                named_params_remaining,
                                                remaining_positional_non_variadic_non_splat_params,
                                            ),
                                        ),
                                        None => (
                                            -1,
                                            (
                                                true,
                                                None,
                                                named_params_remaining,
                                                remaining_positional_non_variadic_non_splat_params,
                                            ),
                                        ),
                                    }
                                }
                            }
                        }
                        let ctxt = context::T {
                            attribute_check_policy: attribute_check_policy.clone(),
                            ..context::default()
                        };
                        let check_arg = |env: &mut Env,
                                         arg: &nast::Argument,
                                         opt_param: Option<&FunParam>,
                                         arg_idx: isize,
                                         param_idx: isize,
                                         is_variadic: bool|
                         -> (
                            Option<(tast::Argument, Ty)>,
                            Option<(PosOrDecl, Ty)>,
                        ) {
                            let (arg_name, param_kind, e) = match arg {
                                aast::Argument::Anormal(e) => (None, ParamKind::Pnormal, e),
                                aast::Argument::Ainout(pos, e) => {
                                    (None, ParamKind::Pinout(pos.clone()), e)
                                }
                                aast::Argument::Anamed(arg_name, e) => {
                                    (Some(arg_name.clone()), ParamKind::Pnormal, e)
                                }
                            };
                            match opt_param {
                                Some(param) => {
                                    let ety = param.type_.clone();
                                    let ety = env::expand_type(env, ety);
                                    typing_class_pointers::check_string_coercion_point(
                                        env, e, &ety,
                                    );
                                    let (te, ty) = {
                                        // Expected type has a like type for checking arguments
                                        // to supportdyn functions
                                        let pess_type = match dynamic_func {
                                            Some(DynFuncKind::SupportdynFunction) => {
                                                typing_array_access::pessimise_type(
                                                    env,
                                                    param.type_.clone(),
                                                )
                                            }
                                            _ => param.type_.clone(),
                                        };
                                        let expected = expected_ty::make(
                                            None,
                                            Some(get_fp_ignore_readonly_error(param)),
                                            aast_utils::get_expr_pos(e),
                                            Ureason::URparam,
                                            pess_type,
                                        );
                                        expr(
                                            Some(&expected),
                                            &context::T {
                                                attribute_check_policy: attribute_check_policy
                                                    .clone(),
                                                accept_using_var: get_fp_accept_disposable(param),
                                                ..context::default()
                                            },
                                            env,
                                            e,
                                        )
                                    };
                                    // If we were using our function subtyping code to handle calls
                                    // we would have a contravariant function arg projection so
                                    // replicate that here
                                    let r_sup = reason::witness(expr_pos.clone());
                                    let update_reason = |r_sup_prj: Reason| -> Reason {
                                        reason::prj_fn_param(
                                            get_reason(&fty).clone(),
                                            r_sup.clone(),
                                            r_sup_prj,
                                            param_idx,
                                            arg_idx,
                                        )
                                    };

                                    let ty = env::update_reason(env, ty, &update_reason);

                                    // We have to update the type on the expression too rather
                                    // than use the type above since it may be different for certain
                                    // special functions
                                    let te = {
                                        let aast::Expr(ty, pos, e) = te;
                                        let ty = env::update_reason(env, ty, &update_reason);
                                        aast::Expr(ty, pos, e)
                                    };
                                    let (ty_mismatch_opt, used_dynamic_info) =
                                        check_argument_type_against_parameter(
                                            Some(is_single_argument),
                                            dynamic_func,
                                            env,
                                            param,
                                            &param_kind,
                                            (e, ty.clone()),
                                            is_variadic,
                                        );
                                    (
                                        Some((
                                            aast_utils::expr_to_arg(
                                                param_kind,
                                                arg_name,
                                                hole_on_ty_mismatch(te, ty_mismatch_opt),
                                            ),
                                            ty,
                                        )),
                                        used_dynamic_info,
                                    )
                                }
                                None => {
                                    let (te, ty) = expr(None, &ctxt, env, e);
                                    // If we were using our function subtyping code to handle calls
                                    // we would have a contravariant function arg projection so
                                    // replicate that here
                                    let r_sup = reason::witness(expr_pos.clone());
                                    let update_reason = |r_sup_prj: Reason| -> Reason {
                                        reason::prj_fn_param(
                                            get_reason(&fty).clone(),
                                            r_sup.clone(),
                                            r_sup_prj,
                                            param_idx,
                                            arg_idx,
                                        )
                                    };

                                    let ty = env::update_reason(env, ty, &update_reason);

                                    // We have to update the type on the expression too rather
                                    // than use the type above since it may be different for certain
                                    // special functions
                                    let te = {
                                        let aast::Expr(ty, pos, e) = te;
                                        let ty = env::update_reason(env, ty, &update_reason);
                                        aast::Expr(ty, pos, e)
                                    };
                                    (
                                        Some((aast_utils::expr_to_arg(param_kind, arg_name, te), ty)),
                                        None,
                                    )
                                }
                            }
                        };
                        // `type arg_with_result = int * Nast.argument * (Tast.argument * locl_ty) option`
                        type ArgWithResult<'a> =
                            (isize, &'a nast::Argument, Option<(tast::Argument, Ty)>);
                        // We return the first position of a dynamic check that was used
                        fn combine_dynamic_info(
                            d1: Option<(PosOrDecl, Ty)>,
                            d2: Option<(PosOrDecl, Ty)>,
                        ) -> Option<(PosOrDecl, Ty)> {
                            if d1.is_some() { d1 } else { d2 }
                        }
                        // For a given pass number, check arguments from left-to-right that correspond
                        // to this pass. If any arguments remain unprocessed, bump the pass number
                        // and repeat.
                        //
                        // `check_args` is tail-recursive: each pass is an iteration of
                        // the loop, which starts again with all the named and
                        // positional parameters, as the OCaml's recursive call does.
                        // It returns `(tel, argtys, used_dynamic_acc,
                        // remaining_positional_non_variadic_non_splat_params)`.
                        let check_args = |pass: isize,
                                          env: &mut Env,
                                          args_with_result: Vec<ArgWithResult<'_>>,
                                          used_dynamic_acc: Option<(PosOrDecl, Ty)>|
                         -> (
                            Vec<tast::Argument>,
                            Vec<(Pos, Ty)>,
                            Option<(PosOrDecl, Ty)>,
                            &[(isize, FunParam)],
                        ) {
                            let mut pass = pass;
                            let mut args_with_result = args_with_result;
                            let mut used_dynamic_acc = used_dynamic_acc;
                            loop {
                                let mut named_params_remaining: NamedParams = named_params.clone();
                                let mut remaining_positional_non_variadic_non_splat_params: &[(
                                    isize,
                                    FunParam,
                                )] = &positional_non_variadic_non_splat_params;
                                // In the order of the arguments (the OCaml's `acc`, reversed).
                                let mut acc: Vec<ArgWithResult<'_>> =
                                    Vec::with_capacity(args_with_result.len());
                                // We've got an argument
                                for (arg_idx, arg, opt_result) in args_with_result {
                                    // Pick up next parameter type info
                                    let (
                                        param_idx,
                                        (
                                            is_variadic,
                                            opt_param,
                                            named_params_remaining_,
                                            remaining_positional_non_variadic_non_splat_params_,
                                        ),
                                    ) = match arg {
                                        aast::Argument::Ainout(_, _) | aast::Argument::Anormal(_) => {
                                            get_next_positional_param_info(
                                                &non_variadic_non_splat_params,
                                                &variadic_or_splat_param,
                                                named_params_remaining,
                                                remaining_positional_non_variadic_non_splat_params,
                                            )
                                        }
                                        aast::Argument::Anamed(Id(_, name), _) => {
                                            get_next_named_param_info(
                                                &non_variadic_non_splat_params,
                                                &variadic_or_splat_param,
                                                &named_variadic_param,
                                                name,
                                                named_params_remaining,
                                                remaining_positional_non_variadic_non_splat_params,
                                            )
                                        }
                                    };
                                    named_params_remaining = named_params_remaining_;
                                    remaining_positional_non_variadic_non_splat_params =
                                        remaining_positional_non_variadic_non_splat_params_;
                                    let (one_result, used_dynamic_info) = {
                                        // If we're on the pass appropriate for this argument
                                        // expression, then check it
                                        let check_on_this_pass = check_pass_and_set_tyvar_variance(
                                            pass,
                                            env,
                                            arg,
                                            opt_param.as_ref(),
                                        );
                                        // Earlier arguments can make the expected-type relation
                                        // unambiguous before an inferred lambda needs its context.
                                        if pass >= 2 && check_on_this_pass {
                                            check_deferred_expected(false, env)
                                        }
                                        if check_on_this_pass {
                                            check_arg(
                                                env,
                                                arg,
                                                opt_param.as_ref(),
                                                arg_idx,
                                                param_idx,
                                                is_variadic,
                                            )
                                        } else {
                                            (opt_result, None)
                                        }
                                    };
                                    used_dynamic_acc =
                                        combine_dynamic_info(used_dynamic_acc, used_dynamic_info);
                                    acc.push((arg_idx, arg, one_result));
                                }
                                // `collect_results`, which reads the results from the last
                                // one: if one is missing we've still not finished, so bump
                                // pass and iterate.
                                if acc.iter().any(|(_, _, opt_result)| opt_result.is_none()) {
                                    pass += 1;
                                    args_with_result = acc;
                                    continue;
                                }
                                let mut tel: Vec<tast::Argument> = Vec::with_capacity(acc.len());
                                let mut argtys: Vec<(Pos, Ty)> = Vec::with_capacity(acc.len());
                                for (_, _, opt_result) in acc {
                                    let (te, ty) = opt_result.unwrap();
                                    argtys.push((aast_utils::get_argument_pos(&te), ty));
                                    tel.push(te);
                                }
                                return (
                                    tel,
                                    argtys,
                                    used_dynamic_acc,
                                    remaining_positional_non_variadic_non_splat_params,
                                );
                            }
                        };
                        // Same as above, but checks the types of the implicit arguments, which are
                        // read from the context
                        let check_implicit_args = |env: &mut Env| -> Option<typing_error::T> {
                            let capability =
                                typing_coeffects::get_type(&ft.implicit_params.capability);
                            {
                                let env_capability = env::get_local_check_defined(
                                    env,
                                    &aast::Lid(expr_pos.clone(), typing_coeffects::capability_id()),
                                )
                                .ty;
                                let base_error =
                                    primary::T::Coeffect(primary::coeffect::T::Call_coeffect {
                                        pos: id_pos.clone(),
                                        available_incl_unsafe: typing_coeffects::pretty(
                                            env,
                                            &env_capability,
                                        ),
                                        available_pos: get_pos(&env_capability),
                                        required_pos: get_pos(&capability),
                                        required: typing_coeffects::pretty(env, &capability),
                                    });
                                typing_ops::sub_type(None, 
                                    expr_pos.clone(),
                                    Ureason::URnone,
                                    env,
                                    env_capability,
                                    capability,
                                    callback::always(base_error),
                                )
                            }
                        };
                        let should_forget_fakes = {
                            // If the function doesn't have write priveleges to properties, fake
                            // members cannot be reassigned, so their refinements stand.
                            let capability =
                                typing_coeffects::get_type(&ft.implicit_params.capability);
                            sub_type::is_sub_type(
                                env,
                                &capability,
                                &make_type::capability(
                                    reason::none(),
                                    missing_special_names::capabilities::WRITE_PROPERTY
                                        .to_string(),
                                ),
                            )
                        };

                        // Pair argument expressions with the result of checking the expression,
                        // initially set to None
                        let args_with_result: Vec<ArgWithResult<'_>> = el
                            .iter()
                            .enumerate()
                            .map(|(idx, e)| (idx as isize, e, None))
                            .collect();
                        let (
                            tel,
                            argtys,
                            used_dynamic_info1,
                            remaining_positional_non_variadic_non_splat_params,
                        ) = check_args(0, env, args_with_result, None);
                        let ty_err_opt = check_implicit_args(env);
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                        let (typed_unpack_element, arity, did_unpack, used_dynamic_info2): (
                            Option<tast::Expr>,
                            isize,
                            bool,
                            Option<(PosOrDecl, Ty)>,
                        ) = match &variadic_or_splat_param {
                            Some(SplatOrVariadic::Splat(splat_param)) => {
                                // For the special case that the last parameter of the function is a type-splat, e.g.
                                //   function foo(t1 $x1, ..., tm $xm, `...`t $x) { _ }
                                // we have either
                                // (1) A call with a expression-splat (unpacked element)
                                //   foo($y1, ... $yn, `...`$y)
                                // Supposing that $yi have types ui, and $y has type u, we just need to assert
                                //      (u1, ..., un, `...`u) <: (t1, ..., tm, `...`t)
                                // and let type-splat subtyping take its course.
                                // (2) OR a call without an expression-splat
                                //   foo($y1, ..., $yn)
                                //  Supposing that $yi have types yi, we just need to assert
                                //    (u1, ..., un) <: (t1, ..., tm, `...`t)
                                let (consumed, required_params, optional_params) =
                                    split_remaining_params_required_optional(
                                        &positional_non_variadic_non_splat_params,
                                        remaining_positional_non_variadic_non_splat_params,
                                    );
                                let positional_argtys_with_pos: Vec<(Pos, Ty)> =
                                    // zip_exn is safe because check_args guarantees el and argtys are same length
                                    zip_exn(el, &argtys)
                                        .into_iter()
                                        .filter_map(|(arg, argty)| match arg {
                                            aast::Argument::Anamed(_, _) => None,
                                            aast::Argument::Anormal(_)
                                            | aast::Argument::Ainout(_, _) => Some(argty),
                                        })
                                        .collect();
                                // `List.drop`
                                let remaining_positional_argtys_with_pos: Vec<(Pos, Ty)> =
                                    positional_argtys_with_pos
                                        .iter()
                                        .skip(std::cmp::max(consumed, 0) as usize)
                                        .cloned()
                                        .collect();
                                let remaining_positional_argtys: Vec<Ty> =
                                    remaining_positional_argtys_with_pos
                                        .iter()
                                        .map(|(_, ty)| ty.clone())
                                        .collect();
                                let (actual_ty, opt_te, remaining_pos) = match unpacked_element {
                                    None => {
                                        // Compute a span for the remaining args
                                        let remaining_pos = match (
                                            remaining_positional_argtys_with_pos.first(),
                                            remaining_positional_argtys_with_pos.last(),
                                        ) {
                                            (Some((pos1, _)), Some((pos2, _))) => {
                                                crate::pos::btw(pos1, pos2)
                                            }
                                            // We have no more arguments so just use position of function id
                                            _ => id_pos.clone(),
                                        };
                                        (
                                            make_type::tuple(
                                                reason::witness(remaining_pos.clone()),
                                                remaining_positional_argtys,
                                            ),
                                            None,
                                            remaining_pos,
                                        )
                                    }
                                    Some(e) => {
                                        let aast::Expr(_, splat_pos, _) = e;
                                        let (te, unpacked_element_ty) =
                                            expr(None, &ctxt, env, e);
                                        (
                                            mk((
                                                reason::witness(splat_pos.clone()),
                                                Ty_::Ttuple(TupleType {
                                                    required: remaining_positional_argtys,
                                                    optional: vec![],
                                                    extra: TupleExtra::Tsplat(unpacked_element_ty),
                                                }),
                                            )),
                                            Some(te),
                                            splat_pos.clone(),
                                        )
                                    }
                                };
                                let expected_ty = mk((
                                    reason::witness_from_decl(splat_param.pos.clone()),
                                    Ty_::Ttuple(TupleType {
                                        required: required_params
                                            .iter()
                                            .map(|(_, fp)| fp.type_.clone())
                                            .collect(),
                                        optional: optional_params
                                            .iter()
                                            .map(|(_, fp)| fp.type_.clone())
                                            .collect(),
                                        extra: TupleExtra::Tsplat(splat_param.type_.clone()),
                                    }),
                                ));
                                let (_ty_err_opt, used_dynamic) =
                                    typing_argument::check_argument_type_against_parameter_type(
                                        None,
                                        None,
                                        dynamic_func,
                                        false,
                                        env,
                                        expected_ty,
                                        remaining_pos,
                                        actual_ty.clone(),
                                    );
                                let used_dynamic_info = if used_dynamic {
                                    Some((splat_param.pos.clone(), actual_ty))
                                } else {
                                    None
                                };
                                (
                                    opt_te,
                                    positional_argtys_with_pos.len() as isize
                                        + remaining_positional_non_variadic_non_splat_params.len()
                                            as isize,
                                    true,
                                    used_dynamic_info,
                                )
                            }
                            None | Some(SplatOrVariadic::Variadic(_)) => match unpacked_element {
                                None => {
                                    let positional_args: Vec<&nast::Argument> = el
                                        .iter()
                                        .filter(|arg| match arg {
                                            aast::Argument::Anamed(_, _) => false,
                                            _ => true,
                                        })
                                        .collect();
                                    (None, positional_args.len() as isize, false, None)
                                }
                                Some(e) => {
                                    let (consumed, required_params, optional_params) =
                                        split_remaining_params_required_optional(
                                            &positional_non_variadic_non_splat_params,
                                            remaining_positional_non_variadic_non_splat_params,
                                        );
                                    let (te, unpacked_element_ty) = expr(None, &ctxt, env, e);
                                    // Construct a constraint for the remaining positional parameters and
                                    // `variadic_or_splat_param`, if present. For example, given
                                    //
                                    // function f(int $i, string $j, float $k = 3.14, mixed ...$m): void {}
                                    // function g((string, float, bool) $t): void {
                                    //   f(3, ...$t);
                                    // }
                                    //
                                    // the constraint type we want is splat([#1], [opt#2], #3).
                                    let aast::Expr(_, p1, _) = e;
                                    let (d_required, d_optional, d_variadic) =
                                        generate_splat_type_vars(
                                            env,
                                            p1,
                                            &required_params,
                                            &optional_params,
                                            &variadic_or_splat_param,
                                        );
                                    let destructure_ty =
                                        InternalType::ConstraintType(mk_constraint_type((
                                            reason::unpack_param((
                                                p1.clone(),
                                                pos_def.clone(),
                                                consumed,
                                            )),
                                            ConstraintType_::Tdestructure(Destructure {
                                                required: d_required.clone(),
                                                optional: d_optional.clone(),
                                                variadic: d_variadic.clone(),
                                                kind: DestructureKind::SplatUnpack,
                                            }),
                                        )));
                                    // Populate the type variables from the expression in the splat
                                    let ty_err_opt = typing_ops::sub_type_i(
                                        None,
                                        None,
                                        p1.clone(),
                                        Ureason::URparam,
                                        env,
                                        InternalType::LoclType(unpacked_element_ty.clone()),
                                        destructure_ty,
                                        callback::unify_error(),
                                    );
                                    let (te, used_dynamic_info) = match &ty_err_opt {
                                        Some(_) => {
                                            // Our type cannot be destructured, add a hole with `nothing`
                                            // as expected type
                                            let ty_expect = make_type::nothing(reason::solve_fail(
                                                pos_or_decl::of_raw_pos(expr_pos.clone()),
                                            ));
                                            (
                                                mk_hole(
                                                    None,
                                                    te,
                                                    unpacked_element_ty.clone(),
                                                    ty_expect,
                                                ),
                                                None,
                                            )
                                        }
                                        None => {
                                            // We have a type that can be destructured so continue and use
                                            // the type variables for the remaining parameters
                                            //
                                            // `err_opts` is in the order of the parameters (the
                                            // OCaml's, which conses, reversed).
                                            let mut err_opts: Vec<Option<(Ty, Ty)>> = vec![];
                                            let mut used_dynamic_info: Option<(PosOrDecl, Ty)> =
                                                None;
                                            check_fold2_exn_lengths(&d_required, &required_params);
                                            for (elt, (_idx, param)) in
                                                d_required.iter().zip(required_params.iter())
                                            {
                                                let (err_opt, used_dynamic_info_) =
                                                    check_argument_type_against_parameter(
                                                        None,
                                                        dynamic_func,
                                                        env,
                                                        param,
                                                        &ParamKind::Pnormal,
                                                        (e, elt.clone()),
                                                        false,
                                                    );
                                                err_opts.push(err_opt);
                                                used_dynamic_info = combine_dynamic_info(
                                                    used_dynamic_info,
                                                    used_dynamic_info_,
                                                );
                                            }
                                            check_fold2_exn_lengths(&d_optional, &optional_params);
                                            for (elt, (_idx, param)) in
                                                d_optional.iter().zip(optional_params.iter())
                                            {
                                                let (err_opt, used_dynamic_info_) =
                                                    check_argument_type_against_parameter(
                                                        None,
                                                        dynamic_func,
                                                        env,
                                                        param,
                                                        &ParamKind::Pnormal,
                                                        (e, elt.clone()),
                                                        false,
                                                    );
                                                err_opts.push(err_opt);
                                                used_dynamic_info = combine_dynamic_info(
                                                    used_dynamic_info,
                                                    used_dynamic_info_,
                                                );
                                            }
                                            let (var_err_opt, var_used_dynamic_info) = match (
                                                &d_variadic,
                                                match &variadic_or_splat_param {
                                                    Some(SplatOrVariadic::Variadic(p)) => Some(p),
                                                    _ => None,
                                                },
                                            ) {
                                                (Some(v), Some(vp)) => {
                                                    check_argument_type_against_parameter(
                                                        None,
                                                        dynamic_func,
                                                        env,
                                                        vp,
                                                        &ParamKind::Pnormal,
                                                        (e, v.clone()),
                                                        true,
                                                    )
                                                }
                                                _ => (None, None),
                                            };
                                            let any_err = err_opts.iter().any(|x| x.is_some());
                                            let subtyping_errs = (err_opts, var_err_opt);
                                            let te = match (any_err, &subtyping_errs.1) {
                                                (false, None) => te,
                                                _ => {
                                                    let aast::Expr(_, pos, _) = &te;
                                                    let pos = pos.clone();
                                                    let packed = pack_errs(
                                                        &pos,
                                                        &unpacked_element_ty,
                                                        &subtyping_errs,
                                                    );
                                                    hole_on_ty_mismatch(
                                                        te,
                                                        Some((unpacked_element_ty.clone(), packed)),
                                                    )
                                                }
                                            };
                                            (
                                                te,
                                                combine_dynamic_info(
                                                    used_dynamic_info,
                                                    var_used_dynamic_info,
                                                ),
                                            )
                                        }
                                    };
                                    add_typing_error_opt(ty_err_opt.as_ref(), env);
                                    let positional_arg_count: isize =
                                        el.iter().fold(0, |acc, e| {
                                            let name = named_params::name_of_arg(e);
                                            let is_named = name.is_some();
                                            if is_named { acc } else { acc + 1 }
                                        });
                                    (
                                        Some(te),
                                        positional_arg_count + d_required.len() as isize,
                                        d_variadic.is_some(),
                                        used_dynamic_info,
                                    )
                                }
                            },
                        };
                        check_deferred_expected(true, env);
                        let used_dynamic_info =
                            combine_dynamic_info(used_dynamic_info1, used_dynamic_info2);
                        // If dynamic_func is set, then the function type is supportdyn<t1 ... tn -> t>
                        // or ~(t1 ... tn -> t)
                        // and we are trying to call it as though it were dynamic. Hence all of the
                        // arguments must be subtypes of dynamic, regardless of whether they have
                        // a like type.
                        if used_dynamic_info.is_some() {
                            // `check_args_dynamic`
                            for (pos, argty) in &argtys {
                                // We've got an argument
                                let ty_err_opt = tutils::supports_dynamic(
                                    env,
                                    argty.clone(),
                                    Some(reasons_callback::unify_error_at(pos.clone())),
                                );
                                add_typing_error_opt(ty_err_opt.as_ref(), env);
                            }
                        }
                        let (arg_names, duplicate_arg_names): (im::OrdSet<String>, Vec<String>) = {
                            // (`SSet.empty`, without allocating a node.)
                            let mut acc: im::OrdSet<String> = EMPTY_NAME_SET.with(Clone::clone);
                            // Consed in OCaml: the last duplicate first.
                            let mut dupes: Vec<String> = vec![];
                            for arg in el {
                                match named_params::name_of_arg(arg) {
                                    Some(name) => {
                                        // `S_set.add pre_existing_key` preserves physical equality
                                        // https://ocaml.org/manual/5.3/api/Set.S.html
                                        // (which is how the OCaml sees that the name is already
                                        // in the set)
                                        if acc.contains(&name) {
                                            dupes.push(name)
                                        } else {
                                            acc.insert(name);
                                        }
                                    }
                                    None => {}
                                }
                            }
                            dupes.reverse();
                            (acc, dupes)
                        };
                        if !duplicate_arg_names.is_empty() {
                            typing_error_utils::add_typing_error(
                                &typing_error::primary(primary::T::Duplicate_named_args {
                                    duplicate_names: duplicate_arg_names,
                                    pos: crate::pos::btw(id_pos, expr_pos),
                                }),
                                env,
                            )
                        }
                        // If we unpacked an array, we don't check arity exactly. Since each
                        // unpacked array consumes 1 or many parameters, it is nonsensical to say
                        // that not enough args were passed in (so we don't do the min check).
                        check_arity_and_names(
                            Some(did_unpack),
                            variadic_or_splat_param.is_some(),
                            env,
                            &crate::pos::btw(id_pos, expr_pos),
                            &pos_def,
                            &ft,
                            arity,
                            &arg_names,
                        );
                        // Variadic params cannot be inout so we can stop early
                        // (`wfold_left2 inout_write_back env non_variadic_non_splat_params el`)
                        for (param, arg) in non_variadic_non_splat_params.iter().zip(el.iter()) {
                            inout_write_back(env, param, arg)
                        }
                        let ret = match (dynamic_func, &used_dynamic_info) {
                            (Some(DynFuncKind::LikeFunction), _) => {
                                make_type::locl_like(r2.clone(), ft.ret.clone())
                            }
                            (
                                Some(DynFuncKind::SupportdynFunction),
                                Some((dynamic_param_pos, dynamic_param_ty)),
                            ) => {
                                let reason = reason::support_dynamic_type_call((
                                    dynamic_param_pos.clone(),
                                    get_reason(dynamic_param_ty).clone(),
                                ));
                                make_type::locl_like(reason, ft.ret.clone())
                            }
                            _ => ft.ret.clone(),
                        };
                        let ret = env::update_reason(env, ret, |def| {
                            reason::flow_call(def, reason::witness(expr_pos.clone()))
                        });
                        (tel, typed_unpack_element, ret, should_forget_fakes)
                    }
                    Ty_::Tnewtype(name, tyl, _)
                        if tyl.len() == 1 && name == sn::classes::SUPPORT_DYN =>
                    {
                        let ty = &tyl[0];
                        // Under extended-reasons we want to use the reason on the newtype since this is
                        // the type at which we recorded the contravariant flow from the decl
                        let ty = env::update_reason(env, ty.clone(), |_| r.clone());
                        let ty = env::expand_type(env, ty);
                        match get_node(&ty) {
                            // If we have a function type of the form supportdyn<(function(t):~u)> then it does no
                            // harm to treat it as supportdyn<(function(~t):~u)> and may produce a more precise
                            // type for function application e.g. consider
                            //   function expect<T as supportdyn<mixed> >(T $obj)[]: ~Invariant<T>;
                            // If we have an argument of type ~t then checking against this signature will
                            // produce ~t <: T <: supportdyn<mixed>, so T will be assigned a like type.
                            // But if we check against the signature transformed as above, we will get
                            // t <: T <: supportdyn<mixed> which is more precise.
                            Ty_::Tfun(ft)
                                if typing_dynamic_utils::try_strip_dynamic(
                                    None,
                                    None,
                                    &mut env.clone(),
                                    &ft.ret,
                                )
                                .is_some()
                                    && el.len() == 1 =>
                            {
                                let ft_params: Vec<FunParam> = ft
                                    .params
                                    .iter()
                                    .map(|fp| FunParam {
                                        type_: tutils::make_like(None, env, fp.type_.clone()),
                                        ..fp.clone()
                                    })
                                    .collect();
                                let ty = mk((
                                    get_reason(&ty).clone(),
                                    Ty_::Tfun(std::rc::Rc::new(FunType {
                                        params: ft_params,
                                        ..FunType::clone(&ft)
                                    })),
                                ));
                                call(
                                    expected,
                                    Some(nullsafe.clone()),
                                    Some(attribute_check_policy.clone()),
                                    in_await.clone(),
                                    dynamic_func,
                                    expr_pos,
                                    recv_pos,
                                    id_pos,
                                    env,
                                    ty,
                                    el,
                                    unpacked_element,
                                )
                            }
                            _ => {
                                let (tel, typed_unpack_element, ret, should_forget_fakes) = call(
                                    expected,
                                    Some(nullsafe.clone()),
                                    Some(attribute_check_policy.clone()),
                                    in_await.clone(),
                                    Some(DynFuncKind::SupportdynFunction),
                                    expr_pos,
                                    recv_pos,
                                    id_pos,
                                    env,
                                    ty.clone(),
                                    el,
                                    unpacked_element,
                                );
                                let ret = match dynamic_func {
                                    Some(DynFuncKind::LikeFunction) => make_type::locl_like(
                                        reason::like_call((
                                            pos_or_decl::of_raw_pos(recv_pos.clone()),
                                            get_reason(&efty).clone(),
                                        )),
                                        ret,
                                    ),
                                    _ => ret,
                                };
                                (tel, typed_unpack_element, ret, should_forget_fakes)
                            }
                        }
                    }
                    _ => {
                        if !tutils::is_tyvar_error(env, &efty) {
                            bad_call(env, expr_pos, &efty)
                        }
                        let ty_err_opt = call_untyped_unpack(env, get_pos(&efty), unpacked_element);
                        let should_forget_fakes = true;
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                        let ty = env::fresh_type_error(env, expr_pos.clone());
                        (vec![], None, ty, should_forget_fakes)
                    }
                }
            }
        }
    }
}

/// The OCaml returns `env * Typing_error.t option`.
pub(crate) fn call_untyped_unpack(
    env: &mut Env,
    f_pos: PosOrDecl,
    unpacked_element: Option<&nast::Expr>,
) -> Option<typing_error::T> {
    match unpacked_element {
        // In the event that we don't have a known function call type, we can still
        // verify that any unpacked arguments (`...$args`) are something that can
        // be actually unpacked.
        None => None,
        Some(e) => {
            let (_, ety) = expr(None, &context::default(), env, e);
            let aast::Expr(_, p, _) = e;
            let ty = env::fresh_type(env, p.clone());
            let destructure_ty =
                make_type::simple_variadic_splat(reason::unpack_param((p.clone(), f_pos, 0)), ty);
            typing_ops::sub_type_i(
                None,
                None,
                p.clone(),
                Ureason::URnone,
                env,
                InternalType::LoclType(ety),
                destructure_ty,
                callback::unify_error(),
            )
        }
    }
}

pub(crate) fn upcast(env: &mut Env, p: &Pos, expr_ty: Ty, hint_ty: Ty) {
    let ty_err_opt = sub_type::sub_type(
        env,
        Some(true),
        None,
        None,
        None,
        expr_ty,
        hint_ty,
        Some(reasons_callback::unify_error_at(p.clone())),
    );
    add_typing_error_opt(ty_err_opt.as_ref(), env);
}

// ---------------------------------------------------------------------------
// type_switch
// ---------------------------------------------------------------------------

/// `refine_local ty env = set_local env locl ty`
fn type_switch_refine_local(locl: &aast::Lid, ty: Ty, env: &mut Env) {
    set_local(None, env, locl.clone(), ty)
}

/// `update_env_with_assumptions` of `type_switch` (`p` is the one of
/// `type_switch`).
fn type_switch_update_env_with_assumptions(env: &mut Env, p: &Pos, assumptions: &SubtypeProp) {
    match assumptions {
        SubtypeProp::Disj(_err, props) => {
            // If we have reached a disjunction then we cannot assume the assumption holds
            // since it is not required. Return environment unchanged
            let props: Vec<&SubtypeProp> = props
                .iter()
                .filter(|prop| !typing_logic::is_unsat(prop))
                .collect();
            match props.as_slice() {
                // make sure it's not a trivial disjunction
                [prop] => type_switch_update_env_with_assumptions(env, p, prop),
                _ => {}
            }
        }
        SubtypeProp::Conj(props) => {
            for prop in props {
                type_switch_update_env_with_assumptions(env, p, prop)
            }
        }
        SubtypeProp::IsSubtype(
            false,
            InternalType::LoclType(ty_sub),
            InternalType::LoclType(ty_super),
        ) => sub_type::add_constraint(
            env,
            ConstraintKind::ConstraintAs,
            ty_sub.clone(),
            ty_super.clone(),
            Some(reasons_callback::unify_error_at(p.clone())),
        ),
        SubtypeProp::IsSubtype(..) => {
            // Assume nothing if coercion is required or if requirement comes from a constraint type
        }
        SubtypeProp::AmbiguousShapeSplat(_) => {}
    }
}

/// Helper do to a combo of operations wildcards for a predicate,
/// (`instantiate_predicate_with_assumptions` of `type_switch`; `reason` is
/// the one of `type_switch`). The OCaml returns `(env, predicate_ty)`.
fn type_switch_instantiate_predicate_with_assumptions(
    env: &mut Env,
    reason: &Reason,
    predicate: &TypePredicate,
    p: &Pos,
    assumptions_f: impl FnOnce(&i_map::T<Ty>) -> SubtypeProp,
) -> Ty {
    let instantiated_tparams: i_map::T<((DeclTparam, String), Ty)> =
        typing_refinement::ty_predicate::instantiate_wildcards_for_predicate(env, predicate, p);
    let generics_map: i_map::T<Ty> = instantiated_tparams
        .iter()
        .map(|(k, (_tparam, locl_ty))| (*k, locl_ty.clone()))
        .collect();
    let assumptions = assumptions_f(&generics_map);
    type_switch_update_env_with_assumptions(env, p, &assumptions);
    // `I_map.values @@ I_map.map (fun (tp, ty) -> (Some tp, ty)) instantiated_tparams`
    let tparams: Vec<(Option<(DeclTparam, String)>, Ty)> = instantiated_tparams
        .iter()
        .map(|(_, (tp, ty))| (Some(tp.clone()), ty.clone()))
        .collect();
    let tparam_substs = type_parameter_env_ops::simplify_tpenv(env, &tparams, reason.clone());
    let generics_map: i_map::T<Ty> = instantiated_tparams
        .iter()
        .map(|(k, ((_tp, name), _ty))| {
            // `S_map.find`
            let ty = match tparam_substs.get(name) {
                Some(ty) => ty.clone(),
                None => panic!("Not_found"),
            };
            (*k, ty)
        })
        .collect();
    typing_refinement::ty_predicate::to_ty(env, &generics_map, p, predicate)
}

/// The OCaml returns `(env * (env -> env) * (env -> env)) option`. With
/// `None`, `*env` is the environment `type_switch` was given.
pub(crate) fn type_switch(
    env: &mut Env,
    p: &Pos,
    ivar: &tast::Expr,
    errs: Option<typing_error::T>,
    reason: Reason,
    predicate: TypePredicate,
) -> Option<(EnvTransformer, EnvTransformer)> {
    let ty: Ty = ivar.0.clone();
    // `let* locl = locl_opt`: no environment if there is no local.
    let env_before_local = env.clone();
    let locl_opt = make_a_local_of_tast(true, env, ivar);
    let locl: aast::Lid = match locl_opt {
        Some(locl) => locl,
        None => {
            *env = env_before_local;
            return None;
        }
    };
    // `refine_local` is [`type_switch_refine_local`],
    // `update_env_with_assumptions` is
    // [`type_switch_update_env_with_assumptions`] and
    // `instantiate_predicate_with_assumptions` is
    // [`type_switch_instantiate_predicate_with_assumptions`].
    //
    // `type_switch_constraint` reads the type of `ivar` (`ty` is rebound
    // after it).
    let type_switch_constraint = |env: &mut Env,
                                  errs: Option<typing_error::T>|
     -> (EnvTransformer, EnvTransformer) {
        env::open_tyvars(env, p.clone());
        let ty_true = env::fresh_type(env, p.clone());
        let ty_false = env::fresh_type(env, p.clone());
        let type_switch_constraint = InternalType::ConstraintType(mk_constraint_type((
            reason.clone(),
            ConstraintType_::TtypeSwitch {
                predicate: predicate.clone(),
                ty_true: ty_true.clone(),
                ty_false: ty_false.clone(),
            },
        )));
        let _ty_err = sub_type::sub_type(env, None, None, None, None, ty_true.clone(), ty.clone(), None);
        let _ty_err =
            sub_type::sub_type(env, None, None, None, None, ty_false.clone(), ty.clone(), None);
        env::set_tyvar_variance_i(env, None, None, &type_switch_constraint);
        let ty_err = typing_ops::sub_type_i(
            Some(false),
            None,
            p.clone(),
            Ureason::URnone,
            env,
            InternalType::LoclType(ty.clone()),
            type_switch_constraint,
            callback::unify_error(),
        );
        let errs = option_merge(errs, ty_err, typing_error::both);
        let ty_err = typing_solver::close_tyvars_and_solve(env);
        let errs = option_merge(errs, ty_err, typing_error::both);
        add_typing_error_opt(errs.as_ref(), env);
        /// `refine_local tyvar ty_refine_f ~ty_refine_is_class env` (of
        /// `type_switch_constraint`, which shadows the one of `type_switch`)
        fn refine_local(
            locl: &aast::Lid,
            reason: &Reason,
            ivar_ty: &Ty,
            tyvar: &Ty,
            ty_refine_f: impl FnOnce(&mut Env) -> Ty,
            ty_refine_is_class: bool,
            env: &mut Env,
        ) {
            let ty_refine = ty_refine_f(env);
            let ty_is_supportdyn = tutils::is_supportdyn(env, ivar_ty);
            let ty = typing_helpers::refine_and_simplify_intersection(
                env,
                ty_refine_is_class,
                // The normal call to is_supportdyn tends not to work on a tyvars
                // and so normally we wouldn't end up wrapping ty_refine in
                // supportdyn.
                // But we know tyvar is part of ty, so we should wrap ty_refine
                // in supportdyn when intersecting if ty is
                Some(ty_is_supportdyn),
                reason.clone(),
                tyvar.clone(),
                ty_refine,
            );
            type_switch_refine_local(locl, ty, env)
        }
        fn predicate_needs_supportdyn(predicate: &TypePredicate) -> bool {
            match &predicate.1 {
                TypePredicate_::IsTag(TypeTag::ClassTag(_, _)) => true,
                TypePredicate_::IsShapeOf(_) => true,
                TypePredicate_::IsTupleOf(TuplePredicate { required: tp_required }) => {
                    tp_required.iter().any(predicate_needs_supportdyn)
                }
                _ => false,
            }
        }
        let ty_refine_is_class = predicate_needs_supportdyn(&predicate);
        let cond_true: EnvTransformer = {
            let (locl, reason, ivar_ty, predicate, p) = (
                locl.clone(),
                reason.clone(),
                ty.clone(),
                predicate.clone(),
                p.clone(),
            );
            Rc::new(move |env: &mut Env| {
                refine_local(
                    &locl,
                    &reason,
                    &ivar_ty,
                    &ty_true,
                    |env: &mut Env| {
                        let predicate_ty = type_switch_instantiate_predicate_with_assumptions(
                            env,
                            &reason,
                            &predicate,
                            &p,
                            |_| typing_logic::valid(),
                        );
                        predicate_ty
                    },
                    ty_refine_is_class,
                    env,
                )
            })
        };
        let cond_false: EnvTransformer = {
            let (locl, reason, ivar_ty, predicate) =
                (locl.clone(), reason.clone(), ty.clone(), predicate.clone());
            Rc::new(move |env: &mut Env| {
                refine_local(
                    &locl,
                    &reason,
                    &ivar_ty,
                    &ty_false,
                    |_env: &mut Env| make_type::neg(reason.clone(), predicate.clone()),
                    false,
                    env,
                )
            })
        };
        (cond_true, cond_false)
    };
    /// The OCaml returns `env * Typing_refinement.ty_partition list option`.
    fn get_partitions(
        env: &mut Env,
        predicate: &TypePredicate,
        ty: Ty,
    ) -> Option<Vec<typing_refinement::TyPartition>> {
        let ty = env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tvar(_) => None,
            Ty_::Tunion(tyl) => {
                let partitions: Vec<Option<Vec<typing_refinement::TyPartition>>> = tyl
                    .iter()
                    .map(|ty| get_partitions(env, predicate, ty.clone()))
                    .collect();
                // `Option.map (Option.all partitions) ~f:List.concat`
                partitions
                    .into_iter()
                    .collect::<Option<Vec<Vec<typing_refinement::TyPartition>>>>()
                    .map(|partitions| partitions.into_iter().flatten().collect())
            }
            _ => {
                let partition = typing_refinement::partition_ty(env, &ty, predicate);
                Some(vec![partition])
            }
        }
    }
    let (like_type_dynamic, ty): (Option<Ty>, Ty) = {
        let ty = env::expand_type(env, ty.clone());
        match get_node(&ty) {
            Ty_::Tunion(tyl) => {
                match typing_dynamic_utils::try_strip_dynamic_from_union(None, env, tyl) {
                    Some((dynamic, tyl)) => {
                        (Some(dynamic), make_type::union(get_reason(&ty).clone(), tyl))
                    }
                    None => (None, ty.clone()),
                }
            }
            _ => (None, ty.clone()),
        }
    };
    // `return @@ match get_partitions env ty with ...`
    let env_before_partitions = env.clone();
    match get_partitions(env, &predicate, ty) {
        None => {
            *env = env_before_partitions;
            Some(type_switch_constraint(env, errs))
        }
        Some(partitions) => {
            // return (env, locl_ty list) where we intend to union the list later;
            // we don't do it here b/c we'll have more types to union with later
            fn union_inter_list(
                reason: &Reason,
                refine: &Ty,
                env: &mut Env,
                tyll: &[Vec<Ty>],
                tyll_span: &[Vec<Ty>],
            ) -> Vec<Ty> {
                let tyl: Vec<Ty> = tyll
                    .iter()
                    .map(|tyl| inter::intersect_list(env, reason.clone(), tyl))
                    .collect();
                let tyl_span: Vec<Ty> = tyll_span
                    .iter()
                    .map(|tyl| {
                        // place the refinement last so that if we do a refinement like
                        // MyReifiedBox<this::T> & MyReifiedBox<int>
                        // we get MyReifiedBox<this::T> where T = int
                        // instead of MyReifiedBox<int>; the latter of which can cause
                        // errors if the refined local is expected to still be a
                        // MyReifiedBox<this::T> after the true branch;
                        // See "intersection_order_to_preserve_type_const_generic" test
                        // (T223013561)
                        let inter = inter::intersect_list(env, reason.clone(), tyl);
                        fn ty_needs_supportdyn(ty: &Ty) -> bool {
                            match get_node(ty) {
                                Ty_::Ttuple(TupleType { required, .. }) => {
                                    required.iter().any(ty_needs_supportdyn)
                                }
                                Ty_::Tshape(_) => true,
                                _ => tutils::is_class(ty),
                            }
                        }
                        typing_helpers::refine_and_simplify_intersection(
                            env,
                            ty_needs_supportdyn(refine),
                            None,
                            reason.clone(),
                            inter,
                            refine.clone(),
                        )
                    })
                    .collect();
                let mut tyl = tyl;
                tyl.extend(tyl_span);
                tyl
            }
            fn union(env: &mut Env, reason: &Reason, tyl: Vec<Ty>) -> Ty {
                // This avoids a degenerate case where tyl is just one type which is an
                // enormous intersection.
                // Union.union_list does some computation on intersections that can be
                // prohibitively expensive for large intersections.
                // However, we don't want to apply to optimization in the general case
                // because some parts of the typechecker unfortunately depend on the
                // normalization.
                match tyl.as_slice() {
                    [ty] => ty.clone(),
                    tyl => typing_union::union_list(env, None, reason.clone(), tyl),
                }
            }
            let ty_true_ty_false_assumptions: Vec<TypeSplitInfo> = partitions
                .into_iter()
                .map(|partition| {
                    let typing_refinement::TyPartition {
                        left,
                        span,
                        right,
                        true_assumptions,
                        false_assumptions,
                        predicate: _,
                    } = partition;
                    let ty_trues: Box<dyn Fn(Ty, &mut Env) -> Vec<Ty>> = {
                        let (reason, span) = (reason.clone(), span.clone());
                        Box::new(move |predicate_ty: Ty, env: &mut Env| {
                            union_inter_list(&reason, &predicate_ty, env, &left, &span)
                        })
                    };
                    let ty_falses: Box<dyn Fn(&mut Env) -> Vec<Ty>> = {
                        let (reason, predicate) = (reason.clone(), predicate.clone());
                        Box::new(move |env: &mut Env| {
                            union_inter_list(
                                &reason,
                                &make_type::neg(reason.clone(), predicate.clone()),
                                env,
                                &right,
                                &span,
                            )
                        })
                    };
                    TypeSplitInfo {
                        ty_trues,
                        ty_falses,
                        true_assumptions,
                        false_assumptions,
                    }
                })
                .collect();
            let ty_true_ty_false_assumptions = Rc::new(ty_true_ty_false_assumptions);
            fn disj_assumptions(mut assumptions: Vec<SubtypeProp>) -> SubtypeProp {
                if assumptions.len() == 1 {
                    // Avoid creating a unary Disj -- this avoids the is_unsat prop
                    // filtering that we do in update_env_with_assumptions.
                    // This is a sneaky way of handling cases such as where we have a
                    // like type whose non-dynamic part is disjoint and we get
                    // `prop &&& FALSE` and we'd like to not filter it out and apply
                    // `prop` to mimic current (unsound) behavior (T214130596)
                    assumptions.pop().unwrap()
                } else {
                    SubtypeProp::Disj(None, assumptions)
                }
            }
            /// `union_helper env dyn extract_ty_f`, whose `extract_ty_f`
            /// takes the environment that the function it returns takes.
            fn union_helper(
                env: &mut Env,
                reason: &Reason,
                ty_true_ty_false_assumptions: &[TypeSplitInfo],
                dyn_: Option<Ty>,
                extract_ty_f: impl Fn(&TypeSplitInfo, &mut Env) -> Vec<Ty>,
            ) -> Ty {
                // `List.fold_left_env ~init:[] ~f:(fun env acc four_tuple -> ... (env, tys @ acc))`
                let mut tys: Vec<Ty> = vec![];
                for four_tuple in ty_true_ty_false_assumptions {
                    let mut new_tys = extract_ty_f(four_tuple, env);
                    new_tys.extend(tys);
                    tys = new_tys;
                }
                let tys = match dyn_ {
                    Some(dyn_) => {
                        let mut with_dyn = vec![dyn_];
                        with_dyn.extend(tys);
                        with_dyn
                    }
                    None => tys,
                };
                union(env, reason, tys)
            }
            let cond_true: EnvTransformer = {
                let (locl, reason, predicate, p, like_type_dynamic, tsis) = (
                    locl.clone(),
                    reason.clone(),
                    predicate.clone(),
                    p.clone(),
                    like_type_dynamic.clone(),
                    ty_true_ty_false_assumptions.clone(),
                );
                Rc::new(move |env: &mut Env| {
                    // The assumptions are instantiated in the environment this
                    // function is given.
                    let env_for_assumptions = env.clone();
                    let predicate_ty = type_switch_instantiate_predicate_with_assumptions(
                        env,
                        &reason,
                        &predicate,
                        &p,
                        |generics_map| {
                            disj_assumptions(
                                tsis.iter()
                                    .map(|TypeSplitInfo { true_assumptions, .. }| {
                                        typing_refinement::uninstantiated_typing_logic::instantiate_prop(
                                            &env_for_assumptions,
                                            generics_map,
                                            &p,
                                            true_assumptions,
                                        )
                                    })
                                    .collect(),
                            )
                        },
                    );
                    let ty_true = match &like_type_dynamic {
                        Some(_) if !typing_helpers::is_enforced(&predicate_ty) => {
                            // When predicate_ty is unenforced, keep dynamic on the outside,
                            // and do not intersect it
                            let ty_true = union_helper(
                                env,
                                &reason,
                                &tsis,
                                None,
                                |TypeSplitInfo { ty_trues, .. }, env| {
                                    ty_trues(predicate_ty.clone(), env)
                                },
                            );
                            let ty_true =
                                inter::intersect(env, reason.clone(), ty_true, predicate_ty.clone());
                            make_type::locl_like(reason.clone(), ty_true)
                        }
                        _ => {
                            let ty_true = union_helper(
                                env,
                                &reason,
                                &tsis,
                                like_type_dynamic.clone(),
                                |TypeSplitInfo { ty_trues, .. }, env| {
                                    ty_trues(predicate_ty.clone(), env)
                                },
                            );
                            inter::intersect(env, reason.clone(), ty_true, predicate_ty.clone())
                        }
                    };
                    type_switch_refine_local(&locl, ty_true, env)
                })
            };
            let cond_false: EnvTransformer = {
                let (locl, reason, predicate, p, like_type_dynamic, tsis) = (
                    locl,
                    reason,
                    predicate,
                    p.clone(),
                    like_type_dynamic,
                    ty_true_ty_false_assumptions,
                );
                Rc::new(move |env: &mut Env| {
                    // We need to instantiate wildcards in order to instantiate the
                    // proposition for the false branch due to the tuple case where the
                    // false branch proposition is a disjunction of combinations of the
                    // propositions of the sub-splits; usually this results in a
                    // non-trivial disjunction and is discarded.
                    // One case where you can get a false proposition that actually keeps
                    // involves an always false and an always true subsplit like:
                    // $x:(vec<T>, int); $x is (vec<_>, string)
                    // Here, you'll get a new T#3 and T#3 <: T but that seems harmless.
                    let env_for_assumptions = env.clone();
                    let _predicate_ty = type_switch_instantiate_predicate_with_assumptions(
                        env,
                        &reason,
                        &predicate,
                        &p,
                        |generics_map| {
                            disj_assumptions(
                                tsis.iter()
                                    .map(|TypeSplitInfo { false_assumptions, .. }| {
                                        typing_refinement::uninstantiated_typing_logic::instantiate_prop(
                                            &env_for_assumptions,
                                            generics_map,
                                            &p,
                                            false_assumptions,
                                        )
                                    })
                                    .collect(),
                            )
                        },
                    );
                    let ty_false = union_helper(
                        env,
                        &reason,
                        &tsis,
                        like_type_dynamic.clone(),
                        |TypeSplitInfo { ty_falses, .. }, env| ty_falses(env),
                    );
                    type_switch_refine_local(&locl, ty_false, env)
                })
            };
            Some((cond_true, cond_false))
        }
    }
}

// ---------------------------------------------------------------------------
// Conditions
// ---------------------------------------------------------------------------

/// [tparamet] = false means the expression is negated.
pub(crate) fn condition(env: &mut Env, tparamet: bool, te: &tast::Expr) {
    let (cond_true, cond_false) = condition_dual(env, te);
    if tparamet {
        cond_true(env)
    } else {
        cond_false(env)
    }
}

/// The OCaml returns `env * (env -> env) * (env -> env)`.
pub(crate) fn condition_dual(env: &mut Env, te: &tast::Expr) -> (EnvTransformer, EnvTransformer) {
    let aast::Expr(ty, p, e) = te;
    fn branch_without_refinement(_env: &mut Env) -> (EnvTransformer, EnvTransformer) {
        (Rc::new(|_env: &mut Env| {}), Rc::new(|_env: &mut Env| {}))
    }
    fn branch_for_type_switch(
        env: &mut Env,
        p: &Pos,
        ivar: &tast::Expr,
        errs: Option<typing_error::T>,
        reason: Reason,
        predicate: TypePredicate,
    ) -> (EnvTransformer, EnvTransformer) {
        // `(_, _, Aast.Call { func = (_, _, Aast.Class_const ((_, _, Aast.CI (_,
        // shapes)), (_, idx))); args = [Aast_defs.Anormal shape; Aast_defs.Anormal
        // field]; _ })`
        fn shapes_call_args<'a>(
            ivar: &'a tast::Expr,
        ) -> Option<(&'a str, &'a str, &'a tast::Expr, &'a tast::Expr)> {
            match ivar {
                aast::Expr(_, _, aast::Expr_::Call(call)) => {
                    match (&call.func, call.args.as_slice()) {
                        (
                            aast::Expr(_, _, aast::Expr_::ClassConst(cc)),
                            [
                                aast::Argument::Anormal(shape),
                                aast::Argument::Anormal(field),
                            ],
                        ) => match &**cc {
                            (aast::ClassId(_, _, aast::ClassId_::CI(Id(_, shapes))), (_, idx)) => {
                                Some((shapes, idx, shape, field))
                            }
                            _ => None,
                        },
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        match (&predicate.1, shapes_call_args(ivar)) {
            // Special case: treat Shapes::idx($s, 'k') is nonnull
            // roughly like $s is shape('k' => nonnull, ...)
            (TypePredicate_::IsTag(TypeTag::NullTag), Some((shapes, idx, shape, field)))
                if shapes == sn::shapes::SHAPES && idx == sn::shapes::IDX =>
            {
                let field = tast::to_nast_expr(field.clone());
                let shape = shape.clone();
                (
                    Rc::new(|_env: &mut Env| {}),
                    Rc::new(move |env: &mut Env| {
                        refine_lvalue_type(env, &shape, |env, shape_ty| {
                            typing_shapes::shapes_idx_not_null(env, shape_ty, &field)
                        })
                    }),
                )
            }
            _ => match type_switch(env, p, ivar, errs, reason, predicate) {
                Some(branches) => branches,
                None => branch_without_refinement(env),
            },
        }
    }
    fn is_null(e: &tast::Expr) -> bool {
        matches!(e, aast::Expr(_, _, aast::Expr_::Null))
    }
    match e {
        aast::Expr_::Binop(binop) if binop.bop == Bop::Ampamp => {
            let aast::Binop {
                lhs: e1, rhs: e2, ..
            } = &**binop;
            let (cond_true, cond_false) = condition_dual(env, e1);
            // `env_inter` is `*env`.
            let cond_true_: EnvTransformer = {
                let (cond_true, e2) = (cond_true.clone(), e2.clone());
                Rc::new(move |env: &mut Env| {
                    cond_true(env);
                    // This is necessary in case there is an assignment in e2
                    // We essentially redo what has been undone in the
                    // `Binop (Ampamp|Barbar)` case of `expr`
                    let (_, _) =
                        expr(None, &context::default(), env, &tast::to_nast_expr(e2.clone()));
                    let (cond_true, _cond_false) = condition_dual(env, &e2);
                    cond_true(env)
                })
            };
            let cond_false_: EnvTransformer = {
                let (e2, p) = (e2.clone(), p.clone());
                Rc::new(move |env: &mut Env| {
                    let ((), ()) = branch(
                        &p,
                        env,
                        |env: &mut Env| cond_false(env),
                        |env: &mut Env| {
                            cond_true(env);
                            // Similarly to the conjunction case, there might be an assignment in
                            // cond2 which we must account for. Again we redo what has been undone in
                            // the `Binop (Ampamp|Barbar)` case of `expr`
                            let (_, _) = expr(
                                None,
                                &context::default(),
                                env,
                                &tast::to_nast_expr(e2.clone()),
                            );
                            let (_cond_true, cond_false) = condition_dual(env, &e2);
                            cond_false(env)
                        },
                    );
                })
            };
            (cond_true_, cond_false_)
        }
        aast::Expr_::Binop(binop) if binop.bop == Bop::Barbar => {
            let aast::Binop {
                lhs: e1, rhs: e2, ..
            } = &**binop;
            let (cond_true, cond_false) = condition_dual(env, e1);
            // `env_inter` is `*env`.
            let cond_true_: EnvTransformer = {
                let (cond_true, cond_false, e2, p) =
                    (cond_true.clone(), cond_false.clone(), e2.clone(), p.clone());
                Rc::new(move |env: &mut Env| {
                    let ((), ()) = branch(
                        &p,
                        env,
                        |env: &mut Env| cond_true(env),
                        |env: &mut Env| {
                            cond_false(env);
                            // Similarly to the conjunction case, there might be an assignment in
                            // cond2 which we must account for. Again we redo what has been undone in
                            // the `Binop (Ampamp|Barbar)` case of `expr`
                            let (_, _) = expr(
                                None,
                                &context::default(),
                                env,
                                &tast::to_nast_expr(e2.clone()),
                            );
                            let (cond_true, _cond_false) = condition_dual(env, &e2);
                            cond_true(env)
                        },
                    );
                })
            };
            let cond_false_: EnvTransformer = {
                let e2 = e2.clone();
                Rc::new(move |env: &mut Env| {
                    cond_false(env);
                    // This is necessary in case there is an assignment in e2
                    // We essentially redo what has been undone in the
                    // `Binop (Ampamp|Barbar)` case of `expr`
                    let (_, _) =
                        expr(None, &context::default(), env, &tast::to_nast_expr(e2.clone()));
                    let (_cond_true, cond_false) = condition_dual(env, &e2);
                    cond_false(env)
                })
            };
            (cond_true_, cond_false_)
        }
        aast::Expr_::Binop(binop)
            if matches!(binop.bop, Bop::Eqeq | Bop::Eqeqeq)
                && (is_null(&binop.lhs) || is_null(&binop.rhs)) =>
        {
            // `lhs = (_, _, Aast.Null); rhs = te` first, then `lhs = te; rhs =
            // (_, _, Aast.Null)`.
            let te = if is_null(&binop.lhs) {
                &binop.rhs
            } else {
                &binop.lhs
            };
            let reason = reason::equal(p.clone());
            branch_for_type_switch(
                env,
                p,
                te,
                None,
                reason.clone(),
                TypePredicate(reason, TypePredicate_::IsTag(TypeTag::NullTag)),
            )
        }
        aast::Expr_::Hole(hole) => condition_dual(env, &hole.0),
        // Call to HH\is_any_array($x) is equivalent to $x is HH\AnyArray<_,_>
        aast::Expr_::Call(call)
            if matches!(
                (&call.func, call.args.as_slice(), &call.unpacked_arg),
                (aast::Expr(_, _, aast::Expr_::Id(f)), [_], None)
                    if f.1 == sn::std_lib_functions::IS_ANY_ARRAY
            ) =>
        {
            let (p, lv) = match (&call.func, call.args.as_slice()) {
                (aast::Expr(_, p, _), [lv]) => (p, lv),
                _ => unreachable!(),
            };
            condition_dual(
                env,
                &aast::Expr(
                    ty.clone(),
                    p.clone(),
                    aast::Expr_::Is(Box::new((
                        aast_utils::arg_to_expr(lv).clone(),
                        aast::Hint(
                            p.clone(),
                            Box::new(aast::Hint_::Happly(
                                Id(p.clone(), sn::collections::ANY_ARRAY.to_string()),
                                vec![
                                    aast::Hint(p.clone(), Box::new(aast::Hint_::Hwildcard)),
                                    aast::Hint(p.clone(), Box::new(aast::Hint_::Hwildcard)),
                                ],
                            )),
                        ),
                    ))),
                ),
            )
        }
        aast::Expr_::Is(is) => {
            let (ivar, hint) = &**is;
            let (ty_err_opt, hint_ty) = phase::localize_hint_for_refinement(env, hint);
            let reason = reason::is_refinement(hint.0.clone());
            match get_node(&hint_ty) {
                Ty_::Tnonnull => {
                    let (cond_true, cond_false) = branch_for_type_switch(
                        env,
                        p,
                        ivar,
                        ty_err_opt,
                        reason.clone(),
                        TypePredicate(reason, TypePredicate_::IsTag(TypeTag::NullTag)),
                    );
                    (cond_false, cond_true)
                }
                _ => match typing_refinement::ty_predicate::of_ty(env, &hint_ty).ok() {
                    None => branch_without_refinement(env),
                    Some(TypePredicate(_, predicate)) => branch_for_type_switch(
                        env,
                        p,
                        ivar,
                        ty_err_opt,
                        reason.clone(),
                        TypePredicate(reason, predicate),
                    ),
                },
            }
        }
        aast::Expr_::Unop(unop) if unop.0 == Uop::Unot => {
            let (_, e) = &**unop;
            let (cond_true, cond_false) = condition_dual(env, e);
            (cond_false, cond_true)
        }
        _ => {
            let (te_true, te_false) = (te.clone(), te.clone());
            (
                Rc::new(move |env: &mut Env| condition_single(env, true, &te_true)),
                Rc::new(move |env: &mut Env| condition_single(env, false, &te_false)),
            )
        }
    }
}

pub(crate) fn condition_single(env: &mut Env, tparamet: bool, te: &tast::Expr) {
    let aast::Expr(ty, p, e) = te;
    match e {
        aast::Expr_::Hole(hole) => condition_single(env, tparamet, &hole.0),
        aast::Expr_::True if !tparamet => lenv::drop_cont(env, c::T::Next),
        aast::Expr_::False if tparamet => lenv::drop_cont(env, c::T::Next),
        aast::Expr_::Binop(binop) if matches!(binop.bop, Bop::Eqeqeq) && tparamet => {
            let aast::Binop { lhs, rhs, .. } = &**binop;
            let aast::Expr(lhs_ty, _, _) = lhs;
            let aast::Expr(rhs_ty, _, _) = rhs;
            let refine = refine_for_strict_equality;
            refine(p, env, lhs, rhs_ty.clone());
            refine(p, env, rhs, lhs_ty.clone());
        }
        aast::Expr_::Binop(binop) if matches!(binop.bop, Bop::Diff | Bop::Diff2) => {
            let aast::Binop {
                bop: op,
                lhs: e1,
                rhs: e2,
            } = &**binop;
            let op = if *op == Bop::Diff {
                Bop::Eqeq
            } else {
                Bop::Eqeqeq
            };
            condition(
                env,
                !tparamet,
                &aast::Expr(
                    ty.clone(),
                    p.clone(),
                    aast::Expr_::Binop(Box::new(aast::Binop {
                        bop: op,
                        lhs: e1.clone(),
                        rhs: e2.clone(),
                    })),
                ),
            )
        }
        aast::Expr_::Call(call)
            if match (&call.func, call.args.as_slice(), &call.unpacked_arg) {
                (
                    aast::Expr(_, _, aast::Expr_::ClassConst(cc)),
                    [aast::Argument::Anormal(_), aast::Argument::Anormal(_)],
                    None,
                ) => match &**cc {
                    (
                        aast::ClassId(_, _, aast::ClassId_::CI(Id(_, class_name))),
                        (_, method_name),
                    ) => class_name == sn::shapes::SHAPES && method_name == sn::shapes::KEY_EXISTS,
                    _ => false,
                },
                _ => false,
            } =>
        {
            let (shape, field) = match call.args.as_slice() {
                [aast::Argument::Anormal(shape), aast::Argument::Anormal(field)] => (shape, field),
                _ => unreachable!(),
            };
            key_exists(env, tparamet, p, shape, field)
        }
        aast::Expr_::Package(package) => {
            let Id(pos, pkg) = &**package;
            let status = match tparamet {
                true => typing_local_packages::LocalPackageRequirement::Exists_in_deployment,
                false => typing_local_packages::LocalPackageRequirement::Not_exists_in_deployment,
            };
            lenv::assert_package_loaded(env, pos.clone(), pkg.clone(), status)
        }
        _ => {}
    }
}

/// The OCaml returns `env * Tast.expr list`.
pub(crate) fn string2(env: &mut Env, idl: &[nast::Expr]) -> Vec<tast::Expr> {
    // `List.fold_left ... (hole_on_ty_mismatch ~ty_mismatch_opt te :: tel)`, then
    // `List.rev`: the expressions in order.
    let mut tel: Vec<tast::Expr> = vec![];
    for x in idl {
        let (te, ty) = expr(None, &context::default(), env, x);
        let aast::Expr(_, p, _) = x;
        let expected_ty = make_type::arraykey(reason::interp_operand(p.clone()));
        let (ty_mismatch_opt, _used_dynamic) =
            typing_argument::check_argument_type_against_parameter_type(
                None,
                Some(Ureason::URstrInterp),
                Some(DynFuncKind::SupportdynFunction),
                false,
                env,
                expected_ty,
                p.clone(),
                ty,
            );
        tel.push(hole_on_ty_mismatch(te, ty_mismatch_opt));
    }
    tel
}

/// Calls the method of a class, but allows the f callback to override the
/// return value type
///
/// The OCaml returns `(make_call env te tal tel typed_unpack_element ty,
/// should_forget_fakes)`, where `make_call` returns the environment and
/// its result; here `make_call` returns its result without the
/// environment, and `f env fty res el tel` returns the type.
pub(crate) fn overload_function<R>(
    make_call: impl FnOnce(
        &mut Env,
        tast::Expr,
        Vec<tast::Targ>,
        Vec<tast::Argument>,
        Option<tast::Expr>,
        Ty,
    ) -> R,
    fpos: &Pos,
    p: &Pos,
    env: &mut Env,
    class_id: &nast::ClassId,
    method_id: &aast::Pstring,
    el: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
    f: impl FnOnce(&mut Env, &Ty, Ty, &[nast::Argument], &[tast::Argument]) -> Ty,
) -> (R, bool) {
    let aast::ClassId(_, cid_pos, _) = class_id;
    let (_tal, tcid, ty) = class_id::class_expr(
        None, None, None, None, None, None, None, None, None, None, env, &[], class_id,
    );
    let (fty, tal) = class_get_expr::class_get(
        true, // is_method
        false, // is_const
        None, // transform_fty
        None, // coerce_from_ty
        None,
        None,
        None,
        None,
        env,
        ty,
        method_id,
        class_id,
    );
    let (tel, typed_unpack_element, res, should_forget_fakes) = call(
        None,
        None,
        None,
        None,
        None,
        p,
        cid_pos,
        &method_id.0,
        env,
        fty.clone(),
        el,
        unpacked_element,
    );
    let ty = f(env, &fty, res, el, &tel);
    let fty = env::expand_type(env, fty);
    let fty = map_ty(fty, |ty_| match ty_ {
        Ty_::Tfun(ft) => Ty_::Tfun(std::rc::Rc::new(FunType {
            ret: ty.clone(),
            ..std::rc::Rc::unwrap_or_clone(ft)
        })),
        ty_ => ty_,
    });
    let te = typing_helpers::make_simplify_typed_expr(
        env,
        fpos.clone(),
        fty,
        aast::Expr_::ClassConst(Box::new((tcid, method_id.clone()))),
    );
    (
        make_call(env, te, tal, tel, typed_unpack_element, ty),
        should_forget_fakes,
    )
}

/// The OCaml returns `env * Tast.expr * locl_ty`.
pub(crate) fn update_array_type(
    lhs_of_null_coalesce: bool,
    p: &Pos,
    env: &mut Env,
    e1: &nast::Expr,
    valkind: valkind::T,
) -> (tast::Expr, Ty) {
    match valkind {
        valkind::T::Lvalue | valkind::T::LvalueSubexpr => {
            let (te1, ty1) = expr(
                None,
                &context::T {
                    valkind: valkind::T::LvalueSubexpr,
                    ..context::default()
                },
                env,
                e1,
            );
            match e1 {
                aast::Expr(_, _, aast::Expr_::Lvar(lid)) => {
                    let aast::Lid(_, x) = &**lid;
                    if !env::is_local_defined(env, x) {
                        // If the Lvar wasn't in the environment, add it in to avoid reporting
                        // subsequent errors.
                        set_local(None, env, aast::Lid(p.clone(), x.clone()), ty1.clone())
                    }
                    (te1, ty1)
                }
                _ => (te1, ty1),
            }
        }
        valkind::T::Other => expr(
            None,
            &context::T {
                lhs_of_null_coalesce,
                ..context::default()
            },
            env,
            e1,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_env_ty_err_opt_orders_errors_as_ocaml() {
        // Seven elements: the errors of the second group of five first, then
        // those of the first, each group in order.
        let xs: Vec<isize> = (1..=7).collect();
        let mut seen = vec![];
        let (errs, ys) = list_map_env_ty_err_opt(
            &mut (),
            &xs,
            |_, x| {
                seen.push(*x);
                (if *x == 3 { None } else { Some(*x) }, *x * 10)
            },
            |errs| errs,
        );
        assert_eq!(seen, vec![1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(ys, vec![10, 20, 30, 40, 50, 60, 70]);
        assert_eq!(errs, vec![6, 7, 1, 2, 4, 5]);
    }

    #[test]
    fn map_env_ty_err_opt_long_lists() {
        // After 1001 groups of five, the rest of the errors come last first,
        // before the groups (which are in reverse order of groups).
        let n = 5 * 1002 + 3;
        let xs: Vec<usize> = (0..n).collect();
        let (errs, ys) = list_map_env_ty_err_opt(&mut (), &xs, |_, x| (Some(*x), *x), |errs| errs);
        assert_eq!(ys, xs);
        let mut expected: Vec<usize> = (5 * 1002..n).rev().collect();
        for group in (0..1002).rev() {
            expected.extend(group * 5..group * 5 + 5);
        }
        assert_eq!(errs, expected);
    }

    #[test]
    fn option_merge_is_that_of_base() {
        assert_eq!(option_merge(None::<i32>, None, |a, b| a + b), None);
        assert_eq!(option_merge(Some(1), None, |a, b| a + b), Some(1));
        assert_eq!(option_merge(None, Some(2), |a, b| a + b), Some(2));
        assert_eq!(option_merge(Some(1), Some(2), |a, b| a * 10 + b), Some(12));
    }

    #[test]
    #[should_panic(expected = "length mismatch in zip_exn: 1 <> 2")]
    fn zip_exn_panics_on_length_mismatch() {
        zip_exn(&[1], &[1, 2]);
    }
}
