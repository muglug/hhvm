// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 10651-11787): module `Lambda`.
//! See `hh/PORTING.md`.
//!
//! # Signatures
//!
//! The functions of the OCaml signature (`lambda`, `bind_params`, `fun_`,
//! `check_function_dynamically_callable`) and the hidden ones
//! (`bind_param`, `closure_bind_param`, `closure_bind_variadic`,
//! `closure_make`) are all `pub(crate)`, with their labelled and optional
//! arguments in the order of their `let`.
//!
//! - `closure_bind_param` is the function OCaml folds over the parameter
//!   types: it takes the accumulator `(t_params, params)` without the
//!   environment and returns the new one; the parameters still to bind are a
//!   slice of the remaining ones.
//! - `fun_` names its `?abstract` argument `abstract_` (`abstract` is a Rust
//!   keyword).
//! - `check_function_dynamically_callable` returns
//!   `(dynamic_params, dynamic_body, dynamic_return_ty)`, the OCaml result
//!   without the environment.
//! - The captured variables of `closure_make` are the
//!   `Typing_local_types.local Aast.capture_lid list` that `lambda` builds,
//!   `[aast::CaptureLid<Local>]`, as `stash_conts_for_closure` takes them.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::feature_logging as fl;
use crate::folded_class as cls;
use crate::naming_attributes;
use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing::stmt;
use crate::typing::user_attribute;
use crate::typing_defs::*;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_return_info;
use crate::typing_env_types::Env;
use crate::typing_error::callback;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_helpers::expected_ty;
// module LEnv = Typing_lenv
use crate::typing_lenv as lenv;
use crate::typing_local_types::Local;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module Phase = Typing_phase
use crate::typing_phase as phase;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
// module SubType = Typing_subtype
use crate::typing_subtype as sub_type;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;

/// `SN.Capabilities.accessGlobals`, which `naming_special_names_rust` lacks
/// (`Capabilities.prefix ^ "AccessGlobals"`).
const CAPABILITIES_ACCESS_GLOBALS: &str = "\\HH\\Capabilities\\AccessGlobals";

/// `Env.get_self_class env |> Decl_entry.to_option`
fn self_class_opt(env: &Env) -> Option<cls::T> {
    decl_entry::to_option(env::get_self_class(env))
}

/// The enforcement of the hint of a parameter: the `decl_hint` and `enforced`
/// that `bind_param` computes twice, with the same code.
fn param_hint_enforcement(env: &Env, param: &nast::FunParam) -> Enforcement {
    let decl_hint = param
        .type_hint
        .1
        .as_ref()
        .map(|h| crate::decl_hint::hint(&env.decl_env, h));
    match decl_hint {
        None => Enforcement::Unenforced,
        Some(ty) => crate::typing_enforceability::get_enforcement(
            Some(true),
            self_class_opt(env).as_ref(),
            env,
            &ty,
        ),
    }
}

/// Given a localized parameter type and parameter information, infer
/// a type for the parameter default expression (if present) and check that
/// it is a subtype of the parameter type (if present).
/// Set the type of the parameter in the locals environment
pub(crate) fn bind_param(
    env: &mut Env,
    immutable: Option<bool>,
    can_read_globals: Option<bool>,
    no_auto_likes: Option<bool>,
    (opt_ty1, param): (Option<Ty>, &nast::FunParam),
) -> tast::FunParam {
    let immutable = immutable.unwrap_or(false);
    let can_read_globals = can_read_globals.unwrap_or(false);
    let no_auto_likes = no_auto_likes.unwrap_or(false);
    let (param_te, ty1): (Option<tast::Expr>, Ty) =
        match crate::aast_utils::get_param_default(param) {
            None => match opt_ty1 {
                None => {
                    // If no parameter type has been provided, we assume that an error
                    // has already been reported, and generate an error type variable
                    let err_ty = env::fresh_type_error_contravariant(env, param.pos.clone());
                    (None, err_ty)
                }
                Some(ty1) => (None, ty1),
            },
            Some(e) => {
                let enforced = param_hint_enforcement(env, param);
                let expected = match &opt_ty1 {
                    None => None,
                    Some(ty1) => Some(expected_ty::make(
                        None,
                        None,
                        param.pos.clone(),
                        Ureason::URparam,
                        ty1.clone(),
                    )),
                };
                let (te, ty2): (tast::Expr, Ty) = {
                    let reason = reason::witness(param.pos.clone());
                    let pure = make_type::mixed(reason.clone());
                    let cap = if can_read_globals {
                        make_type::capability(reason, CAPABILITIES_ACCESS_GLOBALS.to_string())
                    } else {
                        pure.clone()
                    };
                    with_special_coeffects(env, cap, pure, |env| {
                        triple_to_pair(expr::expr(
                            expected.as_ref(),
                            &expr::context::default(),
                            env,
                            e,
                        ))
                    })
                };
                crate::typing_sequencing::sequence_check_expr(e);
                let ty1 = match opt_ty1 {
                    // Type hint is missing
                    None => ty2,
                    // Otherwise we have an explicit type, and the default expression type
                    // must be a subtype
                    Some(ty1) => {
                        // Under Sound Dynamic, if t is the declared type of the parameter, then we
                        // allow the default expression to have any type u such that u <: ~t.
                        // If t is enforced, then the parameter is assumed to have that type when checking the body,
                        //   because we know that enforcement will ensure this.
                        // If t is not enforced, then the parameter is assumed to have type u|t when checking the body,
                        // as though the default expression had been assigned conditionally to the parameter.
                        // If t is type dynamic, leave it alone.
                        let support_dynamic = env::get_support_dynamic_type(env);
                        let like_ty1 = if support_dynamic && !no_auto_likes {
                            tutils::make_like(None, env, ty1.clone())
                        } else {
                            ty1.clone()
                        };
                        // TODO akenn: pass in enforced to function
                        let ty_err_opt = crate::typing_coercion::coerce_type(
                            None,
                            None,
                            None,
                            param.pos.clone(),
                            Ureason::URhint,
                            env,
                            ty2.clone(),
                            like_ty1,
                            enforced,
                            callback::parameter_default_value_wrong_type(),
                        );
                        if let Some(err) = &ty_err_opt {
                            typing_error_utils::add_typing_error(err, env)
                        }
                        if support_dynamic {
                            match enforced {
                                Enforcement::Enforced => ty1,
                                _ => {
                                    if tutils::is_dynamic(env, &ty1) {
                                        ty1
                                    } else {
                                        crate::typing_union::union(env, None, None, ty1, ty2)
                                    }
                                }
                            }
                        } else {
                            ty1
                        }
                    }
                };
                (Some(te), ty1)
            }
        };

    // Update the reason to record the flow from the parameter hint into the parameter
    let ty1 = env::update_reason(env, ty1, |hint| {
        reason::flow_param_hint(hint, reason::witness(param.pos.clone()))
    });
    let param_te = param_te.map(|aast::Expr(_, pos, e)| aast::Expr(ty1.clone(), pos, e));
    let user_attributes = user_attribute::attributes_check_def(
        env,
        sn::attribute_kinds::PARAMETER,
        &param.user_attributes.0,
    );
    let tparam = aast::FunParam {
        annotation: tast::make_expr_annotation(&param.pos, ty1.clone()),
        type_hint: aast::TypeHint(ty1.clone(), param.type_hint.1.clone()),
        pos: param.pos.clone(),
        name: param.name.clone(),
        info: match &param.info {
            aast::FunParamInfo::ParamRequired => aast::FunParamInfo::ParamRequired,
            aast::FunParamInfo::ParamVariadic => aast::FunParamInfo::ParamVariadic,
            aast::FunParamInfo::ParamOptional(_) => aast::FunParamInfo::ParamOptional(param_te),
        },
        callconv: param.callconv.clone(),
        readonly: param.readonly.clone(),
        splat: param.splat.clone(),
        named: param.named.clone(),
        user_attributes: aast::UserAttributes(user_attributes),
        visibility: param.visibility.clone(),
    };
    let mode = get_param_mode(&param.callconv);
    let out_ty = match mode {
        ParamMode::FPinout => {
            let enforced = param_hint_enforcement(env, param);
            let reason = reason::pessimised_inout(get_pos(&ty1));
            match enforced {
                Enforcement::Enforced if env::get_support_dynamic_type(env) => {
                    Some(tutils::make_like(Some(reason), env, ty1.clone()))
                }
                _ => {
                    // In implicit SD mode, all inout parameters are pessimised, unless marked <<__NoAutoLikes>>
                    // `TCO.everything_sdt env.genv.tcopt`
                    if env.genv.tcopt.po.everything_sdt && !no_auto_likes {
                        Some(tutils::make_like(Some(reason), env, ty1.clone()))
                    } else {
                        Some(ty1.clone())
                    }
                }
            }
        }
        _ => None,
    };
    let id = crate::local_id::make_unscoped(param.name.clone());
    env::set_local(
        Some(immutable),
        None,
        env,
        id.clone(),
        ty1.clone(),
        param.pos.clone(),
    );
    env::set_param(env, id.clone(), (ty1, param.pos.clone(), out_ty));
    if crate::typing_helpers::has_accept_disposable_attribute(param) {
        env::set_using_var(env, id)
    }
    tparam
}

pub(crate) fn bind_params(
    env: &mut Env,
    can_read_globals: Option<bool>,
    no_auto_likes: bool,
    ctxs: Option<&aast::Contexts>,
    param_tys: &[Option<Ty>],
    params: &[nast::FunParam],
) -> Vec<tast::FunParam> {
    let can_read_globals = can_read_globals.unwrap_or(false);
    let params_need_immutable = crate::typing_coeffects::get_ctx_vars(ctxs);
    let bind_param_and_check = |env: &mut Env, lty_and_param: (Option<Ty>, &nast::FunParam)| {
        let (_ty, param) = &lty_and_param;
        let name = &param.name;
        let immutable = params_need_immutable.iter().any(|n| n == name);
        let fun_param = bind_param(
            env,
            Some(immutable),
            Some(can_read_globals),
            Some(no_auto_likes),
            lty_and_param,
        );
        fun_param
    };
    // `List.zip_exn param_tys params`
    if param_tys.len() != params.len() {
        panic!(
            "length mismatch in zip_exn: {} <> {}",
            param_tys.len(),
            params.len()
        )
    }
    // `List.map_env`: from left to right.
    param_tys
        .iter()
        .zip(params.iter())
        .map(|(ty, param)| bind_param_and_check(env, (ty.clone(), param)))
        .collect()
}

pub(crate) fn closure_bind_param<'a>(
    env: &mut Env,
    (t_params, params): (Vec<tast::FunParam>, &'a [nast::FunParam]),
    ty: Ty,
) -> (Vec<tast::FunParam>, &'a [nast::FunParam]) {
    match params {
        [] => (t_params, params),
        [param, paraml @ ..] => {
            let ty = match &param.type_hint.1 {
                Some(h) => {
                    let decl_ty = crate::decl_hint::hint(&env.decl_env, h);
                    match crate::typing_enforceability::get_enforcement(
                        Some(true),
                        self_class_opt(env).as_ref(),
                        env,
                        &decl_ty,
                    ) {
                        Enforcement::Unenforced => crate::typing_log::log_pessimise_param(
                            env,
                            false,
                            &param.pos,
                            &param.callconv,
                            &param.name,
                        ),
                        Enforcement::Enforced => {}
                    };
                    ty
                }
                None => {
                    let r = reason::lambda_param((param.pos.clone(), get_reason(&ty).clone()));
                    with_reason(ty, r)
                }
            };
            let t_param = bind_param(env, None, None, None, (Some(ty), param));
            let mut t_params = t_params;
            t_params.push(t_param);
            (t_params, paraml)
        }
    }
}

pub(crate) fn closure_bind_variadic(
    env: &mut Env,
    vparam: &nast::FunParam,
    variadic_ty: Ty,
) -> tast::FunParam {
    let r = reason::var_param_from_decl(get_pos(&variadic_ty));
    let arr_values = with_reason(variadic_ty, r.clone());
    let ty = make_type::vec(r, arr_values);
    bind_param(env, None, None, None, (Some(ty), vparam))
}

pub(crate) fn fun_(
    abstract_: Option<bool>,
    native: Option<bool>,
    disable: Option<bool>,
    env: &mut Env,
    return_: typing_env_return_info::T,
    pos: &Pos,
    named_body: &nast::FuncBody,
    f_kind: ast_defs::FunKind,
) -> Vec<tast::Stmt> {
    let abstract_ = abstract_.unwrap_or(false);
    let native = native.unwrap_or(false);
    let disable = disable.unwrap_or(false);
    env::with_env(env, |env| {
        debug_last_pos.with(|r| *r.borrow_mut() = pos.clone());
        let restore_pos = env::set_inference_env_pos(env, Some(pos.clone()));
        env::set_return(env, return_);
        let tb = if disable {
            diagnostics_state::internal_error(
                pos.clone(),
                &format!(
                    "{}{}{}",
                    "Type inference for this function has been disabled by the ",
                    sn::user_attributes::DISABLE_TYPECHECKER_INTERNAL,
                    " attribute"
                ),
            );
            stmt::block(env, &[])
        } else {
            stmt::block(env, &named_body.fb_ast.0)
        };
        crate::typing_sequencing::sequence_check_block(&named_body.fb_ast);
        let typing_env_return_info::T {
            return_type: ret, ..
        } = env::get_return(env);
        let has_implicit_return = lenv::has_next(env);
        let has_readonly = env::get_readonly(env);
        if (!has_implicit_return) || abstract_ || native || env::is_hhi(env) {
        } else {
            crate::typing_return::fun_implicit_return(env, pos.clone(), ret, f_kind)
        }
        // Collect all locals that carry shadow type variables for the TAST,
        // so downstream consumers can inspect which dynamic locals exist and
        // query their accumulated constraints.
        let dynamic_locals = {
            let shadow_locals =
                crate::typing_inference_env::collect_shadow_locals(&env.inference_env);
            shadow_locals
                .into_iter()
                .map(|(name, pos, v)| tast::DynamicLocalInfo {
                    name,
                    pos,
                    shadow_tvid: v,
                })
                .collect()
        };
        env::set_fun_tast_info(
            env,
            tast::FunTastInfo {
                has_implicit_return,
                has_readonly,
                dynamic_locals,
            },
        );
        restore_pos(env);
        debug_last_pos.with(|r| *r.borrow_mut() = Pos::NONE);
        tb
    })
}

/// Here the body of a function or lambda is typechecked again to ensure it is safe
/// to call it from a dynamic context (eg. under dyn..dyn->dyn assumptions).
/// The code below must be kept in sync with with the fun_def checks.
pub(crate) fn check_function_dynamically_callable(
    _this_class: Option<&cls::T>,
    env: &mut Env,
    f_name: Option<&aast::Sid>,
    f: &nast::Fun_,
    params_decl_ty: &[Option<DeclTy>],
    ret_locl_ty: &Ty,
) -> (Vec<tast::FunParam>, Vec<tast::Stmt>, Ty) {
    env.checked = tast::CheckStatus::CUnderDynamicAssumptions;
    crate::typing_log::log_sd_pass(None, env, &f.span);
    let make_dynamic = |pos: PosOrDecl| make_type::dynamic(reason::support_dynamic_type(pos));
    let dynamic_return_ty = make_dynamic(get_pos(ret_locl_ty));
    let hint_pos = match &f.ret.1 {
        None => match f_name {
            // We don't have a return hint, highlight the function name instead.
            Some(Id(pos, _)) => pos.clone(),
            // Anonymos function, just use the position of the whole function.
            None => f.span.clone(),
        },
        Some(aast::Hint(pos, _)) => pos.clone(),
    };
    let dynamic_return_info = crate::typing_return::make_info(
        None,
        hint_pos,
        f.fun_kind,
        &f.user_attributes.0,
        env,
        dynamic_return_ty.clone(),
    );
    let param_tys =
        crate::typing_param::make_param_local_tys(true, false, env, params_decl_ty, &f.params);
    let dynamic_params = bind_params(env, None, false, f.ctxs.as_ref(), &param_tys, &f.params);
    let (pos, name) = match f_name {
        Some(Id(pos, name)) => (pos.clone(), name.clone()),
        None => (f.span.clone(), ";anonymous".to_string()),
    };
    crate::typing_helpers::set_tyvars_variance_in_callable(env, &dynamic_return_ty, &param_tys);
    let disable = naming_attributes::mem(
        sn::user_attributes::DISABLE_TYPECHECKER_INTERNAL,
        &f.user_attributes.0,
    );

    // The handler reads the options of the environment the OCaml closure
    // captured, the one from before the attempt: read them now.
    // `TCO.silence_errors_under_dynamic env.genv.tcopt`
    let silence_errors_under_dynamic = env.genv.tcopt.tco_silence_errors_under_dynamic;
    let dynamic_body = diagnostics_state::try_with_result(
        || {
            fun_(
                None,
                None,
                Some(disable),
                env,
                dynamic_return_info,
                &pos,
                &f.body,
                f.fun_kind,
            )
        },
        |env_and_dynamic_body, error| {
            if !silence_errors_under_dynamic {
                diagnostics_state::function_is_not_dynamically_callable(&name, &error)
            }
            env_and_dynamic_body
        },
    );
    (dynamic_params, dynamic_body, dynamic_return_ty)
}

/// Make a type-checking function for an anonymous function or lambda.
/// Here ret_ty should include Awaitable wrapper
pub(crate) fn closure_make(
    ret_ty: Option<Ty>,
    supportdyn: bool,
    closure_class_name: Option<String>,
    is_expr_tree_virtual_expr: bool,
    should_invalidate_fakes: bool,
    ignore_readonly: Option<bool>,
    env: &mut Env,
    lambda_pos: &Pos,
    decl_ft: &DeclFunType,
    f: &nast::Fun_,
    ft: FunType,
    used_ids: &[aast::CaptureLid<Local>],
    is_anon: bool,
) -> (tast::Expr, FunType, bool) {
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    // The names of the quantifiers of the function type `type_closure` is
    // given (`ft` of `closure_make`): OCaml computes them after typing the
    // body, from the same `ft`, which nothing changes.
    let quants: Vec<String> = ft
        .tparams
        .iter()
        .map(|Tparam { name: (_, id), .. }| id.clone())
        .collect();

    // `type_closure @@ fun env -> ...`: the function given to `type_closure`.
    let type_closure_f = move |env: &mut Env| -> (tast::Expr, FunType, bool) {
        // Extract capabilities from AAST and add them to the environment
        let capability = match (&f.ctxs, &f.unsafe_ctxs) {
            (None, None) => {
                // if the closure has no explicit coeffect annotations,
                // do _not_ insert (unsafe) capabilities into the environment;
                // instead, rely on the fact that a capability from an enclosing
                // scope can simply be captured, which has the same semantics
                // as redeclaring and shadowing with another same-typed capability.
                // This avoid unnecessary overhead in the most common case, i.e.,
                // when a closure does not need a different (usually smaller)
                // set of capabilities.
                env::get_local(env, &crate::typing_coeffects::local_capability_id()).ty
            }
            (_, _) => {
                let (cap_ty, unsafe_cap_ty) = crate::typing_coeffects::type_capability(
                    env,
                    f.ctxs.as_ref(),
                    f.unsafe_ctxs.as_ref(),
                    &f.span,
                );
                let _ = crate::typing_coeffects::register_capabilities(
                    env,
                    cap_ty.clone(),
                    unsafe_cap_ty,
                );
                cap_ty
            }
        };
        let ft = FunType {
            implicit_params: FunImplicitParams {
                capability: Capability::CapTy(capability),
            },
            ..ft
        };
        // Check attributes on the lambda
        let user_attributes = user_attribute::attributes_check_def(
            env,
            sn::attribute_kinds::LAMBDA,
            &f.user_attributes.0,
        );
        // Regard a lambda as supporting dynamic if
        //   it has the attribute <<__SupportDynamicType>>;
        //   or its enclosing method, function or class has the attribute <<__SupportDynamicType>>;
        //   or it must support dynamic because of the expected type
        let support_dynamic_type =
            naming_attributes::mem(sn::user_attributes::SUPPORT_DYNAMIC_TYPE, &user_attributes)
                || env::get_support_dynamic_type(env)
                || supportdyn;
        let no_auto_likes =
            naming_attributes::mem(sn::user_attributes::NO_AUTO_LIKES, &user_attributes)
                || env::get_no_auto_likes(env);
        // A closure typed in env with parameters p1..pn and captured variables c1..cn
        // roughly compiles to
        //
        // class Closure$name {
        //   private env(c1) c1;
        //   ...
        //   private env(cn) cn;
        //   public static function __invoke(p1, ..., pn) {
        //     /* closure body, references to cn are replaced with $this->cn */
        //   }
        // }
        //
        // To make a class SDT without considering enforcement, we make its properties
        // like types so that they may be written values with type `dynamic`. The following
        // fold analogously makes an SDT closure's captured variables be like types, and
        // elsewhere we skip typing closures entirely when typing the dynamic pass of a function.
        //
        // This is clearly a less precise way to type closures, but it allows us to avoid typing
        // SDT closures 2^depth times.
        if support_dynamic_type {
            // quiet to avoid duplicate error about capturing an undefined variable
            let locals = env::get_locals(Some(true), env, used_ids);
            // `Local_id.Map.map`
            let like_locals: crate::typing_local_types::T = locals
                .into_iter()
                .map(|(id, local)| {
                    let ty = tutils::make_like(
                        Some(reason::captured_like(lambda_pos.clone())),
                        env,
                        local.ty.clone(),
                    );
                    (id, Local { ty, ..local })
                })
                .collect();
            env::set_locals(env, &like_locals)
        }
        // Inout parameters should be pessimised in implicit pessimisation mode
        // `TCO.everything_sdt env.genv.tcopt`
        let ft = if support_dynamic_type && (!no_auto_likes) && env.genv.tcopt.po.everything_sdt
        {
            // The fields of a record are evaluated from right to left; neither
            // has an effect.
            let ft_tparams: Vec<Tparam> = ft
                .tparams
                .iter()
                .map(|tparam| {
                    let Tparam {
                        name: (pos, _),
                        user_attributes: tp_user_attributes,
                        ..
                    } = tparam;
                    if tp_user_attributes.iter().any(|UserAttribute { name: (_, name), .. }| {
                        name == sn::user_attributes::NO_AUTO_BOUND
                    }) {
                        tparam.clone()
                    } else {
                        let reason = reason::witness_from_decl(pos.clone());
                        let mut tp_constraints = vec![(
                            ast_defs::ConstraintKind::ConstraintAs,
                            make_type::supportdyn_mixed(reason),
                        )];
                        tp_constraints.extend(tparam.constraints.iter().cloned());
                        Tparam {
                            constraints: tp_constraints,
                            ..tparam.clone()
                        }
                    }
                })
                .collect();
            let ft_params: Vec<FunParam> = ft
                .params
                .iter()
                .map(|fp| match get_fp_mode(fp) {
                    ParamMode::FPinout => FunParam {
                        type_: tutils::make_like(
                            Some(reason::pessimised_inout(fp.pos.clone())),
                            env,
                            fp.type_.clone(),
                        ),
                        ..fp.clone()
                    },
                    _ => fp.clone(),
                })
                .collect();
            FunType {
                params: ft_params,
                tparams: ft_tparams,
                ..ft
            }
        } else {
            ft
        };
        // Bind any quantifiers in the function type; these are unbound after typing the body
        env::add_generic_parameters_with_bounds(env, &ft.tparams);
        env::clear_params(env);
        // `List.split_n ft.ft_params (List.length f.f_params)`
        let n = std::cmp::min(f.params.len(), ft.params.len());
        let (param_ft_params, extra_ft_params) = ft.params.split_at(n);
        // `List.zip_exn f.f_params param_ft_params`
        if f.params.len() != param_ft_params.len() {
            panic!("Invalid_argument: List.zip_exn: length mismatch")
        }
        let param_ft_pairs: Vec<(&nast::FunParam, &FunParam)> =
            f.params.iter().zip(param_ft_params.iter()).collect();
        let is_positional_variadic = |param: &nast::FunParam| {
            crate::aast_utils::is_param_variadic(param) && param.named.is_none()
        };
        let non_variadic_ft_params: Vec<FunParam> = param_ft_pairs
            .iter()
            .filter_map(|(param, fp)| {
                if crate::aast_utils::is_param_variadic(param) {
                    None
                } else {
                    Some((*fp).clone())
                }
            })
            .collect();
        // A positional variadic can capture additional fixed parameters and the
        // variadic parameter of the expected function type. For example, when
        // (int $first, ...$rest, named bool $flag) ==> {} is supplied where
        // (function(int, int, int..., named bool $flag): void) is expected,
        // $rest captures both the second int and the remaining variadic ints.
        // Its vector element type is the union of its own resolved type and
        // these additional positional types. Named arguments do not enter it.
        let variadic_ft_types: Vec<Ty> = param_ft_pairs
            .iter()
            .filter_map(|(param, fp)| {
                if is_positional_variadic(param) {
                    Some(fp.type_.clone())
                } else {
                    None
                }
            })
            .chain(extra_ft_params.iter().filter_map(|fp| {
                if get_fp_is_named(fp) {
                    None
                } else {
                    Some(fp.type_.clone())
                }
            }))
            .collect();
        let make_variadic_arg = |env: &mut Env, varg: &nast::FunParam| {
            let r = reason::var_param(varg.pos.clone());
            let union = Ty_::Tunion(variadic_ft_types.clone());
            let t_param = closure_bind_variadic(env, varg, mk((r, union)));
            vec![t_param]
        };
        let t_variadic_params: Vec<tast::FunParam> =
            match f.params.iter().find(|p| is_positional_variadic(p)) {
                Some(arg) => make_variadic_arg(env, arg),
                None => vec![],
            };
        let non_variadic_params: Vec<nast::FunParam> = f
            .params
            .iter()
            .filter(|p| !crate::aast_utils::is_param_variadic(p))
            .cloned()
            .collect();
        let (t_params, _) = {
            let mut acc: (Vec<tast::FunParam>, &[nast::FunParam]) =
                (vec![], &non_variadic_params[..]);
            for x in non_variadic_ft_params.iter().map(|x| x.type_.clone()) {
                acc = closure_bind_param(env, acc, x);
            }
            acc
        };
        env::set_fn_kind(env, f.fun_kind);
        let decl_ty = f
            .ret
            .1
            .as_ref()
            .map(|h| crate::decl_hint::hint(&env.decl_env, h));
        let hint_pos = match &f.ret.1 {
            Some(aast::Hint(ret_pos, _)) => ret_pos.clone(),
            None => lambda_pos.clone(),
        };
        let ety_env = empty_expand_env_with_on_error(
            env::invalid_type_hint_assert_primary_pos_in_current_decl(env),
        );
        let ety_env = ExpandEnv {
            wildcard_action: WildcardAction::WildcardFreshTyvar,
            ..ety_env
        };
        let this_class = self_class_opt(env);
        let params_decl_ty: Vec<Option<DeclTy>> = decl_ft
            .params
            .iter()
            .map(|fp| {
                if is_wildcard(&fp.ty) {
                    None
                } else {
                    Some(fp.ty.clone())
                }
            })
            .collect();
        // Do we need to re-check the body of the lambda under dynamic assumptions?
        let sdt_dynamic_check_required = support_dynamic_type
            && !(crate::typing_dynamic::function_parameters_safe_for_dynamic(
                this_class.as_ref(),
                env,
                &params_decl_ty,
            ));
        // We wrap result type in supportdyn if it's explicit and dynamic check isn't required.
        // This is an easy way to ensure that the return values support dynamic.
        let wrap_return_supportdyn = support_dynamic_type && !sdt_dynamic_check_required;
        let hret = crate::typing_return::make_return_type(
            &ety_env,
            this_class.as_ref(),
            Some(false),
            wrap_return_supportdyn,
            env,
            hint_pos.clone(),
            decl_ty,
            ret_ty,
        );
        let ft = FunType {
            ret: hret.clone(),
            ..ft
        };
        let return_info = crate::typing_return::make_info(
            Some(ignore_readonly),
            hint_pos.clone(),
            f.fun_kind,
            &[],
            env,
            hret.clone(),
        );
        env::set_return(env, return_info);
        let local_tpenv = env::get_tpenv(env);
        let sound_dynamic_check_saved_env = env.clone();
        let (tb, had_errors) =
            diagnostics_state::run_and_check_for_errors(|| stmt::block(env, &f.body.fb_ast.0));
        let has_implicit_return = lenv::has_next(env);
        if !has_implicit_return {
        } else {
            crate::typing_return::fun_implicit_return(
                env,
                lambda_pos.clone(),
                hret.clone(),
                f.fun_kind,
            )
        }
        // For an SDT lambda that doesn't have a second check under dynamic assumptions,
        // and with an inferred return type, we must check that the return type supports dynamic
        if support_dynamic_type && (!sdt_dynamic_check_required) && !wrap_return_supportdyn {
            let ty_err_opt = sub_type::sub_type(
                env,
                Some(true),
                None,
                None,
                None,
                hret.clone(),
                make_type::dynamic(reason::support_dynamic_type(
                    crate::pos_or_decl::of_raw_pos(hint_pos.clone()),
                )),
                Some(reasons_callback::unify_error_at(hint_pos.clone())),
            );
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
        }
        let has_readonly = env::get_readonly(env);
        env::set_fun_tast_info(
            env,
            tast::FunTastInfo {
                has_implicit_return,
                has_readonly,
                dynamic_locals: vec![],
            },
        );
        if sdt_dynamic_check_required && !had_errors {
            // `Fn.ignore`: the environment the check returns is dropped.
            let mut sound_dynamic_check_saved_env = sound_dynamic_check_saved_env;
            let _ = check_function_dynamically_callable(
                this_class.as_ref(),
                &mut sound_dynamic_check_saved_env,
                None,
                f,
                &params_decl_ty,
                &hret,
            );
            // The following modification is independent from the line above that
            // does the dynamic check. Check status is changed to dynamic assumptions
            // within the call above. Because we don't store alternative lambdas in
            // the TAST, we unconditionally overwrite the check status to be under
            // normal assumptions here.
            env.checked = tast::CheckStatus::CUnderNormalAssumptions
        }
        let tfun_ = aast::Fun_ {
            annotation: env::save(&local_tpenv, env),
            readonly_this: f.readonly_this.clone(),
            tparams: f.tparams.clone(),
            span: f.span.clone(),
            ret: aast::TypeHint(hret, f.ret.1.clone()),
            readonly_ret: f.readonly_ret.clone(),
            fun_kind: f.fun_kind,
            user_attributes: aast::UserAttributes(user_attributes),
            body: aast::FuncBody {
                fb_ast: aast::Block(tb),
            },
            ctxs: f.ctxs.clone(),
            unsafe_ctxs: f.unsafe_ctxs.clone(),
            params: {
                let mut params = t_params;
                params.extend(t_variadic_params);
                params
            },
            external: f.external,
            hidden: false,
            doc_comment: f.doc_comment.clone(),
        };
        let ty = mk((reason::witness(lambda_pos.clone()), Ty_::Tfun(std::rc::Rc::new(ft.clone()))));
        let used_ids_ty: Vec<aast::CaptureLid<Ty>> = used_ids
            .iter()
            .map(|aast::CaptureLid(local, lid)| aast::CaptureLid(local.ty.clone(), lid.clone()))
            .collect();
        let te = crate::typing_helpers::make_simplify_typed_expr(
            env,
            lambda_pos.clone(),
            ty.clone(),
            if is_anon {
                aast::Expr_::Efun(Box::new(aast::Efun {
                    fun: tfun_,
                    use_: used_ids_ty,
                    closure_class_name,
                    is_expr_tree_virtual_expr,
                }))
            } else {
                aast::Expr_::Lfun(Box::new((tfun_, used_ids_ty)))
            },
        );
        env::set_tyvar_variance(env, None, None, &ty);
        // Finally unbind any quantifers
        env::unbind_generic_parameters(env, &ft.tparams);
        (te, ft, support_dynamic_type)
    };

    // `type_closure`:
    // Wrap the function f so that it can freely clobber function-specific
    // parts of the environment; the clobbered parts are restored before
    // returning the result. Additionally, we also prevent type parameters
    // created in the closure from unsoundly leaking into the environment
    // of the enclosing function.
    //
    // Also here we wrap `supportdyn<_>` around the function type if
    // this is an SDT function.
    let snap = crate::typing_escape::snapshot_env(env);
    let (escaping, (te, ft, support_dynamic_type)) = env::closure(env, |env| {
        stash_conts_for_closure(
            env,
            lambda_pos,
            should_invalidate_fakes,
            is_expr_tree_virtual_expr,
            is_anon,
            used_ids,
            |env| {
                let res = type_closure_f(env);
                // Any quantifiers in the function type won't appear in the
                // snapshot so we have to ensure they aren't mistaken for
                // escaping rigid tyvars
                let escaping = crate::typing_escape::escaping_from_snapshot(&snap, env, &quants);
                (escaping, res)
            },
        )
    });
    // After the body of the function is checked, erase all the type parameters
    // created from the env and the return type.
    let ret_ty = crate::typing_escape::refresh_env_and_type(
        escaping,
        lambda_pos.clone(),
        env,
        ft.ret.clone(),
    );
    (te, FunType { ret: ret_ty, ..ft }, support_dynamic_type)
}

pub(crate) fn lambda(
    should_invalidate_fakes: bool,
    is_anon: bool,
    closure_class_name: Option<String>,
    is_expr_tree_virtual_expr: bool,
    expected: Option<&expected_ty::T>,
    p: &Pos,
    env: &mut Env,
    f: &nast::Fun_,
    used_ids: &[nast::CaptureLid],
) -> (tast::Expr, Ty) {
    // This is the function type as declared on the lambda itself.
    // If type hints are absent then use Twildcard instead.
    let declared_fe = crate::decl_nast::lambda_decl_in_env(&env.decl_env, f);
    let FunElt {
        ty: fe_type,
        pos: fe_pos,
        ..
    } = &declared_fe;
    let (declared_pos, declared_ft): (PosOrDecl, DeclFunType) = match fe_type.node_ref() {
        ty::decl::Ty_::Tfun(ft) => (fe_pos.clone().to_oxidized(), (**ft).clone()),
        _ => panic!("Not a function"),
    };
    let declared_decl_ft = crate::typing_enforceability::compute_enforced_and_pessimize_fun_type(
        self_class_opt(env).as_ref(),
        env,
        declared_ft,
    );
    // When creating a closure, the 'this' type will mean the late bound type
    // of the current enclosing class
    let ety_env = empty_expand_env_with_on_error(
        env::invalid_type_hint_assert_primary_pos_in_current_decl(env),
    );
    // If this is a polymorphic lambda we don't want to substitute any type parameter
    // bound in the lambda signature
    let no_substs: im::OrdSet<String> = if !declared_decl_ft.instantiated {
        declared_decl_ft
            .tparams
            .iter()
            .map(|tp| tp.name.id_ref().as_str().to_string())
            .collect()
    } else {
        im::OrdSet::new()
    };
    // For Twildcard types, generate fresh type variables
    let ety_env = ExpandEnv {
        wildcard_action: WildcardAction::WildcardFreshTyvar,
        no_substs,
        ..ety_env
    };
    let (ty_err_opt, declared_ft) = phase::localize_ft(
        Some(phase::MethodInstantiation {
            use_name: "lambda".to_string(),
            use_pos: p.clone(),
            explicit_targs: vec![],
        }),
        &ety_env,
        declared_pos,
        env,
        &declared_decl_ft,
    );
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    let restore_pos = env::set_inference_env_pos(env, Some(p.clone()));
    // `List.map`: from left to right.
    let used_ids: Vec<aast::CaptureLid<Local>> = used_ids
        .iter()
        .map(|aast::CaptureLid((), id)| {
            // Check that none of the explicit capture variables are from a using clause
            check_escaping_var(env, id);

            let ty = env::get_local(env, &id.1);
            aast::CaptureLid(ty, id.clone())
        })
        .collect();

    // Is the return type declared?
    let is_explicit = f.ret.1.is_some();
    let check_body_under_known_params = |ty_mismatch_opt: Option<(Ty, Ty)>,
                                         supportdyn: bool,
                                         ignore_readonly: Option<bool>,
                                         env: &mut Env,
                                         ret_ty: Option<Ty>,
                                         ft: FunType|
     -> (tast::Expr, Ty) {
        let ignore_readonly = ignore_readonly.unwrap_or(false);
        let (tefun, ft, support_dynamic_type) = closure_make(
            ret_ty,
            supportdyn,
            closure_class_name,
            is_expr_tree_virtual_expr,
            should_invalidate_fakes,
            Some(ignore_readonly),
            env,
            p,
            &declared_decl_ft,
            f,
            ft,
            &used_ids,
            is_anon,
        );
        let ty = mk((reason::witness(p.clone()), Ty_::Tfun(std::rc::Rc::new(ft))));
        let ty = if support_dynamic_type {
            make_type::supportdyn(reason::witness(p.clone()), ty)
        } else {
            ty
        };
        let tefun = hole_on_ty_mismatch(tefun, ty_mismatch_opt);
        restore_pos(env);
        (tefun, ty)
    };
    let eexpected = env_help::expand_expected_opt(true, true, env, expected);
    match &eexpected {
        // When we're in a dynamic pass of a function (or closure) don't type inner closures
        // at all, simply assign them a dynamic type.
        // Exception: we're checking an expression tree. Even in the dynamic pass,
        // maketree_with_type_param needs the lambda to be typed precisely.
        _ if tast::is_under_dynamic_assumptions(env.checked) => {
            restore_pos(env);
            make_result(
                env,
                p.clone(),
                aast::Expr_::Omitted,
                make_type::dynamic(reason::witness(p.clone())),
            )
        }
        Some((_pos, _ur, supportdyn, ty, Ty_::Tfun(expected_ft), expected_ignore_readonly))
            if expected_ft.instantiated =>
        {
            // First check that arities match up
            let arity_ok = check_lambda_arity(env, p, &get_pos(ty), &declared_ft, expected_ft);
            // Use declared types for parameters in preference to those determined
            // by the context (expected parameters): they might be more general.
            fn replace_non_declared_types(
                declared_ft_variadic: bool,
                expected_ft_variadic: bool,
                declared_decl_ft_params: &[DeclFunParam],
                declared_ft_params: &[FunParam],
                expected_ft_params: &[FunParam],
            ) -> Vec<FunParam> {
                match (
                    declared_decl_ft_params,
                    declared_ft_params,
                    expected_ft_params,
                ) {
                    (
                        [declared_decl_ft_param, declared_decl_ft_params @ ..],
                        [declared_ft_param, declared_ft_params @ ..],
                        [expected_ft_param, expected_ft_params @ ..],
                    ) => {
                        let rest = replace_non_declared_types(
                            declared_ft_variadic,
                            expected_ft_variadic,
                            declared_decl_ft_params,
                            declared_ft_params,
                            expected_ft_params,
                        );
                        // If the type parameter did not have a type hint, it is Twildcard and
                        // we use the expected type instead. Otherwise, declared type takes
                        // precedence.
                        let resolved_ft_param = if is_wildcard(&declared_decl_ft_param.ty) {
                            FunParam {
                                type_: expected_ft_param.type_.clone(),
                                ..declared_ft_param.clone()
                            }
                        } else {
                            declared_ft_param.clone()
                        };
                        let mut l = vec![resolved_ft_param];
                        l.extend(rest);
                        l
                    }
                    (_, _, []) => {
                        // Morally, this case should match on ([],[]) because we already
                        // check arity mismatch between declared and expected types. We
                        // handle it more generally here to be graceful.
                        declared_ft_params.to_vec()
                    }
                    ([], [], _) => {
                        if (!declared_ft_variadic) && expected_ft_variadic {
                            vec![]
                        } else {
                            // This means the expected_ft params list can have more positional parameters
                            // than declared parameters in the lambda.
                            expected_ft_params
                                .iter()
                                .filter(|fp| !get_fp_is_named(fp))
                                .cloned()
                                .collect()
                        }
                    }
                    _ => panic!("declared_decl_ft_params length not same as declared_ft_params"),
                }
            }
            let expected_ft = FunType {
                params: replace_non_declared_types(
                    get_ft_variadic(&declared_ft),
                    get_ft_variadic(expected_ft),
                    &declared_decl_ft.params,
                    &declared_ft.params,
                    &expected_ft.params,
                ),
                implicit_params: declared_ft.implicit_params.clone(),
                flags: declared_ft.flags,
                ..FunType::clone(&expected_ft)
            };
            // Don't bother passing in `void` if there is no explicit return
            let ret_ty = match get_node(&expected_ft.ret) {
                Ty_::Tprim(ast_defs::Tprim::Tvoid) if !is_explicit => None,
                _ => Some(expected_ft.ret.clone()),
            };
            crate::typing_log::increment_feature_count(env, fl::lambda::contextual_params);
            let ty_mismatch_opt = if arity_ok {
                None
            } else {
                Some((
                    mk((reason::none(), Ty_::Tfun(std::rc::Rc::new(declared_ft.clone())))),
                    ty.clone(),
                ))
            };
            check_body_under_known_params(
                ty_mismatch_opt,
                *supportdyn,
                Some(*expected_ignore_readonly),
                env,
                ret_ty,
                expected_ft,
            )
        }
        _ => {
            // Extract ignore_readonly from expected type if present
            let expected_ignore_readonly = match &eexpected {
                Some((_, _, _, _, _, ignore_readonly)) => *ignore_readonly,
                None => false,
            };
            // If all parameters are annotated with explicit types, then type-check
            // the body under those assumptions and pick up the result type
            let all_explicit_params = f.params.iter().all(|param| param.type_hint.1.is_some());
            if all_explicit_params {
                crate::typing_log::increment_feature_count(
                    env,
                    if f.params.is_empty() {
                        fl::lambda::no_params
                    } else {
                        fl::lambda::explicit_params
                    },
                );
                env::set_tyvar_variance(
                    env,
                    None,
                    None,
                    &mk((reason::none(), Ty_::Tfun(std::rc::Rc::new(declared_ft.clone())))),
                );
                check_body_under_known_params(
                    None,
                    false,
                    Some(expected_ignore_readonly),
                    env,
                    None,
                    declared_ft,
                )
            } else {
                match &eexpected {
                    Some((_pos, _ur, supportdyn, expected_ty, _, _))
                        if tutils::is_mixed(env, expected_ty)
                            || is_nonnull(expected_ty)
                            || is_dynamic(expected_ty) =>
                    {
                        // If the expected type of a lambda is mixed, nonnull or dynamic,
                        // or supportdyn of these, we construct a function type where the
                        // undeclared parameters are set to mixed (when expected type of
                        // lambda is mixed or nonnull), or dynamic (when expected type of
                        // lambda is dynamic). Wrap mixed or nonnull in supportdyn if the
                        // expected type is supportdyn.
                        // We leave the return type alone, inferring it if necessary.
                        //
                        // For an expected mixed/nonnull type, one could argue that the lambda
                        // doesn't even need to be checked as it can't be called (there is
                        // no downcast to function type). Thus, we should be using nothing
                        // to type the arguments. But generally users are very confused by
                        // the use of nothing and would expect the lambda body to be
                        // checked as though it could be called.
                        let r = reason::witness(p.clone());
                        let param_type = if is_dynamic(expected_ty) {
                            make_type::dynamic(r)
                        } else if *supportdyn {
                            make_type::supportdyn(r.clone(), make_type::mixed(r))
                        } else {
                            make_type::mixed(r)
                        };
                        let replace_non_declared_type =
                            |declared_decl_ft_param: &DeclFunParam,
                             declared_ft_param: &FunParam| {
                                let is_undeclared = is_wildcard(&declared_decl_ft_param.ty);
                                if is_undeclared {
                                    FunParam {
                                        type_: param_type.clone(),
                                        ..declared_ft_param.clone()
                                    }
                                } else {
                                    declared_ft_param.clone()
                                }
                            };
                        let expected_ft = {
                            // `List.map2_exn`
                            if declared_decl_ft.params.len() != declared_ft.params.len() {
                                panic!(
                                    "length mismatch in map2_exn: {} <> {}",
                                    declared_decl_ft.params.len(),
                                    declared_ft.params.len()
                                )
                            }
                            let ft_params: Vec<FunParam> = declared_decl_ft
                                .params
                                .iter()
                                .zip(declared_ft.params.iter())
                                .map(|(ddp, dp)| replace_non_declared_type(ddp, dp))
                                .collect();
                            FunType {
                                params: ft_params,
                                ..declared_ft
                            }
                        };
                        check_body_under_known_params(
                            None,
                            *supportdyn,
                            Some(expected_ignore_readonly),
                            env,
                            None,
                            expected_ft,
                        )
                    }
                    _ => {
                        // Missing types in parameter and result will have been replaced by fresh type variables
                        crate::typing_log::increment_feature_count(
                            env,
                            fl::lambda::fresh_tyvar_params,
                        );
                        let declared_ty = mk((reason::none(), Ty_::Tfun(std::rc::Rc::new(declared_ft.clone()))));
                        let supportdyn = env::get_support_dynamic_type(env);
                        let declared_ty = if supportdyn {
                            make_type::supportdyn(reason::none(), declared_ty)
                        } else {
                            declared_ty
                        };
                        check_expected_ty("Lambda", env, &declared_ty, expected);
                        env::set_tyvar_variance(env, None, None, &declared_ty);
                        // TODO(jjwu): the declared_ft here is set to public,
                        // but is actually inferred from the surrounding context
                        // (don't think this matters in practice, since we check lambdas separately)
                        let ret_ty = declared_ft.ret.clone();
                        check_body_under_known_params(
                            None,
                            supportdyn,
                            Some(expected_ignore_readonly),
                            env,
                            Some(ret_ty),
                            declared_ft,
                        )
                    }
                }
            }
        }
    }
}
