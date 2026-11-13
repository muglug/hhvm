// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_toplevel.ml`. See `hh/PORTING.md`.
//!
//! This module implements the typing.
//!
//! Given an Nast.program, it infers the type of all the local
//! variables, and checks that all the types are correct (aka
//! consistent)
//!
//! # Notes on the port
//!
//! - `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
//!   custom_err_config)` is [`add_naming_error`]: the renderer of naming
//!   errors of this crate (`crate::naming_errors`) does not take the custom
//!   error configuration of the options (as in `typing_env`).
//! - `Nast_check.program ctx nast` has no Rust function of that name:
//!   `crate::nast_check` runs its checks with `check_program`, which collects
//!   the diagnostics instead of adding them. [`nast_check_program`] adds what
//!   it collects. `check_program` also runs `Nast_init_check` on each class,
//!   which the OCaml runs from `Typing_class` (see `typing_class.rs`). It is
//!   run without comments, so that `add_diagnostic` is what applies the
//!   `HH_FIXME`s (see `typing_check_job.rs`). `Nast_check.program` visits the
//!   definitions in the order of the program (all of them with the checks of
//!   `Nast_visitor`, then all of them with the stateful ones); the Rust checks
//!   go through them by kind (functions, classes, typedefs, constants,
//!   modules), each one with all the checks. Only the order in which the
//!   errors are added differs.
//! - `Aast.map_class_alias` (`[@@deriving map]`) is [`map_class_alias`].

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::custom_error_config::CustomErrorConfig;
use oxidized::file_info::NameType;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::scoured_comments::ScouredComments;

use crate::counters;
use crate::ctx::Ctx;
use crate::decl_counters;
use crate::decl_hint;
use crate::decl_provider;
use crate::decl_utils;
use crate::diagnostics_state;
use crate::hack_event_logger;
use crate::naming_attributes;
use crate::provider_context;
use crate::relative_path;
use crate::tast;
use crate::tast_check;
use crate::tast_with_dynamic;
use crate::typechecker_options;
use crate::typechecker_options::TypecheckerOptions;
use crate::typing_coeffects;
use crate::typing_coercion;
use crate::typing_defs::empty_expand_env_with_on_error;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::get_reason;
use crate::typing_dynamic;
use crate::typing_enforceability;
use crate::typing_env as env;
use crate::typing_env_from_def as env_from_def;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_helpers;
use crate::typing_helpers::expected_ty;
use crate::typing_make_type as make_type;
use crate::typing_memoize;
use crate::typing_native;
use crate::typing_param;
use crate::typing_phase as phase;
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
use crate::typing_return;
use crate::typing_solver;
use crate::typing_subtype;
use crate::typing_toplevel_enable as enable;
use crate::typing_toplevel_profile as profile;
use crate::typing_type_wellformedness;
use crate::worker_cancel;

/// `Naming_special_names.Capabilities.accessGlobals` (missing from
/// `naming_special_names_rust`).
const ACCESS_GLOBALS: &str = "\\HH\\Capabilities\\AccessGlobals";

/// `Naming_special_names.AttributeKinds.module_` (missing from
/// `naming_special_names_rust`).
const ATTRIBUTE_KINDS_MODULE: &str = "\\HH\\ModuleAttribute";

/// `Naming_special_names.UnstableFeatures.recursive_case_types` (missing from
/// `naming_special_names_rust`).
const RECURSIVE_CASE_TYPES: &str = "recursive_case_types";

/// `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
/// custom_err_config)`. The renderer of naming errors of this crate does not
/// take the custom error configuration.
fn add_naming_error(err: NamingError, _custom_err_config: CustomErrorConfig) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(err)) {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Nast_check.program ctx nast`: the checks of `crate::nast_check`, whose
/// diagnostics are added in the order they were found. No comments are
/// given, so that the checks drop nothing: `add_diagnostic` applies the
/// `HH_FIXME`s (and `drop_fixmed`), as `Diagnostics.add_diagnostic` does in
/// the OCaml.
fn nast_check_program(ctx: &Arc<Ctx>, nast: &nast::Program) {
    let mut diagnostics = vec![];
    crate::nast_check::check_program_with_comments(
        ctx,
        nast,
        &ScouredComments::default(),
        &mut diagnostics,
    );
    for diagnostic in diagnostics {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Option.iter ~f:(Typing_error_utils.add_typing_error ~env)`
fn add_typing_error_opt(env: &Env, err: &Option<typing_error::T>) {
    if let Some(err) = err {
        typing_error_utils::add_typing_error(err, env)
    }
}

/// `Option.merge ~f:Typing_error.both`
fn merge_errors(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2) {
        (None, e2) => e2,
        (e1, None) => e1,
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
    }
}

fn check_if_this_def_is_the_winner(ctx: &Arc<Ctx>, name_type: NameType, id: &ast_defs::Id) -> bool {
    let ast_defs::Id(pos, name) = id;
    if name.is_empty() || name == "\\" {
        // In case of some parse errors, the AST contains definitions with empty names.
        // There's no useful duplicate-name-check we can do here.
        // Return [false] because there's no such thing as the winner for the empty name.
        false
    } else {
        match decl_provider::is_this_def_the_winner(ctx, name_type, id) {
            decl_provider::Winner::Winner => true,
            decl_provider::Winner::Loser_to(prev_pos) => {
                let custom_err_config =
                    typechecker_options::custom_error_config(&provider_context::get_tcopt(ctx));
                add_naming_error(
                    NamingError::ErrorNameAlreadyBound {
                        name: name.clone(),
                        pos: pos.clone(),
                        prev_pos,
                    },
                    custom_err_config,
                );
                false
            }
            decl_provider::Winner::Not_found => {
                // This is impossible! The fact that we have an AST def for [name] implies
                // that Decl_provider should be able to find at least one decl with this name.
                // Only explanations are (1) weirdness with Provider_context.entry which
                // gives slightly different answers from what direct-decl-parser provides
                // e.g. in case of incorrect parse trees, or order of winner; (2) disk race
                // where the file on disk has changed but we haven't yet updated naming table.
                let pos_s = crate::pos::string(&crate::pos::to_relative_string(pos));
                hack_event_logger::decl_consistency_bug(
                    None,
                    Some(&pos_s),
                    Some(name),
                    "Decl consistency: Ast definition but no decl",
                );
                false
            }
        }
    }
}

/// If it takes longer than `--config timeout=<secs>` then produces None.
/// Otherwise, it returns either 1 or 2 tasts, depending on whether sound-dynamic is enabled.
pub fn fun_def(ctx: &Arc<Ctx>, fd: &nast::FunDef) -> Option<tast_with_dynamic::T<tast::FunDef>> {
    let filename = fd.name.0.filename();
    if provider_context::get_popt(ctx).ignore_string_methods
        && relative_path::is_hhi(relative_path::prefix(filename))
        && relative_path::suffix(filename) == "string.hhi"
    {
        None
    } else {
        let tcopt = provider_context::get_tcopt(ctx);
        enable::if_matches_regexp(None, &tcopt, None, &fd.name, || {
            let f = &fd.fun;
            profile::measure_elapsed_time_and_report(&tcopt, None, &fd.name, || {
                counters::count(counters::category::T::Typing_toplevel, || {
                    diagnostics_state::run_with_span(f.span.clone(), || {
                        let _: bool = check_if_this_def_is_the_winner(ctx, NameType::Fun, &fd.name);
                        let env = env_from_def::fun_env(
                            Some(decl_counters::Origin::TopLevel),
                            Arc::clone(ctx),
                            fd,
                        );
                        typing_helpers::with_timeout(&env, &fd.name, |env| {
                            fun_def_with_env(&tcopt, fd, env)
                        })
                    })
                })
            })
        })
    }
}

/// The body of `fun_def` that `with_timeout env fd.fd_name` runs.
fn fun_def_with_env(
    tcopt: &TypecheckerOptions,
    fd: &nast::FunDef,
    env: &mut Env,
) -> tast_with_dynamic::T<tast::FunDef> {
    let f = &fd.fun;
    let mem = |x: &str| naming_attributes::mem(x, &f.user_attributes.0);
    let pos = fd.name.0.clone();
    env::open_tyvars(env, fd.name.0.clone());
    env::set_env_callable_pos(env, pos.clone());
    env::set_env_function_pos(env, f.span.clone());
    let restore_pos = env::set_inference_env_pos(env, Some(pos.clone()));
    // Set the package membership before checking attributes so that package
    // boundary checks on attribute classes (for strict-isolation packages) see
    // the correct current package.
    env::set_current_package_membership(env, fd.package.clone());
    let user_attributes =
        crate::typing::attributes_check_def(env, sn::attribute_kinds::FN, &f.user_attributes.0);
    let file_attrs = crate::typing::file_attributes(env, &fd.file_attributes);
    let (cap_ty, unsafe_cap_ty) =
        typing_coeffects::type_capability(env, f.ctxs.as_ref(), f.unsafe_ctxs.as_ref(), &fd.name.0);
    env::set_current_module(env, fd.module.clone());
    env::set_internal(env, fd.internal);
    env::set_soft_package_from_attr(env, &f.user_attributes.0);
    if mem(sn::user_attributes::SUPPORT_DYNAMIC_TYPE)
        || mem(sn::user_attributes::DYNAMICALLY_CALLABLE)
    {
        env::set_support_dynamic_type(env, true)
    }
    let no_auto_likes = mem(sn::user_attributes::NO_AUTO_LIKES);
    if no_auto_likes {
        env::set_no_auto_likes(env, true)
    }
    env::assert_packages_loaded_from_attr(env, &f.user_attributes.0);
    // Is sound dynamic enabled, and the function marked <<__SupportDynamicType>> explicitly or implicitly?
    let sdt_function = env::get_support_dynamic_type(env);
    for err in typing_type_wellformedness::fun_def(env, fd) {
        typing_error_utils::add_typing_error(&err, env)
    }
    env::make_depend_on_current_module(env);
    let ty_err_opt = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
        env,
        false,
        &fd.tparams,
        &fd.where_constraints,
    );
    add_typing_error_opt(env, &ty_err_opt);
    env::set_fn_kind(env, f.fun_kind);
    let (return_decl_ty, params_decl_ty) = typing_helpers::hint_fun_decl(&f.params, &f.ret, env);
    let hint_pos = match &f.ret.1 {
        None => fd.name.0.clone(),
        Some(aast::Hint(pos, _)) => pos.clone(),
    };
    // Do we need to check the body of the function again, under dynamic assumptions?
    let sdt_dynamic_check_required = sdt_function
        && !typing_dynamic::function_parameters_safe_for_dynamic(None, env, &params_decl_ty);
    let ety_env =
        empty_expand_env_with_on_error(reasons_callback::invalid_type_hint(hint_pos.clone()));
    let return_ty = typing_return::make_return_type(
        &ety_env,
        None,
        None,
        sdt_function && !sdt_dynamic_check_required,
        env,
        hint_pos.clone(),
        return_decl_ty,
        None,
    );
    let return_ = typing_return::make_info(
        None,
        hint_pos.clone(),
        f.fun_kind,
        &f.user_attributes.0,
        env,
        return_ty.clone(),
    );
    let _ = typing_coeffects::register_capabilities(env, cap_ty.clone(), unsafe_cap_ty);
    let sound_dynamic_check_saved_env = env.clone();
    let param_tys =
        typing_param::make_param_local_tys(false, no_auto_likes, env, &params_decl_ty, &f.params);
    let can_read_globals = typing_subtype::is_sub_type(
        env,
        &cap_ty,
        &make_type::capability(get_reason(&cap_ty).clone(), ACCESS_GLOBALS.to_string()),
    );
    let typed_params = crate::typing::bind_params(
        env,
        Some(can_read_globals),
        no_auto_likes,
        f.ctxs.as_ref(),
        &param_tys,
        &f.params,
    );
    typing_helpers::set_tyvars_variance_in_callable(env, &return_ty, &param_tys);
    let local_tpenv = env::get_tpenv(env);
    let disable = mem(sn::user_attributes::DISABLE_TYPECHECKER_INTERNAL);
    typing_memoize::check_function(env, f);
    typing_memoize::check_erased_generics(
        env,
        &f.user_attributes.0,
        &fd.tparams,
        &f.params,
        &f.ret,
    );
    let (tb, had_errors) = diagnostics_state::run_and_check_for_errors(|| {
        let native = typing_native::is_native_fun(env, f);
        crate::typing::fun_(
            None,
            Some(native),
            Some(disable),
            env,
            return_,
            &pos,
            &f.body,
            f.fun_kind,
        )
    });
    match &f.ret.1 {
        None => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Expecting_return_type_hint(pos.clone())),
            env,
        ),
        Some(_) => {}
    }
    let tparams: Vec<tast::Tparam> = fd
        .tparams
        .iter()
        .map(|tp| crate::typing::type_param(env, tp))
        .collect();
    let e1 = typing_solver::close_tyvars_and_solve(env);
    let e2 = typing_solver::solve_all_unsolved_tyvars(env);
    let ret_hint = f.ret.1.clone();
    let fun_ = aast::Fun_ {
        annotation: env::save(&local_tpenv, env),
        readonly_this: f.readonly_this,
        // For function definitions the declared type parameters appear on the
        // definition rather then function - see [fd_tparams] below
        tparams: vec![],
        span: f.span.clone(),
        readonly_ret: f.readonly_ret,
        ret: aast::TypeHint(return_ty.clone(), ret_hint.clone()),
        params: typed_params,
        ctxs: f.ctxs.clone(),
        unsafe_ctxs: f.unsafe_ctxs.clone(),
        fun_kind: f.fun_kind,
        user_attributes: aast::UserAttributes(user_attributes),
        body: aast::FuncBody {
            fb_ast: aast::Block(tb),
        },
        external: f.external,
        hidden: false,
        doc_comment: f.doc_comment.clone(),
    };
    let under_normal_assumptions = aast::FunDef {
        mode: fd.mode,
        name: fd.name.clone(),
        fun: fun_,
        file_attributes: file_attrs,
        namespace: fd.namespace.clone(),
        internal: fd.internal,
        module: fd.module.clone(),
        tparams,
        where_constraints: fd.where_constraints.clone(),
        package: fd.package.clone(),
    };
    // `{ under_normal_assumptions with fd_fun = { under_normal_assumptions.fd_fun
    // with f_annotation; f_ret; f_params; f_body } }`: the fields that are
    // replaced are not copied.
    let fundef_of_dynamic = |under_normal_assumptions: &tast::FunDef,
                             (dynamic_env, dynamic_params, dynamic_body, dynamic_return_ty): (
        Env,
        Vec<tast::FunParam>,
        Vec<tast::Stmt>,
        Ty,
    )|
     -> tast::FunDef {
        let u = under_normal_assumptions;
        aast::FunDef {
            mode: u.mode,
            name: u.name.clone(),
            fun: aast::Fun_ {
                annotation: env::save(&local_tpenv, &dynamic_env),
                readonly_this: u.fun.readonly_this,
                tparams: u.fun.tparams.clone(),
                span: u.fun.span.clone(),
                readonly_ret: u.fun.readonly_ret,
                ret: aast::TypeHint(dynamic_return_ty, ret_hint.clone()),
                params: dynamic_params,
                ctxs: u.fun.ctxs.clone(),
                unsafe_ctxs: u.fun.unsafe_ctxs.clone(),
                fun_kind: u.fun.fun_kind,
                user_attributes: u.fun.user_attributes.clone(),
                body: aast::FuncBody {
                    fb_ast: aast::Block(dynamic_body),
                },
                external: u.fun.external,
                hidden: u.fun.hidden,
                doc_comment: u.fun.doc_comment.clone(),
            },
            file_attributes: u.file_attributes.clone(),
            namespace: u.namespace.clone(),
            internal: u.internal,
            module: u.module.clone(),
            tparams: u.tparams.clone(),
            where_constraints: u.where_constraints.clone(),
            package: u.package.clone(),
        }
    };
    let (under_normal_assumptions, under_dynamic_assumptions) =
        if sdt_dynamic_check_required && !had_errors && !tcopt.tco_skip_check_under_dynamic {
            // `let env = { env with checked = Tast.CUnderNormalAssumptions }`: this
            // environment is only used here.
            let mut env = env.clone();
            env.checked = tast::CheckStatus::CUnderNormalAssumptions;
            let f_annotation = env::save(&local_tpenv, &env);
            let mut dynamic_env = sound_dynamic_check_saved_env;
            let (dynamic_params, dynamic_body, dynamic_return_ty) =
                crate::typing::check_function_dynamically_callable(
                    None,
                    &mut dynamic_env,
                    Some(&fd.name),
                    f,
                    &params_decl_ty,
                    &return_ty,
                );
            let under_dynamic_assumptions = fundef_of_dynamic(
                &under_normal_assumptions,
                (dynamic_env, dynamic_params, dynamic_body, dynamic_return_ty),
            );
            let mut under_normal_assumptions = under_normal_assumptions;
            under_normal_assumptions.fun.annotation = f_annotation;
            (under_normal_assumptions, Some(under_dynamic_assumptions))
        } else {
            (under_normal_assumptions, None)
        };
    restore_pos(env);
    let ty_err_opt = merge_errors(e1, e2);
    add_typing_error_opt(env, &ty_err_opt);
    tast_with_dynamic::T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    }
}

/// If the input is the winning definition of its symbol,
/// returns [Some t] and as a side effect populates errors encountered
/// during typechecking. If not the winning definition, returns None
/// and emits a "duplicate name" error. (We're not able to check
/// a class that isn't the winning declaration, because we use both
/// the AST and the folded-decl in the work of checking, and the only
/// folded-decl available is that of the winner, so we can't proceed
/// if this definition isn't the winner.
///
/// If any method within the class took longer than `--config timeout=<secs>`
/// to typecheck (default infinite) then it's omitted from the resulting Tast.
pub fn class_def(
    ctx: &Arc<Ctx>,
    class_: &nast::Class_,
) -> Option<tast_with_dynamic::T<tast::Class_>> {
    counters::count(counters::category::T::Typing_toplevel, || {
        diagnostics_state::run_with_span(class_.span.clone(), || {
            if check_if_this_def_is_the_winner(ctx, NameType::Class, &class_.name) {
                // [Typing_class.class_def] is unusual in that it can't work properly
                // unless it's the winner and has the same capitalization.
                // If either isn't met, it will report to telemetry and return None.
                crate::typing_class::class_def(ctx, class_)
            } else {
                None
            }
        })
    })
}

pub fn typedef_def(ctx: &Arc<Ctx>, typedef: &nast::Typedef) -> tast::Typedef {
    let tcopt = provider_context::get_tcopt(ctx);
    profile::measure_elapsed_time_and_report(&tcopt, None, &typedef.name, || {
        diagnostics_state::run_with_span(typedef.span.clone(), || {
            let _: bool = check_if_this_def_is_the_winner(ctx, NameType::Typedef, &typedef.name);
            crate::typing_typedef::typedef_def(ctx, typedef)
        })
    })
}

pub fn gconst_def(ctx: &Arc<Ctx>, cst: &nast::Gconst) -> tast::Gconst {
    let tcopt = provider_context::get_tcopt(ctx);
    profile::measure_elapsed_time_and_report(&tcopt, None, &cst.name, || {
        counters::count(counters::category::T::Typing_toplevel, || {
            diagnostics_state::run_with_span(cst.span.clone(), || {
                let _: bool = check_if_this_def_is_the_winner(ctx, NameType::Const, &cst.name);
                let mut env = env_from_def::gconst_env(
                    Some(decl_counters::Origin::TopLevel),
                    Arc::clone(ctx),
                    cst,
                );
                let env = &mut env;
                env::set_current_package_membership(env, cst.package.clone());
                env::make_depend_on_current_module(env);
                let pos = cst.name.0.clone();
                let restore_pos = env::set_inference_env_pos(env, Some(pos));
                for err in typing_type_wellformedness::global_constant(env, cst) {
                    typing_error_utils::add_typing_error(&err, env)
                }
                let (typed_cst_value, ty_err_opt) = {
                    let value = &cst.value;
                    let aast::Expr(_, _, init) = value;
                    match (&cst.type_, init) {
                        (Some(_), aast::Expr_::Omitted) if env::is_hhi(env) => {
                            // We don't require global consts to have a value set for decl purposes
                            // in HHI files so it may just be a placeholder, therefore we don't care
                            // about checking the value and simply pass it through
                            let (te, _ty) = crate::typing::expr(None, env, value);
                            (te, None)
                        }
                        (Some(hint), _) => {
                            let ty = decl_hint::hint(&env.decl_env, hint);
                            let (enforced, ty) =
                                typing_enforceability::compute_enforced_ty(None, env, ty);
                            let (ty_err_opt1, dty) = phase::localize_no_subst(env, false, &ty);
                            let (te, value_type) = {
                                let expected = expected_ty::make(
                                    None,
                                    None,
                                    hint.0.clone(),
                                    Ureason::URhint,
                                    dty.clone(),
                                );
                                crate::typing::expr_with_pure_coeffects(Some(&expected), env, value)
                            };
                            let ty_err_opt2 = typing_coercion::coerce_type(
                                None,
                                None,
                                None,
                                hint.0.clone(),
                                Ureason::URhint,
                                env,
                                value_type,
                                dty,
                                enforced,
                                typing_error::callback::unify_error(),
                            );
                            let ty_err_opt = merge_errors(ty_err_opt1, ty_err_opt2);
                            (te, ty_err_opt)
                        }
                        (None, _) => {
                            if !decl_utils::is_literal_with_trivially_inferable_type(value)
                                && !env::is_hhi(env)
                            {
                                let custom_err_config = typechecker_options::custom_error_config(
                                    &provider_context::get_tcopt(ctx),
                                );
                                add_naming_error(
                                    NamingError::MissingTypehint(cst.name.0.clone()),
                                    custom_err_config,
                                )
                            }
                            let (te, _value_type) =
                                crate::typing::expr_with_pure_coeffects(None, env, value);
                            (te, None)
                        }
                    }
                };

                add_typing_error_opt(env, &ty_err_opt);
                restore_pos(env);
                aast::Gconst {
                    annotation: env::save(&env::get_tpenv(env), env),
                    mode: cst.mode,
                    name: cst.name.clone(),
                    type_: cst.type_.clone(),
                    value: typed_cst_value,
                    namespace: cst.namespace.clone(),
                    span: cst.span.clone(),
                    emit_id: cst.emit_id.clone(),
                    module: cst.module.clone(),
                    package: cst.package.clone(),
                }
            })
        })
    })
}

pub fn module_def(ctx: &Arc<Ctx>, md: &nast::ModuleDef) -> tast::ModuleDef {
    counters::count(counters::category::T::Typing_toplevel, || {
        diagnostics_state::run_with_span(md.span.clone(), || {
            let _: bool = check_if_this_def_is_the_winner(ctx, NameType::Module, &md.name);
            let mut env = env_from_def::module_env(
                Some(decl_counters::Origin::TopLevel),
                Arc::clone(ctx),
                md,
            );
            let env = &mut env;
            let pos = md.name.0.clone();
            let restore_pos = env::set_inference_env_pos(env, Some(pos));
            let file_attributes = crate::typing::file_attributes(env, &md.file_attributes);
            let user_attributes = crate::typing::attributes_check_def(
                env,
                ATTRIBUTE_KINDS_MODULE,
                &md.user_attributes.0,
            );
            restore_pos(env);
            aast::ModuleDef {
                annotation: env::save(&env::get_tpenv(env), env),
                name: md.name.clone(),
                user_attributes: aast::UserAttributes(user_attributes),
                file_attributes,
                span: md.span.clone(),
                mode: md.mode,
                doc_comment: md.doc_comment.clone(),
            }
        })
    })
}

/// Apply a file-level [<<file: __EnableUnstableFeatures(...)>>] attribute to the
/// typechecker options carried by the context. Per-file check entry points must
/// run this over a definition's file attributes before checking it, otherwise
/// feature gating fires spuriously for definitions that opted into the feature.
///
/// (Both per-file check entry points, this module's [nast_to_tast] and
/// [Typing_check_job.calc_errors_and_tast], must run this before checking a
/// definition, otherwise feature gating (e.g. [__GatedByFeatureFlag]) fires
/// spuriously for definitions that legitimately opted into an unstable feature.)
pub fn set_tcopt_unstable_features(ctx: &Arc<Ctx>, fa: &nast::FileAttribute) -> Arc<Ctx> {
    match naming_attributes::find(
        sn::user_attributes::ENABLE_UNSTABLE_FEATURES,
        &fa.user_attributes.0,
    ) {
        None => Arc::clone(ctx),
        Some(aast::UserAttribute {
            name: _,
            params: ua_params,
        }) => {
            let mut ctx = Arc::clone(ctx);
            for aast::Expr(_, _, feature) in ua_params {
                match feature {
                    aast::Expr_::String(s) => {
                        let s = String::from_utf8_lossy(s).into_owned();
                        // Always add to the unstable features set
                        ctx = provider_context::map_tcopt(&ctx, |t| {
                            let mut tco_enabled_unstable_features =
                                t.tco_enabled_unstable_features.clone();
                            tco_enabled_unstable_features.insert(s.clone());
                            TypecheckerOptions {
                                tco_enabled_unstable_features,
                                ..t
                            }
                        });
                        // Then set any feature-specific options
                        if s == sn::unstable_features::EXPRESSION_TREES {
                            ctx = provider_context::map_tcopt(&ctx, |t| {
                                typechecker_options::set_tco_enable_expression_trees(t, true)
                            })
                        }
                        if s == RECURSIVE_CASE_TYPES {
                            ctx = provider_context::map_tcopt(
                                &ctx,
                                typechecker_options::enable_recursive_case_types,
                            )
                        }
                    }
                    _ => {}
                }
            }
            ctx
        }
    }
}

/// `Aast.map_class_alias on_ex on_en cr` (`[@@deriving map]`): the
/// annotations are in the user attributes of the type parameters.
fn map_class_alias(
    on_ex: &mut dyn FnMut(&()) -> Ty,
    on_en: &mut dyn FnMut(&()) -> tast::SavedEnv,
    cr: &nast::ClassAlias,
) -> aast::ClassAlias<Ty, tast::SavedEnv> {
    let mut mapper = crate::typing::prelude::aast_map::Map { on_ex, on_en };
    let mut map_tparam = |tp: &nast::Tparam| -> tast::Tparam {
        aast::Tparam {
            variance: tp.variance,
            name: tp.name.clone(),
            constraints: tp.constraints.clone(),
            reified: tp.reified,
            user_attributes: aast::UserAttributes(
                tp.user_attributes
                    .0
                    .iter()
                    .map(|ua| aast::UserAttribute {
                        name: ua.name.clone(),
                        params: ua.params.iter().map(|e| mapper.on_expr(e)).collect(),
                    })
                    .collect(),
            ),
        }
    };
    let aast::ClassAlias {
        name,
        tparams,
        original,
        original_tparams,
    } = cr;
    let tparams = tparams.iter().map(&mut map_tparam).collect();
    let original_tparams = original_tparams.iter().map(&mut map_tparam).collect();
    aast::ClassAlias {
        name: name.clone(),
        tparams,
        original: original.clone(),
        original_tparams,
    }
}

/// Run typing on the given named AST (NAST) to produced a typed AST (TAST).
///
/// Set [do_tast_checks] to [false] to skip running TAST checks on the resulting
/// TAST. This means that the associated list of errors may be incomplete. This is
/// useful for performance in cases where we want the TAST, but don't need a correct
/// list of errors.
///
/// It is unfortunate that this routine exists alongside [Typing_check_job.calc_errors_and_tast]
/// which does almost exactly the same thing, except it also does [Naming], and
/// there are minor differences in treatment of some toplevel nodes.
pub fn nast_to_tast(
    do_tast_checks: bool,
    ctx: &Arc<Ctx>,
    nast: &nast::Program,
) -> tast_with_dynamic::T<tast::Program> {
    let convert_def = |def: &nast::Def| -> Option<tast_with_dynamic::T<tast::Def>> {
        worker_cancel::raise_if_stop_requested();
        match def {
            // Sometimes typing will just return `None` but that should only be the case
            // if an error had already been registered e.g. in naming
            aast::Def::Fun(f) => {
                let ctx = f.file_attributes.iter().fold(Arc::clone(ctx), |ctx, fa| {
                    set_tcopt_unstable_features(&ctx, fa)
                });
                match fun_def(&ctx, f) {
                    Some(fs) => Some(tast_with_dynamic::map(|f| aast::Def::Fun(Box::new(f)), fs)),
                    None => None,
                }
            }
            aast::Def::Constant(gc) => Some(tast_with_dynamic::mk_without_dynamic(
                aast::Def::Constant(Box::new(gconst_def(ctx, gc))),
            )),
            aast::Def::Typedef(td) => {
                let ctx = td.file_attributes.iter().fold(Arc::clone(ctx), |ctx, fa| {
                    set_tcopt_unstable_features(&ctx, fa)
                });
                Some(tast_with_dynamic::mk_without_dynamic(aast::Def::Typedef(
                    Box::new(typedef_def(&ctx, td)),
                )))
            }
            aast::Def::Class(c) => {
                let ctx = c.file_attributes.iter().fold(Arc::clone(ctx), |ctx, fa| {
                    set_tcopt_unstable_features(&ctx, fa)
                });
                match class_def(&ctx, c) {
                    Some(cs) => Some(tast_with_dynamic::map(
                        |c| aast::Def::Class(Box::new(c)),
                        cs,
                    )),
                    None => None,
                }
            }
            aast::Def::Stmt(s) => {
                let aast::Stmt(pos, stmt_) = &**s;
                {
                    // `Pos.show_absolute (Pos.to_absolute pos)` and
                    // `Aast_defs.show_stmt_ show_ex_en show_ex_en stmt_`
                    let pos_s = format!("{:?}", crate::pos::to_absolute(pos));
                    let data = format!("{:?}", stmt_);
                    hack_event_logger::invariant_violation_bug(
                        None,
                        Some(&pos_s),
                        Some(&data),
                        None,
                        None,
                        "Top-level statements should be unreachable in nast_to_tast because we convert top-level statements to functions in the Naming phase.",
                    )
                }
                let mut env = typing_env_types::empty(
                    None,
                    None,
                    Arc::clone(ctx),
                    Arc::new(relative_path::default),
                    None,
                );
                Some(tast_with_dynamic::mk_without_dynamic(aast::Def::Stmt(
                    Box::new(crate::typing::stmt(&mut env, s)),
                )))
            }
            aast::Def::Module(md) => Some(tast_with_dynamic::mk_without_dynamic(
                aast::Def::Module(Box::new(module_def(ctx, md))),
            )),
            aast::Def::SetModule(sm) => Some(tast_with_dynamic::mk_without_dynamic(
                aast::Def::SetModule(sm.clone()),
            )),
            aast::Def::ClassAlias(cr) => {
                // TODO(T264548072)
                let dummy_ty = make_type::nothing(reason::none());
                let cr = map_class_alias(
                    &mut |_| dummy_ty.clone(),
                    &mut |_| tast::dummy_saved_env(),
                    cr,
                );
                Some(tast_with_dynamic::mk_without_dynamic(
                    aast::Def::ClassAlias(Box::new(cr)),
                ))
            }
            aast::Def::Namespace(_)
            | aast::Def::NamespaceUse(_)
            | aast::Def::SetNamespaceEnv(_)
            | aast::Def::FileAttributes(_) => {
                panic!("Invalid nodes in NAST. These nodes should be removed during naming.")
            }
        }
    };
    if do_tast_checks {
        nast_check_program(ctx, nast)
    }
    let tast = tast_with_dynamic::collect(nast.0.iter().filter_map(convert_def).collect());
    let tast = tast_with_dynamic::map(aast::Program, tast);
    // We only do TAST checks for non-dynamic components
    if do_tast_checks {
        tast_check::program(ctx, &tast.under_normal_assumptions);
        // Intersect warning checks with dynamic TAST to determine trust
        match &tast.under_dynamic_assumptions {
            None => {
                // If there is no dynamic TAST, everything is trusted
                diagnostics_state::mark_all_warnings_trusted()
            }
            Some(dyn_tast) => {
                // Otherwise, find which warnings also fire under the dynamic TAST; since
                // these cannot be false positives we can mark the as trusted
                let dynamic_keys = diagnostics_state::collect_warning_keys(|| {
                    tast_check::warning_program(ctx, dyn_tast)
                });
                diagnostics_state::mark_warnings_trusted(&dynamic_keys)
            }
        }
    }
    tast
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_special_names() {
        let ml = include_str!("../../naming/naming_special_names.ml");
        assert!(ml.contains("let accessGlobals = prefix ^ \"AccessGlobals\""));
        assert!(ml.contains("let module_ = \"\\\\HH\\\\ModuleAttribute\""));
        assert!(ml.contains("let recursive_case_types = \"recursive_case_types\""));
        assert_eq!(ACCESS_GLOBALS, "\\HH\\Capabilities\\AccessGlobals");
    }
}
