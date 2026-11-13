// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_class.ml`. See `hh/PORTING.md`.
//!
//! # Notes on the port
//!
//! - The functions that return only a result (`method_def`, `class_def_`)
//!   or `unit` read the environment: they take `&Env`. `method_def` is given
//!   the same environment for every method of a class; it works on the copy
//!   that `with_timeout` makes.
//! - `Nast_init_check.class_ env c` (in `class_wellformedness_checks`) is not
//!   called here: in this port `crate::nast_check::check_program` runs it on
//!   every class (without the typing environment), and that function is what
//!   `Nast_check.def` / `Nast_check.program` are (`typing_check_job.rs`,
//!   `typing_toplevel.rs`), so calling it here too would report each of its
//!   errors twice. (`crate::nast_check::nast_init_check` is private, and takes
//!   a `&Ctx` and an error accumulator of its own.)
//! - `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
//!   custom_err_config)` is [`add_naming_error`] (as in `typing_toplevel`).
//! - In `method_def`, `let m = { m with m_ret = (fst m.m_ret, type_hint') }`
//!   changes only the return hint, and only that hint is read of the new
//!   method (for the TAST): the method is not copied, the hint is.

#![allow(non_snake_case)]

use std::sync::Arc;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ConstraintKind;
use oxidized::custom_error_config::CustomErrorConfig;
use oxidized::naming_error;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs::ClassConstKind;
use pos::ToOxidized;
use ty::decl::Ty_ as DeclTy_;
use ty::decl::WhereConstraint;
use ty::reason::Reason as _;

use crate::aast;
use crate::aast_utils;
use crate::ast_defs;
use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_counters;
use crate::decl_entry;
use crate::decl_fun_utils;
use crate::decl_hint;
use crate::decl_instantiate;
use crate::decl_utils;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::hack_event_logger;
use crate::lints_diagnostics;
use crate::naming_attributes;
use crate::nast;
use crate::provider_context;
use crate::s_map;
use crate::tast;
use crate::tast_with_dynamic;
use crate::typechecker_options;
use crate::typechecker_options::TypecheckerOptions;
use crate::typing_class_pointers;
use crate::typing_coeffects;
use crate::typing_coercion;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::empty_expand_env_with_on_error;
use crate::typing_defs::this;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclWhereConstraint;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::deref;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_disposable;
use crate::typing_dynamic;
use crate::typing_enforceability;
use crate::typing_enum;
use crate::typing_env as env;
use crate::typing_env_from_def as env_from_def;
use crate::typing_env_return_info;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_extends;
use crate::typing_helpers;
use crate::typing_helpers::expected_ty;
use crate::typing_implemented_by;
use crate::typing_log;
use crate::typing_make_type as make_type;
use crate::typing_memoize;
use crate::typing_native;
use crate::typing_needs_concrete;
use crate::typing_ops;
use crate::typing_packages::CheckReason;
use crate::typing_packages::PackageWarningInfo;
use crate::typing_param;
use crate::typing_phase as phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
use crate::typing_requirements;
use crate::typing_return;
use crate::typing_solver;
use crate::typing_subtype;
use crate::typing_toplevel_enable as enable;
use crate::typing_toplevel_profile as profile;
use crate::typing_type_wellformedness;
use crate::typing_utils as tutils;
use crate::typing_variance;
use crate::typing_visibility;
use crate::typing_warning;
use crate::typing_warning_utils;
use crate::worker_cancel;

/// `Naming_special_names.Classes.cString` (missing from
/// `naming_special_names_rust`).
const C_STRING: &str = "\\HH\\string";

/// `Naming_special_names.Capabilities.accessGlobals` (missing from
/// `naming_special_names_rust`).
const ACCESS_GLOBALS: &str = "\\HH\\Capabilities\\AccessGlobals";

/// `Naming_special_names.Capabilities.write_props` (missing from
/// `naming_special_names_rust`).
const WRITE_PROPS: &str = "\\HH\\Contexts\\write_props";

/// `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
/// custom_err_config)`. The renderer of naming errors of this crate does not
/// take the custom error configuration.
fn add_naming_error(err: NamingError, _custom_err_config: CustomErrorConfig) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(err)) {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Typing_error_utils.add_typing_error ~env (Typing_error.primary err)`
fn add_primary(env: &Env, err: primary::T) {
    typing_error_utils::add_typing_error(&typing_error::primary(err), env)
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

/// `Naming_attributes.mem x attrs`
fn mem(x: &str, attrs: &aast::UserAttributes<(), ()>) -> bool {
    naming_attributes::mem(x, &attrs.0)
}

/// emit a warning if a method is sealed to a class that does not override it
fn check_sealed_override(env: &Env, cls: &cls::T, m: &nast::Method_) {
    let method_name = &m.name.1;
    let is_sealed = |attr: &&nast::UserAttribute| attr.name.1 == sn::user_attributes::SEALED;
    match m.user_attributes.0.iter().find(is_sealed) {
        None => {}
        Some(sealed_attr) => {
            let iter_item = |aast::Expr(_, pos, expr_): &nast::Expr| match expr_ {
                aast::Expr_::ClassConst(cc) => {
                    let (aast::ClassId(_, _, cid), _) = &**cc;
                    let allowlist_class_name = nast::class_id_to_str(cid);
                    match env::get_class(env, &allowlist_class_name) {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                        decl_entry::T::Found(allowlist_cls) => {
                            let (allowlist_class_kind, verb) =
                                match (cls::kind(&allowlist_cls), cls::kind(cls)) {
                                    (ClassishKind::Cclass(_), ClassishKind::Ctrait) => {
                                        ("Class", "use")
                                    }
                                    (ClassishKind::Cclass(_), _) => ("Class", "extend"),
                                    (ClassishKind::Ctrait, ClassishKind::Ctrait) => {
                                        ("Trait", "use")
                                    }
                                    (ClassishKind::Ctrait, _) => ("Trait", "require extends"),
                                    (ClassishKind::Cinterface, _)
                                    | (ClassishKind::Cenum, _)
                                    | (ClassishKind::CenumClass(_), _) => ("", ""),
                                };
                            if !cls::has_ancestor(&allowlist_cls, &cls::name(cls))
                                && !cls::requires_ancestor(&allowlist_cls, &cls::name(cls))
                            {
                                typing_warning_utils::add(
                                    env,
                                    (
                                        pos.clone(),
                                        typing_warning::Kind::Sealed_not_subtype,
                                        typing_warning::sealed_not_subtype::T {
                                            verb: verb.to_string(),
                                            parent_name: cls::name(cls),
                                            parent_method_name: Some(method_name.clone()),
                                            child_name: allowlist_class_name.clone(),
                                            child_kind: allowlist_class_kind.to_string(),
                                        },
                                    ),
                                )
                            } else {
                                let method_decl_in_allowlist_class = if m.static_ {
                                    env::get_static_member(true, env, &allowlist_cls, method_name)
                                } else {
                                    env::get_method(env, &allowlist_cls, &m.name.1)
                                };
                                match method_decl_in_allowlist_class {
                                    None => {
                                        // the class in the sealed attribute does not define m, raise a warning
                                        typing_warning_utils::add(
                                            env,
                                            (
                                                pos.clone(),
                                                typing_warning::Kind::Sealed_not_override,
                                                typing_warning::sealed_not_override::T {
                                                    method_name: method_name.clone(),
                                                    method_def: cls::name(cls),
                                                    allowlist_class_name: allowlist_class_name
                                                        .clone(),
                                                    allowlist_class_kind: allowlist_class_kind
                                                        .to_string(),
                                                },
                                            ),
                                        )
                                    }
                                    Some(m_allowlist_class) => {
                                        // the method is defined in the allowlist_class
                                        // check that the method is defined by the class itself or inherited from a trait
                                        let is_origin_trait =
                                            match env::get_class(env, &m_allowlist_class.ce_origin)
                                            {
                                                decl_entry::T::Found(cls_origin) => {
                                                    ast_defs::is_c_trait(cls::kind(&cls_origin))
                                                }
                                                decl_entry::T::DoesNotExist
                                                | decl_entry::T::NotYetAvailable => false,
                                            };
                                        if !(m_allowlist_class.ce_origin == allowlist_class_name
                                            || is_origin_trait)
                                        {
                                            typing_warning_utils::add(
                                                env,
                                                (
                                                    pos.clone(),
                                                    typing_warning::Kind::Sealed_not_override,
                                                    typing_warning::sealed_not_override::T {
                                                        method_name: method_name.clone(),
                                                        method_def: cls::name(cls),
                                                        allowlist_class_name: allowlist_class_name
                                                            .clone(),
                                                        allowlist_class_kind: allowlist_class_kind
                                                            .to_string(),
                                                    },
                                                ),
                                            )
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            };
            for item in &sealed_attr.params {
                iter_item(item)
            }
        }
    }
}

/// OCaml returns `(env, dynamic_params, dynamic_body, dynamic_return_ty)`:
/// the environment is `env`, mutated.
fn method_dynamically_callable(
    env: &mut Env,
    cls: &cls::T,
    m: &nast::Method_,
    params_decl_ty: &[Option<DeclTy>],
    return_: &typing_env_return_info::T,
) -> (Vec<tast::FunParam>, Vec<tast::Stmt>, Ty) {
    env.checked = tast::CheckStatus::CUnderDynamicAssumptions;
    let ret_locl_ty = &return_.return_type;
    // Here the body of the method is typechecked again to ensure it is safe
    // to call it from a dynamic context (eg. under dyn..dyn->dyn assumptions).
    // The code below must be kept in sync with with the method_def checks.
    let make_dynamic = |pos: PosOrDecl| make_type::dynamic(reason::support_dynamic_type(pos));
    let dynamic_return_ty = make_dynamic(get_pos(ret_locl_ty));
    let dynamic_return_info = typing_env_return_info::T {
        return_type: dynamic_return_ty.clone(),
        ..return_.clone()
    };
    let param_tys = typing_param::make_param_local_tys(true, false, env, params_decl_ty, &m.params);
    let dynamic_params =
        crate::typing::bind_params(env, None, false, m.ctxs.as_ref(), &param_tys, &m.params);
    let pos = m.name.0.clone();
    typing_helpers::set_tyvars_variance_in_callable(env, &dynamic_return_ty, &param_tys);
    typing_dynamic::add_require_dynamic_bounds(env, cls);
    if cls::get_support_dynamic_type(cls) {
        let this_local = env::get_local(env, &this());
        let this_ty = make_type::intersection(
            reason::support_dynamic_type(PosOrDecl::NONE),
            vec![this_local.ty, make_dynamic(PosOrDecl::NONE)],
        );
        env::set_local(None, None, env, this(), this_ty, Pos::NONE)
    }

    let disable = mem(
        sn::user_attributes::DISABLE_TYPECHECKER_INTERNAL,
        &m.user_attributes,
    );

    // The handler reads the environment the attempt is given.
    let silence_errors_under_dynamic = env.genv.tcopt.tco_silence_errors_under_dynamic;
    let support_dynamic_type = env::get_support_dynamic_type(env);
    let dynamic_body = diagnostics_state::try_with_result(
        || {
            let native = typing_native::is_native_meth(env, m);
            crate::typing::fun_(
                Some(m.abstract_),
                Some(native),
                Some(disable),
                env,
                dynamic_return_info,
                &pos,
                &m.body,
                m.fun_kind,
            )
        },
        |env_and_dynamic_body, error| {
            // `TCO.silence_errors_under_dynamic env.genv.tcopt`
            if !silence_errors_under_dynamic {
                diagnostics_state::method_is_not_dynamically_callable(
                    pos.clone(),
                    &m.name.1,
                    &cls::name(cls),
                    support_dynamic_type,
                    None,
                    Some(&error),
                )
            }
            env_and_dynamic_body
        },
    );
    (dynamic_params, dynamic_body, dynamic_return_ty)
}

fn method_return(
    supportdyn: bool,
    env: &mut Env,
    cls: &cls::T,
    m: &nast::Method_,
    ret_decl_ty: Option<DeclTy>,
) -> typing_env_return_info::T {
    let hint_pos = match &m.ret.1 {
        Some(aast::Hint(hint_pos, _)) => hint_pos.clone(),
        None => m.name.0.clone(),
    };
    let default_ty = match &ret_decl_ty {
        None if m.name.1 == sn::members::__CONSTRUCT => {
            Some(make_type::void(reason::witness(m.name.0.clone())))
        }
        _ => None,
    };
    let ety_env = empty_expand_env_with_on_error(
        env::invalid_type_hint_assert_primary_pos_in_current_decl(env),
    );
    let ret_ty = typing_return::make_return_type(
        &ety_env,
        Some(cls),
        None,
        supportdyn,
        env,
        hint_pos.clone(),
        ret_decl_ty,
        default_ty,
    );
    let return_ = typing_return::make_info(
        None,
        hint_pos,
        m.fun_kind,
        &m.user_attributes.0,
        env,
        ret_ty,
    );
    return_
}

fn method_def(
    is_disposable: bool,
    env: &Env,
    cls: &cls::T,
    m: &nast::Method_,
) -> Option<tast_with_dynamic::T<tast::Method_>> {
    worker_cancel::raise_if_stop_requested();
    let tcopt = env::get_tcopt(env);
    enable::if_matches_regexp(None, &tcopt, Some(env), &m.name, || {
        profile::measure_elapsed_time_and_report(&tcopt, Some(env), &m.name, || {
            diagnostics_state::run_with_span(m.span.clone(), || {
                typing_helpers::with_timeout(env, &m.name, |env| {
                    method_def_with_env(is_disposable, &tcopt, cls, m, env)
                })
            })
        })
    })
}

/// The body of `method_def` that `with_timeout env m.m_name` runs.
fn method_def_with_env(
    is_disposable: bool,
    tcopt: &TypecheckerOptions,
    cls: &cls::T,
    m: &nast::Method_,
    env: &mut Env,
) -> tast_with_dynamic::T<tast::Method_> {
    let errs = decl_fun_utils::check_params(m.abstract_, &m.params);
    for err in &errs {
        typing_error_utils::add_typing_error(err, env)
    }
    let method_name = ast_defs::get_id(&m.name);
    let is_ctor = method_name == sn::members::__CONSTRUCT;
    if is_ctor {
        env::env_with_constructor_droot_member(env)
    } else {
        env::env_with_method_droot_member(env, &method_name, m.static_)
    }
    let initial_env = env.clone();
    let pos = m.name.0.clone();
    env::open_tyvars(env, m.name.0.clone());
    env::reinitialize_locals(env);
    env::set_env_callable_pos(env, pos.clone());
    env::set_env_function_pos(env, m.span.clone());
    let restore_pos = env::set_inference_env_pos(env, Some(pos.clone()));
    let user_attributes =
        crate::typing::attributes_check_def(env, sn::attribute_kinds::MTHD, &m.user_attributes.0);
    if mem(
        sn::user_attributes::SUPPORT_DYNAMIC_TYPE,
        &m.user_attributes,
    ) {
        env::set_support_dynamic_type(env, true)
    }
    {
        let needs_concrete = mem(sn::user_attributes::NEEDS_CONCRETE, &m.user_attributes);
        env::set_needs_concrete(env, needs_concrete)
    }
    let no_auto_likes = match cls::get_any_method(m.static_, cls, &method_name) {
        Some(ce) => typing_defs::get_ce_no_auto_likes(&ce),
        None => mem(sn::user_attributes::NO_AUTO_LIKES, &m.user_attributes),
    };
    if no_auto_likes {
        env::set_no_auto_likes(env, true)
    }
    check_sealed_override(env, cls, m);
    env::assert_packages_loaded_from_attr(env, &m.user_attributes.0);
    env::set_soft_package_from_attr(env, &m.user_attributes.0);
    let (cap_ty, unsafe_cap_ty) =
        typing_coeffects::type_capability(env, m.ctxs.as_ref(), m.unsafe_ctxs.as_ref(), &m.name.0);
    let _ = typing_coeffects::register_capabilities(env, cap_ty.clone(), unsafe_cap_ty);

    env::set_fun_is_constructor(env, is_ctor);
    let ty_err_opt = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
        env,
        false,
        &m.tparams,
        &m.where_constraints,
    );
    add_typing_error_opt(env, &ty_err_opt);
    match env::get_self_ty(env) {
        Some(ty) if !env::is_static(env) => env::set_local(
            None,
            None,
            env,
            this(),
            make_type::this(get_reason(&ty).clone()),
            Pos::NONE,
        ),
        _ => {}
    }
    if is_disposable {
        env::set_using_var(env, this())
    }
    env::clear_params(env);
    let (ret_decl_ty, params_decl_ty) = typing_helpers::hint_fun_decl(&m.params, &m.ret, env);
    // Is sound dynamic enabled and the function is
    // marked <<__SupportDynamicType>> explicitly or implicitly?
    // (Even constructors must be treated as SDT because they can be called
    // through a classname cast to dynamic).
    let sdt_method = env::get_support_dynamic_type(env);
    // Does the body of the method need to be checked again under
    // dynamic assumptions? Note that if there are generic parameters
    // then the check would be done under different assumptions for
    // generics from the normal check, so we play safe and require
    // the second check.
    let sdt_dynamic_check_required = sdt_method
        && !(cls::tparams(cls).is_empty()
            && typing_dynamic::function_parameters_safe_for_dynamic(
                Some(cls),
                env,
                &params_decl_ty,
            ));
    env::set_fn_kind(env, m.fun_kind);
    let return_ = method_return(
        sdt_method && !sdt_dynamic_check_required,
        env,
        cls,
        m,
        ret_decl_ty,
    );
    let sound_dynamic_check_saved_env = env.clone();
    let no_auto_likes = mem(sn::user_attributes::NO_AUTO_LIKES, &m.user_attributes);
    let param_tys =
        typing_param::make_param_local_tys(false, no_auto_likes, env, &params_decl_ty, &m.params);
    typing_memoize::check_method(env, m);
    typing_implemented_by::check_method(env, &ast_defs::Id(pos.clone(), cls::name(cls)), m);
    let can_read_globals = typing_subtype::is_sub_type(
        env,
        &cap_ty,
        &make_type::capability(get_reason(&cap_ty).clone(), ACCESS_GLOBALS.to_string()),
    );
    let typed_params = crate::typing::bind_params(
        env,
        Some(can_read_globals),
        no_auto_likes,
        m.ctxs.as_ref(),
        &param_tys,
        &m.params,
    );
    let ret_locl_ty = return_.return_type.clone();
    typing_helpers::set_tyvars_variance_in_callable(env, &ret_locl_ty, &param_tys);
    let local_tpenv = env::get_tpenv(env);
    let disable = mem(
        sn::user_attributes::DISABLE_TYPECHECKER_INTERNAL,
        &m.user_attributes,
    );
    let (tb, had_errors) = diagnostics_state::run_and_check_for_errors(|| {
        let native = typing_native::is_native_meth(env, m);
        crate::typing::fun_(
            Some(m.abstract_),
            Some(native),
            Some(disable),
            env,
            return_.clone(),
            &pos,
            &m.body,
            m.fun_kind,
        )
    });
    let type_hint_ = match &m.ret.1 {
        None if method_name == sn::members::__CONSTRUCT => Some(aast::Hint(
            pos.clone(),
            Box::new(aast::Hint_::Hprim(ast_defs::Tprim::Tvoid)),
        )),
        None => {
            add_primary(env, primary::T::Expecting_return_type_hint(pos.clone()));
            None
        }
        Some(_) => m.ret.1.clone(),
    };
    // `let m = { m with m_ret = (fst m.m_ret, type_hint') }`
    let tparams: Vec<tast::Tparam> = m
        .tparams
        .iter()
        .map(|tp| crate::typing::type_param(env, tp))
        .collect();
    let e1 = typing_solver::close_tyvars_and_solve(env);
    let e2 = typing_solver::solve_all_unsolved_tyvars(env);

    let return_hint = type_hint_;
    let under_normal_assumptions = aast::Method_ {
        annotation: env::save(&local_tpenv, env),
        span: m.span.clone(),
        final_: m.final_,
        static_: m.static_,
        abstract_: m.abstract_,
        visibility: m.visibility,
        readonly_this: m.readonly_this,
        name: m.name.clone(),
        tparams,
        where_constraints: m.where_constraints.clone(),
        params: typed_params,
        ctxs: m.ctxs.clone(),
        unsafe_ctxs: m.unsafe_ctxs.clone(),
        fun_kind: m.fun_kind,
        user_attributes: aast::UserAttributes(user_attributes),
        readonly_ret: m.readonly_ret,
        ret: aast::TypeHint(ret_locl_ty.clone(), return_hint.clone()),
        body: aast::FuncBody {
            fb_ast: aast::Block(tb),
        },
        external: m.external,
        hidden: m.hidden,
        doc_comment: m.doc_comment.clone(),
    };
    let sdt_dynamic_check_required = sdt_dynamic_check_required
        && !had_errors
        && !{
            // Add `dynamic` lower and upper bound to any type parameters that are marked <<__RequireDynamic>>
            let mut env_with_require_dynamic = sound_dynamic_check_saved_env.clone();
            typing_dynamic::add_require_dynamic_bounds(&mut env_with_require_dynamic, cls);
            typing_dynamic::sound_dynamic_interface_check(
                Some(cls),
                &env_with_require_dynamic,
                &params_decl_ty,
                &return_.return_type,
            )
        };
    // `{ under_normal_assumptions with m_annotation; m_params; m_body; m_ret }`:
    // the fields that are replaced are not copied.
    let method_def_of_dynamic =
        |u: &tast::Method_,
         (dynamic_env, dynamic_params, dynamic_body, dynamic_return_ty): (
            Env,
            Vec<tast::FunParam>,
            Vec<tast::Stmt>,
            Ty,
        )|
         -> tast::Method_ {
            aast::Method_ {
                annotation: env::save(&local_tpenv, &dynamic_env),
                span: u.span.clone(),
                final_: u.final_,
                static_: u.static_,
                abstract_: u.abstract_,
                visibility: u.visibility,
                readonly_this: u.readonly_this,
                name: u.name.clone(),
                tparams: u.tparams.clone(),
                where_constraints: u.where_constraints.clone(),
                params: dynamic_params,
                ctxs: u.ctxs.clone(),
                unsafe_ctxs: u.unsafe_ctxs.clone(),
                fun_kind: u.fun_kind,
                user_attributes: u.user_attributes.clone(),
                readonly_ret: u.readonly_ret,
                ret: aast::TypeHint(dynamic_return_ty, return_hint.clone()),
                body: aast::FuncBody {
                    fb_ast: aast::Block(dynamic_body),
                },
                external: u.external,
                hidden: u.hidden,
                doc_comment: u.doc_comment.clone(),
            }
        };
    let (under_normal_assumptions, under_dynamic_assumptions) =
        if sdt_dynamic_check_required && !tcopt.tco_skip_check_under_dynamic {
            env.checked = tast::CheckStatus::CUnderNormalAssumptions;
            let m_annotation = env::save(&local_tpenv, env);
            let mut dynamic_env = sound_dynamic_check_saved_env;
            let (dynamic_params, dynamic_body, dynamic_return_ty) =
                method_dynamically_callable(&mut dynamic_env, cls, m, &params_decl_ty, &return_);
            let under_dynamic_assumptions = method_def_of_dynamic(
                &under_normal_assumptions,
                (dynamic_env, dynamic_params, dynamic_body, dynamic_return_ty),
            );
            let mut under_normal_assumptions = under_normal_assumptions;
            under_normal_assumptions.annotation = m_annotation;
            (under_normal_assumptions, Some(under_dynamic_assumptions))
        } else {
            (under_normal_assumptions, None)
        };
    restore_pos(env);
    env::log_env_change("method_def", None, &initial_env, env);
    let ty_err_opt = merge_errors(e1, e2);
    add_typing_error_opt(env, &ty_err_opt);
    tast_with_dynamic::T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    }
}

/// Checks that extending the base class is legal, i.e.:
/// - the parent is not final
/// - if the class is const, the parent should also be
fn check_parent(env: &Env, class_def: &nast::Class_, class_type: &cls::T) {
    match env::get_parent_class(env) {
        decl_entry::T::Found(parent_type) => {
            let position = class_def.name.0.clone();
            if cls::has_const_attribute(class_type) && !cls::has_const_attribute(&parent_type) {
                add_primary(env, primary::T::Self_const_parent_not(position.clone()))
            }
            if cls::final_(&parent_type) {
                add_primary(
                    env,
                    primary::T::Extend_final {
                        pos: position,
                        decl_pos: cls::pos(&parent_type),
                        name: cls::name(&parent_type),
                    },
                )
            }
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
    }
}

fn check_consistent_construct_not_abstract_final(
    env: &Env,
    class_def: &nast::Class_,
    class_type: &cls::T,
) {
    if env::get_tcopt(env).strict_consistent_construct
        && cls::abstract_(class_type)
        && class_def.final_
    {
        // Check the NAST directly for the attribute on the current class —
        // no decl lookup needed.
        let has_cc_on_self = mem(
            sn::user_attributes::CONSISTENT_CONSTRUCT,
            &class_def.user_attributes,
        );
        // For abstract final classes, the folded construct kind is FinalClass
        // rather than ConsistentConstruct, so we also check the NAST attribute.
        let is_cc = match env::get_construct(env, class_type).1 {
            typing_defs::ConsistentKind::ConsistentConstruct => true,
            _ => has_cc_on_self,
        };
        if is_cc {
            let inherited_from = if has_cc_on_self {
                None
            } else {
                // The error message would be better if we could
                // tell the user *which* ancestor has the explicit __ConsistentConstruct
                // attribute, but checking would be too expensive
                let cc_parent = class_def.extends.iter().find_map(|h| match &*h.1 {
                    aast::Hint_::Happly(ast_defs::Id(_, name), _) => {
                        match env::get_class(env, name) {
                            decl_entry::T::Found(parent_cls) => {
                                let consistent = env::get_construct(env, &parent_cls).1;
                                match consistent {
                                    typing_defs::ConsistentKind::ConsistentConstruct => {
                                        Some(name.clone())
                                    }
                                    _ => None,
                                }
                            }
                            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
                        }
                    }
                    _ => None,
                });
                match cc_parent {
                    Some(name) => Some(name),
                    None => Some("an ancestor".to_string()),
                }
            };
            typing_warning_utils::add(
                env,
                (
                    class_def.name.0.clone(),
                    typing_warning::Kind::Consistent_construct_abstract_final,
                    typing_warning::consistent_construct_abstract_final::T {
                        name: class_def.name.1.clone(),
                        inherited_from,
                    },
                ),
            )
        }
    }
}

/// If the class is sealed, check that the elements of the whitelist
/// are descendants of the class and emit a warning if not.
fn sealed_subtype(c: &nast::Class_, is_enum: bool, env: &Env) {
    let parent_name = &c.name.1;
    let parent_kind = c.kind;
    let is_sealed = |attr: &&nast::UserAttribute| attr.name.1 == sn::user_attributes::SEALED;
    match c.user_attributes.0.iter().find(is_sealed) {
        None => {}
        Some(sealed_attr) => {
            let iter_item = |aast::Expr(_, pos, expr_): &nast::Expr| match expr_ {
                aast::Expr_::ClassConst(cc) => {
                    let (aast::ClassId(_, _, cid), _) = &**cc;
                    let klass_name = nast::class_id_to_str(cid);
                    let klass = env::get_class(env, &klass_name);
                    match klass {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                        decl_entry::T::Found(decl) => {
                            let includes_ancestor = if is_enum {
                                match cls::enum_type(&decl) {
                                    None => true,
                                    Some(enum_ty) => {
                                        let check = |x: &DeclTy| match x.node_ref() {
                                            DeclTy_::Tapply(id_and_args) => {
                                                id_and_args.0.id_ref().as_str() == parent_name
                                            }
                                            _ => true,
                                        };
                                        enum_ty.includes.iter().any(check)
                                    }
                                }
                            } else {
                                cls::has_ancestor(&decl, parent_name)
                            };
                            // Skip the warning if this is a class with a trait in the sealed allowlist.
                            // This case is now handled as a proper error in nast_check (NastCheck[3108])
                            // since traits cannot extend classes.
                            let class_kind = cls::kind(&decl);
                            let is_class_with_trait = match (parent_kind, class_kind) {
                                (ClassishKind::Cclass(_), ClassishKind::Ctrait) => true,
                                _ => false,
                            };
                            if !includes_ancestor && !is_class_with_trait {
                                let parent_pos = pos.clone();
                                let child_name = cls::name(&decl);
                                let (child_kind, verb) = match (parent_kind, class_kind) {
                                    (ClassishKind::Cinterface, ClassishKind::Cclass(_)) => {
                                        ("Class", "implement")
                                    }
                                    (_, ClassishKind::Cclass(_)) => ("Class", "extend"),
                                    (ClassishKind::Cinterface, ClassishKind::Cinterface) => {
                                        ("Interface", "extend")
                                    }
                                    (_, ClassishKind::Cinterface) => ("Interface", "implement"),
                                    (ClassishKind::Cinterface, ClassishKind::Ctrait) => {
                                        ("Trait", "implement")
                                    }
                                    (_, ClassishKind::Ctrait) => ("Trait", "use"),
                                    (_, ClassishKind::Cenum) => ("Enum", "use"),
                                    (_, ClassishKind::CenumClass(_)) => ("Enum Class", "extend"),
                                };
                                typing_warning_utils::add(
                                    env,
                                    (
                                        parent_pos,
                                        typing_warning::Kind::Sealed_not_subtype,
                                        typing_warning::sealed_not_subtype::T {
                                            verb: verb.to_string(),
                                            parent_name: parent_name.clone(),
                                            parent_method_name: None,
                                            child_name,
                                            child_kind: child_kind.to_string(),
                                        },
                                    ),
                                )
                            }
                        }
                    }
                }
                // unit below is fine because error cases are handled as Parsing[1002]
                _ => {}
            };
            for item in &sealed_attr.params {
                iter_item(item)
            }
        }
    }
}

/// If the parent is sealed, check that the child being checked
/// is in the whitelist.
fn check_parent_sealed((child_pos, child_type): (&Pos, &cls::T), parent_type: &cls::T, env: &Env) {
    match cls::sealed_whitelist(parent_type) {
        None => {}
        Some(whitelist) => {
            let parent_pos = cls::pos(parent_type);
            let parent_name = cls::name(parent_type);
            let child_name = cls::name(child_type);
            let check = |parent_kind: primary::ExtendSealedParentKind,
                         verb: primary::ExtendSealedVerb| {
                if !whitelist.contains(&child_name) {
                    add_primary(
                        env,
                        primary::T::Extend_sealed {
                            pos: child_pos.clone(),
                            parent_pos: parent_pos.clone(),
                            parent_name: parent_name.clone(),
                            parent_kind,
                            verb,
                        },
                    )
                }
            };
            use primary::ExtendSealedParentKind as PK;
            use primary::ExtendSealedVerb as V;
            match (cls::kind(parent_type), cls::kind(child_type)) {
                (ClassishKind::Cinterface, ClassishKind::Cinterface) => check(PK::intf, V::extend),
                (ClassishKind::Cinterface, _) => check(PK::intf, V::implement),
                (ClassishKind::Ctrait, _) => check(PK::trait_, V::use_),
                (ClassishKind::Cclass(_), _) => check(PK::class_, V::extend),
                (ClassishKind::CenumClass(_), _) => check(PK::enum_class, V::extend),
                (ClassishKind::Cenum, _) => check(PK::enum_, V::use_),
            }
        }
    }
}

/// If the parents are sealed, check that the child being checked
/// is in the whitelists.
fn check_parents_sealed(env: &Env, child_def: &nast::Class_, child_type: &cls::T) {
    let parents: &[aast::Hint] = match &child_def.enum_ {
        Some(enum_) => &enum_.includes,
        None => &child_def.extends,
    };
    let parents = parents
        .iter()
        .chain(child_def.implements.iter())
        .chain(child_def.uses.iter());
    for h in parents {
        match &*h.1 {
            aast::Hint_::Happly(ast_defs::Id(_, name), _) => match env::get_class(env, name) {
                decl_entry::T::Found(parent_type) => {
                    check_parent_sealed((&child_def.name.0, child_type), &parent_type, env)
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            },
            _ => {}
        }
    }
}

/// Reject multiple instantiations of the same generic interface
/// in extends and implements clauses.
/// e.g. disallow class C implements I<string>, I<int>
///
/// O(n^2) but we don't expect number of instantiated interfaces to be large
fn check_implements_or_extends_unique(impl_: &[(aast::Hint, DeclTy)], env: &Env) {
    match impl_ {
        [] => {}
        [(hint, ty), rest @ ..] => match ty.node_ref() {
            DeclTy_::Tapply(id_and_args) if !id_and_args.1.is_empty() => {
                let name = id_and_args.0.id_ref().as_str();
                let mut pos_list: Vec<PosOrDecl> = vec![];
                let mut rest_: Vec<(aast::Hint, DeclTy)> = vec![];
                for (h, ty) in rest {
                    match ty.node_ref() {
                        DeclTy_::Tapply(id_and_args2)
                            if name == id_and_args2.0.id_ref().as_str() =>
                        {
                            pos_list.push(Pos::from(id_and_args2.0.pos().clone()))
                        }
                        _ => rest_.push((h.clone(), ty.clone())),
                    }
                }
                if !pos_list.is_empty() {
                    add_primary(
                        env,
                        primary::T::Duplicate_interface {
                            pos: hint.0.clone(),
                            name: name.to_string(),
                            others: pos_list,
                        },
                    )
                }

                check_implements_or_extends_unique(&rest_, env)
            }
            _ => check_implements_or_extends_unique(rest, env),
        },
    }
}

/// Add a dependency to constructors or produce an error if not a Tapply.
fn check_is_tapply_add_constructor_extends_dep(
    env: &Env,
    skip_constructor_dep: Option<bool>,
    deps: &[(aast::Hint, DeclTy)],
) {
    let skip_constructor_dep = skip_constructor_dep.unwrap_or(false);
    for (aast::Hint(p, _dep_hint), dep) in deps {
        match dep.node_ref() {
            DeclTy_::Tapply(id_and_args) => {
                let class_name = id_and_args.0.id_ref().as_str();
                env::add_parent_dep(env, skip_constructor_dep, class_name)
            }
            DeclTy_::Tgeneric(_) => add_primary(
                env,
                primary::T::Expected_class {
                    suffix: Some(Lazy::from_val(
                        " or interface but got a generic".to_string(),
                    )),
                    pos: p.clone(),
                },
            ),
            _ => add_primary(
                env,
                primary::T::Expected_class {
                    suffix: Some(Lazy::from_val(" or interface".to_string())),
                    pos: p.clone(),
                },
            ),
        }
    }
}

/// For const classes, check that members from traits are all constant.
fn check_non_const_trait_members(pos: &Pos, env: &Env, use_list: &aast::Hint) {
    let ((_, trait_, _), err_opt) = decl_utils::unwrap_class_hint(use_list);
    add_typing_error_opt(env, &err_opt);
    match env::get_class(env, &trait_) {
        decl_entry::T::Found(c) if ast_defs::is_c_trait(cls::kind(&c)) => {
            for (x, ce) in cls::props(&c) {
                if !typing_defs::get_ce_const(&ce) {
                    add_primary(
                        env,
                        primary::T::Trait_prop_const_class {
                            pos: pos.clone(),
                            name: x,
                        },
                    )
                }
            }
        }
        _ => {}
    }
}

fn check_consistent_enum_inclusion(
    included_cls: &cls::T,
    (dest_cls_pos, dest_cls): (&Pos, &cls::T),
    env: &Env,
) {
    let included_kind = cls::kind(included_cls);
    let dest_kind = cls::kind(dest_cls);
    // Check package visibility
    match typing_visibility::check_package_access(
        CheckReason::Yes(primary::package::TargetSymbolSpec::Enum),
        dest_cls_pos.clone(),
        cls::pos(included_cls),
        env,
        cls::get_package(included_cls).as_ref(),
        cls::name(included_cls),
    ) {
        typing_visibility::PackageAccessResult::PackageAccessError(err) => {
            typing_error_utils::add_typing_error(&err, env)
        }
        typing_visibility::PackageAccessResult::PackageAccessLinterError((pos, w)) => {
            let PackageWarningInfo {
                current_package,
                current_package_before_override,
                caller_has_package_override,
                target_package,
                target_package_before_override,
                callee_has_package_override,
                classptr_reference_warning,
            } = w;
            lints_diagnostics::crosspackage_linter(
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
        typing_visibility::PackageAccessResult::PackageAccessOk => {}
    }
    match (cls::enum_type(included_cls), cls::enum_type(dest_cls)) {
        (Some(included_e), Some(dest_e)) => {
            // ensure that the base types are identical
            if !crate::typing_defs_core::equal_decl_ty(&included_e.base, &dest_e.base) {
                typing_error_utils::add_typing_error(
                    &typing_error::enum_(primary::enum_::T::Incompatible_enum_inclusion_base {
                        pos: dest_cls_pos.clone(),
                        classish_name: cls::name(dest_cls),
                        src_classish_name: cls::name(included_cls),
                    }),
                    env,
                )
            }
            // ensure that the visibility constraint are compatible
            match (&included_e.constraint, &dest_e.constraint) {
                (None, Some(_)) => typing_error_utils::add_typing_error(
                    &typing_error::enum_(
                        primary::enum_::T::Incompatible_enum_inclusion_constraint {
                            pos: dest_cls_pos.clone(),
                            classish_name: cls::name(dest_cls),
                            src_classish_name: cls::name(included_cls),
                        },
                    ),
                    env,
                ),
                (_, _) => {}
            }
            // ensure normal enums can't include enum classes
            if ast_defs::is_c_enum_class(included_kind) && !ast_defs::is_c_enum_class(dest_kind) {
                add_primary(
                    env,
                    primary::T::Wrong_extend_kind {
                        parent_pos: cls::pos(included_cls),
                        parent_kind: included_kind,
                        parent_name: cls::name(included_cls),
                        pos: dest_cls_pos.clone(),
                        kind: dest_kind,
                        name: cls::name(dest_cls),
                    },
                )
            }
        }
        (None, _) => typing_error_utils::add_typing_error(
            &typing_error::enum_(primary::enum_::T::Enum_inclusion_not_enum {
                pos: dest_cls_pos.clone(),
                classish_name: cls::name(dest_cls),
                src_classish_name: cls::name(included_cls),
            }),
            env,
        ),
        (_, _) => {}
    }
}

fn skip_check_multiple_instantiations(env: &Env, type_name: &str) -> bool {
    match env::get_class(env, type_name) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => true,
        decl_entry::T::Found(cls) => {
            !ast_defs::is_c_interface(cls::kind(&cls)) || cls::allow_multiple_instantiations(&cls)
        }
    }
}

/// The interfaces seen so far, with the type they were seen at and the
/// direct parent (position and name) they were seen through.
type Ancestors = s_map::T<(DeclTy, (Pos, String))>;

/// Check that repeated use of the same interface, but possibly at a different instantiation,
/// is textually in subtype order.
/// This code should shadow that in decl_folded_class.ml/fold.rs.
///
/// @param  parent_pos  position of the parent which has interface [name] as ancestor
/// @param  name        name of the interface we're checking
/// @pararm ty          type of the interface we're checking
fn add_or_check_is_supertype(
    env: &mut Env,
    current_type: &(String, ClassishKind),
    parent_pos_id: &(Pos, String),
    interface_name: &str,
    ty: &DeclTy,
    ancestors: Ancestors,
) -> Ancestors {
    if skip_check_multiple_instantiations(env, interface_name) {
        ancestors
    } else {
        match ancestors.get(interface_name) {
            None => {
                let mut ancestors = ancestors;
                ancestors.insert(
                    interface_name.to_string(),
                    (ty.clone(), parent_pos_id.clone()),
                );
                ancestors
            }
            Some((first_ty, first_parent_pos_id)) => {
                let first_ty = first_ty.clone();
                let first_parent_pos_id = first_parent_pos_id.clone();
                // We want this check to break through module boundaries so we disable
                // the localization of internal newtypes outside their module as newtype
                let ety_env = ExpandEnv {
                    make_internal_opaque: false,
                    ..empty_expand_env()
                };
                let (_err, lty) = phase::localize(&ety_env, env, ty);
                let (_err, first_lty) = phase::localize(&ety_env, env, &first_ty);
                let ty_err_opt = {
                    let (_, winning_pos, winning_instantiation) =
                        decl_utils::unwrap_class_type(&first_ty);
                    let (_, losing_pos, losing_instantiation) = decl_utils::unwrap_class_type(ty);
                    let tcopt = env::get_tcopt(env);
                    let err_prefix = primary::T::Multiple_instantiation_inheritence {
                        type_name: current_type.0.clone(),
                        implements_or_extends: if ast_defs::is_c_interface(current_type.1) {
                            "extends"
                        } else {
                            "implements"
                        }
                        .to_string(),
                        interface_name: interface_name.to_string(),
                        winning_implements: primary::ImplementsInfo {
                            pos: Pos::from(winning_pos.pos().clone()),
                            instantiation: winning_instantiation
                                .iter()
                                .map(|ty| {
                                    typing_print::full_decl(None, &tcopt, &ty.clone().to_oxidized())
                                })
                                .collect(),
                            via_direct_parent: first_parent_pos_id,
                        },
                        losing_implements: primary::ImplementsInfo {
                            pos: Pos::from(losing_pos.pos().clone()),
                            instantiation: losing_instantiation
                                .iter()
                                .map(|ty| {
                                    typing_print::full_decl(None, &tcopt, &ty.clone().to_oxidized())
                                })
                                .collect(),
                            via_direct_parent: parent_pos_id.clone(),
                        },
                    };
                    typing_ops::sub_type_w_err_prefix(
                        None,
                        &parent_pos_id.0,
                        env,
                        first_lty,
                        lty,
                        err_prefix,
                    )
                };
                add_typing_error_opt(env, &ty_err_opt);
                ancestors
            }
        }
    }
}

fn get_instantiated_ancestors_and_self(
    env: &Env,
    (_pos, type_name): &(Pos, String),
    tyargs: &[DeclTy],
    ty: DeclTy,
) -> s_map::T<DeclTy> {
    let class_ = env::get_class(env, type_name);
    let mut instantiated_ancestors: s_map::T<DeclTy> = match class_ {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => s_map::T::new(),
        decl_entry::T::Found(class_) => {
            let subst = decl_instantiate::make_subst(&cls::tparams(&class_), tyargs);
            cls::all_ancestors(&class_)
                .into_iter()
                .collect::<s_map::T<DeclTy>>()
                .into_iter()
                .map(|(name, ty)| (name, decl_instantiate::instantiate(&subst, &ty)))
                .collect()
        }
    };
    instantiated_ancestors.insert(type_name.clone(), ty);
    instantiated_ancestors
}

/// Check that repeated use of the same interface, but possibly at a different instantiation,
/// is textually in subtype order.
fn check_multiple_instantiation_inheritance(
    env: &mut Env,
    current_type: &(String, ClassishKind),
    parents: &[&aast::Hint],
) {
    if ast_defs::is_c_enum_class(current_type.1) {
    } else {
        let parents: Vec<((Pos, String), DeclTy, Vec<DeclTy>)> = parents
            .iter()
            .map(|hint| {
                let decl_ty = decl_hint::hint(&env.decl_env, hint);
                let (_r, name_pos_class_name, tyargs) = decl_utils::unwrap_class_type(&decl_ty);
                let class_name = name_pos_class_name.id_ref().as_str().to_string();
                ((hint.0.clone(), class_name), decl_ty, tyargs)
            })
            .collect();
        // The body of the fold looks the ancestors up in the environment the
        // function is given, not in the one it accumulates.
        let env0 = env.clone();
        let mut ancestors: Ancestors = s_map::T::new();
        for (parent_pos_id, parent_ty, parent_tyargs) in parents {
            let ancestors_and_self = get_instantiated_ancestors_and_self(
                &env0,
                &parent_pos_id,
                &parent_tyargs,
                parent_ty,
            );
            for (ancestor_name, ty) in ancestors_and_self.iter() {
                ancestors = add_or_check_is_supertype(
                    env,
                    current_type,
                    &parent_pos_id,
                    ancestor_name,
                    ty,
                    ancestors,
                )
            }
        }
    }
}

fn is_enum_or_enum_class(k: ClassishKind) -> bool {
    ast_defs::is_c_enum(k) || ast_defs::is_c_enum_class(k)
}

fn check_enum_includes(env: &Env, cls: &nast::Class_) {
    let is_abstract = |k: &ClassConstKind| match k {
        ClassConstKind::CCAbstract(has_default) => !has_default,
        ClassConstKind::CCConcrete => false,
    };
    // checks that there are no duplicated enum-constants when folded-decls are enabled
    if is_enum_or_enum_class(cls.kind) {
        let ast_defs::Id(dest_class_pos, dest_class_name) = &cls.name;
        let mut enum_constant_map: s_map::T<(Pos, String)> = s_map::T::new();
        // prepopulate the map with the constants declared in cls
        for cc in &cls.consts {
            enum_constant_map.insert(cc.id.1.clone(), (cc.id.0.clone(), dest_class_name.clone()));
        }
        // for all included enums
        let included_enums: Vec<(Pos, cls::T)> = aast::enum_includes_map(
            None,
            |ce| {
                ce.includes
                    .iter()
                    .filter_map(|ie| match &*ie.1 {
                        aast::Hint_::Happly(sid, _) => match env::get_class(env, &sid.1) {
                            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
                            decl_entry::T::Found(ie_cls) => Some((ie.0.clone(), ie_cls)),
                        },
                        _ => None,
                    })
                    .collect()
            },
            cls.enum_.as_ref(),
        );
        for (ie_pos, ie_cls) in &included_enums {
            let src_class_name = cls::name(ie_cls);
            // 1. Check for consistency
            match env::get_class(env, dest_class_name) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(cls) => {
                    check_consistent_enum_inclusion(ie_cls, (ie_pos, &cls), env)
                }
            }
            // 2. Check for duplicates
            for (const_name, class_const) in env::consts(env, ie_cls) {
                let cc_origin = class_const.origin.as_str();
                if const_name == "class" {
                    // TODO: Check with @fzn
                } else if is_abstract(&class_const.kind) {
                } else if enum_constant_map.contains_key(&const_name) {
                    // distinguish between multiple inherit and redeclare
                    let (origin_const_pos, origin_class_name) =
                        enum_constant_map[&const_name].clone();
                    if origin_class_name == *dest_class_name {
                        // redeclare
                        add_primary(
                            env,
                            primary::T::Redeclaring_classish_const {
                                pos: dest_class_pos.clone(),
                                classish_name: dest_class_name.clone(),
                                redeclaration_pos: origin_const_pos,
                                existing_const_origin: src_class_name.clone(),
                                const_name: const_name.clone(),
                            },
                        )
                    } else if origin_class_name != cc_origin {
                        // check for diamond inclusion, if not raise an error about multiple inherit
                        add_primary(
                            env,
                            primary::T::Reinheriting_classish_const {
                                pos: dest_class_pos.clone(),
                                classish_name: dest_class_name.clone(),
                                src_pos: ie_pos.clone(),
                                src_classish_name: src_class_name.clone(),
                                existing_const_origin: origin_class_name,
                                const_name: const_name.clone(),
                            },
                        )
                    }
                }
                enum_constant_map
                    .insert(const_name, (dest_class_pos.clone(), cc_origin.to_string()));
            }
        }
    }
}

fn skip_hierarchy_checks(ctx: &Arc<Ctx>) -> bool {
    provider_context::get_tcopt(ctx).tco_skip_hierarchy_checks
}

fn class_type_param(env: &mut Env, ct: &[nast::Tparam]) -> Vec<tast::Tparam> {
    let tparam_list = ct
        .iter()
        .map(|tp| crate::typing::type_param(env, tp))
        .collect();
    tparam_list
}

/// Check whether the type of a static property (class variable) contains
/// any generic type parameters. Outside of traits, this is illegal as static
/// properties are shared across all generic instantiations.
fn check_no_generic_static_property(env: &Env, tc: &cls::T) {
    if ast_defs::is_c_trait(cls::kind(tc)) {
    } else {
        for (_prop_name, prop) in cls::sprops(tc) {
            let ty: &DeclTy = LazyLock::force(&prop.ce_type);
            let var_ty_pos = Pos::from(decl_utils::get_pos(ty));
            let class_pos = cls::pos(tc);
            match tutils::contains_generic_decl(ty) {
                None => {}
                Some(generic_pos) => {
                    // If the static property is inherited from another trait, the position may be
                    // in a different file.
                    if let Some(generic_pos) =
                        env::fill_in_pos_filename_if_in_current_decl(env, &generic_pos)
                    {
                        add_primary(
                            env,
                            primary::T::Static_prop_type_generic_param {
                                class_pos,
                                var_ty_pos,
                                pos: generic_pos,
                            },
                        )
                    }
                }
            }
        }
    }
}

fn typeconst_def(
    cls: &nast::Class_,
    env: &mut Env,
    tconst: &nast::ClassTypeconstDef,
) -> tast::ClassTypeconstDef {
    let aast::ClassTypeconstDef {
        name: id,
        kind: c_tconst_kind,
        user_attributes: c_tconst_user_attributes,
        span: c_tconst_span,
        doc_comment: c_tconst_doc_comment,
        is_ctx: c_tconst_is_ctx,
    } = tconst;
    let ast_defs::Id(pos, _) = id;
    let tcopt = env::get_tcopt(env).clone();
    // `Some env`: the environment as it is before the definition is checked.
    let env_opt = env.clone();
    let default = aast::ClassTypeconstDef {
        name: id.clone(),
        kind: c_tconst_kind.clone(),
        user_attributes: aast::UserAttributes(vec![]),
        span: c_tconst_span.clone(),
        doc_comment: c_tconst_doc_comment.clone(),
        is_ctx: *c_tconst_is_ctx,
    };
    enable::if_matches_regexp(default, &tcopt, Some(&env_opt), id, || {
        profile::measure_elapsed_time_and_report(&tcopt, Some(&env_opt), id, || {
            if ast_defs::is_c_enum(cls.kind) {
                let ast_defs::Id(class_pos, class_name) = &cls.name;
                add_primary(
                    env,
                    primary::T::Cannot_declare_constant {
                        pos: pos.clone(),
                        class_pos: class_pos.clone(),
                        class_name: class_name.clone(),
                    },
                )
            }
            let expansion = crate::type_expansions::expandable::T::TypeConstant {
                receiver_name: cls.name.1.clone(),
                type_const_name: id.1.clone(),
            };
            // Check constraints and report cycles through the definition
            let ty_err_opt = match c_tconst_kind {
                aast::ClassTypeconst::TCAbstract(aast::ClassAbstractTypeconst {
                    as_constraint: c_atc_as_constraint,
                    super_constraint: c_atc_super_constraint,
                    default: c_atc_default,
                }) => {
                    let ty_default_opt = match c_atc_default {
                        Some(ty) => {
                            let (ty_err_opt1, cycles, ty) =
                                phase::localize_hint_no_subst_report_cycles(
                                    env,
                                    false,
                                    (pos.clone(), expansion.clone()),
                                    ty,
                                );
                            add_typing_error_opt(env, &ty_err_opt1);
                            add_typing_error_opt(env, &crate::type_expansions::report(&cycles));
                            Some(ty)
                        }
                        None => None,
                    };
                    let ty_err_opt2 = match c_atc_as_constraint {
                        Some(as_) => {
                            let (ty_err_opt1, as_) = phase::localize_hint_no_subst(env, false, as_);
                            match &ty_default_opt {
                                Some(ty) => {
                                    let ty_err_opt2 = typing_ops::sub_type(
                                        pos.clone(),
                                        Ureason::URtypeconstCstr,
                                        env,
                                        ty.clone(),
                                        as_,
                                        callback::unify_error(),
                                    );
                                    merge_errors(ty_err_opt1, ty_err_opt2)
                                }
                                None => ty_err_opt1,
                            }
                        }
                        None => None,
                    };
                    let ty_err_opt3 = match c_atc_super_constraint {
                        Some(super_) => {
                            let (te1, super_) = phase::localize_hint_no_subst(env, false, super_);
                            match &ty_default_opt {
                                Some(ty) => {
                                    let te2 = typing_ops::sub_type(
                                        pos.clone(),
                                        Ureason::URtypeconstCstr,
                                        env,
                                        super_,
                                        ty.clone(),
                                        callback::unify_error(),
                                    );
                                    merge_errors(te1, te2)
                                }
                                None => te1,
                            }
                        }
                        None => None,
                    };
                    let ty_err_opt = merge_errors(ty_err_opt2, ty_err_opt3);
                    ty_err_opt
                }
                aast::ClassTypeconst::TCConcrete(aast::ClassConcreteTypeconst {
                    c_tc_type: ty,
                }) => {
                    let (ty_err_opt, cycles, _ty) = phase::localize_hint_no_subst_report_cycles(
                        env,
                        false,
                        (pos.clone(), expansion),
                        ty,
                    );
                    add_typing_error_opt(env, &crate::type_expansions::report(&cycles));
                    ty_err_opt
                }
            };
            add_typing_error_opt(env, &ty_err_opt);

            let user_attributes = crate::typing::attributes_check_def(
                env,
                sn::attribute_kinds::TYPE_CONST,
                &c_tconst_user_attributes.0,
            );
            aast::ClassTypeconstDef {
                name: id.clone(),
                kind: c_tconst_kind.clone(),
                user_attributes: aast::UserAttributes(user_attributes),
                span: c_tconst_span.clone(),
                doc_comment: c_tconst_doc_comment.clone(),
                is_ctx: *c_tconst_is_ctx,
            }
        })
    })
}

fn class_const_def(
    in_enum_class: bool,
    c: &nast::Class_,
    cls: &cls::T,
    env: &mut Env,
    cc: &nast::ClassConst,
) -> (tast::ClassConst, Ty) {
    let tcopt = env::get_tcopt(env).clone();
    // `Some env`: the environment as it is before the constant is checked.
    let env_opt = env.clone();
    let default = (
        aast::ClassConst {
            user_attributes: aast::UserAttributes(vec![]),
            type_: None,
            id: cc.id.clone(),
            kind: aast::ClassConstKind::CCAbstract(None),
            span: cc.span.clone(),
            doc_comment: cc.doc_comment.clone(),
        },
        make_type::nothing(reason::none()),
    );
    enable::if_matches_regexp(default, &tcopt, Some(&env_opt), &cc.id, || {
        profile::measure_elapsed_time_and_report(&tcopt, Some(&env_opt), &cc.id, || {
            let aast::ClassConst {
                type_: h,
                id,
                kind: k,
                ..
            } = cc;
            let (hint_ty, opt_expected, et_enforced) = match h {
                None => {
                    match k {
                        aast::ClassConstKind::CCAbstract(_)
                            if !is_enum_or_enum_class(c.kind)
                                && tcopt.tco_require_types_class_consts > 0 =>
                        {
                            let custom_err_config =
                                typechecker_options::custom_error_config(&tcopt);
                            add_naming_error(
                                NamingError::MissingTypehint(id.0.clone()),
                                custom_err_config,
                            )
                        }
                        _ if !is_enum_or_enum_class(c.kind)
                            && tcopt.tco_require_types_class_consts > 1 =>
                        {
                            let custom_err_config =
                                typechecker_options::custom_error_config(&tcopt);
                            add_naming_error(
                                NamingError::MissingTypehint(id.0.clone()),
                                custom_err_config,
                            )
                        }
                        aast::ClassConstKind::CCAbstract(None) => {}
                        aast::ClassConstKind::CCAbstract(Some(e) /* default */)
                        | aast::ClassConstKind::CCConcrete(e) => {
                            if !decl_utils::is_literal_with_trivially_inferable_type(e)
                                && !is_enum_or_enum_class(c.kind)
                                && !env::is_hhi(env)
                            {
                                let custom_err_config =
                                    typechecker_options::custom_error_config(&tcopt);
                                add_naming_error(
                                    NamingError::MissingTypehint(id.0.clone()),
                                    custom_err_config,
                                )
                            }
                        }
                    }
                    let ty = env::fresh_type(env, id.0.clone());
                    (ty, None, Enforcement::Unenforced)
                }
                Some(h) => {
                    let ty = decl_hint::hint(&env.decl_env, h);
                    let (et_enforced, ty) =
                        typing_enforceability::compute_enforced_ty(Some(cls), env, ty);
                    let (ty_err_opt, ty) = phase::localize_no_subst(env, false, &ty);
                    add_typing_error_opt(env, &ty_err_opt);
                    // Removing the HH\MemberOf wrapper in case of enum classes so the
                    // following call to expr_* has the right expected type
                    let opt_ty = if in_enum_class {
                        match get_node(&ty) {
                            Ty_::Tnewtype(memberof, args, _)
                                if args.len() == 2 && memberof == sn::classes::MEMBER_OF =>
                            {
                                args[1].clone()
                            }
                            _ => ty.clone(),
                        }
                    } else {
                        ty.clone()
                    };
                    (
                        ty,
                        Some(expected_ty::make(
                            None,
                            None,
                            id.0.clone(),
                            Ureason::URhint,
                            opt_ty,
                        )),
                        et_enforced,
                    )
                }
            };
            let check = |env: &mut Env, ty_: Ty| -> Option<typing_error::T> {
                // Lifted out to closure to illustrate which variables are captured
                typing_coercion::coerce_type(
                    None,
                    None,
                    None,
                    id.0.clone(),
                    Ureason::URhint,
                    env,
                    ty_,
                    hint_ty.clone(),
                    et_enforced,
                    callback::class_constant_value_does_not_match_hint(),
                )
            };
            let type_and_check =
                |env: &mut Env, e: &nast::Expr| -> (Option<typing_error::T>, tast::Expr, Ty) {
                    let (te, ty_) =
                        crate::typing::expr_with_pure_coeffects(opt_expected.as_ref(), env, e);
                    let err = check(env, ty_.clone());
                    (err, te, ty_)
                };
            let check_class = |env: &Env, e: &nast::Expr, ty: &Ty| {
                typing_class_pointers::check_string_coercion_point(env, e, ty)
            };
            let (ty_err_opt, kind, ty) = match k {
                aast::ClassConstKind::CCConcrete(e) if in_enum_class => {
                    let (cap, unsafe_cap) = {
                        // Enum class constant initializers are restricted to be `write_props`
                        let make_hint = |pos: &Pos, s: &str| {
                            aast::Hint(
                                pos.clone(),
                                Box::new(aast::Hint_::Happly(
                                    ast_defs::Id(pos.clone(), s.to_string()),
                                    vec![],
                                )),
                            )
                        };
                        let e_pos = aast_utils::get_expr_pos(e);
                        let enum_class_ctx = Some(aast::Contexts(
                            e_pos.clone(),
                            vec![make_hint(&e_pos, WRITE_PROPS)],
                        ));
                        typing_coeffects::type_capability(
                            env,
                            enum_class_ctx.as_ref(),
                            enum_class_ctx.as_ref(),
                            &e_pos,
                        )
                    };
                    let (te, ty_) =
                        crate::typing::with_special_coeffects(env, cap, unsafe_cap, |env| {
                            crate::typing::expr(opt_expected.as_ref(), env, e)
                        });
                    let (te, ty_) = match deref(&hint_ty) {
                        (r, Ty_::Tnewtype(memberof, args, def_ty))
                            if args.len() == 2 && memberof == sn::classes::MEMBER_OF =>
                        {
                            let enum_name = args[0].clone();
                            check_class(env, e, &def_ty);
                            let lift = |r: reason::T, ty: Ty| {
                                mk((
                                    r,
                                    Ty_::Tnewtype(
                                        memberof.clone(),
                                        vec![enum_name.clone(), ty.clone()],
                                        ty,
                                    ),
                                ))
                            };
                            let aast::Expr(te_ty, p, te_) = te;
                            let te = aast::Expr(lift(get_reason(&te_ty).clone(), te_ty), p, te_);
                            let ty_ = lift(r, ty_);
                            (te, ty_)
                        }
                        _ => (te, ty_),
                    };
                    let err = check(env, ty_.clone());
                    (err, aast::ClassConstKind::CCConcrete(te), ty_)
                }
                aast::ClassConstKind::CCConcrete(e)
                    if matches!(e.2, aast::Expr_::Omitted) && env::is_hhi(env) =>
                {
                    // We don't require class consts to have a value set for decl purposes
                    // in HHI files so it may just be a placeholder, therefore we don't care
                    // about checking the value and simply pass it through
                    let (te, _ty) = crate::typing::expr(None, env, e);
                    (None, aast::ClassConstKind::CCConcrete(te), hint_ty.clone())
                }
                aast::ClassConstKind::CCConcrete(e) => {
                    check_class(env, e, &hint_ty);
                    let (err, te, ty_) = type_and_check(env, e);
                    (err, aast::ClassConstKind::CCConcrete(te), ty_)
                }
                aast::ClassConstKind::CCAbstract(Some(default)) => {
                    check_class(env, default, &hint_ty);
                    let (err, tdefault, ty_) = type_and_check(env, default);
                    (err, aast::ClassConstKind::CCAbstract(Some(tdefault)), ty_)
                }
                aast::ClassConstKind::CCAbstract(None) => (
                    None,
                    aast::ClassConstKind::CCAbstract(None),
                    hint_ty.clone(),
                ),
            };
            let user_attributes = if ast_defs::is_c_class(c.kind) || ast_defs::is_c_trait(c.kind) {
                crate::typing::attributes_check_def(
                    env,
                    sn::attribute_kinds::CLS_CST,
                    &cc.user_attributes.0,
                )
            } else {
                assert!(cc.user_attributes.0.is_empty());
                vec![]
            };
            add_typing_error_opt(env, &ty_err_opt);
            (
                aast::ClassConst {
                    type_: cc.type_.clone(),
                    id: cc.id.clone(),
                    kind,
                    span: cc.span.clone(),
                    doc_comment: cc.doc_comment.clone(),
                    user_attributes: aast::UserAttributes(user_attributes),
                },
                ty,
            )
        })
    })
}

fn class_constr_def(
    is_disposable: bool,
    env: &Env,
    cls: &cls::T,
    constructor: Option<&nast::Method_>,
) -> Option<tast_with_dynamic::T<tast::Method_>> {
    constructor.and_then(|m| method_def(is_disposable, env, cls, m))
}

/// Type-check a property declaration, with optional initializer
fn class_var_def(
    is_static: bool,
    is_noautodynamic: bool,
    cls: &cls::T,
    env: &mut Env,
    cv: &nast::ClassVar,
) -> tast::ClassVar {
    let tcopt = env::get_tcopt(env).clone();
    // `Some env`: the environment as it is before the property is checked.
    let env_opt = env.clone();
    profile::measure_elapsed_time_and_report(&tcopt, Some(&env_opt), &cv.id, || {
        // First pick up and localize the hint if it exists
        let decl_cty = decl_fun_utils::hint_to_type_opt(&env.decl_env, cv.type_.1.as_ref());
        let no_auto_likes = mem(sn::user_attributes::NO_AUTO_LIKES, &cv.user_attributes);
        let expected = match &decl_cty {
            None => None,
            Some(decl_cty) => {
                let (et_enforced, decl_cty) =
                    typing_enforceability::compute_enforced_ty(Some(cls), env, decl_cty.clone());
                let (ty_err_opt, cty) = phase::localize_no_subst(env, false, &decl_cty);
                let cty = match et_enforced {
                    Enforcement::Enforced if cv.xhp_attr.is_none() => cty,
                    _ => {
                        let add_like = !is_noautodynamic && !no_auto_likes;
                        if env.genv.tcopt.po.everything_sdt && add_like {
                            tutils::make_like(None, env, cty)
                        } else {
                            if add_like {
                                typing_log::log_pessimise_prop(env, &cv.id.0, &cv.id.1)
                            }
                            cty
                        }
                    }
                };
                add_typing_error_opt(env, &ty_err_opt);
                let expected = Some(expected_ty::make(
                    None,
                    None,
                    cv.span.clone(),
                    Ureason::URhint,
                    cty,
                ));
                expected
            }
        };
        // Next check the expression, passing in expected type if present
        let (ty_err_opt, typed_cv_expr) = match &cv.expr {
            None => (None, None),
            Some(e) => {
                let (te, ty) = crate::typing::expr_with_pure_coeffects(expected.as_ref(), env, e);
                // Check that the inferred type is a subtype of the expected type.
                // Eventually this will be the responsibility of `expr`
                let ty_err_opt = match &expected {
                    None => None,
                    Some(expected_ty::T {
                        pos: p,
                        reason: ur,
                        ty: cty,
                        is_dynamic_aware,
                        ignore_readonly,
                    }) => typing_coercion::coerce_type(
                        None,
                        Some(*is_dynamic_aware),
                        Some(*ignore_readonly),
                        p.clone(),
                        ur.clone(),
                        env,
                        ty,
                        cty.clone(),
                        Enforcement::Enforced, // TODO akenn: flow this in
                        callback::class_property_initializer_type_does_not_match_hint(),
                    ),
                };
                (ty_err_opt, Some(te))
            }
        };
        add_typing_error_opt(env, &ty_err_opt);

        let user_attributes = crate::typing::attributes_check_def(
            env,
            if is_static {
                sn::attribute_kinds::STATIC_PROPERTY
            } else {
                sn::attribute_kinds::INST_PROPERTY
            },
            &cv.user_attributes.0,
        );

        if cv.type_.1.is_none() {
            let vis = match cv.visibility {
                aast::Visibility::Public => naming_error::Visibility::Vpublic,
                aast::Visibility::Private => naming_error::Visibility::Vprivate,
                aast::Visibility::Internal => naming_error::Visibility::Vinternal,
                aast::Visibility::Protected => naming_error::Visibility::Vprotected,
                aast::Visibility::ProtectedInternal => naming_error::Visibility::VprotectedInternal,
            };
            let ast_defs::Id(pos, prop_name) = &cv.id;
            let custom_err_config = typechecker_options::custom_error_config(&tcopt);
            add_naming_error(
                NamingError::PropWithoutTypehint {
                    vis,
                    pos: pos.clone(),
                    prop_name: prop_name.clone(),
                },
                custom_err_config,
            )
        }

        let cv_type = match &expected {
            Some(expected) => aast::TypeHint(expected.ty.clone(), cv.type_.1.clone()),
            None => tast::dummy_type_hint(cv.type_.1.clone()),
        };
        let cv_type_ty = &cv_type.0;
        // if the class implements dynamic, then check that the type of the property
        // is enforceable (for writing) and coerces to dynamic (for reading)
        if cls::get_support_dynamic_type(cls)
            && !crate::aast_defs::equal_visibility(cv.visibility, aast::Visibility::Private)
        {
            let mut env_with_require_dynamic = env.clone();
            typing_dynamic::add_require_dynamic_bounds(&mut env_with_require_dynamic, cls);
            let err = match &decl_cty {
                None => None,
                Some(ty) => typing_dynamic::check_property_sound_for_dynamic_write(
                    Some(cls),
                    |pos, prop_name, class_name, (prop_pos, prop_type)| {
                        typing_error::primary(primary::T::Property_is_not_enforceable {
                            pos,
                            prop_name,
                            class_name,
                            prop_pos,
                            prop_type,
                        })
                    },
                    &env_with_require_dynamic,
                    cls::name(cls),
                    (cv.id.0.clone(), cv.id.1.clone()),
                    ty,
                    Some(cv_type_ty.clone()),
                ),
            };
            add_typing_error_opt(env, &err);

            let err = typing_dynamic::check_property_sound_for_dynamic_read(
                |pos, prop_name, class_name, (prop_pos, prop_type)| {
                    typing_error::primary(primary::T::Property_is_not_dynamic {
                        pos,
                        prop_name,
                        class_name,
                        prop_pos,
                        prop_type,
                    })
                },
                &env_with_require_dynamic,
                cls::name(cls),
                (cv.id.0.clone(), cv.id.1.clone()),
                cv_type_ty,
            );
            add_typing_error_opt(env, &err);
        }
        aast::ClassVar {
            final_: cv.final_,
            xhp_attr: cv.xhp_attr.clone(),
            abstract_: cv.abstract_,
            visibility: cv.visibility,
            type_: cv_type,
            id: cv.id.clone(),
            expr: typed_cv_expr,
            user_attributes: aast::UserAttributes(user_attributes),
            doc_comment: cv.doc_comment.clone(),
            // Can make None to save space
            is_static,
            span: cv.span.clone(),
            readonly: cv.readonly,
        }
    })
}

/// Any class that extends a class or implements an interface
/// that declares `<<__SupportDynamicType>>` must itself declare
/// `<<__SupportDynamicType>>`. This is checked elsewhere. But if any generic
/// parameters are marked `<<__RequireDynamic>>` then we must check that the
/// conditional support for dynamic is sound.
///
/// We require that:
/// - If t <: dynamic
/// - and C<T1,..,Tn> extends t
/// - then C<T1,...,Tn> <: dynamic
fn check_generic_class_with_SupportDynamicType(
    env: &mut Env,
    c: &nast::Class_,
    tc: &cls::T,
    parents: &[(aast::Hint, DeclTy)],
) {
    let ast_defs::Id(pc, c_name) = &c.name;
    let check_support_dynamic_type = cls::get_support_dynamic_type(tc);
    if check_support_dynamic_type {
        let dynamic_ty =
            make_type::supportdyn_mixed(reason::dynamic_coercion(reason::witness(pc.clone())));
        // `ty_errs` is a cons list in OCaml (the last error is its head): the
        // errors are pushed here, and the list is reversed at the end.
        let mut ty_errs: Vec<typing_error::T> = vec![];
        for (_, parent_ty) in parents {
            let (ty_err_opt1, parent_lty) = phase::localize_no_subst(env, true, parent_ty);
            let ty_err_opt2 = match get_node(&parent_lty) {
                Ty_::Tclass((_, name), _, _) => match env::get_class(env, name) {
                    decl_entry::T::Found(c) if cls::get_support_dynamic_type(&c) => {
                        let mut env_with_assumptions = env.clone();
                        typing_subtype::add_constraint(
                            &mut env_with_assumptions,
                            ConstraintKind::ConstraintAs,
                            parent_lty.clone(),
                            dynamic_ty.clone(),
                            Some(reasons_callback::unify_error_at(pc.clone())),
                        );
                        match env::get_self_ty(env) {
                            Some(self_ty) => {
                                let ty_name = {
                                    let env = env.clone();
                                    let parent_ty = parent_ty.clone();
                                    Lazy::new(move || {
                                        typing_print::full_strip_ns_decl(
                                            None,
                                            false,
                                            &env,
                                            &parent_ty.to_oxidized(),
                                        )
                                    })
                                };
                                let self_ty_name = {
                                    let env = env.clone();
                                    let self_ty = self_ty.clone();
                                    Lazy::new(move || {
                                        typing_print::full_strip_ns(true, &env, &self_ty)
                                    })
                                };
                                let err = tutils::supports_dynamic(
                                    &mut env_with_assumptions,
                                    self_ty,
                                    Some(reasons_callback::bad_conditional_support_dynamic(
                                        pc.clone(),
                                        c_name.clone(),
                                        name.clone(),
                                        ty_name,
                                        self_ty_name,
                                    )),
                                );
                                *env = env_with_assumptions;
                                err
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                },
                _ => None,
            };
            match merge_errors(ty_err_opt1, ty_err_opt2) {
                None => {}
                Some(e) => ty_errs.push(e),
            }
        }
        ty_errs.reverse();
        add_typing_error_opt(env, &typing_error::multiple_opt(ty_errs));
    }
}

/// Check that the classish type being checked aligns with its
/// parents on the <<__SupportDynamicType>> attribute - if
/// a (non-trait) parent has the attribute, then the type should have
/// it too.
/// The opposite is also true, but not checked here.
fn check_SupportDynamicType(env: &Env, c: &nast::Class_, tc: &cls::T) {
    let support_dynamic_type = cls::get_support_dynamic_type(tc);
    let error_parent_support_dynamic_type = |parent: &cls::T, child_support_dyn: bool| {
        add_primary(
            env,
            primary::T::Parent_support_dynamic_type {
                pos: c.name.0.clone(),
                child_name: c.name.1.clone(),
                child_kind: c.kind,
                parent_name: cls::name(parent),
                parent_kind: cls::kind(parent),
                child_support_dyn,
            },
        )
    };
    match c.kind {
        ClassishKind::Cenum | ClassishKind::CenumClass(_) => {
            // Avoid parent SDT check on things that cannot be SDT themselves
        }
        ClassishKind::Cclass(_) | ClassishKind::Cinterface | ClassishKind::Ctrait => {
            for name in cls::all_ancestor_names(tc) {
                match env::get_class(env, &name) {
                    decl_entry::T::Found(parent_type) => match cls::kind(&parent_type) {
                        ClassishKind::Cclass(_) | ClassishKind::Cinterface => {
                            // ensure that we implement dynamic if we are a subclass/subinterface of a class/interface
                            // that implements dynamic.  Upward well-formedness checks are performed in Typing_extends
                            if cls::get_support_dynamic_type(&parent_type) && !support_dynamic_type
                            {
                                error_parent_support_dynamic_type(
                                    &parent_type,
                                    support_dynamic_type,
                                )
                            }
                        }
                        ClassishKind::Cenum
                        | ClassishKind::CenumClass(_)
                        | ClassishKind::Ctrait => {}
                    },
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
        }
    }
}

/// Check methods with <<__Override>> have a corresponding overridden method.
fn check_override_has_parent<Ex, En>(c: &aast::Class_<Ex, En>, tc: &cls::T, env: &Env) {
    if !ast_defs::is_c_trait(c.kind) {
        // We don't want to check __Override on traits. __Override on
        // traits asserts that the *using* class has an inherited method
        // that we're overriding.
        for m in &c.methods {
            let id = &m.name.1;
            match cls::get_any_method(m.static_, tc, id) {
                Some(ce) => {
                    if typing_defs::get_ce_superfluous_override(&ce) {
                        add_primary(
                            env,
                            primary::T::Should_not_be_override {
                                pos: m.name.0.clone(),
                                class_id: c.name.1.clone(),
                                id: id.clone(),
                            },
                        )
                    }
                }
                None => {}
            }
        }
    }
}

/// Check __Override on class methods included from traits.
fn check_used_methods_with_override(env: &Env, c: &nast::Class_, tc: &cls::T) {
    let ast_defs::Id(class_pos, class_name) = &c.name;

    let check_override = |(meth_name, ce): (String, cls::ClassElt)| {
        if typing_defs::get_ce_superfluous_override(&ce) && ce.ce_origin != *class_name {
            match env::get_class(env, &ce.ce_origin) {
                decl_entry::T::Found(parent_class)
                    if ast_defs::is_c_trait(cls::kind(&parent_class)) =>
                {
                    // If we've included a method from a trait that has
                    // __Override, but there's no inherited method on this class
                    // that we're overridding, that's an error.
                    add_primary(
                        env,
                        primary::T::Override_per_trait {
                            pos: class_pos.clone(),
                            class_name: class_name.clone(),
                            meth_name,
                            trait_name: ce.ce_origin.clone(),
                            meth_pos: LazyLock::force(&ce.ce_pos).clone(),
                        },
                    )
                }
                _ => {}
            }
        }
    };

    if !ast_defs::is_c_trait(c.kind) {
        for x in cls::methods(tc) {
            check_override(x)
        }
        for x in cls::smethods(tc) {
            check_override(x)
        }
    }
}

/// Check proper usage of the __Override attribute.
fn check_override_keyword(env: &Env, c: &nast::Class_, tc: &cls::T) {
    check_override_has_parent(c, tc, env);
    check_used_methods_with_override(env, c, tc)
}

/// If the class is sealed, check that the elements of the whitelist
/// are descendants of the class and emit a warning if not.
fn check_sealed(env: &Env, c: &nast::Class_) {
    let is_enum = is_enum_or_enum_class(c.kind);
    sealed_subtype(c, is_enum, env)
}

fn check_class_require_non_strict_constraints(env: &mut Env, c: &nast::Class_, tc: &cls::T) {
    let this_ty = || DeclTy::new(R::none(), DeclTy_::Tthis);
    let req_non_strict_constraints: Vec<DeclWhereConstraint> =
        cls::all_ancestor_req_class_requirements(tc)
            .into_iter()
            .map(|r| WhereConstraint(this_ty(), ConstraintKind::ConstraintEq, r.ty))
            .chain(
                cls::all_ancestor_req_this_as_requirements(tc)
                    .into_iter()
                    .map(|r| WhereConstraint(this_ty(), ConstraintKind::ConstraintAs, r.ty)),
            )
            .collect();
    let tparams: Vec<DeclTparam> = c
        .tparams
        .iter()
        .map(|tp| decl_hint::aast_tparam_to_decl_tparam(&env.decl_env, tp))
        .collect();
    let ty_err_opt1 = phase::localize_and_add_generic_parameters_and_where_constraints(
        &empty_expand_env(),
        env,
        &tparams,
        &req_non_strict_constraints,
    );
    add_typing_error_opt(env, &ty_err_opt1);
}

/// `class_parents`
#[derive(Clone, Debug)]
struct ClassParents {
    extends: Vec<(aast::Hint, DeclTy)>,
    implements: Vec<(aast::Hint, DeclTy)>,
    uses: Vec<(aast::Hint, DeclTy)>,
    req_extends: Vec<(aast::Hint, DeclTy)>,
    req_implements: Vec<(aast::Hint, DeclTy)>,
    req_class: Vec<(aast::Hint, DeclTy)>,
    req_this_as: Vec<(aast::Hint, DeclTy)>,
    enum_includes: Option<Vec<(aast::Hint, DeclTy)>>,
    xhp_attr_uses: Vec<(aast::Hint, DeclTy)>,
}

fn class_parents_hints_to_types(env: &Env, c: &nast::Class_) -> ClassParents {
    let hints_and_decl_tys = |hints: Vec<&aast::Hint>| -> Vec<(aast::Hint, DeclTy)> {
        hints
            .into_iter()
            .map(|hint| (hint.clone(), decl_hint::hint(&env.decl_env, hint)))
            .collect()
    };
    let extends = hints_and_decl_tys(c.extends.iter().collect());
    let implements = hints_and_decl_tys(c.implements.iter().collect());
    let uses = hints_and_decl_tys(c.uses.iter().collect());
    let (req_extends, req_implements, req_class, req_this_as) = aast::split_reqs(&c.reqs);
    let req_extends = hints_and_decl_tys(req_extends);
    let req_implements = hints_and_decl_tys(req_implements);
    let req_class = hints_and_decl_tys(req_class);
    let req_this_as = hints_and_decl_tys(req_this_as);
    let enum_includes = c
        .enum_
        .as_ref()
        .map(|e| hints_and_decl_tys(e.includes.iter().collect()));
    let xhp_attr_uses = hints_and_decl_tys(c.xhp_attr_uses.iter().collect());
    ClassParents {
        extends,
        implements,
        uses,
        req_extends,
        req_implements,
        req_class,
        req_this_as,
        enum_includes,
        xhp_attr_uses,
    }
}

/// Add dependencies to parent constructors or produce errors if they're not a Tapply.
fn check_parents_are_tapply_add_constructor_deps(
    env: &Env,
    c: &nast::Class_,
    parents: &ClassParents,
) {
    let ClassParents {
        extends,
        implements,
        uses,
        req_extends,
        req_implements,
        req_class,
        req_this_as,
        enum_includes,
        xhp_attr_uses,
    } = parents;
    check_is_tapply_add_constructor_extends_dep(env, None, extends);
    check_is_tapply_add_constructor_extends_dep(
        env,
        Some(!(ast_defs::is_c_trait(c.kind) || ast_defs::is_c_abstract(c.kind))),
        implements,
    );
    check_is_tapply_add_constructor_extends_dep(env, None, uses);
    check_is_tapply_add_constructor_extends_dep(env, None, req_class);
    check_is_tapply_add_constructor_extends_dep(env, None, req_this_as);
    check_is_tapply_add_constructor_extends_dep(env, None, req_extends);
    check_is_tapply_add_constructor_extends_dep(env, None, req_implements);
    if let Some(enum_includes) = enum_includes {
        check_is_tapply_add_constructor_extends_dep(env, None, enum_includes)
    }
    check_is_tapply_add_constructor_extends_dep(env, Some(true), xhp_attr_uses);
}

fn check_class_attributes(
    env: &mut Env,
    cls: &nast::Class_,
) -> (Vec<tast::UserAttribute>, Vec<tast::FileAttribute>) {
    let user_attributes = {
        let kind = if ast_defs::is_c_enum(cls.kind) {
            sn::attribute_kinds::ENUM
        } else if ast_defs::is_c_enum_class(cls.kind) {
            sn::attribute_kinds::ENUM_CLS
        } else {
            sn::attribute_kinds::CLS
        };
        crate::typing::attributes_check_def(env, kind, &cls.user_attributes.0)
    };
    let file_attrs = crate::typing::file_attributes(env, &cls.file_attributes);
    (user_attributes, file_attrs)
}

/// Check type parameter definition, including variance, and add constraints to the environment.
fn check_class_type_parameters_add_constraints(env: &mut Env, c: &nast::Class_, tc: &cls::T) {
    check_class_require_non_strict_constraints(env, c, tc);
    typing_variance::class_def(env, c);
}

/// Check wellformedness of all type hints in the class.
fn check_hint_wellformedness_in_class(env: &mut Env, c: &nast::Class_, parents: &ClassParents) {
    check_parents_are_tapply_add_constructor_deps(env, c, parents);
    for err in typing_type_wellformedness::class_(env, c) {
        typing_error_utils::add_typing_error(&err, env)
    }
}

/// Internal classes can carry `<<__TestsBypassVisibility>>` to become visible
/// from configured test ancestors. If an internal member has the attribute, the
/// containing internal class must also have it so the class symbol itself can be
/// resolved from those tests.
fn check_tests_bypass_visibility_on_internal_class(env: &Env, c: &nast::Class_) {
    let class_is_internal = c.internal;
    let class_has_attr = mem(
        sn::user_attributes::TESTS_BYPASS_VISIBILITY,
        &c.user_attributes,
    );
    if class_is_internal && !class_has_attr {
        let check_member =
            |attrs: &aast::UserAttributes<(), ()>, member_pos: &Pos, member_name: &str| {
                if mem(sn::user_attributes::TESTS_BYPASS_VISIBILITY, attrs) {
                    add_primary(
                        env,
                        primary::T::Tests_bypass_visibility_on_member_without_class {
                            pos: member_pos.clone(),
                            member_name: member_name.to_string(),
                            class_name: c.name.1.clone(),
                        },
                    )
                }
            };
        for m in &c.methods {
            check_member(&m.user_attributes, &m.name.0, &m.name.1)
        }
        for cv in &c.vars {
            check_member(&cv.user_attributes, &cv.id.0, &cv.id.1)
        }
    }
}

/// Perform all class wellformedness checks which don't involve the hierarchy:
/// - attributes
/// - property initialization checks
/// - tests-bypass-visibility wellformedness
/// - type parameter checks
/// - type hint wellformedness
/// - generic static properties
fn class_wellformedness_checks(
    env: &mut Env,
    c: &nast::Class_,
    tc: &cls::T,
    parents: &ClassParents,
) -> (Vec<tast::UserAttribute>, Vec<tast::FileAttribute>) {
    // Class and file level attributes are ran outside of the class context and thus should not
    // have access to `self` in the environment, so we unset self while running these attribute checks.
    //
    // Note: This has the side effect of allowing internal classes to be referenced on class-level attributes
    // that are applied to a public trait. This is intended and safe because class-level attributes are not
    // copied to the use site of a trait.
    let (user_attributes, file_attrs) =
        env::run_with_no_self(env, |env| check_class_attributes(env, c));
    // `Nast_init_check.class_ env c`: run by `crate::nast_check::check_program`
    // (see the documentation of this module), without the typing environment;
    // when the dependency edges are recorded, the lookups it makes through
    // the environment in the OCaml are made here, for their edges.
    if env::deps::records_dependency_edges(env) {
        crate::nast_check::nast_init_check::record_dependency_edges(env, c);
    }
    check_tests_bypass_visibility_on_internal_class(env, c);
    check_class_type_parameters_add_constraints(env, c, tc);
    check_hint_wellformedness_in_class(env, c, parents);
    check_no_generic_static_property(env, tc);
    (user_attributes, file_attrs)
}

/// Reject re-promoting (via a constructor parameter visibility modifier) a
/// property that is already declared by an ancestor. Such re-declaration is
/// error-prone and can make HHVM fatal at runtime when the inherited type-hint
/// bound ends up violated (e.g. with generics). The un-promoted forms remain
/// legal: declaring the property separately, or forwarding the value to
/// `parent::__construct` without a visibility modifier. Private (non-LSB)
/// ancestor properties are excluded since those are shadowed per-subclass rather
/// than inherited.
fn check_no_redeclared_promoted_props(env: &Env, c: &nast::Class_, parents: &ClassParents) {
    let (constructor, _, _) = aast::split_methods(&c.methods);
    match constructor {
        _ if !env::get_tcopt(env).tco_reject_promoted_property_redeclaration => {
            // Rollout flag, off by default: re-promoting an inherited property is a
            // widespread pattern in existing code, so this is gated behind
            // [reject_promoted_property_redeclaration] until callers are migrated.
        }
        None => {}
        Some(m) => {
            let ancestor_prop = |prop_name: &str| {
                parents
                    .extends
                    .iter()
                    .find_map(|(_, parent_ty)| match parent_ty.node_ref() {
                        DeclTy_::Tapply(id_and_args) => {
                            let parent_class_name = id_and_args.0.id_ref().as_str();
                            match env::get_class(env, parent_class_name) {
                                decl_entry::T::Found(parent_cls) => {
                                    // Private (non-LSB) properties are effectively cloned into each
                                    // subclass, so re-declaring one is legal shadowing rather than a
                                    // conflicting redeclaration.
                                    env::get_prop(env, &parent_cls, prop_name)
                                        .filter(|ce| !typing_defs::class_elt_is_private_not_lsb(ce))
                                }
                                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                                    None
                                }
                            }
                        }
                        _ => None,
                    })
            };
            for param in &m.params {
                match &param.visibility {
                    None => {}
                    Some(_) => {
                        let prop_name = param
                            .name
                            .strip_prefix('$')
                            .unwrap_or(&param.name)
                            .to_string();
                        match ancestor_prop(&prop_name) {
                            None => {}
                            Some(parent_ce) => add_primary(
                                env,
                                primary::T::Redeclaring_promoted_property {
                                    pos: param.pos.clone(),
                                    prop_name,
                                    parent_pos: LazyLock::force(&parent_ce.ce_pos).clone(),
                                    parent_name: parent_ce.ce_origin.clone(),
                                },
                            ),
                        }
                    }
                }
            }
        }
    }
}

/// Perform all hierarchy checks,
/// i.e. checking that making this class a child of its parents is legal:
/// - requirements from `require` statements
/// - duplicate parents
/// - parents can have children (not final or const)
/// - __Sealed attribute
/// - dynamic-type related attributes w.r.t. parents
/// - __Disposable attribute w.r.t. parents
/// - individual member checks:
///   - subtyping parent members
///   - not redeclaring class properties
///   - __Override attribute check
///   - enum inclusions
///   - abstract members in concrete class
///   - non-const members in const class
fn class_hierarchy_checks(env: &mut Env, c: &nast::Class_, tc: &cls::T, parents: &ClassParents) {
    if skip_hierarchy_checks(&env::get_ctx(env)) {
    } else {
        let pc = &c.name.0;
        let ClassParents {
            extends,
            implements,
            uses,
            req_extends,
            req_implements,
            req_class: _,
            req_this_as: _,
            enum_includes: _,
            xhp_attr_uses: _,
        } = parents;
        typing_requirements::check_class(env, pc, tc);
        check_override_keyword(env, c, tc);
        check_enum_includes(env, c);
        check_implements_or_extends_unique(implements, env);
        check_implements_or_extends_unique(extends, env);
        {
            let hints: Vec<&aast::Hint> = c
                .implements
                .iter()
                .chain(c.extends.iter())
                .chain(c.uses.iter())
                .collect();
            check_multiple_instantiation_inheritance(env, &(c.name.1.clone(), c.kind), &hints)
        }
        check_parent(env, c, tc);
        check_no_redeclared_promoted_props(env, c, parents);
        check_consistent_construct_not_abstract_final(env, c, tc);
        check_parents_sealed(env, c, tc);
        check_sealed(env, c);
        {
            // `let (_ : env) = ...`: the environment it returns is dropped.
            let extends_implements: Vec<(aast::Hint, DeclTy)> =
                extends.iter().chain(implements.iter()).cloned().collect();
            check_generic_class_with_SupportDynamicType(
                &mut env.clone(),
                c,
                tc,
                &extends_implements,
            )
        }
        if cls::has_const_attribute(tc) {
            for use_list in &c.uses {
                check_non_const_trait_members(pc, env, use_list)
            }
        }
        let impl_: Vec<(aast::Hint, DeclTy)> = extends
            .iter()
            .chain(implements.iter())
            .chain(uses.iter())
            .cloned()
            .collect();
        let impl_ = if env::get_tcopt(env).tco_require_extends_implements_ancestors {
            impl_
                .into_iter()
                .chain(req_extends.iter().cloned())
                .chain(req_implements.iter().cloned())
                .collect()
        } else {
            impl_
        };
        let implements_tys: Vec<DeclTy> = implements.iter().map(|(_, ty)| ty.clone()).collect();
        typing_extends::check_implements_extends_uses(env, &implements_tys, &impl_, (c, tc));
        if typing_disposable::is_disposable_class(env, tc) {
            for h in c.extends.iter().chain(c.uses.iter()) {
                typing_disposable::enforce_is_disposable(env, h)
            }
        }
    }
}

/// The members of a typed class: constants, type constants, instance and
/// static properties, methods.
type TypedMembers = (
    Vec<tast::ClassConst>,
    Vec<tast::ClassTypeconstDef>,
    Vec<tast::ClassVar>,
    Vec<tast::ClassVar>,
    tast_with_dynamic::T<Vec<tast::Method_>>,
);

fn check_class_members(env: &mut Env, c: &nast::Class_, tc: &cls::T) -> TypedMembers {
    let (static_vars, vars) = aast::split_vars(&c.vars);
    let (constructor, static_methods, methods) = aast::split_methods(&c.methods);
    let is_disposable = typing_disposable::is_disposable_class(env, tc);
    let is_noautodynamic = mem(sn::user_attributes::NO_AUTO_DYNAMIC, &c.user_attributes);
    let typed_vars: Vec<tast::ClassVar> = vars
        .iter()
        .map(|cv| class_var_def(false, is_noautodynamic, tc, env, cv))
        .collect();
    let typed_methods: Vec<tast_with_dynamic::T<tast::Method_>> = methods
        .iter()
        .filter_map(|m| method_def(is_disposable, env, tc, m))
        .collect();
    let typed_methods = tast_with_dynamic::collect(typed_methods);
    let typed_typeconsts: Vec<tast::ClassTypeconstDef> = c
        .typeconsts
        .iter()
        .map(|tconst| typeconst_def(c, env, tconst))
        .collect();
    let in_enum_class = env::is_enum_class(env, &c.name.1);
    let consts: Vec<(tast::ClassConst, Ty)> = c
        .consts
        .iter()
        .map(|cc| class_const_def(in_enum_class, c, tc, env, cc))
        .collect();
    let (typed_consts, const_types): (Vec<tast::ClassConst>, Vec<Ty>) = consts.into_iter().unzip();
    typing_enum::enum_class_check(env, &c.name.0, tc, &c.consts, &const_types);
    let typed_constructor = class_constr_def(is_disposable, env, tc, constructor);
    env::set_static(env);
    let typed_static_vars: Vec<tast::ClassVar> = static_vars
        .iter()
        .map(|cv| class_var_def(true, is_noautodynamic, tc, env, cv))
        .collect();
    let typed_static_methods: Vec<tast_with_dynamic::T<tast::Method_>> = static_methods
        .iter()
        .filter_map(|m| method_def(is_disposable, env, tc, m))
        .collect();
    let typed_static_methods = tast_with_dynamic::collect(typed_static_methods);
    let typed_methods = match typed_constructor {
        None => tast_with_dynamic::append(typed_static_methods, typed_methods),
        Some(ms) => tast_with_dynamic::append(
            tast_with_dynamic::cons(ms, typed_static_methods),
            typed_methods,
        ),
    };
    let typed_members = (
        typed_consts,
        typed_typeconsts,
        typed_vars,
        typed_static_vars,
        typed_methods,
    );
    typed_members
}

fn class_def_(
    restore_pos: &dyn Fn(&mut Env),
    env: &Env,
    c: &nast::Class_,
    tc: &cls::T,
) -> tast_with_dynamic::T<tast::Class_> {
    let mut env = env.clone();
    let env = &mut env;
    let parents = class_parents_hints_to_types(env, c);
    let (user_attributes, file_attrs) = class_wellformedness_checks(env, c, tc, &parents);
    class_hierarchy_checks(env, c, tc, &parents);
    typing_needs_concrete::check_class_def(env, c, tc);
    let (typed_consts, typed_typeconsts, typed_vars, typed_static_vars, typed_methods) =
        if env.genv.tcopt.po.ignore_string_methods && C_STRING == c.name.1 {
            (
                vec![],
                vec![],
                vec![],
                vec![],
                tast_with_dynamic::mk_without_dynamic(vec![]),
            )
        } else {
            check_class_members(env, c, tc)
        };
    let tparams = class_type_param(env, &c.tparams);
    let e1 = typing_solver::solve_all_unsolved_tyvars(env);
    check_SupportDynamicType(env, c, tc);
    add_typing_error_opt(env, &e1);
    restore_pos(env);
    let env: &Env = env;
    let mk_class_ = |typed_methods: Vec<tast::Method_>| -> tast::Class_ {
        aast::Class_ {
            span: c.span.clone(),
            annotation: env::save(&env::get_tpenv(env), env),
            mode: c.mode,
            final_: c.final_,
            is_xhp: c.is_xhp,
            has_xhp_keyword: c.has_xhp_keyword,
            kind: c.kind,
            name: c.name.clone(),
            tparams: tparams.clone(),
            extends: c.extends.clone(),
            uses: c.uses.clone(),
            xhp_attr_uses: c.xhp_attr_uses.clone(),
            xhp_category: c.xhp_category.clone(),
            reqs: c.reqs.clone(),
            implements: c.implements.clone(),
            consts: typed_consts.clone(),
            typeconsts: typed_typeconsts.clone(),
            vars: typed_static_vars
                .iter()
                .chain(typed_vars.iter())
                .cloned()
                .collect(),
            methods: typed_methods,
            file_attributes: file_attrs.clone(),
            user_attributes: aast::UserAttributes(user_attributes.clone()),
            namespace: c.namespace.clone(),
            enum_: c.enum_.clone(),
            doc_comment: c.doc_comment.clone(),
            xhp_children: c.xhp_children.clone(),
            xhp_attrs: vec![],
            emit_id: c.emit_id.clone(),
            internal: c.internal,
            module: c.module.clone(),
            docs_url: c.docs_url.clone(),
            package: c.package.clone(),
        }
    };
    let tast_with_dynamic::T {
        under_normal_assumptions,
        under_dynamic_assumptions,
    } = typed_methods;
    tast_with_dynamic::T {
        under_normal_assumptions: mk_class_(under_normal_assumptions),
        under_dynamic_assumptions: under_dynamic_assumptions.map(mk_class_),
    }
}

fn setup_env_for_class_def_check(ctx: &Arc<Ctx>, c: &nast::Class_) -> Env {
    let mut env =
        env_from_def::class_env(Some(decl_counters::Origin::TopLevel), Arc::clone(ctx), c);
    env::set_current_module(&mut env, c.module.clone());
    env::set_internal(&mut env, c.internal);
    env::set_current_package_membership(&mut env, c.package.clone());
    env
}

/// This is a helper for [Typing_toplevel.class_def]. Call that instead.
///
/// Must only be called if [Decl_provider.get_class] for this class's name will return
/// this class's decl. (which it might not, say, if there were duplicate definitions
/// and this class was the loser). This function will return None if the condition isn't
/// met.
pub fn class_def(ctx: &Arc<Ctx>, c: &nast::Class_) -> Option<tast_with_dynamic::T<tast::Class_>> {
    let mut env = setup_env_for_class_def_check(ctx, c);
    let pos = c.name.0.clone();
    let restore_pos = env::set_inference_env_pos(&mut env, Some(pos));
    match env::get_class(&env, &c.name.1) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
            let pos_s = crate::pos::string(&crate::pos::to_relative_string(&c.name.0));
            hack_event_logger::decl_consistency_bug(
                None,
                Some(&pos_s),
                Some(&c.name.1),
                "Decl consistency: class_def, but can't find a decl",
            );
            None
        }
        decl_entry::T::Found(tc) => {
            env::set_support_dynamic_type(&mut env, cls::get_support_dynamic_type(&tc));
            env::make_depend_on_current_module(&env);
            typing_helpers::add_decl_errors(&env, &cls::decl_errors(&tc));
            let result = class_def_(&*restore_pos, &env, c, &tc);
            Some(result)
        }
    }
}

pub struct ClassMemberStandaloneCheckEnv {
    cls: cls::T,
    env: Env,
    class_: nast::Class_,
}

/// Create an environment from a class that can be used to subsequently
/// type-check members of that class individually
pub fn make_class_member_standalone_check_env(
    ctx: &Arc<Ctx>,
    class_: &nast::Class_,
) -> Option<(Env, ClassMemberStandaloneCheckEnv)> {
    let mut env = setup_env_for_class_def_check(ctx, class_);
    let pos = class_.name.0.clone();
    // env flows out; restore will happen when method_def sets its own position
    let restore_pos = env::set_inference_env_pos(&mut env, Some(pos));
    let name = ast_defs::get_id(&class_.name);
    decl_entry::to_option(env::get_class(&env, &name)).map(|cls| {
        check_class_type_parameters_add_constraints(&mut env, class_, &cls);
        restore_pos(&mut env);
        (
            env.clone(),
            ClassMemberStandaloneCheckEnv {
                env,
                cls,
                class_: class_.clone(),
            },
        )
    })
}

/// Type-checks the given method of the class that was specific when creating
/// the [class_member_standalone_check_env]
pub fn method_def_standalone(
    standalone_env: &ClassMemberStandaloneCheckEnv,
    method_name: &str,
) -> Option<tast_with_dynamic::T<tast::Method_>> {
    let is_disposable =
        typing_disposable::is_disposable_class(&standalone_env.env, &standalone_env.cls);
    standalone_env
        .class_
        .methods
        .iter()
        .find(|m| m.name.1 == method_name)
        .and_then(|method_| {
            let static_env;
            let env = if method_.static_ {
                let mut env = standalone_env.env.clone();
                env::set_static(&mut env);
                static_env = env;
                &static_env
            } else {
                &standalone_env.env
            };
            method_def(is_disposable, env, &standalone_env.cls, method_)
        })
}
