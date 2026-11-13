// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_return.ml`. See `hh/PORTING.md`.
//!
//! Typing code concerned with return types.
//!
//! The OCaml defines `make_return_type` twice, the second calling (and
//! shadowing) the first: the first is [`make_return_type_`] here.

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::ast_defs::FunKind;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use ty::decl;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::pos;
use crate::typing_coercion;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_disposable;
use crate::typing_dynamic_utils;
use crate::typing_enforceability;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_return_info;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_log;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_ops;
use crate::typing_partial_enforcement;
use crate::typing_phase;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;
use crate::utils;

/// For async functions, strip Awaitable<_> from the return type
pub fn strip_awaitable(fun_kind: FunKind, env: &Env, ty: Ty) -> Ty {
    if !(fun_kind == FunKind::FAsync) {
        ty
    } else {
        // The environment that `expand_type` returns is dropped.
        let ty = env::expand_type(&mut env.clone(), ty);
        match get_node(&ty) {
            Ty_::Tclass((_, class_name), _, tyl)
                if tyl.len() == 1 && class_name == sn::classes::AWAITABLE =>
            {
                tyl[0].clone()
            }
            _ => {
                let mut env = env.clone();
                let ty_opt = typing_dynamic_utils::try_strip_dynamic(None, None, &mut env, &ty);
                match ty_opt {
                    Some(stripped) => {
                        let stripped = env::expand_type(&mut env.clone(), stripped);
                        match get_node(&stripped) {
                            Ty_::Tclass((_, class_name), _, tyl)
                                if tyl.len() == 1 && class_name == sn::classes::AWAITABLE =>
                            {
                                make_type::locl_like(get_reason(&ty).clone(), tyl[0].clone())
                            }
                            _ => ty,
                        }
                    }
                    None => ty,
                }
            }
        }
    }
}

fn enforce_return_not_disposable(ret_pos: Pos, fun_kind: FunKind, env: &Env, et: Ty) {
    let stripped_et = strip_awaitable(fun_kind, env, et);
    if let Some(ty_err) =
        typing_disposable::is_disposable_type(env, &stripped_et).map(|class_name| {
            typing_error::primary(typing_error::primary::T::Invalid_disposable_return_hint {
                pos: ret_pos,
                class_name: utils::strip_ns(&class_name).to_string(),
            })
        })
    {
        typing_error_utils::add_typing_error(&ty_err, env)
    }
}

fn has_attribute(attr: &str, l: &[nast::UserAttribute]) -> bool {
    l.iter()
        .any(|nast::UserAttribute { name: ua_name, .. }| attr == ua_name.1)
}

fn has_return_disposable_attribute(attrs: &[nast::UserAttribute]) -> bool {
    has_attribute(sn::user_attributes::RETURN_DISPOSABLE, attrs)
}

pub fn make_info(
    ignore_readonly: Option<bool>,
    ret_pos: Pos,
    fun_kind: FunKind,
    attributes: &[nast::UserAttribute],
    env: &Env,
    return_type: Ty,
) -> typing_env_return_info::T {
    let ignore_readonly = ignore_readonly.unwrap_or(false);
    let return_disposable = has_return_disposable_attribute(attributes);
    if !return_disposable {
        enforce_return_not_disposable(ret_pos, fun_kind, env, return_type.clone())
    }
    typing_env_return_info::T {
        return_type,
        return_disposable,
        return_ignore_readonly: ignore_readonly,
    }
}

/// Make a fresh Awaitable<_> etc making sure that any constraints (e.g. supportdyn)
/// are added to the type variable
fn make_wrapped_fresh_type(env: &mut Env, p: Pos, r: Reason, id: &str) -> Ty {
    let class_ = env::get_class(env, id);
    match class_ {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
            env::fresh_type_error(env, p) // Shouldn't happen
        }
        decl_entry::T::Found(class_) => {
            // The error is dropped.
            let (_, ty, _tal) = typing_phase::localize_targs_and_check_constraints(
                nonexact(),
                false,
                cls::pos(&class_),
                p.clone(),
                Some(false),
                env,
                &ast_defs::Id(p, id.to_string()),
                r,
                &cls::tparams(&class_),
                vec![],
            );
            ty
        }
    }
}

/// Create a return type with fresh type variables
fn make_fresh_return_type(env: &mut Env, p: Pos) -> Ty {
    let fun_kind = env::get_fn_kind(env);
    let r = reason::ret_fun_kind_from_decl((
        crate::pos_or_decl::of_raw_pos(p.clone()),
        fun_kind,
    ));
    match fun_kind {
        FunKind::FSync => env::fresh_type(env, p),
        FunKind::FAsync => make_wrapped_fresh_type(env, p, r, sn::classes::AWAITABLE),
        FunKind::FGenerator => make_wrapped_fresh_type(env, p, r, sn::classes::GENERATOR),
        FunKind::FAsyncGenerator => {
            make_wrapped_fresh_type(env, p, r, sn::classes::ASYNC_GENERATOR)
        }
    }
}

/// Force the return type of a function to adhere to the fun_kind specified in
/// the env
fn force_return_kind(is_toplevel: bool, env: &mut Env, p: Pos, ety: Ty) -> Ty {
    let fun_kind = env::get_fn_kind(env);
    let ty = env::expand_type(env, ety);
    match (fun_kind, get_node(&ty)) {
        // Sync functions can return anything
        (FunKind::FSync, _) => ty,
        // Each other fun kind needs a specific return type
        (FunKind::FAsync, _) if is_toplevel => {
            // For toplevel functions, this is already checked in the parser
            ty
        }
        (FunKind::FAsync, Ty_::Tclass((_, class_name), _, _))
            if class_name == sn::classes::AWAITABLE =>
        {
            // For toplevel functions, this is already checked in the parser
            ty
        }
        (FunKind::FAsync, _)
            if {
                // The environments that these return are dropped.
                let stripped = typing_dynamic_utils::strip_dynamic(&mut env.clone(), ty.clone());
                let stripped = env::expand_type(&mut env.clone(), stripped);
                match get_node(&stripped) {
                    Ty_::Tclass((_, class_name), _, _) => class_name == sn::classes::AWAITABLE,
                    _ => false,
                }
            } =>
        {
            ty
        }
        (FunKind::FGenerator, Ty_::Tclass((_, class_name), _, _))
            if class_name == sn::classes::GENERATOR =>
        {
            ty
        }
        (FunKind::FAsyncGenerator, Ty_::Tclass((_, class_name), _, _))
            if class_name == sn::classes::ASYNC_GENERATOR =>
        {
            ty
        }
        _ => {
            let wrapped_ty = make_fresh_return_type(env, p.clone());
            let ty_err_opt = typing_ops::sub_type(None, 
                p,
                Ureason::URreturn,
                env,
                wrapped_ty.clone(),
                ty,
                typing_error::callback::unify_error(),
            );
            if let Some(ty_err) = &ty_err_opt {
                typing_error_utils::add_typing_error(ty_err, env)
            }
            wrapped_ty
        }
    }
}

/// The first `make_return_type` of the OCaml (the second one, which calls this
/// one and then `force_return_kind`, shadows it).
fn make_return_type_(
    ety_env: &ExpandEnv,
    this_class: Option<&cls::T>,
    supportdyn: bool,
    env: &mut Env,
    // Position of return type hint, or function name, if absent
    hint_pos: Pos,
    // Explicit type from source code
    explicit: Option<DeclTy>,
    // A type to use if the explicit type isn't present.
    // e.g. implicit void (for constructors), or contextual type (for lambdas)
    default: Option<Ty>,
) -> Ty {
    match explicit {
        None => {
            let ty = match default {
                None => make_fresh_return_type(env, hint_pos.clone()),
                Some(ty) => ty,
            };
            if supportdyn {
                t_utils::make_supportdyn(
                    reason::support_dynamic_type(crate::pos_or_decl::of_raw_pos(hint_pos)),
                    env,
                    ty,
                )
            } else {
                ty
            }
        }
        Some(ty) => {
            let wrap_awaitable = |p: PosOrDecl, ty: Ty| {
                make_type::awaitable(reason::ret_fun_kind_from_decl((p, FunKind::FAsync)), ty)
            };
            let localize = |wrap: bool, env: &mut Env, dty: DeclTy| -> Ty {
                // `Typechecker_options.everything_sdt`
                if env.genv.tcopt.po.everything_sdt {
                    let pos = PosOrDecl::from(dty.pos().clone());
                    let dty = match dty.node_ref() {
                        decl::Ty_::Tfun(_) => t_utils::make_supportdyn_decl_type(
                            pos.clone(),
                            dty.reason().clone(),
                            dty.clone(),
                        ),
                        _ => dty,
                    };
                    let (ty_err_opt, ty) = typing_phase::localize(ety_env, env, &dty);
                    if let Some(ty_err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(ty_err, env)
                    }
                    // If type doesn't already support dynamic then wrap it if supportdyn=true
                    let ty = if supportdyn {
                        t_utils::make_supportdyn(reason::support_dynamic_type(pos.clone()), env, ty)
                    } else {
                        ty
                    };
                    // If <<__NoAutoLikes>> is specified, then add a like- to enforced returns
                    // so that we can return an expression of like-type.
                    // If <<__NoAutoLikes>> is not specified, then add a like- for the same reason,
                    // but add a like type even for non-enforced returns because these we pessimise anyway.
                    // Never pessimise void.
                    let add_like_reason = match typing_enforceability::get_enforcement(
                        Some(true),
                        this_class,
                        env,
                        &dty,
                    ) {
                        Enforcement::Enforced => Some(reason::enforced_type(pos)),
                        Enforcement::Unenforced => {
                            if env::get_no_auto_likes(env) {
                                None
                            } else {
                                Some(reason::witness_from_decl(pos))
                            }
                        }
                    };
                    let ty = match get_node(&ty) {
                        Ty_::Tprim(ast_defs::Tprim::Tvoid) if !wrap => ty,
                        _ => match add_like_reason {
                            Some(reason) => t_utils::make_like(Some(reason), env, ty),
                            None => ty,
                        },
                    };
                    let ty = if wrap {
                        wrap_awaitable(get_pos(&ty), ty)
                    } else {
                        ty
                    };
                    ty
                } else {
                    let et_enforced =
                        typing_enforceability::get_enforcement(Some(true), this_class, env, &dty);
                    let et_enforced = match et_enforced {
                        Enforcement::Unenforced => {
                            if !env::get_no_auto_likes(env) {
                                typing_log::log_pessimise_return(None, env, &hint_pos, None)
                            }
                            // Return type is not fully enforced according to the naive check
                            // in Typing_enforceability. Let's now ask for what type it is actually
                            // enforced at. If this is a subtype of the Hack type, then we can
                            // treat the return type as fully enforced.
                            // Example: return type is declared to be (~E & arraykey)
                            // for enum E : int as int
                            // get_enforced_type (~E & arraykey) is int
                            // Now since int <:D (~E & arraykey) it suffices to treat
                            // the return type as fully enforced.
                            let enforced_type = typing_partial_enforcement::get_enforced_type(
                                env,
                                decl_entry::to_option(env::get_self_class(env)).as_ref(),
                                &dty,
                            );
                            let is_sub_type = typing_phase::is_sub_type_decl(
                                Some(true),
                                env,
                                &enforced_type,
                                &dty,
                            );
                            if is_sub_type {
                                Enforcement::Enforced
                            } else {
                                Enforcement::Unenforced
                            }
                        }
                        Enforcement::Enforced => Enforcement::Enforced,
                    };
                    let (ty_err_opt, ty) = typing_phase::localize(ety_env, env, &dty);
                    if let Some(ty_err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(ty_err, env)
                    }
                    // If type doesn't already support dynamic then wrap it if supportdyn=true
                    let ty = if supportdyn {
                        t_utils::make_supportdyn(reason::support_dynamic_type(get_pos(&ty)), env, ty)
                    } else {
                        ty
                    };
                    // If return type t is enforced we permit values of type ~t to be returned
                    let ty = t_utils::make_like_if_enforced(env, et_enforced, ty);
                    let ty = if wrap {
                        wrap_awaitable(get_pos(&ty), ty)
                    } else {
                        ty
                    };
                    ty
                }
            };
            match (env::get_fn_kind(env), ty.node_ref()) {
                (FunKind::FAsync, decl::Ty_::Tapply(id_and_tyl))
                    if id_and_tyl.1.len() == 1
                        && id_and_tyl.0.id_ref().as_str() == sn::classes::AWAITABLE =>
                {
                    localize(true, env, id_and_tyl.1[0].clone())
                }
                (FunKind::FAsync, decl::Ty_::Tlike(ty_like)) => match ty_like.node_ref() {
                    decl::Ty_::Tapply(id_and_tyl)
                        if id_and_tyl.1.len() == 1
                            && id_and_tyl.0.id_ref().as_str() == sn::classes::AWAITABLE =>
                    {
                        let r_like = ty.reason().clone();
                        let ty = DeclTy::new(r_like, decl::Ty_::Tlike(id_and_tyl.1[0].clone()));
                        localize(true, env, ty)
                    }
                    _ => localize(false, env, ty.clone()),
                },
                _ => localize(false, env, ty.clone()),
            }
        }
    }
}

pub fn make_return_type(
    ety_env: &ExpandEnv,
    this_class: Option<&cls::T>,
    is_toplevel: Option<bool>,
    // Wrap return type with supportdyn, used when checking SDT functions and methods
    supportdyn: bool,
    env: &mut Env,
    // Position of return type hint, or function name, if absent
    hint_pos: Pos,
    // Explicit type from source code
    explicit: Option<DeclTy>,
    // A type to use if the explicit type isn't present.
    // e.g. implicit void (for constructors), or contextual type (for lambdas)
    default: Option<Ty>,
) -> Ty {
    let is_toplevel = is_toplevel.unwrap_or(true);
    let ty = make_return_type_(
        ety_env,
        this_class,
        supportdyn,
        env,
        hint_pos.clone(),
        explicit,
        default,
    );
    force_return_kind(is_toplevel, env, hint_pos, ty)
}

pub fn implicit_return(
    env: &mut Env,
    pos: Pos,
    expected: Ty,
    actual: Ty,
    hint_pos: Option<PosOrDecl>,
    is_async: bool,
) {
    let reason = Ureason::URreturn;
    let error = typing_error::primary::T::Wellformedness(
        typing_error::primary::wellformedness::T::Missing_return {
            pos: pos.clone(),
            hint_pos,
            is_async,
        },
    );
    let ty_err_opt = typing_ops::sub_type(None, 
        pos,
        reason,
        env,
        actual,
        expected,
        typing_error::callback::of_primary_error(error),
    );

    if let Some(ty_err) = &ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
}

pub fn check_inout_return(ret_pos: Pos, env: &mut Env) {
    // `Local_id.Map.elements` is `Wrapped_map.elements`, `fold (fun k v acc ->
    // (k, v) :: acc) m []`: in decreasing order of the identifiers.
    let params = env::get_params(env);
    // `List.fold ~init:(env, [])`: the errors are prepended.
    let mut ty_errs = vec![];
    for (id, (_ty, param_pos, out_ty_opt)) in params.iter().rev() {
        match out_ty_opt {
            Some(out_ty) => {
                // Whenever the function exits normally, we require that each local
                // corresponding to an inout parameter be compatible with the original
                // type for the parameter (under subtyping rules).
                let local = env::get_local(env, id);
                let ety = env::expand_type(env, local.ty.clone());
                let pos = if !pos::equal(&pos::none, &local.pos) {
                    local.pos.clone()
                } else if !pos::equal(&pos::none, &ret_pos) {
                    ret_pos.clone()
                } else {
                    param_pos.clone()
                };
                let param_ty = mk((reason::inout_param(get_pos(out_ty)), get_node(out_ty).clone()));
                let ty_err_opt = typing_coercion::coerce_type(
                    None,
                    None,
                    None,
                    pos,
                    Ureason::URassignInout,
                    env,
                    ety,
                    param_ty,
                    Enforcement::Unenforced,
                    typing_error::callback::inout_return_type_mismatch(),
                );
                if let Some(e) = ty_err_opt {
                    ty_errs.push(e)
                }
            }
            None => {}
        }
    }
    ty_errs.reverse();
    if let Some(ty_err) = &typing_error::multiple_opt(ty_errs) {
        typing_error_utils::add_typing_error(ty_err, env)
    }
}

fn remove_like_for_return(env: &mut Env, ty: Ty) -> Ty {
    let ty_opt = typing_dynamic_utils::try_strip_dynamic(None, None, env, &ty);
    match ty_opt {
        Some(ty) => ty,
        None => match get_node(&ty) {
            Ty_::Tclass((p, class_name), exact, tyl)
                if tyl.len() == 1 && class_name == sn::classes::AWAITABLE =>
            {
                // `ty` is the type argument here (it shadows the type in the
                // OCaml): its reason is the reason of the result.
                let ty = &tyl[0];
                let ty_res = remove_like_for_return(env, ty.clone());
                mk((
                    get_reason(ty).clone(),
                    Ty_::Tclass((p.clone(), class_name.clone()), exact.clone(), vec![ty_res]),
                ))
            }
            _ => ty,
        },
    }
}

pub fn fun_implicit_return(env: &mut Env, pos: Pos, ret: Ty, fun_kind: FunKind) {
    // Under sound dynamic, void <D: dynamic, which means that it void <D: ~T for any T.
    // However, for ergonomic reasons, it should not be the case that a function
    // erroring about a missing `return` statement would stop if the return type were
    // pessimised. This preserves the behavior that a function explicitly returning dynamic
    // can have an implicit return, while requiring an explicit return for like types.
    let ret = remove_like_for_return(env, ret);
    let ret_pos = Some(get_pos(&ret));

    match fun_kind {
        FunKind::FGenerator | FunKind::FAsyncGenerator => {}
        FunKind::FSync => {
            // A function without a terminal block has an implicit return; the
            // "void" type
            check_inout_return(pos::none, env);
            let r = reason::no_return(pos.clone());
            let rty = make_type::void(r);
            implicit_return(env, pos, ret, rty, ret_pos, false)
        }
        FunKind::FAsync => {
            // An async function without a terminal block has an implicit return;
            // the Awaitable<void> type
            let r = reason::no_return_async(pos.clone());
            let rty = make_type::awaitable(r.clone(), make_type::void(r));
            implicit_return(env, pos, ret, rty, ret_pos, true)
        }
    }
}
