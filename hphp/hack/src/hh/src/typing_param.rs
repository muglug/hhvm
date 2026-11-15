// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_param.ml`. See `hh/PORTING.md`.
//!
//! The parameter hints are declared types (`ty::decl::Ty`): the
//! `Typing_make_type` functions and the reasons that the OCaml applies to them
//! here are the declared-phase ones (`decl_reason_*`, `decl_make_type_*`).

use oxidized::ast_defs::ParamKind;
use oxidized::nast;
use oxidized::pos_or_decl::PosOrDecl;
use pos::BPos;
use ty::decl;
use ty::reason::Reason as _;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::aast_utils;
use crate::ctx::R;
use crate::decl_entry;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::mk;
use crate::typing_disposable;
use crate::typing_enforceability;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_helpers::has_accept_disposable_attribute;
use crate::typing_log;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_utils;
use crate::utils;

/// `Typing_reason.pessimised_inout`, as a reason of the declared phase.
fn decl_reason_pessimised_inout(p: BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::PessimisedInout(p)))
}

/// `Typing_reason.support_dynamic_type_assume`, as a reason of the declared
/// phase.
fn decl_reason_support_dynamic_type_assume(p: BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::SupportDynamicTypeAssume(p)))
}

/// `Typing_make_type.dynamic`, on a declared type.
fn decl_make_type_dynamic(r: R) -> DeclTy {
    DeclTy::new(r, decl::Ty_::Tdynamic)
}

/// `Typing_make_type.intersection`, on declared types.
fn decl_make_type_intersection(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    match tyl.len() {
        // `mixed r`
        0 => DeclTy::new(r.clone(), decl::Ty_::Toption(DeclTy::new(r, decl::Ty_::Tnonnull))),
        1 => tyl.pop().unwrap(),
        _ => DeclTy::new(r, decl::Ty_::Tintersection(tyl.into_boxed_slice())),
    }
}

fn enforce_param_not_disposable(
    env: &Env,
    param: &nast::FunParam,
    ty: &Ty,
) -> Option<typing_error::primary::T> {
    if has_accept_disposable_attribute(param) {
        None
    } else {
        typing_disposable::is_disposable_type(env, ty).map(|class_name| {
            typing_error::primary::T::InvalidDisposableHint {
                pos: param.pos.clone(),
                class_name: utils::strip_ns(&class_name).to_string(),
            }
        })
    }
}

fn check_param_has_hint(env: &Env, param: &nast::FunParam) {
    // `hint_of_type_hint param.param_type_hint`
    let prim_err_opt = if param.type_hint.1.is_none() {
        Some(if aast_utils::is_param_variadic(param) {
            typing_error::primary::T::ExpectingTypeHintVariadic(param.pos.clone())
        } else {
            typing_error::primary::T::ExpectingTypeHint(param.pos.clone())
        })
    } else {
        None
    };
    if let Some(err) = prim_err_opt {
        typing_error_utils::add_typing_error(&typing_error::primary(err), env)
    }
}

/// This function is used to determine the type of an argument.
/// When we want to type-check the body of a function, we need to
/// introduce the type of the arguments of the function in the environment
/// Let's take an example, we want to check the code of foo:
///
/// ```text
/// function foo(int $x): int {
///   // CALL TO make_param_type on (int $x)
///   // Now we know that the type of $x is int
///
///   return $x; // in the environment $x is an int, the code is correct
/// }
/// ```
///
/// When we localize, we want to resolve to "static" or "$this" depending on
/// the context. Even though we are passing in CIstatic, resolve_with_class_id
/// is smart enough to know what to do. Why do this? Consider the following
///
/// ```text
/// abstract class C {
///   abstract const type T;
///
///   private this::T $val;
///
///   final public function __construct(this::T $x) {
///     $this->val = $x;
///   }
///
///   public static function create(this::T $x): this {
///     return new static($x);
///   }
/// }
///
/// class D extends C { const type T = int; }
/// ```
///
/// In __construct() we want to be able to assign $x to $this->val. The type of
/// $this->val will expand to '$this::T', so we need $x to also be '$this::T'.
/// We can do this soundly because when we construct a new class such as,
/// 'new D(0)' we can determine the late static bound type (D) and resolve
/// 'this::T' to 'D::T' which is int.
///
/// A similar line of reasoning is applied for the static method create.
fn make_param_local_ty(
    dynamic_mode: bool,
    no_auto_likes: bool,
    env: &mut Env,
    decl_hint: Option<DeclTy>,
    param: &nast::FunParam,
) -> Option<Ty> {
    // Don't check (again) for existence of hint in dynamic mode
    if !dynamic_mode {
        check_param_has_hint(env, param)
    }
    match decl_hint {
        None => None,
        Some(hint) => {
            let (ty_err_opt, ty) = {
                let (et_enforced, ty) = {
                    let this_class = decl_entry::to_option(env::get_self_class(env));
                    typing_enforceability::compute_enforced_and_pessimize_ty(
                        this_class.as_ref(),
                        env,
                        Some(aast_utils::is_param_variadic(param)),
                        hint,
                    )
                };
                match et_enforced {
                    Enforcement::Unenforced => typing_log::log_pessimise_param(
                        env,
                        param.visibility.is_some(),
                        &param.pos,
                        &param.callconv,
                        &param.name,
                    ),
                    Enforcement::Enforced => {}
                }
                // If a non-inout parameter hint has the form ~t, where t is enforced,
                // then we know that the parameter has type t after enforcement.
                let ty = match (ty.node_ref(), et_enforced, &param.callconv) {
                    (decl::Ty_::Tlike(ty), Enforcement::Enforced, ParamKind::Pnormal) => {
                        ty.clone()
                    }
                    _ => ty,
                };
                // `Typechecker_options.everything_sdt`
                let ty = if env.genv.tcopt.po.everything_sdt {
                    let ty = {
                        // For implicit pessimisation, wrap supportdyn around parameters with function types.
                        match ty.node_ref() {
                            decl::Ty_::Tfun(_) => typing_utils::make_supportdyn_decl_type(
                                PosOrDecl::from(ty.pos().clone()),
                                ty.reason().clone(),
                                ty.clone(),
                            ),
                            _ => ty,
                        }
                    };
                    // For implicit pessimisation, without <<__NoAutoLikes>>, wrap like around non-enforced inout parameters
                    match (et_enforced, &param.callconv) {
                        (Enforcement::Unenforced, ParamKind::Pinout(_)) if !no_auto_likes => {
                            make_type::like(decl_reason_pessimised_inout(ty.pos().clone()), ty)
                        }
                        _ => ty,
                    }
                } else {
                    ty
                };
                phase::localize_no_subst(env, false, &ty)
            };
            if let Some(ty_err) = &ty_err_opt {
                typing_error_utils::add_typing_error(ty_err, env)
            }
            let ty = if aast_utils::is_param_variadic(param) {
                // when checking the body of a function with a variadic
                // argument, "f(C ...$args)", $args is a vec<C>
                let r = reason::var_param(param.pos.clone());
                let arr_values = mk((r.clone(), get_node(&ty).clone()));
                make_type::vec(r, arr_values)
            } else {
                ty
            };
            // We do not permit hints to implement IDisposable or IAsyncDisposable
            let prim_err_opt = enforce_param_not_disposable(env, param, &ty);
            if let Some(err) = prim_err_opt {
                typing_error_utils::add_typing_error(&typing_error::primary(err), env)
            }
            Some(ty)
        }
    }
}

pub fn make_param_local_tys(
    dynamic_mode: bool,
    no_auto_likes: bool,
    env: &mut Env,
    decl_tys: &[Option<DeclTy>],
    params: &[nast::FunParam],
) -> Vec<Option<Ty>> {
    // `List.zip_exn params decl_tys`
    if params.len() != decl_tys.len() {
        panic!(
            "length mismatch in zip_exn: {} <> {}",
            params.len(),
            decl_tys.len()
        )
    }
    params
        .iter()
        .zip(decl_tys.iter())
        .map(|(param, hint)| {
            let ty = {
                let reason = decl_reason_support_dynamic_type_assume(BPos::from(
                    // `Pos_or_decl.of_raw_pos param.param_pos`
                    param.pos.clone(),
                ));
                if dynamic_mode {
                    let dyn_ty = decl_make_type_dynamic(reason.clone());
                    match hint {
                        Some(ty)
                            if typing_enforceability::is_enforceable(
                                decl_entry::to_option(env::get_self_class(env)).as_ref(),
                                env,
                                ty,
                            ) =>
                        {
                            Some(decl_make_type_intersection(reason, vec![ty.clone(), dyn_ty]))
                        }
                        _ => Some(dyn_ty),
                    }
                } else {
                    hint.clone()
                }
            };
            make_param_local_ty(dynamic_mode, no_auto_likes, env, ty, param)
        })
        .collect()
}
