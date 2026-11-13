// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_enforceability.ml`. See `hh/PORTING.md`.
//!
//! - `module FoldedContextAccess : Decl_enforceability.ContextAccess` is the
//!   type [`FoldedContextAccess`], which implements the traits
//!   `decl_enforceability::Provider` and `decl_enforceability::ContextAccess`;
//!   `module E = Decl_enforceability.Enforce (FoldedContextAccess)` is
//!   `decl_enforceability::enforce::get_enforcement::<FoldedContextAccess>`.
//! - `compute_enforced_ty` is defined twice: the last line of the OCaml
//!   module shadows the first definition (which has `?explicitly_untrusted`)
//!   with one without it. The first is in the private module [`shadowed`],
//!   which the functions defined between the two call, as in OCaml.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::typechecker_options::TypecheckerOptions;
use ty::decl;
use ty::decl::Ty_;

use crate::ctx::R;
use crate::decl_enforceability;
use crate::decl_enforceability::ClassOrTypedefResult;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::typing_defs_core::DeclFunParam;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::ParamMode;
use crate::typing_defs_flags;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;

/// `module FoldedContextAccess`
struct FoldedContextAccess;

impl decl_enforceability::Provider for FoldedContextAccess {
    type T = Env;

    type ClassT = cls::T;

    fn get_tcopt(env: &Env) -> &Arc<TypecheckerOptions> {
        &env.genv.tcopt
    }

    fn get_class_or_typedef(ctx: &Env, name: &str) -> Option<ClassOrTypedefResult<cls::T>> {
        // Preserve the decl access behaviour of the enforceability code that used to be here.
        let _ = env::get_class(ctx, name);
        decl_entry::to_option(env::get_class_or_typedef(ctx, name))
    }

    fn get_class(ctx: &Env, x: &str) -> Option<cls::T> {
        decl_entry::to_option(env::get_class(ctx, x))
    }
}

impl decl_enforceability::ContextAccess for FoldedContextAccess {
    fn get_typeconst_type(env: &Env, cls: &cls::T, name: &str) -> Option<DeclTy> {
        match env::get_typeconst(env, cls, name) {
            None => None,
            Some(tc) => match tc.kind {
                decl::Typeconst::TCAbstract(abstract_) => abstract_.as_constraint,
                decl::Typeconst::TCConcrete(concrete) => Some(concrete.ty),
            },
        }
    }

    fn get_tparams(cls: &cls::T) -> Vec<DeclTparam> {
        cls::tparams(cls)
    }

    fn is_final(cls: &cls::T) -> bool {
        cls::final_(cls)
    }

    fn get_name(cls: &cls::T) -> String {
        cls::name(cls)
    }

    fn get_enum_type(cls: &cls::T) -> Option<decl::EnumType<R>> {
        cls::enum_type(cls)
    }
}

/// When `top_enforced` is true, erased container type arguments are treated
/// as enforced if they are top types for their positions.
pub fn get_enforcement(
    top_enforced: Option<bool>,
    this_class: Option<&cls::T>,
    env: &Env,
    ty: &DeclTy,
) -> Enforcement {
    let top_enforced = top_enforced.unwrap_or(false);
    match decl_enforceability::enforce::get_enforcement::<FoldedContextAccess>(
        top_enforced,
        false, // return_from_async
        this_class,
        env,
        ty,
    ) {
        decl_enforceability::Enf::Unenforced(..) => Enforcement::Unenforced,
        decl_enforceability::Enf::Enforced(_) => Enforcement::Enforced,
    }
}

pub fn is_enforceable(this_class: Option<&cls::T>, env: &Env, ty: &DeclTy) -> bool {
    match get_enforcement(Some(true), this_class, env, ty) {
        Enforcement::Enforced => true,
        Enforcement::Unenforced => false,
    }
}

fn get_enforced(
    this_class: Option<&cls::T>,
    env: &Env,
    explicitly_untrusted: bool,
    ty: &DeclTy,
) -> Enforcement {
    if explicitly_untrusted {
        Enforcement::Unenforced
    } else {
        get_enforcement(Some(true), this_class, env, ty)
    }
}

/// The first definition of `compute_enforced_ty`, which the last line of the
/// OCaml module shadows.
mod shadowed {
    use super::*;

    pub(super) fn compute_enforced_ty(
        this_class: Option<&cls::T>,
        env: &Env,
        explicitly_untrusted: Option<bool>,
        ty: DeclTy,
    ) -> (Enforcement, DeclTy) {
        let explicitly_untrusted = explicitly_untrusted.unwrap_or(false);
        let et_enforced = get_enforced(this_class, env, explicitly_untrusted, &ty);
        (et_enforced, ty)
    }
}

pub fn compute_enforced_and_pessimize_ty(
    this_class: Option<&cls::T>,
    env: &Env,
    explicitly_untrusted: Option<bool>,
    ty: DeclTy,
) -> (Enforcement, DeclTy) {
    let explicitly_untrusted = explicitly_untrusted.unwrap_or(false);
    shadowed::compute_enforced_ty(this_class, env, Some(explicitly_untrusted), ty)
}

fn handle_awaitable_return(
    this_class: Option<&cls::T>,
    env: &Env,
    ft_fun_kind: ast_defs::FunKind,
    ft_ret: DeclTy,
) -> DeclTy {
    match (ft_fun_kind, ft_ret.node_ref()) {
        (ast_defs::FunKind::FAsync, Ty_::Tapply(id_and_args))
            if id_and_args.1.len() == 1
                && id_and_args.0.id_ref().as_str() == sn::classes::AWAITABLE =>
        {
            ft_ret
        }
        _ => compute_enforced_and_pessimize_ty(this_class, env, None, ft_ret).1,
    }
}

pub fn compute_enforced_and_pessimize_fun_type(
    this_class: Option<&cls::T>,
    env: &Env,
    ft: DeclFunType,
) -> DeclFunType {
    // Not in the OCaml: the result is `ft` itself (each enforcement computed
    // below is dropped, and each type is given back as it is). What computing
    // the enforcements does besides is look declarations up, for the
    // dependency edges these lookups record: when they record none, nothing
    // is left to do.
    if !env::deps::records_dependency_edges(env) {
        return ft;
    }
    // `get_ft_fun_kind ft`
    let ft_fun_kind = typing_defs_flags::fun::fun_kind(ft.flags);
    let ft_ret = handle_awaitable_return(this_class, env, ft_fun_kind, ft.ret.clone());
    let ft_params: Vec<DeclFunParam> = ft
        .params
        .iter()
        .map(|fp| {
            let fp_type = fp.ty.clone();
            // `get_fp_mode fp`
            let fp_mode = if typing_defs_flags::fun_param::inout(fp.flags) {
                ParamMode::FPinout
            } else {
                ParamMode::FPnormal
            };
            let (_, fp_type) = match fp_mode {
                ParamMode::FPinout => {
                    compute_enforced_and_pessimize_ty(this_class, env, None, fp_type)
                }
                ParamMode::FPnormal => {
                    shadowed::compute_enforced_ty(this_class, env, None, fp_type)
                }
            };
            DeclFunParam {
                ty: fp_type,
                ..fp.clone()
            }
        })
        .collect();
    DeclFunType {
        params: ft_params.into_boxed_slice(),
        ret: ft_ret,
        ..ft
    }
}

/// `let compute_enforced_ty = compute_enforced_ty ?explicitly_untrusted:None`
pub fn compute_enforced_ty(
    this_class: Option<&cls::T>,
    env: &Env,
    ty: DeclTy,
) -> (Enforcement, DeclTy) {
    shadowed::compute_enforced_ty(this_class, env, None, ty)
}
