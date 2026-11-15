// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_nast.ml`. See `hh/PORTING.md`.
//!
//! Module used to convert an AST into a type signature. Historically, all
//! decls were produced this way. Now, they are produced only by the direct decl
//! parser. Only lambda type signatures are produced from ASTs here.
//!
//! The decl types are those of `hackrs` (`ty::decl::Ty<R>`); `fun_elt` is
//! `crate::typing_defs::FunElt`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use pos::BPos;
use pos::Bytes;
use pos::Positioned;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason;

use crate::aast_utils;
use crate::ctx::R;
use crate::decl_env;
use crate::decl_fun_utils as fun_utils;
use crate::decl_hint;
use crate::naming_attributes;
use crate::pos_or_decl;
use crate::typing_defs::FunElt;
use crate::typing_defs::PackageRequirement;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_flags;

pub fn lambda_flags(f: &nast::Fun_) -> typing_defs_flags::fun::T {
    let return_disposable = fun_utils::has_return_disposable_attribute(&f.user_attributes.0);
    let ft_readonly_this = f.readonly_this.is_some();
    let ft_is_memoized = fun_utils::has_memoize_attribute(&f.user_attributes.0);
    let fe_support_dynamic_type = naming_attributes::mem(
        sn::user_attributes::SUPPORT_DYNAMIC_TYPE,
        &f.user_attributes.0,
    );
    let variadic = f
        .params
        .iter()
        .any(|param| aast_utils::is_param_variadic(param) && param.named.is_none());
    let named_variadic = f
        .params
        .iter()
        .any(|param| aast_utils::is_param_variadic(param) && param.named.is_some());
    typing_defs_flags::fun::make(
        f.fun_kind,
        return_disposable,
        f.readonly_ret.is_some(),
        ft_readonly_this,
        fe_support_dynamic_type,
        ft_is_memoized,
        variadic,
        named_variadic,
    )
}

// TODO(jakebailey): Can/should this be done with the direct decl parser?
pub fn lambda_decl_in_env(env: &decl_env::Env, f: &nast::Fun_) -> FunElt {
    let ft_tparams: Vec<DeclTparam> = f
        .tparams
        .iter()
        .map(
            |aast::HintTparam {
                 name: htp_name,
                 constraints: htp_constraints,
                 user_attributes: htp_user_attributes,
             }| {
                let tp_name = {
                    let ast_defs::Id(pos, name) = htp_name;
                    Positioned::new(
                        BPos::from(pos_or_decl::of_raw_pos(pos.clone())),
                        TypeName::new(name),
                    )
                };
                let tp_constraints: Vec<(ast_defs::ConstraintKind, DeclTy)> = htp_constraints
                    .iter()
                    .map(|(kind, hint)| (*kind, decl_hint::hint(env, hint)))
                    .collect();
                let tp_user_attributes: Vec<d::UserAttribute<BPos>> = htp_user_attributes
                    .iter()
                    .map(|ast_defs::Id(pos, id)| {
                        let ua_name = Positioned::new(
                            BPos::from(pos_or_decl::of_raw_pos(pos.clone())),
                            TypeName::new(id),
                        );
                        d::UserAttribute {
                            name: ua_name,
                            params: [].into(),
                            raw_val: None,
                        }
                    })
                    .collect();
                d::Tparam {
                    name: tp_name,
                    constraints: tp_constraints.into(),
                    user_attributes: tp_user_attributes.into(),
                    variance: ast_defs::Variance::Invariant,
                    reified: ast_defs::ReifyKind::Erased,
                }
            },
        )
        .collect();
    let ft_instantiated = ft_tparams.is_empty();
    let params = fun_utils::make_params(env, &f.params);
    let (_pos, capability) =
        decl_hint::aast_contexts_to_decl_capability(env, f.ctxs.as_ref(), &f.span);
    let ret_ty = fun_utils::ret_from_fun_kind(
        None,
        env,
        &f.span,
        f.fun_kind,
        // `hint_of_type_hint f.f_ret`
        f.ret.1.as_ref(),
    );
    let fe_deprecated = crate::naming_attributes_params::deprecated(
        "function",
        &(f.span.clone(), ";anonymous".to_string()),
        &f.user_attributes.0,
    );
    let fe_php_std_lib =
        naming_attributes::mem(sn::user_attributes::PHP_STD_LIB, &f.user_attributes.0);
    let fe_pos = BPos::from(decl_env::make_decl_pos(env, &f.span));
    let ft_flags = lambda_flags(f);
    let fe_type = DeclTy::new(
        R::witness_from_decl(fe_pos.clone()),
        d::Ty_::Tfun(Box::new(d::FunType {
            tparams: ft_tparams.into(),
            where_constraints: [].into(),
            params: params.into(),
            implicit_params: d::FunImplicitParams { capability },
            ret: ret_ty,
            flags: ft_flags,
            // TODO: handle const attribute
            instantiated: ft_instantiated,
        })),
    );
    d::FunElt {
        pos: fe_pos,
        module: None,
        package: None,
        internal: false,
        ty: fe_type,
        deprecated: fe_deprecated.map(Bytes::new),
        php_std_lib: fe_php_std_lib,
        support_dynamic_type: typing_defs_flags::fun::support_dynamic_type(ft_flags),
        no_auto_dynamic: false,
        no_auto_likes: false,
        gated_by_feature_flag: None,
        // Lambdas cannot be require package
        package_requirement: PackageRequirement::RPNormal,
    }
}
