// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_fun_utils.ml`. See `hh/PORTING.md`.
//!
//! The decl types are those of `hackrs` (`ty::decl::Ty<R>`), as in
//! `crate::decl_hint`: the position of a decl type is a `BPos`, made from the
//! `Pos_or_decl.t` that `Decl_env.make_decl_pos` returns.
//!
//! The attribute lists are `Nast.user_attribute list`: slices of
//! `nast::UserAttribute` (the `.0` of a `nast::UserAttributes`). The
//! `Nast.xhp_attr_hint option` arguments are `Option<&aast::Hint>`
//! (`Aast.hint_of_type_hint h` is `h.1.as_ref()`).

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::BPos;
use pos::Positioned;
use pos::Symbol;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::aast_utils;
use crate::ctx::R;
use crate::decl_env;
use crate::decl_hint;
use crate::naming_attributes;
use crate::typing_defs;
use crate::typing_defs_core::DeclFunParam;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_error;

// -- Reasons of the declared phase (`Typing_reason` on decl positions) -------

/// `Reason.var_param_from_decl p`
fn reason_var_param_from_decl(p: BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::VarParamFromDecl(p)))
}

/// `Reason.tuple_from_splat p`
fn reason_tuple_from_splat(p: BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::TupleFromSplat(p)))
}

/// `Reason.ret_fun_kind_from_decl (p, k)`
fn reason_ret_fun_kind_from_decl((p, k): (BPos, ast_defs::FunKind)) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::RetFunKindFromDecl(p, k)))
}

/// `Typing_defs.with_reason` on a decl type: the same node with another
/// reason.
fn with_reason(ty: DeclTy, r: R) -> DeclTy {
    DeclTy::new(r, ty.node_ref().clone())
}

// ---------------------------------------------------------------------------

fn has_accept_disposable_attribute(user_attributes: &[nast::UserAttribute]) -> bool {
    naming_attributes::mem(sn::user_attributes::ACCEPT_DISPOSABLE, user_attributes)
}

fn has_ignore_readonly_error_attribute(user_attributes: &[nast::UserAttribute]) -> bool {
    naming_attributes::mem(sn::user_attributes::IGNORE_READONLY_ERROR, user_attributes)
}

pub fn has_return_disposable_attribute(user_attributes: &[nast::UserAttribute]) -> bool {
    naming_attributes::mem(sn::user_attributes::RETURN_DISPOSABLE, user_attributes)
}

pub fn has_memoize_attribute(user_attributes: &[nast::UserAttribute]) -> bool {
    naming_attributes::mem(sn::user_attributes::MEMOIZE, user_attributes)
        || naming_attributes::mem(sn::user_attributes::MEMOIZE_LSB, user_attributes)
}

pub fn hint_to_type_opt(env: &decl_env::Env, hint: Option<&aast::Hint>) -> Option<DeclTy> {
    hint.map(|h| decl_hint::hint(env, h))
}

fn hint_to_type(default: DeclTy, env: &decl_env::Env, hint: Option<&aast::Hint>) -> DeclTy {
    hint_to_type_opt(env, hint).unwrap_or(default)
}

fn make_wildcard_ty(pos: &BPos) -> DeclTy {
    DeclTy::new(R::witness_from_decl(pos.clone()), d::Ty_::Twildcard)
}

pub fn make_param_ty(env: &decl_env::Env, param: &nast::FunParam) -> DeclFunParam {
    let param_pos = BPos::from(decl_env::make_decl_pos(env, &param.pos));
    let ty = hint_to_type(
        make_wildcard_ty(&param_pos),
        env,
        // `hint_of_type_hint param.param_type_hint`
        param.type_hint.1.as_ref(),
    );
    let ty = if aast_utils::is_param_variadic(param) {
        // When checking a call f($a, $b) to a function f(C ...$args),
        // both $a and $b must be of type C
        with_reason(ty, reason_var_param_from_decl(param_pos.clone()))
    } else if aast_utils::is_param_splat(param) {
        with_reason(ty, reason_tuple_from_splat(param_pos.clone()))
    } else {
        ty
    };
    let mode = typing_defs::get_param_mode(&param.callconv);
    d::FunParam {
        pos: param_pos,
        // The parser uses ... for variadic parameters that lack a name
        name: if param.name == "..." {
            None
        } else {
            Some(Symbol::new(&param.name))
        },
        ty,
        flags: typing_defs::flags::make_fp_flags(
            mode,
            has_accept_disposable_attribute(&param.user_attributes.0),
            aast_utils::get_param_default(param).is_some(),
            param.readonly.is_some(),
            has_ignore_readonly_error_attribute(&param.user_attributes.0),
            param.splat.is_some(),
            param.named.is_some(),
        ),
        def_value: None,
    }
}

pub fn ret_from_fun_kind(
    is_constructor: Option<bool>,
    env: &decl_env::Env,
    pos: &Pos,
    kind: ast_defs::FunKind,
    hint: Option<&aast::Hint>,
) -> DeclTy {
    let is_constructor = is_constructor.unwrap_or(false);
    let pos = BPos::from(decl_env::make_decl_pos(env, pos));
    let ret_ty = || {
        if is_constructor {
            DeclTy::new(
                R::witness_from_decl(pos.clone()),
                d::Ty_::Tprim(aast::Tprim::Tvoid),
            )
        } else {
            hint_to_type(make_wildcard_ty(&pos), env, hint)
        }
    };
    match hint {
        None => match kind {
            ast_defs::FunKind::FGenerator => {
                let r = reason_ret_fun_kind_from_decl((pos.clone(), kind));
                DeclTy::new(
                    r,
                    d::Ty_::Tapply(Box::new((
                        Positioned::new(pos.clone(), TypeName::new(sn::classes::GENERATOR)),
                        [ret_ty(), ret_ty(), ret_ty()].into(),
                    ))),
                )
            }
            ast_defs::FunKind::FAsyncGenerator => {
                let r = reason_ret_fun_kind_from_decl((pos.clone(), kind));
                DeclTy::new(
                    r,
                    d::Ty_::Tapply(Box::new((
                        Positioned::new(pos.clone(), TypeName::new(sn::classes::ASYNC_GENERATOR)),
                        [ret_ty(), ret_ty(), ret_ty()].into(),
                    ))),
                )
            }
            ast_defs::FunKind::FAsync => {
                let r = reason_ret_fun_kind_from_decl((pos.clone(), kind));
                DeclTy::new(
                    r,
                    d::Ty_::Tapply(Box::new((
                        Positioned::new(pos.clone(), TypeName::new(sn::classes::AWAITABLE)),
                        [ret_ty()].into(),
                    ))),
                )
            }
            ast_defs::FunKind::FSync => ret_ty(),
        },
        Some(_) => ret_ty(),
    }
}

pub fn type_param(env: &decl_env::Env, t: &nast::Tparam) -> DeclTparam {
    decl_hint::aast_tparam_to_decl_tparam(env, t)
}

pub fn where_constraint<A>(
    env: &decl_env::Env,
    (ty1, ck, ty2): (&aast::Hint, A, &aast::Hint),
) -> (DeclTy, A, DeclTy) {
    // OCaml evaluates the components of the tuple from right to left (and
    // `Decl_hint.hint` can report an error)
    let ty2 = decl_hint::hint(env, ty2);
    let ty1 = decl_hint::hint(env, ty1);
    (ty1, ck, ty2)
}

// Functions building the types for the parameters of a function
// It's not completely trivial because of optional arguments

/// Check for `optional` keyword where it isn't allowed. Example: `function foo(optional int $x): void {}` (should be a default arg instead)
fn check_params_for_bad_optional_keyword(
    from_abstract_method: bool,
    paraml: &[nast::FunParam],
) -> Vec<typing_error::T> {
    paraml
        .iter()
        .filter_map(|param| {
            let is_optional_not_default = aast_utils::is_param_optional(param)
                && aast_utils::get_param_default(param).is_none();
            if is_optional_not_default {
                if !from_abstract_method {
                    Some(typing_error::primary(
                        typing_error::primary::T::Optional_parameter_not_abstract(
                            param.pos.clone(),
                        ),
                    ))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect()
}

/// Required positional parameters must not come before optional positional parameters.
/// For example: function foo(int $x, ?int $y = null, int $z)
/// produces an error for parameter $z
fn check_params_for_required_after_optional(
    from_abstract_method: bool,
    paraml: &[nast::FunParam],
) -> Option<typing_error::T> {
    enum T<'a> {
        Init,
        SeenOptionalOrDefault,
        FoundRequiredAfterOptionalOrDefault(&'a nast::FunParam),
    }
    let positional_params = paraml.iter().filter(|param| param.named.is_none());
    let mut res = T::Init;
    for param in positional_params {
        let is_optional_or_default =
            aast_utils::get_param_default(param).is_some() || aast_utils::is_param_optional(param);
        res = match res {
            T::Init if is_optional_or_default => T::SeenOptionalOrDefault,
            T::Init => T::Init,
            T::SeenOptionalOrDefault
                if is_optional_or_default
                    || aast_utils::is_param_variadic(param)
                    || aast_utils::is_param_splat(param) =>
            {
                T::SeenOptionalOrDefault
            }
            T::SeenOptionalOrDefault => T::FoundRequiredAfterOptionalOrDefault(param),
            state @ T::FoundRequiredAfterOptionalOrDefault(_) => state,
        };
    }
    match res {
        T::Init | T::SeenOptionalOrDefault => None,
        T::FoundRequiredAfterOptionalOrDefault(param) if from_abstract_method => {
            Some(typing_error::primary(
                typing_error::primary::T::Previous_default_or_optional(param.pos.clone()),
            ))
        }
        T::FoundRequiredAfterOptionalOrDefault(param) => Some(typing_error::primary(
            typing_error::primary::T::Previous_default(param.pos.clone()),
        )),
    }
}

pub fn check_params(from_abstract_method: bool, paraml: &[nast::FunParam]) -> Vec<typing_error::T> {
    let err = check_params_for_required_after_optional(from_abstract_method, paraml);
    let mut res: Vec<typing_error::T> = err.into_iter().collect();
    res.extend(check_params_for_bad_optional_keyword(
        from_abstract_method,
        paraml,
    ));
    res
}

pub fn make_params(env: &decl_env::Env, paraml: &[nast::FunParam]) -> Vec<DeclFunParam> {
    paraml
        .iter()
        .map(|param| make_param_ty(env, param))
        .collect()
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;
    use oxidized::typing_defs_flags::FunParamFlags;

    use super::*;
    use crate::ctx::Ctx;

    fn param(name: &str, info: nast::FunParamInfo) -> nast::FunParam {
        aast::FunParam {
            annotation: (),
            type_hint: aast::TypeHint((), None),
            pos: Pos::NONE,
            name: name.to_string(),
            info,
            readonly: None,
            splat: None,
            callconv: ast_defs::ParamKind::Pnormal,
            named: None,
            user_attributes: aast::UserAttributes(vec![]),
            visibility: None,
        }
    }

    fn with_default() -> nast::FunParamInfo {
        aast::FunParamInfo::ParamOptional(Some(aast::Expr((), Pos::NONE, aast::Expr_::Null)))
    }

    fn primary(err: &typing_error::T) -> &typing_error::primary::T {
        match err {
            typing_error::T::Primary(p) => p,
            err => panic!("not a primary error: {:?}", err),
        }
    }

    fn env() -> decl_env::Env {
        let ctx = Arc::new(Ctx::new(Path::new("/"), TypecheckerOptions::default()).unwrap());
        decl_env::Env {
            mode: oxidized::file_info::Mode::Mstrict,
            droot: None,
            droot_member: None,
            ctx,
        }
    }

    #[test]
    fn required_after_default_is_reported_once() {
        let params = vec![
            param("$x", with_default()),
            param("$y", aast::FunParamInfo::ParamRequired),
            param("$z", aast::FunParamInfo::ParamRequired),
        ];
        let errs = check_params(false, &params);
        assert_eq!(errs.len(), 1);
        assert!(matches!(
            primary(&errs[0]),
            typing_error::primary::T::Previous_default(_)
        ));
        let errs = check_params(true, &params);
        assert_eq!(errs.len(), 1);
        assert!(matches!(
            primary(&errs[0]),
            typing_error::primary::T::Previous_default_or_optional(_)
        ));
    }

    #[test]
    fn variadic_or_named_after_default_is_allowed() {
        let mut named = param("$n", aast::FunParamInfo::ParamRequired);
        named.named = Some(ast_defs::ParamNamed::ParamNamed);
        let params = vec![
            param("$x", with_default()),
            named,
            param("$rest", aast::FunParamInfo::ParamVariadic),
        ];
        assert!(check_params(false, &params).is_empty());
    }

    #[test]
    fn optional_keyword_without_default_outside_abstract_methods() {
        let params = vec![param("$x", aast::FunParamInfo::ParamOptional(None))];
        let errs = check_params(false, &params);
        assert_eq!(errs.len(), 1);
        assert!(matches!(
            primary(&errs[0]),
            typing_error::primary::T::Optional_parameter_not_abstract(_)
        ));
        assert!(check_params(true, &params).is_empty());
    }

    #[test]
    fn make_params_names_flags_and_reasons() {
        let env = env();
        let mut inout = param("$io", aast::FunParamInfo::ParamRequired);
        inout.callconv = ast_defs::ParamKind::Pinout(Pos::NONE);
        let params = vec![
            param("$x", with_default()),
            inout,
            param("...", aast::FunParamInfo::ParamVariadic),
        ];
        let fps = make_params(&env, &params);
        assert_eq!(fps.len(), 3);
        assert_eq!(fps[0].name.map(|s| s.as_str()), Some("$x"));
        assert!(fps[0].flags.contains(FunParamFlags::IS_OPTIONAL));
        assert!(matches!(fps[0].ty.node_ref(), d::Ty_::Twildcard));
        assert!(fps[1].flags.contains(FunParamFlags::INOUT));
        assert!(!fps[1].flags.contains(FunParamFlags::IS_OPTIONAL));
        assert_eq!(fps[2].name, None);
        assert!(matches!(
            fps[2].ty.reason().as_impl(),
            ReasonImpl::FromWitnessDecl(WitnessDecl::VarParamFromDecl(_))
        ));
    }

    #[test]
    fn ret_from_fun_kind_without_hint() {
        let env = env();
        let ty = ret_from_fun_kind(None, &env, &Pos::NONE, ast_defs::FunKind::FAsync, None);
        match ty.node_ref() {
            d::Ty_::Tapply(id_and_tys) => {
                assert_eq!(id_and_tys.0.id_ref().as_str(), sn::classes::AWAITABLE);
                assert_eq!(id_and_tys.1.len(), 1);
                assert!(matches!(id_and_tys.1[0].node_ref(), d::Ty_::Twildcard));
            }
            ty_ => panic!("not an Awaitable: {:?}", ty_),
        }
        let ty = ret_from_fun_kind(
            Some(true),
            &env,
            &Pos::NONE,
            ast_defs::FunKind::FGenerator,
            None,
        );
        match ty.node_ref() {
            d::Ty_::Tapply(id_and_tys) => {
                assert_eq!(id_and_tys.0.id_ref().as_str(), sn::classes::GENERATOR);
                assert_eq!(id_and_tys.1.len(), 3);
                assert!(
                    id_and_tys
                        .1
                        .iter()
                        .all(|ty| matches!(ty.node_ref(), d::Ty_::Tprim(aast::Tprim::Tvoid)))
                );
            }
            ty_ => panic!("not a Generator: {:?}", ty_),
        }
        let ty = ret_from_fun_kind(None, &env, &Pos::NONE, ast_defs::FunKind::FSync, None);
        assert!(matches!(ty.node_ref(), d::Ty_::Twildcard));
    }
}
