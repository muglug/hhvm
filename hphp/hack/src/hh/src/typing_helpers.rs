// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_helpers.ml`. See `hh/PORTING.md`.
//!
//! # Decl errors
//!
//! `add_decl_errors` takes the decl errors of a folded class
//! (`Cls.decl_errors`, its only caller in OCaml is `Typing_class`), which are
//! `ty::decl_error::DeclError<BPos>` in the Rust decl folding (`hackrs`):
//! `crate::folded_class::decl_errors` returns those, not the
//! `Decl_defs.decl_error` of `oxidized`. They carry the same information
//! (`Cyclic_class_def`'s stack is a list of names there, a set here).

use std::cell::RefCell;
use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::BPos;
use ty::decl_error::DeclError;

use crate::decl_fun_utils;
use crate::diagnostics;
use crate::tast;
use crate::typing_defs;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
/// `module Inter = Typing_intersection`
use crate::typing_intersection as inter;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_reason::T as Reason;
/// `module Union = Typing_union`
use crate::typing_union as union;
/// `module Utils = Typing_utils`
use crate::typing_utils as utils;

/// `module ExpectedTy`
///
/// Some mutually recursive inference functions in typing.ml pass around an
/// ~expected argument that enables bidirectional type checking. This module
/// abstracts away that type so that it can be extended and modified without
/// having to touch every consumer.
pub mod expected_ty {
    use oxidized::pos::Pos;

    use crate::typing_defs_core::Ty;
    use crate::typing_reason::Ureason;

    /// `type t = private { ... }`: read the fields, build one with [`make`].
    #[derive(Clone, Debug)]
    pub struct T {
        pub pos: Pos,
        pub reason: Ureason,
        pub ty: Ty,
        pub is_dynamic_aware: bool,
        pub ignore_readonly: bool,
    }

    pub fn make(
        is_dynamic_aware: Option<bool>,
        ignore_readonly: Option<bool>,
        pos: Pos,
        reason: Ureason,
        ty: Ty,
    ) -> T {
        let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
        let ignore_readonly = ignore_readonly.unwrap_or(false);
        T {
            pos,
            reason,
            ty,
            is_dynamic_aware,
            ignore_readonly,
        }
    }
}

fn decl_error_to_typing_error(decl_error: &DeclError<BPos>) -> typing_error::T {
    let primary = match decl_error {
        DeclError::WrongExtendKind {
            pos,
            kind,
            name,
            parent_pos,
            parent_kind,
            parent_name,
        } => typing_error::primary::T::WrongExtendKind {
            pos: Pos::from(pos.clone()),
            kind: *kind,
            name: name.as_str().to_string(),
            parent_pos: Pos::from(parent_pos.clone()),
            parent_kind: *parent_kind,
            parent_name: parent_name.as_str().to_string(),
        },
        DeclError::WrongUseKind {
            pos,
            name,
            parent_pos,
            parent_name,
        } => typing_error::primary::T::WrongUseKind {
            pos: Pos::from(pos.clone()),
            name: name.as_str().to_string(),
            parent_pos: Pos::from(parent_pos.clone()),
            parent_name: parent_name.as_str().to_string(),
        },
        DeclError::CyclicClassDef(pos, stack) => typing_error::primary::T::CyclicClassDef {
            pos: Pos::from(pos.clone()),
            stack: stack.iter().map(|name| name.as_str().to_string()).collect(),
        },
    };
    typing_error::primary(primary)
}

fn add_decl_error(decl_error: &DeclError<BPos>, env: &Env) {
    typing_error_utils::add_typing_error(&decl_error_to_typing_error(decl_error), env)
}

pub fn add_decl_errors(env: &Env, decl_errors: &[DeclError<BPos>]) {
    for decl_error in decl_errors {
        add_decl_error(decl_error, env)
    }
}

// ---------------------------------------------------------------------------
// Handling function/method arguments
// ---------------------------------------------------------------------------

fn param_has_attribute<Ex, En>(param: &aast::FunParam<Ex, En>, attr: &str) -> bool {
    param
        .user_attributes
        .0
        .iter()
        .any(|aast::UserAttribute { name: ua_name, .. }| attr == ua_name.1)
}

pub fn has_accept_disposable_attribute<Ex, En>(param: &aast::FunParam<Ex, En>) -> bool {
    param_has_attribute(param, sn::user_attributes::ACCEPT_DISPOSABLE)
}

/// The OCaml gives `do_` the environment it is given (with a fresh
/// `big_envs` when there is a timeout) and returns what `do_` returns: the
/// environment `do_` ends with is not passed back, so this takes `&Env` and
/// runs `do_` on a copy.
///
/// `fun_name` is a `Pos.t * string`, which is `Ast_defs.id` (both callers pass
/// the name of the definition): `ast_defs::Id` here.
pub fn with_timeout<B>(
    env: &Env,
    fun_name: &ast_defs::Id,
    do_: impl FnOnce(&mut Env) -> B,
) -> Option<B> {
    // `Typechecker_options.timeout`
    let timeout = env::get_tcopt(env).tco_timeout;
    if timeout == 0 {
        Some(do_(&mut env.clone()))
    } else {
        let big_envs = Rc::new(RefCell::new(vec![]));
        let mut env = env.clone();
        env.big_envs = big_envs;
        crate::timeout::with_timeout(
            timeout,
            || {
                // List.iter !big_envs (fun (p, env) ->
                //     Typing_log.log_key "WARN: environment is too big.";
                //     Typing_log.hh_show_env p env);
                let ast_defs::Id(pos, fn_name) = fun_name;
                diagnostics::typechecker_timeout(pos.clone(), fn_name, timeout);
                None
            },
            move || Some(do_(&mut env)),
        )
    }
}

/// If the localized types of the return type is a tyvar we force it to be covariant.
/// The same goes for parameter types, but this time we force them to be contravariant
pub fn set_tyvars_variance_in_callable(env: &mut Env, return_ty: &Ty, param_tys: &[Option<Ty>]) {
    let old_env = env.clone();
    // `let set_variance = Env.set_tyvar_variance ~for_all_vars:true`
    env::set_tyvar_variance(env, None, Some(true), return_ty);
    for opt_ty in param_tys {
        match opt_ty {
            None => {}
            Some(ty) => env::set_tyvar_variance(env, Some(true), Some(true), ty),
        }
    }
    env::log_env_change("set_tyvars_variance_in_callable", None, &old_env, env)
}

pub fn reify_kind(k: aast::ReifyKind) -> aast::ReifyKind {
    match k {
        aast::ReifyKind::Erased => aast::ReifyKind::Erased,
        aast::ReifyKind::SoftReified => aast::ReifyKind::SoftReified,
        aast::ReifyKind::Reified => aast::ReifyKind::Reified,
    }
}

/// Convert a function signature hint (method or toplevel function) into a bunch
/// of decl_tys.
pub fn hint_fun_decl(
    params: &[nast::FunParam],
    ret: &nast::TypeHint,
    env: &Env,
) -> (Option<DeclTy>, Vec<Option<DeclTy>>) {
    // `hint_of_type_hint`
    let ret_decl_ty = decl_fun_utils::hint_to_type_opt(&env.decl_env, ret.1.as_ref());
    let params_decl_ty = params
        .iter()
        .map(|h| decl_fun_utils::hint_to_type_opt(&env.decl_env, h.type_hint.1.as_ref()))
        .collect();
    (ret_decl_ty, params_decl_ty)
}

// T231531028 to improve coverage
pub fn is_enforced(hint_ty: &Ty) -> bool {
    match get_node(hint_ty) {
        Ty_::Toption(ty) => typing_defs::is_nonnull(ty) || is_enforced(ty),
        Ty_::Tclass(_, _, tyl) if tyl.is_empty() => true,
        Ty_::Tprim(_) => true,
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            fields: expected_fdm,
            ..
        })) => expected_fdm.values().all(|ty| is_enforced(&ty.ty)),
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => false,
        _ => false,
    }
}

/// [refine_and_simplify_intersection env p reason ivar_pos ty hint_ty]
/// intersects [ty] and [hint_ty], possibly making [hint_ty] support dynamic
/// first if [ty] also supports dynamic.
/// Then if the result has some like types in which prevent simplification
/// of the intersection, it'll distribute any '&' at the top of the type tree
/// in order to have a union at hand.
/// This is because the resulting type will likely end up on the LHS of a subtyping
/// call down the line, and unions on the LHS behave better than intersections,
/// which result in incomplete typing.
///
/// Parameters:
/// * [reason]          The reason for the result types and other intermediate types.
/// * [is_class]        Whether [hint_ty] is a class
/// * [ty_is_supportdyn] Assume that ty is supportdyn when intersecting with the hint type
pub fn refine_and_simplify_intersection(
    env: &mut Env,
    is_class: bool,
    ty_is_supportdyn: Option<bool>,
    reason: Reason,
    ty: Ty,
    hint_ty: Ty,
) -> Ty {
    let ty_is_supportdyn = ty_is_supportdyn.unwrap_or(false);
    let intersect = |is_class: bool, env: &mut Env, r: Reason, ty: Ty, hint_ty: Ty| -> Ty {
        let hint_ty = if is_class && (ty_is_supportdyn || utils::is_supportdyn(env, &ty)) {
            utils::make_supportdyn(reason.clone(), env, hint_ty)
        } else {
            hint_ty
        };
        inter::intersect(env, r, ty, hint_ty)
    };
    let like_type_simplify = |env: &mut Env, ty: Ty, hint_ty: Ty, is_class: bool| -> Ty {
        // This basically distributes the intersection over the union.
        // Let's call X the type to refine (`ty` here) and H the hint type.
        // We want to intersect ~X with either H if H is enforced, or
        // ~H if H is not enforced.
        //
        // If H is enforced: ~X & H is an intersection so may not behave well
        // if passed as LHS of subtyping, so we distribute the intersection:
        //
        //   ~X & H = (~ & H) | (X & H)
        //
        // (With the hope that (X & H) simplifies)
        //
        //
        // If X is not enforced:
        //
        //   ~X & ~H = ~(X & H)
        let intersection_ty = intersect(is_class, env, reason.clone(), ty, hint_ty.clone());
        if is_enforced(&hint_ty) {
            let dyn_ty = inter::intersect(
                env,
                reason.clone(),
                make_type::dynamic(reason.clone()),
                hint_ty,
            );
            union::union(env, None, None, dyn_ty, intersection_ty)
        } else {
            make_type::locl_like(reason.clone(), intersection_ty)
        }
    };
    // If we are refining a variable of type dynamic, and can fully enforce the result,
    // just drop the dynamic, or convert it into a supportdyn if the type isn't already
    if typing_defs::is_dynamic(&ty) && is_enforced(&hint_ty) {
        if utils::is_supportdyn(env, &hint_ty) {
            hint_ty
        } else {
            utils::make_supportdyn(reason.clone(), env, hint_ty)
        }
    } else {
        match typing_dynamic_utils::try_strip_dynamic(None, None, env, &ty) {
            Some(ty) => like_type_simplify(env, ty, hint_ty, is_class),
            None => intersect(is_class, env, reason.clone(), ty, hint_ty),
        }
    }
}

pub fn make_simplify_typed_expr(env: &mut Env, p: Pos, ty: Ty, te: tast::Expr_) -> tast::Expr {
    let ty = typing_dynamic_utils::recompose_like_type(env, ty);
    tast::make_typed_expr(p, ty, te)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::ShapeFieldType;
    use crate::typing_defs_core::t_shape_map::TShapeField;
    use crate::typing_defs_core::TshapeFieldName;
    use crate::typing_defs_core::PosByteString;
    use crate::typing_defs_core::mk;
    use crate::typing_reason as reason;

    fn r() -> Reason {
        reason::none()
    }

    #[test]
    fn enforced_types() {
        let int = make_type::int(r());
        let nonnull = make_type::nonnull(r());
        let generic = make_type::generic(r(), "T".to_string());
        assert!(is_enforced(&int));
        assert!(is_enforced(&make_type::nullable(r(), int.clone())));
        // `?nonnull`: the option of a nonnull
        assert!(is_enforced(&mk((r(), Ty_::Toption(nonnull)))));
        assert!(is_enforced(&make_type::class_type(r(), "\\C".to_string(), vec![])));
        assert!(!is_enforced(&make_type::class_type(
            r(),
            "\\C".to_string(),
            vec![int.clone()]
        )));
        assert!(!is_enforced(&make_type::nullable(r(), generic.clone())));
        assert!(!is_enforced(&generic));
        assert!(!is_enforced(&make_type::dynamic(r())));
        let field = |name: &str, ty: Ty| {
            (
                TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
                    Pos::NONE,
                    name.into(),
                ))),
                ShapeFieldType {
                    optional: false,
                    ty,
                },
            )
        };
        let shape = |fields: Vec<(TShapeField, ShapeFieldType)>| {
            make_type::closed_shape(r(), fields.into_iter().collect())
        };
        assert!(is_enforced(&shape(vec![])));
        assert!(is_enforced(&shape(vec![
            field("a", int.clone()),
            field("b", make_type::prim_type(r(), Tprim::Tbool)),
        ])));
        assert!(!is_enforced(&shape(vec![
            field("a", int),
            field("b", generic)
        ])));
    }

    #[test]
    fn reify_kind_is_the_identity() {
        for k in [
            aast::ReifyKind::Erased,
            aast::ReifyKind::SoftReified,
            aast::ReifyKind::Reified,
        ] {
            assert_eq!(reify_kind(k), k);
        }
    }
}
