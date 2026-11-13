// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `disjoint_types.ml`. See `hh/PORTING.md`.
//!
//! Check for the __NonDisjoint attribute on type parameters of functions and methods.
//! All type parameters with this attribute should be infered to types which are not disjoint.

#![allow(non_upper_case_globals)]

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::pos::Pos;

use crate::decl_entry;
use crate::error_codes;
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::DeclTparam;
use crate::typing_defs::DeclTy;
use crate::typing_defs::DeclTy_;
use crate::typing_defs::Ty;
use crate::typing_defs::attributes;
use crate::typing_defs::empty_expand_env;
use crate::typing_dynamic_utils;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning_utils;
use crate::utils;

pub const warning_kind: typing_warning::Kind<
    typing_warning::non_disjoint_check::T,
    typing_warning::Migrated,
> = typing_warning::Kind::Non_disjoint_check;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&warning_kind)
}

pub fn add_warning(
    env: &tast_env::Env,
    p: &Pos,
    name: &str,
    ty1: &Ty,
    ty2: &Ty,
    dynamic: bool,
    as_lint: bool,
) {
    let as_lint = if as_lint { Some(None) } else { None };
    typing_warning_utils::add_for_migration(
        &tast_env::get_tcopt(env),
        as_lint,
        (
            p.clone(),
            warning_kind,
            typing_warning::non_disjoint_check::T {
                name: utils::strip_ns(name).to_string(),
                dynamic,
                ty1: tast_env::print_ty(env, ty1),
                ty2: tast_env::print_ty(env, ty2),
            },
        ),
    )
}

pub fn check_non_disjoint(
    is_dynamic_call: bool,
    as_lint: bool,
    env: &tast_env::Env,
    p: &Pos,
    name: &str,
    ty1: &Ty,
    ty2: &Ty,
) {
    match tast_env::is_disjoint(is_dynamic_call, env, ty1, ty2) {
        tast_env::IsDisjointResult::NonDisjoint => {}
        tast_env::IsDisjointResult::DisjointIgnoringDynamic(ty1, ty2) => {
            add_warning(env, p, name, &ty1, &ty2, true, as_lint)
        }
        tast_env::IsDisjointResult::Disjoint => {
            add_warning(env, p, name, ty1, ty2, is_dynamic_call, as_lint)
        }
    }
}

pub fn check_non_disjoint_tyl(
    is_dynamic_call: bool,
    as_lint: bool,
    env: &tast_env::Env,
    p: &Pos,
    name: &str,
    tyl: &[Ty],
) {
    match tyl {
        [] => {}
        [ty, tyl @ ..] => {
            for ty2 in tyl {
                check_non_disjoint(is_dynamic_call, as_lint, env, p, name, ty, ty2)
            }
            check_non_disjoint_tyl(is_dynamic_call, as_lint, env, p, name, tyl)
        }
    }
}

pub fn has_non_disjoint_attr(tp: &DeclTparam) -> bool {
    attributes::mem(sn::user_attributes::NON_DISJOINT, &tp.user_attributes)
}

pub fn is_in_overlapping(tp: &DeclTparam, overlapping: Option<&im::OrdSet<String>>) -> bool {
    match overlapping {
        None => false,
        Some(s) => s.contains(tp.name.id_ref().as_str()),
    }
}

pub fn check_function_type_args_non_disjoint(
    is_dynamic_call: bool,
    as_lint: bool,
    env: &tast_env::Env,
    p: &Pos,
    class_typarams: &[DeclTparam],
    name: &str,
    overlapping: Option<&im::OrdSet<String>>,
    class_tyargs: &[Ty],
    method_tyargs: &[Ty],
    fun_ty: &DeclTy,
) {
    match fun_ty.node_ref() {
        DeclTy_::Tfun(ft) => {
            let method_typarams = &ft.tparams;
            if method_typarams.iter().any(has_non_disjoint_attr) || overlapping.is_some() {
                // `List.zip_with_remainder`: the pairs up to the shorter list.
                let method_pairs = method_typarams.iter().zip(method_tyargs.iter());
                let class_pairs = class_typarams.iter().zip(class_tyargs.iter());
                let tyl: Vec<Ty> = class_pairs
                    .chain(method_pairs)
                    .filter_map(|(tp, ty)| {
                        if has_non_disjoint_attr(tp) || is_in_overlapping(tp, overlapping) {
                            Some(ty.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                check_non_disjoint_tyl(is_dynamic_call, as_lint, env, p, name, &tyl)
            }
        }
        _ => {}
    }
}

pub fn get_origin_info(
    env: &tast_env::Env,
    class_id: &str,
    class_type: &cls::T,
    class_tyargs: &[Ty],
    origin: &str,
) -> Option<(Vec<DeclTparam>, Vec<Ty>)> {
    if origin == class_id {
        Some((cls::tparams(class_type), class_tyargs.to_vec()))
    } else {
        match decl_entry::to_option(tast_env::get_class(env, origin)) {
            None => None,
            Some(origin_class_type) => match cls::get_ancestor(class_type, origin) {
                Some(ty) => match ty.node_ref() {
                    DeclTy_::Tapply(tapply) => {
                        let (_, tyargs) = &**tapply;
                        let ety_env = crate::typing_defs::ExpandEnv {
                            substs: typing_utils::make_locl_subst_for_class_tparams(
                                class_type,
                                class_tyargs,
                            ),
                            ..empty_expand_env()
                        };
                        let origin_class_tyargs: Vec<Ty> = tyargs
                            .iter()
                            .map(|ty| tast_env::localize(&mut env.clone(), &ety_env, ty))
                            .collect();
                        Some((cls::tparams(&origin_class_type), origin_class_tyargs))
                    }
                    _ => None,
                },
                None => None,
            },
        }
    }
}

/// `List.map tal ~f:fst`
fn targ_types(tal: &[tast::Targ]) -> Vec<Ty> {
    tal.iter().map(|aast::Targ(ty, _)| ty.clone()).collect()
}

pub fn member_hook(
    is_dynamic_call: bool,
    as_lint: bool,
    env: &tast_env::Env,
    p: &Pos,
    class_id: &str,
    class_tyargs: &[Ty],
    method_name: &str,
    tal: &[tast::Targ],
) {
    match decl_entry::to_option(tast_env::get_class(env, class_id)) {
        None => {}
        Some(class_type) => match tast_env::get_method(env, &class_type, method_name) {
            None => {}
            Some(ce) => {
                // `{ ce_type = (lazy fun_ty); ... }`: forced by the pattern.
                let fun_ty = (*ce.ce_type).clone();
                match get_origin_info(env, class_id, &class_type, class_tyargs, &ce.ce_origin) {
                    None => {}
                    Some((origin_class_typarams, origin_class_tyargs)) => {
                        check_function_type_args_non_disjoint(
                            is_dynamic_call,
                            as_lint,
                            env,
                            p,
                            &origin_class_typarams,
                            method_name,
                            ce.ce_overlapping_tparams.as_ref(),
                            &origin_class_tyargs,
                            &targ_types(tal),
                            &fun_ty,
                        )
                    }
                }
            }
        },
    }
}

pub fn check_instance_method_call(
    env: &tast_env::Env,
    p: &Pos,
    as_lint: bool,
    function_type: &Ty,
    receiver_type: &Ty,
    method_name: &str,
    tal: &[tast::Targ],
) {
    let is_dynamic_call =
        typing_dynamic_utils::try_strip_dynamic(None, None, &mut env.clone(), function_type)
            .is_some();
    for ri in tast_env::get_receiver_ids(env, receiver_type.clone()) {
        match ri {
            tast_env::ReceiverIdentifier::RIclass(cid, tyargs) => member_hook(
                is_dynamic_call,
                as_lint,
                env,
                p,
                &cid,
                &tyargs,
                method_name,
                tal,
            ),
            _ => {}
        }
    }
}

pub fn check_static_method_call(
    env: &tast_env::Env,
    p: &Pos,
    as_lint: bool,
    class_result: decl_entry::T<cls::T>,
    method_name: &str,
    tal: &[tast::Targ],
) {
    match class_result {
        decl_entry::T::Found(cd) => {
            match tast_env::get_static_member(true, env, &cd, method_name) {
                None => {}
                Some(ce) => {
                    // `{ ce_type = (lazy fun_ty); ... }`: forced by the pattern.
                    let fun_ty = (*ce.ce_type).clone();
                    check_function_type_args_non_disjoint(
                        false,
                        as_lint,
                        env,
                        p,
                        &[],
                        method_name,
                        ce.ce_overlapping_tparams.as_ref(),
                        &[],
                        &targ_types(tal),
                        &fun_ty,
                    )
                }
            }
        }
        _ => {}
    }
}

/// The object `handler ~as_lint`.
struct DisjointTypes {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for DisjointTypes {
    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        let as_lint = self.as_lint;
        let aast::Expr(_, p, e) = e;
        let call = match e {
            aast::Expr_::Call(call) if !call.targs.is_empty() => call,
            _ => return,
        };
        let tal = &call.targs;
        match &call.func {
            // Function call
            aast::Expr(_, _, aast::Expr_::Id(id)) => {
                let name = &id.1;
                match tast_env::get_fun(env, name) {
                    decl_entry::T::Found(fe) => check_function_type_args_non_disjoint(
                        false,
                        as_lint,
                        env,
                        p,
                        &[],
                        name,
                        None,
                        &[],
                        &targ_types(tal),
                        &fe.ty,
                    ),
                    _ => {}
                }
            }
            // Method call
            aast::Expr(function_type, _, aast::Expr_::ObjGet(og))
                if matches!(&og.1.2, aast::Expr_::Id(_))
                    && matches!(og.3, aast::PropOrMethod::IsMethod) =>
            {
                let (aast::Expr(receiver_type, _, _), aast::Expr(_, _, member), _, _) = &**og;
                let method_name = match member {
                    aast::Expr_::Id(id) => &id.1,
                    _ => unreachable!(),
                };
                check_instance_method_call(
                    env,
                    p,
                    as_lint,
                    function_type,
                    receiver_type,
                    method_name,
                    tal,
                )
            }
            // Static method call
            aast::Expr(_, _, aast::Expr_::ClassConst(cc)) => {
                let (aast::ClassId(_, _, ci), (_, method_name)) = &**cc;
                let class_result = match ci {
                    aast::ClassId_::CI(cls) => tast_env::get_class(env, &cls.1),
                    aast::ClassId_::CIself | aast::ClassId_::CIstatic => {
                        tast_env::get_self_class(env)
                    }
                    aast::ClassId_::CIparent => tast_env::get_parent_class(env),
                    _ => decl_entry::T::DoesNotExist,
                };
                check_static_method_call(env, p, as_lint, class_result, method_name, tal)
            }
            _ => {}
        }
    }
}

/// Check for the __NonDisjoint attribute on type parameters of functions and methods.
/// All type parameters with this attribute should be infered to types which are not disjoint.
pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(DisjointTypes { as_lint })
}
