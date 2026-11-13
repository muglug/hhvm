// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 9488-9774): module `Method_caller`.
//! See `hh/PORTING.md`.
//!
//! The signature of the OCaml module exports [`synth_function_type`] and
//! [`synth_function_ref_type`]; the other functions are `pub(crate)` (see
//! `typing/mod.rs`).
//!
//! The `(class_name, method_name)` pair is taken as the tuple the
//! `Expr_::MethodCaller` box holds.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
// module Cls = Folded_class
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::tast;
use crate::typing::prelude::*;
// open Typing_defs (with Typing_defs_core)
use crate::typing_defs::*;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error_utils;
// module Reason = Typing_reason
use crate::typing_reason as reason;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;

/// `Typing_error_utils.add_typing_error ~env (Typing_error.primary err)`
fn add_primary(err: primary::T, env: &Env) {
    typing_error_utils::add_typing_error(&typing_error::primary(err), env)
}

pub(crate) fn validate_polymorphic_instance_method(
    folded_class: &cls::T,
    class_elt: &ClassElt,
    class_name: &aast::ClassName,
    method_name: &aast::Pstring,
    fun_ty: &DeclFunType,
    env: &Env,
) {
    // `{ ce_pos = (lazy class_pos); ce_deprecated; ce_visibility; _ }`
    let class_pos: PosOrDecl = PosOrDecl::clone(&class_elt.ce_pos);
    let ClassElt {
        ce_deprecated,
        ce_visibility,
        ..
    } = class_elt;
    let (use_pos, _method_id) = method_name;
    let classish_kind = cls::kind(folded_class);
    // Meth caller on trait
    if ast_defs::is_c_trait(classish_kind) {
        let ast_defs::Id(pos, trait_name) = class_name;
        add_primary(
            primary::T::Meth_caller_trait {
                pos: pos.clone(),
                trait_name: trait_name.clone(),
            },
            env,
        )
    }

    // Visibility
    for err in tvis::check_obj_access(
        true,
        ast_defs::is_c_interface(classish_kind),
        use_pos.clone(),
        class_pos.clone(),
        get_ce_tests_bypass_visibility(class_elt),
        env,
        ce_visibility,
    ) {
        typing_error_utils::add_typing_error(&err, env)
    }

    if env::get_tcopt(env).tco_meth_caller_only_public_visibility {
        if let Some(err) = tvis::check_meth_caller_access(
            use_pos.clone(),
            class_pos.clone(),
            get_ce_tests_bypass_visibility(class_elt),
            env,
            ce_visibility,
        ) {
            typing_error_utils::add_typing_error(&err, env)
        }
    }

    // Deprecation
    if let Some(err) = tvis::check_deprecated(
        use_pos.clone(),
        class_pos.clone(),
        env,
        ce_deprecated.clone(),
    ) {
        typing_error_utils::add_typing_error(&err, env)
    }

    // Explicit type params
    let is_explicit = |ua: &ty::decl::UserAttribute<pos::BPos>| {
        ua.name.id_ref().as_str() == sn::user_attributes::EXPLICIT
    };
    for tp in fun_ty.tparams.iter() {
        // `{ tp_user_attributes; tp_name = (decl_pos, param_name); _ }`
        if tp.user_attributes.iter().any(is_explicit) {
            add_primary(
                primary::T::Require_generic_explicit {
                    decl_pos: tp.name.pos().clone().to_oxidized(),
                    param_name: tp.name.id_ref().as_str().to_string(),
                    pos: use_pos.clone(),
                },
                env,
            )
        }
    }
    // A method whose signature would reference [this] two or more times cannot
    // be soundly abstracted into a function pointer. Instance methods carry an
    // implicit [this] receiver, so a single explicit [this] parameter is enough.
    // In a final class [this] is nominally coincident with the class itself so
    // there is nothing to abstract and the pointer is sound
    if !cls::final_(folded_class) {
        let positions: Vec<PosOrDecl> =
            crate::typing_extract_method::explicit_this_param_positions(Some(true), env, fun_ty);
        for decl_pos in positions {
            add_primary(
                primary::T::This_as_function_pointer_param {
                    pos: use_pos.clone(),
                    decl_pos,
                },
                env,
            )
        }
    }
}

pub(crate) fn unbound_method(
    class_name: &aast::ClassName,
    method_name: &aast::Pstring,
    folded_class: &cls::T,
) -> typing_error::T {
    if method_name.1 == sn::members::__CONSTRUCT {
        typing_error::primary(primary::T::Construct_not_instance_method(
            method_name.0.clone(),
        ))
    } else {
        let hint = {
            let folded_class = folded_class.clone();
            let method_name = method_name.1.clone();
            Lazy::new(move || {
                let method_suggestion = env::suggest_member(true, &folded_class, &method_name);
                let static_suggestion =
                    env::suggest_static_member(true, &folded_class, &method_name);
                match (method_suggestion, static_suggestion) {
                    // Prefer suggesting a different method, unless there's a
                    // static method whose name matches exactly.
                    (Some(_), Some((def_pos, v))) if v == method_name => {
                        Some((primary::InstanceOrStatic::static_, def_pos, v))
                    }
                    (Some((def_pos, v)), _) => {
                        Some((primary::InstanceOrStatic::instance, def_pos, v))
                    }
                    (None, Some((def_pos, v))) => {
                        Some((primary::InstanceOrStatic::static_, def_pos, v))
                    }
                    (None, None) => None,
                }
            })
        };
        let reason = {
            let rendered_class_name = crate::utils::strip_ns(&class_name.1).to_string();
            let class_name_pos = class_name.0.clone();
            Lazy::new(move || {
                reason::to_string(
                    &format!(
                        "This is why I think it is an object of type {}",
                        rendered_class_name
                    ),
                    &reason::witness(class_name_pos),
                )
                .into_iter()
                .map(|(p, s)| Message(p, s.into()))
                .collect::<Vec<Message<PosOrDecl>>>()
            })
        };
        typing_error::primary(primary::T::Member_not_found {
            pos: method_name.0.clone(),
            kind: primary::MethodOrProperty::method_,
            class_name: class_name.1.clone(),
            class_pos: cls::pos(folded_class),
            member_name: method_name.1.clone(),
            hint,
            reason,
        })
    }
}

/// Parameterised on whether we should build a function type wrapped by FunctionRef or not.
/// We can't do the wrapping outside because the wrapping only happens on some of the exit
/// points, and it needs to get put into the TAST as well.
pub(crate) fn synth_function_type_help(
    build_function_ref_type: bool,
    pos: &Pos,
    (class_name, method_name): &(aast::ClassName, aast::Pstring),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    match env::get_class(env, &class_name.1) {
        decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
            let expr_ =
                aast::Expr_::MethodCaller(Box::new((class_name.clone(), method_name.clone())));
            let expr: nast::Expr = aast::Expr((), pos.clone(), expr_);
            unbound_name(env, class_name, &expr)
        }
        decl_entry::T::Found(folded_class) => {
            match env::get_method(env, &folded_class, &method_name.1) {
                None => {
                    {
                        let err = unbound_method(class_name, method_name, &folded_class);
                        typing_error_utils::add_typing_error(&err, env)
                    }
                    let ty = env::fresh_type_error(env, method_name.0.clone());
                    let expr = aast::Expr_::MethodCaller(Box::new((
                        class_name.clone(),
                        method_name.clone(),
                    )));
                    make_result(env, pos.clone(), expr, ty)
                }
                Some(class_elt) => {
                    // `{ ce_type = (lazy member_decl_ty); ce_pos = (lazy class_pos); _ }`
                    let member_decl_ty: &DeclTy = &class_elt.ce_type;
                    let class_pos: PosOrDecl = PosOrDecl::clone(&class_elt.ce_pos);
                    match member_decl_ty.node_ref() {
                        ty::decl::Ty_::Tfun(fun_ty) => {
                            let reason = member_decl_ty.reason();
                            validate_polymorphic_instance_method(
                                &folded_class,
                                &class_elt,
                                class_name,
                                method_name,
                                fun_ty,
                                env,
                            );

                            // Apply pressimization
                            let fun_ty = crate::typing_enforceability::compute_enforced_and_pessimize_fun_type(
                                Some(&folded_class),
                                env,
                                (**fun_ty).clone(),
                            );
                            // Extract the static method by incorporating any class-level generics
                            // and transforming abstract type constants into generics and subsituting
                            // 'concrete' type constants
                            let fun_ty = {
                                let class_name: PosId = {
                                    let ast_defs::Id(pos, name) = class_name;
                                    (crate::pos_or_decl::of_raw_pos(pos.clone()), name.clone())
                                };
                                let fun_ty: DeclFunType =
                                    crate::typing_extract_method::extract_instance_method(
                                        fun_ty,
                                        &class_name,
                                        &folded_class,
                                        env,
                                    );
                                fun_ty
                            };

                            // Localize
                            let fun_ty = {
                                let (err_opt, fun_ty) =
                                    crate::typing_phase::localize_fun_type_no_subst(
                                        &fun_ty, env, false,
                                    );
                                if let Some(err) = &err_opt {
                                    typing_error_utils::add_typing_error(err, env)
                                }
                                fun_ty
                            };

                            // Discharge any [where] constraints on the function type parameters
                            let fun_ty = {
                                let (ft_tparams, err_opt) =
                                    crate::typing_subtype::apply_where_constraints(
                                        &method_name.0,
                                        &class_pos,
                                        &fun_ty.tparams,
                                        &fun_ty.where_constraints,
                                        env,
                                    );
                                if let Some(err) = &err_opt {
                                    typing_error_utils::add_typing_error(err, env)
                                }
                                // If this is not a polymorphic function type, mark as instantiated
                                let ft_instantiated = fun_ty.tparams.is_empty();
                                FunType {
                                    tparams: ft_tparams,
                                    where_constraints: vec![],
                                    instantiated: ft_instantiated,
                                    ..fun_ty
                                }
                            };

                            // Wrap with supportdyn under SDT
                            let ty = {
                                let reason = reason::localize(&reason.clone().to_oxidized());
                                crate::typing_dynamic::maybe_wrap_with_supportdyn(
                                    get_ce_support_dynamic_type(&class_elt),
                                    reason,
                                    fun_ty,
                                )
                            };

                            let ty = tutils::map_supportdyn(env, ty, |_env: &mut Env, ty: Ty| {
                                match get_node(&ty) {
                                    Ty_::Tfun(ft) => {
                                        let ft = set_ft_is_function_pointer(FunType::clone(&ft), true);
                                        mk((get_reason(&ty).clone(), Ty_::Tfun(std::rc::Rc::new(ft))))
                                    }
                                    _ => ty,
                                }
                            });
                            let ty = set_capture_only_readonly(env, ty);
                            let expr = aast::Expr_::MethodCaller(Box::new((
                                class_name.clone(),
                                method_name.clone(),
                            )));
                            let ty = if build_function_ref_type {
                                make_function_ref(false, pos, ty)
                            } else {
                                ty
                            };
                            make_result(env, pos.clone(), expr, ty)
                        }
                        _ => panic!("Expected a function type"),
                    }
                }
            }
        }
    }
}

/// Build a stand-along function type that corresponds to the given method.
pub fn synth_function_type(
    pos: &Pos,
    class_name_method_name: &(aast::ClassName, aast::Pstring),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    synth_function_type_help(false, pos, class_name_method_name, env)
}

/// Build a stand-along function type that corresponds to the given method, and
/// wrap it in FunctionRef.
pub fn synth_function_ref_type(
    pos: &Pos,
    class_name_method_name: &(aast::ClassName, aast::Pstring),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    synth_function_type_help(true, pos, class_name_method_name, env)
}
