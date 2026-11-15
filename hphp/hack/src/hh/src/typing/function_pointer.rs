// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 9034-9486): module `Function_pointer`.
//! See `hh/PORTING.md`.
//!
//! The signature of the OCaml module exports [`synth`] and
//! [`synth_top_level`]; the other functions are `pub(crate)` (see
//! `typing/mod.rs`).
//!
//! - The `(fpid, targs, source)` triple of `FunctionPointer` is taken as the
//!   tuple the `Expr_::FunctionPointer` box holds.
//! - The function types of the declarations are `hackrs` types
//!   ([`DeclFunType`]); the localized ones are [`FunType`].
//! - A class name with the position of its declaration (`pos_id`) is
//!   [`PosId`].

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

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
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module TOG = Typing_object_get
use crate::typing_object_get as tog;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
// module Union = Typing_union
use crate::typing_union as union_;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;

/// `Typing_error_utils.add_typing_error ~env (Typing_error.primary err)`
fn add_primary(err: primary::T, env: &Env) {
    typing_error_utils::add_typing_error(&typing_error::primary(err), env)
}

pub(crate) fn set_function_pointer(env: &mut Env, ty: Ty) -> Ty {
    tutils::map_supportdyn(env, ty, |_env: &mut Env, ty: Ty| match get_node(&ty) {
        Ty_::Tfun(ft) => {
            let ft = set_ft_is_function_pointer(FunType::clone(&ft), true);
            mk((get_reason(&ty).clone(), Ty_::Tfun(std::rc::Rc::new(ft))))
        }
        _ => ty,
    })
}

// -- Static methods ------------------------------------------------------

/// Given the function type of a static method, synthesize a function type which
/// is abstracted from the class in which it appears. This requires:
/// - quantifying over all class-level generics
/// - quantifying over appearances of [this]
/// - quantifying over any abstract type constants
///
/// In the latter two cases we will need to substitute the generics for
/// their concrete counterparts before localizing the function type
pub(crate) fn synth_polymorphic_static_method_help(
    folded_class: &cls::T,
    class_name: &PosId,
    method_name: &aast::Pstring,
    fun_ty: DeclFunType,
    env: &mut Env,
) -> FunType {
    // Extract the static method by incorporating any class-level generics
    // and transforming abstract type constants into generics and subsituting
    // 'concrete' type constants
    let fun_ty: DeclFunType =
        crate::typing_extract_method::extract_static_method(fun_ty, class_name, folded_class, env);

    // 'Localize' the function type but don't generate fresh type variables in
    // place of type parameters; we have already eliminated occurrences of
    // [Tthis] and [Taccess _] so we don't need to provide any definition for
    // `this`
    let fun_ty = {
        let (err_opt, fun_ty) =
            crate::typing_phase::localize_fun_type_no_subst(&fun_ty, env, false);
        if let Some(err) = &err_opt {
            typing_error_utils::add_typing_error(err, env)
        }
        fun_ty
    };

    // Discharge any [where] constraints on the function type parameters
    let fun_ty = {
        let (ft_tparams, err_opt) = crate::typing_subtype::apply_where_constraints(
            &method_name.0,
            &class_name.0,
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

    fun_ty
}

/// `class_id` is the `Nast.class_id` the method is accessed through, and
/// `class_name` the name of the class that has it.
pub(crate) fn validate_polymorphic_static_method(
    folded_class: &cls::T,
    class_elt: &ClassElt,
    class_name: &str,
    class_id: &nast::ClassId,
    method_name: &aast::Pstring,
    fun_ty: &DeclFunType,
    env: &Env,
) {
    // `{ ce_pos = (lazy class_pos); ce_visibility; ce_deprecated; _ }`
    let class_pos: PosOrDecl = PosOrDecl::clone(&class_elt.ce_pos);
    let ClassElt {
        ce_visibility,
        ce_deprecated,
        ..
    } = class_elt;
    let aast::ClassId(_, _, class_id_) = class_id;
    let (use_pos, method_name) = method_name;
    if let Some(err) = typing_error::multiple_opt(tvis::check_class_access(
        true,
        use_pos.clone(),
        class_pos.clone(),
        get_ce_tests_bypass_visibility(class_elt),
        false,
        env,
        (ce_visibility, get_ce_lsb(class_elt)),
        class_id_,
        folded_class,
    )) {
        typing_error_utils::add_typing_error(&err, env)
    }
    if let Some(err) = tvis::check_deprecated(
        use_pos.clone(),
        class_pos.clone(),
        env,
        ce_deprecated.clone(),
    ) {
        typing_error_utils::add_typing_error(&err, env)
    }
    check_class_get(
        env,
        use_pos,
        &class_pos,
        class_name,
        method_name,
        class_elt,
        class_id,
        true,
        true,
    );
    let is_explicit = |ua: &ty::decl::UserAttribute<pos::BPos>| {
        ua.name.id_ref().as_str() == sn::user_attributes::EXPLICIT
    };
    for tp in fun_ty.tparams.iter() {
        // `{ tp_user_attributes; tp_name = (decl_pos, param_name); _ }`
        if tp.user_attributes.iter().any(is_explicit) {
            add_primary(
                primary::T::RequireGenericExplicit {
                    decl_pos: tp.name.pos().clone().to_oxidized(),
                    param_name: tp.name.id_ref().as_str().to_string(),
                    pos: use_pos.clone(),
                },
                env,
            )
        }
    }
    // A method whose signature would reference [this] two or more times cannot
    // be soundly abstracted into a function pointer. Static methods have no
    // implicit receiver, so this requires two or more explicit [this] params.
    // In a final class [this] is nominally coincident with the class itself so
    // there is nothing to abstract and the pointer is sound
    if !cls::final_(folded_class) {
        let positions: Vec<PosOrDecl> =
            crate::typing_extract_method::explicit_this_param_positions(None, None, env, fun_ty);
        for decl_pos in positions {
            add_primary(
                primary::T::ThisAsFunctionPointerParam {
                    pos: use_pos.clone(),
                    decl_pos,
                },
                env,
            )
        }
    }
}

/// `Primary.Non_class_member { elt = `meth; ... }`, with the type printed in
/// the environment as it is now.
fn non_class_member(env: &Env, method_name: &aast::Pstring, class_ty: &Ty) -> primary::T {
    let ty_name = {
        let env = env.clone();
        let class_ty = class_ty.clone();
        Lazy::new(move || typing_print::error(None, &env, &class_ty))
    };
    primary::T::NonClassMember {
        elt: primary::MethOrProp::Meth,
        member_name: method_name.1.clone(),
        pos: method_name.0.clone(),
        ty_name,
        decl_pos: get_pos(class_ty),
    }
}

/// Inspect the type attempting to synthesize a method type for each contained
/// class type then reconstruct the overall method type. This should ultimately
/// be moved to constaint solving but we repeat a bunch of the decomposition work
/// here:
///
/// Base cases:
/// - Tclass: synthesize a funcion type given the class name and method name
/// - Tdynamic: the type of a method accessed through dynamic is dynamic
/// - Tany: the type of a method accessed through any is any
///
/// Recursion cases:
/// - Tgeneric, Tnewtype: recurse on the upper-bound(s)
/// - Tdependent: recurse on the underlying type
/// - Tunion: recurse through the union and construct the union of the synthesized function types
/// - Tintersection: recurse through the intersection and construct the intersection of the synthesized function types
///
/// All other cases are errors
pub(crate) fn synth_polymorphic_static_method(
    class_id: &nast::ClassId,
    class_ty: Ty,
    method_name: &aast::Pstring,
    env: &mut Env,
) -> Ty {
    let class_ty = env::expand_type(env, class_ty);
    let r = get_reason(&class_ty).clone();
    match get_node(&class_ty) {
        // -- Base cases --------------------------------------------------------
        Ty_::Tclass((_, class_name), _, _) => match env::get_class(env, class_name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                // A 'naming' error will have been raised for the missing / unloaded class
                // so just return nothing for the class and an 'error' tyvar for the method
                env::fresh_type_error(env, method_name.0.clone())
            }
            decl_entry::T::Found(folded_class) => {
                match env::get_static_member(true, env, &folded_class, &method_name.1) {
                    None => {
                        // No such method; raise an error and return a fresh type variable
                        typing_error_utils::add_typing_error(
                            &tog::smember_not_found(
                                method_name.0.clone(),
                                false,
                                true,
                                true,
                                &folded_class,
                                method_name.1.clone(),
                                callback::unify_error(),
                            ),
                            env,
                        );
                        env::fresh_type_error(env, method_name.0.clone())
                    }
                    Some(class_elt) => {
                        // `{ ce_type = (lazy member_decl_ty); ce_pos = (lazy class_pos); _ }`
                        let member_decl_ty: &DeclTy = &class_elt.ce_type;
                        let class_pos: PosOrDecl = PosOrDecl::clone(&class_elt.ce_pos);
                        match member_decl_ty.node_ref() {
                            ty::decl::Ty_::Tfun(fun_ty) => {
                                let reason = member_decl_ty.reason();
                                // Apply pressimization
                                let fun_ty = crate::typing_enforceability::compute_enforced_and_pessimize_fun_type(
                                    Some(&folded_class),
                                    env,
                                    (**fun_ty).clone(),
                                );
                                // Apply the same validation as static method access
                                validate_polymorphic_static_method(
                                    &folded_class,
                                    &class_elt,
                                    class_name,
                                    class_id,
                                    method_name,
                                    &fun_ty,
                                    env,
                                );
                                // Generate a polymorphic type
                                let fun_ty = synth_polymorphic_static_method_help(
                                    &folded_class,
                                    &(class_pos, class_name.clone()),
                                    method_name,
                                    fun_ty,
                                    env,
                                );
                                // Wrap with supportdyn under SDT
                                let ty = {
                                    let reason = reason::localize(&reason.clone().to_oxidized());
                                    crate::typing_dynamic::maybe_wrap_with_supportdyn(
                                        get_ce_support_dynamic_type(&class_elt),
                                        reason,
                                        fun_ty,
                                    )
                                };
                                ty
                            }
                            _ => {
                                // If the static method exists it must be a function type so
                                // something is wrong
                                panic!("Expected a function type")
                            }
                        }
                    }
                }
            }
        },
        Ty_::Tdynamic(_) | Ty_::Tany(_) => {
            // For [dynamic] ([any]) give the method type as [dynamic] ([any])
            map_reason(class_ty.clone(), |class_reason| {
                reason::flow_prop_access(class_reason, reason::witness(method_name.0.clone()))
            })
        }
        // -- Recursive cases ---------------------------------------------------
        // For generics, newtypes and expression dependent types, attempt to access
        // the member via an upper bound
        Ty_::Tgeneric(_) => {
            let upper_bounds =
                tutils::get_concrete_supertypes(None, None, None, true, env, class_ty.clone());
            let has_no_bound = tutils::no_upper_bound(true, env, &upper_bounds);
            if has_no_bound {
                let method_ty = env::fresh_type_error(env, method_name.0.clone());
                add_primary(non_class_member(env, method_name, &class_ty), env);
                method_ty
            } else {
                let class_ty = inter::intersect_list(env, r, &upper_bounds);
                synth_polymorphic_static_method(class_id, class_ty, method_name, env)
            }
        }
        Ty_::Tnewtype(n, tyl, _) => {
            let class_ty = tutils::get_newtype_super(env, r, n, tyl);
            synth_polymorphic_static_method(class_id, class_ty, method_name, env)
        }
        Ty_::Tdependent(_, class_ty) => {
            synth_polymorphic_static_method(class_id, class_ty.clone(), method_name, env)
        }
        Ty_::Tunion(class_tys) => {
            let mut member_tys: Vec<Ty> = vec![];
            for class_ty in class_tys {
                let member_ty =
                    synth_polymorphic_static_method(class_id, class_ty.clone(), method_name, env);
                member_tys.push(member_ty)
            }
            // `member_ty :: member_tys`: the OCaml list is in the reverse order.
            member_tys.reverse();
            union_::union_list(env, None, r, &member_tys)
        }
        Ty_::Tintersection(class_tys) => {
            let f = |env: &mut Env, class_ty: &Ty| {
                synth_polymorphic_static_method(class_id, class_ty.clone(), method_name, env)
            };
            let member_tys = tutils::run_on_intersection(env, f, class_tys);
            inter::intersect_list(env, r, &member_tys)
        }
        // -- Error cases -------------------------------------------------------
        // For all other types return a fresh variable indicating an error
        Ty_::Tvar(_)
        | Ty_::Tnonnull
        | Ty_::TvecOrDict(_, _)
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Taccess(_)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_)
        | Ty_::TclassPtr(_) => {
            if !tutils::is_tyvar_error(env, &class_ty) {
                add_primary(non_class_member(env, method_name, &class_ty), env)
            }
            env::fresh_type_error(env, method_name.0.clone())
        }
    }
}

pub(crate) fn synth_static_method(
    pos: &Pos,
    class_id: &nast::ClassId,
    method_name: &aast::Pstring,
    ty_args: &[nast::Targ],
    source: aast::FunctionPointerSource,
    env: &mut Env,
) -> (tast::Expr, Ty) {
    let (_, tclass_id, class_ty): (Vec<tast::Targ>, tast::ClassId, Ty) =
        crate::typing::class_id::class_expr(
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            env,
            &[],
            class_id,
        );
    // Intersection lookup can discard the localized type arguments.
    let ((method_ty, ty_args), has_explicit_targs) = match ty_args {
        [] => {
            let method_ty = synth_polymorphic_static_method(class_id, class_ty, method_name, env);
            ((method_ty, vec![]), false)
        }
        _ => {
            let (method_ty, ty_args): (Ty, Vec<tast::Targ>) =
                crate::typing::class_get_expr::class_get(
                    true,          // is_method
                    false,         // is_const
                    None,          // transform_fty
                    None,          // coerce_from_ty
                    None,          // attribute_check_policy
                    Some(ty_args), // explicit_targs
                    Some(false),   // incl_tc (What is this?)
                    Some(true),    // is_function_pointer
                    env,
                    class_ty,
                    method_name,
                    class_id,
                );
            env::set_tyvar_variance(env, None, None, &method_ty);
            ((method_ty, ty_args), true)
        }
    };
    let method_ty = set_function_pointer(env, method_ty);
    let method_ty = set_capture_only_readonly(env, method_ty);
    let method_ty = {
        make_function_ref(has_explicit_targs, pos, method_ty)
    };
    let expr = aast::Expr_::FunctionPointer(Box::new((
        aast::FunctionPtrId::FPClassConst(tclass_id, method_name.clone()),
        ty_args,
        source,
    )));
    make_result(env, pos.clone(), expr, method_ty)
}

// -- Top-level functions -------------------------------------------------

/// Synthesize a (possibly polymorphic) function type based on the declared
/// function signature of a top-level function
pub fn synth_top_level(
    pos: &Pos,
    fun_id: &aast::Sid,
    ty_args: &[nast::Targ],
    source: aast::FunctionPointerSource,
    env: &mut Env,
) -> (tast::Expr, Ty) {
    let (ty, ty_args) = fun_id::synth(fun_id, ty_args, env);
    // Modify the function type to indicate this is a function pointer
    let ty = set_function_pointer(env, ty);
    // All function pointers are readonly since they capture no values
    let ty = set_capture_only_readonly(env, ty);
    let ty = {
        let contains_generics = !ty_args.is_empty();
        make_function_ref(contains_generics, pos, ty)
    };
    let expr = aast::Expr_::FunctionPointer(Box::new((
        aast::FunctionPtrId::FPId(fun_id.clone()),
        ty_args,
        source,
    )));
    make_result(env, pos.clone(), expr, ty)
}

pub(crate) fn synth_poly(
    pos: &Pos,
    (fpid, args, source): &(
        nast::FunctionPtrId,
        Vec<nast::Targ>,
        aast::FunctionPointerSource,
    ),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    match (fpid, args) {
        (aast::FunctionPtrId::FPId(fun_id), ty_args) => {
            synth_top_level(pos, fun_id, ty_args, *source, env)
        }
        (aast::FunctionPtrId::FPClassConst(class_id, method_name), ty_args) => {
            synth_static_method(pos, class_id, method_name, ty_args, *source, env)
        }
    }
}

pub(crate) fn synth_mono(
    pos: &Pos,
    (fpid, args, source): &(
        nast::FunctionPtrId,
        Vec<nast::Targ>,
        aast::FunctionPointerSource,
    ),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    match (fpid, args) {
        (aast::FunctionPtrId::FPClassConst(cid, meth), targs) => {
            let (_, ce, cty): (Vec<tast::Targ>, tast::ClassId, Ty) =
                crate::typing::class_id::class_expr(
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                    env,
                    &[],
                    cid,
                );
            let (fpty, tal): (Ty, Vec<tast::Targ>) = crate::typing::class_get_expr::class_get(
                true,             // is_method
                false,            // is_const
                None,             // transform_fty
                None,             // coerce_from_ty
                None,             // attribute_check_policy
                Some(&targs[..]), // explicit_targs
                Some(false),      // incl_tc (What is this?)
                Some(true),       // is_function_pointer
                env,
                cty,
                meth,
                cid,
            );
            env::set_tyvar_variance(env, None, None, &fpty);
            let fpty = set_function_pointer(env, fpty);
            // All function pointers are readonly since they don't capture any values
            let fpty = set_capture_only_readonly(env, fpty);
            let fpty = {
                let contains_generics = !tal.is_empty() || !targs.is_empty();
                make_function_ref(contains_generics, pos, fpty)
            };
            make_result(
                env,
                pos.clone(),
                aast::Expr_::FunctionPointer(Box::new((
                    aast::FunctionPtrId::FPClassConst(ce, meth.clone()),
                    tal,
                    *source,
                ))),
                fpty,
            )
        }
        (aast::FunctionPtrId::FPId(fun_id), ty_args) => {
            let (ty, ty_args) = fun_id::synth(fun_id, ty_args, env);
            let ty = set_function_pointer(env, ty);
            // All function pointers are readonly since they capture no values
            let ty = set_capture_only_readonly(env, ty);
            let ty = make_function_ref(!ty_args.is_empty(), pos, ty);
            make_result(
                env,
                pos.clone(),
                aast::Expr_::FunctionPointer(Box::new((
                    aast::FunctionPtrId::FPId(fun_id.clone()),
                    ty_args,
                    *source,
                ))),
                ty,
            )
        }
    }
}

pub fn synth(
    pos: &Pos,
    fpid_args: &(
        nast::FunctionPtrId,
        Vec<nast::Targ>,
        aast::FunctionPointerSource,
    ),
    env: &mut Env,
) -> (tast::Expr, Ty) {
    let (_, _, source) = fpid_args;
    match source {
        aast::FunctionPointerSource::Code => synth_poly(pos, fpid_args, env),
        aast::FunctionPointerSource::Lowered => {
            // For expression tree code generated during lowering we preserve the
            // treatment of function pointers as monomorphic function types
            synth_mono(pos, fpid_args, env)
        }
    }
}
