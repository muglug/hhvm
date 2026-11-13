// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_memoize.ml`. See `hh/PORTING.md`.
//!
//! # The environment
//!
//! Every function here returns `unit`: the environments the OCaml derives
//! while it checks a parameter are dropped, and each recursive call of
//! `check_memoizable` starts from the environment its caller passes, which
//! the caller goes on using for its other components. So the functions take
//! `&Env`, and `check_memoizable` works on a copy of the one it is given.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use ty::decl::ty as d;

use crate::decl_entry;
use crate::local_id;
use crate::type_visitor::DeclTypeVisitor;
use crate::typing_defs_core::DeclTy;
use crate::naming_attributes;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_dynamic_utils;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_local_ops;
use crate::typing_make_type as make_type;
use crate::typing_object_get;
use crate::typing_phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_solver;
use crate::typing_tdef_locl;
use crate::typing_utils;

/// `Naming_special_names.Classes.cString` (`naming_special_names_rust` does
/// not have it).
const C_STRING: &str = "\\HH\\string";

fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

/// What `check_memoizable` of `check_param` sees of the parameter.
struct Param<'a> {
    /// The environment `check_param` is given: the one the type names of the
    /// error are printed in.
    env: &'a Env,
    param_pos: &'a Pos,
    param_name: &'a str,
}

impl Param<'_> {
    /// `error ty`
    fn error(&self, ty: &Ty) -> primary::T {
        let ty_name = {
            let env = self.env.clone();
            let ty = ty.clone();
            Lazy::new(move || typing_print::error(None, &env, &ty))
        };
        let msgl = {
            let r = get_reason(ty).clone();
            ty_name.map(move |ty_name| {
                messages(reason::to_string(&("This is ".to_string() + ty_name), &r))
            })
        };
        primary::T::Invalid_memoized_param {
            pos: self.param_pos.clone(),
            reason: msgl,
            ty_name,
        }
    }
}

/// The inner `check_memoizable env ty` of `check_param` (`pos` is the
/// position the outer `check_memoizable env pos ty` is given).
fn check_memoizable(param: &Param<'_>, pos: &Pos, env: &Env, ty: &Ty) {
    let mut env = env.clone();
    let env = &mut env;
    let ty = env::expand_type(env, ty.clone());
    let ety_env = empty_expand_env();
    let ty = typing_dynamic_utils::strip_dynamic(env, ty);
    let (ty_err_opt, ty, _) = typing_tdef_locl::force_expand_typedef(&ety_env, env, ty);
    let (_, ty) = typing_utils::strip_supportdyn(env, ty);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    if !typing_utils::is_tyvar_error(env, &ty) {
        match get_node(&ty) {
            Ty_::Tprim(
                ast_defs::Tprim::Tnull
                | ast_defs::Tprim::Tarraykey
                | ast_defs::Tprim::Tbool
                | ast_defs::Tprim::Tint
                | ast_defs::Tprim::Tfloat
                | ast_defs::Tprim::Tnum,
            ) => {}
            Ty_::Tnonnull | Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Tneg(_) => {
                // `let (_ : env) = Typing_local_ops.enforce_memoize_object pos env`
                typing_local_ops::enforce_memoize_object(pos.clone(), env);
            }
            Ty_::Tprim(
                ast_defs::Tprim::Tvoid | ast_defs::Tprim::Tresource | ast_defs::Tprim::Tnoreturn,
            ) => {
                typing_error_utils::add_typing_error(&typing_error::primary(param.error(&ty)), env)
            }
            Ty_::Toption(ty) => check_memoizable(param, pos, env, ty),
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_variadic),
            }) => {
                for ty in t_required {
                    check_memoizable(param, pos, env, ty)
                }
                for ty in t_optional {
                    check_memoizable(param, pos, env, ty)
                }
                check_memoizable(param, pos, env, t_variadic)
            }
            // Just accept all generic types for now. Stricter check_memoizables to come later.
            Ty_::Tgeneric(_) => {
                // FIXME fun fact:
                // the comment above about "stricter check_memoizables to come later" was added in revision
                // in August 2015
            }
            Ty_::Tlabel(_) => {}
            Ty_::Tnewtype(id, _, _) if id == sn::classes::ENUM_CLASS_LABEL => {
                // EnumClassLabels are memoizable
            }
            // For parameter type 'this::TID' defined by 'type const TID as Bar' check_memoizables
            // Bar recursively. Also enums represented using AKnewtype.
            Ty_::Tnewtype(_, _, ty) | Ty_::Tdependent(_, ty) => {
                check_memoizable(param, pos, env, ty)
            }
            // Handling Tunion and Tintersection case here for completeness, even though it
            // shouldn't be possible to have an unresolved type when check_memoizableing
            // the method declaration. No corresponding test case for this.
            Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
                for ty in tyl {
                    check_memoizable(param, pos, env, ty)
                }
            }
            Ty_::TvecOrDict(_, ty) => check_memoizable(param, pos, env, ty),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple { fields: fdm, .. })) => {
                // TODO(shapes) should unknown type affect memoizability?
                for sft in fdm.values() {
                    check_memoizable(param, pos, env, &sft.ty)
                }
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                for ty in ss_elems {
                    check_memoizable(param, pos, env, ty)
                }
            }
            Ty_::Tclass((_, id), _, _) if id == C_STRING => {}
            Ty_::Tclass(..) => {
                env::open_tyvars(env, pos.clone());
                let type_param = env::fresh_type(env, pos.clone());
                let container_type = make_type::container(reason::none(), type_param.clone());
                let ty_err_opt = typing_utils::sub_type(
                    env,
                    None,
                    None,
                    None,
                    None,
                    ty.clone(),
                    container_type.clone(),
                    Some(reasons_callback::unify_error_at(pos.clone())),
                );
                let is_container = ty_err_opt.is_none();

                let mixed = make_type::mixed(reason::none());
                let hackarray = make_type::any_array(reason::none(), mixed.clone(), mixed);
                let is_hackarray = typing_utils::is_sub_type(env, &ty, &hackarray);
                if !is_hackarray {
                    // Check if it's a UNSAFEsingleton memoize param
                    let singleton = make_type::class_type(
                        reason::none(),
                        sn::classes::UNSAFE_SINGLETON_MEMOIZE_PARAM.to_string(),
                        vec![],
                    );
                    if typing_utils::is_sub_type(env, &ty, &singleton) {
                    } else {
                        typing_local_ops::enforce_memoize_object(pos.clone(), env)
                    }
                }
                env::set_tyvar_variance(env, None, None, &container_type);
                let e1 = typing_solver::close_tyvars_and_solve(env);
                if let Some(err) = &e1 {
                    typing_error_utils::add_typing_error(err, env)
                }
                if is_container {
                    check_memoizable(param, pos, env, &type_param)
                } else {
                    let base_error = param.error(&ty);
                    let param_pos = param.param_pos;
                    let class_id = aast::ClassId_::CIexpr(aast::Expr(
                        (),
                        param_pos.clone(),
                        aast::Expr_::Lvar(Box::new(aast::Lid(
                            param_pos.clone(),
                            local_id::make_unscoped(param.param_name),
                        ))),
                    ));
                    let member_id =
                        ast_defs::Id(pos.clone(), sn::members::M_GET_INSTANCE_KEY.to_string());
                    let (ty_err_opt, (tfty, _tal)) = typing_object_get::obj_get(
                        param_pos.clone(),
                        true,
                        None,
                        None,
                        &[],
                        &class_id,
                        &member_id,
                        callback::always(base_error),
                        None,
                        env,
                        ty.clone(),
                    );
                    if let Some(err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    let _ = crate::typing::call(
                        None,
                        None,
                        None,
                        None,
                        pos,
                        pos,
                        pos,
                        env,
                        tfty,
                        &[],
                        None,
                    );
                }
            }
            Ty_::Taccess(_) => {}
            Ty_::Tfun(_)
            | Ty_::Ttuple(TupleType {
                extra: TupleExtra::Tsplat(_),
                ..
            })
            | Ty_::Tvar(_) => {
                typing_error_utils::add_typing_error(&typing_error::primary(param.error(&ty)), env)
            }
            Ty_::TclassPtr(_) => {
                // Follow classname<T> memo check via string bound
            }
        }
    }
}

fn check_param(env: &Env, param: &nast::FunParam) {
    let aast::FunParam {
        type_hint: param_type_hint,
        pos: param_pos,
        name: param_name,
        ..
    } = param;
    let param = Param {
        env,
        param_pos,
        param_name,
    };
    match &param_type_hint.1 {
        None => {}
        Some(hint) => {
            let aast::Hint(hint_pos, _) = hint;
            let mut env = env.clone();
            let (ty_err_opt, ty) = typing_phase::localize_hint_no_subst(&mut env, true, hint);
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, &env)
            }
            // `check_memoizable env hint_pos ty`
            check_memoizable(&param, hint_pos, &env, &ty)
        }
    }
}

fn check(env: &Env, user_attributes: &[nast::UserAttribute], params: &[nast::FunParam]) {
    if naming_attributes::mem(sn::user_attributes::MEMOIZE, user_attributes)
        || naming_attributes::mem(sn::user_attributes::MEMOIZE_LSB, user_attributes)
    {
        for param in params {
            check_param(env, param)
        }
    }
}

fn mentions_generic(name: &str, ty: &DeclTy) -> bool {
    struct Visitor<'n> {
        name: &'n str,
    }
    impl DeclTypeVisitor<bool> for Visitor<'_> {
        fn on_tgeneric(&mut self, found: bool, _r: &crate::ctx::R, n: &str) -> bool {
            found || n == self.name
        }

        // (`on_type found ty = found || parent#on_type found ty` only stops
        // the traversal early.)
    }
    let mut visitor = Visitor { name };
    visitor.on_type(false, ty)
}

/// Whether generic [name] occurs in the type arguments of an `IMemoizeParam`
/// class in [ty]. Such an argument is keyed only by its `getInstanceKey()`.
fn under_instance_key(env: &Env, name: &str, fuel: isize, ty: &DeclTy) -> bool {
    let go = |ty: &DeclTy| under_instance_key(env, name, fuel, ty);
    match ty.node_ref() {
        d::Ty_::Tapply(apply) => {
            let (cname, targs) = (apply.0.id_ref().as_str(), &apply.1);
            match env::get_class(env, cname) {
                decl_entry::T::Found(cls) => {
                    crate::folded_class::has_ancestor(&cls, sn::classes::IMEMOIZE_PARAM)
                        && targs.iter().any(|ty| mentions_generic(name, ty))
                        || targs.iter().any(go)
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                    match env::get_typedef(env, cname) {
                        decl_entry::T::Found(td)
                            if matches!(
                                &td.type_assignment,
                                d::TypedefTypeAssignment::SimpleTypeDef(..)
                            ) && fuel > 0 =>
                        {
                            let body = match &td.type_assignment {
                                d::TypedefTypeAssignment::SimpleTypeDef(_, body) => body,
                                d::TypedefTypeAssignment::CaseType(..) => unreachable!(),
                            };
                            let subst = crate::decl_instantiate::make_subst(&td.tparams, targs);
                            under_instance_key(
                                env,
                                name,
                                fuel - 1,
                                &crate::decl_instantiate::instantiate(&subst, body),
                            )
                        }
                        _ => targs.iter().any(go),
                    }
                }
            }
        }
        d::Ty_::Toption(ty) | d::Ty_::Tlike(ty) => go(ty),
        d::Ty_::TvecOrDict(kv) => go(&kv.0) || go(&kv.1),
        d::Ty_::Tunion(tyl) | d::Ty_::Tintersection(tyl) => tyl.iter().any(go),
        d::Ty_::Ttuple(tuple) => {
            let d::TupleType(t_required, t_optional, t_extra) = &**tuple;
            t_required.iter().chain(t_optional.iter()).any(go)
                || match t_extra {
                    d::TupleExtra::Tvariadic(ty) | d::TupleExtra::Tsplat(ty) => go(ty),
                }
        }
        d::Ty_::Tshape(shape) => match &**shape {
            d::ShapeType::Simple(d::ShapeTypeSimple(_, s_fields)) => {
                s_fields.values().any(|sft| go(&sft.ty))
            }
            d::ShapeType::Splat(_) => false,
        },
        _ => false,
    }
}

/// The memoization cache ignores erased generics, so one cached result serves
/// every instantiation.
pub fn check_erased_generics(
    env: &Env,
    user_attributes: &[nast::UserAttribute],
    tparams: &[nast::Tparam],
    params: &[nast::FunParam],
    ret: &nast::TypeHint,
) {
    if env::get_tcopt(env).tco_ban_memoize_erased_generic_return {
        // `Option.first_some a b`: both are computed, `b` first.
        let attr_pos_lsb =
            naming_attributes::mem_pos(sn::user_attributes::MEMOIZE_LSB, user_attributes);
        let attr_pos = naming_attributes::mem_pos(sn::user_attributes::MEMOIZE, user_attributes)
            .or(attr_pos_lsb);
        match (attr_pos, crate::aast::hint_of_type_hint(ret)) {
            (Some(attr_pos), Some(hint)) => {
                let ret_ty = crate::decl_hint::hint(&env.decl_env, hint);
                let erased: Vec<&nast::Tparam> = tparams
                    .iter()
                    .filter(|tp| match tp.reified {
                        aast::ReifyKind::Reified => false,
                        aast::ReifyKind::Erased | aast::ReifyKind::SoftReified => true,
                    })
                    .collect();
                let (positive, negative) =
                    crate::typing_variance::get_positive_negative_generics(
                        &erased.iter().map(|tp| tp.name.1.clone()).collect(),
                        false,
                        env,
                        (im::OrdMap::new(), im::OrdMap::new()),
                        &ret_ty,
                    );
                for tp in erased.iter() {
                    let ast_defs::Id(pos, tparam_name) = &tp.name;
                    let report = |via_param: Option<Pos>| {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::Memoize_erased_generic_return {
                                pos: pos.clone(),
                                tparam_name: tparam_name.clone(),
                                attr_pos: attr_pos.clone(),
                                via_param,
                            }),
                            env,
                        )
                    };
                    if negative.contains_key(tparam_name) {
                        report(None)
                    } else if positive.contains_key(tparam_name) {
                        let via = params.iter().find_map(|param| {
                            crate::aast::hint_of_type_hint(&param.type_hint)
                                .as_ref()
                                .and_then(|hint| {
                                    if under_instance_key(
                                        env,
                                        tparam_name,
                                        10,
                                        &crate::decl_hint::hint(&env.decl_env, hint),
                                    ) {
                                        Some(param.pos.clone())
                                    } else {
                                        None
                                    }
                                })
                        });
                        if let Some(p) = via {
                            report(Some(p))
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// Checks if a function can be memoized. If the function cannot be
/// memoized this will add an error to the global error list.
pub fn check_function(env: &Env, f: &nast::Fun_) {
    check(env, &f.user_attributes.0, &f.params)
}

/// Checks if a method can be memoized. If the method cannot be
/// memoized this will add an error to the global error list.
pub fn check_method(env: &Env, m: &nast::Method_) {
    check(env, &m.user_attributes.0, &m.params)
}
