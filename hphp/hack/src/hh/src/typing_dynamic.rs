// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_dynamic.ml`. See `hh/PORTING.md`.
//!
//! - `make_like`, `push_like_tyargs` and `try_push_like` thread a boolean
//!   (`changed`) where the OCaml `List.map_env`/`TShapeMap.map_env` thread an
//!   environment; they only read the typing environment.
//! - Where OCaml drops the environment that a call returns
//!   (`snd (Typing_dynamic_utils.try_strip_dynamic env ty)`,
//!   `let (_env, cty) = Typing_phase.localize_no_subst ...`,
//!   `snd (Typing_return.make_return_type ...)`), the call gets a copy of the
//!   environment.
//! - `check_property_sound_for_dynamic_write` returns no environment: the one
//!   that localization gives is used for the rest of the function only, so it
//!   is a copy.

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;
use ty::decl::Ty_ as DeclTy_;

use crate::decl_provider;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::typing_defs;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::set_ft_support_dynamic_type;
use crate::typing_defs_core::t_shape_map;
use crate::typing_dynamic_utils;
use crate::typing_enforceability;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_log;
use crate::typing_make_type;
use crate::typing_phase;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_return;
use crate::typing_utils;

/// Add `supportdyn<mixed>` lower and upper bound to any type parameters that are marked <<__RequireDynamic>>
/// Just add the upper bound to others.
pub fn add_require_dynamic_bounds(env: &mut Env, cls: &decl_provider::ClassDecl) {
    for tp in cls::tparams_ref(cls) {
        let require_dynamic =
            typing_defs::attributes::mem(sn::user_attributes::REQUIRE_DYNAMIC, &tp.user_attributes);
        let dtype = typing_make_type::supportdyn_mixed(reason::witness_from_decl(
            tp.name.pos().clone().to_oxidized(),
        ));
        env::add_upper_bound(None, env, tp.name.id_ref().as_str(), dtype.clone());
        if require_dynamic
            // Implicit pessimisation should ignore the RequireDynamic attribute
            // because everything should be pessimised enough that it isn't necessary.
            && !env.genv.tcopt.po.everything_sdt
        {
            env::add_lower_bound(None, env, tp.name.id_ref().as_str(), dtype)
        }
    }
}

fn is_dynamic_decl(env: &Env, ty: &DeclTy) -> bool {
    match ty.node_ref() {
        DeclTy_::Tdynamic => true,
        DeclTy_::Tgeneric(name) if env::get_require_dynamic(env, name.as_str()) => true,
        _ => false,
    }
}

/// Check that a property type is a subtype of dynamic
///
/// `on_error (fst id) (snd id) classname (pos, ty)` is
/// `on_error(id.0, id.1, classname, (pos, ty))`.
pub fn check_property_sound_for_dynamic_read<A>(
    on_error: impl FnOnce(A, String, String, (PosOrDecl, String)) -> typing_error::T,
    env: &Env,
    classname: String,
    id: (A, String),
    ty: &Ty,
) -> Option<typing_error::T> {
    if !typing_utils::is_supportdyn(env, ty) {
        let pos = get_pos(ty);
        typing_log::log_pessimise_prop(env, &pos_or_decl::unsafe_to_raw_pos(pos.clone()), &id.1);
        let (id_pos, id_name) = id;
        Some(on_error(
            id_pos,
            id_name,
            classname,
            (pos, typing_print::full_strip_ns(true, env, ty)),
        ))
    } else {
        None
    }
}

/// The optional ty should be (if not None) the localisation of the decl_ty.
/// This lets us avoid re-localising the decl type when the caller has already
/// localised it
pub fn check_property_sound_for_dynamic_write<A>(
    this_class: Option<&cls::T>,
    on_error: impl FnOnce(A, String, String, (PosOrDecl, String)) -> typing_error::T,
    env: &Env,
    classname: String,
    id: (A, String),
    decl_ty: &DeclTy,
    ty: Option<Ty>,
) -> Option<typing_error::T> {
    let te_check = typing_enforceability::is_enforceable(this_class, env, decl_ty);
    // If the property type isn't enforceable, but is a supertype of dynamic,
    // then the property will still be safe to write via a receiver expression of type
    // dynamic.
    if !te_check {
        // The environment that localization returns is only used in this
        // function.
        let mut localized_env: Option<Env> = None;
        let (ty_err_opt, ty) = match ty {
            Some(ty) => (None, ty),
            None => {
                let mut lenv = env.clone();
                let res = typing_phase::localize_no_subst(&mut lenv, true, decl_ty);
                localized_env = Some(lenv);
                res
            }
        };
        let env: &Env = localized_env.as_ref().unwrap_or(env);
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env);
        }
        if !(typing_utils::is_any(env, &ty)
            || typing_utils::is_sub_type_for_union(
                env,
                &typing_make_type::dynamic(reason::none()),
                &ty,
            ))
        {
            let pos = decl_utils::get_pos(decl_ty).to_oxidized();
            typing_log::log_pessimise_prop(
                env,
                &pos_or_decl::unsafe_to_raw_pos(pos.clone()),
                &id.1,
            );
            let (id_pos, id_name) = id;
            Some(on_error(
                id_pos,
                id_name,
                classname,
                (
                    pos,
                    typing_print::full_strip_ns_decl(
                        None,
                        false,
                        env,
                        &decl_ty.clone().to_oxidized(),
                    ),
                ),
            ))
        } else {
            None
        }
    } else {
        None
    }
}

/// From the signature alone, are function parameter hints safe for dynamic?
/// i.e. (1) present, and (2) fully-enforced, or `dynamic`.
pub fn function_parameters_safe_for_dynamic(
    this_class: Option<&cls::T>,
    env: &Env,
    params_decl_ty: &[Option<DeclTy>],
) -> bool {
    params_decl_ty.iter().all(|dtyopt| match dtyopt {
        Some(dty) => {
            // If a parameter isn't enforceable, but is just typed as dynamic,
            // the method will still be safe to call via a receiver expression of type
            // dynamic.
            typing_enforceability::is_enforceable(this_class, env, dty) || is_dynamic_decl(env, dty)
        }
        // If a parameter isn't typed (e.g. for a lambda), we might infer
        // a non-SDT type for it and so need to check again under dynamic
        None => false,
    })
}

/// checks that a method can be invoked in a dynamic context by ensuring that
/// the types of its arguments are enforceable and its return type can be
/// coerced to dynamic
pub fn sound_dynamic_interface_check(
    this_class: Option<&cls::T>,
    env: &Env,
    params_decl_ty: &[Option<DeclTy>],
    ret_locl_ty: &Ty,
) -> bool {
    // 1. check if all the parameters of the method are enforceable
    let enforceable_params = function_parameters_safe_for_dynamic(this_class, env, params_decl_ty);
    let coercible_return_type =
        // 2. check if the return type is coercible
        typing_utils::is_supportdyn(env, ret_locl_ty);
    enforceable_params && coercible_return_type
}

pub fn sound_dynamic_interface_check_from_fun_ty(
    this_class: Option<&cls::T>,
    env: &Env,
    fun_ty: &DeclFunType,
) -> bool {
    let params_decl_ty: Vec<Option<DeclTy>> = fun_ty
        .params
        .iter()
        .map(|fun_param| Some(fun_param.ty.clone()))
        .collect();
    // `snd (Typing_return.make_return_type ...)`: the environment is dropped.
    let ret_locl_ty = typing_return::make_return_type(
        &empty_expand_env(),
        this_class,
        None,  // is_toplevel
        false, // supportdyn
        &mut env.clone(),
        Pos::NONE,                // hint_pos
        Some(fun_ty.ret.clone()), // explicit
        None,                     // default
    );
    sound_dynamic_interface_check(this_class, env, &params_decl_ty, &ret_locl_ty)
}

/// Given t, construct ~t.
/// acc is a boolean that remains false if no change was made (e.g. t = dynamic)
fn make_like(env: &Env, changed: bool, ty: Ty) -> (bool, Ty) {
    if typing_defs::is_dynamic(&ty)
        || typing_dynamic_utils::try_strip_dynamic(None, None, &mut env.clone(), &ty).is_some()
    {
        (changed, ty)
    } else {
        let r = get_reason(&ty).clone();
        (true, typing_make_type::locl_like(r, ty))
    }
}

pub fn maybe_wrap_with_supportdyn(should_wrap: bool, locl_r: Reason, ft: FunType) -> Ty {
    if should_wrap {
        let r = reason::support_dynamic_type(reason::to_pos(&locl_r));
        let ft = set_ft_support_dynamic_type(ft, false);
        typing_make_type::supportdyn(r, mk((locl_r, Ty_::Tfun(std::rc::Rc::new(ft)))))
    } else {
        mk((locl_r, Ty_::Tfun(std::rc::Rc::new(ft))))
    }
}

fn push_like_tyargs(env: &Env, tyl: &[Ty], tparams: &[DeclTparam]) -> (bool, Vec<Ty>) {
    if tyl.len() != tparams.len() {
        (false, tyl.to_vec())
    } else {
        let make_like = |changed: bool, ty: &Ty, tp: &DeclTparam| -> (bool, Ty) {
            // Don't both pushing through a contravariant parameter, because
            // Contra<~t> <: Contra<t> <: ~Contra<t> by variance and union
            // subtyping rules already
            match tp.variance {
                ast_defs::Variance::Contravariant => (changed, ty.clone()),
                _ => {
                    let (changed_, ty_) = make_like(env, changed, ty.clone());
                    // Push like onto type argument; if the resulting type is not a subtype of
                    // the the upper bound on the type parameter, then intersect it with the
                    // upper bonud so that the resulting type is well-formed.
                    // For example, dict<~string & arraykey,bool> <: ~dict<string,bool>
                    // because the first type parameter has an upper bound of arraykey.
                    let upper_bounds: Vec<Ty> = tp
                        .constraints
                        .iter()
                        .filter_map(|(c, cty)| match c {
                            ast_defs::ConstraintKind::ConstraintAs => {
                                let (_ty_err_opt, cty) =
                                    typing_phase::localize_no_subst(&mut env.clone(), true, cty);
                                Some(cty)
                            }
                            _ => None,
                        })
                        .collect();
                    // Type meets all bounds, so leave alone
                    if upper_bounds
                        .iter()
                        .all(|bound| typing_utils::is_sub_type_for_union(env, &ty_, bound))
                    {
                        (changed_, ty_)
                    } else {
                        let mut tyl = vec![ty_];
                        tyl.extend(upper_bounds);
                        (
                            changed_,
                            mk((get_reason(ty).clone(), Ty_::Tintersection(tyl))),
                        )
                    }
                }
            }
        };
        // `List.map2_env false tyl tparams ~f:make_like`
        let mut changed = false;
        let tyl = tyl
            .iter()
            .zip(tparams.iter())
            .map(|(ty, tp)| {
                let (changed_, ty) = make_like(changed, ty, tp);
                changed = changed_;
                ty
            })
            .collect();
        (changed, tyl)
    }
}

/// Make parameters of SDT types (tuples, shapes, and classes) into like types,
/// if that results in a well-formed type, otherwise leave them alone.
/// Return None if no change was made.
/// Example input: shape('a' => int, 'b' => string)
/// Output: shape('a' => ~int, 'b' => ~string)
///
/// Example input: dict<int,string>
/// Output: dict<int,~string> (because ~int doesn't subtype arraykey)
pub fn try_push_like(env: &mut Env, ty: &Ty) -> Option<Ty> {
    let r = get_reason(ty).clone();
    match get_node(ty) {
        Ty_::Ttuple(TupleType {
            required,
            optional,
            extra,
        }) => {
            // `List.map_env false t_required ~f:(make_like env)`
            let mut changed = false;
            let t_required: Vec<Ty> = required
                .iter()
                .map(|ty| {
                    let (changed_, ty) = make_like(env, changed, ty.clone());
                    changed = changed_;
                    ty
                })
                .collect();
            let t_optional: Vec<Ty> = optional
                .iter()
                .map(|ty| {
                    let (changed_, ty) = make_like(env, changed, ty.clone());
                    changed = changed_;
                    ty
                })
                .collect();
            let (changed, t_extra) = match extra {
                TupleExtra::Tvariadic(t_variadic) => {
                    let (changed, t_variadic) = make_like(env, changed, t_variadic.clone());
                    (changed, TupleExtra::Tvariadic(t_variadic))
                }
                TupleExtra::Tsplat(t_splat) => {
                    let (changed, t_splat) = make_like(env, changed, t_splat.clone());
                    (changed, TupleExtra::Tsplat(t_splat))
                }
            };
            if changed {
                Some(mk((
                    r,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: t_optional,
                        extra: t_extra,
                    }),
                )))
            } else {
                None
            }
        }
        Ty_::Tfun(ft) => {
            let (changed, ret_ty) = make_like(env, false, ft.ret.clone());
            if changed {
                let mut ft = ft.clone();
                std::rc::Rc::make_mut(&mut ft).ret = ret_ty;
                Some(mk((r, Ty_::Tfun(ft))))
            } else {
                None
            }
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: kind,
            fields,
        })) => {
            // `TShapeMap.map_env add_like_to_shape_field false fields`, on the
            // types of the fields first (in the order of the keys): the map is
            // built only if one changed, as only then is it used.
            let mut changed = false;
            let tys: Vec<Ty> = (fields.values())
                .map(|sft| {
                    let (changed_, ty) = make_like(env, changed, sft.ty.clone());
                    changed = changed_;
                    ty
                })
                .collect();
            if changed {
                let fields: t_shape_map::T<ShapeFieldType> = (fields.iter())
                    .zip(tys)
                    .map(|((name, sft), ty)| {
                        (
                            name.clone(),
                            ShapeFieldType {
                                optional: sft.optional,
                                ty,
                            },
                        )
                    })
                    .collect::<Vec<_>>()
                    .into_iter()
                    .collect();
                Some(mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: kind.clone(),
                        fields,
                    })),
                )))
            } else {
                None
            }
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            let mut changed = false;
            let ss_elems: Vec<Ty> = ss_elems
                .iter()
                .map(|elem| {
                    let pushed = try_push_like(env, elem);
                    match pushed {
                        None => elem.clone(),
                        Some(ty) => {
                            changed = true;
                            ty
                        }
                    }
                })
                .collect();
            if changed {
                let (_, ty) = crate::typing_shape_normalize::splat(None, r, ss_elems, env);
                Some(ty)
            } else {
                None
            }
        }
        Ty_::Tnewtype(n, tyl, bound) => {
            // Not in the OCaml: without type arguments nothing changes (whatever the
            // parameters), and the lookup is made only for its dependency edge.
            if tyl.is_empty() && !crate::deps::records_dependency_edges(env) {
                return None;
            }
            let tparams = env::get_class_or_typedef_tparams(env, n);
            let (changed, tyl) = push_like_tyargs(env, tyl, &tparams);
            if changed {
                Some(mk((r, Ty_::Tnewtype(n.clone(), tyl, bound.clone()))))
            } else {
                None
            }
        }
        Ty_::Tclass((p, n), exact, tyl) => {
            // Not in the OCaml: without type arguments nothing changes (whatever the
            // parameters), and the lookup is made only for its dependency edge.
            if tyl.is_empty() && !crate::deps::records_dependency_edges(env) {
                return None;
            }
            let tparams = env::get_class_or_typedef_tparams(env, n);
            let (changed, tyl) = push_like_tyargs(env, tyl, &tparams);
            if changed {
                Some(mk((
                    r,
                    Ty_::Tclass((p.clone(), n.clone()), exact.clone(), tyl),
                )))
            } else {
                None
            }
        }
        Ty_::Toption(ty) => match try_push_like(env, ty) {
            Some(ty) => Some(mk((r, Ty_::Toption(ty)))),
            None => None,
        },
        Ty_::TvecOrDict(tk, tv) => {
            // `List.map_env false [tk; tv] ~f:(make_like env)`
            let (changed, tk) = make_like(env, false, tk.clone());
            let (changed, tv) = make_like(env, changed, tv.clone());
            if changed {
                Some(mk((r, Ty_::TvecOrDict(tk, tv))))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// If ty is ~ty0 then return ty0
/// Otherwise, recursively apply like-stripping to all covariant positions
///   e.g. tuple and shape components, covariant type arguments to generic classes.
pub fn strip_covariant_like(env: &mut Env, ty: Ty) -> Ty {
    // Not in the OCaml, which builds a new node for each type it goes
    // through: a node none of whose components changes is given back as it
    // is (the new node would be equal to it, reasons included; only its
    // address differs). The components are compared with `phys_equal`.
    let same = |t1: &Ty, t2: &Ty| crate::typing_defs_core::phys_equal(t1, t2);
    let all_same = |tyl1: &[Ty], tyl2: &[Ty]| tyl1.iter().zip(tyl2).all(|(t1, t2)| same(t1, t2));
    match typing_dynamic_utils::try_strip_dynamic(Some(true), None, env, &ty) {
        Some(ty) => ty,
        None => {
            let ty = env::expand_type(env, ty);
            let r = get_reason(&ty).clone();
            match get_node(&ty) {
                Ty_::Ttuple(TupleType {
                    required,
                    optional,
                    extra,
                }) => {
                    let t_required: Vec<Ty> = required
                        .iter()
                        .map(|ty| strip_covariant_like(env, ty.clone()))
                        .collect();
                    let t_optional: Vec<Ty> = optional
                        .iter()
                        .map(|ty| strip_covariant_like(env, ty.clone()))
                        .collect();
                    let t_extra = match extra {
                        TupleExtra::Tvariadic(t_variadic) => {
                            TupleExtra::Tvariadic(strip_covariant_like(env, t_variadic.clone()))
                        }
                        TupleExtra::Tsplat(t_splat) => {
                            TupleExtra::Tsplat(strip_covariant_like(env, t_splat.clone()))
                        }
                    };
                    let extra_same = match (extra, &t_extra) {
                        (TupleExtra::Tvariadic(t1), TupleExtra::Tvariadic(t2))
                        | (TupleExtra::Tsplat(t1), TupleExtra::Tsplat(t2)) => same(t1, t2),
                        _ => false,
                    };
                    if extra_same && all_same(required, &t_required) && all_same(optional, &t_optional)
                    {
                        return ty;
                    }
                    mk((
                        r,
                        Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: t_optional,
                            extra: t_extra,
                        }),
                    ))
                }
                Ty_::Tfun(ft) => {
                    let ret_ty = strip_covariant_like(env, ft.ret.clone());
                    if same(&ret_ty, &ft.ret) {
                        return ty;
                    }
                    let mut ft = ft.clone();
                    std::rc::Rc::make_mut(&mut ft).ret = ret_ty;
                    mk((r, Ty_::Tfun(ft)))
                }
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin,
                    unknown_value: kind,
                    fields,
                })) => {
                    // `TShapeMap.map_env strip_shape_field env fields`, reading
                    // the fields of the shape instead of a copy of them (in the
                    // order of the keys). The new shape has no origin: the
                    // shape is kept only if it has none either.
                    let tys: Vec<Ty> = (fields.values())
                        .map(|ShapeFieldType { ty, .. }| strip_covariant_like(env, ty.clone()))
                        .collect();
                    if matches!(origin, TypeOrigin::MissingOrigin)
                        && fields.values().zip(&tys).all(|(sft, ty)| same(&sft.ty, ty))
                    {
                        return ty;
                    }
                    let fields: t_shape_map::T<ShapeFieldType> = (fields.iter())
                        .zip(tys)
                        .map(|((name, ShapeFieldType { optional, .. }), ty)| {
                            (
                                name.clone(),
                                ShapeFieldType {
                                    optional: *optional,
                                    ty,
                                },
                            )
                        })
                        .collect::<Vec<_>>()
                        .into_iter()
                        .collect();
                    mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: kind.clone(),
                            fields,
                        })),
                    ))
                }
                Ty_::Tnewtype(n, tyl, bound) => {
                    let new_tyl = strip_covariant_like_tyargs_of(env, n, tyl);
                    let new_bound = if n == sn::classes::MEMBER_OF {
                        strip_covariant_like(env, bound.clone())
                    } else {
                        bound.clone()
                    };
                    if same(&new_bound, bound) && all_same(tyl, &new_tyl) {
                        return ty;
                    }
                    mk((r, Ty_::Tnewtype(n.clone(), new_tyl, new_bound)))
                }
                Ty_::Tclass((p, n), exact, tyl) => {
                    let new_tyl = strip_covariant_like_tyargs_of(env, n, tyl);
                    if all_same(tyl, &new_tyl) {
                        return ty;
                    }
                    mk((r, Ty_::Tclass((p.clone(), n.clone()), exact.clone(), new_tyl)))
                }
                Ty_::Toption(ty1) => {
                    let new_ty1 = strip_covariant_like(env, ty1.clone());
                    if same(&new_ty1, ty1) {
                        return ty;
                    }
                    mk((r, Ty_::Toption(new_ty1)))
                }
                Ty_::TvecOrDict(tk, tv) => {
                    let new_tk = strip_covariant_like(env, tk.clone());
                    let new_tv = strip_covariant_like(env, tv.clone());
                    if same(&new_tk, tk) && same(&new_tv, tv) {
                        return ty;
                    }
                    mk((r, Ty_::TvecOrDict(new_tk, new_tv)))
                }
                _ => ty,
            }
        }
    }
}

/// `let tparams = Env.get_class_or_typedef_tparams env n in
/// strip_covariant_like_tyargs env tyl tparams`. Not in the OCaml: without
/// type arguments the result is the empty list whatever the parameters, and
/// the lookup is made only for the dependency edge it records (if any).
fn strip_covariant_like_tyargs_of(env: &mut Env, n: &str, tyl: &[Ty]) -> Vec<Ty> {
    if tyl.is_empty() && !crate::deps::records_dependency_edges(env) {
        return vec![];
    }
    let tparams = env::get_class_or_typedef_tparams(env, n);
    strip_covariant_like_tyargs(env, tyl, &tparams)
}

fn strip_covariant_like_tyargs(env: &mut Env, tyl: &[Ty], tparams: &[DeclTparam]) -> Vec<Ty> {
    if tyl.len() != tparams.len() {
        tyl.to_vec()
    } else {
        let strip_covariant_like_tyarg = |env: &mut Env, ty: &Ty, tp: &DeclTparam| -> Ty {
            match tp.variance {
                ast_defs::Variance::Contravariant | ast_defs::Variance::Invariant => ty.clone(),
                ast_defs::Variance::Covariant => strip_covariant_like(env, ty.clone()),
            }
        };
        tyl.iter()
            .zip(tparams.iter())
            .map(|(ty, tp)| strip_covariant_like_tyarg(env, ty, tp))
            .collect()
    }
}
