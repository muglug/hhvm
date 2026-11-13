// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_solver.ml`. See `hh/PORTING.md`.
//!
//! # Shadowed definitions
//!
//! The OCaml defines `try_bind_to_equal_bound` twice: first with `~freshen`
//! and a reason, which the functions in between call, then (at the end of the
//! file) the one of the `.mli`. The first is in the private module
//! [`with_freshen`]. The first `solve_to_equal_bound_or_wrt_variance`, which
//! only the second one calls, is nested in it.

use itertools::Either;
use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::ast_defs::Variance;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use ty::decl::ty as d;

use crate::aast_defs;
use crate::decl_entry;
use crate::diagnostics_state;
/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::pos_or_decl;
use crate::tast;
use crate::tvid;
use crate::typing_defs;
use crate::typing_defs::shape_field_map;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::is_constraint_type;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TaccessType;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::exact_equal;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::map_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_flags;
/// `module Env = Typing_env`
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_inference_env;
/// `module Inter = Typing_intersection`
use crate::typing_intersection as inter;
use crate::typing_log;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason;
use crate::typing_reason::T as Reason;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;
/// `module Utils = Typing_solver_utils`
use crate::typing_solver_utils as utils;
use crate::typing_union;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `Option.merge a b ~f`
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// The messages of `Typing_reason.to_string`.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

/// `Typing_print.subtype_prop`, which `crate::typing_print` leaves out (as a
/// debugging function): the same function, on [`typing_print::debug_i`].
fn typing_print_subtype_prop(env: &Env, prop: &tl::SubtypeProp) -> String {
    fn subtype_prop(env: &Env, prop: &tl::SubtypeProp) -> String {
        match prop {
            tl::SubtypeProp::Conj(ps) if ps.is_empty() => "TRUE".to_string(),
            tl::SubtypeProp::Conj(ps) => {
                let ps: Vec<String> = ps.iter().map(|p| subtype_prop(env, p)).collect();
                "(".to_string() + &ps.join(" && ") + ")"
            }
            tl::SubtypeProp::Disj(_, ps) if ps.is_empty() => "FALSE".to_string(),
            tl::SubtypeProp::Disj(_, ps) => {
                let ps: Vec<String> = ps.iter().map(|p| subtype_prop(env, p)).collect();
                "(".to_string() + &ps.join(" || ") + ")"
            }
            tl::SubtypeProp::IsSubtype(false, ty1, ty2) => {
                // `^` evaluates its right operand first.
                let ty2 = typing_print::debug_i(env, ty2);
                typing_print::debug_i(env, ty1) + " <: " + &ty2
            }
            tl::SubtypeProp::IsSubtype(true, ty1, ty2) => {
                let ty2 = typing_print::debug_i(env, ty2);
                typing_print::debug_i(env, ty1) + " <D: " + &ty2
            }
            tl::SubtypeProp::AmbiguousShapeSplat(vars) => {
                let vars: Vec<String> = vars.iter().map(|v| tvid::show(*v)).collect();
                "ambiguous_shape_splat(".to_string() + &vars.join(", ") + ")"
            }
        }
    }
    let p_str = subtype_prop(env, prop);
    p_str
}

fn log_remaining_prop(env: &Env) {
    let filename = crate::pos::filename(&env.genv.callable_pos);
    if !crate::relative_path::is_hhi(crate::relative_path::prefix(&filename)) {
        let prop = typing_inference_env::get_nongraph_subtype_prop(&env.inference_env);
        if typing_env::get_tcopt(env).tco_log_inference_constraints {
            let p_as_string = typing_print_subtype_prop(env, &prop);
            let pos = crate::pos::string(&crate::pos::to_absolute(&env.genv.callable_pos));
            let size = tl::size(&prop);
            let n_disj = tl::n_disj(&prop);
            let n_conj = tl::n_conj(&prop);
            crate::typing_logger::inference_cnstr::log(&p_as_string, &pos, size, n_disj, n_conj);
        }
        if (!diagnostics_state::currently_has_errors()) && !tl::is_valid(&prop) {
            typing_log::log_prop(
                1,
                &pos_or_decl::of_raw_pos(env.genv.callable_pos.clone()),
                "There are remaining unsolved constraints!",
                env,
                &prop,
            )
        }
    }
}

/// Given a type ty, replace any covariant or contravariant components of the type
/// with fresh type variables. Components replaced include
///   covariant key and element types for tuples, arrays, and shapes
///   covariant return type and contravariant parameter types for function types
///   co- and contra-variant parameters to classish types and newtypes
/// Note that the variance of type variables is set explicitly to be invariant
/// because we only use this function on the lower or upper bounds of an invariant
/// type variable.
///
/// Also note that freshening lifts through unions and nullables.
///
/// Example 1: the type
///   ?dict<t1,t2>
/// will be transformed to
///   ?dict<#1,#2>
///
/// Example 2: the contravariant/invariant type
///   ContraInv<t1,t2>
/// will be transformed to
///   Contra<#1,t2>
/// leaving the invariant component alone.
///
/// With `None`, OCaml returns no environment: the caller goes on with the
/// one it passed, so it is restored here (the expansion can change it).
fn freshen_inside_ty(env: &mut Env, ty: Ty) -> Option<Ty> {
    let freshen_inside_tyl = |env: &mut Env, tyl: &[Ty]| -> Option<Vec<Ty>> {
        let ty_either_l: Vec<Either<Ty, Ty>> = tyl
            .iter()
            .map(|ty| match freshen_inside_ty(env, ty.clone()) {
                Some(ty) => Either::Left(ty),
                None => Either::Right(ty.clone()),
            })
            .collect();
        if ty_either_l.iter().all(Either::is_right) {
            None
        } else {
            Some(ty_either_l.into_iter().map(Either::into_inner).collect())
        }
    };
    let default = || None;
    let saved_env = env.clone();
    let res: Option<Ty> = (|| {
        let ty = typing_env::expand_type(env, ty);
        let r = get_reason(&ty).clone();
        match get_node(&ty) {
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tdynamic(_)
            | Ty_::Tprim(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_) => default(),
            Ty_::Tgeneric(_) => default(),
            Ty_::Tdependent(..) => default(),
            // Nullable is covariant
            Ty_::Toption(ty) => {
                let ty = freshen_inside_ty(env, ty.clone())?;
                Some(mk((r, Ty_::Toption(ty))))
            }
            Ty_::Tunion(tyl) => {
                let tyl = freshen_inside_tyl(env, tyl)?;
                Some(mk((r, Ty_::Tunion(tyl))))
            }
            Ty_::Tintersection(tyl) => {
                let tyl = freshen_inside_tyl(env, tyl)?;
                Some(inter::intersect_list(env, r, &tyl))
            }
            // Tuples are covariant
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            }) => {
                let t_required: Vec<Ty> = t_required.iter().map(|ty| freshen_ty(env, ty)).collect();
                let t_optional: Vec<Ty> = t_optional.iter().map(|ty| freshen_ty(env, ty)).collect();
                let t_extra = match t_extra {
                    TupleExtra::Tsplat(t_splat) => {
                        let t_splat = freshen_ty(env, t_splat);
                        TupleExtra::Tsplat(t_splat)
                    }
                    TupleExtra::Tvariadic(t_variadic) => {
                        let t_variadic = freshen_ty(env, t_variadic);
                        TupleExtra::Tvariadic(t_variadic)
                    }
                };
                Some(mk((
                    r,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: t_optional,
                        extra: t_extra,
                    }),
                )))
            }
            // Shape data is covariant
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields: fdm,
            })) => {
                let fdm =
                    shape_field_map::map_env(|env: &mut Env, ty: Ty| freshen_ty(env, &ty), env, fdm.clone());
                // TODO(shapes) should freshening impact unknown type?
                Some(mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: shape_kind.clone(),
                        fields: fdm,
                    })),
                )))
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                let ss_elems: Vec<Ty> = ss_elems.iter().map(|ty| freshen_ty(env, ty)).collect();
                Some(mk((r, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })))))
            }
            // Functions are covariant in return type, contravariant in parameter types
            Ty_::Tfun(ft) => {
                let ft_ret = freshen_ty(env, &ft.ret);
                let ft_params: Vec<FunParam> = ft
                    .params
                    .iter()
                    .map(|p| {
                        let fp_type = freshen_ty(env, &p.type_);
                        FunParam {
                            type_: fp_type,
                            ..p.clone()
                        }
                    })
                    .collect();
                Some(mk((
                    r,
                    Ty_::Tfun(std::rc::Rc::new(FunType {
                        ret: ft_ret,
                        params: ft_params,
                        ..FunType::clone(&ft)
                    })),
                )))
            }
            Ty_::Tnewtype(name, tyl, _) if tyl.len() == 1 && name == sn::classes::SUPPORT_DYN => {
                let ty = freshen_inside_ty(env, tyl[0].clone())?;
                Some(make_type::supportdyn(r, ty))
            }
            Ty_::Tnewtype(name, tyl, ty_bound) => {
                if tyl.is_empty() {
                    default()
                } else {
                    match typing_env::get_typedef(env, name) {
                        decl_entry::T::Found(td) => match &td.as_constraint {
                            None => default(),
                            Some(ty) => match ty.node_ref() {
                                d::Ty_::Tgeneric(_) => default(),
                                _ => {
                                    let tparams = typing_env::get_class_or_typedef_tparams(env, name);
                                    if tparams.is_empty() {
                                        default()
                                    } else {
                                        let variancel: Vec<Variance> =
                                            tparams.iter().map(|t| t.variance).collect();
                                        let tyl = freshen_tparams(env, &variancel, tyl)?;
                                        Some(mk((r, Ty_::Tnewtype(name.clone(), tyl, ty_bound.clone()))))
                                    }
                                }
                            },
                        },
                        _ => default(),
                    }
                }
            }
            Ty_::Tclass((p, cid), e, tyl) => {
                if tyl.is_empty() {
                    default()
                } else {
                    let tparams = typing_env::get_class_or_typedef_tparams(env, cid);
                    if tparams.is_empty() {
                        default()
                    } else {
                        let variancel: Vec<Variance> = tparams.iter().map(|t| t.variance).collect();
                        let tyl = freshen_tparams(env, &variancel, tyl)?;
                        Some(mk((r, Ty_::Tclass((p.clone(), cid.clone()), e.clone(), tyl))))
                    }
                }
            }
            Ty_::TvecOrDict(ty1, ty2) => {
                let ty1 = freshen_ty(env, ty1);
                let ty2 = freshen_ty(env, ty2);
                Some(mk((r, Ty_::TvecOrDict(ty1, ty2))))
            }
            Ty_::Tvar(_) => default(),
            Ty_::Taccess(TaccessType(ty, ids)) => {
                let ty = freshen_ty(env, ty);
                Some(mk((r, Ty_::Taccess(TaccessType(ty, ids.clone())))))
            }
            Ty_::TclassPtr(ty) => {
                let ty = freshen_ty(env, ty);
                // TODO(T199606542) Matches classname but does it actually make sense
                // to freshen class pointer? This will disappear when we move to direct
                // strings
                Some(mk((r, Ty_::TclassPtr(ty))))
            }
        }
    })();
    if res.is_none() {
        *env = saved_env;
    }
    res
}

fn freshen_ty(env: &mut Env, ty: &Ty) -> Ty {
    if t_utils::is_tyvar_error(env, ty) {
        typing_env::fresh_type_error(env, pos_or_decl::unsafe_to_raw_pos(get_pos(ty)))
    } else {
        typing_env::fresh_type_invariant(env, pos_or_decl::unsafe_to_raw_pos(get_pos(ty)))
    }
}

fn freshen_tparams(env: &mut Env, variancel: &[Variance], tyl: &[Ty]) -> Option<Vec<Ty>> {
    if variancel.iter().all(|v| *v == Variance::Invariant) {
        None
    } else {
        /// The last types are freshened first, as in OCaml.
        fn freshen_tparams_(env: &mut Env, variancel: &[Variance], tyl: &[Ty]) -> Vec<Ty> {
            match (variancel, tyl) {
                ([], []) => vec![],
                ([variance, variancel @ ..], [ty, tyl @ ..]) => {
                    let mut tyl = freshen_tparams_(env, variancel, tyl);
                    let ty = if *variance == Variance::Invariant {
                        ty.clone()
                    } else {
                        freshen_ty(env, ty)
                    };
                    tyl.insert(0, ty);
                    tyl
                }
                _ => tyl.to_vec(),
            }
        }
        Some(freshen_tparams_(env, variancel, tyl))
    }
}

pub fn bind(env: &mut Env, var: tvid::T, ty: Ty) -> Option<typing_error::T> {
    let old_env = typing_env::old_env_for_log("bind", None, env);
    // If there has been a use of this type variable that led to an "unknown type"
    // error (e.g. method invocation), then record this in the reason info. We
    // can make use of this for linters and code mods that suggest annotations
    let ty = {
        let env: &Env = env;
        map_reason(ty, |r| {
            if typing_env::get_tyvar_eager_solve_fail(env, var) {
                typing_reason::solve_fail(typing_reason::to_pos(&r))
            } else {
                r
            }
        })
    };
    // Remember the T::Tx involving this variable before we erase that from
    // the env.
    let tconsts = typing_env::get_tyvar_type_consts(env, var);
    // Update the variance
    typing_env::update_variance_after_bind(env, var, &ty);
    // Unify the variable
    let (ty, var_in_ty_err_opt) = utils::err_if_var_in_ty_pure(env, var, ty);
    typing_env::add(env, None, var, ty.clone());
    // Make sure we don't project from this variable if it is bound to
    // nothing, as it will lead to type holes.
    let proj_ty_err_opt = if t_utils::is_tyvar_error(env, &ty) {
        None
    // (The OCaml asks `is_nothing` first; it has no effect: the emptiness of
    // `tconsts`, usual, is tested first.)
    } else if !tconsts.is_empty() && t_utils::is_nothing(env, &ty) {
        // `S_map.choose`: the smallest binding.
        let (_, ((proj_pos, tconst_name), _)) = tconsts.get_min().expect("Not_found");
        let pos = typing_env::get_tyvar_pos(env, var);
        Some(typing_error::primary(primary::T::Unresolved_tyvar_projection {
            pos,
            tconst_name: tconst_name.clone(),
            proj_pos: proj_pos.clone(),
        }))
    } else {
        None
    };
    let ty_err_opt = option_merge(var_in_ty_err_opt, proj_ty_err_opt, typing_error::both);
    typing_env::log_env_change_opt("bind", None, old_env, env);
    ty_err_opt
}

/// Solve type variable var by assigning it to the union of its lower bounds.
/// If freshen=true, first freshen the covariant and contravariant components of
/// the bounds.
fn bind_to_lower_bound(
    freshen: bool,
    env: &mut Env,
    r: Reason,
    var: tvid::T,
    lower_bounds: &ity_set::T,
) -> Option<typing_error::T> {
    let old_env = typing_env::old_env_for_log("bind_to_lower_bound", None, env);
    let ty_err_opt = if ity_set::exists(is_constraint_type, lower_bounds) {
        None
    } else {
        let lower_bounds = utils::remove_tyvar_from_lower_bounds(env, var, lower_bounds);
        let lower_bounds = utils::filter_locl_types(&lower_bounds);
        let ty = t_utils::union_list(env, None, r, &ty_set::elements(&lower_bounds));
        // Freshen components of the types in the union wrt their variance.
        // For example, if we have
        //   Cov<C>, Contra<D> <: v
        // then we actually construct the union
        //   Cov<#1> | Contra<#2> with C <: #1 and #2 <: D
        let (freshen_ty_err, ty) = if freshen {
            match freshen_inside_ty(env, ty.clone()) {
                None => (None, ty),
                Some(newty) => {
                    // In theory, the following subtype would only fail if the lower bound
                    // was already in conflict with another bound. However we don't
                    // add such conflicting bounds to avoid cascading errors, so in theory,
                    // the following subtype calls should not fail, and the error callback
                    // should not matter.
                    let on_error = Some(reasons_callback::unify_error_at(
                        typing_env::get_tyvar_pos(env, var),
                    ));
                    let ty_err_opt =
                        t_utils::sub_type(env, None, None, None, None, ty, newty.clone(), on_error);
                    (ty_err_opt, newty)
                }
            }
        } else {
            (None, ty)
        };
        // If any of the components of the union are type variables, then remove
        // var from their upper bounds. Why? Because if we construct
        //   v1 , ... , vn , t <: var
        // for type variables v1, ..., vn and non-type variable t
        // then necessarily we must have var as an upper bound on each of vi
        // so after binding var we end up with redundant bounds
        //   vi <: v1 | ... | vn | t
        for ty in lower_bounds.iter() {
            let ty = typing_env::expand_type(env, ty.clone());
            match get_node(&ty) {
                Ty_::Tvar(v) => typing_env::remove_tyvar_upper_bound(env, *v, var),
                _ => {}
            }
        }
        // In autocomplete mode, we do not solve to nothing, as it makes a lot
        // of checks in the autocompletion fail for bad reasons (especially
        // around invariant generics. Leave them be to try to get leave more
        // flexibility to type filers
        let autocomplete_mode = env.genv.tcopt.tco_autocomplete_mode;
        if autocomplete_mode && t_utils::is_nothing(env, &ty) {
            freshen_ty_err
        } else {
            // Now actually make the assignment var := ty, and remove var from tvenv
            let bind_ty_err = bind(env, var, ty);
            option_merge(freshen_ty_err, bind_ty_err, typing_error::both)
        }
    };
    typing_env::log_env_change_opt("bind_to_lower_bound", None, old_env, env);
    ty_err_opt
}

fn bind_to_upper_bound(
    env: &mut Env,
    r: Reason,
    var: tvid::T,
    upper_bounds: &ity_set::T,
) -> Option<typing_error::T> {
    let old_env = typing_env::old_env_for_log("bind_to_upper_bound", None, env);
    let ty_err_opt = if ity_set::exists(is_constraint_type, upper_bounds) {
        None
    } else {
        let upper_bounds = utils::remove_tyvar_from_upper_bounds(env, var, upper_bounds);
        let upper_bounds = utils::filter_locl_types(&upper_bounds);
        let ty = inter::intersect_list(env, r, &ty_set::elements(&upper_bounds));
        // If ty is a variable (in future, if any of the types in the list are variables),
        // then remove var from their lower bounds. Why? Because if we construct
        //   var <: v1 , ... , vn , t
        // for type variables v1 , ... , vn and non-type variable t
        // then necessarily we must have var as a lower bound on each of vi
        // so after binding var we end up with redundant bounds
        //   v1 & ... & vn & t <: vi
        let ty = typing_env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tvar(v) => typing_env::remove_tyvar_lower_bound(env, *v, var),
            _ => {}
        }
        bind(env, var, ty)
    };
    typing_env::log_env_change_opt("bind_to_upper_bound", None, old_env, env);
    ty_err_opt
}

/// Is the outer skeleton of the types the same (everything that isn't a nested type)?
/// e.g. C<string> same as  C<int>,
///      dict<string,bool> same as dict<int,string>
///      shape('a' => int) same as shape('a' => bool)
/// but shape('a' => int) not same as shape('b' => int)
/// shape(?'a' => int) not same as shape('a' => int)
///
/// Expected invariant:
///   if ty_equal_shallow ty1 ty2
///   then freshen_inside_ty ty1 is identical to freshen_inside_ty ty2
///   up to a choice of fresh type variables.
/// (Or: there is some instantiation of the fresh type variables that
/// makes freshen_inside_ty ty1 and freshen_inside_ty ty2 the same.)
fn ty_equal_shallow(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    // The environments of the expansions are not returned.
    let mut env = env.clone();
    let ty1 = typing_env::expand_type(&mut env, ty1.clone());
    let ty2 = typing_env::expand_type(&mut env.clone(), ty2.clone());
    let env = &env;
    if t_utils::is_tyvar_error(env, &ty1) && t_utils::is_tyvar_error(env, &ty2) {
        true
    } else {
        match (get_node(&ty1), get_node(&ty2)) {
            (Ty_::Tany(_), Ty_::Tany(_))
            | (Ty_::Tnonnull, Ty_::Tnonnull)
            | (Ty_::Tdynamic(_), Ty_::Tdynamic(_))
            | (Ty_::Ttuple(_), Ty_::Ttuple(_)) => true,
            (Ty_::Tprim(p1), Ty_::Tprim(p2)) => aast_defs::equal_tprim(*p1, *p2),
            (Ty_::Tclass(x_sub, exact_sub, _), Ty_::Tclass(x_super, exact_super, _)) => {
                x_sub.1 == x_super.1 && exact_equal(exact_sub, exact_super)
            }
            (Ty_::Tfun(fty1), Ty_::Tfun(fty2)) => typing_defs_flags::fun::equal(fty1.flags, fty2.flags),
            (
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: shape_kind1,
                    fields: fdm1,
                })),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: shape_kind2,
                    fields: fdm2,
                })),
            ) => {
                // The arguments of `Bool.equal` are evaluated right to left.
                let is_nothing2 = t_utils::is_nothing(env, shape_kind2);
                let is_nothing1 = t_utils::is_nothing(env, shape_kind1);
                is_nothing1 == is_nothing2
                    // `List.equal` on `ShapeFieldMap.elements`
                    && fdm1.len() == fdm2.len()
                    && fdm1.iter().zip(fdm2.iter()).all(|((k1, v1), (k2, v2))| {
                        t_shape_field::equal(&k1.0, &k2.0) && v1.optional == v2.optional
                    })
            }
            (Ty_::Tnewtype(n1, _, _), Ty_::Tnewtype(n2, _, _)) => n1 == n2,
            (Ty_::Tdependent(dep1, _), Ty_::Tdependent(dep2, _)) => dep1 == dep2,
            _ => false,
        }
    }
}

/// The definition that the one of the `.mli` shadows (see the module
/// documentation).
mod with_freshen {
    use super::*;

    pub(super) fn try_bind_to_equal_bound(
        freshen: bool,
        env: &mut Env,
        r: Reason,
        var: tvid::T,
    ) -> Option<typing_error::T> {
        if typing_env::tyvar_is_solved(env, var) {
            None
        } else {
            let old_env = typing_env::old_env_for_log("bind_to_equal_bound", None, env);
            utils::remove_tyvar_from_bounds(env, var);
            let is_null = |ity: &InternalType| match ity {
                InternalType::LoclType(ty) => match get_node(ty) {
                    Ty_::Tprim(Tprim::Tnull) => true,
                    _ => false,
                },
                _ => false,
            };
            let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
            let has_null_lower_bound = ity_set::exists(is_null, &lower_bounds);
            let expand_all = |strip_supportdyn: bool,
                              env: &mut Env,
                              tyset: &ity_set::T|
             -> (ity_set::T, ity_set::T) {
                let mut res = ity_set::empty();
                let mut sd_res = ity_set::empty();
                for ty in tyset.iter() {
                    let ty = typing_env::expand_internal_type(env, ty.clone());
                    match ty {
                        InternalType::LoclType(ty) if strip_supportdyn => {
                            let (_, stripped_ty) = t_utils::strip_supportdyn(env, ty.clone());
                            res = ity_set::add(InternalType::LoclType(stripped_ty.clone()), &res);
                            sd_res = ity_set::add(InternalType::LoclType(ty), &sd_res);
                            if has_null_lower_bound {
                                res = ity_set::add(
                                    InternalType::LoclType(make_type::nullable(r.clone(), stripped_ty)),
                                    &res,
                                );
                            }
                        }
                        ty => res = ity_set::add(ty, &res),
                    }
                }
                (res, sd_res)
            };
            let (lower_bounds, sd_lower_bounds) = expand_all(true, env, &lower_bounds);
            let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
            let (upper_bounds, _) = expand_all(false, env, &upper_bounds);
            let equal_bounds = ity_set::inter(&lower_bounds, &upper_bounds);
            let equal_bounds = if ity_set::is_empty(&equal_bounds) {
                ity_set::inter(&sd_lower_bounds, &upper_bounds)
            } else {
                equal_bounds
            };
            let ty_err_opt = match ity_set::choose_opt(&equal_bounds) {
                Some(InternalType::LoclType(ty)) => bind(env, var, ty),
                Some(InternalType::ConstraintType(_)) | None => {
                    if !freshen {
                        None
                    } else {
                        // Search for lower bound and upper bound pair that shallowly match.
                        // Then freshen the inner types on the matched type. We then want
                        // to make var equal to the matched type so we add the constraints
                        //  var <: matched_ty and matched_ty <: var
                        // Finally we bind var to matched_ty
                        let shallow_match = {
                            let env: &Env = env;
                            ity_set::find_first_opt(
                                |lower_bound| {
                                    ity_set::exists(
                                        |upper_bound| match (lower_bound, upper_bound) {
                                            (
                                                InternalType::LoclType(lower_bound),
                                                InternalType::LoclType(upper_bound),
                                            ) => ty_equal_shallow(env, lower_bound, upper_bound),
                                            _ => false,
                                        },
                                        &upper_bounds,
                                    )
                                },
                                &lower_bounds,
                            )
                        };
                        match shallow_match {
                            Some(InternalType::LoclType(shallow_match)) => {
                                let ty = freshen_inside_ty(env, shallow_match.clone())
                                    .unwrap_or(shallow_match);
                                let var_ty = mk((r.clone(), Ty_::Tvar(var)));
                                // In theory, the following subtype would only fail if the shallow match
                                // we've found was already in conflict with another bound. However we don't
                                // add such conflicting bounds to avoid cascading errors, so in theory,
                                // the following subtype calls should not fail, and the error callback
                                // should not matter.
                                let on_error = Some(reasons_callback::unify_error_at(
                                    typing_env::get_tyvar_pos(env, var),
                                ));
                                let ty_sub_err_opt = t_utils::sub_type(
                                    env,
                                    None,
                                    None,
                                    None,
                                    None,
                                    ty.clone(),
                                    var_ty.clone(),
                                    on_error.clone(),
                                );
                                let ty_sup_err_opt = t_utils::sub_type(
                                    env,
                                    None,
                                    None,
                                    None,
                                    None,
                                    var_ty,
                                    ty.clone(),
                                    on_error,
                                );
                                let bind_err_opt = bind(env, var, ty);
                                typing_error::multiple_opt(
                                    [ty_sub_err_opt, ty_sup_err_opt, bind_err_opt]
                                        .into_iter()
                                        .flatten()
                                        .collect(),
                                )
                            }
                            _ => None,
                        }
                    }
                }
            };
            typing_env::log_env_change_opt("bind_to_equal_bound", None, old_env, env);
            ty_err_opt
        }
    }
}

/// Always solve a type variable.
/// We are here because we eagerly solve a type variable to see
/// whether certain operations are allowed on the type (e.g. a  method call).
/// Therefore, we always force to the lower bounds (even contravariant variables),
/// because it produces a "more specific" type, which is more likely to support
/// the operation which we eagerly solved for in the first place.
///
/// During autocompletion, if the set of lower bounds is empty and the
/// variable appears contravariantly, try an upper bound.
fn always_solve_tyvar_down(
    freshen: bool,
    env: &mut Env,
    r: Reason,
    var: tvid::T,
) -> Option<typing_error::T> {
    let autocomplete_mode = env.genv.tcopt.tco_autocomplete_mode;
    // If there is a type that is both a lower and upper bound, force to that type
    let ty_err_opt1 = with_freshen::try_bind_to_equal_bound(freshen, env, r.clone(), var);
    if typing_env::tyvar_is_solved(env, var) {
        ty_err_opt1
    } else {
        let r = if typing_reason::predicates::is_none(&r) {
            typing_reason::witness(typing_env::get_tyvar_pos(env, var))
        } else {
            r
        };
        let ty_err_opt2 = {
            let (to_lower, bounds) = {
                let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
                if autocomplete_mode {
                    let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
                    // Filtering mixed and support_dyn<mixed>
                    let mut acc = ity_set::empty();
                    for ity in upper_bounds.iter() {
                        match ity {
                            InternalType::ConstraintType(_) => acc = ity_set::add(ity.clone(), &acc),
                            InternalType::LoclType(lty) => {
                                let (_, lty) = t_utils::strip_supportdyn(env, lty.clone());
                                match get_node(&lty) {
                                    Ty_::Toption(topt) => match get_node(topt) {
                                        Ty_::Tnonnull => {}
                                        _ => acc = ity_set::add(ity.clone(), &acc),
                                    },
                                    _ => acc = ity_set::add(ity.clone(), &acc),
                                }
                            }
                        }
                    }
                    let upper_bounds = acc;
                    if typing_env::get_tyvar_appears_contravariantly(env, var)
                        && ity_set::is_empty(&lower_bounds)
                        && !ity_set::is_empty(&upper_bounds)
                    {
                        (false, upper_bounds)
                    } else {
                        (true, lower_bounds)
                    }
                } else {
                    (true, lower_bounds)
                }
            };
            // We cannot do more on (<expr#1> as C) than on simply C,
            // so replace expression-dependent types with their bound.
            // This avoids solving to a type so specific that it ends
            // up hurting completeness.
            if to_lower {
                let bounds = {
                    let env: &Env = env;
                    // `ITySet.map`, whose function gives back the elements it
                    // does not change.
                    ity_set::map_phys(
                        |ity| match ity {
                            InternalType::LoclType(lty) => {
                                let lty = typing_env::expand_type(&mut env.clone(), lty.clone());
                                match get_node(&lty) {
                                    Ty_::Tdependent(_, bnd) => Some(InternalType::LoclType(bnd.clone())),
                                    _ => None,
                                }
                            }
                            _ => None,
                        },
                        &bounds,
                    )
                };
                bind_to_lower_bound(freshen, env, r.clone(), var, &bounds)
            } else {
                bind_to_upper_bound(env, r.clone(), var, &bounds)
            }
        };
        let ety = typing_env::expand_var(env, r.clone(), var);
        match get_node(&ety) {
            Ty_::Tvar(var_) if !tvid::equal(var, *var_) => {
                let ty_err_opt3 = always_solve_tyvar_down(freshen, env, r, var);
                typing_error::multiple_opt(
                    [ty_err_opt1, ty_err_opt2, ty_err_opt3]
                        .into_iter()
                        .flatten()
                        .collect(),
                )
            }
            _ => option_merge(ty_err_opt1, ty_err_opt2, typing_error::both),
        }
    }
}

/// Use the variance information about a type variable to force a solution.
///   (1) If the type variable is bounded by t1, ..., tn <: v and it appears only
///   covariantly or not at all in the expression type then
///   we can minimize it i.e. set v := t1 | ... | tn.
///   (2) If the type variable is bounded by v <: t1, ..., tn and it appears only
///   contravariantly in the expression type then we can maximize it. Ideally we
///   would use an intersection v := t1 & ... & tn so for now we only solve
///   if there is a single upper bound.
///   (3) If the type variable is bounded by t1, ..., tm <: v <: u1, ..., un and
///   u1 & ... & un == t1 | ... | tm then we can set v to either of these
///   equivalent types.  Because we don't have intersections, for now we check if
///   there exist i, j such that uj <: ti, which implies ti == uj and allows
///   us to set v := ti.
fn solve_tyvar_wrt_variance(env: &mut Env, r: Reason, var: tvid::T) -> Option<typing_error::T> {
    if typing_env::tyvar_is_solved(env, var) {
        None
    } else {
        let r = if typing_reason::predicates::is_none(&r) {
            typing_reason::witness(typing_env::get_tyvar_pos(env, var))
        } else {
            r
        };
        let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
        let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
        let appears_covariantly = typing_env::get_tyvar_appears_covariantly(env, var);
        let appears_contravariantly = typing_env::get_tyvar_appears_contravariantly(env, var);
        match (appears_covariantly, appears_contravariantly) {
            (true, false) | (false, false) => {
                // As in Local Type Inference by Pierce & Turner, if type variable does
                // not appear at all, or only appears covariantly, solve to lower bound.
                // If there are no lower bounds, and we've got type constant projections
                // on the type variable, then solve to the upper bound anyway, hoping that
                // this resolves the projections.
                if ity_set::is_empty(&lower_bounds)
                    && !typing_env::get_tyvar_type_consts(env, var).is_empty()
                {
                    bind_to_upper_bound(env, r, var, &upper_bounds)
                } else {
                    bind_to_lower_bound(false, env, r, var, &lower_bounds)
                }
            }
            (false, true) => {
                // As in Local Type Inference by Pierce & Turner, if type variable
                // appears only contravariantly, solve to upper bound
                bind_to_upper_bound(env, r, var, &upper_bounds)
            }
            (true, true) => {
                // Not ready to solve yet!
                None
            }
        }
    }
}

pub fn solve_to_equal_bound_or_wrt_variance(
    env: &mut Env,
    r: Reason,
    var: tvid::T,
) -> Option<typing_error::T> {
    /// The first OCaml definition, which this one shadows.
    fn solve_to_equal_bound_or_wrt_variance(
        env: &mut Env,
        r: Reason,
        var: tvid::T,
    ) -> Option<typing_error::T> {
        {
            let env: &Env = env;
            typing_log::log_with_level(env, "prop", 2, || {
                typing_log::log_types(
                    &typing_reason::to_pos(&r),
                    env,
                    &[typing_log::LogStructure::LogHead(
                        format!(
                            "Typing_subtype.solve_to_equal_bound_or_wrt_variance #{}",
                            tvid::show(var)
                        ),
                        vec![],
                    )],
                )
            });
        }
        // If there is a type that is both a lower and upper bound, force to that type
        let ty_err_opt1 = with_freshen::try_bind_to_equal_bound(false, env, r.clone(), var);
        let ty_err_opt2 = solve_tyvar_wrt_variance(env, r, var);
        option_merge(ty_err_opt1, ty_err_opt2, typing_error::both)
    }
    // `solve_until_concrete_ty env ty_errs v`; `ty_errs` is the OCaml list,
    // reversed.
    let mut ty_errs: Vec<typing_error::T> = vec![];
    let mut v = var;
    loop {
        match solve_to_equal_bound_or_wrt_variance(env, r.clone(), v) {
            Some(ty_err) => ty_errs.push(ty_err),
            None => {}
        }
        let ety = typing_env::expand_var(env, r.clone(), v);
        match get_node(&ety) {
            Ty_::Tvar(v_) if !tvid::equal(v, *v_) => v = *v_,
            _ => {
                ty_errs.reverse();
                return typing_error::multiple_opt(ty_errs);
            }
        }
    }
}

fn always_solve_tyvar(env: &mut Env, r: Reason, var: tvid::T) -> Option<typing_error::T> {
    // Shadow type variables are never solved — they exist only to accumulate
    // upper-bound constraints for dynamic inference.
    if typing_env::is_shadow_tyvar(env, var) {
        None
    } else {
        let ty_err_opt1 = solve_to_equal_bound_or_wrt_variance(env, r.clone(), var);
        let ty_err_opt2 = always_solve_tyvar_down(false, env, r, var);
        option_merge(ty_err_opt1, ty_err_opt2, typing_error::both)
    }
}

/// Force solve all remaining unsolved type variables
pub fn solve_all_unsolved_tyvars(env: &mut Env) -> Option<typing_error::T> {
    let old_env = typing_env::old_env_for_log("solve_all_unsolved_tyvars", None, env);
    // The OCaml list of errors, reversed.
    let mut ty_errs: Vec<typing_error::T> = vec![];
    for var in typing_env::get_all_tyvars(env) {
        // Skip shadow type variables — they collect constraints but are never solved
        if typing_env::is_shadow_tyvar(env, var) {
        } else {
            match always_solve_tyvar(env, typing_reason::none(), var) {
                Some(ty_err) => ty_errs.push(ty_err),
                None => {}
            }
        }
    }
    typing_env::log_env_change_opt("solve_all_unsolved_tyvars", None, old_env, env);
    log_remaining_prop(env);
    ty_errs.reverse();
    typing_error::multiple_opt(ty_errs)
}

fn is_tyvar_error(tvid: tvid::T, env: &Env) -> bool {
    typing_inference_env::is_error(&env.inference_env, tvid)
}

/// Expand an already-solved type variable, and solve an unsolved type variable
/// by binding it to the union of its lower bounds, with covariant and contravariant
/// components of the type suitably "freshened". For example,
///    vec<C> <: #1
/// will be solved by
///    #1 := vec<#2>  where C <: #2
/// The optional `default` parameter is used to solve a type variable
/// if `widen_concrete_type` does not produce a result.
pub fn expand_type_and_solve(
    env: &mut Env,
    freshen: Option<bool>,
    description_of_expected: &str,
    p: Pos,
    ty: Ty,
) -> (Option<typing_error::T>, Ty) {
    let freshen = freshen.unwrap_or(true);
    // Not in the OCaml: when `simplify_unions` gives `ty` back without calling
    // `on_tyvar` (see `typing_union::is_own_union`), nothing is solved, the
    // expansion of `ty` is itself and the position set below is restored:
    // the result is `ty`, with no error, and the environment is unchanged.
    if env.log_levels.is_empty() && crate::typing_union::is_own_union(env, &ty) {
        return (None, ty);
    }
    // If we're checking an SDT method or function under dynamic assumptions,
    // then attempt to solve to dynamic if we're left with a type variable
    let default = if tast::is_under_dynamic_assumptions(env.checked) {
        Some(make_type::dynamic(typing_reason::witness(p.clone())))
    } else {
        None
    };
    // TODO: rather than writing to a ref cell from inside the `on_tyvar`
    // function, modify `simplify_unions` to return the accumulated result
    // from this function, if it is provided
    // (Both are the OCaml lists, reversed.)
    let mut vars_solved_to_nothing: Vec<(Reason, tvid::T)> = vec![];
    let mut ty_errs: Vec<typing_error::T> = vec![];
    let restore_pos = typing_env::set_inference_env_pos(env, Some(p.clone()));
    // From here on `*env` is the OCaml `env'`; this is the OCaml `env`.
    let env_before_solving = env.clone();
    let ety = t_utils::simplify_unions(
        env,
        None,
        Some(&mut |env: &mut Env, r: Reason, v: tvid::T| {
            let ty_err_opt = always_solve_tyvar_down(freshen, env, r.clone(), v);
            if let Some(ty_err) = ty_err_opt {
                ty_errs.push(ty_err)
            }
            let ety = typing_env::expand_var(env, r.clone(), v);
            match get_node(&ety) {
                Ty_::Tunion(tyl) if tyl.is_empty() => vars_solved_to_nothing.push((r, v)),
                _ => {}
            }
            ety
        }),
        ty,
    );
    let ety = typing_env::expand_type(env, ety);
    let (err, ty) = match (vars_solved_to_nothing.is_empty(), get_node(&ety)) {
        (false, Ty_::Tunion(tyl)) if tyl.is_empty() => {
            // The OCaml goes on with `env`, dropping `env'`.
            *env = env_before_solving;
            match default {
                Some(default_ty) => {
                    let res = t_utils::sub_type(
                        env,
                        None,
                        None,
                        None,
                        None,
                        ety.clone(),
                        default_ty.clone(),
                        Some(reasons_callback::unify_error_at(p.clone())),
                    );
                    (res, default_ty)
                }
                None => {
                    for (r, v) in vars_solved_to_nothing.iter().rev() {
                        if is_tyvar_error(*v, env) {
                        } else {
                            let ty_err = {
                                let r = r.clone();
                                typing_error::primary(primary::T::Unknown_type {
                                    expected: description_of_expected.to_string(),
                                    pos: p.clone(),
                                    reason: Lazy::new(move || {
                                        messages(typing_reason::to_string("It is unknown", &r))
                                    }),
                                })
                            };
                            ty_errs.push(ty_err);
                            typing_env::set_tyvar_eager_solve_fail(env, *v)
                        }
                    }
                    ty_errs.reverse();
                    let ty_err_opt = typing_error::multiple_opt(ty_errs);
                    let ty = typing_env::fresh_type_error(env, p.clone());
                    (ty_err_opt, ty)
                }
            }
        }
        _ => {
            // `env` is not needed any more: dropped before `restore_pos`
            // writes `env'` (while shared with it, the write would copy).
            drop(env_before_solving);
            ty_errs.reverse();
            let ty_err_opt = typing_error::multiple_opt(ty_errs);
            (ty_err_opt, ety.clone())
        }
    };
    restore_pos(env);
    (err, ty)
}

pub fn expand_type_and_solve_eq(env: &mut Env, ty: Ty) -> (Option<typing_error::T>, Ty) {
    // Not in the OCaml: as in `expand_type_and_solve`, `ty` is then the result.
    if env.log_levels.is_empty() && crate::typing_union::is_own_union(env, &ty) {
        return (None, ty);
    }
    // The OCaml list, reversed.
    let mut ty_err_opts: Vec<Option<typing_error::T>> = vec![];
    let ty = t_utils::simplify_unions(
        env,
        None,
        Some(&mut |env: &mut Env, r: Reason, v: tvid::T| {
            let ty_err_opt = with_freshen::try_bind_to_equal_bound(true, env, r.clone(), v);
            ty_err_opts.push(ty_err_opt);
            typing_env::expand_var(env, r, v)
        }),
        ty,
    );
    let ty = typing_env::expand_type(env, ty);
    let ty_err_opt = typing_error::multiple_opt(ty_err_opts.into_iter().rev().flatten().collect());
    (ty_err_opt, ty)
}

/// When applied to concrete types (typically classes), the `widen_concrete_type`
/// function should produce the largest supertype that is valid for an operation.
/// For example, if we have an expression $x->f for $x:v and exact C <: v, then
/// we widen `exact C` to `B`, if `B` is the base class from which `C` inherits
/// field f.
///
/// The `widen` function extends this to nullables and abstract types.
/// General unions have been dealt with already.
fn widen(
    env: &mut Env,
    widen_concrete_type: &mut dyn FnMut(&mut Env, Ty) -> Option<Ty>,
    ty: Ty,
) -> Ty {
    let ty_nothing = make_type::nothing(typing_reason::none());
    fn widen(
        env: &mut Env,
        widen_concrete_type: &mut dyn FnMut(&mut Env, Ty) -> Option<Ty>,
        ty_nothing: &Ty,
        ty: Ty,
    ) -> Ty {
        t_utils::map_supportdyn(env, ty, |env, ty| {
            let ty = typing_env::expand_type(env, ty);
            match get_node(&ty) {
                Ty_::Tunion(tyl) => {
                    let r = get_reason(&ty).clone();
                    widen_all(env, widen_concrete_type, ty_nothing, r, tyl)
                }
                Ty_::Toption(ty_) => {
                    let r = get_reason(&ty).clone();
                    let tyl = [make_type::null(r.clone()), ty_.clone()];
                    widen_all(env, widen_concrete_type, ty_nothing, r, &tyl)
                }
                // Don't widen the `this` type, because the field type changes up the hierarchy
                // so we lose precision
                Ty_::Tgeneric(name) if name == "this" => ty.clone(),
                // For abstract types, just widen to the bound, if possible
                Ty_::Tdependent(_, ty) => widen(env, widen_concrete_type, ty_nothing, ty.clone()),
                Ty_::Tnewtype(n, tyl, _) => {
                    let r = get_reason(&ty).clone();
                    let ty = t_utils::get_newtype_super(env, r, n, tyl);
                    widen(env, widen_concrete_type, ty_nothing, ty)
                }
                _ => {
                    let ty_opt = widen_concrete_type(env, ty.clone());
                    ty_opt.unwrap_or_else(|| ty_nothing.clone())
                }
            }
        })
    }
    fn widen_all(
        env: &mut Env,
        widen_concrete_type: &mut dyn FnMut(&mut Env, Ty) -> Option<Ty>,
        ty_nothing: &Ty,
        r: Reason,
        tyl: &[Ty],
    ) -> Ty {
        let tyl: Vec<Ty> = tyl
            .iter()
            .map(|ty| widen(env, widen_concrete_type, ty_nothing, ty.clone()))
            .collect();
        typing_union::union_list(env, None, r, &tyl)
    }
    widen(env, widen_concrete_type, &ty_nothing, ty)
}

fn is_nothing(env: &Env, ty: &Ty) -> bool {
    t_utils::is_sub_type_ignore_generic_params(env, ty, &make_type::nothing(typing_reason::none()))
}

/// Using the `widen_concrete_type` function to compute an upper bound,
/// narrow the constraints on a type that are valid for an operation.
/// For example, if we have an expression $x->f for $x:#1 and exact C <: #1, then
/// we can add #1 <: B if C inherits the property f from base class B.
/// Likewise, if we have an expression $x[3] for $x:#2 and vec<string> <: #2, then
/// we can add #2 <: KeyedCollection<int,#3> because that is the largest type
/// consistent with vec for which indexing is valid.
///
/// Note that if further information arises on the type variable, then
/// this approach is not complete. For example, we might have an unrelated
/// exact A <: #1, for which A does not inherit from base class B.
///
/// But in general, narrowing is a useful technique for delaying the complete
/// solving of a constraint whilst supporting checking of operations such as
/// member access and array indexing.
///
/// The optional `default` parameter is used to solve a type variable
/// if `widen_concrete_type` does not produce a result.
pub fn expand_type_and_narrow(
    env: &mut Env,
    default: Option<Ty>,
    allow_nothing: Option<bool>,
    force_solve: Option<bool>,
    description_of_expected: &str,
    mut widen_concrete_type: impl FnMut(&mut Env, Ty) -> Option<Ty>,
    p: Pos,
    ty: Ty,
) -> (Option<typing_error::T>, Ty) {
    let allow_nothing = allow_nothing.unwrap_or(false);
    let force_solve = force_solve.unwrap_or(true);
    // If we're checking an SDT method or function under dynamic assumptions,
    // then attempt to solve to dynamic if we're left with a type variable
    let default = if default.is_some() {
        default
    } else if tast::is_under_dynamic_assumptions(env.checked) {
        Some(make_type::dynamic(typing_reason::witness(p.clone())))
    } else {
        None
    };
    let (ty_err_opt, ty) = {
        let (ty_err_opt1, ty) = expand_type_and_solve_eq(env, ty);
        // Deconstruct the type into union elements (if it's a union). For variables,
        // take the lower bounds. If there are no variables, then we have a concrete
        // type so just return expanded type
        let mut has_tyvar = false;
        let mut seen_tyvars = tvid::set::T::new();
        // Simplify unions in ty, but when we encounter a type variable in the process,
        // recursively replace it with the union of its lower bounds, effectively getting
        // rid of all unsolved type variables in the union.
        let concretized_ty = typing_union::simplify_unions(
            env,
            None,
            Some(&mut |env: &mut Env, r: Reason, v: tvid::T| {
                has_tyvar = true;
                if seen_tyvars.contains(&v) {
                    make_type::nothing(r)
                } else {
                    seen_tyvars.insert(v);
                    let lower_bounds = ty_set::elements(&utils::filter_locl_types(
                        &typing_env::get_tyvar_lower_bounds(env, v),
                    ));
                    typing_union::union_list(env, None, r, &lower_bounds)
                }
            }),
            ty.clone(),
        );
        if !has_tyvar {
            (ty_err_opt1, ty)
        } else {
            let widened_ty = widen(env, &mut widen_concrete_type, concretized_ty);
            let (ty_err_opt2, ty) = match (
                (!allow_nothing) && is_nothing(env, &widened_ty),
                default,
                widened_ty,
            ) {
                (true, None, _) => {
                    if force_solve {
                        expand_type_and_solve(env, None, description_of_expected, p.clone(), ty)
                    } else {
                        (None, ty)
                    }
                }
                (true, Some(widened_ty), _) | (false, _, widened_ty) => {
                    // We really don't want to just guess `nothing` if none of the types can be widened
                    // (The OCaml goes on with this environment if `sub_type` fails.)
                    let env_before_sub_type = env.clone();
                    let res = t_utils::sub_type(
                        env,
                        None,
                        None,
                        None,
                        None,
                        ty.clone(),
                        widened_ty.clone(),
                        Some(reasons_callback::unify_error_at(p.clone())),
                    );
                    match res {
                        None => {
                            let supportdyn = t_utils::is_supportdyn(env, &ty);
                            let res2 = if supportdyn {
                                t_utils::sub_type(
                                    env,
                                    None,
                                    None,
                                    None,
                                    None,
                                    widened_ty.clone(),
                                    make_type::supportdyn_mixed(typing_reason::witness(p.clone())),
                                    Some(reasons_callback::unify_error_at(p.clone())),
                                )
                            } else {
                                None
                            };
                            (res2, widened_ty)
                        }
                        Some(_) => {
                            *env = env_before_sub_type;
                            if force_solve {
                                expand_type_and_solve(env, None, description_of_expected, p.clone(), ty)
                            } else {
                                (None, ty)
                            }
                        }
                    }
                }
            };
            let ty_err_opt = typing_error::union_opt(
                [ty_err_opt1, ty_err_opt2].into_iter().flatten().collect(),
            );
            (ty_err_opt, ty)
        }
    };
    let ty = typing_env::expand_type(env, ty);
    (ty_err_opt, ty)
}

/// Solve type variables on top of stack, without losing completeness (by using
/// their variance), and pop variables off the stack
pub fn close_tyvars_and_solve(env: &mut Env) -> Option<typing_error::T> {
    let old_env = typing_env::old_env_for_log("close_tyvars_and_solve", None, env);
    let tyvars = typing_env::get_current_tyvars(env);
    typing_env::close_tyvars(env);
    // The OCaml list of errors, reversed.
    let mut ty_errs: Vec<typing_error::T> = vec![];
    for tyvar in tyvars {
        match solve_to_equal_bound_or_wrt_variance(env, typing_reason::none(), tyvar) {
            Some(ty_err) => ty_errs.push(ty_err),
            None => {}
        }
    }
    ty_errs.reverse();
    let ty_err_opt = typing_error::multiple_opt(ty_errs);
    typing_env::log_env_change_opt("close_tyvars_and_solve", None, old_env, env);
    ty_err_opt
}

/// Currently, simplify_subtype doesn't look at bounds on type variables.
/// Let's at least notice when these bounds imply an equality.
///
/// Non-side-effecting test for subtypes: the solving happens in a copy of the
/// environment, which is not returned.
pub fn is_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> (bool, Option<typing_error::T>) {
    let mut env = env.clone();
    let env = &mut env;
    let (ty_err_opt1, ty1) = expand_type_and_solve_eq(env, ty1.clone());
    let (ty_err_opt2, ty2) = expand_type_and_solve_eq(env, ty2.clone());
    let ty_err_opt = option_merge(ty_err_opt1, ty_err_opt2, typing_error::both);
    (t_utils::is_sub_type(env, &ty1, &ty2), ty_err_opt)
}

pub fn try_bind_to_equal_bound(env: &mut Env, v: tvid::T) -> Option<typing_error::T> {
    // The reason we pass here doesn't matter since it's used only when `freshen` is true.
    with_freshen::try_bind_to_equal_bound(false, env, typing_reason::none(), v)
}

fn bind_to_like_fresh(
    env: &mut Env,
    r: Reason,
    var: tvid::T,
    lower_bounds: ity_set::T,
    upper_bounds: ity_set::T,
) -> Ty {
    let fresh_ty =
        typing_env::fresh_type_invariant(env, pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)));
    let like_ty = make_type::locl_like(r, fresh_ty.clone());
    let _bind_ty_err = bind(env, var, like_ty.clone());
    match get_node(&fresh_ty) {
        Ty_::Tvar(var_) => {
            typing_env::set_tyvar_lower_bounds(env, *var_, lower_bounds);
            typing_env::set_tyvar_upper_bounds(env, *var_, upper_bounds);
            like_ty
        }
        _ => panic!("fresh_type_invariant did not return a Tvar"),
    }
}

/// Expand an already-solved type variable to its solution.
/// If the type variable is not yet solved, but one of its lower bounds is dynamic,
/// i.e. dynamic, t1, ..., tn <: #0 <: u1, ..., um,
/// then solve the type variable to #0 := ~#1 for fresh type variable #1, where
/// t1, ..., tn <: #1 <: u1, ..., um.
/// This is used in the strip_dynamic functions in Typing_dynamic_utils before matching the type on ~t
pub fn expand_type_for_strip_dynamic(env: &mut Env, ty: Ty) -> Ty {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tvar(var) => {
            let r = get_reason(&ty).clone();
            let var = *var;
            let is_locl_dynamic = |ty: &InternalType| match ty {
                InternalType::LoclType(t) => typing_defs::is_dynamic(t),
                _ => false,
            };
            let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
            let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
            let dynamic_is_lower_bound = ity_set::exists(is_locl_dynamic, &lower_bounds)
                && !ity_set::for_all(is_locl_dynamic, &lower_bounds);
            if dynamic_is_lower_bound {
                // We have dynamic, t1, ..., tn <: #0 <: u
                // Let's simplify to #0 := dynamic | #1
                // with t1, ..., tn <: #1 <: u
                bind_to_like_fresh(
                    env,
                    r,
                    var,
                    ity_set::filter(|t| !is_locl_dynamic(t), &lower_bounds),
                    upper_bounds,
                )
            } else {
                ty.clone()
            }
        }
        _ => ty.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn option_merge_is_that_of_base() {
        let both = |a: isize, b: isize| a * 10 + b;
        assert_eq!(option_merge(None, None, both), None);
        assert_eq!(option_merge(Some(1), None, both), Some(1));
        assert_eq!(option_merge(None, Some(2), both), Some(2));
        assert_eq!(option_merge(Some(1), Some(2), both), Some(12));
    }
}
