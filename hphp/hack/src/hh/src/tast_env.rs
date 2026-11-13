// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tast_env.ml`. See `hh/PORTING.md`.
//!
//! [`Env`] (`Tast_env.env`) is just an alias to `Typing_env.env`, and the
//! functions we provide for it are largely just aliases to functions that take
//! a `Typing_env.env`.
//!
//! If you find that you need to add a new alias here, please take care to
//! ensure that it always works with the information available in the [`Env`]
//! constructed by `Tast_visitor` classes. Only a subset of the information
//! available in the inference phase (`Typing`) will be persisted in a
//! `Tast.program` (and thus available to `Tast_visitor`). Most of the
//! persisted information comes from `Typing_env.save`.
//!
//! The public surface is that of `tast_env.mli`: the functions of
//! `Typing_env.Expose_to_tast_env`, the functions of `Typing_env` that the
//! `.mli` lists (re-exported below), and those defined here. In OCaml the
//! type `env` is abstract outside this module; here it is the typing
//! environment itself, so [`eq_typing_env`] is the identity.
//!
//! Exceptions: [`NotInClass`] (`Not_in_class`) is raised far from where it is
//! caught, so it is a panic payload (`std::panic::panic_any(NotInClass)`).

use std::rc::Rc;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typechecker_options::TypecheckerOptions;
use pos::ToOxidized;
use ty::reason::Reason as _;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_counters;
use crate::decl_entry;
use crate::decl_env;
use crate::decl_hint;
use crate::derive_type_instantiation;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::hh_json_helpers::access::Keytrace;
use crate::provider_context;
use crate::relative_path;
use crate::tast;
use crate::typing_defs;
use crate::typing_defs::CeVisibility;
use crate::typing_defs::DeclTy;
use crate::typing_defs::DeclTy_;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::FunParam;
use crate::typing_defs::FunType;
use crate::typing_defs::ParamMode;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs_flags;
use crate::typing_dynamic_utils;
use crate::typing_env;
use crate::typing_env_from_def;
use crate::typing_env_types;
use crate::typing_equality_check;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_expand;
use crate::typing_inference_env;
use crate::typing_intersection;
use crate::typing_json;
use crate::typing_make_type;
use crate::typing_ops;
use crate::typing_phase;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_reason::Ureason;
use crate::typing_refinement;
use crate::typing_set;
use crate::typing_solver;
use crate::typing_subtype;
use crate::typing_taccess;
use crate::typing_union;
use crate::typing_utils;
use crate::typing_visibility;
use crate::typing_warning;
use crate::typing_warning_utils;
use crate::typing_xhp;
use crate::yojson::safe as yojson;

// All+only functions in Typing_env that are safe in tasts checks
// should hereby be available as Tast_env.get_class, Tast_env.get_typedef, etc.
//
// See comment in typing_env.mli Expose_to_tast_env on when+how to add things
pub use crate::typing_env::expose_to_tast_env::*;
// The functions of `Typing_env` that `tast_env.mli` lists.
pub use crate::typing_env::expand_type;
pub use crate::typing_env::fresh_type;
pub use crate::typing_env::get_ctx;
pub use crate::typing_env::get_current_decl_and_file;
pub use crate::typing_env::get_deps_mode;
pub use crate::typing_env::get_enforceable;
pub use crate::typing_env::get_file;
pub use crate::typing_env::get_newable;
pub use crate::typing_env::get_reified;
pub use crate::typing_env::get_upper_bounds;
pub use crate::typing_env::get_val_kind;
pub use crate::typing_env::is_fresh_generic_parameter;
pub use crate::typing_env::is_hhi;
pub use crate::typing_env::set_static;
pub use crate::typing_env::set_val_kind;
pub use crate::typing_env_types::Env;

/// `type t = env`
pub type T = Env;

/// `class_or_typedef_result`
#[derive(Clone, Debug)]
pub enum ClassOrTypedefResult {
    ClassResult(cls::T),
    TypedefResult(Arc<typing_defs::TypedefType>),
}

/// `exception Not_in_class` (a panic payload).
#[derive(Clone, Copy, Debug)]
pub struct NotInClass;

/// Returns a [`decl_env::Env`]
pub fn get_decl_env(env: &Env) -> &decl_env::Env {
    &env.decl_env
}

/// Return a string representation of the given type using Hack-like syntax.
pub fn print_ty(env: &Env, ty: &Ty) -> String {
    typing_print::full_strip_ns(true, env, ty)
}

pub fn print_decl_ty(msg: Option<bool>, env: &Env, ty: &DeclTy) -> String {
    typing_print::full_strip_ns_decl(msg, false, env, &ty.clone().to_oxidized())
}

pub fn print_error_ty(ignore_dynamic: Option<bool>, env: &Env, ty: &Ty) -> String {
    typing_print::error(ignore_dynamic, env, ty)
}

pub fn print_hint(env: &Env, hint: &aast::Hint) -> String {
    print_decl_ty(None, env, &decl_hint::hint(get_decl_env(env), hint))
}

fn make_param_from_tuple(
    is_optional: bool,
    splat: bool,
    ix: usize,
    pos: PosOrDecl,
    name: &Option<String>,
    ty: Ty,
) -> FunParam {
    FunParam {
        pos,
        name: match name {
            None => None,
            Some(n) => Some(format!("{}[{}]", n, ix)),
        },
        type_: ty,
        flags: typing_defs::make_fp_flags(
            ParamMode::FPnormal,
            false, // accept_disposable
            is_optional,
            false, // readonly
            false, // ignore_readonly_error
            splat,
            false, // named
        ),
        def_value: None,
    }
}

/// Eliminate a type splat parameter in a function type that has been
/// instantiated to a tuple e.g. function(int $i, ...(string,bool) $a)
/// expands to function(int $i, string $a[0], bool $a[1])
///
/// Given a function type whose last parameter $p is a type splat of a tuple,
/// expand the tuple into parameters named $p[0], $p[1] etc.
///
/// For example
///   (function(int $x, ...(string, optional bool) $p):void)
/// expands to
///   (function(int $x, string $p[0], optional bool $p[1]):void)
pub fn expand_splat_param_in_function_type(env: &Env, ty: Ty) -> Ty {
    let ty = typing_env::expand_type(&mut env.clone(), ty);
    match typing_defs::deref(&ty) {
        (r, Ty_::Tfun(ft)) => {
            let (ft_params, ft_flags) = match ft.params.last() {
                Some(fp) if typing_defs::get_fp_splat(fp) => {
                    let fp_ty = typing_env::expand_type(&mut env.clone(), fp.type_.clone());
                    match typing_defs::get_node(&fp_ty) {
                        Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: t_optional,
                            extra: t_extra,
                        }) => {
                            let mut ft_params: Vec<FunParam> =
                                ft.params[..ft.params.len() - 1].to_vec();
                            ft_params.extend(t_required.iter().enumerate().map(|(ix, ty)| {
                                make_param_from_tuple(
                                    false,
                                    false,
                                    ix,
                                    fp.pos.clone(),
                                    &fp.name,
                                    ty.clone(),
                                )
                            }));
                            ft_params.extend(t_optional.iter().enumerate().map(|(ix, ty)| {
                                make_param_from_tuple(
                                    true,
                                    false,
                                    ix + t_required.len(),
                                    fp.pos.clone(),
                                    &fp.name,
                                    ty.clone(),
                                )
                            }));
                            let (extra_params, ft_flags) = match t_extra {
                                // Closed tuples are represented by a variadic type of nothing
                                TupleExtra::Tvariadic(ty) if typing_utils::is_nothing(env, ty) => {
                                    (vec![], ft.flags)
                                }
                                // Convert final splat or variadic tuple element into splat or variadic parameter
                                TupleExtra::Tvariadic(ty) | TupleExtra::Tsplat(ty) => {
                                    let splat = match t_extra {
                                        TupleExtra::Tsplat(_) => true,
                                        TupleExtra::Tvariadic(_) => false,
                                    };
                                    (
                                        vec![make_param_from_tuple(
                                            false,
                                            splat,
                                            t_optional.len() + t_required.len(),
                                            fp.pos.clone(),
                                            &fp.name,
                                            ty.clone(),
                                        )],
                                        if splat {
                                            ft.flags
                                        } else {
                                            typing_defs_flags::fun::set_variadic(true, ft.flags)
                                        },
                                    )
                                }
                            };
                            ft_params.extend(extra_params);
                            (ft_params, ft_flags)
                        }
                        _ => (ft.params.clone(), ft.flags),
                    }
                }
                _ => (ft.params.clone(), ft.flags),
            };
            typing_defs::mk((
                r,
                Ty_::Tfun(std::rc::Rc::new(FunType {
                    params: ft_params,
                    flags: ft_flags,
                    ..std::rc::Rc::unwrap_or_clone(ft)
                })),
            ))
        }
        _ => ty,
    }
}

/// Return a string representation of the given type using Hack-like syntax,
/// formatted with limited width and line breaks, including additional
/// information from the `SymbolOccurrence.t` and (if provided)
/// `SymbolDefinition.t`.
///
pub fn print_ty_with_identity<P>(
    env: &Env,
    ty: Ty,
    sym_occurrence: &crate::symbol_occurrence::T<P>,
    sym_definition: Option<&crate::symbol_definition::T<P>>,
) -> String {
    let ty = expand_splat_param_in_function_type(env, ty);
    typing_print::full_with_identity(true, env, &ty, sym_occurrence, sym_definition)
}

pub fn print_decl_ty_with_identity<P>(
    env: &Env,
    ty: &DeclTy,
    sym_occurrence: &crate::symbol_occurrence::T<P>,
    sym_definition: Option<&crate::symbol_definition::T<P>>,
) -> String {
    typing_print::full_decl_with_identity(
        env,
        true,
        false,
        &ty.clone().to_oxidized(),
        sym_occurrence,
        sym_definition,
    )
}

/// Return a JSON representation of the given type.
pub fn ty_to_json(env: &Env, show_like_ty: Option<bool>, ty: &Ty) -> yojson::T {
    typing_json::from_locl_ty(env, show_like_ty, ty)
}

/// Convert a JSON representation of a type back into a locl-phase type.
pub fn json_to_locl_ty(
    keytrace: Option<Keytrace>,
    ctx: &Arc<Ctx>,
    json: &yojson::T,
) -> Result<Ty, typing_defs::DeserializationError> {
    typing_json::to_locl_ty(keytrace, ctx, json)
}

/// Return the type of the enclosing class definition.
/// When not in a class definition, raise [`NotInClass`].
pub fn get_self_ty_exn(env: &Env) -> Ty {
    match get_self_ty(env) {
        Some(self_ty) => self_ty,
        None => std::panic::panic_any(NotInClass),
    }
}

pub fn get_class_or_typedef(env: &Env, x: &str) -> decl_entry::T<ClassOrTypedefResult> {
    use crate::decl_enforceability::ClassOrTypedefResult as R;
    match typing_env::get_class_or_typedef(env, x) {
        decl_entry::T::Found(R::ClassResult(cd)) => {
            decl_entry::T::Found(ClassOrTypedefResult::ClassResult(cd))
        }
        decl_entry::T::Found(R::TypedefResult(td)) => {
            decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(td))
        }
        decl_entry::T::DoesNotExist => decl_entry::T::DoesNotExist,
        decl_entry::T::NotYetAvailable => decl_entry::T::NotYetAvailable,
    }
}

pub fn outside_expr_tree(env: &mut Env) {
    typing_env::outside_expr_tree(env, None)
}

/// Strip ~ from type
pub fn strip_dynamic(env: &Env, ty: Ty) -> Ty {
    typing_dynamic_utils::strip_dynamic(&mut env.clone(), ty)
}

#[derive(Clone, Debug)]
pub enum IsDisjointResult {
    /// Types are possibly overlapping
    NonDisjoint,
    /// Types are definitely non-overlapping
    Disjoint,
    /// Types overlap in dynamic, but as like-stripped types are disjoint
    DisjointIgnoringDynamic(Ty, Ty),
}

/// Are types disjoint? If is_dynamic_call is true, then
/// we are checking a dynamic call through a like type, so
/// result cannot be precise (i.e. won't return Disjoint)
pub fn is_disjoint(is_dynamic_call: bool, env: &Env, ty1: &Ty, ty2: &Ty) -> IsDisjointResult {
    if !is_dynamic_call
        && !typing_utils::is_nothing(env, ty1)
        && !typing_utils::is_nothing(env, ty2)
        && typing_utils::is_type_disjoint(env, ty1, ty2)
    {
        IsDisjointResult::Disjoint
    } else {
        let ty1 = strip_dynamic(env, ty1.clone());
        let ty2 = strip_dynamic(env, ty2.clone());
        // We don't flag ~null because typically this is a false positive
        if !(typing_utils::is_nothing(env, &ty1) || typing_utils::is_null(env, &ty1))
            && !(typing_utils::is_nothing(env, &ty2) || typing_utils::is_null(env, &ty2))
            && typing_utils::is_type_disjoint(env, &ty1, &ty2)
        {
            IsDisjointResult::DisjointIgnoringDynamic(ty1, ty2)
        } else {
            IsDisjointResult::NonDisjoint
        }
    }
}

/// Strip supportdyn from type, return whether it was there or not
pub fn strip_supportdyn(env: &Env, ty: Ty) -> (bool, Ty) {
    typing_utils::strip_supportdyn(&mut env.clone(), ty)
}

pub fn get_underlying_function_type(
    env: &Env,
    ty: Ty,
) -> Option<(typing_reason::T, std::rc::Rc<FunType>)> {
    typing_utils::get_underlying_function_type(&mut env.clone(), ty)
}

/// Returns an [`Env`] for which [`get_inside_constructor`] is set to `true`.
/// If you are using `Tast_visitor`, you should have no need of this.
pub fn set_inside_constructor(env: &mut Env) {
    Rc::make_mut(&mut env.genv).fun_is_ctor = true;
}

/// Returns whether or not the typing environment is inside the
/// constructor of a class
pub fn get_inside_constructor(env: &Env) -> bool {
    env.genv.fun_is_ctor
}

/// Eliminate type variables (`Typing_defs.Tvar`) in the given type by
/// recursively replacing them with the type they refer to.
pub fn fully_expand(env: &Env, ty: Ty) -> Ty {
    typing_expand::fully_expand(env, ty)
}

/// Types that can have methods called on them. Usually a class but
/// also includes dynamic types
#[derive(Clone, Debug)]
pub enum ReceiverIdentifier {
    RIclass(String, Vec<Ty>),
    RIdynamic,
    RIerr,
    RIany,
}

/// Given some class type or unresolved union of class types, return the
/// identifiers of all receivers the type may represent.
///
/// Intended for uses like constructing call graphs and finding references, where
/// we have the statically known class type of some runtime value or class ID and
/// we would like the name of that class.
pub fn get_receiver_ids(env: &Env, ty: Ty) -> Vec<ReceiverIdentifier> {
    // `acc` is an OCaml list built by consing, reversed at the end: here it
    // is built in the final order by pushing.
    fn aux(env: &Env, seen: &[String], acc: &mut Vec<ReceiverIdentifier>, ty: &Ty) {
        match typing_defs::get_node(ty) {
            Ty_::Tclass((_, cid), _, tyl) => {
                acc.push(ReceiverIdentifier::RIclass(cid.clone(), tyl.clone()))
            }
            Ty_::Toption(ty) | Ty_::Tdependent(_, ty) => aux(env, seen, acc, ty),
            Ty_::Tnewtype(n, tyargs, _) => {
                let ty = typing_utils::get_newtype_super(
                    &mut env.clone(),
                    typing_defs::get_reason(ty).clone(),
                    n,
                    tyargs,
                );
                aux(env, seen, acc, &ty)
            }
            Ty_::Tunion(tys) | Ty_::Tintersection(tys) => {
                for ty in tys {
                    aux(env, seen, acc, ty)
                }
            }
            Ty_::Tgeneric(name) if !seen.contains(name) => {
                let mut seen_ = vec![name.clone()];
                seen_.extend(seen.iter().cloned());
                let seen = seen_;
                let upper_bounds = typing_env::get_upper_bounds(env, name);
                typing_set::fold(|ty, ()| aux(env, &seen, acc, ty), &upper_bounds, ())
            }
            Ty_::Tdynamic(_) => acc.push(ReceiverIdentifier::RIdynamic),
            Ty_::Tany(_) => acc.push(ReceiverIdentifier::RIany),
            _ => {}
        }
    }
    let mut acc = vec![];
    aux(env, &[], &mut acc, &typing_expand::fully_expand(env, ty));
    acc
}

/// Given some class type or unresolved union of class types, return the
/// identifiers of all classes the type may represent.
pub fn get_class_ids(env: &Env, ty: Ty) -> Vec<String> {
    get_receiver_ids(env, ty)
        .into_iter()
        .filter_map(|ri| match ri {
            ReceiverIdentifier::RIclass(cid, _) => Some(cid),
            _ => None,
        })
        .collect()
}

/// For an `EnumClass\Label<T, _>` returns `T`.
pub fn get_label_receiver_ty(env: &mut Env, ty: Ty) -> Ty {
    typing_env::open_tyvars(env, Pos::NONE);
    let ty_in = typing_env::fresh_type(env, Pos::NONE);
    let label_ty = typing_defs::mk((
        typing_reason::none(),
        Ty_::Tnewtype(
            naming_special_names_rust::classes::ENUM_CLASS_LABEL.to_string(),
            vec![
                ty_in.clone(),
                typing_make_type::nothing(typing_reason::none()),
            ],
            typing_make_type::mixed(typing_reason::none()),
        ),
    ));
    typing_env::set_tyvar_variance(env, Some(true), None, &label_ty);
    let _ = typing_subtype::sub_type(env, None, None, None, None, label_ty, ty, None);
    let _ty_err = typing_solver::close_tyvars_and_solve(env);
    typing_env::expand_type(env, ty_in)
}

/// Intersect type with nonnull
pub fn intersect_with_nonnull(env: &mut Env, pos: PosOrDecl, ty: Ty) -> Ty {
    typing_intersection::intersect_with_nonnull(env, pos, ty)
}

/// Get the "as" constraints from an abstract type or generic parameter, or
/// return the type itself if there is no "as" constraint. In the case of a
/// generic parameter whose "as" constraint is another generic parameter, repeat
/// the process until a type is reached that is not a generic parameter. Don't
/// loop on cycles. (For example, function foo<Tu as Tv, Tv as Tu>(...))
/// The abstract_enum flag controls whether arraykey bound enums are considered
/// abstract, or as arraykey bound.
pub fn get_concrete_supertypes(
    expand_supportdyn: Option<bool>,
    abstract_enum: bool,
    env: &mut Env,
    ty: Ty,
) -> Vec<Ty> {
    typing_utils::get_concrete_supertypes(
        None,
        expand_supportdyn,
        Some(false), // include_case_types
        abstract_enum,
        env,
        ty,
    )
}

/// Return `true` if the given class (referred to by the given `class_id_`, if
/// provided) allows the current class (the one returned by `get_self`) to
/// access its members with the given visibility.
pub fn is_visible(
    is_method: bool,
    env: &Env,
    vis: (&CeVisibility, bool),
    cid: Option<&nast::ClassId_>,
    class_: &cls::T,
) -> bool {
    typing_visibility::is_visible(is_method, env, vis, cid, class_)
}

/// Assert that the types of values involved in a strict (non-)equality
/// comparison are compatible; e.g., that the types are not statically
/// known to be disjoint, in which case the comparison will always return
/// true or false.
pub fn assert_nontrivial(p: Pos, bop: ast_defs::Bop, env: &Env, ty1: Ty, ty2: Ty) {
    typing_equality_check::assert_nontrivial(p, bop, env, ty1, ty2)
}

/// Return the declaration-phase type the given hint represents.
pub fn hint_to_ty(env: &Env, hint: &aast::Hint) -> DeclTy {
    decl_hint::hint(&env.decl_env, hint)
}

pub fn localize(env: &mut Env, ety_env: &ExpandEnv, dty: &DeclTy) -> Ty {
    let (ty_err_opt, lty) = typing_phase::localize(ety_env, env, dty);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    lty
}

pub fn localize_hint_for_refinement(env: &mut Env, h: &aast::Hint) -> Ty {
    let (_ty_err_opt, lty) = typing_phase::localize_hint_for_refinement(env, h);
    lty
}

/// Return `Ok(())` if the current hint is supported in the new
/// constraint-based refinement logic. Otherwise returns `Err(string)`,
/// where `string` is the reason why the hint isn't supported.
pub fn supports_new_refinement(env: &Env, h: &aast::Hint) -> Result<(), String> {
    let mut env = env.clone();
    let ty = localize_hint_for_refinement(&mut env, h);
    if typing_defs::is_nonnull(&ty) {
        Ok(())
    } else {
        match typing_refinement::ty_predicate::of_ty(&env, &ty) {
            Err(err) => Err(err),
            Ok(_) => Ok(()),
        }
    }
}

/// Transforms a declaration phase type (`Typing_defs.decl_ty`)
/// into a localized type (`Typing_defs.locl_ty` = `Tast.ty`).
/// Performs no substitutions of generics and initializes the late static bound
/// type (`Typing_defs.Tthis`) to the current class type (the type returned by
/// `get_self`).
///
/// This is mostly provided as legacy support for `AutocompleteService`, and
/// should not be considered a general mechanism for transforming a `decl_ty` to
/// a `Tast.ty`.
///
/// `ignore_errors` silences certain errors because those errors have already fired
/// and/or are not appropriate at the time we call localize.
pub fn localize_no_subst(env: &mut Env, ignore_errors: bool, dty: &DeclTy) -> Ty {
    let (ty_err_opt, lty) = typing_phase::localize_no_subst(env, ignore_errors, dty);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    lty
}

/// Simplify unions in a type.
pub fn simplify_unions(env: &mut Env, ty: Ty) -> Ty {
    typing_union::simplify_unions(env, None, None, ty)
}

pub fn as_bounds_to_non_intersection_type(env: &Env, tys: &[tast::DeclTy]) -> Option<Ty> {
    let t = DeclTy::new(R::none(), DeclTy_::Tintersection(tys.to_vec().into_boxed_slice()));
    // Need to localize in order to simplify
    let locl_ty = localize_no_subst(&mut env.clone(), true, &t);
    // Multiple bounds can be expressed as an intersection,
    // but it might be possible to simplify this
    let locl_ty = typing_intersection::simplify_intersections(&mut env.clone(), None, locl_ty);
    let (_, locl_ty) = strip_supportdyn(env, locl_ty);
    match typing_defs::get_node(&locl_ty) {
        Ty_::Tintersection(tys) if !tys.is_empty() => None,
        _ => Some(locl_ty),
    }
}

/// Simplify intersections in a type.
pub fn simplify_intersections(env: &mut Env, ty: Ty) -> Ty {
    typing_intersection::simplify_intersections(env, None, ty)
}

/// Union a list of types.
pub fn union_list(env: &mut Env, r: typing_reason::T, tyl: &[Ty]) -> Ty {
    typing_union::union_list(env, None, r, tyl)
}

/// Assert that one type is a subtype of another, resolving unbound type
/// variables in both types (if any), with `env` reflecting the new state of
/// these type variables. Produce an error if they cannot be subtypes.
pub fn assert_subtype(
    p: Pos,
    reason: Ureason,
    env: &mut Env,
    ty_have: Ty,
    ty_expect: Ty,
    on_error: typing_error::callback::T,
) {
    let ty_err_opt = typing_ops::sub_type(None, p, reason, env, ty_have, ty_expect, on_error);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}

/// Return `true` when the first type is a subtype of the second type
/// regardless of the values of unbound type variables in both types (if any).
pub fn is_sub_type(env: &Env, ty_sub: &Ty, ty_super: &Ty) -> bool {
    typing_subtype::is_sub_type(env, ty_sub, ty_super)
}

/// Return `false` when the first type is not a subtype of the second type
/// regardless of the values of unbound type variables in both types (if any).
pub fn is_maybe_sub_type(env: &Env, ty_sub: &Ty, ty_super: &Ty) -> bool {
    typing_subtype::is_maybe_sub_type(env, ty_sub, ty_super)
}

pub fn is_dynamic_aware_sub_type(env: &Env, ty_sub: &Ty, ty_super: &Ty) -> bool {
    typing_subtype::is_dynamic_aware_sub_type(env, ty_sub, ty_super)
}

/// Return `true` when the first type can be considered a subtype of the second
/// type after resolving unbound type variables in both types (if any).
pub fn can_subtype(env: &Env, ty_sub: &Ty, ty_super: &Ty) -> bool {
    typing_subtype::can_sub_type(env, ty_sub, ty_super)
}

/// Return `true` when the first type is a subtype of the second type. There is
/// no type T such that for all T', T <: T' and T' <: T (which is the case for Tany
/// and Terr in `can_subtype`)
pub fn is_sub_type_for_union(env: &Env, ty_sub: &Ty, ty_super: &Ty) -> bool {
    typing_subtype::is_sub_type_for_union(env, ty_sub, ty_super)
}

/// Returns (class_name, tconst_name, tconst_reference_position) for each type
/// constant referenced in the type access path.
pub fn referenced_typeconsts(
    env: &Env,
    root: &aast::Hint,
    ids: &[aast::Sid],
) -> Vec<(String, String, Pos)> {
    let root = hint_to_ty(env, root);
    let ety_env = typing_defs::empty_expand_env();
    let (tcs, ty_err_opt) = typing_taccess::referenced_typeconsts(env, &ety_env, (&root, ids));
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    tcs
}

pub fn is_any(env: &Env, ty: &Ty) -> bool {
    typing_utils::is_any_and_not_nothing(env, ty)
}

/// Construct an empty [`Env`]. Unlikely to be the best choice; prefer using
/// `Tast_visitor` or constructing an [`Env`] from a `Tast.def`.
pub fn empty(ctx: Arc<Ctx>) -> Env {
    typing_env_types::empty(None, None, ctx, Arc::new(relative_path::default), None)
}

fn restore_saved_env(env: &mut Env, saved_env: &tast::SavedEnv) {
    let ctx = provider_context::with_tcopt(&env.decl_env.ctx, &saved_env.tcopt);
    // Setting a field to the value it already has changes nothing: skip the
    // copy of the shared record that the write would make.
    if !Arc::ptr_eq(&env.decl_env.ctx, &ctx) {
        Rc::make_mut(&mut env.decl_env).ctx = ctx;
    }
    if !Arc::ptr_eq(&env.genv.tcopt, &saved_env.tcopt) {
        Rc::make_mut(&mut env.genv).tcopt = Arc::clone(&saved_env.tcopt);
    }
    simple_merge_memo(&mut env.inference_env, &saved_env.inference_env);
    env.tpenv = saved_env.tpenv.clone();
    // (`fun_tast_info` is in the rarely written part of the environment: an
    // equal value is not written, which would copy that part.)
    if env.fun_tast_info != saved_env.fun_tast_info {
        env.fun_tast_info = saved_env.fun_tast_info.clone();
    }
    env.checked = saved_env.checked;
}

/// The merges of [`simple_merge_memo`], by the addresses of the roots of
/// the two maps.
type MergeMemo = hash::HashMap<
    (usize, usize),
    (
        typing_inference_env::TvenvHandle,
        typing_inference_env::TvenvHandle,
        typing_inference_env::TvenvHandle,
    ),
>;

thread_local! {
    static MEMO: std::cell::RefCell<MergeMemo> = std::cell::RefCell::new(MergeMemo::default());
}

/// Forget the merges of [`simple_merge_memo`] (they keep the maps they hold
/// alive): `Tast_check.def` starts with this, the walks of one definition
/// share the memo.
pub fn clear_merge_memo() {
    MEMO.with_borrow_mut(|memo| memo.clear())
}

/// `Typing_inference_env.simple_merge env1 env2`, made once for each pair of
/// maps. The TAST checks walk a definition several times (the handlers of
/// `Tast_check` in one pass, then the visitors that some handlers start on
/// each function, then the warning checks), and each walk restores the
/// environment of every lambda from the same environments. The merge reads
/// only the type-variable maps of the two environments and writes only the
/// first one's; a map that is the same object as one seen before (`ptr_eq`:
/// a copy with no change since) has the same contents, so the result is
/// the one computed then. The memo holds the maps it compares with, so their
/// addresses cannot be reused while they are in it.
fn simple_merge_memo(env1: &mut typing_inference_env::T, env2: &typing_inference_env::T) {
    /// More merges than a definition needs; the memo is emptied when it is
    /// reached.
    const SIZE: usize = 1 << 16;
    let key = (
        typing_inference_env::tvenv_addr(env1),
        typing_inference_env::tvenv_addr(env2),
    );
    let hit = MEMO.with_borrow(|memo| match memo.get(&key) {
        Some((h1, h2, res))
            if typing_inference_env::tvenv_handle_is(env1, h1)
                && typing_inference_env::tvenv_handle_is(env2, h2) =>
        {
            Some(res.clone())
        }
        _ => None,
    });
    match hit {
        Some(res) => typing_inference_env::set_tvenv_handle(env1, &res),
        None => {
            let h1 = typing_inference_env::tvenv_handle(env1);
            typing_inference_env::simple_merge(env1, env2);
            let h2 = typing_inference_env::tvenv_handle(env2);
            let res = typing_inference_env::tvenv_handle(env1);
            MEMO.with_borrow_mut(|memo| {
                if memo.len() >= SIZE {
                    memo.clear();
                }
                memo.insert(key, (h1, h2, res));
            })
        }
    }
}

fn check_fun_tast_info_present(env: &Env, fun_tast_info: &Option<tast::FunTastInfo>) {
    match fun_tast_info {
        Some(_) => {}
        None => diagnostics_state::internal_error(
            env.genv.callable_pos.clone(),
            "fun_tast_info of a function or method was not filled in before TAST checking",
        ),
    }
}

/// Construct an [`Env`] from a method definition and the [`Env`] of the
/// context it appears in.
pub fn restore_method_env(env: &mut Env, m: &tast::Method_) {
    let se = &m.annotation;
    restore_saved_env(env, se);
    // Note: OK to not call _restore_pos because each method gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(env, Some(m.span.clone()));
}

/// Construct an [`Env`] from a lambda definition and the [`Env`] of the
/// context it appears in.
pub fn restore_fun_env(env: &mut Env, f: &tast::Fun_) {
    let se = &f.annotation;
    restore_saved_env(env, se);
    // Note: OK to not call _restore_pos because each fn gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(env, Some(f.span.clone()));
}

fn fun_env(ctx: &Arc<Ctx>, fd: &tast::FunDef) -> Env {
    let f = &fd.fun;
    let ctx = provider_context::with_tcopt(ctx, &f.annotation.tcopt);
    let mut env = typing_env_from_def::fun_env(Some(decl_counters::Origin::Tast), ctx, fd);
    restore_fun_env(&mut env, f);
    env
}

fn class_env(ctx: &Arc<Ctx>, c: &tast::Class_) -> Env {
    let ctx = provider_context::with_tcopt(ctx, &c.annotation.tcopt);
    let mut env = typing_env_from_def::class_env(Some(decl_counters::Origin::Tast), ctx, c);
    restore_saved_env(&mut env, &c.annotation);
    // Note: OK to not call _restore_pos because each class gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(&mut env, Some(c.span.clone()));
    env
}

fn typedef_env(ctx: &Arc<Ctx>, t: &tast::Typedef) -> Env {
    let ctx = provider_context::with_tcopt(ctx, &t.annotation.tcopt);
    let mut env = typing_env_from_def::typedef_env(Some(decl_counters::Origin::Tast), ctx, t);
    restore_saved_env(&mut env, &t.annotation);
    // Note: OK to not call _restore_pos because each typedef gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(&mut env, Some(t.span.clone()));
    env
}

fn gconst_env(ctx: &Arc<Ctx>, cst: &tast::Gconst) -> Env {
    let ctx = provider_context::with_tcopt(ctx, &cst.annotation.tcopt);
    let mut env = typing_env_from_def::gconst_env(Some(decl_counters::Origin::Tast), ctx, cst);
    restore_saved_env(&mut env, &cst.annotation);
    // Note: OK to not call _restore_pos because each gconst gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(&mut env, Some(cst.span.clone()));
    env
}

fn module_env(ctx: &Arc<Ctx>, md: &tast::ModuleDef) -> Env {
    let ctx = provider_context::with_tcopt(ctx, &md.annotation.tcopt);
    let mut env = typing_env_from_def::module_env(Some(decl_counters::Origin::Tast), ctx, md);
    restore_saved_env(&mut env, &md.annotation);
    // Note: OK to not call _restore_pos because module gets its own env
    let _restore_pos = typing_env::set_inference_env_pos(&mut env, Some(md.span.clone()));
    env
}

/// Construct an [`Env`] from a toplevel definition.
pub fn def_env(ctx: &Arc<Ctx>, d: &tast::Def) -> Env {
    match d {
        aast::Def::Fun(x) => fun_env(ctx, x),
        aast::Def::Class(x) => class_env(ctx, x),
        aast::Def::Typedef(x) => typedef_env(ctx, x),
        aast::Def::Constant(x) => gconst_env(ctx, x),
        aast::Def::Module(x) => module_env(ctx, x),
        // TODO T44306013
        // The following nodes are included in the TAST, but are not typechecked.
        // However, we need to return an env here so for now create an empty env using
        // the default typechecker options.
        aast::Def::ClassAlias(_)
        | aast::Def::Stmt(_)
        | aast::Def::Namespace(_)
        | aast::Def::NamespaceUse(_)
        | aast::Def::SetNamespaceEnv(_)
        | aast::Def::SetModule(_)
        | aast::Def::FileAttributes(_) => empty(Arc::clone(ctx)),
    }
}

/// Evil, defeats the purpose of separating Tast_env and Typing_env.
///
/// In OCaml `Tast_env.env` is abstract and this is the proof that it is
/// `Typing_env_types.env`. Here the two are the same type, so this is the
/// identity.
pub fn eq_typing_env(env: &Env) -> &typing_env_types::Env {
    env
}

/// Verify that an XHP body expression is legal.
pub fn is_xhp_child(env: &Env, pos: &Pos, ty: &Ty) -> (bool, Option<typing_error::T>) {
    typing_xhp::is_xhp_child(env, pos, ty)
}

pub fn set_allow_wildcards(env: &mut Env) {
    env.allow_wildcards = true;
}

pub fn get_allow_wildcards(env: &Env) -> bool {
    env.allow_wildcards
}

fn extract_from_fun_tast_info<A>(
    env: &Env,
    extractor: impl FnOnce(&tast::FunTastInfo) -> A,
    default_value: A,
) -> A {
    let fun_tast_info = &env.fun_tast_info;
    check_fun_tast_info_present(env, fun_tast_info);
    match fun_tast_info {
        Some(fun_tast_info) => extractor(fun_tast_info),
        // In this case, check_fun_tast_info_present reported an error already
        None => default_value,
    }
}

pub fn fun_has_implicit_return(env: &Env) -> bool {
    extract_from_fun_tast_info(env, |info| info.has_implicit_return, false)
}

pub fn fun_has_readonly(env: &Env) -> bool {
    extract_from_fun_tast_info(env, |info| info.has_readonly, false)
}

/// Check that the position is in the current decl and if it is, resolve
/// it with the current file.
pub fn fill_in_pos_filename_if_in_current_decl(env: &Env, pos: &PosOrDecl) -> Option<Pos> {
    typing_env::fill_in_pos_filename_if_in_current_decl(env, pos)
}

/// See `Tast.check_status` to understand what this function returns from the
/// environment.
pub fn get_check_status(env: &Env) -> tast::CheckStatus {
    env.checked
}

pub fn derive_instantiation(
    env: &mut Env,
    uninstantiated: &DeclTy,
    instantiated: &Ty,
) -> derive_type_instantiation::instantiation::T {
    derive_type_instantiation::derive_instantiation(env, uninstantiated, instantiated)
}

pub fn add_typing_error(err: &typing_error::T, env: &Env) {
    typing_error_utils::add_typing_error(err, env)
}

pub fn add_warning<X: typing_warning_utils::Warning, A>(
    env: &Env,
    warning: typing_warning::T<X, A>,
) {
    typing_warning_utils::add(env, warning)
}

// (A reference: cloning the `Arc`, which all the threads share, at each
// call would write its count from every thread. Callers clone if they keep it.)
pub fn get_tcopt(env: &Env) -> &Arc<TypecheckerOptions> {
    &env.genv.tcopt
}
