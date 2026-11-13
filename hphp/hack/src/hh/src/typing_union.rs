// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_union.ml`. See `hh/PORTING.md`.
//!
//! # Notes on the port
//!
//! - `exception Dont_simplify` is the error type [`DontSimplify`]. It is
//!   raised by `union_funs` and `union_tylists_w_variances` (through
//!   `union_class_or_newtype`) and caught by `simplify_non_subtype_union`,
//!   whose handler returns the environment it had before its `try`. The
//!   cases of that `try` that call `union_class_or_newtype` save the
//!   environment first and restore it on `Err` (nothing happens between the
//!   `try` and those calls); `union_funs` fails before it does anything.
//! - `union_list` and `simplify_unions` are defined twice: the second
//!   definition (optional arguments, logging) shadows the first, which only
//!   it calls. The first is a function of the same name nested in the second.
//! - `make_union` and `fold_union` are not in `typing_union.mli` but are
//!   public: `crate::typing_utils` reaches them (OCaml sets
//!   `Utils.make_union_ref` and `Utils.fold_union_ref` to them). The
//!   `let () = Utils.union_ref := union` (and the same for `union_list`,
//!   `fold_union`, `simplify_unions`, `make_union`, and
//!   `Env.simplify_unions_ref`) at the end of the OCaml are done by the
//!   modules that own those references (`crate::typing_utils`,
//!   `crate::typing_env`).
//! - The `'a` that `Typing_log.log_function` gets is the environment with the
//!   result, as in `typing_subtype/prelude.rs`.
//!
//! # `union_shapes`
//!
//! - `TShapeMap.merge` (`Stdlib.Map.merge`) calls its function on the keys in
//!   decreasing order (OCaml evaluates the arguments of
//!   `concat_or_join (merge f l1 l2) v (f v d1 d2) (merge f r1 r2)` from right
//!   to left), and that function unions the field types: the port does the
//!   same, for the order of the effects (fresh type variables).
//! - The shape maps are `BTreeMap`s, which cannot reproduce which of two
//!   equal keys (keys compare without their positions) `Map.merge` keeps,
//!   which depends on the heights of the two OCaml trees: the merged map has
//!   the key of the first map wherever both have it.
//! - `phys_equal fdm1 fdm2` is `std::ptr::eq` on the two maps (true when both
//!   types share their node); it only skips work. `phys_equal f1 f2` on two
//!   field records is approximated by "same optionality, physically equal
//!   types": the OCaml would then compute `union ty1 ty1`, which returns
//!   `ty1` without changing anything (except for logging).
//!
//! # Lists
//!
//! Several functions build lists by consing onto an accumulator. Here the
//! accumulator is a `Vec` that is pushed to, and it is reversed where OCaml
//! uses the list: the order of the elements of the results, which shows in
//! types and messages, is the OCaml one.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::ast_defs::Tprim;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::tvid;
use crate::typing_algebra;
use crate::typing_defs;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::equal_type_predicate;
use crate::typing_defs_core::ft_params_compare;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::is_type_tag_generic_wildcard;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_defs_core::phys_equal;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::ty_equal;
use crate::typing_defs_core::with_reason;
use crate::typing_defs_flags;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_intersection;
use crate::typing_log;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;
/// `module Utils = Typing_utils`
use crate::typing_utils as utils;

/// `Naming_special_names.Classes.cString`, which `naming_special_names_rust`
/// does not have.
const C_STRING: &str = "\\HH\\string";

/// The `?on_tyvar` argument of `simplify_unions`:
/// `env -> Reason.t -> Tvid.t -> env * locl_ty`.
use crate::typing_utils::OnTyvar;

/// `?on_tyvar` passed on to a call: the callback, reborrowed for the call.
fn reborrow_on_tyvar<'b>(on_tyvar: &'b mut Option<OnTyvar<'_>>) -> Option<OnTyvar<'b>> {
    match on_tyvar {
        Some(on_tyvar) => Some(&mut **on_tyvar),
        None => None,
    }
}

/// `exception Dont_simplify`
#[derive(Debug)]
struct DontSimplify;

/// `orr r_opt r = Some (Option.value r_opt ~default:r)`
fn orr(r_opt: Option<Reason>, r: Reason) -> Option<Reason> {
    Some(r_opt.unwrap_or(r))
}

/// `module Log`
mod log {
    use super::*;

    /// `debug_ty (env, ty)`
    pub fn debug_ty(env: &Env, ty: &Ty) -> Option<String> {
        // The environment that `expand_type` returns is only used to print
        // the type.
        let mut env = env.clone();
        let ty = env::expand_type(&mut env, ty.clone());
        Some(typing_print::debug(&env, &ty))
    }

    /// `debug_ty_opt (env, ty_opt)`
    pub fn debug_ty_opt(env: &Env, ty_opt: &Option<Ty>) -> Option<String> {
        Some(match ty_opt {
            None => "None".to_string(),
            Some(ty) => format!("Some ({})", typing_print::debug(env, ty)),
        })
    }

    /// `log_union env ty1 ty2 f`
    pub fn log_union(env: &mut Env, ty1: &Ty, ty2: &Ty, f: impl FnOnce(&mut Env) -> Ty) -> Ty {
        let arguments = vec![
            ("ty1".to_string(), typing_print::debug(env, ty1)),
            ("ty2".to_string(), typing_print::debug(env, ty2)),
        ];
        let (_env, ty) = typing_log::log_function(
            &get_pos(ty2),
            "Typing_union.union",
            &arguments,
            |(env, ty): &(&mut Env, Ty)| debug_ty(env, ty),
            move || {
                let ty = f(env);
                (env, ty)
            },
        );
        ty
    }

    pub fn should_log(env: &Env, level: isize) -> bool {
        typing_log::should_log(env, "union", level)
    }

    /// `log_simplify_union env r ty1 ty2 f`
    pub fn log_simplify_union(
        env: &mut Env,
        r: &Reason,
        ty1: &Ty,
        ty2: &Ty,
        f: impl FnOnce(&mut Env) -> Option<Ty>,
    ) -> Option<Ty> {
        let arguments = vec![
            ("ty1".to_string(), typing_print::debug(env, ty1)),
            ("ty2".to_string(), typing_print::debug(env, ty2)),
        ];
        let (_env, ty_opt) = typing_log::log_function(
            &reason::to_pos(r),
            "Typing_union.simplify_union",
            &arguments,
            |(env, ty_opt): &(&mut Env, Option<Ty>)| debug_ty_opt(env, ty_opt),
            move || {
                let ty_opt = f(env);
                (env, ty_opt)
            },
        );
        ty_opt
    }

    /// `log_union_list env r tyl f`
    pub fn log_union_list(
        env: &mut Env,
        r: &Reason,
        tyl: &[Ty],
        f: impl FnOnce(&mut Env) -> Ty,
    ) -> Ty {
        let arguments: Vec<(String, String)> = tyl
            .iter()
            .map(|ty| ("ty".to_string(), typing_print::debug(env, ty)))
            .collect();
        let (_env, ty) = typing_log::log_function(
            &reason::to_pos(r),
            "Typing_union.union_list",
            &arguments,
            |(env, ty): &(&mut Env, Ty)| debug_ty(env, ty),
            move || {
                let ty = f(env);
                (env, ty)
            },
        );
        ty
    }

    /// `log_simplify_unions env ty f`
    pub fn log_simplify_unions(env: &mut Env, ty: &Ty, f: impl FnOnce(&mut Env) -> Ty) -> Ty {
        let arguments = vec![("ty".to_string(), typing_print::debug(env, ty))];
        let (_env, ty) = typing_log::log_function(
            &get_pos(ty),
            "Typing_union.simplify_unions",
            &arguments,
            |(env, ty): &(&mut Env, Ty)| debug_ty(env, ty),
            move || {
                let ty = f(env);
                (env, ty)
            },
        );
        ty
    }
}

/// Two types are "equivalent" if when expanded they are equal.
/// If they are equivalent, this function returns a type which is equivalent to
/// both, otherwise returns None.
///
/// We need this instead of simply ty_equal, otherwise a lot of things aren't
/// unioned properly - e.g. we get things like `array<^(int)> | array<^(int)>` -
/// which potentially creates huge unresolved types, damaging perf.
///
/// Furthermore, when unioning classes with type parameters, we allow
///   A<Unresolved[]> | A<B> = A<B>
/// This is because collections are often initialized like
///   $myvec = get_int_vec() ?? vec[]
/// If we don't do this simplification, this potentially produces exponentially
/// growing Unresolved, like in test map_corner_case.php.
fn ty_equiv(env: &mut Env, ty1: Ty, ty2: Ty, are_ty_param: bool) -> Option<Ty> {
    let ety1 = env::expand_type(env, ty1.clone());
    let ety2 = env::expand_type(env, ty2.clone());
    match (get_node(&ety1), get_node(&ety2)) {
        // `((Tunion [], _), (_, ty)) | ((_, ty), (Tunion [], _)) when are_ty_param`
        (Ty_::Tunion(tyl), _) if tyl.is_empty() && are_ty_param => Some(ty2),
        (_, Ty_::Tunion(tyl)) if tyl.is_empty() && are_ty_param => Some(ty1),
        _ if ty_equal(None, &ety1, &ety2) => match get_node(&ty1) {
            Ty_::Tvar(_) => Some(ty1),
            _ => Some(ty2),
        },
        _ => None,
    }
}

/// Destructure a union into a list of its sub-types, decending into sub-unions,
/// and also pulling out null and dynamic.
///
/// The OCaml returns `(env, (tyl_res, r_null, r_union, r_dyn))`.
fn dest_union_list(
    env: &mut Env,
    tyl: &[Ty],
) -> (Vec<Ty>, Option<Reason>, Option<Reason>, Option<Reason>) {
    // `dest_union` and `dest_union_list`: `tyl_res` is consed onto, so it has
    // the types in the reverse of the order they are met.
    let mut todo: Vec<Ty> = tyl.iter().rev().cloned().collect();
    let mut tyl_res: Vec<Ty> = vec![];
    let mut r_null: Option<Reason> = None;
    let mut r_union: Option<Reason> = None;
    let mut r_dyn: Option<Reason> = None;
    while let Some(ty) = todo.pop() {
        // `dest_union env ty tyl ...`, which loops on options.
        let mut ty = ty;
        loop {
            let ety = env::expand_type(env, ty);
            let r = get_reason(&ety).clone();
            match get_node(&ety) {
                Ty_::Tunion(tyl_) => {
                    r_union = orr(r_union, r);
                    todo.extend(tyl_.iter().rev().cloned());
                    break;
                }
                Ty_::Toption(ty_) => {
                    r_null = orr(r_null, r);
                    ty = ty_.clone();
                }
                Ty_::Tprim(Tprim::Tnull) => {
                    r_null = orr(r_null, r);
                    break;
                }
                Ty_::Tdynamic(None) => {
                    r_dyn = orr(r_dyn, r);
                    break;
                }
                // Dynamic types carrying shadow type variables must not be collapsed into
                // the union's single dynamic slot — they remain as distinct types to
                // preserve their per-local shadow type variables and constraint sets.
                Ty_::Tdynamic(Some(_)) => {
                    tyl_res.push(ety);
                    break;
                }
                _ => {
                    tyl_res.push(ety);
                    break;
                }
            }
        }
    }
    tyl_res.reverse();
    (tyl_res, r_null, r_union, r_dyn)
}

/// Constructor for unions and options, taking a list of types and whether the
/// result should be nullable. Simplify things like singleton unions or nullable nothing.
/// This allows the result of any unioning function from this module to be flattened and normalized,
/// with options being "pushed out" of the union (e.g. we return ?(A|B) instead of (A | ?B)
/// or (A | null | B), and similarly with like types).
pub fn make_union(
    env: &mut Env,
    r: Reason,
    tyl: &[Ty],
    reason_nullable_opt: Option<Reason>,
    reason_dyn_opt: Option<Reason>,
) -> Ty {
    fn is_dynamic_or_intersection_with_dynamic(ty: &Ty) -> bool {
        typing_defs::is_dynamic(ty)
            || match get_node(ty) {
                Ty_::Tintersection(tyl) => tyl.iter().any(is_dynamic_or_intersection_with_dynamic),
                _ => false,
            }
    }
    // dynamic | (T & dynamic) = dynamic
    let tyl: Vec<Ty> = match reason_dyn_opt {
        Some(_) => tyl
            .iter()
            .filter(|ty| !is_dynamic_or_intersection_with_dynamic(ty))
            .cloned()
            .collect(),
        None => tyl.to_vec(),
    };
    let ty = if tyl.len() == 1 {
        tyl.into_iter().next().unwrap()
    } else {
        make_type::union(r.clone(), tyl)
    };
    // Given that unions with null are encoded specially in the type system - as options -
    // we still need to simplify unions of null and nonnull here.
    // For example, we may have to construct ?(nonnull | any) which should result in mixed.
    // For something more complex like ?(A | (B & nonnull)), one can
    // distribute the option to give (?A | (?B & ?nonnull)) which then simplifies to ?(A | B).
    // This function performs those simplifications.
    let simplify_nonnull = |env: &mut Env, ty: Ty| -> Ty {
        let nonnull = make_type::nonnull(r.clone());
        let is_nonnull = |ty: &Ty| ty_equal(None, ty, &nonnull);
        fn simplify(env: &mut Env, is_nonnull: &dyn Fn(&Ty) -> bool, ty: Ty) -> Ty {
            let ty = env::expand_type(env, ty);
            let r = get_reason(&ty).clone();
            match get_node(&ty) {
                Ty_::Toption(ty_) => {
                    // ok to remove the Toption since we'll re-add it at the end.
                    simplify(env, is_nonnull, ty_.clone())
                }
                Ty_::Tunion(tyl) => {
                    let tyl: Vec<Ty> = tyl
                        .iter()
                        .map(|ty| simplify(env, is_nonnull, ty.clone()))
                        .collect();
                    if tyl.iter().any(|ty| is_nonnull(ty)) {
                        make_type::nonnull(r)
                    } else {
                        make_type::union(r, tyl)
                    }
                }
                Ty_::Tintersection(tyl) => {
                    let tyl: Vec<Ty> = tyl
                        .iter()
                        .map(|ty| simplify(env, is_nonnull, ty.clone()))
                        .collect();
                    let tyl: Vec<Ty> = tyl.into_iter().filter(|ty| !is_nonnull(ty)).collect();
                    make_type::intersection(r, tyl)
                }
                _ => ty,
            }
        }
        simplify(env, &is_nonnull, ty)
    };
    let ty = if reason_nullable_opt.is_some() {
        simplify_nonnull(env, ty)
    } else {
        ty
    };
    let like_ty = |dyn_r: Reason, ty: Ty| {
        let dynamic = make_type::dynamic(dyn_r.clone());
        make_type::union(dyn_r, vec![dynamic, ty])
    };
    let ty_is_nothing = typing_defs::is_nothing(&ty);
    // Some code is sensitive to dynamic appearing first in the union.
    let ty = match (reason_nullable_opt, reason_dyn_opt) {
        (None, Some(dyn_r)) if ty_is_nothing => make_type::dynamic(dyn_r),
        (Some(null_r), None) if ty_is_nothing => make_type::null(null_r),
        (Some(null_r), Some(dyn_r)) if ty_is_nothing => like_ty(dyn_r, make_type::null(null_r)),
        (None, None) => ty,
        (None, Some(dyn_r)) => match get_node(&ty) {
            Ty_::Tunion(tyl) => {
                let mut tyl_ = vec![make_type::dynamic(dyn_r)];
                tyl_.extend(tyl.iter().cloned());
                make_type::union(get_reason(&ty).clone(), tyl_)
            }
            _ => like_ty(dyn_r, ty),
        },
        (Some(null_r), None) => make_type::nullable(null_r, ty),
        (Some(null_r), Some(dyn_r)) => like_ty(dyn_r, make_type::nullable(null_r, ty)),
    };
    utils::wrap_union_inter_ty_in_var(env, r, ty)
}

fn exact_least_upper_bound(e1: &Exact, e2: &Exact) -> Exact {
    match (e1, e2) {
        (Exact::Exact, Exact::Exact) => Exact::Exact,
        (_, _) => nonexact(),
    }
}

fn try_strip_dynamic_intersect(ty: &Ty) -> Option<Ty> {
    match get_node(ty) {
        Ty_::Tintersection(tyl) if tyl.len() == 2 && typing_defs::is_dynamic(&tyl[0]) => {
            Some(tyl[1].clone())
        }
        Ty_::Tintersection(tyl) if tyl.len() == 2 && typing_defs::is_dynamic(&tyl[1]) => {
            Some(tyl[0].clone())
        }
        _ => None,
    }
}

/// Performs the union of two types.
/// The union is the least upper bound of the subtyping relation.
///
/// There is however one approximation: if type A is covariant,
/// then
///   A<T1> | A<T2> = A<T1|T2>
///
/// This approximation is necessary to avoid type growing exponentially in size.
/// We have seen cases where it would otherwise generate unions involving all
/// the subsets of a set of types.
///
/// If approx_cancel_neg is true, then some unions with negations are treated over-approximately:
/// C<t> | not C simplifies to mixed.
pub fn union(
    env: &mut Env,
    reason: Option<Reason>,
    approx_cancel_neg: Option<bool>,
    ty1: Ty,
    ty2: Ty,
) -> Ty {
    let approx_cancel_neg = approx_cancel_neg.unwrap_or(false);
    if log::should_log(env, 1) {
        let (ty1_, ty2_) = (ty1.clone(), ty2.clone());
        log::log_union(env, &ty1_, &ty2_, move |env| {
            union_(env, reason, approx_cancel_neg, ty1, ty2)
        })
    } else {
        // This path should be fast, so we make sure not to create a closure unlike the other path.
        union_(env, reason, approx_cancel_neg, ty1, ty2)
    }
}

fn union_(env: &mut Env, reason: Option<Reason>, approx_cancel_neg: bool, ty1: Ty, ty2: Ty) -> Ty {
    let r1 = get_reason(&ty1).clone();
    let r2 = get_reason(&ty2).clone();
    if ty_equal(None, &ty1, &ty2) {
        return ty1;
    }
    // Fast path for closed shapes: bypass expensive subtype and negation
    // checks that are O(n) per field and always fail for closed shapes with
    // different field sets. Go directly to union_shapes which handles all
    // cases correctly. Open shapes need subtype checks for canonical
    // representation.
    if let (
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: sk1,
            fields: fdm1,
        })),
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: sk2,
            fields: fdm2,
        })),
    ) = (get_node(&ty1), get_node(&ty2))
    {
        if typing_defs::is_nothing(sk1) && typing_defs::is_nothing(sk2) {
            let r = match reason {
                Some(r) => r,
                _ => union_reason(&r1, &r2),
            };
            let ty = union_shapes(approx_cancel_neg, env, (sk1, fdm1, &r1), (sk2, fdm2, &r2));
            return mk((r, ty));
        }
    }
    if utils::is_sub_type_for_union(env, &ty1, &ty2) {
        ty2
    } else if utils::is_sub_type_for_union(env, &ty2, &ty1) {
        ty1
    } else {
        let r = match reason {
            Some(r) => r,
            _ => union_reason(&r1, &r2),
        };
        let non_ty2 =
            typing_intersection::negate_type(env, reason::none(), &ty2, utils::Approx::ApproxUp);
        if utils::is_sub_type_for_union(env, &non_ty2, &ty1) {
            make_type::mixed(r)
        } else {
            let non_ty1 = typing_intersection::negate_type(
                env,
                reason::none(),
                &ty1,
                utils::Approx::ApproxUp,
            );
            if utils::is_sub_type_for_union(env, &non_ty1, &ty2) {
                make_type::mixed(r)
            } else {
                // Simplify t | (dynamic & not t) to dynamic, if t <:D dynamic
                match (
                    try_strip_dynamic_intersect(&ty1),
                    try_strip_dynamic_intersect(&ty2),
                ) {
                    (Some(ty1a), _) if ty_equal(None, &ty1a, &non_ty2) => make_type::dynamic(r2),
                    (_, Some(ty2a)) if ty_equal(None, &ty2a, &non_ty1) => make_type::dynamic(r1),
                    _ => union_lists(approx_cancel_neg, env, &[ty1], &[ty2], r),
                }
            }
        }
    }
}

fn simplify_union(
    approx_cancel_neg: bool,
    env: &mut Env,
    ty1: Ty,
    ty2: Ty,
    r: Reason,
) -> Option<Ty> {
    if log::should_log(env, 2) {
        let (r_, ty1_, ty2_) = (r.clone(), ty1.clone(), ty2.clone());
        log::log_simplify_union(env, &r_, &ty1_, &ty2_, move |env| {
            simplify_union_(approx_cancel_neg, env, ty1, ty2, r)
        })
    } else {
        simplify_union_(approx_cancel_neg, env, ty1, ty2, r)
    }
}

/// Simplify the union of two types, for example (int|float) as num.
/// Returns None if there is no simplification.
/// Does not deal with null, options, unions and intersections, which are dealt with by union_lists.
/// If approx_cancel_neg is true, then some unions with negations are treated over-approximately:
/// C<t> | not C simplifies to mixed.
fn simplify_union_(
    approx_cancel_neg: bool,
    env: &mut Env,
    ty1: Ty,
    ty2: Ty,
    r: Reason,
) -> Option<Ty> {
    if ty_equal(None, &ty1, &ty2) {
        Some(ty1)
    } else if utils::is_sub_type_for_union(env, &ty1, &ty2) {
        Some(ty2)
    } else if utils::is_sub_type_for_union(env, &ty2, &ty1) {
        Some(ty1)
    } else {
        simplify_non_subtype_union(approx_cancel_neg, env, ty1, ty2, r)
    }
}

/// `(Tclass ((_, c2), _, _), Tneg (_, IsTag (ClassTag (c1, c1_args))))`, in
/// either order: `(c1, c1_args, c2, exact, c2_args)`.
fn neg_class_tag_and_class<'a>(
    ty1: &'a Ty_,
    ty2: &'a Ty_,
) -> Option<(
    &'a String,
    &'a [crate::typing_defs_core::TypeTagGeneric],
    &'a String,
    &'a Exact,
    &'a [Ty],
)> {
    match (ty1, ty2) {
        (
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ClassTag(c1, c1_args)))),
            Ty_::Tclass((_, c2), e, c2_args),
        )
        | (
            Ty_::Tclass((_, c2), e, c2_args),
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ClassTag(c1, c1_args)))),
        ) => Some((c1, c1_args, c2, e, c2_args)),
        _ => None,
    }
}

/// Attempts to find a simplification for `ty1 | ty2`.
/// Won't attempt to check whether one is a subtype of the other.
fn simplify_non_subtype_union(
    approx_cancel_neg: bool,
    env: &mut Env,
    ty1: Ty,
    ty2: Ty,
    r: Reason,
) -> Option<Ty> {
    let ty1 = env::expand_type(env, ty1);
    let ty2 = env::expand_type(env, ty2);
    let r1 = get_reason(&ty1).clone();
    let r2 = get_reason(&ty2).clone();
    let neg_class = neg_class_tag_and_class(get_node(&ty1), get_node(&ty2));
    match (get_node(&ty1), get_node(&ty2)) {
        (Ty_::Tprim(Tprim::Tint), Ty_::Tprim(Tprim::Tfloat))
        | (Ty_::Tprim(Tprim::Tfloat), Ty_::Tprim(Tprim::Tint)) => {
            let r = union_reason(&r1, &r2);
            Some(make_type::num(r))
        }
        (Ty_::Tclass((p, id1), e1, tyl1), Ty_::Tclass((_, id2), e2, tyl2)) if id1 == id2 => {
            let e = exact_least_upper_bound(e1, e2);
            if tyl1.is_empty() {
                Some(mk((r, Ty_::Tclass((p.clone(), id1.clone()), e, tyl1.clone()))))
            } else {
                // The environment of the `try`, which the handler of
                // `Dont_simplify` returns.
                let env_before_try = env.clone();
                match union_class_or_newtype(approx_cancel_neg, env, id1, tyl1, tyl2) {
                    Ok(tyl) => Some(mk((r, Ty_::Tclass((p.clone(), id1.clone()), e, tyl)))),
                    Err(DontSimplify) => {
                        *env = env_before_try;
                        None
                    }
                }
            }
        }
        (Ty_::Tgeneric(name1), Ty_::Tgeneric(name2)) if name1 == name2 => {
            Some(mk((r, Ty_::Tgeneric(name1.clone()))))
        }
        (Ty_::TvecOrDict(tk1, tv1), Ty_::TvecOrDict(tk2, tv2)) => {
            let tk = union(env, None, Some(approx_cancel_neg), tk1.clone(), tk2.clone());
            let tv = union(env, None, Some(approx_cancel_neg), tv1.clone(), tv2.clone());
            Some(mk((r, Ty_::TvecOrDict(tk, tv))))
        }
        (Ty_::Tdependent(dep1, tcstr1), Ty_::Tdependent(dep2, tcstr2)) if dep1 == dep2 => {
            let tcstr = union(env, None, Some(approx_cancel_neg), tcstr1.clone(), tcstr2.clone());
            Some(mk((r, Ty_::Tdependent(*dep1, tcstr))))
        }
        (Ty_::Tdependent(_, ty1_), _) if utils::is_class(ty1_) => {
            ty_equiv(env, ty1_.clone(), ty2.clone(), false)
        }
        (_, Ty_::Tdependent(_, ty2_)) if utils::is_class(ty2_) => {
            ty_equiv(env, ty2_.clone(), ty1.clone(), false)
        }
        (Ty_::Tnewtype(id1, tyl1, _), Ty_::Tnewtype(id2, tyl2, _))
            if tyl1.len() == 1
                && tyl2.len() == 1
                && id1 == id2
                && id1 == sn::classes::SUPPORT_DYN =>
        {
            let r = union_reason(&r1, &r2);
            let try_union =
                simplify_union(approx_cancel_neg, env, tyl1[0].clone(), tyl2[0].clone(), r.clone());
            try_union.map(|ty| make_type::supportdyn(r, ty))
        }
        (Ty_::Tnewtype(id1, tyl1, tcstr1), Ty_::Tnewtype(id2, tyl2, tcstr2))
            if id1 == id2 && id1 != sn::classes::SUPPORT_DYN =>
        {
            if tyl1.is_empty() {
                Some(ty1.clone())
            } else {
                // The environment of the `try`, which the handler of
                // `Dont_simplify` returns.
                let env_before_try = env.clone();
                match union_class_or_newtype(approx_cancel_neg, env, id1, tyl1, tyl2) {
                    Ok(tyl) => {
                        let tcstr = union(
                            env,
                            None,
                            Some(approx_cancel_neg),
                            tcstr1.clone(),
                            tcstr2.clone(),
                        );
                        Some(mk((r, Ty_::Tnewtype(id1.clone(), tyl, tcstr))))
                    }
                    Err(DontSimplify) => {
                        *env = env_before_try;
                        None
                    }
                }
            }
        }
        (Ty_::TclassPtr(ty1_), Ty_::TclassPtr(ty2_)) => {
            // Follows newtype classname<T> equal case above
            let ty = union(env, None, Some(approx_cancel_neg), ty1_.clone(), ty2_.clone());
            Some(mk((r, Ty_::TclassPtr(ty))))
        }
        (Ty_::TclassPtr(ty_c), Ty_::Tnewtype(cn, cn_args, _))
        | (Ty_::Tnewtype(cn, cn_args, _), Ty_::TclassPtr(ty_c))
            if cn_args.len() == 1 && cn == sn::classes::CLASS_OR_CLASSNAME =>
        {
            let ty = union(env, None, Some(approx_cancel_neg), ty_c.clone(), cn_args[0].clone());
            Some(make_type::class_or_classname(r, vec![ty]))
        }
        // TODO: optional and variadic fields T201398626 T201398652
        (
            Ty_::Ttuple(TupleType {
                required: t_required1,
                optional: t_optional1,
                extra: TupleExtra::Tvariadic(t_variadic1),
            }),
            Ty_::Ttuple(TupleType {
                required: t_required2,
                optional: t_optional2,
                extra: TupleExtra::Tvariadic(t_variadic2),
            }),
        ) if t_optional1.is_empty() && t_optional2.is_empty() => {
            if t_required1.len() == t_required2.len() {
                let t_required: Vec<Ty> = t_required1
                    .iter()
                    .zip(t_required2.iter())
                    .map(|(ty1, ty2)| {
                        union(env, None, Some(approx_cancel_neg), ty1.clone(), ty2.clone())
                    })
                    .collect();
                let t_variadic = union(
                    env,
                    None,
                    Some(approx_cancel_neg),
                    t_variadic1.clone(),
                    t_variadic2.clone(),
                );
                Some(mk((
                    r,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: vec![],
                        extra: TupleExtra::Tvariadic(t_variadic),
                    }),
                )))
            } else {
                None
            }
        }
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
            let ty = union_shapes(
                approx_cancel_neg,
                env,
                (shape_kind1, fdm1, &r1),
                (shape_kind2, fdm2, &r2),
            );
            Some(mk((r, ty)))
        }
        (Ty_::Tfun(ft1), Ty_::Tfun(ft2)) => {
            // `union_funs` raises `Dont_simplify` before it does anything, so
            // the environment of the `try` is the current one.
            match union_funs(approx_cancel_neg, env, ft1, ft2) {
                Ok(ft) => Some(mk((r, Ty_::Tfun(std::rc::Rc::new(ft))))),
                Err(DontSimplify) => None,
            }
        }
        (Ty_::Tneg(_), Ty_::Tclass(..)) | (Ty_::Tclass(..), Ty_::Tneg(_))
            if matches!(neg_class, Some((c1, c1_args, c2, Exact::Exact, c2_args))
                if c1_args.is_empty() && c2_args.is_empty() && c1 == c2) =>
        {
            Some(make_type::mixed(r))
        }
        (Ty_::Tneg(_), Ty_::Tclass(..)) | (Ty_::Tclass(..), Ty_::Tneg(_))
            if matches!(neg_class, Some((c1, c1_args, c2, Exact::Nonexact(_), c2_args))
                if c1_args.is_empty() && c2_args.is_empty() && utils::is_sub_class_refl(env, c1, c2)) =>
        {
            // This union is mixed iff for all objects o,
            // o not in complement (union tyl. c1<tyl>) implies o in c2,
            // which is equivalent to
            // (union tyl. c1<tyl>) subset c2.
            // This is certainly the case when c1 is a sub-class of c2, since
            // c2 has no type parameters.
            Some(make_type::mixed(r))
        }
        (Ty_::Tneg(_), Ty_::Tclass(..)) | (Ty_::Tclass(..), Ty_::Tneg(_))
            if matches!(neg_class, Some((c1, c1_args, c2, Exact::Nonexact(_), c2_args))
                if !c2_args.is_empty()
                    && approx_cancel_neg
                    && utils::is_sub_class_refl(env, c1, c2)
                    && c1_args.iter().all(is_type_tag_generic_wildcard)) =>
        {
            // Unlike the case where c2 has no parameters, here we can get a situation
            // where c1 is a sub-class of c2, but they don't union to mixed. For example,
            // Vector<int> | not Vector, which doesn't include Vector<string>, etc. However,
            // we can still approximate up to mixed when it would be both sound and convenient,
            // as controlled by the approx_cancel_neg flag.
            Some(make_type::mixed(r))
        }
        (Ty_::Tneg(_), Ty_::Tclass(..)) | (Ty_::Tclass(..), Ty_::Tneg(_))
            if matches!(neg_class, Some((c1, c1_args, c2, Exact::Exact, c2_args))
                if !c2_args.is_empty()
                    && approx_cancel_neg
                    && c1 == c2
                    && c1_args.iter().all(is_type_tag_generic_wildcard)) =>
        {
            Some(make_type::mixed(r))
        }
        (
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::NumTag))),
            Ty_::Tprim(Tprim::Tarraykey),
        )
        | (
            Ty_::Tprim(Tprim::Tarraykey),
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::NumTag))),
        ) => Some(make_type::neg(
            r.clone(),
            TypePredicate(r, TypePredicate_::IsTag(TypeTag::FloatTag)),
        )),
        (
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ArraykeyTag))),
            Ty_::Tprim(Tprim::Tnum),
        )
        | (
            Ty_::Tprim(Tprim::Tnum),
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ArraykeyTag))),
        ) => Some(make_type::neg(
            r.clone(),
            TypePredicate(
                r,
                TypePredicate_::IsTag(TypeTag::ClassTag(C_STRING.to_string(), vec![])),
            ),
        )),
        (Ty_::Tintersection(tyl1), Ty_::Tintersection(tyl2)) => {
            let (common_tyl, tyl1_, tyl2_) = typing_algebra::factorize_common_types(tyl1, tyl2);
            if common_tyl.is_empty() {
                // No common types, fall back to default case
                ty_equiv(env, ty1.clone(), ty2.clone(), false)
            } else if tyl1_.is_empty() || tyl2_.is_empty() {
                // If one of the intersections is now empty, then the union is mixed,
                // and we just return the common types from the intersetion
                Some(make_type::intersection(r, common_tyl))
            } else {
                let union_ty = match (tyl1_.len(), tyl2_.len()) {
                    (1, 1) => {
                        // It seems like it is wasteful to simplify with the main union function which checks
                        // subtyping. If there was a subtype relationship between these two, there
                        // would have been one with the common types in, and we wouldn't get here.
                        // However, in some cases, that is not the case. E.g., ?#1 & t <: #1 & t will
                        // not pass the initial sub-type check, but will here
                        union(
                            env,
                            None,
                            Some(approx_cancel_neg),
                            tyl1_[0].clone(),
                            tyl2_[0].clone(),
                        )
                    }
                    // `([ty], tyl) | (tyl, [ty])`
                    (1, _) => union_lists(
                        approx_cancel_neg,
                        env,
                        &[tyl1_[0].clone()],
                        &[make_type::intersection(r1.clone(), tyl2_)],
                        r.clone(),
                    ),
                    (_, 1) => union_lists(
                        approx_cancel_neg,
                        env,
                        &[tyl2_[0].clone()],
                        &[make_type::intersection(r1.clone(), tyl1_)],
                        r.clone(),
                    ),
                    _ => make_type::union(
                        r.clone(),
                        vec![
                            make_type::intersection(r1.clone(), tyl1_),
                            make_type::intersection(r2.clone(), tyl2_),
                        ],
                    ),
                };
                if common_tyl.len() == 1 {
                    let common_ty = common_tyl.into_iter().next().unwrap();
                    let inter_ty = typing_intersection::intersect(env, r, common_ty, union_ty);
                    Some(inter_ty)
                } else {
                    let mut tyl = vec![union_ty];
                    tyl.extend(common_tyl);
                    Some(make_type::intersection(r, tyl))
                }
            }
        }
        // TODO with Tclass, union type arguments if covariant
        (_, Ty_::Tneg(predicate)) => {
            simplify_union_with_negation(env, &ty1, predicate, &ty1, &ty2, r)
        }
        (Ty_::Tneg(predicate), _) => {
            simplify_union_with_negation(env, &ty2, predicate, &ty1, &ty2, r)
        }
        (
            Ty_::Tprim(_)
            | Ty_::Tdynamic(_)
            | Ty_::Tgeneric(_)
            | Ty_::Tnewtype(..)
            | Ty_::Tdependent(..)
            | Ty_::Tclass(..)
            | Ty_::Ttuple(_)
            | Ty_::Tfun(_)
            | Ty_::Tshape(_)
            | Ty_::Tvar(_)
            | Ty_::TvecOrDict(..)
            // If T cannot be null, `union T nonnull = nonnull`. However, it's hard
            // to say whether a given T can be null - e.g. opaque newtypes, dependent
            // types, etc. - so for now we leave it here.
            // TODO improve that.
            | Ty_::Tnonnull
            | Ty_::Tany(_)
            | Ty_::Tintersection(_)
            | Ty_::Toption(_)
            | Ty_::Tunion(_)
            | Ty_::Tlabel(_)
            | Ty_::Taccess(_)
            | Ty_::TclassPtr(_),
            _,
        ) => ty_equiv(env, ty1.clone(), ty2.clone(), false),
    }
}

/// The case `ty | Tneg predicate` of `simplify_non_subtype_union` (either way
/// round): `ty` is the one that is not the negation, `ty1` and `ty2` the two
/// types of `simplify_non_subtype_union`.
fn simplify_union_with_negation(
    env: &mut Env,
    ty: &Ty,
    predicate: &TypePredicate,
    ty1: &Ty,
    ty2: &Ty,
    r: Reason,
) -> Option<Ty> {
    match typing_refinement::ty_predicate::of_ty(env, ty).ok() {
        Some(other) if equal_type_predicate(predicate, &other) => Some(make_type::mixed(r)),
        _ => ty_equiv(env, ty1.clone(), ty2.clone(), false),
    }
}

/// Recognise a pattern t1 | t2 | t3 | (t4 & t5 & t6) which happens frequently
/// at control flow join points, and check for types that drop out of the intersection
/// because they union to mixed with types in the union. Assume that all of the types
/// in tyl1 and tyl2 are not unions, having been processed by decompose in the
/// union_lists function. The semantics are that tyl1 and tyl2 are the union of their
/// elements, and we are building the union of the two lists. Instead of just appending,
/// we look for the special case where one of the elements of tyl1 or tyl2 is itself
/// an intersection, and try to cancel things out. We return the simplified
/// lists for further processing.
///
/// For example if tyl1 = [bool; int; string] represents bool | int | string, and
/// tyl2 = [float; (dynamic & not int & not string)],
/// then to union tyl1 and tyl2, we can remove the not int and not string conjuncts
/// from tyl2 because they union to mixed with elements of tyl1. Thus we end up with
/// a result [bool; int; string], [float; dynamic]
fn try_special_union_of_intersection(
    approx_cancel_neg: bool,
    env: &mut Env,
    tyl1: Vec<Ty>,
    tyl2: Vec<Ty>,
    r: &Reason,
) -> (Vec<Ty>, Vec<Ty>) {
    // Assume that inter_ty is an intersection type and look for a pairs of a conjunct in
    // inter_ty and an element of tyl that union to mixed. Remove these from the intersection,
    // and return the remaining elements of the intersection,
    // or return None indicating that no pairs were found.
    //
    // If inter_ty is wrapped in supportdyn, remove it.
    // This is justified because supportdyn<t1 & t2> | u = (supportdyn<mixed> | u) & (t1 | u) & (t2 | u)
    // and if (say) t1 | u = mixed, then we get (supportdyn<mixed> | u) & (t2 | u) and we can pull out
    // u to get supportdyn<t2> | u.
    // If any of the types in tyl are supportdyn, then we can remove that too because
    // in supportdyn<t1 & t2> | supportdyn<u> we can lift the supportdyn out, simplify and then push it back.
    let simplify_inter = |env: &mut Env, inter_ty: &Ty, tyl: &[Ty]| -> Option<Ty> {
        let mut changed = false;
        let (had_supportdyn_inter, stripped_inter_ty) =
            utils::strip_supportdyn(env, inter_ty.clone());
        let sd_r = get_reason(inter_ty).clone();
        let (inter_tyl, inter_r) =
            typing_intersection::destruct_inter_list(env, std::slice::from_ref(&stripped_inter_ty));
        let inter_r = inter_r.unwrap_or_else(|| r.clone());
        // `List.filter_map_env env inter_tyl ~f`
        let mut new_inter_tyl: Vec<Ty> = vec![];
        for inter_ty in inter_tyl {
            // `List.exists_env env tyl ~f`
            let mut exists = false;
            for ty in tyl {
                let stripped_ty = if had_supportdyn_inter {
                    utils::strip_supportdyn(env, ty.clone()).1
                } else {
                    ty.clone()
                };
                let union_is_mixed = match simplify_non_subtype_union(
                    approx_cancel_neg,
                    env,
                    inter_ty.clone(),
                    stripped_ty,
                    r.clone(),
                ) {
                    None => false,
                    Some(ty) => utils::is_mixed(env, &ty),
                };
                if union_is_mixed {
                    exists = true;
                    break;
                }
            }
            if exists {
                changed = true;
            } else {
                new_inter_tyl.push(inter_ty)
            }
        }
        if changed {
            let ty = make_type::intersection(inter_r, new_inter_tyl);
            if had_supportdyn_inter {
                Some(make_type::supportdyn(sd_r, ty))
            } else {
                Some(ty)
            }
        } else {
            None
        }
    };
    // `is_intersection env ty`: each test starts from `env`, and the
    // environment of `strip_supportdyn` is dropped.
    let is_intersection = |env: &Env, ty: &Ty| -> bool {
        let mut env = env.clone();
        let (_, ty) = utils::strip_supportdyn(&mut env, ty.clone());
        utils::is_tintersection(&env, &ty)
    };
    let (inter_tyl1, not_inter_tyl1): (Vec<Ty>, Vec<Ty>) = {
        let env: &Env = env;
        tyl1.iter()
            .cloned()
            .partition(|ty| is_intersection(env, ty))
    };
    let (inter_tyl2, not_inter_tyl2): (Vec<Ty>, Vec<Ty>) = {
        let env: &Env = env;
        tyl2.iter()
            .cloned()
            .partition(|ty| is_intersection(env, ty))
    };
    let res_tyl1 = if inter_tyl1.len() == 1 {
        match simplify_inter(env, &inter_tyl1[0], &not_inter_tyl2) {
            None => tyl1,
            Some(new_inter1) => {
                let mut tyl = vec![new_inter1];
                tyl.extend(not_inter_tyl1.iter().cloned());
                tyl
            }
        }
    } else {
        tyl1
    };
    let res_tyl2 = if inter_tyl2.len() == 1 {
        match simplify_inter(env, &inter_tyl2[0], &not_inter_tyl1) {
            None => tyl2,
            Some(new_inter1) => {
                let mut tyl = vec![new_inter1];
                tyl.extend(not_inter_tyl2);
                tyl
            }
        }
    } else {
        tyl2
    };
    (res_tyl1, res_tyl2)
}

/// Union two lists of types together.
/// This has complexity N*M where N, M are the sized of the two lists.
/// The two lists are first flattened and null and dynamic are extracted from them,
/// then we attempt to simplify each pair of types.
fn union_lists(approx_cancel_neg: bool, env: &mut Env, tyl1: &[Ty], tyl2: &[Ty], r: Reason) -> Ty {
    let product_ty_tyl = |env: &mut Env, ty1: Ty, tyl2: Vec<Ty>| -> Vec<Ty> {
        // `tyl_res` is consed onto: here it is pushed to.
        let mut ty1 = ty1;
        let mut tyl_res: Vec<Ty> = vec![];
        for ty2 in tyl2 {
            let ty_opt =
                simplify_union(approx_cancel_neg, env, ty1.clone(), ty2.clone(), r.clone());
            match ty_opt {
                None => tyl_res.push(ty2),
                Some(ty) => ty1 = ty,
            }
        }
        // `ty1 :: tyl_res`
        let mut res = vec![ty1];
        res.extend(tyl_res.into_iter().rev());
        res
    };
    let product = |env: &mut Env, tyl1: Vec<Ty>, tyl2: Vec<Ty>| -> Vec<Ty> {
        let mut tyl1 = tyl1.into_iter();
        let mut tyl2 = tyl2;
        loop {
            // `([], tyl) | (tyl, []) -> (env, tyl)`
            if tyl1.len() == 0 {
                return tyl2;
            }
            if tyl2.is_empty() {
                return tyl1.collect();
            }
            let ty1 = tyl1.next().unwrap();
            tyl2 = product_ty_tyl(env, ty1, tyl2);
        }
    };
    let (tyl1, r_null1, _r_union1, r_dyn1) = dest_union_list(env, tyl1);
    let (tyl2, r_null2, _r_union2, r_dyn2) = dest_union_list(env, tyl2);
    let (tyl1, tyl2) = try_special_union_of_intersection(approx_cancel_neg, env, tyl1, tyl2, &r);
    let tyl = product(env, tyl1, tyl2);
    let r_null = r_null1.or(r_null2);
    let r_dyn = r_dyn1.or(r_dyn2);
    make_union(env, r, &tyl, r_null, r_dyn)
}

fn union_funs(
    approx_cancel_neg: bool,
    env: &mut Env,
    fty1: &FunType,
    fty2: &FunType,
) -> Result<FunType, DontSimplify> {
    // TODO: If we later add fields to ft, they will be forgotten here.
    if typing_defs_flags::fun::equal(fty1.flags, fty2.flags)
        && ft_params_compare(None, &fty1.params, &fty2.params) == Ordering::Equal
    {
        let ft_ret = union(
            env,
            None,
            Some(approx_cancel_neg),
            fty1.ret.clone(),
            fty2.ret.clone(),
        );
        Ok(FunType {
            ret: ft_ret,
            ..fty1.clone()
        })
    } else {
        Err(DontSimplify)
    }
}

fn union_class_or_newtype(
    approx_cancel_neg: bool,
    env: &mut Env,
    name: &str,
    tyl1: &[Ty],
    tyl2: &[Ty],
) -> Result<Vec<Ty>, DontSimplify> {
    let tparams = env::get_class_or_typedef_tparams(env, name);
    union_tylists_w_variances(approx_cancel_neg, env, &tparams, tyl1, tyl2)
}

fn union_tylists_w_variances(
    approx_cancel_neg: bool,
    env: &mut Env,
    tparams: &[DeclTparam],
    tyl1: &[Ty],
    tyl2: &[Ty],
) -> Result<Vec<Ty>, DontSimplify> {
    let variances: Vec<ast_defs::Variance> = tparams.iter().map(|t| t.variance).collect();
    let variances = {
        let adjust_list_length =
            |l: Vec<ast_defs::Variance>, newlen: usize, filler: ast_defs::Variance| {
                let len = l.len();
                if len < newlen {
                    let mut l = l;
                    l.extend(std::iter::repeat_n(filler, newlen - len));
                    l
                } else {
                    // `List.sub l ~pos:0 ~len:newlen`
                    let mut l = l;
                    l.truncate(newlen);
                    l
                }
            };
        adjust_list_length(variances, tyl1.len(), ast_defs::Variance::Invariant)
    };
    let merge_ty_params = |env: &mut Env,
                           ty1: Ty,
                           ty2: Ty,
                           variance: ast_defs::Variance|
     -> Result<Ty, DontSimplify> {
        match variance {
            ast_defs::Variance::Covariant => {
                Ok(union(env, None, Some(approx_cancel_neg), ty1, ty2))
            }
            _ => {
                let ty_opt = ty_equiv(env, ty1, ty2, true);
                match ty_opt {
                    Some(ty) => Ok(ty),
                    None => Err(DontSimplify),
                }
            }
        }
    };
    // `try List.map3_env env tyl1 tyl2 variances ~f:merge_ty_params with
    // Invalid_argument _ -> raise Dont_simplify`: `List.map3_env` checks the
    // lengths before it calls `f`.
    if tyl1.len() != tyl2.len() || tyl2.len() != variances.len() {
        return Err(DontSimplify);
    }
    let mut tyl: Vec<Ty> = Vec::with_capacity(tyl1.len());
    for ((ty1, ty2), variance) in tyl1.iter().zip(tyl2.iter()).zip(variances) {
        tyl.push(merge_ty_params(env, ty1.clone(), ty2.clone(), variance)?);
    }
    Ok(tyl)
}

/// The OCaml returns the node `Tshape (Shape_simple ...)`, which the callers
/// make a type with.
fn union_shapes(
    approx_cancel_neg: bool,
    env: &mut Env,
    (shape_kind1, fdm1, r1): (&Ty, &t_shape_map::T<ShapeFieldType>, &Reason),
    (shape_kind2, fdm2, r2): (&Ty, &t_shape_map::T<ShapeFieldType>, &Reason),
) -> Ty_ {
    let shape_kind = union_shape_kind(
        approx_cancel_neg,
        env,
        shape_kind1.clone(),
        shape_kind2.clone(),
    );
    if std::ptr::eq(fdm1, fdm2) {
        // Fast path: physically identical field maps need no per-field work
        return Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: shape_kind,
            fields: fdm1.clone(),
        }));
    }
    // Use TShapeMap.merge (Stdlib.Map.merge) instead of the list-based
    // merge_env. This avoids O(n log n) overhead from bindings + find_opt
    // by walking both trees directly in O(n).
    let mut all_from_fdm1 = true;
    let mut all_from_fdm2 = true;
    // The keys of both maps (the key of `fdm1` where both have one), visited
    // in decreasing order as `Map.merge` does.
    let mut keys: BTreeSet<&t_shape_map::Key> = fdm1.keys().collect();
    keys.extend(fdm2.keys());
    let mut fdm: t_shape_map::T<ShapeFieldType> = t_shape_map::T::new();
    for k in keys.into_iter().rev() {
        let fieldopt1 = fdm1.get(k);
        let fieldopt2 = fdm2.get(k);
        let field = match (fieldopt1, fieldopt2) {
            // Fast path: physically identical field records — skip union
            (Some(f1), Some(f2)) if f1.optional == f2.optional && phys_equal(&f1.ty, &f2.ty) => {
                Some(f1.clone())
            }
            _ => match ((shape_kind1, fieldopt1, r1), (shape_kind2, fieldopt2, r2)) {
                ((_, None, _), (_, None, _)) => None,
                // key is present on one side but not the other
                ((_, Some(ShapeFieldType { ty: sft_ty, .. }), _), (shape_kind_other, None, r))
                | ((shape_kind_other, None, r), (_, Some(ShapeFieldType { ty: sft_ty, .. }), _)) => {
                    let sft_ty = if typing_defs::is_nothing(shape_kind_other) {
                        sft_ty.clone()
                    } else {
                        let r = reason::missing_optional_field((
                            reason::to_pos(r),
                            utils::get_printable_shape_field_name(&k.0).to_string(),
                        ));
                        with_reason(shape_kind_other.clone(), r)
                    };
                    all_from_fdm1 = false;
                    all_from_fdm2 = false;
                    Some(ShapeFieldType {
                        optional: true,
                        ty: sft_ty,
                    })
                }
                // key is present on both sides
                (
                    (
                        _,
                        Some(ShapeFieldType {
                            optional: optional1,
                            ty: ty1,
                        }),
                        _,
                    ),
                    (
                        _,
                        Some(ShapeFieldType {
                            optional: optional2,
                            ty: ty2,
                        }),
                        _,
                    ),
                ) => {
                    let sft_optional = *optional1 || *optional2;
                    let sft_ty =
                        union(env, None, Some(approx_cancel_neg), ty1.clone(), ty2.clone());
                    if !(sft_optional == *optional1 && phys_equal(&sft_ty, ty1)) {
                        all_from_fdm1 = false;
                    }
                    if !(sft_optional == *optional2 && phys_equal(&sft_ty, ty2)) {
                        all_from_fdm2 = false;
                    }
                    Some(ShapeFieldType {
                        optional: sft_optional,
                        ty: sft_ty,
                    })
                }
            },
        };
        if let Some(field) = field {
            fdm.insert(k.clone(), field);
        }
    }
    // Preserve physical identity when result matches an input map.
    // This enables the phys_equal fast path for subsequent merges.
    let fdm = if all_from_fdm1 {
        fdm1.clone()
    } else if all_from_fdm2 {
        fdm2.clone()
    } else {
        fdm
    };
    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
        origin: TypeOrigin::MissingOrigin,
        unknown_value: shape_kind,
        fields: fdm,
    }))
}

fn union_shape_kind(
    approx_cancel_neg: bool,
    env: &mut Env,
    shape_kind1: Ty,
    shape_kind2: Ty,
) -> Ty {
    union(env, None, Some(approx_cancel_neg), shape_kind1, shape_kind2)
}

/// TODO: add a new reason with positions of merge point and possibly merged
/// envs.
fn union_reason(r1: &Reason, r2: &Reason) -> Reason {
    if reason::predicates::is_none(r1) {
        r2.clone()
    } else if reason::predicates::is_none(r2) {
        r1.clone()
    } else if reason::compare(r1, r2) <= 0 {
        r1.clone()
    } else {
        r2.clone()
    }
}

/// Takes a list of types, possibly including unions, and flattens it.
/// Returns a set of types.
/// If null is encountered (possibly in an option), get its reason and return it
/// in a separate optional reason (do not add null in the resulting set of types).
/// Do the same if dynamic is encountered.
/// This is because options and dynamic have to be "pushed out" of the resulting union.
///
/// The OCaml returns `(env, r_null, r_union, r_dyn, tys)`.
fn normalize_union(
    env: &mut Env,
    on_tyvar: Option<OnTyvar<'_>>,
    tyl: &[Ty],
) -> (Option<Reason>, Option<Reason>, Option<Reason>, ty_set::T) {
    /// The reasons that the inner `normalize_union` threads.
    struct Reasons {
        r_null: Option<Reason>,
        r_union: Option<Reason>,
        r_dyn: Option<Reason>,
    }
    /// The inner `normalize_union env tyl r_null r_union r_dyn`. For
    /// `ty :: tyl` it computes the set of `ty` (`tys'`), then the set of `tyl`
    /// (`tys`), and returns `TySet.union tys' tys`: the sets are computed from
    /// the first type to the last, and their unions made from the last to the
    /// first.
    fn normalize_union(
        env: &mut Env,
        on_tyvar: &mut Option<OnTyvar<'_>>,
        tyl: Vec<Ty>,
        reasons: &mut Reasons,
    ) -> ty_set::T {
        let mut sets: Vec<ty_set::T> = Vec::with_capacity(tyl.len());
        for ty in tyl {
            let ty = env::expand_type(env, ty);
            let r = get_reason(&ty).clone();
            enum Node {
                Var(tvid::T),
                Null,
                Option(Ty),
                Union(Vec<Ty>),
                DynamicNone,
                SupportDyn(Ty),
                Intersection,
                Other,
            }
            let node = match get_node(&ty) {
                Ty_::Tvar(v) => Node::Var(*v),
                Ty_::Tprim(Tprim::Tnull) => Node::Null,
                Ty_::Toption(ty_) => Node::Option(ty_.clone()),
                Ty_::Tunion(tyl_) => Node::Union(tyl_.clone()),
                Ty_::Tdynamic(None) => Node::DynamicNone,
                // See comment in dest_union above
                Ty_::Tdynamic(Some(_)) => Node::Other,
                Ty_::Tnewtype(n, tyl_, _) if tyl_.len() == 1 && n == sn::classes::SUPPORT_DYN => {
                    Node::SupportDyn(tyl_[0].clone())
                }
                Ty_::Tintersection(_) => Node::Intersection,
                _ => Node::Other,
            };
            let tys_ = match node {
                Node::Var(v) if on_tyvar.is_some() => {
                    let ty_ = match on_tyvar {
                        Some(on_tyvar) => on_tyvar(env, r, v),
                        None => unreachable!(),
                    };
                    if ty_equal(None, &ty, &ty_) {
                        // `proceed env ty'`
                        ty_set::singleton(ty_)
                    } else {
                        normalize_union(env, on_tyvar, vec![ty_], reasons)
                    }
                }
                Node::Null => {
                    reasons.r_null = orr(reasons.r_null.take(), r);
                    ty_set::empty()
                }
                Node::Option(ty_) => {
                    reasons.r_null = orr(reasons.r_null.take(), r);
                    normalize_union(env, on_tyvar, vec![ty_], reasons)
                }
                Node::Union(tyl_) => {
                    reasons.r_union = orr(reasons.r_union.take(), r);
                    normalize_union(env, on_tyvar, tyl_, reasons)
                }
                Node::DynamicNone => {
                    reasons.r_dyn = orr(reasons.r_dyn.take(), r);
                    ty_set::empty()
                }
                Node::SupportDyn(ty_) => {
                    let (_, ty_) = utils::strip_supportdyn(env, ty_);
                    let ty_ = utils::simplify_intersections(env, reborrow_on_tyvar(on_tyvar), &ty_);
                    let ty_ = utils::simple_make_supportdyn(r, env, ty_);
                    ty_set::singleton(ty_)
                }
                Node::Intersection => {
                    let ty = utils::simplify_intersections(env, reborrow_on_tyvar(on_tyvar), &ty);
                    let ety = env::expand_type(env, ty.clone());
                    match get_node(&ety) {
                        Ty_::Tintersection(_) => ty_set::singleton(ty),
                        _ => normalize_union(env, on_tyvar, vec![ty], reasons),
                    }
                }
                Node::Var(_) | Node::Other => ty_set::singleton(ty),
            };
            sets.push(tys_);
        }
        let mut tys = ty_set::empty();
        for tys_ in sets.into_iter().rev() {
            tys = ty_set::union(&tys_, &tys);
        }
        tys
    }
    let mut on_tyvar = on_tyvar;
    let mut reasons = Reasons {
        r_null: None,
        r_union: None,
        r_dyn: None,
    };
    let tys = normalize_union(env, &mut on_tyvar, tyl.to_vec(), &mut reasons);
    (reasons.r_null, reasons.r_union, reasons.r_dyn, tys)
}

/// Is this type minimal with respect to the ground subtype ordering, if we ignore the nothing type?
/// Examples are exact or final non-generic classes.
/// Non-examples (surprisingly) are int or string (because an enum can be a subtype).
///
/// Another example is classname<C>, if C is minimal, and this pattern occurs
/// frequently e.g. vec[C::class, D::class].
///
/// Note that doesn't work for general covariant classes or built-ins e.g. vec<exact C> is not
/// minimal because vec<nothing> <: vec<exact C>. But classname<nothing> is uninhabited so it's
/// ok to suppose that it is equivalent to nothing.
///
/// Finally note that if we did treat string, int, and float as minimal, then the code in
/// union_list_2_by_2 would not simplify int|float to num or string|classname<C> to string.
fn is_minimal(env: &Env, ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tclass(_, Exact::Exact, tyl) if tyl.is_empty() => true,
        Ty_::Tclass((_, name), _, _) if C_STRING == name => false,
        Ty_::Tclass((_, name), _, tyl) if tyl.is_empty() => match env::get_class(env, name) {
            decl_entry::T::Found(cd) => cls::final_(&cd),
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
        },
        Ty_::Tnewtype(name, tyl, _)
            if tyl.len() == 1
                && (name == sn::classes::CLASS_NAME || name == sn::classes::CLASS_OR_CLASSNAME) =>
        {
            is_minimal(env, &tyl[0])
        }
        Ty_::Tdependent(..) => true,
        _ => false,
    }
}

/// Construct union of a list of types by applying binary union pairwise.
/// This uses a quadratic number of subtype tests so we apply the following
/// optimization that's particularly useful for the common pattern of vec[C1::class,...,Cn::class].
///
/// First split the list of types into "final" types (those known to have no non-empty subtypes)
/// and non-final types (that might have a non-empty subtype).
/// For the non-final types, we apply binary union pointwise, which is quadratic in the number
/// of types. Then for each of the final types we drop those that subtype any of the types
///  in the result.
///
/// If m is the number of final types, and n is the number of non-final types, the first
/// stage uses O(n^2) subtype tests and the second stage uses O(mn) subtype tests.
/// One common pattern is a union of exact classnames: constructing this will involve no
/// subtype tests at all.
fn union_list_2_by_2(approx_cancel_neg: bool, env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Vec<Ty> {
    let (tyl_final, tyl_nonfinal): (Vec<Ty>, Vec<Ty>) = {
        let env: &Env = env;
        tyl.into_iter().partition(|ty| is_minimal(env, ty))
    };
    let mut reduced_nonfinal: Vec<Ty> = vec![];
    for ty in tyl_nonfinal {
        // `union_ty_w_tyl env ty res_tyl []`; `tyl_acc` is consed onto: here
        // it is pushed to.
        let res_tyl = std::mem::take(&mut reduced_nonfinal);
        let mut tyl_acc: Vec<Ty> = vec![];
        let mut rest = res_tyl.into_iter();
        let mut merged: Option<Vec<Ty>> = None;
        while let Some(ty_) = rest.next() {
            let union_opt =
                simplify_union(approx_cancel_neg, env, ty.clone(), ty_.clone(), r.clone());
            match union_opt {
                None => tyl_acc.push(ty_),
                Some(union) => {
                    // `tyl @ (union :: tyl_acc)`
                    let mut res: Vec<Ty> = rest.by_ref().collect();
                    res.push(union);
                    res.extend(tyl_acc.drain(..).rev());
                    merged = Some(res);
                    break;
                }
            }
        }
        reduced_nonfinal = match merged {
            Some(res) => res,
            None => {
                // `ty :: tyl_acc`
                let mut res = vec![ty];
                res.extend(tyl_acc.into_iter().rev());
                res
            }
        };
    }
    let reduced_final: Vec<Ty> = tyl_final
        .into_iter()
        .filter(|fty| {
            !reduced_nonfinal
                .iter()
                .any(|ty| utils::is_sub_type_for_union(env, fty, ty))
        })
        .collect();
    let mut res = reduced_final;
    res.extend(reduced_nonfinal);
    res
}

/// Computes the union of a list of types by unioning types two by two.
/// This has quadratic complexity, but in practice we benefit from aggressively
/// simplified unions.
pub fn union_list(env: &mut Env, approx_cancel_neg: Option<bool>, r: Reason, tyl: &[Ty]) -> Ty {
    /// The first OCaml definition, which the second one shadows.
    fn union_list(env: &mut Env, approx_cancel_neg: bool, r: Reason, tyl: &[Ty]) -> Ty {
        if let [ty] = tyl {
            if is_own_union(env, ty) {
                return ty.clone();
            }
        }
        let (r_null, _r_union, r_dyn, tys) = normalize_union(env, None, tyl);
        let tyl = union_list_2_by_2(approx_cancel_neg, env, r.clone(), ty_set::elements(&tys));
        make_union(env, r, &tyl, r_null, r_dyn)
    }
    let approx_cancel_neg = approx_cancel_neg.unwrap_or(false);
    if log::should_log(env, 1) {
        let r_ = r.clone();
        log::log_union_list(env, &r_, tyl, |env| {
            union_list(env, approx_cancel_neg, r, tyl)
        })
    } else {
        union_list(env, approx_cancel_neg, r, tyl)
    }
}

pub fn fold_union(env: &mut Env, approx_cancel_neg: Option<bool>, r: Reason, tyl: &[Ty]) -> Ty {
    let approx_cancel_neg = approx_cancel_neg.unwrap_or(false);
    let mut acc = make_type::nothing(r);
    for ty in tyl {
        acc = union(env, None, Some(approx_cancel_neg), acc, ty.clone());
    }
    acc
}

/// Simplify the unions within a type.
/// Return the result in a flattened, "normalized" form, with options and like types being
/// "pushed out" of the result.
/// E.g. transforms `(int | (int | null | X))` into `?(int | X)`
///
/// This has quadratic complexity, but in practice we benefit from aggressively
/// simplified unions.
/// Not in the OCaml: the union of the list `[ty]` (`simplify_unions`,
/// `union_list`) is `ty` itself when `normalize_union` keeps it as it is (no
/// type variable, null, option, union, dynamic, supportdyn or intersection:
/// it is its own set), as `union_list_2_by_2` gives back the one type of a
/// list (`is_minimal` only reads, but looks classes up: not when that would
/// record a dependency), and `make_union` of one type with no null or
/// dynamic reason is that type (not a union or intersection: nothing to
/// wrap in a type variable). `on_tyvar` is then not called either.
pub(crate) fn is_own_union(env: &Env, ty: &Ty) -> bool {
    let kept = match get_node(ty) {
        Ty_::Tvar(_)
        | Ty_::Tprim(Tprim::Tnull)
        | Ty_::Toption(_)
        | Ty_::Tunion(_)
        | Ty_::Tdynamic(None)
        | Ty_::Tintersection(_) => false,
        Ty_::Tnewtype(n, tyl, _) => !(tyl.len() == 1 && n == sn::classes::SUPPORT_DYN),
        _ => true,
    };
    kept && !env::deps::records_dependency_edges(env)
}

pub fn simplify_unions(
    env: &mut Env,
    approx_cancel_neg: Option<bool>,
    on_tyvar: Option<OnTyvar<'_>>,
    ty: Ty,
) -> Ty {
    /// The first OCaml definition, which the second one shadows.
    fn simplify_unions(
        env: &mut Env,
        approx_cancel_neg: bool,
        on_tyvar: Option<OnTyvar<'_>>,
        ty: Ty,
    ) -> Ty {
        if is_own_union(env, &ty) {
            return ty;
        }
        let r = get_reason(&ty).clone();
        let (r_null, r_union, r_dyn, tys) =
            normalize_union(env, on_tyvar, std::slice::from_ref(&ty));
        let tyl = union_list_2_by_2(approx_cancel_neg, env, r.clone(), ty_set::elements(&tys));
        let r = r_union.unwrap_or(r);
        make_union(env, r, &tyl, r_null, r_dyn)
    }
    let approx_cancel_neg = approx_cancel_neg.unwrap_or(false);
    if log::should_log(env, 1) {
        let ty_ = ty.clone();
        log::log_simplify_unions(env, &ty_, move |env| {
            simplify_unions(env, approx_cancel_neg, on_tyvar, ty)
        })
    } else {
        simplify_unions(env, approx_cancel_neg, on_tyvar, ty)
    }
}
