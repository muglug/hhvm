// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_intersection.ml`. See `hh/PORTING.md`.
//!
//! # Layout
//!
//! - `module Log`, `module TrackedOperation` and `module Recursion_tracker`
//!   are [`log`], [`tracked_operation`] and [`recursion_tracker`] (the local
//!   module, which applies the functor of `crate::recursion_tracker`).
//! - `intersect` and `intersect_list` are defined twice: in the recursive
//!   group (with a recursion tracker), and at the end of the module, where
//!   they start from an empty tracker and shadow the first ones. The first
//!   ones are in the private module [`tracked`]; the functions of the
//!   recursive group, and `simplify_intersections`, call them there, as in
//!   OCaml.
//! - `exception Nothing` is the error type [`Nothing`]: `intersect_shapes`,
//!   the only function that raises it, returns a `Result`, and `intersect_`,
//!   which catches it, goes back to the environment it had before its `try`
//!   (nothing happens between the `try` and the call of `intersect_shapes`).
//! - The `let () = Utils.negate_type_ref := negate_type` (and the same for
//!   `simplify_intersections` and `intersect_list`) at the end of the OCaml
//!   are done by `crate::typing_utils`, which owns those references.
//!
//! # Lists
//!
//! Several functions build lists by consing onto an accumulator. Here the
//! accumulator is a `Vec` that is pushed to, and it is reversed where OCaml
//! uses the list: the order of the elements of the results, which shows in
//! types and messages, is the OCaml one.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::tvid;
use crate::typing_case_type_variant;
use crate::typing_defs;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::Exact;
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
use crate::typing_defs_core::TypeTagGeneric;
use crate::typing_defs_core::deref;
use crate::typing_defs_core::equal_locl_ty;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::ty_equal;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_log;
/// `module MkType = Typing_make_type`
use crate::typing_make_type as mk_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;
/// `module Utils = Typing_utils`
use crate::typing_utils as utils;
/// The `?on_tyvar` argument of `simplify_intersections`:
/// `env -> Reason.t -> Tvid.t -> env * locl_ty`.
use crate::typing_utils::OnTyvar;

/// `?on_tyvar` passed on to a call: the callback, reborrowed for the call.
fn reborrow_on_tyvar<'b>(on_tyvar: &'b mut Option<OnTyvar<'_>>) -> Option<OnTyvar<'b>> {
    match on_tyvar {
        Some(on_tyvar) => Some(&mut **on_tyvar),
        None => None,
    }
}

/// `exception Nothing`
#[derive(Debug)]
struct Nothing;

/// `orr r_opt r = Some (Option.value r_opt ~default:r)`
fn orr(r_opt: Option<Reason>, r: Reason) -> Option<Reason> {
    Some(r_opt.unwrap_or(r))
}

/// `module Log`
mod log {
    use super::*;

    pub fn should_log(env: &Env, level: isize) -> bool {
        typing_log::should_log(env, "intersection", level)
    }

    /// `log_intersection env r ty1 ty2 f`. The `'a` of `Typing_log.log_function`
    /// is the environment with the result of `f`.
    pub fn log_intersection(
        env: &mut Env,
        r: &Reason,
        ty1: &Ty,
        ty2: &Ty,
        f: impl FnOnce(&mut Env) -> Ty,
    ) -> Ty {
        let arguments = vec![
            ("ty1".to_string(), typing_print::debug(env, ty1)),
            ("ty2".to_string(), typing_print::debug(env, ty2)),
        ];
        let (_env, ty) = typing_log::log_function(
            &reason::to_pos(r),
            "Typing_intersection.intersect",
            &arguments,
            |(env, ty): &(&mut Env, Ty)| {
                // The environment that `expand_type` returns is only used to
                // print the type.
                let mut env = (**env).clone();
                let ty = env::expand_type(&mut env, ty.clone());
                Some(typing_print::debug(&env, &ty))
            },
            move || {
                let ty = f(env);
                (env, ty)
            },
        );
        ty
    }
}

/// `module TrackedOperation`
mod tracked_operation {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct T {
        pub ty1: Ty,
        pub ty2: Ty,
    }

    /// `[@@deriving eq]`: `Typing_defs.equal_locl_ty` on the fields, in order.
    pub fn equal(a: &T, b: &T) -> bool {
        equal_locl_ty(&a.ty1, &b.ty1) && equal_locl_ty(&a.ty2, &b.ty2)
    }

    impl crate::recursion_tracker::Operation for T {
        fn equal(a: &Self, b: &Self) -> bool {
            equal(a, b)
        }
    }
}

/// `module Recursion_tracker`: `include Recursion_tracker.Make
/// (TrackedOperation)`, whose `t`, `empty` and
/// `add_op_and_check_infinite_recursion` are those of
/// `crate::recursion_tracker::make` at `tracked_operation::T`, and
/// `check_infinite_recursion`. The signature of the OCaml module hides
/// `add_op_and_check_infinite_recursion` and `is_type_alias`.
mod recursion_tracker {
    use super::*;

    /// `Recursion_tracker.Make (TrackedOperation).t`
    pub type T = crate::recursion_tracker::make::T<tracked_operation::T>;

    pub fn empty() -> T {
        crate::recursion_tracker::make::empty()
    }

    fn add_op_and_check_infinite_recursion(
        t: T,
        op: tracked_operation::T,
    ) -> Result<T, tracked_operation::T> {
        crate::recursion_tracker::make::add_op_and_check_infinite_recursion(t, op)
    }

    fn is_type_alias(ty: &Ty) -> bool {
        match get_node(ty) {
            Ty_::Tnewtype(..) => true,
            _ => false,
        }
    }

    pub fn check_infinite_recursion(t: &T, ty1: &Ty, ty2: &Ty) -> Result<T, tracked_operation::T> {
        if is_type_alias(ty1) || is_type_alias(ty2) {
            // There can be infinite recursion with recursive type aliases, so we track them
            add_op_and_check_infinite_recursion(
                t.clone(),
                tracked_operation::T {
                    ty1: ty1.clone(),
                    ty2: ty2.clone(),
                },
            )
        } else {
            Ok(t.clone())
        }
    }
}

/// Computes the negation of a type when it is known, which is currently the case
/// for null, nonnull, mixed, nothing, primitives, and classes.
/// Otherwise approximate up or down according to
/// `approx` parameter: If approx is `ApproxUp`, return mixed, else if it is `ApproxDown`,
/// return nothing.
pub fn negate_type(env: &mut Env, r: Reason, ty: &Ty, approx: utils::Approx) -> Ty {
    let ty = env::expand_type(env, ty.clone());
    let approximated = if approx == utils::Approx::ApproxUp {
        mk_type::mixed(r.clone())
    } else {
        mk_type::nothing(r.clone())
    };
    match get_node(&ty) {
        Ty_::Tprim(Tprim::Tnull) => mk_type::nonnull(r),
        Ty_::Tprim(_) => match typing_refinement::ty_predicate::of_ty(env, &ty).ok() {
            Some(predicate) => mk_type::neg(r, predicate),
            // void, noreturn
            None => approximated,
        },
        Ty_::Tneg(TypePredicate(r_, TypePredicate_::IsTag(TypeTag::ClassTag(c, args))))
            if args.is_empty() && utils::class_has_no_params(env, c) =>
        {
            mk_type::class_type(r_.clone(), c.clone(), vec![])
        }
        Ty_::Tneg(predicate) => {
            typing_refinement::ty_predicate::to_ty_without_instantiation_opt(env, predicate)
                .unwrap_or(approximated)
        }
        Ty_::Tnonnull => mk_type::null(r),
        Ty_::Tclass((_, c), Exact::Nonexact(_), args) => {
            let tparams: Vec<DeclTparam> = match env::get_class(env, c) {
                decl_entry::T::Found(cls) => cls::tparams(&cls),
                _ => vec![],
            };
            let is_fresh_generic = |ty: &Ty| match get_node(ty) {
                Ty_::Tgeneric(name) => env::is_fresh_generic_parameter(name),
                _ => false,
            };
            let is_all_filled_reified = |tparams: &[DeclTparam], args: &[Ty]| -> bool {
                let mut tparams = tparams.iter();
                let mut args = args.iter();
                loop {
                    match (tparams.next(), args.next()) {
                        (None, None) => return true,
                        (Some(tparam), Some(arg))
                            if (!tparam.reified.is_erased()) && !is_fresh_generic(arg) => {}
                        // too few args counts as unfilled, too many args is malformed, but treat that like the tparam is erased
                        _ => return false,
                    }
                }
            };
            let generics = if is_all_filled_reified(&tparams, args) {
                args.iter()
                    .map(|ty| TypeTagGeneric::Filled(ty.clone()))
                    .collect()
            } else {
                vec![]
            };
            mk_type::neg(
                r.clone(),
                TypePredicate(
                    r,
                    TypePredicate_::IsTag(TypeTag::ClassTag(c.clone(), generics)),
                ),
            )
        }
        _ => approximated,
    }
}

/// Decompose nullable types into unions with null
///
///       decompose_nullable ?A = null | A
///       decompose_nullable ?(A | ?B) = null | A | B
///
///   The implementation has the side-effect of flattening unions if the type is
///   nullable, e.g.,
///
///     decompose_optional ?(A | (B | C)) = null | A | B | C
fn decompose_nullable(ty: Ty) -> Ty {
    fn has_option(ty: &Ty) -> bool {
        match get_node(ty) {
            Ty_::Toption(_) => true,
            Ty_::Tunion(tyl) => tyl.iter().any(has_option),
            _ => false,
        }
    }
    /// `peel ty_acc ty`: `ty_acc` is the OCaml list, reversed.
    fn peel(ty_acc: &mut Vec<Ty>, ty: &Ty) {
        match get_node(ty) {
            Ty_::Toption(ty) => peel(ty_acc, ty),
            Ty_::Tunion(tyl) => {
                for ty in tyl {
                    peel(ty_acc, ty)
                }
            }
            _ => ty_acc.push(ty.clone()),
        }
    }
    if has_option(&ty) {
        let r = get_reason(&ty).clone();
        let null_ty = mk_type::null(r.clone());
        let mut tyl = vec![null_ty];
        peel(&mut tyl, &ty);
        tyl.reverse();
        let tyl = ty_set::elements(&ty_set::of_list(tyl));
        mk_type::union(r, tyl)
    } else {
        ty
    }
}

/// Build a union from a list of types. Flatten if any of the types themselves are union.
/// Also, pull nullable out to a top-level Toption. Undoes decompose atomic.
fn recompose_atomic(env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
    // `traverse nullable dynamic tyl_acc tyl`; `tyl_acc` is pushed to, which
    // gives `List.rev tyl_acc`.
    let mut nullable: Option<Reason> = None;
    let mut dynamic: Option<Reason> = None;
    let mut tyl_acc: Vec<Ty> = vec![];
    let mut todo: Vec<Ty> = tyl.into_iter().rev().collect();
    while let Some(ty) = todo.pop() {
        if utils::is_nothing(env, &ty) {
            continue;
        }
        match get_node(&ty) {
            Ty_::Toption(ty_) => {
                nullable = Some(get_reason(&ty).clone());
                tyl_acc.push(ty_.clone())
            }
            Ty_::Tprim(Tprim::Tnull) => nullable = Some(get_reason(&ty).clone()),
            Ty_::Tdynamic(None) => dynamic = Some(get_reason(&ty).clone()),
            Ty_::Tdynamic(Some(_)) => tyl_acc.push(ty.clone()),
            Ty_::Tunion(tyl_) => todo.extend(tyl_.iter().rev().cloned()),
            _ => tyl_acc.push(ty.clone()),
        }
    }
    utils::make_union(env, r, &tyl_acc, nullable, dynamic)
}

/// Destructure an intersection into a list of its sub-types,
/// decending into sub-intersections.
pub fn destruct_inter_list(env: &mut Env, tyl: &[Ty]) -> (Vec<Ty>, Option<Reason>) {
    // `dest_inter` and `destruct_inter_list`: `tyl_res` is consed onto, so it
    // has the types in the reverse of the order they are met.
    let mut todo: Vec<Ty> = tyl.iter().rev().cloned().collect();
    let mut tyl_res: Vec<Ty> = vec![];
    let mut r_inter: Option<Reason> = None;
    while let Some(ty) = todo.pop() {
        let ty = env::expand_type(env, ty);
        let tyl_ = match get_node(&ty) {
            Ty_::Tintersection(tyl_) => Some(tyl_.clone()),
            _ => None,
        };
        match tyl_ {
            Some(tyl_) => {
                r_inter = orr(r_inter, get_reason(&ty).clone());
                todo.extend(tyl_.into_iter().rev())
            }
            None => tyl_res.push(ty),
        }
    }
    tyl_res.reverse();
    (tyl_res, r_inter)
}

/// Number of '&' symbols in an intersection representation. E.g. for (A & B),
/// returns 1, for A, returns 0.
fn number_of_inter_symbols(env: &mut Env, ty: &Ty) -> isize {
    let mut todo: Vec<Ty> = vec![ty.clone()];
    let mut n: isize = 0;
    while let Some(ty) = todo.pop() {
        let ty = env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tintersection(tyl_) => {
                n = tyl_.len() as isize - 1 + n;
                todo.extend(tyl_.iter().rev().cloned())
            }
            Ty_::Tunion(tyl_) => todo.extend(tyl_.iter().rev().cloned()),
            Ty_::Toption(ty) => todo.push(ty.clone()),
            _ => {}
        }
    }
    n
}

fn collapses(env: &mut Env, ty1: &Ty, ty2: &Ty, inter_ty: &Ty) -> bool {
    let n_inter_inter = number_of_inter_symbols(env, inter_ty);
    let n_inter1 = number_of_inter_symbols(env, ty1);
    let n_inter2 = number_of_inter_symbols(env, ty2);
    n_inter_inter <= n_inter1 + n_inter2
}

fn make_intersection(env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
    let ty = mk_type::intersection(r.clone(), tyl);
    utils::wrap_union_inter_ty_in_var(env, r, ty)
}

/// `intersect` and `intersect_list` of the recursive group, which take a
/// recursion tracker. The functions of the same names at the end of the
/// module shadow them.
mod tracked {
    use super::*;

    pub(super) fn intersect(
        env: &mut Env,
        rec_tracker: &recursion_tracker::T,
        r: Reason,
        ty1: Ty,
        ty2: Ty,
    ) -> Ty {
        if log::should_log(env, 2) {
            let (r_, ty1_, ty2_) = (r.clone(), ty1.clone(), ty2.clone());
            log::log_intersection(env, &r_, &ty1_, &ty2_, |env| {
                intersect_(env, rec_tracker, r, ty1, ty2)
            })
        } else {
            intersect_(env, rec_tracker, r, ty1, ty2)
        }
    }

    pub(super) fn intersect_list(
        env: &mut Env,
        rec_tracker: &recursion_tracker::T,
        r: Reason,
        tyl: &[Ty],
    ) -> Ty {
        // We need to match tyl here because we'd mess the reason if tyl was just
        // [mixed]
        match tyl.split_first() {
            None => mk_type::mixed(r),
            Some((ty, tyl)) => {
                let mut acc = ty.clone();
                for ty_ in tyl {
                    acc = intersect(env, rec_tracker, r.clone(), acc, ty_.clone());
                }
                acc
            }
        }
    }
}

/// Computes the intersection (greatest lower bound) of two types.
/// For the intersection of unions, attempt to simplify by using the distributivity
/// of intersection over union. Uses the the `collapses` test function to make sure
/// the resulting type is no greater in size than the trivial `Tintersection [ty1; ty2]`.
fn intersect_(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty1: Ty,
    ty2: Ty,
) -> Ty {
    if ty_equal(None, &ty1, &ty2) {
        return ty1;
    }
    let ty1 = env::expand_type(env, ty1);
    let ty2 = env::expand_type(env, ty2);
    if utils::is_sub_type_for_union(env, &ty1, &ty2) {
        ty1
    } else if utils::is_sub_type_for_union(env, &ty2, &ty1) {
        ty2
    } else if utils::is_type_disjoint(env, &ty1, &ty2) {
        mk_type::nothing(r)
    } else {
        match recursion_tracker::check_infinite_recursion(rec_tracker, &ty1, &ty2) {
            Err(tracked_operation::T { ty1: _, ty2: _ }) => {
                mk_type::intersection(r, vec![ty1, ty2])
            }
            Ok(rec_tracker) => {
                // Attempt to simplify any case types involved in the intersection.
                // If simplification occurs we re-run [intersect] with the simplified type
                // until no more simplications can be performed.
                //
                // Note: Re-running [intersect] when neither [ty1] or [ty2] has been
                // simplified will lead to infinite recursion.
                let simplified_ty1_opt = try_simplifying_case_type(env, &rec_tracker, &ty1, &ty2);
                let simplified_ty2_opt = try_simplifying_case_type(env, &rec_tracker, &ty2, &ty1);
                match (simplified_ty1_opt, simplified_ty2_opt) {
                    (Some(simplified_ty1), None) => {
                        tracked::intersect(env, &rec_tracker, r, simplified_ty1, ty2)
                    }
                    (None, Some(simplified_ty2)) => {
                        tracked::intersect(env, &rec_tracker, r, ty1, simplified_ty2)
                    }
                    (Some(simplified_ty1), Some(simplified_ty2)) => {
                        tracked::intersect(env, &rec_tracker, r, simplified_ty1, simplified_ty2)
                    }
                    (None, None) => {
                        let ty1 = decompose_nullable(ty1);
                        let ty2 = decompose_nullable(ty2);
                        intersect_decomposed(env, &rec_tracker, r, ty1, ty2)
                    }
                }
            }
        }
    }
}

/// The `try match (deref ty1, deref ty2) with ... with Nothing -> ...` of
/// `intersect_`, on the decomposed types.
fn intersect_decomposed(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty1: Ty,
    ty2: Ty,
) -> Ty {
    let class_sub_classname = env::get_tcopt(env).class_sub_classname;
    match (get_node(&ty1), get_node(&ty2)) {
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
        ) if t_optional1.is_empty()
            && t_optional2.is_empty()
            && t_required1.len() == t_required2.len() =>
        {
            let t_required: Vec<Ty> = t_required1
                .iter()
                .zip(t_required2.iter())
                .map(|(ty1, ty2)| {
                    tracked::intersect(env, rec_tracker, r.clone(), ty1.clone(), ty2.clone())
                })
                .collect();
            let t_variadic = tracked::intersect(
                env,
                rec_tracker,
                r.clone(),
                t_variadic1.clone(),
                t_variadic2.clone(),
            );
            mk((
                r,
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: vec![],
                    extra: TupleExtra::Tvariadic(t_variadic),
                }),
            ))
        }
        // Runtime representation of tuples is vec, which can be observed in Hack via refinement.
        // Therefore it's sound to simplify vec<t> & (t1,...,tn) to (t & t1, ..., t & tn)
        // but because we don't support subtyping directly between tuples and vecs, we need
        // to keep the vec conjunct i.e. simplify to vec<t> & (t & t1, ..., t & tn)
        (
            Ty_::Tclass((_, cn), _, vec_args),
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_variadic),
            }),
        ) if vec_args.len() == 1 && cn == sn::collections::VEC => intersect_vec_and_tuple(
            env,
            rec_tracker,
            r,
            &ty1,
            &vec_args[0],
            get_reason(&ty2).clone(),
            (t_required, t_optional, t_variadic),
        ),
        (
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_variadic),
            }),
            Ty_::Tclass((_, cn), _, vec_args),
        ) if vec_args.len() == 1 && cn == sn::collections::VEC => intersect_vec_and_tuple(
            env,
            rec_tracker,
            r,
            &ty2,
            &vec_args[0],
            get_reason(&ty1).clone(),
            (t_required, t_optional, t_variadic),
        ),
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
            // The environment of the `try`, which the handler of `Nothing`
            // returns.
            let env_before_try = env.clone();
            match intersect_shapes(
                env,
                rec_tracker,
                r.clone(),
                (shape_kind1, fdm1),
                (shape_kind2, fdm2),
            ) {
                Ok((shape_kind, fdm)) => mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: shape_kind,
                        fields: fdm,
                    })),
                )),
                Err(Nothing) => {
                    *env = env_before_try;
                    mk_type::nothing(r)
                }
            }
        }
        (Ty_::Tshape(ShapeType::ShapeSplat(_)), _) | (_, Ty_::Tshape(ShapeType::ShapeSplat(_))) => {
            mk((r, Ty_::Tintersection(vec![ty1.clone(), ty2.clone()])))
        }
        (Ty_::TclassPtr(ty_c1), Ty_::TclassPtr(ty_c2)) => {
            let ty = tracked::intersect(env, rec_tracker, r.clone(), ty_c1.clone(), ty_c2.clone());
            mk((r, Ty_::TclassPtr(ty)))
        }
        (Ty_::Tintersection(tyl1), Ty_::Tintersection(tyl2)) => {
            intersect_lists(env, rec_tracker, r, tyl1, tyl2)
        }
        // Simplify `supportdyn<t> & u` to `supportdyn<t & u>`. Do not apply if `u` is
        // a type variable, else we end up with recursion in constraints.
        (Ty_::Tnewtype(name1, ty1args, _), _)
            if ty1args.len() == 1
                && name1 == sn::classes::SUPPORT_DYN
                && !typing_defs::is_tyvar(&ty2) =>
        {
            let r = get_reason(&ty1).clone();
            let ty =
                tracked::intersect(env, rec_tracker, r.clone(), ty1args[0].clone(), ty2.clone());
            utils::simple_make_supportdyn(r, env, ty)
        }
        (_, Ty_::Tnewtype(name1, ty2args, _))
            if ty2args.len() == 1
                && name1 == sn::classes::SUPPORT_DYN
                && !typing_defs::is_tyvar(&ty1) =>
        {
            let r = get_reason(&ty2).clone();
            let ty =
                tracked::intersect(env, rec_tracker, r.clone(), ty1.clone(), ty2args[0].clone());
            utils::simple_make_supportdyn(r, env, ty)
        }
        // If class<T> <: classname<T>, class<U> & classname<V> -> classname<U & V>
        (Ty_::Tnewtype(cn, cn_args, _), Ty_::TclassPtr(ty_c))
        | (Ty_::TclassPtr(ty_c), Ty_::Tnewtype(cn, cn_args, _))
            if cn_args.len() == 1 && class_sub_classname && cn == sn::classes::CLASS_NAME =>
        {
            let ty = tracked::intersect(
                env,
                rec_tracker,
                r.clone(),
                ty_c.clone(),
                cn_args[0].clone(),
            );
            mk_type::classname(r, vec![ty])
        }
        (Ty_::Tnewtype(cn, cn_args, _), Ty_::TclassPtr(ty_c))
        | (Ty_::TclassPtr(ty_c), Ty_::Tnewtype(cn, cn_args, _))
            if cn_args.len() == 1 && cn == sn::classes::CLASS_OR_CLASSNAME =>
        {
            let ty = tracked::intersect(
                env,
                rec_tracker,
                r.clone(),
                ty_c.clone(),
                cn_args[0].clone(),
            );
            mk_type::class_or_classname(r, vec![ty])
        }
        (Ty_::Tnewtype(cn1, cn1_args, _), Ty_::Tnewtype(cn2, cn2_args, _))
            if cn1_args.len() == 1
                && cn2_args.len() == 1
                && (cn1 == sn::classes::CLASS_OR_CLASSNAME && cn2 == sn::classes::CLASS_NAME
                    || cn1 == sn::classes::CLASS_NAME
                        && cn2 == sn::classes::CLASS_OR_CLASSNAME) =>
        {
            let ty = tracked::intersect(
                env,
                rec_tracker,
                r.clone(),
                cn1_args[0].clone(),
                cn2_args[0].clone(),
            );
            mk_type::class_or_classname(r, vec![ty])
        }
        (Ty_::Tnewtype(cn1, cn1_args, _), Ty_::Tnewtype(cn2, cn2_args, _))
            if cn1_args.len() == 1
                && cn2_args.len() == 1
                && cn1 == sn::classes::CLASS_NAME
                && cn2 == sn::classes::CLASS_NAME =>
        {
            let ty = tracked::intersect(
                env,
                rec_tracker,
                r.clone(),
                cn1_args[0].clone(),
                cn2_args[0].clone(),
            );
            mk_type::classname(r, vec![ty])
        }
        (Ty_::Tintersection(tyl), _) => {
            intersect_lists(env, rec_tracker, r, std::slice::from_ref(&ty2), tyl)
        }
        (_, Ty_::Tintersection(tyl)) => {
            intersect_lists(env, rec_tracker, r, std::slice::from_ref(&ty1), tyl)
        }
        (Ty_::Tunion(tyl1), Ty_::Tunion(tyl2)) => {
            let (common_tyl, tyl1_, tyl2_) =
                crate::typing_algebra::factorize_common_types(tyl1, tyl2);
            let not_common_tyl = intersect_unions(
                env,
                rec_tracker,
                r.clone(),
                (get_reason(&ty1).clone(), &tyl1_),
                (get_reason(&ty2).clone(), &tyl2_),
            );
            let mut tyl = common_tyl;
            tyl.extend(not_common_tyl);
            recompose_atomic(env, r, tyl)
        }
        (Ty_::Tunion(tyl), _) => {
            let inter_tyl = intersect_ty_union(
                env,
                rec_tracker,
                r.clone(),
                mk(deref(&ty2)),
                (get_reason(&ty1).clone(), tyl),
            );
            recompose_atomic(env, r, inter_tyl)
        }
        (_, Ty_::Tunion(tyl)) => {
            let inter_tyl = intersect_ty_union(
                env,
                rec_tracker,
                r.clone(),
                mk(deref(&ty1)),
                (get_reason(&ty2).clone(), tyl),
            );
            recompose_atomic(env, r, inter_tyl)
        }
        (Ty_::Tprim(Tprim::Tnum), Ty_::Tprim(Tprim::Tarraykey))
        | (Ty_::Tprim(Tprim::Tarraykey), Ty_::Tprim(Tprim::Tnum)) => mk_type::int(r),
        (Ty_::Tneg(predicate), _) => intersect_with_negation(
            env,
            rec_tracker,
            r,
            &ty1,
            &ty2,
            get_reason(&ty1).clone(),
            predicate,
            &ty2,
        ),
        (_, Ty_::Tneg(predicate)) => intersect_with_negation(
            env,
            rec_tracker,
            r,
            &ty1,
            &ty2,
            get_reason(&ty2).clone(),
            predicate,
            &ty1,
        ),
        _ => make_intersection(env, r, vec![ty1.clone(), ty2.clone()]),
    }
}

/// The case `vec<ty> & (rt, tuple)` of `intersect_` (either way round).
fn intersect_vec_and_tuple(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    vty: &Ty,
    ty: &Ty,
    rt: Reason,
    (t_required, t_optional, t_variadic): (&[Ty], &[Ty], &Ty),
) -> Ty {
    let t_required: Vec<Ty> = t_required
        .iter()
        .map(|ty_| tracked::intersect(env, rec_tracker, r.clone(), ty.clone(), ty_.clone()))
        .collect();
    let t_optional: Vec<Ty> = t_optional
        .iter()
        .map(|ty_| tracked::intersect(env, rec_tracker, r.clone(), ty.clone(), ty_.clone()))
        .collect();
    let t_variadic =
        tracked::intersect(env, rec_tracker, r.clone(), ty.clone(), t_variadic.clone());
    make_intersection(
        env,
        r,
        vec![
            mk(deref(vty)),
            mk((
                rt,
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: TupleExtra::Tvariadic(t_variadic),
                }),
            )),
        ],
    )
}

/// The case `(neg_reason, Tneg predicate) & ty` of `intersect_` (either way
/// round): `ty1` and `ty2` are the two types of `intersect_`, `ty` the one
/// that is not the negation.
fn intersect_with_negation(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty1: &Ty,
    ty2: &Ty,
    neg_reason: Reason,
    predicate: &TypePredicate,
    ty: &Ty,
) -> Ty {
    let partition = typing_refinement::partition_ty(env, &mk(deref(ty)), predicate);
    if partition.span.is_empty() {
        if partition.left.is_empty() {
            // This is logically the same result as the else case handling
            // would produce but may be simpler
            mk(deref(ty))
        } else {
            // `intersections` is consed onto: the last one first.
            let mut intersections: Vec<Ty> = vec![];
            for tys in &partition.right {
                // recursion here should be safe since, while the type
                // may not be structurally smaller, it should be
                // logically smaller and we shouldn't repeat !predicate
                let intersection =
                    tracked::intersect_list(env, rec_tracker, neg_reason.clone(), tys);
                intersections.push(intersection);
            }
            intersections.reverse();
            let right_ty =
                utils::simplify_unions(env, None, None, mk_type::union(neg_reason, intersections));
            right_ty
        }
    } else {
        make_intersection(env, r, vec![ty1.clone(), ty2.clone()])
    }
}

/// Attempts to simplify an intersection involving a case type and another type. If [case_type]
/// is a case type, we fetch the list of variant types, then filter this list down to only the types
/// that intersect with the data types associated with [ty]. If the resulting filtered type is
/// not a union type, we consider it to be a simplified version of the case type and return it.
/// Otherwise simplification fails and [None] is returned.
///
/// As an example consider:
///   [case_type] = int | vec<int> | string
///   [ty] = not int & not string
///
///  This will result in simplifying the case type to `vec<int>`
///
///  If instead we had:
///    [ty] = not int
///
///  This would fail to simplify because the result filtered type would be `vec<int> | string`
///
///  Finally if we had:
///    [ty] = not vec
///
///  This would succeed, because the union `int | string` would simplify to `arraykey`
fn try_simplifying_case_type(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    case_type: &Ty,
    intersect_ty: &Ty,
) -> Option<Ty> {
    let r = get_reason(case_type).clone();
    match get_node(case_type) {
        Ty_::Tnewtype(name, ty_args, _) => {
            let variants_opt = typing_case_type_variant::get_variant_tys(env, name, ty_args);
            match variants_opt {
                Some(variants) => {
                    let filtered_ty = typing_case_type_variant::filter_variants_using_datatype(
                        false, // safe_for_are_disjoint
                        env,
                        r,
                        &variants,
                        intersect_ty,
                    );
                    if typing_defs::is_union(&filtered_ty) {
                        None
                    } else {
                        Some(filtered_ty)
                    }
                }
                None => None,
            }
        }
        Ty_::Tintersection(tyl) => {
            // For each type in [tyl] try to simplify all case types that are present, filtering based on
            // the intersection of all other types in the intersection.
            //
            // [acc] will contain the rebuilt list with any case types that could be simplified replaced with their simplified form
            // [changed] will be `true` if a case type in the list was simplified, otherwise it will be `false
            //
            // `acc` is consed onto: here it is pushed to.
            let mut acc: Vec<Ty> = vec![];
            let mut changed = false;
            for (i, ty) in tyl.iter().enumerate() {
                // `(intersect_ty :: tyl) @ acc`
                let mut others = vec![intersect_ty.clone()];
                others.extend(tyl[i + 1..].iter().cloned());
                others.extend(acc.iter().rev().cloned());
                let simplified_ty_opt = try_simplifying_case_type(
                    env,
                    rec_tracker,
                    ty,
                    &mk_type::intersection(r.clone(), others),
                );
                match simplified_ty_opt {
                    Some(simplified_ty) => {
                        acc.push(simplified_ty);
                        changed = true
                    }
                    None => acc.push(ty.clone()),
                }
            }
            if changed {
                acc.reverse();
                let simplified_ty = tracked::intersect_list(env, rec_tracker, r, &acc);
                Some(simplified_ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn intersect_shapes(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    (shape_kind1, fdm1): (&Ty, &t_shape_map::T<ShapeFieldType>),
    (shape_kind2, fdm2): (&Ty, &t_shape_map::T<ShapeFieldType>),
) -> Result<(Ty, t_shape_map::T<ShapeFieldType>), Nothing> {
    let combine = |env: &mut Env,
                   _sfn: &t_shape_map::Key,
                   sft1: Option<&ShapeFieldType>,
                   sft2: Option<&ShapeFieldType>|
     -> Result<Option<ShapeFieldType>, Nothing> {
        match (
            (typing_defs::is_nothing(shape_kind1), sft1),
            (typing_defs::is_nothing(shape_kind2), sft2),
        ) {
            ((_, None), (_, None))
            | ((_, Some(ShapeFieldType { optional: true, .. })), (true, None))
            | ((true, None), (_, Some(ShapeFieldType { optional: true, .. }))) => Ok(None),
            (
                (
                    _,
                    Some(ShapeFieldType {
                        optional: false, ..
                    }),
                ),
                (true, None),
            )
            | (
                (true, None),
                (
                    _,
                    Some(ShapeFieldType {
                        optional: false, ..
                    }),
                ),
            ) => Err(Nothing),
            ((_, Some(sft)), (_, None)) => {
                let ty = tracked::intersect(
                    env,
                    rec_tracker,
                    r.clone(),
                    shape_kind2.clone(),
                    sft.ty.clone(),
                );
                Ok(Some(ShapeFieldType {
                    optional: sft.optional,
                    ty,
                }))
            }
            ((_, None), (_, Some(sft))) => {
                let ty = tracked::intersect(
                    env,
                    rec_tracker,
                    r.clone(),
                    shape_kind1.clone(),
                    sft.ty.clone(),
                );
                Ok(Some(ShapeFieldType {
                    optional: sft.optional,
                    ty,
                }))
            }
            (
                (
                    _,
                    Some(ShapeFieldType {
                        optional: opt1,
                        ty: ty1,
                    }),
                ),
                (
                    _,
                    Some(ShapeFieldType {
                        optional: opt2,
                        ty: ty2,
                    }),
                ),
            ) => {
                let opt = *opt1 && *opt2;
                let ty = tracked::intersect(env, rec_tracker, r.clone(), ty1.clone(), ty2.clone());
                Ok(Some(ShapeFieldType { optional: opt, ty }))
            }
        }
    };
    // `TShapeMap.merge_env env fdm1 fdm2 ~combine`: the keys of `fdm2` first,
    // then those of `fdm1` that are not in `fdm2`, each in increasing order.
    let mut fdm: t_shape_map::T<ShapeFieldType> = t_shape_map::T::new();
    for (key, v2) in fdm2 {
        let v1opt = fdm1.get(key);
        if let Some(v) = combine(env, key, v1opt, Some(v2))? {
            fdm.insert(key.clone(), v);
        }
    }
    for (key, v1) in fdm1 {
        if !fdm2.contains_key(key) {
            if let Some(v) = combine(env, key, Some(v1), None)? {
                fdm.insert(key.clone(), v);
            }
        }
    }
    let shape_kind = tracked::intersect(
        env,
        rec_tracker,
        r,
        shape_kind1.clone(),
        shape_kind2.clone(),
    );
    Ok((shape_kind, fdm))
}

fn intersect_lists(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    tyl1: &[Ty],
    tyl2: &[Ty],
) -> Ty {
    // The inner `intersect_lists env tyl1 tyl2 acc_tyl`; `acc_tyl` is consed
    // onto: here it is pushed to.
    let mut tyl1: &[Ty] = tyl1;
    let mut tyl2: Vec<Ty> = tyl2.to_vec();
    let mut acc_tyl: Vec<Ty> = vec![];
    let tyl = loop {
        match (tyl1.split_first(), tyl2.is_empty()) {
            (None, _) => {
                let mut res = tyl2;
                res.extend(acc_tyl.into_iter().rev());
                break res;
            }
            (Some(_), true) => {
                let mut res = tyl1.to_vec();
                res.extend(acc_tyl.into_iter().rev());
                break res;
            }
            (Some((ty1, tyl1_)), false) => {
                let (inter_ty, missed_inter_tyl2) =
                    intersect_ty_tyl(env, rec_tracker, r.clone(), ty1.clone(), &tyl2);
                tyl1 = tyl1_;
                tyl2 = missed_inter_tyl2;
                acc_tyl.push(inter_ty);
            }
        }
    };
    make_intersection(env, r, tyl)
}

fn intersect_ty_tyl(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty: Ty,
    tyl: &[Ty],
) -> (Ty, Vec<Ty>) {
    // try negs last because we expect them to be more likely to fail try_intersect
    let (negs, others): (Vec<Ty>, Vec<Ty>) = tyl.iter().cloned().partition(typing_defs::is_neg);
    let mut tyl = others;
    tyl.extend(negs);
    // `missed_inter_tyl` is consed onto: here it is pushed to.
    let mut ty = ty;
    let mut missed_inter_tyl: Vec<Ty> = vec![];
    for ty_ in tyl {
        let ty_opt = try_intersect(env, rec_tracker, r.clone(), ty.clone(), ty_.clone());
        match ty_opt {
            None => missed_inter_tyl.push(ty_),
            Some(inter_ty) => ty = inter_ty,
        }
    }
    missed_inter_tyl.reverse();
    (ty, missed_inter_tyl)
}

fn try_intersect(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty1: Ty,
    ty2: Ty,
) -> Option<Ty> {
    let ty = tracked::intersect(env, rec_tracker, r, ty1, ty2);
    let ty = env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tintersection(_) => None,
        _ => Some(ty),
    }
}

fn intersect_unions(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    (r1, tyl1): (Reason, &[Ty]),
    (r2, tyl2): (Reason, &[Ty]),
) -> Vec<Ty> {
    // The order matters. (A | B | C) & (A | B) gets simplified to (A | B)
    // while (A | B) & (A | B | C) would become A | B | ((A | B) & C), so we
    // put the longest union first as a heuristic.
    let ((r1, tyl1), (r2, tyl2)) = if tyl1.len() >= tyl2.len() {
        ((r1, tyl1), (r2, tyl2))
    } else {
        ((r2, tyl2), (r1, tyl1))
    };
    let union_ty1 = mk_type::union(r1, tyl1.to_vec());
    intersect_ty_union(env, rec_tracker, r, union_ty1, (r2, tyl2))
}

/// For (A1 | .. | An) & B, compute each of the A1 & B, .. , An & B.
/// Keep those which collapse (see `collapses` function) with B
/// and leave the others unchanged.
/// So if I is the set of indices i such that Ai collapses with B,
/// and J the set of indices such that this is not the case,
/// the result would be
///   (|_{i in I} (Ai & B)) | (B & (|_{j in J} Aj))
fn intersect_ty_union(
    env: &mut Env,
    rec_tracker: &recursion_tracker::T,
    r: Reason,
    ty1: Ty,
    (r_union, tyl2): (Reason, &[Ty]),
) -> Vec<Ty> {
    let inter_tyl: Vec<Ty> = tyl2
        .iter()
        .map(|ty2| tracked::intersect(env, rec_tracker, r.clone(), ty1.clone(), ty2.clone()))
        .collect();
    let zipped: Vec<(Ty, Ty)> = tyl2.iter().cloned().zip(inter_tyl).collect();
    // `snd @@ collapses env ty1 ty2 ~inter_ty`: each test starts from `env`,
    // and the environment it returns is dropped.
    let (collapsed, not_collapsed): (Vec<(Ty, Ty)>, Vec<(Ty, Ty)>) = zipped
        .into_iter()
        .partition(|(ty2, inter_ty)| collapses(&mut env.clone(), &ty1, ty2, inter_ty));
    let collapsed: Vec<Ty> = collapsed
        .into_iter()
        .map(|(_, inter_ty)| inter_ty)
        .collect();
    let mut not_collapsed: Vec<Ty> = match not_collapsed.len() {
        0 => vec![],
        1 => {
            let (_ty2, inter_ty) = not_collapsed.into_iter().next().unwrap();
            vec![inter_ty]
        }
        _ => {
            let not_collapsed: Vec<Ty> = not_collapsed.into_iter().map(|(ty2, _)| ty2).collect();
            vec![mk_type::intersection(
                r.clone(),
                vec![ty1, mk_type::union(r_union, not_collapsed)],
            )]
        }
    };
    not_collapsed.extend(collapsed);
    not_collapsed
}

/// `normalize_intersection env ?on_tyvar tyl`, which returns `(env, r, tys)`.
fn normalize_intersection(
    env: &mut Env,
    mut on_tyvar: Option<OnTyvar<'_>>,
    tyl: &[Ty],
) -> (Option<Reason>, ty_set::T) {
    let mut r: Option<Reason> = None;
    let mut tys_acc: ty_set::T = ty_set::empty();
    let mut todo: Vec<Ty> = tyl.iter().rev().cloned().collect();
    while let Some(ty) = todo.pop() {
        let ty = env::expand_type(env, ty);
        enum Node {
            Var(tvid::T),
            Intersection(Vec<Ty>),
            Union,
            Other,
        }
        let node = match get_node(&ty) {
            Ty_::Tvar(v) => Node::Var(*v),
            Ty_::Tintersection(tyl_) => Node::Intersection(tyl_.clone()),
            Ty_::Tunion(_) => Node::Union,
            _ => Node::Other,
        };
        match node {
            Node::Var(v) if on_tyvar.is_some() => {
                let ty_ = match &mut on_tyvar {
                    Some(on_tyvar) => on_tyvar(env, get_reason(&ty).clone(), v),
                    None => unreachable!(),
                };
                if ty_equal(None, &ty, &ty_) {
                    // `proceed env ty`
                    tys_acc = ty_set::add(ty, &tys_acc)
                } else {
                    todo.push(ty_)
                }
            }
            Node::Intersection(tyl_) => {
                r = orr(r, get_reason(&ty).clone());
                todo.extend(tyl_.into_iter().rev())
            }
            Node::Union => {
                let ty = utils::simplify_unions(env, None, reborrow_on_tyvar(&mut on_tyvar), ty);
                let ety = env::expand_type(env, ty.clone());
                match get_node(&ety) {
                    Ty_::Tunion(_) => tys_acc = ty_set::add(ty, &tys_acc),
                    _ => todo.push(ty),
                }
            }
            Node::Var(_) | Node::Other => tys_acc = ty_set::add(ty, &tys_acc),
        }
    }
    (r, tys_acc)
}

pub fn simplify_intersections(env: &mut Env, on_tyvar: Option<OnTyvar<'_>>, ty: Ty) -> Ty {
    // Not in the OCaml: a type that is not a type variable, an intersection
    // or a union is what `normalize_intersection` keeps (its expansion is
    // itself), and `intersect_list` of that one type gives it back.
    if !matches!(
        get_node(&ty),
        Ty_::Tvar(_) | Ty_::Tintersection(_) | Ty_::Tunion(_)
    ) {
        return ty;
    }
    let r = get_reason(&ty).clone();
    let (r_, tys) = normalize_intersection(env, on_tyvar, std::slice::from_ref(&ty));
    let r = r_.unwrap_or(r);
    tracked::intersect_list(env, &recursion_tracker::empty(), r, &ty_set::elements(&tys))
}

pub fn intersect(env: &mut Env, r: Reason, ty1: Ty, ty2: Ty) -> Ty {
    let rec_tracker = recursion_tracker::empty();
    if log::should_log(env, 1) {
        let (r_, ty1_, ty2_) = (r.clone(), ty1.clone(), ty2.clone());
        log::log_intersection(env, &r_, &ty1_, &ty2_, |env| {
            tracked::intersect(env, &rec_tracker, r, ty1, ty2)
        })
    } else {
        tracked::intersect(env, &rec_tracker, r, ty1, ty2)
    }
}

pub fn intersect_list(env: &mut Env, r: Reason, tyl: &[Ty]) -> Ty {
    tracked::intersect_list(env, &recursion_tracker::empty(), r, tyl)
}

pub fn intersect_with_nonnull(env: &mut Env, pos: PosOrDecl, ty: Ty) -> Ty {
    let r = reason::witness_from_decl(pos);
    let nonnull = mk_type::nonnull(r.clone());
    intersect(env, r, ty, nonnull)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_reason;

    fn prim(p: Tprim) -> Ty {
        mk_type::prim_type(typing_reason::none(), p)
    }

    #[test]
    fn decompose_nullable_flattens_and_adds_null() {
        let int = prim(Tprim::Tint);
        let float = prim(Tprim::Tfloat);
        // ?(int | ?float)
        let ty = mk_type::nullable(
            typing_reason::none(),
            mk_type::union(
                typing_reason::none(),
                vec![
                    int.clone(),
                    mk_type::nullable(typing_reason::none(), float.clone()),
                ],
            ),
        );
        let decomposed = decompose_nullable(ty);
        match get_node(&decomposed) {
            Ty_::Tunion(tyl) => {
                let mut expected = vec![mk_type::null(typing_reason::none()), int, float];
                expected.sort();
                assert_eq!(tyl, &expected);
            }
            _ => panic!("expected a union"),
        }
    }

    #[test]
    fn decompose_nullable_leaves_types_without_options_alone() {
        let ty = mk_type::union(
            typing_reason::none(),
            vec![prim(Tprim::Tint), prim(Tprim::Tfloat)],
        );
        let decomposed = decompose_nullable(ty.clone());
        assert!(crate::typing_defs_core::phys_equal(&ty, &decomposed));
    }

    #[test]
    fn recursion_tracker_tracks_aliases_only() {
        let int = prim(Tprim::Tint);
        let alias = mk((
            typing_reason::none(),
            Ty_::Tnewtype("\\A".to_string(), vec![], int.clone()),
        ));
        let t = recursion_tracker::empty();
        // No alias: nothing is recorded.
        let t = recursion_tracker::check_infinite_recursion(&t, &int, &int).unwrap();
        let t = recursion_tracker::check_infinite_recursion(&t, &int, &int).unwrap();
        // An alias is recorded, and found the second time.
        let t = recursion_tracker::check_infinite_recursion(&t, &alias, &int).unwrap();
        let found = recursion_tracker::check_infinite_recursion(&t, &alias, &int).unwrap_err();
        assert!(equal_locl_ty(&found.ty1, &alias));
        assert!(equal_locl_ty(&found.ty2, &int));
        // The order of the operands matters.
        assert!(recursion_tracker::check_infinite_recursion(&t, &int, &alias).is_ok());
    }
}
