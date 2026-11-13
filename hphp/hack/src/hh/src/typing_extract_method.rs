// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_extract_method.ml`. See `hh/PORTING.md`.
//!
//! The function types handled here are decl types: `hackrs`'s
//! `ty::decl::FunType<R, Ty<R>>` (`crate::typing_defs_core::DeclFunType`),
//! whose positions are `BPos` (`Pos_or_decl.t` in OCaml). The `pos_id` of the
//! class is a `crate::typing_defs_core::PosId`, and the positions returned by
//! [`explicit_this_param_positions`] are `PosOrDecl`s, as in the `.mli`.
//!
//! The submodules `Variance_analysis` and `Typeconst_analysis` (with its
//! `Trie` and `Subst`) are private modules of this one, as in OCaml where the
//! `.mli` does not export them.
//!
//! `Typing_make_type.union`/`intersection`/`mixed` are polymorphic in the
//! phase in OCaml; `crate::typing_make_type` builds localized types only, so
//! the decl versions are [`decl_union`], [`decl_intersection`] and
//! [`decl_mixed`] below.

use std::cell::Cell;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::VecDeque;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::ReifyKind;
use oxidized::ast_defs::Variance;
use oxidized::pos_or_decl::PosOrDecl;
use pos::BPos;
use pos::Positioned;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason;

use crate::ctx::R;
use crate::decl_enforceability;
use crate::decl_entry;
use crate::folded_class;
use crate::s_map;
use crate::s_set;
use crate::typing_defs::Typeconst;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclRefinedConst;
use crate::typing_defs_core::DeclRefinedConstBound;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::TransformTopDown;
use crate::typing_defs_core::transform_top_down_decl_ty;
use crate::typing_defs_flags;
use crate::typing_env;
use crate::typing_env_types::Env;

// -- Helpers of other modules on decl types -----------------------------------

/// `Typing_make_type.mixed r` on a decl type: `mk (r, Toption (nonnull r))`.
fn decl_mixed(r: R) -> DeclTy {
    DeclTy::new(r.clone(), d::Ty_::Toption(DeclTy::new(r, d::Ty_::Tnonnull)))
}

/// `Typing_make_type.union r tyl` on decl types.
fn decl_union(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    if tyl.len() == 1 {
        tyl.pop().unwrap()
    } else {
        DeclTy::new(r, d::Ty_::Tunion(tyl.into()))
    }
}

/// `Typing_make_type.intersection r tyl` on decl types.
fn decl_intersection(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    match tyl.len() {
        0 => decl_mixed(r),
        1 => tyl.pop().unwrap(),
        _ => DeclTy::new(r, d::Ty_::Tintersection(tyl.into())),
    }
}

/// `Option.merge a b ~f`
fn option_merge<T: Clone>(a: &Option<T>, b: &Option<T>, f: impl FnOnce(T, T) -> T) -> Option<T> {
    match (a, b) {
        (None, None) => None,
        (Some(x), None) | (None, Some(x)) => Some(x.clone()),
        (Some(x), Some(y)) => Some(f(x.clone(), y.clone())),
    }
}

/// `x :: l` on a list kept in OCaml order (the head first).
fn cons<T>(x: T, mut l: Vec<T>) -> Vec<T> {
    l.insert(0, x);
    l
}

/// The `on_rc_bound` that every transformation of this module uses:
/// `fun rc_bound ~ctx -> (ctx, `Continue rc_bound)`.
fn continue_rc_bound<A: Clone>(
    rc_bound: DeclRefinedConstBound,
    ctx: &A,
) -> (A, TransformTopDown<DeclRefinedConstBound>) {
    (ctx.clone(), TransformTopDown::Continue(rc_bound))
}

/// The name of a type parameter (`let { tp_name = (_, name); _ } = tp`).
fn tparam_name(tp: &DeclTparam) -> String {
    tp.name.id_ref().as_str().to_string()
}

// -----------------------------------------------------------------------------

fn mk_tparam(pos: BPos, name: &str, tp_constraints: Vec<(ConstraintKind, DeclTy)>) -> DeclTparam {
    d::Tparam {
        variance: Variance::Invariant,
        name: Positioned::new(pos, TypeName::new(name)),
        constraints: tp_constraints.into(),
        reified: ReifyKind::Erased,
        user_attributes: [].into(),
    }
}

fn type_parameter_upper_bounds(
    bounds: s_map::T<Vec<DeclTy>>,
    tparams: &[DeclTparam],
    where_constraints: &[d::WhereConstraint<DeclTy>],
) -> s_map::T<Vec<DeclTy>> {
    let bounds = tparams.iter().fold(bounds, |bounds, tp| {
        let name = tp.name.id_ref().as_str();
        let upper: Vec<DeclTy> = tp
            .constraints
            .iter()
            .filter_map(|(kind, ty)| match kind {
                ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq => Some(ty.clone()),
                _ => None,
            })
            .collect();
        bounds.update(name.to_string(), upper)
    });
    // `ty :: Option.value old ~default:[]`
    let add_upper = |bounds: s_map::T<Vec<DeclTy>>, name: &str, ty: &DeclTy| {
        let old = bounds.get(name).cloned().unwrap_or_default();
        bounds.update(name.to_string(), cons(ty.clone(), old))
    };
    where_constraints
        .iter()
        .fold(bounds, |bounds, d::WhereConstraint(left, kind, right)| {
            let bounds = match (left.node_ref(), kind) {
                (
                    d::Ty_::Tgeneric(name),
                    ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq,
                ) => add_upper(bounds, name.as_str(), right),
                _ => bounds,
            };
            match (right.node_ref(), kind) {
                (
                    d::Ty_::Tgeneric(name),
                    ConstraintKind::ConstraintSuper | ConstraintKind::ConstraintEq,
                ) => add_upper(bounds, name.as_str(), left),
                _ => bounds,
            }
        })
}

mod variance_analysis {
    use super::*;

    /// The `~update` argument of [`find`]: `update ty acc var`.
    type Update<'a, A> = &'a dyn Fn(&DeclTy, A, Variance) -> A;
    /// The `~is_invariant` argument of [`find`].
    type IsInvariant<'a, A> = &'a dyn Fn(&A) -> bool;

    #[allow(dead_code)]
    pub fn show_variances(variances: &s_map::T<Option<Variance>>) -> String {
        let str = variances
            .iter()
            .map(|(name, variance_opt)| {
                let var_str = match variance_opt {
                    None => "bivariant".to_string(),
                    Some(v) => crate::ast_defs::show_variance(*v),
                };
                format!("{}: {}", name, var_str)
            })
            .collect::<Vec<_>>()
            .join("\n");
        format!("variances:\n{}\n", str)
    }

    fn mul(v1: Variance, v2: Variance) -> Variance {
        use Variance::*;
        match (v1, v2) {
            (Invariant, _) | (_, Invariant) => Invariant,
            (Covariant, v) | (v, Covariant) => v,
            (Contravariant, Contravariant) => Covariant,
        }
    }

    fn join(v1: Variance, v2: Variance) -> Variance {
        use Variance::*;
        match (v1, v2) {
            (Covariant, Covariant) => Covariant,
            (Contravariant, Contravariant) => Contravariant,
            (Invariant, _)
            | (_, Invariant)
            | (Covariant, Contravariant)
            | (Contravariant, Covariant) => Invariant,
        }
    }

    fn find<A>(
        ty: &DeclTy,
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        // Update the accumulator
        let acc = update(ty, acc, var);
        // Traverse the type
        match ty.node_ref() {
            d::Ty_::Tthis
            | d::Ty_::Tmixed
            | d::Ty_::Twildcard
            | d::Ty_::Tany
            | d::Ty_::Tnonnull
            | d::Ty_::Tdynamic
            | d::Ty_::Tprim(_)
            | d::Ty_::Tgeneric(_)
            | d::Ty_::Taccess(_) => acc,
            d::Ty_::Toption(ty) | d::Ty_::Tlike(ty) | d::Ty_::TclassPtr(ty) => {
                find(ty, var, update, is_invariant, acc, env)
            }
            d::Ty_::TvecOrDict(kv) => {
                let (ty_k, ty_v) = &**kv;
                let acc = find(ty_k, var, update, is_invariant, acc, env);
                if is_invariant(&acc) {
                    acc
                } else {
                    find(ty_v, var, update, is_invariant, acc, env)
                }
            }
            d::Ty_::Tunion(tys) | d::Ty_::Tintersection(tys) => {
                find_list(tys, var, update, is_invariant, acc, env)
            }
            d::Ty_::Trefinement(tr) => {
                let acc = find(&tr.ty, var, update, is_invariant, acc, env);
                if is_invariant(&acc) {
                    acc
                } else {
                    // The variance of generics / `this` inside refinements depends on
                    // the refinement kind:
                    //
                    // - Exact refinements (`= T`) are invariant. This prevents us
                    //   substituting for the upper or lower bounds of generated type
                    //   parameters and correctly handles cases like this:
                    //
                    //   abstract class WithRfmt {
                    //     abstract const type T  as arraykey;
                    //     public function foo(this::T $_) : void {}
                    //   }
                    //
                    //   Before any optimization, the generated type of
                    //   `meth_caller(WithRfmt::class, 'foo')` is:
                    //
                    //   ```
                    //   (function
                    //     <TThis as WithRfmt with type { T = T#0 }
                    //     , T#0 as arraykey
                    //     >(TThis, T#0): void
                    //   )
                    //   ```
                    //
                    //   If we don't treat `T#0` as invariant in the exact refinement,
                    //   we would substitute it for its upper bound (`arraykey`) and
                    //   lose the restriction that the second argument must be connected
                    //   to the type constant `T` in the first.
                    //
                    // - `as` (upper bound) refinements are covariant: we compose the
                    //   outer variance with covariant (identity).
                    //
                    // - `super` (lower bound) refinements are contravariant: we compose
                    //   the outer variance with contravariant.
                    //
                    // For `TRloose`, the variance of each bound position is composed
                    // with the outer context variance using `mul`.
                    let cr_consts: Vec<&DeclRefinedConst> = tr.refinement.consts.values().collect();
                    find_cr_consts(&cr_consts, var, update, is_invariant, acc, env)
                }
            }
            d::Ty_::Tfun(fun_ty) => find_fun_ty(fun_ty, var, update, is_invariant, acc, env),
            d::Ty_::Ttuple(tuple_ty) => {
                find_tuple_ty(tuple_ty, var, update, is_invariant, acc, env)
            }
            d::Ty_::Tshape(shape_ty) => match &**shape_ty {
                d::ShapeType::Simple(shape_ty) => {
                    find_shape_ty(shape_ty, var, update, is_invariant, acc, env)
                }
                d::ShapeType::Splat(ss_elems) => {
                    find_list(ss_elems, var, update, is_invariant, acc, env)
                }
            },
            d::Ty_::Tapply(id_and_tys) => {
                let (class_name, tys) = &**id_and_tys;
                let variances: Vec<Variance> = match typing_env::get_class_or_typedef_tparams(
                    env,
                    class_name.id_ref().as_str(),
                ) {
                    tparams if tparams.is_empty() => {
                        // In the case the class / type def doesn't exist or isn't available
                        // we should be conservative and assume all type parameters are
                        // invariant
                        tys.iter().map(|_| Variance::Invariant).collect()
                    }
                    tparams => tparams.iter().map(|tp| tp.variance).collect(),
                };
                find_with_variances(tys, &variances, var, update, is_invariant, acc, env)
            }
        }
    }

    fn find_cr_consts<A>(
        cr_consts: &[&DeclRefinedConst],
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        match cr_consts.split_first() {
            None => acc,
            Some((rc, cr_consts)) => match &rc.bound {
                d::RefinedConstBound::Exact(ty) => {
                    // Exact refinements (= T) are invariant
                    let acc = find(ty, Variance::Invariant, update, is_invariant, acc, env);
                    if is_invariant(&acc) {
                        acc
                    } else {
                        find_cr_consts(cr_consts, var, update, is_invariant, acc, env)
                    }
                }
                d::RefinedConstBound::Loose(d::RefinedConstBounds {
                    lower: tr_lower,
                    upper: tr_upper,
                }) => {
                    // Upper bounds (as T) are covariant: compose with outer variance
                    let acc = find_list(tr_upper, var, update, is_invariant, acc, env);
                    if is_invariant(&acc) {
                        acc
                    } else {
                        // Lower bounds (super T) are contravariant: compose with outer variance
                        let acc = find_list(
                            tr_lower,
                            mul(var, Variance::Contravariant),
                            update,
                            is_invariant,
                            acc,
                            env,
                        );
                        if is_invariant(&acc) {
                            acc
                        } else {
                            find_cr_consts(cr_consts, var, update, is_invariant, acc, env)
                        }
                    }
                }
            },
        }
    }

    fn find_list<A>(
        tys: &[DeclTy],
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        // `match tys with [] -> acc | ty :: tys -> ...`, the recursion as a loop
        let mut acc = acc;
        for ty in tys {
            acc = find(ty, var, update, is_invariant, acc, env);
            if is_invariant(&acc) {
                return acc;
            }
        }
        acc
    }

    fn find_with_variances<A>(
        tys: &[DeclTy],
        variances: &[Variance],
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        // The recursion as a loop; it stops at the end of the shorter list
        // (assumes well-formedness)
        let mut acc = acc;
        for (ty, tp_variance) in tys.iter().zip(variances.iter()) {
            acc = find(ty, mul(var, *tp_variance), update, is_invariant, acc, env);
            if is_invariant(&acc) {
                return acc;
            }
        }
        acc
    }

    fn find_tuple_ty<A>(
        d::TupleType(t_required, t_optional, t_extra): &d::TupleType<R>,
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        let acc = find_list(t_required, var, update, is_invariant, acc, env);
        if is_invariant(&acc) {
            acc
        } else {
            let acc = find_list(t_optional, var, update, is_invariant, acc, env);
            if is_invariant(&acc) {
                acc
            } else {
                match t_extra {
                    d::TupleExtra::Tsplat(ty) => find(ty, var, update, is_invariant, acc, env),
                    d::TupleExtra::Tvariadic(t_variadic) => {
                        find(t_variadic, var, update, is_invariant, acc, env)
                    }
                }
            }
        }
    }

    fn find_shape_ty<A>(
        d::ShapeTypeSimple(s_unknown_value, s_fields): &d::ShapeTypeSimple<R>,
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        let acc = find(s_unknown_value, var, update, is_invariant, acc, env);
        if is_invariant(&acc) {
            acc
        } else {
            // `TShapeMap.bindings`: the `BTreeMap` of the fields is ordered as
            // `TShapeField.compare` orders them (on the names only)
            let tys: Vec<DeclTy> = s_fields.values().map(|sft| sft.ty.clone()).collect();
            find_list(&tys, var, update, is_invariant, acc, env)
        }
    }

    fn find_fun_ty<A>(
        fun_ty: &DeclFunType,
        var: Variance,
        update: Update<'_, A>,
        is_invariant: IsInvariant<'_, A>,
        acc: A,
        env: &Env,
    ) -> A {
        let acc = find(&fun_ty.ret, var, update, is_invariant, acc, env);
        if is_invariant(&acc) {
            acc
        } else {
            let var = mul(var, Variance::Contravariant);
            let tys: Vec<DeclTy> = fun_ty.params.iter().map(|fp| fp.ty.clone()).collect();
            let acc = find_list(&tys, var, update, is_invariant, acc, env);
            if is_invariant(&acc) {
                acc
            } else {
                // Type parameters may appearing in upper, lower, or equality bounds
                // of other type parameters so we need to consider the polarity of these
                // occurences too
                let (tys, variances): (Vec<DeclTy>, Vec<Variance>) = fun_ty
                    .tparams
                    .iter()
                    .flat_map(|tp| {
                        tp.constraints.iter().map(|(cstr_kind, ty)| {
                            let variance = match cstr_kind {
                                ConstraintKind::ConstraintAs => Variance::Contravariant,
                                ConstraintKind::ConstraintSuper => Variance::Covariant,
                                ConstraintKind::ConstraintEq => Variance::Invariant,
                            };
                            (ty.clone(), variance)
                        })
                    })
                    .unzip();
                let var = Variance::Covariant;
                find_with_variances(&tys, &variances, var, update, is_invariant, acc, env)
            }
        }
    }

    fn mentions_this(ty: &DeclTy) -> bool {
        let res = Cell::new(false);
        let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
            d::Ty_::Tthis => {
                res.set(true);
                (*ctx, TransformTopDown::Stop(ty))
            }
            _ => (*ctx, TransformTopDown::Continue(ty)),
        };
        let _ = transform_top_down_decl_ty(ty.clone(), &on_ty, &continue_rc_bound::<()>, &());
        res.get()
    }

    fn mentioned_ty_params(ty: &DeclTy) -> s_set::T {
        let res = RefCell::new(s_set::T::new());
        let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
            d::Ty_::Tgeneric(nm) => {
                res.borrow_mut().insert(nm.as_str().to_string());
                (*ctx, TransformTopDown::Stop(ty))
            }
            _ => (*ctx, TransformTopDown::Continue(ty)),
        };
        let _ = transform_top_down_decl_ty(ty.clone(), &on_ty, &continue_rc_bound::<()>, &());
        res.into_inner()
    }

    fn update(acc: Option<Variance>, var: Variance) -> Option<Variance> {
        Some(match acc {
            None => var,
            Some(acc) => join(acc, var),
        })
    }

    fn update_this(ty: &DeclTy, acc: Option<Variance>, var: Variance) -> Option<Variance> {
        match ty.node_ref() {
            d::Ty_::Tthis => update(acc, var),
            d::Ty_::Tmixed
            | d::Ty_::Twildcard
            | d::Ty_::Tany
            | d::Ty_::Tnonnull
            | d::Ty_::Tdynamic
            | d::Ty_::Tprim(_)
            | d::Ty_::Tgeneric(_)
            | d::Ty_::Taccess(_)
            | d::Ty_::Toption(_)
            | d::Ty_::Tlike(_)
            | d::Ty_::TclassPtr(_)
            | d::Ty_::TvecOrDict(_)
            | d::Ty_::Tunion(_)
            | d::Ty_::Tintersection(_)
            | d::Ty_::Trefinement(_)
            | d::Ty_::Tfun(_)
            | d::Ty_::Ttuple(_)
            | d::Ty_::Tshape(_)
            | d::Ty_::Tapply(_) => acc,
        }
    }

    fn is_invariant(v: &Option<Variance>) -> bool {
        match v {
            None => false,
            Some(Variance::Invariant) => true,
            Some(_) => false,
        }
    }

    /// Count the occurrences of the bare [this] type inside [ty], treating [ty] as
    /// a parameter type (i.e. the top-level position is contravariant), from which
    /// a value of type [this] can be obtained — i.e. occurrences reached
    /// contravariantly or invariantly. Purely covariant occurrences (a value of
    /// type [this] cannot be obtained from them) and occurrences of [this] as the
    /// root of a type constant access (e.g. [this::T]) are not counted.
    pub fn count_obtainable_this_in_param(
        follow_bounds: bool,
        upper_bounds: &s_map::T<Vec<DeclTy>>,
        ty: &DeclTy,
        env: &Env,
    ) -> isize {
        type Ctx = (s_map::T<Vec<DeclTy>>, s_set::T);
        let on_ty = |ty: DeclTy, ctx: &Ctx| -> (Ctx, TransformTopDown<DeclTy>) {
            let (upper_bounds, seen) = ctx;
            match ty.node_ref() {
                d::Ty_::Tgeneric(name) if !seen.contains(name.as_str()) => {
                    match upper_bounds.get(name.as_str()) {
                        Some(bounds) if !bounds.is_empty() => {
                            // `List.dedup_and_sort bounds ~compare:compare_decl_ty`
                            let mut bounds = bounds.clone();
                            bounds.sort_by(|a, b| {
                                crate::typing_defs_core::compare_decl_ty(None, a, b)
                            });
                            bounds.dedup_by(|a, b| {
                                crate::typing_defs_core::compare_decl_ty(None, a, b)
                                    == std::cmp::Ordering::Equal
                            });
                            let seen = seen.update(name.as_str().to_string());
                            let ty = decl_intersection(ty.reason().clone(), bounds);
                            ((upper_bounds.clone(), seen), TransformTopDown::Restart(ty))
                        }
                        _ => (ctx.clone(), TransformTopDown::Stop(ty)),
                    }
                }
                d::Ty_::Tgeneric(_) => (ctx.clone(), TransformTopDown::Stop(ty)),
                d::Ty_::Tfun(ft) => {
                    let upper_bounds = type_parameter_upper_bounds(
                        upper_bounds.clone(),
                        &ft.tparams,
                        &ft.where_constraints,
                    );
                    let seen = ft.tparams.iter().fold(seen.clone(), |seen, tparam| {
                        seen.without(tparam.name.id_ref().as_str())
                    });
                    ((upper_bounds, seen), TransformTopDown::Continue(ty))
                }
                _ => (ctx.clone(), TransformTopDown::Continue(ty)),
            }
        };
        let ty = if !follow_bounds {
            ty.clone()
        } else {
            transform_top_down_decl_ty(
                ty.clone(),
                &on_ty,
                &continue_rc_bound::<Ctx>,
                &(upper_bounds.clone(), s_set::T::new()),
            )
        };
        let ty = &ty;
        // [find] already excludes [this::T] (it does not descend into [Taccess])
        // and threads variance correctly through containers, function types and
        // declared class-level variance, so we just count the [this] nodes reached
        // in a position from which a value of type [this] can be *obtained*. We
        // disable the [is_invariant] early-exit so that every occurrence is visited.
        //
        // An occurrence is "obtainable" when it is reached contravariantly or
        // invariantly:
        // - contravariant (e.g. [this], [vec<this>], [(function(): this)]): the
        //   caller supplies, or a callback yields, a [this] value;
        // - invariant (e.g. [Box<this>] where [Box<T>] is invariant): the value can
        //   be read out (e.g. [Box::get]). Invariance pins the container's element
        //   *type*, but its runtime contents may be any subtype, so two invariant
        //   occurrences can still yield two values of different runtime classes.
        // Purely covariant occurrences (e.g. [(function(this): void)], which only
        // *accepts* a [this]) yield nothing and are not counted.
        let update = |ty: &DeclTy, acc: isize, var: Variance| match ty.node_ref() {
            d::Ty_::Tthis => match var {
                Variance::Contravariant | Variance::Invariant => acc + 1,
                Variance::Covariant => acc,
            },
            _ => acc,
        };
        find(
            ty,
            Variance::Contravariant,
            &update,
            &|_: &isize| false,
            0,
            env,
        )
    }

    pub fn analyse_this(fun_ty: &DeclFunType, env: &Env) -> Option<Variance> {
        let v_opt = find_fun_ty(
            fun_ty,
            Variance::Covariant,
            &update_this,
            &is_invariant,
            None,
            env,
        );
        match v_opt {
            Some(Variance::Invariant) => Some(Variance::Invariant),
            _ => {
                // The previous traversal handles usage of `this` in parameters, return type,
                // type parameter bounds (including class refinements within those bounds).
                // However, we also need to prevent the substitution of `this` for its bound if it appears
                // in a where constraint
                let res: Result<bool, ()> = fun_ty.where_constraints.iter().try_fold(
                    false,
                    |acc, d::WhereConstraint(ty1, _, ty2)| {
                        if mentions_this(ty1) || mentions_this(ty2) {
                            Err(())
                        } else {
                            Ok(acc)
                        }
                    },
                );
                if res.is_err() {
                    Some(Variance::Invariant)
                } else {
                    v_opt
                }
            }
        }
    }

    fn update_ty_params(
        ty_param_names: &s_set::T,
        ty: &DeclTy,
        acc: s_map::T<Option<Variance>>,
        var: Variance,
    ) -> s_map::T<Option<Variance>> {
        match ty.node_ref() {
            d::Ty_::Tgeneric(name) if ty_param_names.contains(name.as_str()) => {
                // `S_map.update name f acc`, where `f` always returns `Some _`
                let mut acc = acc;
                let v = match acc.get(name.as_str()) {
                    None | Some(None) => Some(var),
                    Some(Some(v)) => Some(join(*v, var)),
                };
                acc.insert(name.as_str().to_string(), v);
                acc
            }
            d::Ty_::Tthis
            | d::Ty_::Tmixed
            | d::Ty_::Twildcard
            | d::Ty_::Tany
            | d::Ty_::Tnonnull
            | d::Ty_::Tdynamic
            | d::Ty_::Tprim(_)
            | d::Ty_::Tgeneric(_)
            | d::Ty_::Taccess(_)
            | d::Ty_::Toption(_)
            | d::Ty_::Tlike(_)
            | d::Ty_::TclassPtr(_)
            | d::Ty_::TvecOrDict(_)
            | d::Ty_::Tunion(_)
            | d::Ty_::Tintersection(_)
            | d::Ty_::Trefinement(_)
            | d::Ty_::Tfun(_)
            | d::Ty_::Ttuple(_)
            | d::Ty_::Tshape(_)
            | d::Ty_::Tapply(_) => acc,
        }
    }

    fn all_invariant(vs: &s_map::T<Option<Variance>>) -> bool {
        vs.values().all(is_invariant)
    }

    pub fn analyse_ty_params(
        fun_ty: &DeclFunType,
        ty_param_names: &s_set::T,
        env: &Env,
    ) -> s_map::T<Option<Variance>> {
        let update = |ty: &DeclTy, acc: s_map::T<Option<Variance>>, var: Variance| {
            update_ty_params(ty_param_names, ty, acc, var)
        };
        let acc: s_map::T<Option<Variance>> = s_map::of_list(
            ty_param_names
                .iter()
                .map(|name| (name.clone(), None))
                .collect(),
        );
        let var_opt = find_fun_ty(
            fun_ty,
            Variance::Covariant,
            &update,
            &all_invariant,
            acc,
            env,
        );
        let in_where_constraint = fun_ty.where_constraints.iter().fold(
            s_set::T::new(),
            |acc, d::WhereConstraint(ty1, _, ty2)| {
                acc.union(mentioned_ty_params(ty1))
                    .union(mentioned_ty_params(ty2))
            },
        );
        var_opt
            .into_iter()
            .map(|(nm, var_opt)| {
                let v = if in_where_constraint.contains(&nm) {
                    Some(Variance::Invariant)
                } else {
                    var_opt
                };
                (nm, v)
            })
            .collect()
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::typing_extract_method::tests::generic;
        use crate::typing_extract_method::tests::int;
        use crate::typing_extract_method::tests::this;

        #[test]
        fn mul_composes_variances() {
            use Variance::*;
            assert_eq!(mul(Covariant, Contravariant), Contravariant);
            assert_eq!(mul(Contravariant, Covariant), Contravariant);
            assert_eq!(mul(Contravariant, Contravariant), Covariant);
            assert_eq!(mul(Covariant, Covariant), Covariant);
            assert_eq!(mul(Invariant, Covariant), Invariant);
            assert_eq!(mul(Contravariant, Invariant), Invariant);
        }

        #[test]
        fn join_is_invariant_unless_both_agree() {
            use Variance::*;
            assert_eq!(join(Covariant, Covariant), Covariant);
            assert_eq!(join(Contravariant, Contravariant), Contravariant);
            assert_eq!(join(Covariant, Contravariant), Invariant);
            assert_eq!(join(Invariant, Covariant), Invariant);
        }

        #[test]
        fn update_this_only_counts_this() {
            use Variance::*;
            assert_eq!(update_this(&this(), None, Covariant), Some(Covariant));
            assert_eq!(
                update_this(&this(), Some(Covariant), Contravariant),
                Some(Invariant)
            );
            assert_eq!(
                update_this(&int(), Some(Covariant), Contravariant),
                Some(Covariant)
            );
            assert_eq!(update_this(&generic("T"), None, Covariant), None);
        }

        #[test]
        fn mentions_this_and_mentioned_ty_params() {
            let ty = DeclTy::new(
                crate::typing_extract_method::tests::r(),
                d::Ty_::Tunion(
                    [
                        generic("T"),
                        DeclTy::new(R::none(), d::Ty_::Toption(this())),
                    ]
                    .into(),
                ),
            );
            assert!(mentions_this(&ty));
            assert!(!mentions_this(&generic("T")));
            let names: Vec<String> = mentioned_ty_params(&ty).into_iter().collect();
            assert_eq!(names, vec!["T"]);
        }

        #[test]
        fn update_ty_params_joins_the_variances_of_a_name() {
            use Variance::*;
            let names: s_set::T = ["T".to_string()].into_iter().collect();
            let acc: s_map::T<Option<Variance>> = [("T".to_string(), None)].into_iter().collect();
            let acc = update_ty_params(&names, &generic("T"), acc, Covariant);
            assert_eq!(acc.get("T"), Some(&Some(Covariant)));
            let acc = update_ty_params(&names, &generic("U"), acc, Contravariant);
            assert_eq!(acc.get("U"), None);
            let acc = update_ty_params(&names, &generic("T"), acc, Contravariant);
            assert_eq!(acc.get("T"), Some(&Some(Invariant)));
            assert!(all_invariant(&acc));
        }
    }
}

// -- Type constant analysis and substitutions ------------------------------

mod typeconst_analysis {
    use super::*;

    /// A type constant in an access path: the `(Pos_or_decl.t * string)` of a
    /// `Taccess`.
    pub type Const = Positioned<TypeConstName, BPos>;

    /// Find the intersection of a type constant definition; this is used to find
    /// the implied bounds on nested type constants when the outer type constant
    /// has upper and lower bounds but here we make no assumptions about
    /// well-formedness of the bounds i.e. we don't assumed LB <: UB.
    /// There are three cases to consider
    /// - Both type constants are abstract; here we take the least upper bound
    /// and greatest lower bound
    /// - Both type constants are concrete; here we take the intersection of the
    /// constants
    /// - One is concrete and the other abstract; here we treat the concrete
    /// constants as an abstract constant with equal upper and lower bound
    ///
    /// When the bounds of the type constants _are_ subtypes, this is equivalent
    /// to using the definition in the lower bound. We don't do that here since
    /// lifting the method definition is just and elaboration step.
    fn meet_typeconst(reason: &R, tc1: &Typeconst, tc2: &Typeconst) -> Typeconst {
        match (tc1, tc2) {
            (
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: ty1 }),
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: ty2 }),
            ) => {
                let tc_type = decl_intersection(reason.clone(), vec![ty1.clone(), ty2.clone()]);
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type })
            }
            (
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: ub1,
                    super_constraint: lb1,
                    default: dflt1,
                }),
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: ub2,
                    super_constraint: lb2,
                    default: dflt2,
                }),
            ) => {
                let atc_as_constraint = option_merge(ub1, ub2, |ty1, ty2| {
                    decl_intersection(reason.clone(), vec![ty1, ty2])
                });
                let atc_super_constraint = option_merge(lb1, lb2, |ty1, ty2| {
                    decl_union(reason.clone(), vec![ty1, ty2])
                });
                let atc_default = option_merge(dflt1, dflt2, |ty1, ty2| {
                    decl_intersection(reason.clone(), vec![ty1, ty2])
                });
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    default: atc_default,
                })
            }
            (
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    ..
                }),
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }),
            )
            | (
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }),
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    ..
                }),
            ) => {
                let tc_type = match (atc_as_constraint, atc_super_constraint) {
                    (None, None) => tc_type.clone(),
                    (Some(ub), None) => {
                        decl_intersection(reason.clone(), vec![tc_type.clone(), ub.clone()])
                    }
                    (None, Some(lb)) => {
                        decl_union(reason.clone(), vec![tc_type.clone(), lb.clone()])
                    }
                    (Some(ub), Some(lb)) => decl_union(
                        reason.clone(),
                        vec![
                            lb.clone(),
                            decl_intersection(reason.clone(), vec![tc_type.clone(), ub.clone()]),
                        ],
                    ),
                };
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type })
            }
        }
    }

    /// Helper to accumulate the path of projections on a given root type
    fn access_path(root: &DeclTy, prefix: Vec<Const>) -> (DeclTy, Vec<Const>) {
        match root.node_ref() {
            d::Ty_::Taccess(ta) => access_path(&ta.ty, cons(ta.type_const.clone(), prefix)),
            _ => (root.clone(), prefix),
        }
    }

    /// Helper to lift transformation on [decl_ty] into transformations on a
    /// [typeconst]
    fn transform_typeconst(typeconst: &Typeconst, f: &dyn Fn(DeclTy) -> DeclTy) -> Typeconst {
        match typeconst {
            d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }) => {
                let tc_type = f(tc_type.clone());
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type })
            }
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: atc_as_constraint,
                super_constraint: atc_super_constraint,
                default: atc_default,
            }) => {
                let atc_as_constraint = atc_as_constraint.clone().map(f);
                let atc_super_constraint = atc_super_constraint.clone().map(f);
                let atc_default = atc_default.clone().map(f);
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    default: atc_default,
                })
            }
        }
    }

    pub mod trie {
        use super::*;

        #[derive(Clone)]
        pub enum Base {
            Root,
            Typeconst {
                typeconst: Typeconst,
                pos: BPos,
                origin: Option<String>,
            },
        }

        pub fn transform_base(base: &Base, f: &dyn Fn(DeclTy) -> DeclTy) -> Base {
            match base {
                Base::Root => Base::Root,
                Base::Typeconst {
                    typeconst,
                    pos,
                    origin,
                } => {
                    let typeconst = transform_typeconst(typeconst, f);
                    Base::Typeconst {
                        typeconst,
                        pos: pos.clone(),
                        origin: origin.clone(),
                    }
                }
            }
        }

        #[derive(Clone)]
        pub struct T {
            pub base: Base,
            pub children: s_map::T<Status>,
        }

        #[derive(Clone)]
        pub enum Status {
            Undefined,
            Defined(T),
        }

        fn merge_help(s1: &Status, s2: &Status) -> Option<Status> {
            match (s1, s2) {
                (Status::Undefined, s) | (s, Status::Undefined) => Some(s.clone()),
                (Status::Defined(t1), Status::Defined(t2)) => Some(Status::Defined(merge(t1, t2))),
            }
        }

        pub fn merge(t1: &T, t2: &T) -> T {
            let combine: &dyn Fn(&String, &Status, &Status) -> Option<Status> =
                &|_key, s1, s2| merge_help(s1, s2);
            let children = s_map::union(Some(combine), &t1.children, &t2.children);
            T {
                base: t1.base.clone(),
                children,
            }
        }

        pub fn transform(t: &T, f: &dyn Fn(DeclTy) -> DeclTy) -> T {
            let T { base, children } = t;
            let base = transform_base(base, f);
            let children = children
                .iter()
                .map(|(k, status)| (k.clone(), transform_status(status, f)))
                .collect();
            T { base, children }
        }

        fn transform_status(status: &Status, f: &dyn Fn(DeclTy) -> DeclTy) -> Status {
            match status {
                Status::Undefined => Status::Undefined,
                Status::Defined(t) => Status::Defined(transform(t, f)),
            }
        }

        // -- Pretty printing -----------------------------------------------------

        /// `Typing_print.debug_decl env ty` (the printer takes the `oxidized`
        /// form of decl types)
        fn debug_decl(env: &Env, ty: &DeclTy) -> String {
            use pos::ToOxidized;
            crate::typing_print::debug_decl(env, &ty.clone().to_oxidized())
        }

        // The accumulators of the printing functions are OCaml lists built by
        // consing, which `show` reverses: here they are vectors in the
        // reversed order (pushed to), which `show` concatenates as they are.

        fn show_help(
            t: &s_map::T<Status>,
            indent: usize,
            acc: Vec<String>,
            env: &Env,
        ) -> Vec<String> {
            t.iter().fold(acc, |acc, (nm, status)| {
                show_status((nm, status), indent, acc, env)
            })
        }

        fn show_status(
            (nm, status): (&str, &Status),
            indent: usize,
            mut acc: Vec<String>,
            env: &Env,
        ) -> Vec<String> {
            match status {
                Status::Undefined => {
                    let padding = " ".repeat(indent);
                    acc.push(format!("{}{} == undefined\n", padding, nm));
                    acc
                }
                Status::Defined(T {
                    base: Base::Typeconst { typeconst, .. },
                    children,
                }) => {
                    let acc = show_typeconst((nm, typeconst), indent, acc, env);
                    let indent = indent + 4;
                    show_help(children, indent, acc, env)
                }
                Status::Defined(T {
                    base: Base::Root,
                    children,
                }) => {
                    let padding = " ".repeat(indent);
                    acc.push(format!("{}this\n", padding));
                    let indent = indent + 4;
                    show_help(children, indent, acc, env)
                }
            }
        }

        fn show_typeconst(
            (nm, typeconst): (&str, &Typeconst),
            indent: usize,
            mut acc: Vec<String>,
            env: &Env,
        ) -> Vec<String> {
            let padding = " ".repeat(indent);
            let data = match typeconst {
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }) => {
                    format!("{}{} == {}\n", padding, nm, debug_decl(env, tc_type))
                }
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    ..
                }) => format!(
                    "{}{} as {} super {}\n",
                    padding,
                    nm,
                    match atc_as_constraint {
                        None => "(none)".to_string(),
                        Some(ty) => debug_decl(env, ty),
                    },
                    match atc_super_constraint {
                        None => "(none)".to_string(),
                        Some(ty) => debug_decl(env, ty),
                    }
                ),
            };
            acc.push(data);
            acc
        }

        pub fn show((name, t): (&str, &T), env: &Env) -> String {
            show_help(&t.children, 4, vec![format!("{}\n", name)], env).concat()
        }

        // -- Helpers ------------------------------------------------------------
        pub fn empty() -> T {
            T {
                base: Base::Root,
                children: s_map::T::new(),
            }
        }

        pub fn constants(t: &T) -> Vec<String> {
            t.children.keys().cloned().collect()
        }

        pub fn update(t: T, const_name: &str, child: Status) -> T {
            let T { mut children, base } = t;
            children.insert(const_name.to_string(), child);
            T { base, children }
        }

        fn of_typeconst(origin: Option<String>, typeconst: Typeconst, const_pos: BPos) -> T {
            let base = Base::Typeconst {
                typeconst,
                pos: const_pos,
                origin,
            };
            T {
                base,
                children: s_map::T::new(),
            }
        }

        pub fn status_of_typeconst(
            origin: Option<String>,
            typeconst: Typeconst,
            const_pos: BPos,
        ) -> Status {
            let t = of_typeconst(origin, typeconst, const_pos);
            Status::Defined(t)
        }

        pub fn find_path(t: &T, path: &[Const]) -> Option<Status> {
            match path.split_first() {
                None => Some(Status::Defined(t.clone())),
                Some((next, rest)) => match t.children.get(next.id_ref().as_str()) {
                    None => None,
                    Some(Status::Undefined) => Some(Status::Undefined),
                    Some(Status::Defined(t)) => find_path(t, rest),
                },
            }
        }
    }

    /// An analysis is a set of of type constant tries one of which is considered
    /// to be [this]
    #[derive(Clone)]
    pub struct T {
        pub this_name: String,
        pub this_folded_class: folded_class::T,
        pub this_trie: trie::T,
        pub tries: s_map::T<(DeclTy, trie::T)>,
    }

    fn create(this_name: String, this_folded_class: folded_class::T) -> T {
        T {
            this_name,
            this_folded_class,
            this_trie: trie::empty(),
            tries: s_map::T::new(),
        }
    }

    #[derive(Clone)]
    struct Root {
        root_name: String,
        root_folded_class: folded_class::T,
        root_trie: trie::T,
    }

    #[derive(Clone)]
    struct State {
        root: Root,
        analysis: T,
    }

    /// Pretty print an analysis for debugging
    #[allow(dead_code)]
    pub fn show(t: &T, env: &Env) -> String {
        let T {
            this_name,
            this_trie,
            tries,
            ..
        } = t;
        let this = (format!("this ({})", this_name), this_trie.clone());
        let others = tries
            .iter()
            .map(|(key, (_, trie))| (key.clone(), trie.clone()));
        let lines: Vec<String> = std::iter::once(this)
            .chain(others)
            .map(|(name, trie)| trie::show((&name, &trie), env))
            .collect();
        lines.join("\n\n")
    }

    fn find_trie_for(state: &State, class_name: &str) -> Option<trie::T> {
        let State {
            root,
            analysis: T { tries, .. },
        } = state;
        if class_name == root.root_name {
            Some(root.root_trie.clone())
        } else {
            tries.get(class_name).map(|(_, trie)| trie.clone())
        }
    }

    // -- Helpers -------------------------------------------------------------

    enum TypeForAccess {
        Constant(DeclTy),
        UpperBound(DeclTy),
        LowerBound(DeclTy),
        UpperAndLowerBounds { upper: DeclTy, lower: DeclTy },
        NoType,
    }

    fn transform_type_for_access(t: TypeForAccess, f: &dyn Fn(DeclTy) -> DeclTy) -> TypeForAccess {
        match t {
            TypeForAccess::Constant(decl_ty) => TypeForAccess::Constant(f(decl_ty)),
            TypeForAccess::UpperBound(decl_ty) => TypeForAccess::UpperBound(f(decl_ty)),
            TypeForAccess::LowerBound(decl_ty) => TypeForAccess::LowerBound(f(decl_ty)),
            TypeForAccess::UpperAndLowerBounds { upper, lower } => {
                // OCaml evaluates the fields of a record from right to left (`f`
                // has no effect)
                let lower = f(lower);
                let upper = f(upper);
                TypeForAccess::UpperAndLowerBounds { upper, lower }
            }
            TypeForAccess::NoType => TypeForAccess::NoType,
        }
    }

    /// When accessing a type constant through another type constant we need to
    /// determine the type that contains the next type constant.
    /// For a 'concrete' type constant this is the definition and for an 'abstract' type constant it is
    /// the upper-bound, if it exists.
    fn type_for_access(typeconst: &Typeconst) -> TypeForAccess {
        match typeconst {
            d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }) => {
                TypeForAccess::Constant(tc_type.clone())
            }
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: Some(ty),
                super_constraint: None,
                ..
            }) => TypeForAccess::UpperBound(ty.clone()),
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: None,
                super_constraint: Some(ty),
                ..
            }) => {
                // We can't actually do anything with this but we return it explicitly
                // just in case we want to distinguish from the [No_type] case
                TypeForAccess::LowerBound(ty.clone())
            }
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: Some(upper),
                super_constraint: Some(lower),
                ..
            }) => TypeForAccess::UpperAndLowerBounds {
                upper: upper.clone(),
                lower: lower.clone(),
            },
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: None,
                super_constraint: None,
                ..
            }) => TypeForAccess::NoType,
        }
    }

    /// Helper to convert between type constant refinement representations
    fn typeconst_of_refined_const(rc: &DeclRefinedConst, const_pos: &BPos) -> Typeconst {
        match &rc.bound {
            d::RefinedConstBound::Exact(tc_type) => {
                d::Typeconst::TCConcrete(d::ConcreteTypeconst {
                    ty: tc_type.clone(),
                })
            }
            d::RefinedConstBound::Loose(bounds) => {
                let d::RefinedConstBounds {
                    lower: tr_lower,
                    upper: tr_upper,
                } = bounds;
                let atc_as_constraint = if tr_upper.is_empty() {
                    None
                } else {
                    let reason = R::witness_from_decl(const_pos.clone());
                    Some(decl_intersection(reason, tr_upper.to_vec()))
                };
                let atc_super_constraint = if tr_lower.is_empty() {
                    None
                } else {
                    let reason = R::witness_from_decl(const_pos.clone());
                    Some(decl_union(reason, tr_lower.to_vec()))
                };
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    default: None,
                })
            }
        }
    }

    /// When following a path of type constant accesses the meaning of [this] is
    /// relative to the class containing the type constant. Since we want to
    /// extract the contants for use from some base class we need to make these
    /// references absolute.
    ///
    /// As an example, consider the following
    ///
    /// ```text
    /// class C<T> { }
    ///
    /// class B {
    ///   const type TB as C<this>;
    /// }
    ///
    /// abstract class A {
    ///   abstract const type TA as B;
    ///   public static function wibble(this::TA::TB $_): void {}
    /// }
    /// ```
    ///
    /// When access `this::TA::TB` we end up with `C<this>` where `this` corresponds
    /// to the class in which `TB` is defined. Since we have access this type
    /// through `A` we can make it 'absolute' by subsituting occurrences of
    /// this in the definition of `this::TA::TB` with prefix of that path i.e.
    /// `this::TA`. Doing so gives us `this::TA::TB as C<this::TA>`
    fn this_to_absolute(ty: DeclTy, prefix: &[Const]) -> DeclTy {
        // `build this reason prefix ~k`: the continuation applied to the
        // result for the rest of the prefix
        fn build(this: DeclTy, reason: &R, prefix: &[Const]) -> DeclTy {
            match prefix.split_first() {
                None => this,
                Some((next, rest)) => {
                    let root = build(this, reason, rest);
                    DeclTy::new(
                        reason.clone(),
                        d::Ty_::Taccess(Box::new(d::TaccessType {
                            ty: root,
                            type_const: next.clone(),
                        })),
                    )
                }
            }
        }
        let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
            d::Ty_::Tthis => {
                let reason = ty.reason().clone();
                (*ctx, TransformTopDown::Stop(build(ty, &reason, prefix)))
            }
            _ => (*ctx, TransformTopDown::Continue(ty)),
        };
        transform_top_down_decl_ty(ty, &on_ty, &continue_rc_bound::<()>, &())
    }

    fn replace_this_with(ty: DeclTy, replacement: &DeclTy) -> DeclTy {
        let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
            d::Ty_::Tthis => (*ctx, TransformTopDown::Stop(replacement.clone())),
            _ => (*ctx, TransformTopDown::Continue(ty)),
        };
        transform_top_down_decl_ty(ty, &on_ty, &continue_rc_bound::<()>, &())
    }

    /// Accumulate all types mentioned in the definition or bounds of a type constant
    fn accumulate_tys(typeconst: &Typeconst, tys: Vec<DeclTy>) -> Vec<DeclTy> {
        match typeconst {
            d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }) => {
                cons(tc_type.clone(), tys)
            }
            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: atc_as_constraint,
                super_constraint: atc_super_constraint,
                ..
            }) => match (atc_as_constraint, atc_super_constraint) {
                (Some(ty1), Some(ty2)) => cons(ty1.clone(), cons(ty2.clone(), tys)),
                (Some(ty), _) | (_, Some(ty)) => cons(ty.clone(), tys),
                _ => tys,
            },
        }
    }

    enum Path {
        This(Vec<Const>),
        Class(DeclTy, String, Vec<Const>),
    }

    /// Fold over [ty] and accumulate type constant access paths for any
    /// [Taccess] which is rooted in [TThis]
    fn paths_of_ty(ty: &DeclTy) -> Vec<Path> {
        // `paths := p :: !paths`: pushed here, and reversed at the end
        let paths: RefCell<Vec<Path>> = RefCell::new(vec![]);
        let on_ty = |decl_ty: DeclTy, ctx: &()| match decl_ty.node_ref() {
            d::Ty_::Taccess(ta) => {
                let (ty, path) = access_path(&ta.ty, vec![ta.type_const.clone()]);
                match ty.node_ref() {
                    d::Ty_::Tthis => paths.borrow_mut().push(Path::This(path)),
                    d::Ty_::Tapply(id_and_tys) => {
                        let class_name = id_and_tys.0.id_ref().as_str().to_string();
                        paths
                            .borrow_mut()
                            .push(Path::Class(ty.clone(), class_name, path))
                    }
                    _ => {}
                }
                (*ctx, TransformTopDown::Stop(decl_ty))
            }
            _ => (*ctx, TransformTopDown::Continue(decl_ty)),
        };
        let _ = transform_top_down_decl_ty(ty.clone(), &on_ty, &continue_rc_bound::<()>, &());
        let mut paths = paths.into_inner();
        paths.reverse();
        paths
    }

    // -- Core logic ----------------------------------------------------------

    fn meet_trie_opt(trie1: &trie::T, trie2: &trie::T, reason: &R) -> Option<trie::T> {
        let trie::T {
            base: b1,
            children: c1,
        } = trie1;
        let trie::T {
            base: b2,
            children: c2,
        } = trie2;
        if !(c1.is_empty() && c2.is_empty()) {
            None
        } else {
            let base_opt = match (b1, b2) {
                (trie::Base::Root, trie::Base::Root) => Some(b1.clone()),
                (
                    trie::Base::Typeconst {
                        typeconst: tc1,
                        pos,
                        origin,
                    },
                    trie::Base::Typeconst { typeconst: tc2, .. },
                ) => {
                    let typeconst = meet_typeconst(reason, tc1, tc2);
                    Some(trie::Base::Typeconst {
                        typeconst,
                        pos: pos.clone(),
                        origin: origin.clone(),
                    })
                }
                _ => None,
            };
            base_opt.map(|base| trie::T {
                base,
                children: c1.clone(),
            })
        }
    }

    /// What `find_type_const`, `access_typeconsts`, `access_typeconst` and
    /// `add_path` thread: the types discovered in the definitions and bounds
    /// of type constants (an OCaml list, head first) and the analysis.
    type Tys = Vec<DeclTy>;

    /// Find the definition or bounds of the next type constant [const_name]
    /// when projecting from [base]. If the constant already appeared in some
    /// other path we can use the information stored in [children] otherwise
    /// we have to look it up from the decl
    fn find_type_const(
        trie: &trie::T,
        tys: Tys,
        const_: &Const,
        prefix: &[Const],
        state: State,
        env: &Env,
    ) -> (trie::Status, Tys, State) {
        let trie::T { children, base } = trie;
        let const_pos = const_.pos();
        let const_name = const_.id_ref().as_str();
        match children.get(const_name) {
            // Happy path - we've already seen the constant as part of some other path
            // so reuse the result
            Some(status) => (status.clone(), tys, state),
            // We haven't already seen this constant within this path we need to find the
            // definition within the current type we are projecting from
            None => match base {
                trie::Base::Root => {
                    // If we are projecting from the root we can use the [folded_class]
                    // corresponding to that root directly - since we are at the root
                    // we don't need to rewrite `this` to make absolute
                    let typeconst_opt =
                        typing_env::get_typeconst(env, &state.root.root_folded_class, const_name);
                    let (status, tys) = match typeconst_opt {
                        None => (trie::Status::Undefined, tys),
                        Some(ttc) => {
                            let typeconst = ttc.kind;
                            let origin = ttc.origin.as_str().to_string();
                            // The type constant may be an alias - if so we need need to add
                            // the path to ensure it is substituted
                            let tys = accumulate_tys(&typeconst, tys);
                            let status = trie::status_of_typeconst(
                                Some(origin),
                                typeconst,
                                const_pos.clone(),
                            );
                            (status, tys)
                        }
                    };
                    (status, tys, state)
                }
                trie::Base::Typeconst { typeconst, .. } => {
                    // If the root is a type constant we first need to get the type we're
                    // accessing through:
                    // - for a 'concrete' type constant this is the definition;
                    // - for an 'abstract' type constant it is declared bounds
                    let ty_access = type_for_access(typeconst);
                    access_typeconsts(ty_access, tys, const_, prefix, state, env)
                }
            },
        }
    }

    fn access_typeconsts(
        ty_access: TypeForAccess,
        tys: Tys,
        const_: &Const,
        prefix: &[Const],
        state: State,
        env: &Env,
    ) -> (trie::Status, Tys, State) {
        match ty_access {
            TypeForAccess::Constant(ty) => {
                // Concrete type constant
                access_typeconst(&ty, tys, const_, prefix, state, env)
            }
            TypeForAccess::UpperBound(ty) => {
                // Abstract type constant with an [as] bound only
                access_typeconst(&ty, tys, const_, prefix, state, env)
            }
            TypeForAccess::LowerBound(_) => {
                // Abstract type constant with a [super] bound only; this is undefined
                // since a type constant in a lower bound doesn't require that a concrete
                // definition has such a constant
                (trie::Status::Undefined, tys, state)
            }
            TypeForAccess::NoType => {
                // Abstract type constant with no declared bounds
                (trie::Status::Undefined, tys, state)
            }
            TypeForAccess::UpperAndLowerBounds { upper, lower } => {
                // Abstract type constant with both [as] and [super] bounds;
                // by transitivity if we have LB <: TC <: UB we must have LB <: UB
                // but we are free to declare a type constant where this isn't true.
                // Since we are only elaborating here we treat this as though the user
                // had instead declared the unsatisfiable bounds on a generic so we
                // don't generate an error
                let (status1, tys, state) =
                    access_typeconst(&upper, tys, const_, prefix, state, env);
                let (status2, tys, state) =
                    access_typeconst(&lower, tys, const_, prefix, state, env);
                let status = match (status1, status2) {
                    (status1 @ trie::Status::Defined(_), trie::Status::Undefined) => {
                        // Defined in upper bound but not present in the lower bound - this breaks
                        // the requirement that LB <: UB. We still generate a type without
                        // warning since we are just elaborating the declaration. Any attempt
                        // to use the function will lead to an error, though
                        status1
                    }
                    (
                        status1 @ trie::Status::Undefined,
                        trie::Status::Defined(_) | trie::Status::Undefined,
                    ) => {
                        // Undefined in the upper bound and since we can't conclude it's present
                        // in a type satisfying the bounds we have to say it is undefined
                        status1
                    }
                    (trie::Status::Defined(trie1), trie::Status::Defined(trie2)) => {
                        // Defined in both upper and lower bounds; find the meet of the concrete
                        // or abstract definitions. In practice any instantiable class must have
                        // agreement between type constants but we can't assume that here
                        // since it's possible to _declare_ a typeconstant whose upper and
                        // lower bounds aren't subtypes and so allow disagreement.
                        let reason = R::witness_from_decl(const_.pos().clone());
                        let trie_opt = meet_trie_opt(&trie1, &trie2, &reason);
                        match trie_opt {
                            None => trie::Status::Undefined,
                            Some(trie) => trie::Status::Defined(trie),
                        }
                    }
                };

                (status, tys, state)
            }
        }
    }

    /// Access [const_name] through [base_ty] and modify occurences of `this` in the
    /// typeconstant definition so they are absolute with respect to [folded_class]
    ///
    /// This returns a `(typeconst option, path) result` since it may be the case
    /// that [base_ty] is a path which we haven't yet added to the analysis
    fn access_typeconst(
        base_ty: &DeclTy,
        tys: Tys,
        const_: &Const,
        prefix: &[Const],
        state: State,
        env: &Env,
    ) -> (trie::Status, Tys, State) {
        let const_pos = const_.pos();
        let const_name = const_.id_ref().as_str();
        match base_ty.node_ref() {
            d::Ty_::Tthis => {
                // For this use the [folded_class] corresponding to the absolute root
                // class for the analysis
                let typeconst_opt =
                    typing_env::get_typeconst(env, &state.root.root_folded_class, const_name);
                let (status, tys) = match typeconst_opt {
                    None => (trie::Status::Undefined, tys),
                    Some(ttc) => {
                        let origin = ttc.origin.as_str().to_string();
                        // Ensure references to `this` are made absolute
                        let typeconst =
                            transform_typeconst(&ttc.kind, &|ty| this_to_absolute(ty, prefix));
                        // Accumulate the types in the type constant - if they are aliases
                        // to another type constant we will need to add them to the
                        // analysis
                        let tys = accumulate_tys(&typeconst, tys);
                        let status =
                            trie::status_of_typeconst(Some(origin), typeconst, const_pos.clone());
                        (status, tys)
                    }
                };
                (status, tys, state)
            }
            d::Ty_::Tapply(id_and_tys) => {
                let class_name = id_and_tys.0.id_ref().as_str();
                let folded_class_opt =
                    decl_entry::to_option(typing_env::get_class(env, class_name));
                let typeconst_opt = folded_class_opt.and_then(|folded_class| {
                    typing_env::get_typeconst(env, &folded_class, const_name)
                });
                let (status, tys) = match typeconst_opt {
                    None => (trie::Status::Undefined, tys),
                    Some(ttc) => {
                        let origin = ttc.origin.as_str().to_string();
                        let typeconst =
                            transform_typeconst(&ttc.kind, &|ty| this_to_absolute(ty, prefix));
                        // Accumulate the types in the type constant - if they are aliases
                        // to another type constant we will need to add them to the
                        // analysis
                        let tys = accumulate_tys(&typeconst, tys);
                        let status =
                            trie::status_of_typeconst(Some(origin), typeconst, const_pos.clone());
                        (status, tys)
                    }
                };
                (status, tys, state)
            }
            d::Ty_::Trefinement(tr) => {
                // If there is a refinement check if it contains the contant we want;
                // if not, search in the root type
                match tr.refinement.consts.get(&TypeConstName::new(const_name)) {
                    Some(refined_const) => {
                        // For the definition of the refined constant [this] is in the same
                        // class so don't make absolute
                        let typeconst = typeconst_of_refined_const(refined_const, const_pos);
                        // Accumulate the types in the type constant - if they are aliases
                        // to another type constant we will need to add them to the
                        // analysis
                        let tys = accumulate_tys(&typeconst, tys);
                        let status = trie::status_of_typeconst(None, typeconst, const_pos.clone());
                        (status, tys, state)
                    }
                    None => access_typeconst(&tr.ty, tys, const_, prefix, state, env),
                }
            }
            d::Ty_::Taccess(ta) => {
                // We're accessing a type constant through a type constant access path;
                // ensure the path has been added then access the type constant through
                // its definition or upper bound
                let (ty, path) = access_path(&ta.ty, vec![ta.type_const.clone()]);
                let (state, status_opt) = match ty.node_ref() {
                    d::Ty_::Tthis => {
                        let paths = vec![Path::This(path.clone())];
                        let state = add_paths(state, paths, env);
                        let status_opt = trie::find_path(&state.root.root_trie, &path);
                        (state, status_opt)
                    }
                    d::Ty_::Tapply(id_and_tys) => {
                        let class_name = id_and_tys.0.id_ref().as_str().to_string();
                        let paths = vec![Path::Class(ty.clone(), class_name.clone(), path.clone())];
                        let state = add_paths(state, paths, env);
                        let status_opt = find_trie_for(&state, &class_name)
                            .and_then(|trie| trie::find_path(&trie, &path));
                        (state, status_opt)
                    }
                    _ => {
                        // Here we assume the root must either be [Tapply] or [Tthis] -
                        // the other possibility, [Trefinement], is disallowed
                        (state, None)
                    }
                };
                let base_ty_opt = status_opt.and_then(|status| match status {
                    trie::Status::Undefined => None,
                    trie::Status::Defined(trie::T {
                        base: trie::Base::Root,
                        ..
                    }) => Some(TypeForAccess::Constant(ty.clone())),
                    trie::Status::Defined(trie::T {
                        base: trie::Base::Typeconst { typeconst, .. },
                        ..
                    }) => {
                        let replace = |t: DeclTy| replace_this_with(t, &ty);
                        Some(transform_type_for_access(
                            type_for_access(&typeconst),
                            &replace,
                        ))
                    }
                });
                match base_ty_opt {
                    None => (trie::Status::Undefined, tys, state),
                    Some(base_ty) => access_typeconsts(base_ty, tys, const_, prefix, state, env),
                }
            }
            d::Ty_::Tintersection(members) => {
                // For intersections, we require the type constant to be defined on at least
                // one of its elements; if it is defined on multiple we will refine each element
                // to ensure they agree
                //
                // NB: in the OCaml the pattern `Tintersection tys` shadows the
                // accumulated [tys], so the fold starts from the elements of the
                // intersection, and the [tys] passed in are dropped.
                let (trie_opt, tys, state) = members.iter().fold(
                    (None, members.to_vec(), state),
                    |(acc, tys, state): (Option<trie::T>, Tys, State), ty| {
                        // The result is dropped when the constant is undefined
                        let saved = (tys.clone(), state.clone());
                        match access_typeconst(ty, tys, const_, prefix, state, env) {
                            (trie::Status::Undefined, _, _) => {
                                let (tys, state) = saved;
                                (acc, tys, state)
                            }
                            (trie::Status::Defined(trie2), tys, state) => {
                                let reason = R::witness_from_decl(const_pos.clone());
                                let acc = match acc {
                                    None => Some(trie2),
                                    Some(trie1) => meet_trie_opt(&trie1, &trie2, &reason),
                                };
                                (acc, tys, state)
                            }
                        }
                    },
                );
                let status = match trie_opt {
                    None => trie::Status::Undefined,
                    Some(trie) => trie::Status::Defined(trie),
                };
                (status, tys, state)
            }
            d::Ty_::Tunion(members) => {
                // For unions, we require the refinement to be present on all elements. If
                // it is missing on one the result is undefined
                //
                // NB: as for intersections, the pattern `Tunion tys` of the OCaml
                // shadows the accumulated [tys].
                let (trie_opt_res, tys, state) = members.iter().fold(
                    (Ok(None), members.to_vec(), state),
                    |(acc, tys, state): (Result<Option<trie::T>, ()>, Tys, State), ty| match acc {
                        Err(_) => (acc, tys, state),
                        Ok(acc) => {
                            // The result is dropped when the constant is undefined
                            let saved = (tys.clone(), state.clone());
                            match access_typeconst(ty, tys, const_, prefix, state, env) {
                                (trie::Status::Undefined, _, _) => {
                                    let (tys, state) = saved;
                                    (Err(()), tys, state)
                                }
                                (trie::Status::Defined(trie2), tys, state) => {
                                    let reason = R::witness_from_decl(const_pos.clone());
                                    match acc {
                                        None => (Ok(Some(trie2)), tys, state),
                                        Some(trie1) => match meet_trie_opt(&trie1, &trie2, &reason)
                                        {
                                            Some(trie) => (Ok(Some(trie)), tys, state),
                                            _ => (Err(()), tys, state),
                                        },
                                    }
                                }
                            }
                        }
                    },
                );
                let status = match trie_opt_res {
                    Err(_) => trie::Status::Undefined,
                    Ok(trie_opt) => match trie_opt {
                        None => trie::Status::Undefined,
                        Some(trie) => trie::Status::Defined(trie),
                    },
                };
                (status, tys, state)
            }
            // We can't access type constants through any other type so return [Undefined]
            _ => (trie::Status::Undefined, tys, state),
        }
    }

    fn add_path(
        trie: trie::T,
        tys: Tys,
        (prefix, path): (Vec<Const>, &[Const]),
        state: State,
        env: &Env,
    ) -> (trie::T, Tys, State) {
        match path.split_first() {
            None => {
                // End of the type constant access path; return the updated trie and
                // the types appearing in the definitions or bounds of type constants
                // discovered
                (trie, tys, state)
            }
            Some((const_, path)) => {
                let const_name = const_.id_ref().as_str();
                // Find the type constant [const_name]
                match find_type_const(&trie, tys, const_, &prefix, state, env) {
                    (trie::Status::Undefined, tys, state) => {
                        // If it was undefined we have an error so we can't add the rest of the
                        // path
                        let trie = trie::update(trie, const_name, trie::Status::Undefined);
                        (trie, tys, state)
                    }
                    (trie::Status::Defined(child), tys, state) => {
                        // We found the constant so continue adding the remainder of the path
                        let (child, tys, state) = add_path(
                            child,
                            tys,
                            (cons(const_.clone(), prefix), path),
                            state,
                            env,
                        );
                        // Update the trie with the subtrie for [child]
                        (
                            trie::update(trie, const_name, trie::Status::Defined(child)),
                            tys,
                            state,
                        )
                    }
                }
            }
        }
    }

    /// Add a number of type constant access [paths] while resolving from
    /// [state.root]
    fn add_paths(state: State, paths: Vec<Path>, env: &Env) -> State {
        let mut pending: VecDeque<Path> = paths.into();
        // `let rec aux state = match Queue.dequeue pending with ...`
        let mut state = state;
        loop {
            match pending.pop_front() {
                None => return state,
                Some(Path::This(path)) => {
                    let root_trie = state.root.root_trie.clone();
                    let (root_trie, tys, state_) =
                        add_path(root_trie, vec![], (vec![], &path), state, env);
                    for ty in &tys {
                        pending.extend(paths_of_ty(ty));
                    }
                    let root = Root {
                        root_trie,
                        ..state_.root
                    };
                    state = State {
                        root,
                        analysis: state_.analysis,
                    };
                }
                Some(Path::Class(this_ty, class_name, path)) => {
                    let class_name = if class_name == sn::classes::SELF {
                        state.root.root_name.clone()
                    } else {
                        class_name
                    };
                    let folded_class_opt =
                        decl_entry::to_option(typing_env::get_class(env, &class_name));
                    match folded_class_opt {
                        None => {}
                        Some(folded_class) => {
                            // Find the existing trie for this class if it exists
                            let class_trie =
                                find_trie_for(&state, &class_name).unwrap_or_else(trie::empty);
                            // Add the path with the class as [this]
                            let class_root = Root {
                                root_name: class_name.clone(),
                                root_folded_class: folded_class,
                                root_trie: class_trie.clone(),
                            };
                            let State { root, analysis } = state;
                            let class_state = State {
                                root: class_root,
                                analysis,
                            };
                            let (class_trie, tys, class_state) =
                                add_path(class_trie, vec![], (vec![], &path), class_state, env);
                            // Add the paths ensuring that we replace occurrences of this with class type
                            for ty in &tys {
                                pending
                                    .extend(paths_of_ty(&replace_this_with(ty.clone(), &this_ty)));
                            }
                            // Move the trie for the current class in to the map
                            let analysis = {
                                let mut tries = class_state.analysis.tries.clone();
                                let entry = match tries.get(&class_name) {
                                    None => (this_ty, class_trie),
                                    Some((this_ty, existing_trie)) => (
                                        this_ty.clone(),
                                        trie::merge(existing_trie, &class_trie),
                                    ),
                                };
                                tries.insert(class_name, entry);
                                T {
                                    tries,
                                    ..class_state.analysis
                                }
                            };
                            state = State { root, analysis };
                        }
                    }
                }
            }
        }
    }

    // -- API -----------------------------------------------------------------

    fn add_type(t: T, ty: &DeclTy, env: &Env) -> T {
        let paths = paths_of_ty(ty);
        let root = Root {
            root_name: t.this_name.clone(),
            root_folded_class: t.this_folded_class.clone(),
            root_trie: t.this_trie.clone(),
        };
        let State { root, analysis } = add_paths(State { root, analysis: t }, paths, env);
        let t = T {
            this_trie: root.root_trie,
            ..analysis
        };
        let T {
            this_name,
            this_trie,
            tries,
            this_folded_class,
        } = t;
        // For analysis of classes other than this we need to subsitute occurrences
        // of [this] at the root of typeconst accesses for the class type
        let tries: s_map::T<(DeclTy, trie::T)> = tries
            .iter()
            .map(|(class_name, (replacement, trie))| {
                let f = |ty: DeclTy| replace_this_with(ty, replacement);
                (
                    class_name.clone(),
                    (replacement.clone(), trie::transform(trie, &f)),
                )
            })
            .collect();
        // For the analysis of this we need to subsitute occurrences of typeconst
        // access rooted in the explicit class with [this]
        let this_trie = {
            let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
                d::Ty_::Tapply(id_and_tys) if this_name == id_and_tys.0.id_ref().as_str() => (
                    *ctx,
                    TransformTopDown::Stop(DeclTy::new(ty.reason().clone(), d::Ty_::Tthis)),
                ),
                _ => (*ctx, TransformTopDown::Continue(ty)),
            };
            trie::transform(&this_trie, &|ty: DeclTy| {
                transform_top_down_decl_ty(ty, &on_ty, &continue_rc_bound::<()>, &())
            })
        };
        T {
            this_name,
            this_folded_class,
            this_trie,
            tries,
        }
    }

    fn add_fun_type(t: T, fun_ty: &DeclFunType, env: &Env) -> T {
        let ty = DeclTy::new(R::none(), d::Ty_::Tfun(Box::new(fun_ty.clone())));
        add_type(t, &ty, env)
    }

    /// Generate an analysis of a function type which resolves all type constants
    /// mentioned in the functin type
    pub fn of_fun_type(
        fun_ty: &DeclFunType,
        class_name: &str,
        folded_class: &folded_class::T,
        env: &Env,
    ) -> T {
        let empty = create(class_name.to_string(), folded_class.clone());
        add_fun_type(empty, fun_ty, env)
    }

    fn this_constants(t: &T) -> Vec<String> {
        trie::constants(&t.this_trie)
    }

    pub mod subst {
        use super::*;

        pub mod path {
            use super::*;

            /// `type t = string list [@@deriving ord]`
            pub type T = Vec<String>;

            /// `module Map = Stdlib.Map.Make (Minimal)`
            pub type Map<V> = BTreeMap<T, V>;
        }

        #[derive(Clone)]
        pub struct T {
            pub this_name: String,
            pub this_ty: DeclTy,
            pub tparams: Vec<DeclTparam>,
            pub this_subst: path::Map<DeclTy>,
            pub class_subst: s_map::T<path::Map<DeclTy>>,
        }

        mod projection {
            use super::*;

            #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
            pub enum T {
                This(path::T),
                Class(String, path::T),
            }

            /// `module Set = Stdlib.Set.Make (Minimal)`
            pub type Set = im::OrdSet<T>;
        }

        // -- Application -------------------------------------------------------
        pub fn apply(t: &T, ty: DeclTy) -> DeclTy {
            let T {
                this_name,
                this_ty,
                this_subst,
                class_subst,
                ..
            } = t;
            let on_ty = |ty: DeclTy,
                         ctx: &projection::Set|
             -> (projection::Set, TransformTopDown<DeclTy>) {
                match ty.node_ref() {
                    d::Ty_::Tthis => (ctx.clone(), TransformTopDown::Stop(this_ty.clone())),
                    d::Ty_::Taccess(ta) => {
                        // Try and find a substitution for this type
                        let (root_ty, path) = access_path(&ta.ty, vec![ta.type_const.clone()]);
                        let path: path::T = path
                            .iter()
                            .map(|c| c.id_ref().as_str().to_string())
                            .collect();
                        let projection_opt = match root_ty.node_ref() {
                            d::Ty_::Tthis => Some(projection::T::This(path.clone())),
                            d::Ty_::Tapply(id_and_tys) => Some(projection::T::Class(
                                id_and_tys.0.id_ref().as_str().to_string(),
                                path.clone(),
                            )),
                            _ => None,
                        };
                        match projection_opt {
                            None => (ctx.clone(), TransformTopDown::Stop(ty)),
                            Some(projection) => {
                                if ctx.contains(&projection) {
                                    // If we have made this substitution before doing so again will
                                    // cause us to never terminate so we bail; in practice the
                                    // type constant cycle check should already have caught this
                                    // TODO(mjt) add error
                                    (ctx.clone(), TransformTopDown::Stop(ty))
                                } else {
                                    // Try and find a substitution
                                    let subst_ty_opt = match &projection {
                                        projection::T::This(_) => {
                                            let ty_opt = this_subst.get(&path).cloned();
                                            if ty_opt.is_some() {
                                                ty_opt
                                            } else {
                                                let subst_opt = class_subst.get(this_name);
                                                subst_opt
                                                    .and_then(|subst| subst.get(&path).cloned())
                                            }
                                        }
                                        projection::T::Class(class_name, _) => {
                                            let subst_opt = class_subst.get(class_name);
                                            subst_opt.and_then(|subst| subst.get(&path).cloned())
                                        }
                                    };
                                    // If there is no substitution, stop; if there is record that we've
                                    // seen the source key before and restart the rewrite
                                    match subst_ty_opt {
                                        None => (ctx.clone(), TransformTopDown::Stop(ty)),
                                        Some(ty) => {
                                            let ctx = ctx.update(projection);
                                            (ctx, TransformTopDown::Restart(ty))
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => (ctx.clone(), TransformTopDown::Continue(ty)),
                }
            };
            transform_top_down_decl_ty(
                ty,
                &on_ty,
                &continue_rc_bound::<projection::Set>,
                &projection::Set::new(),
            )
        }

        pub fn apply_fun_ty(t: &T, fun_ty: DeclFunType) -> DeclFunType {
            let ty = DeclTy::new(R::none(), d::Ty_::Tfun(Box::new(fun_ty)));
            match apply(t, ty).node_ref() {
                d::Ty_::Tfun(fun_ty) => (**fun_ty).clone(),
                _ => panic!("Expected function type"),
            }
        }

        // -- Build substitution for --------------------------------------------

        #[derive(Clone)]
        struct GenericInfo {
            pos: BPos,
            upper_bound: Option<DeclTy>,
            lower_bound: Option<DeclTy>,
        }

        /// A substitution from paths of type constants (`A::B`) to types.
        type Subst = path::Map<DeclTy>;
        /// The generics introduced for abstract type constants.
        type Generics = s_map::T<GenericInfo>;

        /// `List.rev rev_path`
        fn rev(rev_path: &[String]) -> path::T {
            rev_path.iter().rev().cloned().collect()
        }

        // -- Build substitution for concrete type constants --------------------

        /// In `aux`, the environment, which the OCaml threads in the
        /// accumulator, is the first parameter.
        fn class_subst_help(
            trie: &trie::T,
            env: &mut Env,
            generics: Generics,
        ) -> (Subst, Generics) {
            fn aux(
                env: &mut Env,
                trie::T { base, children }: &trie::T,
                (const_name, rev_path): (&str, Vec<String>),
                acc: (Subst, Generics),
            ) -> (Subst, Generics) {
                let acc = match base {
                    trie::Base::Typeconst {
                        typeconst: d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }),
                        ..
                    } => {
                        let (mut subst, generics) = acc;
                        let path = rev(&rev_path);
                        subst.insert(path, tc_type.clone());
                        (subst, generics)
                    }
                    trie::Base::Typeconst {
                        typeconst:
                            d::Typeconst::TCAbstract(d::AbstractTypeconst {
                                as_constraint: upper_bound,
                                super_constraint: lower_bound,
                                ..
                            }),
                        pos,
                        ..
                    } => {
                        let (subst, mut generics) = acc;
                        let generic_name = typing_env::fresh_param_name(env, const_name);
                        let subst = {
                            let mut subst = subst;
                            let path = rev(&rev_path);
                            let reason = R::witness_from_decl(pos.clone());
                            let ty =
                                DeclTy::new(reason, d::Ty_::Tgeneric(TypeName::new(&generic_name)));
                            subst.insert(path, ty);
                            subst
                        };
                        generics.insert(
                            generic_name,
                            GenericInfo {
                                pos: pos.clone(),
                                upper_bound: upper_bound.clone(),
                                lower_bound: lower_bound.clone(),
                            },
                        );
                        (subst, generics)
                    }
                    trie::Base::Root => acc,
                };
                // `S_map.fold`, in increasing order of the keys
                children
                    .iter()
                    .fold(acc, |acc, (key, status)| match status {
                        trie::Status::Undefined => acc,
                        trie::Status::Defined(t) => {
                            aux(env, t, (key, cons(key.clone(), rev_path.clone())), acc)
                        }
                    })
            }
            aux(env, trie, ("", vec![]), (path::Map::new(), generics))
        }

        fn class_subst(
            super::T { tries, .. }: &super::T,
            env: &mut Env,
            generics: Generics,
        ) -> (s_map::T<Subst>, Generics) {
            tries.iter().fold(
                (s_map::T::new(), generics),
                |(mut tries, generics), (class_name, (_ty, trie))| {
                    let (subst, generics) = class_subst_help(trie, env, generics);
                    tries.insert(class_name.clone(), subst);
                    (tries, generics)
                },
            )
        }

        // -- Build substitution for abstract type constants --------------------

        /// The refinements of a class refinement (`refined_const S_map.t`).
        type Rfmts = BTreeMap<TypeConstName, DeclRefinedConst>;

        fn add_refinement(
            mut rfmts: Rfmts,
            const_name: &str,
            path: &[String],
            subst: &Subst,
        ) -> Rfmts {
            let full_path = rev(&cons(const_name.to_string(), path.to_vec()));
            let ty_opt = subst.get(&full_path);
            match ty_opt {
                None => rfmts,
                Some(ty) => {
                    rfmts.insert(
                        TypeConstName::new(const_name),
                        d::RefinedConst {
                            bound: d::RefinedConstBound::Exact(ty.clone()),
                            is_ctx: false,
                        },
                    );
                    rfmts
                }
            }
        }

        /// Where we have intersections we don't require that all elements of that
        /// intersection define a type constant for the purposes of projections.
        /// However, when an element _does_ define the constant we want to refine it
        /// so we have agreement. This predicate is used to check whether a given
        /// constant is defined by a given class
        fn should_refine<'a>(env: &'a Env, class_name: &str) -> Box<dyn Fn(&str) -> bool + 'a> {
            let folded_class_opt = decl_entry::to_option(typing_env::get_class(env, class_name));
            match folded_class_opt {
                None => Box::new(|_| true),
                Some(class_decl) => Box::new(move |const_name| {
                    typing_env::get_typeconst(env, &class_decl, const_name).is_some()
                }),
            }
        }

        fn root_class_name_opt(decl_ty: &DeclTy) -> Option<String> {
            match decl_ty.node_ref() {
                d::Ty_::Tapply(id_and_tys) => Some(id_and_tys.0.id_ref().as_str().to_string()),
                d::Ty_::Trefinement(tr) => root_class_name_opt(&tr.ty),
                _ => None,
            }
        }

        fn add_refinements(
            children: &s_map::T<trie::Status>,
            pred: &dyn Fn(&str) -> bool,
            path: &[String],
            subst: &Subst,
            init: Rfmts,
        ) -> Rfmts {
            // `S_map.fold`, in increasing order of the keys
            children.iter().fold(init, |rfmts, (const_name, _)| {
                if pred(const_name) {
                    add_refinement(rfmts, const_name, path, subst)
                } else {
                    rfmts
                }
            })
        }

        fn refine_ty(
            env: &Env,
            decl_ty: &DeclTy,
            subst: &Subst,
            path: &[String],
            children: &s_map::T<trie::Status>,
        ) -> DeclTy {
            if children.is_empty() {
                decl_ty.clone()
            } else {
                let reason = decl_ty.reason().clone();
                match decl_ty.node_ref() {
                    d::Ty_::Tapply(id_and_tys) => {
                        let class_name = id_and_tys.0.id_ref().as_str();
                        let pred = should_refine(env, class_name);
                        let cr_consts =
                            add_refinements(children, &*pred, path, subst, BTreeMap::new());
                        let class_refinements = d::ClassRefinement { consts: cr_consts };
                        let ty_ = d::Ty_::Trefinement(Box::new(d::TrefinementType {
                            ty: decl_ty.clone(),
                            refinement: class_refinements,
                        }));
                        DeclTy::new(reason, ty_)
                    }
                    d::Ty_::Trefinement(tr) => {
                        let inner_decl_ty = &tr.ty;
                        let cr_consts = &tr.refinement.consts;
                        let pred: Box<dyn Fn(&str) -> bool + '_> =
                            match root_class_name_opt(inner_decl_ty) {
                                None => Box::new(|_| true),
                                Some(class_name) => should_refine(env, &class_name),
                            };
                        let cr_consts =
                            add_refinements(children, &*pred, path, subst, cr_consts.clone());
                        let class_refinements = d::ClassRefinement { consts: cr_consts };
                        DeclTy::new(
                            reason,
                            d::Ty_::Trefinement(Box::new(d::TrefinementType {
                                ty: inner_decl_ty.clone(),
                                refinement: class_refinements,
                            })),
                        )
                    }
                    d::Ty_::Tunion(tys) => {
                        let tys: Vec<DeclTy> = tys
                            .iter()
                            .map(|ty| refine_ty(env, ty, subst, path, children))
                            .collect();
                        DeclTy::new(reason, d::Ty_::Tunion(tys.into()))
                    }
                    d::Ty_::Tintersection(tys) => {
                        let tys: Vec<DeclTy> = tys
                            .iter()
                            .map(|ty| refine_ty(env, ty, subst, path, children))
                            .collect();
                        DeclTy::new(reason, d::Ty_::Tintersection(tys.into()))
                    }
                    _ => decl_ty.clone(),
                }
            }
        }

        /// The environment, which the OCaml threads in the accumulator, is
        /// the first parameter.
        fn update(
            env: &mut Env,
            acc: (Subst, Generics),
            key: &str,
            typeconst: &Typeconst,
            pos: &BPos,
            children: &s_map::T<trie::Status>,
            path: &[String],
        ) -> (Subst, Generics) {
            match typeconst {
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty: tc_type }) => {
                    let (mut subst, generics) = acc;
                    subst.insert(rev(path), tc_type.clone());
                    (subst, generics)
                }
                d::Typeconst::TCAbstract(d::AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    ..
                }) => {
                    let (subst, mut generics) = acc;
                    let generic_name = typing_env::fresh_param_name(env, key);
                    let subst = {
                        let mut subst = subst;
                        let reason = R::witness_from_decl(pos.clone());
                        let ty =
                            DeclTy::new(reason, d::Ty_::Tgeneric(TypeName::new(&generic_name)));
                        subst.insert(rev(path), ty);
                        subst
                    };
                    let env: &Env = env;
                    let upper_bound = atc_as_constraint
                        .as_ref()
                        .map(|ty| refine_ty(env, ty, &subst, path, children));
                    let lower_bound = atc_super_constraint
                        .as_ref()
                        .map(|ty| refine_ty(env, ty, &subst, path, children));
                    generics.insert(
                        generic_name,
                        GenericInfo {
                            pos: pos.clone(),
                            upper_bound,
                            lower_bound,
                        },
                    );
                    (subst, generics)
                }
            }
        }

        /// In `aux`, the environment, which the OCaml threads in the
        /// accumulator, is the first parameter.
        fn this_subst(
            super::T { this_trie, .. }: &super::T,
            env: &mut Env,
            generics: Generics,
        ) -> (Subst, Generics) {
            let trie::T { base, children } = this_trie;
            fn aux(
                env: &mut Env,
                children: &s_map::T<trie::Status>,
                path: &[String],
                init: (Subst, Generics),
            ) -> (Subst, Generics) {
                // `S_map.fold`, in increasing order of the keys
                children
                    .iter()
                    .fold(init, |acc, (key, status)| match status {
                        trie::Status::Undefined => acc,
                        trie::Status::Defined(trie::T { children, base }) => match base {
                            trie::Base::Typeconst { typeconst, pos, .. } => {
                                let path = cons(key.clone(), path.to_vec());
                                let acc = aux(env, children, &path, acc);
                                update(env, acc, key, typeconst, pos, children, &path)
                            }
                            trie::Base::Root => acc,
                        },
                    })
            }
            let init = (path::Map::new(), generics);
            match base {
                trie::Base::Root => aux(env, children, &[], init),
                _ => init,
            }
        }

        // -- Build all substitutions from the analysis ---------------------------
        fn refine_this(this_ty: DeclTy, this_subst: &Subst, type_constants: &[String]) -> DeclTy {
            if type_constants.is_empty() {
                this_ty
            } else {
                let add_exact_refinements = |init: Rfmts| -> Rfmts {
                    type_constants.iter().fold(init, |mut rfmts: Rfmts, name| {
                        match this_subst.get(&vec![name.clone()]) {
                            Some(ty) => {
                                rfmts.insert(
                                    TypeConstName::new(name),
                                    d::RefinedConst {
                                        bound: d::RefinedConstBound::Exact(ty.clone()),
                                        is_ctx: false,
                                    },
                                );
                                rfmts
                            }
                            None => rfmts,
                        }
                    })
                };
                let reason = this_ty.reason().clone();
                match this_ty.node_ref() {
                    d::Ty_::Tapply(_) => {
                        let cr_consts = add_exact_refinements(BTreeMap::new());
                        let class_refinement = d::ClassRefinement { consts: cr_consts };
                        DeclTy::new(
                            reason,
                            d::Ty_::Trefinement(Box::new(d::TrefinementType {
                                ty: this_ty.clone(),
                                refinement: class_refinement,
                            })),
                        )
                    }
                    d::Ty_::Trefinement(tr) => {
                        let this_ty = &tr.ty;
                        let cr_consts = add_exact_refinements(tr.refinement.consts.clone());
                        let class_refinement = d::ClassRefinement { consts: cr_consts };
                        DeclTy::new(
                            reason,
                            d::Ty_::Trefinement(Box::new(d::TrefinementType {
                                ty: this_ty.clone(),
                                refinement: class_refinement,
                            })),
                        )
                    }
                    _ => this_ty.clone(),
                }
            }
        }

        fn mk_tparams(generics: &Generics, env: &Env) -> Vec<DeclTparam> {
            generics
                .iter()
                .map(
                    |(
                        name,
                        GenericInfo {
                            pos,
                            upper_bound,
                            lower_bound,
                        },
                    )| {
                        // We're generating a decl type so we need to add implicit
                        // upper bounds of [supportdyn<mixed>] under sdt or [mixed] otherwise
                        let tp_constraints: Vec<(ConstraintKind, DeclTy)> = {
                            let reason = R::witness_from_decl(pos.clone());
                            let ub = {
                                let tcopt = &env.genv.tcopt;
                                // `Typechecker_options.everything_sdt tcopt`
                                if tcopt.po.everything_sdt {
                                    (
                                        ConstraintKind::ConstraintAs,
                                        decl_enforceability::supportdyn_mixed(pos, &reason),
                                    )
                                } else {
                                    (
                                        ConstraintKind::ConstraintAs,
                                        DeclTy::new(reason, d::Ty_::Tmixed),
                                    )
                                }
                            };
                            [
                                upper_bound
                                    .clone()
                                    .map(|ty| (ConstraintKind::ConstraintAs, ty)),
                                lower_bound
                                    .clone()
                                    .map(|ty| (ConstraintKind::ConstraintSuper, ty)),
                                Some(ub),
                            ]
                            .into_iter()
                            .flatten()
                            .collect()
                        };
                        crate::typing_extract_method::mk_tparam(pos.clone(), name, tp_constraints)
                    },
                )
                .collect()
        }

        pub fn of_typeconst_analysis(
            analysis: &super::T,
            this_name: String,
            this_ty: DeclTy,
            env: &mut Env,
        ) -> T {
            let (this_subst, class_subst, generics) = {
                let generics = s_map::T::new();
                let (this_subst, generics) = this_subst(analysis, env, generics);
                let (class_subst, generics) = class_subst(analysis, env, generics);
                (this_subst, class_subst, generics)
            };
            let tparams = mk_tparams(&generics, env);
            let subst = T {
                this_name,
                this_ty: this_ty.clone(),
                this_subst,
                class_subst,
                tparams,
            };
            // Apply refinements to [this] to ensure it lines up with any abstract constants
            let this_ty = refine_this(this_ty, &subst.this_subst, &this_constants(analysis));
            T { this_ty, ..subst }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::typing_extract_method::tests::access;
        use crate::typing_extract_method::tests::fun_ty;
        use crate::typing_extract_method::tests::generic;
        use crate::typing_extract_method::tests::int;
        use crate::typing_extract_method::tests::r;
        use crate::typing_extract_method::tests::this;
        use crate::typing_extract_method::tests::void;

        fn names(path: &[Const]) -> Vec<String> {
            path.iter()
                .map(|c| c.id_ref().as_str().to_string())
                .collect()
        }

        fn konst(name: &str) -> Const {
            Positioned::new(BPos::none(), TypeConstName::new(name))
        }

        fn concrete(ty: DeclTy) -> Typeconst {
            d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty })
        }

        #[test]
        fn access_path_lists_the_constants_from_the_root() {
            let ty = access(access(this(), "A"), "B");
            let (root, path) = access_path(&ty, vec![]);
            assert!(matches!(root.node_ref(), d::Ty_::Tthis));
            assert_eq!(names(&path), vec!["A", "B"]);
        }

        #[test]
        fn this_to_absolute_roots_this_at_the_prefix() {
            // The prefix is consed as the path is followed: `[B; A]` is `this::A::B`
            let prefix = vec![konst("B"), konst("A")];
            let ty = this_to_absolute(DeclTy::new(r(), d::Ty_::Toption(this())), &prefix);
            let inner = match ty.node_ref() {
                d::Ty_::Toption(inner) => inner.clone(),
                ty_ => panic!("not an option: {:?}", ty_),
            };
            let (root, path) = access_path(&inner, vec![]);
            assert!(matches!(root.node_ref(), d::Ty_::Tthis));
            assert_eq!(names(&path), vec!["A", "B"]);
        }

        #[test]
        fn replace_this_with_replaces_every_this() {
            let ty = DeclTy::new(r(), d::Ty_::Tunion([this(), access(this(), "T")].into()));
            let ty = replace_this_with(ty, &int());
            match ty.node_ref() {
                d::Ty_::Tunion(tys) => {
                    assert!(matches!(tys[0].node_ref(), d::Ty_::Tprim(_)));
                    let (root, _) = access_path(&tys[1], vec![]);
                    assert!(matches!(root.node_ref(), d::Ty_::Tprim(_)));
                }
                ty_ => panic!("not a union: {:?}", ty_),
            }
        }

        #[test]
        fn accumulate_tys_conses_the_bounds() {
            let tc = d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: Some(generic("U")),
                super_constraint: Some(generic("L")),
                default: None,
            });
            let tys = accumulate_tys(&tc, vec![generic("X")]);
            assert_eq!(tys.len(), 3);
            assert!(tys[0].node_ref() == generic("U").node_ref());
            assert!(tys[1].node_ref() == generic("L").node_ref());
            assert!(tys[2].node_ref() == generic("X").node_ref());
            let tys = accumulate_tys(&concrete(int()), vec![]);
            assert_eq!(tys.len(), 1);
        }

        #[test]
        fn meet_typeconst_of_concrete_and_bounded_abstract() {
            let abs = d::Typeconst::TCAbstract(d::AbstractTypeconst {
                as_constraint: Some(generic("U")),
                super_constraint: Some(generic("L")),
                default: None,
            });
            // union [lb; intersection [tc_type; ub]]
            match meet_typeconst(&r(), &abs, &concrete(int())) {
                d::Typeconst::TCConcrete(d::ConcreteTypeconst { ty }) => match ty.node_ref() {
                    d::Ty_::Tunion(tys) => {
                        assert_eq!(tys.len(), 2);
                        assert!(tys[0].node_ref() == generic("L").node_ref());
                        assert!(matches!(tys[1].node_ref(), d::Ty_::Tintersection(_)));
                    }
                    ty_ => panic!("not a union: {:?}", ty_),
                },
                tc => panic!("not concrete: {:?}", tc),
            }
        }

        #[test]
        fn trie_merge_prefers_defined_children() {
            let defined = trie::status_of_typeconst(None, concrete(int()), BPos::none());
            let t1 = trie::update(trie::empty(), "A", trie::Status::Undefined);
            let t2 = trie::update(
                trie::update(trie::empty(), "A", defined),
                "B",
                trie::Status::Undefined,
            );
            let t = trie::merge(&t1, &t2);
            assert_eq!(trie::constants(&t), vec!["A", "B"]);
            assert!(matches!(
                t.children.get("A"),
                Some(trie::Status::Defined(_))
            ));
            assert!(matches!(t.children.get("B"), Some(trie::Status::Undefined)));
            assert!(matches!(
                trie::find_path(&t, &[konst("A")]),
                Some(trie::Status::Defined(_))
            ));
            assert!(matches!(
                trie::find_path(&t, &[konst("B"), konst("C")]),
                Some(trie::Status::Undefined)
            ));
            assert!(trie::find_path(&t, &[konst("C")]).is_none());
        }

        #[test]
        fn paths_of_ty_are_in_the_order_of_the_ocaml_list() {
            // `paths := p :: !paths`: the last access found comes first
            let ft = fun_ty(
                vec![],
                vec![access(this(), "A"), access(this(), "B")],
                void(),
            );
            let ty = DeclTy::new(r(), d::Ty_::Tfun(Box::new(ft)));
            let paths: Vec<Vec<String>> = paths_of_ty(&ty)
                .iter()
                .map(|p| match p {
                    Path::This(path) => names(path),
                    Path::Class(..) => panic!("not rooted in this"),
                })
                .collect();
            assert_eq!(paths, vec![vec!["B"], vec!["A"]]);
        }
    }

    pub fn to_subst(t: &T, this_ty: DeclTy, env: &mut Env) -> subst::T {
        let T { this_name, .. } = t;
        subst::of_typeconst_analysis(t, this_name.clone(), this_ty, env)
    }
}

// -- Helpers ---------------------------------------------------------------
fn ty_generics(names: s_set::T, ty: &DeclTy) -> s_set::T {
    let acc = RefCell::new(names);
    let on_ty = |decl_ty: DeclTy, ctx: &()| match decl_ty.node_ref() {
        d::Ty_::Tgeneric(nm) => {
            acc.borrow_mut().insert(nm.as_str().to_string());
            (*ctx, TransformTopDown::Stop(decl_ty))
        }
        _ => (*ctx, TransformTopDown::Continue(decl_ty)),
    };
    let _ = transform_top_down_decl_ty(ty.clone(), &on_ty, &continue_rc_bound::<()>, &());
    acc.into_inner()
}

/// Returns the positions of the explicit parameters from which a value of type
/// [this] can be obtained (i.e. [this] occurs contravariantly or invariantly in
/// the parameter type), but only when the function pointer would actually be able
/// to relate two unrelated subtypes of [this] — the binary method problem.
///
/// A single obtainable occurrence can be soundly abstracted into one type
/// parameter during extraction. Two or more lets the caller obtain two values of
/// type [this] whose runtime classes can differ, which the underlying method
/// conflates as a single self type — the binary method problem. Invariance on a
/// container pins its element *type*, not the runtime class of its contents (a
/// [Box<B>] may hold any subtype of [B]), so invariant occurrences are obtainable
/// too.
///
/// For instance methods the implicit [this] receiver is itself an obtainable
/// occurrence, so [~has_implicit_this:true] should be passed; in that case a
/// single obtainable explicit occurrence is enough to trigger the error.
///
/// Covariant occurrences (e.g. a parameter of type [(function(this): void)],
/// which only *accepts* a [this]) and [this::T] type constant projections are
/// never counted.
pub fn explicit_this_param_positions(
    has_implicit_this: Option<bool>,
    class_tparams: Option<&[DeclTparam]>,
    env: &Env,
    fun_ty: &DeclFunType,
) -> Vec<PosOrDecl> {
    let has_implicit_this = has_implicit_this.unwrap_or(false);
    let class_tparams = class_tparams.unwrap_or(&[]);
    let upper_bounds = if !has_implicit_this {
        s_map::T::new()
    } else {
        let tparams: Vec<DeclTparam> = class_tparams
            .iter()
            .chain(fun_ty.tparams.iter())
            .cloned()
            .collect();
        type_parameter_upper_bounds(s_map::T::new(), &tparams, &fun_ty.where_constraints)
    };
    let init = if has_implicit_this { 1 } else { 0 };
    // `positions` is consed in the OCaml and reversed at the end: here it is
    // pushed to, in the order of the parameters
    let (total, positions) = fun_ty.params.iter().fold(
        (init, vec![]),
        |(total, mut positions): (isize, Vec<PosOrDecl>), fp| {
            match variance_analysis::count_obtainable_this_in_param(
                has_implicit_this,
                &upper_bounds,
                &fp.ty,
                env,
            ) {
                0 => (total, positions),
                n => {
                    positions.push(PosOrDecl::from(fp.pos.clone()));
                    (total + n, positions)
                }
            }
        },
    );
    if total >= 2 { positions } else { vec![] }
}

fn drop_unused_generics(fun_ty: DeclFunType, names: &s_set::T) -> DeclFunType {
    // First find any generics mentioned in parameters or in the return type
    let names = {
        let names = ty_generics(names.clone(), &fun_ty.ret);
        let names = match &fun_ty.implicit_params.capability {
            d::Capability::CapTy(ty) => ty_generics(names, ty),
            d::Capability::CapDefaults(_) => names,
        };
        let names = fun_ty
            .params
            .iter()
            .fold(names, |names, ft_param| ty_generics(names, &ft_param.ty));
        // We have to include where constraints to cover legacy projection from
        // generics
        fun_ty
            .where_constraints
            .iter()
            .fold(names, |names, d::WhereConstraint(ty1, _, ty2)| {
                ty_generics(ty_generics(names, ty1), ty2)
            })
    };
    // `S_map.of_list`: a later binding of a name replaces an earlier one.
    let dependencies: s_map::T<s_set::T> = fun_ty
        .tparams
        .iter()
        .map(|tp| {
            let name = tp.name.id_ref().as_str();
            let dependencies = tp
                .constraints
                .iter()
                .fold(s_set::T::new(), |dependencies, (_, ty)| {
                    ty_generics(dependencies, ty)
                });
            (name.to_string(), dependencies.without(name))
        })
        .collect();
    // `let rec close used pending = ...`: `pending` is a list, head first.
    let names = {
        let mut used = s_set::T::new();
        let mut pending: Vec<String> = names.iter().cloned().collect();
        pending.reverse();
        // (The head of the list is the last element of the vector.)
        while let Some(name) = pending.pop() {
            if used.contains(&name) {
                continue;
            }
            used.insert(name.clone());
            match dependencies.get(&name) {
                None => {}
                Some(dependencies) => {
                    // `List.rev_append (S_set.elements dependencies) pending`:
                    // the last element comes first.
                    for dependency in dependencies.iter() {
                        pending.push(dependency.clone())
                    }
                }
            }
        }
        used
    };
    let ft_tparams: Vec<DeclTparam> = fun_ty
        .tparams
        .iter()
        .filter(|tp| names.contains(tp.name.id_ref().as_str()))
        .cloned()
        .collect();
    DeclFunType {
        tparams: ft_tparams.into(),
        ..fun_ty
    }
}

/// Find a nice name for a generic corresponding to [this] for polymorphic
/// function pointers
fn gen_this_name(ft_tparams: &[DeclTparam]) -> String {
    let names: s_set::T = ft_tparams.iter().map(tparam_name).collect();
    let base = "Tthis";
    fn aux(names: &s_set::T, base: &str, n_opt: Option<isize>) -> String {
        let name = match n_opt {
            None => base.to_string(),
            // `Format.sprintf "%s#%n" base n`
            Some(n) => format!("{}#{}", base, n),
        };
        if names.contains(&name) {
            aux(
                names,
                base,
                match n_opt {
                    None => Some(0),
                    Some(n) => Some(n + 1),
                },
            )
        } else {
            name
        }
    }
    aux(&names, base, None)
}

fn apply_subst_generic(fun_ty: DeclFunType, subst: &s_map::T<DeclTy>) -> DeclFunType {
    let names: s_set::T = subst.keys().cloned().collect();
    let dependencies: s_map::T<s_set::T> = subst
        .iter()
        .map(|(name, ty)| {
            // `S_set.inter names (ty_generics S_set.empty ty)`
            let generics = ty_generics(s_set::T::new(), ty);
            (name.clone(), names.clone().intersection(generics))
        })
        .collect();
    let is_recursive = |name: &String| -> bool {
        // `let rec visit seen = function ...`: the list, head first.
        let mut seen = s_set::T::new();
        let mut pending: VecDeque<String> = dependencies[name].iter().cloned().collect();
        loop {
            match pending.pop_front() {
                None => return false,
                Some(next) if *name == next => return true,
                Some(next) if seen.contains(&next) => {}
                Some(next) => {
                    seen.insert(next.clone());
                    // `S_set.elements next_dependencies @ rest`
                    let next_dependencies = &dependencies[&next];
                    for dependency in next_dependencies.iter().rev() {
                        pending.push_front(dependency.clone())
                    }
                }
            }
        }
    };
    let subst: s_map::T<DeclTy> = subst
        .iter()
        .filter(|(name, _)| !is_recursive(name))
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect();
    let subst = &subst;
    let on_ty = |ty: DeclTy, ctx: &()| match ty.node_ref() {
        d::Ty_::Tgeneric(nm) => match subst.get(nm.as_str()) {
            Some(ty) => {
                // Since other type parameters can appear inside bounds of type parameters
                // we restart the transform after making a substitution
                (*ctx, TransformTopDown::Restart(ty.clone()))
            }
            None => (*ctx, TransformTopDown::Stop(ty)),
        },
        _ => (*ctx, TransformTopDown::Continue(ty)),
    };
    let ty = DeclTy::new(R::none(), d::Ty_::Tfun(Box::new(fun_ty)));
    let ty = transform_top_down_decl_ty(ty, &on_ty, &continue_rc_bound::<()>, &());
    match ty.node_ref() {
        d::Ty_::Tfun(fun_ty) => (**fun_ty).clone(),
        _ => panic!("Expected function type"),
    }
}

// -- API -------------------------------------------------------------------
fn extract_method(
    fun_ty: DeclFunType,
    class_name: &PosId,
    folded_class: &folded_class::T,
    env: &mut Env,
) -> DeclFunType {
    // `fst class_name`, as the position of a decl type
    let class_pos = BPos::from(class_name.0.clone());
    // We will need to handle substitution of [this] differently depending on
    // the variance of its appearance in the function type:
    // - If occurs co- or contravariantly we can substitute it with the the
    //   class itself or introduce a new type parameter with a lower or upper bound
    //   respectively. We prefer the former since instantiated types can take
    //   advantage of bidirectional typing
    // - If it occurs invariantly we want to introduce a new type parameter so
    //   that function pointers are polymorphic in the type of [this] unless
    //   the class is final. In this case we can substitute [this] with the class
    let this_variance = if folded_class::final_(folded_class) {
        // There is no point being polymorphic in [this] if it corresponds to a
        // final class
        None
    } else {
        variance_analysis::analyse_this(&fun_ty, env)
    };

    // Record the list of type parameter appearing in the original function type;
    // we need this since even though a parameter may be unused it may have
    // reify directives which should be preserved
    let original_tparam_names: s_set::T = {
        let names: Vec<String> = fun_ty.tparams.iter().map(tparam_name).collect();
        names.into_iter().collect()
    };

    // Get the class level generics; we need this to build a type for [this] and
    // to add to the function generics. We can set any reified type parameters to
    // be erased here since the requirement is met when the class is instantiated
    // and no longer necessary on type parameters in the function pointer
    let class_tparams: Vec<DeclTparam> = folded_class::tparams(folded_class)
        .into_iter()
        .map(|tp| d::Tparam {
            reified: ReifyKind::Erased,
            ..tp
        })
        .collect();

    // Build the type corresponding to [this] or its upper bound
    let this_ty = DeclTy::new(
        R::witness_from_decl(class_pos.clone()),
        d::Ty_::Tapply(Box::new((
            Positioned::new(class_pos.clone(), TypeName::new(&class_name.1)),
            class_tparams
                .iter()
                .map(|tp| {
                    DeclTy::new(
                        R::witness_from_decl(tp.name.pos().clone()),
                        d::Ty_::Tgeneric(tp.name.id()),
                    )
                })
                .collect(),
        ))),
    );

    // Analyse the function type to determine which type constants have to
    // be quantified over and the definition of concrete type constants
    let analysis = typeconst_analysis::of_fun_type(&fun_ty, &class_name.1, folded_class, env);

    // Generate the type parameters corresponding to abstract type constants, a
    // substitution from to be applied to [Taccess] types and a refined version
    // of [this] with equalities to generics standing in for abstract type
    // constants
    let subst = typeconst_analysis::to_subst(&analysis, this_ty.clone(), env);

    // Add class-level generics, the generics for [this] and any generics
    // for abstract type constants; some of these may end up not being used
    // but we will clear that up later
    let fun_ty = {
        let tparams = &subst.tparams;
        let ft_tparams: Vec<DeclTparam> = class_tparams
            .into_iter()
            .chain(tparams.iter().cloned())
            .chain(fun_ty.tparams.iter().cloned())
            .collect();
        DeclFunType {
            tparams: ft_tparams.into(),
            ..fun_ty
        }
    };

    // At this point the 'this_ty' in the substitution is refined but may still
    // contain occurrences of [this]. Depending on the variance of this in the
    // function type we need to replace this with the generic it will be the
    // upper bound of (invariant case) or the unrefined version of 'this_ty'.
    // In the former case, we need to add the type parameter to function type
    let (fun_ty, subst) = match this_variance {
        Some(Variance::Invariant) => {
            let refined_this_ty = subst.this_ty.clone();
            let this_generic_name = gen_this_name(&fun_ty.tparams);
            let this_generic_ty = DeclTy::new(
                R::witness_from_decl(class_pos.clone()),
                d::Ty_::Tgeneric(TypeName::new(&this_generic_name)),
            );
            let subst = typeconst_analysis::subst::T {
                this_ty: this_generic_ty,
                ..subst
            };
            // Replace occurrences of this in the upperbound with the generic
            let this_ty_upper_bound = typeconst_analysis::subst::apply(&subst, refined_this_ty);
            // Add the generic to the function type
            let this_tparam = mk_tparam(
                class_pos.clone(),
                &this_generic_name,
                vec![(ConstraintKind::ConstraintAs, this_ty_upper_bound)],
            );
            let ft_tparams: Vec<DeclTparam> = std::iter::once(this_tparam)
                .chain(fun_ty.tparams.iter().cloned())
                .collect();
            (
                DeclFunType {
                    tparams: ft_tparams.into(),
                    ..fun_ty
                },
                subst,
            )
        }
        _ => {
            let refined_this_ty = subst.this_ty.clone();
            // `this_ty` is the unrefined type of the class built above
            let this_ty = typeconst_analysis::subst::apply(
                &typeconst_analysis::subst::T {
                    this_ty,
                    ..subst.clone()
                },
                refined_this_ty,
            );
            let subst = typeconst_analysis::subst::T { this_ty, ..subst };
            (fun_ty, subst)
        }
    };

    // Apply a subsitution replacing
    // - [Tthis] with either a type parameter or the refined class
    // - any concrete [Taccess] with its definition (except where its definition is abstract...)
    // - any abstract [Taccess] with the corresponding generic
    let fun_ty = typeconst_analysis::subst::apply_fun_ty(&subst, fun_ty);

    // Next, analyse the variance of the remaining generics; if any occur
    // only co- or contravariantly in the function type we can avoid quantifying
    // over them by substituting for their lower- or upper-bound respectively
    let fun_ty = {
        let ft_tparams = &fun_ty.tparams;
        let ty_param_names: s_set::T = ft_tparams.iter().map(tparam_name).collect();
        let ty_param_bounds: s_map::T<(BPos, Vec<(ConstraintKind, DeclTy)>)> = s_map::of_list(
            ft_tparams
                .iter()
                .map(|tp| {
                    (
                        tparam_name(tp),
                        (tp.name.pos().clone(), tp.constraints.to_vec()),
                    )
                })
                .collect(),
        );
        let variances = variance_analysis::analyse_ty_params(&fun_ty, &ty_param_names, env);
        let subst: s_map::T<DeclTy> = variances
            .iter()
            .filter_map(|(name, variance_opt)| {
                let ty_opt = match variance_opt {
                    None | Some(Variance::Invariant) => None,
                    Some(Variance::Contravariant) => {
                        let (pos, constraints) = match ty_param_bounds.get(name) {
                            Some(bounds) => bounds,
                            None => panic!("Not_found"),
                        };
                        let ubs: Vec<DeclTy> = constraints
                            .iter()
                            .filter_map(|(c, ty)| match c {
                                ConstraintKind::ConstraintAs | ConstraintKind::ConstraintEq => {
                                    Some(ty.clone())
                                }
                                _ => None,
                            })
                            .collect();
                        let reason = R::witness_from_decl(pos.clone());
                        let ub = decl_intersection(reason, ubs);
                        Some(ub)
                    }
                    Some(Variance::Covariant) => {
                        let (pos, constraints) = match ty_param_bounds.get(name) {
                            Some(bounds) => bounds,
                            None => panic!("Not_found"),
                        };
                        let lbs: Vec<DeclTy> = constraints
                            .iter()
                            .filter_map(|(c, ty)| match c {
                                ConstraintKind::ConstraintSuper | ConstraintKind::ConstraintEq => {
                                    Some(ty.clone())
                                }
                                _ => None,
                            })
                            .collect();
                        let reason = R::witness_from_decl(pos.clone());
                        let lb = decl_union(reason, lbs);
                        Some(lb)
                    }
                };
                ty_opt.map(|ty| (name.clone(), ty))
            })
            .collect();
        apply_subst_generic(fun_ty, &subst)
    };

    // We may have introduced some unused generics; check which ones appear
    // in parameters, implicit parameters or the return type and then find the
    // transitive closure. Any generics not in this set can be dropped.
    // Note: the original set of generic is used as the starting point since
    // we need to keep the original type params if they are marked as reify
    drop_unused_generics(fun_ty, &original_tparam_names)
}

pub fn extract_instance_method(
    fun_ty: DeclFunType,
    class_name: &PosId,
    folded_class: &folded_class::T,
    env: &mut Env,
) -> DeclFunType {
    // `fst class_name`, as the position of a decl type
    let class_pos = BPos::from(class_name.0.clone());
    let self_param = {
        let fp_flags = {
            // `Typing_defs_core.Flags.get_ft_readonly_this fun_ty`
            let readonly_this = typing_defs_flags::fun::readonly_this(fun_ty.flags);
            typing_defs_flags::fun_param::set_readonly(
                readonly_this,
                typing_defs_flags::fun_param::default(),
            )
        };
        d::FunParam {
            pos: class_pos.clone(),
            ty: DeclTy::new(R::witness_from_decl(class_pos.clone()), d::Ty_::Tthis),
            name: None,
            def_value: None,
            flags: fp_flags,
        }
    };
    let fun_ty = {
        let ft_params: Vec<d::FunParam<R, DeclTy>> = std::iter::once(self_param)
            .chain(fun_ty.params.iter().cloned())
            .collect();
        DeclFunType {
            params: ft_params.into(),
            ..fun_ty
        }
    };
    extract_method(fun_ty, class_name, folded_class, env)
}

pub fn extract_static_method(
    fun_ty: DeclFunType,
    class_name: &PosId,
    folded_class: &folded_class::T,
    env: &mut Env,
) -> DeclFunType {
    let fun_ty = extract_instance_method(fun_ty, class_name, folded_class, env);
    let ft_params: Vec<d::FunParam<R, DeclTy>> = match fun_ty.params.split_first() {
        Some((_, ft_params)) => ft_params.to_vec(),
        None => panic!("Expected at least one parameter"),
    };
    let fun_ty = DeclFunType {
        params: ft_params.into(),
        ..fun_ty
    };
    // In generic methods we don't need to retain unused class-level generics even
    // if they are marked [reify]
    drop_unused_generics(fun_ty, &s_set::T::new())
}

#[cfg(test)]
mod tests {
    use oxidized::aast_defs::Tprim;
    use oxidized::typing_defs_flags::FunParamFlags;
    use oxidized::typing_defs_flags::FunTypeFlags;

    use super::*;

    pub(crate) fn r() -> R {
        R::none()
    }

    pub(crate) fn generic(n: &str) -> DeclTy {
        DeclTy::new(r(), d::Ty_::Tgeneric(TypeName::new(n)))
    }

    pub(crate) fn int() -> DeclTy {
        DeclTy::new(r(), d::Ty_::Tprim(Tprim::Tint))
    }

    pub(crate) fn void() -> DeclTy {
        DeclTy::new(r(), d::Ty_::Tprim(Tprim::Tvoid))
    }

    pub(crate) fn this() -> DeclTy {
        DeclTy::new(r(), d::Ty_::Tthis)
    }

    pub(crate) fn access(root: DeclTy, name: &str) -> DeclTy {
        DeclTy::new(
            r(),
            d::Ty_::Taccess(Box::new(d::TaccessType {
                ty: root,
                type_const: Positioned::new(BPos::none(), TypeConstName::new(name)),
            })),
        )
    }

    pub(crate) fn tparam(name: &str, constraints: Vec<(ConstraintKind, DeclTy)>) -> DeclTparam {
        mk_tparam(BPos::none(), name, constraints)
    }

    pub(crate) fn fun_ty(
        tparams: Vec<DeclTparam>,
        params: Vec<DeclTy>,
        ret: DeclTy,
    ) -> DeclFunType {
        d::FunType {
            tparams: tparams.into(),
            where_constraints: [].into(),
            params: params
                .into_iter()
                .map(|ty| d::FunParam {
                    pos: BPos::none(),
                    name: None,
                    ty,
                    flags: FunParamFlags::empty(),
                    def_value: None,
                })
                .collect(),
            implicit_params: d::FunImplicitParams {
                capability: d::Capability::CapDefaults(BPos::none()),
            },
            ret,
            flags: FunTypeFlags::empty(),
            instantiated: false,
        }
    }

    fn names(tparams: &[DeclTparam]) -> Vec<String> {
        tparams.iter().map(tparam_name).collect()
    }

    fn is_generic(ty: &DeclTy, name: &str) -> bool {
        matches!(ty.node_ref(), d::Ty_::Tgeneric(n) if n.as_str() == name)
    }

    #[test]
    fn gen_this_name_avoids_the_names_of_the_tparams() {
        assert_eq!(gen_this_name(&[]), "Tthis");
        assert_eq!(gen_this_name(&[tparam("T", vec![])]), "Tthis");
        assert_eq!(gen_this_name(&[tparam("Tthis", vec![])]), "Tthis#0");
        assert_eq!(
            gen_this_name(&[tparam("Tthis#0", vec![]), tparam("Tthis", vec![])]),
            "Tthis#1"
        );
    }

    #[test]
    fn drop_unused_generics_keeps_generics_used_transitively() {
        // function<T, U as T, V, W super V>(U): void
        let ft = fun_ty(
            vec![
                tparam("T", vec![]),
                tparam("U", vec![(ConstraintKind::ConstraintAs, generic("T"))]),
                tparam("V", vec![]),
                tparam("W", vec![(ConstraintKind::ConstraintSuper, generic("V"))]),
            ],
            vec![generic("U")],
            void(),
        );
        let ft = drop_unused_generics(ft, &s_set::T::new());
        assert_eq!(names(&ft.tparams), vec!["T", "U"]);
    }

    #[test]
    fn drop_unused_generics_keeps_the_given_names() {
        let ft = fun_ty(
            vec![tparam("T", vec![]), tparam("V", vec![])],
            vec![],
            void(),
        );
        let keep: s_set::T = ["V".to_string()].into_iter().collect();
        let ft = drop_unused_generics(ft, &keep);
        assert_eq!(names(&ft.tparams), vec!["V"]);
    }

    #[test]
    fn drop_unused_generics_terminates_on_a_self_bounded_generic() {
        // function<T as T>(T): void
        let ft = fun_ty(
            vec![tparam(
                "T",
                vec![(ConstraintKind::ConstraintAs, generic("T"))],
            )],
            vec![generic("T")],
            void(),
        );
        let ft = drop_unused_generics(ft, &s_set::T::new());
        assert_eq!(names(&ft.tparams), vec!["T"]);
    }

    #[test]
    fn apply_subst_generic_restarts_after_a_substitution() {
        // T := ?U, U := int on (T, V): U
        let subst: s_map::T<DeclTy> = [
            (
                "T".to_string(),
                DeclTy::new(r(), d::Ty_::Toption(generic("U"))),
            ),
            ("U".to_string(), int()),
        ]
        .into_iter()
        .collect();
        let ft = apply_subst_generic(
            fun_ty(vec![], vec![generic("T"), generic("V")], generic("U")),
            &subst,
        );
        match ft.params[0].ty.node_ref() {
            d::Ty_::Toption(ty) => assert!(matches!(ty.node_ref(), d::Ty_::Tprim(Tprim::Tint))),
            ty_ => panic!("not an option: {:?}", ty_),
        }
        assert!(is_generic(&ft.params[1].ty, "V"));
        assert!(matches!(ft.ret.node_ref(), d::Ty_::Tprim(Tprim::Tint)));
    }

    #[test]
    fn ty_generics_adds_to_the_given_names() {
        let ty = DeclTy::new(
            r(),
            d::Ty_::TvecOrDict(Box::new((generic("K"), generic("V")))),
        );
        let names = ty_generics(["T".to_string()].into_iter().collect(), &ty);
        let names: Vec<String> = names.into_iter().collect();
        assert_eq!(names, vec!["K", "T", "V"]);
    }

    #[test]
    fn decl_make_type_helpers() {
        assert!(matches!(
            decl_union(r(), vec![]).node_ref(),
            d::Ty_::Tunion(tys) if tys.is_empty()
        ));
        assert!(matches!(
            decl_union(r(), vec![int()]).node_ref(),
            d::Ty_::Tprim(Tprim::Tint)
        ));
        match decl_intersection(r(), vec![]).node_ref() {
            d::Ty_::Toption(ty) => assert!(matches!(ty.node_ref(), d::Ty_::Tnonnull)),
            ty_ => panic!("not mixed: {:?}", ty_),
        }
        assert!(matches!(
            decl_intersection(r(), vec![int(), generic("T")]).node_ref(),
            d::Ty_::Tintersection(tys) if tys.len() == 2
        ));
    }
}
