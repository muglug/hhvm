// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_solver_utils.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;

/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::tvid;
use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::ty_equal;
/// `module Env = Typing_env`
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error_utils;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

pub fn filter_locl_types(types: &ity_set::T) -> ty_set::T {
    let mut res = ty_set::empty();
    for ty in types.iter() {
        match ty {
            InternalType::LoclType(ty) => res = ty_set::add(ty.clone(), &res),
            _ => {}
        }
    }
    res
}

/// If a type variable appear in one of its own lower bounds under a combination
/// of unions and intersections, it can be simplified away from this lower bound by
/// replacing any of its occurrences with nothing.
/// E.g.
/// - if #1 has lower bound (#1 | A), the lower bound can be simplified to
///   (nothing | A) = A.
/// - if #1 has lower bound (#1 & A), the lower bound can be simplified to
///   (nothing & A) = nothing.
pub fn remove_tyvar_from_lower_bound(
    env: &mut Env,
    var: tvid::T,
    lower_bound: InternalType,
) -> InternalType {
    fn is_nothing(ty: &Ty) -> bool {
        ty_equal(None, &make_type::nothing(typing_reason::none()), ty)
    }
    fn remove(env: &mut Env, var: tvid::T, ty: Ty) -> Ty {
        let ty = typing_env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tvar(v) if tvid::equal(*v, var) => make_type::nothing(typing_reason::none()),
            Ty_::Toption(ty_) => {
                let r = get_reason(&ty).clone();
                let ty = remove(env, var, ty_.clone());
                make_type::nullable(r, ty)
            }
            Ty_::Tunion(tyl) => {
                let r = get_reason(&ty).clone();
                let tyl: Vec<Ty> = tyl.iter().map(|ty| remove(env, var, ty.clone())).collect();
                let tyl = tyl.into_iter().filter(|ty| !is_nothing(ty)).collect();
                make_type::union(r, tyl)
            }
            Ty_::Tintersection(tyl) => {
                let r = get_reason(&ty).clone();
                let tyl: Vec<Ty> = tyl.iter().map(|ty| remove(env, var, ty.clone())).collect();
                if tyl.iter().any(is_nothing) {
                    make_type::nothing(r)
                } else {
                    make_type::intersection(r, tyl)
                }
            }
            Ty_::Tnewtype(name, tyargs, _)
                if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN =>
            {
                let r = get_reason(&ty).clone();
                let ty = remove(env, var, tyargs[0].clone());
                if is_nothing(&ty) {
                    make_type::nothing(r)
                } else {
                    make_type::supportdyn(r, ty)
                }
            }
            _ => ty.clone(),
        }
    }
    fn remove_i(env: &mut Env, var: tvid::T, ty: InternalType) -> InternalType {
        match ty {
            InternalType::LoclType(ty) => {
                let ty = remove(env, var, ty);
                InternalType::LoclType(ty)
            }
            _ => ty,
        }
    }
    remove_i(env, var, lower_bound)
}

/// A bound that `remove_tyvar_from_lower_bound` and
/// `remove_tyvar_from_upper_bound` give back as it is (the same type, and no
/// write to the environment): not a type variable (which `expand_type` may
/// change), an option, a union, an intersection or `supportdyn<_>` (which
/// they rebuild). Not in the OCaml (see [`remove_tyvar_from_lower_bounds`]).
fn remove_tyvar_keeps_bound(bound: &InternalType) -> bool {
    match bound {
        InternalType::ConstraintType(_) => true,
        InternalType::LoclType(ty) => match get_node(ty) {
            Ty_::Tvar(_) | Ty_::Toption(_) | Ty_::Tunion(_) | Ty_::Tintersection(_) => false,
            Ty_::Tnewtype(name, tyargs, _) => !(tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN),
            _ => true,
        },
    }
}

pub fn remove_tyvar_from_lower_bounds(
    env: &mut Env,
    var: tvid::T,
    lower_bounds: &ity_set::T,
) -> ity_set::T {
    remove_tyvar_from_lower_bounds_opt(env, var, lower_bounds).unwrap_or_else(|| lower_bounds.clone())
}

/// [`remove_tyvar_from_lower_bounds`], `None` when the result has the same
/// elements as `lower_bounds`.
fn remove_tyvar_from_lower_bounds_opt(
    env: &mut Env,
    var: tvid::T,
    lower_bounds: &ity_set::T,
) -> Option<ity_set::T> {
    // Not in the OCaml, which rebuilds the set: when `remove` gives every
    // bound back as it is and the filter below keeps them all, the result
    // has the same elements (the same types) as `lower_bounds`.
    if lower_bounds.iter().all(remove_tyvar_keeps_bound) {
        let env: &Env = env;
        if !lower_bounds.iter().any(|ty| t_utils::is_nothing_i(env, ty)) {
            return None;
        }
    }
    let mut acc = ity_set::empty();
    for lower_bound in lower_bounds.iter() {
        let lower_bound = remove_tyvar_from_lower_bound(env, var, lower_bound.clone());
        acc = ity_set::add(lower_bound, &acc);
    }
    let lower_bounds = acc;
    let env: &Env = env;
    let is_not_nothing = |ty: &InternalType| !t_utils::is_nothing_i(env, ty);
    Some(ity_set::filter(is_not_nothing, &lower_bounds))
}

/// If a type variable appear in one of its own upper bounds under a combination
/// of unions and intersections, it can be simplified away from this upper bound by
/// replacing any of its occurrences with mixed.
/// E.g.
/// - if #1 has upper bound (#1 & A), the upper bound can be simplified to
///   (mixed & A) = A.
/// - if #1 has upper bound (#1 | A), the upper bound can be simplified to
///   (mixed | A) = mixed
pub fn remove_tyvar_from_upper_bound(
    env: &mut Env,
    var: tvid::T,
    upper_bound: InternalType,
) -> InternalType {
    fn is_mixed(ty: &Ty) -> bool {
        ty_equal(None, ty, &make_type::mixed(typing_reason::none()))
            || ty_equal(
                None,
                ty,
                &make_type::intersection(typing_reason::none(), vec![]),
            )
    }
    fn remove(env: &mut Env, var: tvid::T, ty: Ty) -> Ty {
        t_utils::map_supportdyn(env, ty, |env, ty| {
            let ty = typing_env::expand_type(env, ty);
            match get_node(&ty) {
                Ty_::Tvar(v) if tvid::equal(*v, var) => make_type::mixed(typing_reason::none()),
                Ty_::Toption(ty_) => {
                    let r = get_reason(&ty).clone();
                    let ty = remove(env, var, ty_.clone());
                    make_type::nullable(r, ty)
                }
                Ty_::Tunion(tyl) => {
                    let r = get_reason(&ty).clone();
                    let tyl: Vec<Ty> = tyl.iter().map(|ty| remove(env, var, ty.clone())).collect();
                    if tyl.iter().any(is_mixed) {
                        make_type::mixed(r)
                    } else {
                        make_type::union(r, tyl)
                    }
                }
                Ty_::Tintersection(tyl) => {
                    let r = get_reason(&ty).clone();
                    let tyl: Vec<Ty> = tyl.iter().map(|ty| remove(env, var, ty.clone())).collect();
                    let tyl = tyl.into_iter().filter(|ty| !is_mixed(ty)).collect();
                    make_type::intersection(r, tyl)
                }
                _ => ty.clone(),
            }
        })
    }
    fn remove_i(env: &mut Env, var: tvid::T, ty: InternalType) -> InternalType {
        match ty {
            InternalType::LoclType(ty) => {
                let ty = remove(env, var, ty);
                InternalType::LoclType(ty)
            }
            _ => ty,
        }
    }
    remove_i(env, var, upper_bound)
}

pub fn remove_tyvar_from_upper_bounds(
    env: &mut Env,
    var: tvid::T,
    upper_bounds: &ity_set::T,
) -> ity_set::T {
    remove_tyvar_from_upper_bounds_opt(env, var, upper_bounds).unwrap_or_else(|| upper_bounds.clone())
}

/// [`remove_tyvar_from_upper_bounds`], `None` when the result has the same
/// elements as `upper_bounds` (as for the lower bounds).
fn remove_tyvar_from_upper_bounds_opt(
    env: &mut Env,
    var: tvid::T,
    upper_bounds: &ity_set::T,
) -> Option<ity_set::T> {
    if upper_bounds.iter().all(remove_tyvar_keeps_bound) {
        let env: &Env = env;
        if !upper_bounds.iter().any(|ty| t_utils::is_mixed_i(env, ty)) {
            return None;
        }
    }
    let mut acc = ity_set::empty();
    for upper_bound in upper_bounds.iter() {
        let upper_bound = remove_tyvar_from_upper_bound(env, var, upper_bound.clone());
        acc = ity_set::add(upper_bound, &acc);
    }
    let upper_bounds = acc;
    let env: &Env = env;
    let is_not_mixed = |ty: &InternalType| !t_utils::is_mixed_i(env, ty);
    Some(ity_set::filter(is_not_mixed, &upper_bounds))
}

/// Remove a type variable from its upper and lower bounds. More precisely,
/// if a type variable appears in one of its bounds under any combination of unions
/// and intersections, it can be simplified away from the bound.
/// For example,
/// - if #1 has lower bound (#1 | A), the lower bound can be simplified to A
/// - if #1 has upper bound (#1 | B), the upper bound can be simplified to mixed
///   and dually for intersections.
pub fn remove_tyvar_from_bounds(env: &mut Env, var: tvid::T) {
    let old_env = typing_env::old_env_for_log("remove_tyvar_from_bounds", Some(3), env);
    let lower_bounds = typing_env::get_tyvar_lower_bounds(env, var);
    let upper_bounds = typing_env::get_tyvar_upper_bounds(env, var);
    let lower_bounds = remove_tyvar_from_lower_bounds_opt(env, var, &lower_bounds);
    let upper_bounds = remove_tyvar_from_upper_bounds_opt(env, var, &upper_bounds);
    // Setting bounds with the same elements as the variable has changes
    // nothing (the OCaml, `remove_tyvar_from_bounds`, rebuilds both sets and
    // sets them all the same): keeping the old set and skipping the write
    // measured -0.3% check-instr.
    if let Some(lower_bounds) = lower_bounds {
        typing_env::set_tyvar_lower_bounds(env, var, lower_bounds);
    }
    if let Some(upper_bounds) = upper_bounds {
        typing_env::set_tyvar_upper_bounds(env, var, upper_bounds);
    }
    typing_env::log_env_change_opt("remove_tyvar_from_bounds", Some(3), old_env, env)
}

fn var_occurs_in_ty(env: &mut Env, var: tvid::T, ty: &Ty) -> bool {
    struct Finder<'a> {
        env: &'a mut Env,
        var: tvid::T,
    }
    impl LoclTypeVisitor<bool> for Finder<'_> {
        fn on_tvar(&mut self, occurs: bool, r: &Reason, v: isize) -> bool {
            let ety = typing_env::expand_var(self.env, r.clone(), v);
            match get_node(&ety) {
                Ty_::Tvar(v) => tvid::equal(*v, self.var),
                _ => self.on_type(occurs, &ety),
            }
        }

        fn on_type(&mut self, occurs: bool, ty: &Ty) -> bool {
            if occurs {
                occurs
            } else if !ty.may_have_tyvars() {
                // Not in the OCaml, which visits it: no type variable occurs
                // in it (see `typing_defs_core::ty_flags`; a clear flag is
                // exact). With the same test in the other tyvar visitors:
                // -3.0% check-instr.
                false
            } else {
                locl_type_visitor_on_type(self, occurs, ty)
            }
        }
    }
    let mut finder = Finder { env, var };
    finder.on_type(false, ty)
}

/// `super#on_type` in a class that inherits `Type_visitor.locl_type_visitor`
/// and overrides `on_type`: the dispatch of the inherited `on_type`, which
/// calls the methods of `this` (so the overriding ones too, as `this#...`).
fn locl_type_visitor_on_type<A, V: LoclTypeVisitor<A> + ?Sized>(this: &mut V, acc: A, ty: &Ty) -> A {
    let r = get_reason(ty);
    match get_node(ty) {
        Ty_::Tany(_) => this.on_tany(acc, r),
        Ty_::Tnonnull => this.on_tnonnull(acc, r),
        Ty_::Tdynamic(_) => this.on_tdynamic(acc, r),
        Ty_::Toption(ty) => this.on_toption(acc, r, ty),
        Ty_::Tprim(prim) => this.on_tprim(acc, r, *prim),
        Ty_::Tvar(id) => this.on_tvar(acc, r, *id),
        Ty_::Tfun(fty) => this.on_tfun(acc, r, fty),
        Ty_::Tgeneric(x) => this.on_tgeneric(acc, r, x),
        Ty_::Tnewtype(x, tyl, ty) => this.on_tnewtype(acc, r, x, tyl, ty),
        Ty_::Tdependent(x, ty) => this.on_tdependent(acc, r, x, ty),
        Ty_::Ttuple(t) => this.on_ttuple(acc, r, t),
        Ty_::Tunion(tyl) => this.on_tunion(acc, r, tyl),
        Ty_::Tintersection(tyl) => this.on_tintersection(acc, r, tyl),
        Ty_::Tshape(s) => this.on_tshape(acc, r, s),
        Ty_::Tclass(cls, exact, tyl) => this.on_tclass(acc, r, cls, exact, tyl),
        Ty_::TvecOrDict(ty1, ty2) => this.on_tvec_or_dict(acc, r, ty1, ty2),
        Ty_::Taccess(ta) => this.on_taccess(acc, r, ta),
        Ty_::Tneg(tneg) => this.on_neg_type(acc, r, tneg),
        Ty_::Tlabel(name) => this.on_tlabel(acc, r, name),
        Ty_::TclassPtr(ty) => this.on_tclass_ptr(acc, r, ty),
    }
}

/// The environment of the OCaml is not returned: the occurrence check works
/// on a copy, which the message of the error prints with.
pub fn err_if_var_in_ty_pure(env: &Env, var: tvid::T, ty: Ty) -> (Ty, Option<typing_error::T>) {
    let mut env = env.clone();
    let var_occurs_in_ty = var_occurs_in_ty(&mut env, var, &ty);
    if var_occurs_in_ty {
        let ty_err = {
            let pos = typing_env::get_tyvar_pos(&env, var);
            let ty_ = ty.clone();
            typing_error::primary(primary::T::UnificationCycle {
                pos,
                ty_name: Lazy::new(move || typing_print::full_rec(true, &env, var, &ty_)),
            })
        };
        (make_type::union(get_reason(&ty).clone(), vec![]), Some(ty_err))
    } else {
        (ty, None)
    }
}

pub fn err_if_var_in_ty(env: &Env, var: tvid::T, ty: Ty) -> Ty {
    match err_if_var_in_ty_pure(env, var, ty) {
        (ty, Some(err)) => {
            typing_error_utils::add_typing_error(&err, env);
            ty
        }
        (ty, _) => ty,
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_constraints::ConstraintType_;
    use crate::typing_defs_constraints::HasTypeMember;
    use crate::typing_defs_constraints::mk_constraint_type;
    use crate::typing_defs_core::mk;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    #[test]
    fn filter_locl_types_keeps_the_locl_types() {
        let int = prim(Tprim::Tint);
        let cty = InternalType::ConstraintType(mk_constraint_type((
            typing_reason::none(),
            ConstraintType_::ThasTypeMember(HasTypeMember {
                id: "T".to_string(),
                lower: int.clone(),
                upper: int.clone(),
            }),
        )));
        let set = ity_set::of_list(vec![cty, InternalType::LoclType(int.clone())]);
        assert_eq!(ty_set::elements(&filter_locl_types(&set)), vec![int]);
    }
}
