// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_subtype_method.ml`. See `hh/PORTING.md`.

use oxidized::ast_defs::ReifyKind;
use oxidized::pos::Pos;
use ty::decl::ty as d;

use crate::typing_defs::ExpandEnv;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclWhereConstraint;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::WhereConstraint;
/// `module Env = Typing_env`
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_generic_constraint;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
/// `module Reason = Typing_reason`
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_solver;
use crate::typing_subtype;

/// `Decl_subst.make_locl`, for localized types.
///
/// `crate::decl_subst::make_locl` maps the names to
/// `oxidized::typing_defs_core::Ty`, which has no inferred types (PORTING.md:
/// never use it for one); this is the same function for [`Ty`].
fn decl_subst_make_locl(tparams: &[DeclTparam], tyl: &[Ty]) -> crate::pmap::Map<String, Ty> {
    let mut subst = crate::pmap::Map::new();
    let mut tyl = tyl;
    for t in tparams {
        match tyl {
            [] => {}
            [ty, rl @ ..] => {
                subst.insert(t.name.id_ref().as_str().to_string(), ty.clone());
                tyl = rl;
            }
        }
    }
    subst
}

/// Check that the method decl with signature ft_sub can be used to override
/// (is a subtype of) method decl with signature ft_super.
///
/// This goes beyond subtyping on function types because methods can have
/// generic parameters with bounds, and `where` constraints.
///
/// Suppose ft_super is of the form
///    <T1 csuper1, ..., Tn csupern>(tsuper1, ..., tsuperm) : tsuper where wsuper
/// and ft_sub is of the form
///    <T1 csub1, ..., Tn csubn>(tsub1, ..., tsubm) : tsub where wsub
/// where csuperX and csubX are constraints on type parameters and wsuper and
/// wsub are 'where' constraints. Note that all types in the superclass,
/// including constraints (so csuperX, tsuperX, tsuper and wsuper) have had
/// any class type parameters instantiated appropriately according to
/// the actual arguments of the superclass. For example, suppose we have
///
///   class Super<T> {
///     function foo<Tu as A<T>>(T $x) : B<T> where T super C<T>
///   }
///   class Sub extends Super<D> {
///     ...override of foo...
///   }
/// then the actual signature in the superclass that we need to check is
///     function foo<Tu as A<D>>(D $x) : B<D> where D super C<D>
/// Note in particular the general form of the 'where' constraint.
///
/// (Currently, this instantiation happens in
///   Typing_extends.check_class_implements which in turn calls
///   Decl_instantiate.instantiate_ce)
///
/// Then for ft_sub to be a subtype of ft_super it must be the case that
/// (1) tsuper1 <: tsub1, ..., tsupern <: tsubn (under constraints
///     T1 csuper1, ..., Tn csupern and wsuper).
///
///     This is contravariant subtyping on parameter types.
///
/// (2) tsub <: tsuper (under constraints T1 csuper1, ..., Tn csupern and wsuper)
///     This is covariant subtyping on result type. For constraints consider
///       e.g. consider ft_super = <T super I>(): T
///                 and ft_sub = <T>(): I
///
/// (3) The constraints for ft_super entail the constraints for ft_sub, because
///     we might be calling the function having checked that csuperX are
///     satisfied but the definition of the function (e.g. consider an override)
///     has been checked under csubX.
///     More precisely, we must assume constraints T1 csuper1, ..., Tn csupern
///     and wsuper, and check that T1 satisfies csub1, ..., Tn satisfies csubn
///     and that wsub holds under those assumptions.
pub fn subtype_method_decl(
    check_return: bool,
    env: &mut Env,
    r_sub: &Reason,
    ft_sub: &DeclFunType,
    r_super: &Reason,
    ft_super: &DeclFunType,
    on_error: reasons_callback::T,
) {
    let p_sub = typing_reason::to_pos(r_sub);
    let p_super = typing_reason::to_pos(r_super);
    let ety_env = empty_expand_env();
    // We check constraint entailment and contravariant parameter/covariant result
    // subtyping in the context of the ft_super constraints. But we'd better
    // restore tpenv afterwards
    let old_tpenv = typing_env::get_tpenv(env);
    let old_global_tpenv = typing_env::get_global_tpenv(env);
    typing_env::open_tyvars(env, Pos::NONE);

    // First extend the environment with the type parameters from the supertype, along
    // with their bounds and the function's where constraints
    let ty_err1 = phase::localize_and_add_generic_parameters_and_where_constraints(
        &ety_env,
        env,
        &ft_super.tparams,
        &ft_super.where_constraints,
    );
    if let Some(ty_err) = &ty_err1 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    // Reified type parameters should match those in the overridden method (TODO).
    // For non-reified parameters, we allow a generic method to override
    // a method whose signature is an instance of the generic type. For example,
    //   foo(int):int
    // can be overridden by
    //   foo<T>(T):T
    // To implement this, we use localize_targs to generate fresh type variables for the
    // generic parameters, and add bounds and where constraints.
    // A more complex example is the following:
    //   interface I { abstract const type TC as num; }
    // Now consider
    // class B {
    //   function foo(num):void;
    // }
    // overridden by
    // class C<T as I> extends B {
    //   function foo<TF>(TF):void where TF super T::TC;
    // }
    // We need to find type variable #1 with T::TC <: #1 such that
    // (by contravariance of parameter types) num <: #1.
    // Clearly #1:=num is a solution, as T::TC <: num from the type constant bound.
    // Dually, suppose we have
    // class C<T as I> extends B {
    //   function foo<TF>(TF):void where TF as T::TC;
    // }
    // This time, we need to find type variable #1 with #1 <: T::TC
    // such that num <: #1.
    // There is no solution, as by transitivity we need num <: T::TC which does not hold.
    let non_reified_tparams: Vec<DeclTparam> = ft_sub
        .tparams
        .iter()
        .filter(|tp| match tp.reified {
            ReifyKind::Erased => true,
            _ => false,
        })
        .cloned()
        .collect();
    let (ty_err2, explicit_targs) = phase::localize_targs(
        true, // check_type_integrity
        true, // is_method
        p_sub.clone(),
        Pos::NONE,
        "overriding".to_string(),
        Some(false), // check_explicit_targs
        env,
        &non_reified_tparams,
        vec![],
    );
    if let Some(ty_err) = &ty_err2 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    let tvarl: Vec<Ty> = explicit_targs.into_iter().map(|targ| targ.0).collect();
    let substs = decl_subst_make_locl(&non_reified_tparams, &tvarl);
    let ty_err3 = phase::check_tparams_constraints(
        Pos::NONE,
        &ExpandEnv {
            substs: substs.clone(),
            ..ety_env.clone()
        },
        env,
        &ft_sub.tparams,
    );
    if let Some(ty_err) = &ty_err3 {
        typing_error_utils::add_typing_error(ty_err, env)
    }

    // Localize the function type for the method in the subtype.
    // Non-reified generic method parameters will be replaced by the type
    // variables generated by localize_targs
    let (ty_err4, locl_ft_sub) = phase::localize_ft(
        None,
        &ExpandEnv {
            substs: substs.clone(),
            ..ety_env.clone()
        },
        p_sub,
        env,
        ft_sub,
    );
    if let Some(ty_err) = &ty_err4 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    // Localize the function type for the method in the supertype.
    // Generic method parameters will be left alone.
    let (ty_err5, locl_ft_super) = phase::localize_ft(None, &ety_env, p_super, env, ft_super);
    if let Some(ty_err) = &ty_err5 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    let add_where_constraints = |env: &mut Env, cstrl: &[WhereConstraint]| {
        for WhereConstraint(ty1, ck, ty2) in cstrl {
            typing_subtype::add_constraint(env, *ck, ty1.clone(), ty2.clone(), Some(on_error.clone()))
        }
    };
    // Now extend the environment with `where` constraints from the supertype
    add_where_constraints(env, &locl_ft_super.where_constraints);
    // Check the where constraints from the subtype.
    // Localize the where constraints here rather than using locl_ft_sub.ft_where_constraints,
    // as localize_ft loses changes to tpenv (see comments in code for localize_ft)
    let check_where_constraints =
        |ety_env: &ExpandEnv, env: &mut Env, cstrl: &[DeclWhereConstraint]| {
            // The OCaml list of errors, reversed.
            let mut ty_errs: Vec<typing_error::T> = vec![];
            for d::WhereConstraint(ty, ck, cstr_ty) in cstrl {
                let (e1, ty) = phase::localize(ety_env, env, ty);
                let (e2, cstr_ty) = phase::localize(ety_env, env, cstr_ty);
                let e3 = typing_generic_constraint::check_constraint(
                    env,
                    *ck,
                    ty,
                    cstr_ty,
                    Some(on_error.clone()),
                );
                let ty_err_opt =
                    typing_error::multiple_opt([e1, e2, e3].into_iter().flatten().collect());
                if let Some(e) = ty_err_opt {
                    ty_errs.push(e)
                }
            }
            ty_errs.reverse();
            typing_error::multiple_opt(ty_errs)
        };
    let ty_err6 = check_where_constraints(
        &ExpandEnv {
            substs,
            ..ety_env.clone()
        },
        env,
        &ft_sub.where_constraints,
    );

    if let Some(ty_err) = &ty_err6 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    // Finally apply ordinary contra/co subtyping on the function types
    let ty_err7 = typing_subtype::subtype_funs(
        check_return,
        true, // for_override
        Some(on_error.clone()),
        r_sub.clone(),
        locl_ft_sub,
        r_super.clone(),
        locl_ft_super,
        env,
    );
    if let Some(ty_err) = &ty_err7 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    let ty_err8 = typing_solver::close_tyvars_and_solve(env);
    if let Some(ty_err) = &ty_err8 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    // Restore the type parameter environment
    typing_env::env_with_global_tpenv(env, old_global_tpenv);
    typing_env::env_with_tpenv(env, old_tpenv)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::ast_defs::Variance;
    use pos::BPos;
    use pos::Positioned;
    use pos::TypeName;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;

    #[test]
    fn decl_subst_takes_as_many_types_as_there_are() {
        let tparam = |name: &str| DeclTparam {
            variance: Variance::Invariant,
            name: Positioned::new(BPos::none(), TypeName::new(name)),
            constraints: Box::new([]),
            reified: ReifyKind::Erased,
            user_attributes: Box::new([]),
        };
        let int = mk((typing_reason::none(), Ty_::Tprim(Tprim::Tint)));
        let subst = decl_subst_make_locl(&[tparam("T"), tparam("U")], &[int.clone()]);
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("T"), Some(&int));
    }
}
