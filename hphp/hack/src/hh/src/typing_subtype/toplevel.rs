// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 12682-13559): the top-level functions after the recursive group.
//! See `hh/PORTING.md`.
//!
//! These are the entry points of `Typing_subtype` (`typing_subtype.mli`),
//! re-exported at `crate::typing_subtype::*`, and the functions they use.
//!
//! - `include Subtype_tell` is the `pub use` of the four functions of its
//!   signature.
//! - The functions that OCaml defines twice (`decompose_subtype_add_bound`,
//!   `decompose_subtype`, `add_constraint`: the second definition logs and
//!   calls the first, which it shadows) have the first definition nested in
//!   the second under the same name, so that nothing else can call it.
//! - The functions that return no environment (`is_sub_type`,
//!   `is_type_disjoint`, `apply_where_constraints`, ...) take `&Env`, and
//!   work on a copy where the OCaml threads an environment of its own.
//! - Lists of errors that the OCaml builds by consing (the last error first)
//!   are vectors in the order the errors are produced, reversed where the
//!   OCaml reads the list.

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::internal_type_set as ity_set;
use crate::naming_special_names::classes::C_CLOSURE;
use crate::pos_or_decl;
use crate::tvid;
use crate::type_parameter_env;
use crate::typing_cont_key;
use crate::typing_defs;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::Tparam;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::WhereConstraint;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::is_nonexact;
use crate::typing_defs_core::locl_subst;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::phys_equal;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_kinding_defs;
use crate::typing_log;
use crate::typing_logic as tl;
use crate::typing_make_type as make_type;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_refinement;
use crate::typing_set;
use crate::typing_subtype::instantiate;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_subtype::subtype_ask;
use crate::typing_subtype::subtype_simplify;
use crate::typing_subtype::subtype_trans;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

// == API ===================================================================

// == Tell API ==============================================================

/// `include Subtype_tell`
pub use crate::typing_subtype::subtype_tell::sub_type;
pub use crate::typing_subtype::subtype_tell::sub_type_against_expected_type;
pub use crate::typing_subtype::subtype_tell::sub_type_i;
pub use crate::typing_subtype::subtype_tell::sub_type_or_fail;

// -- add_constraint(s) entry point -----------------------------------------

pub fn decompose_subtype_add_bound(
    is_dynamic_aware: bool,
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
) {
    /// The first OCaml definition, which the logging one shadows.
    fn decompose_subtype_add_bound(
        is_dynamic_aware: bool,
        env: &mut Env,
        ty_sub: Ty,
        ty_super: Ty,
    ) {
        let ty_super = env::expand_type(env, ty_super);
        let ty_sub = env::expand_type(env, ty_sub);
        match (get_node(&ty_sub), get_node(&ty_super)) {
            (_, Ty_::Tany(_)) => {}
            // name_sub <: ty_super so add an upper bound on name_sub
            (Ty_::Tgeneric(name_sub), _) if !phys_equal(&ty_sub, &ty_super) => {
                let ty_super =
                    sd::transform_dynamic_upper_bound(is_dynamic_aware, env, ty_super.clone());
                // TODO(T69551141) handle type arguments. Passing targs to get_lower_bounds,
                // but the add_upper_bound call must be adapted
                let tys = env::get_upper_bounds(env, name_sub);
                // Don't add the same type twice!
                if typing_set::mem(&ty_super, &tys) {
                } else {
                    // `~intersect` closes over the environment before the bound
                    // is added.
                    let intersect_env = env.clone();
                    let mut intersect = |ty: Ty, tyl: &[Ty]| {
                        subtype_simplify::try_intersect(None, &intersect_env, ty, tyl)
                    };
                    env::add_upper_bound(Some(&mut intersect), env, name_sub, ty_super)
                }
            }
            // ty_sub <: name_super so add a lower bound on name_super
            (_, Ty_::Tgeneric(name_super)) if !phys_equal(&ty_sub, &ty_super) => {
                let tys = env::get_lower_bounds(env, name_super);
                // Don't add the same type twice!
                if typing_set::mem(&ty_sub, &tys) {
                } else {
                    // `~union` closes over the environment before the bound is
                    // added.
                    let union_env = env.clone();
                    let mut union =
                        |ty: Ty, tyl: &[Ty]| subtype_simplify::try_union(&union_env, ty, tyl);
                    env::add_lower_bound(Some(&mut union), env, name_super, ty_sub.clone())
                }
            }
            (_, _) => {}
        }
    }

    let ty_sub = env::expand_type(env, ty_sub);
    let ty_super = env::expand_type(env, ty_super);
    if logging::should_log_subtype(env, 2, &ty_sub, &ty_super) {
        // `log_subtype` prints with the environment before the call, which
        // the continuation changes: a copy.
        let log_env = env.clone();
        let (log_ty_sub, log_ty_super) = (ty_sub.clone(), ty_super.clone());
        logging::log_subtype(
            None, // this_ty
            "Typing_subtype.decompose_subtype_add_bound",
            &log_env,
            &log_ty_sub,
            &log_ty_super,
            || decompose_subtype_add_bound(is_dynamic_aware, env, ty_sub, ty_super),
        )
    } else {
        decompose_subtype_add_bound(is_dynamic_aware, env, ty_sub, ty_super)
    }
}

pub fn decompose_subtype_add_prop(env: &mut Env, prop: &tl::SubtypeProp) {
    match prop {
        tl::SubtypeProp::Conj(props) => {
            for prop in props {
                decompose_subtype_add_prop(env, prop)
            }
        }
        tl::SubtypeProp::Disj(_, props) => match props.as_slice() {
            [] => env::mark_inconsistent(env),
            [prop_] => decompose_subtype_add_prop(env, prop_),
            _ => {
                let callable_pos = env.genv.callable_pos.clone();
                typing_log::log_prop(
                    2,
                    &pos_or_decl::of_raw_pos(callable_pos),
                    "decompose_subtype_add_prop",
                    env,
                    prop,
                );
            }
        },
        tl::SubtypeProp::IsSubtype(
            is_dynamic_aware,
            InternalType::LoclType(ty1),
            InternalType::LoclType(ty2),
        ) => decompose_subtype_add_bound(*is_dynamic_aware, env, ty1.clone(), ty2.clone()),
        tl::SubtypeProp::IsSubtype(..) => {
            // Subtyping queries between locl types are not creating
            // constraint types only if require_soundness is unset.
            // Otherwise type refinement subtyping queries may create
            // Thas_type_member() constraint types.
            panic!(
                "{}{}",
                "Subtyping locl types in completeness mode should yield ",
                "propositions involving locl types only."
            )
        }
        tl::SubtypeProp::AmbiguousShapeSplat(_) => {
            panic!("Ambiguous shape-splat propositions are not produced in completeness mode")
        }
    }
}

pub fn decompose_subtype_add_bound_err(
    is_dynamic_aware: bool,
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
) -> Option<typing_error::T> {
    let ty_super = env::expand_type(env, ty_super);
    let ty_sub = env::expand_type(env, ty_sub);
    match (get_node(&ty_sub), get_node(&ty_super)) {
        (_, Ty_::Tany(_)) => None,
        // name_sub <: ty_super so add an upper bound on name_sub
        (Ty_::Tgeneric(name_sub), _) if !phys_equal(&ty_sub, &ty_super) => {
            let ty_super =
                sd::transform_dynamic_upper_bound(is_dynamic_aware, env, ty_super.clone());
            let tys = env::get_upper_bounds(env, name_sub);
            // Don't add the same type twice!
            if typing_set::mem(&ty_super, &tys) {
                None
            } else {
                // `~intersect` closes over the environment before the bound is
                // added.
                let intersect_env = env.clone();
                let mut intersect = |ty: Ty, tyl: &[Ty]| {
                    subtype_simplify::try_intersect(None, &intersect_env, ty, tyl)
                };
                env::add_upper_bound(Some(&mut intersect), env, name_sub, ty_super);
                None
            }
        }
        // ty_sub <: name_super so add a lower bound on name_super
        (_, Ty_::Tgeneric(name_super)) if !phys_equal(&ty_sub, &ty_super) => {
            let tys = env::get_lower_bounds(env, name_super);
            // Don't add the same type twice!
            if typing_set::mem(&ty_sub, &tys) {
                None
            } else {
                // `~union` closes over the environment before the bound is
                // added.
                let union_env = env.clone();
                let mut union =
                    |ty: Ty, tyl: &[Ty]| subtype_simplify::try_union(&union_env, ty, tyl);
                env::add_lower_bound(Some(&mut union), env, name_super, ty_sub.clone());
                None
            }
        }
        (_, _) => None,
    }
}

pub fn decompose_subtype_add_prop_err(
    env: &mut Env,
    prop: &tl::SubtypeProp,
) -> Option<typing_error::T> {
    match prop {
        tl::SubtypeProp::Conj(props) => {
            // `errs` is the OCaml list (the last error first).
            let mut errs: Vec<typing_error::T> = vec![];
            for prop in props {
                let err_opt = decompose_subtype_add_prop_err(env, prop);
                if let Some(err) = err_opt {
                    errs.insert(0, err);
                }
            }
            typing_error::multiple_opt(errs)
        }
        tl::SubtypeProp::Disj(err_opt, props) => match props.as_slice() {
            [] => err_opt.clone(),
            [prop_] => decompose_subtype_add_prop_err(env, prop_),
            _ => {
                let callable_pos = env.genv.callable_pos.clone();
                typing_log::log_prop(
                    2,
                    &pos_or_decl::of_raw_pos(callable_pos),
                    "decompose_subtype_add_prop",
                    env,
                    prop,
                );
                None
            }
        },
        tl::SubtypeProp::IsSubtype(
            is_dynamic_aware,
            InternalType::LoclType(ty1),
            InternalType::LoclType(ty2),
        ) => decompose_subtype_add_bound_err(*is_dynamic_aware, env, ty1.clone(), ty2.clone()),
        tl::SubtypeProp::IsSubtype(..) => {
            // Subtyping queries between locl types are not creating
            // constraint types only if require_soundness is unset.
            // Otherwise type refinement subtyping queries may create
            // Thas_type_member() constraint types.
            panic!(
                "{}{}",
                "Subtyping locl types in completeness mode should yield ",
                "propositions involving locl types only."
            )
        }
        tl::SubtypeProp::AmbiguousShapeSplat(_) => {
            panic!("Ambiguous shape-splat propositions are not produced in completeness mode")
        }
    }
}

/// Given two types that we know are in a subtype relationship
///   ty_sub <: ty_super
/// add to env.tpenv any bounds on generic type parameters that must
/// hold for ty_sub <: ty_super to be valid.
///
/// For example, suppose we know Cov<T> <: Cov<D> for a covariant class Cov.
/// Then it must be the case that T <: D so we add an upper bound D to the
/// bounds for T.
///
/// Although some of this code is similar to that for sub_type_inner, its
/// purpose is different. sub_type_inner takes two types t and u and makes
/// updates to the substitution of type variables (through unification) to
/// make t <: u true.
///
/// decompose_subtype takes two types t and u for which t <: u is *assumed* to
/// hold, and makes updates to bounds on generic parameters that *necessarily*
/// hold in order for t <: u.
pub fn decompose_subtype(
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) {
    /// The first OCaml definition, which the logging one shadows.
    fn decompose_subtype(
        env: &mut Env,
        ty_sub: Ty,
        ty_super: Ty,
        on_error: Option<reasons_callback::T>,
    ) {
        let prop = subtype::simplify(
            &subtype_env::create(
                Some(false),            // require_soundness
                Some(true),             // require_completeness
                None,                   // ignore_readonly
                None,                   // no_top_bottom
                None,                   // is_dynamic_aware
                None,                   // is_coeffect
                None,                   // in_transitive_closure
                None,                   // ignore_likes
                None,                   // has_member_arg_posl
                None,                   // report_ambiguous_shape_splat
                should_cls_sub_cn(env), // class_sub_classname
                2,                      // log_level
                on_error,
            ),
            None, // this_ty
            Lhs {
                sub_supportdyn: None,
                ty_sub: &ty_sub,
            },
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &ty_super,
            },
            env,
        );
        decompose_subtype_add_prop(env, &prop)
    }

    let ty_sub = env::expand_type(env, ty_sub);
    let ty_super = env::expand_type(env, ty_super);
    if logging::should_log_subtype(env, 2, &ty_sub, &ty_super) {
        // `log_subtype` prints with the environment before the call, which
        // the continuation changes: a copy.
        let log_env = env.clone();
        let (log_ty_sub, log_ty_super) = (ty_sub.clone(), ty_super.clone());
        logging::log_subtype(
            None, // this_ty
            "Typing_subtype.decompose_subtype",
            &log_env,
            &log_ty_sub,
            &log_ty_super,
            || decompose_subtype(env, ty_sub, ty_super, on_error),
        )
    } else {
        decompose_subtype(env, ty_sub, ty_super, on_error)
    }
}

pub fn decompose_subtype_err(
    env: &mut Env,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let prop = subtype::simplify(
        &subtype_env::create(
            Some(false),            // require_soundness
            Some(true),             // require_completeness
            None,                   // ignore_readonly
            None,                   // no_top_bottom
            None,                   // is_dynamic_aware
            None,                   // is_coeffect
            None,                   // in_transitive_closure
            None,                   // ignore_likes
            None,                   // has_member_arg_posl
            None,                   // report_ambiguous_shape_splat
            should_cls_sub_cn(env), // class_sub_classname
            2,                      // log_level
            on_error,
        ),
        None, // this_ty
        Lhs {
            sub_supportdyn: None,
            ty_sub: &ty_sub,
        },
        subtype::Rhs {
            super_like: false,
            super_supportdyn: false,
            ty_super: &ty_super,
        },
        env,
    );
    decompose_subtype_add_prop_err(env, &prop)
}

/// Decompose a general constraint
pub fn decompose_constraint(
    env: &mut Env,
    ck: ast_defs::ConstraintKind,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) {
    // constraints are caught based on reason, not error callback. Using unify_error
    match ck {
        ast_defs::ConstraintKind::ConstraintAs => {
            decompose_subtype(env, ty_sub, ty_super, on_error)
        }
        ast_defs::ConstraintKind::ConstraintSuper => {
            decompose_subtype(env, ty_super, ty_sub, on_error)
        }
        ast_defs::ConstraintKind::ConstraintEq => {
            decompose_subtype(env, ty_sub.clone(), ty_super.clone(), on_error.clone());
            decompose_subtype(env, ty_super, ty_sub, on_error)
        }
    }
}

pub fn decompose_constraint_err(
    env: &mut Env,
    ck: ast_defs::ConstraintKind,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    // constraints are caught based on reason, not error callback. Using unify_error
    match ck {
        ast_defs::ConstraintKind::ConstraintAs => {
            decompose_subtype_err(env, ty_sub, ty_super, on_error)
        }
        ast_defs::ConstraintKind::ConstraintSuper => {
            decompose_subtype_err(env, ty_super, ty_sub, on_error)
        }
        ast_defs::ConstraintKind::ConstraintEq => {
            let err_opt1 =
                decompose_subtype_err(env, ty_sub.clone(), ty_super.clone(), on_error.clone());
            let err_opt2 = decompose_subtype_err(env, ty_super, ty_sub, on_error);
            typing_error::multiple_opt(vec![err_opt1, err_opt2].into_iter().flatten().collect())
        }
    }
}

/// Given a constraint ty1 ck ty2 where ck is AS, SUPER or =,
/// add bounds to type parameters in the environment that necessarily
/// must hold in order for ty1 ck ty2.
///
/// First, we invoke decompose_constraint to add initial bounds to
/// the environment. Then we iterate, decomposing constraints that
/// arise through transitivity across bounds.
///
/// For example, suppose that env already contains
///   C<T1> <: T2
/// for some covariant class C. Now suppose we add the
/// constraint "T2 as C<T3>" i.e. we end up with
///   C<T1> <: T2 <: C<T3>
/// Then by transitivity we know that T1 <: T3 so we add this to the
/// environment too.
///
/// We repeat this process until no further bounds are added to the
/// environment, or some limit is reached. (It's possible to construct
/// types that expand forever under inheritance.)
///
/// `constraint_iteration_limit` in OCaml (a value): a constant here.
pub const CONSTRAINT_ITERATION_LIMIT: isize = 20;

pub fn add_constraint(
    env: &mut Env,
    ck: ast_defs::ConstraintKind,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) {
    /// The first OCaml definition, which the logging one shadows.
    fn add_constraint(
        env: &mut Env,
        ck: ast_defs::ConstraintKind,
        ty_sub: Ty,
        ty_super: Ty,
        on_error: Option<reasons_callback::T>,
    ) {
        let oldsize = env::get_tpenv_size(env);
        decompose_constraint(env, ck, ty_sub, ty_super, on_error.clone());
        if env::get_tpenv_size(env) == oldsize {
        } else {
            fn iter(n: isize, env: &mut Env, on_error: &Option<reasons_callback::T>) {
                if n > CONSTRAINT_ITERATION_LIMIT {
                } else {
                    let oldsize = env::get_tpenv_size(env);
                    // Each list is computed from the environment at the point
                    // where its fold starts.
                    for x in env::get_generic_parameters(env) {
                        for ty_sub_ in typing_set::elements(&env::get_lower_bounds(env, &x)) {
                            for ty_super_ in typing_set::elements(&env::get_upper_bounds(env, &x)) {
                                decompose_subtype(env, ty_sub_.clone(), ty_super_, on_error.clone())
                            }
                        }
                    }
                    if env::get_tpenv_size(env) == oldsize {
                    } else {
                        iter(n + 1, env, on_error)
                    }
                }
            }
            iter(0, env, &on_error)
        }
    }

    let ty_sub = env::expand_type(env, ty_sub);
    let ty_super = env::expand_type(env, ty_super);
    if logging::should_log_subtype(env, 1, &ty_sub, &ty_super) {
        // `log_subtype` prints with the environment before the call, which
        // the continuation changes: a copy.
        let log_env = env.clone();
        let (log_ty_sub, log_ty_super) = (ty_sub.clone(), ty_super.clone());
        logging::log_subtype(
            None, // this_ty
            "Typing_subtype.add_constraint",
            &log_env,
            &log_ty_sub,
            &log_ty_super,
            || add_constraint(env, ck, ty_sub, ty_super, on_error),
        )
    } else {
        add_constraint(env, ck, ty_sub, ty_super, on_error)
    }
}

pub fn add_constraint_err(
    env: &mut Env,
    ck: ast_defs::ConstraintKind,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let oldsize = env::get_tpenv_size(env);
    let err_opt = decompose_constraint_err(env, ck, ty_sub, ty_super, on_error.clone());
    if env::get_tpenv_size(env) == oldsize {
        err_opt
    } else {
        /// `err_opts` is in the order the errors are produced (the OCaml list
        /// has the last one first).
        fn iter(
            n: isize,
            env: &mut Env,
            mut err_opts: Vec<Option<typing_error::T>>,
            on_error: &Option<reasons_callback::T>,
        ) -> Option<typing_error::T> {
            if n > CONSTRAINT_ITERATION_LIMIT {
                typing_error::multiple_opt(err_opts.into_iter().rev().flatten().collect())
            } else {
                let oldsize = env::get_tpenv_size(env);
                // Each list is computed from the environment at the point
                // where its fold starts.
                for x in env::get_generic_parameters(env) {
                    for ty_sub_ in typing_set::elements(&env::get_lower_bounds(env, &x)) {
                        for ty_super_ in typing_set::elements(&env::get_upper_bounds(env, &x)) {
                            let err_opt = decompose_subtype_err(
                                env,
                                ty_sub_.clone(),
                                ty_super_,
                                on_error.clone(),
                            );
                            err_opts.push(err_opt);
                        }
                    }
                }
                if env::get_tpenv_size(env) == oldsize {
                    typing_error::multiple_opt(err_opts.into_iter().rev().flatten().collect())
                } else {
                    iter(n + 2, env, err_opts, on_error)
                }
            }
        }
        iter(0, env, vec![err_opt], &on_error)
    }
}

pub fn add_constraints(p: &Pos, env: &mut Env, constraints: &[(Ty, ast_defs::ConstraintKind, Ty)]) {
    let add_constraint = |env: &mut Env, (ty1, ck, ty2): &(Ty, ast_defs::ConstraintKind, Ty)| {
        add_constraint(
            env,
            *ck,
            ty1.clone(),
            ty2.clone(),
            Some(reasons_callback::unify_error_at(p.clone())),
        )
    };
    for cstr in constraints {
        add_constraint(env, cstr)
    }
}

pub fn add_constraints_err(
    p: &Pos,
    env: &mut Env,
    constraints: &[(Ty, ast_defs::ConstraintKind, Ty)],
) -> Option<typing_error::T> {
    let add_constraint = |env: &mut Env, (ty1, ck, ty2): &(Ty, ast_defs::ConstraintKind, Ty)| {
        add_constraint_err(
            env,
            *ck,
            ty1.clone(),
            ty2.clone(),
            Some(reasons_callback::unify_error_at(p.clone())),
        )
    };
    // In the order the errors are produced (the OCaml list has the last one
    // first).
    let mut err_opts: Vec<Option<typing_error::T>> = vec![];
    for cstr in constraints {
        let err = add_constraint(env, cstr);
        err_opts.push(err);
    }
    typing_error::multiple_opt(err_opts.into_iter().rev().flatten().collect())
}

/// `S_map.of_list` on the OCaml list that has the last element of `l` first:
/// for a key bound twice, the binding that comes first in `l` wins.
fn s_map_of_rev_list<V: Clone>(l: Vec<(String, V)>) -> im::OrdMap<String, V> {
    let mut map = im::OrdMap::new();
    for (k, v) in l.into_iter().rev() {
        map.insert(k, v);
    }
    map
}

/// `S_map.find`, which raises `Not_found`.
fn s_map_find<'a, V>(key: &str, map: &'a im::OrdMap<String, V>) -> &'a V {
    match map.get(key) {
        Some(v) => v,
        None => panic!("Not_found"),
    }
}

/// Given type parameters and where constraints possibly referring to those
/// parameters, simplify the constraints such that they can be moved into the
/// bounds of the type parameters
pub fn apply_where_constraints(
    pos: &Pos,
    def_pos: &PosOrDecl,
    tparams: &[Tparam],
    where_constraints: &[WhereConstraint],
    env: &Env,
) -> (Vec<Tparam>, Option<typing_error::T>) {
    // The environment is not returned: the one the function threads is a copy.
    let mut env = env.clone();
    let env = &mut env;
    // First, build a substitution to fresh type parameter names so that we don't
    // accidentally pick up bounds which happen to be in the context but aren't
    // implied by the constraints
    let (subst_fwd, subst_bwd, old_to_new) = {
        let mut subst: Vec<(String, Ty)> = vec![];
        let mut subst_bwd: Vec<(String, Ty)> = vec![];
        let mut old_to_new: Vec<(String, String)> = vec![];
        for Tparam {
            name: (_, orig_nm), ..
        } in tparams
        {
            let new_nm = env::fresh_param_name(env, orig_nm);
            let new_ty = mk((typing_reason::none(), Ty_::Tgeneric(new_nm.clone())));
            let old_ty = mk((typing_reason::none(), Ty_::Tgeneric(orig_nm.clone())));
            subst.push((orig_nm.clone(), new_ty));
            subst_bwd.push((new_nm.clone(), old_ty));
            old_to_new.push((orig_nm.clone(), new_nm));
        }
        let subst: locl_subst::T = s_map_of_rev_list(subst);
        let subst_bwd: locl_subst::T = s_map_of_rev_list(subst_bwd);
        (subst, subst_bwd, s_map_of_rev_list(old_to_new))
    };
    let combine_reasons = |src: Reason, _dest: Reason| src;
    // Apply the substitution to the [where] constraints
    let where_constraints: Vec<(Ty, ast_defs::ConstraintKind, Ty)> = {
        let apply = |ty: &Ty| locl_subst::apply(ty.clone(), &subst_fwd, &combine_reasons);
        where_constraints
            .iter()
            .map(|WhereConstraint(ty_l, cstr_kind, ty_r)| (apply(ty_l), *cstr_kind, apply(ty_r)))
            .collect()
    };
    // Bind the fresh type parameters and decompose the constraints so we can
    // can capture the implied bounds on the type parameters
    let (tpenv, err_opt) = {
        let tparams: Vec<Tparam> = tparams
            .iter()
            .map(|tparam| {
                let (pos, orig_nm) = &tparam.name;
                let new_nm = s_map_find(orig_nm, &old_to_new).clone();
                let tp_name = (pos.clone(), new_nm);
                Tparam {
                    name: tp_name,
                    ..tparam.clone()
                }
            })
            .collect();
        let mut tpenv = env.tpenv.clone();
        instantiate::bind_tparams(
            typing_reason::witness_from_decl(def_pos.clone()),
            &tparams,
            0,
            env,
            &mut tpenv,
        );
        env.tpenv = tpenv;
        // Decompose the constraints and grab the modified type parameter env
        let err_opt = add_constraints_err(pos, env, &where_constraints);
        // The new bounds will be applied in the [next] continuation since
        // [add_constraints] is written for refinement
        let m = &env.lenv.per_cont_env;
        let tpenv = match m.get(&typing_cont_key::T::Next) {
            None => env.tpenv.clone(),
            Some(entry) => entry.tpenv.clone(),
        };
        (tpenv, err_opt)
    };
    // Update the type parameters with the bounds implied by the where constraint
    // by mapping back from the fresh type parameter's bounds
    let apply = |ty: &Ty| locl_subst::apply(ty.clone(), &subst_bwd, &combine_reasons);
    let apply_bounds = |tp_constraints: &[(ast_defs::ConstraintKind, Ty)],
                        entry: &typing_kinding_defs::Kind|
     -> Vec<(ast_defs::ConstraintKind, Ty)> {
        let typing_kinding_defs::Kind {
            lower_bounds,
            upper_bounds,
            ..
        } = entry;
        // Both folds cons onto the front of the list, the lower bounds first.
        let cstrs = typing_set::fold(
            |ty: &Ty, mut cstrs: Vec<(ast_defs::ConstraintKind, Ty)>| {
                cstrs.insert(0, (ast_defs::ConstraintKind::ConstraintSuper, apply(ty)));
                cstrs
            },
            lower_bounds,
            tp_constraints.to_vec(),
        );
        typing_set::fold(
            |ty: &Ty, mut cstrs: Vec<(ast_defs::ConstraintKind, Ty)>| {
                cstrs.insert(0, (ast_defs::ConstraintKind::ConstraintAs, apply(ty)));
                cstrs
            },
            upper_bounds,
            cstrs,
        )
    };
    (
        tparams
            .iter()
            .map(|default| {
                let Tparam {
                    name: (_, orig_name),
                    constraints: tp_constraints,
                    ..
                } = default;
                let new_name = s_map_find(orig_name, &old_to_new);
                let entry_opt = type_parameter_env::get(new_name, &tpenv);
                match entry_opt {
                    None => default.clone(),
                    Some(entry) => {
                        let tp_constraints = apply_bounds(tp_constraints, &entry);
                        Tparam {
                            constraints: tp_constraints,
                            ..default.clone()
                        }
                    }
                }
            })
            .collect(),
        err_opt,
    )
}

// -- subtype_funs entry point ----------------------------------------------

pub fn subtype_funs(
    check_return: bool,
    for_override: bool,
    on_error: Option<reasons_callback::T>,
    r_sub: Reason,
    ft_sub: FunType,
    r_super: Reason,
    ft_super: FunType,
    env: &mut Env,
) -> Option<typing_error::T> {
    // This is used for checking subtyping of function types for method override
    // (see Typing_subtype_method) so types are fully-explicit and therefore we
    // permit subtyping to dynamic
    let old_env = env.clone();
    let class_sub_classname = !for_override && should_cls_sub_cn(env);
    let prop = subtype::simplify_funs(
        &subtype_env::create(
            None,                   // require_soundness
            None,                   // require_completeness
            None,                   // ignore_readonly
            None,                   // no_top_bottom
            Some(false),            // is_dynamic_aware
            None,                   // is_coeffect
            None,                   // in_transitive_closure
            None,                   // ignore_likes
            None,                   // has_member_arg_posl
            None,                   // report_ambiguous_shape_splat
            class_sub_classname,    // class_sub_classname
            2,                      // log_level
            on_error.clone(),
        ),
        check_return,
        for_override,
        false, // super_like
        (r_sub.clone(), &ft_sub),
        (r_super.clone(), &ft_super),
        env,
    );
    let ty_err = subtype_trans::prop_to_env(
        &InternalType::LoclType(mk((r_sub, Ty_::Tfun(std::rc::Rc::new(ft_sub))))),
        &InternalType::LoclType(mk((r_super, Ty_::Tfun(std::rc::Rc::new(ft_super))))),
        env,
        prop,
        on_error,
    );
    if ty_err.is_some() {
        *env = old_env;
    }
    ty_err
}

// == Ask API ===============================================================

// -- is_sub_type entry point -----------------------------------------------

/// Non-side-effecting test for subtypes.
/// result = true implies ty1 <: ty2
/// result = false implies NOT ty1 <: ty2 OR we don't know
pub fn is_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    subtype_ask::is_sub_type_alt_i(
        false, // require_completeness
        false, // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) == Some(true)
}

/// Non-side-effecting test for subtypes.
/// result = true implies ty1 <: ty2 OR we don't know
/// result = false implies NOT ty1 <: ty2
pub fn is_maybe_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    !(subtype_ask::is_sub_type_alt_i(
        false, // require_completeness
        false, // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) == Some(false))
}

// -- is_dynamic_aware_sub_type entry point ---------------------------------

pub fn is_dynamic_aware_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    subtype_ask::is_sub_type_alt_i(
        false, // require_completeness
        false, // no_top_bottom
        true,  // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) == Some(true)
}

// -- is_sub_type_for_union entry point -------------------------------------

pub fn is_sub_type_for_union_help(
    env: &Env,
    is_dynamic_aware: Option<bool>,
    ty1: &Ty,
    ty2: &Ty,
) -> bool {
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    subtype_ask::is_sub_type_alt_i(
        false, // require_completeness
        true,  // no_top_bottom
        is_dynamic_aware,
        None, // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) == Some(true)
}

pub fn is_sub_type_for_union(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    is_sub_type_for_union_help(env, Some(false), ty1, ty2)
}

/// Entry point
pub fn is_sub_type_for_union_i(env: &Env, ty1: &InternalType, ty2: &InternalType) -> bool {
    subtype_ask::is_sub_type_for_union_i(env, Some(false), ty1, ty2)
}

// -- is_sub_type_ignore_generic_params entry point -------------------------

pub fn is_sub_type_ignore_generic_params(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    subtype_ask::is_sub_type_alt_i(
        // TODO(T121047839): Should this set a dedicated ignore_generic_param flag instead?
        true,  // require_completeness
        true,  // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) == Some(true)
}

pub fn is_sub_type_opt_ignore_generic_params(env: &Env, ty1: &Ty, ty2: &Ty) -> Option<bool> {
    subtype_ask::is_sub_type_alt_i(
        // TODO(T121047839): Should this set a dedicated ignore_generic_param flag instead?
        true,  // require_completeness
        true,  // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    )
}

// -- can_sub_type entry point ----------------------------------------------

pub fn can_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    subtype_ask::is_sub_type_alt_i(
        false, // require_completeness
        true,  // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env,
        &InternalType::LoclType(ty1.clone()),
        &InternalType::LoclType(ty2.clone()),
    ) != Some(false)
}

// -- is_type_disjoint entry point ------------------------------------------

/// The `visited` pair of the disjointness functions: the type variables and
/// the generics already seen (`Tvid.Set.t * S_set.t`).
pub type Visited = (tvid::set::T, im::OrdSet<String>);

thread_local! {
    /// The depth of the calls of [`is_type_disjoint_help`] in progress on
    /// this thread (see [`MAX_DISJOINT_DEPTH`]).
    static DISJOINT_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The deepest nesting of [`is_type_disjoint_help`] calls before it raises
/// `Stack_overflow`.
///
/// The OCaml has no bound: a newtype whose constraint is itself
/// (`newtype A as A = int`), seen from a file where it is opaque but whose
/// definition was not reported as cyclic (a context entry that redeclares
/// it), makes `is_type_disjoint_help` recurse through
/// `get_concrete_supertypes` forever: the OCaml process hangs, its memory
/// growing. Here the recursion would overflow the thread's stack and abort
/// the process; past this depth it raises the OCaml's `Stack_overflow`
/// instead, which the callers handle as any exception (the Glean indexer
/// reports an indexing failure for the file and goes on). The depth of a
/// real disjointness check is that of the nesting of its types, far below
/// this; 10,000 frames fit in the 1 GiB stacks of the checking threads.
const MAX_DISJOINT_DEPTH: u32 = 10_000;

/// Leaves a level of [`DISJOINT_DEPTH`], also when unwinding.
struct DisjointDepthGuard;

impl Drop for DisjointDepthGuard {
    fn drop(&mut self) {
        DISJOINT_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

/// visited record which type variables & generics we've seen, to cut off cycles.
pub fn is_type_disjoint_help(visited: &Visited, env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let depth = DISJOINT_DEPTH.with(|d| {
        let depth = d.get() + 1;
        d.set(depth);
        depth
    });
    let _guard = DisjointDepthGuard;
    if depth > MAX_DISJOINT_DEPTH {
        std::panic::panic_any(crate::rt::ocaml_exn::Uncaught::stack_overflow())
    }
    // The environment that the expansions return is used from here on, but
    // not returned: a copy.
    let mut env = env.clone();
    let ty1 = env::expand_type(&mut env, ty1.clone());
    let ty2 = env::expand_type(&mut env, ty2.clone());
    match (get_node(&ty1), get_node(&ty2)) {
        (_, Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Taccess(_))
        | (Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Taccess(_), _) => false,
        (Ty_::Tshape(_), Ty_::Tshape(_)) => {
            // This could be more precise, e.g., if we have two closed shapes with different fields.
            // However, intersection already detects this and simplifies to nothing, so it's not
            // so important here.
            false
        }
        (Ty_::Tshape(_), _) => {
            // Treat shapes as dict<arraykey, mixed> because that implementation detail
            // leaks through when doing is dict<_, _> on them, and they are also
            // Traversable, KeyedContainer, etc. (along with darrays).
            // We could translate darray to a more precise dict type with the same
            // type arguments, but it doesn't matter since disjointness doesn't ever
            // look at them.
            let r = get_reason(&ty1).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &make_type::dict(
                    r.clone(),
                    make_type::arraykey(r.clone()),
                    make_type::mixed(r),
                ),
                &ty2,
            )
        }
        (_, Ty_::Tshape(_)) => {
            let r = get_reason(&ty2).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &ty1,
                &make_type::dict(
                    r.clone(),
                    make_type::arraykey(r.clone()),
                    make_type::mixed(r),
                ),
            )
        }
        (
            Ty_::Ttuple(TupleType {
                required: tyl1,
                optional: t_optional1,
                extra: TupleExtra::Tvariadic(t_variadic1),
            }),
            Ty_::Ttuple(TupleType {
                required: tyl2,
                optional: t_optional2,
                extra: TupleExtra::Tvariadic(t_variadic2),
            }),
        ) if t_optional1.is_empty()
            && t_optional2.is_empty()
            && typing_defs::is_nothing(t_variadic1)
            && typing_defs::is_nothing(t_variadic2) =>
        {
            // `List.exists2`, which compares the lengths before it looks at
            // the elements.
            if tyl1.len() != tyl2.len() {
                true
            } else {
                tyl1.iter()
                    .zip(tyl2.iter())
                    .any(|(ty1, ty2)| is_type_disjoint_help(visited, &env, ty1, ty2))
            }
        }
        // TODO optional and variadic components T201398626 T201398652
        (Ty_::Ttuple(_), _) => {
            // Treat tuples as vec<mixed> because that implementation detail
            // leaks through when doing is vec<_> on them, and they are also
            // Traversable, Container, etc. along with varrays.
            // We could translate varray to a more precise vec type with the same
            // type argument, but it doesn't matter since disjointness doesn't ever
            // look at it.
            let r = get_reason(&ty1).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &make_type::vec(r.clone(), make_type::mixed(r)),
                &ty2,
            )
        }
        (_, Ty_::Ttuple(_)) => {
            let r = get_reason(&ty2).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &ty1,
                &make_type::vec(r.clone(), make_type::mixed(r)),
            )
        }
        (Ty_::TvecOrDict(tyk, tyv), _) => {
            let r = get_reason(&ty1).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &make_type::union(
                    r.clone(),
                    vec![
                        make_type::vec(r.clone(), tyv.clone()),
                        make_type::dict(r, tyk.clone(), tyv.clone()),
                    ],
                ),
                &ty2,
            )
        }
        (_, Ty_::TvecOrDict(tyk, tyv)) => {
            let r = get_reason(&ty2).clone();
            is_type_disjoint_help(
                visited,
                &env,
                &ty1,
                &make_type::union(
                    r.clone(),
                    vec![
                        make_type::vec(r.clone(), tyv.clone()),
                        make_type::dict(r, tyk.clone(), tyv.clone()),
                    ],
                ),
            )
        }
        (Ty_::Tgeneric(name), _) => is_generic_disjoint(visited, &env, name, &ty1, &ty2),
        (_, Ty_::Tgeneric(name)) => is_generic_disjoint(visited, &env, name, &ty2, &ty1),
        (Ty_::Tnewtype(..) | Ty_::Tdependent(..) | Ty_::Tintersection(_), _) => {
            let bounds = t_utils::get_concrete_supertypes(
                None,  // cache
                None,  // expand_supportdyn
                None,  // include_case_types
                false, // abstract_enum
                &mut env,
                ty1.clone(),
            );
            is_intersection_type_disjoint(visited, &env, &bounds, &ty2)
        }
        (_, Ty_::Tnewtype(..) | Ty_::Tdependent(..) | Ty_::Tintersection(_)) => {
            let bounds = t_utils::get_concrete_supertypes(
                None,  // cache
                None,  // expand_supportdyn
                None,  // include_case_types
                false, // abstract_enum
                &mut env,
                ty2.clone(),
            );
            is_intersection_type_disjoint(visited, &env, &bounds, &ty1)
        }
        (Ty_::Tvar(tv), _) => is_tyvar_disjoint(visited, &env, *tv, &ty2),
        (_, Ty_::Tvar(tv)) => is_tyvar_disjoint(visited, &env, *tv, &ty1),
        (Ty_::Tunion(tyl), _) => tyl
            .iter()
            .all(|ty| is_type_disjoint_help(visited, &env, &ty2, ty)),
        (_, Ty_::Tunion(tyl)) => tyl
            .iter()
            .all(|ty| is_type_disjoint_help(visited, &env, &ty1, ty)),
        (Ty_::Toption(ty1), _) => {
            is_type_disjoint_help(visited, &env, ty1, &ty2)
                && is_type_disjoint_help(
                    visited,
                    &env,
                    &make_type::null(typing_reason::none()),
                    &ty2,
                )
        }
        (_, Ty_::Toption(ty2)) => {
            is_type_disjoint_help(visited, &env, &ty1, ty2)
                && is_type_disjoint_help(
                    visited,
                    &env,
                    &ty1,
                    &make_type::null(typing_reason::none()),
                )
        }
        (Ty_::Tnonnull, _) => is_sub_type_for_union_help(
            &env,
            None, // is_dynamic_aware
            &ty2,
            &make_type::null(typing_reason::none()),
        ),
        (_, Ty_::Tnonnull) => is_sub_type_for_union_help(
            &env,
            None, // is_dynamic_aware
            &ty1,
            &make_type::null(typing_reason::none()),
        ),
        (
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ClassTag(c1, tag_args)))),
            Ty_::Tclass((_, c2), _, _tyl),
        )
        | (
            Ty_::Tclass((_, c2), _, _tyl),
            Ty_::Tneg(TypePredicate(_, TypePredicate_::IsTag(TypeTag::ClassTag(c1, tag_args)))),
        ) if tag_args.is_empty() => {
            // These are disjoint iff for all objects o, o in c2<_tyl> implies that
            // o notin (complement (Union tyl'. c1<tyl'>)), which is just that
            // c2<_tyl> subset Union tyl'. c1<tyl'>. If c2 is a subclass of c1, then
            // whatever _tyl is, we can chase up the hierarchy to find an instantiation
            // for tyl'. If c2 is not a subclass of c1, then no matter what the tyl' are
            // the subset realtionship cannot hold, since either c1 and c2 are disjoint tags,
            // or c1 is a non-equal subclass of c2, and so objects that are exact c2,
            // can't inhabit c1. NB, we aren't allowing abstractness of a class to cause
            // types to be considered disjoint.
            // e.g., in abstract class C {}; class D extends C {}, we wouldn't consider
            // neg D and C to be disjoint.
            t_utils::is_sub_class_refl(&env, c2, c1)
        }
        (Ty_::Tneg(pred1), _) => typing_refinement::passes_predicate(&env, &ty2, pred1),
        (_, Ty_::Tneg(pred2)) => typing_refinement::passes_predicate(&env, &ty1, pred2),
        (Ty_::Tprim(tp1), Ty_::Tprim(tp2)) => subtype_negation::is_tprim_disjoint(*tp1, *tp2),
        (Ty_::Tclass((_, cname), ex, _), Ty_::Tprim(Tprim::Tarraykey))
        | (Ty_::Tprim(Tprim::Tarraykey), Ty_::Tclass((_, cname), ex, _))
            if C_STRING == cname.as_str()
                || (cname.as_str() == sn::classes::STRINGISH && is_nonexact(ex)) =>
        {
            false
        }
        // Same as above case, runtime conflates equality of "A" === A::class
        (Ty_::Tprim(Tprim::Tarraykey), Ty_::TclassPtr(_))
        | (Ty_::TclassPtr(_), Ty_::Tprim(Tprim::Tarraykey)) => false,
        (Ty_::Tclass((_, id), _, _), Ty_::TclassPtr(_))
        | (Ty_::TclassPtr(_), Ty_::Tclass((_, id), _, _))
            if id.as_str() == C_STRING =>
        {
            false
        }
        (Ty_::Tprim(_), Ty_::TclassPtr(_)) | (Ty_::TclassPtr(_), Ty_::Tprim(_)) => true,
        // A function type can be an instance of a Closure
        (Ty_::Tfun(_), Ty_::Tclass((_, closure), _, _))
        | (Ty_::Tclass((_, closure), _, _), Ty_::Tfun(_))
            if C_CLOSURE == closure.as_str() =>
        {
            false
        }
        (Ty_::Tprim(_), Ty_::Tfun(_) | Ty_::Tclass(..))
        | (Ty_::Tfun(_) | Ty_::Tclass(..), Ty_::Tprim(_)) => true,
        (Ty_::Tfun(_), Ty_::Tfun(_)) => false,
        (Ty_::Tfun(_), Ty_::Tclass(..)) | (Ty_::Tclass(..), Ty_::Tfun(_)) => true,
        (Ty_::Tclass((_, c1), ex1, _), Ty_::Tclass((_, c2), ex2, _)) => {
            subtype_negation::is_class_disjoint(&env, c1, ex1, c2, ex2)
        }
        (Ty_::Tprim(_), Ty_::Tlabel(_)) | (Ty_::Tlabel(_), Ty_::Tprim(_)) => true,
        (Ty_::Tfun(_), Ty_::Tlabel(_)) | (Ty_::Tlabel(_), Ty_::Tfun(_)) => true,
        (Ty_::Tclass(..), Ty_::Tlabel(_)) | (Ty_::Tlabel(_), Ty_::Tclass(..)) => true,
        (Ty_::Tlabel(name1), Ty_::Tlabel(name2)) => name1 != name2,
        (Ty_::TclassPtr(_ty), _) | (_, Ty_::TclassPtr(_ty)) => {
            // TODO(T199606542) Improve disjointnesss check, should be
            // disjoint iff objects of _ty would be disjoint
            false
        }
    }
}

/// incomplete, e.g., is_intersection_type_disjoint (?int & ?float) num
pub fn is_intersection_type_disjoint(
    visited_tvyars: &Visited,
    env: &Env,
    inter_tyl: &[Ty],
    ty: &Ty,
) -> bool {
    inter_tyl
        .iter()
        .any(|inter_ty| is_type_disjoint_help(visited_tvyars, env, ty, inter_ty))
}

pub fn is_intersection_itype_set_disjoint(
    visited_tvyars: &Visited,
    env: &Env,
    inter_ty_set: &ity_set::T,
    ty: &Ty,
) -> bool {
    ity_set::exists(
        |ity| is_itype_disjoint(visited_tvyars, env, ty, ity),
        inter_ty_set,
    )
}

pub fn is_itype_disjoint(
    visited_tvyars: &Visited,
    env: &Env,
    lty1: &Ty,
    ity: &InternalType,
) -> bool {
    match ity {
        InternalType::LoclType(lty2) => is_type_disjoint_help(visited_tvyars, env, lty1, lty2),
        InternalType::ConstraintType(_) => false,
    }
}

pub fn is_tyvar_disjoint(visited: &Visited, env: &Env, tyvar: tvid::T, ty: &Ty) -> bool {
    let (visited_tyvars, visited_generics) = visited;
    if visited_tyvars.contains(&tyvar) {
        // There is a cyclic type variable bound, this will lead to a type error
        false
    } else {
        let bounds = env::get_tyvar_upper_bounds(env, tyvar);
        let mut visited_tyvars = visited_tyvars.clone();
        visited_tyvars.insert(tyvar);
        is_intersection_itype_set_disjoint(
            &(visited_tyvars, visited_generics.clone()),
            env,
            &bounds,
            ty,
        )
    }
}

pub fn is_generic_disjoint(visited: &Visited, env: &Env, name: &str, gen_ty: &Ty, ty: &Ty) -> bool {
    let (visited_tyvars, visited_generics) = visited;
    if visited_generics.contains(name) {
        false
    } else {
        // `get_concrete_supertypes` returns an environment, which is the one
        // used from here on but is not returned: a copy.
        let mut env = env.clone();
        let bounds = t_utils::get_concrete_supertypes(
            None,  // cache
            None,  // expand_supportdyn
            None,  // include_case_types
            false, // abstract_enum
            &mut env,
            gen_ty.clone(),
        );
        is_intersection_type_disjoint(
            &(
                visited_tyvars.clone(),
                visited_generics.update(name.to_string()),
            ),
            &env,
            &bounds,
            ty,
        )
    }
}

/// Determines whether the types are definitely disjoint, or whether they might
/// overlap.
pub fn is_type_disjoint(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    is_type_disjoint_help(&(tvid::set::T::new(), im::OrdSet::new()), env, ty1, ty2)
}

// == Polymorphic type instatiation =========================================

/// Expose for use from typing but ensure tyvar ranks are 0
pub fn instantiate_fun_type(
    pos: Pos,
    fun_ty: FunType,
    env: &mut Env,
) -> (Option<typing_error::T>, FunType) {
    instantiate::instantiate_fun_type(None, pos, fun_ty, 0, env)
}

// -- Set function references -----------------------------------------------

/// Hack to allow for circular dependencies between Ocaml modules.
///
/// The OCaml calls it when the module is initialised (`let () = set_fun_refs
/// ()`). Rust has no module initialisation: the references of
/// `crate::typing_utils` (`static <name>_ref: fn ...`) are immutable and
/// hold the functions the OCaml assigns here (`sub_type`,
/// `sub_type_against_expected_type`, `sub_type_i`, `add_constraint`,
/// `is_sub_type`, `is_sub_type_for_union`, `is_sub_type_for_union_i`,
/// `is_sub_type_ignore_generic_params`,
/// `is_sub_type_opt_ignore_generic_params`, `is_type_disjoint`,
/// `can_sub_type`), as `crate::typing_env::SIMPLIFY_UNIONS_REF` does, so
/// there is nothing to do; it is kept for the callers of the OCaml function.
pub fn set_fun_refs() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn s_map_of_rev_list_keeps_the_first_binding_of_a_key() {
        // The OCaml list is `[(T, 3); (U, 2); (T, 1)]`, and `S_map.of_list`
        // adds its bindings from left to right.
        let m = s_map_of_rev_list(vec![
            ("T".to_string(), 1),
            ("U".to_string(), 2),
            ("T".to_string(), 3),
        ]);
        assert_eq!(m.len(), 2);
        assert_eq!(*s_map_find("T", &m), 1);
        assert_eq!(*s_map_find("U", &m), 2);
    }

    #[test]
    #[should_panic(expected = "Not_found")]
    fn s_map_find_raises_not_found() {
        let m: im::OrdMap<String, isize> = s_map_of_rev_list(vec![]);
        s_map_find("T", &m);
    }

    #[test]
    fn constraint_iteration_limit_is_the_ocaml_one() {
        assert_eq!(CONSTRAINT_ITERATION_LIMIT, 20);
    }
}
