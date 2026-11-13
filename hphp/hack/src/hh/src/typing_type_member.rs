// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_type_member.ml`. See `hh/PORTING.md`.
//!
//! This module is meant to eventually replace Typing_taccess,
//! with drastically simpler logic. The idea here is to only
//! have *lookup* logic on class types, unlike Typing_taccess
//! that aims to work on any locl type.

use pos::ToOxidized;

use crate::class_refinement;
use crate::decl_entry;
use crate::expression_id;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::dependent_kind;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DependentType;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::RefinedConst;
use crate::typing_defs_core::RefinedConstBound;
use crate::typing_defs_core::RefinedConstBounds;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_make_type;
use crate::typing_reason as reason;
use crate::typing_set as ty_set;
use crate::typing_utils;

/// The localized result of a type member lookup; in case it is
/// [Abstract] existing lower and upper bounds are also returned.
#[derive(Clone, Debug)]
pub enum TypeMember {
    NotYetAvailable,
    Error(Option<typing_error::T>),
    Exact(Ty),
    Abstract {
        name: PosId,
        /// The bounds are optional: None for lower is equivalent
        /// to nothing and None for upper is equivalent to mixed.
        /// Having them optional ensures that [collect_bounds] below
        /// does not pick up trivial bounds and clutter the tpenv.
        lower: Option<Ty>,
        upper: Option<Ty>,
    },
}

/// Locl types are able to describe unknown concrete class types.
/// Either via expression-dependent types (those represent the
/// runtime class type of an object resulting from an expression
/// evaluation). Or via the this type in a possibly abstract class
/// (meant to represent the concrete class type of the object that
/// will be the receiver when the method is invoked).
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug)]
pub enum UnknownConcreteClassKind {
    EDT(expression_id::T),
    This,
}

fn make_missing_err(
    on_error: Option<reasons_callback::T>,
    cls_id: &PosId,
    const_name: &str,
) -> Option<typing_error::T> {
    match on_error {
        Some(on_error) => Some(typing_error::apply_reasons(
            secondary::T::Missing_class_constant {
                pos: cls_id.0.clone(),
                class_name: cls_id.1.clone(),
                const_name: const_name.to_string(),
            },
            on_error,
        )),
        None => None,
    }
}

/// Lookups a type member from the class decl of `cls_id`.
fn lookup_class_decl_type_member(
    env: &mut Env,
    on_error: Option<reasons_callback::T>,
    this_ty: Ty,
    cls_id: &PosId,
    type_id: &PosId,
) -> TypeMember {
    let ety_env = ExpandEnv {
        this_ty,
        on_error: on_error.clone(),
        ..empty_expand_env()
    };
    // Things are not perfect here, localize may itself call into
    // Typing_taccess, leading to legacy behavior.
    let localize = |env: &mut Env, decl_ty: &DeclTy| -> (Option<typing_error::T>, Ty) {
        typing_utils::localize(&ety_env, env, decl_ty)
    };
    match env_::get_class(env, &cls_id.1) {
        decl_entry::T::NotYetAvailable => TypeMember::NotYetAvailable,
        decl_entry::T::DoesNotExist => {
            TypeMember::Error(make_missing_err(on_error, cls_id, &type_id.1))
        }
        decl_entry::T::Found(cls) => match env_::get_typeconst(env, &cls, &type_id.1) {
            None => TypeMember::Error(make_missing_err(on_error, cls_id, &type_id.1)),
            Some(typeconst) => match &typeconst.kind {
                ty::decl::Typeconst::TCConcrete(tcc) => {
                    let (err_opt, lty) = localize(env, &tcc.ty);
                    match err_opt {
                        Some(_) => TypeMember::Error(err_opt),
                        None => TypeMember::Exact(lty),
                    }
                }
                ty::decl::Typeconst::TCAbstract(tca) => {
                    let name: PosId = (
                        typeconst.name.pos().clone().to_oxidized(),
                        typeconst.name.id().as_str().to_string(),
                    );
                    let (err_opt_1, lty_as) = match &tca.as_constraint {
                        Some(decl_ty) => {
                            let (err_opt, lty) = localize(env, decl_ty);
                            (err_opt, Some(lty))
                        }
                        None => (None, None),
                    };
                    let (err_opt_2, lty_super) = match &tca.super_constraint {
                        Some(decl_ty) => {
                            let (err_opt, lty) = localize(env, decl_ty);
                            (err_opt, Some(lty))
                        }
                        None => (None, None),
                    };
                    // `Option.first_some err_opt_1 err_opt_2`
                    match err_opt_1.or(err_opt_2) {
                        err_opt @ Some(_) => TypeMember::Error(err_opt),
                        None => TypeMember::Abstract {
                            name,
                            lower: lty_super,
                            upper: lty_as,
                        },
                    }
                }
            },
        },
    }
}

/// Lookups a type member in a class definition, or in the exact
/// refinement information available.
pub fn lookup_class_type_member(
    env: &mut Env,
    on_error: Option<reasons_callback::T>,
    this_ty: Ty,
    (cls_id, exact): (&PosId, &Exact),
    type_id: &PosId,
) -> TypeMember {
    let (combine_lower, combine_upper) = {
        fn dedup_then(f: impl FnOnce(Vec<Ty>) -> Ty, tys: Vec<Ty>) -> Option<Ty> {
            let ts = ty_set::of_list(tys);
            if ty_set::is_empty(&ts) {
                None
            } else {
                Some(f(ty_set::elements(&ts)))
            }
        }
        (
            |tys: Vec<Ty>| dedup_then(|tyl| typing_make_type::union(reason::none(), tyl), tys),
            |tys: Vec<Ty>| {
                dedup_then(
                    |tyl| typing_make_type::intersection(reason::none(), tyl),
                    tys,
                )
            },
        )
    };
    let refined_type_member = match exact {
        Exact::Nonexact(cr) => match {
            let refined_const: Option<RefinedConst> =
                class_refinement::get_refined_const(type_id, cr);
            refined_const
        } {
            Some(RefinedConst {
                bound: RefinedConstBound::TRexact(ty),
                ..
            }) => TypeMember::Exact(ty),
            Some(RefinedConst {
                bound:
                    RefinedConstBound::TRloose(RefinedConstBounds {
                        lower: tr_lower,
                        upper: tr_upper,
                    }),
                ..
            }) => {
                let lower = combine_lower(tr_lower);
                let upper = combine_upper(tr_upper);
                // FIXME(refinements): The position is pointing at
                // the class when we would like to point in the
                // refinement.
                let name = (cls_id.0.clone(), type_id.1.clone());
                TypeMember::Abstract { name, lower, upper }
            }
            None => TypeMember::Error(None),
        },
        _ => TypeMember::Error(None),
    };
    match refined_type_member {
        TypeMember::Exact(_) => refined_type_member,
        TypeMember::Abstract {
            name: _,
            lower: ref mem_lower,
            upper: ref mem_upper,
        } => {
            // In this case, we still lookup the class decl to potentially
            // obtain more information on the type member.
            match lookup_class_decl_type_member(env, on_error, this_ty, cls_id, type_id) {
                TypeMember::NotYetAvailable => TypeMember::NotYetAvailable,
                TypeMember::Error(_) => refined_type_member,
                result @ TypeMember::Exact(_) => result,
                TypeMember::Abstract {
                    name: cls_name,
                    lower: cls_lower,
                    upper: cls_upper,
                } => {
                    // `List.filter_map ~f:Fn.id [b1; b2]`
                    let to_list = |b1: &Option<Ty>, b2: Option<Ty>| -> Vec<Ty> {
                        b1.iter().cloned().chain(b2).collect()
                    };
                    let lower = combine_lower(to_list(mem_lower, cls_lower));
                    let upper = combine_upper(to_list(mem_upper, cls_upper));
                    TypeMember::Abstract {
                        name: cls_name,
                        lower,
                        upper,
                    }
                }
            }
        }
        _ => lookup_class_decl_type_member(env, on_error, this_ty, cls_id, type_id),
    }
}

/// Given an unknown concrete class ([Tdependent(_)] or
/// [Tgeneric("this")]) and its bounds, creates a rigid type
/// variable that stands for the type constant found in the
/// concrete class.
pub fn make_type_member(
    env: &mut Env,
    on_error: Option<reasons_callback::T>,
    this_ty: Ty,
    ucc_kind: UnknownConcreteClassKind,
    bnd_tys: &[Ty],
    type_id: &PosId,
) -> Ty {
    /// `collect_bounds env lo_bnds up_bnds bnd_tys`. The lists of bounds are
    /// built by consing in OCaml: here the head of the OCaml list is the
    /// last element of the vector.
    fn collect_bounds(
        env: &mut Env,
        on_error: &Option<reasons_callback::T>,
        this_ty: &Ty,
        type_id: &PosId,
        lo_bnds: &mut Vec<Ty>,
        up_bnds: &mut Vec<Ty>,
        bnd_tys: Vec<Ty>,
    ) {
        // The remaining bounds, the next one last (`tyl @ bnd_tys` puts the
        // conjuncts of an intersection in front of the rest).
        let mut bnd_tys: Vec<Ty> = bnd_tys.into_iter().rev().collect();
        while let Some(bnd_ty) = bnd_tys.pop() {
            let bnd_ty = env_::expand_type(env, bnd_ty);
            match get_node(&bnd_ty) {
                Ty_::Tclass(x_bnd, exact_bnd, _tyl_bnd) => {
                    let type_member = lookup_class_type_member(
                        env,
                        on_error.clone(),
                        this_ty.clone(),
                        (x_bnd, exact_bnd),
                        type_id,
                    );
                    match type_member {
                        TypeMember::NotYetAvailable | TypeMember::Error(_) => {}
                        TypeMember::Exact(ty) => {
                            lo_bnds.push(ty.clone());
                            up_bnds.push(ty);
                        }
                        TypeMember::Abstract {
                            name: _,
                            lower,
                            upper,
                        } => {
                            // `Option.fold ~init:bnds ~f:(Fun.flip List.cons)`
                            let maybe_add = |bnds: &mut Vec<Ty>, bnd: Option<Ty>| {
                                if let Some(bnd) = bnd {
                                    bnds.push(bnd)
                                }
                            };
                            maybe_add(lo_bnds, lower);
                            maybe_add(up_bnds, upper);
                        }
                    }
                }
                Ty_::Tintersection(tyl) => bnd_tys.extend(tyl.iter().rev().cloned()),
                _ => {}
            }
        }
    }
    let rigid_tvar_name = {
        let ucc_string_id = match ucc_kind {
            UnknownConcreteClassKind::This => "this".to_string(),
            UnknownConcreteClassKind::EDT(eid) => {
                dependent_kind::to_string(&DependentType::DTexpr(eid))
            }
        };
        format!("{}::{}", ucc_string_id, type_id.1)
    };
    let reason = reason::none();
    let ty = typing_make_type::generic(reason, rigid_tvar_name.clone());
    let mut lower_bounds = vec![];
    let mut upper_bounds = vec![];
    collect_bounds(
        env,
        &on_error,
        &this_ty,
        type_id,
        &mut lower_bounds,
        &mut upper_bounds,
        bnd_tys.to_vec(),
    );
    // `List.fold bounds ~init:env ~f:(fun env bnd -> add env rigid_tvar_name bnd)`,
    // from the head of the OCaml list
    for bnd in lower_bounds.into_iter().rev() {
        env_::add_lower_bound(None, env, &rigid_tvar_name, bnd)
    }
    for bnd in upper_bounds.into_iter().rev() {
        env_::add_upper_bound(None, env, &rigid_tvar_name, bnd)
    }
    ty
}
