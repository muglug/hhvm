// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_type_wellformedness.ml`. See `hh/PORTING.md`.
//!
//! This module checks wellformedness of type hints in the decls and bodies.
//! Wellformedness checks include:
//! - constraints on type parameters (e.g. C<string> where C requires T as arraykey)
//! - constraints on type splats (e.g. ...T requires T as (mixed...) )
//! - hint well-kinded-ness
//! - trivial syntactic errors:
//!     - writing ?nonnull instead of mixed
//!     - ?void, ?noreturn, ?mixed
//!     - Tuple<X, Y> instead of (X, Y))
//!
//! # Port notes
//!
//! - The record `env` of the OCaml is [`Env`]; the typing environment is
//!   `TEnv` (`Typing_env_types.env`). The functions of the `.mli` (and the
//!   others that return an error list without the environment) take the
//!   typing environment by reference and work on a copy where the OCaml
//!   changes it locally.
//! - The OCaml evaluates the operands of `@`, and the elements of a list
//!   literal, from right to left. Checking a hint has effects (errors that the
//!   integrity checks and `check_happly` report directly, lints, recorded
//!   dependencies), so the lists are computed here in that order, the last one
//!   first, and then concatenated.
//! - `hint_ ~in_signature env p h` takes the hint `(p, h)` whole.
//! - `typing_type_wellformedness.ml` defines `hint` twice: the first is
//!   [`hint`] here, the second (over the typing environment, which only `expr`
//!   uses) is [`hint_tenv`].

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::ConstraintKind;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::ToOxidized;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::aast_defs;
use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
/// `module FunUtils = Decl_fun_utils`
use crate::decl_fun_utils as fun_utils;
use crate::decl_hint;
/// `module Inst = Decl_instantiate`
use crate::decl_instantiate as inst;
use crate::lint;
use crate::naming_attributes;
use crate::typechecker_options;
use crate::typing_case_type_utils;
use crate::typing_defs::*;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env as TEnv;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::primary::package::TargetSymbolSpec;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_error_utils;
use crate::typing_generic_constraint;
use crate::typing_make_type as make_type;
use crate::typing_packages::CheckReason;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
use crate::typing_reason;
use crate::typing_shapes;
use crate::typing_type_integrity;

/// `type env`
#[derive(Clone)]
pub struct Env {
    pub typedef_tparams: Vec<nast::Tparam>,
    pub tenv: TEnv,
    /// True while traversing an interface declaration.
    pub in_interface: bool,
}

/// `l1 @ l2`, once both are computed.
fn append<A>(mut l1: Vec<A>, l2: Vec<A>) -> Vec<A> {
    l1.extend(l2);
    l1
}

fn check_tparams_constraints(
    env: &mut TEnv,
    use_pos: Pos,
    tparams: &[DeclTparam],
    targs: &[Ty],
) -> Option<typing_error::T> {
    // If there is an arity mismatch, we have already emitted an error,
    // so let's not bother checking the constraints.
    // E.g. what would it mean to check C<D>
    // if definition is class C<T1 as I<T2>, T2 as J>
    if tparams.len() == targs.len() {
        let ety_env: ExpandEnv = ExpandEnv {
            substs: crate::decl_subst::make_locl(tparams, targs),
            ..empty_expand_env()
        };
        phase::check_tparams_constraints(use_pos, &ety_env, env, tparams)
    } else {
        None
    }
}

fn loclty_of_hint(
    visibility_behavior: Option<VisibilityBehavior>,
    unchecked_tparams: &[nast::Tparam],
    env: &mut TEnv,
    h: &aast::Hint,
) -> (Pos, Ty) {
    let visibility_behavior = visibility_behavior.unwrap_or(VisibilityBehavior::NeverExpandNewtype);
    let hint_pos = h.0.clone();
    let decl_ty = decl_hint::hint(&env.decl_env, h);
    let unchecked_tparams: Vec<DeclTparam> = unchecked_tparams
        .iter()
        .map(|t| decl_hint::aast_tparam_to_decl_tparam(&env.decl_env, t))
        .collect();
    let tyl: Vec<DeclTy> = unchecked_tparams
        .iter()
        .map(|t| {
            // `Typing_defs.make_tany ()`
            DeclTy::new(R::witness_from_decl(t.name.pos().clone()), d::Ty_::Tany)
        })
        .collect();
    let subst = inst::make_subst(&unchecked_tparams, &tyl);
    let decl_ty = inst::instantiate(&subst, &decl_ty);
    let ety_env =
        empty_expand_env_with_on_error(reasons_callback::invalid_type_hint(hint_pos.clone()));
    let ety_env = ExpandEnv {
        visibility_behavior,
        ..ety_env
    };
    let (ty_err_opt, locl_ty) = phase::localize(&ety_env, env, &decl_ty);
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
    (hint_pos, locl_ty)
}

/// `[ `Found of typeconst_type | `Missing | `Skip ]`
enum ClassConst {
    Found(TypeconstType),
    Missing,
    Skip,
}

fn check_hrefinement(
    unchecked_tparams: &[nast::Tparam],
    env: &TEnv,
    h: &aast::Hint,
    rl: &[aast::Refinement],
) {
    let mut env = env.clone();
    let (_, locl_ty) = loclty_of_hint(None, unchecked_tparams, &mut env, h);
    let env = env;
    match get_node(&locl_ty) {
        Ty_::Tclass(cls_id, _, _) => {
            let cls = env::get_class(&env, &cls_id.1);
            let get_class_const = |const_sid: &aast::Sid| -> ClassConst {
                match &cls {
                    decl_entry::T::Found(cls) => match env::get_typeconst(&env, cls, &const_sid.1) {
                        Some(ttc) => ClassConst::Found(ttc),
                        None => ClassConst::Missing,
                    },
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        ClassConst::Skip
                    }
                }
            };
            let check_ref = |r: &aast::Refinement| -> Option<typing_error::T> {
                let (const_sid, is_ctx) = match r {
                    aast::Refinement::Rctx(sid, _) => (sid, true),
                    aast::Refinement::Rtype(sid, _) => (sid, false),
                };
                let on_error = reasons_callback::invalid_class_refinement(const_sid.0.clone());
                match get_class_const(const_sid) {
                    ClassConst::Skip => None,
                    ClassConst::Found(ttc) if ttc.is_ctx == is_ctx => None,
                    ClassConst::Missing => Some(typing_error::apply_reasons(
                        secondary::T::MissingClassConstant {
                            pos: cls_id.0.clone(),
                            class_name: cls_id.1.clone(),
                            const_name: const_sid.1.clone(),
                        },
                        on_error,
                    )),
                    ClassConst::Found(ttc) => {
                        let kind_str = |is_ctx: bool| {
                            if is_ctx { "ctx" } else { "type" }.to_string()
                        };
                        let correct_kind = kind_str(ttc.is_ctx);
                        let wrong_kind = kind_str(is_ctx);
                        Some(typing_error::apply_reasons(
                            secondary::T::InvalidRefinedConstKind {
                                pos: cls_id.0.clone(),
                                class_name: cls_id.1.clone(),
                                const_name: const_sid.1.clone(),
                                correct_kind,
                                wrong_kind,
                            },
                            on_error,
                        ))
                    }
                }
            };
            for r in rl {
                if let Some(err) = check_ref(r) {
                    typing_error_utils::add_typing_error(&err, &env)
                }
            }
        }
        _ => {}
    }
}

/// Mostly check constraints on type parameters.
fn check_happly(unchecked_tparams: &[nast::Tparam], env: &mut TEnv, h: &aast::Hint) {
    let (hint_pos, locl_ty) = loclty_of_hint(None, unchecked_tparams, env, h);
    let ty_err_opt = match get_node(&locl_ty) {
        Ty_::Tnewtype(name, targs, _) | Ty_::Tclass((_, name), _, targs) => {
            let tparams = env::get_class_or_typedef_tparams(env, name);
            check_tparams_constraints(env, hint_pos, &tparams, targs)
        }
        _ => None,
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}

fn check_shape_splat_hint(env: &Env, p: &Pos, h: &aast::Hint) -> Option<typing_error::T> {
    let mut tenv = env.tenv.clone();
    let (hint_pos, locl_ty) = loclty_of_hint(
        Some(VisibilityBehavior::ExpandVisibleNewtypeOnly),
        &env.typedef_tparams,
        &mut tenv,
        h,
    );
    // The top shape(mixed...)
    let cstr_ty = {
        let reason = typing_reason::witness(p.clone());
        let top = make_type::top_shape(reason.clone());
        make_type::locl_like(reason, top)
    };
    // The environment it returns is dropped.
    typing_generic_constraint::check_tparams_constraint(
        &mut tenv,
        hint_pos,
        ConstraintKind::ConstraintAs,
        cstr_ty,
        locl_ty,
    )
}

fn check_tuple_splat_hint(env: &Env, p: &Pos, h: &aast::Hint) -> Vec<typing_error::T> {
    // It's important that we pass tenv down to subtyping
    // because tpenv might have been updated during localization
    let mut tenv = env.tenv.clone();
    let (hint_pos, locl_ty) = loclty_of_hint(
        Some(VisibilityBehavior::ExpandVisibleNewtypeOnly),
        &env.typedef_tparams,
        &mut tenv,
        h,
    );
    // The top tuple (mixed...)
    let cstr_ty = mk((
        typing_reason::witness(p.clone()),
        Ty_::Ttuple(TupleType {
            required: vec![],
            optional: vec![],
            extra: TupleExtra::Tvariadic(make_type::mixed(typing_reason::witness(p.clone()))),
        }),
    ));
    // The environment it returns is dropped.
    let err = typing_generic_constraint::check_tparams_constraint(
        &mut tenv,
        hint_pos,
        ConstraintKind::ConstraintAs,
        cstr_ty,
        locl_ty,
    );
    err.into_iter().collect()
}

fn union_intersection_type_hints_enabled(env: &TEnv) -> bool {
    let tcopt = env::get_tcopt(env);
    tcopt.po.union_intersection_type_hints
        || typechecker_options::is_unstable_feature_enabled(tcopt, "union_intersection_type_hints")
}

/// Whether [ty] contains a union requiring union/intersection type hints.
/// This is intentionally narrower than [Typing_defs.is_denotable]: localized
/// source hints such as [~T] and open [shape(...)] contain internal
/// representations that are not themselves denotable.
///
/// (Each call goes on with the environment `strip_supportdyn` returns, and
/// drops it.)
fn contains_non_denotable_union(env: &TEnv, ty: &Ty) -> bool {
    let mut env = env.clone();
    let (_, ty) = crate::typing_utils::strip_supportdyn(&mut env, ty.clone());
    let env = &env;
    match get_node(&ty) {
        Ty_::Tunion(tys) => {
            // Localized like types are unions containing dynamic. Check the type below
            // the like rather than rejecting the representation of the like itself.
            match crate::typing_dynamic_utils::try_strip_dynamic_from_union(None, env, tys) {
                Some((_, tys)) => match tys.as_slice() {
                    [] => false,
                    [ty] => contains_non_denotable_union(env, ty),
                    _ => {
                        let ty = make_type::union(get_reason(&ty).clone(), tys);
                        !is_denotable(&ty)
                    }
                },
                None => !is_denotable(&ty),
            }
        }
        Ty_::Tclass(_, _, tys) | Ty_::Tintersection(tys) => {
            tys.iter().any(|ty| contains_non_denotable_union(env, ty))
        }
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => {
            t_required
                .iter()
                .any(|ty| contains_non_denotable_union(env, ty))
                || t_optional
                    .iter()
                    .any(|ty| contains_non_denotable_union(env, ty))
                || match t_extra {
                    TupleExtra::Tsplat(ty) | TupleExtra::Tvariadic(ty) => {
                        contains_non_denotable_union(env, ty)
                    }
                }
        }
        Ty_::TvecOrDict(tk, tv) => {
            contains_non_denotable_union(env, tk) || contains_non_denotable_union(env, tv)
        }
        Ty_::Taccess(TaccessType(ty, _)) => contains_non_denotable_union(env, ty),
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            unknown_value: s_unknown_value,
            fields: s_fields,
            ..
        })) => {
            contains_non_denotable_union(env, s_unknown_value)
                || s_fields
                    .iter()
                    .any(|(_, field)| contains_non_denotable_union(env, &field.ty))
        }
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => ss_elems
            .iter()
            .any(|ty| contains_non_denotable_union(env, ty)),
        Ty_::Tfun(ft) => {
            contains_non_denotable_union(env, &ft.ret)
                || ft
                    .params
                    .iter()
                    .any(|param| contains_non_denotable_union(env, &param.type_))
        }
        Ty_::Toption(ty) | Ty_::TclassPtr(ty) => contains_non_denotable_union(env, ty),
        Ty_::Tnonnull
        | Ty_::Tdynamic(_)
        | Ty_::Tprim(_)
        | Ty_::Tnewtype(..)
        | Ty_::Tgeneric(_)
        | Ty_::Tneg(_)
        | Ty_::Tany(_)
        | Ty_::Tvar(_)
        | Ty_::Tdependent(..)
        | Ty_::Tlabel(_) => false,
    }
}

/// Reject non-denotable union field types produced by a shape splat.
pub fn shape_splat_field_denotability_errors(
    env: &TEnv,
    claim_pos: &Pos,
    hint: &aast::Hint,
    ty: &Ty,
) -> Vec<typing_error::T> {
    let hint_has_shape_splat = match &*hint.1 {
        aast::Hint_::Hshape(aast::NastShapeInfo {
            field_map: nsi_field_map,
            ..
        }) => nsi_field_map.iter().any(|e| match e {
            aast::ShapeElement::SESplat(_) => true,
            aast::ShapeElement::SEField(_) => false,
        }),
        _ => false,
    };
    if !union_intersection_type_hints_enabled(env) && hint_has_shape_splat {
        // Shape normalization can only produce simple shapes, shape splats, union
        // intersection, a single type param / newtype or any of those wrapped in
        // supportdyn so the traversal is limited to those cases
        //
        // (`acc` is consed onto and reversed at the end: here in order.)
        fn collect(env: &TEnv, ty: &Ty, acc: &mut Vec<primary::shape_splat::NonDenotableField>) {
            let mut env = env.clone();
            let (_, ty) = crate::typing_utils::strip_supportdyn(&mut env, ty.clone());
            let env = &env;
            match get_node(&ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    fields: s_fields, ..
                })) => {
                    for (field, field_ty) in s_fields.iter() {
                        let sft_ty = &field_ty.ty;
                        if contains_non_denotable_union(env, sft_ty) {
                            acc.push(primary::shape_splat::NonDenotableField {
                                label: t_shape_field::name(&field.0).to_string(),
                                pos: t_shape_field::pos(&field.0),
                                ty: sft_ty.clone(),
                            })
                        }
                    }
                }
                Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems: tys }))
                | Ty_::Tunion(tys)
                | Ty_::Tintersection(tys) => {
                    for ty in tys.iter() {
                        collect(env, ty, acc)
                    }
                }
                _ => {}
            }
        }
        let mut fields = vec![];
        collect(env, ty, &mut fields);
        if fields.is_empty() {
            vec![]
        } else {
            vec![typing_error::primary(primary::T::ShapeSplat(
                primary::shape_splat::T::NonDenotableShapeSplatFields {
                    pos: claim_pos.clone(),
                    fields,
                },
            ))]
        }
    } else {
        vec![]
    }
}

/// Check every shape splat in a callable type hint. Nested function hints are
/// traversed completely because both their parameter and return types can
/// construct non-denotable unions.
fn callable_hint_shape_splat_field_denotability_errors(
    env: &Env,
    hint: &aast::Hint,
) -> Vec<typing_error::T> {
    let aast::Hint(pos, hint_) = hint;
    let check_hint = callable_hint_shape_splat_field_denotability_errors;
    let check_hints = |env: &Env, hints: &[aast::Hint]| -> Vec<typing_error::T> {
        hints.iter().flat_map(|h| check_hint(env, h)).collect()
    };
    let check_hint_opt = |env: &Env, hint: &Option<aast::Hint>| -> Vec<typing_error::T> {
        match hint {
            None => vec![],
            Some(hint) => check_hint(env, hint),
        }
    };
    match &**hint_ {
        aast::Hint_::Hshape(aast::NastShapeInfo {
            field_map: nsi_field_map,
            ..
        }) if nsi_field_map.iter().any(|e| match e {
            aast::ShapeElement::SESplat(_) => true,
            aast::ShapeElement::SEField(_) => false,
        }) =>
        {
            // Check the normalized outer shape rather than its nested splats: a later
            // field or splat can overwrite a non-denotable field from an inner shape.
            let mut tenv = env.tenv.clone();
            let (_, ty) = phase::localize_hint_no_subst(&mut tenv, true, hint);
            shape_splat_field_denotability_errors(&tenv, pos, hint, &ty)
        }
        aast::Hint_::Hshape(aast::NastShapeInfo {
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
            ..
        }) => {
            let field_errors: Vec<typing_error::T> = nsi_field_map
                .iter()
                .flat_map(|e| match e {
                    aast::ShapeElement::SEField(aast::ShapeFieldInfo { hint: sfi_hint, .. })
                    | aast::ShapeElement::SESplat(sfi_hint) => check_hint(env, sfi_hint),
                })
                .collect();
            append(field_errors, check_hint_opt(env, nsi_unknown_fields_type))
        }
        aast::Hint_::Hfun(aast::HintFun {
            tparams: hf_tparams,
            param_tys: hf_param_tys,
            variadic_ty: hf_variadic_ty,
            named_variadic_ty: hf_named_variadic_ty,
            return_ty: hf_return_ty,
            ..
        }) => {
            let tparams: Vec<nast::Tparam> = hf_tparams
                .iter()
                .map(aast_defs::tparam_of_hint_tparam)
                .collect();
            let mut tenv = env.tenv.clone();
            let _ = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
                &mut tenv,
                true,
                &tparams,
                &[],
            );
            let env = &Env {
                tenv,
                ..env.clone()
            };
            let errs = check_hints(env, hf_param_tys);
            let errs = append(errs, check_hint_opt(env, hf_variadic_ty));
            let errs = append(errs, check_hint_opt(env, hf_named_variadic_ty));
            append(errs, check_hint(env, hf_return_ty))
        }
        aast::Hint_::Htuple(aast::TupleInfo {
            required: tup_required,
            extra: tup_extra,
        }) => {
            let errs = check_hints(env, tup_required);
            let extra_errs = match tup_extra {
                aast::TupleExtra::Hextra(aast::TupleExtraInfo {
                    optional: tup_optional,
                    variadic: tup_variadic,
                }) => append(
                    check_hints(env, tup_optional),
                    check_hint_opt(env, tup_variadic),
                ),
                aast::TupleExtra::Hsplat(hint) => check_hint(env, hint),
            };
            append(errs, extra_errs)
        }
        aast::Hint_::Hrefinement(root, refinements) => {
            let refinement_errors: Vec<typing_error::T> = refinements
                .iter()
                .flat_map(|r| match r {
                    aast::Refinement::Rctx(_, aast::CtxRefinement::CRexact(hint))
                    | aast::Refinement::Rtype(_, aast::TypeRefinement::TRexact(hint)) => {
                        check_hint(env, hint)
                    }
                    aast::Refinement::Rctx(
                        _,
                        aast::CtxRefinement::CRloose(aast::CtxRefinementBounds {
                            lower: cr_lower,
                            upper: cr_upper,
                        }),
                    ) => append(
                        check_hint_opt(env, cr_lower),
                        check_hint_opt(env, cr_upper),
                    ),
                    aast::Refinement::Rtype(
                        _,
                        aast::TypeRefinement::TRloose(aast::TypeRefinementBounds {
                            lower: tr_lower,
                            upper: tr_upper,
                        }),
                    ) => append(check_hints(env, tr_lower), check_hints(env, tr_upper)),
                })
                .collect();
            append(check_hint(env, root), refinement_errors)
        }
        aast::Hint_::HvecOrDict(key, value) => {
            append(check_hint_opt(env, key), check_hint(env, value))
        }
        aast::Hint_::Happly(_, hints)
        | aast::Hint_::Hunion(hints)
        | aast::Hint_::Hintersection(hints) => check_hints(env, hints),
        aast::Hint_::Haccess(root, _) => check_hint(env, root),
        aast::Hint_::HclassPtr(_, hint)
        | aast::Hint_::Hoption(hint)
        | aast::Hint_::Hsoft(hint)
        | aast::Hint_::Hlike(hint) => check_hint(env, hint),
        aast::Hint_::Hmixed
        | aast::Hint_::Hwildcard
        | aast::Hint_::Hnonnull
        | aast::Hint_::Hprim(_)
        | aast::Hint_::Hthis
        | aast::Hint_::Habstr(_)
        | aast::Hint_::Hdynamic
        | aast::Hint_::Hnothing
        | aast::Hint_::HfunContext(_)
        | aast::Hint_::Hvar(_) => vec![],
    }
}

fn callable_type_hint_shape_splat_field_denotability_errors(
    env: &Env,
    type_hint: &nast::TypeHint,
) -> Vec<typing_error::T> {
    if union_intersection_type_hints_enabled(&env.tenv) {
        vec![]
    } else {
        match crate::aast::hint_of_type_hint(type_hint) {
            None => vec![],
            Some(hint) => callable_hint_shape_splat_field_denotability_errors(env, hint),
        }
    }
}

fn context_hint(in_signature: Option<bool>, env: &Env, h: &aast::Hint) -> Vec<typing_error::T> {
    let in_signature = in_signature.unwrap_or(true);
    typing_type_integrity::check_context_hint_integrity(in_signature, &env.tenv, h);
    hint_(in_signature, true, env, h)
}

fn hint_(
    in_signature: bool,
    report_redundant_shape_splat: bool,
    env: &Env,
    h: &aast::Hint,
) -> Vec<typing_error::T> {
    let aast::Hint(p, h_) = h;
    let hint =
        |env: &Env, h: &aast::Hint| hint_(in_signature, report_redundant_shape_splat, env, h);
    let hint_opt = |env: &Env, h: &Option<aast::Hint>| match h {
        None => vec![],
        Some(h) => hint(env, h),
    };
    let hints = |env: &Env, xs: &[aast::Hint]| xs.iter().flat_map(|h| hint(env, h)).collect::<Vec<_>>();
    match &**h_ {
        aast::Hint_::Hmixed
        | aast::Hint_::Hwildcard
        | aast::Hint_::Hnonnull
        | aast::Hint_::Hprim(_)
        | aast::Hint_::Hthis
        | aast::Hint_::Haccess(..)
        | aast::Hint_::Habstr(_)
        | aast::Hint_::Hdynamic
        | aast::Hint_::Hnothing => vec![],
        aast::Hint_::Hoption(aast::Hint(_, h))
            if matches!(&**h, aast::Hint_::Hprim(aast::Tprim::Tnull)) =>
        {
            lint::option_null(p.clone());
            vec![]
        }
        aast::Hint_::Hoption(aast::Hint(_, h))
            if matches!(&**h, aast::Hint_::Hprim(aast::Tprim::Tvoid)) =>
        {
            vec![typing_error::primary(primary::T::OptionReturnOnlyTypehint {
                pos: p.clone(),
                kind: primary::OptionReturnOnlyTypehintKind::Void,
            })]
        }
        aast::Hint_::Hoption(aast::Hint(_, h))
            if matches!(&**h, aast::Hint_::Hprim(aast::Tprim::Tnoreturn)) =>
        {
            vec![typing_error::primary(primary::T::OptionReturnOnlyTypehint {
                pos: p.clone(),
                kind: primary::OptionReturnOnlyTypehintKind::Noreturn,
            })]
        }
        aast::Hint_::Hoption(aast::Hint(_, h)) if matches!(&**h, aast::Hint_::Hmixed) => {
            lint::option_mixed(p.clone());
            vec![]
        }
        aast::Hint_::HvecOrDict(ty1, ty2) => {
            let errs2 = hint(env, ty2);
            let errs1 = hint_opt(env, ty1);
            append(errs1, errs2)
        }
        aast::Hint_::Hunion(hl) | aast::Hint_::Hintersection(hl) => hints(env, hl),
        aast::Hint_::Htuple(aast::TupleInfo {
            required: tup_required,
            extra: tup_extra,
        }) => {
            let extra_errs = match tup_extra {
                aast::TupleExtra::Hextra(aast::TupleExtraInfo {
                    optional: tup_optional,
                    variadic: tup_variadic,
                }) => {
                    let errs2 = hint_opt(env, tup_variadic);
                    let errs1 = hints(env, tup_optional);
                    append(errs1, errs2)
                }
                aast::TupleExtra::Hsplat(h) => {
                    let errs2 = check_tuple_splat_hint(env, p, h);
                    let errs1 = hint(env, h);
                    append(errs1, errs2)
                }
            };
            let required_errs = hints(env, tup_required);
            append(required_errs, extra_errs)
        }
        aast::Hint_::HclassPtr(_, h)
        | aast::Hint_::Hoption(h)
        | aast::Hint_::Hsoft(h)
        | aast::Hint_::Hlike(h) => hint(env, h),
        aast::Hint_::Hfun(aast::HintFun {
            is_readonly: _,
            tparams: hf_tparams,
            param_tys: hl,
            param_info: hf_param_info,
            variadic_ty: variadic_hint,
            named_variadic_ty: named_variadic_hint,
            ctxs: hf_ctxs,
            return_ty: h,
            is_readonly_return: _,
        }) => {
            let splat_err = match (hl.last(), hf_param_info.last()) {
                (
                    Some(h),
                    Some(Some(aast::HfParamInfo {
                        splat: Some(ast_defs::SplatKind::Splat),
                        ..
                    })),
                ) => check_tuple_splat_hint(env, p, h),
                _ => vec![],
            };
            // Bind any type parameters bound in the function hint and check the hint
            let env = {
                let mut typedef_tparams: Vec<nast::Tparam> = hf_tparams
                    .iter()
                    .map(aast_defs::tparam_of_hint_tparam)
                    .collect();
                typedef_tparams.extend(env.typedef_tparams.iter().cloned());
                Env {
                    typedef_tparams,
                    ..env.clone()
                }
            };
            let env = &env;
            let tparams_errs: Vec<_> = hf_tparams
                .iter()
                .flat_map(|aast::HintTparam { constraints, .. }| {
                    constraints
                        .iter()
                        .flat_map(|(_, h)| hint(env, h))
                        .collect::<Vec<_>>()
                })
                .collect();
            let ctxs_errs = contexts_opt(env, hf_ctxs.as_ref());
            let named_variadic_errs = hint_opt(env, named_variadic_hint);
            let variadic_errs = hint_opt(env, variadic_hint);
            let ret_errs = hint(env, h);
            let params_errs = hints(env, hl);
            let errs = append(ctxs_errs, tparams_errs);
            let errs = append(named_variadic_errs, errs);
            let errs = append(variadic_errs, errs);
            let errs = append(ret_errs, errs);
            let errs = append(splat_err, errs);
            append(params_errs, errs)
        }
        aast::Hint_::Happly(ast_defs::Id(p, name), _) if name == "\\Tuple" || name == "\\tuple" => {
            vec![typing_error::wellformedness(
                primary::wellformedness::T::TupleSyntax(p.clone()),
            )]
        }
        aast::Hint_::Happly(_, hl) => {
            // `let _tenv = check_happly ...`: the environment is dropped.
            check_happly(&env.typedef_tparams, &mut env.tenv.clone(), h);
            hints(env, hl)
        }
        aast::Hint_::Hrefinement(hr, rl) => {
            check_hrefinement(&env.typedef_tparams, &env.tenv, h, rl);
            let mut refinement_hints: Vec<&aast::Hint> = vec![];
            for r in rl {
                let mut hs: Vec<&aast::Hint> = match r {
                    aast::Refinement::Rctx(_, aast::CtxRefinement::CRexact(h)) => vec![h],
                    aast::Refinement::Rctx(
                        _,
                        aast::CtxRefinement::CRloose(aast::CtxRefinementBounds {
                            lower: hl,
                            upper: hr,
                        }),
                    ) => hl.iter().chain(hr.iter()).collect(),
                    aast::Refinement::Rtype(_, aast::TypeRefinement::TRexact(h)) => vec![h],
                    aast::Refinement::Rtype(
                        _,
                        aast::TypeRefinement::TRloose(aast::TypeRefinementBounds {
                            lower: hl,
                            upper: hr,
                        }),
                    ) => hl.iter().chain(hr.iter()).collect(),
                };
                hs.extend(refinement_hints);
                refinement_hints = hs;
            }
            std::iter::once(hr)
                .chain(refinement_hints)
                .flat_map(|h| hint(env, h))
                .collect()
        }
        aast::Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: nsi_allows_unknown_fields,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) => {
            let fields: Vec<&aast::ShapeFieldInfo> = nsi_field_map
                .iter()
                .filter_map(|e| match e {
                    aast::ShapeElement::SEField(sfi) => Some(sfi),
                    aast::ShapeElement::SESplat(_) => None,
                })
                .collect();
            // A splat of a type parameter (`...T`) cannot be flattened into a concrete
            // normal form, so it leaves a residual shape splat that relies on the
            // (still experimental) shape-splat subtyping. It is therefore gated by
            // `shape_splat_type_parameters`, distinct from concrete splats, which are
            // admitted at parse time by `shape_splat_concrete`.
            let splat_feature_errors: Vec<typing_error::T> =
                if typechecker_options::is_unstable_feature_enabled(
                    &env.tenv.genv.tcopt,
                    "shape_splat_type_parameters",
                ) {
                    vec![]
                } else {
                    nsi_field_map
                        .iter()
                        .filter_map(|e| match e {
                            aast::ShapeElement::SESplat(aast::Hint(pos, h))
                                if matches!(&**h, aast::Hint_::Habstr(_)) =>
                            {
                                let name = match &**h {
                                    aast::Hint_::Habstr(name) => name.clone(),
                                    _ => unreachable!(),
                                };
                                Some(typing_error::primary(primary::T::GatedByFeatureFlag {
                                    pos: pos.clone(),
                                    name,
                                    feature: "shape_splat_type_parameters".to_string(),
                                }))
                            }
                            aast::ShapeElement::SEField(_) | aast::ShapeElement::SESplat(_) => None,
                        })
                        .collect()
                };
            let (tenv, errors) = {
                let get_name = |sfi: &aast::ShapeFieldInfo| sfi.name.clone();
                let mut tenv = env.tenv.clone();
                let keys: Vec<ast_defs::ShapeFieldName> = fields.iter().map(|sfi| get_name(sfi)).collect();
                let errors = typing_shapes::check_shape_keys_validity(&mut tenv, &keys);
                (tenv, errors)
            };
            let env = &Env {
                tenv,
                ..env.clone()
            };
            let redundant_splat: Option<&aast::Hint> =
                match (nsi_allows_unknown_fields, nsi_field_map.as_slice()) {
                    (false, [aast::ShapeElement::SESplat(operand)]) => Some(operand),
                    _ => None,
                };
            // Recursively well-formedness-check both field hints and the operand of
            // each splat, so an ill-formed hint inside a splat (undefined class,
            // wrong alias arity, unknown generic, ...) is still reported. A splat of
            // a bare type parameter (`Habstr`) yields no error here and is instead
            // gated above via [splat_feature_errors].
            let rec_errors: Vec<typing_error::T> = nsi_field_map
                .iter()
                .flat_map(|e| match e {
                    aast::ShapeElement::SEField(aast::ShapeFieldInfo { hint: sfi_hint, .. }) => {
                        hint(env, sfi_hint)
                    }
                    aast::ShapeElement::SESplat(h) => {
                        let errs = if redundant_splat.is_some() {
                            hint_(in_signature, false, env, h)
                        } else {
                            hint(env, h)
                        };
                        let err_opt = check_shape_splat_hint(env, p, h);
                        match err_opt {
                            None => errs,
                            Some(err) => {
                                let mut l = vec![err];
                                l.extend(errs);
                                l
                            }
                        }
                    }
                })
                .collect();
            let unknown_fields_errors = match nsi_unknown_fields_type {
                Some(h) => hint(env, h),
                None => vec![],
            };
            let redundant_splat_errors = match (report_redundant_shape_splat, redundant_splat) {
                (true, Some(aast::Hint(operand_pos, operand_))) => {
                    vec![typing_error::wellformedness(
                        primary::wellformedness::T::RedundantShapeSplat {
                            pos: p.clone(),
                            operand_pos: operand_pos.clone(),
                            is_dynamic: match &**operand_ {
                                aast::Hint_::Hdynamic => true,
                                _ => false,
                            },
                        },
                    )]
                }
                _ => vec![],
            };
            let errs = append(splat_feature_errors, redundant_splat_errors);
            let errs = append(unknown_fields_errors, errs);
            let errs = append(rec_errors, errs);
            append(errors, errs)
        }
        aast::Hint_::HfunContext(_) => {
            // TODO(coeffects): check if arg is a function type in the locals?
            vec![]
        }
        aast::Hint_::Hvar(_) => {
            // TODO(coeffects)
            vec![]
        }
    }
}

fn contexts(env: &Env, ctxs: &aast::Contexts) -> Vec<typing_error::T> {
    let aast::Contexts(_, hl) = ctxs;
    hl.iter().flat_map(|h| context_hint(None, env, h)).collect()
}

fn contexts_opt(env: &Env, ctxs: Option<&aast::Contexts>) -> Vec<typing_error::T> {
    match ctxs {
        None => vec![],
        Some(ctxs) => contexts(env, ctxs),
    }
}

fn hint(
    in_signature: Option<bool>,
    should_check_package_boundary: Option<CheckReason>,
    env: &Env,
    h: &aast::Hint,
) -> Vec<typing_error::T> {
    let in_signature = in_signature.unwrap_or(true);
    let should_check_package_boundary =
        should_check_package_boundary.unwrap_or(CheckReason::Yes(TargetSymbolSpec::Symbol));
    // Do not use this one recursively to avoid quadratic runtime!
    typing_type_integrity::check_hint_integrity(
        in_signature,
        should_check_package_boundary,
        &env.tenv,
        h,
    );
    hint_(in_signature, true, env, h)
}

fn hint_opt(
    in_signature: Option<bool>,
    should_check_package_boundary: Option<CheckReason>,
    env: &Env,
    h: Option<&aast::Hint>,
) -> Vec<typing_error::T> {
    match h {
        None => vec![],
        Some(h) => hint(in_signature, should_check_package_boundary, env, h),
    }
}

fn hints(in_signature: Option<bool>, env: &Env, hl: &[aast::Hint]) -> Vec<typing_error::T> {
    hl.iter().flat_map(|h| hint(in_signature, None, env, h)).collect()
}

/// [should_check_package_boundary] for a type hint given whether this position
/// is runtime-enforced.
fn enforceable_type_alias_check(env: &Env, is_enforceable: bool) -> CheckReason {
    if !is_enforceable || env.in_interface {
        CheckReason::No
    } else {
        CheckReason::Yes(TargetSymbolSpec::EnforceableTypeAlias)
    }
}

fn type_hint(is_enforceable: bool, env: &Env, th: &nast::TypeHint) -> Vec<typing_error::T> {
    let should_check_package_boundary = enforceable_type_alias_check(env, is_enforceable);
    match crate::aast::hint_of_type_hint(th) {
        None => vec![],
        Some(h) => hint(None, Some(should_check_package_boundary), env, h),
    }
}

fn fun_param(env: &Env, param: &nast::FunParam) -> Vec<typing_error::T> {
    // Variadic typehints (`T ...$args`) are not enforced at runtime.
    let is_enforceable = match &param.info {
        aast::FunParamInfo::ParamVariadic => false,
        aast::FunParamInfo::ParamOptional(_) | aast::FunParamInfo::ParamRequired => true,
    };
    // (`a @ b`: `b` is computed first.)
    let denotability_errors =
        callable_type_hint_shape_splat_field_denotability_errors(env, &param.type_hint);
    append(
        type_hint(is_enforceable, env, &param.type_hint),
        denotability_errors,
    )
}

fn fun_params(env: &Env, params: &[nast::FunParam]) -> Vec<typing_error::T> {
    params.iter().flat_map(|param| fun_param(env, param)).collect()
}

fn tparam(env: &Env, t: &nast::Tparam) -> Vec<typing_error::T> {
    t.constraints
        .iter()
        .flat_map(|(ck, h)| {
            let should_check_package_boundary = match ck {
                ConstraintKind::ConstraintAs => enforceable_type_alias_check(env, true),
                _ => CheckReason::No,
            };
            hint(None, Some(should_check_package_boundary), env, h)
        })
        .collect()
}

fn tparams(env: &Env, tps: &[nast::Tparam]) -> Vec<typing_error::T> {
    tps.iter().flat_map(|t| tparam(env, t)).collect()
}

fn where_constr(env: &Env, wc: &aast::WhereConstraintHint) -> Vec<typing_error::T> {
    let aast::WhereConstraintHint(h1, _, h2) = wc;
    let errs2 = hint(None, Some(CheckReason::No), env, h2);
    let errs1 = hint(None, None, env, h1);
    append(errs1, errs2)
}

fn where_constrs(env: &Env, wcs: &[aast::WhereConstraintHint]) -> Vec<typing_error::T> {
    wcs.iter().flat_map(|wc| where_constr(env, wc)).collect()
}

fn requirements(env: &Env, reqs: &[aast::ClassReq]) -> Vec<typing_error::T> {
    reqs.iter()
        .flat_map(|aast::ClassReq(h, _kind)| hint(None, None, env, h))
        .collect()
}

fn check_splat_is_tuple(env: &Env, params: &[nast::FunParam]) -> Vec<typing_error::T> {
    match params.last() {
        Some(aast::FunParam {
            splat: Some(ast_defs::SplatKind::Splat),
            pos: param_pos,
            type_hint: aast::TypeHint(_, Some(h)),
            ..
        }) => check_tuple_splat_hint(env, param_pos, h),
        _ => vec![],
    }
}

fn fun_(tenv: &TEnv, f: &nast::Fun_) -> Vec<typing_error::T> {
    let support_dynamic_type = naming_attributes::mem(
        sn::user_attributes::SUPPORT_DYNAMIC_TYPE,
        &f.user_attributes.0,
    ) || env::get_support_dynamic_type(tenv);
    let no_auto_likes =
        naming_attributes::mem(sn::user_attributes::NO_AUTO_LIKES, &f.user_attributes.0)
            || env::get_no_auto_likes(tenv);
    let add_implicit_upper_bound = support_dynamic_type
        && !no_auto_likes
        // `Typechecker_options.everything_sdt`
        && tenv.genv.tcopt.po.everything_sdt;

    let mut tenv = tenv.clone();
    let ty_err_opt = {
        let tparams: Vec<nast::Tparam> = f
            .tparams
            .iter()
            .map(|ht_param| {
                // We have to add the implicit upper bound here
                let tparam: nast::Tparam = aast_defs::tparam_of_hint_tparam(ht_param);
                if tparam
                    .user_attributes
                    .0
                    .iter()
                    .any(|ua| ua.name.1 == sn::user_attributes::NO_AUTO_BOUND)
                    || !add_implicit_upper_bound
                {
                    tparam
                } else {
                    let pos = &tparam.name.0;
                    let hint = aast::Hint(
                        pos.clone(),
                        Box::new(aast::Hint_::Happly(
                            ast_defs::Id(pos.clone(), sn::classes::SUPPORT_DYN.to_string()),
                            vec![aast::Hint(pos.clone(), Box::new(aast::Hint_::Hmixed))],
                        )),
                    );
                    let mut tp_constraints = vec![(ConstraintKind::ConstraintAs, hint)];
                    tp_constraints.extend(tparam.constraints.iter().cloned());
                    nast::Tparam {
                        constraints: tp_constraints,
                        ..tparam
                    }
                }
            })
            .collect();
        phase::localize_and_add_ast_generic_parameters_and_where_constraints(
            &mut tenv,
            true,
            &tparams,
            &[],
        )
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, &tenv)
    }
    let env = Env {
        typedef_tparams: vec![],
        tenv: tenv.clone(),
        in_interface: false,
    };
    let errs = {
        let errs2 = check_splat_is_tuple(&env, &f.params);
        let errs1 = fun_utils::check_params(false, &f.params);
        append(errs1, errs2)
    };
    for err in &errs {
        typing_error_utils::add_typing_error(err, &tenv)
    }
    let denotability_errors =
        callable_type_hint_shape_splat_field_denotability_errors(&env, &f.ret);
    let params_errs = fun_params(&env, &f.params);
    let ret_errs = type_hint(true, &env, &f.ret);
    append(ret_errs, append(params_errs, denotability_errors))
}

pub fn fun_def(tenv: &TEnv, fd: &nast::FunDef) -> Vec<typing_error::T> {
    // Add type parameters to typing environment and localize the bounds
    // and where constraints
    let mut tenv = tenv.clone();
    let ty_err_opt = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
        &mut tenv,
        true,
        &fd.tparams,
        &fd.where_constraints,
    );
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, &tenv)
    }
    let env = Env {
        typedef_tparams: vec![],
        tenv: tenv.clone(),
        in_interface: false,
    };
    let where_errs = where_constrs(&env, &fd.where_constraints);
    let fun_errs = fun_(&tenv, &fd.fun);
    let tparams_errs = tparams(&env, &fd.tparams);
    append(tparams_errs, append(fun_errs, where_errs))
}

fn enum_opt(
    base_is_enforceable: Option<bool>,
    env: &Env,
    e: Option<&nast::Enum_>,
) -> Vec<typing_error::T> {
    let base_is_enforceable = base_is_enforceable.unwrap_or(false);
    let f = |aast::Enum_ {
                 base: e_base,
                 constraint: e_constraint,
                 ..
             }: &nast::Enum_| {
        let base_check = if base_is_enforceable {
            enforceable_type_alias_check(env, true)
        } else {
            CheckReason::No
        };
        let errs2 = hint_opt(None, Some(CheckReason::No), env, e_constraint.as_ref());
        let errs1 = hint(None, Some(base_check), env, e_base);
        append(errs1, errs2)
    };
    match e {
        None => vec![],
        Some(e) => f(e),
    }
}

fn const_(env: &Env, cc: &nast::ClassConst) -> Vec<typing_error::T> {
    hint_opt(None, Some(CheckReason::No), env, cc.type_.as_ref())
}

fn consts(env: &Env, cs: &[nast::ClassConst]) -> Vec<typing_error::T> {
    cs.iter().flat_map(|c| const_(env, c)).collect()
}

fn typeconsts(
    env: &Env,
    tcs: &[nast::ClassTypeconstDef],
    cls_name: &aast::Sid,
) -> Vec<typing_error::T> {
    let cls = env::get_class(&env.tenv, &cls_name.1);
    let get_class_const = |const_sid: &aast::Sid| -> ClassConst {
        match &cls {
            decl_entry::T::Found(cls) => match env::get_typeconst(&env.tenv, cls, &const_sid.1) {
                Some(ttc) => ClassConst::Found(ttc),
                None => ClassConst::Missing,
            },
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => ClassConst::Skip,
        }
    };
    let f = |tconst: &nast::ClassTypeconstDef| {
        let should_check_package_boundary = if !env::package_allow_all_tconst_violations(&env.tenv)
        {
            CheckReason::Yes(TargetSymbolSpec::TypeConst)
        } else {
            match get_class_const(&tconst.name) {
                ClassConst::Found(ttc) => match &ttc.reifiable {
                    None => CheckReason::No,
                    Some(reifiable_attr_pos) => {
                        CheckReason::Yes(TargetSymbolSpec::ReifiableTypeConst {
                            reifiable_attr_pos: reifiable_attr_pos.clone().to_oxidized(),
                            tconst_name: ttc.name.id_ref().as_str().to_string(),
                        })
                    }
                },
                ClassConst::Missing | ClassConst::Skip => CheckReason::No,
            }
        };
        match &tconst.kind {
            aast::ClassTypeconst::TCAbstract(aast::ClassAbstractTypeconst {
                as_constraint: c_atc_as_constraint,
                super_constraint: c_atc_super_constraint,
                default: c_atc_default,
            }) => {
                let errs3 = hint_opt(
                    None,
                    Some(should_check_package_boundary.clone()),
                    env,
                    c_atc_default.as_ref(),
                );
                let errs2 = hint_opt(
                    None,
                    Some(should_check_package_boundary.clone()),
                    env,
                    c_atc_super_constraint.as_ref(),
                );
                let errs1 = hint_opt(
                    None,
                    Some(should_check_package_boundary),
                    env,
                    c_atc_as_constraint.as_ref(),
                );
                append(errs1, append(errs2, errs3))
            }
            aast::ClassTypeconst::TCConcrete(aast::ClassConcreteTypeconst { c_tc_type }) => {
                hint(None, Some(should_check_package_boundary), env, c_tc_type)
            }
        }
    };
    tcs.iter().flat_map(f).collect()
}

/// Treat private or internal class members as internal
fn at_least_internal(vis: aast::Visibility) -> bool {
    match vis {
        aast::Visibility::Internal
        | aast::Visibility::Private
        | aast::Visibility::ProtectedInternal => true,
        aast::Visibility::Protected | aast::Visibility::Public => false,
    }
}

fn class_vars(env: &Env, cvs: &[&nast::ClassVar]) -> Vec<typing_error::T> {
    let f = |cv: &&nast::ClassVar| {
        let mut tenv = env.tenv.clone();
        env::set_internal(&mut tenv, at_least_internal(cv.visibility));
        let env = Env {
            tenv,
            ..env.clone()
        };
        type_hint(true, &env, &cv.type_)
    };
    cvs.iter().flat_map(f).collect()
}

fn method_(env: &Env, m: &nast::Method_) -> Vec<typing_error::T> {
    // `__RequirePackage` on a method grants signature-time access to its
    // packages, mirroring what `Typing_class` does for the method body.
    let mut tenv = env.tenv.clone();
    env::assert_packages_loaded_from_attr(&mut tenv, &m.user_attributes.0);
    // Add method type parameters to environment and localize the bounds
    // and where constraints
    let ty_err_opt = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
        &mut tenv,
        true,
        &m.tparams,
        &m.where_constraints,
    );
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, &tenv)
    }
    // Only throw hack error if class and method are both public
    let internal = at_least_internal(m.visibility) || env::get_internal(&tenv);
    env::set_internal(&mut tenv, internal);

    let env = &Env {
        tenv,
        ..env.clone()
    };
    let denotability_errors =
        callable_type_hint_shape_splat_field_denotability_errors(env, &m.ret);
    let ret_errs = append(type_hint(true, env, &m.ret), denotability_errors);
    let where_errs = where_constrs(env, &m.where_constraints);
    let tparams_errs = tparams(env, &m.tparams);
    let params_errs = fun_params(env, &m.params);
    let splat_errs = check_splat_is_tuple(env, &m.params);
    let errs = append(where_errs, ret_errs);
    let errs = append(tparams_errs, errs);
    let errs = append(params_errs, errs);
    append(splat_errs, errs)
}

fn methods(env: &Env, ms: &[&nast::Method_]) -> Vec<typing_error::T> {
    ms.iter().flat_map(|m| method_(env, m)).collect()
}

fn method_opt(env: &Env, m: Option<&nast::Method_>) -> Vec<typing_error::T> {
    match m {
        None => vec![],
        Some(m) => method_(env, m),
    }
}

fn hint_no_kind_check(env: &Env, h: &aast::Hint) -> Vec<typing_error::T> {
    hint_(true, true, env, h)
}

pub fn class_(tenv: &TEnv, c: &nast::Class_) -> Vec<typing_error::T> {
    let env = Env {
        typedef_tparams: vec![],
        tenv: tenv.clone(),
        in_interface: ast_defs::is_c_interface(c.kind),
    };
    let aast::Class_ {
        span: _,
        annotation: _,
        mode: _,
        final_: _,
        is_xhp: _,
        has_xhp_keyword: _,
        kind: c_kind,
        name: c_name,
        tparams: c_tparams,
        extends: c_extends,
        uses: c_uses,
        xhp_category: _,
        reqs: c_reqs,
        implements: c_implements,
        consts: c_consts,
        typeconsts: c_typeconsts,
        vars: c_vars,
        methods: c_methods,
        xhp_children: _,
        xhp_attrs: _,
        // Collapsed into c_vars during Naming
        xhp_attr_uses: _,
        // These represent `attribute :a;` declarations, and it is a parse error
        // to write `attribute :a<string>`
        namespace: _,
        user_attributes: _,
        file_attributes: _,
        enum_: c_enum,
        doc_comment: _,
        emit_id: _,
        internal: _,
        module: _,
        docs_url: _,
        package: _,
    } = c;

    // Add type parameters to typing environment and localize the bounds
    let mut tenv = tenv.clone();
    let ty_err_opt = {
        let req_class_constraints: Vec<aast::WhereConstraintHint> = c_reqs
            .iter()
            .filter_map(|req| match req {
                aast::ClassReq(t, aast::RequireKind::RequireClass) => {
                    let pos = t.0.clone();
                    Some(aast::WhereConstraintHint(
                        aast::Hint(pos, Box::new(aast::Hint_::Hthis)),
                        ConstraintKind::ConstraintEq,
                        t.clone(),
                    ))
                }
                _ => None,
            })
            .collect();
        phase::localize_and_add_ast_generic_parameters_and_where_constraints(
            &mut tenv,
            true,
            c_tparams,
            &req_class_constraints,
        )
    };
    if let Some(err) = &ty_err_opt {
        typing_error_utils::add_typing_error(err, &tenv)
    }
    let env = &Env { tenv, ..env };
    let (c_constructor, c_statics, c_methods) = crate::aast::split_methods(c_methods);
    let (c_static_vars, c_vars) = crate::aast::split_vars(c_vars);
    // The elements of the list are computed from the last one to the first.
    let mut errss: Vec<Vec<typing_error::T>> = vec![
        // Regular enums enforce the base at runtime; enum classes do not.
        enum_opt(Some(ast_defs::is_c_enum(*c_kind)), env, c_enum.as_ref()),
        methods(env, &c_methods),
        methods(env, &c_statics),
        consts(env, c_consts),
        class_vars(env, &c_vars),
        class_vars(env, &c_static_vars),
        typeconsts(env, c_typeconsts, c_name),
        requirements(env, c_reqs),
        hints(Some(false), env, c_uses),
        // But for interfaces and trait use, we allow internal
        hints(Some(false), env, c_implements),
        // Extends clause must be checked, so that we reject public classes extending internal ones
        hints(Some(true), env, c_extends),
        tparams(env, c_tparams),
        if !ast_defs::is_c_interface(*c_kind) {
            method_opt(env, c_constructor)
        } else {
            vec![]
        },
    ];
    errss.reverse();
    errss.into_iter().flatten().collect()
}

pub fn typedef(tenv: &TEnv, t: &nast::Typedef) -> Vec<typing_error::T> {
    let aast::Typedef {
        tparams: t_tparams,
        annotation: _,
        name: t_name,
        as_constraint: t_as_constraint,
        super_constraint: t_super_constraint,
        assignment: t_assignment,
        runtime_type: _,
        mode: _,
        namespace: _,
        user_attributes: _,
        span: _,
        emit_id: _,
        is_ctx: _,
        file_attributes: _,
        internal: _,
        module: _,
        docs_url: _,
        doc_comment: _,
        package: _,
    } = t;
    let (
        should_check_internal_signature,
        should_check_package_boundary,
        typedef_tparams,
        hint_constraints_pairs,
    ): (
        bool,
        CheckReason,
        Vec<nast::Tparam>,
        Vec<(&aast::Hint, &[aast::WhereConstraintHint])>,
    ) = match t_assignment {
        // We only need to check that the type alias as a public API if it's transparent, since
        // an opaque type alias is inherently internal
        // Since type aliases cannot have constraints we shouldn't check
        // if its type params satisfy the constraints of any tapply it
        // references.
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: aast::TypedefVisibility::Transparent,
            hint: tvh_hint,
        }) => (
            true,
            CheckReason::Yes(TargetSymbolSpec::TransparentTypeAlias),
            t_tparams.clone(),
            vec![(tvh_hint, &[][..])],
        ),
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: _,
            hint: tvh_hint,
        }) => (false, CheckReason::No, vec![], vec![(tvh_hint, &[][..])]),
        aast::TypedefAssignment::CaseType(variant, variants) => {
            let hint_constraints_pairs = std::iter::once(variant)
                .chain(variants.iter())
                .map(|v| (&v.hint, &v.where_constraints[..]))
                .collect();
            (
                false,
                CheckReason::Yes(TargetSymbolSpec::CaseType),
                vec![],
                hint_constraints_pairs,
            )
        }
    };
    // We don't allow constraints on typdef parameters, but we still
    // need to record their kinds in the generic var environment
    let tenv_with_typedef_tparams = {
        let mut env = tenv.clone();
        let where_constraints = [];
        let ty_err_opt = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
            &mut env,
            true,
            t_tparams,
            &where_constraints,
        );
        if let Some(err) = &ty_err_opt {
            typing_error_utils::add_typing_error(err, &env)
        }
        env
    };

    // For typdefs, we do want to do the simple kind checks on the body
    // (e.g., arities match up), but no constraint checks. We need to check the
    // kinds of typedefs separately, because check_happly replaces all the generic
    // parameters of typedefs by Tany, which makes the kind check moot
    //
    // `maybe`: we always check the constraints for internal types, so treat in_signature:true
    if let Some(h) = t_as_constraint {
        typing_type_integrity::check_hint_integrity(
            true,
            should_check_package_boundary.clone(),
            &tenv_with_typedef_tparams,
            h,
        )
    }
    if let Some(h) = t_super_constraint {
        typing_type_integrity::check_hint_integrity(
            true,
            should_check_package_boundary.clone(),
            &tenv_with_typedef_tparams,
            h,
        )
    }
    // TODO check kinded-ness for constraints too
    for (hint, _constraints) in &hint_constraints_pairs {
        typing_type_integrity::check_hint_integrity(
            should_check_internal_signature,
            should_check_package_boundary.clone(),
            &tenv_with_typedef_tparams,
            hint,
        )
    }
    let env = &Env {
        typedef_tparams: typedef_tparams.clone(),
        tenv: tenv.clone(),
        in_interface: false,
    };
    // We checked the kinds already above.
    let pairs_errs: Vec<typing_error::T> = hint_constraints_pairs
        .iter()
        .flat_map(|(hint, constraints)| {
            let where_constraints =
                typing_case_type_utils::filter_where_clauses_with_recursive_mentions(
                    tenv,
                    t_name,
                    constraints,
                );
            let mut tenv = tenv.clone();
            // The error is dropped.
            let _err =
                phase::localize_and_add_where_constraints(&mut tenv, true, &where_constraints);
            let env = &Env {
                typedef_tparams: typedef_tparams.clone(),
                tenv,
                in_interface: false,
            };
            let errs2 = where_constrs(env, constraints);
            let errs1 = hint_no_kind_check(env, hint);
            append(errs1, errs2)
        })
        .collect();
    let super_errs = match t_super_constraint {
        None => vec![],
        Some(h) => hint_no_kind_check(env, h),
    };
    let as_errs = match t_as_constraint {
        None => vec![],
        Some(h) => hint_no_kind_check(env, h),
    };
    append(as_errs, append(super_errs, pairs_errs))
}

pub fn global_constant(tenv: &TEnv, gconst: &nast::Gconst) -> Vec<typing_error::T> {
    let env = Env {
        typedef_tparams: vec![],
        tenv: tenv.clone(),
        in_interface: false,
    };
    let aast::Gconst {
        annotation: _,
        mode: _,
        name: _,
        type_: cst_type,
        value: _,
        namespace: _,
        span: _,
        emit_id: _,
        module: _,
        package: _,
    } = gconst;
    hint_opt(None, Some(CheckReason::No), &env, cst_type.as_ref())
}

/// The second `hint` of the OCaml (see the module documentation).
fn hint_tenv(
    should_check_package_boundary: Option<CheckReason>,
    tenv: &TEnv,
    h: &aast::Hint,
) -> Vec<typing_error::T> {
    let should_check_package_boundary =
        should_check_package_boundary.unwrap_or(CheckReason::Yes(TargetSymbolSpec::Symbol));
    let env = Env {
        typedef_tparams: vec![],
        tenv: tenv.clone(),
        in_interface: false,
    };
    hint(Some(false), Some(should_check_package_boundary), &env, h)
}

/// Check well-formedness of type hints. See .mli file for more.
///
/// Check type wellformedness of any hint appearing in this
/// expression, e.g. parameter type hints of lambda expressions,
/// hints in `is` and `as` expressions, etc.
pub fn expr(tenv: &TEnv, e: &nast::Expr) -> Vec<typing_error::T> {
    let aast::Expr((), _p, e) = e;
    // We don't recurse on expressions here because this is called by Typing.expr
    match e {
        aast::Expr_::Is(e_h) => hint_tenv(Some(CheckReason::No), tenv, &e_h.1),
        aast::Expr_::As(as_) => {
            let aast::As_ {
                expr: _,
                hint: h,
                is_nullable: _,
                enforce_deep: _,
            } = &**as_;
            hint_tenv(Some(CheckReason::No), tenv, h)
        }
        aast::Expr_::Upcast(e_h) => hint_tenv(None, tenv, &e_h.1),
        aast::Expr_::Cast(h_e) => hint_tenv(None, tenv, &h_e.0),
        aast::Expr_::New(new) => {
            let (_, hl, _, _, _) = &**new;
            hl.iter()
                // ignore package checks on targs
                .flat_map(|aast::Targ(_, h)| hint_tenv(Some(CheckReason::No), tenv, h))
                .collect()
        }
        aast::Expr_::Call(call) => call
            .targs
            .iter()
            // ignore package checks on targs
            .flat_map(|aast::Targ(_, h)| hint_tenv(Some(CheckReason::No), tenv, h))
            .collect(),
        aast::Expr_::Lfun(f_) => fun_(tenv, &f_.0),
        aast::Expr_::Efun(ef) => fun_(tenv, &ef.fun),
        aast::Expr_::ExpressionTree(_)
        | aast::Expr_::Invalid(_)
        | aast::Expr_::Shape(_)
        | aast::Expr_::ValCollection(_)
        | aast::Expr_::KeyValCollection(_)
        | aast::Expr_::Null
        | aast::Expr_::This
        | aast::Expr_::True
        | aast::Expr_::False
        | aast::Expr_::Omitted
        | aast::Expr_::Id(_)
        | aast::Expr_::Lvar(_)
        | aast::Expr_::Dollardollar(_)
        | aast::Expr_::Clone(_)
        | aast::Expr_::ArrayGet(_)
        | aast::Expr_::ObjGet(_)
        | aast::Expr_::ClassGet(_)
        | aast::Expr_::ClassConst(_)
        | aast::Expr_::FunctionPointer(_)
        | aast::Expr_::Int(_)
        | aast::Expr_::Float(_)
        | aast::Expr_::String(_)
        | aast::Expr_::String2(_)
        | aast::Expr_::PrefixedString(_)
        | aast::Expr_::Yield(_)
        | aast::Expr_::Await(_)
        | aast::Expr_::Delay(_)
        | aast::Expr_::ReadonlyExpr(_)
        | aast::Expr_::Tuple(_)
        | aast::Expr_::List(_)
        | aast::Expr_::Unop(_)
        | aast::Expr_::Binop(_)
        | aast::Expr_::Assign(_)
        | aast::Expr_::Pipe(_)
        | aast::Expr_::Eif(_)
        | aast::Expr_::Xml(_)
        | aast::Expr_::Import(_)
        | aast::Expr_::Collection(_)
        | aast::Expr_::Lplaceholder(_)
        | aast::Expr_::MethodCaller(_)
        | aast::Expr_::Pair(_)
        | aast::Expr_::EnumClassLabel(_)
        | aast::Expr_::ETSplice(_)
        | aast::Expr_::Hole(_)
        | aast::Expr_::Package(_)
        | aast::Expr_::Nameof(_)
        | aast::Expr_::DestructureShape(_)
        | aast::Expr_::DestructureTuple(_) => vec![],
    }
}

/// Check well-formedness of type hints. See .mli file for more.
///
/// This function is not used but ensures we don't forget to
/// extend this module for future top-level definitions we may add.
fn _toplevel_def(tenv: &TEnv, def: &nast::Def) -> Vec<typing_error::T> {
    match def {
        aast::Def::Fun(f) => {
            let aast::FunDef {
                namespace: _,
                mode: _,
                file_attributes: _,
                fun: fd_fun,
                name: _,
                internal: _,
                module: _,
                tparams: _,
                where_constraints: _,
                package: _,
            } = &**f;

            fun_(tenv, fd_fun)
        }
        aast::Def::Constant(gc) => global_constant(tenv, gc),
        aast::Def::Typedef(td) => typedef(tenv, td),
        aast::Def::Class(c) => class_(tenv, c),
        aast::Def::ClassAlias(_)
        | aast::Def::Stmt(_)
        | aast::Def::Namespace(_)
        | aast::Def::NamespaceUse(_)
        | aast::Def::SetNamespaceEnv(_)
        | aast::Def::FileAttributes(_)
        | aast::Def::SetModule(_)
        | aast::Def::Module(_) => vec![],
    }
}
