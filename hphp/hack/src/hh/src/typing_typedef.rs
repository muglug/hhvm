// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_typedef.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::decl_counters;
use crate::decl_hint;
use crate::decl_utils;
use crate::tast;
use crate::type_expansions;
use crate::type_expansions::expandable;
use crate::typing_case_type_check;
use crate::typing_case_type_utils;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::VisibilityBehavior;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env as env;
use crate::typing_env_from_def as env_from_def;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_phase as phase;
use crate::typing_type_wellformedness;
use crate::typing_variance;

/// `Option.merge ~f:Typing_error.both`
fn merge_errors(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2) {
        (None, e2) => e2,
        (e1, None) => e1,
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
    }
}

/// `Option.iter ~f:(Typing_error_utils.add_typing_error ~env)`
fn add_typing_error_opt(env: &Env, err: &Option<typing_error::T>) {
    if let Some(err) = err {
        typing_error_utils::add_typing_error(err, env)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintDirection {
    As,
    Super,
}

pub mod constraints {
    use super::*;

    fn report_cyclic_constraint(
        env: &Env,
        cycles: &[type_expansions::CycleReporter],
        cstr_direction: ConstraintDirection,
    ) {
        match cstr_direction {
            ConstraintDirection::As => add_typing_error_opt(env, &type_expansions::report(cycles)),
            ConstraintDirection::Super => {}
        }
    }

    fn check_subtype_constraint(
        env: &mut Env,
        ty: Ty,
        cstr_ty: Ty,
        t_pos: &Pos,
        cstr_direction: ConstraintDirection,
    ) -> Option<typing_error::T> {
        let (ty_sub, ty_super) = match cstr_direction {
            ConstraintDirection::As => (ty, cstr_ty),
            ConstraintDirection::Super => (cstr_ty, ty),
        };
        crate::typing_ops::sub_type(
            t_pos.clone(),
            crate::typing_reason::Ureason::URnewtypeCstr,
            env,
            ty_sub,
            ty_super,
            typing_error::callback::newtype_alias_must_satisfy_constraint(),
        )
    }

    /// [check env tcstr constraint_direction name ty] checks that
    /// `ty <: tcstr` or `tcstr <: ty` depending on [constraint_direction]
    pub fn check(
        env: &mut Env,
        tcstr: Option<&aast::Hint>,
        cstr_direction: ConstraintDirection,
        (t_pos, t_name): (&Pos, &str),
        ty: &Ty,
    ) -> Option<typing_error::T> {
        match tcstr {
            Some(tcstr) => {
                let (ty_err_opt1, cycles, cstr_ty) = phase::localize_hint_no_subst_report_cycles(
                    env,
                    false,
                    (t_pos.clone(), expandable::T::TypeAlias(t_name.to_string())),
                    tcstr,
                );
                report_cyclic_constraint(env, &cycles, cstr_direction);
                let ty_err_opt2 =
                    check_subtype_constraint(env, ty.clone(), cstr_ty, t_pos, cstr_direction);
                merge_errors(ty_err_opt1, ty_err_opt2)
            }
            _ => None,
        }
    }
}

/// Checks that variants of a case type are disjoint
fn check_overlapping(
    env: &mut Env,
    (t_pos, t_name): (&Pos, &str),
    hints: &[&aast::Hint],
) -> Option<typing_error::T> {
    // The inner `check_overlapping` is given the environment
    // `check_overlapping` is called with, not the one `data_type_from_hint`
    // returns.
    let env0 = env.clone();
    // Given two types with their associated data types, check if
    // the data types overlap. If they do report an error
    let check_overlapping =
        |data_type1: &typing_case_type_check::RuntimeDataType,
         acc: &mut Vec<typing_error::T>,
         data_type2: &typing_case_type_check::RuntimeDataType| {
            match typing_case_type_check::check_overlapping(
                &env0,
                t_pos.clone(),
                t_name.to_string(),
                data_type1,
                data_type2,
            ) {
                None => {}
                Some(err) => acc.push(typing_error::casetype(err)),
            }
        };

    // We check for overlaps pairwise between each variant type in the union
    //
    // `acc` is a cons list in OCaml (the last error found is its head): the
    // errors are pushed here, and the list is reversed at the end.
    let pairwise_check =
        |acc: &mut Vec<typing_error::T>, data_types: &[typing_case_type_check::RuntimeDataType]| {
            for (i, data_type) in data_types.iter().enumerate() {
                for other in &data_types[i + 1..] {
                    check_overlapping(data_type, acc, other)
                }
            }
        };
    let data_types: Vec<typing_case_type_check::RuntimeDataType> = hints
        .iter()
        .map(|hint| typing_case_type_check::data_type_from_hint(false, env, hint))
        .collect();
    let mut acc = vec![];
    pairwise_check(&mut acc, &data_types);
    acc.reverse();
    typing_error::multiple_opt(acc)
}

/// Forbid recursive type aliases like `A = A` and `A = ?A`
/// (modulo indirection via other type aliases),
/// something defined as contractiveness in Pierce's Types and Programming Languages.
/// Note that we'd also want to forbid any recursion under union like `A = A | int`,
/// but these are already forbidden by `check_overlapping`, so left to check
/// are A = A and A = ?A.
fn check_invalid_recursive_case_type(
    env: &mut Env,
    (pos, name): (&Pos, &str),
    hints: &[&aast::Hint],
) -> Option<typing_error::T> {
    fn is_invalid_single_type(name: &str, ty: &Ty) -> bool {
        match get_node(ty) {
            Ty_::Tnewtype(id, _targs, _bound) => name == id,
            Ty_::Toption(ty) => is_invalid_single_type(name, ty),
            Ty_::Taccess(_)
            | Ty_::Tgeneric(_)
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::TclassPtr(_)
            | Ty_::Tshape(_)
            | Ty_::Tnonnull
            | Ty_::TvecOrDict(..)
            | Ty_::Tdynamic(_)
            | Ty_::Tvar(_)
            | Ty_::Tclass(..)
            | Ty_::Tany(_) => false,
            Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
                tyl.iter().any(|ty| is_invalid_single_type(name, ty))
            }
            Ty_::Tdependent(..) => panic!("Unexpected type Tdependent out of localizing a hint"),
            Ty_::Tneg(_) => panic!("Unexpected type Tneg out of localizing a hint"),
            Ty_::Tlabel(_) => panic!("Unexpected type Tlabel out of localizing a hint"),
        }
    }
    match hints {
        [hint] => {
            let ty = decl_hint::hint(&env.decl_env, hint);
            let (_err, ty) = phase::localize(
                &ExpandEnv {
                    visibility_behavior: VisibilityBehavior::AlwaysExpandNewtype,
                    type_expansions: type_expansions::empty_w_cycle_report(Some((
                        pos.clone(),
                        expandable::T::TypeAlias(name.to_string()),
                    ))),
                    ..empty_expand_env()
                },
                env,
                &ty,
            );
            if is_invalid_single_type(name, &ty) {
                Some(typing_error::casetype(
                    primary::casetype::T::Invalid_recursive {
                        pos: pos.clone(),
                        name: name.to_string(),
                    },
                ))
            } else {
                None
            }
        }
        _ => {
            // Recursive types like `A = A | int` are already forbidden
            // by `check_overlapping`, so we skip the check.
            None
        }
    }
}

/// Checks that variants of a case type are disjoint, and rule out other invalid recursive case types
fn casetype_def(env: &mut Env, typedef: &nast::Typedef) {
    let aast::Typedef {
        annotation: (),
        name: t_name,
        tparams: _,
        as_constraint: _,
        super_constraint: _,
        assignment: t_assignment,
        runtime_type: _,
        user_attributes: _,
        mode: _,
        namespace: _,
        span: _,
        emit_id: _,
        is_ctx: _,
        file_attributes: _,
        internal: _,
        module: _,
        docs_url: _,
        doc_comment: _,
        package: _,
    } = typedef;
    match t_assignment {
        aast::TypedefAssignment::SimpleTypeDef(_) => {}
        aast::TypedefAssignment::CaseType(variant, variants) => {
            let hints: Vec<&aast::Hint> = std::iter::once(variant)
                .chain(variants.iter())
                .map(|v| &v.hint)
                .collect();
            let t_name = (&t_name.0, t_name.1.as_str());
            let err1 = check_overlapping(env, t_name, &hints);
            let err2 = check_invalid_recursive_case_type(env, t_name, &hints);
            add_typing_error_opt(env, &err1);
            add_typing_error_opt(env, &err2);
        }
    }
}

fn check_cycles(
    env: &mut Env,
    (t_pos, t_name): (&Pos, &str),
    t_assignment: &aast::TypedefAssignment,
    hints: &[&aast::Hint],
) {
    let case_type_root = match t_assignment {
        aast::TypedefAssignment::SimpleTypeDef(_) => None,
        aast::TypedefAssignment::CaseType(..) => Some(t_name.to_string()),
    };
    let mut cycles: Vec<type_expansions::CycleReporter> = vec![];
    for hint in hints {
        let (_ty_err_opt, new_cycles, _ty) = phase::localize_typedef_structure(
            env,
            true,
            (t_pos.clone(), expandable::T::TypeAlias(t_name.to_string())),
            case_type_root.clone(),
            hint,
        );
        // `new_cycles @ cycles`
        let mut all = new_cycles;
        all.append(&mut cycles);
        cycles = all;
    }
    if let Some(e) = type_expansions::report(&cycles) {
        let e = match t_assignment {
            aast::TypedefAssignment::SimpleTypeDef(_) => e,
            aast::TypedefAssignment::CaseType(..) => {
                typing_error::with_code(e, oxidized::error_codes::Typing::RecursiveCaseType)
            }
        };
        typing_error_utils::add_typing_error(&e, env)
    }
}

fn check_where_clauses_with_recursive_mentions(
    env: &Env,
    t_name: &aast::Sid,
    where_constraints: &[aast::WhereConstraintHint],
) {
    let ast_defs::Id(pos, name) = t_name;
    let report = |(_wc, decl_tyl): &(
        aast::WhereConstraintHint,
        Vec<crate::typing_defs_core::DeclTy>,
    )| {
        if !decl_tyl.is_empty() {
            let mentions = decl_tyl
                .iter()
                .map(|decl_ty| Pos::from(decl_utils::get_pos(decl_ty)))
                .collect();
            typing_error_utils::add_typing_error(
                &typing_error::casetype(primary::casetype::T::Recursive_where_clause {
                    pos: pos.clone(),
                    name: name.clone(),
                    mentions,
                }),
                env,
            )
        }
    };
    let pairs = typing_case_type_utils::find_where_clause_recursive_mentions(
        env,
        t_name,
        where_constraints,
    );
    for pair in &pairs {
        report(pair)
    }
}

/// This is a helper for [Typing_toplevel.typedef_def]. Call that instead.
pub fn typedef_def(ctx: &Arc<Ctx>, typedef: &nast::Typedef) -> tast::Typedef {
    let mut env = env_from_def::typedef_env(
        Some(decl_counters::Origin::TopLevel),
        Arc::clone(ctx),
        typedef,
    );
    let env = &mut env;
    let aast::Typedef {
        annotation: (),
        name: t_name,
        tparams: t_tparams,
        as_constraint: t_as_constraint,
        super_constraint: t_super_constraint,
        assignment: t_assignment,
        runtime_type: t_runtime_type,
        user_attributes: t_user_attributes,
        mode: t_mode,
        namespace: t_namespace,
        span: t_span,
        emit_id: t_emit_id,
        is_ctx: t_is_ctx,
        file_attributes: t_file_attributes,
        internal: t_internal,
        module: t_module,
        docs_url: t_docs_url,
        doc_comment: t_doc_comment,
        package: t_package,
    } = typedef;
    env::set_current_module(env, t_module.clone());
    env::set_internal(env, *t_internal);
    env::set_current_package_membership(env, t_package.clone());
    let restore_pos = {
        let ast_defs::Id(pos, _) = t_name;
        env::set_inference_env_pos(env, Some(pos.clone()))
    };
    let file_attributes = crate::typing::file_attributes(env, t_file_attributes);
    // `do_report_cycles` is a function of the environment, applied below.
    let (do_report_cycles, hint_constraints_pairs): (
        Box<dyn Fn(&Env) -> bool>,
        Vec<(&aast::Hint, Option<&Vec<aast::WhereConstraintHint>>)>,
    ) = match t_assignment {
        aast::TypedefAssignment::SimpleTypeDef(aast::TypedefVisibilityAndHint {
            vis: _,
            hint: tvh_hint,
        }) => (Box::new(|_env: &Env| true), vec![(tvh_hint, None)]),
        aast::TypedefAssignment::CaseType(variant, variants) => (
            Box::new(|env: &Env| {
                let recursive_case_types = |env: &Env| env::get_tcopt(env).recursive_case_types;
                !recursive_case_types(env)
            }),
            std::iter::once(variant)
                .chain(variants.iter())
                .map(|v| (&v.hint, Some(&v.where_constraints)))
                .collect(),
        ),
    };
    let ty_err_opt1 = phase::localize_and_add_ast_generic_parameters_and_where_constraints(
        env,
        false,
        t_tparams,
        &[],
    );
    add_typing_error_opt(env, &ty_err_opt1);
    for err in typing_type_wellformedness::typedef(env, typedef) {
        typing_error_utils::add_typing_error(&err, env)
    }
    env::make_depend_on_current_module(env);
    typing_variance::typedef(env, typedef);

    if do_report_cycles(env) {
        let hints: Vec<&aast::Hint> = hint_constraints_pairs.iter().map(|(h, _)| *h).collect();
        check_cycles(env, (&t_name.0, t_name.1.as_str()), t_assignment, &hints)
    }
    for constraints in hint_constraints_pairs.iter().filter_map(|(_, c)| *c) {
        check_where_clauses_with_recursive_mentions(env, t_name, constraints)
    }
    let check_variant =
        |env: &mut Env,
         (hint, constraints_opt): &(&aast::Hint, Option<&Vec<aast::WhereConstraintHint>>)| {
            let (localize_ty_err_opt, ty) = phase::localize_hint_no_subst(env, false, hint);
            add_typing_error_opt(env, &localize_ty_err_opt);
            let mut env_for_variant = match constraints_opt {
                None => env.clone(),
                Some(constraints) => {
                    let mut env = env.clone();
                    let constraints =
                        typing_case_type_utils::filter_where_clauses_with_recursive_mentions(
                            &env,
                            t_name,
                            constraints,
                        );
                    let _err =
                        phase::localize_and_add_where_constraints(&mut env, true, &constraints);
                    env
                }
            };
            let t_name = (&t_name.0, t_name.1.as_str());
            let t_as_constraint_err_opt = constraints::check(
                &mut env_for_variant,
                t_as_constraint.as_ref(),
                ConstraintDirection::As,
                t_name,
                &ty,
            );
            add_typing_error_opt(&env_for_variant, &t_as_constraint_err_opt);
            // The errors of the second check are reported in the environment
            // the first check returned.
            let env_for_variant_after_as = env_for_variant.clone();
            let t_super_constraint_err_opt = constraints::check(
                &mut env_for_variant,
                t_super_constraint.as_ref(),
                ConstraintDirection::Super,
                t_name,
                &ty,
            );
            add_typing_error_opt(&env_for_variant_after_as, &t_super_constraint_err_opt);
            // we return env instead of env_for_variant because env_for_variant contains
            // assumptions from the where clause which we do not want to assume for
            // other variants
        };
    for pair in &hint_constraints_pairs {
        check_variant(env, pair)
    }
    casetype_def(env, typedef);
    let user_attributes = crate::typing::attributes_check_def(
        env,
        sn::attribute_kinds::TYPE_ALIAS,
        &t_user_attributes.0,
    );
    let tparams: Vec<tast::Tparam> = t_tparams
        .iter()
        .map(|tp| crate::typing::type_param(env, tp))
        .collect();
    restore_pos(env);
    aast::Typedef {
        annotation: env::save(&env::get_tpenv(env), env),
        name: t_name.clone(),
        mode: *t_mode,
        user_attributes: aast::UserAttributes(user_attributes),
        as_constraint: t_as_constraint.clone(),
        super_constraint: t_super_constraint.clone(),
        assignment: t_assignment.clone(),
        runtime_type: t_runtime_type.clone(),
        tparams,
        namespace: t_namespace.clone(),
        span: t_span.clone(),
        emit_id: t_emit_id.clone(),
        is_ctx: *t_is_ctx,
        file_attributes,
        internal: *t_internal,
        module: t_module.clone(),
        docs_url: t_docs_url.clone(),
        doc_comment: t_doc_comment.clone(),
        package: t_package.clone(),
    }
}
