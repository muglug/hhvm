// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_requirements.ml`. See `hh/PORTING.md`.
//!
//! A requirement (`Pos_or_decl.t * decl_ty`) is a `typing_defs::Requirement`
//! (`pos`, `ty`).

use oxidized::ast_defs::ClassishKind;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ast_defs;
use crate::decl_entry;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::typing_defs::Requirement;
use crate::typing_defs_core::DeclTy;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_phase;
use crate::typing_utils as tutils;

/// `Typing_defs.get_pos` of a declared type.
fn get_pos(ty: &DeclTy) -> PosOrDecl {
    PosOrDecl::from(decl_utils::get_pos(ty))
}

/// Only applied to classes. Checks that all the requirements of the traits
/// and interfaces it uses are satisfied.
fn check_fulfillment(
    env: &mut Env,
    class_pos: &Pos,
    tc: &cls::T,
    (is_strict, req): (bool, &Requirement),
) {
    let Requirement {
        pos: trait_pos,
        ty: req_ty,
    } = req;
    let trait_pos = PosOrDecl::from(trait_pos.clone());
    match tutils::try_unwrap_class_type(req_ty) {
        None => {}
        Some((_r, req_id, _paraml)) => {
            let req_name = req_id.id_ref().as_str().to_string();
            let req_pos = get_pos(req_ty);
            if is_strict || req_name != cls::name(tc) {
                match cls::get_ancestor(tc, &req_name) {
                    None => typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Unsatisfied_req {
                            pos: class_pos.clone(),
                            trait_pos,
                            req_pos,
                            req_name,
                        }),
                        env,
                    ),
                    Some(impl_ty) => {
                        let ty_err_opt = typing_phase::sub_type_decl(
                            env,
                            &impl_ty,
                            req_ty,
                            Some(reasons_callback::unsatisfied_req_callback(
                                class_pos.clone(),
                                trait_pos,
                                req_pos,
                                req_name,
                            )),
                        );
                        if let Some(err) = &ty_err_opt {
                            typing_error_utils::add_typing_error(err, env)
                        }
                    }
                }
            }
        }
    }
}

fn check_require_class(env: &mut Env, class_pos: &Pos, tc: &cls::T, req: &Requirement) {
    let Requirement {
        pos: trait_pos,
        ty: req_ty,
    } = req;
    let trait_pos = PosOrDecl::from(trait_pos.clone());
    match tutils::try_unwrap_class_type(req_ty) {
        None => {}
        Some((_r, req_id, _paraml)) => {
            let req_name = req_id.id_ref().as_str().to_string();
            // in a `require class t;` trait constraint, t must be a non-generic class
            // name.  Since lowering enforces _paraml to be empty, it is safe to
            // ignore _param here.  Additionally we enforce that the class that uses
            // the trait with a require class constraint does not have type parameters.
            if !(req_name == cls::name(tc) && cls::tparams(tc).is_empty()) {
                let req_pos = get_pos(req_ty);
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Unsatisfied_req_class {
                        pos: class_pos.clone(),
                        trait_pos,
                        req_pos,
                        req_name,
                    }),
                    env,
                )
            }
        }
    }
}

// HHVM enformcement rejects conflicting require class and require extends
// constraints on the same class, eg:
//
//  trait T1 { require extends C; }
//  trait T2 { require class C; }
//  trait T { use T1, T2; }
//
//  The check below, only run on traits, detects and rejects such cases,
//  ensuring that Hack does not accept code on which HHVM enforcement
//  raises an error.

fn get_require_class_name_pos(ty: &DeclTy) -> Option<(String, PosOrDecl)> {
    match tutils::try_unwrap_class_type(ty) {
        Some((_, id, _)) => Some((
            id.id_ref().as_str().to_string(),
            PosOrDecl::from(id.pos().clone()),
        )),
        None => None,
    }
}

fn check_require_class_require_extends_conflict(
    env: &mut Env,
    trait_pos: &Pos,
    required_classes: &[(String, PosOrDecl)],
    tc: &cls::T,
) {
    let require_extends_implements: Vec<(String, PosOrDecl)> = cls::all_ancestor_reqs(tc)
        .iter()
        .filter_map(|r| get_require_class_name_pos(&r.ty))
        .collect();
    for (nc, pc) in required_classes {
        match require_extends_implements.iter().find(|(ne, _)| nc == ne) {
            None => {}
            Some((_, pe)) => typing_error_utils::add_typing_error(
                &typing_error::primary(primary::T::Incompatible_reqs {
                    pos: trait_pos.clone(),
                    req_name: nc.clone(),
                    req_class_pos: pc.clone(),
                    req_extends_pos: pe.clone(),
                }),
                env,
            ),
        }
    }
}

/// If a trait `T` requires `C`, but `C` does not use `T`, then Hack won't report any
/// type error on the body of `T` because the intersection of `C` and `T` is empty.
/// Although this behaviour is sound, it is likely to be confusing for the programmer.
/// We thus eagerly emit an error if a trait requires a class that does not use it.
fn check_require_class_use(
    env: &mut Env,
    trait_pos: &Pos,
    required_classes: &[(primary::TraitNotUsedReqConstraintKind, (String, PosOrDecl))],
    tc: &cls::T,
) {
    for (req_constraint_kind, (nc, pc)) in required_classes {
        match env::get_class(env, nc) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                // existence of class is checked in Naming
            }
            decl_entry::T::Found(trc) => {
                if (!cls::has_ancestor(&trc, &cls::name(tc)))
                    && ast_defs::is_c_class(cls::kind(&trc))
                {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Trait_not_used {
                            pos: trait_pos.clone(),
                            trait_name: cls::name(tc),
                            req_class_pos: pc.clone(),
                            class_pos: cls::pos(&trc),
                            class_name: cls::name(&trc),
                            req_constraint_kind: *req_constraint_kind,
                        }),
                        env,
                    )
                }
            }
        }
    }
}

fn check_trait_require_class(env: &mut Env, trait_pos: &Pos, tc: &cls::T) {
    // `List.fold_right`: from the last requirement to the first, each one put
    // at the front, which keeps the order of the requirements.
    let mut required_classes: Vec<(primary::TraitNotUsedReqConstraintKind, (String, PosOrDecl))> =
        vec![];
    let mut required_equal_classes: Vec<(String, PosOrDecl)> = vec![];
    for rc in cls::all_ancestor_req_constraints_requirements(tc).iter().rev() {
        let (req_constraint_kind, req) = match rc {
            ty::decl::folded::ConstraintRequirement::CREqual(req) => {
                (primary::TraitNotUsedReqConstraintKind::class_, req)
            }
            ty::decl::folded::ConstraintRequirement::CRSubtype(req) => {
                (primary::TraitNotUsedReqConstraintKind::this_as, req)
            }
        };
        match get_require_class_name_pos(&req.ty) {
            None => {}
            Some(required_class) => {
                match req_constraint_kind {
                    primary::TraitNotUsedReqConstraintKind::class_ => {
                        required_equal_classes.insert(0, required_class.clone())
                    }
                    primary::TraitNotUsedReqConstraintKind::this_as => {}
                }
                required_classes.insert(0, (req_constraint_kind, required_class));
            }
        }
    }
    check_require_class_use(env, trait_pos, &required_classes, tc);
    check_require_class_require_extends_conflict(env, trait_pos, &required_equal_classes, tc)
}

/// Check whether a class satifies all the requirements of the traits it uses,
/// namely [require extends] and [require implements].
pub fn check_class(env: &mut Env, class_pos: &Pos, tc: &cls::T) {
    match cls::kind(tc) {
        ClassishKind::Cclass(_) => {
            // `List.map ... (Cls.all_ancestor_req_this_as_requirements tc)
            //  @ List.map ... (Cls.all_ancestor_reqs tc)`: the right operand first.
            let strict_reqs = cls::all_ancestor_reqs(tc);
            let this_as_reqs = cls::all_ancestor_req_this_as_requirements(tc);
            let reqs: Vec<(bool, &Requirement)> = this_as_reqs
                .iter()
                .map(|r| (false, r))
                .chain(strict_reqs.iter().map(|r| (true, r)))
                .collect();
            for req in reqs {
                check_fulfillment(env, class_pos, tc, req)
            }
            for req in cls::all_ancestor_req_class_requirements(tc).iter() {
                check_require_class(env, class_pos, tc, req)
            }
        }
        ClassishKind::Ctrait => check_trait_require_class(env, class_pos, tc),
        ClassishKind::Cinterface | ClassishKind::CenumClass(_) | ClassishKind::Cenum => {}
    }
}
