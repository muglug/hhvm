// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_coeffects.ml`. See `hh/PORTING.md`.
//!
//! The values `capability_id` and `local_capability_id` are functions here
//! (`Local_id.make_unscoped` is pure: they are the same identifier each time).

use oxidized::aast;
use oxidized::local_id::LocalId;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;
use ty::decl;

use crate::decl_entry;
use crate::decl_hint;
use crate::diagnostics;
use crate::local_id;
use crate::naming_special_names as sn;
use crate::naming_special_names::coeffects::CONTEXTS as SN_COEFFECTS_CONTEXTS;
use crate::pos_or_decl;
use crate::typing_defs_core::Capability;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
use crate::typing_intersection;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_type_integrity;
use crate::typing_utils;

/// `SN.Coeffects.capability` (missing from `naming_special_names_rust`).
const SN_COEFFECTS_CAPABILITY: &str = "$#capability";

pub fn capability_id() -> LocalId {
    local_id::make_unscoped(SN_COEFFECTS_CAPABILITY)
}

pub fn local_capability_id() -> LocalId {
    local_id::make_unscoped(sn::coeffects::LOCAL_CAPABILITY)
}

pub fn register_capabilities(env: &mut Env, cap_ty: Ty, unsafe_cap_ty: Ty) -> Ty {
    let cap_pos = get_pos(&cap_ty);
    // Represents the capability for local operations inside a function body, excluding calls.
    env::set_local(
        None,
        None,
        env,
        local_capability_id(),
        cap_ty.clone(),
        pos_or_decl::unsafe_to_raw_pos(cap_pos.clone()),
    );
    let ty = typing_intersection::intersect(
        env,
        reason::hint(cap_pos.clone()),
        cap_ty,
        unsafe_cap_ty,
    );
    // The implicit argument for ft_implicit_params.capability
    env::set_local(
        None,
        None,
        env,
        capability_id(),
        ty.clone(),
        pos_or_decl::unsafe_to_raw_pos(cap_pos),
    );
    ty
}

pub fn get_type(capability: &Capability) -> Ty {
    match capability {
        Capability::CapTy(cap) => cap.clone(),
        Capability::CapDefaults(p) => make_type::default_capability(p.clone()),
    }
}

/// `Diagnostics.add_diagnostic Nast_check_error.(to_user_diagnostic @@
/// Illegal_context { pos; name = Typing_print.full_decl (Env.get_tcopt env) ty })`
fn add_illegal_context(env: &Env, pos: &Pos, ty: &DeclTy) {
    let error = NastCheckError::IllegalContext {
        pos: pos.clone(),
        name: typing_print::full_decl(None, &env::get_tcopt(env), &ty.clone().to_oxidized()),
    };
    let diagnostic = crate::naming_phase_error::to_user_diagnostic(NamingPhaseError::NastCheck(error));
    diagnostics::add_diagnostic(diagnostic);
}

pub fn validate_capability(env: &Env, pos: &Pos, ty: &DeclTy) {
    match ty.node_ref() {
        decl::Ty_::Tintersection(tys) => {
            for ty in tys.iter() {
                validate_capability(env, pos, ty)
            }
        }
        decl::Ty_::Tapply(id_and_tyl)
            if id_and_tyl
                .0
                .id_ref()
                .as_str()
                .starts_with(SN_COEFFECTS_CONTEXTS) => {}
        decl::Ty_::Tapply(id_and_tyl) => {
            let n = id_and_tyl.0.id_ref().as_str();
            match env::get_class_or_typedef(env, n) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                    // unbound name error
                }
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(td)) if td.is_ctx => {}
                _ => add_illegal_context(env, pos, ty),
            }
        }
        decl::Ty_::Tgeneric(name) if sn::coeffects::is_generated_generic(name.as_str()) => {}
        decl::Ty_::Taccess(taccess) => {
            let root = &taccess.ty;
            let c = taccess.type_const.id_ref().as_str();
            // The environment this returns is dropped by the OCaml (the function
            // returns `unit`): work on a copy.
            let mut env = env.clone();
            let env = &mut env;
            let (ty_err_opt, root) = phase::localize_no_subst(env, false, root);
            if let Some(ty_err) = &ty_err_opt {
                typing_error_utils::add_typing_error(ty_err, env)
            }
            let candidates =
                typing_utils::get_concrete_supertypes(None, None, None, false, env, root);
            let env = &*env;
            let check_ctx_const = |t: &Ty| match get_node(t) {
                Ty_::Tclass((_, name), _, _) => match env::get_class(env, name) {
                    decl_entry::T::Found(cls) => match env::get_typeconst(env, &cls, c) {
                        Some(tc) => {
                            if !tc.is_ctx {
                                add_illegal_context(env, pos, ty)
                            }
                        }
                        None => {
                            // typeconst not found
                        }
                    },
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        // unbound name error
                    }
                },
                _ => {}
            };
            for t in &candidates {
                check_ctx_const(t)
            }
        }
        _ => add_illegal_context(env, pos, ty),
    }
}

pub fn pretty(env: &Env, ty: &Ty) -> Lazy<String> {
    let mut env = env.clone();
    let ty = ty.clone();
    Lazy::new(move || {
        let ty = typing_intersection::simplify_intersections(&mut env, None, ty);
        typing_print::coeffects(&env, &ty)
    })
}

pub fn is_generated_generic(s: &str) -> bool {
    s.starts_with(sn::coeffects::GENERATED_GENERIC_PREFIX)
}

pub fn type_capability(
    env: &mut Env,
    ctxs: Option<&aast::Contexts>,
    unsafe_ctxs: Option<&aast::Contexts>,
    default_pos: &Pos,
) -> (Ty, Ty) {
    // No need to repeat the following check (saves time) for unsafe_ctx
    // because it's synthetic and well-kinded by construction
    if let Some(aast::Contexts(_pos, hl)) = ctxs {
        for h in hl {
            typing_type_integrity::check_context_hint_integrity(false, env, h)
        }
    }

    let cc = decl_hint::aast_contexts_to_decl_capability;
    let (decl_pos, cap) = cc(&env.decl_env, ctxs, default_pos);
    let (ty_err_opt1, cap_ty) = match cap {
        decl::ty::Capability::CapTy(ty) => {
            // `Typechecker_options.strict_contexts`
            if env::get_tcopt(env).tco_strict_contexts {
                validate_capability(env, &decl_pos, &ty)
            }
            phase::localize_no_subst(env, false, &ty)
        }
        decl::ty::Capability::CapDefaults(p) => {
            (None, make_type::default_capability(PosOrDecl::from(p)))
        }
    };
    if let Some(ty_err) = &ty_err_opt1 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    let (ty_err_opt2, unsafe_cap_ty) = match cc(&env.decl_env, unsafe_ctxs, default_pos).1 {
        decl::ty::Capability::CapTy(ty) => phase::localize_no_subst(env, false, &ty),
        decl::ty::Capability::CapDefaults(p) => {
            (None, make_type::default_capability_unsafe(PosOrDecl::from(p)))
        }
    };
    if let Some(ty_err) = &ty_err_opt2 {
        typing_error_utils::add_typing_error(ty_err, env)
    }
    (cap_ty, unsafe_cap_ty)
}

// Checking this with List.exists will be a single op in the vast majority of cases (empty)
pub fn get_ctx_vars(ctxs: Option<&aast::Contexts>) -> Vec<String> {
    match ctxs {
        None => vec![],
        Some(aast::Contexts(_, cs)) => cs
            .iter()
            .filter_map(|c| match c {
                aast::Hint(_, h) => match &**h {
                    aast::Hint_::Haccess(aast::Hint(_, h), _) => match &**h {
                        aast::Hint_::Hvar(n) => Some(n.clone()),
                        _ => None,
                    },
                    _ => None,
                },
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Id;

    use super::*;

    #[test]
    fn special_names_are_the_ocaml_ones() {
        assert_eq!(capability_id(), (0, "$#capability".to_string()));
        assert_eq!(local_capability_id(), (0, "$#local_capability".to_string()));
        assert!("\\HH\\Contexts\\defaults".starts_with(SN_COEFFECTS_CONTEXTS));
        assert!(is_generated_generic("T/[ctx $f]"));
        assert!(!is_generated_generic("T"));
    }

    #[test]
    fn ctx_vars_are_the_variables_of_accesses() {
        let p = Pos::NONE;
        let hint = |h: aast::Hint_| aast::Hint(p.clone(), Box::new(h));
        let ctxs = aast::Contexts(
            p.clone(),
            vec![
                hint(aast::Hint_::Haccess(
                    hint(aast::Hint_::Hvar("$x".to_string())),
                    vec![Id(p.clone(), "C".to_string())],
                )),
                hint(aast::Hint_::Happly(
                    Id(p.clone(), "\\HH\\Contexts\\defaults".to_string()),
                    vec![],
                )),
                hint(aast::Hint_::Haccess(
                    hint(aast::Hint_::Hvar("$y".to_string())),
                    vec![Id(p.clone(), "C".to_string())],
                )),
            ],
        );
        assert_eq!(get_ctx_vars(Some(&ctxs)), vec!["$x", "$y"]);
        assert!(get_ctx_vars(None).is_empty());
    }
}
