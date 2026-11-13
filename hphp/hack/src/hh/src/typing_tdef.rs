// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_tdef.ml`. See `hh/PORTING.md`.
//!
//! Typedefs are `hackrs` declarations (`crate::typing_defs::TypedefType`), so
//! the decl types here are `hackrs`'s (`DeclTy`).

use pos::Symbol;
use pos::ToOxidized;
use ty::reason::Reason as _;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ctx::R;
use crate::decl_entry;
use crate::decl_instantiate;
use crate::decl_subst;
use crate::type_expansions;
use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

/// The type parameters of a typedef (`td.td_tparams`): a handle on the typedef,
/// read as the slice of its parameters (OCaml shares the list; copying the
/// parameters copies their constraints and attributes).
#[derive(Clone, Debug)]
pub struct TypedefTparams(crate::decl_provider::TypedefDecl);

impl std::ops::Deref for TypedefTparams {
    type Target = [DeclTparam];
    fn deref(&self) -> &[DeclTparam] {
        &self.0.tparams[..]
    }
}

/// The result of looking up and expanding a single typedef.
/// [Expanded] contains the raw (unsubstituted) body as a [decl_ty],
/// [Opaque] contains the upper-bound constraint.
/// Both include the type parameters needed by the caller for substitution.
#[derive(Clone, Debug)]
pub enum Expansion {
    Expanded {
        tparams: TypedefTparams,
        body: DeclTy,
        cstr: DeclTy,
    },
    Opaque {
        tparams: TypedefTparams,
        cstr: DeclTy,
    },
    Cyclic {
        td_type_assignment: TypedefTypeAssignment,
    },
}

#[derive(Clone)]
pub struct ExpansionResult {
    pub ety_env: ExpandEnv,
    pub cycles: Vec<type_expansions::CycleReporter>,
    pub expansion: Expansion,
}

/// `MakeType.mixed r` for a decl type: `mk (r, Toption (nonnull r))`.
/// (`crate::typing_make_type::mixed` builds localized types only.)
fn decl_mixed(r: R) -> DeclTy {
    DeclTy::new(
        r.clone(),
        DeclTy_::Toption(DeclTy::new(r, DeclTy_::Tnonnull)),
    )
}

/// `Reason.implicit_upper_bound (p, s)` for a decl reason.
fn decl_implicit_upper_bound(p: &<R as ty::reason::Reason>::Pos, s: &str) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::ImplicitUpperBound(p.clone(), Symbol::new(s))))
}

/// Compute the upper bound constraint, defaulting to [mixed].
fn get_typedef_constraint(td: &TypedefType) -> DeclTy {
    match &td.as_constraint {
        None => decl_mixed(decl_implicit_upper_bound(&td.pos, "?nonnull")),
        Some(cstr) => cstr.clone(),
    }
}

/// Decide whether to expand a typedef based on visibility, and return the
/// raw body or [None] for opaque. Does not perform substitution or cycle
/// checking.
fn resolve_typedef_body(
    visibility_behavior: &VisibilityBehavior,
    env: &Env,
    x: &str,
    td: &TypedefType,
) -> Option<DeclTy> {
    if env::should_expand_type_alias(env, visibility_behavior, x, td) {
        let body = match &td.type_assignment {
            ty::decl::ty::TypedefTypeAssignment::SimpleTypeDef(_vis, td_type) => td_type.clone(),
            ty::decl::ty::TypedefTypeAssignment::CaseType(variant, variants) => {
                crate::typing_utils::get_case_type_variants_as_type(variant, variants)
            }
        };
        Some(body)
    } else {
        None
    }
}

/// [expand_typedef ety_env env r name] looks up the type alias [name]
/// and returns a decl-level expansion result. For visible typedefs, the
/// result contains the raw (unsubstituted) body; for opaque ones, the
/// upper-bound constraint. The caller handles substitution and localization.
///
/// Expansion behavior is controlled through [ety_env.visibility_behavior]:
/// - [Always_expand_newtype] forces expansion of all type aliases
/// - [Expand_visible_newtype_only] only expands visible aliases (default)
pub fn expand_typedef(ety_env: &ExpandEnv, env: &Env, r: &Reason, x: &str) -> ExpansionResult {
    let td = crate::utils::unsafe_opt(decl_entry::to_option(env::get_typedef(env, x)));
    match add_type_expansion_check_cycles(
        ety_env,
        type_expansions::Expansion {
            name: type_expansions::expandable::T::TypeAlias(x.to_string()),
            use_pos: typing_reason::to_pos(r),
            def_pos: Some(td.pos.clone().to_oxidized()),
        },
    ) {
        Err(cycle) => ExpansionResult {
            ety_env: ety_env.clone(),
            cycles: vec![cycle],
            expansion: Expansion::Cyclic {
                td_type_assignment: td.type_assignment.clone(),
            },
        },
        Ok(ety_env) => {
            let tparams = TypedefTparams(td.clone());
            match resolve_typedef_body(&ety_env.visibility_behavior, env, x, &td) {
                Some(body) => {
                    let cstr = get_typedef_constraint(&td);
                    ExpansionResult {
                        ety_env,
                        cycles: vec![],
                        expansion: Expansion::Expanded { tparams, body, cstr },
                    }
                }
                None => {
                    let cstr = get_typedef_constraint(&td);
                    ExpansionResult {
                        ety_env,
                        cycles: vec![],
                        expansion: Expansion::Opaque { tparams, cstr },
                    }
                }
            }
        }
    }
}

/// Recursively expand all typedef layers at the decl level.
/// Internally sets [Always_expand_newtype] and calls [expand_typedef]
/// in a loop, performing decl-level substitution at each step,
/// until a non-typedef is reached.
pub fn force_expand_decl_typedef(
    ety_env: &ExpandEnv,
    env: &Env,
    ty: &DeclTy,
) -> (ExpandEnv, DeclTy) {
    let ety_env = ExpandEnv {
        visibility_behavior: VisibilityBehavior::AlwaysExpandNewtype,
        ..ety_env.clone()
    };
    fn aux(env: &Env, ety_env: ExpandEnv, ty: &DeclTy) -> (ExpandEnv, DeclTy) {
        match ty.node_ref() {
            DeclTy_::Tapply(id_and_args) => {
                let (name, args) = &**id_and_args;
                let name = name.id_ref().as_str();
                match decl_entry::to_option(env::get_typedef(env, name)) {
                    Some(_) => {
                        // `expand_typedef` only takes the position of the
                        // reason, which localizing the reason keeps.
                        let result = expand_typedef(
                            &ety_env,
                            env,
                            &typing_reason::localize(&ty.reason().clone().to_oxidized()),
                            name,
                        );
                        match result.expansion {
                            Expansion::Expanded {
                                tparams,
                                body,
                                cstr: _,
                            } => {
                                let subst = decl_subst::make_decl(&tparams, args);
                                let body = decl_instantiate::instantiate(&subst, &body);
                                aux(env, result.ety_env, &body)
                            }
                            Expansion::Opaque { .. } | Expansion::Cyclic { .. } => {
                                (result.ety_env, ty.clone())
                            }
                        }
                    }
                    None => (ety_env, ty.clone()),
                }
            }
            _ => (ety_env, ty.clone()),
        }
    }
    aux(env, ety_env, ty)
}

#[cfg(test)]
mod tests {
    use pos::BPos;

    use super::*;

    #[test]
    fn default_constraint_is_question_nonnull() {
        let r = decl_implicit_upper_bound(&BPos::none(), "?nonnull");
        let ty = decl_mixed(r);
        match ty.node_ref() {
            DeclTy_::Toption(inner) => {
                assert!(matches!(inner.node_ref(), DeclTy_::Tnonnull));
                assert!(matches!(
                    inner.reason().as_impl(),
                    ReasonImpl::FromWitnessDecl(WitnessDecl::ImplicitUpperBound(_, s))
                        if s.as_str() == "?nonnull"
                ));
            }
            _ => panic!("expected ?nonnull"),
        }
    }
}
