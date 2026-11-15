// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_tdef_locl.ml`. See `hh/PORTING.md`.
//!
//! Locl-level typedef expansion: bridges [Typing_tdef] (decl-level expansion)
//! and [Typing_phase] (localization) without requiring either to depend on the
//! other.

use naming_special_names_rust as sn;
use oxidized::pos_or_decl::PosOrDecl;

use crate::type_expansions;
use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_phase as phase;
use crate::typing_tdef;

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn merge_errs(
    e1: Option<typing_error::T>,
    e2: Option<typing_error::T>,
) -> Option<typing_error::T> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// Expand a [locl_ty], smashing typedef abstraction and collecting a trail
/// of where the typedefs come from. Peels [Tnewtype] layers one at a time,
/// expanding at the decl level and localizing at each step.
///
/// /!\ This only does something if passed a [Tnewtype].
pub fn force_expand_typedef(
    ety_env: &ExpandEnv,
    env: &mut Env,
    t: Ty,
) -> (Option<typing_error::T>, Ty, Vec<PosOrDecl>) {
    fn aux(
        e1: Option<typing_error::T>,
        ety_env: &ExpandEnv,
        env: &mut Env,
        t: Ty,
    ) -> (Option<typing_error::T>, Ty, Vec<PosOrDecl>) {
        let default = |e1, t| {
            (
                e1,
                t,
                type_expansions::def_positions(&ety_env.type_expansions),
            )
        };
        let expansion = match get_node(&t) {
            Ty_::Tnewtype(x, _, _) if x == sn::classes::ENUM_CLASS_LABEL => {
                // Labels are Resources at runtime, so we don't want to force them
                // to string. MemberOf on the other hand are "typed alias" on the
                // underlying type so it's ok to force them. So we only special case
                // Labels here
                None
            }
            Ty_::Tnewtype(x, argl, _) if !(env::is_enum(env, x) || env::is_enum_class(env, x)) => {
                let r = get_reason(&t).clone();
                let ety_env_expand = ExpandEnv {
                    visibility_behavior: VisibilityBehavior::AlwaysExpandNewtype,
                    ..ety_env.clone()
                };
                let typing_tdef::ExpansionResult {
                    ety_env: result_ety_env,
                    cycles: _,
                    expansion,
                } = typing_tdef::expand_typedef(&ety_env_expand, env, &r, x);
                Some((r, argl.clone(), result_ety_env, expansion))
            }
            _ => None,
        };
        match expansion {
            Some((
                r,
                argl,
                result_ety_env,
                typing_tdef::Expansion::Expanded {
                    tparams,
                    body,
                    cstr: _,
                },
            )) => {
                let substs = crate::decl_subst::make_locl(&tparams[..], &argl);
                // Use default visibility behavior for body localization, NOT
                // Always_expand_newtype. This ensures opaque newtypes in the body
                // remain as Tnewtype, allowing the outer force_expand loop to
                // handle them one at a time and accumulate the expansion trail.
                let ety_env_inner = ExpandEnv {
                    substs,
                    under_type_constructor: false,
                    visibility_behavior: default_visibility_behaviour(),
                    ..result_ety_env.clone()
                };
                let (e2, ty) = phase::localize(&ety_env_inner, env, &body);
                let ty = with_reason(ty, r);
                let err = merge_errs(e1, e2);
                aux(err, &result_ety_env, env, ty)
            }
            Some((
                _,
                _,
                _,
                typing_tdef::Expansion::Opaque { .. } | typing_tdef::Expansion::Cyclic { .. },
            ))
            | None => default(e1, t),
        }
    }
    aux(None, ety_env, env, t)
}
