// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_modules.ml`. See `hh/PORTING.md`.
//!
//! `can_access_internal` returns a polymorphic variant, which has no name in
//! OCaml: here it is [`CanAccessInternalResult`], with the OCaml tags.

use oxidized::pos_or_decl::PosOrDecl;

use crate::ast_defs;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_utils;

/// ``[ `Yes | `Disjoint of string * string | `Outside of string
/// | `OutsideViaTrait of Pos_or_decl.t ]``
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanAccessInternalResult {
    Yes,
    /// `(current, target)`
    Disjoint(String, String),
    Outside(String),
    OutsideViaTrait(PosOrDecl),
}

/// [can_access_internal ~env ~current ~target target_pos] returns whether a symbol defined in
/// module [current] is allowed to access an internal symbol defined in [target] under [env].
pub fn can_access_internal(
    env: &Env,
    current: Option<String>,
    target: Option<String>,
) -> CanAccessInternalResult {
    match (current, target) {
        (None, None) | (Some(_), None) => CanAccessInternalResult::Yes,
        (None, Some(m)) => CanAccessInternalResult::Outside(m),
        (Some(m_current), Some(m_target)) if m_current == m_target => {
            match env::get_self_id(env) {
                None => CanAccessInternalResult::Yes,
                Some(self_) => match env::get_class(env, &self_) {
                    decl_entry::T::Found(cls)
                        if ast_defs::is_c_trait(cls::kind(&cls))
                            && !cls::internal(&cls)
                            && !cls::is_module_level_trait(&cls) =>
                    {
                        CanAccessInternalResult::OutsideViaTrait(cls::pos(&cls))
                    }
                    decl_entry::T::Found(_)
                    | decl_entry::T::DoesNotExist
                    | decl_entry::T::NotYetAvailable => CanAccessInternalResult::Yes,
                },
            }
        }
        (Some(current), Some(target)) => CanAccessInternalResult::Disjoint(current, target),
    }
}

pub fn is_class_visible(env: &Env, cls: &cls::T) -> bool {
    if cls::internal(cls) {
        // OCaml evaluates the labelled arguments right to left.
        let target = cls::get_module(cls);
        let current = env::get_current_module(env);
        match can_access_internal(env, current, target) {
            CanAccessInternalResult::Yes => true,
            _ => {
                cls::tests_bypass_visibility(cls)
                    && typing_utils::is_tests_bypass_visibility_context(env)
            }
        }
    } else {
        true
    }
}
