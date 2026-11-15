// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_expand.ml`. See `hh/PORTING.md`.
//!
//! Gets rid of all the type variables,
//! this is only useful when declaring class constants.
//! The thing is, we don't want any type variable left in
//! type declarations, (it would force us to maintain a global
//! substitution, which would be way too big).

use crate::type_mapper;
use crate::type_mapper::TvarExpandingTypeMapper;
use crate::typing_defs::*;
use crate::typing_defs_constraints::InternalType;
use crate::typing_env_types::Env;

/// `object inherit Type_mapper.tvar_expanding_type_mapper end`
pub struct Visitor;

impl TvarExpandingTypeMapper for Visitor {}

pub fn visitor() -> Visitor {
    Visitor
}

// ---------------------------------------------------------------------------
// External API
// ---------------------------------------------------------------------------

/// (The OCaml drops the environment that the mapper returns: this works on a
/// copy.)
pub fn fully_expand(env: &Env, ty: Ty) -> Ty {
    let mut env = env.clone();
    type_mapper::fresh_env(&mut env);
    visitor().on_type(&mut env, ty)
}

pub fn fully_expand_i(env: &Env, ty: InternalType) -> InternalType {
    match ty {
        InternalType::ConstraintType(_) => ty,
        InternalType::LoclType(ty) => InternalType::LoclType(fully_expand(env, ty)),
    }
}
