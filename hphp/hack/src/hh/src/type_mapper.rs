// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/type_mapper.ml`. See `hh/PORTING.md`.
//!
//! The classes of `Type_mapper_generic` with the typing environment for
//! `'env`. See `type_mapper_generic.rs` for how classes are ported: a mapper
//! that would inherit `Type_mapper.deep_type_mapper` implements
//! `type_mapper_generic::DeepTypeMapper<Env>` (which makes it a
//! [`DeepTypeMapper`]), and one that would inherit
//! `Type_mapper.tvar_expanding_type_mapper` implements
//! [`TvarExpandingTypeMapper`].

use oxidized::ast_defs::Tprim;

use crate::type_mapper_generic as map;
use crate::type_mapper_generic::type_mapper_methods_common;
use crate::type_mapper_generic::type_mapper_methods_deep;
use crate::typing_defs::*;
use crate::typing_env_types::Env;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

/// `type result = env * locl_ty`: the environment is threaded.
pub type Result = Ty;

pub fn fresh_env(_env: &mut Env) {}

/// `class shallow_type_mapper = object inherit [env] Map.shallow_type_mapper end`
/// (and `class type type_mapper_type`, the type of the three classes here).
pub trait ShallowTypeMapper: map::ShallowTypeMapper<Env> {}

impl<M: map::ShallowTypeMapper<Env> + ?Sized> ShallowTypeMapper for M {}

/// `class deep_type_mapper = object inherit [env] Map.deep_type_mapper end`
pub trait DeepTypeMapper: map::DeepTypeMapper<Env> {}

impl<M: map::DeepTypeMapper<Env> + ?Sized> DeepTypeMapper for M {}

/// `class tvar_expanding_type_mapper`: `deep_type_mapper`, with `on_tvar`
/// overridden.
#[allow(unused_variables)]
pub trait TvarExpandingTypeMapper {
    type_mapper_methods_common!(Env);
    type_mapper_methods_deep!(Env);

    fn on_tvar(&mut self, env: &mut Env, r: Reason, n: isize) -> Ty {
        let ty = crate::typing_env::get_type(env, r, n);
        if crate::typing_defs::is_tyvar(&ty) {
            ty
        } else {
            self.on_type(env, ty)
        }
    }
}
