// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_local_types.ml`. See `hh/PORTING.md`.

use oxidized::local_id::LocalId;
use oxidized::pos::Pos;

use crate::expression_id;
use crate::typing_defs_core::Ty;

#[derive(Clone, Debug)]
pub struct Local {
    /// The type of the local
    pub ty: Ty,
    /// The position at which the variable got its type.
    pub pos: Pos,
    /// Along with a type, each local variable has a expression id associated with
    /// it. This is used when generating expression dependent types for the 'this'
    /// type. The idea is that if two local variables have the same expression_id
    /// then they refer to the same late bound type, and thus have compatible
    /// 'this' types.
    pub eid: expression_id::T,
    /// If the variable is bound to a expression tree splice that has nested expression
    /// trees with free variables, this records the types of those variables along with
    /// the position they occurred in.
    pub macro_splice_vars: Option<im::OrdMap<LocalId, (Pos, Ty)>>,
}

/// `local Local_id.Map.t`. Persistent, with versions that share their
/// entries (`crate::pmap`): the environment copies it at every branch and
/// saves it with every expression.
pub type T = crate::pmap::Map<LocalId, Local>;

pub fn empty() -> T {
    // `Local_id.Map.empty`, a constant.
    T::new()
}

pub fn add_to_local_types(id: LocalId, local: Local, mut m: T) -> T {
    m.insert(id, local);
    m
}
