// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_atomic_data_types.ml`. See `hh/PORTING.md`.
//!
//! Computes runtime data types for types that cannot be decomposed into
//! smaller types.

use oxidized::aast;

use crate::typing_data_type::data_type;
use crate::typing_data_type::tag;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::TypeTag;
use crate::typing_env_types::Env;

/// `type t = DataType.t`
pub type T = data_type::T;

/// Types we consider as atomic
#[derive(Clone, Debug)]
pub enum AtomicTy {
    Primitive(aast::Tprim),
    Function,
    Nonnull,
    Tuple,
    Shape,
    Label,
    Class(String, Vec<Ty>),
}

/// `let function_ = DataType.fun_to_datatypes`
fn function_() -> T {
    data_type::fun_to_datatypes()
}

fn nonnull() -> T {
    data_type::nonnull_to_datatypes()
}

fn tuple() -> T {
    data_type::tuple_to_datatypes()
}

fn shape() -> T {
    data_type::shape_to_datatypes()
}

fn mixed() -> T {
    data_type::mixed()
}

fn label() -> T {
    data_type::label_to_datatypes()
}

/// When safe_for_are_disjoint is true, do not specially handle interfaces'
/// sealed attribute or required ancestors.
/// Temporary flag to avoid an issue with `are_disjoint` T215053987
pub fn of_ty(safe_for_are_disjoint: bool, env: &mut Env, ty: &AtomicTy) -> T {
    match ty {
        AtomicTy::Primitive(prim) => data_type::prim_to_datatypes(*prim),
        AtomicTy::Function => function_(),
        AtomicTy::Nonnull => nonnull(),
        AtomicTy::Tuple => tuple(),
        AtomicTy::Shape => shape(),
        AtomicTy::Label => label(),
        AtomicTy::Class(name, args) => {
            let generics = tag::generics_for_class_and_tyl(env, name, args);
            data_type::class::to_datatypes(safe_for_are_disjoint, env, name, &generics)
        }
    }
}

/// When safe_for_are_disjoint is true, do not specially handle interfaces'
/// sealed attribute or required ancestors.
/// Temporary flag to avoid an issue with `are_disjoint` T215053987
pub fn of_tag(safe_for_are_disjoint: bool, env: &mut Env, tag: &TypeTag) -> T {
    let of_ty = |env: &mut Env, ty: AtomicTy| of_ty(safe_for_are_disjoint, env, &ty);
    match tag {
        TypeTag::BoolTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tbool)),
        TypeTag::IntTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tint)),
        TypeTag::ArraykeyTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tarraykey)),
        TypeTag::FloatTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tfloat)),
        TypeTag::NumTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tnum)),
        TypeTag::ResourceTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tresource)),
        TypeTag::NullTag => of_ty(env, AtomicTy::Primitive(aast::Tprim::Tnull)),
        TypeTag::ClassTag(name, args) => {
            let generics = tag::generics_for_class_and_tag_generic_l(env, name, args);
            data_type::class::to_datatypes(safe_for_are_disjoint, env, name, &generics)
        }
        TypeTag::EnumTag(id) => data_type::enum_to_datatypes(id),
        TypeTag::GenericTag { name, from_like: _ } => data_type::generic_to_datatypes(name),
    }
}

/// The empty set of data types
pub fn empty() -> T {
    data_type::set::empty()
}

/// Computes the complement for the set of values contained in [t]
pub fn complement(dt: &T) -> T {
    data_type::set::diff(&mixed(), dt)
}

/// Computes the union of the two given sets
pub fn union(dt1: &T, dt2: &T) -> T {
    data_type::set::union(dt1, dt2)
}

/// Returns true if the given data types are known to have no values in
/// common, otherwise returns false
pub fn are_disjoint(env: &Env, dt1: &T, dt2: &T) -> bool {
    data_type::set::are_disjoint(env, dt1, dt2)
}

/// Returns true iff the two given types are known to be disjoint based on
/// comparison of their datatypes
pub fn are_locl_tys_disjoint(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let safe_for_are_disjoint = true;
    // The environments that `fromTy` returns are dropped.
    let mut env = env.clone();
    let tags1 = data_type::from_ty(safe_for_are_disjoint, &mut env, ty1);
    let tags2 = data_type::from_ty(safe_for_are_disjoint, &mut env, ty2);
    data_type::set::are_disjoint(&env, &tags1, &tags2)
}
