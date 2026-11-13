// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_shape_splat_key.ml`. See `hh/PORTING.md`.
//!
//! Canonical keys for memoizing shape-splat operands. Ordinary types retain
//! their structural identity. Newtypes retain their name, arguments, and
//! module opacity, but omit their stored bound because consumers re-fetch it
//! from the typedef. Omitting it prevents comparison from branching through
//! each level of a deeply nested splat-bound chain.
//!
//! `type t` is abstract in the `.mli`: [`T`] wraps the canonical type, and is
//! ordered by [`compare`] (so `Map.Make` over it is a `BTreeMap`, [`map::T`]).

use std::cmp::Ordering;

use crate::type_mapper_generic::DeepTypeMapper;
use crate::typing_defs;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::mk;
use crate::typing_make_type as make_type;
use crate::typing_reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

/// `type t = locl_ty` (abstract in the `.mli`).
#[derive(Clone, Debug)]
pub struct T(Ty);

/// `let transparent_marker = Typing_make_type.int Typing_reason.none` (a
/// module-level value: the type is built on each use, which is cheap and has
/// no effect).
fn transparent_marker() -> Ty {
    make_type::int(typing_reason::none())
}

/// `let module_opaque_marker = Typing_make_type.bool Typing_reason.none`
fn module_opaque_marker() -> Ty {
    make_type::bool(typing_reason::none())
}

/// `class mapper`: `inherit [unit] Type_mapper_generic.deep_type_mapper`,
/// overriding `on_tnewtype`.
struct Mapper;

impl DeepTypeMapper<()> for Mapper {
    fn on_tnewtype(
        &mut self,
        env: &mut (),
        reason: Reason,
        name: String,
        args: Vec<Ty>,
        _bound: Ty,
    ) -> Ty {
        let args = self.on_locl_ty_list(env, args);
        let opacity = if typing_reason::predicates::is_opaque_type_from_module(&reason) {
            module_opaque_marker()
        } else {
            transparent_marker()
        };
        mk((reason, Ty_::Tnewtype(name, args, opacity)))
    }
}

/// `let mapper = new mapper`
fn mapper() -> Mapper {
    Mapper
}

pub fn of_ty(ty: &Ty) -> T {
    T(mapper().on_type(&mut (), ty.clone()))
}

/// `let compare = Typing_defs.compare_locl_ty ?normalize_lists:None`
pub fn compare(t1: &T, t2: &T) -> Ordering {
    typing_defs::compare_locl_ty(None, &t1.0, &t2.0)
}

impl PartialEq for T {
    fn eq(&self, other: &Self) -> bool {
        compare(self, other) == Ordering::Equal
    }
}

impl Eq for T {}

impl PartialOrd for T {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(compare(self, other))
    }
}

impl Ord for T {
    fn cmp(&self, other: &Self) -> Ordering {
        compare(self, other)
    }
}

/// `module Map = Map.Make (struct type nonrec t = t let compare = compare end)`
pub mod map {
    /// `'a Map.t`
    pub type T<V> = std::collections::BTreeMap<super::T, V>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing_make_type as mt;

    fn r() -> Reason {
        typing_reason::none()
    }

    fn newtype(name: &str, args: Vec<Ty>, bound: Ty) -> Ty {
        mk((r(), Ty_::Tnewtype(name.to_string(), args, bound)))
    }

    #[test]
    fn newtype_bounds_are_ignored() {
        let n1 = newtype("\\N", vec![mt::int(r())], mt::string(r()));
        let n2 = newtype("\\N", vec![mt::int(r())], mt::float(r()));
        assert_eq!(compare(&of_ty(&n1), &of_ty(&n2)), Ordering::Equal);
        // The arguments still count.
        let n3 = newtype("\\N", vec![mt::float(r())], mt::string(r()));
        assert_ne!(compare(&of_ty(&n1), &of_ty(&n3)), Ordering::Equal);
        // Nested newtypes too.
        let v1 = mt::vec(r(), n1);
        let v2 = mt::vec(r(), n2);
        assert_eq!(of_ty(&v1), of_ty(&v2));
    }

    #[test]
    fn ordinary_types_keep_their_structure() {
        assert_ne!(of_ty(&mt::int(r())), of_ty(&mt::string(r())));
        let mut m: map::T<bool> = map::T::new();
        m.insert(of_ty(&mt::int(r())), true);
        assert_eq!(m.get(&of_ty(&mt::int(r()))), Some(&true));
        assert_eq!(m.get(&of_ty(&mt::float(r()))), None);
    }
}
