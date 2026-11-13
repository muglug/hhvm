// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `subtype_recursion_tracker.ml`. See `hh/PORTING.md`.
//!
//! `include Recursion_tracker.Make (Subtype_op)`: [`T`], [`empty`] and
//! [`add_op_and_check_infinite_recursion`] are those of
//! `crate::recursion_tracker::make` at the operation [`subtype_op::T`].

use crate::recursion_tracker;

/// `module Subtype_op`
pub mod subtype_op {
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::equal_locl_ty;

    /// `type t = { ty_sub; ty_super }`. As for the other types that mirror
    /// `oxidized`, the prefix that the fields share (`ty_`) is dropped:
    /// `ty_sub` is `sub` and `ty_super` is `super_`.
    #[derive(Clone, Debug)]
    pub struct T {
        pub sub: Ty,
        pub super_: Ty,
    }

    /// `[@@deriving eq]`: `Typing_defs.equal_locl_ty` on the fields, in order.
    pub fn equal(a: &T, b: &T) -> bool {
        equal_locl_ty(&a.sub, &b.sub) && equal_locl_ty(&a.super_, &b.super_)
    }

    impl crate::recursion_tracker::Operation for T {
        fn equal(a: &Self, b: &Self) -> bool {
            equal(a, b)
        }
    }
}

/// `Recursion_tracker.Make (Subtype_op).t`
pub type T = recursion_tracker::make::T<subtype_op::T>;

pub fn empty() -> T {
    recursion_tracker::make::empty()
}

/// No operation recorded (not in the OCaml).
pub fn is_empty(t: &T) -> bool {
    recursion_tracker::make::is_empty(t)
}

pub fn add_op_and_check_infinite_recursion(
    t: T,
    op: subtype_op::T,
) -> Result<T, subtype_op::T> {
    recursion_tracker::make::add_op_and_check_infinite_recursion(t, op)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;

    use super::*;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::get_reason;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn prim(r: typing_reason::T, p: Tprim) -> Ty {
        mk((r, Ty_::Tprim(p)))
    }

    #[test]
    fn the_equality_of_operations_ignores_reasons() {
        let int = prim(typing_reason::none(), Tprim::Tint);
        let float = prim(typing_reason::none(), Tprim::Tfloat);
        let int_witness = prim(typing_reason::witness(Pos::NONE), Tprim::Tint);
        let t = add_op_and_check_infinite_recursion(
            empty(),
            subtype_op::T {
                sub: int.clone(),
                super_: float.clone(),
            },
        )
        .unwrap();
        let found = add_op_and_check_infinite_recursion(
            t.clone(),
            subtype_op::T {
                sub: int_witness,
                super_: float.clone(),
            },
        )
        .unwrap_err();
        // The operation that was there is returned, with its reasons.
        assert!(matches!(&**get_reason(&found.sub), crate::typing_reason::T_::NoReason));
        assert!(
            add_op_and_check_infinite_recursion(
                t,
                subtype_op::T {
                    sub: float,
                    super_: int,
                },
            )
            .is_ok()
        );
    }
}
