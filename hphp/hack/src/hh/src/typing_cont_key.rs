// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_cont_key.ml`. See `hh/PORTING.md`.
//!
//! `Typing_continuations` is `include Typing_cont_key` plus `Map`, and
//! `crate::typing_continuations` was ported first, with the contents of this
//! module in it (the type and its functions). So that `Typing_cont_key.t` and
//! `Typing_continuations.t` are one type here too, this module re-exports
//! them from there, where the OCaml includes in the other direction.

/// `Typing_cont_key.t`: `Next`, `Continue`, `Break`, `Catch`, `Do`, `Exit`,
/// `Fallthrough`, `Finally`, ordered in that order (`[@@deriving ord]`).
pub use crate::typing_continuations::T;
pub use crate::typing_continuations::all;
/// `[@@deriving ord]`
pub use crate::typing_continuations::compare;
/// `[@@deriving eq]`
pub use crate::typing_continuations::equal;
/// `[@@deriving show]`
pub use crate::typing_continuations::show;
pub use crate::typing_continuations::to_string;

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use super::*;

    #[test]
    fn all_is_in_the_order_of_the_ocaml_definition() {
        assert_eq!(
            all(),
            vec![
                T::Next,
                T::Continue,
                T::Break,
                T::Catch,
                T::Do,
                T::Exit,
                T::Fallthrough,
                T::Finally
            ]
        );
        let names: Vec<String> = all().iter().map(to_string).collect();
        assert_eq!(
            names,
            vec![
                "Next",
                "Continue",
                "Break",
                "Catch",
                "Do",
                "Exit",
                "Fallthrough",
                "Finally"
            ]
        );
    }

    #[test]
    fn derived_functions() {
        // The order is that of the constructors.
        let all = all();
        for (i, a) in all.iter().enumerate() {
            for (j, b) in all.iter().enumerate() {
                assert_eq!(compare(a, b), i.cmp(&j));
                assert_eq!(equal(a, b), i == j);
            }
        }
        assert_eq!(compare(&T::Next, &T::Finally), Ordering::Less);
        assert_eq!(show(&T::Fallthrough), "Typing_cont_key.Fallthrough");
        // The same type as `Typing_continuations.t`.
        let k: crate::typing_continuations::T = T::Do;
        assert!(equal(&k, &T::Do));
    }
}
