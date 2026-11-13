// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tany_sentinel.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::tany_sentinel::TanySentinel` (the argument of
//! `Ty_::Tany`), re-exported here. `[@@deriving hash]` is its `Hash`.

pub use oxidized::tany_sentinel::*;

/// `Tany_sentinel.t`
pub type T = TanySentinel;

/// `[@@deriving eq]`
pub fn equal(a: &T, b: &T) -> bool {
    a == b
}

pub fn value() -> T {
    TanySentinel
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_is_the_only_value() {
        assert!(equal(&value(), &value()));
        assert_eq!(value(), oxidized::tany_sentinel::TanySentinel);
    }
}
