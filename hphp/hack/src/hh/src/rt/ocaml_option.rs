// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the functions of `Base`'s `Option` (`Core.Option`) that the ported
//! modules use and that Rust's `Option` has no method for.

/// `Option.merge a b ~f`
pub fn merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, b) => b,
        (a, None) => a,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_is_that_of_base() {
        let f = |a: isize, b: isize| a * 10 + b;
        assert_eq!(merge(None, None, f), None);
        assert_eq!(merge(Some(1), None, f), Some(1));
        assert_eq!(merge(None, Some(2), f), Some(2));
        // `f` gets the first argument first.
        assert_eq!(merge(Some(1), Some(2), f), Some(12));
    }
}
