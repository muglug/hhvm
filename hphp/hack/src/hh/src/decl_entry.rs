// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_entry.ml`. See `hh/PORTING.md`.

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum T<A> {
    /// The decleration does not exist in the current repo state.
    /// This sould result in a symbol not found error.
    DoesNotExist,
    /// We can't find it in the abstraction/layer that should be
    /// providing access to symbols in the current repo, but that
    /// doesn't necessarily mean it doesn't exist at all in the repo.
    /// The type checker should continue type checking but should avoid
    /// expensive behavior like backtracking as a subsequent type check
    /// is likely to be invoked with more informaiton available.
    /// Avoid expensive operations like backtracking.
    NotYetAvailable,
    /// Decl entry was found.
    Found(A),
}

pub fn of_option_or_does_not_exist<A>(x: Option<A>) -> T<A> {
    match x {
        Some(x) => T::Found(x),
        None => T::DoesNotExist,
    }
}

pub fn to_option<A>(x: T<A>) -> Option<A> {
    match x {
        T::DoesNotExist | T::NotYetAvailable => None,
        T::Found(x) => Some(x),
    }
}

pub fn bind<A, B>(x: T<A>, f: impl FnOnce(A) -> T<B>) -> T<B> {
    match x {
        T::DoesNotExist => T::DoesNotExist,
        T::NotYetAvailable => T::NotYetAvailable,
        T::Found(x) => f(x),
    }
}

pub fn map<A, B>(x: T<A>, f: impl FnOnce(A) -> B) -> T<B> {
    match x {
        T::DoesNotExist => T::DoesNotExist,
        T::NotYetAvailable => T::NotYetAvailable,
        T::Found(x) => T::Found(f(x)),
    }
}

pub fn map_or<A, B>(x: T<A>, f: impl FnOnce(A) -> B, default: B) -> B {
    match x {
        T::DoesNotExist | T::NotYetAvailable => default,
        T::Found(x) => f(x),
    }
}

pub fn iter<A>(x: T<A>, f: impl FnOnce(A)) {
    match x {
        T::DoesNotExist | T::NotYetAvailable => {}
        T::Found(x) => f(x),
    }
}

pub fn fold<A, B>(x: T<A>, f: impl FnOnce(B, A) -> B, init: B) -> B {
    match x {
        T::DoesNotExist | T::NotYetAvailable => init,
        T::Found(x) => f(init, x),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn options() {
        assert_eq!(of_option_or_does_not_exist(Some(1)), T::Found(1));
        assert_eq!(of_option_or_does_not_exist::<i32>(None), T::DoesNotExist);
        assert_eq!(to_option(T::Found(1)), Some(1));
        assert_eq!(to_option::<i32>(T::DoesNotExist), None);
        assert_eq!(to_option::<i32>(T::NotYetAvailable), None);
    }

    #[test]
    fn combinators_keep_the_two_kinds_of_absence_apart() {
        assert_eq!(map(T::Found(1), |x| x + 1), T::Found(2));
        assert_eq!(map(T::<i32>::DoesNotExist, |x| x + 1), T::DoesNotExist);
        assert_eq!(
            map(T::<i32>::NotYetAvailable, |x| x + 1),
            T::NotYetAvailable
        );
        assert_eq!(bind(T::Found(1), |x| T::Found(x + 1)), T::Found(2));
        assert_eq!(
            bind(T::Found(1), |_| T::<i32>::NotYetAvailable),
            T::NotYetAvailable
        );
        assert_eq!(
            bind(T::<i32>::NotYetAvailable, |x| T::Found(x)),
            T::NotYetAvailable
        );
        assert_eq!(
            bind(T::<i32>::DoesNotExist, |x| T::Found(x)),
            T::DoesNotExist
        );
        assert_eq!(map_or(T::Found(1), |x| x + 1, 0), 2);
        assert_eq!(map_or(T::<i32>::NotYetAvailable, |x| x + 1, 0), 0);
        assert_eq!(fold(T::Found(1), |acc, x| acc + x, 10), 11);
        assert_eq!(fold(T::<i32>::DoesNotExist, |acc, x| acc + x, 10), 10);
        let mut seen = vec![];
        iter(T::Found(1), |x| seen.push(x));
        iter(T::<i32>::DoesNotExist, |x| seen.push(x));
        assert_eq!(seen, vec![1]);
    }
}
