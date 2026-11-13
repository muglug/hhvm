// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tvid.ml`. See `hh/PORTING.md`.
//!
//! [`T`] is `isize`, as in `oxidized::tvid`, `crate::typing_defs_core`
//! (`Ty_::Tvar(isize)`) and `crate::typing_reason`.
//!
//! [`Provider`] is a handle on a counter: the clones of a provider (those of
//! a typing environment) share it. See `crate::ident_provider`.

use crate::ident_provider;

/// A type variable id
pub type T = ident_provider::ident::T;

pub type Provider = ident_provider::T;

/// `[@@deriving eq]`
pub fn equal(a: T, b: T) -> bool {
    ident_provider::ident::equal(a, b)
}

/// `[@@deriving ord]`
pub fn compare(a: T, b: T) -> std::cmp::Ordering {
    ident_provider::ident::compare(a, b)
}

/// `[@@deriving show]`
pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
    write!(fmt, "{}", ident_provider::ident::show(t))
}

/// `[@@deriving show]`
pub fn show(t: T) -> String {
    ident_provider::ident::show(t)
}

pub fn make(provider: &Provider) -> T {
    ident_provider::provide(provider)
}

pub fn make_provider() -> Provider {
    ident_provider::init()
}

/// `Tvid.Map`: the map of `oxidized::tvid`, which the callers use.
///
/// In OCaml this is `Ident_provider.Ident.Map`; `crate::ident_provider` has
/// another type for that (`im::OrdMap`), so the two are not interchangeable
/// here.
pub mod map {
    pub use oxidized::tvid::map::Map;
    /// `Tvid.Map.t`
    pub type T<V> = Map<V>;
}

/// `Tvid.Set`: the set of `oxidized::tvid`, which the callers use (see
/// [`map`]).
pub mod set {
    pub use oxidized::tvid::set::Set;
    /// `Tvid.Set.t`
    pub type T = Set;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn make_counts_from_zero() {
        let provider = make_provider();
        assert_eq!(make(&provider), 0);
        assert_eq!(make(&provider), 1);
        assert_eq!(show(make(&provider)), "2");
    }

    #[test]
    fn a_cloned_provider_shares_the_counter() {
        // What cloning a typing environment does to its `tvar_id_provider`.
        #[derive(Clone)]
        struct Env {
            tvar_id_provider: Provider,
        }
        let env = Env {
            tvar_id_provider: make_provider(),
        };
        let v0 = make(&env.tvar_id_provider);
        let saved = env.clone();
        let v1 = make(&env.tvar_id_provider);
        let v2 = make(&saved.tvar_id_provider);
        let v3 = make(&env.tvar_id_provider);
        assert_eq!((v0, v1, v2, v3), (0, 1, 2, 3));
    }

    #[test]
    fn maps_and_sets_are_those_of_oxidized() {
        let mut s: set::T = oxidized::tvid::set::Set::new();
        s.insert(3);
        s.insert(1);
        let s2: set::Set = s;
        assert_eq!(s2.into_iter().collect::<Vec<T>>(), vec![1, 3]);
        let mut m: map::T<&str> = oxidized::tvid::map::Map::new();
        m.insert(2, "b");
        m.insert(1, "a");
        let m2: map::Map<&str> = m;
        assert_eq!(m2.into_iter().collect::<Vec<_>>(), vec![(1, "a"), (2, "b")]);
        assert!(equal(1, 1));
        assert!(!equal(1, 2));
        assert_eq!(compare(1, 2), std::cmp::Ordering::Less);
        let mut out = String::new();
        pp(&mut out, 12).unwrap();
        assert_eq!(out, "12");
    }
}
