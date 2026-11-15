// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `heap/ident_provider.ml`. See `hh/PORTING.md`.

use std::cell::Cell;
use std::rc::Rc;

/// `int ref`: a counter. The copies of a provider (`clone`) share it, like
/// the copies of the environment that holds it share the `ref` in OCaml.
#[derive(Clone, Debug)]
pub struct T(Rc<Cell<isize>>);

pub mod ident {
    pub type T = isize;

    /// `Ident.Map`: the functions of `Stdlib.Map` are the methods of the map,
    /// and the ones `Wrapped_map` adds are here.
    pub mod map {
        pub use crate::wrapped_map::*;

        pub type T<A> = im::OrdMap<super::T, A>;
    }

    /// `Ident.Set`
    pub mod set {
        pub type T = im::OrdSet<super::T>;
    }

    pub fn equal(x: T, y: T) -> bool {
        x == y
    }

    pub fn compare(x: T, y: T) -> std::cmp::Ordering {
        x.cmp(&y)
    }

    pub fn show(x: T) -> String {
        x.to_string()
    }

    /// `1 lsl 62`. OCaml integers have 63 bits, of which bit 62 is the sign
    /// bit: the mask is `min_int`, `-4611686018427387904`, and an immutable
    /// identifier is a negative number (`make_immutable 1` is
    /// `-4611686018427387903`). It is printed as such (`<expr#-46...>`) and
    /// ordered before the other identifiers. On 64 bits the same number has
    /// the bits 62 and 63 set, which is what this is: for every identifier
    /// an OCaml integer can hold, `is_immutable` and `make_immutable` give
    /// the OCaml results.
    pub const IMMUTABLE_MASK: isize = -(1 << 62);

    pub fn is_immutable(i: T) -> bool {
        i & IMMUTABLE_MASK != 0
    }

    pub fn make_immutable(i: T) -> T {
        i | IMMUTABLE_MASK
    }

    pub fn dodgy_from_int(i: isize) -> T {
        i
    }
}

pub fn init() -> T {
    T(Rc::new(Cell::new(0)))
}

/// The identifier that [`provide`] would hand out next (no OCaml
/// counterpart: lets a caller see whether a computation made identifiers).
pub fn peek(provider: &T) -> ident::T {
    provider.0.get()
}

pub fn provide(provider: &T) -> ident::T {
    let id = provider.0.get();
    provider.0.set(id + 1);
    id
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_identifiers() {
        let provider = init();
        assert_eq!(provide(&provider), 0);
        assert_eq!(provide(&provider), 1);
        // A copy hands out the identifiers that follow.
        let copy = provider.clone();
        assert_eq!(provide(&copy), 2);
        assert_eq!(provide(&provider), 3);
        // Another provider starts again.
        assert_eq!(provide(&init()), 0);
    }

    #[test]
    fn copies_of_copies_share_the_counter() {
        let provider = init();
        let copy = provider.clone();
        let copy_of_copy = copy.clone();
        drop(provider);
        assert_eq!(provide(&copy_of_copy), 0);
        assert_eq!(provide(&copy), 1);
        assert_eq!(provide(&copy_of_copy), 2);
    }

    #[test]
    fn immutable() {
        assert!(!ident::is_immutable(5));
        assert!(!ident::is_immutable(0));
        let i = ident::make_immutable(5);
        assert!(ident::is_immutable(i));
        // The numbers of OCaml (63-bit integers), where `1 lsl 62` is
        // `min_int`: `5 lor (1 lsl 62)` is `-4611686018427387899`.
        assert_eq!(ident::IMMUTABLE_MASK, -4611686018427387904);
        assert_eq!(i, -4611686018427387899);
        assert_eq!(ident::make_immutable(0), -4611686018427387904);
        assert_eq!(ident::show(ident::make_immutable(1)), "-4611686018427387903");
        // The identifier is still in the low bits, and the result is ordered
        // before the mutable identifiers, as in OCaml.
        assert_eq!(i & ((1 << 62) - 1), 5);
        assert_eq!(ident::compare(i, 0), std::cmp::Ordering::Less);
        assert_eq!(ident::make_immutable(i), i);
        // `dodgy_from_int` of a printed immutable identifier gives it back
        // (`Typing_escape` parses `<expr#N>`).
        assert_eq!(ident::dodgy_from_int(-4611686018427387899), i);
        assert_eq!(ident::show(12), "12");
        assert_eq!(ident::dodgy_from_int(7), 7);
    }
}
