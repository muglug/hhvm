// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/expression_id.ml`. See `hh/PORTING.md`.
//!
//! [`T`] is `isize`, as in `crate::typing_defs_core` and
//! `crate::typing_reason`.
//!
//! [`Provider`] is a handle on a counter: the clones of a provider (those of
//! a typing environment) share it. See `crate::ident_provider`.
//!
//! [`make_immutable`] is `Ident_provider.Ident.make_immutable`, which sets the
//! bit `1 lsl 62`. That is the sign bit of an OCaml integer (63 bits): an
//! immutable id is a negative number (`make_immutable 1` is
//! `-4611686018427387903`), [`display`] prints it as such
//! (`<expr#-4611686018427387903>`) and it is ordered before the other ids.
//! `crate::ident_provider` gives the same numbers on 64 bits.

use crate::ident_provider;

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

pub fn pp(fmt: &mut dyn std::fmt::Write, t: T) -> std::fmt::Result {
    write!(fmt, "{}", ident_provider::ident::show(t))
}

pub fn make(provider: &Provider) -> T {
    ident_provider::provide(provider)
}

/// `Expression_id.Map` (`Ident_provider.Ident.Map`)
pub mod map {
    pub use crate::ident_provider::ident::map::*;
}

pub fn make_provider() -> Provider {
    ident_provider::init()
}

pub fn make_immutable(t: T) -> T {
    ident_provider::ident::make_immutable(t)
}

pub fn is_immutable(t: T) -> bool {
    ident_provider::ident::is_immutable(t)
}

pub fn display(id: T) -> String {
    format!("<expr#{}>", ident_provider::ident::show(id))
}

/// Shows the internal value if the ID. Only use for debugging
pub fn debug(x: T) -> String {
    ident_provider::ident::show(x)
}

/// You probably should get your types straight before using this.
/// Hint: don't use string mingling.
pub fn dodgy_from_int(x: isize) -> T {
    ident_provider::ident::dodgy_from_int(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn make_counts_from_zero() {
        let provider = make_provider();
        assert_eq!(make(&provider), 0);
        assert_eq!(make(&provider), 1);
        assert_eq!(display(make(&provider)), "<expr#2>");
        assert_eq!(debug(dodgy_from_int(12)), "12");
    }

    #[test]
    fn a_cloned_provider_shares_the_counter() {
        // What cloning a typing environment does to its
        // `expression_id_provider`, and what `Typing_env.make_expression_id`
        // relies on when it only has `&Env`.
        #[derive(Clone)]
        struct Env {
            expression_id_provider: Provider,
        }
        let env = Env {
            expression_id_provider: make_provider(),
        };
        let e0 = make(&env.expression_id_provider);
        let saved = env.clone();
        let e1 = make(&mut saved.expression_id_provider.clone());
        let e2 = make(&env.expression_id_provider);
        let e3 = make(&saved.expression_id_provider);
        assert_eq!((e0, e1, e2, e3), (0, 1, 2, 3));
        // It is not the counter of type variables.
        let tvids = crate::tvid::make_provider();
        assert_eq!(crate::tvid::make(&tvids), 0);
        assert_eq!(make(&env.expression_id_provider), 4);
    }

    #[test]
    fn immutable() {
        let provider = make_provider();
        let _ = make(&provider);
        let id = make(&provider);
        assert_eq!(id, 1);
        assert!(!is_immutable(id));
        let imm = make_immutable(id);
        assert!(is_immutable(imm));
        assert!(!equal(imm, id));
        assert!(equal(make_immutable(imm), imm));
        // What OCaml prints: `1 lor (1 lsl 62)` is negative on 63 bits.
        assert_eq!(imm, -4611686018427387903);
        assert_eq!(display(imm), "<expr#-4611686018427387903>");
        assert_eq!(debug(imm), "-4611686018427387903");
        assert_eq!(display(make_immutable(0)), "<expr#-4611686018427387904>");
        assert_eq!(
            display(make_immutable(dodgy_from_int(41))),
            "<expr#-4611686018427387863>"
        );
        // The id is still in the low bits, and the immutable id is ordered
        // before every mutable one.
        assert_eq!(imm & ((1 << 62) - 1), id);
        assert_eq!(compare(imm, 0), std::cmp::Ordering::Less);
        assert_eq!(compare(id, id), std::cmp::Ordering::Equal);
        assert_eq!(compare(0, id), std::cmp::Ordering::Less);
        let mut out = String::new();
        pp(&mut out, id).unwrap();
        assert_eq!(out, "1");
    }
}
