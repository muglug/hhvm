// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_continuations.ml`. See `hh/PORTING.md`.
//!
//! The OCaml module is `include Typing_cont_key` plus `Map`, so the contents
//! of `typing_cont_key.ml` are here too.

/// `Typing_cont_key.t`. The order of the constructors is the order of the
/// keys of `Map` (OCaml's derived `compare`).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum T {
    Next,
    Continue,
    Break,
    Catch,
    Do,
    Exit,
    Fallthrough,
    Finally,
}

pub fn equal(a: &T, b: &T) -> bool {
    a == b
}

pub fn compare(a: &T, b: &T) -> std::cmp::Ordering {
    a.cmp(b)
}

/// `[@@deriving show]`: the constructor qualified by the module that defines
/// it.
pub fn show(t: &T) -> String {
    format!("Typing_cont_key.{}", to_string(t))
}

pub fn all() -> Vec<T> {
    vec![
        T::Next,
        T::Continue,
        T::Break,
        T::Catch,
        T::Do,
        T::Exit,
        T::Fallthrough,
        T::Finally,
    ]
}

pub fn to_string(t: &T) -> String {
    match t {
        T::Next => "Next",
        T::Continue => "Continue",
        T::Break => "Break",
        T::Catch => "Catch",
        T::Do => "Do",
        T::Exit => "Exit",
        T::Fallthrough => "Fallthrough",
        T::Finally => "Finally",
    }
    .to_string()
}

impl crate::pmap::Key for T {
    #[inline]
    fn prefix(&self) -> u64 {
        *self as u64
    }
    const EXACT: bool = true;
}

/// `Wrapped_map.Make (Typing_cont_key)`.
pub mod map {
    pub type T<V> = crate::pmap::Map<super::T, V>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_is_declaration_order() {
        let mut sorted = all();
        sorted.reverse();
        sorted.sort();
        assert_eq!(sorted, all());
        assert!(T::Next < T::Continue && T::Fallthrough < T::Finally);
    }

    #[test]
    fn printing() {
        assert_eq!(to_string(&T::Fallthrough), "Fallthrough");
        assert_eq!(show(&T::Next), "Typing_cont_key.Next");
    }

    #[test]
    fn map_iterates_in_key_order() {
        let m: map::T<u8> = [(T::Finally, 0), (T::Next, 1), (T::Catch, 2)]
            .into_iter()
            .collect();
        assert_eq!(
            m.keys().copied().collect::<Vec<_>>(),
            vec![T::Next, T::Catch, T::Finally]
        );
    }
}
