// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/local_id.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::local_id::LocalId` (`int * string`), re-exported
//! here with `make_unscoped` and `get_name`. This module has the rest.
//! (`make_unscoped`: make an id for an unscoped variable. Two calls with the
//! same input string will return the same id.)
//!
//! Not here: `pp`, `Map.pp`, `Map.show` and `Map.hash_fold_t`.

use std::sync::atomic::AtomicIsize;
use std::sync::atomic::Ordering;

pub use oxidized::local_id::*;

pub type T = LocalId;

/// The counter is global, as in OCaml: two scoped identifiers never have the
/// same number, whatever thread made them.
static CTR: AtomicIsize = AtomicIsize::new(1);

fn next() -> isize {
    // `incr ctr; !ctr`
    CTR.fetch_add(1, Ordering::Relaxed) + 1
}

pub fn equal(x: &T, y: &T) -> bool {
    x == y
}

/// By number, then by name.
pub fn compare(x: &T, y: &T) -> std::cmp::Ordering {
    (x.0.cmp(&y.0)).then_with(|| x.1.as_bytes().cmp(y.1.as_bytes()))
}

pub fn to_string(x: &T) -> String {
    x.1.clone()
}

pub fn to_int(x: &T) -> isize {
    x.0
}

/// Could this local variable have been written by the user, as opposed to an
/// internally generated variable?
/// Yes: $foo, $_bar1, $$
/// No: $#foo, $0bar
pub fn is_user_denotable(lid: &T) -> bool {
    let lid_s = lid.1.as_bytes();
    // Allow $foo or $_bar1 but not $#foo or $0bar.
    //
    // `Str.string_match (Str.regexp "^\\$[a-zA-z_][a-zA-Z0-9_]*$") lid_s 0`.
    // The range `A-z` of the first set is as it is written: the letters,
    // and the six characters between `Z` and `a` (`_` is one of them). `$`
    // is the end of the string, or the end of a line.
    let matches_local_regexp = match lid_s {
        [b'$', b'A'..=b'z', rest @ ..] => {
            let after = rest
                .iter()
                .position(|c| !(c.is_ascii_alphanumeric() || *c == b'_'));
            match after {
                None => true,
                Some(i) => rest[i] == b'\n',
            }
        }
        _ => false,
    };
    matches_local_regexp || lid_s == b"$$"
}

/// Returns a fresh id every time. This is used to enforce that two locals
/// with the same name but with different scopes have different ids.
pub fn make_scoped(x: &str) -> T {
    (next(), x.to_string())
}

pub fn make(i: isize, x: &str) -> T {
    (i, x.to_string())
}

pub fn tmp() -> T {
    let res = next();
    (res, format!("__tmp{}", res))
}

/// `Local_id.Set`
pub mod set {
    pub use oxidized::local_id::set::*;

    pub type T = im::OrdSet<super::T>;
}

/// `Local_id.Map`: the functions of `Stdlib.Map` are the methods of the map,
/// and the ones `Wrapped_map` adds are here.
pub mod map {
    pub use oxidized::local_id::map::*;

    pub use crate::wrapped_map::*;

    pub type T<A> = im::OrdMap<super::T, A>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn denotable() {
        let ok = |s: &str| is_user_denotable(&make_unscoped(s));
        assert!(ok("$foo"));
        assert!(ok("$_bar1"));
        assert!(ok("$$"));
        assert!(ok("$x"));
        assert!(ok("$this"));
        assert!(!ok("$#foo"));
        assert!(!ok("$0bar"));
        assert!(!ok("$"));
        assert!(!ok(""));
        assert!(!ok("foo"));
        assert!(!ok("$foo bar"));
        assert!(!ok("$foo$"));
        assert!(!ok("$$$"));
        // The first set is `[a-zA-z_]`: `A-z` has `[`, `\`, `]`, `^`, `_`
        // and the backquote.
        assert!(ok("$[x"));
        assert!(ok("$^"));
        assert!(!ok("$x["));
        assert!(!ok("$@x"));
        assert!(!ok("${x"));
        // `$` also matches at the end of a line.
        assert!(ok("$foo\nbar"));
        assert!(!ok("$foo\rbar"));
        // Not ASCII letters.
        assert!(!ok("$é"));
    }

    #[test]
    fn ids() {
        assert_eq!(make_unscoped("$x"), (0, "$x".to_string()));
        assert_eq!(make(3, "$x"), (3, "$x".to_string()));
        let a = make_scoped("$x");
        let b = make_scoped("$x");
        // Fresh ids: more than 1, and different.
        assert!(to_int(&a) > 1 && to_int(&b) > 1 && to_int(&a) != to_int(&b));
        assert!(!equal(&a, &b));
        assert_eq!(to_string(&a), "$x");
        assert_eq!(get_name(&a), "$x");
        let t = tmp();
        assert_eq!(to_string(&t), format!("__tmp{}", to_int(&t)));
        // By number first.
        assert_eq!(
            compare(&make(1, "$z"), &make(2, "$a")),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            compare(&make(1, "$a"), &make(1, "$b")),
            std::cmp::Ordering::Less
        );
    }
}
