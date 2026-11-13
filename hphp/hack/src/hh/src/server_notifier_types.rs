// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server_notifier_types.ml`. See `hh/PORTING.md`.
//!
//! `Watchman.clock` and `Edenfs_watcher.clock` are both `string`
//! (`watchman/watchman_sig.ml`, `stubs/edenfs_watcher.ml`), and have no Rust
//! module yet: they are `String` here.

use crate::format;
use crate::format::Formatter;
use crate::rt::ocaml_printf::sprintf_S;

/// `Server_notifier_types.clock`
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Clock {
    Watchman(String),
    Eden(String),
}

/// `pp_clock` (`[@@deriving show]`): `(Server_notifier_types.Watchman "c:1:2")`.
pub fn pp_clock(fmt: &mut Formatter, clock: &Clock) {
    let (ctor, a0) = match clock {
        Clock::Watchman(a0) => ("Server_notifier_types.Watchman", a0),
        Clock::Eden(a0) => ("Server_notifier_types.Eden", a0),
    };
    // "(@[<2>%s@ " ctor, the argument ("%S"), "@])"
    format::pp_print_string(fmt, "(");
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, ctor);
    format::pp_print_space(fmt);
    format::pp_print_string(fmt, &sprintf_S(a0));
    format::pp_close_box(fmt);
    format::pp_print_string(fmt, ")");
}

/// `show_clock`
pub fn show_clock(clock: &Clock) -> String {
    format::asprintf(|fmt| pp_clock(fmt, clock))
}

/// `equal_clock` (`[@@deriving eq]`)
pub fn equal_clock(a: &Clock, b: &Clock) -> bool {
    a == b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn show() {
        assert_eq!(
            show_clock(&Clock::Watchman("c:123:4".to_string())),
            r#"(Server_notifier_types.Watchman "c:123:4")"#
        );
        assert_eq!(
            show_clock(&Clock::Eden("x\"y".to_string())),
            r#"(Server_notifier_types.Eden "x\"y")"#
        );
        assert!(equal_clock(
            &Clock::Eden("a".to_string()),
            &Clock::Eden("a".to_string())
        ));
        assert!(!equal_clock(
            &Clock::Eden("a".to_string()),
            &Clock::Watchman("a".to_string())
        ));
    }
}
