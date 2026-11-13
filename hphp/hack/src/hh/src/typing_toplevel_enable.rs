// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_toplevel_enable.ml`. See `hh/PORTING.md`.
//!
//! `id` is a `'a * string` in OCaml; every caller passes the name of a
//! definition (`Ast_defs.id`), so it is an `ast_defs::Id` here.
//!
//! The regular expression of `--config typecheck_if_name_matches_regexp` is
//! an OCaml `Str` regular expression: it is translated to a Rust one by
//! `crate::files::ignored_path_regexes`, which anchors it at the start of the
//! string, as `Str.string_match re s 0` does (as `typing_packages` does for
//! its patterns).

use oxidized::ast_defs;

use crate::typechecker_options::TypecheckerOptions;
use crate::typing_env as env;
use crate::typing_env_types::Env;

/// `Str.string_match (Str.regexp regexp) s 0`
fn str_string_match(regexp: &str, s: &str) -> bool {
    // `Str.regexp` raises `Failure` on a malformed regular expression, which
    // nothing catches.
    let re = match crate::files::ignored_path_regexes(&[regexp.to_string()]) {
        Ok(mut res) => res.remove(0),
        Err(e) => panic!("{}", e),
    };
    re.is_match(s)
}

/// Typecheck only definitions whose identifier matches the regular expression.
pub fn if_matches_regexp<B>(
    default: B,
    tcopt: &TypecheckerOptions,
    env_opt: Option<&Env>,
    id: &ast_defs::Id,
    f: impl FnOnce() -> B,
) -> B {
    // `Typechecker_options.typecheck_if_name_matches_regexp`
    match &tcopt.tco_typecheck_if_name_matches_regexp {
        None => f(),
        Some(regexp) => {
            let id = match env_opt.and_then(env::get_self_id) {
                Some(class_name) => class_name + "::" + &id.1,
                None => id.1.clone(),
            };
            if str_string_match(regexp, &id) {
                f()
            } else {
                default
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn str_string_match_is_anchored_at_the_start_only() {
        assert!(str_string_match("foo", "foobar"));
        assert!(str_string_match("Foo::.*", "Foo::bar"));
        assert!(!str_string_match("bar", "foobar"));
        // `Str` groups and alternates with `\(`, `\)` and `\|`.
        assert!(str_string_match("\\(a\\|b\\)c", "bcd"));
        assert!(!str_string_match("(a|b)c", "bc"));
    }
}
