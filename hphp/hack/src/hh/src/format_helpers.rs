// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `format_helpers.ml`. See `hh/PORTING.md`.
//!
//! Combinators over `Format.formatter` (`crate::format::Formatter`). A
//! printer of `'a` (`Format.formatter -> 'a -> unit`) is a function
//! `(&mut Formatter, A)`; `A` is often a reference.
//!
//! - The combinators take all their arguments, as their OCaml definitions do
//!   (`prefix pp_pfx pp_v ppf v`). Where OCaml applies one partially
//!   (`Fmt.(prefix (const string "?") pp_v)`), the caller writes a closure.
//! - The printers that are only ever called with `()` (separators, the
//!   branches of `cond`, the `?none` of `option`, the prefix of `prefix`...)
//!   take `()`: OCaml's are polymorphic in that argument (`sp ppf _`), but
//!   every call passes `()`.
//! - `const` is defined twice in `format_helpers.ml`: `const str ppf _ =
//!   string ppf str`, which `dbl_colon` and `dbl_hash` use, and then `const
//!   pp_v v ppf _ = pp_v ppf v`, which shadows it and is the one the module
//!   exports. Here the first is the private `const_str` and the second is
//!   [`const_`].

use crate::format;
use crate::format::Formatter;

/// A printer that is called with `()`, as the optional `?sep` and `?none`
/// arguments are.
pub type Sep<'a> = &'a dyn Fn(&mut Formatter, ());

/// `pf fmt = Format.fprintf fmt`. A Rust format string has no break hints and
/// no boxes (`@ `, `@[`) and no `%a`: the text it makes is printed as one
/// string, which is what `Format.fprintf` prints for a format string without
/// them. Write the others as calls (see the documentation of `crate::format`).
pub fn pf(fmt: &mut Formatter, args: std::fmt::Arguments<'_>) {
    format::pp_print_string(fmt, &std::fmt::format(args))
}

pub fn string(ppf: &mut Formatter, s: &str) {
    format::pp_print_string(ppf, s)
}

pub fn sp(ppf: &mut Formatter, _: ()) {
    format::pp_print_space(ppf)
}

pub fn cut(ppf: &mut Formatter, _: ()) {
    format::pp_print_cut(ppf)
}

/// `Format.asprintf "%a" pp_v v`
pub fn to_to_string<A>(pp_v: impl FnOnce(&mut Formatter, A), v: A) -> String {
    format::asprintf(|ppf| pp_v(ppf, v))
}

pub fn of_to_string<A>(f: impl Fn(A) -> String, ppf: &mut Formatter, v: A) {
    string(ppf, &f(v))
}

pub fn cond(
    pp_t: impl Fn(&mut Formatter, ()),
    pp_f: impl Fn(&mut Formatter, ()),
    ppf: &mut Formatter,
    test: bool,
) {
    if test { pp_t(ppf, ()) } else { pp_f(ppf, ()) }
}

/// `sep` defaults to [`sp`].
pub fn pair<A, B>(
    sep: Option<Sep<'_>>,
    pp_a: impl Fn(&mut Formatter, A),
    pp_b: impl Fn(&mut Formatter, B),
    ppf: &mut Formatter,
    (a, b): (A, B),
) {
    let pp_sep: Sep<'_> = match sep {
        Some(pp_sep) => pp_sep,
        None => &sp,
    };
    pp_a(ppf, a);
    pp_sep(ppf, ());
    pp_b(ppf, b)
}

/// `sep` defaults to [`sp`].
pub fn triple<A, B, C>(
    sep: Option<Sep<'_>>,
    pp_a: impl Fn(&mut Formatter, A),
    pp_b: impl Fn(&mut Formatter, B),
    pp_c: impl Fn(&mut Formatter, C),
    ppf: &mut Formatter,
    (a, b, c): (A, B, C),
) {
    let pp_sep: Sep<'_> = match sep {
        Some(pp_sep) => pp_sep,
        None => &sp,
    };
    pp_a(ppf, a);
    pp_sep(ppf, ());
    pp_b(ppf, b);
    pp_sep(ppf, ());
    pp_c(ppf, c)
}

pub fn prefix<A>(
    pp_pfx: impl Fn(&mut Formatter, ()),
    pp_v: impl Fn(&mut Formatter, A),
    ppf: &mut Formatter,
    v: A,
) {
    pp_pfx(ppf, ());
    pp_v(ppf, v)
}

pub fn suffix<A>(
    pp_sfx: impl Fn(&mut Formatter, ()),
    pp_v: impl Fn(&mut Formatter, A),
    ppf: &mut Formatter,
    v: A,
) {
    pp_v(ppf, v);
    pp_sfx(ppf, ())
}

pub fn surround<A>(
    l: &str,
    r: &str,
    pp_v: impl Fn(&mut Formatter, A),
    ppf: &mut Formatter,
    v: A,
) {
    string(ppf, l);
    pp_v(ppf, v);
    string(ppf, r)
}

pub fn quote<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    surround("'", "'", pp_v, ppf, v)
}

pub fn parens<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    surround("(", ")", pp_v, ppf, v)
}

pub fn braces<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    surround("{", "}", pp_v, ppf, v)
}

pub fn angles<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    surround("<", ">", pp_v, ppf, v)
}

pub fn brackets<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    surround("[", "]", pp_v, ppf, v)
}

pub fn comma(ppf: &mut Formatter, _: ()) {
    string(ppf, ",");
    sp(ppf, ())
}

pub fn amp(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, "&");
    sp(ppf, ())
}

pub fn equal_to(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, "=");
    sp(ppf, ())
}

pub fn colon(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, ":");
    sp(ppf, ())
}

pub fn semicolon(ppf: &mut Formatter, _: ()) {
    string(ppf, ";")
}

pub fn semi_sep(ppf: &mut Formatter, _: ()) {
    semicolon(ppf, ());
    sp(ppf, ())
}

pub fn arrow(ppf: &mut Formatter, _: ()) {
    string(ppf, "->")
}

pub fn with_(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, "with");
    sp(ppf, ())
}

pub fn fat_arrow(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, "=>");
    sp(ppf, ())
}

/// The first `const` of `format_helpers.ml` (`const str ppf _ = string ppf
/// str`), which the second shadows: only `dbl_colon` and `dbl_hash` use it.
fn const_str(str: &str, ppf: &mut Formatter, _: ()) {
    string(ppf, str)
}

pub fn dbl_colon(v: &mut Formatter, x: ()) {
    const_str("::", v, x)
}

pub fn dbl_hash(v: &mut Formatter, x: ()) {
    const_str("#", v, x)
}

pub fn vbar(ppf: &mut Formatter, _: ()) {
    sp(ppf, ());
    string(ppf, "|");
    sp(ppf, ())
}

pub fn nop(_: &mut Formatter, _: ()) {}

/// The second `const` of `format_helpers.ml`, the one it exports.
pub fn const_<A>(pp_v: impl Fn(&mut Formatter, A), v: A, ppf: &mut Formatter, _: ()) {
    pp_v(ppf, v)
}

/// `none` defaults to [`nop`].
pub fn option<A>(
    none: Option<Sep<'_>>,
    pp_v: impl Fn(&mut Formatter, A),
    ppf: &mut Formatter,
    v: Option<A>,
) {
    let pp_none: Sep<'_> = match none {
        Some(pp_none) => pp_none,
        None => &nop,
    };
    match v {
        Some(v) => pp_v(ppf, v),
        _ => pp_none(ppf, ()),
    }
}

/// `sep` defaults to [`sp`].
pub fn list<A>(
    sep: Option<Sep<'_>>,
    pp_elt: impl Fn(&mut Formatter, &A),
    ppf: &mut Formatter,
    v: &[A],
) {
    let pp_sep: Sep<'_> = match sep {
        Some(pp_sep) => pp_sep,
        None => &sp,
    };
    let mut is_first = true;
    let mut pp_elt = |ppf: &mut Formatter, v: &A| {
        if is_first {
            is_first = false
        } else {
            pp_sep(ppf, ())
        }
        pp_elt(ppf, v)
    };
    for v in v {
        pp_elt(ppf, v)
    }
}

pub fn hbox<A>(pp_v: impl Fn(&mut Formatter, A), ppf: &mut Formatter, v: A) {
    format::pp_open_hbox(ppf);
    pp_v(ppf, v);
    format::pp_close_box(ppf)
}

/// `indent` defaults to 0.
pub fn vbox<A>(
    indent: Option<isize>,
    pp_v: impl Fn(&mut Formatter, A),
    ppf: &mut Formatter,
    v: A,
) {
    let indent = indent.unwrap_or(0);
    format::pp_open_vbox(ppf, indent);
    pp_v(ppf, v);
    format::pp_close_box(ppf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn print(pp: impl FnOnce(&mut Formatter)) -> String {
        format::asprintf(pp)
    }

    /// The expected outputs are those of the OCaml (`format_helpers.ml` and
    /// OCaml 5's `Format`) for the same calls. Outside of a box, the last
    /// break hint breaks the line (see the tests of `crate::format`).
    #[test]
    fn combinators() {
        let ints = [1, 2, 3];
        let pp_int = |ppf: &mut Formatter, i: &i32| string(ppf, &i.to_string());
        assert_eq!(
            print(|ppf| list(Some(&comma), pp_int, ppf, &ints)),
            "1, 2,\n3"
        );
        assert_eq!(print(|ppf| list(None, pp_int, ppf, &ints)), "1 2\n3");
        assert_eq!(print(|ppf| list(None, pp_int, ppf, &[] as &[i32])), "");
        assert_eq!(
            print(|ppf| parens(|ppf, v| list(Some(&vbar), pp_int, ppf, v), ppf, &ints[..])),
            "(1 | 2 |\n3)"
        );
        assert_eq!(
            print(|ppf| pair(Some(&dbl_colon), string, string, ppf, ("C", "f"))),
            "C::f"
        );
        assert_eq!(
            print(|ppf| pair(None, string, string, ppf, ("a", "b"))),
            "a\nb"
        );
        assert_eq!(
            print(|ppf| triple(Some(&fat_arrow), string, string, string, ppf, ("a", "b", "c"))),
            "a => b =>\nc"
        );
        assert_eq!(
            print(|ppf| prefix(|ppf, ()| const_(string, "?", ppf, ()), string, ppf, "int")),
            "?int"
        );
        assert_eq!(
            print(|ppf| suffix(sp, string, ppf, "inout")),
            "inout\n"
        );
        assert_eq!(print(|ppf| quote(string, ppf, "k")), "'k'");
        assert_eq!(print(|ppf| angles(string, ppf, "T")), "<T>");
        assert_eq!(print(|ppf| braces(string, ppf, "x")), "{x}");
        assert_eq!(print(|ppf| brackets(string, ppf, "x")), "[x]");
        assert_eq!(print(|ppf| option(None, string, ppf, None)), "");
        assert_eq!(
            print(|ppf| option(Some(&|ppf, ()| string(ppf, "none")), string, ppf, None)),
            "none"
        );
        assert_eq!(print(|ppf| option(None, string, ppf, Some("x"))), "x");
        assert_eq!(
            print(|ppf| cond(|ppf, ()| string(ppf, "?"), nop, ppf, true)),
            "?"
        );
        assert_eq!(print(|ppf| cond(|ppf, ()| string(ppf, "?"), nop, ppf, false)), "");
        assert_eq!(print(|ppf| amp(ppf, ())), " &\n");
        assert_eq!(print(|ppf| equal_to(ppf, ())), " =\n");
        assert_eq!(print(|ppf| colon(ppf, ())), " :\n");
        assert_eq!(print(|ppf| semi_sep(ppf, ())), ";\n");
        assert_eq!(print(|ppf| arrow(ppf, ())), "->");
        assert_eq!(print(|ppf| with_(ppf, ())), " with\n");
        assert_eq!(print(|ppf| dbl_hash(ppf, ())), "#");
        assert_eq!(print(|ppf| cut(ppf, ())), "\n");
        assert_eq!(
            print(|ppf| of_to_string(|i: i32| i.to_string(), ppf, 7)),
            "7"
        );
        assert_eq!(to_to_string(string, "abc"), "abc");
        assert_eq!(print(|ppf| pf(ppf, format_args!("{}-{}", 1, 2))), "1-2");
        assert_eq!(
            print(|ppf| vbox(Some(2), |ppf, v| list(None, pp_int, ppf, v), ppf, &ints[..])),
            "1\n  2\n  3"
        );
        assert_eq!(
            print(|ppf| hbox(|ppf, v| list(None, pp_int, ppf, v), ppf, &ints[..])),
            "1 2 3"
        );
    }
}
