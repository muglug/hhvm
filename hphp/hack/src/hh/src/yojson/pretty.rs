// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lib/pretty.ml` of Yojson 2.0.2 (the version the OCaml build
//! used): the pretty printer (`Server_progress` writes `progress.json` with
//! it), transliterated (`std = false`) on the crate's port of `Format`, so
//! line breaks and indentation are those of OCaml.

use crate::format;
use crate::format::Formatter;
use crate::yojson::safe as yojson;
use crate::yojson::safe::T;

// ~~ Pretty-printing (lib/pretty.ml) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `json_string_of_float` (not `std`), the same as the compact printer's.
fn json_string_of_float(x: f64) -> String {
    yojson::to_string(&T::Float(x))
}

/// `json_string_of_string`
fn json_string_of_string(s: &str) -> String {
    yojson::to_string(&T::String(s.to_string()))
}

/// `pp_list sep ppx out l`: the elements separated by `sep` and a break.
fn pp_list<A>(sep: &str, ppx: impl Fn(&mut Formatter, &A), out: &mut Formatter, l: &[A]) {
    // let pp_sep out () = Format.fprintf out "%s@ " sep in
    // Format.pp_print_list ~pp_sep ppx out l
    for (i, x) in l.iter().enumerate() {
        if i > 0 {
            format::pp_print_string(out, sep);
            format::pp_print_space(out);
        }
        ppx(out, x)
    }
}

fn is_atom(x: &T) -> bool {
    match x {
        T::Null | T::Bool(_) | T::Int(_) | T::Float(_) | T::String(_) | T::Intlit(_) => true,
        T::List(l) => l.is_empty(),
        T::Assoc(l) => l.is_empty(),
    }
}

fn is_atom_list(l: &[T]) -> bool {
    l.iter().all(is_atom)
}

/// `format ~inside_box std out x`. `inside_box` indicates that we're already
/// within a box that imposes a certain style and we shouldn't create a new
/// one. This is used for printing field values like this:
///
/// ```text
///   foo: [
///     bar
///   ]
/// ```
///
/// rather than something else like
///
/// ```text
///   foo:
///     [
///       bar
///     ]
/// ```
fn format_(inside_box: bool, out: &mut Formatter, x: &T) {
    match x {
        T::Null => format::pp_print_string(out, "null"),
        T::Bool(x) => format::pp_print_string(out, if *x { "true" } else { "false" }),
        T::Int(x) => format::pp_print_string(out, &x.to_string()),
        T::Float(x) => format::pp_print_string(out, &json_string_of_float(*x)),
        T::String(s) => format::pp_print_string(out, &json_string_of_string(s)),
        T::Intlit(s) => format::pp_print_string(out, s),
        T::List(l) if l.is_empty() => format::pp_print_string(out, "[]"),
        T::List(l) => {
            if !inside_box {
                format::pp_open_hvbox(out, 2);
            }
            // "[@;<1 0>@[<hov>%a@]@;<1 -2>]" when it is a list of atoms (use
            // line wrapping like we would do for a paragraph of text);
            // "[@;<1 0>@[<hv>%a@]@;<1 -2>]" otherwise (print the elements
            // horizontally if they fit on the line, otherwise in a column)
            format::pp_print_string(out, "[");
            format::pp_print_break(out, 1, 0);
            if is_atom_list(l) {
                format::pp_open_hovbox(out, 0);
            } else {
                format::pp_open_hvbox(out, 0);
            }
            pp_list(",", |out, x| format_(false, out, x), out, l);
            format::pp_close_box(out);
            format::pp_print_break(out, 1, -2);
            format::pp_print_string(out, "]");
            if !inside_box {
                format::pp_close_box(out);
            }
        }
        T::Assoc(l) if l.is_empty() => format::pp_print_string(out, "{}"),
        T::Assoc(l) => {
            if !inside_box {
                format::pp_open_hvbox(out, 2);
            }
            // "{@;<1 0>%a@;<1 -2>}"
            format::pp_print_string(out, "{");
            format::pp_print_break(out, 1, 0);
            pp_list(",", format_field, out, l);
            format::pp_print_break(out, 1, -2);
            format::pp_print_string(out, "}");
            if !inside_box {
                format::pp_close_box(out);
            }
        }
    }
}

/// `format_field std out (name, x)`: "@[<hv2>%s: %a@]"
fn format_field(out: &mut Formatter, (name, x): &(String, T)) {
    format::pp_open_hvbox(out, 2);
    format::pp_print_string(out, &json_string_of_string(name));
    format::pp_print_string(out, ": ");
    format_(true, out, x);
    format::pp_close_box(out);
}

/// `Pretty.pp out x` (`std` false): "@[<hv2>%a@]"
pub fn pp(out: &mut Formatter, x: &T) {
    format::pp_open_hvbox(out, 2);
    format_(true, out, x);
    format::pp_close_box(out);
}

/// `to_string x` (`?std` is not given: `false`), i.e.
/// `Format.asprintf "%a" pp x`. No newline at the end.
pub fn to_string(x: &T) -> String {
    format::asprintf(|out| pp(out, x))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(x: &str) -> T {
        T::String(x.to_string())
    }

    #[test]
    fn pretty_short_values_stay_on_one_line() {
        assert_eq!(to_string(&T::Null), "null");
        assert_eq!(to_string(&T::List(vec![])), "[]");
        assert_eq!(to_string(&T::Assoc(vec![])), "{}");
        assert_eq!(
            to_string(&T::Assoc(vec![("a".to_string(), T::Int(1))])),
            r#"{ "a": 1 }"#
        );
        assert_eq!(
            to_string(&T::List(vec![T::Int(1), T::Float(2.), s("x")])),
            r#"[ 1, 2.0, "x" ]"#
        );
    }

    #[test]
    fn pretty_progress_json() {
        // What `Server_progress.write_file` writes: too long for one line of
        // 78 columns, so the object is broken vertically.
        let json = T::Assoc(vec![
            ("pid".to_string(), T::Int(12345)),
            ("disposition".to_string(), T::List(vec![s("DWorking")])),
            ("message".to_string(), s("typechecking")),
            ("timestamp".to_string(), T::Float(1731234567.123456)),
        ]);
        assert_eq!(
            to_string(&json),
            "{\n  \"pid\": 12345,\n  \"disposition\": [ \"DWorking\" ],\n  \"message\": \"typechecking\",\n  \"timestamp\": 1731234567.123456\n}"
        );
    }

    #[test]
    fn pretty_nested() {
        // A list of atoms is wrapped like a paragraph inside the field's box.
        let words: Vec<T> = (0..30).map(|i| T::Int(i * 1000)).collect();
        let json = T::Assoc(vec![("numbers".to_string(), T::List(words))]);
        assert_eq!(
            to_string(&json),
            "{\n  \"numbers\": [\n    0, 1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000, 10000, 11000,\n    12000, 13000, 14000, 15000, 16000, 17000, 18000, 19000, 20000, 21000,\n    22000, 23000, 24000, 25000, 26000, 27000, 28000, 29000\n  ]\n}"
        );
        // A list of objects that fits is horizontal.
        let json = T::List(vec![
            T::Assoc(vec![("a".to_string(), T::Int(1))]),
            T::Assoc(vec![("b".to_string(), T::Int(2))]),
        ]);
        assert_eq!(to_string(&json), r#"[ { "a": 1 }, { "b": 2 } ]"#);
    }

    #[test]
    fn round_trip() {
        let json = T::Assoc(vec![
            ("pid".to_string(), T::Int(1)),
            ("disposition".to_string(), T::List(vec![s("DReady")])),
            ("message".to_string(), s("a \"quoted\" message\twith tab")),
            ("timestamp".to_string(), T::Float(0.1 + 0.2)),
        ]);
        assert_eq!(yojson::from_string(&to_string(&json)), Ok(json.clone()));
        assert_eq!(yojson::from_string(&yojson::to_string(&json)), Ok(json));
    }
}
