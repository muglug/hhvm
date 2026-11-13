// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `S_set` (`utils/collections/s_set.ml`): `Set.Make (String_key)`. See
//! `hh/PORTING.md`.
//!
//! The set is an `im::OrdSet` (`s_set::T`): the functions of `Stdlib.Set`
//! are its methods.
//!
//! `pp`, `show` and `to_string` print on `crate::format`. Not here:
//! `pp_large`, `show_large` and `yojson_of_t`.

pub type T = im::OrdSet<String>;

pub type Elt = String;

/// `Printf`'s `%S`: `"` ^ `String.escaped s` ^ `"` (on bytes: those outside
/// the printable ASCII range become `\ddd`).
#[allow(non_snake_case)]
fn sprintf_S(s: &str) -> String {
    let mut res = String::with_capacity(s.len() + 2);
    res.push('"');
    for &c in s.as_bytes() {
        match c {
            b'"' => res.push_str("\\\""),
            b'\\' => res.push_str("\\\\"),
            b'\n' => res.push_str("\\n"),
            b'\t' => res.push_str("\\t"),
            b'\r' => res.push_str("\\r"),
            b'\x08' => res.push_str("\\b"),
            b' '..=b'~' => res.push(c as char),
            _ => res.push_str(&format!("\\{:03}", c)),
        }
    }
    res.push('"');
    res
}

/// `"@[<2>{"`, `" "` if the set is not empty, the first `max_elts` elements
/// (all of them for `None`) printed by `"%S"` and separated by `";@ "`, `" "`
/// if the set is not empty, `"@,}@]"`.
pub fn pp_limit(max_elts: Option<Option<isize>>, fmt: &mut crate::format::Formatter, sset: &T) {
    use crate::format;
    let max_elts = max_elts.unwrap_or(None);
    format::pp_open_box(fmt, 2);
    format::pp_print_string(fmt, "{");
    let elements: Vec<&String> = sset.iter().collect();
    if !elements.is_empty() {
        format::pp_print_string(fmt, " ");
    }
    for (i, s) in elements.iter().enumerate() {
        match max_elts {
            Some(max_elts) if i as isize >= max_elts => (),
            _ => {
                if i > 0 {
                    format::pp_print_string(fmt, ";");
                    format::pp_print_space(fmt);
                }
                format::pp_print_string(fmt, &sprintf_S(s));
            }
        }
    }
    if !elements.is_empty() {
        format::pp_print_string(fmt, " ");
    }
    format::pp_print_cut(fmt);
    format::pp_print_string(fmt, "}");
    format::pp_close_box(fmt);
}

pub fn pp(fmt: &mut crate::format::Formatter, sset: &T) {
    pp_limit(Some(None), fmt, sset)
}

pub fn show(sset: &T) -> String {
    crate::format::asprintf(|fmt| pp(fmt, sset))
}

pub fn to_string(sset: &T) -> String {
    show(sset)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn printers() {
        let set: T = ["b", "a\\"].iter().map(|s| s.to_string()).collect();
        assert_eq!(show(&set), "{ \"a\\\\\"; \"b\" }");
        assert_eq!(show(&T::new()), "{}");
        let one_elt = crate::format::asprintf(|fmt| pp_limit(Some(Some(1)), fmt, &set));
        assert_eq!(one_elt, "{ \"a\\\\\" }");
    }
}
