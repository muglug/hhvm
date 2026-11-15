// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/collections/s_set.ml`: `Set.Make (String_key)`. See
//! `hh/PORTING.md`.
//!
//! The set is an `im::OrdSet` (`s_set::T`): the functions of `Stdlib.Set`
//! are its methods. OCaml's `Set.Make` is an AVL tree; `im::OrdSet` is
//! persistent too (a clone costs nothing) and iterates in the same order, as
//! hh/PORTING.md asks of a set the code copies freely. The same holds for
//! `Relative_path.Set`, `Path.Set` and `Pos.Set`.
//!
//! The `im::OrdSet` methods and their OCaml `Set.S` names:
//!
//! ```text
//! im::OrdSet method        OCaml
//! new, default             empty
//! is_empty, len            is_empty, cardinal
//! contains                 mem
//! insert                   add (on the set in place)
//! update                   add (a new set)
//! remove                   remove (on the set in place)
//! without                  remove (a new set)
//! unit                     singleton
//! iter                     elements, iter (increasing order)
//! get_min, get_max         min_elt_opt, max_elt_opt
//! union                    union
//! intersection             inter
//! relative_complement      diff (`difference` is the symmetric one)
//! is_subset                subset
//! ```
//!
//! `pp`, `show` and `to_string` print on `crate::format`. Not here:
//! `pp_large`, `show_large` and `yojson_of_t`.

use crate::rt::ocaml_printf::sprintf_s;

pub type T = im::OrdSet<String>;

pub type Elt = String;

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
                format::pp_print_string(fmt, &sprintf_s(s));
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
