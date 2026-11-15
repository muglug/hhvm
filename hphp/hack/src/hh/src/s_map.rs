// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/collections/s_map.ml`: `Wrapped_map.Make (String_key)`.
//! See `hh/PORTING.md`.
//!
//! The map is an `im::OrdMap` (`s_map::T<A>`): the functions of
//! `Stdlib.Map` are its methods, and the ones `Wrapped_map` adds are here.
//! OCaml's `Map.Make` is an AVL tree; `im::OrdMap` is persistent too (a clone
//! costs nothing and shares the nodes) and iterates in the same key order,
//! which is what hh/PORTING.md asks of a map the code copies freely. (The maps
//! of the typing environment use `crate::pmap::Map` instead.) The same holds
//! for `Relative_path.Map`, `Pos.Map` and the other `im::OrdMap` maps.
//!
//! The `im::OrdMap` methods and their OCaml `Map.S` names:
//!
//! ```text
//! im::OrdMap method        OCaml
//! new, default             empty
//! is_empty, len            is_empty, cardinal
//! get                      find_opt
//! contains_key             mem
//! insert                   add (on the map in place; gives the old value)
//! update                   add (a new map)
//! remove                   remove (on the map in place; gives the value)
//! without                  remove (a new map)
//! unit                     singleton
//! iter, keys, values       bindings (increasing order of the keys)
//! get_min, get_max         min_binding_opt, max_binding_opt
//! union                    union (fun _ v1 _ -> Some v1)
//! union_with               union (a combine that always gives `Some`)
//! ```
//!
//! Not here: `hash_fold_t` and `yojson_of_t`.

pub use crate::wrapped_map::*;

pub type T<A> = im::OrdMap<String, A>;

pub type Key = String;

pub fn pp<A: Clone>(
    pp_data: impl Fn(&mut crate::format::Formatter, &A),
    fmt: &mut crate::format::Formatter,
    x: &T<A>,
) {
    make_pp(
        // `Format.fprintf fmt "%S" s`
        |fmt, s: &String| {
            crate::format::pp_print_string(
                fmt,
                &crate::rt::ocaml_printf::sprintf_s_bytes(s.as_bytes()),
            )
        },
        pp_data,
        fmt,
        x,
    )
}

pub fn show<A: Clone>(pp_data: impl Fn(&mut crate::format::Formatter, &A), x: &T<A>) -> String {
    crate::format::asprintf(|fmt| pp(pp_data, fmt, x))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn printers() {
        let pp_int = |fmt: &mut crate::format::Formatter, n: &isize| {
            crate::format::pp_print_string(fmt, &n.to_string())
        };
        let map: T<isize> = [("b", 2isize), ("a\\", 1)]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        assert_eq!(show(pp_int, &map), "{ \"a\\\\\" -> 1; \"b\" -> 2 }");
        assert_eq!(show(pp_int, &T::new()), "{}");
    }
}
