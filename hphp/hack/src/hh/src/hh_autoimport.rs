// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Hh_autoimport` (`parser/hh_autoimport.ml`). See `hh/PORTING.md`.
//!
//! The lists are those of the `hh_autoimport_rust` crate
//! (`parser/hh_autoimport.rs`), which the parser uses. That crate's list of
//! types has one name that `hh_autoimport.ml` does not have,
//! `class_or_classname`, and the expected outputs depend on the difference
//! (`HH\class_or_classname<C>` keeps its namespace when it is printed), so
//! that name is not an autoimport type here.

/// Whether the given string is the name of an autoimport type.
pub fn is_hh_autoimport(x: &str) -> bool {
    ::hh_autoimport::is_hh_autoimport(x) && x != "class_or_classname"
}

#[allow(non_snake_case)]
pub fn strip_HH_namespace_if_autoimport(id: &str) -> &str {
    match id.strip_prefix("HH\\") {
        Some(stripped_id) if is_hh_autoimport(stripped_id) => stripped_id,
        _ => id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The strings of the list `let <name> = [ ... ]` of `hh_autoimport.ml`.
    fn ocaml_list(name: &str) -> Vec<&'static str> {
        let ml = include_str!("../../parser/hh_autoimport.ml");
        let start = ml
            .find(&format!("let {} =\n  [", name))
            .expect("the list is in hh_autoimport.ml");
        let list = &ml[start..];
        let list = &list[..list.find(']').unwrap()];
        list.split('"').skip(1).step_by(2).collect()
    }

    #[test]
    fn same_types_as_ocaml() {
        let ocaml = ocaml_list("types");
        assert!(ocaml.len() > 50);
        for name in &ocaml {
            assert!(is_hh_autoimport(name), "{}", name);
        }
        // Nothing else: the names of the crate's list that are autoimport
        // types here are those of the OCaml list.
        let rust: Vec<&str> = ::hh_autoimport::TYPES
            .iter()
            .copied()
            .filter(|name| is_hh_autoimport(name))
            .collect();
        assert_eq!(rust, ocaml);
        assert!(!is_hh_autoimport("class_or_classname"));
    }

    #[test]
    fn strip() {
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\vec"), "vec");
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\Traversable"), "Traversable");
        // Not an autoimport type.
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\Lib\\Vec"), "HH\\Lib\\Vec");
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\Foo"), "HH\\Foo");
        assert_eq!(
            strip_HH_namespace_if_autoimport("HH\\class_or_classname"),
            "HH\\class_or_classname"
        );
        // Autoimport functions are not types.
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\invariant"), "HH\\invariant");
        // Only the `HH\` prefix, without a leading backslash.
        assert_eq!(strip_HH_namespace_if_autoimport("\\HH\\vec"), "\\HH\\vec");
        assert_eq!(strip_HH_namespace_if_autoimport("vec"), "vec");
        assert_eq!(strip_HH_namespace_if_autoimport("HH\\"), "HH\\");
    }
}
