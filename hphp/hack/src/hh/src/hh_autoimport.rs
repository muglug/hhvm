// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/hh_autoimport.ml`. See `hh/PORTING.md`.
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

/// Strip any `HH\` prefix from the provided string if the string
/// is the name of a autoimport type.
pub fn strip_hh_namespace_if_autoimport(id: &str) -> &str {
    match id.strip_prefix("HH\\") {
        Some(stripped_id) if is_hh_autoimport(stripped_id) => stripped_id,
        _ => id,
    }
}

/// `funcs`: the crate's list without the names that `hh_autoimport.ml`
/// does not have (`objprof_get_data_extended`,
/// `objprof_get_data_extended_with_graph_stats`,
/// `objprof_get_data_with_graph_stats`, `objprof_get_paths_with_graph_stats`,
/// `package_exists`): the lowerer (the Rust parser, in the OCaml too) uses the
/// crate's list, `Namespace_env.default_fun_uses` this one.
pub fn funcs() -> impl Iterator<Item = &'static str> {
    const NOT_IN_OCAML: [&str; 5] = [
        "objprof_get_data_extended",
        "objprof_get_data_extended_with_graph_stats",
        "objprof_get_data_with_graph_stats",
        "objprof_get_paths_with_graph_stats",
        "package_exists",
    ];
    ::hh_autoimport::FUNCS_MAP
        .keys()
        .map(String::as_str)
        .filter(|name| !NOT_IN_OCAML.contains(name))
}

/// `types` (see [`is_hh_autoimport`]).
pub fn types() -> impl Iterator<Item = &'static str> {
    ::hh_autoimport::TYPES
        .iter()
        .copied()
        .filter(|name| is_hh_autoimport(name))
}

/// `consts`
pub fn consts() -> impl Iterator<Item = &'static str> {
    ::hh_autoimport::CONSTS_MAP.keys().map(String::as_str)
}

/// `namespaces`
pub fn namespaces() -> impl Iterator<Item = &'static str> {
    ::hh_autoimport::NAMESPACES.iter().copied()
}

/// `Namespace_env.empty_with_default` (`hh_autoimport_map_of_list` of each
/// list: `NAME` -> `HH\NAME`; the options are `Parser_options.default`'s:
/// no auto namespace map, the typechecking mode, XHP elements mangled).
/// Not the default of the lowerer (`namespace_env::Env::empty`), which uses
/// the crate's lists.
pub fn namespace_env_empty_with_default() -> oxidized::namespace_env::Env {
    let map = |names: &mut dyn Iterator<Item = &'static str>| -> oxidized::s_map::SMap<String> {
        names.map(|n| (n.to_string(), format!("HH\\{}", n))).collect()
    };
    oxidized::namespace_env::Env {
        ns_uses: map(&mut namespaces()),
        class_uses: map(&mut types()),
        fun_uses: map(&mut funcs()),
        const_uses: map(&mut consts()),
        name: None,
        mode: oxidized::namespace_env::Mode::ForTypecheck,
        disable_xhp_element_mangling: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_funcs_as_ocaml() {
        let mut ocaml = ocaml_list("funcs");
        ocaml.sort();
        assert_eq!(funcs().collect::<Vec<_>>(), ocaml);
        assert_eq!(namespaces().collect::<Vec<_>>(), vec!["Rx"]);
        let env = namespace_env_empty_with_default();
        assert_eq!(env.class_uses.get("vec").map(String::as_str), Some("HH\\vec"));
        assert_eq!(env.fun_uses.len(), ocaml_list("funcs").len());
    }

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
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\vec"), "vec");
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\Traversable"), "Traversable");
        // Not an autoimport type.
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\Lib\\Vec"), "HH\\Lib\\Vec");
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\Foo"), "HH\\Foo");
        assert_eq!(
            strip_hh_namespace_if_autoimport("HH\\class_or_classname"),
            "HH\\class_or_classname"
        );
        // Autoimport functions are not types.
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\invariant"), "HH\\invariant");
        // Only the `HH\` prefix, without a leading backslash.
        assert_eq!(strip_hh_namespace_if_autoimport("\\HH\\vec"), "\\HH\\vec");
        assert_eq!(strip_hh_namespace_if_autoimport("vec"), "vec");
        assert_eq!(strip_hh_namespace_if_autoimport("HH\\"), "HH\\");
    }
}
