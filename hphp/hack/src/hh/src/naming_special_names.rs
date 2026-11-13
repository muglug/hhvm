// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Naming_special_names` (`naming/naming_special_names.ml`). See
//! `hh/PORTING.md`.
//!
//! The names are those of the `naming_special_names_rust` crate
//! (`naming/naming_special_names.rs`), re-exported here: use them from that
//! crate, as `PORTING.md` says. This module only adds what the typechecker
//! uses and the crate does not have: a few functions of
//! `naming_special_names.ml`, and the names they are made of when the crate
//! lacks those too. They are in a module named after the OCaml one, which
//! also has what the crate has for it.

#![allow(non_upper_case_globals)]

pub use naming_special_names_rust::*;

/// `Naming_special_names.Classes`
pub mod classes {
    pub use naming_special_names_rust::classes::*;

    pub const cHHTypedFormatString: &str = "\\HH\\TypedFormatString";

    pub fn is_typed_format_string(x: &str) -> bool {
        x == cHHTypedFormatString
    }
}

/// `Naming_special_names.SpecialFunctions`
pub mod special_functions {
    use naming_special_names_rust::pseudo_functions;

    pub const classname_to_class: &str = "\\HH\\classname_to_class";

    pub const classname_to_class_strict_isolation_backdoor: &str =
        "\\HH\\classname_to_class_strict_isolation_backdoor";

    pub const exit: &str = pseudo_functions::EXIT;

    pub const get_class_from_type: &str = "\\HH\\ReifiedGenerics\\get_class_from_type";

    pub const global_get: &str = "\\HH\\global_get";

    pub const global_set: &str = "\\HH\\global_set";

    pub const global_unset: &str = "\\HH\\global_set";

    pub const tag_provenance_here: &str = "\\HH\\tag_provenance_here";

    pub const unsafe_cast: &str = pseudo_functions::UNSAFE_CAST;

    pub const unsafe_nonnull_cast: &str = pseudo_functions::UNSAFE_NONNULL_CAST;

    pub const all_special_functions: &[&str] = &[
        classname_to_class,
        classname_to_class_strict_isolation_backdoor,
        exit,
        get_class_from_type,
        global_get,
        global_set,
        global_unset,
        tag_provenance_here,
        unsafe_cast,
        unsafe_nonnull_cast,
    ];

    pub fn is_special_function(x: &str) -> bool {
        all_special_functions.contains(&x)
    }
}

/// `Naming_special_names.StdlibFunctions`
pub mod stdlib_functions {
    use naming_special_names_rust::pre_namespaced_functions;
    use naming_special_names_rust::pseudo_functions;
    pub use naming_special_names_rust::std_lib_functions::*;

    pub const type_structure: &str = "\\HH\\type_structure";

    pub const type_structure_classname: &str = "\\HH\\type_structure_classname";

    pub const type_structure_class: &str = "\\HH\\type_structure_class";

    /// All Id funcions that Typing.dispatch_call handles specially
    pub const special_dispatch: &[&str] = &[
        pre_namespaced_functions::ECHO,
        pseudo_functions::ISSET,
        pseudo_functions::UNSET,
        type_structure,
        type_structure_classname,
        type_structure_class,
        pseudo_functions::UNSAFE_CAST,
        pseudo_functions::UNSAFE_NONNULL_CAST,
    ];

    pub fn needs_special_dispatch(x: &str) -> bool {
        special_dispatch.contains(&x)
    }
}

/// `Naming_special_names.Coeffects`
pub mod coeffects {
    pub use naming_special_names_rust::coeffects::*;

    pub const local_capability: &str = "$#local_capability";

    pub const generated_generic_prefix: &str = "T/";

    pub fn is_generated_generic(x: &str) -> bool {
        x.starts_with(generated_generic_prefix)
    }

    /// "T/[ctx $foo]" to "ctx $foo".
    pub fn unwrap_generated_generic(name: &str) -> &str {
        let name = name.strip_prefix("T/[").unwrap_or(name);
        name.strip_suffix(']').unwrap_or(name)
    }
}

/// `Naming_special_names.SimpliHack` (the crate has none of it)
pub mod simpli_hack {
    pub const prefix: &str = "\\HH\\SimpliHack\\";

    pub const file: &str = "\\HH\\SimpliHack\\file";

    pub const constructor: &str = "\\HH\\SimpliHack\\constructor";

    pub const methods: &str = "\\HH\\SimpliHack\\methods";

    pub const static_methods: &str = "\\HH\\SimpliHack\\static_methods";

    pub const fields: &str = "\\HH\\SimpliHack\\fields";

    pub const static_fields: &str = "\\HH\\SimpliHack\\static_fields";
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value of `let <name> = "<value>"` in the module `<module>` of
    /// `naming_special_names.ml`, as it is written there (with its escapes).
    fn ocaml_string(module: &str, name: &str) -> &'static str {
        let ml = include_str!("../../naming/naming_special_names.ml");
        let module_start = ml
            .find(&format!("\nmodule {} = struct", module))
            .unwrap_or_else(|| panic!("module {}", module));
        let ml = &ml[module_start..];
        let def = format!("\n  let {} =", name);
        let start = ml.find(&def).unwrap_or_else(|| panic!("{}.{}", module, name)) + def.len();
        let rest = &ml[start..];
        let open = rest.find('"').unwrap();
        let rest = &rest[open + 1..];
        &rest[..rest.find('"').unwrap()]
    }

    /// A Rust string as OCaml writes it: backslashes doubled.
    fn escaped(s: &str) -> String {
        s.replace('\\', "\\\\")
    }

    #[test]
    fn same_names_as_ocaml() {
        assert_eq!(
            escaped(classes::cHHTypedFormatString),
            ocaml_string("Classes", "cHHTypedFormatString")
        );
        for (name, value) in [
            ("classname_to_class", special_functions::classname_to_class),
            (
                "classname_to_class_strict_isolation_backdoor",
                special_functions::classname_to_class_strict_isolation_backdoor,
            ),
            ("get_class_from_type", special_functions::get_class_from_type),
            ("global_get", special_functions::global_get),
            ("global_set", special_functions::global_set),
            ("global_unset", special_functions::global_unset),
            ("tag_provenance_here", special_functions::tag_provenance_here),
        ] {
            assert_eq!(escaped(value), ocaml_string("SpecialFunctions", name), "{}", name);
        }
        for (name, value) in [
            ("exit", special_functions::exit),
            ("unsafe_cast", special_functions::unsafe_cast),
            ("unsafe_nonnull_cast", special_functions::unsafe_nonnull_cast),
            ("isset", pseudo_functions::ISSET),
            ("unset", pseudo_functions::UNSET),
        ] {
            assert_eq!(escaped(value), ocaml_string("PseudoFunctions", name), "{}", name);
        }
        for (name, value) in [
            ("type_structure", stdlib_functions::type_structure),
            ("type_structure_classname", stdlib_functions::type_structure_classname),
            ("type_structure_class", stdlib_functions::type_structure_class),
        ] {
            assert_eq!(escaped(value), ocaml_string("StdlibFunctions", name), "{}", name);
        }
        assert_eq!(
            pre_namespaced_functions::ECHO,
            ocaml_string("PreNamespacedFunctions", "echo")
        );
        assert_eq!(
            coeffects::local_capability,
            ocaml_string("Coeffects", "local_capability")
        );
        assert_eq!(
            coeffects::generated_generic_prefix,
            ocaml_string("Coeffects", "generated_generic_prefix")
        );
    }

    #[test]
    fn predicates() {
        assert!(classes::is_typed_format_string("\\HH\\TypedFormatString"));
        assert!(!classes::is_typed_format_string("\\HH\\FormatString"));
        assert!(!classes::is_typed_format_string("HH\\TypedFormatString"));

        assert!(special_functions::is_special_function("\\exit"));
        assert!(special_functions::is_special_function("\\HH\\global_set"));
        assert!(special_functions::is_special_function(
            "\\HH\\FIXME\\UNSAFE_CAST"
        ));
        // `global_unset` is the name of `global_set` in OCaml.
        assert!(!special_functions::is_special_function("\\HH\\global_unset"));
        assert!(!special_functions::is_special_function("exit"));

        assert!(stdlib_functions::needs_special_dispatch("echo"));
        assert!(stdlib_functions::needs_special_dispatch("\\isset"));
        assert!(stdlib_functions::needs_special_dispatch("\\HH\\type_structure_class"));
        assert!(!stdlib_functions::needs_special_dispatch("\\echo"));
        assert!(!stdlib_functions::needs_special_dispatch("\\get_class"));

        assert!(coeffects::is_generated_generic("T/[ctx $foo]"));
        assert!(coeffects::is_generated_generic("T/"));
        assert!(!coeffects::is_generated_generic("T"));
        assert!(!coeffects::is_generated_generic("Tfoo"));
        assert_eq!(coeffects::unwrap_generated_generic("T/[ctx $foo]"), "ctx $foo");
        // Each end on its own.
        assert_eq!(coeffects::unwrap_generated_generic("T/[ctx $foo"), "ctx $foo");
        assert_eq!(coeffects::unwrap_generated_generic("ctx $foo]"), "ctx $foo");
        assert_eq!(coeffects::unwrap_generated_generic("T/[]"), "");
        assert_eq!(coeffects::unwrap_generated_generic("T/["), "");
        assert_eq!(coeffects::unwrap_generated_generic("Tfoo"), "Tfoo");
    }
}
