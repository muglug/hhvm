// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_special_names.ml`. See `hh/PORTING.md`.
//!
//! The names are those of the `naming_special_names_rust` crate
//! (`naming/naming_special_names.rs`), re-exported here: use them from that
//! crate, as `PORTING.md` says. This module only adds what the typechecker
//! uses and the crate does not have: a few functions of
//! `naming_special_names.ml`, and the names they are made of when the crate
//! lacks those too. They are in a module named after the OCaml one, which
//! also has what the crate has for it.

pub use naming_special_names_rust::*;

/// `Naming_special_names.Classes`
pub mod classes {
    pub use naming_special_names_rust::classes::*;

    pub const C_HH_TYPED_FORMAT_STRING: &str = "\\HH\\TypedFormatString";

    pub fn is_typed_format_string(x: &str) -> bool {
        x == C_HH_TYPED_FORMAT_STRING
    }

    pub const C_CLOSURE: &str = "\\Closure";

    pub const C_FUNCTION_REF: &str = "\\HH\\FunctionRef";

    /// The crate has it as `typehints::HH_STRING` only.
    pub const C_STRING: &str = "\\HH\\string";
}

/// `Naming_special_names.AttributeKinds`
pub mod attribute_kinds {
    pub use naming_special_names_rust::attribute_kinds::*;

    pub const MODULE: &str = "\\HH\\ModuleAttribute";

    /// `plain_english_map` (an `S_map`: looked up by key).
    pub fn plain_english_map_find_opt(k: &str) -> Option<&'static str> {
        [
            (CLS, "a class"),
            (CLS_CST, "a constant of a class"),
            (ENUM, "an enum"),
            (TYPE_ALIAS, "a typealias"),
            (FN, "a function"),
            (MTHD, "a method"),
            (INST_PROPERTY, "an instance property"),
            (STATIC_PROPERTY, "a static property"),
            (PARAMETER, "a parameter"),
            (TYPE_PARAM, "a type parameter"),
            (FILE, "a file"),
            (TYPE_CONST, "a type constant"),
            (LAMBDA, "a lambda expression"),
            (ENUM_CLS, "an enum class"),
            (MODULE, "a module"),
        ]
        .into_iter()
        .find(|(key, _)| *key == k)
        .map(|(_, v)| v)
    }
}

/// `Naming_special_names.UserAttributes`: the `contexts` of the
/// `attr_info`s of `as_map` and `systemlib_map`, in the order of the
/// keys (`S_map.bindings`), generated from `naming/naming_special_names.ml`
/// (only the `contexts` of each `attr_info`: the crate has none of them).
pub mod user_attributes {
    pub use naming_special_names_rust::user_attributes::*;

    use super::attribute_kinds as ak;

    /// `as_map`
    pub static AS_MAP: &[(&str, &[&str])] = &[
        ("__AcceptDisposable", &[ak::PARAMETER]),
        ("__AllowUncheckedEnumValues", &[ak::ENUM]),
        ("__AsioLowPri", &[ak::FN, ak::MTHD]),
        ("__ConsistentConstruct", &[ak::CLS]),
        (
            "__Const",
            &[ak::CLS, ak::INST_PROPERTY, ak::PARAMETER, ak::STATIC_PROPERTY],
        ),
        ("__Deprecated", &[ak::FN, ak::MTHD]),
        ("__DisableTypecheckerInternal", &[ak::FN, ak::MTHD]),
        ("__DisjointShapeSplat", &[ak::TYPE_ALIAS]),
        ("__Docs", &[ak::CLS, ak::ENUM, ak::ENUM_CLS, ak::TYPE_ALIAS]),
        ("__DynamicallyCallable", &[ak::FN, ak::MTHD]),
        ("__DynamicallyConstructible", &[ak::CLS]),
        ("__DynamicallyReferenced", &[ak::CLS]),
        ("__EnableMethodTraitDiamond", &[ak::CLS]),
        ("__EnableUnstableFeatures", &[ak::FILE]),
        ("__Enforceable", &[ak::TYPE_CONST, ak::TYPE_PARAM]),
        ("__EntryPoint", &[ak::FN]),
        ("__EnumClass", &[ak::CLS, ak::ENUM_CLS]),
        ("__Explicit", &[ak::TYPE_PARAM]),
        ("__GatedByFeatureFlag", &[ak::CLS, ak::TYPE_ALIAS, ak::FN]),
        ("__HasReifiedParent", &[]),
        ("__IgnoreReadonlyError", &[ak::PARAMETER]),
        ("__ImplementedBy", &[ak::MTHD]),
        ("__LSB", &[ak::STATIC_PROPERTY]),
        ("__LateInit", &[ak::INST_PROPERTY, ak::STATIC_PROPERTY]),
        ("__Memoize", &[ak::FN, ak::MTHD]),
        ("__MemoizeLSB", &[ak::MTHD]),
        ("__MockClass", &[ak::CLS]),
        ("__ModuleLevelTrait", &[ak::CLS]),
        ("__NEVER_INLINE", &[ak::FN, ak::MTHD]),
        ("__NativeData", &[ak::CLS]),
        ("__NeedsConcrete", &[ak::MTHD]),
        ("__Newable", &[ak::TYPE_PARAM]),
        ("__NoAutoBound", &[ak::TYPE_PARAM]),
        (
            "__NoAutoDynamic",
            &[ak::FN, ak::CLS, ak::MTHD, ak::TYPE_ALIAS],
        ),
        (
            "__NoAutoLikes",
            &[
                ak::FN,
                ak::MTHD,
                ak::STATIC_PROPERTY,
                ak::INST_PROPERTY,
                ak::PARAMETER,
                ak::LAMBDA,
            ],
        ),
        ("__NoDisjointUnion", &[ak::TYPE_PARAM]),
        ("__NoFlatten", &[]),
        (
            "__NoSupportDynamicType",
            &[ak::FN, ak::CLS, ak::MTHD, ak::LAMBDA, ak::ENUM_CLS],
        ),
        ("__NonDisjoint", &[ak::TYPE_PARAM]),
        ("__Overlapping", &[ak::FN, ak::MTHD]),
        ("__Override", &[ak::MTHD]),
        ("__PHPStdLib", &[ak::CLS, ak::FN, ak::MTHD]),
        ("__PackageOverride", &[ak::FILE]),
        ("__ProvenanceSkipFrame", &[ak::FN, ak::MTHD, ak::LAMBDA]),
        ("__Reifiable", &[ak::TYPE_CONST]),
        ("__Reified", &[]),
        ("__RequireDynamic", &[ak::TYPE_PARAM]),
        ("__RequirePackage", &[ak::FN, ak::MTHD]),
        ("__ReturnDisposable", &[ak::FN, ak::MTHD, ak::LAMBDA]),
        ("__SafeForGlobalAccessCheck", &[ak::STATIC_PROPERTY]),
        ("__Sealed", &[ak::CLS, ak::ENUM_CLS, ak::ENUM, ak::MTHD]),
        ("__ShapeKey", &[ak::CLS_CST]),
        (
            "__SimpliHack",
            &[
                ak::CLS,
                ak::CLS_CST,
                ak::ENUM,
                ak::ENUM_CLS,
                ak::FILE,
                ak::FN,
                ak::INST_PROPERTY,
                ak::LAMBDA,
                ak::MTHD,
                ak::MODULE,
                ak::PARAMETER,
                ak::STATIC_PROPERTY,
                ak::TYPE_ALIAS,
                ak::TYPE_CONST,
                ak::TYPE_PARAM,
            ],
        ),
        (
            "__Soft",
            &[
                ak::INST_PROPERTY,
                ak::PARAMETER,
                ak::STATIC_PROPERTY,
                ak::TYPE_PARAM,
            ],
        ),
        (
            "__SoftInternal",
            &[
                ak::FN,
                ak::CLS,
                ak::MTHD,
                ak::INST_PROPERTY,
                ak::STATIC_PROPERTY,
                ak::PARAMETER,
                ak::ENUM,
                ak::ENUM_CLS,
            ],
        ),
        ("__SoftRequirePackage", &[ak::FN, ak::MTHD]),
        ("__StrictSwitch", &[ak::FN, ak::MTHD]),
        (
            "__SupportDynamicType",
            &[ak::FN, ak::CLS, ak::MTHD, ak::LAMBDA, ak::ENUM_CLS],
        ),
        (
            "__TestsBypassVisibility",
            &[ak::CLS, ak::MTHD, ak::INST_PROPERTY, ak::STATIC_PROPERTY],
        ),
        ("__UNSAFE_AllowMultipleInstantiations", &[ak::CLS]),
        ("__Warn", &[ak::TYPE_PARAM]),
    ];

    /// These are names which are allowed in the systemlib but not in normal programs
    /// (`systemlib_map`)
    pub static SYSTEMLIB_MAP: &[(&str, &[&str])] = &[
        ("__ALWAYS_INLINE", &[ak::FN, ak::MTHD]),
        ("__EagerVMSync", &[ak::FN, ak::MTHD]),
        ("__IgnoreCoeffectLocalErrors", &[ak::FN, ak::MTHD]),
        ("__IgnoreReadonlyLocalErrors", &[ak::FN, ak::MTHD]),
        ("__IsFoldable", &[ak::FN, ak::MTHD]),
        ("__Native", &[ak::FN, ak::MTHD]),
        ("__OutOnly", &[ak::PARAMETER]),
    ];

    /// `S_map.find_opt name map`, giving the `contexts` of the `attr_info`.
    pub fn find_opt(
        name: &str,
        map: &'static [(&'static str, &'static [&'static str])],
    ) -> Option<&'static [&'static str]> {
        map.iter()
            .find(|(k, _)| *k == name)
            .map(|(_, contexts)| *contexts)
    }
}

/// `Naming_special_names.PseudoFunctions`
pub mod pseudo_functions {
    pub use naming_special_names_rust::pseudo_functions::*;

    pub const HH_TIME: &str = "\\hh_time";
}

/// `Naming_special_names.SpecialFunctions`
pub mod special_functions {
    use naming_special_names_rust::pseudo_functions;

    pub const CLASSNAME_TO_CLASS: &str = "\\HH\\classname_to_class";

    pub const CLASSNAME_TO_CLASS_STRICT_ISOLATION_BACKDOOR: &str =
        "\\HH\\classname_to_class_strict_isolation_backdoor";

    pub const EXIT: &str = pseudo_functions::EXIT;

    pub const GET_CLASS_FROM_TYPE: &str = "\\HH\\ReifiedGenerics\\get_class_from_type";

    pub const GLOBAL_GET: &str = "\\HH\\global_get";

    pub const GLOBAL_SET: &str = "\\HH\\global_set";

    pub const GLOBAL_UNSET: &str = "\\HH\\global_set";

    pub const TAG_PROVENANCE_HERE: &str = "\\HH\\tag_provenance_here";

    pub const UNSAFE_CAST: &str = pseudo_functions::UNSAFE_CAST;

    pub const UNSAFE_NONNULL_CAST: &str = pseudo_functions::UNSAFE_NONNULL_CAST;

    pub const ALL_SPECIAL_FUNCTIONS: &[&str] = &[
        CLASSNAME_TO_CLASS,
        CLASSNAME_TO_CLASS_STRICT_ISOLATION_BACKDOOR,
        EXIT,
        GET_CLASS_FROM_TYPE,
        GLOBAL_GET,
        GLOBAL_SET,
        GLOBAL_UNSET,
        TAG_PROVENANCE_HERE,
        UNSAFE_CAST,
        UNSAFE_NONNULL_CAST,
    ];

    pub fn is_special_function(x: &str) -> bool {
        ALL_SPECIAL_FUNCTIONS.contains(&x)
    }
}

/// `Naming_special_names.StdlibFunctions`
pub mod stdlib_functions {
    use naming_special_names_rust::pre_namespaced_functions;
    use naming_special_names_rust::pseudo_functions;
    pub use naming_special_names_rust::std_lib_functions::*;

    pub const TYPE_STRUCTURE: &str = "\\HH\\type_structure";

    pub const TYPE_STRUCTURE_CLASSNAME: &str = "\\HH\\type_structure_classname";

    pub const TYPE_STRUCTURE_CLASS: &str = "\\HH\\type_structure_class";

    pub const GET_CLASS_FROM_TYPE: &str = "\\HH\\ReifiedGenerics\\get_class_from_type";

    /// All Id funcions that Typing.dispatch_call handles specially
    pub const SPECIAL_DISPATCH: &[&str] = &[
        pre_namespaced_functions::ECHO,
        pseudo_functions::ISSET,
        pseudo_functions::UNSET,
        TYPE_STRUCTURE,
        TYPE_STRUCTURE_CLASSNAME,
        TYPE_STRUCTURE_CLASS,
        pseudo_functions::UNSAFE_CAST,
        pseudo_functions::UNSAFE_NONNULL_CAST,
    ];

    pub fn needs_special_dispatch(x: &str) -> bool {
        SPECIAL_DISPATCH.contains(&x)
    }
}

/// `Naming_special_names.Shapes`
pub mod shapes {
    pub use naming_special_names_rust::shapes::*;

    pub const C_READONLY_SHAPES: &str = "\\HH\\Readonly\\Shapes";

    pub const PUT: &str = "put";
}

/// `Naming_special_names.Coeffects`
pub mod coeffects {
    pub use naming_special_names_rust::coeffects::*;

    pub const LOCAL_CAPABILITY: &str = "$#local_capability";

    /// The OCaml's value: the crate's `CONTEXTS`, which this shadows, lacks the
    /// leading backslash.
    pub const CONTEXTS: &str = "\\HH\\Contexts";

    pub const GENERATED_GENERIC_PREFIX: &str = "T/";

    pub fn is_generated_generic(x: &str) -> bool {
        x.starts_with(GENERATED_GENERIC_PREFIX)
    }

    /// "T/[ctx $foo]" to "ctx $foo".
    pub fn unwrap_generated_generic(name: &str) -> &str {
        let name = name.strip_prefix("T/[").unwrap_or(name);
        name.strip_suffix(']').unwrap_or(name)
    }
}

/// `Naming_special_names.Capabilities` (the crate has none of it)
pub mod capabilities {
    /// `Coeffects.contexts ^ "\\defaults"`
    pub const DEFAULTS: &str = "\\HH\\Contexts\\defaults";

    /// `Coeffects.contexts ^ "\\write_props"`
    pub const WRITE_PROPS: &str = "\\HH\\Contexts\\write_props";

    pub const PREFIX: &str = "\\HH\\Capabilities\\";

    pub const WRITE_PROPERTY: &str = "\\HH\\Capabilities\\WriteProperty";

    pub const ACCESS_GLOBALS: &str = "\\HH\\Capabilities\\AccessGlobals";

    pub const READ_GLOBALS: &str = "\\HH\\Capabilities\\ReadGlobals";

    pub const SYSTEM_LOCAL: &str = "\\HH\\Capabilities\\SystemLocal";

    pub const IMPLICIT_POLICY: &str = "\\HH\\Capabilities\\ImplicitPolicy";

    pub const IMPLICIT_POLICY_LOCAL: &str = "\\HH\\Capabilities\\ImplicitPolicyLocal";

    pub const IO: &str = "\\HH\\Capabilities\\IO";

    pub const RX: &str = "\\HH\\Capabilities\\Rx";

    pub const RX_LOCAL: &str = "\\HH\\Capabilities\\RxLocal";
}

/// `Naming_special_names.SimpliHack` (the crate has none of it)
pub mod simpli_hack {
    pub const PREFIX: &str = "\\HH\\SimpliHack\\";

    pub const FILE: &str = "\\HH\\SimpliHack\\file";

    pub const CONSTRUCTOR: &str = "\\HH\\SimpliHack\\constructor";

    pub const METHODS: &str = "\\HH\\SimpliHack\\methods";

    pub const STATIC_METHODS: &str = "\\HH\\SimpliHack\\static_methods";

    pub const FIELDS: &str = "\\HH\\SimpliHack\\fields";

    pub const STATIC_FIELDS: &str = "\\HH\\SimpliHack\\static_fields";
}

/// `Naming_special_names.UnstableFeatures`
pub mod unstable_features {
    pub use naming_special_names_rust::unstable_features::*;

    pub const NAMED_PARAMETERS_METH_CALLER: &str = "named_parameters_meth_caller";
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
        for (name, value) in [
            ("cHHTypedFormatString", classes::C_HH_TYPED_FORMAT_STRING),
            ("cClosure", classes::C_CLOSURE),
            ("cFunctionRef", classes::C_FUNCTION_REF),
            ("cString", classes::C_STRING),
        ] {
            assert_eq!(escaped(value), ocaml_string("Classes", name), "{}", name);
        }
        assert_eq!(escaped(attribute_kinds::MODULE), ocaml_string("AttributeKinds", "module_"));
        assert_eq!(escaped(pseudo_functions::HH_TIME), ocaml_string("PseudoFunctions", "hh_time"));
        assert_eq!(
            escaped(stdlib_functions::GET_CLASS_FROM_TYPE),
            ocaml_string("StdlibFunctions", "get_class_from_type")
        );
        assert_eq!(
            escaped(shapes::C_READONLY_SHAPES),
            ocaml_string("Shapes", "cReadonlyShapes")
        );
        assert_eq!(shapes::PUT, ocaml_string("Shapes", "put"));
        assert_eq!(
            unstable_features::NAMED_PARAMETERS_METH_CALLER,
            ocaml_string("UnstableFeatures", "named_parameters_meth_caller")
        );
        assert_eq!(escaped(coeffects::CONTEXTS), ocaml_string("Coeffects", "contexts"));
        assert_eq!(escaped(capabilities::PREFIX), ocaml_string("Capabilities", "prefix"));
        assert_eq!(capabilities::DEFAULTS, format!("{}\\defaults", coeffects::CONTEXTS));
        assert_eq!(capabilities::WRITE_PROPS, format!("{}\\write_props", coeffects::CONTEXTS));
        // `let <name> = prefix ^ "<suffix>"`
        for (name, value) in [
            ("writeProperty", capabilities::WRITE_PROPERTY),
            ("accessGlobals", capabilities::ACCESS_GLOBALS),
            ("readGlobals", capabilities::READ_GLOBALS),
            ("systemLocal", capabilities::SYSTEM_LOCAL),
            ("implicitPolicy", capabilities::IMPLICIT_POLICY),
            ("implicitPolicyLocal", capabilities::IMPLICIT_POLICY_LOCAL),
            ("io", capabilities::IO),
            ("rx", capabilities::RX),
        ] {
            assert_eq!(
                value,
                format!("{}{}", capabilities::PREFIX, ocaml_string("Capabilities", name)),
                "{}",
                name
            );
        }
        assert_eq!(capabilities::RX_LOCAL, format!("{}Local", capabilities::RX));
        for (name, value) in [
            ("classname_to_class", special_functions::CLASSNAME_TO_CLASS),
            (
                "classname_to_class_strict_isolation_backdoor",
                special_functions::CLASSNAME_TO_CLASS_STRICT_ISOLATION_BACKDOOR,
            ),
            ("get_class_from_type", special_functions::GET_CLASS_FROM_TYPE),
            ("global_get", special_functions::GLOBAL_GET),
            ("global_set", special_functions::GLOBAL_SET),
            ("global_unset", special_functions::GLOBAL_UNSET),
            ("tag_provenance_here", special_functions::TAG_PROVENANCE_HERE),
        ] {
            assert_eq!(escaped(value), ocaml_string("SpecialFunctions", name), "{}", name);
        }
        for (name, value) in [
            ("exit", special_functions::EXIT),
            ("unsafe_cast", special_functions::UNSAFE_CAST),
            ("unsafe_nonnull_cast", special_functions::UNSAFE_NONNULL_CAST),
            ("isset", pseudo_functions::ISSET),
            ("unset", pseudo_functions::UNSET),
        ] {
            assert_eq!(escaped(value), ocaml_string("PseudoFunctions", name), "{}", name);
        }
        for (name, value) in [
            ("type_structure", stdlib_functions::TYPE_STRUCTURE),
            ("type_structure_classname", stdlib_functions::TYPE_STRUCTURE_CLASSNAME),
            ("type_structure_class", stdlib_functions::TYPE_STRUCTURE_CLASS),
        ] {
            assert_eq!(escaped(value), ocaml_string("StdlibFunctions", name), "{}", name);
        }
        assert_eq!(
            pre_namespaced_functions::ECHO,
            ocaml_string("PreNamespacedFunctions", "echo")
        );
        assert_eq!(
            coeffects::LOCAL_CAPABILITY,
            ocaml_string("Coeffects", "local_capability")
        );
        assert_eq!(
            coeffects::GENERATED_GENERIC_PREFIX,
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
