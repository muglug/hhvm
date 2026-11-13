// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_attributes.ml`. See `hh/PORTING.md`.
//!
//! The tables of `Naming_special_names` that this module reads
//! (`AttributeKinds.plain_english_map`, and the `contexts` of
//! `UserAttributes.as_map` and `UserAttributes.systemlib_map`) have no Rust
//! counterpart (`naming_special_names_rust::attribute_kinds` lacks
//! `module_`, and nothing has the contexts of the builtin attributes): they
//! are in [`sn`] below, generated from `naming/naming_special_names.ml`
//! (only the `contexts` of each `attr_info`, which is all this module uses).

#![allow(non_upper_case_globals)]

use oxidized::aast;
use oxidized::naming_error::NamingError;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::string_utils;
use crate::typechecker_options;
use crate::typing_coeffects;
use crate::typing_defs_core::PosString;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_lenv;
use crate::typing_make_type as make_type;

/// The parts of `Naming_special_names` that this module needs and that
/// `naming_special_names_rust` does not have.
pub mod sn {
    /// `Naming_special_names.AttributeKinds`
    pub mod attribute_kinds {
        pub const cls: &str = "\\HH\\ClassAttribute";
        pub const clscst: &str = "\\HH\\ClassConstantAttribute";
        pub const enum_: &str = "\\HH\\EnumAttribute";
        pub const typealias: &str = "\\HH\\TypeAliasAttribute";
        pub const fn_: &str = "\\HH\\FunctionAttribute";
        pub const mthd: &str = "\\HH\\MethodAttribute";
        pub const instProperty: &str = "\\HH\\InstancePropertyAttribute";
        pub const staticProperty: &str = "\\HH\\StaticPropertyAttribute";
        pub const parameter: &str = "\\HH\\ParameterAttribute";
        pub const typeparam: &str = "\\HH\\TypeParameterAttribute";
        pub const file: &str = "\\HH\\FileAttribute";
        pub const typeconst: &str = "\\HH\\TypeConstantAttribute";
        pub const lambda: &str = "\\HH\\LambdaAttribute";
        pub const enumcls: &str = "\\HH\\EnumClassAttribute";
        pub const module_: &str = "\\HH\\ModuleAttribute";

        /// `plain_english_map` (an `S_map`: looked up by key).
        pub fn plain_english_map_find_opt(k: &str) -> Option<&'static str> {
            [
                (cls, "a class"),
                (clscst, "a constant of a class"),
                (enum_, "an enum"),
                (typealias, "a typealias"),
                (fn_, "a function"),
                (mthd, "a method"),
                (instProperty, "an instance property"),
                (staticProperty, "a static property"),
                (parameter, "a parameter"),
                (typeparam, "a type parameter"),
                (file, "a file"),
                (typeconst, "a type constant"),
                (lambda, "a lambda expression"),
                (enumcls, "an enum class"),
                (module_, "a module"),
            ]
            .into_iter()
            .find(|(key, _)| *key == k)
            .map(|(_, v)| v)
        }
    }

    /// `Naming_special_names.UserAttributes`: the `contexts` of the
    /// `attr_info`s of `as_map` and `systemlib_map`, in the order of the
    /// keys (`S_map.bindings`).
    pub mod user_attributes {
        use super::attribute_kinds as ak;

        /// `as_map`
        pub static as_map: &[(&str, &[&str])] = &[
            ("__AcceptDisposable", &[ak::parameter]),
            ("__AllowUncheckedEnumValues", &[ak::enum_]),
            ("__AsioLowPri", &[ak::fn_, ak::mthd]),
            ("__ConsistentConstruct", &[ak::cls]),
            (
                "__Const",
                &[ak::cls, ak::instProperty, ak::parameter, ak::staticProperty],
            ),
            ("__Deprecated", &[ak::fn_, ak::mthd]),
            ("__DisableTypecheckerInternal", &[ak::fn_, ak::mthd]),
            ("__DisjointShapeSplat", &[ak::typealias]),
            ("__Docs", &[ak::cls, ak::enum_, ak::enumcls, ak::typealias]),
            ("__DynamicallyCallable", &[ak::fn_, ak::mthd]),
            ("__DynamicallyConstructible", &[ak::cls]),
            ("__DynamicallyReferenced", &[ak::cls]),
            ("__EnableMethodTraitDiamond", &[ak::cls]),
            ("__EnableUnstableFeatures", &[ak::file]),
            ("__Enforceable", &[ak::typeconst, ak::typeparam]),
            ("__EntryPoint", &[ak::fn_]),
            ("__EnumClass", &[ak::cls, ak::enumcls]),
            ("__Explicit", &[ak::typeparam]),
            ("__GatedByFeatureFlag", &[ak::cls, ak::typealias, ak::fn_]),
            ("__HasReifiedParent", &[]),
            ("__IgnoreReadonlyError", &[ak::parameter]),
            ("__ImplementedBy", &[ak::mthd]),
            ("__LSB", &[ak::staticProperty]),
            ("__LateInit", &[ak::instProperty, ak::staticProperty]),
            ("__Memoize", &[ak::fn_, ak::mthd]),
            ("__MemoizeLSB", &[ak::mthd]),
            ("__MockClass", &[ak::cls]),
            ("__ModuleLevelTrait", &[ak::cls]),
            ("__NEVER_INLINE", &[ak::fn_, ak::mthd]),
            ("__NativeData", &[ak::cls]),
            ("__NeedsConcrete", &[ak::mthd]),
            ("__Newable", &[ak::typeparam]),
            ("__NoAutoBound", &[ak::typeparam]),
            (
                "__NoAutoDynamic",
                &[ak::fn_, ak::cls, ak::mthd, ak::typealias],
            ),
            (
                "__NoAutoLikes",
                &[
                    ak::fn_,
                    ak::mthd,
                    ak::staticProperty,
                    ak::instProperty,
                    ak::parameter,
                    ak::lambda,
                ],
            ),
            ("__NoDisjointUnion", &[ak::typeparam]),
            ("__NoFlatten", &[]),
            (
                "__NoSupportDynamicType",
                &[ak::fn_, ak::cls, ak::mthd, ak::lambda, ak::enumcls],
            ),
            ("__NonDisjoint", &[ak::typeparam]),
            ("__Overlapping", &[ak::fn_, ak::mthd]),
            ("__Override", &[ak::mthd]),
            ("__PHPStdLib", &[ak::cls, ak::fn_, ak::mthd]),
            ("__PackageOverride", &[ak::file]),
            ("__ProvenanceSkipFrame", &[ak::fn_, ak::mthd, ak::lambda]),
            ("__Reifiable", &[ak::typeconst]),
            ("__Reified", &[]),
            ("__RequireDynamic", &[ak::typeparam]),
            ("__RequirePackage", &[ak::fn_, ak::mthd]),
            ("__ReturnDisposable", &[ak::fn_, ak::mthd, ak::lambda]),
            ("__SafeForGlobalAccessCheck", &[ak::staticProperty]),
            ("__Sealed", &[ak::cls, ak::enumcls, ak::enum_, ak::mthd]),
            ("__ShapeKey", &[ak::clscst]),
            (
                "__SimpliHack",
                &[
                    ak::cls,
                    ak::clscst,
                    ak::enum_,
                    ak::enumcls,
                    ak::file,
                    ak::fn_,
                    ak::instProperty,
                    ak::lambda,
                    ak::mthd,
                    ak::module_,
                    ak::parameter,
                    ak::staticProperty,
                    ak::typealias,
                    ak::typeconst,
                    ak::typeparam,
                ],
            ),
            (
                "__Soft",
                &[
                    ak::instProperty,
                    ak::parameter,
                    ak::staticProperty,
                    ak::typeparam,
                ],
            ),
            (
                "__SoftInternal",
                &[
                    ak::fn_,
                    ak::cls,
                    ak::mthd,
                    ak::instProperty,
                    ak::staticProperty,
                    ak::parameter,
                    ak::enum_,
                    ak::enumcls,
                ],
            ),
            ("__SoftRequirePackage", &[ak::fn_, ak::mthd]),
            ("__StrictSwitch", &[ak::fn_, ak::mthd]),
            (
                "__SupportDynamicType",
                &[ak::fn_, ak::cls, ak::mthd, ak::lambda, ak::enumcls],
            ),
            (
                "__TestsBypassVisibility",
                &[ak::cls, ak::mthd, ak::instProperty, ak::staticProperty],
            ),
            ("__UNSAFE_AllowMultipleInstantiations", &[ak::cls]),
            ("__Warn", &[ak::typeparam]),
        ];

        /// These are names which are allowed in the systemlib but not in normal programs
        /// (`systemlib_map`)
        pub static systemlib_map: &[(&str, &[&str])] = &[
            ("__ALWAYS_INLINE", &[ak::fn_, ak::mthd]),
            ("__EagerVMSync", &[ak::fn_, ak::mthd]),
            ("__IgnoreCoeffectLocalErrors", &[ak::fn_, ak::mthd]),
            ("__IgnoreReadonlyLocalErrors", &[ak::fn_, ak::mthd]),
            ("__IsFoldable", &[ak::fn_, ak::mthd]),
            ("__Native", &[ak::fn_, ak::mthd]),
            ("__OutOnly", &[ak::parameter]),
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
}

pub type AttributeInterfaceName = String;

/// `new_object_checker`: `Pos.t -> env -> Typing_defs.pos_string ->
/// Nast.argument list -> env`.
pub type NewObjectChecker<'a> = dyn Fn(&Pos, &mut Env, &PosString, &[nast::Argument]) + 'a;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_naming_phase_error(error: NamingPhaseError) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(error) {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Naming_error_utils.render_custom_error`
fn render_custom_error(
    t: &[itertools::Either<String, crate::custom_error_eval::value::T>],
) -> String {
    use itertools::Either;

    use crate::custom_error_eval::value;
    // `List.fold_right`: from the last element to the first.
    let mut acc = String::new();
    for v in t.iter().rev() {
        acc = match v {
            Either::Left(str) => format!("{}{}", str, acc),
            Either::Right(value::T::Name(nm)) => {
                format!("{}{}", crate::markdown_lite::md_codify(nm), acc)
            }
            Either::Right(_) => acc,
        }
    }
    acc
}

/// `Diagnostics.add_diagnostic (Naming_error_utils.to_user_diagnostic err
/// custom_err_config)`: the diagnostic of `crate::naming_errors`, with the
/// messages of the custom error config (which that renderer does not add).
fn add_naming_error(err: NamingError, custom_err_config: &crate::custom_error_config::T) {
    let custom_msgs: Vec<String> =
        crate::custom_error_eval::eval_naming_error(custom_err_config, &err)
            .iter()
            .map(|t| render_custom_error(t))
            .collect();
    if let Some(mut diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::Naming(err))
    {
        diagnostic.custom_msgs = custom_msgs;
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

fn check_implements(
    check_new_object: &NewObjectChecker<'_>,
    attr_interface: &str,
    ua: &nast::UserAttribute,
    env: &mut Env,
) {
    let aast::UserAttribute {
        name: oxidized::ast_defs::Id(attr_pos, attr_name),
        params,
    } = ua;
    let expr_kind = match sn::attribute_kinds::plain_english_map_find_opt(attr_interface) {
        Some(ek) => ek,
        None => "this expression",
        // this case should never execute
    };
    let is_systemlib = typing_env::get_tcopt(env).po.is_systemlib;
    if attr_name.starts_with("__") {
        // Check against builtins
        let check_attr = |map: &'static [(&'static str, &'static [&'static str])]| {
            match sn::user_attributes::find_opt(attr_name, map) {
                Some(contexts) => {
                    if !contexts.iter().any(|c| *c == attr_interface) {
                        add_naming_phase_error(NamingPhaseError::NastCheck(
                            NastCheckError::WrongExpressionKindBuiltinAttribute {
                                expr_kind: expr_kind.to_string(),
                                pos: attr_pos.clone(),
                                attr_name: attr_name.clone(),
                            },
                        ))
                    }
                    true
                }
                None => false,
            }
        };
        if check_attr(sn::user_attributes::as_map)
            || (is_systemlib && check_attr(sn::user_attributes::systemlib_map))
        {
        } else {
            let all_valid_user_attributes: Vec<String> = sn::user_attributes::as_map
                .iter()
                .filter(|(_, contexts)| contexts.iter().any(|c| *c == attr_interface))
                .map(|(name, _)| name.to_string())
                .collect();

            let closest_attr_name = string_utils::most_similar(
                None,
                attr_name,
                &all_valid_user_attributes,
                |x: &String| x.clone(),
            );

            let custom_err_config =
                typechecker_options::custom_error_config(&typing_env::get_tcopt(env));
            add_naming_error(
                NamingError::UnboundAttributeName {
                    pos: attr_pos.clone(),
                    attr_name: attr_name.clone(),
                    closest_attr_name,
                },
                &custom_err_config,
            )
        }
    } else {
        match typing_env::get_class(env, attr_name) {
            decl_entry::T::Found(attr_class) => {
                // Found matching class
                let attr_cid = PosString(cls::pos(&attr_class), cls::name(&attr_class));
                // Package-boundary enforcement for attribute classes (strict-isolation
                // targets) is handled uniformly with other class references in
                // `class_id_`'s `should_check_package_boundary`; nothing to do here.
                if !cls::has_ancestor(&attr_class, attr_interface) {
                    let attr_class_pos: PosOrDecl = cls::pos(&attr_class);
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Wrong_expression_kind_attribute {
                            expr_kind: expr_kind.to_string(),
                            pos: attr_pos.clone(),
                            attr_name: attr_name.clone(),
                            attr_class_pos,
                            attr_class_name: cls::name(&attr_class),
                            intf_name: attr_interface.to_string(),
                        }),
                        env,
                    )
                } else {
                    let args: Vec<nast::Argument> = params
                        .iter()
                        .map(|e| aast::Argument::Anormal(e.clone()))
                        .collect();
                    check_new_object(attr_pos, env, &attr_cid, &args)
                }
            }
            decl_entry::T::NotYetAvailable => {
                // A retry will happen. Don't emit error to avoid error-based backtracking
            }
            _ => {
                let custom_err_config =
                    typechecker_options::custom_error_config(&typing_env::get_tcopt(env));
                add_naming_error(
                    NamingError::UnboundAttributeName {
                        pos: attr_pos.clone(),
                        attr_name: attr_name.clone(),
                        closest_attr_name: None,
                    },
                    &custom_err_config,
                )
            }
        }
    }
}

/// The first `check_def` of `typing_attributes.ml`, which the second one
/// shadows (and calls). `List.fold_right`: from the last attribute to the
/// first.
fn check_def_(
    env: &mut Env,
    check_new_object: &NewObjectChecker<'_>,
    kind: &str,
    attributes: &[nast::UserAttribute],
) {
    for attr in attributes.iter().rev() {
        check_implements(check_new_object, kind, attr, env)
    }
}

/// Checks a list of user attributes:
/// - checks that the attributes are on the proper kind of element,
///   by checking subtyping of the attribute class with the provided attribute interface
///   (e.g. FileAttribute, MethodAttribute, see Naming_special_names for a full list)
/// - checks for unbound attribute names
/// - runs the provided new_object_checker, which checks creating an instance of the attribute class.
///
/// TODO(coeffects) change to mixed after changing those constructors to pure
pub fn check_def(
    env: &mut Env,
    check_new_object: &NewObjectChecker<'_>,
    kind: &str,
    attributes: &[nast::UserAttribute],
) {
    let defaults = make_type::default_capability(PosOrDecl::NONE);
    let conts = typing_env::all_continuations(env);
    typing_lenv::stash_and_do(env, &conts, |env| {
        let _ = typing_coeffects::register_capabilities(env, defaults.clone(), defaults);
        check_def_(env, check_new_object, kind, attributes)
    })
}

#[cfg(test)]
mod tests {
    use super::sn::user_attributes;

    #[test]
    fn tables_are_sorted() {
        for map in [user_attributes::as_map, user_attributes::systemlib_map] {
            assert!(map.windows(2).all(|w| w[0].0 < w[1].0));
        }
        assert_eq!(user_attributes::as_map.len(), 61);
        assert_eq!(user_attributes::systemlib_map.len(), 7);
    }
}
