// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_named_params.ml`. See `hh/PORTING.md`.
//!
//! The OCaml function is polymorphic in the phase of the function types; its
//! only caller (`Typing_subtype`) passes localized ones, which is what this
//! takes.

use std::collections::BTreeMap;

use crate::typing_defs;
use crate::typing_defs_core;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;

/// `type mismatch`. The lists are in decreasing order of the names, as the
/// OCaml builds them (prepending while folding over an `S_map`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mismatch {
    pub extra_names: Vec<String>,
    pub missing_names: Vec<String>,
    pub too_optional_names: Vec<String>,
    /// True when the expected (super) function type has a named-variadic
    /// parameter but the actual (sub) function type does not. In that case
    /// the consumer of the expected type may pass arbitrary named args,
    /// which the actual function cannot absorb.
    pub missing_named_variadic: bool,
}

pub fn find_names_mismatch(actual_ft: &FunType, expected_ft: &FunType) -> Mismatch {
    // Build the name → param map, EXCLUDING the named-variadic entry.
    // A named-variadic represents "accepts any name of this element type",
    // not a required named parameter, so it must not participate in
    // missing/extra-name matching.
    fn named_params_of(ft: &FunType) -> BTreeMap<String, &FunParam> {
        let mut acc = BTreeMap::new();
        for fp in typing_defs::ft_params_without_named_variadic(ft) {
            match typing_defs::named_params::name_of_named_param(fp) {
                Some(name) => {
                    acc.insert(name, fp);
                }
                None => {}
            }
        }
        acc
    }
    let actual_named_params = named_params_of(actual_ft);
    let expected_named_params = named_params_of(expected_ft);
    let actual_has_named_variadic = typing_defs::ft_named_variadic_param(actual_ft).is_some();
    let expected_has_named_variadic = typing_defs::ft_named_variadic_param(expected_ft).is_some();
    // `S_map.fold` visits the names in increasing order, and each is
    // prepended to the accumulator.
    let mut extra_names = vec![];
    for (name, actual_fp) in &actual_named_params {
        // function(optional named bool $b): void   <:   function(): void
        let is_expected = expected_named_params.contains_key(name);
        let is_required = !typing_defs_core::get_fp_is_optional(actual_fp);
        if is_required && !is_expected {
            extra_names.insert(0, name.clone());
        }
    }
    let mut acc = Mismatch {
        extra_names,
        missing_names: vec![],
        too_optional_names: vec![],
        missing_named_variadic: expected_has_named_variadic && !actual_has_named_variadic,
    };
    for (name, expected_fp) in &expected_named_params {
        match actual_named_params.get(name) {
            Some(actual_fp) => {
                let expected_is_optional = typing_defs_core::get_fp_is_optional(expected_fp);
                let actual_is_required = !typing_defs_core::get_fp_is_optional(actual_fp);
                if expected_is_optional && actual_is_required {
                    acc.too_optional_names.insert(0, name.clone());
                }
            }
            None => {
                // If the actual function has a named-variadic, it absorbs any name
                // the caller of the expected function might send. The element-type
                // compatibility check happens separately during parameter subtyping.
                if actual_has_named_variadic {
                } else {
                    acc.missing_names.insert(0, name.clone());
                }
            }
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;
    use oxidized::typing_defs_flags::FunParamFlags;
    use oxidized::typing_defs_flags::FunTypeFlags;

    use super::*;
    use crate::typing_defs_core::Capability;
    use crate::typing_defs_core::FunImplicitParams;
    use crate::typing_make_type as make_type;
    use crate::typing_reason as reason;

    fn named(name: &str, optional: bool) -> FunParam {
        let mut flags = FunParamFlags::NAMED;
        flags.set(FunParamFlags::IS_OPTIONAL, optional);
        FunParam {
            pos: Pos::NONE,
            name: Some(format!("${}", name)),
            type_: make_type::mixed(reason::none()),
            flags,
            def_value: None,
        }
    }

    fn positional() -> FunParam {
        FunParam {
            pos: Pos::NONE,
            name: Some("$p".to_string()),
            type_: make_type::mixed(reason::none()),
            flags: FunParamFlags::empty(),
            def_value: None,
        }
    }

    fn ft(params: Vec<FunParam>, named_variadic: bool) -> FunType {
        FunType {
            tparams: vec![],
            where_constraints: vec![],
            params,
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(Pos::NONE),
            },
            ret: make_type::void(reason::none()),
            flags: if named_variadic {
                FunTypeFlags::NAMED_VARIADIC
            } else {
                FunTypeFlags::empty()
            },
            instantiated: false,
        }
    }

    #[test]
    fn names_are_listed_in_decreasing_order() {
        let actual = ft(
            vec![
                positional(),
                named("a", false),
                named("c", false),
                named("b", true),
                named("e", false),
            ],
            false,
        );
        let expected = ft(vec![named("d", false), named("e", true), named("f", false)], false);
        assert_eq!(
            find_names_mismatch(&actual, &expected),
            Mismatch {
                // required in actual, absent from expected (b is optional)
                extra_names: vec!["c".to_string(), "a".to_string()],
                missing_names: vec!["f".to_string(), "d".to_string()],
                too_optional_names: vec!["e".to_string()],
                missing_named_variadic: false,
            }
        );
    }

    #[test]
    fn a_named_variadic_absorbs_missing_names_and_is_not_a_name() {
        // The named-variadic is the last parameter: it is not matched by name.
        let actual = ft(vec![named("a", false), named("v", false)], true);
        let expected = ft(vec![named("a", false), named("b", false)], false);
        let m = find_names_mismatch(&actual, &expected);
        assert!(m.missing_names.is_empty());
        assert!(m.extra_names.is_empty());
        assert!(!m.missing_named_variadic);
        // The other way around: the expected type has a named-variadic that
        // the actual one lacks, and "b" is required by the actual type only.
        let m = find_names_mismatch(&expected, &actual);
        assert!(m.missing_named_variadic);
        assert_eq!(m.extra_names, vec!["b".to_string()]);
    }
}
