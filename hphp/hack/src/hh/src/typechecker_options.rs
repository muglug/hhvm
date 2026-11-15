// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `options/typechecker_options.ml`. See `hh/PORTING.md`.
//!
//! The type is `oxidized::typechecker_options::TypecheckerOptions`
//! (`Global_options.t`), re-exported here.
//!
//! Most of `typechecker_options.ml` is one function for each field, which
//! returns the field (`let skip_tast_checks t = t.tco_skip_tast_checks`).
//! Those are not here: read the field. This module has the functions that do
//! something else, and the two accessors that the error renderers call as
//! functions (`custom_error_config` and `tco_extended_reasons`).

use std::sync::LazyLock;

use oxidized::custom_error_config::CustomErrorConfig;
use oxidized::experimental_features::FeatureStatus;
use oxidized::global_options::ExtendedReasonsConfig;
use oxidized::s_set::SSet;
pub use oxidized::typechecker_options::*;

pub type T = TypecheckerOptions;

pub fn legacy_experimental_feature_enabled(t: &T, feature: &str) -> bool {
    t.tco_legacy_experimental_features.contains(feature)
}

// TYPECHECKER-SPECIFIC OPTIONS

pub const EXPERIMENTAL_SUPPORTDYNAMIC_TYPE_HINT: &str = "supportdynamic_type_hint";

pub const EXPERIMENTAL_CONSIDER_TYPE_CONST_ENFORCEABLE: &str =
    "experimental_consider_type_const_enforceable";

/// Resolve the this type inside enum classes using the proper context
pub const EXPERIMENTAL_SOUND_ENUM_CLASS_TYPE_CONST: &str = "sound_enum_class_this_type";

pub const EXPERIMENTAL_TRY_CONSTRAINT_METHOD_INFERENCE: &str =
    "experimental_try_constraint_method_inference";

pub static EXPERIMENTAL_ALL: LazyLock<SSet> = LazyLock::new(|| {
    [
        EXPERIMENTAL_SUPPORTDYNAMIC_TYPE_HINT,
        EXPERIMENTAL_CONSIDER_TYPE_CONST_ENFORCEABLE,
        EXPERIMENTAL_SOUND_ENUM_CLASS_TYPE_CONST,
        EXPERIMENTAL_TRY_CONSTRAINT_METHOD_INFERENCE,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
});

/// There are no migration flags at the moment.
pub static MIGRATION_FLAGS_ALL: LazyLock<SSet> = LazyLock::new(SSet::new);

pub fn set_package_info(t: T, package_info: oxidized::package_info::PackageInfo) -> T {
    let popt = oxidized::parser_options::ParserOptions {
        package_info,
        ..t.po
    };
    T { po: popt, ..t }
}

pub fn set_skip_hierarchy_checks(t: T) -> T {
    T {
        tco_skip_hierarchy_checks: true,
        ..t
    }
}

pub fn custom_error_config(t: &T) -> CustomErrorConfig {
    t.tco_custom_error_config.clone()
}

pub fn set_skip_check_under_dynamic(t: T) -> T {
    T {
        tco_skip_check_under_dynamic: true,
        ..t
    }
}

pub fn set_tco_enable_expression_trees(t: T, b: bool) -> T {
    T {
        tco_enable_expression_trees: b,
        ..t
    }
}

pub fn pessimise_builtins(t: &T) -> bool {
    // `everything_sdt t || t.tco_pessimise_builtins`
    t.po.everything_sdt || t.tco_pessimise_builtins
}

pub fn log_fanout(t: &T, fanout_cardinal: isize) -> bool {
    match t.tco_log_large_fanouts_threshold {
        None => false,
        Some(threshold) => fanout_cardinal >= threshold,
    }
}

pub fn set_tco_autocomplete_mode(t: T) -> T {
    T {
        tco_autocomplete_mode: true,
        ..t
    }
}

pub fn tco_extended_reasons(t: &T) -> Option<ExtendedReasonsConfig> {
    t.tco_extended_reasons.clone()
}

pub fn check_duplicate_runtime_shape_keys(t: &T) -> bool {
    t.po.check_duplicate_runtime_shape_keys
        && t.po.include_enum_member_values
        && t.po.include_const_shape_key_values
}

pub fn needs_concrete_class_function_pointer_check(t: &T) -> isize {
    t.needs_concrete_class_function_pointer_check
}

pub fn enable_recursive_case_types(t: T) -> T {
    T {
        recursive_case_types: true,
        ..t
    }
}

pub fn is_unstable_feature_enabled(t: &T, name: &str) -> bool {
    t.tco_enabled_unstable_features.contains(name)
        || match t.po.experimental_features.get(name) {
            Some(FeatureStatus::OngoingRelease) => true,
            _ => false,
        }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pessimise_builtins_is_everything_sdt_or_the_option() {
        let mut t = T::default();
        t.po.everything_sdt = false;
        t.tco_pessimise_builtins = false;
        assert!(!pessimise_builtins(&t));
        t.tco_pessimise_builtins = true;
        assert!(pessimise_builtins(&t));
        t.tco_pessimise_builtins = false;
        t.po.everything_sdt = true;
        assert!(pessimise_builtins(&t));
    }

    #[test]
    fn features() {
        let mut t = T::default();
        assert!(!legacy_experimental_feature_enabled(
            &t,
            EXPERIMENTAL_SOUND_ENUM_CLASS_TYPE_CONST
        ));
        t.tco_legacy_experimental_features = EXPERIMENTAL_ALL.clone();
        assert!(legacy_experimental_feature_enabled(
            &t,
            EXPERIMENTAL_SOUND_ENUM_CLASS_TYPE_CONST
        ));
        assert_eq!(EXPERIMENTAL_ALL.len(), 4);

        assert!(!is_unstable_feature_enabled(&t, "some_feature"));
        t.po.experimental_features
            .insert("some_feature".to_string(), FeatureStatus::Unstable);
        assert!(!is_unstable_feature_enabled(&t, "some_feature"));
        t.po.experimental_features
            .insert("some_feature".to_string(), FeatureStatus::OngoingRelease);
        assert!(is_unstable_feature_enabled(&t, "some_feature"));
        t.po.experimental_features.clear();
        t.tco_enabled_unstable_features
            .insert("some_feature".to_string());
        assert!(is_unstable_feature_enabled(&t, "some_feature"));
    }

    #[test]
    fn setters_and_predicates() {
        let mut t = T::default();
        assert_eq!(needs_concrete_class_function_pointer_check(&t), 2);
        t.needs_concrete_class_function_pointer_check = 1;
        assert_eq!(needs_concrete_class_function_pointer_check(&t), 1);

        t.tco_log_large_fanouts_threshold = None;
        assert!(!log_fanout(&t, 1000));
        t.tco_log_large_fanouts_threshold = Some(10);
        assert!(log_fanout(&t, 10) && !log_fanout(&t, 9));

        let t = set_tco_enable_expression_trees(t, false);
        assert!(!t.tco_enable_expression_trees);
        let t = set_tco_enable_expression_trees(t, true);
        assert!(t.tco_enable_expression_trees);
        let t = set_skip_hierarchy_checks(t);
        let t = set_skip_check_under_dynamic(t);
        let t = set_tco_autocomplete_mode(t);
        let t = enable_recursive_case_types(t);
        assert!(
            t.tco_skip_hierarchy_checks
                && t.tco_skip_check_under_dynamic
                && t.tco_autocomplete_mode
                && t.recursive_case_types
        );
        // The other fields are kept.
        assert_eq!(t.tco_log_large_fanouts_threshold, Some(10));
    }
}
