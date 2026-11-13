// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Typechecker_options` (`options/typechecker_options.ml`). See
//! `hh/PORTING.md`.
//!
//! The type is `oxidized::typechecker_options::TypecheckerOptions`
//! (`Global_options.t`), re-exported here.
//!
//! Most of `typechecker_options.ml` is one function for each field, which
//! returns the field (`let skip_tast_checks t = t.tco_skip_tast_checks`).
//! Those are not here: read the field. This module has the functions that do
//! something else, and the two accessors that the error renderers call as
//! functions (`custom_error_config` and `tco_extended_reasons`).

#![allow(non_upper_case_globals)]

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

pub const experimental_supportdynamic_type_hint: &str = "supportdynamic_type_hint";

pub const experimental_consider_type_const_enforceable: &str =
    "experimental_consider_type_const_enforceable";

/// Resolve the this type inside enum classes using the proper context
pub const experimental_sound_enum_class_type_const: &str = "sound_enum_class_this_type";

pub const experimental_try_constraint_method_inference: &str =
    "experimental_try_constraint_method_inference";

pub static experimental_all: LazyLock<SSet> = LazyLock::new(|| {
    [
        experimental_supportdynamic_type_hint,
        experimental_consider_type_const_enforceable,
        experimental_sound_enum_class_type_const,
        experimental_try_constraint_method_inference,
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
});

/// There are no migration flags at the moment.
pub static migration_flags_all: LazyLock<SSet> = LazyLock::new(SSet::new);

pub fn set_skip_hierarchy_checks(t: T) -> T {
    T {
        tco_skip_hierarchy_checks: true,
        ..t
    }
}

pub fn any_coeffects(t: &T) -> bool {
    t.tco_coeffects || t.tco_coeffects_local
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

pub fn needs_concrete_body_or_call_check_enabled(t: &T) -> bool {
    t.needs_concrete_body_check > 0
        || t.needs_concrete_forwarding_call_check > 0
        || t.needs_concrete_class_call_check > 0
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
    fn features() {
        let mut t = T::default();
        assert!(!legacy_experimental_feature_enabled(
            &t,
            experimental_sound_enum_class_type_const
        ));
        t.tco_legacy_experimental_features = experimental_all.clone();
        assert!(legacy_experimental_feature_enabled(
            &t,
            experimental_sound_enum_class_type_const
        ));
        assert_eq!(experimental_all.len(), 4);

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
        t.tco_coeffects = false;
        t.tco_coeffects_local = false;
        assert!(!any_coeffects(&t));
        t.tco_coeffects_local = true;
        assert!(any_coeffects(&t));

        t.needs_concrete_body_check = 0;
        t.needs_concrete_forwarding_call_check = 0;
        t.needs_concrete_class_call_check = 0;
        assert!(!needs_concrete_body_or_call_check_enabled(&t));
        t.needs_concrete_class_call_check = 1;
        assert!(needs_concrete_body_or_call_check_enabled(&t));

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
