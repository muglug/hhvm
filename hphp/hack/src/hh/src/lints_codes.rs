// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints_codes.ml`. See `hh/PORTING.md`.

/// `module Codes`: the codes of the lints, as OCaml has them (`int`s).
#[allow(non_upper_case_globals)]
pub mod codes {
    // 5501 - 5541 reserved for FB.

    pub const deprecated: isize = 5542;

    // 5543 - 5548 reserved.

    pub const include_use: isize = 5549;

    // 5550 - 5561 reserved.

    pub const clone_use: isize = 5562;

    // 5563 - 5567 reserved.

    pub const loop_variable_shadows_local_variable: isize = 5568;

    // 5569 - 5574 reserved.

    pub const duplicate_key: isize = 5575;

    // 5576 - 5580 reserved.

    pub const if_literal: isize = 5581;

    // 5582 - 5607 reserved.

    pub const non_equatable_comparison: isize = 5607;

    pub const invalid_contains_check: isize = 5608;

    pub const is_always_true: isize = 5609;

    pub const is_always_false: isize = 5610;

    // let deprecated_invalid_null_check = 5611

    pub const invalid_switch_case_value_type: isize = 5614;

    // 5615 reserved.

    pub const missing_override_attribute: isize = 5616;

    // let sketchy_null_check = 5618

    pub const invalid_truthiness_test: isize = 5622;

    pub const sketchy_truthiness_test: isize = 5623;

    pub const redundant_generic: isize = 5624;

    // let deprecated_pocket_universes_reserved_syntax = 5625

    // let deprecated_as_invalid_type = 5626

    pub const class_overrides_all_trait_methods: isize = 5627;

    pub const as_always_succeeds: isize = 5628;

    pub const as_always_fails: isize = 5629;

    // let deprecated_redundant_nonnull_assertion = 5630

    pub const bool_method_return_hint: isize = 5631;

    // let deprecated_missing_via_label_attribute = 5632

    // let deprecated_nullsafe_not_needed = 5633

    pub const duplicate_property_enum_init: isize = 5634;

    pub const duplicate_property: isize = 5635;

    // 5636 - 5637 reserved.

    pub const invalid_disjointness_check: isize = 5638;

    /// DEPRECATED
    pub const inferred_variance: isize = 5639;

    pub const switch_nonexhaustive: isize = 5640;

    pub const bad_xhp_enum_attribute_value: isize = 5641;

    pub const unreachable_method_in_trait: isize = 5642;

    pub const comparing_booleans: isize = 5643;

    pub const pointless_booleans_expression: isize = 5644;

    pub const unconditional_recursion: isize = 5645;

    pub const branch_return_same_value: isize = 5646;

    // 5647 reserved.

    pub const redundant_cast: isize = 5648;

    pub const internal_classname: isize = 5649;

    pub const async_lambda: isize = 5650;

    pub const awaitable_awaitable: isize = 5651;

    pub const cast_non_primitive: isize = 5652;

    pub const class_pointer_to_string: isize = 5653;

    // let deprecated_nullsafe_on_null = 5654

    pub const package_into_override: isize = 5655;

    pub const crosspackage_classptr_reference: isize = 5656;
}

#[cfg(test)]
mod tests {
    use super::codes;

    #[test]
    fn codes_used_by_typing() {
        assert_eq!(codes::non_equatable_comparison, 5607);
        assert_eq!(codes::is_always_true, 5609);
        assert_eq!(codes::invalid_truthiness_test, 5622);
        assert_eq!(codes::duplicate_property, 5635);
        assert_eq!(codes::cast_non_primitive, 5652);
        assert_eq!(codes::crosspackage_classptr_reference, 5656);
    }
}
