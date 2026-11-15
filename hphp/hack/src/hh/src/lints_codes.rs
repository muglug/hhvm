// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/lints_codes.ml`. See `hh/PORTING.md`.

/// `module Codes`: the codes of the lints, as OCaml has them (`int`s).
pub mod codes {
    // 5501 - 5541 reserved for FB.

    pub const DEPRECATED: isize = 5542;

    // 5543 - 5548 reserved.

    pub const INCLUDE_USE: isize = 5549;

    // 5550 - 5561 reserved.

    pub const CLONE_USE: isize = 5562;

    // 5563 - 5567 reserved.

    pub const LOOP_VARIABLE_SHADOWS_LOCAL_VARIABLE: isize = 5568;

    // 5569 - 5574 reserved.

    pub const DUPLICATE_KEY: isize = 5575;

    // 5576 - 5580 reserved.

    pub const IF_LITERAL: isize = 5581;

    // 5582 - 5607 reserved.

    pub const NON_EQUATABLE_COMPARISON: isize = 5607;

    pub const INVALID_CONTAINS_CHECK: isize = 5608;

    pub const IS_ALWAYS_TRUE: isize = 5609;

    pub const IS_ALWAYS_FALSE: isize = 5610;

    // let deprecated_invalid_null_check = 5611

    pub const INVALID_SWITCH_CASE_VALUE_TYPE: isize = 5614;

    // 5615 reserved.

    pub const MISSING_OVERRIDE_ATTRIBUTE: isize = 5616;

    // let sketchy_null_check = 5618

    pub const INVALID_TRUTHINESS_TEST: isize = 5622;

    pub const SKETCHY_TRUTHINESS_TEST: isize = 5623;

    pub const REDUNDANT_GENERIC: isize = 5624;

    // let deprecated_pocket_universes_reserved_syntax = 5625

    // let deprecated_as_invalid_type = 5626

    pub const CLASS_OVERRIDES_ALL_TRAIT_METHODS: isize = 5627;

    pub const AS_ALWAYS_SUCCEEDS: isize = 5628;

    pub const AS_ALWAYS_FAILS: isize = 5629;

    // let deprecated_redundant_nonnull_assertion = 5630

    pub const BOOL_METHOD_RETURN_HINT: isize = 5631;

    // let deprecated_missing_via_label_attribute = 5632

    // let deprecated_nullsafe_not_needed = 5633

    pub const DUPLICATE_PROPERTY_ENUM_INIT: isize = 5634;

    pub const DUPLICATE_PROPERTY: isize = 5635;

    // 5636 - 5637 reserved.

    pub const INVALID_DISJOINTNESS_CHECK: isize = 5638;

    /// DEPRECATED
    pub const INFERRED_VARIANCE: isize = 5639;

    pub const SWITCH_NONEXHAUSTIVE: isize = 5640;

    pub const BAD_XHP_ENUM_ATTRIBUTE_VALUE: isize = 5641;

    pub const UNREACHABLE_METHOD_IN_TRAIT: isize = 5642;

    pub const COMPARING_BOOLEANS: isize = 5643;

    pub const POINTLESS_BOOLEANS_EXPRESSION: isize = 5644;

    pub const UNCONDITIONAL_RECURSION: isize = 5645;

    pub const BRANCH_RETURN_SAME_VALUE: isize = 5646;

    // 5647 reserved.

    pub const REDUNDANT_CAST: isize = 5648;

    pub const INTERNAL_CLASSNAME: isize = 5649;

    pub const ASYNC_LAMBDA: isize = 5650;

    pub const AWAITABLE_AWAITABLE: isize = 5651;

    pub const CAST_NON_PRIMITIVE: isize = 5652;

    pub const CLASS_POINTER_TO_STRING: isize = 5653;

    // let deprecated_nullsafe_on_null = 5654

    pub const PACKAGE_INTO_OVERRIDE: isize = 5655;

    pub const CROSSPACKAGE_CLASSPTR_REFERENCE: isize = 5656;
}

#[cfg(test)]
mod tests {
    use super::codes;

    #[test]
    fn codes_used_by_typing() {
        assert_eq!(codes::NON_EQUATABLE_COMPARISON, 5607);
        assert_eq!(codes::IS_ALWAYS_TRUE, 5609);
        assert_eq!(codes::INVALID_TRUTHINESS_TEST, 5622);
        assert_eq!(codes::DUPLICATE_PROPERTY, 5635);
        assert_eq!(codes::CAST_NON_PRIMITIVE, 5652);
        assert_eq!(codes::CROSSPACKAGE_CLASSPTR_REFERENCE, 5656);
    }
}
