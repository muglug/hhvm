// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/logging/feature_logging.ml` (`Feature_logging`), the stub
//! that the open-source build links: every feature name is the empty string.
//! See `hh/PORTING.md`.
//!
//! The OCaml values are `const`s with the OCaml names in upper case; the function
//! `unknown_params_with_uses` is a function.

pub mod lambda {
    pub const CONTEXTUAL_PARAMS: &str = "";

    pub const EXPLICIT_PARAMS: &str = "";

    pub const NO_PARAMS: &str = "";

    pub const NON_FUNCTION_TYPED_CONTEXT: &str = "";

    pub const NON_STRICT_UNKNOWN_PARAMS: &str = "";

    pub const UNTYPED_CONTEXT: &str = "";

    pub const UNKNOWN_PARAMS: &str = "";

    pub fn unknown_params_with_uses<A>(_: A) -> &'static str {
        ""
    }

    pub const FRESH_TYVAR_PARAMS: &str = "";
}

#[cfg(test)]
mod tests {
    use super::lambda;

    #[test]
    fn every_feature_name_is_empty() {
        for s in [
            lambda::CONTEXTUAL_PARAMS,
            lambda::EXPLICIT_PARAMS,
            lambda::NO_PARAMS,
            lambda::NON_FUNCTION_TYPED_CONTEXT,
            lambda::NON_STRICT_UNKNOWN_PARAMS,
            lambda::UNTYPED_CONTEXT,
            lambda::UNKNOWN_PARAMS,
            lambda::unknown_params_with_uses(3),
            lambda::FRESH_TYVAR_PARAMS,
        ] {
            assert_eq!(s, "");
        }
    }
}
