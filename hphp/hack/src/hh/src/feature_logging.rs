// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stubs/logging/feature_logging.ml` (`Feature_logging`), the stub
//! that the open-source build links: every feature name is the empty string.
//! See `hh/PORTING.md`.
//!
//! The OCaml values are `const`s with the OCaml names; the function
//! `unknown_params_with_uses` is a function.

#![allow(non_upper_case_globals)]

pub mod lambda {
    pub const contextual_params: &str = "";

    pub const explicit_params: &str = "";

    pub const no_params: &str = "";

    pub const non_function_typed_context: &str = "";

    pub const non_strict_unknown_params: &str = "";

    pub const untyped_context: &str = "";

    pub const unknown_params: &str = "";

    pub fn unknown_params_with_uses<A>(_: A) -> &'static str {
        ""
    }

    pub const fresh_tyvar_params: &str = "";
}

#[cfg(test)]
mod tests {
    use super::lambda;

    #[test]
    fn every_feature_name_is_empty() {
        for s in [
            lambda::contextual_params,
            lambda::explicit_params,
            lambda::no_params,
            lambda::non_function_typed_context,
            lambda::non_strict_unknown_params,
            lambda::untyped_context,
            lambda::unknown_params,
            lambda::unknown_params_with_uses(3),
            lambda::fresh_tyvar_params,
        ] {
            assert_eq!(s, "");
        }
    }
}
