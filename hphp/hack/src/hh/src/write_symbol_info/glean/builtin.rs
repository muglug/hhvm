// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Builtin` of the `glean_schema` library (`write_symbol_info/glean/builtin.ml`).

/// `Builtin.Unit`.
pub mod unit {
    use crate::yojson::safe::T as Json;

    /// `Builtin.Unit.t`.
    pub type T = ();

    /// `Builtin.Unit.to_json`.
    pub fn to_json(_: &T) -> Json {
        Json::Assoc(vec![])
    }

    #[cfg(test)]
    pub fn of_json(_: &Json) -> T {}
}
