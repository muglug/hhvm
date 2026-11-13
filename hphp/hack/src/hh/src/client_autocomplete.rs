// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_autocomplete.ml` (the printer of autocomplete
//! results). See `hh/PORTING.md`. Nothing calls it in this version of the
//! OCaml (`hh_client` has no autocomplete mode); ported with its module.
//!
//! Owned by **F3** (plan §7.3).

use crate::autocomplete_service;
use crate::autocomplete_types::AutocompleteItem;

pub fn go(results: &[AutocompleteItem], output_json: bool) {
    if output_json {
        let results = results
            .iter()
            .map(autocomplete_service::autocomplete_result_to_json)
            .collect();
        println!(
            "{}",
            crate::yojson::safe::to_string(&crate::yojson::safe::T::List(results))
        )
    } else {
        for res in results {
            let name = &res.res_label;
            let ty = &res.res_detail;
            println!("{} {}", name, ty)
        }
    }
}
