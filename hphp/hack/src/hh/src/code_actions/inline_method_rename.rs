// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/refactors/inline_method/inline_method_rename.ml`.
//! See `hh/PORTING.md`.
//!
//! Enables creating fresh variables that resemble existing variables,
//! for use in generated code in the refactor.
//!
//! Given `used_vars` containing "$a" and "$b",
//! `rename_all ["$b"; "$c"]` is `["$b_"; "$c"]`
//!
//! (The OCaml functions return the new `t`: here it is changed in place.)

use std::collections::BTreeMap;
use std::collections::BTreeSet;

pub struct T {
    used_vars: BTreeSet<String>,
    old_to_new: BTreeMap<String, String>,
}

pub fn create(used_vars: BTreeSet<String>) -> T {
    T {
        used_vars,
        old_to_new: BTreeMap::new(),
    }
}

/// idempotent, generates a fresh name not in `used_vars`
pub fn rename(t: &mut T, old_var: &str) -> String {
    let next_var = |used_vars: &BTreeSet<String>, s: &str| -> String {
        let mut s = s.to_string();
        while used_vars.contains(&s) {
            s.push('_')
        }
        s
    };
    match t.old_to_new.get(old_var) {
        Some(new_var) => new_var.clone(),
        None => {
            let new_var = next_var(&t.used_vars, old_var);
            t.used_vars.insert(new_var.clone());
            t.old_to_new.insert(old_var.to_string(), new_var.clone());
            new_var
        }
    }
}

/// idempotent, preserves order
///
/// (`List.fold_right`: the variables are renamed from the last to the
/// first.)
pub fn rename_all(t: &mut T, old_vars: &[String]) -> Vec<String> {
    let mut new_vars: Vec<String> = old_vars.iter().rev().map(|old_var| rename(t, old_var)).collect();
    new_vars.reverse();
    new_vars
}
