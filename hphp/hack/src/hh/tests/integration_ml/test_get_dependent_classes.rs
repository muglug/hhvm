// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_get_dependent_classes.ml` (group B).

use hh::decl_redecl_service;
use hh::naming_table;
use hh::provider_utils;
use hh::relative_path::RelativePath;
use hh::s_set;

use crate::base as test;

fn files() -> Vec<(String, String)> {
    [
        ("C", "class C {}"),
        ("D", "class D extends C {}"),
        ("E", "class E extends D {}"),
        ("F", "trait F { require extends E; }"),
        ("G", "trait G { use F; }"),
        ("H", "trait H {}"),
        ("I", "class I { use H; }"),
        ("J", "interface J {}"),
        ("K", "interface K extends J {}"),
        ("L", "trait L { require implements K; }"),
        ("M", "class :M {}"),
        ("N", "class :N { attribute :M; }"),
        ("Unrelated", "class Unrelated {}"),
    ]
    .iter()
    .map(|(name, contents)| (format!("{}.php", name), format!("<?hh\n{}", contents)))
    .collect()
}

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let files = files();
    let files: Vec<(&str, &str)> = files.iter().map(|(n, c)| (n.as_str(), c.as_str())).collect();
    let env = test::setup_disk(env, &files);
    test::assert_no_diagnostics(&env);
    let ctx = provider_utils::ctx_from_server_env(&env);

    let get_classes = |path: &RelativePath| -> s_set::T {
        match naming_table::get_file_info(&env.naming_table, path) {
            None => s_set::T::new(),
            Some(info) => info.ids.classes.iter().map(|id| id.name.clone()).collect(),
        }
    };
    let dependent_classes = decl_redecl_service::get_descendant_classes(
        &ctx,
        1,
        &get_classes,
        &["\\C", "\\H", "\\J", "\\:M"].iter().map(|s| s.to_string()).collect(),
    );
    let mut expected_dependent_classes: Vec<String> = [
        "\\C", "\\D", "\\E", "\\F", "\\G", "\\H", "\\I", "\\J", "\\K", "\\L", "\\:M", "\\:N",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    // `List.sort ~compare:String.compare` (byte order, as `S_set.elements`)
    expected_dependent_classes.sort();
    let elements: Vec<String> = dependent_classes.into_iter().collect();
    for c in &elements {
        println!("{}", c);
    }

    if elements != expected_dependent_classes {
        test::fail("Missing dependent classes");
    }
}
