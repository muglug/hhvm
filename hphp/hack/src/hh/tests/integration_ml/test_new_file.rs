// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_new_file.ml` (group A).

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh

function f(): int {
  return 3
}
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    let expected_errors = [concat!(
        "ERROR: File \"/foo.php\", line 4, characters 11-11:\n",
        "A semicolon `;` is expected here. (Parsing[1002])",
    )];
    let errs = test::diagnostic_list(&env.diagnostics);
    // `List.zip`
    if expected_errors.len() != errs.len() {
        test::fail("Expected 1 error.");
    }
    for (expected, err) in expected_errors.iter().zip(errs) {
        test::assert_single_diagnostic(expected, &[err]);
    }
}
