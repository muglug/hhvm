// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_duplicated_file.ml` (group C).
//! Duplicate the same file twice

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh //strict
    class Foo {
        public function g(): int {
            return 1;
        }
    }
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    if !test::diagnostic_list(&env.diagnostics).is_empty() {
        test::fail("Expected no errors");
    }
    let (env, loop_output) = test::run_loop_once(
        env,
        test::loop_input(&[("foo.php", FOO_CONTENTS), ("bar.php", FOO_CONTENTS)]),
    );
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }

    let expected_result = concat!(
        "ERROR: File \"/foo.php\", line 2, characters 11-13:\n",
        "Name already bound: `Foo` (Naming[2012])\n",
        "  File \"/bar.php\", line 2, characters 11-13:\n",
        "  Previous definition is here\n",
    );
    test::assert_single_diagnostic(expected_result, &test::diagnostic_list(&env.diagnostics));
}
