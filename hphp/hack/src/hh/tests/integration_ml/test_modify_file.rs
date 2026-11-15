// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_modify_file.ml` (group A).

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh
        function g(): string {
            return 'a';
        }
";

const FOO_CHANGES: &str = "<?hh
        function g(): int {
            return 'a';
        }
";

pub fn test() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    if !test::diagnostic_list(&env.diagnostics).is_empty() {
        test::fail("Expected no errors");
    }
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_CHANGES)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }

    let expected_error = concat!(
        "ERROR: File \"/foo.php\", line 3, characters 20-22:\n",
        "Invalid return type (Typing[4110])\n",
        "  File \"/foo.php\", line 2, characters 23-25:\n",
        "  Expected `int`\n",
        "  File \"/foo.php\", line 3, characters 20-22:\n",
        "  But got `string`\n",
    );
    test::assert_single_diagnostic(expected_error, &test::diagnostic_list(&env.diagnostics));
}
