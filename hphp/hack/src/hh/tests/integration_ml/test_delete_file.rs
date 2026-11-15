// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_delete_file.ml` (group A).

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh
    class Foo {
        public static function g(): int {
            return 1;
        }
    }
";

const BAR_CONTENTS: &str = "<?hh
        function h(): int {
            return Foo::g();
        }
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let (env, loop_output) = test::run_loop_once(
        env,
        test::loop_input(&[("foo.php", FOO_CONTENTS), ("bar.php", BAR_CONTENTS)]),
    );
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    if !test::diagnostic_list(&env.diagnostics).is_empty() {
        test::fail("Expected no errors");
    }
    let (env, loop_output) = test::run_loop_once(
        env,
        test::loop_input(&[("foo.php", ""), ("bar.php", BAR_CONTENTS)]),
    );
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    let expected_error = concat!(
        "ERROR: File \"/bar.php\", line 3, characters 20-22:\n",
        "Unbound name: `Foo` (an object type) (Naming[2049])\n",
    );
    test::assert_single_diagnostic(expected_error, &test::diagnostic_list(&env.diagnostics));
}
