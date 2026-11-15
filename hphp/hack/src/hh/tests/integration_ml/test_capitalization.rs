// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_capitalization.ml` (group C).

use crate::base as test;

const FOO1_CONTENTS: &str = "<?hh
  class foo {}
";

const FOO2_CONTENTS: &str = "<?hh
  class FOO {}
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let (env, loop_output) = test::run_loop_once(
        env,
        test::loop_input(&[("foo1.php", FOO1_CONTENTS), ("foo2.php", FOO2_CONTENTS)]),
    );
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }

    // TODO: get rid of repeating errors in error list
    let expected_error = concat!(
        "ERROR: File \"/foo2.php\", line 2, characters 9-11:\n",
        "Name already bound: `FOO` (Naming[2012])\n",
        "  File \"/foo1.php\", line 2, characters 9-11:\n",
        "  Previous definition is here\n",
    );
    test::assert_env_diagnostics(&env, expected_error);

    // Change a wholly unrelated file.
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("bar.php", "")]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }

    // The same errors should still be there
    test::assert_env_diagnostics(&env, expected_error);
}
