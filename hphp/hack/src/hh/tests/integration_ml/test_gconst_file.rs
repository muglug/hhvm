// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_gconst_file.ml` (group A).

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh // strict
  const int A = 5;
";

const BAR_CONTENTS: &str = "<?hh // strict
  const int B = A;
";

const FOO_NEW_CONTENTS: &str = "<?hh // strict
  const string A = '';
";

pub fn test() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    test::assert_no_diagnostics(&env);

    let (env, loop_output) = test::run_loop_once(env, test::loop_input(&[("bar.php", BAR_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    test::assert_no_diagnostics(&env);

    let (env, loop_output) =
        test::run_loop_once(env, test::loop_input(&[("foo.php", FOO_NEW_CONTENTS)]));
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }

    let expected_error = concat!(
        "ERROR: File \"/bar.php\", line 2, characters 9-11:\n",
        "Wrong type hint (Typing[4110])\n",
        "  File \"/bar.php\", line 2, characters 9-11:\n",
        "  Expected `int`\n",
        "  File \"/foo.php\", line 2, characters 9-14:\n",
        "  But got `string`",
    );
    test::assert_single_diagnostic(expected_error, &test::diagnostic_list(&env.diagnostics));
}
