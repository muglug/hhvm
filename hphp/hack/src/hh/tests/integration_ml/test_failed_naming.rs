// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_failed_naming.ml` (group C).

use crate::base as test;

const F1: &str = "f1.php";

const F2: &str = "f2.php";

const TEST: &str = "test.php";

const TEST_CONTENTS: &str = "<?hh // strict

function test(C $c) : void {}
";

fn contents(s: &str) -> String {
    format!(
        "<?hh // strict

class {} {{}}
",
        s
    )
}

const ERRORS: &str = "
ERROR: File \"/test.php\", line 3, characters 15-15:
Unbound name: `C` (Naming[2049])
";

pub fn test() {
    let c_contents = contents("C");
    let d_contents = contents("D");
    let env = test::setup_server(None, &[], None);
    let env = test::setup_disk(
        env,
        &[(TEST, TEST_CONTENTS), (F1, &c_contents), (F2, &d_contents)],
    );
    test::assert_no_diagnostics(&env);

    // Rename C to (duplicate of) D
    let (env, _) = test::run_loop_once(env, test::loop_input(&[(F1, &d_contents)]));
    // Remove the duplicate
    let (env, _) = test::run_loop_once(env, test::loop_input(&[(F1, "")]));
    test::assert_env_diagnostics(&env, ERRORS);
}
