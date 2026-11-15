// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_unbound_name.ml` (group A).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const A_CONTENTS: &str = "<?hh // strict

final class A {
  const mixed C = dict[
    'k' => B::class,
  ];
}
";

const B_CONTENTS: &str = "<?hh // strict

class B {}
";

const ERRORS: &str = r#"
ERROR: File "/A.php", line 5, characters 12-12:
Unbound name: `B` (an object type) (Naming[2049])
"#;

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let env = test::setup_disk(env, &[(A_FILE_NAME, A_CONTENTS), (B_FILE_NAME, "")]);
    test::assert_env_diagnostics(&env, ERRORS);

    let (env, _) = test::run_loop_once(env, test::loop_input(&[(B_FILE_NAME, B_CONTENTS)]));
    test::assert_no_diagnostics(&env);
}
