// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_unbound_name_2.ml` (group A).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const A_CONTENTS: &str = "<?hh // strict

type my_shape = shape(
  'outer' => shape(
    B::KEY => string
  ),
);
";

const B_CONTENTS: &str = "<?hh // strict
class B {
  <<__ShapeKey>>
  const string KEY = \"KEY\";
}
";

const ERRORS: &str = r#"
ERROR: File "/A.php", line 5, characters 5-5:
Unbound name: `B` (an object type) (Naming[2049])
"#;

pub fn test() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let env = test::setup_disk(env, &[(A_FILE_NAME, A_CONTENTS), (B_FILE_NAME, "")]);
    test::assert_env_diagnostics(&env, ERRORS);

    let (env, _) = test::run_loop_once(env, test::loop_input(&[(B_FILE_NAME, B_CONTENTS)]));
    test::assert_no_diagnostics(&env);
}
