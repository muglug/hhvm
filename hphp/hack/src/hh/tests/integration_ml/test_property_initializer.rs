// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_property_initializer.ml` (group A).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const A_CONTENTS: &str = "<?hh // strict

abstract class A {
  protected ?int $x;
}
";

const A_CONTENTS_REQUIRE_INIT: &str = "<?hh // strict

abstract class A {
  protected int $x;
}
";

const B_CONTENTS: &str = "<?hh // strict

class B extends A {}
";

const ERRORS: &str = r#"
ERROR: File "/B.php", line 3, characters 7-7:
Class `B` has properties that cannot be null and aren't always set in `__construct`. (NastCheck[3015])
  File "/A.php", line 4, characters 17-18:
  `$this->x` is not initialized.
"#;

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let env = test::setup_disk(env, &[(A_FILE_NAME, A_CONTENTS), (B_FILE_NAME, B_CONTENTS)]);
    test::assert_no_diagnostics(&env);

    let (env, _) = test::change_files(env, &[(A_FILE_NAME, A_CONTENTS_REQUIRE_INIT)]);
    test::assert_env_diagnostics(&env, ERRORS);
}
