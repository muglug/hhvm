// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_property_initializer2.ml` (group A).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const C_FILE_NAME: &str = "C.php";

const A_CONTENTS: &str = "<?hh // strict

abstract class A {
  public X $x;
}
";

const B_CONTENTS: &str = "<?hh // strict

type X = int;
";

const B_CONTENTS_AFTER: &str = "<?hh // strict

type X = ?int;
";

const C_CONTENTS: &str = "<?hh // strict

class C extends A {}
";

const ERRORS: &str = r#"
ERROR: File "/C.php", line 3, characters 7-7:
Class `C` has properties that cannot be null and aren't always set in `__construct`. (NastCheck[3015])
  File "/A.php", line 4, characters 12-13:
  `$this->x` is not initialized.
"#;

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let env = test::setup_disk(
        env,
        &[
            (A_FILE_NAME, A_CONTENTS),
            (B_FILE_NAME, B_CONTENTS),
            (C_FILE_NAME, C_CONTENTS),
        ],
    );
    test::assert_env_diagnostics(&env, ERRORS);

    let (env, _) = test::change_files(env, &[(B_FILE_NAME, B_CONTENTS_AFTER)]);
    test::assert_no_diagnostics(&env);
}
