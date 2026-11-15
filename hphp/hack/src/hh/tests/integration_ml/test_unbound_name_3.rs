// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_unbound_name_3.ml` (group A).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const C_FILE_NAME: &str = "C.php";

const A_CONTENTS: &str = "<?hh
  new module foo {}
";

const B_CONTENTS: &str = "<?hh
new module foo {}
";

const C_CONTENTS: &str = "<?hh
module foo;
class Foo {}
";

const ERRORS: &str = r#"
ERROR: File "/B.php", line 2, characters 12-14:
Name already bound: `foo` (Naming[2012])
  File "/A.php", line 2, characters 14-16:
  Previous definition is here
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

    let (env, _) = test::run_loop_once(env, test::loop_input(&[(B_FILE_NAME, "")]));
    test::assert_no_diagnostics(&env);
}
