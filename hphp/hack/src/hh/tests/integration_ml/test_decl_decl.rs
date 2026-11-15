// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_decl_decl.ml` (group B).

use crate::base as test;

const A_FILE_NAME: &str = "A.php";

const B_FILE_NAME: &str = "B.php";

const C_FILE_NAME: &str = "C.php";

const A_CONTENTS: &str = "<?hh // strict

class A {
  /* HH_FIXME[4336] */
  /* HH_FIXME[4422] */
  final public function f() : C {
  }
}
";

const B_CONTENTS: &str = "<?hh // strict

class B extends A {}
";

const C_CONTENTS: &str = "<?hh // strict

class C {}
";

const ERRORS: &str = r#"
ERROR: File "/A.php", line 6, characters 31-31:
Unbound name: `C` (Naming[2049])
"#;

const HHCONFIG_CONTENTS: &str = "
allowed_fixme_codes_strict = 4336,4422
allowed_decl_fixme_codes = 4336,4422
";

pub fn test() {
    let custom_config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(custom_config), &[], None);
    let env = test::setup_disk(
        env,
        &[(A_FILE_NAME, A_CONTENTS), (B_FILE_NAME, B_CONTENTS), (C_FILE_NAME, "")],
    );
    test::assert_env_diagnostics(&env, ERRORS);

    let (env, _) = test::run_loop_once(env, test::loop_input(&[(C_FILE_NAME, C_CONTENTS)]));
    test::assert_no_diagnostics(&env);
}
