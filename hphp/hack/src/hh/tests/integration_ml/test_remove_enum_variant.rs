// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_remove_enum_variant.ml` (group B).
//! (The `.hhconfig` key `new_exhaustivity_check` no longer exists: it is
//! ignored by both implementations; R1 checked on the oracle that 4019 is
//! reported anyway.)

use crate::base as test;

const HHCONFIG_CONTENTS: &str = "
new_exhaustivity_check = true
";

const E_CONTENTS: &str = "<?hh

enum E: int {
  A = 1;
  B = 2;
}
";

const E_CHANGES: &str = "<?hh

enum E: int {
  A = 1;
}
";

const F_CONTENTS: &str = "<?hh

function f(E $e): int {
  switch ($e) {
    case E::A:
      return 4;
  }
  return 42;
}
";

const F_ERRORS: &str = "ERROR: File \"/f.php\", line 4, characters 3-50:
This `switch` statement is nonexhaustive. At least the following cases are missing: `E::B` (Typing[4019])
  File \"/f.php\", line 4, characters 11-12:
  The scrutinee has type `E`.
";

pub fn test() {
    let custom_config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(custom_config), &[], None);
    let env = test::setup_disk(env, &[("e.php", E_CONTENTS), ("f.php", F_CONTENTS)]);
    test::assert_single_diagnostic(F_ERRORS, &test::diagnostic_list(&env.diagnostics));

    let (env, _) = test::run_loop_once(env, test::loop_input(&[("e.php", E_CHANGES)]));
    test::assert_no_diagnostics(&env);
}
