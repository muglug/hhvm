// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_ignore_fixme_hhi.ml` (group A).

use crate::base as test;

const FILE_NAME: &str = "f.php";

const HHI_NAME: &str = "g.hhi";

const FILE_CONTENTS: &str = "<?hh // strict

function f(): float {
  /* HH_FIXME[4110] */
  return 4;
}
";

const HHI_CONTENTS: &str = "<?hh

/* HH_FIXME[4110] */
const float C = 4.0;
";

const HHCONFIG_CONTENTS: &str = "";

const ERRORS: &str = r#"
ERROR: File "/f.php", line 5, characters 10-10:
Invalid return type (Typing[4110])
  File "/f.php", line 3, characters 15-19:
  Expected `float`
  File "/f.php", line 5, characters 10-10:
  But got `int`

ERROR: File "/f.php", line 4, characters 3-22:
You cannot use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error 4110 (Typing[4110])
"#;

pub fn test() {
    let config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(config), &[(HHI_NAME, HHI_CONTENTS)], None);
    let env = test::setup_disk(env, &[(FILE_NAME, FILE_CONTENTS)]);
    test::assert_env_diagnostics(&env, ERRORS);
}
