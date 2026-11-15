// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_interrupt2.ml` (group D).

use hh::relative_path;
use hh::relative_path::Prefix;
use hh::server_main;
use hh::typing_check_service;

use crate::base as test;

const FOO_NAME: &str = "foo.php";

fn bar_name(n: usize) -> String {
    format!("bar{}.php", n)
}

fn foo_contents(ty: &str) -> String {
    format!(
        "<?hh //strict
/* HH_FIXME[4336] */
function foo() : {} {{
}}
",
        ty
    )
}

fn bar_contents(n: usize) -> String {
    format!(
        "<?hh //strict

function bar{}() : int {{
  return foo();
}}
",
        n
    )
}

const EXPECTED_ERRORS: &str = r#"
ERROR: File "/bar1.php", line 4, characters 10-14:
Invalid return type (Typing[4110])
  File "/bar1.php", line 3, characters 19-21:
  Expected `int`
  File "/foo.php", line 3, characters 18-23:
  But got `string`

ERROR: File "/bar2.php", line 4, characters 10-14:
Invalid return type (Typing[4110])
  File "/bar2.php", line 3, characters 19-21:
  Expected `int`
  File "/foo.php", line 3, characters 18-23:
  But got `string`
"#;

const HHCONFIG_CONTENTS: &str = "
allowed_fixme_codes_strict = 4336
allowed_decl_fixme_codes = 4336
";

pub fn test() {
    let custom_config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(custom_config), &test::raw_hhi_contents(), None);
    server_main::force_break_recheck_loop_for_test(false);

    // There are initially no errors
    let (bar1, bar2) = (bar_name(1), bar_name(2));
    let (bar1_contents, bar2_contents) = (bar_contents(1), bar_contents(2));
    let foo_int = foo_contents("int");
    let env = test::setup_disk(
        env,
        &[(FOO_NAME, &foo_int), (&bar1, &bar1_contents), (&bar2, &bar2_contents)],
    );
    test::assert_no_diagnostics(&env);

    // This change will recheck all files and reveal errors in bar1 and bar2
    let foo_string = foo_contents("string");
    let loop_input = test::loop_input(&[(FOO_NAME, &foo_string)]);
    // ... but we'll pretend that this recheck will be cancelled before getting
    // to bar1
    let bar1_path = relative_path::create(Prefix::Root, &test::prepend_root(&bar_name(1)));
    typing_check_service::test_mocking::set_is_cancelled(bar1_path);

    let (env, _) = test::run_loop_once(env, loop_input);
    // We'll get all the errors anyway due to server looping until check is
    // fully finished
    test::assert_env_diagnostics(&env, EXPECTED_ERRORS);
}
