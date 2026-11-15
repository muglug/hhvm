// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_interrupt.ml` (group D).

use hh::naming_table;
use hh::provider_utils;
use hh::relative_path;
use hh::relative_path::Prefix;
use hh::typing_check_service;

use crate::base as test;

const FOO_NAME: &str = "foo.php";

fn bar_name(n: usize) -> String {
    format!("bar{}.php", n)
}

const FOO_CONTENTS: &str = "<?hh //strict
/* HH_FIXME[4336] */
function foo() : string {
}
";

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
    // There are errors in both bar files
    let (bar1, bar2) = (bar_name(1), bar_name(2));
    let (bar1_contents, bar2_contents) = (bar_contents(1), bar_contents(2));
    let env = test::setup_disk(
        env,
        &[(FOO_NAME, FOO_CONTENTS), (&bar1, &bar1_contents), (&bar2, &bar2_contents)],
    );
    // Prepare rechecking of all files
    let ctx = provider_utils::ctx_from_server_env(&env);
    let defs_per_file = naming_table::to_defs_per_file(&env.naming_table, None);
    // Pretend that this rechecking will be cancelled before we get to bar1
    let bar1_path = relative_path::create(Prefix::Root, &test::prepend_root(&bar_name(1)));
    typing_check_service::test_mocking::set_is_cancelled(bar1_path.clone());

    // Run the recheck
    let interrupt = typing_check_service::no_interrupt(());
    let fnl: Vec<relative_path::T> = defs_per_file.keys().cloned().collect();
    let check_info = typing_check_service::CheckInfo {
        // (`Typing_check_service.go_with_interrupt` is the daemon's:
        // `~drop_fixmed:false`.)
        keep_fixmed: true,
        check_reason: "test_interrupt".to_string(),
        log_errors: false,
        discard_warnings: false,
    };
    let (((), typing_check_service::Result { diagnostics, .. }), cancelled) =
        typing_check_service::go_with_interrupt(
            &ctx,
            hh::telemetry::create(),
            &fnl,
            interrupt,
            &check_info,
            None,
            None,
        );
    // Assert that we got the errors in bar2 only...
    test::assert_diagnostics(&diagnostics, EXPECTED_ERRORS);

    // ...while bar1 is among cancelled jobs
    match cancelled {
        Some((x, _)) if x.len() == 1 && x[0] == bar1_path => {}
        _ => panic!("assert false"),
    }
}
