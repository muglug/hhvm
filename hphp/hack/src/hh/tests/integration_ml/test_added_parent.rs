// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_added_parent.ml` (group B).

use crate::base as test;

const FOO_NAME: &str = "foo.php";

const FOO_CONTENTS: &str = "<?hh // strict

class Foo {
  /* HH_FIXME[4336] */
  public function f() : string {
  }
}
";

const FOO_CHILD_NAME: &str = "foo_child.php";

const FOO_CHILD_CONTENTS: &str = "<?hh // strict

/* HH_FIXME[2049] */
/* HH_FIXME[4123] */
class FooChild extends Foo {}
";

const BAR_NAME: &str = "bar.php";

const BAR_CONTENTS: &str = "<?hh // strict

function take_int(int $x) : void {}

function test(FooChild $foo_child) : void {
  /* HH_FIXME[4053] */
  take_int($foo_child->f());
}
";

const BAR_ERRORS: &str = "ERROR: File \"/bar.php\", line 7, characters 12-26:
Invalid argument (Typing[4110])
  File \"/bar.php\", line 3, characters 19-21:
  Expected `int`
  File \"/foo.php\", line 5, characters 25-30:
  But got `string`
";

const HHCONFIG_CONTENTS: &str = "
allowed_fixme_codes_strict = 2049,4053,4110,4123,4336
allowed_decl_fixme_codes = 2049,4123,4336
";

pub fn test() {
    let custom_config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(custom_config), &test::raw_hhi_contents(), None);
    let env = test::setup_disk(
        env,
        &[
            (FOO_NAME, ""),
            (FOO_CHILD_NAME, FOO_CHILD_CONTENTS),
            (BAR_NAME, BAR_CONTENTS),
        ],
    );
    // We need to suppress all the errors (see HH_FIXMEs above), otherwise the
    // logic that always rechecks the files with errors kicks in and does the
    // same job as phase2 fanout. We want to test the latter one in this test.
    test::assert_no_diagnostics(&env);

    // restore parent, but with a mismatching return type of f()
    let (env, _) = test::run_loop_once(env, test::loop_input(&[(FOO_NAME, FOO_CONTENTS)]));
    test::assert_single_diagnostic(BAR_ERRORS, &test::diagnostic_list(&env.diagnostics));
}
