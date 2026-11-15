// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_remove_method.ml` (group B).

use crate::base as test;

const FOO_NAME: &str = "foo.php";

const FOO_CONTENTS_BEFORE: &str = "<?hh // strict

class Foo {
  public function f() : void {}
}
";

const FOO_CONTENTS_AFTER: &str = "<?hh // strict

class Foo {}
";

const FOO_CHILD_NAME: &str = "foo_child.php";

const FOO_CHILD_CONTENTS: &str = "<?hh // strict

class FooChild extends Foo {}
";

const BAR_NAME: &str = "bar.php";

const BAR_CONTENTS: &str = "<?hh // strict

function test(FooChild $foo_child) : void {
  $foo_child->f();
}
";

const BAR_ERRORS: &str = "ERROR: File \"/bar.php\", line 4, characters 15-15:
No instance method `f` in `FooChild` (Typing[4053])
  File \"/bar.php\", line 3, characters 15-22:
  This is why I think it is an object of type FooChild
  File \"/foo_child.php\", line 3, characters 7-14:
  Declaration of `FooChild` is here
";

const HHCONFIG_CONTENTS: &str = "";

pub fn test() {
    let custom_config = test::load_config_with_hhconfig(HHCONFIG_CONTENTS);
    let env = test::setup_server(Some(custom_config), &[], None);
    let env = test::setup_disk(
        env,
        &[
            (FOO_NAME, FOO_CONTENTS_BEFORE),
            (FOO_CHILD_NAME, FOO_CHILD_CONTENTS),
            (BAR_NAME, BAR_CONTENTS),
        ],
    );
    // We need to suppress all the errors (see HH_FIXMEs above), otherwise the
    // logic that always rechecks the files with errors kicks in and does the
    // same job as phase2 fanout. We want to test the latter one in this test.
    test::assert_no_diagnostics(&env);

    // restore parent, but with a mismatching return type of f()
    let (env, _) = test::run_loop_once(env, test::loop_input(&[(FOO_NAME, FOO_CONTENTS_AFTER)]));
    test::assert_single_diagnostic(BAR_ERRORS, &test::diagnostic_list(&env.diagnostics));
}
