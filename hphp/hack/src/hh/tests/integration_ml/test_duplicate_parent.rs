// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_duplicate_parent.ml` (group C).

use crate::base as test;

const FOO_CONTENTS: &str = "<?hh
    class Foo {
        public static ?int $x;
    }
";

const QUX_CONTENTS: &str = "<?hh
function h(): int {
    return 1;
}

class Foo {}

function setUpClass(): void {
    new Foo();
    h();
}
";

const BAR_CONTENTS: &str = "<?hh
      class Bar extends Foo {}

      function main(Bar $a): void {
          $a::$y;
      }
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let (env, loop_output) = test::run_loop_once(
        env,
        test::loop_input(&[
            ("foo.php", FOO_CONTENTS),
            ("qux.php", QUX_CONTENTS),
            ("bar.php", BAR_CONTENTS),
        ]),
    );
    if !loop_output.did_read_disk_changes {
        test::fail("Expected the server to process disk updates");
    }
    let bar_error = concat!(
        "ERROR: File \"/bar.php\", line 5, characters 15-16:\n",
        "No class variable `$y` in `Bar` (Typing[4090])\n",
        "  File \"/foo.php\", line 3, characters 23-26:\n",
        "  Did you mean `$x` instead?\n",
        "  File \"/bar.php\", line 2, characters 13-15:\n",
        "  Declaration of `Bar` is here\n",
    );
    let qux_error = concat!(
        "ERROR: File \"/qux.php\", line 6, characters 7-9:\n",
        "Name already bound: `Foo` (Naming[2012])\n",
        "  File \"/foo.php\", line 2, characters 11-13:\n",
        "  Previous definition is here\n",
    );
    // We should get exactly these two errors
    match test::diagnostic_list(&env.diagnostics).as_slice() {
        [x, y] => {
            test::assert_single_diagnostic(qux_error, std::slice::from_ref(y));
            test::assert_single_diagnostic(bar_error, std::slice::from_ref(x));
        }
        errs => test::fail(&format!(
            "Expected exactly two errors, but got:\n{}",
            test::diagnostic_strings(errs).join("\n")
        )),
    }
}
