// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/test_lazy_decl_idempotence.ml` (group B).
//!
//! `Decl_class_elements.get_for_classes ~old:false classes` is not
//! computed: R1's `remove_defs` takes no `~elems` (always empty with the
//! member heaps of `Shared_memory`, see R1's note).

use hh::decl_redecl_service;
use hh::file_info;
use hh::provider_utils;
use hh::relative_path;
use hh::typing_check_service;

use crate::base as test;

const FOO_NAME: &str = "\\Foo";

const BAR_NAME: &str = "\\Bar";

const FOO_FILE_NAME: &str = "foo.php";

const BAR_FILE_NAME: &str = "bar.php";

const FOO_CONTENTS: &str = r#"<?hh //strict

const string GLOBAL_X = "X";

class Foo {
  // this is an error (lack of typehint) revealed during declaration only
  const X = GLOBAL_X;
}
"#;

const BAR_CONTENTS: &str = r#"<?hh //strict
class Bar {
  public function test(Foo $x) : void {}
}
"#;

const EXPECTED_ERRORS: &str = r#"
ERROR: File "/foo.php", line 7, characters 9-9:
Please add a type hint (Naming[2035])
"#;

pub fn test() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let env = test::setup_disk(env, &[(FOO_FILE_NAME, FOO_CONTENTS), (BAR_FILE_NAME, BAR_CONTENTS)]);
    let ctx = provider_utils::ctx_from_server_env(&env);
    let classes = [FOO_NAME, BAR_NAME];
    let foo_path = relative_path::from_root(FOO_FILE_NAME);
    let bar_path = relative_path::from_root(BAR_FILE_NAME);
    // Remove things from shared memory (that were put there by Test.setup_disk)
    // to simulate lazy saved state init.
    let defs = file_info::Names {
        funs: Default::default(),
        classes: classes.iter().map(|s| s.to_string()).collect(),
        types: Default::default(),
        consts: Default::default(),
        modules: Default::default(),
    };
    decl_redecl_service::remove_defs(&defs, &ctx, false);
    hh::rt::decl_epoch::invalidate_local_caches();

    // Local caches need to be invalidated whenever things are removed from shared
    // memory (to avoid getting cached old versions of declarations)
    let check_info = typing_check_service::CheckInfo {
        // (`Typing_check_service.go` is the daemon's: `~drop_fixmed:false`.)
        keep_fixmed: true,
        check_reason: "test".to_string(),
        log_errors: false,
        discard_warnings: false,
    };
    let typing_check_service::Result { diagnostics, .. } =
        typing_check_service::go(&ctx, hh::telemetry::create(), &[bar_path.clone()], &check_info, None);
    test::assert_diagnostics(&diagnostics, "");
    let typing_check_service::Result { diagnostics, .. } =
        typing_check_service::go(&ctx, hh::telemetry::create(), &[bar_path], &check_info, None);
    test::assert_diagnostics(&diagnostics, "");

    let typing_check_service::Result { diagnostics, .. } =
        typing_check_service::go(&ctx, hh::telemetry::create(), &[foo_path.clone()], &check_info, None);
    test::assert_diagnostics(&diagnostics, EXPECTED_ERRORS);
    let typing_check_service::Result { diagnostics, .. } =
        typing_check_service::go(&ctx, hh::telemetry::create(), &[foo_path], &check_info, None);
    test::assert_diagnostics(&diagnostics, EXPECTED_ERRORS);

    let _ = env;
}
