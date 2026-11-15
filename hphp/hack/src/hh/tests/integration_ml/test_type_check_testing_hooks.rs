// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The contract of `Server_env.type_check_testing_hooks` (`server_env.mli`),
//! which `test/fanout/scheduled/scheduled_fanout.ml` relies on: during one
//! recheck, `after_indexing` runs once after parsing, `after_file_redecl`
//! after each changed file is redeclared in-process, `before_file_checks`
//! at the entry of `Typing_check_service.go_with_interrupt` with the files
//! to check in order (early enough for `TestMocking.set_is_cancelled` to
//! apply to this check), and `after_file_check` after each file is checked,
//! in that order.

use std::sync::Arc;
use std::sync::Mutex;

use hh::relative_path;
use hh::server_env;
use hh::typing_check_service;

use crate::base as test;

const FOO_NAME: &str = "foo.php";

const FOO_CONTENTS_BEFORE: &str = "<?hh

class Foo {
  public function f(): void {}
}
";

const FOO_CONTENTS_AFTER: &str = "<?hh

class Foo {
  public function f(): int { return 1; }
}
";

const BAR_NAME: &str = "bar.php";

const BAR_CONTENTS: &str = "<?hh

function bar(Foo $foo): void {
  $foo->f();
}
";

const BAZ_NAME: &str = "baz.php";

const BAZ_CONTENTS: &str = "<?hh

function baz(Foo $foo): void {
  $foo->f();
}
";

pub fn test() {
    let env = test::setup_server(None, &[], None);
    let env = test::setup_disk(
        env,
        &[
            (FOO_NAME, FOO_CONTENTS_BEFORE),
            (BAR_NAME, BAR_CONTENTS),
            (BAZ_NAME, BAZ_CONTENTS),
        ],
    );
    test::assert_no_diagnostics(&env);

    let events: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(vec![]));
    let checked: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(vec![]));
    let record = |events: &Arc<Mutex<Vec<String>>>| {
        let events = Arc::clone(events);
        move |event: String| events.lock().unwrap().push(event)
    };
    let hooks = server_env::TypeCheckTestingHooks {
        after_indexing: {
            let record = record(&events);
            Box::new(move || record("after_indexing".to_string()))
        },
        before_redecl: {
            let record = record(&events);
            Box::new(move |defs_per_file| {
                let paths: Vec<String> = defs_per_file.keys().map(relative_path::suffix).collect();
                record(format!("before_redecl {}", paths.join(" ")))
            })
        },
        after_file_redecl: {
            let record = record(&events);
            Box::new(move |path| {
                record(format!("after_file_redecl {}", relative_path::suffix(path)))
            })
        },
        before_file_checks: {
            let record = record(&events);
            let checked = Arc::clone(&checked);
            Box::new(move |paths| {
                let paths: Vec<String> = paths.iter().map(relative_path::suffix).collect();
                record(format!("before_file_checks {}", paths.join(" ")));
                let mut checked = checked.lock().unwrap();
                if checked.is_empty() {
                    *checked = paths;
                    // Cancelled from the hook: taken out of this very check
                    // (once: the next recheck checks it).
                    typing_check_service::test_mocking::set_is_cancelled(relative_path::from_root(
                        BAZ_NAME,
                    ));
                }
            })
        },
        after_file_check: {
            let record = record(&events);
            Box::new(move |path| {
                record(format!("after_file_check {}", relative_path::suffix(path)))
            })
        },
    };
    let env = server_env::Env {
        type_check_testing_hooks: Some(Arc::new(hooks)),
        ..env
    };
    let (env, _) = test::run_loop_once(env, test::loop_input(&[(FOO_NAME, FOO_CONTENTS_AFTER)]));

    let checked = checked.lock().unwrap().clone();
    // The fanout of `Foo::f`: its file and the two that call it.
    for name in [FOO_NAME, BAR_NAME, BAZ_NAME] {
        assert!(
            checked.iter().any(|p| p == name),
            "{} is not checked: {:?}",
            name,
            checked
        );
    }
    let mut expected = vec![
        "after_indexing".to_string(),
        format!("before_redecl {}", FOO_NAME),
        format!("after_file_redecl {}", FOO_NAME),
        format!("before_file_checks {}", checked.join(" ")),
    ];
    expected.extend(
        checked
            .iter()
            .filter(|p| *p != BAZ_NAME)
            .map(|p| format!("after_file_check {}", p)),
    );
    let got = events.lock().unwrap().clone();
    assert_eq!(got, expected);
    // The file cancelled is kept for retry, and the next recheck checks it.
    test::assert_needs_recheck(&env, BAZ_NAME);
    events.lock().unwrap().clear();
    let (env, _) = test::run_loop_once(env, test::default_loop_input());
    let got = events.lock().unwrap().clone();
    assert_eq!(
        got,
        [
            "after_indexing".to_string(),
            "before_redecl ".to_string(),
            format!("before_file_checks {}", BAZ_NAME),
            format!("after_file_check {}", BAZ_NAME),
        ]
    );
    test::assert_no_diagnostics(&env);
    test::assert_needs_no_recheck(&env, BAZ_NAME);
}
