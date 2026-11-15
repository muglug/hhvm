// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The server side of `test/integration/test_validate_isolation.py`
//! (`hh --validate-isolation`), in process: the cases of that test, asked of
//! `Server_isolation_validate.go` directly rather than through the client.

use hh::relative_path;
use hh::server_command_types::isolation_validation;
use hh::server_env::Env;
use hh::server_env::Genv;
use hh::server_env_build;
use hh::server_isolation_validate;

use crate::base as test;

/// A server started with `--config isolation_allow_decl_repackaging=<allow>`.
fn genv(allow: bool) -> Genv {
    let default = server_env_build::default_genv();
    Genv {
        config: test::server_config(),
        local_config: hh::server_local_config::T {
            isolation_allow_decl_repackaging: allow,
            ..default.local_config
        },
        ..default
    }
}

fn validate(genv: &Genv, env: &Env, candidate: &[&str]) -> isolation_validation::Result {
    let files: Vec<_> = candidate.iter().map(|f| relative_path::from_root(f)).collect();
    server_isolation_validate::go(genv, env, &files)
}

fn referrers(result: &isolation_validation::Result) -> Vec<&str> {
    result.violations.iter().map(|v| v.referrer.as_str()).collect()
}

pub fn test_validate_isolation() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let env = test::setup_disk(
        env,
        &[
            ("validate_helper.php", "<?hh\nfunction validate_helper(): void {}\n"),
            (
                "validate_user.php",
                "<?hh\nfunction validate_user(): void {\n  validate_helper();\n}\n",
            ),
            (
                "validate_overridden.php",
                "<?hh\n<<file: __PackageOverride(\"foo\")>>\nfunction validate_overridden(): void {}\n",
            ),
        ],
    );
    let genv = genv(true);

    // The candidate leaves out its only referrer, so the call into it is a
    // violation.
    let result = validate(&genv, &env, &["validate_helper.php"]);
    assert_eq!(result.refused, None);
    assert_eq!(result.files_checked, 2, "{:?}", result);
    assert!(!result.isolatable);
    assert!(result.unknown_files.is_empty());
    assert_eq!(referrers(&result), vec!["validate_user.php"], "{:?}", result);
    assert_eq!(result.violations[0].line, 3);
    assert!(
        !result.violations[0].message.contains("hh_isolation_candidate"),
        "{:?}",
        result
    );

    // The same two files, with the referrer now inside the candidate.
    let result = validate(&genv, &env, &["validate_helper.php", "validate_user.php"]);
    assert!(result.isolatable, "{:?}", result);
    assert!(result.violations.is_empty());

    // A path the naming table never saw.
    let result = validate(&genv, &env, &["validate_nonexistent.php"]);
    assert_eq!(result.unknown_files, vec!["validate_nonexistent.php"]);
    assert!(result.violations.is_empty());
    assert!(!result.isolatable);

    // A file that names its own package.
    let result = validate(&genv, &env, &["validate_overridden.php"]);
    assert_eq!(result.overridden_files, vec!["validate_overridden.php"]);
    assert!(result.unknown_files.is_empty());
    assert!(result.violations.is_empty());
    assert!(!result.isolatable);

    // The first answer again: nothing of the runs in between is left.
    let again = validate(&genv, &env, &["validate_helper.php"]);
    assert_eq!(referrers(&again), vec!["validate_user.php"]);
}

pub fn test_validate_isolation_leaves_the_server_alone() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let env = test::setup_disk(
        env,
        &[
            ("leftover_helper.php", "<?hh\nfunction leftover_helper(): void {}\n"),
            (
                "leftover_user.php",
                "<?hh\nfunction leftover_user(): void {\n  leftover_helper();\n}\n",
            ),
        ],
    );
    let genv = genv(true);
    // Giving the helper a parameter makes the call in leftover_user.php
    // wrong, in a way only its decl can reveal.
    let errors_from_a_recheck = |env: Env| -> (Env, Vec<String>) {
        let (env, _) = test::change_files(
            env,
            &[("leftover_helper.php", "<?hh\nfunction leftover_helper(int $_): void {}\n")],
        );
        let errors = test::diagnostic_strings(&test::diagnostic_list(&env.diagnostics));
        let (env, _) = test::change_files(
            env,
            &[("leftover_helper.php", "<?hh\nfunction leftover_helper(): void {}\n")],
        );
        test::assert_no_diagnostics(&env);
        (env, errors)
    };
    let (env, before) = errors_from_a_recheck(env);
    let first = validate(&genv, &env, &["leftover_helper.php"]);
    let (env, after) = errors_from_a_recheck(env);
    assert!(before.iter().any(|e| e.contains("leftover_user.php")), "{:?}", before);
    assert_eq!(before, after);
    // A decl rebuilt under the synthesized package and left behind would make
    // the second run disagree with the first.
    assert_eq!(first, validate(&genv, &env, &["leftover_helper.php"]));
    assert!(!first.isolatable);
}

pub fn test_validate_isolation_refuses_without_the_config() {
    let env = test::setup_server(None, &test::raw_hhi_contents(), None);
    let env = test::setup_disk(env, &[("gated.php", "<?hh\nfunction gated(): void {}\n")]);
    let result = validate(&genv(false), &env, &["gated.php"]);
    let refused = result.refused.as_deref().unwrap();
    assert!(refused.contains("isolation_allow_decl_repackaging"));
    assert!(refused.contains("Do this on a server nothing else uses"));
    assert!(!result.isolatable);
    assert_eq!(result.files_checked, 0);
    test::assert_no_diagnostics(&env);
}
