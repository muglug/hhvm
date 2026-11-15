// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The `integration_ml` tests of `hphp/hack/test/integration_ml`, ported
//! (plan §4.2). One binary (`harness = false`): without `--run` it runs
//! itself once per test (`main --run <test>`), because a process can only
//! initialise one server (process globals: the dep graph, the path
//! prefixes, `decl_store`), as in the OCaml (`did_init`).
//!
//! Owned by **T1** (plan §3.1).
//!
//! ```text
//! cargo +nightly test --release -p hh --features server --test integration_ml -- [FILTER...]
//! ```
//! A filter selects the tests whose name contains it (`A/` = group A,
//! `B/remove_method`, ...). Each test gets a fresh directory (its root,
//! hhi and tmp directories, see `base.rs`), removed afterwards unless
//! `HH_INTEGRATION_ML_KEEP=1`. A test that runs longer than
//! `HH_INTEGRATION_ML_TIMEOUT` seconds (default 300) is killed. The
//! environment is passed on, so `RAYON_NUM_THREADS=1`/`8` and
//! `HH_FORGET_EVERY_FILE=1` apply to the tests.
//!
//! A test marked "expected to fail: <owner>" is one whose feature is not
//! ported yet: it is run and reported, but its failure does not fail the
//! run (and if it passes, the runner says the mark can go). Never delete
//! or weaken a test: mark it.

use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;
use std::time::Instant;

// (The ported harness has helpers that no test in scope uses yet.)
#[allow(dead_code)]
mod base;
mod module_fanout_after_interrupt_tests;
mod server_interrupt_test_harness;
mod test_added_parent;
mod test_capitalization;
mod test_decl_decl;
mod test_delete_file;
mod test_duplicate_parent;
mod test_duplicated_file;
mod test_failed_naming;
mod test_gconst_file;
mod test_get_dependent_classes;
mod test_ignore_fixme_hhi;
mod test_interrupt;
mod test_interrupt2;
mod test_lazy_decl_idempotence;
mod test_modify_file;
mod test_new_file;
mod test_property_initializer;
mod test_property_initializer2;
mod test_remove_enum_variant;
mod test_remove_method;
mod test_type_check_testing_hooks;
mod test_unbound_name;
mod test_unbound_name_2;
mod test_unbound_name_3;
mod test_validate_isolation;

struct Test {
    /// `<group>/<name of the OCaml runner>`
    name: &'static str,
    run: fn(),
    /// "expected to fail: <owner>": the feature is not ported yet.
    expected_to_fail: Option<&'static str>,
}

const fn t(name: &'static str, run: fn(), expected_to_fail: Option<&'static str>) -> Test {
    Test {
        name,
        run,
        expected_to_fail,
    }
}

/// The tests of plan §4.2, by group, in the plan's order.
const TESTS: &[Test] = &[
    // A: basic recheck (S1)
    t("A/modify_file", test_modify_file::test, None),
    t("A/new_file", test_new_file::test, None),
    t("A/delete_file", test_delete_file::test, None),
    t("A/gconst_file", test_gconst_file::test, None),
    t("A/unbound_name", test_unbound_name::test, None),
    t("A/unbound_name_2", test_unbound_name_2::test, None),
    t("A/unbound_name_3", test_unbound_name_3::test, None),
    t("A/property_initializer", test_property_initializer::test, None),
    t("A/property_initializer2", test_property_initializer2::test, None),
    t("A/ignore_fixme_hhi", test_ignore_fixme_hhi::test, None),
    // B: decl change -> fanout (R1 fanout, S1 wiring)
    t("B/added_parent", test_added_parent::test, None),
    t("B/remove_method", test_remove_method::test, None),
    t("B/remove_enum_variant", test_remove_enum_variant::test, None),
    t("B/decl_decl", test_decl_decl::test, None),
    t("B/get_dependent_classes", test_get_dependent_classes::test, None),
    t("B/lazy_decl_idempotence", test_lazy_decl_idempotence::test, None),
    // C: naming (N1)
    t("C/failed_naming", test_failed_naming::test, None),
    t("C/duplicated_file", test_duplicated_file::test, None),
    t("C/duplicate_parent", test_duplicate_parent::test, None),
    t("C/capitalization", test_capitalization::test, None),
    // D: interrupts (TCS cancellation, SRV handlers)
    t("D/interrupt", test_interrupt::test, None),
    t("D/interrupt2", test_interrupt2::test, None),
    t("D/type_check_testing_hooks", test_type_check_testing_hooks::test, None),
    t(
        "D/module_fanout_after_interrupt/test_files_to_recheck_uses_latest_section",
        module_fanout_after_interrupt_tests::test_files_to_recheck_uses_latest_section,
        None,
    ),
    t(
        "D/module_fanout_after_interrupt/test_nine_changed_files",
        module_fanout_after_interrupt_tests::test_nine_changed_files,
        None,
    ),
    t(
        "D/module_fanout_after_interrupt/test_ten_changed_files",
        module_fanout_after_interrupt_tests::test_ten_changed_files,
        None,
    ),
    // E: `hh --validate-isolation` (`test/integration/test_validate_isolation.py`)
    t("E/validate_isolation", test_validate_isolation::test_validate_isolation, None),
    t(
        "E/validate_isolation_leaves_the_server_alone",
        test_validate_isolation::test_validate_isolation_leaves_the_server_alone,
        None,
    ),
    t(
        "E/validate_isolation_refuses_without_the_config",
        test_validate_isolation::test_validate_isolation_refuses_without_the_config,
        None,
    ),
];

/// Waits for `child`, killing it after `timeout`.
fn wait_with_timeout(
    child: &mut std::process::Child,
    timeout: Duration,
) -> Option<std::process::ExitStatus> {
    let start = Instant::now();
    loop {
        match child.try_wait().expect("integration_ml: wait") {
            Some(status) => return Some(status),
            None if start.elapsed() > timeout => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
            None => std::thread::sleep(Duration::from_millis(20)),
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if let [_, flag, name] = args.as_slice() {
        if flag == "--run" {
            match TESTS.iter().find(|test| test.name == name) {
                Some(test) => (test.run)(),
                None => {
                    eprintln!("integration_ml: no test {}", name);
                    std::process::exit(2)
                }
            }
            return;
        }
    }
    // `cargo test` passes its own flags (`--nocapture`, ...): a filter is
    // any argument that does not start with `-`.
    let filters: Vec<&String> = args.iter().skip(1).filter(|a| !a.starts_with('-')).collect();
    let exe = std::env::current_exe().expect("integration_ml: current_exe");
    let keep = std::env::var_os("HH_INTEGRATION_ML_KEEP").is_some_and(|v| v == "1");
    let timeout = Duration::from_secs(
        std::env::var("HH_INTEGRATION_ML_TIMEOUT")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300),
    );
    let base_dir = std::env::temp_dir().join(format!("hh_iml.{}", std::process::id()));
    let (mut passed, mut failed, mut expected_failures, mut unexpected_passes) =
        (vec![], vec![], vec![], vec![]);
    for (index, test) in TESTS.iter().enumerate() {
        if !filters.is_empty() && !filters.iter().any(|f| test.name.contains(f.as_str())) {
            continue;
        }
        let dir: PathBuf = base_dir.join(index.to_string());
        std::fs::create_dir_all(&dir).expect("integration_ml: mkdir");
        let start = Instant::now();
        let mut child = Command::new(&exe)
            .args(["--run", test.name])
            .env("HH_INTEGRATION_ML_DIR", &dir)
            .spawn()
            .expect("integration_ml: spawn");
        let status = wait_with_timeout(&mut child, timeout);
        let ok = status.is_some_and(|s| s.success());
        let how = match status {
            None => format!(" (killed after {}s)", timeout.as_secs()),
            Some(_) => format!(" ({:.1}s)", start.elapsed().as_secs_f64()),
        };
        let verdict = match (ok, test.expected_to_fail) {
            (true, None) => {
                passed.push(test.name);
                "ok".to_string()
            }
            (true, Some(owner)) => {
                passed.push(test.name);
                unexpected_passes.push(test.name);
                format!("ok (marked \"expected to fail: {}\": remove the mark)", owner)
            }
            (false, None) => {
                failed.push(test.name);
                "FAILED".to_string()
            }
            (false, Some(owner)) => {
                expected_failures.push(test.name);
                format!("FAILED (expected to fail: {})", owner)
            }
        };
        println!("test {} ... {}{}", test.name, verdict, how);
        if ok && !keep {
            let _ = std::fs::remove_dir_all(&dir);
        } else if !ok {
            println!("  (files of the test: {})", dir.display());
        }
    }
    if !keep {
        // Empty unless a test failed.
        let _ = std::fs::remove_dir(&base_dir);
    }
    println!(
        "\nintegration_ml: {} passed, {} failed, {} failed as expected",
        passed.len(),
        failed.len(),
        expected_failures.len()
    );
    if !unexpected_passes.is_empty() {
        println!("marked \"expected to fail\" but passed: {:?}", unexpected_passes);
    }
    if !failed.is_empty() {
        println!("failures: {:?}", failed);
        std::process::exit(101)
    }
}
