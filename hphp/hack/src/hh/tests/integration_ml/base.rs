// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `test/integration_ml/integration_test_base.ml` (+ `.mli`,
//! `integration_test_base_types.ml`): an in-process server driven one loop
//! iteration at a time (`Server_main.serve_one_iteration` with a
//! `test_client_provider::T`), without a monitor.
//!
//! Owned by **T1** (plan §3.1).
//!
//! Deviations from the OCaml harness, all invisible to the tests:
//! - **A real temporary root instead of `Test_disk`.** The OCaml roots are
//!   `/`, `/hhi` and `/tmp` on a fake disk (`Test_disk.set`); here they are
//!   three real directories, `<dir>/root/`, `<dir>/hhi/`, `<dir>/tmp/`,
//!   where `<dir>` is made for each test by the runner (`main.rs`,
//!   environment variable `HH_INTEGRATION_ML_DIR`) and removed after it.
//!   `Test_disk.set path contents` writes the file (`""` writes an empty
//!   file, as the fake disk keeps an empty file). Because the root is not
//!   `/`, every assertion that compares printed diagnostics first passes
//!   the output through [`relativize`] (root prefix -> `/`), so the
//!   expected strings of the OCaml tests are kept verbatim.
//!   `HH_LOCALCONF_PATH` points at an empty directory, so that no `hh.conf`
//!   of the machine is read (the fake disk has none).
//! - **One process per test**, not `did_init` + `in_daemon`: the runner
//!   re-executes itself for each test (`main --run <test>`).
//! - The OCaml's process-global `Test_client_provider` refs are a
//!   [`test_client_provider::T`] made afresh by each [`run_loop_once`] (= `clear ()`).
//! - `Shared_mem.init`, `Event_logger.init_fake`, `Folly.ensure_folly_init`:
//!   nothing to do.
//! - Not ported (no test in scope uses them; the IDE tests are out of
//!   scope, plan §4.2): `start_initial_full_check` (prechecked files are not
//!   ported, plan §3.4), `assert_ide_completions`, `assert_find_refs`,
//!   `assert_rename`, `doc`, module `Client`.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use hh::diagnostics;
use hh::relative_path;
use hh::relative_path::Prefix;
use hh::test_client_provider;
use hh::s_set;
use hh::server_command_types;
use hh::server_config;
use hh::server_env;
use hh::server_env::Env;
use hh::server_env::Genv;
use hh::server_env_build;
use hh::server_main;
use hh::server_notifier;
use hh::typing_deps;
use hh::user_diagnostic;
use oxidized::global_options::GlobalOptions;
use oxidized::parser_options::ParserOptions;

type Diag = diagnostics::T;

/// `disk_changes_type`: (path, contents).
pub type DiskChanges<'a> = &'a [(&'a str, &'a str)];

/// `'a loop_inputs` (`new_client = Some (RequestResponse cmd)`).
#[derive(Default)]
pub struct LoopInputs {
    pub disk_changes: Vec<(String, String)>,
    pub new_client: Option<server_command_types::T>,
}

/// `'a loop_outputs`
#[derive(Default)]
pub struct LoopOutputs {
    pub did_read_disk_changes: bool,
    pub total_changed_files_count: isize,
    pub total_rechecked_count: isize,
    pub last_actual_total_rechecked_count: Option<isize>,
    pub new_client_response: Option<server_command_types::CommandResult>,
}

/// `default_loop_input`
pub fn default_loop_input() -> LoopInputs {
    LoopInputs::default()
}

/// `{ default_loop_input with disk_changes }`
pub fn loop_input(disk_changes: DiskChanges) -> LoopInputs {
    LoopInputs {
        disk_changes: disk_changes
            .iter()
            .map(|(x, y)| (x.to_string(), y.to_string()))
            .collect(),
        new_client: None,
    }
}

// ~~ The roots (`root`, `hhi`, `tmp`) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

struct Roots {
    /// `root` (with a trailing slash, as `"/"`)
    root: String,
    /// `hhi` (no trailing slash, as `"/hhi"`)
    hhi: String,
    /// `tmp`
    tmp: String,
}

static ROOTS: OnceLock<Roots> = OnceLock::new();

fn roots() -> &'static Roots {
    ROOTS.get_or_init(|| {
        let dir = match std::env::var_os("HH_INTEGRATION_ML_DIR") {
            Some(dir) => PathBuf::from(dir),
            None => {
                fail("integration_ml: HH_INTEGRATION_ML_DIR is not set (run the tests through the runner)")
            }
        };
        let make = |name: &str| -> String {
            let d = dir.join(name);
            std::fs::create_dir_all(&d).expect("integration_ml: mkdir");
            // `Path.make` is a realpath (on macOS /var is /private/var).
            let d = std::fs::canonicalize(&d).expect("integration_ml: realpath");
            d.to_str().expect("integration_ml: UTF-8 path").to_string()
        };
        let localconf = make("localconf");
        // SAFETY: set before any other thread of the test starts.
        unsafe {
            std::env::set_var("HH_LOCALCONF_PATH", &localconf);
        }
        Roots {
            root: format!("{}/", make("root")),
            hhi: make("hhi"),
            tmp: make("tmp"),
        }
    })
}

/// `root`: the root of the test, with a trailing slash (the OCaml's `"/"`).
pub fn root() -> &'static str {
    &roots().root
}

/// `hhi`: the hhi directory of the test (the OCaml's `"/hhi"`).
pub fn hhi() -> &'static str {
    &roots().hhi
}

/// `Relative_path.set_path_prefix Relative_path.Root (Path.make root)`
/// (the tests that load a `.hhconfig` before `setup_server`).
pub fn set_root_prefix() {
    relative_path::set_path_prefix(Prefix::Root, Path::new(root()));
}

/// `Test_disk.set path contents`, `path` absolute.
pub fn disk_set(path: &str, contents: &str) {
    let path = Path::new(path);
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir).expect("integration_ml: mkdir");
    }
    std::fs::write(path, contents).expect("integration_ml: write");
}

/// `Hhi.get_raw_hhi_contents () |> Array.to_list`
pub fn raw_hhi_contents() -> Vec<(&'static str, &'static str)> {
    hhi::HHI_CONTENTS.to_vec()
}

/// `Server_config.load ~silent:false ~from:"" ~cli_config_overrides:[]`
/// after `Test_disk.set hhconfig_filename hhconfig_contents` (with the root
/// prefix set first, as the tests do).
pub fn load_config_with_hhconfig(hhconfig_contents: &str) -> server_config::T {
    set_root_prefix();
    disk_set(&format!("{}.hhconfig", root()), hhconfig_contents);
    match server_config::load(false, "", &[]) {
        Ok((config, _local_config)) => config,
        Err(e) => fail(&format!("Server_config.load: {:?}", e)),
    }
}

// ~~ The server ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `server_config`: `Server_env_build.default_genv`'s config with the
/// test's parser and typechecker options.
pub fn server_config() -> server_config::T {
    let po = ParserOptions {
        disable_xhp_element_mangling: false,
        deregister_php_stdlib: true,
        ..ParserOptions::default()
    };
    let global_opts = GlobalOptions {
        po: po.clone(),
        tco_num_local_workers: Some(1),
        tco_saved_state: Default::default(),
        tco_fetch_remote_old_decls: false,
        ..GlobalOptions::default()
    };
    let config = server_env_build::default_genv().config;
    let config = server_config::set_tc_options(config, global_opts);
    server_config::set_parser_options(config, po)
}

/// `!genv` (`{ Server_env_build.default_genv with config = server_config }`)
/// with the given notifier.
fn genv(notifier: server_notifier::T) -> Genv {
    Genv {
        config: server_config(),
        notifier,
        ..server_env_build::default_genv()
    }
}

/// Init part common to fresh and saved state init (`test_init_common`).
fn test_init_common(hhi_files: &[(&str, &str)]) {
    // (`did_init`: each test runs in a process of its own.)
    // SAFETY: set before any other thread of the test starts.
    unsafe {
        std::env::set_var("HH_TEST_MODE", "1");
    }
    relative_path::set_path_prefix(Prefix::Root, Path::new(root()));
    relative_path::set_path_prefix(Prefix::Hhi, Path::new(hhi()));
    relative_path::set_path_prefix(Prefix::Tmp, Path::new(&roots().tmp));
    hh::server_progress::disable();
    // `Typing_deps.trace` is `ref true` in the OCaml process and nothing in
    // the test turns it off (only `Server_env_build.make_genv` does, in
    // check mode); the Rust flag starts `false` for the batch checker, so
    // the test, as every driver that wants the edges, turns it on.
    typing_deps::TRACE.store(true, Ordering::SeqCst);
    server_main::force_break_recheck_loop_for_test(true);
    for (fn_, contents) in hhi_files {
        disk_set(&format!("{}/{}", hhi(), fn_), contents);
    }
}

/// `setup_server ?custom_config ?hhi_files ?edges_dir ()`
///
/// Hhi files are loaded during server setup. If given a list of string +
/// contents, we add them to the test disk and add them to
/// disk_needs_parsing. After one server run loop, they will be loaded.
/// This isn't exactly the same as how initialization does it, but the
/// purpose is not to test the hhi files, but to test incremental mode
/// behavior with Hhi files present.
pub fn setup_server(
    custom_config: Option<server_config::T>,
    hhi_files: &[(&str, &str)],
    edges_dir: Option<&str>,
) -> Env {
    test_init_common(hhi_files);
    let init_id = hh::random_id::short_string();
    let deps_mode = match edges_dir {
        Some(edges_dir) => typing_deps::mode::T::SaveToDiskMode {
            graph: None,
            new_edges_dir: edges_dir.to_string(),
            human_readable_dep_map_dir: None,
        },
        None => typing_deps::mode::T::InMemoryMode(None),
    };
    let config = match custom_config {
        Some(config) => config,
        None => server_config(),
    };
    let env = server_env_build::make_env(&init_id, deps_mode, None, &config, Path::new(root()));
    let hhi_set: relative_path::set::T = hhi_files
        .iter()
        .map(|(fn_, _)| relative_path::create(Prefix::Hhi, &format!("{}/{}", hhi(), fn_)))
        .collect();
    hh::server_progress::disable();
    // Return environment
    Env {
        disk_needs_parsing: hhi_set,
        ..env
    }
}

/// `run_loop_once env inputs`
pub fn run_loop_once(env: Env, inputs: LoopInputs) -> (Env, LoopOutputs) {
    // `Test_client_provider.clear ()`
    let mut client_provider = test_client_provider::T::default();
    if let Some(x) = inputs.new_client {
        client_provider.mock_new_client_type(server_command_types::ConnectionType::NonPersistent);
        client_provider.mock_client_request(x);
    }
    let disk_changes: Vec<(String, String)> = inputs
        .disk_changes
        .iter()
        .map(|(x, y)| (prepend_root(x), y.clone()))
        .collect();
    for (path, contents) in &disk_changes {
        disk_set(path, contents);
    }
    let did_read_disk_changes_ref = Arc::new(AtomicBool::new(false));
    let changes: s_set::T = disk_changes.iter().map(|(path, _)| path.clone()).collect();
    let get_changes_sync: Arc<dyn Fn() -> s_set::T + Send + Sync> = {
        let did_read = Arc::clone(&did_read_disk_changes_ref);
        Arc::new(move || {
            if !did_read.swap(true, Ordering::SeqCst) {
                changes.clone()
            } else {
                s_set::T::new()
            }
        })
    };
    let get_changes_async = {
        let get_changes_sync = Arc::clone(&get_changes_sync);
        move || server_notifier::Changes::SyncChanges(get_changes_sync())
    };
    let genv = genv(server_notifier::init_mock(get_changes_async, move || {
        get_changes_sync()
    }));
    // Always pick up disk changes in tests immediately
    let env = Env {
        last_notifier_check_time: 0.0,
        ..env
    };
    let env = server_main::serve_one_iteration(&genv, env, &mut client_provider);
    let server_env::RecheckLoopStats {
        total_changed_files_count,
        total_rechecked_count,
        ..
    } = env.last_recheck_loop_stats;
    let last_actual_total_rechecked_count = env
        .last_recheck_loop_stats_for_actual_work
        .as_ref()
        .map(|stats| stats.total_rechecked_count);
    // `Test_client_provider.get_client_response Non_persistent` (the
    // provider is dropped here: its response is moved out, not cloned).
    let new_client_response = client_provider.client_response.take();
    (
        env,
        LoopOutputs {
            did_read_disk_changes: did_read_disk_changes_ref.load(Ordering::SeqCst),
            total_changed_files_count,
            total_rechecked_count,
            last_actual_total_rechecked_count,
            new_client_response,
        },
    )
}

/// `prepend_root x`
pub fn prepend_root(x: &str) -> String {
    format!("{}{}", root(), x)
}

/// `fail x`: prints `x` (stdout) and the call stack (stderr), then raises
/// `Integration_test_failure` (a panic: the test process exits non-zero).
pub fn fail(x: &str) -> ! {
    println!("{}", x);
    eprintln!("{}", std::backtrace::Backtrace::force_capture());
    panic!("Integration_test_failure")
}

// ~~ Utility functions to help format/throw errors for informative errors ~~

/// `relativize s`: replaces every occurrence of the root prefix with `/`.
pub fn relativize(s: &str) -> String {
    let root_prefix = relative_path::path_of_prefix(Prefix::Root).expect("the root prefix is set");
    s.replace(&root_prefix, "/")
}

/// `indent_string_with indent error`
fn indent_string_with(indent: &str, error: &str) -> String {
    // `Str.split (regexp "\n")`: delimiters at the beginning and at the end
    // of the string are ignored.
    let pieces: Vec<&str> = error.split('\n').collect();
    let start = pieces.iter().position(|p| !p.is_empty()).unwrap_or(pieces.len());
    let end = pieces.iter().rposition(|p| !p.is_empty()).map_or(start, |i| i + 1);
    let pieces = &pieces[start..end.max(start)];
    format!("{}{}", indent, pieces.join(&format!("\n{}", indent)))
}

/// `indent_strings_with indent errors`
fn indent_strings_with(indent: &str, errors: &[String]) -> String {
    errors.iter().map(|e| indent_string_with(indent, e)).collect()
}

/// `assertEqual expected got` (both stripped).
pub fn assert_equal(expected: &str, got: &str) {
    let expected = expected.trim();
    let got = got.trim();
    if expected != got {
        fail(&format!("Expected:\n{}\n\nBut got:\n{}\n", expected, got))
    }
}

/// `change_files env disk_changes`
pub fn change_files(env: Env, disk_changes: DiskChanges) -> (Env, LoopOutputs) {
    let (env, loop_output) = run_loop_once(env, loop_input(disk_changes));
    if !loop_output.did_read_disk_changes {
        fail("Expected the server to process disk updates");
    }
    (env, loop_output)
}

/// `setup_disk env disk_changes`
pub fn setup_disk(env: Env, disk_changes: DiskChanges) -> Env {
    change_files(env, disk_changes).0
}

/// `diagnostic_strings diag_list` (relativized: see the module doc).
pub fn diagnostic_strings(diag_list: &[diagnostics::Diagnostic]) -> Vec<String> {
    diag_list
        .iter()
        .map(|x| relativize(&user_diagnostic::to_string(&user_diagnostic::to_absolute(x))))
        .collect()
}

/// `assertSingleDiagnostic expected diag_list`
pub fn assert_single_diagnostic(expected: &str, diag_list: &[diagnostics::Diagnostic]) {
    let diagnostic_strings = diagnostic_strings(diag_list);
    match diagnostic_strings.as_slice() {
        [x] => assert_equal(expected, x),
        _ => {
            let diag_count = diag_list.len();
            let fmt_expected = indent_string_with(" < ", expected);
            let fmt_actual = indent_strings_with(" > ", &diagnostic_strings);
            let msg = format!(
                "Expected to have exactly one diagnostic, namely:

{}

... but got {} diagnostics...

{}
",
                fmt_expected, diag_count, fmt_actual
            );
            fail(&msg)
        }
    }
}

/// `Diagnostics.get_diagnostic_list env.diagnostics`
pub fn diagnostic_list(diagnostics: &Diag) -> Vec<diagnostics::Diagnostic> {
    diagnostics::get_diagnostic_list(None, diagnostics.clone())
}

/// `full_check_status env`
pub fn full_check_status(env: Env) -> (Env, LoopOutputs) {
    // the empty string isn't just a test placeholder - when a file is deleted
    // or renamed, the content is set to the empty string internally
    run_loop_once(env, loop_input(&[("__dummy_file_to_trigger_full_check.php", "")]))
}

/// `assert_diagnostics diagnostics expected`
pub fn assert_diagnostics(diagnostics: &Diag, expected: &str) {
    let mut buf = String::with_capacity(1024);
    for diagnostic in diagnostic_list(diagnostics) {
        buf.push_str(&user_diagnostic::to_string(&user_diagnostic::to_absolute(
            &diagnostic,
        )));
        buf.push('\n');
    }
    assert_equal(expected, &relativize(&buf))
}

/// `assert_env_diagnostics env expected`
pub fn assert_env_diagnostics(env: &Env, expected: &str) {
    assert_diagnostics(&env.diagnostics, expected)
}

/// `assert_no_diagnostics env`
pub fn assert_no_diagnostics(env: &Env) {
    assert_env_diagnostics(env, "")
}

/// `assert_needs_recheck env x`
pub fn assert_needs_recheck(env: &Env, x: &str) {
    if !env
        .needs_recheck
        .contains(&relative_path::create_detect_prefix(&prepend_root(x)))
    {
        eprintln!("Expected {} to need recheck", x);
        panic!("assert false")
    }
}

/// `assert_needs_no_recheck env x`
pub fn assert_needs_no_recheck(env: &Env, x: &str) {
    if env
        .needs_recheck
        .contains(&relative_path::create_detect_prefix(&prepend_root(x)))
    {
        eprintln!("Expected {} not to need recheck", x);
        panic!("assert false")
    }
}
