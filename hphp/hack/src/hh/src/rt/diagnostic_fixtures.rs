// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Fixtures for the tests of the diagnostic formatters (no OCaml
//! counterpart).
//!
//! The formatters read the terminal (`Unix.isatty`, `Tty.supports_color`),
//! the environment (`FORCE_ERROR_COLOR`), the current directory (paths are
//! shown relative to it) and the source files. So that a test sees exactly
//! what `hphp/hack/test/verify.py` gives `hh_single_type_check`,
//! [`run_in_suite`] runs its body in a child process: this test binary,
//! running that one test, with its stdout a pipe, `TERM` unset,
//! `FORCE_ERROR_COLOR` set to `true` or `false`, the prefixes of
//! `Relative_path` set as `hh_single_type_check` sets them (the root is `/`),
//! and as its current directory the directory of the suite,
//! `hphp/hack/test/<suite>`. What the body returns comes back to the parent,
//! which compares it with what the test expects.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;
use std::sync::Arc;

use bstr::BString;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::user_diagnostic::Severity;
use oxidized::user_diagnostic::UserDiagnostic;
use relative_path::Prefix;
use relative_path::RelativePath;

use crate::pos::Absolute;

/// `Diagnostics.finalized_diagnostic`
pub type FinalizedDiagnostic = UserDiagnostic<Absolute, Absolute>;

/// Set in the child process: where it writes what the body returned.
const OUT_VAR: &str = "HH_DIAGNOSTIC_FORMATTER_TEST_OUT";

/// The directory of the test suites, `hphp/hack/test`.
pub fn test_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test")
}

/// In the parent process (the test as cargo runs it), runs this test again in
/// a child process, as described in the module documentation, and returns
/// `Some` of what `body` returned there; the test fails if the child does.
/// In the child, runs `body` and returns `None`.
///
/// `module_path` is `module_path!()` of the test module and `test` the name
/// of the test function; `suite` is the directory of the suite, relative to
/// `hphp/hack/test`.
pub fn run_in_suite(
    module_path: &str,
    test: &str,
    suite: &str,
    force_color: bool,
    body: impl FnOnce() -> String,
) -> Option<String> {
    if let Some(out_file) = std::env::var_os(OUT_VAR) {
        // `Sys.getcwd` gives the path without symbolic links: so do the
        // paths of the files.
        let dir = std::fs::canonicalize(test_dir().join(suite)).unwrap();
        std::env::set_current_dir(&dir).unwrap();
        set_prefixes();
        let out = body();
        std::fs::write(out_file, out).unwrap();
        return None;
    }
    // libtest names a test by its path without the crate.
    let module_path = match module_path.split_once("::") {
        Some((_crate, path)) => path,
        None => module_path,
    };
    let name = format!("{module_path}::{test}");
    let out_file = std::env::temp_dir().join(format!(
        "hh_diagnostic_formatter_test_{}_{}.out",
        std::process::id(),
        name.replace("::", "_")
    ));
    let _ = std::fs::remove_file(&out_file);
    let out = Command::new(std::env::current_exe().unwrap())
        .args([name.as_str(), "--exact", "--nocapture", "--test-threads=1"])
        .env(OUT_VAR, &out_file)
        .env(
            "FORCE_ERROR_COLOR",
            if force_color { "true" } else { "false" },
        )
        .env_remove("TERM")
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && stdout.contains("1 passed"),
        "the test {name} failed in its child process:\n{stdout}\n{stderr}"
    );
    let res = std::fs::read_to_string(&out_file)
        .unwrap_or_else(|e| panic!("{}: {e}", out_file.display()));
    let _ = std::fs::remove_file(&out_file);
    Some(res)
}

/// The prefixes of `Relative_path`, as `hh_single_type_check` sets them when
/// it has no `--root`.
fn set_prefixes() {
    crate::relative_path::set_path_prefix(Prefix::Root, Path::new("/"));
    crate::relative_path::set_path_prefix(
        Prefix::Hhi,
        &std::env::temp_dir().join("hh_diagnostic_formatter_test_hhi"),
    );
    crate::relative_path::set_path_prefix(Prefix::Tmp, Path::new("tmp"));
}

/// The contents of a file of the test suites (`suite_file` is relative to
/// `hphp/hack/test`).
pub fn suite_file(suite_file: &str) -> String {
    let path = test_dir().join(suite_file);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The expected output `file` of the suite `suite`.
pub fn expected(suite: &str, file: &str) -> String {
    suite_file(&format!("{suite}/{file}"))
}

/// The position in `file` (relative to the current directory, so to the
/// directory of the suite in [`run_in_suite`]) from `start` to `end`, each
/// `(line, column)`: lines start at 1, columns at 0 (bytes), and the end is
/// exclusive. A line may be the one just after the end of the file. The path
/// of the position is the absolute path of the file (a `Dummy` path, as
/// `hh_single_type_check` makes them). In a file that does not exist, every
/// line starts at offset 0.
pub fn pos(file: &str, start: (usize, usize), end: (usize, usize)) -> Absolute {
    let path = std::env::current_dir().unwrap().join(file);
    let bols: Option<Vec<usize>> = std::fs::read(&path).ok().map(|content| {
        let mut bols = vec![0];
        for (i, c) in content.iter().enumerate() {
            if *c == b'\n' {
                bols.push(i + 1);
            }
        }
        bols
    });
    let lnum_bol_offset = |(line, col): (usize, usize)| {
        let bol = match &bols {
            None => 0,
            Some(bols) => *bols
                .get(line - 1)
                .unwrap_or_else(|| panic!("{file} has no line {line}")),
        };
        (line, bol, bol + col)
    };
    let file = Arc::new(RelativePath::make(Prefix::Dummy, path));
    let pos = Pos::from_lnum_bol_offset(file, lnum_bol_offset(start), lnum_bol_offset(end));
    crate::pos::to_absolute(&pos)
}

/// The position of `File "file", line L, characters S-E` (columns from 1,
/// `end` inclusive).
pub fn chars(file: &str, line: usize, start: usize, end: usize) -> Absolute {
    pos(file, (line, start - 1), (line, end))
}

pub fn msg(pos: Absolute, s: &str) -> Message<Absolute> {
    Message(pos, BString::from(s))
}

pub fn diagnostic(
    severity: Severity,
    code: isize,
    claim: Message<Absolute>,
    reasons: Vec<Message<Absolute>>,
) -> FinalizedDiagnostic {
    UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation: Explanation::Empty,
        quickfixes: vec![],
        custom_msgs: vec![],
        is_fixmed: false,
        function_pos: None,
    }
}

pub fn err(
    code: isize,
    claim: Message<Absolute>,
    reasons: Vec<Message<Absolute>>,
) -> FinalizedDiagnostic {
    diagnostic(Severity::Err, code, claim, reasons)
}

pub fn warning(
    code: isize,
    claim: Message<Absolute>,
    reasons: Vec<Message<Absolute>>,
) -> FinalizedDiagnostic {
    diagnostic(Severity::Warning { is_trusted: true }, code, claim, reasons)
}

/// What `hh_single_type_check --batch-files` writes for these diagnostics in
/// this format (`write_error_list`): each of them, then the summary, or
/// `No errors` (there is no `--max-errors` in the suites).
pub fn single_type_check_output(
    format: oxidized::diagnostics::Format,
    to_string: impl Fn(&FinalizedDiagnostic) -> String,
    errors: &[FinalizedDiagnostic],
) -> String {
    if errors.is_empty() {
        return "No errors\n".to_string();
    }
    let mut out: String = errors.iter().map(to_string).collect();
    if let Some(summary) =
        crate::diagnostics_state::format_summary(format, errors.len() as isize, 0, Some(0), None)
    {
        out.push_str(&summary);
    }
    out
}

/// Panics with both texts, and the first line where they differ, if they
/// differ.
pub fn assert_same_text(actual: &str, expected: &str) {
    if actual != expected {
        let line = actual
            .split('\n')
            .zip(expected.split('\n'))
            .position(|(a, e)| a != e)
            .unwrap_or_else(|| actual.split('\n').count().min(expected.split('\n').count()));
        panic!(
            "the texts differ from line {}:\n--- actual\n{}\n--- expected\n{}\n---\nactual:   {:?}\nexpected: {:?}",
            line + 1,
            actual,
            expected,
            actual,
            expected
        );
    }
}
