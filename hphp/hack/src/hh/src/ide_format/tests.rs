// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Tests of `ide_format` against the OCaml's behaviour:
//!
//! - `test/hackfmt/ide_format`: the expected outputs of the OCaml
//!   `hh_single_ide_format` (whole-document formatting through `go_ide`),
//!   reproduced here by a port of that driver;
//! - `test/hackfmt/range_tests`: the `--at-char` and `--range` cases, through
//!   `go_ide` with a position or a range;
//! - fake `hackfmt` executables for the arguments passed, each exit code,
//!   death by a signal, the timeout, and a missing executable.
//!
//! The real `hackfmt` is `$HH_TEST_HACKFMT` when set, else the one built
//! next to the test binary (`cargo build --release -p hackfmt` into the same
//! target directory); the tests that need it are skipped without it.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;

use super::*;

/// `HACKFMT_TEST_PATH` is process-wide: the tests that set it take this.
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn test_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test/hackfmt")
}

fn real_hackfmt() -> Option<PathBuf> {
    // Not `HACKFMT_TEST_PATH`, which the tests set for `go_ide`.
    if let Some(p) = std::env::var_os("HH_TEST_HACKFMT") {
        return Some(PathBuf::from(p));
    }
    // target/release/deps/<test> -> target/release/hackfmt
    let exe = std::env::current_exe().ok()?;
    let p = exe.parent()?.parent()?.join("hackfmt");
    p.exists().then_some(p)
}

fn with_hackfmt<A>(path: &Path, f: impl FnOnce() -> A) -> A {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let old = std::env::var_os("HACKFMT_TEST_PATH");
    // SAFETY: the tests that touch the environment hold ENV_LOCK.
    unsafe { std::env::set_var("HACKFMT_TEST_PATH", path) };
    let r = f();
    match old {
        Some(old) => unsafe { std::env::set_var("HACKFMT_TEST_PATH", old) },
        None => unsafe { std::env::remove_var("HACKFMT_TEST_PATH") },
    }
    r
}

fn options(tab_size: isize, insert_spaces: bool) -> FormattingOptions {
    FormattingOptions {
        tab_size,
        insert_spaces,
    }
}

// ---------------------------------------------------------------------------
// `hh_single_ide_format.ml`, ported to produce the `.exp` text.
// ---------------------------------------------------------------------------

fn str_of_range(r: &ide_api_types::Range) -> String {
    format!(
        "{}-{} (1-indexed)",
        position::to_string_one_based(&r.st),
        position::to_string_one_based(&r.ed)
    )
}

fn with_line_numbers(code: &str) -> String {
    crate::rt::ocaml_string::split_lines(code)
        .iter()
        .enumerate()
        .map(|(i, line)| format!("{} {}", i + 1, line))
        .collect::<Vec<_>>()
        .join("\n")
}

fn apply_edit(orig_code: &str, edit: &IdeResponse) -> String {
    let st = &edit.range.st;
    let ed = &edit.range.ed;
    assert!(position::is_beginning_of_line(st));
    assert!(position::is_beginning_of_line(ed));
    let orig_lines = crate::rt::ocaml_string::split_lines(orig_code);
    let (start_line, _) = position::line_column_zero_based(st);
    let (end_line, _) = position::line_column_zero_based(ed);
    let mut updated: Vec<String> = orig_lines
        .iter()
        .enumerate()
        .filter(|(n, _)| (*n as isize) < start_line)
        .map(|(_, l)| l.clone())
        .collect();
    updated.extend(crate::rt::ocaml_string::split_lines(&edit.new_text));
    updated.extend(
        orig_lines
            .iter()
            .enumerate()
            .filter(|(n, _)| (*n as isize) >= end_line)
            .map(|(_, l)| l.clone()),
    );
    let suffix = match (updated.len(), updated.last()) {
        (0, _) => "",
        (_, Some(l)) if l.is_empty() => "",
        _ => "\n",
    };
    updated.join("\n") + suffix
}

fn run_format_test(hackfmt: &Path, filename: &Path) -> String {
    let code = std::fs::read_to_string(filename).unwrap();
    let mut out = String::new();
    match go_ide("foo.php", &code, &IdeAction::Document, &options(2, true)) {
        Ok(edit) => {
            let new_code = apply_edit(&code, &edit);
            out.push_str("> lines and columns in ranges are 1-indexed\n");
            out.push_str(&format!("received code:\n{}\n\n", with_line_numbers(&code)));
            out.push_str(&format!(
                "New text at range {} is\n'{}'\n\n",
                str_of_range(&edit.range),
                edit.new_text
            ));
            out.push_str(&format!(
                "Code after applying language server edits:\n'{}'\n\n",
                new_code
            ));
            let hackfmt_stdout = std::process::Command::new(hackfmt)
                .arg(filename)
                .output()
                .unwrap()
                .stdout;
            if new_code.as_bytes() == hackfmt_stdout.as_slice() {
                out.push_str("Matched Hackfmt result\n");
            } else {
                panic!(
                    "Did not match hackfmt result!'{}'\n",
                    String::from_utf8_lossy(&hackfmt_stdout)
                );
            }
        }
        Err(s) => panic!("something went wrong! {}", s),
    }
    out
}

#[test]
fn ide_format_suite_matches_ocaml_expectations() {
    let Some(hackfmt) = real_hackfmt() else {
        eprintln!("skipped: no hackfmt executable");
        return;
    };
    let dir = test_dir().join("ide_format");
    let mut n = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "php") {
            let exp = std::fs::read_to_string(path.with_extension("php.exp")).unwrap();
            let got = with_hackfmt(&hackfmt, || run_format_test(&hackfmt, &path));
            assert_eq!(got, exp, "{}", path.display());
            n += 1;
        }
    }
    assert!(n >= 6);
}

// ---------------------------------------------------------------------------
// `--at-char` and `--range` cases.
// ---------------------------------------------------------------------------

fn flags_of(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path.with_extension("flags"))
        .unwrap()
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

#[test]
fn at_char_cases() {
    let Some(hackfmt) = real_hackfmt() else {
        eprintln!("skipped: no hackfmt executable");
        return;
    };
    let dir = test_dir().join("range_tests");
    let mut n = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "php") {
            continue;
        }
        let flags = flags_of(&path);
        if flags[0] != "--at-char" {
            continue;
        }
        let offset: isize = flags[1].parse().unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        let exp = std::fs::read_to_string(path.with_extension("php.exp")).unwrap();
        let position = file_content::offset_to_position(&content, offset);
        assert_eq!(file_content::get_offset(&content, &position), offset);
        let got = with_hackfmt(&hackfmt, || {
            go_ide("f.php", &content, &IdeAction::Position(position), &options(2, true))
        });
        if exp.starts_with("Invalid argument") {
            // hackfmt exits with 3 (`InvalidCliArg`).
            assert_eq!(got, Err("Invalid argument".to_string()), "{}", path.display());
            n += 1;
            continue;
        }
        let got = got.unwrap();
        // The expected output is `FROM TO\n` then the text (no trailing
        // newline is added by go_ide).
        let exp_lines = input_lines(exp.as_bytes());
        let (from0, to0) = match_range_line(&exp_lines[0]).unwrap();
        assert_eq!(
            got.range,
            ide_api_types::Range {
                st: file_content::offset_to_position(&content, from0),
                ed: file_content::offset_to_position(&content, to0),
            },
            "{}",
            path.display()
        );
        assert_eq!(got.new_text, exp_lines[1..].join("\n"), "{}", path.display());
        n += 1;
    }
    assert_eq!(n, 15);
}

#[test]
fn range_cases() {
    let Some(hackfmt) = real_hackfmt() else {
        eprintln!("skipped: no hackfmt executable");
        return;
    };
    let dir = test_dir().join("range_tests");
    let mut n = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "php") {
            continue;
        }
        let flags = flags_of(&path);
        if flags[0] != "--range" {
            continue;
        }
        // hackfmt's `--range` offsets are 1-based.
        let from1: isize = flags[1].parse().unwrap();
        let to1: isize = flags[2].parse().unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        let range = ide_api_types::Range {
            st: file_content::offset_to_position(&content, from1 - 1),
            ed: file_content::offset_to_position(&content, to1 - 1),
        };
        let (expanded, from0, to0) =
            expand_range_to_whole_rows(&content, &ide_api_types::ide_range_to_fc(&range));
        let got = with_hackfmt(&hackfmt, || {
            go_ide("f.php", &content, &IdeAction::Range(range), &options(2, true))
        })
        .unwrap();
        assert_eq!(got.range, ide_api_types::ide_range_from_fc(&expanded));
        assert!(position::is_beginning_of_line(&got.range.st));
        // What hackfmt prints for the expanded range, as lines + "\n".
        let out = std::process::Command::new(&hackfmt)
            .args(["--indent-width", "2", "--range"])
            .arg((from0 + 1).to_string())
            .arg((to0 + 1).to_string())
            .arg(&path)
            .output()
            .unwrap();
        let lines = input_lines(&out.stdout);
        assert_eq!(got.new_text, lines.join("\n") + "\n", "{}", path.display());
        if (from0, to0) == (from1 - 1, to1 - 1) {
            let exp = std::fs::read_to_string(path.with_extension("php.exp")).unwrap();
            // (The suite's runner ignores trailing newlines.)
            assert_eq!(got.new_text.trim_end_matches('\n'), exp.trim_end_matches('\n'), "{}", path.display());
        }
        n += 1;
    }
    assert_eq!(n, 8);
}

// ---------------------------------------------------------------------------
// Pure functions.
// ---------------------------------------------------------------------------

#[test]
fn split_lines_is_cores() {
    assert_eq!(crate::rt::ocaml_string::split_lines(""), Vec::<String>::new());
    assert_eq!(crate::rt::ocaml_string::split_lines("\n"), vec![""]);
    assert_eq!(crate::rt::ocaml_string::split_lines("a"), vec!["a"]);
    assert_eq!(crate::rt::ocaml_string::split_lines("a\n"), vec!["a"]);
    assert_eq!(crate::rt::ocaml_string::split_lines("a\n\n"), vec!["a", ""]);
    assert_eq!(crate::rt::ocaml_string::split_lines("a\r\nb\r"), vec!["a", "b\r"]);
    assert_eq!(crate::rt::ocaml_string::split_lines("\r\n"), vec![""]);
}

#[test]
fn input_lines_is_input_line() {
    assert_eq!(input_lines(b""), Vec::<String>::new());
    assert_eq!(input_lines(b"a"), vec!["a"]);
    assert_eq!(input_lines(b"a\n"), vec!["a"]);
    assert_eq!(input_lines(b"a\n\nb"), vec!["a", "", "b"]);
    assert_eq!(input_lines(b"a\r\n"), vec!["a\r"]);
}

#[test]
fn range_line() {
    assert_eq!(match_range_line("10 12"), Some((10, 12)));
    assert_eq!(match_range_line("10  12"), None);
    assert_eq!(match_range_line(" 10 12"), None);
    assert_eq!(match_range_line("10 12 "), None);
    assert_eq!(match_range_line("a 12"), None);
    assert_eq!(match_range_line(""), None);
}

#[test]
fn minimal_edits() {
    let r = |l1, l2| ide_api_types::Range {
        st: position::from_zero_based(l1, 0),
        ed: position::from_zero_based(l2, 0),
    };
    // No change.
    assert_eq!(minimal_edit("a\nb\n", "a\nb\n"), noop_edit());
    // One line changed in the middle.
    let e = minimal_edit("a\nb\nc\n", "a\nB\nc\n");
    assert_eq!((e.new_text.as_str(), e.range), ("B\n", r(1, 2)));
    // A line deleted: start backs up one line, empty text.
    let e = minimal_edit("a\nb\nb\nc\n", "a\nb\nc\n");
    assert_eq!((e.new_text.as_str(), e.range), ("", r(1, 2)));
    // New lines appended after identical old lines: no first change (the
    // OCaml compares only the old lines), so a no-op.
    assert_eq!(minimal_edit("a\n", "a\nb\n"), noop_edit());
}

#[test]
fn expand_ranges() {
    let content = "ab\ncd\nef";
    let pos = position::from_one_based;
    let fc = |st, ed| file_content::Range { st, ed };
    // Already whole rows.
    assert_eq!(
        expand_range_to_whole_rows(content, &fc(pos(1, 1), pos(2, 1))),
        (fc(pos(1, 1), pos(2, 1)), 0, 3)
    );
    // Start pulled back, end pushed to the next line.
    assert_eq!(
        expand_range_to_whole_rows(content, &fc(pos(1, 2), pos(2, 2))),
        (fc(pos(1, 1), pos(3, 1)), 0, 6)
    );
    // End on the last line (no newline): pulled back to the end of file.
    assert_eq!(
        expand_range_to_whole_rows(content, &fc(pos(2, 2), pos(3, 2))),
        (fc(pos(2, 1), pos(3, 3)), 3, 8)
    );
}

#[test]
fn options_to_args() {
    assert_eq!(formatting_options_to_args(&options(2, true)), vec!["--indent-width", "2"]);
    assert_eq!(
        formatting_options_to_args(&options(4, false)),
        vec!["--indent-width", "4", "--tabs"]
    );
}

// ---------------------------------------------------------------------------
// Fake hackfmt executables.
// ---------------------------------------------------------------------------

fn fake_hackfmt(name: &str, script: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("hh_ide_format_tests_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, format!("#!/bin/sh\n{}\n", script)).unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    path
}

#[test]
fn error_strings_of_exit_codes() {
    for (code, msg) in [
        (2, "File failed to parse without errors"),
        (3, "Invalid argument"),
        (4, "Invalid diff"),
        (1, "Internal Error"),
        (255, "Internal Error"),
    ] {
        let fake = fake_hackfmt(&format!("exit{}", code), &format!("cat >/dev/null; exit {}", code));
        let r = with_hackfmt(&fake, || {
            go_ide("f.php", "<?hh\n", &IdeAction::Document, &options(2, true))
        });
        assert_eq!(r, Err(msg.to_string()));
    }
    let fake = fake_hackfmt("killed", "cat >/dev/null; kill -9 $$");
    let r = with_hackfmt(&fake, || {
        go_ide("f.php", "<?hh\n", &IdeAction::Document, &options(2, true))
    });
    assert_eq!(r, Err("Call to hackfmt was killed".to_string()));
}

#[test]
fn at_char_output_errors() {
    let fake = fake_hackfmt("noout", "cat >/dev/null");
    let pos = position::from_one_based(1, 1);
    let r = with_hackfmt(&fake, || {
        go_ide("f.php", "<?hh\n", &IdeAction::Position(pos), &options(2, true))
    });
    assert_eq!(r, Err("Got no lines in at-position formatting".to_string()));
    let fake = fake_hackfmt("badrange", "cat >/dev/null; echo 'x y'; echo text");
    let r = with_hackfmt(&fake, || {
        go_ide("f.php", "<?hh\n", &IdeAction::Position(pos), &options(2, true))
    });
    assert_eq!(r, Err("Range not found on first line of --at-char output".to_string()));
}

#[test]
fn real_hackfmt_on_invalid_syntax() {
    let Some(hackfmt) = real_hackfmt() else {
        eprintln!("skipped: no hackfmt executable");
        return;
    };
    let r = with_hackfmt(&hackfmt, || {
        go_ide("f.php", "<?hh\nfunction {\n", &IdeAction::Document, &options(2, true))
    });
    assert_eq!(r, Err("File failed to parse without errors".to_string()));
}

#[test]
fn arguments_as_the_ocaml_passes_them() {
    let dir = std::env::temp_dir().join(format!("hh_ide_format_tests_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let log = dir.join("args.log");
    let fake = fake_hackfmt(
        "echoargs",
        &format!("printf '%s|' \"$0\" \"$@\" > '{}'; cat", log.display()),
    );
    let content = "<?hh\nfunction f(): void {}\n";
    let read_log = || std::fs::read_to_string(&log).unwrap();
    let fake_s = fake.display().to_string();

    let r = with_hackfmt(&fake, || {
        go_ide("foo.php", content, &IdeAction::Document, &options(2, true))
    });
    assert_eq!(r, Ok(noop_edit()));
    assert_eq!(
        read_log(),
        format!("{}|--indent-width|2|--filename-for-logging|foo.php|", fake_s)
    );

    let range = ide_api_types::Range {
        st: position::from_one_based(2, 3),
        ed: position::from_one_based(2, 5),
    };
    let r = with_hackfmt(&fake, || {
        go_ide("foo.php", content, &IdeAction::Range(range), &options(4, false))
    })
    .unwrap();
    assert_eq!(
        read_log(),
        format!(
            "{}|--indent-width|4|--tabs|--range|6|28|--filename-for-logging|foo.php|",
            fake_s
        )
    );
    // The fake echoes the whole content back.
    assert_eq!(r.new_text, content);
    assert_eq!(
        r.range,
        ide_api_types::Range {
            st: position::from_one_based(2, 1),
            ed: position::from_one_based(3, 1),
        }
    );

    let r = with_hackfmt(&fake, || {
        go_ide(
            "foo.php",
            "1 3\nabc",
            &IdeAction::Position(position::from_one_based(2, 2)),
            &options(2, true),
        )
    })
    .unwrap();
    assert_eq!(
        read_log(),
        format!(
            "{}|--at-char|5|--indent-width|2|--filename-for-logging|foo.php|",
            fake_s
        )
    );
    assert_eq!(r.new_text, "abc");
    assert_eq!(
        r.range,
        ide_api_types::Range {
            st: position::from_one_based(1, 2),
            ed: position::from_one_based(1, 4),
        }
    );
}

#[test]
fn formatter_not_found() {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let missing = "/nonexistent/hackfmt-for-test";
    let old = std::env::var_os("HACKFMT_TEST_PATH");
    unsafe { std::env::set_var("HACKFMT_TEST_PATH", missing) };
    let r = go_ide("f.php", "<?hh\n", &IdeAction::Document, &options(2, true));
    match old {
        Some(old) => unsafe { std::env::set_var("HACKFMT_TEST_PATH", old) },
        None => unsafe { std::env::remove_var("HACKFMT_TEST_PATH") },
    }
    let default = crate::path::make(&default_hackfmt_path());
    if Path::new(&default).exists() {
        eprintln!("skipped: {} exists", default);
        return;
    }
    assert_eq!(
        r,
        Err(format!(
            "Could not locate formatter - looked in: {} {}",
            missing, default
        ))
    );
}

#[test]
fn timeout() {
    let fake = fake_hackfmt("sleeper", "cat >/dev/null; sleep 20");
    let (r, elapsed) = with_hackfmt(&fake, || {
        let start = Instant::now();
        let r = go_ide("f.php", "<?hh\n", &IdeAction::Document, &options(2, true));
        (r, start.elapsed())
    });
    assert_eq!(r, Err("Call to hackfmt timed out".to_string()));
    assert!(elapsed >= Duration::from_secs(HACKFMT_TIMEOUT));
    assert!(elapsed < Duration::from_secs(HACKFMT_TIMEOUT + 3));
}

#[test]
fn default_hackfmt_path_has_the_suffix() {
    let bindir = option_env!("CMAKE_INSTALL_FULL_BINDIR").unwrap_or("/usr/local/bin");
    assert_eq!(default_hackfmt_path_of("_rust"), format!("{bindir}/hackfmt_rust"));
    assert_eq!(default_hackfmt_path_of(""), format!("{bindir}/hackfmt"));
    // The test binary has no suffix.
    assert_eq!(default_hackfmt_path(), format!("{bindir}/hackfmt"));
}
