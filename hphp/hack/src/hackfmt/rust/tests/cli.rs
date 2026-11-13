// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Command-line tests (some adapted from Hakana's formatter tests).

use std::fs;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;

struct TempDir(PathBuf);

impl TempDir {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("hackfmt-cli-test-{}-{}", name, std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        TempDir(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }

    fn write(&self, name: &str, contents: &str) {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn read(&self, name: &str) -> String {
        fs::read_to_string(self.0.join(name)).unwrap()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(root: &Path, args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_hackfmt"))
        .current_dir(root)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(stdin.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

fn stdout(o: &Output) -> &str {
    std::str::from_utf8(&o.stdout).unwrap()
}

fn stderr(o: &Output) -> &str {
    std::str::from_utf8(&o.stderr).unwrap()
}

const UNFORMATTED: &str = "<?hh\nfunction f():void{foo(1,2);}\n";
const FORMATTED: &str = "<?hh\nfunction f(): void {\n  foo(1, 2);\n}\n";

#[test]
fn stdin_and_parse_errors() {
    let root = TempDir::new("stdin");
    let result = run(root.path(), &[], "function f():void{foo(1,2);}");
    assert_eq!(result.status.code(), Some(0));
    assert_eq!(stdout(&result), "function f(): void {\n  foo(1, 2);\n}\n");
    assert_eq!(stderr(&result), "");

    let error = run(root.path(), &[], "<?hh\nfunction f(:void{");
    assert_eq!(error.status.code(), Some(2));
    assert_eq!(stdout(&error), "");
    assert!(stderr(&error).ends_with("\nFile failed to parse without errors\n"), "{}", stderr(&error));
    assert_eq!(
        stderr(&error),
        "(2,17)-(2,17) A variable name is expected here.\n\
         (2,17)-(2,17) A right parenthesis `)` is expected here.\n\
         (2,18)-(3,1) A right brace `}` is expected here.\n\
         File failed to parse without errors\n"
    );
}

#[test]
fn windows_line_endings_on_stdin_become_newlines() {
    // Like OCaml's In_channel.input_line, reading stdin drops the '\r' of
    // "\r\n" and ends the text with a newline.
    let root = TempDir::new("crlf");
    let result = run(root.path(), &[], "<?hh\r\nfunction f():void{}");
    assert_eq!(stdout(&result), "<?hh\nfunction f(): void {}\n");
}

#[test]
fn check_and_inplace_do_not_rewrite_unchanged_or_invalid_files() {
    let root = TempDir::new("check");
    root.write("a.php", UNFORMATTED);
    root.write("b.php", FORMATTED);
    root.write("c.php", "<?hh\nfunction f(:void{\n");
    root.write("d.txt", UNFORMATTED);
    let check = run(root.path(), &["--check-formatting", "a.php", "b.php", "c.php", "d.txt"], "");
    assert_eq!(check.status.code(), Some(0));
    assert_eq!(stdout(&check), "a.php\n");
    let err = stderr(&check);
    assert!(err.starts_with("Unexpected file extension (probably not a Hack file): d.txt\n"), "{err}");
    assert!(err.ends_with("Parse error in file: c.php\n"), "{err}");

    let inplace = run(root.path(), &["-i", "a.php", "b.php", "c.php"], "");
    assert_eq!(inplace.status.code(), Some(0));
    assert_eq!(root.read("a.php"), FORMATTED);
    assert_eq!(root.read("b.php"), FORMATTED);
    assert_eq!(root.read("c.php"), "<?hh\nfunction f(:void{\n");
}

#[test]
fn parallel_check_matches_sequential() {
    let root = TempDir::new("parallel");
    let mut files = vec![];
    for i in 0..40 {
        let name = format!("f{:02}.php", i);
        match i % 3 {
            0 => root.write(&name, UNFORMATTED),
            1 => root.write(&name, FORMATTED),
            _ => root.write(&name, "<?hh\nfunction f(:void{\n"),
        }
        files.push(name);
    }
    let mut args = vec!["--check-formatting"];
    args.extend(files.iter().map(|s| s.as_str()));
    let sequential = run(root.path(), &[&["-j", "1"], args.as_slice()].concat(), "");
    let parallel = run(root.path(), &[&["-j", "8"], args.as_slice()].concat(), "");
    assert_eq!(sequential.status.code(), parallel.status.code());
    assert_eq!(sequential.stdout, parallel.stdout);
    assert_eq!(sequential.stderr, parallel.stderr);
    assert!(stdout(&sequential).starts_with("f00.php\nf03.php\n"));
}

#[test]
fn inplace_stops_at_the_first_read_error() {
    // OCaml hackfmt only checks that the last file exists; a missing file in
    // the middle is an internal error raised when the loop gets to it, after
    // the files before it were written.
    for jobs in ["1", "4"] {
        let root = TempDir::new(&format!("stop{jobs}"));
        root.write("a.php", UNFORMATTED);
        root.write("c.php", UNFORMATTED);
        let result = run(root.path(), &["-j", jobs, "-i", "a.php", "missing.php", "c.php"], "");
        assert_eq!(result.status.code(), Some(255));
        assert_eq!(
            stderr(&result),
            "Internal Error: (Sys_error \"missing.php: No such file or directory\")\n"
        );
        assert_eq!(root.read("a.php"), FORMATTED);
        assert_eq!(root.read("c.php"), UNFORMATTED);
    }
}

#[test]
fn leading_blank_lines() {
    // Hakana's rule: a file never starts with a blank line. OCaml hackfmt
    // keeps one.
    let root = TempDir::new("blank");
    let source = "\n\nfunction f():void {}\n";
    assert_eq!(stdout(&run(root.path(), &[], source)), "function f(): void {}\n");
    assert_eq!(
        stdout(&run(root.path(), &["--hackfmt-compat"], source)),
        "\nfunction f(): void {}\n"
    );
}

#[test]
fn hakana_fixme_comments_are_ordinary_comments() {
    let root = TempDir::new("fixme");
    let source = "<?hh\nfunction f(): void {\n  /* HAKANA_FIXME[X] */\n  $x   =  1;\n  /* HH_FIXME[4110] */\n  $y   =  1;\n}\n";
    assert_eq!(
        stdout(&run(root.path(), &[], source)),
        "<?hh\nfunction f(): void {\n  /* HAKANA_FIXME[X] */\n  $x = 1;\n  /* HH_FIXME[4110] */\n  $y   =  1;\n}\n"
    );
}

#[test]
fn hhconfig_options_and_cli_overrides() {
    let root = TempDir::new("hhconfig");
    root.write(".hhconfig", "hackfmt.indent_width = 4\nhackfmt.tabs = true\n");
    root.write("a.php", UNFORMATTED);
    assert_eq!(
        stdout(&run(root.path(), &["a.php"], "")),
        "<?hh\nfunction f(): void {\n\tfoo(1, 2);\n}\n"
    );
    root.write(".hhconfig", "hackfmt.indent_width = 4\n");
    assert_eq!(
        stdout(&run(root.path(), &["a.php"], "")),
        "<?hh\nfunction f(): void {\n    foo(1, 2);\n}\n"
    );
    assert_eq!(stdout(&run(root.path(), &["a.php", "--indent-width", "3"], "")), "<?hh\nfunction f(): void {\n   foo(1, 2);\n}\n");
    root.write(".hhconfig", "hackfmt.indent_width = four\n");
    let bad = run(root.path(), &["a.php"], "");
    assert_eq!(bad.status.code(), Some(2));
    assert_eq!(
        stderr(&bad),
        "Fatal error: exception Invalid_argument(\"invalid digit found in string\")\n"
    );
}

#[test]
fn argument_errors() {
    let root = TempDir::new("args");
    let unknown = run(root.path(), &["--frobnicate"], "");
    assert_eq!(unknown.status.code(), Some(2));
    assert!(stderr(&unknown).contains(": unknown option '--frobnicate'.\nUsage: "));
    let help = run(root.path(), &["--help"], "");
    assert_eq!(help.status.code(), Some(0));
    assert!(stdout(&help).contains("\n  --range [start end]  Range of character positions"));
    let missing = run(root.path(), &["--range", "1"], "");
    assert!(stderr(&missing).contains(": option '--range' needs an argument.\n"));
    let wrong = run(root.path(), &["--at-char", "x"], "");
    assert!(stderr(&wrong).contains(": wrong argument 'x'; option '--at-char' expects an integer.\n"));
    root.write("a.php", UNFORMATTED);
    let two = run(root.path(), &["a.php", "a.php"], "");
    assert_eq!(two.status.code(), Some(3));
    assert_eq!(stderr(&two), "Invalid argument: More than one file given\n");
    let not_hack = run(root.path(), &[], "");
    assert_eq!(not_hack.status.code(), Some(0));
}

#[test]
fn ranges_and_at_char() {
    let root = TempDir::new("ranges");
    root.write("a.php", "<?hh\nfunction f():void{\nfoo(1,2);\n}\n");
    let range = run(root.path(), &["--line-range", "3", "3", "a.php"], "");
    assert_eq!(stdout(&range), "  foo(1, 2);\n");
    // The parent of the token at 29 (the first comma) is the list item `1,`.
    let at = run(root.path(), &["--at-char", "29", "a.php"], "");
    assert_eq!(stdout(&at), "24 30\nfoo(1,");
    let at = run(root.path(), &["--at-char", "32", "a.php"], "");
    assert_eq!(stdout(&at), "24 33\nfoo(1, 2);");
    let bad = run(root.path(), &["--at-char", "25", "a.php"], "");
    assert_eq!(bad.status.code(), Some(3));
    assert_eq!(
        stderr(&bad),
        "Invalid argument: Offset must point to the last character of a token\n"
    );
}

#[test]
fn diff_dry_run() {
    let root = TempDir::new("diff");
    root.write("a.php", "<?hh\nfunction f():void{\nfoo(1,2);\n}\nfunction g():void{\nbar(1,2);\n}\n");
    let diff = "--- a/a.php\n+++ b/a.php\n@@ -6,1 +6,1 @@\n-bar(1);\n+bar(1,2);\n";
    let result = run(root.path(), &["--diff-dry-run", "--root", "."], diff);
    assert_eq!(result.status.code(), Some(0), "{}", stderr(&result));
    assert_eq!(
        stdout(&result),
        "*** a.php\n<?hh\nfunction f():void{\nfoo(1,2);\n}\nfunction g():void{\n  bar(1, 2);\n}\n"
    );
    let missing = run(root.path(), &["--diff-dry-run", "--root", "."], "+++ b/nope.php\n@@ -1 +1 @@\n+x\n");
    assert_eq!(missing.status.code(), Some(4));
    assert_eq!(stderr(&missing), "Invalid diff: No such file or directory: nope.php\n");
}

#[test]
fn recursive_directories() {
    let root = TempDir::new("recursive");
    root.write("src/b.php", UNFORMATTED);
    root.write("src/a/x.hack", "function f():void{}\n");
    root.write("src/notes.txt", "hello");
    let without = run(root.path(), &["--check-formatting", "src"], "");
    assert_eq!(stdout(&without), "");
    assert_eq!(
        stderr(&without),
        "Unexpected file extension (probably not a Hack file): src\n"
    );
    let with = run(root.path(), &["--check-formatting", "--recursive", "src"], "");
    assert_eq!(stdout(&with), "src/a/x.hack\nsrc/b.php\n");
    assert_eq!(stderr(&with), "");
}
