// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the tests `test/integration_ml/ide/*.ml` (`Test.Client` of
//! `integration_test_base.ml` driving `Client_ide_daemon.Test`). Each scenario runs in a child process of the test binary (the
//! prefixes of `Relative_path` and the providers' state are per process, as
//! in the OCaml's test runner): `cargo test ... --lib client_ide_daemon::tests`.

use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

use super::test;
use super::test::Env;
use crate::client_ide_message;
use crate::client_ide_message::request;
use crate::client_ide_message::Diagnostic;
use crate::file_content;
use crate::path;
use crate::relative_path;
use crate::server_config;

const CHILD: &str = "HH_IDE_DAEMON_TEST";

/// Runs the scenario `name` in a child process; its failure (a panic) fails
/// the test, with the child's output.
fn run_in_child(name: &str) {
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["client_ide_daemon::tests::child", "--exact", "--nocapture", "--test-threads=1"])
        .env(CHILD, name)
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the scenario {name} failed:\n{stdout}\n{}",
        &stderr[stderr.len().saturating_sub(20000)..]
    );
}

/// The child process: runs the scenario named by [`CHILD`].
#[test]
fn child() {
    let Some(name) = std::env::var_os(CHILD) else {
        return;
    };
    let name = name.to_string_lossy().into_owned();
    let scenario = SCENARIOS
        .iter()
        .find(|(n, _)| *n == name)
        .unwrap_or_else(|| panic!("no scenario {name}"))
        .1;
    crate::check::run_on_large_stack("test", scenario).unwrap();
}

// ---------------------------------------------------------------------------
// Integration_test_base (the parts the IDE tests use)
// ---------------------------------------------------------------------------

/// `Test.fail`
fn fail(x: &str) -> ! {
    println!("{}", x);
    panic!("Integration_test_failure")
}

/// `Test.relativize`
fn relativize(s: &str) -> String {
    let root = relative_path::path_of_prefix(relative_path::Prefix::Root).unwrap();
    s.replace(&root, "/")
}

/// `Test.assertEqual`
fn assert_equal(expected: &str, got: &str) {
    let expected = expected.trim();
    let got = got.trim();
    if expected != got {
        fail(&format!("Expected:\n{}\n\nBut got:\n{}\n", expected, got))
    }
}

/// `Test.doc`
fn doc(suffix: &str, file_contents: &str) -> client_ide_message::Document {
    client_ide_message::Document {
        file_path: path::make(&relative_path::to_absolute(&relative_path::from_root(suffix))),
        file_contents: file_contents.to_string(),
    }
}

/// `list_to_string`
fn list_to_string(l: &[String]) -> String {
    l.iter().map(|x| format!("{}\n", x)).collect()
}

/// `Test.assert_ide_completions`
fn assert_ide_completions(response: &crate::autocomplete_types::IdeResult, expected: &[&str]) {
    let results: Vec<String> = response.completions.iter().map(|x| x.res_label.clone()).collect();
    let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
    assert_equal(&list_to_string(&expected), &list_to_string(&results));
}

type Diagnostics = std::collections::BTreeMap<String, Vec<Diagnostic>>;

/// `Test.Client`
mod client {
    use super::*;

    thread_local! {
        /// `Test_disk`: the contents written by `setup_disk`.
        static TEST_DISK: std::cell::RefCell<std::collections::HashMap<String, String>> =
            Default::default();
    }

    fn real_tempdir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().canonicalize().unwrap().join(format!(
            "hh-g1-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    pub fn with_env(custom_config: Option<server_config::T>, f: impl FnOnce(Env)) {
        let root = real_tempdir("root");
        let hhi_root = real_tempdir("hhi");
        let tmp = real_tempdir("tmp");
        let naming_sqlite = tmp.join("naming_table.sql");
        relative_path::set_path_prefix(relative_path::Prefix::Root, &root);
        relative_path::set_path_prefix(relative_path::Prefix::Hhi, &hhi_root);
        relative_path::set_path_prefix(relative_path::Prefix::Tmp, &tmp);
        let _save_result = crate::naming_sqlite::save_file_infos(
            naming_sqlite.to_str().unwrap(),
            &Default::default(),
            "",
        )
        .unwrap();
        let env = test::init(custom_config, &path::make(naming_sqlite.to_str().unwrap()));
        f(env);
        for dir in [root, hhi_root, tmp] {
            let _ = std::fs::remove_dir_all(dir);
        }
    }

    pub fn setup_disk(env: Env, files_and_contents: &[(&str, &str)]) -> Env {
        let files_and_contents: Vec<(relative_path::T, &str)> = files_and_contents
            .iter()
            .map(|(suffix, contents)| (relative_path::from_root(suffix), *contents))
            .collect();
        for (path, contents) in &files_and_contents {
            let file = relative_path::to_absolute(path);
            if let Some(dir) = std::path::Path::new(&file).parent() {
                std::fs::create_dir_all(dir).unwrap();
            }
            std::fs::write(&file, contents).unwrap();
            TEST_DISK.with_borrow_mut(|disk| disk.insert(file, contents.to_string()));
        }
        test::index(env, &files_and_contents.into_iter().map(|(p, _)| p).collect())
    }

    pub fn edit_file(env: Env, suffix: &str, contents: &str) -> (Env, Diagnostics) {
        let (env, ()) = test::handle(env, request::did_open_or_change(doc(suffix, contents)));
        let (env, diagnostics) = test::handle(env, request::diagnostics(doc(suffix, contents)));
        let diagnostics = std::iter::once((format!("/{}", suffix), diagnostics)).collect();
        (env, diagnostics)
    }

    pub fn open_file(env: Env, suffix: &str) -> (Env, Diagnostics) {
        let contents = TEST_DISK.with_borrow(|disk| {
            disk.get(&relative_path::to_absolute(&relative_path::from_root(suffix)))
                .cloned()
                .unwrap_or_else(|| panic!("Test_disk: no file {}", suffix))
        });
        edit_file(env, suffix, &contents)
    }

    pub fn close_file(env: Env, suffix: &str) -> (Env, Diagnostics) {
        let (env, diagnostics) = test::handle(
            env,
            request::did_close(path::make(&relative_path::to_absolute(&relative_path::from_root(
                suffix,
            )))),
        );
        let diagnostics = std::iter::once((format!("/{}", suffix), diagnostics)).collect();
        (env, diagnostics)
    }

    fn diagnostics_to_string(x: &Diagnostics) -> String {
        let mut buf = String::new();
        for (path, diagnostics) in x {
            buf.push_str(&format!("{}:\n", path));
            for diagnostic in diagnostics {
                // For testing we just compare the error itself. Other tests
                // exercise full diagnostics information
                buf.push_str(&format!(
                    "{}\n",
                    crate::user_diagnostic::to_string(&diagnostic.diagnostic_error)
                ));
            }
        }
        buf
    }

    pub fn assert_no_diagnostics(diagnostics: &Diagnostics) {
        let is_any = diagnostics.values().any(|d| !d.is_empty());
        if is_any {
            let diagnostics_as_string = relativize(&diagnostics_to_string(diagnostics));
            fail(&format!(
                "Did not expect to receive IDE diagnostics. Got:\n{}",
                diagnostics_as_string
            ))
        }
    }

    pub fn assert_diagnostics_string(diagnostics: &Diagnostics, expected: &str) {
        let diagnostics_as_string = relativize(&diagnostics_to_string(diagnostics));
        assert_equal(expected, &diagnostics_as_string)
    }
}

fn pos(line: isize, column: isize) -> file_content::position::T {
    file_content::position::from_one_based(line, column)
}

fn completion(env: Env, suffix: &str, contents: &str, line: isize, column: isize) -> (Env, crate::autocomplete_types::IdeResult) {
    test::handle(
        env,
        request::completion(
            doc(suffix, contents),
            pos(line, column),
            client_ide_message::CompletionRequest {
                is_manually_invoked: true,
            },
        ),
    )
}

/// `Global_options.set ~po ?allowed_fixme_codes_strict Global_options.default`
/// in `Server_config.default_config` (with `set_tc_options` and
/// `set_parser_options`).
fn custom_config(
    po: oxidized::parser_options::ParserOptions,
    allowed_fixme_codes_strict: Option<&[isize]>,
) -> server_config::T {
    let mut global_opts = oxidized::global_options::GlobalOptions::default();
    global_opts.po = po.clone();
    if let Some(codes) = allowed_fixme_codes_strict {
        global_opts.allowed_fixme_codes_strict = codes.iter().copied().collect();
    }
    let custom_config = server_config::default_config();
    let custom_config = server_config::set_tc_options(custom_config, global_opts);
    server_config::set_parser_options(custom_config, po)
}

// ---------------------------------------------------------------------------
// The scenarios
// ---------------------------------------------------------------------------

type Scenario = fn();

const SCENARIOS: &[(&str, Scenario)] = &[
    ("added_parent", test_added_parent_ide),
    ("auto_ns_aliasing", test_auto_ns_aliasing),
    ("autoclose_xhp", test_autoclose_xhp),
    ("diagnostics_in_closed_file", test_diagnostics_in_closed_file),
    ("error_pos", test_error_pos),
    ("failed_naming", test_failed_naming_ide),
    ("ide_close", test_ide_close),
    ("ide_consistency", test_ide_consistency),
    ("ide_diagnostic_subscription", test_ide_diagnostic_subscription),
    ("ide_file_sync", test_ide_file_sync),
    ("identify_symbol", test_identify_symbol),
    ("ide_parsing_errors", test_ide_parsing_errors),
    ("naming_errors", test_naming_errors),
    ("override_", test_override),
    ("union_intersection_type_hints_single_file", test_union_intersection_type_hints_single_file),
    ("remove_function", test_remove_function),
    ("remove_parent", test_remove_parent),
    ("unsaved_changes", test_unsaved_changes),
    ("service", test_service),
];

macro_rules! scenario_tests {
    ($($name:ident),*) => {
        $(
            #[test]
            fn $name() {
                run_in_child(stringify!($name))
            }
        )*
    };
}

scenario_tests!(
    added_parent,
    auto_ns_aliasing,
    autoclose_xhp,
    diagnostics_in_closed_file,
    error_pos,
    failed_naming,
    ide_close,
    ide_consistency,
    ide_diagnostic_subscription,
    ide_file_sync,
    identify_symbol,
    ide_parsing_errors,
    naming_errors,
    override_,
    union_intersection_type_hints_single_file,
    remove_function,
    remove_parent,
    unsaved_changes,
    service
);

/// test_added_parent_ide.ml
fn test_added_parent_ide() {
    let foo_name = "foo.php";
    let foo_contents = "<?hh // strict

class Foo {
  /* HH_FIXME[4110] */
  public function f() : string {
  }
}
";
    let foo_child_name = "foo_child.php";
    let foo_child_contents = "<?hh // strict

/* HH_FIXME[2049] */
/* HH_FIXME[4123] */
class FooChild extends Foo {}
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh // strict

function take_int(int $x) : void {}

function test(FooChild $foo_child) : void {
  take_int($foo_child->f());
}
";
    let bar_initial_diagnostics = "
/bar.php:
ERROR: File \"/bar.php\", line 6, characters 24-24:
No instance method `f` in `FooChild` (Typing[4053])
  File \"/bar.php\", line 5, characters 15-22:
  This is why I think it is an object of type FooChild
  File \"/foo_child.php\", line 5, characters 7-14:
  Declaration of `FooChild` is here
";
    let bar_diagnostics = "
/bar.php:
ERROR: File \"/bar.php\", line 6, characters 12-26:
Invalid argument (Typing[4110])
  File \"/bar.php\", line 3, characters 19-21:
  Expected `int`
  File \"/foo.php\", line 5, characters 25-30:
  But got `string`
";
    client::with_env(None, |env| {
        let env = client::setup_disk(
            env,
            &[(foo_name, ""), (foo_child_name, foo_child_contents), (bar_name, bar_contents)],
        );
        // At first, bar.php reports "no member f found in FooChild"
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, bar_initial_diagnostics);
        // We will define member f in Foo (the base of FooChild)
        let env = client::setup_disk(env, &[(foo_name, foo_contents)]);
        // But ClientIdeDaemon plays fast-and-lose with invalidation. It doesn't
        // flag that FooChild decl must be recomputed until we open foo_child.php.
        // And it doesn't flag that bar.php's TAST must be recomputed until
        // we close and open that file.
        let (env, _diagnostics) = client::open_file(env, foo_child_name);
        let (env, _diagnostics) = client::close_file(env, bar_name);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, bar_diagnostics);
        let _ = env;
    })
}

/// test_auto_ns_aliasing.ml
fn test_auto_ns_aliasing() {
    let foo_contents = "<?hh // strict

namespace HH\\LongName\\ShortName;

function foo() : void {}
";
    let autocomplete_contents = [
        "<?hh // strict

function testTypecheck(): void {
  ShortName\\foAUTO332;
}
",
        "<?hh

function testTypecheck(): void {
  \\ShortName\\foAUTO332;
}
",
        "<?hh // strict

function testTypecheck(): void {
  HH\\LongName\\ShortName\\foAUTO332;
}
",
        "<?hh // strict

function testTypecheck(): void {
  \\HH\\LongName\\ShortName\\foAUTO332;
}
",
        "<?hh // strict

namespace Test;

function testTypecheck(): void {
  HH\\LongName\\ShortName\\foAUTO332;
}
",
        "<?hh // strict

namespace Test;

function testTypecheck(): void {
  \\HH\\LongName\\ShortName\\foAUTO332;
}
",
        "<?hh // strict

namespace Test;

function testTypecheck(): void {
  ShortName\\foAUTO332;
}
",
        "<?hh // strict

namespace Test;

function testTypecheck(): void {
  \\ShortName\\foAUTO332;
}
",
    ];
    let po = oxidized::parser_options::ParserOptions {
        auto_namespace_map: vec![("ShortName".to_string(), "HH\\LongName\\ShortName".to_string())],
        deregister_php_stdlib: true,
        ..Default::default()
    };
    client::with_env(Some(custom_config(po, None)), |env| {
        let env = client::setup_disk(env, &[("foo.php", foo_contents)]);
        let get_name = |i: usize| format!("test{}.php", i);
        let cleaned: Vec<(String, String)> = autocomplete_contents
            .iter()
            .enumerate()
            .map(|(i, contents)| (get_name(i), contents.replace("AUTO332", "")))
            .collect();
        let files: Vec<(&str, &str)> = cleaned.iter().map(|(n, c)| (n.as_str(), c.as_str())).collect();
        let env = client::setup_disk(env, &files);
        let test_ide = |env: Env, contents: &str, i: usize, expected: &[&str]| {
            let path = format!("test{}.php", i);
            let offset = contents.find(crate::autocomplete_types::AUTOCOMPLETE_TOKEN).unwrap() as isize;
            let clean_contents = contents.replace("AUTO332", "");
            let position = file_content::offset_to_position(contents, offset);
            let (line, column) = file_content::position::line_column_one_based(&position);
            let (env, _diagnostics) = client::open_file(env, &path);
            let (env, response) = completion(env, &path, &clean_contents, line, column);
            assert_ide_completions(&response, expected);
            let _ = env;
        };
        // Note that autocomplete now hides namespaces when you've already typed them!
        // This means that all tests will simply return "foo" as long as you're in
        // the correct namespace when autocomplete is triggered.
        test_ide(env.clone(), autocomplete_contents[0], 0, &["foo"]);
        test_ide(env.clone(), autocomplete_contents[1], 1, &[]);
        test_ide(env.clone(), autocomplete_contents[2], 2, &["foo"]);
        test_ide(env.clone(), autocomplete_contents[3], 3, &["foo"]);
        test_ide(env.clone(), autocomplete_contents[4], 4, &[]);
        test_ide(env.clone(), autocomplete_contents[5], 5, &["foo"]);
        test_ide(env.clone(), autocomplete_contents[6], 6, &["foo"]);
        test_ide(env, autocomplete_contents[7], 7, &[]);
    })
}

/// test_autoclose_xhp.ml
fn test_autoclose_xhp() {
    let foo_contents = "<?hh
final class :xhp:foo extends :x:element {}
function test0(): void {
  <xhp:foo>

}
";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[("foo.php", foo_contents)]);
        let (env, response) = test::handle(env, request::auto_close(doc("foo.php", foo_contents), pos(4, 12)));
        match response {
            Some(close_tag) => assert_equal(&close_tag, "$0</xhp:foo>"),
            None => fail("Expected to insert the close tag $0</xhp:foo>"),
        }
        let _ = env;
    })
}

/// test_diagnostics_in_closed_file.ml
fn test_diagnostics_in_closed_file() {
    let foo_name = "foo.php";
    let foo_contents = |ty: &str| {
        format!(
            "<?hh // strict

/* HH_FIXME[4336] */
function foo() : {} {{
}}
",
            ty
        )
    };
    let foo_returns_int = foo_contents("int");
    let foo_returns_string = foo_contents("string");
    let bar_name = "bar.php";
    let bar_contents = "<?hh // strict


function test(): int {
  return foo();
}
";
    let bar_diagnostics = "
/bar.php:
ERROR: File \"/bar.php\", line 5, characters 10-14:
Invalid return type (Typing[4110])
  File \"/bar.php\", line 4, characters 18-20:
  Expected `int`
  File \"/foo.php\", line 4, characters 18-23:
  But got `string`
";
    let po = oxidized::parser_options::ParserOptions {
        allowed_decl_fixme_codes: [4336].into_iter().collect(),
        ..Default::default()
    };
    client::with_env(Some(custom_config(po, Some(&[4336]))), |env| {
        let env = client::setup_disk(env, &[(foo_name, &foo_returns_int), (bar_name, bar_contents)]);
        // Bar is clean with respect to foo as it is on disk
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_no_diagnostics(&diagnostics);
        // If we make an in-editor change to foo, that won't yet affect bar
        let (env, _diagnostics) = client::edit_file(env, foo_name, &foo_returns_string);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_no_diagnostics(&diagnostics);
        // If we save the changes to foo, then bar will now exhibit the error
        let env = client::setup_disk(env, &[(foo_name, &foo_returns_string)]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, bar_diagnostics);
        // And if we fix foo, then bar will now be correct again
        let env = client::setup_disk(env, &[(foo_name, &foo_returns_int)]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_error_pos.ml
fn test_error_pos() {
    let foo_name = "foo.php";
    let foo_contents = |s: &str| {
        format!(
            "<?hh // strict
{}
/* HH_FIXME[4336] */
function foo(): string {{
}}",
            s
        )
    };
    let bar_name = |i: usize| format!("bar{}.php", i);
    let bar_contents = |i: usize| {
        format!(
            "<?hh

function bar{} (): int {{
  return foo();
}}
",
            i
        )
    };
    let bar_107_name = bar_name(107);
    let bar_107_foo_line_3_diagnostics = r#"
/bar107.php:
ERROR: File "/bar107.php", line 4, characters 10-14:
Invalid return type (Typing[4110])
  File "/bar107.php", line 3, characters 21-23:
  Expected `int`
  File "/foo.php", line 4, characters 17-22:
  But got `string`
"#;
    let bar_107_foo_line_5_diagnostics = r#"
/bar107.php:
ERROR: File "/bar107.php", line 4, characters 10-14:
Invalid return type (Typing[4110])
  File "/bar107.php", line 3, characters 21-23:
  Expected `int`
  File "/foo.php", line 6, characters 17-22:
  But got `string`
"#;
    let bar_108_foo_line_5_diagnostics = r#"
/bar108.php:
ERROR: File "/bar108.php", line 4, characters 10-14:
Invalid return type (Typing[4110])
  File "/bar108.php", line 3, characters 21-23:
  Expected `int`
  File "/foo.php", line 6, characters 17-22:
  But got `string`
"#;
    let po = oxidized::parser_options::ParserOptions {
        allowed_decl_fixme_codes: [4336].into_iter().collect(),
        ..Default::default()
    };
    client::with_env(Some(custom_config(po, Some(&[4336]))), |env| {
        // 200 files with errors
        let mut disk_contents: Vec<(String, String)> = vec![(foo_name.to_string(), foo_contents(""))];
        // `create_bars acc 200` conses bar1 .. bar200 in front of foo.
        let mut bars: Vec<(String, String)> = (1..=200).map(|i| (bar_name(i), bar_contents(i))).collect();
        bars.append(&mut disk_contents);
        let disk: Vec<(&str, &str)> = bars.iter().map(|(n, c)| (n.as_str(), c.as_str())).collect();
        let env = client::setup_disk(env, &disk);
        let (env, diagnostics) = client::open_file(env, &bar_107_name);
        client::assert_diagnostics_string(&diagnostics, bar_107_foo_line_3_diagnostics);
        // Move foo 2 lines down and save to disk
        let env = client::setup_disk(env, &[(foo_name, &foo_contents("\n\n"))]);
        let (env, diagnostics) = client::open_file(env, &bar_107_name);
        client::assert_diagnostics_string(&diagnostics, bar_107_foo_line_5_diagnostics);
        let (env, diagnostics) = client::open_file(env, &bar_name(108));
        client::assert_diagnostics_string(&diagnostics, bar_108_foo_line_5_diagnostics);
        // Fix one of the errors in the editor
        let (env, diagnostics) = client::edit_file(env, &bar_107_name, "");
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_failed_naming_ide.ml
fn test_failed_naming_ide() {
    let foo1_name = "foo1.php";
    let foo2_name = "foo2.php";
    let foo_contents = "<?hh // strict

function foo() : void {}
";
    let bar_contents = "<?hh // strict
function test(): void {
  foo();
}
";
    let init_diagnostics = r#"
/foo2.php:
ERROR: File "/foo2.php", line 3, characters 10-12:
Name already bound: `foo` (Naming[2012])
  File "/foo1.php", line 3, characters 10-12:
  Previous definition is here
"#;
    client::with_env(None, |env| {
        let env = client::setup_disk(
            env,
            &[(foo1_name, foo_contents), (foo2_name, foo_contents), ("bar.php", bar_contents)],
        );
        let (env, diagnostics) = client::open_file(env, foo2_name);
        client::assert_diagnostics_string(&diagnostics, init_diagnostics);
        // Replace one of the duplicate definitions with a parsing error
        let env = client::setup_disk(env, &[(foo2_name, "<?hh // strict \n {")]);
        let (env, diagnostics) = client::open_file(env, foo2_name);
        client::assert_diagnostics_string(
            &diagnostics,
            r#"
/foo2.php:
ERROR: File "/foo2.php", line 3, characters 1-1:
A right brace `}` is expected here. (Parsing[1002])
"#,
        );
        // Remove the parsing error - there should be no errors after that
        let env = client::setup_disk(env, &[(foo2_name, "<?hh // strict")]);
        let (env, diagnostics) = client::open_file(env, foo2_name);
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_ide_close.ml
fn test_ide_close() {
    let foo_name = "foo.php";
    let foo_disk_contents = "<?hh // strict

function foo(bool $x) : void {}

function test() : void {
  foo(4);
}
";
    let foo_disk_diagnostics = "
/foo.php:
ERROR: File \"/foo.php\", line 6, characters 7-7:
Invalid argument (Typing[4110])
  File \"/foo.php\", line 3, characters 14-17:
  Expected `bool`
  File \"/foo.php\", line 6, characters 7-7:
  But got `int`
";
    let foo_ide_contents = "<?hh

{
";
    let foo_ide_diagnostics = "
/foo.php:
ERROR: File \"/foo.php\", line 3, characters 2-2:
A right brace `}` is expected here. (Parsing[1002])
";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(foo_name, foo_disk_contents)]);
        let (env, diagnostics) = client::open_file(env, foo_name);
        client::assert_diagnostics_string(&diagnostics, foo_disk_diagnostics);
        let (env, diagnostics) = client::edit_file(env, foo_name, foo_ide_contents);
        client::assert_diagnostics_string(&diagnostics, foo_ide_diagnostics);
        // Close the file and check that error lists are back to reflecting disk contents
        let (env, diagnostics) = client::close_file(env, foo_name);
        client::assert_diagnostics_string(&diagnostics, foo_disk_diagnostics);
        let _ = env;
    })
}

/// test_ide_consistency.ml
fn test_ide_consistency() {
    let foo_name = "foo.php";
    let foo_contents = "<?hh
class C {
  public function foo() {

  }
}
";
    let foo_contents_with_parse_error = "<?hh
class C {
  public function bar() {PARSE_ERROR

  }
}
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh
function test() {
  (new C())->f
}
";
    client::with_env(None, |env| {
        // Two unsaved files. Autocomplete doesn't respect other unsaved files.
        let (env, _diagnostics) = client::edit_file(env, foo_name, foo_contents);
        let (env, _diagnostics) = client::edit_file(env, bar_name, bar_contents);
        let (env, response) = completion(env, bar_name, bar_contents, 3, 15);
        assert_ide_completions(&response, &[]);
        // save one file, so the other now will respect it
        let env = client::setup_disk(env, &[(foo_name, foo_contents)]);
        let (env, response) = completion(env, bar_name, bar_contents, 3, 15);
        assert_ide_completions(&response, &["foo"]);
        // even with parse errors, it is still respected
        let env = client::setup_disk(env, &[(foo_name, foo_contents_with_parse_error)]);
        let (env, response) = completion(env, bar_name, bar_contents, 3, 15);
        assert_ide_completions(&response, &["bar"]);
        let _ = env;
    })
}

/// test_ide_diagnostic_subscription.ml (not in the dune rules of this
/// version: run all the same).
fn test_ide_diagnostic_subscription() {
    let foo_name = "foo.php";
    let foo_contents = "<?hh
{
";
    let foo_diagnostics = "
/foo.php:
ERROR: File \"/foo.php\", line 2, characters 2-2:
A right brace `}` is expected here. (Parsing[1002])";
    let foo_clear_diagnostics = "
/foo.php:
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh // strict
function test() {} // missing return type
";
    let bar_diagnostics = "
/bar.php:
ERROR: File \"/bar.php\", line 2, characters 10-13:
Was expecting a return type hint (Typing[4030])";
    client::with_env(None, |env| {
        // Initially bar.php has a single typing error on disk
        let env = client::setup_disk(env, &[(bar_name, bar_contents)]);
        // We'll find the error upon opening
        let (env, diagnostics) = client::open_file(env, bar_name);
        // Initial list of errors is pushed after subscribing
        client::assert_diagnostics_string(&diagnostics, bar_diagnostics);
        // Open and edit foo.php (different file) with errors
        let (env, diagnostics) = client::edit_file(env, foo_name, foo_contents);
        client::assert_diagnostics_string(&diagnostics, foo_diagnostics);
        // Fix the errors in file foo.php
        let (env, diagnostics) = client::edit_file(env, foo_name, "");
        client::assert_diagnostics_string(&diagnostics, foo_clear_diagnostics);
        // Change foo.php, but still no new errors
        let (env, diagnostics) = client::edit_file(env, foo_name, "<?hh\n");
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_ide_file_sync.ml
fn test_ide_file_sync() {
    let foo_name = "foo.php";
    let foo_no_errors = "<?hh
function foo() {

}
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh
function test() {
  fo
}
";
    let bar_new_contents = "<?hh
function foo2() {}
function test() {
  fo
}
";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(foo_name, foo_no_errors)]);
        // Open a new file in editor
        let (env, _diagnostics) = client::edit_file(env, bar_name, "");
        // Start typing in the new file
        let (env, _diagnostics) = client::edit_file(env, bar_name, bar_contents);
        // Request completions
        let (env, response) = completion(env, bar_name, bar_contents, 3, 5);
        assert_ide_completions(&response, &["foo"]);
        // Add a new definition to the file and save it
        let (env, _diagnostics) = client::edit_file(env, bar_name, bar_new_contents);
        let env = client::setup_disk(env, &[(bar_name, bar_new_contents)]);
        // Check that new definition is among the completions
        let (env, response) = completion(env, bar_name, bar_new_contents, 4, 5);
        assert_ide_completions(&response, &["foo", "foo2"]);
        let _ = env;
    })
}

/// test_identify_symbol.ml
fn test_identify_symbol() {
    let foo_contents = "<?hh

function foo() {

}
";
    let bar_contents = "<?hh

function test() {
  foo();
}";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[("foo.php", foo_contents)]);
        let (env, response) = test::handle(env, request::definition(doc("bar.php", bar_contents), pos(4, 4)));
        match response.as_slice() {
            [(_, def)] => {
                let string_pos = relativize(&crate::pos::string(&def.pos));
                let expected_pos = "File \"/foo.php\", line 3, characters 10-12:";
                assert_equal(expected_pos, &string_pos)
            }
            _ => fail("Expected to find exactly one definition"),
        }
        let _ = env;
    })
}

/// test_ide_parsing_errors.ml
fn test_ide_parsing_errors() {
    let foo_parent_name = "foo_parent.php";
    let foo_parent_contents1 = "<?hh // strict

class FooParent {
  public function lol() : void {}
}
";
    let foo_parent_contents2 = "<?hh // strict

class FooParent {}
";
    let foo_name = "foo.php";
    let foo_contents1 = "<?hh // strict

class Foo extends FooParent {
  public function bar() : void {
  }
}
";
    let foo_contents2 = "<?hh // strict

class Fo
";
    let foo_diagnostics = "
/foo.php:
ERROR: File \"/foo.php\", line 3, characters 9-9:
A left brace `{` is expected here. (Parsing[1002])
";
    let autocomplete_contents = "<?hh

function test(Foo $foo) {
  $foo->AUTO332
}

";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(foo_parent_name, foo_parent_contents1), (foo_name, foo_contents1)]);
        // Introduce an irrecoverable parsing error in Foo definition - if we would
        // proceed to try to redeclare foo.php, Foo will no longer exist
        let env = client::setup_disk(env, &[(foo_name, foo_contents2)]);
        let (env, diagnostics) = client::open_file(env, foo_name);
        client::assert_diagnostics_string(&diagnostics, foo_diagnostics);
        // Change the Foo parent to trigger invalidating Foo
        let env = client::setup_disk(env, &[(foo_parent_name, foo_parent_contents2)]);
        // If Foo is irrecoverable, then it shouldn't be available for completion
        let (env, _diagnostics) = client::edit_file(env, "test.php", autocomplete_contents);
        let (env, response) = completion(env, "test.php", autocomplete_contents, 4, 9);
        assert_ide_completions(&response, &[]);
        let _ = env;
    })
}

/// test_naming_errors.ml
fn test_naming_errors() {
    client::with_env(None, |env| {
        // Two bar files use `foo` which is still unbound.
        let env = client::setup_disk(
            env,
            &[
                ("bar_expects_int.php", "<?hh\nfunction bar_int(): int { return foo(); }\n"),
                ("bar_expects_null.php", "<?hh\nfunction bar_null(): null { return foo(); }\n"),
            ],
        );
        let (env, diagnostics) = client::open_file(env, "bar_expects_int.php");
        client::assert_diagnostics_string(
            &diagnostics,
            r#"
/bar_expects_int.php:
ERROR: File "/bar_expects_int.php", line 2, characters 34-36:
Unbound name: `foo` (a global function) (Naming[2049])

ERROR: File "/bar_expects_int.php", line 2, characters 34-36:
Unbound name (typing): `foo` (Typing[4107])
"#,
        );
        let (env, diagnostics) = client::open_file(env, "bar_expects_null.php");
        client::assert_diagnostics_string(
            &diagnostics,
            r#"
/bar_expects_null.php:
ERROR: File "/bar_expects_null.php", line 2, characters 36-38:
Unbound name: `foo` (a global function) (Naming[2049])

ERROR: File "/bar_expects_null.php", line 2, characters 36-38:
Unbound name (typing): `foo` (Typing[4107])
"#,
        );
        // Now create `foo` in foo_null.php which returns null.
        let env = client::setup_disk(
            env,
            &[("foo_returns_null.php", "<?hh\nfunction foo() : null { return null; }\n")],
        );
        let (env, diagnostics) = client::open_file(env, "bar_expects_int.php");
        let bar_expects_int_but_got_null = r#"
/bar_expects_int.php:
ERROR: File "/bar_expects_int.php", line 2, characters 34-38:
Invalid return type (Typing[4110])
  File "/bar_expects_int.php", line 2, characters 21-23:
  Expected `int`
  File "/foo_returns_null.php", line 2, characters 18-21:
  But got `null`
"#;
        client::assert_diagnostics_string(&diagnostics, bar_expects_int_but_got_null);
        let (env, diagnostics) = client::open_file(env, "bar_expects_null.php");
        client::assert_no_diagnostics(&diagnostics);
        // Create another `foo` in foo_returns_int.php which returns int.
        // For some reason, the foo_returns_null definition is still considered the winner.
        let env = client::setup_disk(
            env,
            &[("foo_returns_int.php", "<?hh\nfunction foo() : int { return 1; }\n")],
        );
        let (env, diagnostics) = client::open_file(env, "foo_returns_int.php");
        client::assert_diagnostics_string(&diagnostics, "/foo_returns_int.php:\n");
        let (env, diagnostics) = client::open_file(env, "foo_returns_null.php");
        client::assert_diagnostics_string(&diagnostics, "/foo_returns_null.php:\n");
        let (env, diagnostics) = client::open_file(env, "bar_expects_int.php");
        client::assert_diagnostics_string(&diagnostics, bar_expects_int_but_got_null);
        let (env, diagnostics) = client::open_file(env, "bar_expects_null.php");
        client::assert_diagnostics_string(&diagnostics, "/bar_expects_null.php:\n");
        // Erase foo_returns_null.php. Now everyone agrees that foo_returns_int.php is the winner.
        let env = client::setup_disk(env, &[("foo_returns_null.php", "")]);
        let (env, diagnostics) = client::open_file(env, "foo_returns_int.php");
        client::assert_diagnostics_string(&diagnostics, "/foo_returns_int.php:\n");
        let (env, diagnostics) = client::open_file(env, "foo_returns_null.php");
        client::assert_diagnostics_string(&diagnostics, "/foo_returns_null.php:\n");
        let (env, diagnostics) = client::open_file(env, "bar_expects_int.php");
        client::assert_diagnostics_string(&diagnostics, "/bar_expects_int.php:\n");
        let (env, diagnostics) = client::open_file(env, "bar_expects_null.php");
        client::assert_diagnostics_string(
            &diagnostics,
            r#"
/bar_expects_null.php:
ERROR: File "/bar_expects_null.php", line 2, characters 36-40:
Invalid return type (Typing[4110])
  File "/bar_expects_null.php", line 2, characters 22-25:
  Expected `null`
  File "/foo_returns_int.php", line 2, characters 18-20:
  But got `int`
"#,
        );
        let _ = env;
    })
}

/// test_override.ml
fn test_override() {
    let a_name = "A.php";
    let a_with_foo_contents = "<?hh // strict

interface A {
  public function foo(): void;
}
";
    let a_without_foo_contents = "<?hh // strict

interface A {
}
";
    let b_name = "B.php";
    let b_contents = "<?hh // strict
abstract class B implements A {}
";
    let c_name = "C.php";
    let c_contents = "<?hh // strict

class C extends B {
  <<__Override>>
  public function foo(): void {}
}
";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(a_name, a_with_foo_contents), (b_name, b_contents), (c_name, c_contents)]);
        // c has no errors
        let (env, diagnostics) = client::open_file(env, c_name);
        client::assert_no_diagnostics(&diagnostics);
        // when we edit a to cause downstream errors,
        // then c will only discover the errors after b has been touched
        let env = client::setup_disk(env, &[(a_name, a_without_foo_contents)]);
        // (The OCaml comments out the steps that produced Decl_elems_bug.)
        // edit a to fix the downstream errors
        let env = client::setup_disk(env, &[(a_name, a_with_foo_contents)]);
        let (env, _diagnostics) = client::open_file(env, c_name);
        let env = client::setup_disk(env, &[(b_name, b_contents)]);
        let (env, diagnostics) = client::open_file(env, c_name);
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_union_intersection_type_hints_single_file.ml
fn test_union_intersection_type_hints_single_file() {
    let gated_def_name = "gated_def.php";
    let gated_def_contents = "<?hh
<<file: __EnableUnstableFeatures('union_intersection_type_hints')>>

<<__GatedByFeatureFlag('union_intersection_type_hints')>>
newtype MyGated<T> = T;
";
    let use_name = "use_gated.php";
    let use_contents = "<?hh
<<file: __EnableUnstableFeatures('union_intersection_type_hints')>>

type UseGated = MyGated<int>;
";
    let po = oxidized::parser_options::ParserOptions {
        allow_unstable_features: true,
        ..Default::default()
    };
    client::with_env(Some(custom_config(po, None)), |env| {
        let env = client::setup_disk(env, &[(gated_def_name, gated_def_contents), (use_name, use_contents)]);
        // Opening the using file drives [Typing_toplevel.nast_to_tast]. Because the
        // file enables the feature, referencing the gated newtype must NOT raise
        // GatedByFeatureFlag (Typing[4509]).
        let (env, diagnostics) = client::open_file(env, use_name);
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_remove_function.ml
fn test_remove_function() {
    let foo_name = "foo.php";
    let foo_contents = "<?hh // strict

function foo() : void {}
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh // strict

function test(): void {
  foo();
}
";
    let full_diagnostics = "
/bar.php:
ERROR: File \"/bar.php\", line 4, characters 3-5:
Unbound name: `foo` (a global function) (Naming[2049])

ERROR: File \"/bar.php\", line 4, characters 3-5:
Unbound name (typing): `foo` (Typing[4107])
";
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(foo_name, foo_contents), (bar_name, bar_contents)]);
        // no diagnostics initially
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_no_diagnostics(&diagnostics);
        // Delete foo()
        let env = client::setup_disk(env, &[(foo_name, "")]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, full_diagnostics);
        let _ = env;
    })
}

/// test_remove_parent.ml
fn test_remove_parent() {
    let foo_parent_name = "foo_parent.php";
    let foo_parent_contents = "<?hh // strict

class FooParent {
  public function lol() : void {}
}
";
    let foo_name = "foo.php";
    let foo_contents = "<?hh // strict

class Foo extends FooParent {
  public function test() : void {
    $this->lol();
  }
}
";
    let foo_parent_missing_diagnostics = r#"
/foo.php:
ERROR: File "/foo.php", line 3, characters 19-27:
Unbound name: `FooParent` (an object type) (Naming[2049])

ERROR: File "/foo.php", line 5, characters 12-14:
No instance method `lol` in `Foo` (Typing[4053])
  File "/foo.php", line 4, characters 19-22:
  Did you mean `test` instead?
  File "/foo.php", line 3, characters 7-9:
  This is why I think it is an object of type Foo
  File "/foo.php", line 3, characters 7-9:
  Declaration of `Foo` is here
"#;
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(foo_parent_name, foo_parent_contents), (foo_name, foo_contents)]);
        let (env, diagnostics) = client::open_file(env, foo_name);
        client::assert_no_diagnostics(&diagnostics);
        let env = client::setup_disk(env, &[(foo_parent_name, "")]);
        let (env, diagnostics) = client::open_file(env, foo_name);
        client::assert_diagnostics_string(&diagnostics, foo_parent_missing_diagnostics);
        let env = client::setup_disk(env, &[(foo_parent_name, foo_parent_contents)]);
        let (env, diagnostics) = client::open_file(env, foo_name);
        client::assert_no_diagnostics(&diagnostics);
        let _ = env;
    })
}

/// test_unsaved_changes.ml
fn test_unsaved_changes() {
    let foo_name = "foo.php";
    let foo_takes_int_contents = "<?hh // strict

function foo(int $x) : void {}
";
    let foo_takes_string_contents = "<?hh // strict

function foo(string $x) : void {}
";
    let bar_name = "bar.php";
    let bar_contents = "<?hh // strict

function test(mixed $x): void {
  foo($x);
}
";
    let disk_diagnostics = r#"
/bar.php:
ERROR: File "/bar.php", line 4, characters 7-8:
Invalid argument (Typing[4110])
  File "/foo.php", line 3, characters 14-16:
  Expected `int`
  File "/bar.php", line 3, characters 15-19:
  But got `mixed`
"#;
    let ide_diagnostics = r#"
/bar.php:
ERROR: File "/bar.php", line 4, characters 7-8:
Invalid argument (Typing[4110])
  File "/foo.php", line 3, characters 14-19:
  Expected `string`
  File "/bar.php", line 3, characters 15-19:
  But got `mixed`
"#;
    client::with_env(None, |env| {
        let env = client::setup_disk(env, &[(bar_name, bar_contents), (foo_name, foo_takes_int_contents)]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, disk_diagnostics);
        // an unsaved foo.php doesn't affect bar.php
        let (env, _diagnostics) = client::edit_file(env, foo_name, foo_takes_string_contents);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, disk_diagnostics);
        // saving it does affect bar.php
        let env = client::setup_disk(env, &[(foo_name, foo_takes_string_contents)]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, ide_diagnostics);
        // save it back again
        let env = client::setup_disk(env, &[(foo_name, foo_takes_int_contents)]);
        let (env, diagnostics) = client::open_file(env, bar_name);
        client::assert_diagnostics_string(&diagnostics, disk_diagnostics);
        let _ = env;
    })
}

/// Not an OCaml test: the whole service (`Client_ide_service` and the daemon
/// thread), initialized on a root by building its naming table, then a few
/// requests, then a file change, then the stop.
fn test_service() {
    use crate::client_ide_service;
    let scratch = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("hh-g1-service-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&scratch);
    let root = scratch.join("root");
    let tmp = scratch.join("tmp");
    std::fs::create_dir_all(&root).unwrap();
    std::fs::create_dir_all(&tmp).unwrap();
    // (The naming-table builder reads `$HH_LOCALCONF_PATH/hh.conf`, else
    // `/etc/hh.conf`, and fails without one: as the OCaml's does.)
    std::fs::write(tmp.join("hh.conf"), "").unwrap();
    // SAFETY: the child process is single-threaded at this point.
    unsafe {
        std::env::set_var("HH_TMPDIR", &tmp);
        std::env::set_var("HH_LOCALCONF_PATH", &tmp);
    }
    std::fs::write(root.join(".hhconfig"), "").unwrap();
    std::fs::write(
        root.join("a.php"),
        "<?hh\n/** Docs of A. */\nclass A {\n  public function f(): int { return 1; }\n}\n",
    )
    .unwrap();
    let b = "<?hh\nfunction b(A $a): string {\n  return $a->f();\n}\n";
    std::fs::write(root.join("b.php"), b).unwrap();
    let root_s = root.to_str().unwrap().to_string();
    relative_path::set_path_prefix(relative_path::Prefix::Root, &root);
    let lsp_log = tmp.join("lsp.log");
    let t = client_ide_service::make(client_ide_message::DaemonArgs {
        init_id: "test".to_string(),
        verbose_to_stderr: false,
        verbose_to_file: false,
        client_lsp_log_fn: lsp_log.to_str().unwrap().to_string(),
        error_filter: crate::filter_diagnostics::filter::make(true, vec![], vec![]),
    });
    client_ide_service::initialize_from_saved_state(&t, root_s.clone(), None, None, vec![], false, vec![])
        .unwrap();
    let serve = {
        let t = t.clone();
        std::thread::spawn(move || client_ide_service::serve(&t))
    };
    // Done_init
    let notifications = client_ide_service::get_notifications(&t);
    match crate::lwt_message_queue::pop(&notifications) {
        Some(client_ide_message::Notification::DoneInit(Ok(()))) => {}
        other => panic!("expected Done_init(Ok), got {:?}", other),
    }
    assert!(matches!(client_ide_service::get_status(&t), client_ide_service::status::T::Ready));
    let document = client_ide_message::Document {
        file_path: format!("{}/b.php", root_s),
        file_contents: b.to_string(),
    };
    let mut unblocked = 0.;
    let mut progress = || {};
    let () = client_ide_service::rpc(
        &t,
        "1",
        &mut unblocked,
        &mut progress,
        request::did_open_or_change(document.clone()),
    )
    .unwrap();
    let diagnostics = client_ide_service::rpc(&t, "2", &mut unblocked, &mut progress, request::diagnostics(document.clone()))
        .unwrap();
    let texts: Vec<String> = diagnostics
        .iter()
        .map(|d| relativize(&crate::user_diagnostic::to_string(&d.diagnostic_error)))
        .collect();
    assert_eq!(texts.len(), 1, "{:?}", texts);
    assert!(texts[0].contains("Invalid return type (Typing[4110])"), "{:?}", texts);
    let hover = client_ide_service::rpc(&t, "3", &mut unblocked, &mut progress, request::hover(document.clone(), pos(3, 14)))
        .unwrap();
    let hover = crate::hover_service::as_marked_string_list(&hover);
    assert!(format!("{:?}", hover).contains("public function f(): int"), "{:?}", hover);
    let definition = client_ide_service::rpc(&t, "4", &mut unblocked, &mut progress, request::definition(document.clone(), pos(2, 13)))
        .unwrap();
    assert_eq!(definition.len(), 1);
    assert!(crate::pos::string(&definition[0].1.pos).contains("a.php\", line 3, characters 7-7"));
    let symbols = client_ide_service::rpc(&t, "5", &mut unblocked, &mut progress, request::workspace_symbol("b".to_string()))
        .unwrap();
    assert!(!symbols.is_empty());
    // a.php changes on disk: f now returns a string.
    std::fs::write(
        root.join("a.php"),
        "<?hh\nclass A {\n  public function f(): string { return 's'; }\n}\n",
    )
    .unwrap();
    let () = client_ide_service::rpc(
        &t,
        "6",
        &mut unblocked,
        &mut progress,
        request::did_change_watched_files(std::iter::once(relative_path::from_root("a.php")).collect()),
    )
    .unwrap();
    let diagnostics = client_ide_service::rpc(&t, "7", &mut unblocked, &mut progress, request::diagnostics(document.clone()))
        .unwrap();
    assert!(diagnostics.is_empty(), "{:?}", diagnostics.len());
    // A request the daemon cannot serve before its init would have been
    // `RequestCancelled`; after the stop, every rpc fails.
    client_ide_service::stop(&t, "8", client_ide_service::stop_reason::T::Testing, None);
    assert!(matches!(client_ide_service::get_status(&t), client_ide_service::status::T::Stopped(_)));
    let r = client_ide_service::rpc(&t, "9", &mut unblocked, &mut progress, request::hover(document, pos(3, 14)));
    assert!(r.is_err());
    serve.join().unwrap();
    // The daemon's log, and the naming table it built.
    let ide_log = std::fs::read_to_string(crate::server_files::client_ide_log(&root_s)).unwrap();
    for line in [
        "[ide-daemon] Starting client IDE service at ",
        "[ide-daemon] Extracted hhi files to directory ",
        "Init: lsp skipped - no naming_table_load_info",
        "Init: find error -  - {\"stack\":",
        "Init: fetch error -  - {\"stack\":",
        "Init: build?",
        "[ide-daemon] Finished saved state initialization. State: ",
        "Init: build ok, at ",
        "Loading naming table from SQLite...",
        "[ide-incremental] Batch change 0 files, e.g. [none]",
        "[ide-incremental] Batch change 1 files, e.g. a.php",
        "[ide-daemon] Removing hhi directory ",
        "SERVERLESS_IDE_DONE(ok)",
    ] {
        assert!(ide_log.contains(line), "no line {:?} in\n{}", line, ide_log);
    }
    assert!(std::path::Path::new(&crate::server_files::client_ide_naming_table(&root_s)).exists());
    let _ = std::fs::remove_dir_all(&scratch);
}

/// Not a test of the suite: the comparison with the OCaml `hh_client lsp`.
/// Runs the service on `$HH_IDE_DAEMON_CMP_ROOT`, answers the queries of
/// `$HH_IDE_DAEMON_CMP_QUERIES` (one JSON query per line) and writes a normalized
/// form of each answer to `$HH_IDE_DAEMON_CMP_OUT`, to be compared with the OCaml's
/// LSP answers normalized the same way. The conversions to LSP are those of
/// `client_lsp.ml`, in the normalized form only.
#[test]
#[ignore]
fn compare() {
    crate::check::run_on_large_stack("compare", compare_).unwrap();
}

fn compare_() {
    use serde_json::json;
    use serde_json::Value;

    use crate::client_ide_service;
    let root = std::env::var("HH_IDE_DAEMON_CMP_ROOT").unwrap();
    let queries = std::fs::read_to_string(std::env::var("HH_IDE_DAEMON_CMP_QUERIES").unwrap()).unwrap();
    let out_path = std::env::var("HH_IDE_DAEMON_CMP_OUT").unwrap();
    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(&root));
    let t0 = std::time::Instant::now();
    // `Client_lsp`'s error filter.
    let (config, local_config) = server_config::load(true, "", &[]).unwrap();
    let error_filter = crate::filter_diagnostics::filter::make(
        local_config.warnings_default_all,
        server_config::warnings_generated_files(&config)
            .iter()
            .map(|s| crate::rt::ocaml_str::regexp(s).ok().unwrap())
            .collect(),
        vec![],
    );
    let t = client_ide_service::make(client_ide_message::DaemonArgs {
        init_id: "cmp".to_string(),
        verbose_to_stderr: false,
        verbose_to_file: false,
        client_lsp_log_fn: format!("{}.lsp_log", out_path),
        error_filter,
    });
    client_ide_service::initialize_from_saved_state(&t, root.clone(), None, None, vec![], false, vec![]).unwrap();
    let serve = {
        let t = t.clone();
        std::thread::spawn(move || client_ide_service::serve(&t))
    };
    match crate::lwt_message_queue::pop(&client_ide_service::get_notifications(&t)) {
        Some(client_ide_message::Notification::DoneInit(Ok(()))) => {}
        other => panic!("init: {:?}", other),
    }
    eprintln!("init took {:.1}s", t0.elapsed().as_secs_f64());
    let rss = || -> u64 {
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
        usage.ru_maxrss as u64
    };
    eprintln!("max rss after init: {} MB", rss() / (1 << 20));
    let range = |r: &crate::lsp::Range| json!([r.start.line, r.start.character, r.end_.line, r.end_.character]);
    let pos_range = |p: &crate::pos::Absolute| range(&crate::lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, p));
    let mut out = std::fs::File::create(&out_path).unwrap();
    let mut unblocked = 0.;
    let mut progress = || {};
    let mut opened: Option<String> = None;
    let mut document = None;
    let mut id = 0;
    for line in queries.lines() {
        let q: Value = serde_json::from_str(line).unwrap();
        let file = q["file"].as_str().unwrap().to_string();
        let mut next_id = || {
            id += 1;
            id.to_string()
        };
        if opened.as_deref() != Some(&file) {
            if let Some(prev) = &opened {
                let _ = client_ide_service::rpc(&t, &next_id(), &mut unblocked, &mut progress, request::did_close(prev.clone()));
            }
            let text = String::from_utf8_lossy(&std::fs::read(&file).unwrap()).into_owned();
            let d = client_ide_message::Document {
                file_path: file.clone(),
                file_contents: text,
            };
            let () = client_ide_service::rpc(&t, &next_id(), &mut unblocked, &mut progress, request::did_open_or_change(d.clone()))
                .unwrap();
            document = Some(d);
            opened = Some(file.clone());
        }
        let mut d = document.clone().unwrap();
        // The query's edit (didChange in the OCaml driver), undone after it.
        let edited = if let Some(append) = q["append"].as_str() {
            Some(format!("{}{}", d.file_contents, append))
        } else if let Some(del) = q["delete"].as_array() {
            let (a, b) = (del[0].as_u64().unwrap() as usize, del[1].as_u64().unwrap() as usize);
            let ln = q["line"].as_u64().unwrap() as usize;
            let mut lines: Vec<String> = d.file_contents.split('\n').map(|s| s.to_string()).collect();
            let l: Vec<char> = lines[ln].chars().collect();
            lines[ln] = l[..a].iter().chain(l[b..].iter()).collect();
            Some(lines.join("\n"))
        } else {
            None
        };
        if let Some(text) = &edited {
            d.file_contents = text.clone();
            let () = client_ide_service::rpc(&t, &next_id(), &mut unblocked, &mut progress, request::did_open_or_change(d.clone()))
                .unwrap();
        }
        // LSP positions are 0-based.
        let p = file_content::position::from_zero_based(
            q["line"].as_i64().unwrap_or(0) as isize,
            q["character"].as_i64().unwrap_or(0) as isize,
        );
        let start = std::time::Instant::now();
        let kind = q["kind"].as_str().unwrap();
        macro_rules! rpc {
            ($r:expr) => {
                client_ide_service::rpc(&t, &next_id(), &mut unblocked, &mut progress, $r)
            };
        }
        let result: Result<Value, crate::lsp::error::T> = match kind {
            "diagnostics" => rpc!(request::diagnostics(d.clone())).map(|ds| {
                let mut v = vec![];
                for diag in &ds {
                    let e = &diag.diagnostic_error;
                    let msgs: Vec<(crate::pos::Absolute, String)> = crate::user_diagnostic::to_list(e)
                        .into_iter()
                        .map(|oxidized::message::Message(p, m)| {
                            (p, crate::markdown_lite::render(None, None, &String::from_utf8_lossy(&m)))
                        })
                        .collect();
                    let (first, rest) = msgs.split_first().unwrap();
                    let mut related: Vec<Value> = rest
                        .iter()
                        .map(|(p, m)| json!([crate::pos::filename(p), pos_range(p), m]))
                        .collect();
                    for m in &e.custom_msgs {
                        related.push(json!([crate::pos::filename(&first.0), pos_range(&first.0), crate::markdown_lite::render(None, None, m)]));
                    }
                    let sev = match e.severity {
                        crate::user_diagnostic::Severity::Err => 1,
                        _ => 2,
                    };
                    v.push(json!([pos_range(&first.0), e.code, sev, first.1, related]));
                    for h in &diag.diagnostic_related_hints {
                        v.push(json!([pos_range(h), e.code, 4, first.1, related]));
                    }
                }
                Value::Array(v)
            }),
            "documentSymbol" => rpc!(request::document_symbol(d.clone())).map(|outline| {
                use crate::symbol_definition::ClassishKind;
                use crate::symbol_definition::Kind;
                use crate::symbol_definition::MemberKind;
                fn go(defs: &[crate::symbol_definition::T<crate::pos::Absolute>], container: Option<&str>, acc: &mut Vec<Value>, file: &str) {
                    for def in defs {
                        let kind = match &def.kind {
                            Kind::Function => 12,
                            Kind::Classish { classish_kind: ClassishKind::Class, .. } => 5,
                            Kind::Member { member_kind, .. } => match member_kind {
                                MemberKind::Method => 6,
                                MemberKind::Property => 7,
                                MemberKind::ClassConst => 14,
                                MemberKind::TypeConst => 5,
                            },
                            Kind::GlobalConst => 14,
                            Kind::Classish { classish_kind: ClassishKind::Enum, .. } => 10,
                            Kind::Classish { .. } => 11,
                            Kind::LocalVar | Kind::Param => 13,
                            Kind::TypeVar => 26,
                            Kind::Typedef => 5,
                            Kind::Module => 2,
                        };
                        let pos = if crate::pos::start_offset(&def.pos) < crate::pos::start_offset(&def.span) {
                            def.span.clone()
                        } else {
                            crate::pos::to_absolute(&crate::pos::btw(
                                &crate::pos::to_relative(&def.pos),
                                &crate::pos::to_relative(&def.span),
                            ))
                        };
                        let r = crate::lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, &pos);
                        let f = crate::pos::filename(&pos);
                        acc.push(json!([
                            def.name,
                            kind,
                            if f.is_empty() { file.to_string() } else { f },
                            [r.start.line, r.start.character, r.end_.line, r.end_.character],
                            container,
                            def.detail
                        ]));
                        if let Kind::Classish { members, .. } = &def.kind {
                            go(members, Some(&def.name), acc, file);
                        }
                    }
                }
                // `lsp_document_symbols_of_outline ~filename ~accu:[] ~container_name:None`,
                // exactly (each end of a list reverses the accumulator).
                fn lsp_document_symbols_of_outline(
                    file: &str,
                    mut accu: Vec<Value>,
                    container: Option<&str>,
                    defs: &[crate::symbol_definition::T<crate::pos::Absolute>],
                ) -> Vec<Value> {
                    match defs.split_first() {
                        None => {
                            accu.reverse();
                            accu
                        }
                        Some((def, defs)) => {
                            let mut one = vec![];
                            go(std::slice::from_ref(def), container, &mut one, file);
                            // (`go` also adds the children: keep the def only.)
                            accu.insert(0, one.swap_remove(0));
                            let children: &[_] = match &def.kind {
                                Kind::Classish { members, .. } => members,
                                _ => &[],
                            };
                            let accu = lsp_document_symbols_of_outline(file, accu, Some(&def.name), children);
                            lsp_document_symbols_of_outline(file, accu, container, defs)
                        }
                    }
                }
                Value::Array(lsp_document_symbols_of_outline(&file, vec![], None, &outline))
            }),
            "hover" => rpc!(request::hover(d.clone(), p)).map(|infos| {
                let contents = crate::hover_service::as_marked_string_list(&infos);
                if contents.is_empty() {
                    Value::Null
                } else {
                    let range = infos.iter().find_map(|i| i.pos.clone()).map(|p| {
                        range(&crate::lsp_helpers::hack_pos_to_lsp_range(|a: &relative_path::T, b: &relative_path::T| a == b, &p))
                    });
                    let contents: Vec<Value> = contents
                        .iter()
                        .map(|m| match m {
                            crate::lsp::MarkedString::MarkedString(s) => json!(s),
                            crate::lsp::MarkedString::MarkedCode(l, v) => json!([l, v]),
                        })
                        .collect();
                    json!({"contents": contents, "range": range})
                }
            }),
            "definition" => rpc!(request::definition(d.clone(), p)).map(|results| {
                Value::Array(
                    results
                        .iter()
                        .map(|(_, def)| {
                            let f = crate::pos::filename(&def.pos);
                            json!([
                                if f.is_empty() { file.clone() } else { f },
                                pos_range(&def.pos),
                                crate::utils::strip_ns(&crate::symbol_definition::full_name(def))
                            ])
                        })
                        .collect(),
                )
            }),
            "highlight" => rpc!(request::document_highlight(d.clone(), p)).map(|ranges| {
                Value::Array(
                    ranges
                        .iter()
                        .map(|r| {
                            let (sl, sc) = file_content::position::line_column_zero_based(&r.st);
                            let (el, ec) = file_content::position::line_column_zero_based(&r.ed);
                            json!([sl, sc, el, ec])
                        })
                        .collect(),
                )
            }),
            "completion" => rpc!(request::completion(
                d.clone(),
                p,
                client_ide_message::CompletionRequest {
                    is_manually_invoked: true
                }
            ))
            .map(|r| {
                json!({
                    "isIncomplete": !r.is_complete,
                    "items": r.completions.iter().map(|c| json!([
                        c.res_label,
                        c.res_detail,
                        crate::autocomplete_types::sort_text(c)
                    ])).collect::<Vec<_>>()
                })
            }),
            "signatureHelp" => rpc!(request::signature_help(d.clone(), p)).map(|r| {
                serde_json::from_str(&crate::yojson::safe::to_string(&crate::lsp_fmt::print_signature_help(&r))).unwrap()
            }),
            k => panic!("{}", k),
        };
        if edited.is_some() {
            let original = document.clone().unwrap();
            let () = client_ide_service::rpc(&t, &next_id(), &mut unblocked, &mut progress, request::did_open_or_change(original))
                .unwrap();
        }
        let (result, error) = match result {
            Ok(v) => (v, Value::Null),
            Err(e) => (Value::Null, json!({"code": format!("{:?}", e.code), "message": e.message})),
        };
        use std::io::Write;
        writeln!(
            out,
            "{}",
            json!({"q": q, "result": result, "error": error, "secs": start.elapsed().as_secs_f64()})
        )
        .unwrap();
    }
    eprintln!("max rss at the end: {} MB", rss() / (1 << 20));
    client_ide_service::stop(&t, "stop", client_ide_service::stop_reason::T::Testing, None);
    serve.join().unwrap();
}

/// `Exception.get_ctor_string` of `Outfd_write_error`, as `handle_messages`
/// logs it.
#[test]
fn outfd_write_error_ctor_string() {
    let payload: Box<dyn std::any::Any + Send> =
        Box::new(super::OutfdWriteError("write".to_string(), "".to_string()));
    let e = crate::exception::wrap(payload);
    assert_eq!(
        crate::client_ide_utils::ctor_string(&e),
        r#"Client_ide_daemon.Outfd_write_error("write", "")"#
    );
}
