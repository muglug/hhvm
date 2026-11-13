// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The errors file: the golden files of the OCaml server
//! (`rt/ocaml_marshal/fixtures`), and the scenarios of
//! `test/integration_ml/server_progress_tests.ml` (`test_errors_complete`,
//! `test_errors_during`, `test_errors_kill`, `test_errors_existing`) played
//! on the writer and reader of this module, with the readers'
//! `Server_progress_lwt` stream and the `expect_qitem` strings of
//! `server_progress_test_helpers.ml`.

use std::sync::Arc;
use std::time::Duration;

use oxidized::explanation::Elem;
use oxidized::explanation::Explanation;
use oxidized::message::Message as DiagMessage;
use oxidized::pos::Pos;
use oxidized::quickfix::Edits;
use oxidized::quickfix::HintStyle;
use oxidized::quickfix::Quickfix;

use super::*;
use crate::pos::APos;
use crate::rt::ocaml_marshal::Value;
use crate::rt::ocaml_marshal::tests::GOLDEN_ERRORS_FILES;
use crate::rt::ocaml_marshal::tests::errors_file_payloads;
use crate::server_progress_lwt;
use crate::server_progress_lwt::WatchError;

/// The tests share the root, the write state and the temporary directory
/// (with the other tests of the module).
fn serial() -> MutexGuard<'static, ()> {
    super::tests::serial()
}

fn golden(name: &str) -> &'static [u8] {
    GOLDEN_ERRORS_FILES.iter().find(|(n, _)| *n == name).unwrap().1
}

fn golden_messages(name: &str) -> Vec<(Value, errors_file::Message)> {
    errors_file_payloads(golden(name))
        .into_iter()
        .map(|p| {
            let v = ocaml_marshal::from_bytes(p, 0).unwrap();
            let m = codec::message_of_ocaml(&v).unwrap();
            (v, m)
        })
        .collect()
}

/// `show_errors` of `server_progress_test_helpers.ml`
fn show_errors(errors: &relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>>) -> String {
    let counts: Vec<String> = errors
        .iter()
        .map(|(path, errors)| format!("{}={}", relative_path::suffix(path), errors.len()))
        .collect();
    format!("Errors [{}]", counts.join(","))
}

/// `show_read_result`
fn show_read_result(r: &errors_read::ReadResult) -> String {
    match r {
        errors_read::ReadResult::RCompleted(completion, msg) => {
            format!("{} [{}]", completion_reason_short_description(completion), msg)
        }
        errors_read::ReadResult::RItem(ErrorsFileItem::Errors { errors, .. }) => show_errors(errors),
        errors_read::ReadResult::RItem(ErrorsFileItem::Telemetry(t)) => {
            let key = match telemetry::to_yojson(t) {
                yojson::T::Assoc(elems) => {
                    let mut keys: Vec<String> = elems.into_iter().map(|(k, _)| k).collect();
                    keys.sort();
                    keys.into_iter().next().unwrap_or_else(|| "[]".to_string())
                }
                _ => "[primitive]".to_string(),
            };
            format!("Telemetry [{}]", key)
        }
    }
}

/// `expect_qitem`: what the stream gives within `delay`, as a string.
fn qitem(
    q: &std::sync::mpsc::Receiver<Result<errors_read::ReadResult, WatchError>>,
    delay: Duration,
) -> String {
    match q.recv_timeout(delay) {
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => "nothing".to_string(),
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => "closed".to_string(),
        Ok(Err(e)) => server_progress_lwt::watch_error_short_description(&e).to_string(),
        Ok(Ok(r)) => show_read_result(&r),
    }
}

fn expect_qitems(
    q: &std::sync::mpsc::Receiver<Result<errors_read::ReadResult, WatchError>>,
    expected: &[&str],
) {
    for e in expected {
        let delay = if *e == "nothing" { 1 } else { 10 };
        assert_eq!(qitem(q, Duration::from_secs(delay)), *e);
    }
}

// ~~ The golden files of the OCaml server ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Every message decodes to the typed messages, and the typed messages
/// encode to the OCaml's bytes but for the sharing (see [`codec`]).
#[test]
fn golden_messages_decode_and_encode() {
    for (name, file) in GOLDEN_ERRORS_FILES {
        for (i, p) in errors_file_payloads(file).into_iter().enumerate() {
            let v = ocaml_marshal::from_bytes(p, 0).unwrap();
            let m = codec::message_of_ocaml(&v)
                .unwrap_or_else(|e| panic!("{} message {}: {}", name, i, e));
            let ours = errors_file::marshal(&m);
            let theirs = ocaml_marshal::to_bytes(&v.unshare(), &[]).unwrap();
            assert!(ours == theirs, "{} message {}: {:?}", name, i, m);
            assert_eq!(errors_file::unmarshal(&ours), m);
        }
    }
}

fn kinds(name: &str) -> Vec<String> {
    golden_messages(name)
        .into_iter()
        .map(|(_, m)| match m {
            errors_file::Message::VersionHeader { .. } => "VersionHeader".to_string(),
            errors_file::Message::Header { clock, .. } => {
                format!("Header {}", if clock.is_some() { "clock" } else { "noclock" })
            }
            errors_file::Message::Item(item) => {
                show_read_result(&errors_read::ReadResult::RItem(item))
            }
            errors_file::Message::End {
                reason,
                log_message,
                ..
            } => show_read_result(&errors_read::ReadResult::RCompleted(reason, log_message)),
        })
        .collect()
}

#[test]
fn golden_message_sequences() {
    let header = ["VersionHeader", "Header clock"];
    let telemetry = [
        "Telemetry [to_recheck_count]",
        "Telemetry [will_use_distc]",
        "Telemetry [process_in_parallel]",
    ];
    let seq = |rest: &[&str]| -> Vec<String> {
        header
            .iter()
            .chain(telemetry.iter())
            .chain(rest.iter())
            .map(|s| s.to_string())
            .collect()
    };
    assert_eq!(
        kinds("r1"),
        seq(&["Errors [a.php=2,b.php=1,w.php=1]", "typecheck completed [complete]"])
    );
    assert_eq!(
        kinds("r3_stopped"),
        seq(&["Errors [b.php=1]", "hh_server gracefully stopped [unlink]"])
    );
    let r4 = kinds("r4_restarted");
    assert_eq!(r4[..5], seq(&[])[..]);
    assert_eq!(r4.last().unwrap(), "typecheck restarted due to file changes [new_empty_file]");
    match &golden_messages("r4_restarted").last().unwrap().1 {
        errors_file::Message::End {
            reason: CompletionReason::Restarted { user_message, .. },
            ..
        } => assert!(user_message.starts_with("Files have changed on disk! ["), "{}", user_message),
        m => panic!("{:?}", m),
    }
    assert_eq!(kinds("r4_second")[..2], header.map(|s| s.to_string())[..]);
    // The version is the oracle's build revision, the command line its own.
    match &golden_messages("r1")[..2] {
        [
            (_, errors_file::Message::VersionHeader { version, extra }),
            (_, errors_file::Message::Header { cmdline, clock, .. }),
        ] => {
            assert_eq!(version.len(), 40);
            assert_eq!(*extra, yojson::T::Assoc(vec![]));
            assert!(cmdline.ends_with(" Server_main.daemon_main "), "{}", cmdline);
            assert!(matches!(clock, Some(server_notifier_types::Clock::Watchman(_))));
        }
        _ => panic!(),
    }
}

/// The positions of the golden files are `Pos_tiny`; the others decode and
/// encode as OCaml's `Pos.compress` makes them.
#[test]
fn positions() {
    use oxidized::file_pos_large::FilePosLarge;
    let check = |start: (usize, usize, usize), end: (usize, usize, usize), ctor: u8| {
        let p = crate::pos::make_absolute(
            "/a.php".to_string(),
            FilePosLarge::from_lnum_bol_offset(start.0, start.1, start.2),
            FilePosLarge::from_lnum_bol_offset(end.0, end.1, end.2),
        );
        let v = codec::pos(&p);
        assert_eq!(v.as_block().unwrap().0, ctor, "{:?} {:?}", start, end);
        let back = codec::pos_of_ocaml(&v).unwrap();
        assert!(crate::pos::equal_absolute(&p, &back));
        assert_eq!(back.raw_span(), p.raw_span());
    };
    // On one line, short: tiny.
    check((3, 10, 15), (3, 10, 20), 2);
    // Two lines: small.
    check((3, 10, 15), (4, 30, 31), 0);
    // A column past 511 on two lines: large.
    check((3, 10, 600), (4, 700, 701), 1);
    // Wider than 63 characters on a line: small.
    check((1, 0, 0), (1, 0, 100), 0);
    // The dummy position.
    let dummy = crate::pos::make_absolute(
        "".to_string(),
        FilePosLarge::make_dummy(),
        FilePosLarge::make_dummy(),
    );
    let v = codec::pos(&dummy);
    assert_eq!(v.fields(2, 2).unwrap()[1].as_int().unwrap(), -1);
    assert!(codec::pos_of_ocaml(&v).unwrap().raw_span().start.is_dummy());
}

// ~~ The writer against the OCaml's output ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The relative diagnostic that `to_absolute` turns into `d` (the files
/// being under `root`).
fn to_relative(d: &FinalizedDiagnostic, root: &str) -> diagnostics_state::Diagnostic {
    let pos = |p: &Absolute| -> Pos {
        let file = p.pos_file();
        let suffix = file.strip_prefix(root).unwrap_or_else(|| panic!("{} not in {}", file, root));
        Pos::from_raw_span(
            Arc::new(relative_path::T::make(
                relative_path::Prefix::Root,
                std::path::PathBuf::from(suffix),
            )),
            p.raw_span(),
        )
    };
    let pod = |p: &Absolute| crate::pos_or_decl::of_raw_pos(pos(p));
    let cpos = |c: &oxidized::classish_positions_types::Pos<Absolute>| {
        use oxidized::classish_positions_types::Pos as C;
        match c {
            C::Precomputed(p) => C::Precomputed(pos(p)),
            C::ClassishEndOfBody(s) => C::ClassishEndOfBody(s.clone()),
            C::ClassishStartOfBody(s) => C::ClassishStartOfBody(s.clone()),
            C::ClassishClosingBrace(s) => C::ClassishClosingBrace(s.clone()),
        }
    };
    user_diagnostic::UserDiagnostic {
        severity: d.severity,
        code: d.code,
        claim: DiagMessage(pos(&d.claim.0), d.claim.1.clone()),
        reasons: d.reasons.iter().map(|m| DiagMessage(pod(&m.0), m.1.clone())).collect(),
        explanation: match &d.explanation {
            Explanation::Derivation(elems) => Explanation::Derivation(
                elems
                    .iter()
                    .map(|e| match e {
                        Elem::Witness(p, s) => Elem::Witness(pod(p), s.clone()),
                        Elem::WitnessNoPos(s) => Elem::WitnessNoPos(s.clone()),
                        Elem::Rule(s) => Elem::Rule(s.clone()),
                        Elem::Step(s, b) => Elem::Step(s.clone(), *b),
                        Elem::Trans(s) => Elem::Trans(s.clone()),
                        Elem::Prefix { prefix, sep } => Elem::Prefix {
                            prefix: prefix.clone(),
                            sep: sep.clone(),
                        },
                        Elem::Suffix { suffix, sep } => Elem::Suffix {
                            suffix: suffix.clone(),
                            sep: sep.clone(),
                        },
                    })
                    .collect(),
            ),
            Explanation::Debug(s) => Explanation::Debug(s.clone()),
            Explanation::Empty => Explanation::Empty,
        },
        quickfixes: d
            .quickfixes
            .iter()
            .map(|q| Quickfix {
                title: q.title.clone(),
                edits: match &q.edits {
                    Edits::Eager(l) => Edits::Eager(l.iter().map(|(s, p)| (s.clone(), pos(p))).collect()),
                    Edits::ClassishEnd { new_text, name } => Edits::ClassishEnd {
                        new_text: new_text.clone(),
                        name: name.clone(),
                    },
                    Edits::AddFunctionAttribute {
                        function_pos,
                        attribute_name,
                    } => Edits::AddFunctionAttribute {
                        function_pos: pos(function_pos),
                        attribute_name: attribute_name.clone(),
                    },
                },
                hint_styles: q
                    .hint_styles
                    .iter()
                    .map(|h| match h {
                        HintStyle::HintStyleSilent(c) => HintStyle::HintStyleSilent(cpos(c)),
                        HintStyle::HintStyleHint(c) => HintStyle::HintStyleHint(cpos(c)),
                    })
                    .collect(),
            })
            .collect(),
        custom_msgs: d.custom_msgs.clone(),
        is_fixmed: d.is_fixmed,
        function_pos: d.function_pos.as_ref().map(pos),
    }
}

/// A root of its own, and its errors file (removed).
fn set_test_root(root: &str) -> String {
    crate::server_files::tests::testing_tmp();
    set_root(root.to_string());
    enable_error_production(true);
    let file = errors_file_path().unwrap();
    let _ = std::fs::remove_file(&file);
    file
}

/// The messages of an errors file written here.
fn read_all(file: &str) -> Vec<errors_file::Message> {
    errors_file_payloads(&std::fs::read(file).unwrap())
        .into_iter()
        .map(errors_file::unmarshal)
        .collect()
}

/// `report` of the relative diagnostics behind the OCaml's report writes
/// the OCaml's `Errors` item (the hashes included), but for the timestamp
/// and the sharing.
#[test]
fn report_writes_what_ocaml_writes() {
    let _serial = serial();
    for (name, root) in [("r1", "/private/tmp/hh-incr/err/r1/"), ("r2", "/private/tmp/hh-incr/err/r2/")] {
        let item = golden_messages(name)
            .into_iter()
            .find_map(|(_, m)| match m {
                errors_file::Message::Item(ErrorsFileItem::Errors { errors, timestamp }) => {
                    Some((errors, timestamp))
                }
                _ => None,
            })
            .unwrap();
        let (errors, _) = item;
        relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(root));
        let mut diagnostics = diagnostics_state::T::new();
        for (path, errs) in errors.iter() {
            // A fixmed copy of the first error, which `report` drops.
            let mut ds: Vec<_> = errs.iter().map(|(d, _)| to_relative(d, root)).collect();
            let mut fixmed = ds[0].clone();
            fixmed.is_fixmed = true;
            ds.insert(0, fixmed);
            // Reversed: `report` sorts.
            ds.reverse();
            diagnostics.insert(path.clone(), ds);
        }
        let file = set_test_root(&format!("/nonexistent/hh_errors_report_test/{}", name));
        errors_write::new_empty_file(None, true, ("u".to_string(), "l".to_string()));
        errors_write::report(&diagnostics);
        assert_eq!(errors_write::get_state_for_test(), "Reporting[1]");
        // Nothing to report: nothing written, no count.
        errors_write::report(&diagnostics_state::T::new());
        assert_eq!(errors_write::get_state_for_test(), "Reporting[1]");
        let messages = read_all(&file);
        assert_eq!(messages.len(), 3);
        let ours = match &messages[2] {
            errors_file::Message::Item(ErrorsFileItem::Errors { timestamp, .. }) => {
                errors_file::Message::Item(ErrorsFileItem::Errors {
                    errors: errors.clone(),
                    timestamp: *timestamp,
                })
            }
            m => panic!("{:?}", m),
        };
        assert!(messages[2] == ours, "{}", name);
        let payload = errors_file_payloads(&std::fs::read(&file).unwrap())[2].to_vec();
        assert!(payload == errors_file::marshal(&ours), "{}", name);
        errors_write::unlink_at_server_stop();
        assert!(!std::path::Path::new(&file).exists());
    }
}

// ~~ The scenarios of server_progress_tests.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A typecheck's telemetry items, as the OCaml typecheck writes them.
fn typecheck_telemetry() {
    for (key, value) in [
        ("to_recheck_count", yojson::T::Int(1)),
        ("will_use_distc", yojson::T::Bool(false)),
        ("process_in_parallel", yojson::T::Bool(true)),
    ] {
        errors_write::telemetry(&telemetry::json(key, value, telemetry::create()));
    }
}

/// The errors of `b.php` of the OCaml tests (`function test_b(): int {}`),
/// taken from the golden file.
fn b_php_errors(root: &str) -> diagnostics_state::T {
    let (_, m) = golden_messages("r1")
        .into_iter()
        .find(|(_, m)| matches!(m, errors_file::Message::Item(ErrorsFileItem::Errors { .. })))
        .unwrap();
    let errors = match m {
        errors_file::Message::Item(ErrorsFileItem::Errors { errors, .. }) => errors,
        _ => unreachable!(),
    };
    relative_path::set_path_prefix(
        relative_path::Prefix::Root,
        std::path::Path::new("/private/tmp/hh-incr/err/r1/"),
    );
    let mut diagnostics = diagnostics_state::T::new();
    for (path, errs) in errors.iter() {
        if relative_path::suffix(path) == "b.php" {
            let ds = errs
                .iter()
                .map(|(d, _)| to_relative(d, "/private/tmp/hh-incr/err/r1/"))
                .collect();
            diagnostics.insert(path.clone(), ds);
        }
    }
    let _ = root;
    diagnostics
}

fn open(file: &str) -> (std::fs::File, isize) {
    let fd = std::fs::File::open(file).unwrap();
    let errors_read::OpenSuccess { pid, .. } = errors_read::openfile(&fd).unwrap();
    (fd, pid)
}

/// `test_errors_complete`: after a completed typecheck, two clients read
/// the whole file, one after the other; after the server stops, the file
/// is gone.
#[test]
fn errors_complete() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/complete");
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    typecheck_telemetry();
    errors_write::report(&b_php_errors(""));
    errors_write::complete(&telemetry::create());
    assert_eq!(errors_write::get_state_for_test(), "Closed");
    for _client in 0..2 {
        let (fd, pid) = open(&file);
        assert_eq!(pid, ocaml_unix::getpid());
        let q = server_progress_lwt::watch_errors_file(pid, fd);
        expect_qitems(
            &q,
            &[
                "Telemetry [to_recheck_count]",
                "Telemetry [will_use_distc]",
                "Telemetry [process_in_parallel]",
                "Errors [b.php=1]",
                "typecheck completed [complete]",
                "closed",
            ],
        );
    }
    errors_write::unlink_at_server_stop();
    assert!(!std::path::Path::new(&file).exists());
    assert_eq!(errors_write::get_state_for_test(), "Absent");
}

/// `test_errors_during`: two clients follow a typecheck under way; when the
/// server stops, each reads the end and its stream closes.
#[test]
fn errors_during() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/during");
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    typecheck_telemetry();
    errors_write::report(&b_php_errors(""));
    let expected = [
        "Telemetry [to_recheck_count]",
        "Telemetry [will_use_distc]",
        "Telemetry [process_in_parallel]",
        "Errors [b.php=1]",
        "nothing",
    ];
    let (fd1, pid) = open(&file);
    let q1 = server_progress_lwt::watch_errors_file(pid, fd1);
    expect_qitems(&q1, &expected);
    let (fd2, pid) = open(&file);
    let q2 = server_progress_lwt::watch_errors_file(pid, fd2);
    expect_qitems(&q2, &expected);
    errors_write::unlink_at_server_stop();
    assert!(!std::path::Path::new(&file).exists());
    expect_qitems(&q1, &["hh_server gracefully stopped [unlink]", "closed"]);
    expect_qitems(&q2, &["hh_server gracefully stopped [unlink]", "closed"]);
}

/// `test_errors_kill`: the server dies mid-typecheck (here, the process
/// named in the header of a file left as a killed server leaves it): a
/// client following the file learns it, and the file stays.
#[test]
fn errors_kill() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/kill");
    let mut server = std::process::Command::new("sleep").arg("60").spawn().unwrap();
    let pid = server.id() as isize;
    // Once the child has exec'd `sleep`.
    let cmdline = loop {
        match proc::get_cmdline(pid) {
            Ok(c) if c.starts_with("sleep") => break c,
            _ => std::thread::sleep(Duration::from_millis(10)),
        }
    };
    errors_write::create_file_for_test(pid, &cmdline);
    let (fd, read_pid) = open(&file);
    assert_eq!(read_pid, pid);
    let q = server_progress_lwt::watch_errors_file(pid, fd);
    assert_eq!(qitem(&q, Duration::from_secs(1)), "nothing");
    server.kill().unwrap();
    server.wait().unwrap();
    // `watch_pid` polls every 5s.
    expect_qitems(&q, &["hh_server died", "closed"]);
    assert!(std::path::Path::new(&file).exists());
    // A client that opens it now is told at once.
    let fd = std::fs::File::open(&file).unwrap();
    match errors_read::openfile(&fd) {
        Err((e @ errors_read::OpenError::OKilled(None), msg)) => {
            assert_eq!(msg, "Errors-file is from defunct PID");
            assert_eq!(errors_read::open_error_short_description(&e), "hh_server died");
        }
        r => panic!("{:?}", r.map(|_| ())),
    }
    let _ = std::fs::remove_file(&file);
}

/// `test_errors_existing`: a file left by a dead server is replaced at the
/// next typecheck; a new typecheck ends the file of the previous one with a
/// `Restarted` sentinel once the new file is in place.
#[test]
fn errors_existing_and_restarted() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/existing");
    let mut child = std::process::Command::new("true").spawn().unwrap();
    let dead = child.id() as isize;
    child.wait().unwrap();
    errors_write::create_file_for_test(dead, "hh_server");
    let fd = std::fs::File::open(&file).unwrap();
    assert!(matches!(
        errors_read::openfile(&fd),
        Err((errors_read::OpenError::OKilled(None), _))
    ));
    // The server starts: Absent, so nothing to end; the leftover is unlinked.
    errors_write::new_empty_file(
        Some(server_notifier_types::Clock::Watchman("c:1:2".to_string())),
        false,
        ("first".to_string(), "first log".to_string()),
    );
    assert_eq!(errors_write::get_state_for_test(), "Reporting[0]");
    let (fd1, pid) = open(&file);
    let fd1_inode = fd1.metadata().unwrap();
    errors_write::report(&b_php_errors(""));
    assert_eq!(errors_write::get_state_for_test(), "Reporting[1]");
    let q1 = server_progress_lwt::watch_errors_file(pid, fd1);
    expect_qitems(&q1, &["Errors [b.php=1]", "nothing"]);
    // A new typecheck before the first completed.
    errors_write::new_empty_file(None, false, ("Files changed".to_string(), "log".to_string()));
    assert_eq!(errors_write::get_state_for_test(), "Reporting[0]");
    match q1.recv_timeout(Duration::from_secs(10)).unwrap().unwrap() {
        errors_read::ReadResult::RCompleted(
            CompletionReason::Restarted {
                user_message,
                log_message,
            },
            msg,
        ) => {
            assert_eq!((user_message.as_str(), log_message.as_str()), ("Files changed", "log"));
            assert_eq!(msg, "new_empty_file");
            // The new file is already there.
            use std::os::unix::fs::MetadataExt;
            let new = std::fs::metadata(&file).unwrap();
            assert_ne!(new.ino(), fd1_inode.ino());
        }
        r => panic!("{:?}", r),
    }
    expect_qitems(&q1, &["closed"]);
    let (fd2, _) = open(&file);
    let q2 = server_progress_lwt::watch_errors_file(pid, fd2);
    expect_qitems(&q2, &["nothing"]);
    errors_write::complete(&telemetry::create());
    expect_qitems(&q2, &["typecheck completed [complete]", "closed"]);
    // After `complete`, a new typecheck has no old file to end.
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    errors_write::unlink_at_server_stop();
    assert!(!std::path::Path::new(&file).exists());
}

#[test]
fn bad_states_and_disabled_production() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/states");
    let msg = |f: fn()| -> String {
        let e = std::panic::catch_unwind(f).unwrap_err();
        e.downcast_ref::<String>().cloned().unwrap()
    };
    assert_eq!(errors_write::get_state_for_test(), "Absent");
    assert_eq!(msg(|| errors_write::report(&b_php_errors(""))), "Cannot report in state Absent");
    assert_eq!(
        msg(|| errors_write::telemetry(&telemetry::create())),
        "Cannot report in state Absent"
    );
    assert_eq!(
        msg(|| errors_write::complete(&telemetry::create())),
        "Cannot complete in state Absent"
    );
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    errors_write::complete(&telemetry::create());
    assert_eq!(
        msg(|| errors_write::complete(&telemetry::create())),
        "Cannot complete in state Closed"
    );
    errors_write::unlink_at_server_stop();
    // Production off: every function does nothing, whatever the state.
    enable_error_production(false);
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    errors_write::report(&b_php_errors(""));
    errors_write::complete(&telemetry::create());
    assert!(!std::path::Path::new(&file).exists());
    assert_eq!(errors_write::get_state_for_test(), "Absent");
    enable_error_production(true);
    // A header that is not first: OCaml's failwith.
    errors_write::new_empty_file(None, false, (String::new(), String::new()));
    let fd = std::fs::File::open(&file).unwrap();
    let e = std::panic::catch_unwind(|| errors_read::read_next_errors(&fd)).unwrap_err();
    assert_eq!(
        e.downcast_ref::<&str>().copied(),
        Some(
            "do Server_progress.ErrorsRead.openfile before read_next_error or Server_progress_lwt.watch_errors_file"
        )
    );
    errors_write::unlink_at_server_stop();
}

/// A version header of another build (both longer than 16 characters) is
/// refused; a dev build's (empty) is not.
#[test]
fn version_mismatch() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/version");
    let write = |version: &str| {
        let fd = std::fs::File::create(&file).unwrap();
        errors_file::write_message(
            &fd,
            &errors_file::Message::VersionHeader {
                version: version.to_string(),
                extra: yojson::T::Assoc(vec![]),
            },
        )
        .unwrap();
        errors_file::write_message(
            &fd,
            &errors_file::Message::Header {
                pid: ocaml_unix::getpid(),
                cmdline: proc::get_cmdline(ocaml_unix::getpid()).unwrap(),
                timestamp: 0.0,
                clock: None,
            },
        )
        .unwrap();
    };
    let ours = crate::build_id::build_revision();
    write("");
    assert!(errors_read::openfile(&std::fs::File::open(&file).unwrap()).is_ok());
    write(&"0".repeat(40));
    let r = errors_read::openfile(&std::fs::File::open(&file).unwrap());
    if ours.len() > 16 {
        match r {
            Err((errors_read::OpenError::OBuildIdMismatch, msg)) => {
                assert_eq!(msg, format!("errors-file is version {}, but we are {}", "0".repeat(40), ours))
            }
            r => panic!("{:?}", r.map(|_| ())),
        }
    } else {
        assert!(r.is_ok());
    }
    let _ = std::fs::remove_file(&file);
}

/// A payload cut short is `Malformed`; a garbled preamble is OCaml's
/// uncaught `Malformed_Preamble_Exception`.
#[test]
fn truncated_files() {
    let _serial = serial();
    let file = set_test_root("/nonexistent/hh_errors_test/truncated");
    let r1 = golden("r1");
    std::fs::write(&file, &r1[..r1.len() - 3]).unwrap();
    let fd = std::fs::File::open(&file).unwrap();
    let mut results = vec![];
    // Skip the headers (their pid is the oracle's, dead).
    let _ = errors_file::read_message(&fd).unwrap();
    let _ = errors_file::read_message(&fd).unwrap();
    loop {
        match errors_read::read_next_errors(&fd) {
            Ok(Some(r)) => results.push(show_read_result(&r)),
            Ok(None) => {
                results.push("nothing yet".to_string());
                break;
            }
            Err(ErrorsFileReadError::Malformed) => {
                results.push("malformed error".to_string());
                break;
            }
        }
    }
    assert_eq!(results.last().unwrap(), "malformed error");
    assert_eq!(results.len(), 5);
    std::fs::write(&file, b"\x00\x00\x00\x00\x01x").unwrap();
    let fd = std::fs::File::open(&file).unwrap();
    assert!(std::panic::catch_unwind(|| errors_read::read_next_errors(&fd)).is_err());
    let _ = std::fs::remove_file(&file);
}

/// The OCaml client (`hh_client check` with `consume_streaming_errors`)
/// reads a file written here. Needs a client that runs on this machine:
/// `HH_ERR_OCAML_CLIENT=/tmp/hh-incr/err/oc.sh` (the oracle's, with the
/// macOS shims of the ERR notes); skipped without it.
#[test]
fn ocaml_client_reads_our_file() {
    let Ok(client) = std::env::var("HH_ERR_OCAML_CLIENT") else {
        return;
    };
    let _serial = serial();
    let root = "/private/tmp/hh-incr/err/r1";
    let tmp = crate::server_files::tests::testing_tmp();
    let (_, m) = golden_messages("r1")
        .into_iter()
        .find(|(_, m)| matches!(m, errors_file::Message::Item(ErrorsFileItem::Errors { .. })))
        .unwrap();
    let errors = match m {
        errors_file::Message::Item(ErrorsFileItem::Errors { errors, .. }) => errors,
        _ => unreachable!(),
    };
    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(root));
    let mut diagnostics = diagnostics_state::T::new();
    for (path, errs) in errors.iter() {
        diagnostics.insert(
            path.clone(),
            errs.iter().map(|(d, _)| to_relative(d, &format!("{}/", root))).collect(),
        );
    }
    set_root(root.to_string());
    let file = errors_file_path().unwrap();
    let _ = std::fs::remove_file(&file);
    errors_write::new_empty_file(None, true, (String::new(), String::new()));
    typecheck_telemetry();
    errors_write::report(&diagnostics);
    errors_write::complete(&telemetry::create());
    for format in ["plain", "raw"] {
        let out = std::process::Command::new(&client)
            .args(["check", "--config", "consume_streaming_errors=true", "--error-format", format, root])
            .env("HH_TMPDIR", &tmp)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let expected = std::fs::read_to_string(format!("/tmp/hh-incr/err/golden/r1.{}.out", format))
            .unwrap_or_default();
        eprintln!("--- {} exit {:?}\n{}\n{}", format, out.status.code(), stdout, String::from_utf8_lossy(&out.stderr));
        assert_eq!(out.status.code(), Some(2), "{}", format);
        if !expected.is_empty() {
            assert_eq!(stdout, expected, "{}", format);
        }
    }
    errors_write::unlink_at_server_stop();
}
