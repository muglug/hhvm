// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_isolation_move.ml`. See `hh/PORTING.md`.
//!
//! The client is synchronous: every `Lwt.t` of the OCaml is the value
//! itself, and an exception that crosses `Lwt` (a failed request, a
//! `Failure` of an undo) is an `Err` of [`Exn`]. The OCaml's
//! `Unix.Unix_error`s, which the functions that touch the disk catch, are
//! `Err`s holding their `Exn.to_string`, which is all the handlers use.

use std::io::Write;

use crate::client_connect;
use crate::client_env;
use crate::exit_status;
use crate::filter_diagnostics;
use crate::hh_client::Exn;
use crate::relative_path;
use crate::rt::ocaml_exn::Uncaught;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;
use crate::server_command_types;
use crate::server_isolation_types;
use crate::utils::print_count;

/// `Exn.to_string exn`
fn exn_to_string(exn: &Exn) -> String {
    match exn {
        // (The printer `Exit_status` registers.)
        Exn::ExitWith(es) => {
            Uncaught::Printexc(format!("Exit_status.Exit_with({})", exit_status::show(es)))
                .to_string()
        }
        Exn::Other(e) => Uncaught::Printexc(crate::exception::get_ctor_string(e)).to_string(),
    }
}

/// `Exn.to_string` of the `Unix.Unix_error` that `fun_name arg` raised.
fn unix_error_to_string(e: &std::io::Error, fun_name: &str, arg: &str) -> String {
    Uncaught::Printexc(ocaml_unix::unix_error_to_string(e, fun_name, arg)).to_string()
}

/// `exception Failure of string`, raised by [`dir_move::undo`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure(pub String);

/// `raise (Failure message)` as an [`Exn`] (`Lwt.fail_with message`).
fn failure_exn(message: String) -> Exn {
    Exn::Other(crate::exception::wrap(FailurePrinted(message)))
}

/// A `Failure`, printed as `Printexc.to_string` prints it.
struct FailurePrinted(String);

impl std::fmt::Debug for FailurePrinted {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failure({:?})", self.0)
    }
}

/// The paths the move deals in: directories and files relative to the root.
pub mod paths {
    use super::*;

    /// `file` as the server reports it, an absolute path, relative to the root when
    /// it is under it.
    pub fn relative_to_root(file: &str) -> relative_path::T {
        match relative_path::strip_root_if_possible(file) {
            Some(suffix) => relative_path::from_root(&suffix),
            None => relative_path::create(relative_path::Prefix::Dummy, file),
        }
    }

    /// `file`, named as it was before `source` moved to `target`.
    pub fn original_path(
        source: &relative_path::T,
        target: &relative_path::T,
        file: &relative_path::T,
    ) -> relative_path::T {
        if relative_path::is_within(target, file) {
            let file_suffix = relative_path::suffix(file);
            let below_target = file_suffix
                .strip_prefix(relative_path::suffix(target).as_str())
                .expect("String.chop_prefix_exn");
            relative_path::from_root(&(relative_path::suffix(source) + below_target))
        } else {
            file.clone()
        }
    }

    /// `parent` followed by the last name of `source`: where `source` goes when
    /// moved into `parent`.
    pub fn target_name(parent: &str, source: &str) -> String {
        ocaml_filename::concat(parent, &ocaml_filename::basename(source))
    }

    pub fn target_under(parent: &relative_path::T, source: &relative_path::T) -> relative_path::T {
        relative_path::from_root(&target_name(
            &relative_path::suffix(parent),
            &relative_path::suffix(source),
        ))
    }
}

pub mod dir_move {
    use super::*;

    /// What a move has done to the disk, newest first, so that undoing it is
    /// reading it from the front.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Step {
        MadeDir(String),
        Renamed { from: String, into: String },
    }

    /// The directories above `target` that do not exist yet, outermost first.
    pub fn missing_parents(target: &str) -> Vec<String> {
        let mut dir = ocaml_filename::dirname(target);
        let mut missing = vec![];
        while !(dir.is_empty() || dir == "." || crate::disk::file_exists(&dir)) {
            let parent = ocaml_filename::dirname(&dir);
            missing.push(dir);
            dir = parent;
        }
        missing.reverse();
        missing
    }

    /// `Unix.mkdir path 0o755`, journalled.
    fn make_dir(journal: &mut Vec<Step>, path: &str) -> Result<(), String> {
        use std::os::unix::fs::DirBuilderExt;
        std::fs::DirBuilder::new()
            .mode(0o755)
            .create(path)
            .map_err(|e| unix_error_to_string(&e, "mkdir", path))?;
        journal.insert(0, Step::MadeDir(path.to_string()));
        Ok(())
    }

    /// `Unix.lstat` succeeds; `ENOENT` is `false`, and any other error raises.
    fn exists(path: &str) -> Result<bool, String> {
        match std::fs::symlink_metadata(path) {
            Ok(_) => Ok(true),
            Err(e) if e.raw_os_error() == Some(libc::ENOENT) => Ok(false),
            Err(e) => Err(unix_error_to_string(&e, "lstat", path)),
        }
    }

    fn rename(from: &str, into: &str) -> Result<(), String> {
        std::fs::rename(from, into).map_err(|e| unix_error_to_string(&e, "rename", from))
    }

    /// A step whose result is already there is skipped.
    fn undo_step(step: &Step) -> Result<(), String> {
        match step {
            Step::Renamed { from, into } => {
                if exists(into)? {
                    rename(into, from)?
                }
                Ok(())
            }
            Step::MadeDir(path) => match std::fs::remove_dir(path) {
                Ok(()) => Ok(()),
                Err(e)
                    if matches!(
                        e.raw_os_error(),
                        Some(libc::ENOTEMPTY | libc::EEXIST | libc::ENOENT)
                    ) =>
                {
                    Ok(())
                }
                Err(e) => Err(unix_error_to_string(&e, "rmdir", path)),
            },
        }
    }

    /// Every step is tried, so one that fails does not leave the rest undone, and
    /// the failures are then reported together.
    pub fn undo(steps: &[Step]) -> Result<(), Failure> {
        let failures: Vec<String> = steps
            .iter()
            .filter_map(|step| match undo_step(step) {
                Ok(()) => None,
                Err(exn) => Some(match step {
                    Step::MadeDir(path) => format!("{}: {}", path, exn),
                    Step::Renamed { from, into } => format!("{} to {}: {}", into, from, exn),
                }),
            })
            .collect();
        if !failures.is_empty() {
            Err(Failure(format!(
                "could not undo the move completely:\n  {}",
                failures.join("\n  ")
            )))
        } else {
            Ok(())
        }
    }

    pub fn move_(source: &str, target: &str) -> Result<Vec<Step>, String> {
        let mut journal = vec![];
        let result = (|| {
            for dir in missing_parents(target) {
                make_dir(&mut journal, &dir)?
            }
            rename(source, target)?;
            journal.insert(
                0,
                Step::Renamed {
                    from: source.to_string(),
                    into: target.to_string(),
                },
            );
            Ok(())
        })();
        match result {
            Ok(()) => Ok(journal),
            Err(reason) => match undo(&journal) {
                Ok(()) => Err(reason),
                Err(Failure(undo_failure)) => Err(format!("{}; {}", reason, undo_failure)),
            },
        }
    }
}

pub mod move_error {
    use std::collections::BTreeSet;

    use bstr::ByteSlice;

    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub code: isize,
        pub file: relative_path::T,
        pub line: isize,
        pub message: String,
    }

    pub fn of_status(status: &server_command_types::server_status::T) -> Vec<T> {
        use crate::user_diagnostic::Severity;
        status
            .error_list
            .iter()
            .filter_map(|diagnostic| match diagnostic.severity {
                Severity::Warning { .. } => None,
                Severity::Err => {
                    let oxidized::message::Message(pos, message) = &diagnostic.claim;
                    Some(T {
                        code: diagnostic.code,
                        file: paths::relative_to_root(&crate::pos::filename(pos)),
                        line: crate::pos::line(pos),
                        message: message.to_str_lossy().into_owned(),
                    })
                }
            })
            .collect()
    }

    pub fn key(t: &T) -> String {
        let T {
            code,
            file,
            line,
            message,
        } = t;
        format!(
            "{}\0{}\0{}\0{}",
            code,
            relative_path::storage_to_string(file),
            line,
            message
        )
    }

    pub fn keys(errors: &[T]) -> BTreeSet<String> {
        errors.iter().map(key).collect()
    }

    pub fn same(a: &[T], b: &[T]) -> bool {
        keys(a) == keys(b)
    }

    /// `message` with the path `from` named `into`, wherever `from` is not part
    /// of a longer name: `a/b` is in `see a/b/c` and not in `see a/b_c`.
    pub fn rename_path(message: &str, from: &str, into: &str) -> String {
        let is_name_char = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c == b'-' || c == b'.';
        let message = message.as_bytes();
        let from = from.as_bytes();
        let length = message.len();
        let n = from.len();
        let is_path_at = |i: usize| {
            i + n <= length
                && &message[i..i + n] == from
                && (i == 0 || !is_name_char(message[i - 1]))
                && (i + n == length || !is_name_char(message[i + n]))
        };
        let mut buffer: Vec<u8> = Vec::with_capacity(length);
        let mut i = 0;
        while i < length {
            if is_path_at(i) {
                buffer.extend_from_slice(into.as_bytes());
                i += n
            } else {
                buffer.push(message[i]);
                i += 1
            }
        }
        // (Valid UTF-8: `from` can only match at a character boundary.)
        String::from_utf8_lossy(&buffer).into_owned()
    }

    pub fn introduced(
        source: &relative_path::T,
        target: &relative_path::T,
        baseline: &[T],
        after: Vec<T>,
    ) -> Vec<T> {
        let known = keys(baseline);
        after
            .into_iter()
            .filter_map(|error| {
                let error = T {
                    file: paths::original_path(source, target, &error.file),
                    message: rename_path(
                        &error.message,
                        &relative_path::suffix(target),
                        &relative_path::suffix(source),
                    ),
                    ..error
                };
                if known.contains(&key(&error)) {
                    None
                } else {
                    Some(error)
                }
            })
            .collect()
    }
}

pub mod output {
    use super::*;
    use crate::yojson::safe::T as J;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Outcome {
        Refused(String),
        Blocked(Vec<server_isolation_types::Blocker>),
        NotMoved {
            errors: Vec<move_error::T>,
            baseline_restored: bool,
        },
        Moved {
            files: isize,
        },
    }

    pub fn is_moved(outcome: &Outcome) -> bool {
        match outcome {
            Outcome::Moved { .. } => true,
            Outcome::Refused(_) | Outcome::Blocked(_) | Outcome::NotMoved { .. } => false,
        }
    }

    pub fn error_to_json(error: &move_error::T) -> J {
        let move_error::T {
            code,
            file,
            line,
            message,
        } = error;
        J::Assoc(vec![
            ("code".to_string(), J::Int(*code)),
            ("file".to_string(), J::String(relative_path::suffix(file))),
            ("line".to_string(), J::Int(*line)),
            ("message".to_string(), J::String(message.clone())),
        ])
    }

    pub fn blocker_to_json(blocker: &server_isolation_types::Blocker) -> J {
        let server_isolation_types::Blocker { file, references } = blocker;
        J::Assoc(vec![
            ("file".to_string(), J::String(file.clone())),
            (
                "references".to_string(),
                J::List(references.iter().map(|f| J::String(f.clone())).collect()),
            ),
        ])
    }

    /// The fields only this kind of outcome has. The others are `null`.
    pub fn outcome_fields(outcome: &Outcome) -> Vec<(&'static str, J)> {
        match outcome {
            Outcome::Moved { files } => vec![("files", J::Int(*files))],
            Outcome::Refused(reason) => vec![("refused", J::String(reason.clone()))],
            Outcome::Blocked(blockers) => vec![
                (
                    "blockers",
                    J::List(
                        blockers
                            .iter()
                            .map(|server_isolation_types::Blocker { file, .. }| {
                                J::String(file.clone())
                            })
                            .collect(),
                    ),
                ),
                (
                    "blocked_by",
                    J::List(blockers.iter().map(blocker_to_json).collect()),
                ),
            ],
            Outcome::NotMoved {
                errors,
                baseline_restored,
            } => vec![
                (
                    "new_errors",
                    J::List(errors.iter().map(error_to_json).collect()),
                ),
                ("baseline_restored", J::Bool(*baseline_restored)),
            ],
        }
    }

    pub const OUTCOME_FIELD_NAMES: [&str; 6] = [
        "files",
        "refused",
        "blockers",
        "blocked_by",
        "new_errors",
        "baseline_restored",
    ];

    pub fn to_json(source: &str, target: &str, outcome: &Outcome) -> J {
        let fields = outcome_fields(outcome);
        let mut assoc = vec![
            ("source".to_string(), J::String(source.to_string())),
            ("target".to_string(), J::String(target.to_string())),
            ("moved".to_string(), J::Bool(is_moved(outcome))),
        ];
        assoc.extend(OUTCOME_FIELD_NAMES.iter().map(|name| {
            (
                name.to_string(),
                fields
                    .iter()
                    .find(|(n, _)| n == name)
                    .map_or(J::Null, |(_, v)| v.clone()),
            )
        }));
        J::Assoc(assoc)
    }

    pub fn first_line(message: &str) -> &str {
        match message.find('\n') {
            Some(i) => &message[..i],
            None => message,
        }
    }

    pub const SHOWN_ERRORS: usize = 10;

    fn print_blocked(
        out: &mut dyn Write,
        blockers: &[server_isolation_types::Blocker],
    ) -> std::io::Result<()> {
        let files: Vec<String> = blockers
            .iter()
            .map(|server_isolation_types::Blocker { file, .. }| file.clone())
            .collect();
        write!(
            out,
            "Not moved: referenced from {} outside.\n",
            print_count(files.len() as isize, "file")
        )?;
        crate::utils::fprint_capped_list(out, None, Some("; --json lists them all"), &files)
    }

    fn print_not_moved(
        out: &mut dyn Write,
        errors: &[move_error::T],
        baseline_restored: bool,
    ) -> std::io::Result<()> {
        write!(
            out,
            "Not moved: the move introduced {}, and it was undone.\n",
            print_count(errors.len() as isize, "error")
        )?;
        for move_error::T {
            code,
            file,
            line,
            message,
        } in errors.iter().take(SHOWN_ERRORS)
        {
            write!(
                out,
                "  {} {}:{}: {}\n",
                code,
                relative_path::suffix(file),
                line,
                first_line(message)
            )?
        }
        if errors.len() > SHOWN_ERRORS {
            write!(out, "  and {} more\n", errors.len() - SHOWN_ERRORS)?
        }
        if !baseline_restored {
            eprint!(
                "warning: the server's errors after the undo differ from those before the move; `hh restart` clears that\n"
            )
        }
        Ok(())
    }

    pub fn print_text(
        out: &mut dyn Write,
        source: &str,
        target: &str,
        outcome: &Outcome,
    ) -> std::io::Result<()> {
        match outcome {
            Outcome::Moved { files } => write!(
                out,
                "Moved: {} from {} to {}, with no new errors.\n",
                print_count(*files, "file"),
                source,
                target
            ),
            Outcome::Refused(reason) => write!(out, "Did not run: {}\n", reason),
            Outcome::Blocked(blockers) => print_blocked(out, blockers),
            Outcome::NotMoved {
                errors,
                baseline_restored,
            } => print_not_moved(out, errors, *baseline_restored),
        }
    }

    pub fn print_outcome(
        out: &mut dyn Write,
        source: &str,
        target: &str,
        output_json: bool,
        outcome: &Outcome,
    ) -> std::io::Result<()> {
        if output_json {
            write!(
                out,
                "{}\n",
                crate::yojson::safe::to_string(&to_json(source, target, outcome))
            )
        } else {
            print_text(out, source, target, outcome)
        }
    }

    pub fn exit_status(outcome: &Outcome) -> exit_status::T {
        match outcome {
            Outcome::Moved { .. } => exit_status::T::NoError,
            Outcome::Refused(_) => exit_status::T::InputError,
            Outcome::Blocked(_) | Outcome::NotMoved { .. } => exit_status::T::TypeError,
        }
    }
}

use output::Outcome;

/// A file that blocks a move, as JSON: the file, and the files of the moved
/// set that it references.
pub use output::blocker_to_json;

pub fn refusal(source: &relative_path::T, target: &relative_path::T) -> Option<String> {
    if !crate::disk::is_directory(&relative_path::to_absolute(source)) {
        Some(format!(
            "{} is not a directory",
            relative_path::suffix(source)
        ))
    } else if relative_path::equal(source, target) {
        Some(format!(
            "{} is already in {}",
            relative_path::suffix(source),
            ocaml_filename::dirname(&relative_path::suffix(source))
        ))
    } else if crate::disk::file_exists(&relative_path::to_absolute(target)) {
        Some(format!(
            "{} already exists, and moving into it would merge two packages",
            relative_path::suffix(target)
        ))
    } else if relative_path::is_within(source, target) || relative_path::is_within(target, source) {
        Some("the source and the target must not contain one another".to_string())
    } else {
        None
    }
}

/// The question [`move_into`] asks the server about a directory.
type AskMovable<'a> = dyn Fn(&relative_path::T) -> Result<server_isolation_types::Result, Exn> + 'a;

/// The server's status, which [`move_into`] reads the errors from.
type Status<'a> = dyn Fn() -> Result<server_command_types::server_status::T, Exn> + 'a;

/// Asks the server whether it has seen a move of `files` Hack files from
/// `old_dir` to `new_dir`: it knows all of them in `new_dir` and none in
/// `old_dir`. Otherwise says how many it knew in each.
fn check_seen(
    ask_movable: &AskMovable<'_>,
    new_dir: &relative_path::T,
    old_dir: &relative_path::T,
    files: isize,
) -> Result<Result<(), (isize, isize)>, Exn> {
    let asked_new = ask_movable(new_dir)?;
    let asked_old = ask_movable(old_dir)?;
    let files_in_new_dir = asked_new.total_seeds;
    let files_in_old_dir = asked_old.total_seeds;
    if files_in_new_dir == files && files_in_old_dir == 0 {
        Ok(Ok(()))
    } else {
        Ok(Err((files_in_new_dir, files_in_old_dir)))
    }
}

fn unseen_message(
    source: &relative_path::T,
    target: &relative_path::T,
    files: isize,
    (files_in_target, files_in_source): (isize, isize),
) -> String {
    format!(
        "the server knew {} of the {} Hack files at {}, and {} at {}, after the move, so a typecheck would not reflect it; the move was undone. The server may not see a renamed directory unless it runs with `--config edenfs_file_watcher_enabled=true`",
        files_in_target,
        files,
        relative_path::suffix(target),
        files_in_source,
        relative_path::suffix(source)
    )
}

/// The errors the server reports once it has seen the move from `old_dir` to
/// `new_dir`, or how many Hack files it knew in each if it has not. The
/// typecheck only means something once the server has seen the move: one that
/// missed it would answer for the tree as it was, and pass.
fn errors_after_move(
    ask_movable: &AskMovable<'_>,
    status: &Status<'_>,
    files: isize,
    new_dir: &relative_path::T,
    old_dir: &relative_path::T,
) -> Result<Result<Vec<move_error::T>, (isize, isize)>, Exn> {
    match check_seen(ask_movable, new_dir, old_dir, files)? {
        Err(counts) => Ok(Err(counts)),
        Ok(()) => {
            let after = status()?;
            Ok(Ok(move_error::of_status(&after)))
        }
    }
}

/// What the server says about a directory moved to `target`.
enum Verdict {
    /// It had not seen the move: how many Hack files it knew at `target`
    /// and at `source`.
    Unseen((isize, isize)),
    /// It saw the move and reports no new errors.
    Clean,
    /// It saw the move and reports these.
    Introduced(Vec<move_error::T>),
}

/// Runs `f`, and calls `revert` if it raises, adding to the error if the undo
/// fails too.
fn reverting_on_exn<A>(
    revert: impl FnOnce() -> Result<(), Failure>,
    f: impl FnOnce() -> Result<A, Exn>,
) -> Result<A, Exn> {
    match f() {
        Ok(a) => Ok(a),
        Err(exn) => match revert() {
            Ok(()) => Err(exn),
            Err(Failure(undo_failure)) => Err(failure_exn(format!(
                "{}; {}",
                exn_to_string(&exn),
                undo_failure
            ))),
        },
    }
}

fn verdict(
    source: &relative_path::T,
    target: &relative_path::T,
    baseline: &[move_error::T],
    errors_after_move: &dyn Fn(
        &relative_path::T,
        &relative_path::T,
    ) -> Result<Result<Vec<move_error::T>, (isize, isize)>, Exn>,
) -> Result<Verdict, Exn> {
    match errors_after_move(target, source)? {
        Err(counts) => Ok(Verdict::Unseen(counts)),
        Ok(after) => {
            let errors = move_error::introduced(source, target, baseline, after);
            Ok(if errors.is_empty() {
                Verdict::Clean
            } else {
                Verdict::Introduced(errors)
            })
        }
    }
}

/// `raise (Failure undo_failure)` of an undo that could not be completed.
fn raise_failure(r: Result<(), Failure>) -> Result<(), Exn> {
    r.map_err(|Failure(message)| failure_exn(message))
}

fn move_and_check(
    source: &relative_path::T,
    target: &relative_path::T,
    files: isize,
    ask_movable: &AskMovable<'_>,
    status: &Status<'_>,
) -> Result<Outcome, Exn> {
    let errors_after_move = |new_dir: &relative_path::T, old_dir: &relative_path::T| {
        errors_after_move(ask_movable, status, files, new_dir, old_dir)
    };
    let baseline = status()?;
    let baseline = move_error::of_status(&baseline);
    match dir_move::move_(
        &relative_path::to_absolute(source),
        &relative_path::to_absolute(target),
    ) {
        Err(reason) => Ok(Outcome::Refused(format!(
            "could not move {} to {}: {}",
            relative_path::suffix(source),
            relative_path::suffix(target),
            reason
        ))),
        Ok(moved) => {
            let revert = || dir_move::undo(&moved);
            let verdict = reverting_on_exn(revert, || {
                verdict(source, target, &baseline, &errors_after_move)
            })?;
            match verdict {
                Verdict::Unseen(counts) => {
                    raise_failure(revert())?;
                    Ok(Outcome::Refused(unseen_message(
                        source, target, files, counts,
                    )))
                }
                Verdict::Clean => Ok(Outcome::Moved { files }),
                Verdict::Introduced(errors) => {
                    raise_failure(revert())?;
                    let restored = errors_after_move(source, target)?;
                    let baseline_restored = match restored {
                        Ok(restored) => move_error::same(&baseline, &restored),
                        Err(_) => false,
                    };
                    Ok(Outcome::NotMoved {
                        errors,
                        baseline_restored,
                    })
                }
            }
        }
    }
}

fn try_move(
    source: &relative_path::T,
    target: &relative_path::T,
    ask_movable: &AskMovable<'_>,
    status: &Status<'_>,
) -> Result<Outcome, Exn> {
    match refusal(source, target) {
        Some(reason) => Ok(Outcome::Refused(reason)),
        None => {
            let gate = ask_movable(source)?;
            match (&gate.refused, &gate.movability) {
                (Some(reason), _) => Ok(Outcome::Refused(reason.clone())),
                (None, Some(server_isolation_types::Movability::Blocked(blockers))) => {
                    Ok(Outcome::Blocked(blockers.clone()))
                }
                (None, None) => Ok(Outcome::Refused(
                    "the server did not say whether the directory can move".to_string(),
                )),
                (None, Some(server_isolation_types::Movability::Movable)) => {
                    let files = gate.total_seeds;
                    if files == 0 {
                        Ok(Outcome::Refused(format!(
                            "{} holds no Hack files",
                            relative_path::suffix(source)
                        )))
                    } else {
                        move_and_check(source, target, files, ask_movable, status)
                    }
                }
            }
        }
    }
}

/// `move_into args ~connect ~options ~error_filter ~parent` moves the
/// directory `options.seed_dir`, repo-relative, into `parent` under its own
/// name, if nothing outside references into it and the move introduces no
/// errors, and otherwise leaves it where it was. It asks the running server,
/// with the isolation query for each directory and the status for the errors,
/// each answered after the server has picked up every change on disk. It prints
/// what came of it, as JSON when `args.output_json` is set, and gives the exit
/// status: zero only when the directory moved.
///
/// `connect` opens a new connection to the server (its argument is
/// `use_priority_pipe`). Each request needs its own, because the server closes
/// the connection after it answers.
///
/// Source control is not told. Raises if an undo cannot be completed.
// Moves [options.seed_dir] into [parent], then prints the outcome and gives
// its exit status. It first asks the server whether the directory can move at
// all, and moves it only if so. The server is asked about one directory at a
// time, so each question is [options] with that directory as the seed and no
// file for the clusters.
pub fn move_into(
    args: &client_env::ClientCheckEnv,
    connect: &dyn Fn(bool) -> Result<client_connect::Conn, Exn>,
    options: &server_isolation_types::Options,
    error_filter: &filter_diagnostics::filter::T,
    parent: &str,
) -> Result<exit_status::T, Exn> {
    let seed_dir = options
        .seed_dir
        .clone()
        .expect("Option.value_exn: the seed directory of --isolation-move-to");
    fn rpc<A: server_command_types::ResultOf>(
        args: &client_env::ClientCheckEnv,
        connect: &dyn Fn(bool) -> Result<client_connect::Conn, Exn>,
        command: server_command_types::T,
    ) -> Result<A, Exn> {
        let conn = connect(server_command_types::use_priority_pipe(&command))?;
        let (result, _telemetry) = client_connect::rpc(&conn, &args.desc, command)?;
        Ok(result)
    }
    let ask_movable = |dir: &relative_path::T| -> Result<server_isolation_types::Result, Exn> {
        rpc(
            args,
            connect,
            server_command_types::T::FindIsolatableClusters(server_isolation_types::Options {
                seed_dir: Some(relative_path::suffix(dir)),
                clusters_destination: server_isolation_types::ClustersDestination::Dropped,
                ..options.clone()
            }),
        )
    };
    let status = || -> Result<server_command_types::server_status::T, Exn> {
        rpc(
            args,
            connect,
            server_command_types::T::Status {
                max_errors: None,
                error_filter: error_filter.clone(),
            },
        )
    };
    let (source, target, outcome) = match (
        relative_path::from_root_opt(&seed_dir),
        relative_path::from_root_opt(parent),
    ) {
        (Some(source), Some(parent)) => {
            let target = paths::target_under(&parent, &source);
            let outcome = try_move(&source, &target, &ask_movable, &status)?;
            (
                relative_path::suffix(&source),
                relative_path::suffix(&target),
                outcome,
            )
        }
        _ => (
            seed_dir.clone(),
            paths::target_name(parent, &seed_dir),
            Outcome::Refused(
                "the source and the target must be directories relative to the root".to_string(),
            ),
        ),
    };
    {
        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();
        let _ = output::print_outcome(&mut stdout, &source, &target, args.output_json, &outcome);
        let _ = stdout.flush();
    }
    Ok(output::exit_status(&outcome))
}

#[cfg(test)]
mod tests;
