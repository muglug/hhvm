// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_args.ml`. See `hh/PORTING.md`.
//!
//! The command line is parsed with `crate::rt::ocaml_arg`, the emulation of
//! OCaml's `Arg`, so that the messages, the `--help` and `--ultrahelp` text
//! and the exit codes are OCaml's (`test/help`, `test/client_args_telemetry`).
//!
//! # Exceptions
//!
//! - `Arg.Bad` raised in a spec's function is `Err(ocaml_arg::Exn::Bad(..))`
//!   (`ocaml_arg`'s convention), and the `Exit_status.Exit_with` that
//!   `Find_refs_wire_format` raises in one is `Err(ocaml_arg::Exn::Raise(..))`
//!   (the spec lists here are `ocaml_arg::Spec<'_, ExitWith>`). The
//!   exceptions that `parse_args` catches (`Arg.Help`, `Parse_error`, and
//!   `Arg.Bad` raised after the parse), and that `Exit_with`, are [`Raised`],
//!   returned by the `parse_*` functions; `parse_args` returns the
//!   `Exit_with` for `Hh_client.main` to exit with.
//! - `Die` exits the process. Its log is the telemetry sample of OCaml's
//!   `Hack_event_logger`, which is a stub in the OSS build (and compiled with
//!   `port` only here): its calls are not made (see [`die`]).
//! - The catch-alls of `parse_without_command` and `interpret_root`
//!   (`Die.internal_exception`, which logs and raises again) still catch
//!   panics (`failwith` and the like), and the `Sys_error` that
//!   `Wwwroot.interpret_command_line_root_parameter` returns; they raise it
//!   again as a panic, for the toplevel of `hh_client` (an uncaught
//!   exception).
//!
//! # Lists
//!
//! The OCaml accumulates several options by consing onto a list (`--config`,
//! `--single`, `-W` codes, the batch modes); the `Vec`s here keep the order
//! of those lists (head first), so `--single a --single b` gives
//! `["b", "a"]`, as in OCaml.
//!
//! `Sys.argv` is `crate::rt::ocaml_sys::argv()`.

use std::cell::Cell;
use std::cell::RefCell;
use std::io::Read;
use std::io::Write;
use std::panic::AssertUnwindSafe;

use crate::client_command;
use crate::client_command::Command;
use crate::client_command::CommandKeyword;
use crate::client_command::HeavyCommand;
use crate::client_command::LightCommand;
use crate::client_decompress_zhhdg;
use crate::client_download_saved_state;
use crate::client_env;
use crate::client_env::ClientCheckEnv;
use crate::client_env::ClientMode;
use crate::client_env::ClientMode::*;
use crate::client_env::LogErrorsParams;
use crate::client_env::RenameMode;
use crate::client_env::StatusSingle;
use crate::client_lsp;
use crate::client_rage;
use crate::client_start;
use crate::client_stop;
use crate::diagnostics_state;
use crate::exception;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::filter_diagnostics;
use crate::find_refs_wire_format;
use crate::hh_logger;
use crate::hh_version;
use crate::path;
use crate::rt::ocaml_arg;
use crate::rt::ocaml_arg::stdlib_exit;
use crate::rt::ocaml_str;
use crate::rt::ocaml_sys;
use crate::server_args;
use crate::server_files;
use crate::sys_utils::SysError;
use crate::wwwroot;

/// Whether an option is shown in --help or only in --ultrahelp.
/// See snapshot tests: $FBCODE/hphp/hack/test/help
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgKind {
    /// An argument that is for users and agents.
    /// Will be shown in both hh --help and hh --ultrahelp
    ArgUserFacing,
    /// An argument that is for language and release teams,
    /// or for very rare use cases.
    /// will be shown only in hh --ultrahelp
    ArgNonUserFacing,
}

use ArgKind::*;

/// The exceptions of the functions of the spec lists: `Arg`'s, and
/// `Exit_status.Exit_with` (`Exn::Raise`, from `Find_refs_wire_format`).
type Exn = ocaml_arg::Exn<ExitWith>;
type Res = ocaml_arg::Res<ExitWith>;
type Spec<'a> = ocaml_arg::Spec<'a, ExitWith>;

/// An entry of the spec list of a parser, before the `ArgKind` is added.
type Entry<'a> = (String, Spec<'a>, String);

/// Arg specs shared across more than 1 arg parser.
pub mod common_argspecs {
    use std::cell::Cell;
    use std::cell::RefCell;

    use super::Entry;
    use super::Exn;
    use super::Res;
    use super::Spec;
    use crate::string_utils;

    pub fn add_key_value(
        option_name: &str,
        value_ref: &RefCell<Vec<(String, String)>>,
        value: String,
    ) -> Res {
        match string_utils::split2('=', &value) {
            Some(key_value) => {
                value_ref.borrow_mut().insert(0, key_value);
                Ok(())
            }
            None => Err(Exn::Bad(format!(
                "option '{}' expects an argument in the form <key>=<value>",
                option_name
            ))),
        }
    }

    pub fn config<'a>(value_ref: &'a RefCell<Vec<(String, String)>>) -> Entry<'a> {
        (
            "--config".to_string(),
            Spec::String(Box::new(move |value| {
                add_key_value("--config", value_ref, value)
            })),
            " override arbitrary value from hh.conf and .hhconfig (format: <key>=<value>)"
                .to_string(),
        )
    }

    pub fn custom_hhi_path<'a>(value_ref: &'a RefCell<Option<String>>) -> Entry<'a> {
        (
            "--custom-hhi-path".to_string(),
            Spec::String(Box::new(move |s| {
                *value_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " use custom hhi files".to_string(),
        )
    }

    pub fn custom_telemetry_data<'a>(value_ref: &'a RefCell<Vec<(String, String)>>) -> Entry<'a> {
        (
            "--custom-telemetry-data".to_string(),
            Spec::String(Box::new(move |value| {
                add_key_value("--custom-telemetry-data", value_ref, value)
            })),
            "Add a custom column to all logged telemetry samples (format: <column>=<value>)"
                .to_string(),
        )
    }

    pub fn force_dormant_start<'a>(value_ref: &'a Cell<bool>) -> Entry<'a> {
        (
            "--force-dormant-start".to_string(),
            Spec::Bool(Box::new(move |x| {
                value_ref.set(x);
                Ok(())
            })),
            " If server is dormant, force start a new one instead of waiting for".to_string()
                + " the next one to start up automatically (default: false)",
        )
    }

    pub fn from<'a>(value_ref: &'a RefCell<String>) -> Entry<'a> {
        (
            "--from".to_string(),
            Spec::SetString(value_ref),
            " so we know who's calling hh_client - e.g. nuclide, vim, emacs, vscode"
                // This setting also controls whether spinner is displayed, and whether
                // clientCheckStatus.ml uses error-formatting.
                .to_string(),
        )
    }

    pub fn no_prechecked<'a>(value_ref: &'a Cell<Option<bool>>) -> Entry<'a> {
        (
            "--no-prechecked".to_string(),
            Spec::Unit(Box::new(move || {
                value_ref.set(Some(false));
                Ok(())
            })),
            " override value of \"prechecked_files\" flag from hh.conf".to_string(),
        )
    }

    pub fn prechecked<'a>(value_ref: &'a Cell<Option<bool>>) -> Entry<'a> {
        (
            "--prechecked".to_string(),
            Spec::Unit(Box::new(move || {
                value_ref.set(Some(true));
                Ok(())
            })),
            " override value of \"prechecked_files\" flag from hh.conf".to_string(),
        )
    }

    pub fn with_mini_state<'a>(value_ref: &'a RefCell<Option<String>>) -> Entry<'a> {
        (
            "--with-mini-state".to_string(),
            Spec::String(Box::new(move |s| {
                *value_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " Init with the given saved state instead of the one based on current repo version."
                .to_string(),
        )
    }

    pub fn watchman_debug_logging<'a>(value_ref: &'a Cell<bool>) -> Entry<'a> {
        (
            "--watchman-debug-logging".to_string(),
            Spec::Set(value_ref),
            " Logs full Watchman requests and responses. This is very noisy".to_string(),
        )
    }

    pub fn allow_non_opt_build<'a>(value_ref: &'a Cell<bool>) -> Entry<'a> {
        (
            "--allow-non-opt-build".to_string(),
            Spec::Set(value_ref),
            " Override build mode check triggered by warn_on_non_opt_build .hhconfig option"
                .to_string(),
        )
    }

    pub fn ignore_hh_version<'a>(value_ref: &'a Cell<bool>) -> Entry<'a> {
        (
            "--ignore-hh-version".to_string(),
            Spec::Set(value_ref),
            " ignore hh_version check when loading saved states (default: false)".to_string(),
        )
    }

    pub fn saved_state_ignore_hhconfig<'a>(value_ref: &'a Cell<bool>) -> Entry<'a> {
        (
            "--saved-state-ignore-hhconfig".to_string(),
            Spec::Set(value_ref),
            " ignore hhconfig hash when loading saved states (default: false)".to_string(),
        )
    }

    pub fn naming_table<'a>(value_ref: &'a RefCell<Option<String>>) -> Entry<'a> {
        (
            "--naming-table".to_string(),
            Spec::String(Box::new(move |s| {
                *value_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " use the provided naming table instead of fetching it from a saved state"
                .to_string(),
        )
    }

    pub fn preexisting_warnings<'a>(preexisting_warnings: &'a Cell<bool>) -> Entry<'a> {
        (
            "--preexisting-warnings".to_string(),
            Spec::Set(preexisting_warnings),
            " show all preexisting warnings in typechecked files (default: false)".to_string(),
        )
    }
}

pub fn parse_command() -> CommandKeyword {
    let argv = ocaml_sys::argv();
    if argv.len() < 2 {
        CommandKeyword::CKNone
    } else {
        match argv[1].to_ascii_lowercase().as_str() {
            "check" => CommandKeyword::CKCheck,
            "start" => CommandKeyword::CKStart,
            "stop" => CommandKeyword::CKStop,
            "restart" => CommandKeyword::CKRestart,
            "lsp" => CommandKeyword::CKLsp,
            "saved-state-project-metadata" => CommandKeyword::CKSavedStateProjectMetadata,
            "download-saved-state" => CommandKeyword::CKDownloadSavedState,
            "rage" => CommandKeyword::CKRage,
            "decompress-zhhdg" => CommandKeyword::CKDecompressZhhdg,
            _ => CommandKeyword::CKNone,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgError {
    pub message: String,
    pub usage: Option<String>,
}

/// The exceptions that `parse_args` catches: `Arg.Help`, `Parse_error`, and
/// `Arg.Bad` raised outside `Arg`'s parse; and the `Exit_status.Exit_with`
/// that it lets through.
#[derive(Debug)]
pub enum Raised {
    /// `Arg.Help message`
    Help(String),
    /// `exception Parse_error of arg_error`
    ParseError(ArgError),
    /// `Arg.Bad message`
    Bad(String),
    /// `Exit_status.Exit_with`
    ExitWith(ExitWith),
}

impl PartialEq for Raised {
    /// (`Exit_with`s are equal when they show the same.)
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Raised::Help(a), Raised::Help(b)) => a == b,
            (Raised::ParseError(a), Raised::ParseError(b)) => a == b,
            (Raised::Bad(a), Raised::Bad(b)) => a == b,
            (Raised::ExitWith(ExitWith(a)), Raised::ExitWith(ExitWith(b))) => {
                exit_status::show(a) == exit_status::show(b)
            }
            _ => false,
        }
    }
}

/// An exception raised by a function that runs outside `Arg`'s parse.
fn raised_of_exn(e: Exn) -> Raised {
    match e {
        Exn::Bad(message) => Raised::Bad(message),
        Exn::Help(message) => Raised::Help(message),
        Exn::Stop(_) => unreachable!("Arg.Stop does not leave Arg"),
        Exn::Raise(e) => Raised::ExitWith(e),
    }
}

/// The first `is_interactive` of `client_args.ml` (on a `--from` value),
/// which the one on commands, [`is_interactive`], shadows there.
pub fn is_interactive_from(from: &str) -> bool {
    ["", "[sh]"].contains(&from)
}

/// On malformed command line args, ensure we record telemetry.
pub mod die {
    use super::*;

    fn log(_exit_code: isize, _exit_status: &exit_status::T, _e: &exception::T) {
        // Avoid the user seeing stderr from failures to write to scuba
        let stderr_level = hh_logger::level::min_level_stderr();
        hh_logger::level::set_min_level_stderr(hh_logger::level::T::Off);
        // `Utils.try_finally ~finally:(restore the level)`: the body is
        // `Hack_event_logger.client_init` (with placeholders: arg parsing
        // failed, so there is no trustworthy root, --from or
        // --custom-telemetry-data yet), `client_bad_args ~command_name:"Args"
        // ~exit_code exit_status e` and `flush`, with every exception but
        // `Exit_status.Exit_with` (hh_client's SIGINT handler raises it)
        // swallowed. Those are no-ops in the OSS build
        // (`stubs/logging/hack_event_logger.ml`), and `crate::hack_event_logger`
        // is compiled with `port` only, so they are not called.
        hh_logger::level::set_min_level_stderr(stderr_level);
    }

    fn die(exit_status: exit_status::T, e: exception::T) -> ! {
        let exit_code = exit_status::exit_code(&exit_status);
        log(exit_code, &exit_status, &e);
        stdlib_exit(exit_code as i32)
    }

    fn report(message: &str) {
        eprintln!("{}", message);
        let _ = std::io::stderr().flush();
    }

    /// Report [message] and optional [usage] on stderr, log [message] in a
    /// [CLIENT_BAD_ARGS] sample, and exit with [Exit_status.Client_bad_args].
    /// An empty [message] prints nothing, leaving [usage] to stand alone.
    pub fn bad_args(message: &str, usage: Option<&str>) -> ! {
        if !message.is_empty() {
            report(message);
        }
        if let Some(usage) = usage {
            report(usage);
        }
        die(
            exit_status::T::ClientBadArgs,
            exception::wrap(Exn::Bad(message.to_string())),
        )
    }

    /// Like [bad_args], but prefixes [message] with "Error:".
    pub fn bad_www_root(message: &str) -> ! {
        report(message);
        die(
            exit_status::T::ClientBadArgs,
            exception::wrap(Exn::Bad(message.to_string())),
        )
    }

    /// Log+re-raise. Should be unreachable:
    /// There is no reason to show a user a backtrace when they provide
    /// ill-formed command-line arguments to hh
    ///
    /// (`e` is never an `Exit_status.Exit_with`, which OCaml raises again
    /// as it is: the callers return that one as `Raised::ExitWith`.)
    pub fn internal_exception(e: exception::T) -> ! {
        // `Uncaught_exception e` holds the `e` that is logged and raised
        // again.
        let exit_status = exit_status::T::UncaughtException(e);
        let exit_code = exit_status::exit_code(&exit_status);
        if let exit_status::T::UncaughtException(e) = &exit_status {
            log(exit_code, &exit_status, e);
        }
        match exit_status {
            exit_status::T::UncaughtException(e) => exception::reraise(e),
            _ => unreachable!(),
        }
    }
}

pub fn parse_without_command(
    options: Vec<Entry<'_>>,
    usage: &str,
    command: &str,
) -> Result<Vec<String>, Raised> {
    let args: RefCell<Vec<String>> = RefCell::new(vec![]);
    let argv = ocaml_sys::argv();
    let mut speclist = ocaml_arg::align(options, None);
    let current = Cell::new(0);
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        ocaml_arg::parse_argv(
            Some(&current),
            &argv,
            &mut speclist,
            &mut |x| {
                args.borrow_mut().push(x);
                Ok(())
            },
            usage,
        )
    }));
    match result {
        Ok(Ok(())) => {}
        // [Arg] newline-terminates its messages and the rest of hh_client's are
        // unterminated; drop it here so everything downstream has one convention.
        Ok(Err(Exn::Bad(message))) => {
            let message = message.strip_suffix('\n').unwrap_or(&message);
            let (message, usage) = match message.split_once('\n') {
                None => (message.to_string(), None),
                Some((message, usage)) => (message.to_string(), Some(usage.to_string())),
            };
            return Err(Raised::ParseError(ArgError { message, usage }));
        }
        Ok(Err(Exn::Help(help))) => return Err(Raised::Help(help)),
        Ok(Err(Exn::Stop(_))) => unreachable!("Arg.parse_argv converts Stop"),
        // `Die.internal_exception` raises an `Exit_with` again as it is.
        Ok(Err(Exn::Raise(exit_with))) => return Err(Raised::ExitWith(exit_with)),
        Err(payload) => die::internal_exception(exception::wrap(payload)),
    }
    let args = args.into_inner();
    match args.as_slice() {
        [x, rest @ ..] if x.to_ascii_lowercase() == command.to_ascii_lowercase() => {
            Ok(rest.to_vec())
        }
        _ => Ok(args),
    }
}

pub fn interpret_root(paths: &[String]) -> path::T {
    match std::panic::catch_unwind(|| wwwroot::interpret_command_line_root_parameter(paths)) {
        Err(payload) => die::internal_exception(exception::wrap(payload)),
        Ok(Err(sys_error)) => die::internal_exception(exception::wrap(sys_error)),
        Ok(Ok(Ok(root))) => root,
        Ok(Ok(Err(message))) => die::bad_www_root(&format!("Error: {}", message)),
    }
}

pub fn validate_check_args(invalid_warning_codes: &[isize]) {
    if !invalid_warning_codes.is_empty() {
        die::bad_args(
            &format!(
                "Unknown warning codes: {}",
                invalid_warning_codes
                    .iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            None,
        )
    }
}

/// `Unix.time ()`: the time in seconds, to the second.
fn unix_time() -> f64 {
    // SAFETY: `time(NULL)` only returns the time.
    unsafe { libc::time(std::ptr::null_mut()) as f64 }
}

/// `Base.String.strip`: without the whitespace (` `, `\t`, `\n`, `\x0b`,
/// `\x0c`, `\r`) at both ends.
fn base_strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
}

/// `In_channel.read_all f`: the contents of the file, or the `Sys_error` of
/// opening it (`"<f>: <error>"`) or of reading it (`"<error>"`). Bytes that
/// are not UTF-8 become U+FFFD.
fn in_channel_read_all(f: &str) -> Result<String, SysError> {
    let mut file = std::fs::File::open(f).map_err(|e| SysError::of_io_error(f, &e))?;
    let mut contents = vec![];
    file.read_to_end(&mut contents).map_err(|e| {
        let SysError(message) = SysError::of_io_error("", &e);
        SysError(message.strip_prefix(": ").unwrap_or(&message).to_string())
    })?;
    Ok(String::from_utf8_lossy(&contents).into_owned())
}

/// `x :: xs`
fn cons<A: Clone>(x: A, xs: &[A]) -> Vec<A> {
    let mut v = Vec::with_capacity(xs.len() + 1);
    v.push(x);
    v.extend_from_slice(xs);
    v
}

fn single_mode_error() -> Exn {
    Exn::Bad("only a single mode should be specified".to_string())
}

fn opt<'a>(key: &str, spec: Spec<'a>, doc: &str, kind: ArgKind) -> (String, Spec<'a>, String, ArgKind) {
    (key.to_string(), spec, doc.to_string(), kind)
}

fn tuple_3_append<'a>((a1, a2, a3): Entry<'a>, a4: ArgKind) -> (String, Spec<'a>, String, ArgKind) {
    (a1, a2, a3, a4)
}

/// `modify_callback option callback`: the callback, which records `option`
/// in `current_option` while it runs (and leaves it there if it raises).
fn modify_callback<'a, A: 'a>(
    current_option: &'a RefCell<Option<String>>,
    option: &str,
    mut callback: Box<dyn FnMut(A) -> Res + 'a>,
) -> Box<dyn FnMut(A) -> Res + 'a> {
    let option = option.to_string();
    Box::new(move |value| {
        *current_option.borrow_mut() = Some(option.clone());
        callback(value)?;
        *current_option.borrow_mut() = None;
        Ok(())
    })
}

fn modify_spec<'a>(
    current_option: &'a RefCell<Option<String>>,
    option: &str,
    spec: Spec<'a>,
) -> Spec<'a> {
    match spec {
        Spec::Unit(mut callback) => {
            let mut callback = modify_callback(current_option, option, Box::new(move |()| callback()));
            Spec::Unit(Box::new(move || callback(())))
        }
        Spec::Bool(callback) => Spec::Bool(modify_callback(current_option, option, callback)),
        Spec::String(callback) => Spec::String(modify_callback(current_option, option, callback)),
        Spec::Int(callback) => Spec::Int(modify_callback(current_option, option, callback)),
        Spec::Float(callback) => Spec::Float(modify_callback(current_option, option, callback)),
        Spec::Rest(callback) => Spec::Rest(modify_callback(current_option, option, callback)),
        Spec::Tuple(specs) => Spec::Tuple(
            specs
                .into_iter()
                .map(|spec| modify_spec(current_option, option, spec))
                .collect(),
        ),
        spec => spec,
    }
}

fn to_arg_specs(options: Vec<(String, Spec<'_>, String, ArgKind)>) -> Vec<Entry<'_>> {
    options
        .into_iter()
        .map(|(key, spec, doc, _kind)| (key, spec, doc))
        .collect()
}

fn ultrahelp_entry<'a>() -> Entry<'a> {
    (
        "--ultrahelp".to_string(),
        Spec::Unit(Box::new(|| Ok(()))),
        " see full options (for language and release teams)".to_string(),
    )
}

// *** *** NB *** *** ***
// Commonly-used options are documented in hphp/hack/man/hh_client.1 --
// if you are making significant changes you need to update the manpage as
// well. Experimental or otherwise volatile options need not be documented
// there, but keep what's there up to date please.
pub fn parse_check_args(cmd: CommandKeyword, from_default: &str) -> Result<ClientCheckEnv, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    // arg parse output refs
    let autostart = Cell::new(true);
    let config: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let custom_telemetry_data: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let custom_hhi_path: RefCell<Option<String>> = RefCell::new(None);
    let error_format: Cell<Option<diagnostics_state::Format>> = Cell::new(None);
    let force_dormant_start = Cell::new(false);
    let from = RefCell::new(from_default.to_string());
    let show_spinner: Cell<Option<bool>> = Cell::new(None);
    let show_tast = Cell::new(false);
    let ignore_hh_version = Cell::new(false);
    let save_64bit: RefCell<Option<String>> = RefCell::new(None);
    let save_human_readable_64bit_dep_map: RefCell<Option<String>> = RefCell::new(None);
    let saved_state_ignore_hhconfig = Cell::new(false);
    let max_errors: Cell<Option<isize>> = Cell::new(None);
    let mode: RefCell<Option<ClientMode>> = RefCell::new(None);
    let logname = Cell::new(false);
    let monitor_logname = Cell::new(false);
    let client_logname = Cell::new(false);
    let ide_logname = Cell::new(false);
    let lsp_logname = Cell::new(false);
    let lock_file = Cell::new(false);
    let no_load = Cell::new(false);
    let output_json = Cell::new(false);
    let output_jsonl = Cell::new(false);
    let prechecked: Cell<Option<bool>> = Cell::new(None);
    let mini_state: RefCell<Option<String>> = RefCell::new(None);
    let rename_before = RefCell::new(String::new());
    let sort_results = Cell::new(false);
    let stdin_name: RefCell<Option<String>> = RefCell::new(None);
    let timeout: Cell<Option<f64>> = Cell::new(None);
    let version = Cell::new(false);
    let watchman_debug_logging = Cell::new(false);
    let allow_non_opt_build = Cell::new(false);
    let preexisting_warnings = Cell::new(false);
    let reason: RefCell<Option<String>> = RefCell::new(None);
    let warning_switches: RefCell<Vec<filter_diagnostics::Switch>> = RefCell::new(vec![]);
    let invalid_warning_codes: RefCell<Vec<isize>> = RefCell::new(vec![]);
    let desc = RefCell::new(client_command::command_name(cmd).to_string());
    // custom behaviors
    let current_option: RefCell<Option<String>> = RefCell::new(None);
    let dump_config = Cell::new(false);

    let from_ref = &from;
    let set_from = move |x: &'static str| {
        move || -> Res {
            *from_ref.borrow_mut() = x.to_string();
            Ok(())
        }
    };
    let single_files: RefCell<Vec<String>> = RefCell::new(vec![]);
    let only_log_errors = Cell::new(false);
    let log_to_file: RefCell<Option<String>> = RefCell::new(None);
    let (mode_ref, current_option_ref, desc_ref) = (&mode, &current_option, &desc);
    let set_mode = move |validate: Option<bool>, x: ClientMode| -> Res {
        let validate = validate.unwrap_or(true);
        if validate && mode_ref.borrow().is_some() {
            Err(single_mode_error())
        } else {
            *mode_ref.borrow_mut() = Some(x);
            if let Some(option) = &*current_option_ref.borrow() {
                *desc_ref.borrow_mut() = option.clone();
            }
            Ok(())
        }
    };
    let single_files_ref = &single_files;
    let add_single = move |x: String| -> Res {
        single_files_ref.borrow_mut().insert(0, x);
        Ok(())
    };
    let log_to_file_ref = &log_to_file;
    let set_log_to_file = move |x: String| -> Res {
        *log_to_file_ref.borrow_mut() = Some(x);
        Ok(())
    };
    let add_multi = move |f: String| -> Res {
        let files = match in_channel_read_all(&f) {
            Ok(contents) => contents,
            Err(SysError(message)) => {
                return Err(Exn::Bad(format!("could not read --multi file: {}", message)));
            }
        };
        let files: Vec<String> = base_strip(&files).split('\n').map(str::to_string).collect();
        let mut single_files = single_files_ref.borrow_mut();
        let rest = std::mem::take(&mut *single_files);
        *single_files = files;
        single_files.extend(rest);
        Ok(())
    };
    let warning_switches_ref = &warning_switches;
    let add_warning_switch = move |switch: filter_diagnostics::Switch| {
        warning_switches_ref.borrow_mut().insert(0, switch);
    };
    let invalid_warning_codes_ref = &invalid_warning_codes;
    let add_invalid_warning_code = move |i: isize| {
        invalid_warning_codes_ref.borrow_mut().insert(0, i);
    };
    let set_mode_from_single_files = |show_tast: bool, preexisting_warnings: bool| -> Res {
        let single_files = single_files.borrow().clone();
        match single_files.as_slice() {
            [] => Ok(()),
            _ => set_mode(
                None,
                MODESTATUSSINGLE(StatusSingle {
                    filenames: single_files,
                    show_tast,
                    preexisting_warnings,
                }),
            ),
        }
    };
    let set_mode_only_log_errors = |config: LogErrorsParams| -> Res {
        if only_log_errors.get() {
            set_mode(None, MODELOGERRORS(config))
        } else {
            Ok(())
        }
    };
    // parse args
    let usage = match cmd {
        CommandKeyword::CKCheck => format!(
            "Usage: {} check [OPTION]... [WWW-ROOT]\n\nWWW-ROOT is assumed to be current directory if unspecified\n",
            argv0
        ),
        CommandKeyword::CKNone => format!(
            "Usage: {} [COMMAND] [OPTION]... [WWW-ROOT]\n\nValid values for COMMAND:\n\
             \tcheck\t\tShows current Hack errors\n\
             \tstart\t\tStarts a Hack server\n\
             \tstop\t\tStops a Hack server\n\
             \trestart\t\tRestarts a Hack server\n\
             \tlsp\t\tRuns a persistent language service\n\
             \trage\t\tReport a bug\n\
             \nDefault values if unspecified:\n\
             \tCOMMAND\t\tcheck\n\
             \tWWW-ROOT\tCurrent directory\n\nCheck command options:\n",
            argv0
        ),
        CommandKeyword::CKSavedStateProjectMetadata => format!(
            "Usage: {} saved-state-project-metadata [OPTION]... [WWW-ROOT]\nOutput the project metadata for the current saved state\n\nWWW-ROOT is assumed to be current directory if unspecified\n",
            argv0
        ),
        CommandKeyword::CKDownloadSavedState
        | CommandKeyword::CKLsp
        | CommandKeyword::CKRage
        | CommandKeyword::CKRestart
        | CommandKeyword::CKStart
        | CommandKeyword::CKDecompressZhhdg
        | CommandKeyword::CKStop => panic!("No other keywords should make it here"),
    };
    // The local refs of the `Arg.Tuple` options.
    let ide_find_refs_by_symbol3_action = RefCell::new(String::new());
    let ide_find_refs_by_symbol3_stream_file = RefCell::new("-".to_string());
    let notebook_number = RefCell::new(String::new());
    let package_lint_full_target_file = RefCell::new(String::new());
    let rename_mode = Cell::new(RenameMode::Unspecified);
    let (action_ref, stream_file_ref) = (
        &ide_find_refs_by_symbol3_action,
        &ide_find_refs_by_symbol3_stream_file,
    );
    let (notebook_number_ref, target_file_ref, rename_mode_ref, rename_before_ref) = (
        &notebook_number,
        &package_lint_full_target_file,
        &rename_mode,
        &rename_before,
    );
    let (config_ref, prechecked_ref, error_format_ref) = (&config, &prechecked, &error_format);
    let (timeout_ref, reason_ref, show_spinner_ref, show_tast_ref) =
        (&timeout, &reason, &show_spinner, &show_tast);
    let (max_errors_ref, save_64bit_ref, save_hr_ref, stdin_name_ref) = (
        &max_errors,
        &save_64bit,
        &save_human_readable_64bit_dep_map,
        &stdin_name,
    );
    let (only_log_errors_ref, autostart_ref) = (&only_log_errors, &autostart);
    // A batch mode (`Arg.Rest`): the first position, or one more for the same
    // mode.
    let options: Vec<(String, Spec<'_>, String, ArgKind)> = vec![
        // Please keep these sorted in the alphabetical order.
        tuple_3_append(
            common_argspecs::allow_non_opt_build(&allow_non_opt_build),
            ArgNonUserFacing,
        ),
        opt(
            "--autostart-server",
            Spec::Bool(Box::new(move |b| {
                autostart_ref.set(b);
                Ok(())
            })),
            " automatically start hh_server if it's not running (default: true)",
            ArgNonUserFacing,
        ),
        tuple_3_append(common_argspecs::config(&config), ArgUserFacing),
        opt(
            "--cst-search",
            Spec::Unit(Box::new(move || set_mode(None, MODECSTSEARCH(None)))),
            &(" (mode) Search the concrete syntax trees of files in the codebase".to_string()
                + " for a given pattern"),
            ArgNonUserFacing,
        ),
        opt(
            "--cst-search-files",
            Spec::Rest(Box::new(move |fn_: String| {
                let m = match &*mode_ref.borrow() {
                    None | Some(MODECSTSEARCH(None)) => MODECSTSEARCH(Some(vec![fn_])),
                    Some(MODECSTSEARCH(Some(fnl))) => MODECSTSEARCH(Some(cons(fn_, fnl))),
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            &(" Run CST search on this set of files,".to_string()
                + " rather than all the files in the codebase."),
            ArgNonUserFacing,
        ),
        tuple_3_append(
            common_argspecs::custom_hhi_path(&custom_hhi_path),
            ArgNonUserFacing,
        ),
        tuple_3_append(
            common_argspecs::custom_telemetry_data(&custom_telemetry_data),
            ArgNonUserFacing,
        ),
        opt(
            "--deps-out-at-pos-batch",
            Spec::Rest(Box::new(move |position: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEDEPSOUTATPOSBATCH(vec![position]),
                    Some(MODEDEPSOUTATPOSBATCH(positions)) => {
                        MODEFUNDEPSATPOSBATCH(cons(position, positions))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) for each entry in input list get list of what it depends on [file:line:character list]",
            ArgUserFacing,
        ),
        opt(
            "--deps-in-at-pos-batch",
            Spec::Rest(Box::new(move |position: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEDEPSINATPOSBATCH(vec![position]),
                    Some(MODEDEPSINATPOSBATCH(positions)) => {
                        MODEDEPSINATPOSBATCH(cons(position, positions))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) for each entry in input list get list of what depends on it [file:line:character list]",
            ArgUserFacing,
        ),
        opt(
            "--dump-config",
            Spec::Set(&dump_config),
            " Output configuration",
            ArgNonUserFacing,
        ),
        opt(
            "--dump-full-fidelity-parse",
            Spec::String(Box::new(move |x| set_mode(None, MODEFULLFIDELITYPARSE(x)))),
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--dump-symbol-info",
            Spec::String(Box::new(move |files| {
                set_mode(None, MODEDUMPSYMBOLINFO(files))
            })),
            //  Input format:
            //  The file list can either be "-" which accepts the input from stdin
            //  separated by newline(for long list) or directly from command line
            //  separated by semicolon.
            //  Output format:
            //    [
            //      "function_calls": list of fun_calls;
            //    ]
            //  Note: results list can be in any order
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--error-format",
            Spec::String(Box::new(move |s| {
                use diagnostics_state::Format;
                match s.as_str() {
                    "raw" => error_format_ref.set(Some(Format::Raw)),
                    "agent" => error_format_ref.set(Some(Format::Agent)),
                    "plain" => error_format_ref.set(Some(Format::Plain)),
                    "context" => error_format_ref.set(Some(Format::Context)),
                    "highlighted" => error_format_ref.set(Some(Format::Highlighted)),
                    "extended" => error_format_ref.set(Some(Format::Extended)),
                    "plain_highlighted" => error_format_ref.set(Some(Format::PlainHighlighted)),
                    _ => print!("Warning: unrecognized error format.\n"),
                }
                Ok(())
            })),
            "<format> Error formatting style (default: highlighted); valid formats: agent, extended, raw, context, highlighted, plain, plain_highlighted",
            ArgUserFacing,
        ),
        opt(
            "--enforcement-at-pos-batch",
            Spec::Rest(Box::new(move |position: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEENFORCEMENTATPOSBATCH(vec![position]),
                    Some(MODEENFORCEMENTATPOSBATCH(positions)) => {
                        MODEENFORCEMENTATPOSBATCH(cons(position, positions))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) show enforcement at multiple positions [file:line:character list]",
            ArgUserFacing,
        ),
        opt(
            "--file-dependents",
            Spec::Unit(Box::new(move || {
                prechecked_ref.set(Some(false));
                set_mode(None, MODEFILELEVELDEPENDENCIES)
            })),
            " (mode) Given a list of filepaths, shows list of (possibly) dependent files",
            ArgUserFacing,
        ),
        opt(
            "--find-class-refs",
            Spec::String(Box::new(move |x| set_mode(None, MODEFINDCLASSREFS(x)))),
            " (mode) finds references of the provided class name",
            ArgUserFacing,
        ),
        opt(
            "--find-isolatable-clusters",
            Spec::Unit(Box::new(move || set_mode(None, MODEFINDISOLATABLECLUSTERS))),
            " (mode) find clusters of files that can be isolated from the codebase",
            ArgNonUserFacing,
        ),
        opt(
            "--find-refs",
            Spec::String(Box::new(move |x| set_mode(None, MODEFINDREFS(x)))),
            &(" (mode) finds references of the provided symbol; optionally specify the symbol kind like \"Kind|Symbol\" (looks for functions or methods if unspecified)".to_string()
                + "; valid kinds are Method, Property, Class_const, Typeconst, Function, Class, ExplicitClass, and GConst"
                + "; use ExplicitClass instead of Class to exclude references via self/static/parent"),
            ArgUserFacing,
        ),
        opt(
            "--find-my-tests",
            Spec::String(Box::new(move |path| set_mode(Some(true), MODEFINDMYTESTS(path)))),
            " (mode) return test files that reference the given symbols, using the version specified in the JSON config (default: staging)",
            ArgNonUserFacing,
        ),
        opt(
            "--find-my-tests-staging",
            Spec::String(Box::new(move |path| set_mode(Some(true), MODEFINDMYTESTS(path)))),
            " (deprecated, use --find-my-tests) alias for --find-my-tests",
            ArgNonUserFacing,
        ),
        tuple_3_append(
            common_argspecs::force_dormant_start(&force_dormant_start),
            ArgNonUserFacing,
        ),
        tuple_3_append(common_argspecs::from(&from), ArgUserFacing),
        opt(
            "--from-arc-diff",
            Spec::Unit(Box::new(set_from("arc_diff"))),
            " (deprecated) equivalent to --from arc_diff",
            ArgNonUserFacing,
        ),
        opt(
            "--from-arc-land",
            Spec::Unit(Box::new(set_from("arc_land"))),
            " (deprecated) equivalent to --from arc_land",
            ArgNonUserFacing,
        ),
        opt(
            "--from-check-trunk",
            Spec::Unit(Box::new(set_from("check_trunk"))),
            " (deprecated) equivalent to --from check_trunk",
            ArgNonUserFacing,
        ),
        opt(
            "--from-emacs",
            Spec::Unit(Box::new(set_from("emacs"))),
            " (deprecated) equivalent to --from emacs",
            ArgNonUserFacing,
        ),
        opt(
            "--from-vim",
            Spec::Unit(Box::new(move || {
                *from_ref.borrow_mut() = "vim".to_string();
                Ok(())
            })),
            " (deprecated) equivalent to --from vim",
            ArgNonUserFacing,
        ),
        opt(
            "--full-fidelity-schema",
            Spec::Unit(Box::new(move || set_mode(None, MODEFULLFIDELITYSCHEMA))),
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--fun-deps-at-pos-batch",
            Spec::Rest(Box::new(move |position: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEFUNDEPSATPOSBATCH(vec![position]),
                    Some(MODEFUNDEPSATPOSBATCH(positions)) => {
                        MODEFUNDEPSATPOSBATCH(cons(position, positions))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) for each entry in input list get list of function dependencies [file:line:character list]",
            ArgNonUserFacing,
        ),
        opt(
            "--get-method-name",
            Spec::String(Box::new(move |x| set_mode(None, MODEIDENTIFYSYMBOL3(x)))),
            // alias for --identify-function
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--go-to-impl-class",
            Spec::String(Box::new(move |x| set_mode(None, MODEGOTOIMPLCLASS(x)))),
            " (mode) goes to implementation of the provided class/trait/interface/etc. with the given name",
            ArgNonUserFacing,
        ),
        opt(
            "--go-to-impl-method",
            Spec::String(Box::new(move |x| set_mode(None, MODEGOTOIMPLMETHOD(x)))),
            " (mode) goes to implementation of the provided method name",
            ArgNonUserFacing,
        ),
        opt(
            "--hack-to-notebook",
            Spec::Unit(Box::new(move || set_mode(None, MODEHACKTONOTEBOOK))),
            "Convert a Hack file generated by `hh --notebook-to-hack` into a notebook. Pass hack file contents via stdin",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-find-refs-by-symbol",
            Spec::String(Box::new(move |x| {
                let args = find_refs_wire_format::cli_args::from_string_exn(&x).map_err(Exn::Raise)?;
                set_mode(None, MODEIDEFINDREFSBYSYMBOL(args))
            })),
            "(mode) similar to IDE_FIND_REFS, but takes a symbol name rather than position",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-find-refs-by-symbol3",
            Spec::Tuple(vec![
                Spec::String(Box::new(move |s| {
                    *action_ref.borrow_mut() = s;
                    Ok(())
                })),
                Spec::String(Box::new(move |s| {
                    *stream_file_ref.borrow_mut() = s;
                    Ok(())
                })),
                Spec::String(Box::new(move |hints| {
                    let args = find_refs_wire_format::cli_args::from_string_triple_exn((
                        &action_ref.borrow(),
                        &stream_file_ref.borrow(),
                        &hints,
                    ))
                    .map_err(Exn::Raise)?;
                    set_mode(None, MODEIDEFINDREFSBYSYMBOL(args))
                })),
            ]),
            "(mode) similar to FIND_REFS, but takes [action stream_file hints]",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-go-to-impl-by-symbol",
            Spec::String(Box::new(move |x| {
                let args = find_refs_wire_format::cli_args::from_string_exn(&x).map_err(Exn::Raise)?;
                set_mode(None, MODEIDEGOTOIMPLBYSYMBOL(args))
            })),
            "(mode) similar to IDE_GO_TO_IMPL, but takes a symbol name rather than position",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-get-definition",
            Spec::String(Box::new(move |x| set_mode(None, MODEIDENTIFYSYMBOL2(x)))),
            // alias for --identify-function
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-outline",
            Spec::Unit(Box::new(move || set_mode(None, MODEOUTLINE2))),
            "",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-rename-by-symbol",
            Spec::String(Box::new(move |x| set_mode(None, MODEIDERENAMEBYSYMBOL(x)))),
            &(" (mode) renames, but takes a Find_refs.action. Usage: ".to_string()
                + " <new name>|<comma_separated_action>"),
            ArgNonUserFacing,
        ),
        opt(
            "--identify-function",
            Spec::String(Box::new(move |x| set_mode(None, MODEIDENTIFYSYMBOL1(x)))),
            &(" (mode) print the full function name at the position ".to_string()
                + "[line:character] of the text on stdin"),
            ArgUserFacing,
        ),
        opt(
            "--identify",
            Spec::String(Box::new(move |x| set_mode(None, MODEIDENTIFYSYMBOL(x)))),
            " (mode) identify the named symbol",
            ArgUserFacing,
        ),
        tuple_3_append(
            common_argspecs::ignore_hh_version(&ignore_hh_version),
            ArgNonUserFacing,
        ),
        opt(
            "--in-memory-dep-table-size",
            Spec::Unit(Box::new(move || set_mode(None, MODEINMEMORYDEPTABLESIZE))),
            " number of entries in the in-memory dependency table",
            ArgNonUserFacing,
        ),
        opt(
            "--inheritance-ancestor-classes",
            Spec::String(Box::new(move |x| {
                set_mode(None, MODEMETHODJUMPANCESTORS(x, "Class".to_string()))
            })),
            " (mode) prints a list of classes that this class extends",
            // can use --inheritance-ancestor-classes-batch
            ArgNonUserFacing,
        ),
        opt(
            "--inheritance-ancestor-classes-batch",
            Spec::Rest(Box::new(move |class_: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEMETHODJUMPANCESTORSBATCH(vec![class_], "Class".to_string()),
                    Some(MODEMETHODJUMPANCESTORSBATCH(classes, filter)) if filter == "Class" => {
                        MODEMETHODJUMPANCESTORSBATCH(cons(class_, classes), "Class".to_string())
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) prints a list of classes that these classes extend",
            ArgUserFacing,
        ),
        opt(
            "--inheritance-ancestor-interfaces",
            Spec::String(Box::new(move |x| {
                set_mode(None, MODEMETHODJUMPANCESTORS(x, "Interface".to_string()))
            })),
            " (mode) prints a list of interfaces that this class implements",
            // can use --inheritance-ancestor-interfaces-batch
            ArgNonUserFacing,
        ),
        opt(
            "--inheritance-ancestor-interfaces-batch",
            Spec::Rest(Box::new(move |class_: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEMETHODJUMPANCESTORSBATCH(vec![class_], "Interface".to_string()),
                    Some(MODEMETHODJUMPANCESTORSBATCH(classes, filter))
                        if filter == "Interface" =>
                    {
                        MODEMETHODJUMPANCESTORSBATCH(
                            cons(class_, classes),
                            "Interface".to_string(),
                        )
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) prints a list of interfaces that these classes implement",
            ArgUserFacing,
        ),
        opt(
            "--inheritance-ancestor-traits",
            Spec::String(Box::new(move |x| {
                set_mode(None, MODEMETHODJUMPANCESTORS(x, "Trait".to_string()))
            })),
            " (mode) prints a list of traits that this class uses",
            // can use --inheritance-ancestor-traits-batch
            ArgNonUserFacing,
        ),
        opt(
            "--inheritance-ancestor-traits-batch",
            Spec::Rest(Box::new(move |class_: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEMETHODJUMPANCESTORSBATCH(vec![class_], "Trait".to_string()),
                    Some(MODEMETHODJUMPANCESTORSBATCH(classes, filter)) if filter == "Trait" => {
                        MODEMETHODJUMPANCESTORSBATCH(cons(class_, classes), "Trait".to_string())
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) prints a list of traits that these classes use",
            ArgUserFacing,
        ),
        opt(
            "--inheritance-ancestors",
            Spec::String(Box::new(move |x| {
                set_mode(None, MODEMETHODJUMPANCESTORS(x, "No_filter".to_string()))
            })),
            &(" (mode) prints a list of all related classes or methods".to_string()
                + " to the given class"),
            ArgUserFacing,
        ),
        opt(
            "--inheritance-children",
            Spec::String(Box::new(move |x| set_mode(None, MODEMETHODJUMPCHILDREN(x)))),
            &(" (mode) prints a list of all related classes or methods".to_string()
                + " to the given class"),
            ArgUserFacing,
        ),
        opt(
            "--json",
            Spec::Set(&output_json),
            " output json for machine consumption (default: false)",
            ArgUserFacing,
        ),
        opt(
            "--jsonl",
            Spec::Set(&output_jsonl),
            " output streaming jsonl (JSON Lines) for machine consumption (default: false)",
            ArgUserFacing,
        ),
        opt(
            "--lint",
            Spec::Unit(Box::new(move || set_mode(None, MODELINT))),
            " (mode) lint the given list of files",
            ArgUserFacing,
        ),
        opt(
            "--lint-all",
            Spec::Int(Box::new(move |x| set_mode(None, MODELINTALL(x)))),
            " (mode) find all occurrences of lint with the given error code",
            ArgUserFacing,
        ),
        opt(
            "--lint-stdin",
            Spec::String(Box::new(move |filename| {
                set_mode(None, MODELINTSTDIN(filename))
            })),
            &(" (mode) lint a file given on stdin; the filename should be the".to_string()
                + " argument to this option"),
            ArgUserFacing,
        ),
        opt(
            "--list-files",
            Spec::Unit(Box::new(move || set_mode(None, MODELISTFILES))),
            " (mode) list files with errors",
            ArgUserFacing,
        ),
        opt(
            "--lock-file",
            Spec::Set(&lock_file),
            " (mode) show lock file name and exit",
            ArgNonUserFacing,
        ),
        opt(
            "--max-errors",
            Spec::Int(Box::new(move |num_errors| {
                max_errors_ref.set(Some(num_errors));
                Ok(())
            })),
            " Maximum number of errors to display",
            ArgUserFacing,
        ),
        tuple_3_append(
            common_argspecs::preexisting_warnings(&preexisting_warnings),
            ArgUserFacing,
        ),
        opt(
            "--logname",
            Spec::Set(&logname),
            " (mode) show log filename and exit",
            ArgUserFacing,
        ),
        opt(
            "--monitor-logname",
            Spec::Set(&monitor_logname),
            " (mode) show monitor log filename and exit",
            ArgNonUserFacing,
        ),
        opt(
            "--client-logname",
            Spec::Set(&client_logname),
            " (mode) show client log filename and exit",
            ArgNonUserFacing,
        ),
        opt(
            "--ide-logname",
            Spec::Set(&ide_logname),
            " (mode) show client ide log filename and exit",
            ArgNonUserFacing,
        ),
        opt(
            "--lsp-logname",
            Spec::Set(&lsp_logname),
            " (mode) show client lsp log filename and exit",
            ArgNonUserFacing,
        ),
        opt(
            "--no-load",
            Spec::Set(&no_load),
            " start from a fresh state",
            ArgNonUserFacing,
        ),
        opt(
            "--notebook-to-hack",
            Spec::Tuple(vec![
                Spec::String(Box::new(move |s| {
                    *notebook_number_ref.borrow_mut() = s;
                    Ok(())
                })),
                Spec::String(Box::new(move |notebook_header| {
                    let notebook_number = notebook_number_ref.borrow().clone();
                    set_mode(
                        None,
                        MODENOTEBOOKTOHACK {
                            notebook_number,
                            notebook_header,
                        },
                    )
                })),
            ]),
            &("Convert notebook to a Hack file. Arg: notebook_number (example: \"N12345\"). ".to_string()
                + "Pass notebook in .ipynb format to stdin and a header (such as a copyright notice comment)"),
            ArgNonUserFacing,
        ),
        opt(
            "--outline",
            Spec::Unit(Box::new(move || set_mode(None, MODEOUTLINE))),
            " (mode) prints an outline of the text on stdin",
            ArgUserFacing,
        ),
        opt(
            "--outline-for-agents",
            Spec::String(Box::new(move |x| set_mode(None, MODEOUTLINEFORAGENTS(x)))),
            " <file> (mode) outline the file, including line spans, to help agents efficiently navigate large files",
            ArgUserFacing,
        ),
        opt(
            "--package-lint",
            Spec::String(Box::new(move |x| set_mode(None, MODEPACKAGELINT(x)))),
            "Support for linting of __PackageOverride annotations",
            ArgNonUserFacing,
        ),
        opt(
            "--package-lint-full",
            Spec::Tuple(vec![
                Spec::String(Box::new(move |s| {
                    *target_file_ref.borrow_mut() = s;
                    Ok(())
                })),
                Spec::String(Box::new(move |candidates_csv| {
                    // `String.split ~on:','` (every piece), without the empty ones.
                    let candidates: Vec<String> = candidates_csv
                        .split(',')
                        .filter(|s| !s.is_empty())
                        .map(str::to_string)
                        .collect();
                    if candidates.is_empty() {
                        return Err(Exn::Bad(
                            "--package-lint-full requires at least one candidate file".to_string(),
                        ));
                    }
                    let target_file = target_file_ref.borrow().clone();
                    set_mode(None, MODEPACKAGELINTFULL((target_file, candidates)))
                })),
            ]),
            " <target_file> <file1,file2,...> Package-aware find-refs lint",
            ArgNonUserFacing,
        ),
        opt(
            "--pause",
            Spec::Unit(Box::new(move || set_mode(None, MODEPAUSE))),
            " pause automatic rechecks after current work finishes; the next client request resumes them",
            ArgNonUserFacing,
        ),
        tuple_3_append(common_argspecs::prechecked(&prechecked), ArgNonUserFacing),
        tuple_3_append(common_argspecs::no_prechecked(&prechecked), ArgNonUserFacing),
        tuple_3_append(
            common_argspecs::with_mini_state(&mini_state),
            ArgNonUserFacing,
        ),
        opt(
            "--profile-log",
            Spec::Unit(Box::new(move || {
                config_ref
                    .borrow_mut()
                    .insert(0, ("profile_log".to_string(), "true".to_string()));
                Ok(())
            })),
            " enable profile logging",
            ArgNonUserFacing,
        ),
        opt(
            "--refactor",
            Spec::Tuple(vec![
                Spec::Symbol(
                    vec![
                        "Class".to_string(),
                        "Function".to_string(),
                        "Method".to_string(),
                    ],
                    Box::new(move |x| {
                        rename_mode_ref.set(client_env::string_to_rename_mode(&x));
                        Ok(())
                    }),
                ),
                Spec::String(Box::new(move |x| {
                    *rename_before_ref.borrow_mut() = x;
                    Ok(())
                })),
                Spec::String(Box::new(move |x| {
                    let rename_before = rename_before_ref.borrow().clone();
                    set_mode(None, MODERENAME(rename_mode_ref.get(), rename_before, x))
                })),
            ]),
            &(" (mode) rename a symbol, Usage: --refactor ".to_string()
                + "[\"Class\", \"Function\", \"Method\"] <Current Name> <New Name>"),
            ArgUserFacing,
        ),
        opt(
            "--remove-dead-fixme",
            Spec::Int(Box::new(move |code| {
                let m = match &*mode_ref.borrow() {
                    None => MODEREMOVEDEADFIXMES(vec![code]),
                    Some(MODEREMOVEDEADFIXMES(codel)) => MODEREMOVEDEADFIXMES(cons(code, codel)),
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            &(" (mode) remove dead HH_FIXME for specified error code ".to_string()
                + "(first do hh_client restart --no-load)"),
            ArgNonUserFacing,
        ),
        opt(
            "--remove-dead-fixmes",
            Spec::Unit(Box::new(move || set_mode(None, MODEREMOVEDEADFIXMES(vec![])))),
            &(" (mode) remove dead HH_FIXME for any error code < 5000 ".to_string()
                + "(first do hh_client restart --no-load)"),
            ArgNonUserFacing,
        ),
        opt(
            "--remove-dead-unsafe-casts",
            Spec::Unit(Box::new(move || set_mode(None, MODEREMOVEDEADUNSAFECASTS))),
            " (mode) remove dead UNSAFE_CASTS (first do hh_client restart --no-load)",
            ArgNonUserFacing,
        ),
        opt(
            "--reason",
            Spec::String(Box::new(move |value| {
                *reason_ref.borrow_mut() = Some(value);
                Ok(())
            })),
            " reason for invoking hh, logged to telemetry",
            ArgUserFacing,
        ),
        opt(
            "--retries",
            Spec::Int(Box::new(move |n| {
                timeout_ref.set(Some(n.max(5) as f64));
                Ok(())
            })),
            " (deprecated) same as --timeout",
            ArgNonUserFacing,
        ),
        opt(
            "--retry-if-init",
            Spec::Bool(Box::new(|_| Ok(()))),
            " (deprecated and ignored)",
            ArgNonUserFacing,
        ),
        opt(
            "--rewrite-declarations",
            Spec::Unit(Box::new(move || set_mode(None, MODEREWRITEDECLARATIONS))),
            "Rewrite Hack source code allowed in notebooks to valid Hack.\n\
             For example in `function foo(): void {} function foo(): void{}` we\n\
             rewrite to the function names to something like `foo_1` and `foo_2`.\n",
            ArgNonUserFacing,
        ),
        opt(
            "--rewrite-lambda-parameters",
            Spec::Rest(Box::new(move |fn_: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODEREWRITELAMBDAPARAMETERS(vec![fn_]),
                    Some(MODEREWRITELAMBDAPARAMETERS(fnl)) => {
                        MODEREWRITELAMBDAPARAMETERS(cons(fn_, fnl))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            &(" (mode) rewrite lambdas in the files from the given list".to_string()
                + " with suggested parameter types"),
            ArgNonUserFacing,
        ),
        opt(
            "--save-naming",
            Spec::String(Box::new(move |x| set_mode(None, MODESAVENAMING(x)))),
            &(" (mode) Save the naming table to the given file.".to_string()
                + " Returns the number of files and symbols written to disk."),
            ArgNonUserFacing,
        ),
        opt(
            "--save-64bit",
            Spec::String(Box::new(move |x| {
                *save_64bit_ref.borrow_mut() = Some(x);
                Ok(())
            })),
            " save discovered 64-bit to the given directory",
            ArgNonUserFacing,
        ),
        opt(
            "--save-human-readable-64bit-dep-map",
            Spec::String(Box::new(move |x| {
                *save_hr_ref.borrow_mut() = Some(x);
                Ok(())
            })),
            " save map of 64bit hashes to names to files in the given directory",
            ArgNonUserFacing,
        ),
        tuple_3_append(
            common_argspecs::saved_state_ignore_hhconfig(&saved_state_ignore_hhconfig),
            ArgNonUserFacing,
        ),
        opt(
            "--search",
            Spec::String(Box::new(move |x| set_mode(None, MODESEARCH(x)))),
            " (mode) --search this_is_just_to_check_liveness_of_hh_server",
            ArgNonUserFacing,
        ),
        opt(
            "--server-rage",
            Spec::Unit(Box::new(move || set_mode(None, MODESERVERRAGE))),
            " (mode) dumps internal state of hh_server",
            ArgNonUserFacing,
        ),
        opt(
            "--show-spinner",
            Spec::Bool(Box::new(move |x| {
                show_spinner_ref.set(Some(x));
                Ok(())
            })),
            " shows a spinner while awaiting the typechecker",
            ArgNonUserFacing,
        ),
        opt(
            "--single",
            Spec::String(Box::new(add_single)),
            "<path> Return errors in file with provided name (give '-' for stdin)",
            ArgUserFacing,
        ),
        opt(
            "--multi",
            Spec::String(Box::new(add_multi)),
            "<path> Return errors for files read from the given file (one per line)",
            ArgUserFacing,
        ),
        opt(
            "--log-errors",
            Spec::Unit(Box::new(move || {
                only_log_errors_ref.set(true);
                Ok(())
            })),
            " (mode) type check the given list of files and log their errors (use --log-to-file to specify output file)",
            ArgNonUserFacing,
        ),
        opt(
            "--log-to-file",
            Spec::String(Box::new(set_log_to_file)),
            "<path> Write logged errors to specified file (use with --log-errors)",
            ArgNonUserFacing,
        ),
        opt(
            "--show-tast",
            Spec::Unit(Box::new(move || {
                show_tast_ref.set(true);
                Ok(())
            })),
            " in combination with `--single`, output the TASTs of the file along with TAST hashes.",
            ArgNonUserFacing,
        ),
        opt(
            "--sort-results",
            Spec::Set(&sort_results),
            " sort output for CST search.",
            ArgNonUserFacing,
        ),
        opt(
            "--stats",
            Spec::Unit(Box::new(move || set_mode(None, MODESTATS))),
            " display some server statistics",
            ArgUserFacing,
        ),
        opt(
            "--stdin-name",
            Spec::String(Box::new(move |x| {
                *stdin_name_ref.borrow_mut() = Some(x);
                Ok(())
            })),
            " substitute stdin for contents of file with specified name",
            ArgNonUserFacing,
        ),
        opt(
            "--status",
            Spec::Unit(Box::new(move || set_mode(None, MODESTATUS))),
            " (mode) show a human readable list of errors (default)",
            ArgUserFacing,
        ),
        opt(
            "--timeout",
            Spec::Float(Box::new(move |x| {
                timeout_ref.set(Some(base_float_max(5., x)));
                Ok(())
            })),
            " set the timeout in seconds (default: no timeout)",
            ArgUserFacing,
        ),
        opt(
            "--type-at-pos",
            Spec::String(Box::new(move |x| set_mode(None, MODETYPEATPOS(x)))),
            " (mode) show type at a given position in file [file:line:character]",
            // can use --type-at-pos-batch
            ArgNonUserFacing,
        ),
        opt(
            "--infer-dynamic",
            Spec::String(Box::new(move |x| set_mode(None, MODEINFERDYNAMIC(x, false)))),
            " (mode) infer types for dynamic locals [function_name or ClassName::method_name]",
            ArgUserFacing,
        ),
        opt(
            "--infer-dynamic-as-data",
            Spec::String(Box::new(move |x| set_mode(None, MODEINFERDYNAMIC(x, true)))),
            " (mode) infer types for dynamic locals as data [function_name or ClassName::method_name]",
            ArgUserFacing,
        ),
        opt(
            "--type-at-pos-batch",
            Spec::Rest(Box::new(move |position: String| {
                let m = match &*mode_ref.borrow() {
                    None => MODETYPEATPOSBATCH(vec![position]),
                    Some(MODETYPEATPOSBATCH(positions)) => {
                        MODETYPEATPOSBATCH(cons(position, positions))
                    }
                    Some(_) => return Err(single_mode_error()),
                };
                set_mode(Some(false), m)
            })),
            " (mode) show types at multiple positions [file:line:character list]",
            ArgUserFacing,
        ),
        opt(
            "--type-error-at-pos",
            Spec::String(Box::new(move |x| set_mode(None, MODETYPEERRORATPOS(x)))),
            " (mode) show type error at a given position in file [line:character]",
            ArgUserFacing,
        ),
        opt(
            "--is-subtype",
            Spec::Unit(Box::new(move || set_mode(None, MODEISSUBTYPE))),
            " (mode) take a JSON list of subtype queries via stdin",
            ArgUserFacing,
        ),
        opt(
            "--tast-holes",
            Spec::String(Box::new(move |x| set_mode(None, MODETASTHOLES(x)))),
            " (mode) return all TAST Holes in a given file",
            ArgNonUserFacing,
        ),
        opt(
            "--tast-holes-batch",
            Spec::String(Box::new(move |x| set_mode(None, MODETASTHOLESBATCH(x)))),
            " (mode) return all TAST Holes for a set of files. Argument is a file containing a newline-separated list of files",
            ArgNonUserFacing,
        ),
        opt(
            "--verbose-on",
            Spec::Unit(Box::new(move || set_mode(None, MODEVERBOSE(true)))),
            " (mode) turn on verbose server log",
            ArgNonUserFacing,
        ),
        opt(
            "--verbose-off",
            Spec::Unit(Box::new(move || set_mode(None, MODEVERBOSE(false)))),
            " (mode) turn off verbose server log",
            ArgNonUserFacing,
        ),
        opt(
            "--version",
            Spec::Set(&version),
            " (mode) show version and exit",
            ArgUserFacing,
        ),
        opt(
            "-Wall",
            Spec::Unit(Box::new(move || {
                add_warning_switch(filter_diagnostics::Switch::WAll);
                Ok(())
            })),
            " show all warnings",
            ArgUserFacing,
        ),
        opt(
            "-Wnone",
            Spec::Unit(Box::new(move || {
                add_warning_switch(filter_diagnostics::Switch::WNone);
                Ok(())
            })),
            " hide all warnings",
            ArgUserFacing,
        ),
        opt(
            "-W",
            Spec::Int(Box::new(move |code| {
                match filter_diagnostics::code::of_enum(code) {
                    None => add_invalid_warning_code(code),
                    Some(code) => add_warning_switch(filter_diagnostics::Switch::CodeOn(code)),
                }
                Ok(())
            })),
            " show all warnings with a given code, e.g. -W 12001",
            ArgUserFacing,
        ),
        opt(
            "-Wno",
            Spec::Int(Box::new(move |code| {
                match filter_diagnostics::code::of_enum(code) {
                    None => add_invalid_warning_code(code),
                    Some(code) => add_warning_switch(filter_diagnostics::Switch::CodeOff(code)),
                }
                Ok(())
            })),
            " hide all warnings with a given code, e.g. -Wno 12001",
            ArgUserFacing,
        ),
        opt(
            "-Wignore-files",
            Spec::String(Box::new(move |regexp| {
                let regexp = match ocaml_str::regexp(&regexp) {
                    Ok(regexp) => regexp,
                    Err(ocaml_str::Failure(message)) => {
                        return Err(Exn::Bad(
                            "option '-Wignore-files' expects a valid regular expression: "
                                .to_string()
                                + &message,
                        ));
                    }
                };
                add_warning_switch(filter_diagnostics::Switch::IgnoredFiles(regexp));
                Ok(())
            })),
            " hide warnings in files matching a regexp",
            ArgUserFacing,
        ),
        opt(
            "-Wgenerated",
            Spec::Unit(Box::new(move || {
                add_warning_switch(filter_diagnostics::Switch::GeneratedFilesOn);
                Ok(())
            })),
            " show warnings in generated files",
            ArgUserFacing,
        ),
        tuple_3_append(
            common_argspecs::watchman_debug_logging(&watchman_debug_logging),
            ArgNonUserFacing,
        ),
        // Please keep these sorted in the alphabetical order
    ];
    // If the user typed an option like "--type-at-pos" which set a mode which triggered
    // a command, we want to be able to show "hh_server is busy [--type-at-pos]" to show that
    // hh_server is currently busy with something that the user typed. The string
    // description that appears inside the square brackets must go into args.desc.
    // Unfortunately this isn't well supported by the Arg library, so we have to hack it up
    // ourselves: (1) For any option that takes say Arg.Unit(callback), we'll change it into
    // Arg.Unit(modified_callback) where modified_callback sets 'current_option' to the
    // option string being handled and then calls the original callback. (2) If the original
    // callback calls set_mode, then set_mode will take the opportunity to do desc := current_option.
    let options: Vec<(String, Spec<'_>, String, ArgKind)> = options
        .into_iter()
        .map(|(option, spec, text, kind)| {
            let spec = modify_spec(current_option_ref, &option, spec);
            (option, spec, text, kind)
        })
        .collect();
    let argv_has = {
        let arg_set: std::collections::BTreeSet<String> = ocaml_sys::argv().into_iter().collect();
        move |key: &str| arg_set.contains(key)
    };
    // To keep `--help` readable for users and agents:
    // --help shows only Arg_user_facing options
    // --ultrahelp shows all options.
    if argv_has("--ultrahelp") {
        let mut display_options = to_arg_specs(options);
        display_options.push(ultrahelp_entry());
        print!(
            "{}",
            ocaml_arg::usage_string(&ocaml_arg::align(display_options, None), &usage)
        );
        stdlib_exit(0)
    }
    if argv_has("--help") || argv_has("-help") {
        let main_options: Vec<_> = options
            .into_iter()
            .filter(|(_key, _spec, _doc, kind)| match kind {
                ArgUserFacing => true,
                ArgNonUserFacing => false,
            })
            .collect();
        let mut display_options = to_arg_specs(main_options);
        display_options.push(ultrahelp_entry());
        print!(
            "{}",
            ocaml_arg::usage_string(&ocaml_arg::align(display_options, None), &usage)
        );
        stdlib_exit(0)
    }
    let args = parse_without_command(
        to_arg_specs(options),
        &usage,
        client_command::command_name(cmd),
    )?;

    validate_check_args(&invalid_warning_codes.borrow());

    if output_json.get() && output_jsonl.get() {
        die::bad_args("--json and --jsonl are mutually exclusive", None);
    }

    if version.get() {
        if output_json.get() {
            server_args::print_json_version()
        } else {
            println!("{}", hh_version::version());
            let _ = std::io::stdout().flush();
        }
        stdlib_exit(0)
    }

    set_mode_from_single_files(show_tast.get(), preexisting_warnings.get())
        .map_err(raised_of_exn)?;
    set_mode_only_log_errors(LogErrorsParams {
        log_file: log_to_file.borrow().clone(),
        preexisting_warnings: preexisting_warnings.get(),
    })
    .map_err(raised_of_exn)?;
    let mode = mode.take().unwrap_or(MODESTATUS);
    // fixups
    let (root, paths) = match (&mode, args) {
        (MODELINT, args) | (MODEFILELEVELDEPENDENCIES, args) | (MODELOGERRORS(_), args) => {
            (interpret_root(&[]), args)
        }
        (_, args) => (interpret_root(&args), vec![]),
    };

    if lock_file.get() {
        let lock_file_link = server_files::lock_file(&root);
        print_flush(&lock_file_link);
        stdlib_exit(0)
    }

    if ide_logname.get() {
        let ide_log_link = server_files::client_ide_log(&root);
        print_flush(&ide_log_link);
        stdlib_exit(0)
    }

    if lsp_logname.get() {
        let lsp_log_link = server_files::client_lsp_log(&root);
        print_flush(&lsp_log_link);
        stdlib_exit(0)
    }

    if monitor_logname.get() {
        let monitor_log_link = server_files::monitor_log_link(&root);
        print_flush(&monitor_log_link);
        stdlib_exit(0)
    }

    if client_logname.get() {
        let client_log_link = server_files::client_log(&root);
        print_flush(&client_log_link);
        stdlib_exit(0)
    }

    if logname.get() {
        let log_link = server_files::log_link(&root);
        print_flush(&log_link);
        stdlib_exit(0)
    }

    if *from.borrow() == "emacs" {
        print!("-*- mode: compilation -*-\n");
        let _ = std::io::stdout().flush();
    }

    let from = from.into_inner();
    let is_interactive = is_interactive_from(&from);
    let no_load = no_load.get()
        || match mode {
            MODEREMOVEDEADFIXMES(_) => true,
            _ => false,
        };
    let mut warning_switches = warning_switches.into_inner();
    warning_switches.reverse();
    Ok(ClientCheckEnv {
        autostart: autostart.get(),
        config: config.into_inner(),
        custom_hhi_path: custom_hhi_path.into_inner(),
        custom_telemetry_data: custom_telemetry_data.into_inner(),
        error_format: error_format.get(),
        force_dormant_start: force_dormant_start.get(),
        from,
        show_spinner: show_spinner.get().unwrap_or(is_interactive),
        ignore_hh_version: ignore_hh_version.get(),
        saved_state_ignore_hhconfig: saved_state_ignore_hhconfig.get(),
        paths,
        max_errors: max_errors.get(),
        preexisting_warnings: preexisting_warnings.get(),
        reason: reason.into_inner(),
        mode,
        no_load,
        save_64bit: save_64bit.into_inner(),
        save_human_readable_64bit_dep_map: save_human_readable_64bit_dep_map.into_inner(),
        output_json: output_json.get(),
        output_jsonl: output_jsonl.get(),
        prechecked: prechecked.get(),
        mini_state: mini_state.into_inner(),
        root,
        sort_results: sort_results.get(),
        stdin_name: stdin_name.into_inner(),
        deadline: timeout.get().map(|t| unix_time() + t),
        watchman_debug_logging: watchman_debug_logging.get(),
        allow_non_opt_build: allow_non_opt_build.get(),
        desc: desc.into_inner(),
        is_interactive,
        warning_switches,
        dump_config: dump_config.get(),
    })
}

/// `Printf.printf "%s\n%!" s`
fn print_flush(s: &str) {
    println!("{}", s);
    let _ = std::io::stdout().flush();
}

/// `Base.Float.max`: NaN if either is NaN.
fn base_float_max(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if x > y {
        x
    } else {
        y
    }
}

/// `Base.String.capitalize`: the first character in upper case (ASCII).
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
    }
}

pub fn parse_start_env(command: &str, from_default: &str) -> Result<client_start::Env, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!(
        "Usage: {} {} [OPTION]... [WWW-ROOT]\n{} a Hack server\n\nWWW-ROOT is assumed to be current directory if unspecified\n",
        argv0,
        command,
        capitalize(command)
    );
    let no_load = Cell::new(false);
    let watchman_debug_logging = Cell::new(false);
    let ignore_hh_version = Cell::new(false);
    let saved_state_ignore_hhconfig = Cell::new(false);
    let prechecked: Cell<Option<bool>> = Cell::new(None);
    let mini_state: RefCell<Option<String>> = RefCell::new(None);
    let from = RefCell::new(from_default.to_string());
    let config: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let custom_hhi_path: RefCell<Option<String>> = RefCell::new(None);
    let custom_telemetry_data: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let allow_non_opt_build = Cell::new(false);
    let preexisting_warnings = Cell::new(false);
    let wait_deprecation_msg = || -> Res {
        eprint!("WARNING: --wait is deprecated, does nothing, and will be going away soon!\n");
        let _ = std::io::stderr().flush();
        Ok(())
    };
    let config_ref = &config;
    let options: Vec<Entry<'_>> = vec![
        // Please keep these sorted in the alphabetical order
        common_argspecs::allow_non_opt_build(&allow_non_opt_build),
        common_argspecs::config(&config),
        common_argspecs::custom_hhi_path(&custom_hhi_path),
        common_argspecs::custom_telemetry_data(&custom_telemetry_data),
        common_argspecs::from(&from),
        common_argspecs::ignore_hh_version(&ignore_hh_version),
        (
            "--no-load".to_string(),
            Spec::Set(&no_load),
            " start from a fresh state".to_string(),
        ),
        common_argspecs::no_prechecked(&prechecked),
        common_argspecs::prechecked(&prechecked),
        common_argspecs::with_mini_state(&mini_state),
        (
            "--profile-log".to_string(),
            Spec::Unit(Box::new(move || {
                config_ref
                    .borrow_mut()
                    .insert(0, ("profile_log".to_string(), "true".to_string()));
                Ok(())
            })),
            " enable profile logging".to_string(),
        ),
        common_argspecs::saved_state_ignore_hhconfig(&saved_state_ignore_hhconfig),
        (
            "--wait".to_string(),
            Spec::Unit(Box::new(wait_deprecation_msg)),
            " this flag is deprecated and does nothing!".to_string(),
        ),
        common_argspecs::watchman_debug_logging(&watchman_debug_logging),
        common_argspecs::preexisting_warnings(&preexisting_warnings),
        // Please keep these sorted in the alphabetical order
    ];
    let args = parse_without_command(options, &usage, command)?;
    let root = interpret_root(&args);
    Ok(client_start::Env {
        config: config.into_inner(),
        custom_hhi_path: custom_hhi_path.into_inner(),
        custom_telemetry_data: custom_telemetry_data.into_inner(),
        exit_on_failure: true,
        from: from.into_inner(),
        ignore_hh_version: ignore_hh_version.get(),
        saved_state_ignore_hhconfig: saved_state_ignore_hhconfig.get(),
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        no_load: no_load.get(),
        prechecked: prechecked.get(),
        mini_state: mini_state.into_inner(),
        root,
        silent: false,
        watchman_debug_logging: watchman_debug_logging.get(),
        allow_non_opt_build: allow_non_opt_build.get(),
        preexisting_warnings: preexisting_warnings.get(),
    })
}

pub fn parse_saved_state_project_metadata_args(from_default: &str) -> Result<HeavyCommand, Raised> {
    Ok(HeavyCommand::CSavedStateProjectMetadata(parse_check_args(
        CommandKeyword::CKSavedStateProjectMetadata,
        from_default,
    )?))
}

pub fn parse_start_args(from_default: &str) -> Result<HeavyCommand, Raised> {
    Ok(HeavyCommand::CStart(parse_start_env("start", from_default)?))
}

pub fn parse_restart_args(from_default: &str) -> Result<HeavyCommand, Raised> {
    Ok(HeavyCommand::CRestart(parse_start_env("restart", from_default)?))
}

pub fn parse_stop_args(from_default: &str) -> Result<HeavyCommand, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!(
        "Usage: {} stop [OPTION]... [WWW-ROOT]\nStop a hack server\n\nWWW-ROOT is assumed to be current directory if unspecified\n",
        argv0
    );
    let from = RefCell::new(from_default.to_string());
    let options = vec![common_argspecs::from(&from)];
    let args = parse_without_command(options, &usage, "stop")?;
    let root = interpret_root(&args);
    Ok(HeavyCommand::CStop(client_stop::Env {
        root,
        from: from.into_inner(),
    }))
}

pub fn parse_lsp_args() -> Result<HeavyCommand, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!(
        "Usage: {} lsp [OPTION]...\nRuns a persistent language service\n",
        argv0
    );
    let from = RefCell::new(String::new());
    let config: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let disable_format_on_save = Cell::new(false);
    let notebook_mode = Cell::new(false);
    let verbose = Cell::new(false);
    let ignore_hh_version = Cell::new(false);
    let naming_table: RefCell<Option<String>> = RefCell::new(None);
    let warnings_saved_state_path: RefCell<Option<path::T>> = RefCell::new(None);
    let warnings_saved_state_path_ref = &warnings_saved_state_path;
    let options: Vec<Entry<'_>> = vec![
        common_argspecs::from(&from),
        common_argspecs::config(&config),
        (
            "--disable-format-on-save".to_string(),
            Spec::Set(&disable_format_on_save),
            " disable `textDocument/willSaveWaitUntil` handling of format-on-save".to_string(),
        ),
        // Please keep these sorted in the alphabetical order
        (
            "--enhanced-hover".to_string(),
            Spec::Unit(Box::new(|| Ok(()))),
            " [legacy] no-op".to_string(),
        ),
        (
            "--ffp-autocomplete".to_string(),
            Spec::Unit(Box::new(|| Ok(()))),
            " [legacy] no-op".to_string(),
        ),
        common_argspecs::ignore_hh_version(&ignore_hh_version),
        common_argspecs::naming_table(&naming_table),
        (
            "--warnings-saved-state".to_string(),
            Spec::String(Box::new(move |s| {
                *warnings_saved_state_path_ref.borrow_mut() = Some(path::make(&s));
                Ok(())
            })),
            " path to the warnings saved state".to_string(),
        ),
        (
            "--notebook-mode".to_string(),
            Spec::Set(&notebook_mode),
            " enable notebook mode, which is designed for use in notebooks. For example, this mode enables top-level statements."
                .to_string(),
        ),
        (
            "--ranked-autocomplete".to_string(),
            Spec::Unit(Box::new(|| Ok(()))),
            " [legacy] no-op".to_string(),
        ),
        (
            "--serverless-ide".to_string(),
            Spec::Unit(Box::new(|| Ok(()))),
            " [legacy] no-op".to_string(),
        ),
        (
            "--verbose".to_string(),
            Spec::Set(&verbose),
            " verbose logs to stderr and `hh --ide-logname` and `--lsp-logname`".to_string(),
        ),
        // Please keep these sorted in the alphabetical order
    ];
    let args = parse_without_command(options, &usage, "lsp")?;
    let root = interpret_root(&args);
    Ok(HeavyCommand::CLsp(client_lsp::Args {
        from: from.into_inner(),
        config: config.into_inner(),
        disable_format_on_save: disable_format_on_save.get(),
        ignore_hh_version: ignore_hh_version.get(),
        naming_table: naming_table.into_inner(),
        warnings_saved_state_path: warnings_saved_state_path.into_inner(),
        notebook_mode: notebook_mode.get(),
        verbose: verbose.get(),
        root_from_cli: root,
    }))
}

/// `In_channel.input_line_exn ic` (`~fix_win_eol:true`): the next line
/// (`Stdlib.input_line`: up to a `\n`, or the rest of the input), without
/// its `\n`, and then without a `\r` at its end (Stdio's `trim`, which also
/// applies to a last line that has no `\n`); raises `End_of_file` (a panic
/// with that message) at the end of the input. Bytes that are not UTF-8
/// become U+FFFD.
fn input_line_exn(ic: &mut impl std::io::BufRead) -> String {
    let mut line = vec![];
    match ic.read_until(b'\n', &mut line) {
        Ok(0) => panic!("End_of_file"),
        Ok(_) => {
            if line.last() == Some(&b'\n') {
                line.pop();
            }
            if line.last() == Some(&b'\r') {
                line.pop();
            }
            String::from_utf8_lossy(&line).into_owned()
        }
        Err(e) => panic!("Sys_error: {}", e),
    }
}

/// `In_channel.input_line_exn In_channel.stdin`
fn input_line_exn_stdin() -> String {
    input_line_exn(&mut std::io::stdin().lock())
}

pub fn parse_rage_args() -> Result<HeavyCommand, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!("Usage: {} rage [OPTION]... [WWW-ROOT]\n", argv0);
    let from = RefCell::new(String::new());
    let desc: RefCell<Option<String>> = RefCell::new(None);
    let rageid: RefCell<Option<String>> = RefCell::new(None);
    let lsp_log: RefCell<Option<String>> = RefCell::new(None);
    let (desc_ref, rageid_ref, lsp_log_ref) = (&desc, &rageid, &lsp_log);
    let options: Vec<Entry<'_>> = vec![
        common_argspecs::from(&from),
        (
            "--desc".to_string(),
            Spec::String(Box::new(move |s| {
                *desc_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " description of problem".to_string(),
        ),
        (
            "--rageid".to_string(),
            Spec::String(Box::new(move |s| {
                *rageid_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " (optional) use this id, and finish even if parent process dies".to_string(),
        ),
        (
            "--lsp-log".to_string(),
            Spec::String(Box::new(move |s| {
                *lsp_log_ref.borrow_mut() = Some(s);
                Ok(())
            })),
            " (optional) gather lsp logs from this filename".to_string(),
        ),
    ];
    let args = parse_without_command(options, &usage, "rage")?;
    let root = interpret_root(&args);
    // hh_client normally handles Ctrl+C by printing an exception-stack.
    // But for us, in an interactive prompt, Ctrl+C is an unexceptional way to quit.
    ocaml_sys::set_signal(libc::SIGINT, ocaml_sys::SignalBehavior::SignalDefault);

    enum Info {
        NoInfo,
        VerboseHhStart,
        Unsaved,
    }
    let desc = match desc.into_inner() {
        Some(desc) => desc,
        None => {
            print!(
                "Sorry that hh isn't working. What's wrong?\n\
                 0. There's something wrong relating to VSCode or IDE\n\
                 1. hh_server takes ages to initialize\n\
                 2. hh is stuck in an infinite loop\n\
                 3. hh gives some error message about the monitor\n\
                 4. hack says it has an internal typecheck bug and asked me to report it\n\
                 5. hack is reporting errors that are clearly incorrect [please elaborate]\n\
                 6. I'm not sure how to write my code to avoid these hack errors\n\
                 7. hh says something about unsaved changes from an editor even after I've quit my editor\n\
                 8. something's wrong with hack VS Code or other editor\n\
                 [other] Please type either one of the above numbers, or a freeform description\n\
                 \nrage> "
            );
            let _ = std::io::stdout().flush();
            let response = input_line_exn_stdin();
            let (response, info) = if response == "0" {
                print!(
                    "Please use the VSCode bug nub (at the right of the status bar) instead of hh rage.\n"
                );
                stdlib_exit(0)
            } else if response == "1" {
                ("hh_server slow initialize".to_string(), Info::VerboseHhStart)
            } else if response == "2" {
                ("hh stuck in infinite loop".to_string(), Info::VerboseHhStart)
            } else if response == "3" {
                ("hh monitor problem".to_string(), Info::VerboseHhStart)
            } else if response == "4" {
                client_rage::verify_typechecker_err_src();
                ("internal typecheck bug".to_string(), Info::NoInfo)
            } else if response == "5" {
                print!("Please elaborate on which errors are incorrect...\nrage> ");
                let _ = std::io::stdout().flush();
                (input_line_exn_stdin(), Info::NoInfo)
            } else if response == "6" {
                print!(
                    "Please ask in the appropriate support groups for advice on coding in Hack; \
                     `hh rage` is solely for reporting bugs in the tooling, not for reporting typechecker or \
                     language issues.\n"
                );
                stdlib_exit(0)
            } else if response == "7" {
                ("unsaved editor changes".to_string(), Info::Unsaved)
            } else if response == "8" {
                print!(
                    "Please file the bug from within your editor to capture the right logs. \
                     Note: you can do Preferences > Settings > Hack > Verbose, then `pkill hh_client`, \
                     then reproduce the error, then file the bug. This way we'll get even richer logs.\n"
                );
                stdlib_exit(0)
            } else {
                (response, Info::VerboseHhStart)
            };
            match info {
                Info::NoInfo => {}
                Info::VerboseHhStart => {
                    print!(
                        "\nPOWER USERS ONLY: Sometimes the normal logging from hh_server isn't \
                         enough to diagnose an issue, and we'll ask you to switch hh_server to \
                         write verbose logs, then have you repro the issue, then use `hh rage` to \
                         gather up those now-verbose logs. To restart hh_server with verbose logs, \
                         do `hh stop && hh start --config min_log_level=debug`. \
                         Once done, then you can repro the issue, and then do rage again.\n\n"
                    );
                    let _ = std::io::stdout().flush();
                }
                Info::Unsaved => {
                    print!(
                        "\nNote: you can often work around this issue yourself by quitting your editor, then `pkill hh_client`.\n"
                    );
                    let _ = std::io::stdout().flush();
                }
            }
            response
        }
    };
    Ok(HeavyCommand::CRage(client_rage::Env {
        root,
        from: from.into_inner(),
        desc,
        rageid: rageid.into_inner(),
        lsp_log: lsp_log.into_inner(),
    }))
}

pub fn parse_decompress_zhhdg_args() -> Result<LightCommand, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!(
        "Usage: {} decompress-zhhdg --path [PATH]\n\nDecompress a .zhhdg file by running the depgraph decompressor, and write a .hhdg file in the same directory.\n",
        argv0
    );
    let from = RefCell::new(String::new());
    let path = RefCell::new(String::new());
    let path_ref = &path;
    let options = ocaml_arg::align(
        vec![
            common_argspecs::from(&from),
            (
                "--path".to_string(),
                Spec::String(Box::new(move |arg| {
                    *path_ref.borrow_mut() = arg;
                    Ok(())
                })),
                " The path on disk to the .zhhdg file".to_string(),
            ),
        ],
        None,
    );
    let _args = parse_without_command(options, &usage, "decompress-zhhdg")?;
    let path = match path.into_inner().as_str() {
        "" => die::bad_args("The '--path' option is required.", None),
        p => p.to_string(),
    };
    let from = from.into_inner();
    Ok(LightCommand::CDecompressZhhdg(client_decompress_zhhdg::Env {
        path,
        from,
    }))
}

pub fn parse_download_saved_state_args() -> Result<HeavyCommand, Raised> {
    let argv0 = ocaml_sys::argv().first().cloned().unwrap_or_default();
    let usage = format!(
        "Usage: {} download-saved-state [OPTION]... [WWW-ROOT]\n\nDownload a saved-state to disk for the given repository, to make future\ninvocations of `hh` faster.",
        argv0
    );

    let from = RefCell::new(String::new());
    let should_save_replay = Cell::new(false);
    let replay_token: RefCell<Option<String>> = RefCell::new(None);
    let saved_state_manifold_api_key: RefCell<Option<String>> = RefCell::new(None);
    let (replay_token_ref, api_key_ref) = (&replay_token, &saved_state_manifold_api_key);
    let options = ocaml_arg::align(
        vec![
            common_argspecs::from(&from),
            (
                "--type".to_string(),
                Spec::String(Box::new(|_| Ok(()))),
                " (unused)".to_string(),
            ),
            (
                "--save-replay".to_string(),
                Spec::Set(&should_save_replay),
                " Produce a token that can be later consumed by --replay-token to replay the same saved-state download."
                    .to_string(),
            ),
            (
                "--saved-state-manifold-api-key".to_string(),
                Spec::String(Box::new(move |arg| {
                    *api_key_ref.borrow_mut() = Some(arg);
                    Ok(())
                })),
                " An API key for Manifold to use when downloading the specified saved state."
                    .to_string(),
            ),
            (
                "--replay-token".to_string(),
                Spec::String(Box::new(move |arg| {
                    *replay_token_ref.borrow_mut() = Some(arg);
                    Ok(())
                })),
                " A token produced from a previous invocation of this command with --save-replay."
                    .to_string(),
            ),
        ],
        None,
    );
    let args = parse_without_command(options, &usage, "download-saved-state")?;
    let root = match args.as_slice() {
        [] => die::bad_args(
            "--download-saved-state requires a WWW_ROOT argument",
            Some(&usage),
        ),
        _ => interpret_root(&args),
    };
    let from = match from.into_inner().as_str() {
        "" => die::bad_args("The '--from' option is required.", None),
        from => from.to_string(),
    };
    Ok(HeavyCommand::CDownloadSavedState(
        client_download_saved_state::Env {
            root,
            from,
            saved_state_manifold_api_key: saved_state_manifold_api_key.into_inner(),
            should_save_replay: should_save_replay.get(),
            replay_token: replay_token.into_inner(),
        },
    ))
}

/// The `Exit_status.Exit_with` that a spec's function raised is the `Err`.
pub fn parse_args(from_default: &str) -> Result<Command, ExitWith> {
    let command = parse_command();
    let result = match command {
        CommandKeyword::CKNone | CommandKeyword::CKCheck => {
            parse_check_args(CommandKeyword::CKCheck, from_default)
                .map(|env| Command::WithConfig(HeavyCommand::CCheck(env)))
        }
        CommandKeyword::CKStart => parse_start_args(from_default).map(Command::WithConfig),
        CommandKeyword::CKStop => parse_stop_args(from_default).map(Command::WithConfig),
        CommandKeyword::CKRestart => parse_restart_args(from_default).map(Command::WithConfig),
        CommandKeyword::CKLsp => parse_lsp_args().map(Command::WithConfig),
        CommandKeyword::CKRage => parse_rage_args().map(Command::WithConfig),
        CommandKeyword::CKSavedStateProjectMetadata => {
            parse_saved_state_project_metadata_args(from_default).map(Command::WithConfig)
        }
        CommandKeyword::CKDownloadSavedState => {
            parse_download_saved_state_args().map(Command::WithConfig)
        }
        CommandKeyword::CKDecompressZhhdg => {
            parse_decompress_zhhdg_args().map(Command::WithoutConfig)
        }
    };
    match result {
        Ok(command) => Ok(command),
        // [Arg.parse_argv] raises rather than printing, so hh_client has to
        // reproduce what [Arg.parse] used to do here.
        Err(Raised::Help(message)) => {
            print!("{}", message);
            stdlib_exit(0)
        }
        Err(Raised::ParseError(ArgError { message, usage })) => {
            die::bad_args(&message, usage.as_deref())
        }
        Err(Raised::Bad(message)) => die::bad_args(&message, None),
        Err(Raised::ExitWith(exit_with)) => Err(exit_with),
    }
}

pub fn root(command: &HeavyCommand) -> path::T {
    match command {
        HeavyCommand::CCheck(ClientCheckEnv { root, .. })
        | HeavyCommand::CStart(client_start::Env { root, .. })
        | HeavyCommand::CRestart(client_start::Env { root, .. })
        | HeavyCommand::CStop(client_stop::Env { root, .. })
        | HeavyCommand::CRage(client_rage::Env { root, .. })
        | HeavyCommand::CSavedStateProjectMetadata(ClientCheckEnv { root, .. })
        | HeavyCommand::CDownloadSavedState(client_download_saved_state::Env { root, .. }) => {
            root.clone()
        }
        HeavyCommand::CLsp(client_lsp::Args { root_from_cli, .. }) => root_from_cli.clone(),
    }
}

pub fn config(command: &HeavyCommand) -> Option<Vec<(String, String)>> {
    match command {
        HeavyCommand::CCheck(ClientCheckEnv { config, .. })
        | HeavyCommand::CStart(client_start::Env { config, .. })
        | HeavyCommand::CRestart(client_start::Env { config, .. })
        | HeavyCommand::CLsp(client_lsp::Args { config, .. })
        | HeavyCommand::CSavedStateProjectMetadata(ClientCheckEnv { config, .. }) => {
            Some(config.clone())
        }
        HeavyCommand::CStop(_) | HeavyCommand::CDownloadSavedState(_) | HeavyCommand::CRage(_) => {
            None
        }
    }
}

pub fn from(command: &HeavyCommand) -> String {
    match command {
        HeavyCommand::CCheck(ClientCheckEnv { from, .. })
        | HeavyCommand::CStart(client_start::Env { from, .. })
        | HeavyCommand::CRestart(client_start::Env { from, .. })
        | HeavyCommand::CLsp(client_lsp::Args { from, .. })
        | HeavyCommand::CSavedStateProjectMetadata(ClientCheckEnv { from, .. })
        | HeavyCommand::CStop(client_stop::Env { from, .. })
        | HeavyCommand::CDownloadSavedState(client_download_saved_state::Env { from, .. })
        | HeavyCommand::CRage(client_rage::Env { from, .. }) => from.clone(),
    }
}

pub fn dump_config(command: &HeavyCommand) -> bool {
    match command {
        HeavyCommand::CCheck(ClientCheckEnv { dump_config, .. }) => *dump_config,
        _ => false,
    }
}

pub fn is_interactive(cmd: &HeavyCommand) -> bool {
    is_interactive_from(&from(cmd))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh directory with a `.hhconfig`, resolved (on macOS the temporary
    /// directory is behind a symbolic link).
    fn hh_root(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!(
            "hh_client_args_{}_{}",
            name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(".hhconfig"), "").unwrap();
        std::fs::canonicalize(&dir)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string()
    }

    fn with_args<A>(args: &[&str], f: impl FnOnce() -> A) -> A {
        let mut argv = vec!["/path/to/hh_client".to_string()];
        argv.extend(args.iter().map(|s| s.to_string()));
        ocaml_sys::with_argv_FOR_TESTING(argv, f)
    }

    fn check(args: &[&str]) -> Result<ClientCheckEnv, Raised> {
        with_args(args, || parse_check_args(CommandKeyword::CKCheck, ""))
    }

    #[test]
    fn default_mode_and_root() {
        let root = hh_root("default");
        let env = check(&[&root]).unwrap();
        assert_eq!(env.mode, MODESTATUS);
        assert_eq!(env.root, root);
        assert_eq!(env.desc, "check");
        assert!(env.is_interactive);
        assert!(env.show_spinner);
        assert!(env.autostart);
        assert_eq!(env.deadline, None);
        assert!(env.paths.is_empty());
        // `check` is dropped from the anonymous arguments.
        let env = check(&["check", &root]).unwrap();
        assert_eq!(env.root, root);
    }

    #[test]
    fn options_set_the_env() {
        let root = hh_root("options");
        let env = check(&[
            "--type-at-pos",
            "f.php:1:2",
            "--from",
            "vim",
            "--config",
            "a=1",
            "--config=b=2",
            "--single",
            "x",
            "-Wall",
            "-W",
            "12001",
            "-Wnone",
            "--autostart-server",
            "false",
            "--timeout",
            "1",
            "--error-format",
            "raw",
            &root,
        ]);
        // `--single` after a mode is an error when the mode is set from it.
        assert_eq!(
            env.unwrap_err(),
            Raised::Bad("only a single mode should be specified".to_string())
        );
        let env = check(&[
            "--type-at-pos",
            "f.php:1:2",
            "--from",
            "vim",
            "--config",
            "a=1",
            "--config=b=2",
            "-Wall",
            "-W",
            "12001",
            "-Wnone",
            "--autostart-server",
            "false",
            "--timeout",
            "1",
            "--error-format",
            "raw",
            &root,
        ])
        .unwrap();
        assert_eq!(env.mode, MODETYPEATPOS("f.php:1:2".to_string()));
        assert_eq!(env.desc, "--type-at-pos");
        assert_eq!(env.from, "vim");
        assert!(!env.is_interactive);
        assert!(!env.show_spinner);
        assert!(!env.autostart);
        assert_eq!(
            env.config,
            vec![
                ("b".to_string(), "2".to_string()),
                ("a".to_string(), "1".to_string())
            ]
        );
        assert_eq!(env.error_format, Some(diagnostics_state::Format::Raw));
        assert_eq!(env.warning_switches.len(), 3);
        assert!(matches!(
            env.warning_switches[0],
            filter_diagnostics::Switch::WAll
        ));
        assert!(matches!(
            env.warning_switches[2],
            filter_diagnostics::Switch::WNone
        ));
        // `--timeout` is at least 5 seconds, from `Unix.time ()`.
        let deadline = env.deadline.unwrap();
        assert!(deadline >= unix_time() + 4.0 && deadline <= unix_time() + 5.0);
    }

    #[test]
    fn singles_and_batches_are_in_ocaml_list_order() {
        let root = hh_root("singles");
        let env = check(&["--single", "a", "--single", "b", &root]).unwrap();
        assert_eq!(
            env.mode,
            MODESTATUSSINGLE(StatusSingle {
                filenames: vec!["b".to_string(), "a".to_string()],
                show_tast: false,
                preexisting_warnings: false
            })
        );
        assert_eq!(env.desc, "check");
        // `Arg.Rest` takes the root too.
        let env = check(&[&root, "--type-at-pos-batch", "p1", "p2"]).unwrap();
        assert_eq!(
            env.mode,
            MODETYPEATPOSBATCH(vec!["p2".to_string(), "p1".to_string()])
        );
        assert_eq!(env.desc, "--type-at-pos-batch");
        // The OCaml turns a second position of --deps-out-at-pos-batch into
        // MODE_FUN_DEPS_AT_POS_BATCH.
        let env = check(&[&root, "--deps-out-at-pos-batch", "p1", "p2"]).unwrap();
        assert_eq!(
            env.mode,
            MODEFUNDEPSATPOSBATCH(vec!["p2".to_string(), "p1".to_string()])
        );
        let env = check(&["--remove-dead-fixme", "1", "--remove-dead-fixme", "2", &root]).unwrap();
        assert_eq!(env.mode, MODEREMOVEDEADFIXMES(vec![2, 1]));
        assert!(env.no_load);
        let env = check(&["--refactor", "Class", "A", "B", &root]).unwrap();
        assert_eq!(
            env.mode,
            MODERENAME(RenameMode::Class, "A".to_string(), "B".to_string())
        );
        let env = check(&["--ide-find-refs-by-symbol3", "C|Class,\\C", "-", "x|y", &root]).unwrap();
        match env.mode {
            MODEIDEFINDREFSBYSYMBOL(args) => {
                assert_eq!(args.symbol_name, "C");
                assert_eq!(args.hint_suffixes, vec!["x", "y"]);
            }
            mode => panic!("{:?}", mode),
        }
    }

    #[test]
    fn parse_errors_are_arg_errors() {
        let root = hh_root("errors");
        match check(&["--nope", &root]) {
            Err(Raised::ParseError(ArgError { message, usage })) => {
                assert_eq!(message, "/path/to/hh_client: unknown option '--nope'.");
                let usage = usage.unwrap();
                assert!(
                    usage.starts_with("Usage: /path/to/hh_client check [OPTION]... [WWW-ROOT]\n"),
                    "{}",
                    usage
                );
                assert!(usage.ends_with("  --help                                   Display this list of options"));
            }
            r => panic!("{:?}", r),
        }
        match check(&["--lint", "--lint", &root]) {
            Err(Raised::ParseError(ArgError { message, .. })) => {
                assert_eq!(
                    message,
                    "/path/to/hh_client: only a single mode should be specified."
                );
            }
            r => panic!("{:?}", r),
        }
        match check(&["--package-lint-full", "t.php", ",", &root]) {
            Err(Raised::ParseError(ArgError { message, .. })) => {
                assert_eq!(
                    message,
                    "/path/to/hh_client: --package-lint-full requires at least one candidate file."
                );
            }
            r => panic!("{:?}", r),
        }
        match check(&["-Wignore-files", "[", &root]) {
            Err(Raised::ParseError(ArgError { message, .. })) => {
                assert_eq!(
                    message,
                    "/path/to/hh_client: option '-Wignore-files' expects a valid regular expression: [ class not closed by ]."
                );
            }
            r => panic!("{:?}", r),
        }
    }

    #[test]
    fn other_commands() {
        let root = hh_root("commands");
        let start = with_args(&["start", "--no-load", "--config", "k=v", &root], || {
            parse_start_env("start", "x")
        })
        .unwrap();
        assert!(start.no_load);
        assert_eq!(start.from, "x");
        assert_eq!(start.root, root);
        assert!(start.exit_on_failure);
        match with_args(&["stop", "--help"], || parse_stop_args("")) {
            Err(Raised::Help(help)) => assert_eq!(
                help,
                "Usage: /path/to/hh_client stop [OPTION]... [WWW-ROOT]\nStop a hack server\n\nWWW-ROOT is assumed to be current directory if unspecified\n\n  --from  so we know who's calling hh_client - e.g. nuclide, vim, emacs, vscode\n  -help   Display this list of options\n  --help  Display this list of options\n"
            ),
            r => panic!("{:?}", r),
        }
        match with_args(&["lsp", "--verbose", "--warnings-saved-state", "/w", &root], || {
            parse_lsp_args()
        })
        .unwrap()
        {
            HeavyCommand::CLsp(args) => {
                assert!(args.verbose);
                assert_eq!(args.warnings_saved_state_path, Some("/w".to_string()));
                assert_eq!(args.root_from_cli, root);
            }
            c => panic!("{:?}", c),
        }
        assert_eq!(
            with_args(&["Decompress-Zhhdg"], parse_command),
            CommandKeyword::CKDecompressZhhdg
        );
        assert_eq!(with_args(&[], parse_command), CommandKeyword::CKNone);
        assert_eq!(with_args(&["--json"], parse_command), CommandKeyword::CKNone);
    }

    #[test]
    fn multi_files_and_singles_are_in_ocaml_list_order() {
        let root = hh_root("multi");
        let multi = std::path::Path::new(&root).join("files.txt");
        // `String.strip`, then one file per line (inner blanks are kept).
        std::fs::write(&multi, " \ta\n b \n\n").unwrap();
        let multi = multi.to_str().unwrap();
        let filenames = |args: &[&str]| match check(args).unwrap().mode {
            MODESTATUSSINGLE(StatusSingle { filenames, .. }) => filenames,
            mode => panic!("{:?}", mode),
        };
        // `files @ !single_files`, while `add_single` conses.
        assert_eq!(
            filenames(&["--single", "s", "--multi", multi, &root]),
            vec!["a", " b", "s"]
        );
        assert_eq!(
            filenames(&["--multi", multi, "--single", "s", &root]),
            vec!["s", "a", " b"]
        );
        match check(&["--multi", "/nonexistent/hh_client_args_multi", &root]) {
            Err(Raised::ParseError(ArgError { message, .. })) => assert_eq!(
                message,
                "/path/to/hh_client: could not read --multi file: /nonexistent/hh_client_args_multi: No such file or directory."
            ),
            r => panic!("{:?}", r),
        }
    }

    #[test]
    fn desc_from_and_command_keyword() {
        let root = hh_root("desc");
        // A mode set inside an `Arg.Tuple` (whose specs are modified too).
        let env = check(&["--refactor", "Method", "A::f", "g", &root]).unwrap();
        assert_eq!(
            env.mode,
            MODERENAME(RenameMode::Method, "A::f".to_string(), "g".to_string())
        );
        assert_eq!(env.desc, "--refactor");
        // Options that set no mode leave the command name.
        let env = check(&["--json", "--from-arc-diff", &root]).unwrap();
        assert_eq!(env.desc, "check");
        assert_eq!(env.mode, MODESTATUS);
        assert_eq!(env.from, "arc_diff");
        assert!(!env.is_interactive);
        // `--remove-dead-fixmes` implies `no_load`.
        let env = check(&["--remove-dead-fixmes", &root]).unwrap();
        assert_eq!(env.mode, MODEREMOVEDEADFIXMES(vec![]));
        assert_eq!(env.desc, "--remove-dead-fixmes");
        assert!(env.no_load);
        // The command keyword is dropped whatever its case.
        let env = check(&["CHECK", &root]).unwrap();
        assert_eq!(env.root, root);
        // `-W`/`-Wno` keep the order of the command line.
        let env = check(&["-Wgenerated", "-Wall", &root]).unwrap();
        assert!(matches!(
            env.warning_switches.as_slice(),
            [
                filter_diagnostics::Switch::GeneratedFilesOn,
                filter_diagnostics::Switch::WAll
            ]
        ));
    }

    #[test]
    fn timeouts_are_at_least_five_seconds() {
        let root = hh_root("timeouts");
        // `Unix.time () +. t`, with `Unix.time` in whole seconds.
        let delay = |args: &[&str]| {
            let before = unix_time();
            check(args).unwrap().deadline.unwrap() - before
        };
        // `float_of_int (max 5 n)`
        let d = delay(&["--retries", "3", &root]);
        assert!((5.0..=6.0).contains(&d), "{}", d);
        // `Float.max 5. x`
        let d = delay(&["--timeout", "7.5", &root]);
        assert!((7.5..=8.5).contains(&d), "{}", d);
        assert!(delay(&["--timeout", "nan", &root]).is_nan());
    }

    #[test]
    fn exit_with_goes_through_the_parse() {
        let root = hh_root("exit_with");
        // `Find_refs_wire_format` raises `Exit_with Input_error` in a spec's
        // function; `parse_without_command` raises it again
        // (`Die.internal_exception`), for `main` to exit with it.
        match check(&["--ide-find-refs-by-symbol", "bogus", &root]) {
            Err(Raised::ExitWith(e)) => {
                assert!(matches!(e, exit_status::ExitWith(exit_status::T::InputError)))
            }
            _ => panic!("not Exit_with"),
        }
    }

    #[test]
    fn input_lines_as_stdio_reads_them() {
        let mut ic = std::io::Cursor::new(b"a\r\nb\n\nc\r".to_vec());
        assert_eq!(input_line_exn(&mut ic), "a");
        assert_eq!(input_line_exn(&mut ic), "b");
        assert_eq!(input_line_exn(&mut ic), "");
        // `~fix_win_eol` trims a `\r` at the end of a last line too.
        assert_eq!(input_line_exn(&mut ic), "c");
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| input_line_exn(&mut ic)));
        assert_eq!(*r.unwrap_err().downcast::<&str>().unwrap(), "End_of_file");
    }
}
