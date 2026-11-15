// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_args.ml`. See `hh/PORTING.md`.
//!
//! The command line of `hh_server`. `options` is abstract in the `.mli`: its
//! fields are private, and read and changed with the accessors and setters.
//!
//! `Server_args` includes `Cli_args` (`include Cli_args`): its types and
//! functions are re-exported.
//!
//! # `Arg`
//!
//! `parse_options` parses `Sys.argv` with OCaml's `Arg` (`Arg.align`, then
//! `Arg.parse`): `crate::rt::ocaml_arg`. `Arg.current` is its per-thread
//! counter, as `Arg.parse` uses the global one.
//!
//! Exceptions: what `parse_options` lets through to its caller (the
//! catch-all handler of `Monitor_start.start`) is a [`ServerArgsError`]:
//!
//! - `raise (Arg.Bad message)` (a malformed `--with-mini-state`) happens
//!   after `Arg.parse`, so `Arg.parse` does not catch it.
//! - `String_utils.Incorrect_format` (a `--config` or
//!   `--custom-telemetry-data` without exactly one `=`) is raised inside an
//!   `Arg.String` callback, which `Arg.parse` does not catch either (it is
//!   the `Exn::Raise` of the spec list).
//! - What `Cli_args.get_saved_state_spec` lets through (see `crate::cli_args`),
//!   and the `Sys_error` of `Wwwroot.assert_www_directory`.

use std::cell::Cell;
use std::cell::RefCell;
use std::os::fd::RawFd;
use std::sync::LazyLock;

use crate::ai_options;
pub use crate::cli_args::*;
use crate::exit;
use crate::exit_status;
use crate::hh_version;
use crate::path;
use crate::rt::ocaml_arg;
use crate::rt::ocaml_arg::Spec;
use crate::string_utils::IncorrectFormat;
use crate::string_utils;
use crate::sys_utils::SysError;
use crate::wwwroot;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SavedStateTarget {
    SavedStateTargetInfo(SavedStateTargetInfo),
}

// ~~ The options from the command line ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Unix.file_descr` is a raw file descriptor. (`serde`: the monitor passes
/// the options to the server it spawns, `Server_main.params`.)
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Options {
    ai_mode: Option<ai_options::T>,
    check_mode: bool,
    config: Vec<(String, String)>,
    custom_hhi_path: Option<String>,
    custom_telemetry_data: Vec<(String, String)>,
    dump_fanout: bool,
    from: String,
    /// Whether to show preexisting warnings in typechecked files.
    preexisting_warnings: bool,
    ignore_hh_version: bool,
    saved_state_ignore_hhconfig: bool,
    json_mode: bool,
    max_procs: Option<isize>,
    no_load: bool,
    prechecked: Option<bool>,
    root: path::T,
    save_64bit: Option<String>,
    save_human_readable_64bit_dep_map: Option<String>,
    save_naming_filename: Option<String>,
    // AKA, daemon mode
    should_detach: bool,
    waiting_client: Option<RawFd>,
    watchman_debug_logging: bool,
    with_saved_state: Option<SavedStateTarget>,
    allow_non_opt_build: bool,
    write_symbol_info: Option<String>,
    /// `--save-state FILE` (the saved-state producer; see
    /// [`save_filename`]).
    save_filename: Option<String>,
    /// `--gen-saved-ignore-type-errors` (the saved-state producer)
    gen_saved_ignore_type_errors: bool,
}

// ~~ Usage code ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Sys.argv.(0)`
fn sys_argv_0() -> String {
    match std::env::args_os().next() {
        Some(arg) => arg.to_string_lossy().into_owned(),
        None => "".to_string(),
    }
}

pub static USAGE: LazyLock<String> =
    LazyLock::new(|| format!("Usage: {} [WWW DIRECTORY]\n", sys_argv_0()));

// ~~ Options ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `module Messages`
pub mod messages {
    use std::sync::LazyLock;

    pub const AI: &str = " run ai with options";

    pub const CHECK: &str = " check and exit";

    pub const CONFIG: &str = " override arbitrary value from hh.conf (format: <key>=<value>)";

    pub const CUSTOM_HHI_PATH: &str = " use custom hhi files";

    pub const DAEMON: &str = " detach process";

    pub const DUMP_FANOUT: &str = " dump fanout to stdout as JSON, then exit";

    pub const ENABLE_GLOBAL_ACCESS_CHECK: &str =
        " run global access checker to check global writes and reads";

    pub const FROM: &str = " so we know who's invoking - e.g. nuclide, vim, emacs, vscode";

    pub const FROM_VIM: &str = " DEPRECATED";

    pub const FROM_EMACS: &str = " DEPRECATED";

    pub const FROM_HHCLIENT: &str = " DEPRECATED";

    pub const IGNORE_HH_VERSION: &str = " ignore hh_version check when loading saved states";

    pub const SAVED_STATE_IGNORE_HHCONFIG: &str = " ignore hhconfig hash when loading saved states";

    pub const JSON: &str = " output errors in json format (arc lint mode)";

    pub const MAX_PROCS: &str = " max numbers of workers";

    pub const NO_LOAD: &str = " don't load from a saved state";

    pub const PRECHECKED: &str = " override value of \"prechecked_files\" flag from hh.conf";

    pub const PROFILE_LOG: &str = " enable profile logging";

    pub const SAVE_NAMING: &str = " save naming table to file";

    pub const SAVE_64BIT: &str = " save discovered 64-bit to the given directory";

    pub const SAVE_HUMAN_READABLE_64BIT_DEP_MAP: &str =
        " save human readable map of 64bit hashes to names to files in the given directory";

    pub const WAITING_CLIENT: &str = concat!(
        " send message to fd/handle when server has begun",
        " starting and again when it's done starting"
    );

    pub const WATCHMAN_DEBUG_LOGGING: &str =
        " Logs full Watchman requests and responses. This is very noisy";

    pub static WITH_SAVED_STATE: LazyLock<String> = LazyLock::new(|| {
        " Init with the given saved state instead of fetching it.\n".to_string()
            + "Expects a JSON string specified as: "
            + crate::cli_args::SAVED_STATE_JSON_DESCR
    });

    pub const WRITE_SYMBOL_INFO: &str = " write symbol info to json files";
}

pub fn print_json_version() {
    println!("{}", yojson::to_string(&hh_version::version_json()));
}

// ~~ What `String_utils` has and `crate::string_utils` does not yet ~~~~~~~~~~

// ~~ The main entry point ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The exceptions that `parse_options` lets through to its caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServerArgsError {
    /// `Arg.Bad` of a malformed `--with-mini-state`, raised after `Arg.parse`
    Bad(String),
    /// `String_utils.Incorrect_format`, raised in an `Arg.String` callback
    IncorrectFormat(IncorrectFormat),
    /// What `Cli_args.get_saved_state_spec` lets through
    CliArgs(CliArgsError),
    /// The `Sys_error` of `Wwwroot.assert_www_directory`
    SysError(SysError),
    /// (Test builds only.) What `Arg.parse` would print before it exits
    /// (`Bad` or `Help`): see [`arg_parse`].
    #[cfg(test)]
    ArgParse(ocaml_arg::Exn<IncorrectFormat>),
}

/// The result of the functions of the spec list of `parse_options`.
type Res = ocaml_arg::Res<IncorrectFormat>;

pub fn parse_options() -> Result<Options, ServerArgsError> {
    parse_options_of_argv(
        std::env::args_os()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect(),
        &USAGE,
    )
}

/// `parse_options ()` with `Sys.argv` = `argv` and `usage_msg` for
/// `usage` (which OCaml makes of `Sys.argv.(0)`).
pub fn parse_options_of_argv(argv: Vec<String>, usage_msg: &str) -> Result<Options, ServerArgsError> {
    let ai_mode = RefCell::new(None);
    let check_mode = Cell::new(false);
    let config: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let custom_hhi_path = RefCell::new(None);
    let custom_telemetry_data: RefCell<Vec<(String, String)>> = RefCell::new(vec![]);
    let dump_fanout = Cell::new(false);
    let from = RefCell::new("".to_string());
    let from_emacs = Cell::new(false);
    let from_hhclient = Cell::new(false);
    let from_vim = Cell::new(false);
    let preexisting_warnings = Cell::new(false);
    let ignore_hh = Cell::new(false);
    let saved_state_ignore_hhconfig = Cell::new(false);
    let json_mode = Cell::new(false);
    let max_procs = Cell::new(None);
    let no_load = Cell::new(false);
    let prechecked = Cell::new(None);
    let root = RefCell::new("".to_string());
    let save_64bit = RefCell::new(None);
    let save_human_readable_64bit_dep_map = RefCell::new(None);
    let save_naming = RefCell::new(None);
    let should_detach = Cell::new(false);
    let version = Cell::new(false);
    let waiting_client = Cell::new(None);
    let watchman_debug_logging = Cell::new(false);
    let with_saved_state: RefCell<Option<String>> = RefCell::new(None);
    let allow_non_opt_build = Cell::new(false);
    let write_symbol_info = RefCell::new(None);
    let save = RefCell::new(None);
    let gen_saved_ignore_type_errors = Cell::new(false);
    let set_save_state = |s: String| -> Res {
        *save.borrow_mut() = Some(s);
        Ok(())
    };
    let set_ai = |s: String| -> Res {
        *ai_mode.borrow_mut() = Some(ai_options::prepare(true, &s));
        Ok(())
    };
    let set_max_procs = |n: isize| -> Res {
        max_procs.set(Some(n));
        Ok(())
    };
    let set_save_naming = |s: String| -> Res {
        *save_naming.borrow_mut() = Some(s);
        Ok(())
    };
    // `Sys_utils.int_to_fd_naughty`: the integer is the descriptor.
    let set_wait = |fd: isize| -> Res {
        waiting_client.set(Some(fd as RawFd));
        Ok(())
    };
    let set_with_saved_state = |s: String| -> Res {
        *with_saved_state.borrow_mut() = Some(s);
        Ok(())
    };
    let set_write_symbol_info = |s: String| -> Res {
        *write_symbol_info.borrow_mut() = Some(s);
        Ok(())
    };
    let set_from = |s: String| -> Res {
        *from.borrow_mut() = s;
        Ok(())
    };
    {
        let options: ocaml_arg::Speclist<'_, IncorrectFormat> =
            vec![
            ("--ai".into(), Spec::String(Box::new(set_ai)), messages::AI.into()),
            (
                "--allow-non-opt-build".into(),
                Spec::Set(&allow_non_opt_build),
                "".into(),
            ),
            ("--check".into(), Spec::Set(&check_mode), messages::CHECK.into()),
            (
                "--config".into(),
                Spec::String(Box::new(|s: String| {
                    let kv = string_utils::split2_exn('=', &s).map_err(ocaml_arg::Exn::Raise)?;
                    config.borrow_mut().insert(0, kv);
                    Ok(())
                })),
                messages::CONFIG.into(),
            ),
            (
                "--custom-hhi-path".into(),
                Spec::String(Box::new(|s: String| {
                    *custom_hhi_path.borrow_mut() = Some(s);
                    Ok(())
                })),
                messages::CUSTOM_HHI_PATH.into(),
            ),
            (
                "--custom-telemetry-data".into(),
                Spec::String(Box::new(|s: String| {
                    let kv = string_utils::split2_exn('=', &s).map_err(ocaml_arg::Exn::Raise)?;
                    custom_telemetry_data.borrow_mut().insert(0, kv);
                    Ok(())
                })),
                "Add a custom column to all logged telemetry samples (format: <column>=<value>)"
                    .into(),
            ),
            ("--daemon".into(), Spec::Set(&should_detach), messages::DAEMON.into()),
            (
                "--dump-fanout".into(),
                Spec::Set(&dump_fanout),
                messages::DUMP_FANOUT.into(),
            ),
            (
                "--enable-global-access-check".into(),
                Spec::Unit(Box::new(|| {
                    config.borrow_mut().insert(
                        0,
                        ("enable_global_access_check".to_string(), "true".to_string()),
                    );
                    Ok(())
                })),
                messages::ENABLE_GLOBAL_ACCESS_CHECK.into(),
            ),
            (
                "--from-emacs".into(),
                Spec::Set(&from_emacs),
                messages::FROM_EMACS.into(),
            ),
            (
                "--from-hhclient".into(),
                Spec::Set(&from_hhclient),
                messages::FROM_HHCLIENT.into(),
            ),
            ("--from-vim".into(), Spec::Set(&from_vim), messages::FROM_VIM.into()),
            ("--from".into(), Spec::String(Box::new(set_from)), messages::FROM.into()),
            (
                "--preexisting-warnings".into(),
                Spec::Set(&preexisting_warnings),
                " show all preexisting warnings in typechecked files (default: false)".into(),
            ),
            (
                "--ignore-hh-version".into(),
                Spec::Set(&ignore_hh),
                messages::IGNORE_HH_VERSION.into(),
            ),
            ("--json".into(), Spec::Set(&json_mode), messages::JSON.into()),
            (
                "--max-procs".into(),
                Spec::Int(Box::new(set_max_procs)),
                messages::MAX_PROCS.into(),
            ),
            ("--no-load".into(), Spec::Set(&no_load), messages::NO_LOAD.into()),
            (
                "--no-prechecked".into(),
                Spec::Unit(Box::new(|| {
                    prechecked.set(Some(false));
                    Ok(())
                })),
                messages::PRECHECKED.into(),
            ),
            (
                "--prechecked".into(),
                Spec::Unit(Box::new(|| {
                    prechecked.set(Some(true));
                    Ok(())
                })),
                messages::PRECHECKED.into(),
            ),
            (
                "--profile-log".into(),
                Spec::Unit(Box::new(|| {
                    config
                        .borrow_mut()
                        .insert(0, ("profile_log".to_string(), "true".to_string()));
                    Ok(())
                })),
                messages::PROFILE_LOG.into(),
            ),
            (
                "--save-naming".into(),
                Spec::String(Box::new(set_save_naming)),
                messages::SAVE_NAMING.into(),
            ),
            (
                "--save-64bit".into(),
                Spec::String(Box::new(|s: String| {
                    *save_64bit.borrow_mut() = Some(s);
                    Ok(())
                })),
                messages::SAVE_64BIT.into(),
            ),
            (
                "--save-human-readable-64bit-dep-map".into(),
                Spec::String(Box::new(|s: String| {
                    *save_human_readable_64bit_dep_map.borrow_mut() = Some(s);
                    Ok(())
                })),
                messages::SAVE_HUMAN_READABLE_64BIT_DEP_MAP.into(),
            ),
            (
                "--saved-state-ignore-hhconfig".into(),
                Spec::Set(&saved_state_ignore_hhconfig),
                messages::SAVED_STATE_IGNORE_HHCONFIG.into(),
            ),
            ("--version".into(), Spec::Set(&version), "".into()),
            (
                "--waiting-client".into(),
                Spec::Int(Box::new(set_wait)),
                messages::WAITING_CLIENT.into(),
            ),
            (
                "--watchman-debug-logging".into(),
                Spec::Set(&watchman_debug_logging),
                messages::WATCHMAN_DEBUG_LOGGING.into(),
            ),
            (
                "--with-mini-state".into(),
                Spec::String(Box::new(set_with_saved_state)),
                messages::WITH_SAVED_STATE.clone(),
            ),
            (
                "--write-symbol-info".into(),
                Spec::String(Box::new(set_write_symbol_info)),
                messages::WRITE_SYMBOL_INFO.into(),
            ),
            ("-d".into(), Spec::Set(&should_detach), messages::DAEMON.into()),
            // The saved-state producer: the options of the OCaml just
            // before this version (removed upstream by f6cc06f5b6e, "Remove
            // hh_client --save-state and hh_server --save-state"), hidden from
            // `--help` (an empty doc) so that the help stays the OCaml's.
            (
                "--gen-saved-ignore-type-errors".into(),
                Spec::Set(&gen_saved_ignore_type_errors),
                "".into(),
            ),
            ("--save-mini".into(), Spec::String(Box::new(set_save_state)), "".into()),
            ("--save-state".into(), Spec::String(Box::new(set_save_state)), "".into()),
            ("-s".into(), Spec::String(Box::new(set_save_state)), "".into()),
        ];
        let mut options = ocaml_arg::align(options, None);
        arg_parse(
            &argv,
            &mut options,
            &mut |s: String| -> Res {
                *root.borrow_mut() = s;
                Ok(())
            },
            usage_msg,
        )?;
    }
    if version.get() {
        if json_mode.get() {
            print_json_version()
        } else {
            println!("{}", hh_version::version());
        }
        ocaml_arg::stdlib_exit(0)
    };
    // --json, --save, --write-symbol-info all imply check
    let check_mode = write_symbol_info.borrow().is_some()
        || check_mode.get()
        || json_mode.get()
        || save.borrow().is_some();
    if check_mode && waiting_client.get().is_some() {
        eprint!("--check is incompatible with wait modes!\n");
        exit::exit(None, None, None, None, exit_status::T::InputError)
    };
    let with_saved_state = match get_saved_state_spec(with_saved_state.borrow().as_deref())
        .map_err(ServerArgsError::CliArgs)?
    {
        Ok(Some(spec)) => Some(SavedStateTarget::SavedStateTargetInfo(spec)),
        Ok(None) => None,
        Err(message) => return Err(ServerArgsError::Bad(message)),
    };
    match root.borrow().as_str() {
        "" => {
            eprint!("You must specify a root directory!\n");
            exit::exit(None, None, None, None, exit_status::T::InputError)
        }
        _ => {}
    };
    let root_path = path::make(&root.borrow());
    wwwroot::assert_www_directory(&root_path).map_err(ServerArgsError::SysError)?;
    if gen_saved_ignore_type_errors.get() && save.borrow().is_none() {
        eprint!("--gen-saved-ignore-type-errors is only valid when combined with --save-state\n");
        ocaml_arg::stdlib_exit(1)
    };
    Ok(Options {
        ai_mode: ai_mode.into_inner(),
        check_mode,
        config: config.into_inner(),
        custom_hhi_path: custom_hhi_path.into_inner(),
        custom_telemetry_data: custom_telemetry_data.into_inner(),
        dump_fanout: dump_fanout.get(),
        from: from.into_inner(),
        preexisting_warnings: preexisting_warnings.get(),
        ignore_hh_version: ignore_hh.get(),
        saved_state_ignore_hhconfig: saved_state_ignore_hhconfig.get(),
        json_mode: json_mode.get(),
        max_procs: max_procs.get(),
        no_load: no_load.get(),
        prechecked: prechecked.get(),
        root: root_path,
        save_64bit: save_64bit.into_inner(),
        save_human_readable_64bit_dep_map: save_human_readable_64bit_dep_map.into_inner(),
        save_naming_filename: save_naming.into_inner(),
        should_detach: should_detach.get(),
        waiting_client: waiting_client.get(),
        watchman_debug_logging: watchman_debug_logging.get(),
        with_saved_state,
        allow_non_opt_build: allow_non_opt_build.get(),
        write_symbol_info: write_symbol_info.into_inner(),
        save_filename: save.into_inner(),
        gen_saved_ignore_type_errors: gen_saved_ignore_type_errors.get(),
    })
}

/// `Arg.parse` (`crate::rt::ocaml_arg::parse`). In test builds, it returns
/// what `Arg.parse` would print (`ocaml_arg::Exn::Bad` or `Help`) instead of
/// printing it and exiting (`ServerArgsError::ArgParse`), so that tests can
/// look at it.
fn arg_parse(
    argv: &[String],
    speclist: &mut ocaml_arg::Speclist<'_, IncorrectFormat>,
    anonfun: &mut ocaml_arg::AnonFun<'_, IncorrectFormat>,
    errmsg: &str,
) -> Result<(), ServerArgsError> {
    #[cfg(not(test))]
    return ocaml_arg::parse(argv, speclist, anonfun, errmsg)
        .map_err(ServerArgsError::IncorrectFormat);
    #[cfg(test)]
    match ocaml_arg::parse_argv(None, argv, speclist, anonfun, errmsg) {
        Ok(()) => Ok(()),
        Err(ocaml_arg::Exn::Raise(e)) => Err(ServerArgsError::IncorrectFormat(e)),
        Err(e) => Err(ServerArgsError::ArgParse(e)),
    }
}

/// useful in testing code
pub fn default_options(root: &str) -> Options {
    Options {
        ai_mode: None,
        check_mode: false,
        config: vec![],
        custom_hhi_path: None,
        custom_telemetry_data: vec![],
        dump_fanout: false,
        from: "".to_string(),
        preexisting_warnings: false,
        ignore_hh_version: false,
        saved_state_ignore_hhconfig: false,
        json_mode: false,
        max_procs: None,
        no_load: true,
        prechecked: None,
        root: path::make(root),
        save_64bit: None,
        save_human_readable_64bit_dep_map: None,
        save_naming_filename: None,
        should_detach: false,
        waiting_client: None,
        watchman_debug_logging: false,
        with_saved_state: None,
        allow_non_opt_build: false,
        write_symbol_info: None,
        save_filename: None,
        gen_saved_ignore_type_errors: false,
    }
}

/// Useful for executables which don't want to make a subscription to a
/// file-watching service.
pub fn default_options_with_check_mode(root: &str) -> Options {
    Options {
        check_mode: true,
        ..default_options(root)
    }
}

// ~~ Accessors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn ai_mode(options: &Options) -> Option<ai_options::T> {
    options.ai_mode.clone()
}

pub fn check_mode(options: &Options) -> bool {
    options.check_mode
}

pub fn config(options: &Options) -> Vec<(String, String)> {
    options.config.clone()
}

pub fn custom_hhi_path(options: &Options) -> Option<String> {
    options.custom_hhi_path.clone()
}

pub fn custom_telemetry_data(options: &Options) -> Vec<(String, String)> {
    options.custom_telemetry_data.clone()
}

pub fn dump_fanout(options: &Options) -> bool {
    options.dump_fanout
}

pub fn from(options: &Options) -> String {
    options.from.clone()
}

pub fn ignore_hh_version(options: &Options) -> bool {
    options.ignore_hh_version
}

pub fn saved_state_ignore_hhconfig(options: &Options) -> bool {
    options.saved_state_ignore_hhconfig
}

pub fn json_mode(options: &Options) -> bool {
    options.json_mode
}

pub fn max_procs(options: &Options) -> Option<isize> {
    options.max_procs
}

pub fn no_load(options: &Options) -> bool {
    options.no_load
}

pub fn prechecked(options: &Options) -> Option<bool> {
    options.prechecked
}

pub fn root(options: &Options) -> path::T {
    options.root.clone()
}

pub fn save_64bit(options: &Options) -> Option<String> {
    options.save_64bit.clone()
}

pub fn save_human_readable_64bit_dep_map(options: &Options) -> Option<String> {
    options.save_human_readable_64bit_dep_map.clone()
}

/// `save_filename options`: `--save-state FILE` (the saved-state producer).
pub fn save_filename(options: &Options) -> Option<String> {
    options.save_filename.clone()
}

/// `gen_saved_ignore_type_errors options` (the saved-state producer)
pub fn gen_saved_ignore_type_errors(options: &Options) -> bool {
    options.gen_saved_ignore_type_errors
}

pub fn save_naming_filename(options: &Options) -> Option<String> {
    options.save_naming_filename.clone()
}

pub fn should_detach(options: &Options) -> bool {
    options.should_detach
}

pub fn waiting_client(options: &Options) -> Option<RawFd> {
    options.waiting_client
}

pub fn watchman_debug_logging(options: &Options) -> bool {
    options.watchman_debug_logging
}

pub fn with_saved_state(options: &Options) -> Option<SavedStateTarget> {
    options.with_saved_state.clone()
}

pub fn is_using_precomputed_saved_state(options: &Options) -> bool {
    match with_saved_state(options) {
        Some(SavedStateTarget::SavedStateTargetInfo(_)) => true,
        None => false,
    }
}

pub fn allow_non_opt_build(options: &Options) -> bool {
    options.allow_non_opt_build
}

pub fn write_symbol_info(options: &Options) -> Option<String> {
    options.write_symbol_info.clone()
}

pub fn preexisting_warnings(options: &Options) -> bool {
    options.preexisting_warnings
}

// ~~ Setters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn clear_precomputed_saved_state(options: Options) -> Options {
    Options {
        with_saved_state: None,
        ..options
    }
}

pub fn set_ai_mode(options: Options, ai_mode: Option<ai_options::T>) -> Options {
    Options { ai_mode, ..options }
}

pub fn set_check_mode(options: Options, check_mode: bool) -> Options {
    Options {
        check_mode,
        ..options
    }
}

pub fn set_max_procs(options: Options, procs: isize) -> Options {
    Options {
        max_procs: Some(procs),
        ..options
    }
}

pub fn set_no_load(options: Options, is_no_load: bool) -> Options {
    Options {
        no_load: is_no_load,
        ..options
    }
}

pub fn set_config(options: Options, config: Vec<(String, String)>) -> Options {
    Options { config, ..options }
}

pub fn set_from(options: Options, from: String) -> Options {
    Options { from, ..options }
}

pub fn set_save_64bit(options: Options, save_64bit: Option<String>) -> Options {
    Options {
        save_64bit,
        ..options
    }
}

pub fn set_save_naming_filename(options: Options, save_naming_filename: Option<String>) -> Options {
    Options {
        save_naming_filename,
        ..options
    }
}

// ~~ Misc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn to_string(options: &Options) -> String {
    let Options {
        ai_mode,
        check_mode,
        config,
        custom_hhi_path,
        custom_telemetry_data,
        dump_fanout,
        from,
        preexisting_warnings,
        ignore_hh_version,
        saved_state_ignore_hhconfig,
        json_mode,
        max_procs,
        no_load,
        prechecked,
        root,
        save_64bit,
        save_human_readable_64bit_dep_map,
        save_naming_filename,
        should_detach,
        waiting_client,
        watchman_debug_logging,
        with_saved_state,
        allow_non_opt_build,
        write_symbol_info,
        // (Not in the OCaml's `to_string` of this version: the saved-state
        // producer's.)
        save_filename: _,
        gen_saved_ignore_type_errors: _,
    } = options;
    let ai_mode_str = match ai_mode {
        None => "<>",
        Some(_) => "Some(...)",
    };
    let saved_state_str = match with_saved_state {
        None => "<>",
        Some(_) => "SavedStateTarget(...)",
    };
    let waiting_client_str = match waiting_client {
        None => "<>",
        Some(_) => "WaitingClient(...)",
    };
    let custom_hhi_path_str = match custom_hhi_path {
        None => "<>",
        Some(path) => path,
    };
    let save_64bit_str = match save_64bit {
        None => "<>",
        Some(path) => path,
    };
    let save_human_readable_64bit_dep_map_str = match save_human_readable_64bit_dep_map {
        None => "<>",
        Some(path) => path,
    };
    let save_naming_filename_str = match save_naming_filename {
        None => "<>",
        Some(path) => path,
    };
    let prechecked_str = match prechecked {
        None => "<>".to_string(),
        Some(b) => b.to_string(),
    };
    let max_procs_str = match max_procs {
        None => "<>".to_string(),
        Some(n) => n.to_string(),
    };
    let write_symbol_info_str = match write_symbol_info {
        None => "<>",
        Some(s) => s,
    };
    let config_str = format!(
        "[{}]",
        config
            .iter()
            .map(|(key, value)| format!("{}={}", key, value))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let custom_telemetry_data_str = format!(
        "[{}]",
        custom_telemetry_data
            .iter()
            .map(|(column, value)| format!("{}={}", column, value))
            .collect::<Vec<_>>()
            .join(", ")
    );
    [
        "Server_args.options({",
        "ai_mode: ",
        ai_mode_str,
        ", ",
        "check_mode: ",
        &check_mode.to_string(),
        ", ",
        "config: ",
        &config_str,
        "custom_hhi_path: ",
        custom_hhi_path_str,
        "custom_telemetry_data: ",
        &custom_telemetry_data_str,
        "dump_fanout: ",
        &dump_fanout.to_string(),
        ", ",
        "from: ",
        from,
        ", ",
        "preexisting_warnings: ",
        &preexisting_warnings.to_string(),
        ", ",
        "ignore_hh_version: ",
        &ignore_hh_version.to_string(),
        ", ",
        "saved_state_ignore_hhconfig: ",
        &saved_state_ignore_hhconfig.to_string(),
        ", ",
        "json_mode: ",
        &json_mode.to_string(),
        ", ",
        "maxprocs: ",
        &max_procs_str,
        ", ",
        "no_load: ",
        &no_load.to_string(),
        ", ",
        "prechecked: ",
        &prechecked_str,
        ", ",
        "root: ",
        &path::to_string(root),
        ", ",
        "save_64bit: ",
        save_64bit_str,
        ", ",
        "save_human_readable_64bit_dep_map: ",
        save_human_readable_64bit_dep_map_str,
        ", ",
        "save_naming_filename: ",
        save_naming_filename_str,
        ", ",
        "should_detach: ",
        &should_detach.to_string(),
        ", ",
        "waiting_client: ",
        waiting_client_str,
        ", ",
        "watchman_debug_logging: ",
        &watchman_debug_logging.to_string(),
        ", ",
        "with_saved_state: ",
        saved_state_str,
        ", ",
        "allow_non_opt_build: ",
        &allow_non_opt_build.to_string(),
        ", ",
        "write_symbol_info: ",
        write_symbol_info_str,
        ", ",
        "})",
    ]
    .concat()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn argv(l: &[&str]) -> Vec<String> {
        // Each parse starts at the beginning, as the only parse of a process
        // does (`Arg.current` is 0).
        ocaml_arg::with_current(|current| current.set(0));
        l.iter().map(|s| s.to_string()).collect()
    }

    fn scratch_root(name: &str) -> String {
        let dir =
            std::env::temp_dir().join(format!("hh_server_args_{}_{}", name, std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(".hhconfig"), b"").unwrap();
        dir.to_str().unwrap().to_string()
    }

    #[test]
    fn options_of_a_command_line() {
        let dir = scratch_root("cmdline");
        let options = parse_options_of_argv(
            argv(&[
                "hh_server",
                "--check",
                "--config",
                "a=1",
                "--enable-global-access-check",
                "--config=b=2",
                "--profile-log",
                "--max-procs",
                "4",
                "--from",
                "test",
                "--no-prechecked",
                "--prechecked",
                "--custom-telemetry-data",
                "c=d",
                "-d",
                &dir,
            ]),
            "Usage: hh_server [WWW DIRECTORY]\n",
        )
        .unwrap();
        assert!(check_mode(&options));
        assert!(should_detach(&options));
        assert_eq!(max_procs(&options), Some(4));
        assert_eq!(from(&options), "test");
        assert_eq!(prechecked(&options), Some(true));
        // `--config` and friends prepend.
        assert_eq!(
            config(&options),
            vec![
                ("profile_log".to_string(), "true".to_string()),
                ("b".to_string(), "2".to_string()),
                ("enable_global_access_check".to_string(), "true".to_string()),
                ("a".to_string(), "1".to_string()),
            ]
        );
        assert_eq!(
            custom_telemetry_data(&options),
            vec![("c".to_string(), "d".to_string())]
        );
        assert_eq!(root(&options), path::make(&dir));
        assert!(!no_load(&options));
        assert!(!is_using_precomputed_saved_state(&options));
        assert_eq!(
            to_string(&options),
            format!(
                "Server_args.options({{ai_mode: <>, check_mode: true, config: [profile_log=true, b=2, enable_global_access_check=true, a=1]custom_hhi_path: <>custom_telemetry_data: [c=d]dump_fanout: false, from: test, preexisting_warnings: false, ignore_hh_version: false, saved_state_ignore_hhconfig: false, json_mode: false, maxprocs: 4, no_load: false, prechecked: true, root: {}, save_64bit: <>, save_human_readable_64bit_dep_map: <>, save_naming_filename: <>, should_detach: true, waiting_client: <>, watchman_debug_logging: false, with_saved_state: <>, allow_non_opt_build: false, write_symbol_info: <>, }})",
                path::make(&dir)
            )
        );
        // --json implies check.
        let options = parse_options_of_argv(argv(&["hh_server", "--json", &dir]), "U\n").unwrap();
        assert!(check_mode(&options));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn with_mini_state() {
        let root = scratch_root("mini_state");
        let spec = r#"{"data_dump": {"state": "/ss/b", "corresponding_base_revision": "abc", "deptable": "/ss/b.hhdg", "changes": ["a.php"]}}"#;
        let options = parse_options_of_argv(
            argv(&["hh_server", "--with-mini-state", spec, &root]),
            "U\n",
        )
        .unwrap();
        assert!(is_using_precomputed_saved_state(&options));
        match with_saved_state(&options) {
            Some(SavedStateTarget::SavedStateTargetInfo(info)) => {
                assert_eq!(info.naming_table_path, "/ss/b");
                assert_eq!(info.changes, vec![crate::relative_path::from_root("a.php")]);
            }
            None => panic!("no saved state"),
        }
        // A spec that does not parse is `Arg.Bad`, raised after `Arg.parse`.
        let bad = parse_options_of_argv(
            argv(&["hh_server", "--with-mini-state", "{}", &root]),
            "U\n",
        )
        .unwrap_err();
        assert_eq!(
            bad,
            ServerArgsError::Bad(
                "Parsing failed:\n  data dump failure: Missing key: data_dump\n  from_file failure: Missing key: from_file\nSee input: {}\n".to_string()
            )
        );
        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn config_needs_one_equal_sign() {
        let e = parse_options_of_argv(argv(&["hh_server", "--config", "a=b=c", "/"]), "U\n")
            .unwrap_err();
        assert_eq!(e, ServerArgsError::IncorrectFormat(IncorrectFormat));
        // `Str.split` skips one `=` at the start and the end.
        assert_eq!(
            string_utils::split2_exn('=', "=k=v"),
            Ok(("k".to_string(), "v".to_string()))
        );
        for bad in ["k=", "kv", "a==b"] {
            assert_eq!(string_utils::split2_exn('=', bad), Err(IncorrectFormat), "{}", bad);
        }
        // `--custom-telemetry-data` too.
        let e = parse_options_of_argv(
            argv(&["hh_server", "--custom-telemetry-data", "c", "/"]),
            "U\n",
        )
        .unwrap_err();
        assert_eq!(e, ServerArgsError::IncorrectFormat(IncorrectFormat));
    }

    /// `hh_server --help` (and the usage after an error), as `Arg.align` and
    /// `Arg.usage` make it. The expected text was computed independently,
    /// from `stdlib/arg.ml`.
    #[test]
    fn help() {
        let raised = |l: &[&str]| {
            match parse_options_of_argv(argv(l), "Usage: hh_server [WWW DIRECTORY]\n") {
                Err(ServerArgsError::ArgParse(e)) => e,
                r => panic!("{:?}", r),
            }
        };
        let help = HELP.to_string();
        assert_eq!(
            raised(&["hh_server", "--help"]),
            ocaml_arg::Exn::Help(help.clone())
        );
        assert_eq!(
            raised(&["hh_server", "-help"]),
            ocaml_arg::Exn::Help(help.clone())
        );
        assert_eq!(
            raised(&["hh_server", "--bogus"]),
            ocaml_arg::Exn::Bad(format!("hh_server: unknown option '--bogus'.\n{}", help))
        );
        assert_eq!(
            raised(&["hh_server", "--max-procs", "four"]),
            ocaml_arg::Exn::Bad(format!(
                "hh_server: wrong argument 'four'; option '--max-procs' expects an integer.\n{}",
                help
            ))
        );
        assert_eq!(
            raised(&["hh_server", "/", "--from"]),
            ocaml_arg::Exn::Bad(format!(
                "hh_server: option '--from' needs an argument.\n{}",
                help
            ))
        );
    }

    const HELP: &str = r#"Usage: hh_server [WWW DIRECTORY]

  --ai                                 run ai with options
  --check                              check and exit
  --config                             override arbitrary value from hh.conf (format: <key>=<value>)
  --custom-hhi-path                    use custom hhi files
  --custom-telemetry-data Add          a custom column to all logged telemetry samples (format: <column>=<value>)
  --daemon                             detach process
  --dump-fanout                        dump fanout to stdout as JSON, then exit
  --enable-global-access-check         run global access checker to check global writes and reads
  --from-emacs                         DEPRECATED
  --from-hhclient                      DEPRECATED
  --from-vim                           DEPRECATED
  --from                               so we know who's invoking - e.g. nuclide, vim, emacs, vscode
  --preexisting-warnings               show all preexisting warnings in typechecked files (default: false)
  --ignore-hh-version                  ignore hh_version check when loading saved states
  --json                               output errors in json format (arc lint mode)
  --max-procs                          max numbers of workers
  --no-load                            don't load from a saved state
  --no-prechecked                      override value of "prechecked_files" flag from hh.conf
  --prechecked                         override value of "prechecked_files" flag from hh.conf
  --profile-log                        enable profile logging
  --save-naming                        save naming table to file
  --save-64bit                         save discovered 64-bit to the given directory
  --save-human-readable-64bit-dep-map  save human readable map of 64bit hashes to names to files in the given directory
  --saved-state-ignore-hhconfig        ignore hhconfig hash when loading saved states
  --waiting-client                     send message to fd/handle when server has begun starting and again when it's done starting
  --watchman-debug-logging             Logs full Watchman requests and responses. This is very noisy
  --with-mini-state                    Init with the given saved state instead of fetching it.
Expects a JSON string specified as: A JSON specification for how to initialize with a saved state.

Saved state JSON looks like this:
{
  "state": <saved state filename>,
  "corresponding_base_revision" : <Mercurial commit hash>,
  "deptable": <dependency table filename>,
  "changes": [array of files changed since that saved state]
}

For example:
{
  "deptable": "/home/unixname/saved-states/ss1.sql",
  "state": "/home/unixname/saved-states/ss1",
  "changes": [],
  "prechecked_changes": [],
  "corresponding_base_revision": "bab0de0041defb4d7a5d520d224aa4922ed04d37"
}

You can put this saved state JSON into a file and pass this JSON as the argument:
{
  "from_file": "/home/unixname/saved-states/ss1.json"
}

Alternatively, you can pass this JSON as the argument, with the saved state JSON embedded:
{
  "data_dump":
  {
    "deptable": "/home/unixname/saved-states/ss1.sql",
    "state": "/home/unixname/saved-states/ss1",
    "changes": [],
    "prechecked_changes": [],
    "corresponding_base_revision": "bab0de0041defb4d7a5d520d224aa4922ed04d37"
  }
}

  --write-symbol-info                  write symbol info to json files
  -d                                   detach process
  -help                                Display this list of options
  --help                               Display this list of options
"#;

    #[test]
    fn defaults_and_setters() {
        let o = default_options("/");
        assert!(no_load(&o));
        assert!(!check_mode(&o));
        assert!(check_mode(&default_options_with_check_mode("/")));
        let o = set_max_procs(set_no_load(o, false), 3);
        assert_eq!(max_procs(&o), Some(3));
        assert!(!no_load(&o));
        let o = set_save_naming_filename(set_from(o, "x".to_string()), Some("n".to_string()));
        assert_eq!(save_naming_filename(&o), Some("n".to_string()));
        assert_eq!(from(&o), "x");
    }
}
