// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hh_client.ml`. See `hh/PORTING.md`.
//!
//! Hack for HipHop: type checker's client code.
//!
//! This code gets called in various different ways:
//! - from emacs, where the output is asynchronous
//! - from vim, where vim is blocked until this code exits
//! - from arc diff, our linter
//! - from arc land, our commit hook
//! - from check trunk, our irc bot which checks the state of trunk
//! - manually, from the command line
//!
//! Usage: hh_client [OPTION]... [WWW DIRECTORY] [FILE]...
//!
//! # What is not ported yet
//!
//! The command line is parsed and validated in full (`Client_args`). The
//! actions that are not there yet are the temporary stand-in of the daemon
//! plan (§3.4): `hh_client: <command> is not ported to Rust yet` on stderr,
//! exit 10 (`Input_error`): `Client_lsp.main` (G3), `Client_decompress_zhhdg.main`,
//! and the Meta-only `Client_saved_state_project_metadata.main` and
//! `Client_download_saved_state.main`. Each has a function here that its
//! assignment replaces with the call. `Client_check.main` refuses the modes
//! that are not ported in the same way.
//!
//! # The OCaml mechanisms
//!
//! - The toplevel `let () = try main () with ...` is [`toplevel`], which the
//!   `hh_client` binary calls.
//! - The exceptions are `Result`s (PORTING.md, "Exceptions"): an action
//!   returns `Err` of what it lets through (`Exit_status.Exit_with`, or an
//!   error that nothing catches until here), which the `with exn ->` of
//!   [`exec_command_with_config`] and [`exec_command_without_config`] get as
//!   an [`Exn`]. Those handlers, and the toplevel's, catch everything, so
//!   they also catch panics (`failwith`, `todo!`, ...) with `catch_unwind`.
//! - The SIGINT handler cannot raise `Exit_with Interrupted` in the main
//!   thread: it runs on a thread of its own (`rt::ocaml_sys::set_signal`) and
//!   does what catching that exception would do: inside the `try`s of
//!   `exec_command_without_config` and `exec_command_with_config`, their
//!   `with` arm ([`set_interrupt_catch`]: `[DecompressZhhdg] ...` on stdout,
//!   or `handle_exn_and_exit`); elsewhere `Exit.exit Interrupted`, as `main`
//!   and the toplevel do (exit 130).
//! - `Hack_event_logger` is a stub in the OSS build (and compiled with `port`
//!   only here): its calls are not made. `Hh_logger` does not write a log yet
//!   (`crate::hh_logger`), so `CLIENT_BAD_EXIT` lines are not shown.
//! - `Lwt_utils.run_main f` is `f()`.
//! - `Daemon.check_entry_point` and `Startup_initializer.init` do nothing:
//!   the Rust server layer does not fork daemons (design 7.3), and the OSS
//!   initializer is a no-op.

use std::cell::RefCell;
use std::io::Write;
use std::panic::AssertUnwindSafe;
use std::sync::Arc;
use std::sync::Mutex;

use crate::client_args;
use crate::client_command;
use crate::client_connect::ClientConnectError;
use crate::client_command::Command;
use crate::client_command::HeavyCommand;
use crate::client_command::LightCommand;
use crate::client_decompress_zhhdg;
use crate::client_download_saved_state;
use crate::client_env;
use crate::client_lsp;
use crate::client_rage;
use crate::client_start;
use crate::client_start::ClientStartError;
use crate::client_stop;
use crate::config_file;
use crate::exception;
use crate::exit;
use crate::exit_status;
use crate::exit_status::ExitWith;
use crate::hh_logger;
use crate::path;
use crate::proc;
use crate::random_id;
use crate::relative_path;
use crate::rt::ocaml_sys;
use crate::rt::ocaml_unix;
use crate::server_config;
use crate::server_files;
use crate::server_local_config;
use crate::server_local_config_qe;
use crate::server_progress;
use crate::sys_utils;

pub fn init_event_logger(
    _root: &path::T,
    _command: &HeavyCommand,
    _init_id: &str,
    _from: &str,
    _config: &server_config::T,
    _local_config: &server_local_config::T,
) {
    // `Hack_event_logger.client_init ~init_id ~from ~is_interactive:(Client_args.is_interactive command)
    // ~custom_columns:(Client_command.get_custom_telemetry_data command) root`, then
    // `set_hhconfig_version (Server_config.version config |> Config_file.version_to_string_opt)`,
    // `set_rollout_group local_config.rollout_group` and
    // `set_rollout_flags (Server_local_config_load.to_rollout_flags local_config)`: no-ops in
    // the OSS build (see the module documentation).
}

pub fn log_qe_fetch(_fetch: &server_local_config_qe::Fetch) {
    // `Hack_event_logger.client_qe_fetch ~start_time ~end_time`: a no-op in
    // the OSS build.
}

/// (Not in OCaml: the emulation of the SIGINT handler's exception, see
/// [`set_up_signals`].) What the `try ... with` that the `Exit_with
/// Interrupted` of the SIGINT handler would reach in OCaml does with it (it
/// ends in `Exit.exit`), while the main thread is inside one: the `try`s of
/// [`exec_command_without_config`] and [`exec_command_with_config`] set it
/// for their extent. `None` elsewhere, where the exception reaches the
/// handler of `main` or of the toplevel, which do `Exit.exit Interrupted`.
/// An action whose OCaml catches `Exit_with Interrupted` itself sets its own
/// while it runs (and puts the previous one back).
static INTERRUPT_CATCH: Mutex<Option<Arc<dyn Fn() + Send + Sync>>> = Mutex::new(None);

/// Sets [`INTERRUPT_CATCH`].
pub fn set_interrupt_catch(catch: Option<Arc<dyn Fn() + Send + Sync>>) {
    *INTERRUPT_CATCH.lock().unwrap_or_else(|e| e.into_inner()) = catch;
}

pub fn set_up_signals() {
    // Ignore SIGPIPE since if it arises from clientConnect then it might indicate server hangup;
    // we detect this case already and handle it better than a signal (unhandled signals cause program exit).
    ocaml_sys::set_signal(libc::SIGPIPE, ocaml_sys::SignalBehavior::SignalIgnore);
    // `raise Exit_status.(Exit_with Interrupted)`: the handler runs on a thread
    // of its own, so it does what catching the exception would do.
    ocaml_sys::set_signal(
        libc::SIGINT,
        ocaml_sys::SignalBehavior::SignalHandle(Arc::new(|_| {
            let catch = INTERRUPT_CATCH
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .clone();
            if let Some(catch) = catch {
                catch();
            }
            // `main` and the toplevel: `Exit.exit exit_status`
            exit::exit(None, None, None, exit_status::T::Interrupted)
        })),
    );
}

pub fn set_up_logger(command_name: &str, init_id: &str, root: &path::T) {
    // We'll chose where Hh_logger.log gets sent
    hh_logger::level::set_min_level_file(hh_logger::level::T::Info);
    hh_logger::level::set_min_level_stderr(hh_logger::level::T::Error);
    hh_logger::set_id(&format!("{}#{}", command_name, init_id));
    let client_log_fn = server_files::client_log(root);
    // For irritating reasons T67177821 we might not have permissions
    // to write to the file. Pending a fix, let's only set up Hh_logger
    // to write to the file if we can indeed safely write to it.
    match sys_utils::touch(
        sys_utils::TouchMode::TouchExistingFileOrCreateNew {
            mkdir_if_new: false,
            perm_if_new: 0o666,
        },
        &client_log_fn,
    ) {
        Ok(()) => hh_logger::set_log(&client_log_fn),
        Err(_) => {}
    }
}

pub fn set_up_root(root: &path::T) {
    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new(root));
    server_progress::set_root(root.clone());
}

/// An exception that is only its printed form (`Exception.to_string`): the
/// second value of the `exn` that [`exit_status_of_exn`] returns twice.
struct Printed(String);

impl std::fmt::Debug for Printed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// An exception that reaches the handlers of this module (`exn`):
/// `Exit_status.Exit_with`, or any other, wrapped (an error value that an
/// action returned, or the payload of a panic).
#[derive(Debug)]
pub enum Exn {
    /// `Exit_status.Exit_with`
    ExitWith(exit_status::T),
    /// Any other exception
    Other(exception::T),
}

impl Exn {
    /// A caught panic.
    pub fn of_panic(payload: Box<dyn std::any::Any + Send>) -> Self {
        Exn::Other(exception::wrap(payload))
    }
}

impl From<ExitWith> for Exn {
    fn from(ExitWith(es): ExitWith) -> Self {
        Exn::ExitWith(es)
    }
}

impl From<ClientStartError> for Exn {
    fn from(e: ClientStartError) -> Self {
        match e {
            ClientStartError::ExitWith(e) => e.into(),
            ClientStartError::UncaughtReadError(e) => Exn::Other(exception::wrap(e)),
        }
    }
}

impl From<ClientConnectError> for Exn {
    fn from(e: ClientConnectError) -> Self {
        match e {
            ClientConnectError::ExitWith(e) => e.into(),
            ClientConnectError::UncaughtReadError(e) => Exn::Other(exception::wrap(e)),
            ClientConnectError::TwoRetriesInARow(e) => Exn::Other(exception::wrap(e)),
        }
    }
}

/// The exit status of a caught exception, and the exception. OCaml returns
/// the same `Exception.t` in both when the exit status is
/// `Uncaught_exception e`; an `exception::T` cannot be copied, so the second
/// one is another with the same printed form (it only goes to telemetry).
pub fn exit_status_of_exn(exn: Exn) -> (exit_status::T, exception::T) {
    match exn {
        Exn::ExitWith(es) => {
            let exit_with = ExitWith(es);
            let e = exception::wrap(Printed(format!("{:?}", exit_with)));
            let ExitWith(es) = exit_with;
            (es, e)
        }
        Exn::Other(e) => {
            let es = exit_status::T::UncaughtException(exception::wrap(Printed(
                exception::get_ctor_string(&e),
            )));
            (es, e)
        }
    }
}

pub fn handle_exn_and_exit(exn: Exn, command_name: &str) -> ! {
    let is_exit_with = matches!(exn, Exn::ExitWith(_));
    let (es, _e) = exit_status_of_exn(exn);
    // hide the spinner
    crate::client_spinner::report(false, false, None);
    // We trust that if someone raised Exit_with then they had the decency to print
    // out a user-facing message; we will only print out a user-facing message here
    // for uncaught exceptions: lvl=Error gets sent to stderr, but lvl=Info doesn't.
    let _lvl = if is_exit_with {
        hh_logger::level::T::Info
    } else {
        hh_logger::level::T::Error
    };
    hh_logger::log(&format!(
        "CLIENT_BAD_EXIT [{}] {}",
        command_name,
        exit_status::show_expanded(&es)
    ));
    // `Hack_event_logger.client_bad_exit ~command_name es e`: a no-op in the
    // OSS build.
    exit::exit(None, None, None, es)
}

/// The `with exn -> ...` of [`exec_command_without_config`].
fn handle_exn_without_config(name: &str, exn: Exn) -> ! {
    let (es, _e) = exit_status_of_exn(exn);
    print!("[{}] {}\n", name, exit_status::show_expanded(&es));
    exit::exit(None, None, None, es)
}

/// `Exit_with Interrupted`, which the SIGINT handler raises.
fn interrupted() -> Exn {
    Exn::ExitWith(exit_status::T::Interrupted)
}

pub fn exec_command_without_config(command: LightCommand) -> ! {
    let name = client_command::name_camel_case_light(&command);
    set_interrupt_catch(Some(Arc::new(move || {
        handle_exn_without_config(name, interrupted())
    })));
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| -> Result<(), Exn> {
        let exit_status = match command {
            LightCommand::CDecompressZhhdg(env) => client_decompress_zhhdg_main(env)?,
        };
        exit::exit(None, None, None, exit_status)
    }));
    // Out of the `try`.
    set_interrupt_catch(None);
    match result {
        Ok(Ok(())) => unreachable!("Exit.exit returns"),
        Ok(Err(exn)) => handle_exn_without_config(name, exn),
        Err(payload) => handle_exn_without_config(name, Exn::of_panic(payload)),
    }
}

pub fn exec_command_with_config(command: HeavyCommand, init_proc_stack: Vec<String>) -> ! {
    let init_id = random_id::short_string();
    let command_name = client_command::name_camel_case_heavy(&command);

    // The global variable Relative_path.root must be initialized for a wide variety of things
    let root = client_args::root(&command);
    set_up_root(&root);
    let from = client_args::from(&command);

    set_up_logger(command_name, &init_id, &root);
    hh_logger::log(&format!("[hh_client] {}", ocaml_sys::argv().join(" ")));

    let cli_config_overrides = client_args::config(&command).unwrap_or_default();
    server_config::warn_on_invalid_config_keys(&cli_config_overrides);

    let qe_fetches: RefCell<Vec<server_local_config_qe::Fetch>> = RefCell::new(vec![]);
    let apply_qe_overrides = |silent: bool, config: &config_file::T| -> config_file::T {
        let (config, fetches) = server_local_config_qe::apply_qe_overrides(silent, config.clone());
        *qe_fetches.borrow_mut() = fetches;
        config
    };
    // (Outside the `try`: what it raises goes to the toplevel.)
    let (config, local_config) = match load_with_dynamic_overrides(
        &apply_qe_overrides,
        !client_args::dump_config(&command),
        &from,
        &cli_config_overrides,
    ) {
        Ok(configs) => configs,
        Err(e) => uncaught_exception(exception::wrap(e)),
    };
    init_event_logger(&root, &command, &init_id, &from, &config, &local_config);
    for fetch in qe_fetches.borrow().iter() {
        log_qe_fetch(fetch);
    }

    let init_proc_stack = if from.is_empty() || local_config.log_init_proc_stack_also_on_absent_from
    {
        Some(init_proc_stack)
    } else {
        None
    };
    set_interrupt_catch(Some(Arc::new(move || {
        handle_exn_and_exit(interrupted(), command_name)
    })));
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| -> Result<(), Exn> {
        let exit_status = match command {
            HeavyCommand::CCheck(check_env) => {
                client_check_main(check_env, &config, &local_config, init_proc_stack)?
                // never returns; does [Exit.exit] itself
            }
            HeavyCommand::CStart(env) => client_start_main(env)?,
            HeavyCommand::CStop(env) => client_stop_main(env)?,
            HeavyCommand::CRestart(env) => client_restart_main(env)?,
            HeavyCommand::CLsp(args) => {
                client_lsp_main(args, &init_id, &config, &local_config, init_proc_stack)?
            }
            HeavyCommand::CRage(env) => client_rage::main(&env, &local_config),
            HeavyCommand::CSavedStateProjectMetadata(env) => {
                client_saved_state_project_metadata_main(env, &local_config)?
            }
            HeavyCommand::CDownloadSavedState(env) => {
                client_download_saved_state_main(env, &local_config)?
            }
        };
        exit::exit(None, None, None, exit_status)
    }));
    // Out of the `try`.
    set_interrupt_catch(None);
    match result {
        Ok(Ok(())) => unreachable!("Exit.exit returns"),
        Ok(Err(exn)) => handle_exn_and_exit(exn, command_name),
        Err(payload) => handle_exn_and_exit(Exn::of_panic(payload), command_name),
    }
}

// ~~ The calls into modules that are not ported yet ~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Server_config.load_with_dynamic_overrides ~apply_dynamic_overrides
/// ~silent ~from ~cli_config_overrides`
fn load_with_dynamic_overrides(
    apply_dynamic_overrides: &dyn Fn(bool, &config_file::T) -> config_file::T,
    silent: bool,
    from: &str,
    cli_config_overrides: &[(String, String)],
) -> Result<(server_config::T, server_local_config::T), server_config::ServerConfigError> {
    server_config::load_with_dynamic_overrides(
        apply_dynamic_overrides,
        silent,
        from,
        cli_config_overrides,
    )
}

/// `Client_check.main check_env config local_config ~init_proc_stack`
fn client_check_main(
    check_env: client_env::ClientCheckEnv,
    config: &server_config::T,
    local_config: &server_local_config::T,
    init_proc_stack: Option<Vec<String>>,
) -> Result<exit_status::T, Exn> {
    crate::client_check::main(check_env, config, local_config, init_proc_stack)
}

/// `Lwt_utils.run_main (fun () -> Client_start.main env)`
fn client_start_main(env: client_start::Env) -> Result<exit_status::T, Exn> {
    Ok(client_start::main(&env)?)
}

/// `Lwt_utils.run_main (fun () -> Client_stop.main env)`
fn client_stop_main(env: client_stop::Env) -> Result<exit_status::T, Exn> {
    Ok(client_stop::main(&env)?)
}

/// `Lwt_utils.run_main (fun () -> Client_restart.main env)`
fn client_restart_main(env: client_start::Env) -> Result<exit_status::T, Exn> {
    Ok(crate::client_restart::main(&env)?)
}

/// `Lwt_utils.run_main (fun () -> Client_lsp.main args ~init_id ~config
/// ~local_config ~init_proc_stack)`
fn client_lsp_main(
    _args: client_lsp::Args,
    _init_id: &str,
    _config: &server_config::T,
    _local_config: &server_local_config::T,
    _init_proc_stack: Option<Vec<String>>,
) -> Result<exit_status::T, Exn> {
    not_ported("lsp")
}

/// `Lwt_utils.run_main (fun () -> Client_saved_state_project_metadata.main
/// env local_config)`
fn client_saved_state_project_metadata_main(
    _env: client_env::ClientCheckEnv,
    _local_config: &server_local_config::T,
) -> Result<exit_status::T, Exn> {
    not_ported("saved-state-project-metadata")
}

/// `Lwt_utils.run_main (fun () -> Client_download_saved_state.main env
/// local_config)`
fn client_download_saved_state_main(
    _env: client_download_saved_state::Env,
    _local_config: &server_local_config::T,
) -> Result<exit_status::T, Exn> {
    not_ported("download-saved-state")
}

/// `Client_decompress_zhhdg.main env`
fn client_decompress_zhhdg_main(_env: client_decompress_zhhdg::Env) -> Result<exit_status::T, Exn> {
    not_ported("decompress-zhhdg")
}

/// The temporary stand-in of plan §3.4 for a command that is not ported
/// yet: a message on stderr, then exit 10 (`Input_error`).
fn not_ported(command: &str) -> Result<exit_status::T, Exn> {
    eprintln!("hh_client: {} is not ported to Rust yet", command);
    Ok(exit_status::T::InputError)
}

// ~~ main ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn main() -> ! {
    server_local_config_qe::prepare_client_startup();
    // no-op, needed at entry-point for Daemon hookup: `Daemon.check_entry_point ()`
    // This invokes fbinit logic, which subsumes Folly.ensure_folly_init ():
    // `Startup_initializer.init ()`
    set_up_signals();
    let init_proc_stack = proc::get_proc_stack(None, None, ocaml_unix::getpid());
    let from_default = if proc::is_likely_from_interactive_shell(&init_proc_stack) {
        "[sh]"
    } else {
        ""
    };
    let command = match client_args::parse_args(from_default) {
        Ok(command) => command,
        Err(ExitWith(exit_status)) => exit::exit(None, None, None, exit_status),
    };
    match command {
        Command::WithoutConfig(command) => exec_command_without_config(command),
        Command::WithConfig(command) => exec_command_with_config(command, init_proc_stack),
    }
}

/// `let () = try main () with ...`, the toplevel of `hh_client.ml` (and its
/// `let () = Random.self_init ()`, which `Random_id` does not need here).
///
/// Its `Exit_status.Exit_with exit_status -> Exit.exit exit_status` arm has
/// nothing to catch here: `main` handles the one of `Client_args.parse_args`
/// itself, and the handlers of the `exec_command_*` catch everything. What
/// is left is a panic (an uncaught exception).
pub fn toplevel() -> ! {
    let result = std::panic::catch_unwind(|| {
        main();
    });
    match result {
        Ok(()) => unreachable!("main returns"),
        Err(exn) => uncaught_exception(exception::wrap(exn)),
    }
}

/// The `| exn -> ...` arm of the toplevel, for an exception that reaches it
/// (a panic, or an error value that nothing in between handles).
fn uncaught_exception(e: exception::T) -> ! {
    let exit_status = exit_status::T::UncaughtException(e);
    eprintln!("{}", exit_status::show_expanded(&exit_status));
    let _ = std::io::stderr().flush();
    exit::exit(None, None, None, exit_status)
}
