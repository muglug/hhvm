// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_check_status.ml`. See `hh/PORTING.md`.
//!
//! - `Printf.printf` is `print!` on stdout (the same buffer as
//!   `std::io::stdout()`, which `Server_error.print_error_list` is given);
//!   `%!` flushes it. A failed write panics, as OCaml raises `Sys_error`,
//!   except in the printing of [`go_streaming_on_fd`], which OCaml catches:
//!   there a broken pipe is `Exit_with Client_broken_pipe`.
//! - `Lwt`: [`go_streaming_on_fd`]'s `Lwt.pick` of `consume` and
//!   `show_progress` is one loop that waits for the next item of the errors
//!   stream (a channel, `crate::server_progress_lwt`) until the next
//!   second, when it shows the progress. `Lwt_unix.sleep` is a sleep.
//! - The exceptions that OCaml raises to the caller (`Exit_status.Exit_with`,
//!   and those of `connect_then_close`) are the `Err` of an
//!   [`hh_client::Exn`].
//! - `Hack_event_logger` calls are no-ops in the OSS build and are not made.
//! - `Lwt_utils.exec_checked` (for the watchman queries) is [`exec_checked`],
//!   private here; the signal numbers it logs are the system's, not OCaml's.
//! - `Edenfs_watcher.Standalone.get_changes_since` is the OSS stub
//!   (`failwith "not implemented"`): a panic.

use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::sync::Arc;
use std::sync::Mutex;

use crate::agent_diagnostic_formatter;
use crate::client_connect::ProgressCallback;
use crate::client_env;
use crate::contextual_diagnostic_formatter;
use crate::diagnostics;
use crate::diagnostics::Format;
use crate::exit_status;
use crate::extended_diagnostic_formatter;
use crate::filter_diagnostics;
use crate::find_utils;
use crate::format;
use crate::format::Formatter;
use crate::hh_client::Exn;
use crate::hh_json_helpers;
use crate::hh_logger;
use crate::highlighted_diagnostic_formatter;
use crate::path;
use crate::plain_highlighted_diagnostic_formatter;
use crate::raw_diagnostic_formatter;
use crate::relative_path;
use crate::rt::ocaml_unix;
use crate::server_command_types::StatusLiveness;
use crate::server_command_types::server_status;
use crate::server_error;
use crate::server_files;
use crate::server_local_config;
use crate::server_notifier;
use crate::server_notifier_types;
use crate::server_notifier_types::Clock;
use crate::server_progress;
use crate::server_progress::CompletionReason;
use crate::server_progress::ErrorsFileItem;
use crate::diagnostics::FinalizedDiagnostic;
use crate::server_progress::errors_read;
use crate::server_progress::errors_read::ReadResult;
use crate::server_progress_lwt;
use crate::server_progress_lwt::WatchError;
use crate::telemetry;
use crate::tty;
use crate::user_diagnostic;
use crate::user_diagnostic::Severity;
use crate::utils;
use crate::yojson::safe as yojson;

/// `Printf.printf "%s" s` (no flush).
fn printf(s: &str) {
    print!("{}", s)
}

/// `%!`: flush stdout.
fn flush_stdout() {
    if let Err(e) = std::io::stdout().flush() {
        panic!("Sys_error: {}", e)
    }
}

fn print_diagnostic_raw(e: &FinalizedDiagnostic) {
    printf(&raw_diagnostic_formatter::to_string(e))
}

fn print_diagnostic_agent(e: &FinalizedDiagnostic) {
    printf(&agent_diagnostic_formatter::to_string(e))
}

fn print_diagnostic_plain(e: &FinalizedDiagnostic) {
    printf(&user_diagnostic::to_string(e))
}

fn print_diagnostic_contextual(e: &FinalizedDiagnostic) {
    printf(&contextual_diagnostic_formatter::to_string(None, e))
}

fn print_diagnostic_highlighted(e: &FinalizedDiagnostic) {
    printf(&highlighted_diagnostic_formatter::to_string(e))
}

fn print_diagnostic_extended(e: &FinalizedDiagnostic) {
    printf(&extended_diagnostic_formatter::to_string(e))
}

fn print_diagnostic_plain_highlighted(e: &FinalizedDiagnostic) {
    printf(&plain_highlighted_diagnostic_formatter::to_string(e))
}

/// The text [`print_diagnostic`] prints.
fn diagnostic_string(error_format: Format, e: &FinalizedDiagnostic) -> String {
    match error_format {
        Format::Raw => raw_diagnostic_formatter::to_string(e),
        Format::Agent => agent_diagnostic_formatter::to_string(e),
        Format::Plain => user_diagnostic::to_string(e),
        Format::Context => contextual_diagnostic_formatter::to_string(None, e),
        Format::Highlighted => highlighted_diagnostic_formatter::to_string(e),
        Format::Extended => extended_diagnostic_formatter::to_string(e),
        Format::PlainHighlighted => plain_highlighted_diagnostic_formatter::to_string(e),
    }
}

pub fn print_diagnostic(error_format: Format, e: &FinalizedDiagnostic) {
    crate::server_local_config_qe::log_agent_error_format_exposure();
    match error_format {
        Format::Raw => print_diagnostic_raw(e),
        Format::Agent => print_diagnostic_agent(e),
        Format::Plain => print_diagnostic_plain(e),
        Format::Context => print_diagnostic_contextual(e),
        Format::Highlighted => print_diagnostic_highlighted(e),
        Format::Extended => print_diagnostic_extended(e),
        Format::PlainHighlighted => print_diagnostic_plain_highlighted(e),
    }
}

pub fn is_stale_msg(liveness: StatusLiveness) -> Option<String> {
    match liveness {
        StatusLiveness::StaleStatus => Some(
            "(but this may be stale, probably due to".to_string()
                + " file watcher being unresponsive)\n",
        ),
        StatusLiveness::LiveStatus => None,
    }
}

/// `go status error_format ~is_interactive ~output_json ~output_jsonl
/// ~max_errors`
pub fn go(
    status: server_status::T,
    error_format: Option<Format>,
    is_interactive: bool,
    output_json: bool,
    output_jsonl: bool,
    max_errors: Option<isize>,
) -> exit_status::T {
    let server_status::T {
        liveness,
        error_list,
        dropped_count,
        last_recheck_stats,
        file_watcher_clock: _,
    } = status;
    if !output_json && !output_jsonl && !error_list.is_empty() {
        crate::server_local_config_qe::log_agent_error_format_exposure();
    }
    let stale_msg = is_stale_msg(liveness);
    if output_jsonl {
        let error_format = diagnostics::format_or_default(error_format);
        for e in &error_list {
            crate::client_jsonl_printer::print_diagnostic(error_format, e);
        }
        let (error_count, warning_count) = diagnostics::count_errors_and_warnings(&error_list);
        let passed = error_count == 0;
        crate::client_jsonl_printer::print_summary(passed, error_count, warning_count);
        if passed {
            exit_status::T::NoError
        } else {
            exit_status::T::TypeError
        }
    } else {
        let error_count = if output_json
            || (error_format.is_none() && !is_interactive)
            || error_list.is_empty()
        {
            server_error::print_error_list(
                &mut std::io::stdout(),
                stale_msg.as_deref(),
                output_json,
                error_format,
                &error_list,
                last_recheck_stats.as_ref(),
            );
            0
        } else {
            let error_format = diagnostics::format_or_default(error_format);
            for e in &error_list {
                print_diagnostic(error_format, e);
            }
            let (error_count, warning_count) =
                diagnostics::count_errors_and_warnings(&error_list);
            if let Some(msg) = diagnostics::format_summary(
                error_format,
                error_count,
                warning_count,
                Some(dropped_count),
                max_errors,
            ) {
                printf(&msg)
            }
            // [stale_msg] ultimately comes from [Server_main.query_notifier], and says whether the check
            // reflects data from a sync file watcher query, or just whatever has arrived asynchronously
            // so far.
            if let Some(msg) = &stale_msg {
                printf(msg)
            }
            error_count
        };
        if error_count == 0 {
            exit_status::T::NoError
        } else {
            exit_status::T::TypeError
        }
    }
}

/// `end_sentinel` (`[@@deriving show]`)
pub enum EndSentinel {
    Completed(CompletionReason),
    WatchError(WatchError),
}

/// `pp_end_sentinel`
pub fn pp_end_sentinel(fmt: &mut Formatter, e: &EndSentinel) {
    // A constructor with an argument: "(@[<2>%s@ " ctor, the argument, "@])"
    let with_arg = |fmt: &mut Formatter, ctor: &str, arg: &dyn Fn(&mut Formatter)| {
        format::pp_print_string(fmt, "(");
        format::pp_open_box(fmt, 2);
        format::pp_print_string(fmt, ctor);
        format::pp_print_space(fmt);
        arg(fmt);
        format::pp_close_box(fmt);
        format::pp_print_string(fmt, ")");
    };
    match e {
        EndSentinel::Completed(c) => with_arg(fmt, "Client_check_status.Completed", &|fmt| {
            server_progress::pp_completion_reason(fmt, c)
        }),
        EndSentinel::WatchError(w) => with_arg(fmt, "Client_check_status.Watch_error", &|fmt| {
            server_progress_lwt::pp_watch_error(fmt, w)
        }),
    }
}

pub fn show_end_sentinel(e: &EndSentinel) -> String {
    format::asprintf(|fmt| pp_end_sentinel(fmt, e))
}

pub fn end_sentinel_short_string(e: &EndSentinel) -> String {
    match e {
        EndSentinel::WatchError(_) => "Killed".to_string(),
        EndSentinel::Completed(c) => server_progress::show_completion_reason(c),
    }
}

pub mod diagnostics_info {
    use super::*;

    #[derive(Clone, Copy, Debug, Default)]
    pub struct T {
        pub diagnostics_count: (isize, isize),
    }

    pub fn empty() -> T {
        T {
            diagnostics_count: (0, 0),
        }
    }

    fn add_tuples((i, j): (isize, isize), (k, l): (isize, isize)) -> (isize, isize) {
        (i + k, j + l)
    }

    pub fn accumulate(
        T { diagnostics_count }: T,
        diagnostics: &relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>>,
    ) -> T {
        let mut diagnostic_counts = diagnostics_count;
        for diagnostics in diagnostics.values() {
            let list: Vec<FinalizedDiagnostic> = diagnostics.iter().map(|(d, _)| d.clone()).collect();
            diagnostic_counts = add_tuples(
                diagnostics::count_errors_and_warnings(&list),
                diagnostic_counts,
            );
        }
        T {
            diagnostics_count: diagnostic_counts,
        }
    }

    pub fn total_count(T { diagnostics_count: (e, w) }: &T) -> isize {
        e + w
    }
}

pub mod diagnostic_printer {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub struct T {
        max_errors: isize,
        printed_count: isize,
        extra_error_count: isize,
        extra_warning_count: isize,
        /// Whether we've been printing the counts of extra
        /// diagnostics after hitting the --max-error limit.
        /// Used to skip printing the diagnostic summary
        /// (e.g. "1 error, 2 warnings") if true.
        has_already_printed_extra: bool,
    }

    pub fn init(max_errors: Option<isize>) -> T {
        T {
            max_errors: max_errors.unwrap_or(isize::MAX),
            printed_count: 0,
            extra_error_count: 0,
            extra_warning_count: 0,
            has_already_printed_extra: false,
        }
    }

    /// (`out` is where `print_diagnostic` prints: stdout, through the
    /// broken-pipe check of [`go_streaming_on_fd`].)
    pub(super) fn print_diagnostic_if_below_limit(
        state: T,
        diagnostic: &FinalizedDiagnostic,
        error_format: Format,
        out: &mut dyn FnMut(&str) -> Result<(), Exn>,
    ) -> Result<T, Exn> {
        if state.printed_count < state.max_errors {
            out(&diagnostic_string(error_format, diagnostic))?;
            Ok(T {
                printed_count: state.printed_count + 1,
                ..state
            })
        } else {
            match diagnostic.severity {
                Severity::Err => Ok(T {
                    extra_error_count: state.extra_error_count + 1,
                    ..state
                }),
                Severity::Warning { .. } => Ok(T {
                    extra_warning_count: state.extra_warning_count + 1,
                    ..state
                }),
            }
        }
    }

    pub(super) fn print_extra_diagnostics_if_any(
        state: T,
        out: &mut dyn FnMut(&str) -> Result<(), Exn>,
    ) -> Result<T, Exn> {
        let T {
            max_errors,
            extra_error_count,
            extra_warning_count,
            has_already_printed_extra,
            printed_count: _,
        } = state;
        if extra_error_count + extra_warning_count == 0 {
            Ok(state)
        } else {
            if has_already_printed_extra {
                // \x1b[1A  = move cursor up once.
                //            We do this because the last printed line is the status,
                //            which we don't want to touch
                // \r       = move cursor to beginning of line
                // \x1b[0K  = erase until end of line
                out("\x1b[1A\r\x1b[0K")?;
                out_flush(out)?;
            }
            let explanation = format!("(not showing all due to --max-errors {})\n", max_errors);
            match (extra_error_count, extra_warning_count) {
                (n, 0) => out(&format!("{} errors found {}", n, explanation))?,
                (0, m) => out(&format!("{} warnings found {}", m, explanation))?,
                (n, m) => out(&format!("{} errors, {} warnings found {}", n, m, explanation))?,
            }
            // \x1b[1B = move cursor down once, to go back to the last line
            out("\x1b[1B")?;
            out_flush(out)?;
            Ok(T {
                has_already_printed_extra: true,
                ..state
            })
        }
    }

    /// `%!` through `out` (an empty string is a flush).
    fn out_flush(out: &mut dyn FnMut(&str) -> Result<(), Exn>) -> Result<(), Exn> {
        out("")
    }

    pub fn has_printed_counts(T {
        has_already_printed_extra,
        ..
    }: &T) -> bool {
        *has_already_printed_extra
    }
}

/// `Printf.printf` within the `try ... with Sys_error "Broken pipe"` of
/// `consume`: the text, then a flush when `s` is empty (`%!`). A broken pipe
/// is `Exit_with Client_broken_pipe`; another failure panics (`Sys_error`).
fn streaming_printf(s: &str) -> Result<(), Exn> {
    let mut out = std::io::stdout();
    let res = if s.is_empty() {
        out.flush()
    } else {
        out.write_all(s.as_bytes())
    };
    match res {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::BrokenPipe => {
            Err(Exn::ExitWith(exit_status::T::ClientBrokenPipe))
        }
        Err(e) => panic!("Sys_error: {}", e),
    }
}

/// `partial_telemetry_ref`, which the SIGINT handler reads.
pub type PartialTelemetryRef = Arc<Mutex<Option<telemetry::T>>>;

/// This function produces streaming diagnostics: it reads the errors.bin opened
/// as [fd], displays diagnostics as they come using the [args.error_format] over stdout, and
/// displays a progress-spinner over stderr if [args.show_spinner]. It keeps "tailing"
/// [fd] until eventually the producing process writes an end-sentinel in it (signalling
/// that the typecheck has been completed or restarted or aborted), or until the producing
/// process terminates.
pub fn go_streaming_on_fd(
    pid: isize,
    fd: std::fs::File,
    args: &client_env::ClientCheckEnv,
    error_filter: &filter_diagnostics::filter::T,
    partial_telemetry_ref: &PartialTelemetryRef,
    initial_telemetry: telemetry::T,
    progress_callback: &ProgressCallback,
) -> Result<(exit_status::T, telemetry::T), Exn> {
    let inode = crate::sys_utils::show_inode(&fd);
    let errors_stream = server_progress_lwt::watch_errors_file(pid, errors_reader(fd));
    go_streaming_on_fd_inner(
        &inode,
        errors_stream,
        args,
        error_filter,
        partial_telemetry_ref,
        initial_telemetry,
        progress_callback,
    )
}

/// The rest of [`go_streaming_on_fd`], once `errors_stream` watches the
/// file whose `Sys_utils.show_inode` is `inode`.
fn go_streaming_on_fd_inner(
    inode: &str,
    errors_stream: std::sync::mpsc::Receiver<Result<ReadResult, WatchError>>,
    args: &client_env::ClientCheckEnv,
    error_filter: &filter_diagnostics::filter::T,
    partial_telemetry_ref: &PartialTelemetryRef,
    initial_telemetry: telemetry::T,
    progress_callback: &ProgressCallback,
) -> Result<(exit_status::T, telemetry::T), Exn> {
    let client_env::ClientCheckEnv {
        max_errors,
        error_format,
        output_jsonl,
        ..
    } = args;
    let (max_errors, output_jsonl) = (*max_errors, *output_jsonl);
    let start_time = ocaml_unix::gettimeofday();
    let mut first_error_time: Option<f64> = None;
    let mut latest_progress: Option<String> = None;
    let mut errors_file_telemetry = telemetry::create();

    // This constructs a telemetry that we'll use for both partial-progress
    // and completed events.
    let telemetry_so_far = |errors_file_telemetry: &telemetry::T,
                            first_error_time: Option<f64>,
                            displayed_count: isize| {
        let t = telemetry::merge(initial_telemetry.clone(), errors_file_telemetry.clone());
        let t = telemetry::bool_("streaming", true, t);
        let t = telemetry::int_opt("max_errors", max_errors, t);
        let t = telemetry::float_opt(
            "first_error_time",
            first_error_time.map(|t| t - start_time),
            t,
        );
        telemetry::int_("displayed_count", displayed_count, t)
    };

    // If the user does Ctrl+C, it generates SIGINT and we can't run any code in response.
    // But we'd still like to report telemetry in that case. So we pre-emptively store
    // telemetry in [partial_telemetry_ref] which the SIGINT handler will be able to read:
    // if it finds [Some], then the SIGINT handler will deem the operation a success
    // and will log CLIENT_CHECK_PARTIAL instead of CLIENT_CHECK_BAD_EXIT.
    let update_partial_telemetry = |errors_file_telemetry: &telemetry::T,
                                    first_error_time: Option<f64>,
                                    displayed_count: isize| {
        if displayed_count > 0 {
            *partial_telemetry_ref
                .lock()
                .unwrap_or_else(|e| e.into_inner()) = Some(telemetry_so_far(
                errors_file_telemetry,
                first_error_time,
                displayed_count,
            ));
        }
    };

    // this lwt process reads the progress.json file once a second and displays a spinner;
    // it never terminates
    let show_progress = |latest_progress: &mut Option<String>| {
        let message = server_progress::read().message;
        *latest_progress = Some(message);
        progress_callback(latest_progress.clone());
    };

    let error_format = diagnostics::format_or_default(*error_format);
    // this lwt process consumes diagnostics from the errors.bin file by polling
    // every 0.2s, and displays them. It terminates once the errors.bin file has an "end"
    // sentinel written to it, or the process that was writing errors.bin terminates.
    let mut diagnostics_info = diagnostics_info::empty();
    let mut printer = diagnostic_printer::init(max_errors);
    // The first `show_progress` runs once `consume` waits for the stream;
    // then once a second.
    let mut next_progress: Option<std::time::Instant> = None;
    let end_sentinel = loop {
        let item = match next_progress {
            None => match errors_stream.try_recv() {
                Ok(item) => Some(item),
                Err(std::sync::mpsc::TryRecvError::Empty) => {
                    show_progress(&mut latest_progress);
                    next_progress =
                        Some(std::time::Instant::now() + std::time::Duration::from_secs(1));
                    continue;
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => None,
            },
            Some(next) => {
                let timeout = next.saturating_duration_since(std::time::Instant::now());
                match errors_stream.recv_timeout(timeout) {
                    Ok(item) => Some(item),
                    Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                        show_progress(&mut latest_progress);
                        next_progress = Some(next + std::time::Duration::from_secs(1));
                        continue;
                    }
                    Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => None,
                }
            }
        };
        match item {
            None => {
                // The contract of [errors_stream] (from [Server_progress_lwt.watch_errors_file]) is
                // that it will always have a single [Some error] item as its last item, before the
                // stream is closed and hence subsequent [Lwt_stream.get] return [None].
                // If we're here, it means that contract has been violated.
                panic!("Expected end_sentinel before end of stream")
            }
            Some(Err(error)) => break EndSentinel::WatchError(error),
            Some(Ok(ReadResult::RCompleted(x, _))) => break EndSentinel::Completed(x),
            Some(Ok(ReadResult::RItem(item))) => match item {
                ErrorsFileItem::Telemetry(telemetry_item) => {
                    errors_file_telemetry =
                        telemetry::merge(errors_file_telemetry, telemetry_item);
                    update_partial_telemetry(
                        &errors_file_telemetry,
                        first_error_time,
                        diagnostics_info::total_count(&diagnostics_info),
                    );
                }
                ErrorsFileItem::Errors {
                    errors,
                    timestamp: _,
                } => {
                    first_error_time = first_error_time.or(Some(ocaml_unix::gettimeofday()));
                    // We'll clear the spinner, print diagnostics to stdout, flush stdout, and restore the spinner
                    progress_callback(None);
                    let diagnostics: relative_path::map::T<Vec<(FinalizedDiagnostic, isize)>> =
                        errors
                            .into_iter()
                            .map(|(path, errors)| {
                                (path, filter_diagnostics::filter_with_hash(error_filter, errors))
                            })
                            .collect();
                    diagnostics_info = diagnostics_info::accumulate(diagnostics_info, &diagnostics);
                    printer = if output_jsonl {
                        for diagnostics_in_file in diagnostics.values() {
                            for (diag, _) in diagnostics_in_file {
                                streaming_printf(&format!(
                                    "{}\n",
                                    crate::client_jsonl_printer::diagnostic_line(
                                        error_format,
                                        diag
                                    )
                                ))?;
                                streaming_printf("")?;
                            }
                        }
                        streaming_printf("")?;
                        printer
                    } else {
                        let mut out = |s: &str| streaming_printf(s);
                        let mut printer = printer;
                        for diagnostics_in_file in diagnostics.values() {
                            for (diag, _) in diagnostics_in_file {
                                printer = diagnostic_printer::print_diagnostic_if_below_limit(
                                    printer,
                                    diag,
                                    error_format,
                                    &mut out,
                                )?;
                            }
                        }
                        let printer =
                            diagnostic_printer::print_extra_diagnostics_if_any(printer, &mut out)?;
                        streaming_printf("")?;
                        printer
                    };
                    progress_callback(latest_progress.clone());
                    update_partial_telemetry(
                        &errors_file_telemetry,
                        first_error_time,
                        diagnostics_info::total_count(&diagnostics_info),
                    );
                }
            },
        }
    };
    let diagnostics_info::T {
        diagnostics_count: (error_count, warning_count),
    } = diagnostics_info;
    // Clear the spinner
    progress_callback(None);

    match end_sentinel {
        EndSentinel::Completed(CompletionReason::Complete(telemetry)) => {
            // complete either because the server completed, or we truncated early
            if output_jsonl {
                let passed = error_count == 0;
                crate::client_jsonl_printer::print_summary(passed, error_count, warning_count)
            } else if !diagnostic_printer::has_printed_counts(&printer) {
                if let Some(msg) = diagnostics::format_summary(
                    error_format,
                    error_count,
                    warning_count,
                    None,
                    max_errors,
                ) {
                    printf(&msg)
                }
            }
            let telemetry = telemetry::merge(
                telemetry_so_far(
                    &errors_file_telemetry,
                    first_error_time,
                    error_count + warning_count,
                ),
                telemetry,
            );
            if error_count == 0 {
                Ok((exit_status::T::NoError, telemetry))
            } else {
                Ok((exit_status::T::TypeError, telemetry))
            }
        }
        EndSentinel::Completed(CompletionReason::Restarted {
            user_message,
            log_message,
        }) => {
            hh_logger::log(&format!(
                "Errors-file: on {}, read Restarted({},{})",
                inode, user_message, log_message
            ));
            if output_jsonl {
                crate::client_jsonl_printer::print_restarted(&user_message)
            } else {
                // All errors, warnings, informationals go to stdout.
                let msg = tty::apply_color(
                    None,
                    tty::Style::Bold(tty::RawColor::Red),
                    &(user_message + "\nPlease re-run hh."),
                );
                printf(&format!("\n{}\n", msg));
                flush_stdout();
            }
            Err(Exn::ExitWith(exit_status::T::TypecheckRestarted))
        }
        end_sentinel @ (EndSentinel::Completed(CompletionReason::Stopped)
        | EndSentinel::WatchError(_)) => {
            hh_logger::log(&format!(
                "Errors-file: on {}, read {}",
                inode,
                show_end_sentinel(&end_sentinel)
            ));
            let short = end_sentinel_short_string(&end_sentinel);
            if output_jsonl {
                crate::client_jsonl_printer::print_stopped(&format!(
                    "hh_server has terminated. [{}]",
                    short
                ))
            } else {
                printf(&format!("hh_server has terminated. [{}]\n", short));
                flush_stdout();
            }
            Err(Exn::ExitWith(exit_status::T::TypecheckAbandoned))
        }
    }
}

// ~~ The errors file (`Server_progress.ErrorsRead`) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Server_progress.ErrorsRead.openfile fd`
fn errors_read_openfile(
    fd: &mut std::fs::File,
) -> Result<errors_read::OpenSuccess, (errors_read::OpenError, errors_read::LogMessage)> {
    errors_read::openfile(fd)
}

/// The descriptor `fd`, after [`errors_read_openfile`], as what
/// `Server_progress_lwt.watch_errors_file` reads with
/// `Server_progress.ErrorsRead.read_next_errors`.
fn errors_reader(fd: std::fs::File) -> Box<dyn server_progress_lwt::ErrorsReader> {
    Box::new(fd)
}

// ~~ File watchers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Lwt_utils.Process_success.t` (its `stdout`) or
/// `Lwt_utils.Process_failure.t` (its `to_string`).
struct ProcessFailure {
    command_line: String,
    /// `Unix.WEXITED n` (`Ok n`) or `Unix.WSIGNALED n` (`Err n`).
    process_status: Result<i32, i32>,
    stdout: String,
    stderr: String,
    exn: Option<String>,
    start_time: f64,
    end_time: f64,
}

/// `Lwt_utils.Process_failure.to_string`
fn process_failure_to_string(process_failure: &ProcessFailure) -> String {
    let exn_message = match &process_failure.exn {
        Some(exn) => exn.clone(),
        None => "<none>".to_string(),
    };
    let exit_code = match process_failure.process_status {
        Ok(exit_code) => format!(
            "WEXITED {} ({})",
            exit_code,
            exit_status::exit_code_to_string(exit_code as isize)
        ),
        Err(signal) => format!(
            "WSIGNALLED {} ({}){}",
            signal,
            string_of_signal(signal),
            if signal == libc::SIGKILL {
                " - this often indicates a timeout"
            } else {
                ""
            }
        ),
    };
    let stderr = match process_failure.stderr.as_str() {
        "" => "<none>",
        stderr => stderr,
    };
    format!(
        "Process '{}' failed with\nExit code: {}\n{} -- {}\nException: {}\nStderr: {}\nStdout: {}",
        process_failure.command_line,
        exit_code,
        utils::timestring(process_failure.start_time),
        utils::timestring(process_failure.end_time),
        exn_message,
        stderr,
        process_failure.stdout
    )
}

/// `Print_signal.string_of_signal`, on the system's signal numbers.
fn string_of_signal(n: i32) -> String {
    match n {
        libc::SIGABRT => "sigabrt",
        libc::SIGALRM => "sigalrm",
        libc::SIGFPE => "sigfpe",
        libc::SIGHUP => "sighup",
        libc::SIGILL => "sigill",
        libc::SIGINT => "sigint",
        libc::SIGKILL => "sigkill",
        libc::SIGPIPE => "sigpipe",
        libc::SIGQUIT => "sigquit",
        libc::SIGSEGV => "sigsegv",
        libc::SIGTERM => "sigterm",
        libc::SIGUSR1 => "sigusr1",
        libc::SIGUSR2 => "sigusr2",
        libc::SIGCHLD => "sigchld",
        libc::SIGCONT => "sigcont",
        libc::SIGSTOP => "sigstop",
        libc::SIGTSTP => "sigtstp",
        libc::SIGTTIN => "sigttin",
        libc::SIGTTOU => "sigttou",
        libc::SIGVTALRM => "sigvtalrm",
        libc::SIGPROF => "sigprof",
        libc::SIGBUS => "sigbus",
        libc::SIGSYS => "sigsys",
        libc::SIGTRAP => "sigtrap",
        libc::SIGURG => "sigurg",
        libc::SIGXCPU => "sigxcpu",
        libc::SIGXFSZ => "sigxfsz",
        _ => return format!("unknown signal {}", n),
    }
    .to_string()
}

/// `Lwt_utils.exec_checked ?input Exec_command.Watchman args`: the stdout of
/// a successful run (exit 0).
fn exec_checked(input: Option<&str>, args: &[String]) -> Result<String, ProcessFailure> {
    use std::process::Stdio;
    let program = "watchman";
    let start_time = ocaml_unix::gettimeofday();
    let command_line = std::iter::once(program.to_string())
        .chain(args.iter().cloned())
        .collect::<Vec<_>>()
        .join(" ");
    let child = std::process::Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();
    let mut child = match child {
        Ok(child) => child,
        // (`Lwt_process` forks first: the child that cannot exec exits 127.)
        Err(_) => {
            return Err(ProcessFailure {
                command_line,
                process_status: Ok(127),
                stdout: String::new(),
                stderr: String::new(),
                exn: None,
                start_time,
                end_time: ocaml_unix::gettimeofday(),
            });
        }
    };
    let mut exn = None;
    {
        let stdin = child.stdin.take();
        if let (Some(input), Some(mut stdin)) = (input, stdin) {
            if let Err(e) = stdin.write_all(input.as_bytes()) {
                exn = Some(format!("Unix.Unix_error(Unix.{:?}, \"write\", \"\")", e.kind()));
            }
        }
    }
    let output = child.wait_with_output();
    let end_time = ocaml_unix::gettimeofday();
    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
            let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            use std::os::unix::process::ExitStatusExt;
            match (output.status.code(), output.status.signal()) {
                (Some(0), _) => Ok(stdout),
                (code, signal) => Err(ProcessFailure {
                    command_line,
                    process_status: match (code, signal) {
                        (Some(code), _) => Ok(code),
                        (None, Some(signal)) => Err(signal),
                        (None, None) => Ok(-1),
                    },
                    stdout,
                    stderr,
                    exn,
                    start_time,
                    end_time,
                }),
            }
        }
        Err(e) => Err(ProcessFailure {
            command_line,
            process_status: Ok(-1),
            stdout: String::new(),
            stderr: String::new(),
            exn: Some(format!("Unix.Unix_error(Unix.{:?}, \"waitpid\", \"\")", e.kind())),
            start_time,
            end_time,
        }),
    }
}

/// `Watchman_lwt.watch_project ~root ~sockname`: `(watch, relative_path)`
/// of `Watchman_sig.Types.watch_project_response`, or the
/// `Watchman_lwt.error_to_string` of the failure.
fn watchman_watch_project(
    root: &path::T,
    sockname: Option<&str>,
) -> Result<(String, Option<String>), String> {
    let mut args = vec!["watch-project".to_string(), path::to_string(root)];
    if let Some(sockname) = sockname {
        args.push("--sockname".to_string());
        args.push(sockname.to_string());
    }
    let stdout = exec_checked(None, &args).map_err(|e| {
        format!(
            "Error while running `watchman` command: {}",
            process_failure_to_string(&e)
        )
    })?;
    let unexpected = || format!("Error while parsing watchman response: {}", stdout);
    // `watch_project_response_of_yojson @@ Yojson.Safe.from_string stdout`
    // (a JSON syntax error is an exception that nothing here catches).
    let json = match yojson::from_string(&stdout) {
        Ok(json) => json,
        Err(e) => panic!("Yojson.Json_error({:?})", e.0),
    };
    let field = |name: &str| match &json {
        yojson::T::Assoc(fields) => fields
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v.clone()),
        _ => None,
    };
    let watch = match field("watch") {
        Some(yojson::T::String(watch)) => watch,
        _ => return Err(unexpected()),
    };
    let relative_path = match field("relative_path") {
        None => None,
        Some(yojson::T::String(p)) => Some(p),
        Some(_) => return Err(unexpected()),
    };
    Ok((watch, relative_path))
}

/// Gets all files-changed since [clock] which match the standard hack
/// predicate [FilesToIgnore.watchman_server_expression_terms].
/// The returns are relative to the watchman root.
/// CARE! This is not the same as a Relative_path.t. For instance if root
/// contains a symlink root/a.php ~> /tmp/b.php and the symlink itself
/// changed, then watchman would report a change on "a.php" but Relative_path.t
/// by definition only refers to paths after symlinks have been resolved
/// which in this case would be (Relative_path.Tmp,"b.php").
///
/// The caller must explicitly pass in [~fail_on_new_instance:false]
/// and [~fail_during_state:false] so that the callsite is self-documenting
/// about what it will do during these two scenarios. (no other options
/// are currently supported.)
fn watchman_get_raw_updates_since(
    root: &path::T,
    clock: &str,
    watchman_sockname: Option<&str>,
    fail_on_new_instance: bool,
    fail_during_state: bool,
) -> Result<Vec<String>, String> {
    if fail_on_new_instance {
        panic!("Not yet implemented: fail_on_new_instance");
    }
    if fail_during_state {
        panic!("Not yet implemented: fail_during_state");
    }
    let (watch, relative_path) = watchman_watch_project(root, watchman_sockname)?;
    let mut fields = vec![];
    if let Some(p) = relative_path {
        fields.push(("relative_path".to_string(), yojson::T::String(p)));
    }
    fields.push(("since".to_string(), yojson::T::String(clock.to_string())));
    fields.push((
        "fields".to_string(),
        yojson::T::List(vec![yojson::T::String("name".to_string())]),
    ));
    fields.push((
        "expression".to_string(),
        hh_json_helpers::adhoc_json_helpers::pred(
            "allof",
            crate::files_to_ignore::watchman_server_expression_terms(),
        ),
    ));
    let query = yojson::T::List(vec![
        yojson::T::String("query".to_string()),
        yojson::T::String(watch),
        yojson::T::Assoc(fields),
    ]);
    // unsorted: watchman query, consumed by external tool
    let query = yojson::to_string(&query);
    let args: Vec<String> = match watchman_sockname {
        None => vec!["-j".to_string()],
        Some(sockname) => vec!["--sockname".to_string(), sockname.to_string(), "-j".to_string()],
    };
    hh_logger::log(&format!("watchman query: {}", query));
    let result = exec_checked(Some(&query), &args);
    match result {
        Err(e) => {
            let msg = process_failure_to_string(&e);
            hh_logger::log(&format!("watchman response: {}", msg));
            Err(msg)
        }
        Ok(stdout) => {
            let files = match yojson::from_string(&stdout) {
                Err(e) => Err(format!("Yojson.Json_error({:?})", e.0)),
                Ok(json) => {
                    match hh_json_helpers::jget::string_array_exn(Some(&json), "files") {
                        Ok(files) => Ok((json, files)),
                        Err(e) => Err(format!("{:?}", e)),
                    }
                }
            };
            match files {
                Err(e) => {
                    let msg = format!(
                        "ClientCheckStatus: watchman parse failure. Expected field `files`.\n{}\nRESPONSE:{}\n",
                        e, stdout
                    );
                    hh_logger::log(&msg);
                    // `Hack_event_logger.invariant_violation_bug msg`: a no-op
                    // in the OSS build.
                    Err(msg)
                }
                Ok((json, files)) => {
                    let mut has_changed = false;
                    // unsorted: parsed programmatically, not snapshot-tested
                    let json_str = yojson::to_string(&hh_json_helpers::json_truncate(
                        None,
                        None,
                        Some(10),
                        None,
                        None,
                        Some(&mut has_changed),
                        &json,
                    ));
                    let has_changed = if has_changed { " [truncated]" } else { "" };
                    hh_logger::log(&format!("watchman response:{} {}", has_changed, json_str));
                    Ok(files)
                }
            }
        }
    }
}

/// `edenfs_watcher_get_raw_updates_since ~root ~clock ~local_config`: the
/// OSS `Edenfs_watcher.Standalone.get_changes_since` is
/// `failwith "not implemented"`.
fn edenfs_watcher_get_raw_updates_since(
    _root: &path::T,
    _clock: &str,
    _local_config: &server_local_config::T,
) -> Result<(Vec<String>, Option<telemetry::T>), String> {
    panic!("not implemented")
}

/// Gets all files-changed since [clock] which match the standard hack
/// predicate [FilesToIgnore.server_watch_spec].
///
/// If the returned flag is true, then paths are relative to the watch root.
/// Otherwise, they are absolute.
///
/// Note that we pick the file watcher to query based on the clock type that
/// the server wrote to the errors file.
/// This way, we ensure to use the same file watcher as the server.
fn file_watcher_get_raw_updates_since(
    root: &path::T,
    clock: &Clock,
    local_config: &server_local_config::T,
) -> Result<(Vec<String>, Option<telemetry::T>, bool), String> {
    match clock {
        Clock::Watchman(clock) => {
            let watchman_sockname = local_config.watchman.sockname.as_deref();
            let changes =
                watchman_get_raw_updates_since(root, clock, watchman_sockname, false, false);
            changes.map(|changes| (changes, None, true))
        }
        Clock::Eden(clock) => {
            let changes_and_telemetry =
                edenfs_watcher_get_raw_updates_since(root, clock, local_config);
            changes_and_telemetry.map(|(changes, telemetry_opt)| (changes, telemetry_opt, false))
        }
    }
}

/// Identifier for a file, based on inode and ctime
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FileId {
    inode: u64,
    /// The ctime field, a.k.a. change time,
    /// meaning the time of the latest metadata change.
    /// This is the creation time if there has been
    /// no other metadata changes, which is likely the case here.
    ctime: f64,
}

impl FileId {
    fn of_fd(fd: &std::fs::File) -> FileId {
        match fd.metadata() {
            Ok(stats) => FileId {
                inode: stats.ino(),
                ctime: stats.ctime() as f64 + stats.ctime_nsec() as f64 / 1e9,
            },
            Err(e) => panic!("Unix.Unix_error(Unix.{:?}, \"fstat\", \"\")", e.kind()),
        }
    }
}

fn show_progress_and_sleep(progress_callback: &ProgressCallback) {
    // (`Server_progress.read` does not fail here: its failures read as a
    // stopped server.)
    let message = Some(server_progress::read().message);
    if let Some(msg) = message {
        progress_callback(Some(msg))
    }
    std::thread::sleep(std::time::Duration::from_secs(1))
}

/// [keep_trying_to_open] tries to open the errors.bin file.
/// There is a whole load of ceremony to do with what happens when you want to open errors.bin,
/// e.g. start the server if necessary, check for version mismatch, report failures to the user.
/// Concrete examples:
/// * There is no server running. "hh check" must start up a server, before it can stream errors from it.
/// * There is no server running, but our attempt to start the server failed, either
///   synchronously (e.g. we had `--autostart-server false`)
///   or asynchronously (e.g. saved-state failed to load).
///   "hh check" must detect that no streaming errors are forthcoming.
/// * There is a server running, and it has already written errors.bin, but it is the wrong binary version.
///   "hh check" must cause it to shut down, and a new server start up, before it can stream errors.
/// * There is an errors.bin from an existing server, and its typecheck started 20s ago, but moments
///   before "hh check" a file was changed on disk. "hh check" must detect this,
///   learn that it cannot use the existing errors.bin, and instead use the
///   new errors.bin that will be forthcoming.
///   We care about that case very much as we anticipate a common use case is to
///   save a file and immediately type hh afterwards. We wouldn't want that `hh`
///   call to return the old errors.
///
/// How this function fulfills those cases:
/// * It of course has to check whether files on disk have changed since this errors.bin was started.
///   It does this with a synchronous file watcher query,
///   and displays "hh_server is busy [file watcher sync]".
/// * If there is a fault like "errors.bin was started too long ago and files have changed
///   in the meantime" which can be rectified by waiting and trying again on the assumption
///   that a server is running and will pick up the changes, then this will wait and try
///   again indefinitely. It will display "hh_server is busy [hh_server sync]".
///   The parameter [already_checked_clock] indicates that we have already done a
///   (costly) file watcher query for this clock, and will not do another file watcher query until
///   we see a new errors.bin which started at a different (newer) clock.
/// * If there is a fault like "missing errors.bin" or "binary mismatch" which can
///   be rectified by connecting to the monitor+server, this will do so at most once
///   with the [connect_then_close] callback parameter, then resume looking for a
///   suitable errors.bin again with "hh_server is busy [hh_server sync]".
///   If it already tried once with no effect, then it will raise Exit_status.Exit_with.
///
/// (The OCaml comment goes on with a subtle example of the errors.bin
/// clock and the semantics of the deadline and of the spinner; see
/// `client_check_status.ml`.)
///
/// (OCaml's recursion is a loop.)
#[allow(clippy::too_many_arguments)]
pub fn keep_trying_to_open(
    local_config: &server_local_config::T,
    has_already_attempted_connect: bool,
    connect_then_close: &mut dyn FnMut() -> Result<(), Exn>,
    already_checked_file: Option<FileId>,
    progress_callback: &ProgressCallback,
    deadline: Option<f64>,
    opening_attempts: isize,
    telemetry: telemetry::T,
    root: &path::T,
) -> Result<(isize, std::fs::File, telemetry::T), Exn> {
    let mut has_already_attempted_connect = has_already_attempted_connect;
    let mut already_checked_file = already_checked_file;
    let mut opening_attempts = opening_attempts;
    let mut telemetry = telemetry;
    loop {
        if let Some(deadline) = deadline {
            if ocaml_unix::gettimeofday() > deadline {
                progress_callback(None);
                return Err(Exn::ExitWith(exit_status::T::OutOfTime));
            }
        }
        let fd_opt = {
            use std::os::unix::fs::OpenOptionsExt;
            std::fs::OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NONBLOCK)
                .open(server_files::errors_file_path(root))
                .ok()
        };
        match fd_opt {
            None => {
                // If no existing file, then there must not yet be a server up and running.
                // So, connect to the monitor and wait for server "hello" as proof that the server
                // started okay. Our call might fail, e.g. in case of --autostart false or failure to
                // load saved-state. In these cases, it will raise an ExitStatus exception which
                // bubbles up to our caller.
                if !has_already_attempted_connect {
                    hh_logger::log("Errors-file: absent, so connecting then trying again");
                    connect_then_close()?;
                } else {
                    // Retry opening errors file every 0.1 second from now on.
                    show_progress_and_sleep(progress_callback);
                }
                has_already_attempted_connect = true;
                already_checked_file = None;
                opening_attempts += 1;
                continue;
            }
            Some(mut fd) => {
                let file_id = FileId::of_fd(&fd);
                if Some(file_id) == already_checked_file {
                    // we've already checked this file! so just wait a short time, then retry
                    show_progress_and_sleep(progress_callback);
                    opening_attempts += 1;
                    continue;
                }
                already_checked_file = Some(file_id);
                match errors_read_openfile(&mut fd) {
                    Err((open_error, log_message)) if !has_already_attempted_connect => {
                        hh_logger::log(&format!(
                            "Errors-file: on {}, read sentinel {} [{}], so connecting then trying again",
                            crate::sys_utils::show_inode(&fd),
                            errors_read::show_open_error(&open_error),
                            log_message
                        ));
                        // If there was an existing file but it was bad -- e.g. came from a dead server,
                        // or binary mismatch, then we will connect as before. In the case of binary mismatch,
                        // we rely on the standard codepaths in clientConnect and monitorConnect: namely, it will
                        // either succeed in starting and connecting to a new server of the correct binary, or
                        // (e.g. without autostart) it will raise Exit_status.(Exit_with Exit_status.Build_id_mismatch).
                        // The exception will bubble up to our caller; here we need only handle success.
                        drop(fd);
                        connect_then_close()?;
                        has_already_attempted_connect = true;
                        opening_attempts += 1;
                        continue;
                    }
                    Err((open_error, log_message)) => {
                        // But if there was an existing file that's still bad even after our connection
                        // attempt, there's not much we can do
                        hh_logger::log(&format!(
                            "Errors-file: on {}, read sentinel {} [{}], and already connected once, so giving up.",
                            crate::sys_utils::show_inode(&fd),
                            errors_read::show_open_error(&open_error),
                            log_message
                        ));
                        progress_callback(None);
                        return match open_error {
                            errors_read::OpenError::OBuildIdMismatch => {
                                Err(Exn::ExitWith(exit_status::T::BuildIdMismatch))
                            }
                            errors_read::OpenError::OReadError(
                                server_progress::ErrorsFileReadError::Malformed,
                            ) => Err(Exn::ExitWith(exit_status::T::ServerHungUpShouldAbort(None))),
                            errors_read::OpenError::OKilled(finale_data) => {
                                Err(Exn::ExitWith(exit_status::T::ServerHungUpShouldAbort(
                                    finale_data.map(Box::new),
                                )))
                            }
                        };
                    }
                    Ok(errors_read::OpenSuccess {
                        pid, clock: None, ..
                    }) => {
                        // If there's an existing file, but it's not using watchman or Edenfs_watcher, then we cannot offer
                        // consistency guarantees. We'll just go with it. This happens for instance
                        // if the server was started using dfind instead of watchman or Edenfs_watcher.
                        hh_logger::log(&format!(
                            "Errors-file: {} is present, without Watchman or Edenfs_watcher, so just going with it.",
                            crate::sys_utils::show_inode(&fd)
                        ));
                        let telemetry =
                            telemetry::int_("opening_attempts", opening_attempts, telemetry);
                        return Ok((pid, fd, telemetry));
                    }
                    Ok(errors_read::OpenSuccess {
                        pid,
                        clock: Some(clock),
                        ..
                    }) => {
                        hh_logger::log(&format!(
                            "Errors-file: {} is present, was started at clock {}, so querying {}...",
                            crate::sys_utils::show_inode(&fd),
                            server_notifier_types::show_clock(&clock),
                            server_notifier::show_file_watcher_name(&clock)
                        ));
                        // Neither Watchman or Eden support "what files have changed from error.bin's clock until
                        // hh-invocation clock?". We'll instead use the (less permissive, still correct) query
                        // "what files have changed from error.bin's clock until now?".
                        let since_result =
                            file_watcher_get_raw_updates_since(root, &clock, local_config);
                        match since_result {
                            Err(e) => {
                                hh_logger::log(&format!(
                                    "Errors-file: file watcher failure:\n{}\n",
                                    e
                                ));
                                // The errors file is present, was started at clock `clock` but the file watcher query failed.
                                // We'll assume there has not been any file change since that clock.,
                                // If there has, hh_server will ultimately tell us with a restart sentinel, and we'll
                                // ask the user to re-run hh. This is sub-optimal UX, but still better UX than
                                // loudly failing now.
                                let telemetry =
                                    telemetry::int_("opening_attempts", opening_attempts, telemetry);
                                return Ok((pid, fd, telemetry));
                            }
                            Ok((raw_updates, file_watcher_telemetry_opt, paths_are_relative)) => {
                                let raw_updates: crate::s_set::T = if paths_are_relative {
                                    raw_updates
                                        .iter()
                                        .map(|file| {
                                            crate::rt::ocaml_filename::concat(
                                                &path::to_string(root),
                                                file,
                                            )
                                        })
                                        .collect()
                                } else {
                                    raw_updates.into_iter().collect()
                                };
                                let updates =
                                    find_utils::post_file_watcher_filter_from_fully_qualified_raw_updates(
                                        root,
                                        &raw_updates,
                                    );
                                telemetry = match file_watcher_telemetry_opt {
                                    None => telemetry,
                                    Some(file_watcher_telemetry) => telemetry::object_(
                                        "file_watcher",
                                        file_watcher_telemetry,
                                        telemetry,
                                    ),
                                };
                                if updates.is_empty() {
                                    // If there was an existing errors.bin, and no files have changed since then,
                                    // then use it!
                                    hh_logger::log(&format!(
                                        "Errors-file: {} is present, was started at clock {} and {} reports no updates since then, so using it!",
                                        crate::sys_utils::show_inode(&fd),
                                        server_notifier_types::show_clock(&clock),
                                        server_notifier::show_file_watcher_name(&clock)
                                    ));
                                    let telemetry = telemetry::int_(
                                        "opening_attempts",
                                        opening_attempts,
                                        telemetry,
                                    );
                                    return Ok((pid, fd, telemetry));
                                } else {
                                    // But if files have changed since the errors.bin, then we will keep spinning
                                    // under trust that hh_server will eventually recognize those changes and create
                                    // a new errors.bin file, which we'll then pick up on another iteration.
                                    // CARE! This only works if hh_server's test for "are there new files" is at least
                                    // as strict as our own.
                                    // They're identical, in fact, because they both use the same watch_spec filter
                                    // [FilesToIgnore.server_watch_spec] and the same [Find_utils.post_file_watcher_filter].
                                    // (`Relative_path.Set.choose`: the least element.)
                                    let example = updates.iter().next().map(relative_path::suffix);
                                    hh_logger::log(&format!(
                                        "Errors-file: {} is present, was started at clock {}, but file watcher reports updates since then, so trying again. {} updates, for example {}",
                                        crate::sys_utils::show_inode(&fd),
                                        server_notifier_types::show_clock(&clock),
                                        updates.len(),
                                        example.unwrap_or_default()
                                    ));
                                    opening_attempts += 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Provides typechecker errors by displaying them to stdout.
/// Errors are printed soon after they are known instead of all at once at the end.
pub fn go_streaming(
    args: &client_env::ClientCheckEnv,
    local_config: &server_local_config::T,
    error_filter: &filter_diagnostics::filter::T,
    partial_telemetry_ref: &PartialTelemetryRef,
    connect_then_close: &mut dyn FnMut() -> Result<(), Exn>,
) -> Result<(exit_status::T, telemetry::T), Exn> {
    let client_env::ClientCheckEnv {
        root,
        show_spinner,
        deadline,
        ..
    } = args;
    let show_spinner = *show_spinner;
    let progress_callback: ProgressCallback =
        Arc::new(move |s| crate::client_spinner::report(show_spinner, false, s));
    let mut connect_then_close = || {
        // must clear spinner in case [connect_then_close] writes to stderr
        progress_callback(None);
        connect_then_close()
    };
    let telemetry = telemetry::create();
    let start_time = ocaml_unix::gettimeofday();
    let (pid, fd, initial_telemetry) = keep_trying_to_open(
        local_config,
        false,
        &mut connect_then_close,
        None,
        &progress_callback,
        *deadline,
        1,
        telemetry,
        root,
    )?;
    let initial_telemetry =
        telemetry::duration(Some("keep_trying_to_open"), start_time, None, initial_telemetry);
    go_streaming_on_fd(
        pid,
        fd,
        args,
        error_filter,
        partial_telemetry_ref,
        initial_telemetry,
        &progress_callback,
    )
}

#[cfg(test)]
mod tests;
