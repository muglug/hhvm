// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_format.ml`.
//!
//! Owned by **FMT** (plan §7.3).
//!
//! IDE formatting runs the `hackfmt` executable as a child process, as the
//! OCaml does: argv[0] is the executable's path, the content goes to its
//! stdin, its stdout is read as lines, its stderr is the caller's, and the
//! environment is inherited. The executable is the first that exists of
//! `$HACKFMT_TEST_PATH` and `Build_options.default_hackfmt_path`
//! ([`default_hackfmt_path`]).
//!
//! `Timeout.read_process` (a `SIGALRM` timer of 6 seconds around writing
//! the content, reading the output and waiting for the child) is a deadline
//! on a `poll` loop here. As in the OCaml, a child that times out is neither
//! killed nor waited for: our ends of its pipes are closed.
//!
//! Exceptions. `Unix.create_process` failing (the file exists but cannot be
//! executed) is an exception that the OCaml lets through to the caller of
//! `go_ide`; here it is a panic with the same text (`Unix.Unix_error(...)`).
//! One difference: if `hackfmt` exits before reading all its input, writing
//! the rest raises `Sys_error "Broken pipe"` in the OCaml (only possible
//! with more than a pipe buffer of content); here the write stops and the
//! exit status is reported as for any other exit.

use std::io::Read;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::time::Duration;
use std::time::Instant;

use crate::file_content;
use crate::file_content::position;
use crate::hackfmt_error;
use crate::hh_logger;
use crate::ide_api_types;
use crate::lsp::document_formatting::FormattingOptions;
use crate::server_format_types;
use crate::server_format_types::IdeAction;
use crate::server_format_types::IdeResponse;
use crate::server_format_types::IdeResult;

/// The timeout of a call to hackfmt, in seconds.
/// SLACK: bump timeout from 2s -> 6s to allow autoformatting large files
const HACKFMT_TIMEOUT: u64 = 6;

/// `Build_options.default_hackfmt_path`: `<bindir>/hackfmt`, where `bindir`
/// is `CMAKE_INSTALL_FULL_BINDIR` at build time (`options/discover.ml`).
/// When the build does not say, `/usr/local/bin`, the value of the OCaml
/// build (CMake's default prefix). Rust: the file name is `hackfmt` + the
/// suffix of the running executable ([`crate::rt::exe_suffix`]:
/// `hh_server_rust` runs `<bindir>/hackfmt_rust`, never the OCaml-installed
/// `hackfmt`).
pub fn default_hackfmt_path() -> String {
    default_hackfmt_path_of(&crate::rt::exe_suffix::executable_suffix())
}

/// [`default_hackfmt_path`] for a given executable suffix.
pub fn default_hackfmt_path_of(suffix: &str) -> String {
    format!(
        "{}/hackfmt{}",
        option_env!("CMAKE_INSTALL_FULL_BINDIR").unwrap_or("/usr/local/bin"),
        suffix
    )
}

/// What `Timeout.read_process` with the reader of `call_external_formatter`
/// ends with.
enum ReadOutcome {
    Exited(Vec<u8>, ExitStatus),
    TimedOut,
}

fn set_nonblocking(fd: i32) {
    // SAFETY: fcntl on a file descriptor we own.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFL);
        libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
    }
}

/// `Timeout.read_process ~timeout ~on_timeout ~reader cmd args`, with the
/// reader of `call_external_formatter`: write `content` to the child's
/// stdin and close it, read its stdout to the end, wait for it; all of it
/// before `deadline`.
fn read_process(path: &str, args: &[String], content: &str, deadline: Instant) -> ReadOutcome {
    let mut child = match Command::new(path)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => panic!(
            "{}",
            crate::rt::ocaml_unix::unix_error_to_string(&e, "create_process", path)
        ),
    };
    let mut stdin = child.stdin.take();
    let mut stdout = child.stdout.take().expect("piped stdout");
    let content = content.as_bytes();
    let mut written = 0;
    if content.is_empty() {
        stdin = None;
    }
    if let Some(stdin) = &stdin {
        set_nonblocking(stdin.as_raw_fd());
    }
    set_nonblocking(stdout.as_raw_fd());
    let mut output = Vec::new();
    let mut buf = vec![0u8; 65536];
    loop {
        let now = Instant::now();
        if now >= deadline {
            return ReadOutcome::TimedOut;
        }
        let remaining_ms = (deadline - now).as_millis().clamp(1, i32::MAX as u128) as i32;
        let mut fds = vec![libc::pollfd {
            fd: stdout.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        }];
        if let Some(stdin) = &stdin {
            fds.push(libc::pollfd {
                fd: stdin.as_raw_fd(),
                events: libc::POLLOUT,
                revents: 0,
            });
        }
        // SAFETY: `fds` is a valid array of `fds.len()` pollfds.
        let n = unsafe { libc::poll(fds.as_mut_ptr(), fds.len() as libc::nfds_t, remaining_ms) };
        if n < 0 {
            let err = std::io::Error::last_os_error();
            if err.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&err, "select", ""));
        }
        if fds.len() > 1 && fds[1].revents != 0 {
            let pipe = stdin.as_mut().expect("stdin is open");
            match pipe.write(&content[written..]) {
                Ok(k) => {
                    written += k;
                    if written == content.len() {
                        // `Out_channel.close oc`
                        stdin = None;
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                // The child closed its stdin (see the module documentation).
                Err(_) => stdin = None,
            }
        }
        if fds[0].revents != 0 {
            match stdout.read(&mut buf) {
                Ok(0) => break,
                Ok(k) => output.extend_from_slice(&buf[..k]),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => panic!("Sys_error(\"{}\")", e),
            }
        }
    }
    // `Timeout.close_process_in`: close stdout, `waitpid`.
    drop(stdin);
    drop(stdout);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return ReadOutcome::Exited(output, status),
            Ok(None) => {}
            Err(e) => panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "waitpid", "")),
        }
        if Instant::now() >= deadline {
            return ReadOutcome::TimedOut;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

/// The lines that repeated `Stdlib.input_line` reads from `output` until
/// `End_of_file`: split at `'\n'`, with a last line that has no newline
/// when the output does not end with one.
fn input_lines(output: &[u8]) -> Vec<String> {
    let s = String::from_utf8_lossy(output);
    let mut lines: Vec<String> = s.split('\n').map(str::to_string).collect();
    if lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
}

// TODO t14922604: Further improve error handling
pub fn call_external_formatter(
    cmd: &str,
    content: &str,
    args: &[String],
) -> Result<Vec<String>, String> {
    let deadline = Instant::now() + Duration::from_secs(HACKFMT_TIMEOUT);
    match read_process(cmd, args, content, deadline) {
        ReadOutcome::Exited(output, status) => match status.code() {
            Some(0) => Ok(input_lines(&output)),
            Some(v) => Err(hackfmt_error::get_error_string_from_exit_value(v).to_string()),
            None => Err("Call to hackfmt was killed".to_string()),
        },
        ReadOutcome::TimedOut => {
            hh_logger::log("Formatter timeout");
            Err("Call to hackfmt timed out".to_string())
        }
    }
}

pub fn formatting_options_to_args(options: &FormattingOptions) -> Vec<String> {
    let mut args = vec!["--indent-width".to_string(), options.tabSize.to_string()];
    if !options.insertSpaces {
        args.push("--tabs".to_string());
    }
    args
}

pub fn range_offsets_to_args(from: isize, to_: isize) -> Vec<String> {
    vec!["--range".to_string(), from.to_string(), to_.to_string()]
}

/// returns lines of stdout we get from shelling out to hackfmt
pub fn go_hackfmt(
    filename_for_logging: Option<&str>,
    content: &str,
    args: Vec<String>,
) -> Result<Vec<String>, String> {
    let mut args = args;
    if let Some(filename) = filename_for_logging {
        args.push("--filename-for-logging".to_string());
        args.push(filename.to_string());
    }
    hh_logger::log(&args.join(" "));
    let mut paths = vec![crate::path::to_string(&crate::path::make(
        &default_hackfmt_path(),
    ))];
    if let Some(p) = std::env::var_os("HACKFMT_TEST_PATH") {
        paths.insert(0, p.to_string_lossy().into_owned());
    }
    // `Sys.file_exists`
    let path = paths.iter().find(|p| std::path::Path::new(p).exists());
    match path {
        Some(path) => call_external_formatter(path, content, &args),
        None => {
            hh_logger::log("Formatter not found");
            Err(format!(
                "Could not locate formatter - looked in: {}",
                paths.join(" ")
            ))
        }
    }
}

/// Our formatting engine can only handle ranges that span entire rows.
/// This is signified by a range that starts at column 1 on one row,
/// and ends at column 1 on another (because it's half-open).
/// Nuclide always provides correct ranges, but other editors might not.
pub fn expand_range_to_whole_rows(
    content: &str,
    range: &file_content::Range,
) -> (file_content::Range, isize, isize) {
    // It's easy to expand the start of the range if necessary, but to expand
    // the end of the range requires more work...
    let range = file_content::Range {
        st: position::beginning_of_line(&range.st),
        ..*range
    };
    let (from0, to0) = file_content::get_offsets(content, (&range.st, &range.ed));
    if position::is_beginning_of_line(&range.ed) || to0 == content.len() as isize {
        // common case is performant.
        (range, from0, to0)
    } else {
        // First guess: we'll extend range.ed to the end of the line.
        let ed = position::beginning_of_next_line(&range.ed);
        // But if this is longer than the length of the file, pull back.
        let ed_file = file_content::offset_to_position(content, content.len() as isize);
        let ed = if position::compare(&ed, &ed_file) <= 0 {
            ed
        } else {
            ed_file
        };
        let range = file_content::Range { ed, ..range };
        let (from0, to0) = file_content::get_offsets(content, (&range.st, &range.ed));
        (range, from0, to0)
    }
}

/// `range_regexp` (`^\([0-9]+\) \([0-9]+\)$`), matched with
/// `Str.string_match` at 0: two integers separated by a space.
fn match_range_line(range_line: &str) -> Option<(isize, isize)> {
    // `$` also matches before a newline; `input_line` leaves none.
    let line = range_line.strip_suffix('\n').unwrap_or(range_line);
    let (a, b) = line.split_once(' ')?;
    let is_digits = |s: &str| !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit());
    if !is_digits(a) || !is_digits(b) {
        return None;
    }
    // `int_of_string` raises `Failure "int_of_string"` past max_int.
    let int_of_string = |s: &str| -> isize {
        s.parse()
            .unwrap_or_else(|_| panic!("Failure(\"int_of_string\")"))
    };
    Some((int_of_string(a), int_of_string(b)))
}

pub fn zip_with_index<'a, A, B>(xs: &'a [A], ys: &'a [B]) -> Vec<(isize, &'a A, Option<&'a B>)> {
    xs.iter()
        .enumerate()
        .map(|(i, x)| (i as isize, x, ys.get(i)))
        .collect()
}

pub fn opt_string_eq(x: &str, y: Option<&String>) -> bool {
    match y {
        Some(y) => x == y,
        None => false,
    }
}

/// 0-indexed (line count starts from 0)
pub fn first_changed_line_idx(old_lines: &[String], new_lines: &[String]) -> Option<isize> {
    let numbered_lines = zip_with_index(old_lines, new_lines);
    let first_novel_line = numbered_lines
        .into_iter()
        .find(|(_, x, y)| !opt_string_eq(x, *y));
    first_novel_line.map(|(i, _, _)| i)
}

pub fn last_changed_line_idx(old_lines: &[String], new_lines: &[String]) -> Option<isize> {
    let rev_old: Vec<String> = old_lines.iter().rev().cloned().collect();
    let rev_new: Vec<String> = new_lines.iter().rev().cloned().collect();
    first_changed_line_idx(&rev_old, &rev_new).map(|rev_idx| old_lines.len() as isize - rev_idx)
}

/// `List.drop xs n`
fn list_drop<A: Clone>(xs: &[A], n: isize) -> Vec<A> {
    let n = n.clamp(0, xs.len() as isize) as usize;
    xs[n..].to_vec()
}

/// Drop the last [n] items in [xs].
pub fn drop_tail<A: Clone>(xs: &[A], n: isize) -> Vec<A> {
    let rev: Vec<A> = xs.iter().rev().cloned().collect();
    let mut kept = list_drop(&rev, n);
    kept.reverse();
    kept
}

/// An empty edit that has no effect.
pub fn noop_edit() -> IdeResponse {
    let range = file_content::Range {
        st: position::beginning_of_file(),
        ed: position::beginning_of_file(),
    };
    IdeResponse {
        new_text: String::new(),
        range: ide_api_types::ide_range_from_fc(&range),
    }
}

/// Core's `String.split_lines`: the lines, without their `"\n"` or
/// `"\r\n"`; no last empty line for a final newline; `[]` for `""`.
pub fn split_lines(s: &str) -> Vec<String> {
    if s.is_empty() {
        return vec![];
    }
    let mut pieces: Vec<&str> = s.split('\n').collect();
    let ends_with_newline = s.ends_with('\n');
    if ends_with_newline {
        pieces.pop();
    }
    let n = pieces.len();
    pieces
        .into_iter()
        .enumerate()
        .map(|(i, piece)| {
            let terminated = i + 1 < n || ends_with_newline;
            match piece.strip_suffix('\r') {
                Some(stripped) if terminated => stripped.to_string(),
                _ => piece.to_string(),
            }
        })
        .collect()
}

/// Return an IDE text edit that doesn't include unchanged leading or trailing lines.
pub fn minimal_edit(old_src: &str, new_src: &str) -> IdeResponse {
    let old_src_lines = split_lines(old_src);
    let new_src_lines = split_lines(new_src);

    // 0-indexed (line count starts from 0)
    let range_start_line = first_changed_line_idx(&old_src_lines, &new_src_lines);
    let range_end_line = last_changed_line_idx(&old_src_lines, &new_src_lines);

    match (range_start_line, range_end_line) {
        (Some(range_start_line), Some(range_end_line)) => {
            let new_src_novel_lines = drop_tail(
                &list_drop(&new_src_lines, range_start_line),
                old_src_lines.len() as isize - range_end_line,
            );
            let (new_text, start_line_adjustment) = if new_src_novel_lines.is_empty()
                && range_end_line < old_src_lines.len() as isize
            {
                // Empty `new_src_novel_lines` does not mean that there was no change
                // (otherwise we wouldn't have reached here),
                // it means some lines have been deleted. `-1` here allows to delete those lines.
                (String::new(), -1)
            } else {
                (new_src_novel_lines.join("\n") + "\n", 0)
            };
            let range_start_line = range_start_line + start_line_adjustment;
            let range = file_content::Range {
                st: position::from_zero_based(range_start_line, 0),
                ed: position::from_zero_based(range_end_line, 0),
            };
            IdeResponse {
                new_text,
                range: ide_api_types::ide_range_from_fc(&range),
            }
        }
        _ => noop_edit(),
    }
}

pub fn go_ide(
    filename_for_logging: &str,
    content: &str,
    action: &IdeAction,
    options: &FormattingOptions,
) -> IdeResult {
    let convert_to_ide_result =
        |old_format_result: server_format_types::Result, range: &file_content::Range| -> IdeResult {
            let range = ide_api_types::ide_range_from_fc(range);
            old_format_result.map(|new_text| IdeResponse { new_text, range })
        };
    let formatting_args = formatting_options_to_args(options);
    match action {
        IdeAction::Document => {
            // hackfmt currently takes one-indexed integers for range formatting.
            go_hackfmt(Some(filename_for_logging), content, formatting_args)
                .map(|lines| lines.join("\n"))
                .map(|new_text| minimal_edit(content, &new_text))
        }
        IdeAction::Range(range) => {
            let fc_range = ide_api_types::ide_range_to_fc(range);
            let (range, from0, to0) = expand_range_to_whole_rows(content, &fc_range);
            let mut args = formatting_args;
            args.extend(range_offsets_to_args(from0 + 1, to0 + 1));
            let result = go_hackfmt(Some(filename_for_logging), content, args)
                .map(|lines| lines.join("\n") + "\n");
            convert_to_ide_result(result, &range)
        }
        IdeAction::Position(position) => {
            // `get_offset` returns a zero-based index, and `--at-char` takes a
            // zero-based index.
            let offset = file_content::get_offset(content, position);
            let mut args = vec!["--at-char".to_string(), offset.to_string()];
            args.extend(formatting_args);
            let lines = go_hackfmt(Some(filename_for_logging), content, args)?;
            // `hackfmt --at-char` returns the range that was formatted, as well as the
            // contents of that range. For example, it might return
            //
            //     10 12
            //     }
            //
            // signifying that we should replace the character under the cursor with the
            // following content, starting at index 10. We need to extract the range
            // from the first line and forward it to the client so that it knows where
            // to apply the edit.
            let (range_line, lines) = match lines.split_first() {
                Some((range_line, lines)) => (range_line, lines),
                None => return Err("Got no lines in at-position formatting".to_string()),
            };
            // Extract the offsets in the first line that form the range.
            match match_range_line(range_line) {
                None => Err("Range not found on first line of --at-char output".to_string()),
                Some((from0, to0)) => {
                    let range = ide_api_types::ide_range_from_fc(&file_content::Range {
                        st: file_content::offset_to_position(content, from0),
                        ed: file_content::offset_to_position(content, to0),
                    });
                    let new_text = lines.join("\n");
                    Ok(IdeResponse { new_text, range })
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
