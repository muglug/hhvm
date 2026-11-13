// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `pid_log.ml`. See `hh/PORTING.md`.
//!
//! The `.pids` file of a root (`Server_files.pids_file`): one line
//! `<pid>\t<reason>` per process the server started, read by `hh_client
//! stop`.
//!
//! `Sys_utils.mkdir_no_fail` is not in `crate::sys_utils` yet: it is
//! transliterated below, private, and should move there.

use std::fs::File;
use std::io::Write;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;
use crate::sys_utils::SysError;

/// `log_oc : Out_channel.t option ref`. (A panic while it is held, such as
/// the `failwith` of [`log`], does not make it unusable: OCaml's ref stays as
/// it is.)
fn log_oc() -> MutexGuard<'static, Option<File>> {
    static LOG_OC: Mutex<Option<File>> = Mutex::new(None);
    LOG_OC.lock().unwrap_or_else(|e| e.into_inner())
}

fn enabled() -> &'static AtomicBool {
    static ENABLED: AtomicBool = AtomicBool::new(true);
    &ENABLED
}

pub fn disable() {
    enabled().store(false, Ordering::SeqCst)
}

/// `Sys_utils.mkdir_no_fail dir`: `Unix.mkdir dir 0o777` under umask 0; a
/// directory that exists already is fine, any other error is raised.
fn mkdir_no_fail(dir: &str) {
    match ocaml_unix::mkdir_with_umask(dir, 0o777, 0) {
        Ok(()) => {}
        Err(e) if e.raw_os_error() == Some(libc::EEXIST) => {}
        Err(e) => panic!("{}", ocaml_unix::unix_error_to_string(&e, "mkdir", dir)),
    }
}

/// Creates the pids file (truncated; under umask `0o111`, so mode `0o666`)
/// and keeps it open for [`log`]. The file is close-on-exec. Raises
/// `Sys_error` (panics) if it cannot be created.
pub fn init(pids_file: &str) {
    let mut log_oc = log_oc();
    assert!(log_oc.is_none());
    mkdir_no_fail(&ocaml_filename::dirname(pids_file));
    // `Out_channel.create pids_file` (perm 0o666) under the umask 0o111.
    let oc = match ocaml_unix::openfile_with_umask(
        pids_file,
        &[
            ocaml_unix::OpenFlag::OWronly,
            ocaml_unix::OpenFlag::OCreat,
            ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o111,
    ) {
        Ok(oc) => oc,
        Err(e) => panic!("{}", SysError::of_io_error(pids_file, &e)),
    };
    *log_oc = Some(oc);
}

/// Appends `<pid>\t<reason>` (`reason` defaults to `"unknown"`) and flushes.
/// When the log was not initialized: nothing if `no_fail` (default
/// `false`), `failwith` otherwise. Nothing at all once [`disable`]d.
pub fn log(reason: Option<&str>, no_fail: Option<bool>, pid: isize) {
    let no_fail = no_fail.unwrap_or(false);
    if enabled().load(Ordering::SeqCst) {
        let reason = match reason {
            None => "unknown",
            Some(s) => s,
        };
        let mut log_oc = log_oc();
        match &mut *log_oc {
            None if no_fail => {}
            None => panic!("Can't write pid to uninitialized pids log"),
            Some(oc) => {
                // `Printf.fprintf oc "%d\t%s\n%!"`: the channel buffers the
                // line and `%!` flushes it, so it reaches the file in one
                // write (a `File` is not buffered: `writeln!` would write
                // each piece separately, and a reader such as `hh_client
                // stop` could see half a line).
                let line = format!("{}\t{}\n", pid, reason);
                if let Err(e) = oc.write_all(line.as_bytes()).and_then(|()| oc.flush()) {
                    panic!("{}", SysError(e.to_string()))
                }
            }
        }
    }
}

/// `exception FailedToGetPids`: the pids file could not be read
/// (`Sys_error`), the only error [`get_pids`] reports, which its caller
/// (`hh_client stop`) catches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FailedToGetPids;

/// The `(pid, reason)` of each line `^\([0-9]+\)\t\(.+\)` of the file, in
/// order; the other lines are skipped. (`In_channel.input_line`: lines end
/// at `\n`, a final `\r` is dropped, a last line without `\n` counts.)
pub fn get_pids(pids_file: &str) -> Result<Vec<(isize, String)>, FailedToGetPids> {
    let contents = match std::fs::read(pids_file) {
        Ok(contents) => contents,
        Err(_) => return Err(FailedToGetPids),
    };
    let mut results = vec![];
    let mut rows: Vec<&[u8]> = contents.split(|c| *c == b'\n').collect();
    // `input_line` gives no line after a final newline (or for an empty file).
    if rows.last().is_some_and(|row| row.is_empty()) {
        rows.pop();
    }
    for row in rows {
        // `fix_win_eol`
        let row = row.strip_suffix(b"\r").unwrap_or(row);
        // `Str.string_match (Str.regexp "^\\([0-9]+\\)\t\\(.+\\)") row 0`:
        // `.` is any character but a newline, and there is none in a line.
        let digits = row.iter().take_while(|c| c.is_ascii_digit()).count();
        if digits > 0 && row.get(digits) == Some(&b'\t') && row.len() > digits + 1 {
            let pid = std::str::from_utf8(&row[..digits]).unwrap();
            // `int_of_string`, which fails beyond `max_int`.
            let pid = match pid.parse::<i64>() {
                Ok(pid) if pid < (1 << 62) => pid as isize,
                _ => panic!("int_of_string"),
            };
            let reason = String::from_utf8_lossy(&row[digits + 1..]).into_owned();
            results.push((pid, reason));
        }
    }
    Ok(results)
}

pub fn close() {
    // `Option.iter !log_oc ~f:Out_channel.close`: dropping the file closes it.
    *log_oc() = None;
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::MetadataExt;

    use super::*;

    /// The log is global: one test does it all.
    #[test]
    fn init_log_get_close() {
        let dir = std::env::temp_dir().join(format!("hh_pid_log_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let pids_file = dir.join("root.pids");
        let pids_file = pids_file.to_str().unwrap();
        assert_eq!(get_pids(pids_file), Err(FailedToGetPids));

        // Not initialized.
        log(None, Some(true), 1);
        assert_eq!(
            std::panic::catch_unwind(|| log(None, None, 1))
                .unwrap_err()
                .downcast_ref::<&str>()
                .copied(),
            Some("Can't write pid to uninitialized pids log")
        );

        init(pids_file);
        // `assert (Option.is_none !log_oc)`: only once.
        assert!(std::panic::catch_unwind(|| init(pids_file)).is_err());
        assert_eq!(std::fs::metadata(pids_file).unwrap().mode() & 0o777, 0o666);
        assert_eq!(std::fs::metadata(&dir).unwrap().mode() & 0o777, 0o777);
        log(Some("monitor"), None, 123);
        log(None, None, 456);
        assert_eq!(
            std::fs::read_to_string(pids_file).unwrap(),
            "123\tmonitor\n456\tunknown\n"
        );
        assert_eq!(
            get_pids(pids_file),
            Ok(vec![(123, "monitor".to_string()), (456, "unknown".to_string())])
        );
        close();
        log(None, Some(true), 789);

        // The lines that do not match are skipped; a final `\r` goes.
        std::fs::write(
            pids_file,
            "1\tmain\r\nx\ty\n2\t\n\t3\n42\tworker 1\tz\n7\tlast",
        )
        .unwrap();
        assert_eq!(
            get_pids(pids_file),
            Ok(vec![
                (1, "main".to_string()),
                (42, "worker 1\tz".to_string()),
                (7, "last".to_string())
            ])
        );

        // Once disabled, nothing is logged, not even the failure.
        disable();
        log(None, None, 1);
        enabled().store(true, Ordering::SeqCst);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
