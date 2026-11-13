// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Proc` (`utils/sys/proc.ml`): the functions that the ported modules need
//! so far, `get_cmdline` and `is_alive` (`Server_progress` uses them to tell
//! a live server from a dead one). See `hh/PORTING.md`.
//!
//! `get_proc_stat`, `get_proc_stack` and `is_likely_from_interactive_shell`
//! were added for `hh_client` (which guesses its `--from` from the stack of
//! its parent processes). OCaml reads `/proc/<pid>/stat` for the parent pid;
//! on macOS, as for the command line, this port asks the system
//! (`proc_pidinfo`), so that macOS behaves as Linux does.
//!
//! OCaml reads `/proc/<pid>/cmdline`, which only Linux has: on macOS every
//! read fails, so OCaml's `is_alive` is `false` for every process there (and
//! `progress.json` always reads as "stopped"). This port reads the same
//! command line on macOS with `sysctl(KERN_PROCARGS2)` (the arguments, each
//! followed by a NUL, as in `/proc/<pid>/cmdline`); on other systems it
//! fails as OCaml does.

use crate::rt::ocaml_printf::sprintf_S;
use crate::rt::ocaml_unix;

/// The command line of a process, its arguments each followed by a NUL
/// (the contents of `/proc/<pid>/cmdline`), or the message of the
/// `Sys_error` that reading it raised.
#[cfg(target_os = "linux")]
fn read_cmdline(pid: isize) -> Result<Vec<u8>, String> {
    let cmdline_path = format!("/proc/{}/cmdline", pid);
    crate::sys_utils::cat(&cmdline_path).map_err(|e| e.0)
}

#[cfg(target_os = "macos")]
fn read_cmdline(pid: isize) -> Result<Vec<u8>, String> {
    let cmdline_path = format!("/proc/{}/cmdline", pid);
    let fail = |e: std::io::Error| {
        crate::sys_utils::SysError::of_io_error(&cmdline_path, &e).0
    };
    // SAFETY: the `sysctl` calls are given buffers of the sizes they are
    // told.
    unsafe {
        let mut argmax: libc::c_int = 0;
        let mut size = std::mem::size_of::<libc::c_int>();
        let mut mib = [libc::CTL_KERN, libc::KERN_ARGMAX];
        if libc::sysctl(
            mib.as_mut_ptr(),
            2,
            &mut argmax as *mut libc::c_int as *mut libc::c_void,
            &mut size,
            std::ptr::null_mut(),
            0,
        ) == -1
        {
            return Err(fail(std::io::Error::last_os_error()));
        }
        let mut buf = vec![0u8; argmax.max(0) as usize];
        let mut size = buf.len();
        let mut mib = [libc::CTL_KERN, libc::KERN_PROCARGS2, pid as libc::c_int];
        if libc::sysctl(
            mib.as_mut_ptr(),
            3,
            buf.as_mut_ptr() as *mut libc::c_void,
            &mut size,
            std::ptr::null_mut(),
            0,
        ) == -1
        {
            return Err(fail(std::io::Error::last_os_error()));
        }
        buf.truncate(size);
        // argc, the executable path, NULs, then the arguments (then the
        // environment).
        let invalid = || fail(std::io::Error::from_raw_os_error(libc::EINVAL));
        if buf.len() < 4 {
            return Err(invalid());
        }
        let argc = i32::from_ne_bytes([buf[0], buf[1], buf[2], buf[3]]);
        let mut i = 4;
        while i < buf.len() && buf[i] != 0 {
            i += 1;
        }
        while i < buf.len() && buf[i] == 0 {
            i += 1;
        }
        let mut cmdline = vec![];
        for _ in 0..argc {
            let start = i;
            while i < buf.len() && buf[i] != 0 {
                i += 1;
            }
            if i >= buf.len() {
                return Err(invalid());
            }
            cmdline.extend_from_slice(&buf[start..=i]);
            i += 1;
        }
        Ok(cmdline)
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn read_cmdline(pid: isize) -> Result<Vec<u8>, String> {
    let cmdline_path = format!("/proc/{}/cmdline", pid);
    crate::sys_utils::cat(&cmdline_path).map_err(|e| e.0)
}

/// Takes a PID and returns the full command line the process was started with
/// (its arguments separated by spaces, with a space at the end: the NULs of
/// `/proc/<pid>/cmdline` are replaced). Bytes that are not UTF-8 become
/// U+FFFD.
pub fn get_cmdline(pid: isize) -> Result<String, String> {
    match read_cmdline(pid) {
        Ok(cmdline) => {
            // Str.global_replace cmdline_delimiter_re " "
            let line: Vec<u8> = cmdline
                .into_iter()
                .map(|c| if c == 0 { b' ' } else { c })
                .collect();
            Ok(String::from_utf8_lossy(&line).into_owned())
        }
        Err(sys_error) => {
            // `Exn.to_string` of the `Sys_error` (a sexp).
            let error = format!(
                "No 'cmdline' file found for PID {}: '(Sys_error {})'",
                pid,
                sprintf_S(&sys_error)
            );
            Err(error)
        }
    }
}

/// `Proc.proc_stat`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProcStat {
    pub cmdline: String,
    pub ppid: isize,
}

// On macOS the parent pid is not scanned from a `stat` file.
/// Why `/proc/<pid>/stat` gave no parent pid: the `Sys_error` of reading it,
/// or the `Scanf` failure of reading the parent pid in it.
enum StatError {
    Sys(String),
    #[cfg_attr(target_os = "macos", allow(dead_code))]
    Scan(String),
}

/// `Scanf.bscanf stat "%d (%s@) %c %d"` on the contents of
/// `/proc/<pid>/stat`: the parent pid (the fourth field), or the message of
/// the `Scanf.Scan_failure` (approximate: the text of `Scanf`'s messages is
/// not reproduced, only their form).
#[cfg_attr(all(target_os = "macos", not(test)), allow(dead_code))]
fn scan_stat_ppid(stat: &[u8]) -> Result<isize, String> {
    let fail = |what: &str, i: usize| -> String {
        format!(
            "(Scanf.Scan_failure \"scanf: bad input at char number {}: {}\")",
            i, what
        )
    };
    let skip_whitespace = |i: &mut usize| {
        while *i < stat.len() && matches!(stat[*i], b' ' | b'\t' | b'\n' | b'\r') {
            *i += 1;
        }
    };
    let scan_int = |i: &mut usize| -> Result<isize, String> {
        let start = *i;
        if *i < stat.len() && (stat[*i] == b'-' || stat[*i] == b'+') {
            *i += 1;
        }
        let digits = *i;
        while *i < stat.len() && (stat[*i].is_ascii_digit() || stat[*i] == b'_') {
            *i += 1;
        }
        if *i == digits {
            return Err(fail("character is not a decimal digit", *i));
        }
        let text: String = String::from_utf8_lossy(&stat[start..*i])
            .chars()
            .filter(|c| *c != '_')
            .collect();
        text.parse::<isize>()
            .map_err(|_| fail("int_of_string", start))
    };
    let mut i = 0;
    // %d
    scan_int(&mut i)?;
    // " (" : any whitespace, then '('
    skip_whitespace(&mut i);
    if i >= stat.len() || stat[i] != b'(' {
        return Err(fail("looking for '('", i));
    }
    i += 1;
    // "%s@)": everything up to the first ')'
    while i < stat.len() && stat[i] != b')' {
        i += 1;
    }
    if i >= stat.len() {
        return Err(fail("looking for ')', found end of input", i));
    }
    i += 1;
    // " %c"
    skip_whitespace(&mut i);
    if i >= stat.len() {
        return Err(fail("looking for a character, found end of input", i));
    }
    i += 1;
    // " %d"
    skip_whitespace(&mut i);
    scan_int(&mut i)
}

/// The parent pid of `pid` (what OCaml scans in `/proc/<pid>/stat`).
#[cfg(not(target_os = "macos"))]
fn read_stat_ppid(pid: isize) -> Result<isize, StatError> {
    let stat_path = format!("/proc/{}/stat", pid);
    let stat = crate::sys_utils::cat(&stat_path).map_err(|e| StatError::Sys(e.0))?;
    scan_stat_ppid(&stat).map_err(StatError::Scan)
}

#[cfg(target_os = "macos")]
fn read_stat_ppid(pid: isize) -> Result<isize, StatError> {
    let stat_path = format!("/proc/{}/stat", pid);
    // SAFETY: `info` is as large as `proc_pidinfo` is told it is.
    let mut info: libc::proc_bsdinfo = unsafe { std::mem::zeroed() };
    let size = std::mem::size_of::<libc::proc_bsdinfo>() as libc::c_int;
    let ret = unsafe {
        libc::proc_pidinfo(
            pid as libc::c_int,
            libc::PROC_PIDTBSDINFO,
            0,
            &mut info as *mut libc::proc_bsdinfo as *mut libc::c_void,
            size,
        )
    };
    if ret != size {
        // As Linux would say of a process that is not there.
        let e = std::io::Error::from_raw_os_error(libc::ENOENT);
        return Err(StatError::Sys(
            crate::sys_utils::SysError::of_io_error(&stat_path, &e).0,
        ));
    }
    Ok(info.pbi_ppid as isize)
}

/// Takes a PID and returns the information about the process, including
/// the name and the PID of the parent process (PPID)
pub fn get_proc_stat(pid: isize) -> Result<ProcStat, String> {
    match read_stat_ppid(pid) {
        Ok(ppid) => match get_cmdline(pid) {
            Ok(cmdline) => Ok(ProcStat { cmdline, ppid }),
            Err(err) => Err(err),
        },
        Err(StatError::Scan(e)) => {
            let error = format!("Error reading 'stat' for PID {}: {}", pid, e);
            Err(error)
        }
        Err(StatError::Sys(sys_error)) => {
            // `Exn.to_string` of the `Sys_error` (a sexp).
            let error = format!(
                "No 'stat' file found for PID {}: '(Sys_error {})'",
                pid,
                sprintf_S(&sys_error)
            );
            Err(error)
        }
    }
}

/// `Stdlib.String.trim`: without the ` `, `\x0c`, `\n`, `\r` and `\t` at
/// both ends.
fn stdlib_trim(s: &[u8]) -> &[u8] {
    let is_space = |c: &u8| matches!(c, b' ' | b'\x0c' | b'\n' | b'\r' | b'\t');
    let start = s.iter().position(|c| !is_space(c)).unwrap_or(s.len());
    let end = s.iter().rposition(|c| !is_space(c)).map_or(start, |i| i + 1);
    &s[start..end.max(start)]
}

/// This returns the cmdlines of all callers in the PPID stack, with the ancestor caller at head
/// e.g. "/usr/lib/systemd/systemd --system" and the cmdline of the [pid] parameter at the tail.
/// There's the theoretical possibility of failng to read a /proc/{PID}/stat
/// or /proc/{PID}/cmdline on linux, and the real eventuality that it doesn't work
/// outside linux -- in these cases the returned string list contains strings that start with
/// the word "ERROR".
pub fn get_proc_stack(max_depth: Option<isize>, max_length: Option<usize>, pid: isize) -> Vec<String> {
    let max_depth = max_depth.unwrap_or(-1);
    let max_length = max_length.unwrap_or(usize::MAX);
    let prepare_cmdline = |cmdline: &str| -> String {
        let cmdline = stdlib_trim(cmdline.as_bytes());
        if max_length >= cmdline.len() {
            String::from_utf8_lossy(cmdline).into_owned()
        } else {
            String::from_utf8_lossy(stdlib_trim(&cmdline[..max_length])).into_owned() + "..."
        }
    };
    // We could have max_depth as optional, but then everybody would have to pass in None
    let mut curr_pid = pid;
    let mut acc: Vec<String> = vec![];
    let mut counter = 0;
    loop {
        if curr_pid == 0 {
            return acc;
        } else if counter == max_depth {
            return acc;
        } else {
            match get_proc_stat(curr_pid) {
                Ok(stat) => {
                    acc.insert(0, prepare_cmdline(&stat.cmdline));
                    curr_pid = stat.ppid;
                    counter += 1;
                }
                Err(e) => return vec![format!("ERROR {}", e)],
            }
        }
    }
}

/// This heuristic function judges whether [init_proc_stack] indicates an hh binary
/// that was invoked from an interactive shell, rather than from some script/tool.
pub fn is_likely_from_interactive_shell(init_proc_stack: &[String]) -> bool {
    // Things at the bottom of the stack like "/usr/local/bin/hh_client" indicate
    // the actual binary, or "/bin/bash /usr/local/bin/hh" a trivial wrapper around it.
    // We will ignore these.
    let is_skippable_hh_cmdline = |cmdline: &str| -> bool {
        let parts: Vec<&str> = cmdline.split(' ').collect();
        match parts.as_slice() {
            [] => false,
            // (And the names the Rust binaries are installed under.)
            ["/bin/bash", cmd, ..] | [cmd, ..] => {
                ["hh", "hh_client", "hh_server", "hh_client_rust", "hh_server_rust"]
                    .contains(&crate::rt::ocaml_filename::basename(cmd).as_str())
            }
        }
    };
    // After stripping binary/wrapper, if what's left has the form "-bash" or "/usr/bin/bash --init-file ..."
    // then that shows it's an interactive shell. However "bash -c cmd" is not.
    let is_interactive_shell_cmdline = |cmdline: &str| -> bool {
        let parts: Vec<&str> = cmdline.split(' ').collect();
        match parts.as_slice() {
            [] => false,
            [cmd] if cmd.ends_with("sh") => true,
            [cmd, arg, ..] if cmd.ends_with("sh") => {
                arg.starts_with('-') && !arg.starts_with("-c")
            }
            _ => false,
        }
    };

    for cmdline in init_proc_stack.iter().rev() {
        if is_skippable_hh_cmdline(cmdline) {
            continue;
        } else if is_interactive_shell_cmdline(cmdline) {
            return true;
        } else {
            return false;
        }
    }
    false
}

/// There's no reliable way to tell whether an arbitrary PID is still alive.
/// That's because after the process has long since died, its PID might be recycled
/// for use by another process. This routine makes a best-effort attempt:
/// 1. Can we read /proc/<pid>/cmdline? - yes if it's alive or still being held onto.
/// 2. Is "expected" a substring of cmdline? - this is our best-effort protection
///    against pid recyling, since the chance that it gets recycled *and* the recycled one
///    has the process-name we were expecting just seems pretty low. Note that cmdline
///    will be empty if the process has been zombified. Also that if a process modifies
///    its argv then the cmdline will reflect that. In effect, cmdline is the command-line
///    that the process wants you to see.
/// 3. Can we send SIGKILL 0 to it? If this succeeds without throwing an exception,
///    then the process is alive.
pub fn is_alive(pid: isize, expected: &str) -> bool {
    // 1. Can we fetch /proc/<pid>/cmdline ?
    match get_cmdline(pid) {
        Err(_) => false,
        Ok(cmdline) => {
            // 2. Is /proc/<pid>/cmdline the process-name that we expected?
            // To consider: it would be more accurate, but less usable, to test whether /proc/stat
            // records the same starttime as expected. See 'man proc' for more details.
            if cmdline.contains(expected) {
                // 3. Does "SIGKILL <pid> 0" succeed to send a message to the process?
                ocaml_unix::kill(pid, 0).is_ok()
            } else {
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cmdline_of_this_process() {
        let pid = ocaml_unix::getpid();
        let cmdline = get_cmdline(pid).unwrap();
        // The arguments, each followed by a space.
        let args: Vec<String> = std::env::args().collect();
        assert_eq!(cmdline, format!("{} ", args.join(" ")));
        assert!(is_alive(pid, ""));
        assert!(is_alive(pid, &args[0]));
        assert!(!is_alive(pid, "certainly not in the command line"));
    }

    #[test]
    fn proc_stack_of_this_process() {
        let pid = ocaml_unix::getpid();
        // This process and its parent (cargo) are ours; further up, macOS
        // does not show the command lines of other users' processes.
        let stack = get_proc_stack(Some(2), None, pid);
        assert_eq!(stack.len(), 2, "{:?}", stack);
        assert!(!stack[0].starts_with("ERROR"), "{:?}", stack);
        let args: Vec<String> = std::env::args().collect();
        assert_eq!(stack.last().unwrap(), &args.join(" "));
        assert_eq!(get_proc_stack(Some(1), None, pid).len(), 1);
        assert_eq!(
            get_proc_stack(Some(1), Some(3), pid),
            vec![format!("{}...", &args[0][..3])]
        );
        let stat = get_proc_stat(pid).unwrap();
        assert_eq!(stat.ppid, unsafe { libc::getppid() } as isize);
    }

    #[test]
    fn stat_lines() {
        assert_eq!(scan_stat_ppid(b"123 (bash) S 45 1 2 3"), Ok(45));
        assert_eq!(scan_stat_ppid(b"123 (a b) R 7"), Ok(7));
        assert!(scan_stat_ppid(b"123 (a)b) R 7").is_err());
        assert!(scan_stat_ppid(b"x").is_err());
    }

    #[test]
    fn interactive_shells() {
        let s = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert!(is_likely_from_interactive_shell(&s(&["/sbin/init", "-bash", "/usr/local/bin/hh_client"])));
        assert!(is_likely_from_interactive_shell(&s(&[
            "/usr/bin/zsh",
            "/bin/bash /usr/local/bin/hh",
            "/usr/local/bin/hh_client check"
        ])));
        assert!(is_likely_from_interactive_shell(&s(&["/bin/bash --init-file x", "hh"])));
        assert!(!is_likely_from_interactive_shell(&s(&["bash -c hh", "hh"])));
        assert!(!is_likely_from_interactive_shell(&s(&["python3 x.py", "hh_client"])));
        assert!(!is_likely_from_interactive_shell(&s(&["hh_client"])));
        assert!(!is_likely_from_interactive_shell(&s(&["ERROR No 'stat' file"])));
    }

    #[test]
    fn dead_processes() {
        let mut child = std::process::Command::new("true").spawn().unwrap();
        let pid = child.id() as isize;
        child.wait().unwrap();
        assert!(!is_alive(pid, ""));
        let err = get_cmdline(pid).unwrap_err();
        assert!(
            err.starts_with(&format!(
                "No 'cmdline' file found for PID {}: '(Sys_error \"/proc/{}/cmdline: ",
                pid, pid
            )),
            "{}",
            err
        );
        assert!(!is_alive(-1, ""));
        assert!(!is_alive(0, ""));
    }
}
