// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/sys_utils.ml`: the functions that the ported modules
//! need so far (add the others as they are needed). See `hh/PORTING.md`.

use std::io::Read;
use std::io::Seek;
use std::io::SeekFrom;
use std::io::Write;
use std::os::fd::AsRawFd;
use std::sync::LazyLock;

use crate::build_id;
use crate::path;
use crate::rt::ocaml_printf;
use crate::rt::ocaml_unix::LockCommand;
use crate::rt::ocaml_unix::OpenFlag;
use crate::rt::ocaml_unix;
use crate::rt::ocaml_unix::UnixError;
use std::sync::MutexGuard;
use std::sync::Mutex;

pub const NULL_PATH: &str = "/dev/null";

pub const TEMP_DIR_NAME: &str = "/tmp";

/// `external realpath : string -> string option = "hh_realpath"`:
/// `realpath(3)` (`std::fs::canonicalize` is `realpath` on Unix), `None` when
/// it fails. A canonical path that is not valid UTF-8 is `None` too (the
/// OCaml string would be its bytes).
pub fn realpath(path: &str) -> Option<String> {
    std::fs::canonicalize(path)
        .ok()
        .and_then(|path| path.into_os_string().into_string().ok())
}

/// `Sys_error`, the exception of the standard library's system functions,
/// with its message (`"<file>: No such file or directory"`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SysError(pub String);

impl std::fmt::Display for SysError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sys_error({:?})", self.0)
    }
}

impl std::error::Error for SysError {}

impl SysError {
    /// The `Sys_error` of a failed operation on `path`: OCaml's message is
    /// the path and `strerror` (`std::io::Error` adds ` (os error N)`).
    pub fn of_io_error(path: &str, err: &std::io::Error) -> Self {
        let msg = err.to_string();
        let msg = match (err.raw_os_error(), msg.rfind(" (os error ")) {
            (Some(_), Some(i)) => msg[..i].to_string(),
            _ => msg,
        };
        SysError(format!("{}: {}", path, msg))
    }
}

/// `cat` (`Disk.cat`, `Real_disk.cat`): the contents of a file, read in
/// binary (the bytes of the file, as an OCaml string has them). Raises
/// `Sys_error` when the file cannot be read.
pub fn cat(filename: &str) -> Result<Vec<u8>, SysError> {
    std::fs::read(filename).map_err(|err| SysError::of_io_error(filename, &err))
}

/// `exec_read cmd`: the first line that `/bin/sh -c cmd` prints
/// (`Unix.open_process_in`, `In_channel.input_line`: without the `\n`, or
/// `\r\n`), `None` if it prints nothing. As in OCaml, the command must exit
/// with 0 (`assert`: a panic otherwise), and it is waited for once the first
/// line is read and its output closed. (Bytes that are not UTF-8 become
/// U+FFFD.)
pub fn exec_read(cmd: &str) -> Option<String> {
    use std::io::BufRead;
    let mut child = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("Unix.Unix_error: open_process_in {}: {}", cmd, e));
    let result = {
        let mut ic = std::io::BufReader::new(child.stdout.take().expect("piped stdout"));
        let mut line = vec![];
        match ic.read_until(b'\n', &mut line) {
            Ok(0) => None,
            Ok(_) => {
                if line.last() == Some(&b'\n') {
                    line.pop();
                    if line.last() == Some(&b'\r') {
                        line.pop();
                    }
                }
                Some(String::from_utf8_lossy(&line).into_owned())
            }
            Err(e) => panic!("Sys_error: {}", e),
        }
        // `ic` is closed here, before the process is waited for.
    };
    let status = child
        .wait()
        .unwrap_or_else(|e| panic!("Unix.Unix_error: close_process_in {}: {}", cmd, e));
    assert!(status.code() == Some(0), "Assert_failure: exec_read {}", cmd);
    result
}

/// `Sys_utils.touch_mode`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TouchMode {
    /// Can be used on files and folders. This won't open/close fds, which is
    /// important for some callers.
    TouchExisting { follow_symlinks: bool },
    TouchExistingFileOrCreateNew { mkdir_if_new: bool, perm_if_new: u32 },
}

/// `Sys_utils.touch mode file`: sets the access and modification times of
/// `file` to now (`Touch_existing`: of the link itself unless
/// `follow_symlinks`), or creates it with `perm_if_new` (under umask 0, its
/// directory too if `mkdir_if_new`) when it is not there. The error is that
/// of `Unix.utimes` / `lutimes` or of creating the file (OCaml raises
/// `Unix_error` or `Sys_error`).
///
/// The process umask is not changed (it is shared by all threads): a file or
/// directory this creates gets its mode afterwards.
pub fn touch(mode: TouchMode, file: &str) -> std::io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::DirBuilderExt;
    use std::os::unix::fs::OpenOptionsExt;
    use std::os::unix::fs::PermissionsExt;
    match mode {
        TouchMode::TouchExisting { follow_symlinks } => {
            let c = std::ffi::CString::new(std::path::Path::new(file).as_os_str().as_bytes())
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidInput, e))?;
            // SAFETY: `c` is a NUL-terminated path; a null `times` means now.
            let ret = unsafe {
                if follow_symlinks {
                    libc::utimes(c.as_ptr(), std::ptr::null())
                } else {
                    libc::lutimes(c.as_ptr(), std::ptr::null())
                }
            };
            if ret == 0 {
                Ok(())
            } else {
                Err(std::io::Error::last_os_error())
            }
        }
        TouchMode::TouchExistingFileOrCreateNew {
            mkdir_if_new,
            perm_if_new,
        } => {
            if mkdir_if_new {
                // `mkdir_no_fail (Filename.dirname file)` with umask 0.
                let dir = match std::path::Path::new(file).parent() {
                    Some(d) if !d.as_os_str().is_empty() => d.to_path_buf(),
                    _ => std::path::PathBuf::from("."),
                };
                match std::fs::DirBuilder::new().mode(0o777).create(&dir) {
                    Ok(()) => {
                        let _ = std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o777));
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
                    Err(e) => return Err(e),
                }
            }
            // `Out_channel.create ~append:true ~binary:true ~perm:perm_if_new file`
            match std::fs::OpenOptions::new()
                .append(true)
                .create_new(true)
                .mode(perm_if_new)
                .open(file)
            {
                Ok(f) => {
                    let _ = f.set_permissions(std::fs::Permissions::from_mode(perm_if_new));
                    Ok(())
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    std::fs::OpenOptions::new().append(true).open(file).map(|_| ())
                }
                Err(e) => Err(e),
            }
        }
    }
}

/// `mkdir_p` (`Disk.mkdir_p`, `Real_disk.mkdir_p`; added for the file
/// watchers): creates `d` and its missing parents, with mode 0o777 under
/// umask 0. The error of `Unix.mkdir`, or `NotADirectory d` when `d` exists
/// and is not a directory.
pub fn mkdir_p(d: &str) -> std::io::Result<()> {
    if d.is_empty() {
        panic!("Unexpected empty directory, should never happen")
    }
    let path = std::path::Path::new(d);
    if !path.exists() {
        mkdir_p(&crate::path::dirname(&d.to_string()))?;
        // `Unix.mkdir d 0o777` under umask 0: the mode is set afterwards
        // (the umask is shared by all threads).
        use std::os::unix::fs::DirBuilderExt;
        use std::os::unix::fs::PermissionsExt;
        match std::fs::DirBuilder::new().mode(0o777).create(d) {
            Ok(()) => {
                let _ = std::fs::set_permissions(d, std::fs::Permissions::from_mode(0o777));
                Ok(())
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(()),
            Err(e) => Err(e),
        }
    } else if path.is_dir() {
        Ok(())
    } else {
        Err(std::io::Error::new(
            std::io::ErrorKind::NotADirectory,
            format!("Disk_sig.Types.NotADirectory({:?})", d),
        ))
    }
}

/// `rm_dir_tree path` (`Real_disk.rm_dir_tree`): removes
/// `path` and, if it is a directory, everything under it; a path deleted
/// out from under us is no error. Other errors raise (a panic with the
/// `io::Error`), as the OCaml's `Unix_error`.
pub fn rm_dir_tree(path: &str) {
    let res = (|| -> std::io::Result<()> {
        let stats = std::fs::symlink_metadata(path)?;
        if stats.is_dir() {
            for entry in std::fs::read_dir(path)? {
                let name = entry?.file_name();
                rm_dir_tree(&format!("{}/{}", path, name.to_string_lossy()));
            }
            std::fs::remove_dir(path)
        } else {
            std::fs::remove_file(path)
        }
    })();
    match res {
        Ok(()) => {}
        // Path has been deleted out from under us - can ignore it.
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => std::panic::panic_any(e),
    }
}

/// `unlink_no_fail` (added for the file watchers): `Unix.unlink`, except
/// that a missing file is no error.
pub fn unlink_no_fail(fn_: &str) -> std::io::Result<()> {
    match std::fs::remove_file(fn_) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(e),
    }
}

/// `Filename.extension_len`
fn extension_len(name: &[u8]) -> usize {
    fn check(name: &[u8], i0: isize, mut i: isize) -> usize {
        loop {
            if i < 0 || name[i as usize] == b'/' {
                return 0;
            } else if name[i as usize] == b'.' {
                i -= 1;
            } else {
                return name.len() - i0 as usize;
            }
        }
    }
    let mut i = name.len() as isize - 1;
    loop {
        if i < 0 || name[i as usize] == b'/' {
            return 0;
        } else if name[i as usize] == b'.' {
            return check(name, i, i - 1);
        } else {
            i -= 1;
        }
    }
}

/// `splitext` (added for the file watchers): the name without its
/// extension, and the extension without its dot. `Filename.chop_extension`
/// raises `Invalid_argument` on a name without an extension.
pub fn splitext(filename: &str) -> (String, String) {
    let l = extension_len(filename.as_bytes());
    if l == 0 {
        panic!("Invalid_argument: Filename.chop_extension")
    }
    let root = &filename[..filename.len() - l];
    let root_length = root.len();
    // -1 because the extension includes the period, e.g. ".foo"
    let ext = &filename[root_length + 1..];
    (root.to_string(), ext.to_string())
}

/// `make_link_of_timestamped linkname` (added for the file watchers): for
/// `<dir>/<base>.<ext>`, creates the directory `<dir>/<ext>s`, makes
/// `linkname` a symbolic link to `<dir>/<ext>s/<base>-<YYYY-MM-DD-HH-MM-SS>.<ext>`
/// (local time) and returns that file name (the file is not created).
pub fn make_link_of_timestamped(linkname: &str) -> std::io::Result<String> {
    // `Filename.concat`
    fn concat(dirname: &str, filename: &str) -> String {
        if dirname.is_empty() || dirname.ends_with('/') {
            format!("{}{}", dirname, filename)
        } else {
            format!("{}/{}", dirname, filename)
        }
    }
    let dir = crate::path::dirname(&linkname.to_string());
    mkdir_p(&dir)?;
    let base = crate::path::basename(&linkname.to_string());
    let (base, ext) = splitext(&base);
    let dir = concat(&dir, &format!("{}s", ext));
    mkdir_p(&dir)?;
    // `localtime (time ())`
    let tm = crate::rt::ocaml_unix::localtime(crate::rt::ocaml_unix::time());
    let year = tm.tm_year + 1900;
    let time_str = format!(
        "{}-{:02}-{:02}-{:02}-{:02}-{:02}",
        year,
        tm.tm_mon + 1,
        tm.tm_mday,
        tm.tm_hour,
        tm.tm_min,
        tm.tm_sec
    );
    let filename = concat(&dir, &format!("{}-{}.{}", base, time_str, ext));
    unlink_no_fail(linkname)?;
    std::os::unix::fs::symlink(&filename, linkname)?;
    Ok(filename)
}

/// `Sys_utils.nbr_procs`: the number of processors online.
pub fn nbr_procs() -> isize {
    // (`nproc ()` of `sys_utils_stubs.c`: `sysconf(_SC_NPROCESSORS_ONLN)`.)
    let n = unsafe { libc::sysconf(libc::_SC_NPROCESSORS_ONLN) };
    if n < 1 { 1 } else { n as isize }
}

/// `sysinfo` (the fields the ported modules read; in bytes)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Sysinfo {
    pub freeram: isize,
    pub totalswap: isize,
    pub freeswap: isize,
}

/// `external sysinfo : unit -> sysinfo option = "hh_sysinfo"`: `sysinfo(2)`
/// on Linux, `None` elsewhere.
pub fn sysinfo() -> Option<Sysinfo> {
    #[cfg(target_os = "linux")]
    {
        let mut info: libc::sysinfo = unsafe { std::mem::zeroed() };
        // (`caml_failwith "Failed to sysinfo()"`: the call does not fail
        // with a valid pointer.)
        if unsafe { libc::sysinfo(&mut info) } != 0 {
            return None;
        }
        let unit = info.mem_unit as isize;
        Some(Sysinfo {
            freeram: info.freeram as isize * unit,
            totalswap: info.totalswap as isize * unit,
            freeswap: info.freeswap as isize * unit,
        })
    }
    #[cfg(not(target_os = "linux"))]
    None
}

/// `Sys_utils.is_nfs`: whether `path` is on NFS (or SMB/CIFS).
pub fn is_nfs(path: &str) -> bool {
    let Ok(c) = std::ffi::CString::new(path) else {
        return false;
    };
    // SAFETY: `buf` is written by `statfs` before it is read.
    unsafe {
        let mut buf: libc::statfs = std::mem::zeroed();
        if libc::statfs(c.as_ptr(), &mut buf) != 0 {
            panic!("Failure: statfs failed");
        }
        #[cfg(target_os = "linux")]
        {
            const NFS_SUPER_MAGIC: i64 = 0x6969;
            const SMB_SUPER_MAGIC: i64 = 0x517B;
            const CIFS_MAGIC_NUMBER: i64 = 0xFF534D42;
            matches!(
                buf.f_type as i64,
                NFS_SUPER_MAGIC | SMB_SUPER_MAGIC | CIFS_MAGIC_NUMBER
            )
        }
        #[cfg(not(target_os = "linux"))]
        {
            let name = std::ffi::CStr::from_ptr(buf.f_fstypename.as_ptr()).to_string_lossy();
            matches!(&*name, "nfs" | "smbfs" | "cifs")
        }
    }
}

/// `Sys_utils.set_priorities ~cpu_priority ~io_priority`
pub fn set_priorities(cpu_priority: isize, io_priority: isize) {
    // No need to check the return value, if we failed then whatever.
    #[cfg(target_os = "linux")]
    // SAFETY: `ioprio_set` takes three integers.
    unsafe {
        const IOPRIO_WHO_PROCESS: libc::c_long = 1;
        const IOPRIO_CLASS_BE: libc::c_long = 2;
        const IOPRIO_CLASS_SHIFT: libc::c_long = 13;
        libc::syscall(
            libc::SYS_ioprio_set,
            IOPRIO_WHO_PROCESS,
            libc::getpid() as libc::c_long,
            (IOPRIO_CLASS_BE << IOPRIO_CLASS_SHIFT) | io_priority as libc::c_long,
        );
    }
    #[cfg(not(target_os = "linux"))]
    let _ = io_priority;
    // SAFETY: `nice` takes an integer.
    unsafe {
        libc::nice(cpu_priority as libc::c_int);
    }
}

/// `Sys_utils.mkdir_no_fail dir`: `Unix.mkdir dir 0o777` under umask 0; a
/// directory that exists already is fine, any other error is raised.
pub fn mkdir_no_fail(dir: &str) -> std::io::Result<()> {
    match ocaml_unix::mkdir_with_umask(dir, 0o777, 0) {
        Err(e) if e.raw_os_error() == Some(libc::EEXIST) => Ok(()),
        res => res,
    }
}

/// `Sys_utils.get_env`
pub fn get_env(name: &str) -> Option<String> {
    std::env::var_os(name).map(|s| s.to_string_lossy().into_owned())
}

/// `Sys_utils.getenv_user`
pub fn getenv_user() -> Option<String> {
    let user_var = "USER";
    let logname_var = "LOGNAME";
    let user = get_env(user_var);
    let logname = get_env(logname_var);
    user.or(logname)
}

/// `Sys_utils.exec_try_read cmd`: the first line that `/bin/sh -c cmd`
/// prints (`In_channel.input_line`, without its `\n` or `\r\n`), if it
/// prints one and exits with 0.
pub fn exec_try_read(cmd: &str) -> Option<String> {
    use std::io::BufRead;
    let mut child = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("Unix.Unix_error: open_process_in {}: {}", cmd, e));
    let out = {
        let mut ic = std::io::BufReader::new(child.stdout.take().expect("piped stdout"));
        let mut line = vec![];
        match ic.read_until(b'\n', &mut line) {
            Ok(0) => None,
            Ok(_) => {
                if line.last() == Some(&b'\n') {
                    line.pop();
                    if line.last() == Some(&b'\r') {
                        line.pop();
                    }
                }
                Some(String::from_utf8_lossy(&line).into_owned())
            }
            Err(e) => panic!("Sys_error: {}", e),
        }
    };
    let status = child
        .wait()
        .unwrap_or_else(|e| panic!("Unix.Unix_error: close_process_in {}: {}", cmd, e));
    match (out, status.code()) {
        (Some(out), Some(0)) => Some(out),
        _ => None,
    }
}

/// `Sys_utils.logname_impl`
pub fn logname_impl() -> String {
    match getenv_user() {
        Some(user) => user,
        // `Utils.unsafe_opt` raises `Invalid_argument` on `None`, which is
        // caught to try the next command.
        None => match exec_try_read("logname") {
            Some(logname) => logname,
            None => match exec_try_read("id -un") {
                Some(logname) => logname,
                None => "[unknown]".to_string(),
            },
        },
    }
}

/// `Sys_utils.logname ()`: computed once (`Lazy.force logname_lazy`).
pub fn logname() -> String {
    static LOGNAME_LAZY: LazyLock<String> = LazyLock::new(logname_impl);
    LOGNAME_LAZY.clone()
}

/// `Sys_utils.get_primary_owner`: the `Sys_error` of reading the owners
/// file is the `Err`.
pub fn get_primary_owner() -> Result<String, SysError> {
    let owners_file = "/etc/devserver.owners";
    let logged_in_user = logname();
    if !path::file_exists(&owners_file.to_string()) {
        Ok(logged_in_user)
    } else {
        let contents = cat(owners_file)?;
        let lines = crate::rt::ocaml_string::split_lines(&String::from_utf8_lossy(&contents));
        if lines.contains(&logged_in_user) {
            Ok(logged_in_user)
        } else {
            Ok(lines.last().cloned().unwrap_or(logged_in_user))
        }
    }
}

/// `Sys_utils.prod_telemetry`
pub fn prod_telemetry() -> bool {
    match std::env::var_os("HH_TEST_MODE") {
        Some(v) if v == "0" => true,
        Some(_) => false,
        None => !build_id::is_dev_build(),
    }
}

/// `Sys_utils.deterministic_behavior_for_tests`
pub fn deterministic_behavior_for_tests() -> bool {
    !prod_telemetry()
}

/// `Sys_utils.executable_path ()`: the real path of the running program.
pub fn executable_path() -> String {
    let exe = crate::path::executable_name();
    realpath(&exe).unwrap_or(exe)
}

/// The exceptions that `Sys_utils.protected_read_exn` and
/// `protected_write_exn` raise, as `Printexc.to_string` shows them.
pub enum ProtectedIoError {
    /// `Unix.Unix_error (err, fun_name, arg)`
    UnixError(std::io::Error, &'static str, String),
    /// `End_of_file`
    EndOfFile,
    /// `Failure msg`
    Failure(String),
}

impl std::fmt::Debug for ProtectedIoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProtectedIoError::UnixError(err, fun_name, arg) => {
                f.write_str(&ocaml_unix::unix_error_to_string(err, fun_name, arg))
            }
            ProtectedIoError::EndOfFile => f.write_str("End_of_file"),
            ProtectedIoError::Failure(msg) => write!(f, "Failure({})", ocaml_printf::sprintf_s(msg)),
        }
    }
}

/// The `lockf` locks of `protected_read_exn` and `protected_write_exn` are
/// POSIX record locks, held by a process: they keep a reader from seeing a
/// writer of another process half-way (the monitor and the server were two
/// processes), but not two threads of this one. This mutex does that between
/// threads; it is taken for one locked read or one write, and not held while
/// a reader waits for an empty file to be written.
pub fn protected_io_between_threads() -> MutexGuard<'static, ()> {
    static PROTECTED_IO: Mutex<()> = Mutex::new(());
    PROTECTED_IO.lock().unwrap_or_else(|e| e.into_inner())
}

/// `Sys_utils.protected_read_exn filename`: the contents of the file, read
/// under a shared (reader) lock on the whole file. An empty file is read
/// again after 1ms, for as long as it stays empty (Unix has no way to
/// atomically create a file and lock it, so the writer may have created it
/// without having written it yet).
pub fn protected_read_exn(filename: &str) -> Result<String, ProtectedIoError> {
    // TODO(ljw): this function is vulnerable to EINTR. Although we only hit it about once a month.
    // TODO(ljw): we should use atomic-create for this!

    // We can't use the standard Disk.cat because we need to read from an existing (locked)
    // fd for the file; not open the file a second time and read from that.
    let cat_from_fd = |fd: &mut std::fs::File| -> Result<Vec<u8>, ProtectedIoError> {
        let unix_error = |e| ProtectedIoError::UnixError(e, "lseek", String::new());
        let total = fd.seek(SeekFrom::End(0)).map_err(unix_error)? as usize;
        let _0 = fd.seek(SeekFrom::Start(0)).map_err(unix_error)?;
        let mut buf = vec![0u8; total];
        let mut offset = 0;
        while offset != total {
            let bytes_read = fd
                .read(&mut buf[offset..])
                .map_err(|e| ProtectedIoError::UnixError(e, "read", String::new()))?;
            if bytes_read == 0 {
                return Err(ProtectedIoError::EndOfFile);
            }
            offset += bytes_read
        }
        Ok(buf)
    };
    loop {
        let content = {
            let _between_threads = protected_io_between_threads();
            let mut fd =
                ocaml_unix::openfile_with_umask(filename, &[OpenFlag::ORdonly], 0o666, 0)
                    .map_err(|e| ProtectedIoError::UnixError(e, "open", filename.to_string()))?;
            // try_finally ~finally:(Unix.close fd): the file is closed when
            // `fd` is dropped.
            ocaml_unix::lockf(fd.as_raw_fd(), LockCommand::FRlock, 0)
                .map_err(|e| ProtectedIoError::UnixError(e, "lockf", String::new()))?;
            let content = cat_from_fd(&mut fd)?;
            drop(fd);
            content
        };
        if content.is_empty() {
            std::thread::sleep(std::time::Duration::from_secs_f64(0.001));
        } else {
            // An OCaml string holds any bytes; bytes that are not UTF-8
            // become U+FFFD here.
            return Ok(String::from_utf8_lossy(&content).into_owned());
        }
    }
}

/// `Sys_utils.protected_write_exn filename content`: under umask `0o000`
/// (mode `0o666` if it is created), opens the file, takes an exclusive lock
/// on all of it, writes `content` from the start and truncates it there.
pub fn protected_write_exn(filename: &str, content: &str) -> Result<(), ProtectedIoError> {
    if content.is_empty() {
        return Err(ProtectedIoError::Failure(
            "Empty content not supported.".to_string(),
        ));
    }
    let _between_threads = protected_io_between_threads();
    let mut fd = ocaml_unix::openfile_with_umask(
        filename,
        &[OpenFlag::ORdwr, OpenFlag::OCreat],
        0o666,
        0o000,
    )
    .map_err(|e| ProtectedIoError::UnixError(e, "open", filename.to_string()))?;
    // try_finally ~finally:(Unix.close fd): the file is closed when `fd` is
    // dropped.
    ocaml_unix::lockf(fd.as_raw_fd(), LockCommand::FLock, 0)
        .map_err(|e| ProtectedIoError::UnixError(e, "lockf", String::new()))?;
    let _written = fd
        .write_all(content.as_bytes())
        .map_err(|e| ProtectedIoError::UnixError(e, "write", String::new()))?;
    fd.set_len(content.len() as u64)
        .map_err(|e| ProtectedIoError::UnixError(e, "ftruncate", String::new()))?;
    Ok(())
}

/// `Sys_utils.restart_on_EINTR`
pub fn restart_on_eintr<A>(mut f: impl FnMut() -> std::io::Result<A>) -> std::io::Result<A> {
    loop {
        match f() {
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            r => return r,
        }
    }
}

/// `Sys_utils.show_inode fd`: `inode#<st_dev>:<st_ino>`.
pub fn show_inode(fd: &std::fs::File) -> String {
    use std::os::unix::fs::MetadataExt;
    match fd.metadata() {
        // `st_dev` is an `int` of OCaml: a 32-bit `dev_t` on macOS, so
        // sign-extended there.
        #[cfg(target_os = "macos")]
        Ok(stat) => format!("inode#{}:{}", stat.dev() as i32, stat.ino()),
        #[cfg(not(target_os = "macos"))]
        Ok(stat) => format!("inode#{}:{}", stat.dev() as i64, stat.ino()),
        Err(e) => panic!("{}", UnixError(e, "fstat", String::new())),
    }
}

/// `Sys_utils.with_lock fd lock_command ~f`: takes the lock on the whole
/// file (`lockf` from offset 0, length 0, the file position being put back
/// after), runs `f`, then unlocks, whatever `f` did.
///
/// `lockf` locks belong to a process, so they keep another process (a
/// client) from seeing a message half-written, but not another thread of
/// this one: the mutex does that.
pub fn with_lock<A>(
    fd: &std::fs::File,
    lock_command: LockCommand,
    f: impl FnOnce() -> Result<A, UnixError>,
) -> Result<A, UnixError> {
    static BETWEEN_THREADS: Mutex<()> = Mutex::new(());
    let _between_threads = BETWEEN_THREADS.lock().unwrap_or_else(|e| e.into_inner());
    // helper function to set current file position to 0, then do "f",
    // then restore it to what it was before
    let with_pos0 = |f: &mut dyn FnMut() -> Result<(), UnixError>| -> Result<(), UnixError> {
        let pos = ocaml_unix::lseek(fd, 0, libc::SEEK_CUR)?;
        let _ = ocaml_unix::lseek(fd, 0, libc::SEEK_SET)?;
        f()?;
        let _ = ocaml_unix::lseek(fd, pos, libc::SEEK_SET)?;
        Ok(())
    };
    let lockf = |cmd: LockCommand| {
        restart_on_eintr(|| ocaml_unix::lockf(fd.as_raw_fd(), cmd, 0))
            .map_err(|e| UnixError(e, "lockf", String::new()))
    };
    // lockf is applied starting at the file-descriptors current position.
    // We use "with_pos0" so that when we acquire or release the lock,
    // we're locking from the start of the file through to (len=0) the end.
    with_pos0(&mut || lockf(lock_command))?;
    // finally (also when `f` panics, as `Utils.try_finally` runs it on an
    // exception)
    struct Unlock<'a>(&'a dyn Fn() -> Result<(), UnixError>);
    impl Drop for Unlock<'_> {
        fn drop(&mut self) {
            if std::thread::panicking() {
                let _ = (self.0)();
            }
        }
    }
    let unlock = || with_pos0(&mut || lockf(LockCommand::FUlock));
    let guard = Unlock(&unlock);
    let result = f();
    std::mem::forget(guard);
    let unlocked = unlock();
    let result = result?;
    unlocked?;
    Ok(result)
}

/// `Sys_utils.write_non_intr fd buf pos len`
pub fn write_non_intr(mut fd: &std::fs::File, buf: &[u8]) -> Result<(), UnixError> {
    let mut pos = 0;
    while pos < buf.len() {
        // must use Unix.single_write, not Unix.write, because the latter does arbitrarily
        // many OS calls and we don't know which one got the EINTR
        let n = restart_on_eintr(|| fd.write(&buf[pos..]))
            .map_err(|e| UnixError(e, "single_write", String::new()))?;
        pos += n;
    }
    Ok(())
}

/// `Sys_utils.read_non_intr fd len`: `None` if the end of the file comes
/// first (what was read before it is consumed).
pub fn read_non_intr(mut fd: &std::fs::File, len: usize) -> Result<Option<Vec<u8>>, UnixError> {
    let mut buf = vec![0u8; len];
    let mut pos = 0;
    let mut is_eof = false;
    while pos < len && !is_eof {
        let n = restart_on_eintr(|| fd.read(&mut buf[pos..]))
            .map_err(|e| UnixError(e, "read", String::new()))?;
        pos += n;
        if n == 0 {
            is_eof = true;
        }
    }
    Ok(if is_eof { None } else { Some(buf) })
}

/// `Sys_utils.atomically_create_and_init_file path ~rd ~wr file_perm ~init`:
/// a new file at `path`, made by `init` before anyone can see it, or `None`
/// if `path` already exists.
///
/// OCaml opens an unnamed file in the directory (`O_TMPFILE`), runs `init`,
/// then links it to `path` (`linkat` of `/proc/self/fd/<fd>`, which fails
/// with `EEXIST` if `path` exists). That is what this does on Linux. macOS
/// has neither `O_TMPFILE` nor `/proc` (the OCaml raises `Unix_error
/// (ENOSYS, "hh_open_tmpfile", dir)` there, so the OCaml server cannot
/// stream errors on macOS): there the unnamed file is a file of a unique
/// name in the same directory (`.<name>.tmp.<pid>.<n>`), linked to `path`
/// then unlinked, which gives a client the same guarantee (`path` appears
/// with its contents already written, or not at all).
pub fn atomically_create_and_init_file(
    path: &str,
    rd: bool,
    wr: bool,
    file_perm: u32,
    init: impl FnOnce(&std::fs::File) -> Result<(), UnixError>,
) -> Result<Option<std::fs::File>, UnixError> {
    use std::os::fd::FromRawFd;
    let dir = crate::rt::ocaml_filename::dirname(path);
    let access = match (rd, wr) {
        (true, true) => libc::O_RDWR,
        (true, false) => libc::O_RDONLY,
        (false, true) => libc::O_WRONLY,
        (false, false) => 0,
    };
    let c = |s: &str| std::ffi::CString::new(s).map_err(|_| {
        UnixError(std::io::Error::from_raw_os_error(libc::ENOENT), "open", s.to_string())
    });
    #[cfg(target_os = "linux")]
    let (fd, link) = {
        let cdir = c(&dir)?;
        // SAFETY: `open` of a NUL-terminated path.
        let fd = unsafe { libc::open(cdir.as_ptr(), libc::O_TMPFILE | access | libc::O_CLOEXEC, file_perm) };
        if fd == -1 {
            return Err(UnixError(std::io::Error::last_os_error(), "hh_open_tmpfile", dir));
        }
        // SAFETY: `fd` was just opened and is owned by nobody else.
        let fd = unsafe { std::fs::File::from_raw_fd(fd) };
        let link = |fd: &std::fs::File| -> std::io::Result<()> {
            let src = c(&format!("/proc/self/fd/{}", fd.as_raw_fd())).map_err(|e| e.0)?;
            let dst = c(path).map_err(|e| e.0)?;
            // SAFETY: two NUL-terminated paths.
            let r = unsafe {
                libc::linkat(libc::AT_FDCWD, src.as_ptr(), libc::AT_FDCWD, dst.as_ptr(), libc::AT_SYMLINK_FOLLOW)
            };
            if r == -1 { Err(std::io::Error::last_os_error()) } else { Ok(()) }
        };
        (fd, link)
    };
    #[cfg(not(target_os = "linux"))]
    let (fd, link, tmp) = {
        static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let tmp = format!(
            "{}/.{}.tmp.{}.{}",
            dir,
            crate::rt::ocaml_filename::basename(path),
            ocaml_unix::getpid(),
            COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        let ctmp = c(&tmp)?;
        // SAFETY: `open` of a NUL-terminated path.
        let fd = unsafe {
            libc::open(
                ctmp.as_ptr(),
                libc::O_CREAT | libc::O_EXCL | access | libc::O_CLOEXEC,
                file_perm as libc::c_uint,
            )
        };
        if fd == -1 {
            return Err(UnixError(std::io::Error::last_os_error(), "hh_open_tmpfile", dir));
        }
        // SAFETY: `fd` was just opened and is owned by nobody else.
        let fd = unsafe { std::fs::File::from_raw_fd(fd) };
        let tmp2 = tmp.clone();
        let link = move |_fd: &std::fs::File| -> std::io::Result<()> {
            let r = std::fs::hard_link(&tmp2, path);
            let _ = std::fs::remove_file(&tmp2);
            r
        };
        (fd, link, tmp)
    };
    match init(&fd) {
        Ok(()) => {}
        Err(e) => {
            #[cfg(not(target_os = "linux"))]
            let _ = std::fs::remove_file(&tmp);
            // Unix.close fd; Exception.reraise e
            drop(fd);
            return Err(e);
        }
    }
    // If the user's callback worked, we can proceed to atomically move the file into place.
    // If this fails due to pre-existing, then we'll return None.
    match link(&fd) {
        Ok(()) => Ok(Some(fd)),
        Err(e) if e.raw_os_error() == Some(libc::EEXIST) => {
            drop(fd);
            Ok(None)
        }
        Err(e) => {
            let arg = format!("/proc/self/fd/{}", fd.as_raw_fd());
            drop(fd);
            Err(UnixError(e, "link", arg))
        }
    }
}

/// The exceptions of `exec_read_lines`: `Unix.Unix_error` of starting or
/// waiting for the command, `Assert_failure` when it does not exit with 0.
#[derive(Debug)]
pub enum ExecReadLinesError {
    Unix(UnixError),
    /// `Printexc.to_string` of the `Assert_failure`
    AssertFailure(String),
}

/// `exec_read_lines ?reverse cmd`: the lines that `/bin/sh -c cmd` prints
/// (`In_channel.input_line`), the last first if `reverse`; the command must
/// exit with 0 (`assert`).
pub fn exec_read_lines(reverse: bool, cmd: &str) -> Result<Vec<String>, ExecReadLinesError> {
    use std::io::BufRead;
    let mut child = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(cmd)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| ExecReadLinesError::Unix(UnixError(e, "fork", String::new())))?;
    let mut lines = vec![];
    if let Some(out) = child.stdout.take() {
        for line in std::io::BufReader::new(out).split(b'\n') {
            match line {
                Ok(line) => lines.push(String::from_utf8_lossy(&line).into_owned()),
                Err(_) => break,
            }
        }
    }
    let status = child
        .wait()
        .map_err(|e| ExecReadLinesError::Unix(UnixError(e, "waitpid", String::new())))?;
    if status.code() != Some(0) {
        return Err(ExecReadLinesError::AssertFailure(
            "File \"hack/src/utils/sys/sys_utils.ml\", line 159, characters 2-8: Assertion failed"
                .to_string(),
        ));
    }
    if reverse {
        lines.reverse();
    }
    Ok(lines)
}

/// `Sys_utils.check_dmesg_for_oom pid name`: runs `dmesg`
/// (`exec_read_lines ~reverse:true`, which asserts that it exits with 0:
/// it does not where reading the kernel buffer needs privileges, as on
/// macOS, and then this raises `Assert_failure`).
pub fn check_dmesg_for_oom(pid: i32, name: &str) -> Result<bool, ExecReadLinesError> {
    let dmesg = exec_read_lines(true, "dmesg")?;
    Ok(find_oom_in_dmesg_output(pid, name, &dmesg))
}

/// `Sys_utils.find_oom_in_dmesg_output pid name lines`
pub fn find_oom_in_dmesg_output(pid: i32, name: &str, lines: &[String]) -> bool {
    // oomd: "Memory cgroup out of memory: Killed process 4083583 (hh_server)" (https://facebookmicrosites.github.io/oomd/)
    // oomkiller: "Out of memory: Kill process 4083583 (hh_server)"
    let re = regex::Regex::new(&format!(
        r"[Oo]ut of memory: Kill(ed)? process ([0-9]+) \({}\)",
        regex::escape(name)
    ))
    .unwrap();
    let pid = pid.to_string();
    lines.iter().any(|line| match re.captures(line) {
        Some(caps) => caps[2] == *pid,
        None => false,
    })
}

/// `split_lines` (`Str.split nl_regexp`, `nl_regexp = Str.regexp "[\r\n]"`):
/// the pieces between `\r`s and `\n`s, one at the very start skipped, none
/// after the last.
pub fn split_lines(s: &str) -> Vec<String> {
    let is_nl = |c: char| c == '\r' || c == '\n';
    let mut start = if s.starts_with(is_nl) { 1 } else { 0 };
    let mut pieces = vec![];
    while start < s.len() {
        match s[start..].find(is_nl) {
            None => {
                pieces.push(s[start..].to_string());
                break;
            }
            Some(i) => {
                pieces.push(s[start..start + i].to_string());
                start = start + i + 1;
            }
        }
    }
    pieces
}

/// `parse_path_list paths`: a path `@FILE` stands for the lines of `FILE`.
/// The `Sys_error` of reading `FILE` is raised (a panic).
pub fn parse_path_list(paths: &[String]) -> Vec<String> {
    paths
        .iter()
        .flat_map(|path| {
            if path.starts_with('@') {
                let path = crate::string_utils::lstrip(path, "@");
                match cat(path) {
                    Ok(content) => split_lines(&String::from_utf8_lossy(&content)),
                    Err(e) => panic!("{}", e),
                }
            } else {
                vec![path.clone()]
            }
        })
        .collect()
}

/// `Sys_utils.expanduser`: a leading `~` (or `~user`) is the home directory.
pub fn expanduser(path: &str) -> String {
    match path.strip_prefix('~') {
        None => path.to_string(),
        Some(rest) => {
            let (user, rest) = match rest.find('/') {
                Some(i) => (&rest[..i], &rest[i..]),
                None => (rest, ""),
            };
            let home = if user.is_empty() {
                std::env::var("HOME").ok().or_else(|| home_of_uid(None))
            } else {
                home_of_uid(Some(user))
            };
            match home {
                Some(home) => format!("{}{}", home, rest),
                None => path.to_string(),
            }
        }
    }
}

/// `(Unix.getpwuid (Unix.getuid ())).pw_dir`, or `getpwnam` of `user`.
pub fn home_of_uid(user: Option<&str>) -> Option<String> {
    unsafe {
        let pw = match user {
            None => libc::getpwuid(libc::getuid()),
            Some(user) => {
                let user = std::ffi::CString::new(user).ok()?;
                libc::getpwnam(user.as_ptr())
            }
        };
        if pw.is_null() || (*pw).pw_dir.is_null() {
            None
        } else {
            Some(
                std::ffi::CStr::from_ptr((*pw).pw_dir)
                    .to_string_lossy()
                    .into_owned(),
            )
        }
    }
}

/// `Sys_utils.redirect_stdout_and_stderr_to_file filename`: `freopen
/// filename "w" stdout`, then `dup2 stdout stderr`.
pub fn redirect_stdout_and_stderr_to_file(filename: &str) -> std::io::Result<()> {
    use std::io::Write;
    use std::os::fd::AsRawFd;
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    let f = crate::rt::ocaml_unix::openfile_with_umask(
        filename,
        &[
            crate::rt::ocaml_unix::OpenFlag::OWronly,
            crate::rt::ocaml_unix::OpenFlag::OCreat,
            crate::rt::ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o022,
    )?;
    // SAFETY: `dup2` onto the standard descriptors.
    unsafe {
        if libc::dup2(f.as_raw_fd(), 1) < 0 {
            return Err(std::io::Error::last_os_error());
        }
        if libc::dup2(1, 2) < 0 {
            return Err(std::io::Error::last_os_error());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_lines_as_str_split() {
        assert_eq!(split_lines("a\r\nb\n\nc\n"), vec!["a", "", "b", "", "c"]);
        assert_eq!(split_lines("\na"), vec!["a"]);
        assert_eq!(split_lines(""), Vec::<String>::new());
    }

    #[test]
    fn mkdir_no_fail_raises_other_errors() {
        let err = std::panic::catch_unwind(|| {
            let dir = "/nonexistent/hh_tmp_test/x";
            if let Err(e) = mkdir_no_fail(dir) {
                panic!("{}", crate::rt::ocaml_unix::unix_error_to_string(&e, "mkdir", dir))
            }
        })
        .unwrap_err();
        assert_eq!(
            err.downcast_ref::<String>().unwrap(),
            r#"Unix.Unix_error(Unix.ENOENT, "mkdir", "/nonexistent/hh_tmp_test/x")"#
        );
    }

    #[test]
    fn timestamped_links() {
        assert_eq!(splitext("a/b.c.dfind"), ("a/b.c".to_string(), "dfind".to_string()));
        assert_eq!(splitext("zSa.dfind"), ("zSa".to_string(), "dfind".to_string()));
        let dir = std::env::temp_dir().join(format!("hh_sys_utils_link_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let link = dir.join("x").join("root.dfind");
        let link = link.to_str().unwrap();
        let file = make_link_of_timestamped(link).unwrap();
        let prefix = dir.join("x").join("dfinds").join("root-");
        assert!(file.starts_with(prefix.to_str().unwrap()), "{file}");
        assert!(file.ends_with(".dfind"));
        // `<base>-YYYY-MM-DD-HH-MM-SS.<ext>`
        assert_eq!(file.len(), prefix.to_str().unwrap().len() + 19 + ".dfind".len());
        assert_eq!(std::fs::read_link(link).unwrap().to_str().unwrap(), file);
        // A second link replaces the first.
        make_link_of_timestamped(link).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn cat_of_missing_and_existing_files() {
        assert_eq!(
            cat("/nonexistent/hh_sys_utils_test"),
            Err(SysError(
                "/nonexistent/hh_sys_utils_test: No such file or directory".to_string()
            ))
        );
        let path = std::env::temp_dir().join(format!("hh_sys_utils_cat_{}", std::process::id()));
        std::fs::write(&path, b"a\x00\xffb").unwrap();
        assert_eq!(cat(path.to_str().unwrap()), Ok(b"a\x00\xffb".to_vec()));
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn touch_creates_with_perm() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("hh_sys_utils_touch_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let file = dir.join("f");
        let file = file.to_str().unwrap();
        let create = TouchMode::TouchExistingFileOrCreateNew {
            mkdir_if_new: false,
            perm_if_new: 0o666,
        };
        assert!(touch(create, file).is_err());
        let create = TouchMode::TouchExistingFileOrCreateNew {
            mkdir_if_new: true,
            perm_if_new: 0o666,
        };
        touch(create, file).unwrap();
        let mode = std::fs::metadata(file).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o666);
        std::fs::write(file, b"x").unwrap();
        touch(create, file).unwrap();
        assert_eq!(std::fs::read(file).unwrap(), b"x");
        touch(TouchMode::TouchExisting { follow_symlinks: true }, file).unwrap();
        assert!(touch(TouchMode::TouchExisting { follow_symlinks: false }, "/nonexistent/x").is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn realpath_of_missing_and_existing_paths() {
        assert_eq!(realpath("/nonexistent/hh_sys_utils_test"), None);
        assert_eq!(realpath(""), None);
        let tmp = std::env::temp_dir();
        let canonical = std::fs::canonicalize(&tmp).unwrap();
        assert_eq!(
            realpath(tmp.to_str().unwrap()),
            Some(canonical.to_str().unwrap().to_string())
        );
    }

    #[test]
    fn exec_read_first_line() {
        assert_eq!(exec_read("printf 'a b\\r\\nc\\n'"), Some("a b".to_string()));
        assert_eq!(exec_read("printf 'no newline'"), Some("no newline".to_string()));
        assert_eq!(exec_read("printf '\\n'"), Some("".to_string()));
        assert_eq!(exec_read("true"), None);
    }

    #[test]
    #[should_panic(expected = "Assert_failure: exec_read exit 3")]
    fn exec_read_failing_command() {
        exec_read("exit 3");
    }
}
