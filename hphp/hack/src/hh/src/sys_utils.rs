// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/sys_utils.ml`: the functions that the ported modules
//! need so far (add the others as they are needed). See `hh/PORTING.md`.

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
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as libc::time_t)
        .unwrap_or(0);
    // SAFETY: `localtime_r` writes the broken-down time into `tm`.
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    unsafe {
        libc::localtime_r(&secs, &mut tm);
    }
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

#[cfg(test)]
mod tests {
    use super::*;

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
