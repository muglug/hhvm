// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `socket/socket.ml`. See `hh/PORTING.md`.
//!
//! Ported in full by the client-connection assignment (D1): the client finds
//! the server's socket with [`make_valid_socket_path`], and the server end of
//! the protocol (`crate::rt::protocol`) binds it with [`init_unix_socket`].
//! The path is a contract (design 5.5): `Server_files.socket_file`, made to
//! fit in a `sockaddr_un`.
//!
//! `Sys_utils.with_umask 0o111 (fun () -> ... Unix.bind ...)` does not change
//! the umask of this (multi-threaded) process: the socket file is given the
//! mode that umask would give (`0o666`) after `bind`. `Opaque_digest` (OCaml's
//! `Digest`) is MD5. `Sys_utils.mkdir_no_fail` and `Sys_utils.temp_dir_name`
//! are not in `crate::sys_utils` yet: they are transliterated below, private,
//! and should move there.

#![allow(non_upper_case_globals)]

use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;

use crate::exit;
use crate::exit_status;
use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_unix;

/// `Sys_utils.temp_dir_name`
const temp_dir_name: &str = "/tmp";

/// `Sys_utils.mkdir_no_fail dir`: `Unix.mkdir dir 0o777` under umask 0; a
/// directory that exists already is fine, any other error is raised.
fn mkdir_no_fail(dir: &str) -> std::io::Result<()> {
    match ocaml_unix::mkdir_with_umask(dir, 0o777, 0) {
        Err(e) if e.raw_os_error() == Some(libc::EEXIST) => Ok(()),
        res => res,
    }
}

/// Initializes the unix domain socket
///
/// (`SO_REUSEADDR` means nothing to a Unix socket; the listener is
/// close-on-exec, as `std` makes every descriptor. The backlog is 10.)
pub fn unix_socket(sock_name: &str) -> UnixListener {
    let res = (|| -> std::io::Result<UnixListener> {
        mkdir_no_fail(&ocaml_filename::dirname(sock_name))?;
        if std::path::Path::new(sock_name).exists() {
            // `Sys.remove` raises `Sys_error`, which the `with` does not
            // catch.
            if let Err(e) = std::fs::remove_file(sock_name) {
                panic!("Sys_error(\"{}: {}\")", sock_name, unix_error_message(&e));
            }
        }
        let sock = bind_with_backlog(sock_name, 10)?;
        // `with_umask 0o111`
        std::fs::set_permissions(sock_name, std::fs::Permissions::from_mode(0o666))?;
        Ok(sock)
    })();
    match res {
        Ok(sock) => sock,
        Err(err) => {
            eprint!("{}\n", unix_error_message(&err));
            exit::exit(None, None, None, exit_status::T::SocketError)
        }
    }
}

/// `Unix.socket PF_UNIX SOCK_STREAM 0`, `bind`, `listen sock backlog`.
fn bind_with_backlog(sock_name: &str, backlog: i32) -> std::io::Result<UnixListener> {
    use std::os::fd::FromRawFd;
    // Fails (`EINVAL`-like) on a path that does not fit a `sockaddr_un`.
    let _addr = std::os::unix::net::SocketAddr::from_pathname(sock_name)?;
    let c_path = std::ffi::CString::new(sock_name)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidInput, e))?;
    // SAFETY: plain socket calls on a descriptor we own; `sockaddr_un` is
    // zeroed and filled within its bounds (`from_pathname` checked the
    // length).
    unsafe {
        let fd = libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0);
        if fd < 0 {
            return Err(std::io::Error::last_os_error());
        }
        let listener = UnixListener::from_raw_fd(fd);
        if libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) < 0 {
            return Err(std::io::Error::last_os_error());
        }
        let mut sun: libc::sockaddr_un = std::mem::zeroed();
        sun.sun_family = libc::AF_UNIX as libc::sa_family_t;
        let bytes = c_path.as_bytes_with_nul();
        for (i, b) in bytes.iter().enumerate() {
            sun.sun_path[i] = *b as libc::c_char;
        }
        let len = (std::mem::size_of::<libc::sa_family_t>() + bytes.len()) as libc::socklen_t;
        if libc::bind(fd, &sun as *const _ as *const libc::sockaddr, len) < 0 {
            return Err(std::io::Error::last_os_error());
        }
        if libc::listen(fd, backlog) < 0 {
            return Err(std::io::Error::last_os_error());
        }
        Ok(listener)
    }
}

/// `Unix.error_message`: `strerror` of the error.
fn unix_error_message(err: &std::io::Error) -> String {
    match err.raw_os_error() {
        Some(code) => {
            // SAFETY: `strerror` returns a valid C string for any code.
            let s = unsafe { std::ffi::CStr::from_ptr(libc::strerror(code)) };
            s.to_string_lossy().into_owned()
        }
        None => err.to_string(),
    }
}

/// The sockaddr_un structure puts a strict limit on the length of a socket
/// address. This is 108 chars on Linux.
pub const max_addr_length: usize = 103;

pub const min_name_length: usize = 17;

/// `Filename.chop_extension`: the name without its extension (from the last
/// `.` of the base name); `Invalid_argument "Filename.chop_extension"` if
/// there is none.
fn chop_extension(name: &str) -> &str {
    let base_start = name.rfind('/').map_or(0, |i| i + 1);
    match name[base_start..].rfind('.') {
        Some(i) => &name[..base_start + i],
        None => panic!("Invalid_argument: Filename.chop_extension"),
    }
}

/// `Opaque_digest.to_hex (Opaque_digest.string s)`: MD5, in lowercase hex.
fn digest_to_hex(s: &str) -> String {
    use md5::Digest;
    let digest = md5::Md5::digest(s.as_bytes());
    digest.iter().map(|b| format!("{:02x}", b)).collect()
}

pub fn make_valid_socket_path(path: &str) -> String {
    // Path will resolve the realpath, in case two processes are referring to the
    // same socket using different paths (like with symlinks
    let path = path::to_string(&path::make(path));
    let dir = format!("{}/", ocaml_filename::dirname(&path));
    let filename = ocaml_filename::basename(&path);
    let root_part = chop_extension(&filename).to_string();
    let root_length = root_part.len();
    let extension_length = filename.len() - root_length;
    let extension = filename[root_length..].to_string();
    // It's possible that the directory path is too long. If so, let's give up and
    // use /tmp/
    let dir = if dir.len() > max_addr_length - min_name_length {
        temp_dir_name.to_string()
    } else {
        dir
    };
    let max_root_part_length = max_addr_length as isize - dir.len() as isize - extension_length as isize;
    let root_part = if root_length as isize > max_root_part_length {
        let len = root_part.len();
        let prefix = &root_part[0..5];
        let suffix = &root_part[len - 5..];
        let digest = digest_to_hex(&root_part);
        // 5 char prefix + 5 char suffix + 2 periods
        let max_digest_length = max_root_part_length - 12;
        let digest_part = if digest.len() as isize > max_digest_length {
            // `String.sub digest 0 max_digest_length` raises on a negative
            // length.
            if max_digest_length < 0 {
                panic!("Invalid_argument: String.sub / Bytes.sub");
            }
            digest[0..max_digest_length as usize].to_string()
        } else {
            digest
        };
        format!("{}.{}.{}", prefix, digest_part, suffix)
    } else {
        root_part
    };
    ocaml_filename::concat(&dir, &format!("{}{}", root_part, extension))
}

pub fn init_unix_socket(socket_file: &str) -> UnixListener {
    unix_socket(&make_valid_socket_path(socket_file))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_paths_are_kept() {
        assert_eq!(
            make_valid_socket_path("/nonexistent/hh/zSwww.sock"),
            "/nonexistent/hh/zSwww.sock"
        );
    }

    #[test]
    fn long_names_are_digested() {
        let long = "zS".to_string() + &"a".repeat(120);
        let p = make_valid_socket_path(&format!("/nonexistent/hh/{}.sock", long));
        // The whole digest fits (32 hex digits, at most 103 - 16 - 5 - 12).
        let digest = digest_to_hex(&long);
        assert_eq!(p, format!("/nonexistent/hh/zSaaa.{}.aaaaa.sock", digest));
        assert!(p.len() <= max_addr_length);
        // A directory that leaves less room: the digest is cut.
        let dir = "/nonexistent/".to_string() + &"d".repeat(60);
        let p = make_valid_socket_path(&format!("{}/{}.sock", dir, long));
        assert_eq!(p.len(), max_addr_length);
        assert!(p.ends_with(&format!(".{}.aaaaa.sock", &digest[0..103 - 74 - 5 - 12])));
        // A directory too long for any name: `/tmp`, as OCaml (which then
        // concatenates without a slash after `/tmp`: `Filename.concat` adds
        // it).
        let dir = "/nonexistent/".to_string() + &"d".repeat(90);
        let p = make_valid_socket_path(&format!("{}/zSx.sock", dir));
        assert_eq!(p, "/tmp/zSx.sock");
    }

    #[test]
    fn digest_is_md5() {
        assert_eq!(digest_to_hex(""), "d41d8cd98f00b204e9800998ecf8427e");
    }

    #[test]
    fn binds_and_accepts() {
        let dir = std::env::temp_dir().join(format!("hh_socket_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        // `mkdir_no_fail` makes the socket's directory, not its parents.
        std::fs::create_dir_all(&dir).unwrap();
        let sock = format!("{}/s/x.sock", dir.to_str().unwrap());
        let listener = init_unix_socket(&sock);
        let path = make_valid_socket_path(&sock);
        let _client = std::os::unix::net::UnixStream::connect(&path).unwrap();
        let (_server, _) = listener.accept().unwrap();
        // Binding again replaces the old socket file.
        drop(listener);
        let _listener = init_unix_socket(&sock);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
