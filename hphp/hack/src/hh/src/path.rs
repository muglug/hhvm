// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/path.ml`, all of `path.mli`. See `hh/PORTING.md`.
//!
//! This module is compiled with either feature (`port` or `server`), so it
//! cannot use `crate::rt` (`server` only): the pieces of OCaml's standard
//! library it needs (`Filename.dirname`, `Filename.basename`, `%S`) are
//! private copies of `crate::rt::ocaml_filename` and `crate::rt::ocaml_printf`.

use crate::rt::ocaml_printf::sprintf_s;
use crate::sys_utils;

/// `Path.t`
pub type T = String;

/// Resolves a path (using realpath)
///
/// The advantage of using a path instead of strings is that you
/// don't need to care about symlinks or trailing slashes: each
/// path gets normalized by calling realpath.
///
/// A few things to keep in mind:
/// - paths are always absolute. So the empty string "" becomes
///   the current directory (in absolute)
pub fn make(path: &str) -> T {
    match sys_utils::realpath(path) {
        Some(path) => path,
        // assert false?
        None => path.to_string(),
    }
}

pub fn to_string(path: &T) -> String {
    path.clone()
}

/// [concat p1 p2] returns a path equivalent to [p1 ^ "/" ^ p2].
/// In the resulting path [p1] (resp. [p2]) has all its trailing (resp.
/// leading) "." and "/" removed.
/// eg: concat "a/." ".//b" => "a/b" concat "." "b" => "./b" concat "a" "." =>
/// "a/." concat "a" "/b" => "a/b"
pub fn concat(path: &T, more: &str) -> T {
    make(&filename_concat(path, more))
}

/// `Filename.concat` (OCaml's standard library, on Unix): `dirname ^ "/" ^
/// filename`, without the `/` when `dirname` is empty or already ends with
/// one.
fn filename_concat(dirname: &str, filename: &str) -> String {
    if dirname.is_empty() || dirname.ends_with('/') {
        format!("{dirname}{filename}")
    } else {
        format!("{dirname}/{filename}")
    }
}

// The rest of `path.mli`. The functions of `Stdlib.Sys` that `Path`
// includes and exports (`file_exists`, `is_directory`, `chdir`, `getcwd`,
// `remove`, `executable_name`) are here too. Those that raise `Sys_error` in
// OCaml return it as `sys_utils::SysError`, as `sys_utils::cat` does.

/// `Path.S`
pub mod s {
    use std::cmp::Ordering;

    use crate::format::Formatter;

    pub type T = String;

    /// `pp` (`[@@deriving show]` on a string: `%S`)
    pub fn pp(fmt: &mut Formatter, x: &T) {
        crate::format::pp_print_string(fmt, &super::sprintf_s(x))
    }

    pub fn show(x: &T) -> String {
        super::sprintf_s(x)
    }

    pub fn equal(x: &T, y: &T) -> bool {
        x == y
    }

    /// `String.compare`: byte by byte.
    pub fn compare(x: &T, y: &T) -> Ordering {
        x.as_bytes().cmp(y.as_bytes())
    }

    pub fn to_string(x: &T) -> String {
        x.clone()
    }
}

/// `pp` (`[@@deriving show]`, through `S.pp`): the path as an OCaml string
/// literal.
pub fn pp(fmt: &mut crate::format::Formatter, x: &T) {
    s::pp(fmt, x)
}

/// `show`
pub fn show(x: &T) -> String {
    s::show(x)
}

pub fn dummy_path() -> T {
    String::new()
}

/// `Sys_utils.cat`: the contents of the file, its bytes.
pub fn cat(path: &T) -> Result<Vec<u8>, sys_utils::SysError> {
    sys_utils::cat(path)
}

pub fn equal(x: &T, y: &T) -> bool {
    s::equal(x, y)
}

pub fn compare(x: &T, y: &T) -> std::cmp::Ordering {
    s::compare(x, y)
}

/// `Filename.dirname`
pub fn dirname(path: &T) -> T {
    filename_dirname(path)
}

/// `Filename.basename`
pub fn basename(path: &T) -> String {
    filename_basename(path)
}

// OCaml's standard library (see the module documentation).

/// `Filename.parent_dir_name`
fn filename_parent_dir_name() -> &'static str {
    ".."
}

/// `Filename.basename` on Unix (`generic_basename`): the name without its
/// directory and trailing `/`; `"."` for `""`, `"/"` for a name of `/`s.
fn filename_basename(name: &str) -> String {
    let s = name.as_bytes();
    if s.is_empty() {
        return ".".to_string();
    }
    // find_end
    let mut n = s.len() as isize - 1;
    while n >= 0 && s[n as usize] == b'/' {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_string();
    }
    // find_beg
    let p = (n + 1) as usize;
    while n >= 0 && s[n as usize] != b'/' {
        n -= 1;
    }
    if n < 0 {
        name[..p].to_string()
    } else {
        name[(n + 1) as usize..p].to_string()
    }
}

/// `Filename.dirname` on Unix (`generic_dirname`): the directory part of the
/// name, without trailing `/`; `"."` when there is none, `"/"` at the root.
fn filename_dirname(name: &str) -> String {
    let s = name.as_bytes();
    if s.is_empty() {
        return ".".to_string();
    }
    // trailing_sep
    let mut n = s.len() as isize - 1;
    while n >= 0 && s[n as usize] == b'/' {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_string();
    }
    // base
    while n >= 0 && s[n as usize] != b'/' {
        n -= 1;
    }
    if n < 0 {
        return ".".to_string();
    }
    // intermediate_sep
    while n >= 0 && s[n as usize] == b'/' {
        n -= 1;
    }
    if n < 0 {
        name[..1].to_string()
    } else {
        name[..(n + 1) as usize].to_string()
    }
}

/// Creates a Path without running it through `realpath`. This is unsafe because
/// it doesn't normalize symlinks, trailing slashes, or relative paths. The path
/// you pass here must be absolute, and free of symlinks (including ../).
pub fn make_unsafe(path: &str) -> T {
    path.to_string()
}

/// `Sys.file_exists`: whether `stat` succeeds (following symbolic links).
pub fn file_exists(path: &T) -> bool {
    std::fs::metadata(path).is_ok()
}

/// `Sys.is_directory`: `Sys_error` if there is no file of that name.
pub fn is_directory(path: &T) -> Result<bool, sys_utils::SysError> {
    match std::fs::metadata(path) {
        Ok(m) => Ok(m.is_dir()),
        Err(err) => Err(sys_utils::SysError::of_io_error(path, &err)),
    }
}

/// `Sys.chdir`
pub fn chdir(path: &T) -> Result<(), sys_utils::SysError> {
    std::env::set_current_dir(path).map_err(|err| sys_utils::SysError::of_io_error(path, &err))
}

/// `Sys.getcwd ()`. (`Sys_error` with the message of the error alone, as
/// OCaml's `caml_sys_error NO_ARG`.)
pub fn getcwd() -> Result<T, sys_utils::SysError> {
    match std::env::current_dir() {
        Ok(dir) => Ok(dir.to_string_lossy().into_owned()),
        Err(err) => {
            let sys_error = sys_utils::SysError::of_io_error("", &err);
            Err(sys_utils::SysError(
                sys_error.0.trim_start_matches(": ").to_string(),
            ))
        }
    }
}

/// `Stdlib.output_string`
pub fn output(oc: &mut dyn std::io::Write, path: &T) -> std::io::Result<()> {
    oc.write_all(path.as_bytes())
}

/// `Sys.remove` (`unlink`)
pub fn remove(path: &T) -> Result<(), sys_utils::SysError> {
    std::fs::remove_file(path).map_err(|err| sys_utils::SysError::of_io_error(path, &err))
}

pub fn parent(path: &T) -> Result<T, sys_utils::SysError> {
    if is_directory(path)? {
        Ok(make(&concat(path, filename_parent_dir_name())))
    } else {
        Ok(make(&dirname(path)))
    }
}

/// `Sys.executable_name`: the path of the running executable (computed once,
/// as OCaml does at startup; `argv.(0)` when the system cannot tell).
pub fn executable_name() -> T {
    static EXECUTABLE_NAME: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
        match std::env::current_exe() {
            Ok(exe) => exe.to_string_lossy().into_owned(),
            Err(_) => std::env::args().next().unwrap_or_default(),
        }
    });
    EXECUTABLE_NAME.clone()
}

/// The name of the files of a root under `/tmp/hh_server`: `\` is `zB`, `:`
/// is `zC`, `/` is `zS`, NUL is `z0` and `z` is `zZ`.
pub fn slash_escaped_string_of_path(path: &T) -> String {
    let mut buf = String::with_capacity(path.len());
    for ch in path.chars() {
        match ch {
            '\\' => buf.push_str("zB"),
            ':' => buf.push_str("zC"),
            '/' => buf.push_str("zS"),
            '\x00' => buf.push_str("z0"),
            'z' => buf.push_str("zZ"),
            _ => buf.push(ch),
        }
    }
    buf
}

/// The inverse of [`slash_escaped_string_of_path`] (a `z` followed by
/// anything else stays as it is), then `make`.
pub fn path_of_slash_escaped_string(str: &str) -> T {
    let s = str.as_bytes();
    let length = s.len();
    let mut buf: Vec<u8> = Vec::with_capacity(length);
    let mut i = 0;
    while i < length {
        let replacement = if i < length - 1 && s[i] == b'z' {
            match s[i + 1] {
                b'B' => Some(b'\\'),
                b'C' => Some(b':'),
                b'S' => Some(b'/'),
                b'0' => Some(b'\x00'),
                b'Z' => Some(b'z'),
                _ => None,
            }
        } else {
            None
        };
        let (c, next_i) = match replacement {
            Some(r) => (r, i + 2),
            None => (s[i], i + 1),
        };
        buf.push(c);
        i = next_i;
    }
    // Only ASCII bytes were replaced, by ASCII bytes: still UTF-8.
    make(&String::from_utf8(buf).expect("UTF-8 in, UTF-8 out"))
}

/// `Path.Set` (`Reordered_argument_set (Set.Make (S))`): an `im::OrdSet`, as
/// for every OCaml set the code copies freely (see `crate::s_set`); the
/// functions are those of the collection.
pub mod set {
    pub type T = im::OrdSet<super::T>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slash_escaping() {
        // What `/tmp/hh_server/<esc>.*` and Slack's
        // `bin/claude/hack/lsp_naming_table_util.py` expect: `/` is `zS`,
        // `z` is `zZ`.
        assert_eq!(
            slash_escaped_string_of_path(&"/home/z/www".to_string()),
            "zShomezSzZzSwww"
        );
        assert_eq!(
            slash_escaped_string_of_path(&"C:\\a\x00b".to_string()),
            "CzCzBaz0b"
        );
        assert_eq!(slash_escaped_string_of_path(&"é/ç".to_string()), "ézSç");
        for p in ["/nonexistent/hh_path_test/zz", "/nonexistent/a:b\\c", "/nonexistent/éz"] {
            let p = p.to_string();
            assert_eq!(
                path_of_slash_escaped_string(&slash_escaped_string_of_path(&p)),
                p
            );
        }
        // A `z` that escapes nothing, and one at the end.
        assert_eq!(path_of_slash_escaped_string("zSnonexistentzSzazX"), "/nonexistent/zazX");
        assert_eq!(path_of_slash_escaped_string("zSnonexistentzSz"), "/nonexistent/z");
    }

    #[test]
    fn sys_functions() {
        let tmp = make(std::env::temp_dir().to_str().unwrap());
        assert!(file_exists(&tmp));
        assert_eq!(is_directory(&tmp), Ok(true));
        let missing = "/nonexistent/hh_path_test".to_string();
        assert!(!file_exists(&missing));
        assert_eq!(
            is_directory(&missing),
            Err(sys_utils::SysError(
                "/nonexistent/hh_path_test: No such file or directory".to_string()
            ))
        );
        assert!(parent(&missing).is_err());
        let file = concat(&tmp, &format!("hh_path_test_{}", std::process::id()));
        std::fs::write(&file, "contents").unwrap();
        assert_eq!(cat(&file), Ok(b"contents".to_vec()));
        assert_eq!(parent(&file), Ok(tmp.clone()));
        assert_eq!(dirname(&file), tmp);
        assert_eq!(parent(&concat(&tmp, "")), Ok(make(&dirname(&tmp))));
        remove(&file).unwrap();
        assert!(remove(&file).is_err());
        assert!(getcwd().is_ok());
        assert!(!executable_name().is_empty());
        let mut out = vec![];
        output(&mut out, &"/a/b".to_string()).unwrap();
        assert_eq!(out, b"/a/b");
    }

    #[test]
    fn show_and_compare() {
        assert_eq!(show(&"/a/\"b\"".to_string()), r#""/a/\"b\"""#);
        assert_eq!(compare(&"a".to_string(), &"b".to_string()), std::cmp::Ordering::Less);
        assert!(equal(&dummy_path(), &make_unsafe("")));
        assert_eq!(basename(&"/a/b/".to_string()), "b");
        assert_eq!(s::to_string(&"x".to_string()), "x");
    }

    #[test]
    fn filename_functions_as_ocaml() {
        for (name, dir, base) in [
            ("", ".", "."),
            ("/", "/", "/"),
            ("//", "/", "/"),
            ("a", ".", "a"),
            ("/a", "/", "a"),
            ("a/b", "a", "b"),
            ("a//b", "a", "b"),
            ("/a/b/", "/a", "b"),
            ("//a", "/", "a"),
            ("été/ça", "été", "ça"),
        ] {
            assert_eq!(filename_dirname(name), dir, "dirname {name:?}");
            assert_eq!(filename_basename(name), base, "basename {name:?}");
        }
        assert_eq!(sprintf_s("a\"b\\c\n\t\r\x08"), r#""a\"b\\c\n\t\r\b""#);
        assert_eq!(sprintf_s("\x01\u{e9}~"), "\"\\001\\195\\169~\"");
    }

    #[test]
    fn concat_and_make() {
        assert_eq!(filename_concat("a", "b"), "a/b");
        assert_eq!(filename_concat("a/", "b"), "a/b");
        assert_eq!(filename_concat("", "b"), "b");
        // A path that does not exist is kept as it is.
        assert_eq!(
            concat(&"/nonexistent/dir".to_string(), "f.sqlite3"),
            "/nonexistent/dir/f.sqlite3"
        );
        // One that exists is resolved.
        let tmp = std::env::temp_dir();
        let canonical = std::fs::canonicalize(&tmp).unwrap();
        assert_eq!(make(tmp.to_str().unwrap()), canonical.to_str().unwrap());
        assert_eq!(to_string(&make("/nonexistent")), "/nonexistent");
    }
}
