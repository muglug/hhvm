// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `Pcre`, the OCaml binding of PCRE (the `pcre-ocaml` library, which
//! is not in this tree), as far as the typechecker uses it (`Typing_regex`):
//! the compilation of a pattern and the information about its subpatterns.
//! See `hh/PORTING.md`.
//!
//! As `pcre-ocaml`, this calls the C library `libpcre` (PCRE1, 8.x), whose
//! compiler decides which patterns are valid and gives the messages and the
//! offsets of `Pcre.Error (Pcre.BadPattern (msg, offset))`, which end up in
//! error messages (`Bad regex pattern; ... [14]`). The crate is linked with
//! the system `libpcre` (`-lpcre`).
//!
//! An OCaml string is given to the C functions as a C string (`String_val`):
//! it ends at its first NUL byte, here too.
//!
//! Exceptions: `Pcre.Error` is [`Error`], returned in a `Result`;
//! `Invalid_argument` (from `pcre_study` and `get_stringnumber`) is
//! [`InvalidArgument`].

use std::ffi::CStr;
use std::ffi::CString;
use std::ffi::c_char;
use std::ffi::c_int;
use std::ffi::c_uchar;
use std::ffi::c_void;

mod ffi {
    use super::*;

    /// `pcre`, opaque.
    #[repr(C)]
    pub struct Pcre {
        _private: [u8; 0],
    }

    /// `pcre_extra`, opaque here.
    #[repr(C)]
    pub struct PcreExtra {
        _private: [u8; 0],
    }

    pub const PCRE_INFO_CAPTURECOUNT: c_int = 2;
    pub const PCRE_INFO_NAMEENTRYSIZE: c_int = 7;
    pub const PCRE_INFO_NAMECOUNT: c_int = 8;
    pub const PCRE_INFO_NAMETABLE: c_int = 9;
    pub const PCRE_ERROR_NOSUBSTRING: c_int = -7;

    #[link(name = "pcre")]
    unsafe extern "C" {
        pub fn pcre_compile(
            pattern: *const c_char,
            options: c_int,
            errptr: *mut *const c_char,
            erroffset: *mut c_int,
            tableptr: *const c_uchar,
        ) -> *mut Pcre;
        pub fn pcre_study(
            code: *const Pcre,
            options: c_int,
            errptr: *mut *const c_char,
        ) -> *mut PcreExtra;
        pub fn pcre_free_study(extra: *mut PcreExtra);
        pub fn pcre_fullinfo(
            code: *const Pcre,
            extra: *const PcreExtra,
            what: c_int,
            where_: *mut c_void,
        ) -> c_int;
        pub fn pcre_get_stringnumber(code: *const Pcre, name: *const c_char) -> c_int;
        pub static pcre_free: unsafe extern "C" fn(*mut c_void);
    }
}

/// `Pcre.error`
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Partial matches are not supported
    Partial,
    /// Pattern contains items that cannot be used together with partial matching.
    BadPartial,
    /// [BadPattern (msg, pos)] regular expression is malformed.  The reason is
    /// in [msg], the position of the error in the pattern in [pos].
    BadPattern(String, isize),
    /// UTF8 string being matched is invalid
    BadUTF8,
    /// Gets raised when a UTF8 string being matched with offset is invalid.
    BadUTF8Offset,
    /// Maximum allowed number of match attempts with backtracking or recursion
    /// is reached during matching.
    MatchLimit,
    RecursionLimit,
    /// Workspace array size used by DFA matching is too small.
    WorkspaceSize,
    /// [InternalError msg] C-library exhibits unknown/undefined behaviour.
    /// The reason is in [msg].
    InternalError(String),
}

/// OCaml's `Invalid_argument msg`, raised by the binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidArgument(pub String);

/// `Pcre.cflag`: the compilation flags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cflag {
    Caseless,
    Multiline,
    Dotall,
    Extended,
    Anchored,
    DollarEndonly,
    Extra,
    Ungreedy,
    Utf8,
    NoUtf8Check,
    NoAutoCapture,
    AutoCallout,
    Firstline,
    Ucp,
}

/// `int_of_cflag`: the `PCRE_*` options of `pcre.h`.
fn int_of_cflag(flag: Cflag) -> c_int {
    match flag {
        Cflag::Caseless => 0x0001,
        Cflag::Multiline => 0x0002,
        Cflag::Dotall => 0x0004,
        Cflag::Extended => 0x0008,
        Cflag::Anchored => 0x0010,
        Cflag::DollarEndonly => 0x0020,
        Cflag::Extra => 0x0040,
        Cflag::Ungreedy => 0x0200,
        Cflag::Utf8 => 0x0800,
        Cflag::NoAutoCapture => 0x1000,
        Cflag::NoUtf8Check => 0x2000,
        Cflag::AutoCallout => 0x4000,
        Cflag::Firstline => 0x40000,
        Cflag::Ucp => 0x20000000,
    }
}

/// `cflags`: the options of a list of flags.
pub fn cflags(flags: &[Cflag]) -> c_int {
    flags.iter().fold(0, |acc, flag| int_of_cflag(*flag) | acc)
}

/// `String_val`: the bytes of an OCaml string up to its first NUL, as a C
/// string.
fn c_string(s: &[u8]) -> CString {
    let end = s.iter().position(|c| *c == 0).unwrap_or(s.len());
    CString::new(&s[..end]).unwrap()
}

/// `Pcre.regexp`: a compiled (and studied) pattern.
pub struct Regexp {
    code: *mut ffi::Pcre,
    extra: *mut ffi::PcreExtra,
}

impl Drop for Regexp {
    fn drop(&mut self) {
        // SAFETY: `code` and `extra` come from `pcre_compile` and
        // `pcre_study`, and are freed once.
        unsafe {
            if !self.extra.is_null() {
                ffi::pcre_free_study(self.extra);
            }
            (ffi::pcre_free)(self.code as *mut c_void);
        }
    }
}

/// `Pcre.regexp ?study ?limit ?limit_recursion ?iflags ?flags ?chtables pat`,
/// with the arguments the typechecker gives it: the default `study`
/// (`true`), no limits, the default tables, and either `flags` or `iflags`.
/// `Err` is the `Pcre.Error` of the compilation (`BadPattern`); a failure of
/// `pcre_study` raises `Invalid_argument`, which nothing catches.
pub fn regexp(iflags: Option<c_int>, flags: Option<&[Cflag]>, pat: &[u8]) -> Result<Regexp, Error> {
    let options = match flags {
        Some(flag_list) => cflags(flag_list),
        None => iflags.unwrap_or(0),
    };
    let pattern = c_string(pat);
    let mut error: *const c_char = std::ptr::null();
    let mut error_ofs: c_int = 0;
    // SAFETY: `pattern` is a NUL-terminated string; the error pointers are
    // valid for writing.
    let code = unsafe {
        ffi::pcre_compile(
            pattern.as_ptr(),
            options,
            &mut error,
            &mut error_ofs,
            std::ptr::null(),
        )
    };
    if code.is_null() {
        // SAFETY: on failure, `error` points to a static message.
        let msg = if error.is_null() {
            String::new()
        } else {
            unsafe { CStr::from_ptr(error) }
                .to_string_lossy()
                .into_owned()
        };
        return Err(Error::BadPattern(msg, error_ofs as isize));
    }
    // `study = true`
    let mut study_error: *const c_char = std::ptr::null();
    // SAFETY: `code` is a compiled pattern.
    let extra = unsafe { ffi::pcre_study(code, 0, &mut study_error) };
    let rex = Regexp { code, extra };
    if !study_error.is_null() {
        // SAFETY: `study_error` points to a static message.
        let msg = unsafe { CStr::from_ptr(study_error) }
            .to_string_lossy()
            .into_owned();
        drop(rex);
        std::panic::panic_any(InvalidArgument(msg));
    }
    Ok(rex)
}

/// `pcre_fullinfo` for an `int` (or a pointer) of information.
fn fullinfo<T>(rex: &Regexp, what: c_int, where_: &mut T) -> c_int {
    // SAFETY: `where_` has the type `pcre_fullinfo` writes for `what`.
    unsafe { ffi::pcre_fullinfo(rex.code, rex.extra, what, where_ as *mut T as *mut c_void) }
}

/// `Pcre.capturecount`: the number of capturing subpatterns.
pub fn capturecount(rex: &Regexp) -> Result<isize, Error> {
    let mut options: c_int = 0;
    let ret = fullinfo(rex, ffi::PCRE_INFO_CAPTURECOUNT, &mut options);
    if ret != 0 {
        Err(Error::InternalError("pcre_capturecount_stub".to_string()))
    } else {
        Ok(options as isize)
    }
}

/// `Pcre.names`: the names of the named subpatterns, in the order of the
/// name table of PCRE (which is sorted by name).
pub fn names(rex: &Regexp) -> Result<Vec<String>, Error> {
    let mut name_count: c_int = 0;
    if fullinfo(rex, ffi::PCRE_INFO_NAMECOUNT, &mut name_count) != 0 {
        return Err(Error::InternalError(
            "pcre_names_stub: namecount".to_string(),
        ));
    }
    let mut entry_size: c_int = 0;
    if fullinfo(rex, ffi::PCRE_INFO_NAMEENTRYSIZE, &mut entry_size) != 0 {
        return Err(Error::InternalError(
            "pcre_names_stub: nameentrysize".to_string(),
        ));
    }
    let mut tbl_ptr: *const c_uchar = std::ptr::null();
    if fullinfo(rex, ffi::PCRE_INFO_NAMETABLE, &mut tbl_ptr) != 0 {
        return Err(Error::InternalError(
            "pcre_names_stub: nametable".to_string(),
        ));
    }
    let mut res = Vec::with_capacity(name_count as usize);
    for i in 0..name_count as usize {
        // SAFETY: the name table has `name_count` entries of `entry_size`
        // bytes, each a 2-byte number followed by a NUL-terminated name.
        let name =
            unsafe { CStr::from_ptr(tbl_ptr.add(i * entry_size as usize + 2) as *const c_char) };
        res.push(name.to_string_lossy().into_owned());
    }
    Ok(res)
}

/// `Pcre.get_stringnumber rex name`: the number of the subpattern of that
/// name, or `Invalid_argument "Named string not found"`.
pub fn get_stringnumber(rex: &Regexp, name: &str) -> Result<isize, InvalidArgument> {
    let name = c_string(name.as_bytes());
    // SAFETY: `name` is a NUL-terminated string.
    let ret = unsafe { ffi::pcre_get_stringnumber(rex.code, name.as_ptr()) };
    if ret == ffi::PCRE_ERROR_NOSUBSTRING {
        Err(InvalidArgument("Named string not found".to_string()))
    } else {
        Ok(ret as isize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_groups() {
        let rex = regexp(None, Some(&[]), b"(?P<zz>a)(?<bb>b)(c)").unwrap();
        assert_eq!(capturecount(&rex), Ok(3));
        assert_eq!(
            names(&rex).unwrap(),
            vec!["bb".to_string(), "zz".to_string()]
        );
        assert_eq!(get_stringnumber(&rex, "zz"), Ok(1));
        assert!(get_stringnumber(&rex, "nope").is_err());
    }

    #[test]
    fn bad_patterns() {
        assert_eq!(
            regexp(None, Some(&[]), b"He(?'l'\\D)(?'l'\\D)o").err(),
            Some(Error::BadPattern(
                "two named subpatterns have the same name".to_string(),
                14
            ))
        );
        assert_eq!(
            regexp(None, Some(&[]), b"\\x{10FFFF}").err(),
            Some(Error::BadPattern(
                "character value in \\x{} or \\o{} is too large".to_string(),
                9
            ))
        );
        assert!(regexp(None, Some(&[Cflag::Utf8]), b"\\x{10FFFF}").is_ok());
    }
}
