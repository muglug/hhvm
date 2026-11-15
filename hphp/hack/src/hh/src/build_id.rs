// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/build_id.ml`. See `hh/PORTING.md`.
//!
//! The externals are those of `utils/core/get_build_id.c`, over the constants
//! that the OCaml build generated (`BuildInfo_kRevision`,
//! `BuildInfo_kRevisionCommitTimeUnix`, `BuildInfo_kBuildMode`,
//! `BuildInfo_kPackageName`, `HH_BUILD_TIMESTAMP`). The build script
//! (`hh/build.rs`) computes them as `gen_build_id.ml` did and passes them as
//! `HH_BUILD_REVISION`, `HH_BUILD_COMMIT_TIME` and `HH_BUILD_TIMESTAMP`; the
//! build mode and the package name are always `""` there, as in the OSS
//! OCaml build. Each value is computed once, like OCaml's toplevel `let`s.

use std::sync::LazyLock;

/// `BuildInfo_kRevision`
const BUILD_INFO_K_REVISION: &str = env!("HH_BUILD_REVISION");

/// `BuildInfo_kRevisionCommitTimeUnix`
const BUILD_INFO_K_REVISION_COMMIT_TIME_UNIX: &str = env!("HH_BUILD_COMMIT_TIME");

/// `BuildInfo_kBuildMode`: `""` ("not implemented" in `gen_build_id.ml`).
const BUILD_INFO_K_BUILD_MODE: &str = "";

/// `BuildInfo_kPackageName`: `""` ("package name always empty").
const BUILD_INFO_K_PACKAGE_NAME: &str = "";

/// `HH_BUILD_TIMESTAMP` (`utils/core/config/dune`: the time of the build).
const HH_BUILD_TIMESTAMP: &str = env!("HH_BUILD_TIMESTAMP");

fn parse_unix_time(what: &str, s: &str) -> u64 {
    match s.parse() {
        Ok(t) => t,
        Err(_) => panic!("Build_id: {what} is not a number: {s:?}"),
    }
}

/// The mark of the Rust implementation at the end of its build revision
/// (`<commit>-rust`), so that a client and a monitor can tell "the other
/// implementation" from "another version of this one" (the Rust and the
/// OCaml binaries are installed side by side and share the files of a root:
/// see `crate::monitor_utils::cross_implementation_policy`).
pub const RUST_BUILD_MARKER: &str = "-rust";

/// Whether a build revision (of a client or a monitor) is the Rust
/// implementation's.
pub fn is_rust_build_revision(revision: &str) -> bool {
    revision.ends_with(RUST_BUILD_MARKER)
}

/// `external get_build_revision : unit -> string = "hh_get_build_revision"`,
/// with the mark of the Rust implementation ([`RUST_BUILD_MARKER`]).
fn get_build_revision() -> String {
    format!("{}{}", BUILD_INFO_K_REVISION, RUST_BUILD_MARKER)
}

/// `external get_build_commit_time : unit -> int = "hh_get_build_commit_time"`
fn get_build_commit_time() -> isize {
    parse_unix_time("BuildInfo_kRevisionCommitTimeUnix", BUILD_INFO_K_REVISION_COMMIT_TIME_UNIX)
        as isize
}

/// `get_built_timestamp` of `get_build_id.c`: the commit time, or the time of
/// the build when it is 0, in local time (`localtime`).
fn get_built_timestamp() -> libc::tm {
    unsafe extern "C" {
        /// POSIX `tzset(3)` (not exported by the `libc` crate on every
        /// target).
        fn tzset();
    }
    let mut timestamp =
        parse_unix_time("BuildInfo_kRevisionCommitTimeUnix", BUILD_INFO_K_REVISION_COMMIT_TIME_UNIX);
    // #ifdef HH_BUILD_TIMESTAMP
    if timestamp == 0 {
        timestamp = parse_unix_time("HH_BUILD_TIMESTAMP", HH_BUILD_TIMESTAMP);
    }
    let timestamp = timestamp as libc::time_t;
    // SAFETY: `tm` is plain data; `tzset` and `localtime_r` only write it
    // and the timezone globals (`localtime` sets the timezone up too).
    unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        tzset();
        if libc::localtime_r(&timestamp, &mut tm).is_null() {
            panic!("Build_id: localtime failed for {timestamp}");
        }
        tm
    }
}

/// `external get_build_commit_time_string : unit -> string =
/// "hh_get_build_commit_time_string"`: `strftime "%c"` (in the C locale,
/// which neither OCaml nor Rust changes) into a buffer of 25 bytes.
fn get_build_commit_time_string() -> String {
    let timestamp = get_built_timestamp();
    let mut timestamp_string = [0u8; 25];
    // SAFETY: the buffer is 25 bytes and its size is passed; the format is a
    // NUL-terminated literal.
    let len = unsafe {
        libc::strftime(
            timestamp_string.as_mut_ptr() as *mut libc::c_char,
            timestamp_string.len(),
            c"%c".as_ptr(),
            &timestamp,
        )
    };
    String::from_utf8_lossy(&timestamp_string[..len]).into_owned()
}

/// `external get_build_mode : unit -> string = "hh_get_build_mode"`
fn get_build_mode() -> String {
    BUILD_INFO_K_BUILD_MODE.to_string()
}

/// `external get_build_package_name : unit -> string =
/// "hh_get_build_package_name"`
fn get_build_package_name() -> String {
    BUILD_INFO_K_PACKAGE_NAME.to_string()
}

static BUILD_REVISION: LazyLock<String> = LazyLock::new(get_build_revision);

static BUILD_COMMIT_TIME: LazyLock<isize> = LazyLock::new(get_build_commit_time);

static BUILD_COMMIT_TIME_STRING: LazyLock<String> = LazyLock::new(get_build_commit_time_string);

static BUILD_MODE: LazyLock<String> = LazyLock::new(get_build_mode);

static BUILD_PACKAGE_NAME: LazyLock<String> = LazyLock::new(get_build_package_name);

static IS_BUILD_OPTIMIZED: LazyLock<bool> = LazyLock::new(|| {
    let build_mode = build_mode();
    build_mode.starts_with("dbgo") || build_mode.starts_with("opt") || build_mode.is_empty()
});

/// The package name is empty when not built by fbpkg
static IS_DEV_BUILD: LazyLock<bool> = LazyLock::new(|| build_package_name().is_empty());

pub fn build_revision() -> String {
    BUILD_REVISION.clone()
}

pub fn build_commit_time() -> isize {
    *BUILD_COMMIT_TIME
}

pub fn build_commit_time_string() -> String {
    BUILD_COMMIT_TIME_STRING.clone()
}

pub fn build_mode() -> String {
    BUILD_MODE.clone()
}

/// Not in `build_id.mli`; `is_dev_build` reads it.
pub fn build_package_name() -> String {
    BUILD_PACKAGE_NAME.clone()
}

pub fn is_build_optimized() -> bool {
    *IS_BUILD_OPTIMIZED
}

/// Returns [true] iff the embedded package name is empty.
pub fn is_dev_build() -> bool {
    *IS_DEV_BUILD
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values() {
        // The OSS build: no build mode, no package name.
        assert_eq!(build_mode(), "");
        assert!(is_build_optimized());
        assert!(is_dev_build());
        assert_eq!(build_package_name(), "");
        // A revision is 40 hex digits (git) or empty (no repository), then
        // the mark of the Rust implementation.
        let rev = build_revision();
        assert!(is_rust_build_revision(&rev));
        let commit = &rev[..rev.len() - RUST_BUILD_MARKER.len()];
        assert!(commit.is_empty() || commit.bytes().all(|c| c.is_ascii_hexdigit()));
        assert!(build_commit_time() >= 0);
    }

    #[test]
    fn commit_time_string_is_strftime_c() {
        // `%c` in the C locale: `%a %b %e %H:%M:%S %Y`, e.g.
        // `Tue Nov 10 12:00:00 2026` (24 characters).
        let s = build_commit_time_string();
        assert_eq!(s.len(), 24, "{s:?}");
        let words: Vec<&str> = s.split_whitespace().collect();
        assert_eq!(words.len(), 5, "{s:?}");
        assert!(
            ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"].contains(&words[0]),
            "{s:?}"
        );
        assert_eq!(words[3].len(), 8, "{s:?}");
        assert_eq!(&words[3][2..3], ":");
        assert_eq!(words[4].len(), 4, "{s:?}");
    }
}
