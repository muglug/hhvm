// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the suffix of the running executable, and the
//! "sibling binary" lookups built on it. The Rust binaries are installed next
//! to the OCaml ones under suffixed names (`hh_server_rust`, `hh_client_rust`,
//! `hackfmt_rust`), so where the OCaml locates another program by its name
//! (`hh_server` next to `hh_client`, `<bindir>/hackfmt`), the Rust binaries
//! add their own suffix, and so find each other and never the OCaml ones.
//!
//! The rule. The suffix is the part of the file name of `Sys.executable_name`
//! ([`crate::path::executable_name`]) after the base program name it starts
//! with ([`BASE_NAMES`]): `hh_client_rust` -> `_rust`, `hh_client` -> ``, a
//! name that starts with no base name (e.g. a test binary) -> ``. The sibling
//! of base name `b` is `Path.concat (Path.dirname Sys.executable_name)
//! (b ^ suffix)`, i.e. the directory is taken from the same path as the
//! suffix, which is the path the OCaml uses for its own sibling lookup
//! (`Client_start.get_hhserver_path`). So symlinks behave as in the OCaml's
//! lookup: `Sys.executable_name` (like Rust's `current_exe`) is
//! `/proc/self/exe` on Linux, i.e. symlinks resolved (a symlink `hh_client`
//! to `.../hh_client_rust` gives `_rust` and the target's directory), and
//! `_NSGetExecutablePath` on macOS, i.e. the path that was executed, NOT
//! resolved (the same symlink gives `` and the symlink's directory, where the
//! OCaml would look too). A wrapper script that execs `hh_client_rust` gives
//! `_rust` everywhere.

/// The program names the binaries are built as, longest first where one is a
/// prefix of another. (Not `hh`: it keeps its name, locates no sibling, and
/// as a prefix it would take e.g. `hhvm` for `hh` + `vm`.)
pub const BASE_NAMES: &[&str] = &["hh_single_type_check", "hh_client", "hh_server", "hackfmt"];

/// The suffix of an executable's file name: what follows the first of
/// [`BASE_NAMES`] it starts with, `` if it starts with none.
pub fn suffix_of_file_name(file_name: &str) -> &str {
    BASE_NAMES
        .iter()
        .find_map(|base| file_name.strip_prefix(base))
        .unwrap_or("")
}

/// The suffix of the executable at path `exe` (only its file name counts:
/// the path is not resolved).
pub fn suffix_of_executable(exe: &str) -> String {
    suffix_of_file_name(&crate::rt::ocaml_filename::basename(exe)).to_string()
}

/// The suffix of the running executable.
pub fn executable_suffix() -> String {
    suffix_of_executable(&crate::path::executable_name())
}

/// The sibling `base` of the executable at path `exe`: `Path.concat
/// (Path.dirname exe) (base ^ suffix)` (realpath'd when it exists, as
/// `Path.concat` does).
pub fn sibling_of(exe: &str, base: &str) -> String {
    let exe = exe.to_string();
    crate::path::to_string(&crate::path::concat(
        &crate::path::dirname(&exe),
        &format!("{}{}", base, suffix_of_executable(&exe)),
    ))
}

/// The sibling binary `base` of the running executable: its directory +
/// `base` + its suffix.
pub fn sibling_binary(base: &str) -> String {
    sibling_of(&crate::path::executable_name(), base)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suffixes() {
        assert_eq!(suffix_of_file_name("hh_client_rust"), "_rust");
        assert_eq!(suffix_of_file_name("hh_client"), "");
        assert_eq!(suffix_of_file_name("hh_server_rust"), "_rust");
        assert_eq!(suffix_of_file_name("hh_server"), "");
        assert_eq!(suffix_of_file_name("hackfmt_rust"), "_rust");
        assert_eq!(suffix_of_file_name("hh_single_type_check_rust"), "_rust");
        // Dots and other underscores in the suffix are kept.
        assert_eq!(suffix_of_file_name("hh_client.v2_rust"), ".v2_rust");
        assert_eq!(suffix_of_file_name("hh_server_rust_dbg"), "_rust_dbg");
        // No base name: no suffix.
        assert_eq!(suffix_of_file_name("hh"), "");
        assert_eq!(suffix_of_file_name("hh_rust"), "");
        assert_eq!(suffix_of_file_name("hh_wip11-0123abcd"), "");
        assert_eq!(suffix_of_file_name("hhvm"), "");
        assert_eq!(suffix_of_file_name(""), "");
    }

    #[test]
    fn suffixes_of_paths() {
        // Dots and underscores in the directories do not count.
        assert_eq!(suffix_of_executable("/opt/hh_server.v1_2/bin/hh_client_rust"), "_rust");
        assert_eq!(suffix_of_executable("/opt/hh_client_x/bin/hh_client"), "");
        assert_eq!(suffix_of_executable("./hh_client_rust"), "_rust");
        assert_eq!(suffix_of_executable("hh_server_rust"), "_rust");
    }

    fn temp_dir(name: &str) -> std::path::PathBuf {
        let d = std::env::temp_dir().join(format!("hh_exe_suffix_{}_{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        crate::path::make(&d.to_string_lossy()).into()
    }

    #[test]
    fn siblings() {
        let d = temp_dir("siblings");
        let ds = d.to_string_lossy().into_owned();
        assert_eq!(sibling_of(&format!("{ds}/hh_client_rust"), "hh_server"), format!("{ds}/hh_server_rust"));
        assert_eq!(sibling_of(&format!("{ds}/hh_client"), "hh_server"), format!("{ds}/hh_server"));
        assert_eq!(sibling_of(&format!("{ds}/hh_server_rust"), "hackfmt"), format!("{ds}/hackfmt_rust"));
        // The path of `exe` is not resolved: a symlink `hh_client` to an
        // `hh_client_rust` elsewhere is a plain `hh_client` (the platform's
        // `Sys.executable_name` decides whether symlinks are resolved).
        let other = d.join("other");
        std::fs::create_dir_all(&other).unwrap();
        std::fs::write(other.join("hh_client_rust"), "").unwrap();
        std::os::unix::fs::symlink(other.join("hh_client_rust"), d.join("hh_client")).unwrap();
        assert_eq!(sibling_of(&format!("{ds}/hh_client"), "hh_server"), format!("{ds}/hh_server"));
        // An existing sibling that is a symlink is resolved, as `Path.concat`
        // does.
        std::os::unix::fs::symlink(other.join("hh_client_rust"), d.join("hh_server_rust")).unwrap();
        assert_eq!(
            sibling_of(&format!("{ds}/hh_client_rust"), "hh_server"),
            format!("{ds}/other/hh_client_rust")
        );
        std::fs::remove_dir_all(&d).unwrap();
    }

    /// The child half of [`symlink_to_the_running_executable`].
    #[test]
    fn exe_suffix_probe() {
        if std::env::var_os("HH_EXE_SUFFIX_PROBE").is_some() {
            println!("PROBE suffix=[{}] sibling=[{}]", executable_suffix(), sibling_binary("hh_server"));
        }
    }

    /// The running test binary, hard-linked as `hh_client_rust` and run
    /// through a symlink `hh_client`: what the platform's `current_exe` gives
    /// decides (resolved on Linux, not on macOS, as `Sys.executable_name`).
    #[test]
    fn symlink_to_the_running_executable() {
        let exe = std::env::current_exe().unwrap();
        // Next to the test binary, so the hard link stays on one filesystem.
        let d = exe.parent().unwrap().join(format!("exe_suffix_test_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(d.join("real")).unwrap();
        std::fs::create_dir_all(d.join("link")).unwrap();
        let d: std::path::PathBuf = crate::path::make(&d.to_string_lossy()).into();
        let real = d.join("real/hh_client_rust");
        if std::fs::hard_link(&exe, &real).is_err() {
            std::fs::copy(&exe, &real).unwrap();
        }
        let link = d.join("link/hh_client");
        std::os::unix::fs::symlink(&real, &link).unwrap();
        let probe = |program: &std::path::Path| {
            let out = std::process::Command::new(program)
                .args(["--exact", "rt::exe_suffix::tests::exe_suffix_probe", "--nocapture"])
                .env("HH_EXE_SUFFIX_PROBE", "1")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
            stdout
                .lines()
                .find(|l| l.starts_with("PROBE "))
                .unwrap_or_else(|| panic!("no probe output: {stdout}"))
                .to_string()
        };
        let ds = d.to_string_lossy().into_owned();
        assert_eq!(
            probe(&real),
            format!("PROBE suffix=[_rust] sibling=[{ds}/real/hh_server_rust]")
        );
        let expected_through_link = if cfg!(target_os = "linux") {
            format!("PROBE suffix=[_rust] sibling=[{ds}/real/hh_server_rust]")
        } else {
            format!("PROBE suffix=[] sibling=[{ds}/link/hh_server]")
        };
        assert_eq!(probe(&link), expected_through_link);
        std::fs::remove_dir_all(&d).unwrap();
    }
}
