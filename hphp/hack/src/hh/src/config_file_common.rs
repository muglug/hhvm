// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/config_file/config_file_common.ml`. See `hh/PORTING.md`.
//!
//! In OCaml, `Config_file_common.t` was the Rust `config_file::ConfigFile`,
//! reached through `Config_file_ffi_externs` (the `hh_config_file_*`
//! externals of `utils/config_file/rust/ffi.rs`). Here it is that type, and
//! the externals are its methods: what the getters accept and the messages
//! of their errors are those of the `config_file` crate, as they were in
//! OCaml.
//!
//! Exceptions: the getters that OCaml lets raise `Invalid_argument` panic
//! with `Invalid_argument: <message>`. `parse`, whose `Sys_error` its callers
//! catch, returns it.

#![allow(non_upper_case_globals)]

use std::sync::RwLock;

use sha1::Digest;

use crate::hh_logger;
use crate::sys_utils;
use crate::yojson;

/// `Config_file_ffi_externs.config`.
pub type T = ::config_file::ConfigFile;

pub const file_path_relative_to_repo_root: &str = ".hhconfig";

/// `pkgs_config_path_relative_to_repo_root : string ref`, initially
/// `"PACKAGES.toml"` (`None` stands for that initial value).
static pkgs_config_path_relative_to_repo_root: RwLock<Option<String>> = RwLock::new(None);

pub fn empty() -> T {
    T::default()
}

pub fn is_empty(config: &T) -> bool {
    config.is_empty()
}

/// `hh_config_file_print_to_stderr`: `key = value` lines, then a flush.
pub fn print_to_stderr(config: &T) {
    use std::io::Write;
    for (key, value) in config.iter() {
        eprintln!("{} = {}", key, value);
    }
    let _ = std::io::stderr().flush();
}

/// `Int.of_string_opt` (and `Int.of_string`, which raises `Failure` where
/// this is `None`): an OCaml integer literal (a sign, `0x`, `0o`, `0b` or
/// `0u`, digits and `_`), within the range of an OCaml `int` (63 bits).
pub(crate) fn int_of_string_opt(s: &str) -> Option<isize> {
    const MAX: i128 = (1 << 62) - 1;
    let (negative, s) = match s.strip_prefix('-') {
        Some(s) => (true, s),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let lower = s.to_ascii_lowercase();
    let (radix, digits, decimal) = if let Some(d) = lower.strip_prefix("0x") {
        (16, d, false)
    } else if let Some(d) = lower.strip_prefix("0o") {
        (8, d, false)
    } else if let Some(d) = lower.strip_prefix("0b") {
        (2, d, false)
    } else if let Some(d) = lower.strip_prefix("0u") {
        (10, d, false)
    } else {
        (10, lower.as_str(), true)
    };
    // The first character is a digit; `_` can follow.
    if !digits.chars().next()?.is_digit(radix) {
        return None;
    }
    let mut n: i128 = 0;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        n = n * radix as i128 + c.to_digit(radix)? as i128;
        // Unsigned literals can use all the 63 bits; they wrap around.
        if n > 2 * MAX + 1 {
            return None;
        }
    }
    if decimal {
        // Decimal literals are signed: up to `max_int`, or `-min_int`.
        if n > MAX + (negative as i128) {
            return None;
        }
    } else if n > MAX {
        n -= 2 * (MAX + 1);
    }
    Some((if negative { -n } else { n }) as isize)
}

/// `Config_file_common.Getters` (`Getters_S`).
pub mod getters {
    use oxidized::global_options::AllOrSome;

    use super::T;
    use crate::config_file_version;

    /// `ok_or_invalid_arg`: the value, or `invalid_arg` of the error.
    fn ok_or_invalid_arg<A, E: std::fmt::Display>(r: Result<A, E>) -> A {
        match r {
            Ok(x) => x,
            Err(e) => panic!("Invalid_argument: {}", e),
        }
    }

    pub fn string_opt(key: &str, config: &T) -> Option<String> {
        config.get_str(key).map(str::to_string)
    }

    /// Does not immediately raise if key is not an int
    pub fn int_opt_result(key: &str, config: &T) -> Option<Result<isize, String>> {
        config.get_int(key).map(|r| r.map_err(|e| e.to_string()))
    }

    pub fn int_opt(key: &str, config: &T) -> Option<isize> {
        config.get_int(key).map(ok_or_invalid_arg)
    }

    pub fn float_opt(key: &str, config: &T) -> Option<f64> {
        config.get_float(key).map(ok_or_invalid_arg)
    }

    pub fn bool_opt(key: &str, config: &T) -> Option<bool> {
        config.get_bool(key).map(ok_or_invalid_arg)
    }

    pub fn all_or_some_ints_opt(key: &str, config: &T) -> Option<AllOrSome<isize>> {
        config.get_all_or_some_ints(key).map(ok_or_invalid_arg)
    }

    pub fn string_list_opt(key: &str, config: &T) -> Option<Vec<String>> {
        config
            .get_str_list(key)
            .map(|iter| iter.map(str::to_string).collect())
    }

    /// `None` too when one of the elements is not an integer (OCaml catches
    /// the `Failure` of `Int.of_string`).
    pub fn int_list_opt(key: &str, config: &T) -> Option<Vec<isize>> {
        string_list_opt(key, config)?
            .iter()
            .map(|s| super::int_of_string_opt(s))
            .collect()
    }

    pub fn string_(key: &str, default: &str, config: &T) -> String {
        string_opt(key, config).unwrap_or_else(|| default.to_string())
    }

    pub fn int_(key: &str, default: isize, config: &T) -> isize {
        int_opt(key, config).unwrap_or(default)
    }

    pub fn float_(key: &str, default: f64, config: &T) -> f64 {
        float_opt(key, config).unwrap_or(default)
    }

    pub fn bool_(key: &str, default: bool, config: &T) -> bool {
        bool_opt(key, config).unwrap_or(default)
    }

    pub fn all_or_some_ints(key: &str, default: AllOrSome<isize>, config: &T) -> AllOrSome<isize> {
        all_or_some_ints_opt(key, config).unwrap_or(default)
    }

    pub fn string_list(key: &str, default: Vec<String>, config: &T) -> Vec<String> {
        string_list_opt(key, config).unwrap_or(default)
    }

    pub fn bool_if_min_version(
        key: &str,
        default: bool,
        current_version: &config_file_version::Version,
        config: &T,
    ) -> bool {
        let version_value = string_(key, &default.to_string(), config);
        match version_value.as_str() {
            "true" => true,
            "false" => false,
            version_value => {
                let version_value = config_file_version::parse_version(Some(version_value));
                config_file_version::compare_versions(current_version, &version_value) >= 0
            }
        }
    }
}

pub fn get_pkgconfig_path() -> String {
    match &*pkgs_config_path_relative_to_repo_root.read().unwrap() {
        Some(path) => path.clone(),
        None => "PACKAGES.toml".to_string(),
    }
}

pub fn set_pkgconfig_path(fn_: &str) {
    *pkgs_config_path_relative_to_repo_root.write().unwrap() = Some(fn_.to_string());
}

/// Apply overrides using provided overrides.
/// [log_reason] is solely used for logging, so we can write to stderr indicating where
/// these overrides came from and what they were.
pub fn apply_overrides(config: &T, overrides: &T, log_reason: Option<&str>) -> T {
    if is_empty(overrides) {
        config.clone()
    } else {
        let mut config = config.clone();
        config.apply_overrides(overrides);
        if let Some(from) = log_reason {
            use std::io::Write;
            eprint!("*** Overrides from {}:\n", from);
            let _ = std::io::stderr().flush();
            print_to_stderr(overrides);
            eprint!("\n");
            let _ = std::io::stderr().flush();
        }
        config
    }
}

/// Config file format:
/// # Some comment. Indicate by a pound sign at the start of a new line
/// key = a possibly space-separated value
pub fn parse_contents(contents: &[u8]) -> T {
    T::from_slice(contents)
}

/// Compute the hhconfig hash using the concatenation of hhconfig's and package config's content
pub fn hash(parsed: &T, hhconfig_contents: &[u8], pkgconfig_contents: &[u8]) -> String {
    match getters::string_opt("override_hhconfig_hash", parsed) {
        Some(hash) => hash,
        None => {
            // `Sha1.digest (hhconfig_contents ^ pkgconfig_contents)`: the
            // digest in lowercase hexadecimal.
            let mut hasher = sha1::Sha1::new();
            hasher.update(hhconfig_contents);
            hasher.update(pkgconfig_contents);
            format!("{:x}", hasher.finalize())
        }
    }
}

/// Non-lwt implementation of parse
pub fn parse(fn_: &str) -> Result<(String, T), sys_utils::SysError> {
    let contents = sys_utils::cat(fn_)?;
    let parsed = parse_contents(&contents);
    let hash = hash(&parsed, &contents, b"");
    Ok((hash, parsed))
}

pub fn parse_local_config(fn_: &str) -> T {
    match parse(fn_) {
        Ok((_hash, config)) => config,
        Err(e) => {
            // `Exn.to_string e`, the S-expression of the exception.
            hh_logger::log(&format!("Loading config exception: (Sys_error {:?})", e.0));
            hh_logger::log(&format!("Could not load config at {}", fn_));
            empty()
        }
    }
}

/// (`Yojson.Safe.from_string` of what `serde_json` printed cannot fail: a
/// `Json_error` there would be a bug, a panic, like the `failwith`.)
pub fn to_json(t: &T) -> yojson::safe::T {
    match t.to_json() {
        Ok(json) => match yojson::safe::from_string(&json) {
            Ok(json) => json,
            Err(e) => panic!("Yojson.Json_error: {}", e.0),
        },
        Err(e) => panic!("{}", e),
    }
}

/// A key given twice keeps its last value.
pub fn of_list(list: &[(String, String)]) -> T {
    list.iter().cloned().collect()
}

/// In increasing order.
pub fn keys(config: &T) -> Vec<String> {
    config.keys().map(str::to_string).collect()
}

#[cfg(test)]
mod tests {
    use oxidized::global_options::AllOrSome;

    use super::getters::*;
    use super::*;
    use crate::config_file_version::Version;
    use crate::config_file_version::VersionComponents;

    fn config(s: &str) -> T {
        parse_contents(s.as_bytes())
    }

    #[test]
    fn getters_read_values() {
        let c = config(
            "s = hello world\ni = 0x10\nf = 1.5\nb = true\nl = a, b,c\nints = 1,2, 3\nbad_ints = 1,x\nall = all\n",
        );
        assert_eq!(string_opt("s", &c), Some("hello world".to_string()));
        assert_eq!(string_opt("missing", &c), None);
        assert_eq!(string_("missing", "d", &c), "d");
        assert_eq!(int_opt("i", &c), Some(16));
        assert_eq!(int_("missing", 7, &c), 7);
        assert_eq!(
            int_opt_result("s", &c),
            Some(Err("invalid digit found in string".to_string()))
        );
        assert_eq!(float_opt("f", &c), Some(1.5));
        assert_eq!(bool_opt("b", &c), Some(true));
        assert_eq!(bool_("missing", false, &c), false);
        assert_eq!(
            string_list_opt("l", &c),
            Some(vec!["a".to_string(), "b".to_string(), "c".to_string()])
        );
        assert_eq!(int_list_opt("ints", &c), Some(vec![1, 2, 3]));
        // `Int.of_string` fails on one element: no list at all.
        assert_eq!(int_list_opt("bad_ints", &c), None);
        assert_eq!(all_or_some_ints_opt("all", &c), Some(AllOrSome::All));
        assert_eq!(
            all_or_some_ints("missing", AllOrSome::ASome(vec![1]), &c),
            AllOrSome::ASome(vec![1])
        );
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: invalid digit found in string")]
    fn int_opt_raises_invalid_argument() {
        int_opt("i", &config("i = ten"));
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: provided string was not `true` or `false`")]
    fn bool_opt_raises_invalid_argument() {
        bool_opt("b", &config("b = yes"));
    }

    #[test]
    fn min_version() {
        let current = Version::VersionComponents(VersionComponents {
            major: 4,
            minor: 10,
            build: 0,
        });
        let c = config("t = true\nf = false\nold = ^4.9.0\nnew = ^4.11.0\nopaque = foo\n");
        assert!(bool_if_min_version("t", false, &current, &c));
        assert!(!bool_if_min_version("f", true, &current, &c));
        assert!(bool_if_min_version("old", false, &current, &c));
        assert!(!bool_if_min_version("new", true, &current, &c));
        // An opaque version is smaller than any components.
        assert!(bool_if_min_version("opaque", false, &current, &c));
        assert!(bool_if_min_version("missing", true, &current, &c));
        assert!(!bool_if_min_version("missing", false, &current, &c));
    }

    #[test]
    fn ocaml_ints() {
        assert_eq!(int_of_string_opt("42"), Some(42));
        assert_eq!(int_of_string_opt("-42"), Some(-42));
        assert_eq!(int_of_string_opt("+42"), Some(42));
        assert_eq!(int_of_string_opt("0x1F"), Some(31));
        assert_eq!(int_of_string_opt("0X1f"), Some(31));
        assert_eq!(int_of_string_opt("1_000"), Some(1000));
        assert_eq!(int_of_string_opt("_1"), None);
        assert_eq!(int_of_string_opt(""), None);
        assert_eq!(int_of_string_opt(" 1"), None);
        assert_eq!(
            int_of_string_opt("4611686018427387903"),
            Some(4611686018427387903)
        );
        assert_eq!(int_of_string_opt("4611686018427387904"), None);
        assert_eq!(
            int_of_string_opt("-4611686018427387904"),
            Some(-4611686018427387904)
        );
        // Unsigned literals wrap around.
        assert_eq!(int_of_string_opt("0x7fffffffffffffff"), Some(-1));
    }

    #[test]
    fn overrides_hash_and_keys() {
        let c = config("a = 1\nb = 2\n");
        let o = of_list(&[
            ("b".to_string(), "3".to_string()),
            ("c".to_string(), "4".to_string()),
        ]);
        let applied = apply_overrides(&c, &o, None);
        assert_eq!(keys(&applied), vec!["a", "b", "c"]);
        assert_eq!(string_opt("b", &applied), Some("3".to_string()));
        assert!(is_empty(&empty()));
        // The SHA1 of the concatenation, unless the config overrides it.
        assert_eq!(
            hash(&c, b"ab", b"c"),
            "a9993e364706816aba3e25717850c26c9cd0d89d"
        );
        assert_eq!(
            hash(&config("override_hhconfig_hash = xyz"), b"ab", b"c"),
            "xyz"
        );
        assert_eq!(
            to_json(&c),
            yojson::safe::T::Assoc(vec![
                ("a".to_string(), yojson::safe::T::String("1".to_string())),
                ("b".to_string(), yojson::safe::T::String("2".to_string())),
            ])
        );
    }

    #[test]
    fn pkgconfig_path_and_local_config() {
        assert_eq!(get_pkgconfig_path(), "PACKAGES.toml");
        assert!(is_empty(&parse_local_config("/nonexistent/hh.conf")));
        assert!(parse("/nonexistent/hh.conf").is_err());
    }
}
