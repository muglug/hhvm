// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/config_file/config_file_version.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use std::sync::LazyLock;

use crate::hh_logger;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VersionComponents {
    pub major: isize,
    pub minor: isize,
    pub build: isize,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Version {
    OpaqueVersion(Option<String>),
    VersionComponents(VersionComponents),
}

/// `pad` defaults to `true`.
pub fn version_to_string_opt(pad: Option<bool>, v: &Version) -> Option<String> {
    let pad = pad.unwrap_or(true);
    match v {
        Version::OpaqueVersion(s) => s.clone(),
        Version::VersionComponents(VersionComponents {
            major,
            minor,
            build,
        }) => {
            if pad {
                Some(format!("{}.{:02}.{}", major, minor, build))
            } else {
                Some(format!("{}.{}.{}", major, minor, build))
            }
        }
    }
}

/// An OCaml `Str` regular expression: `\^` is a `^` character and `\(`,
/// `\)` group.
pub const version_re_str: &str = r"\^\([0-9]+\)\.\([0-9]+\)\.\([0-9]+\)";

/// `Str.regexp version_re_str`, matched as `Str.string_match` matches: at
/// the start of the string, not necessarily up to its end.
static version_re: LazyLock<regex::Regex> =
    LazyLock::new(|| regex::Regex::new(r"^\^([0-9]+)\.([0-9]+)\.([0-9]+)").unwrap());

/// `int_of_string` of a sequence of decimal digits: `None` (OCaml raises
/// `Failure`) when it does not fit an OCaml `int` (63 bits).
fn int_of_digits(s: &str) -> Option<isize> {
    match s.parse::<i64>() {
        Ok(n) if n <= (1 << 62) - 1 => Some(n as isize),
        _ => None,
    }
}

pub fn parse_version(version: Option<&str>) -> Version {
    match version {
        Some(version) if version_re.is_match(version) => {
            let caps = version_re.captures(version).unwrap();
            // `try ... with _ ->`: one of the numbers is too big.
            match (
                int_of_digits(&caps[1]),
                int_of_digits(&caps[2]),
                int_of_digits(&caps[3]),
            ) {
                (Some(major), Some(minor), Some(build)) => {
                    Version::VersionComponents(VersionComponents {
                        major,
                        minor,
                        build,
                    })
                }
                _ => {
                    hh_logger::log(&format!(
                        "Failed to parse server version '{}', treating it as an opaque string",
                        version
                    ));
                    Version::OpaqueVersion(Some(version.to_string()))
                }
            }
        }
        Some(version) => {
            hh_logger::log(&format!(
                "Server version '{}' does not match version pattern {}, treating it as an opaque string",
                version, version_re_str
            ));
            Version::OpaqueVersion(Some(version.to_string()))
        }
        None => {
            hh_logger::log("Server version is not set");
            Version::OpaqueVersion(None)
        }
    }
}

/// `compare` (OCaml's polymorphic comparison): -1, 0 or 1.
fn compare<A: Ord + ?Sized>(a: &A, b: &A) -> isize {
    a.cmp(b) as isize
}

pub fn compare_versions(v1: &Version, v2: &Version) -> isize {
    use Version::*;
    match (v1, v2) {
        (VersionComponents(c1), VersionComponents(c2)) => compare(c1, c2),
        (OpaqueVersion(Some(s1)), OpaqueVersion(Some(s2))) => compare(s1.as_str(), s2.as_str()),
        (OpaqueVersion(None), OpaqueVersion(None)) => 0,
        (OpaqueVersion(None), OpaqueVersion(Some(_)))
        | (OpaqueVersion(_), VersionComponents(_)) => -1,
        (OpaqueVersion(Some(_)), OpaqueVersion(None))
        | (VersionComponents(_), OpaqueVersion(_)) => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn components(major: isize, minor: isize, build: isize) -> Version {
        Version::VersionComponents(VersionComponents {
            major,
            minor,
            build,
        })
    }

    #[test]
    fn parsing() {
        assert_eq!(parse_version(Some("^4.12.3")), components(4, 12, 3));
        // `Str.string_match` matches a prefix.
        assert_eq!(parse_version(Some("^4.12.3-rc1")), components(4, 12, 3));
        // The `^` is required.
        assert_eq!(
            parse_version(Some("4.12.3")),
            Version::OpaqueVersion(Some("4.12.3".to_string()))
        );
        assert_eq!(
            parse_version(Some("^99999999999999999999.1.1")),
            Version::OpaqueVersion(Some("^99999999999999999999.1.1".to_string()))
        );
        assert_eq!(parse_version(None), Version::OpaqueVersion(None));
    }

    #[test]
    fn printing_and_comparing() {
        assert_eq!(
            version_to_string_opt(None, &components(4, 2, 3)),
            Some("4.02.3".to_string())
        );
        assert_eq!(
            version_to_string_opt(Some(false), &components(4, 2, 3)),
            Some("4.2.3".to_string())
        );
        assert_eq!(
            version_to_string_opt(None, &Version::OpaqueVersion(None)),
            None
        );
        assert_eq!(
            compare_versions(&components(4, 2, 3), &components(4, 10, 0)),
            -1
        );
        assert_eq!(
            compare_versions(&components(5, 0, 0), &components(4, 10, 0)),
            1
        );
        assert_eq!(
            compare_versions(&components(4, 2, 3), &components(4, 2, 3)),
            0
        );
        let opaque = |s: Option<&str>| Version::OpaqueVersion(s.map(str::to_string));
        assert_eq!(compare_versions(&opaque(None), &opaque(None)), 0);
        assert_eq!(compare_versions(&opaque(None), &opaque(Some("a"))), -1);
        assert_eq!(
            compare_versions(&opaque(Some("a")), &components(1, 1, 1)),
            -1
        );
        assert_eq!(compare_versions(&components(1, 1, 1), &opaque(None)), 1);
        assert_eq!(compare_versions(&opaque(Some("b")), &opaque(Some("a"))), 1);
    }
}
