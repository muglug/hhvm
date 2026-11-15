// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_isolation_validate.ml`. See `hh/PORTING.md`.

use std::io::Write;

use crate::exit_status;
use crate::server_command_types::isolation_validation;
use crate::utils::print_count;
use crate::yojson::safe::T as J;

/// Print the verdict, the references that contradict it, and the candidate
/// paths nothing was checked for.
// A candidate can only ever be shown *not* to be isolatable, so the count of
// files checked is what bounds the claim.
pub fn output(result: &isolation_validation::Result, output_json: bool) {
    let stdout = std::io::stdout();
    let mut stdout = stdout.lock();
    let _ = write_output(&mut stdout, result, output_json);
    let _ = stdout.flush();
}

/// [`output`] to `out`, so that the tests can read it.
pub(crate) fn write_output(
    out: &mut dyn Write,
    result: &isolation_validation::Result,
    output_json: bool,
) -> std::io::Result<()> {
    if output_json {
        let j = J::Assoc(vec![
            (
                "refused".to_string(),
                match &result.refused {
                    None => J::Null,
                    Some(reason) => J::String(reason.clone()),
                },
            ),
            ("isolatable".to_string(), J::Bool(result.isolatable)),
            ("files_checked".to_string(), J::Int(result.files_checked)),
            (
                "violations".to_string(),
                J::List(
                    result
                        .violations
                        .iter()
                        .map(|v| {
                            J::Assoc(vec![
                                ("referrer".to_string(), J::String(v.referrer.clone())),
                                ("line".to_string(), J::Int(v.line)),
                                ("message".to_string(), J::String(v.message.clone())),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "unknown_files".to_string(),
                J::List(
                    result
                        .unknown_files
                        .iter()
                        .map(|f| J::String(f.clone()))
                        .collect(),
                ),
            ),
            (
                "overridden_files".to_string(),
                J::List(
                    result
                        .overridden_files
                        .iter()
                        .map(|f| J::String(f.clone()))
                        .collect(),
                ),
            ),
        ]);
        write!(out, "{}\n", crate::yojson::safe::to_string(&j))
    } else {
        match &result.refused {
            Some(reason) => write!(out, "Did not run: {}\n", reason),
            None => {
                if result.isolatable {
                    write!(
                        out,
                        "Isolatable: no package boundary violated, over the {} checked.\n",
                        print_count(result.files_checked, "file")
                    )?
                } else {
                    write!(
                        out,
                        "Not isolatable: {}, from {} checked.\n",
                        print_count(result.violations.len() as isize, "package violation"),
                        print_count(result.files_checked, "file")
                    )?
                }
                // Paths the candidate could not be built from come before the violations:
                // they are an input problem, which outranks the verdict (see [status]),
                // and after a long list of violations they went unread.
                if !result.unknown_files.is_empty() {
                    write!(
                        out,
                        "Unknown to the naming table, so nothing was checked for them:\n"
                    )?;
                    for f in &result.unknown_files {
                        write!(out, "  {}\n", f)?
                    }
                }
                if !result.overridden_files.is_empty() {
                    write!(
                        out,
                        "Carry a __PackageOverride, so the candidate package cannot claim them:\n"
                    )?;
                    for f in &result.overridden_files {
                        write!(out, "  {}\n", f)?
                    }
                }
                for v in &result.violations {
                    write!(out, "  {}:{}  {}\n", v.referrer, v.line, v.message)?
                }
                Ok(())
            }
        }
    }
}

/// Exit status for the verdict, so a script need not parse stdout.
// A path the candidate could not be built from is an input problem and outranks
// the verdict, which did not cover it. A refusal outranks both: no verdict was
// reached at all, and what has to change is the server rather than the input.
pub fn status(result: &isolation_validation::Result) -> exit_status::T {
    if result.refused.is_some() {
        exit_status::T::ConfigError
    } else if !(result.unknown_files.is_empty() && result.overridden_files.is_empty()) {
        exit_status::T::InputError
    } else if result.isolatable {
        exit_status::T::NoError
    } else {
        exit_status::T::TypeError
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::server_command_types::isolation_validation::Violation;

    fn result() -> isolation_validation::Result {
        isolation_validation::Result {
            refused: None,
            isolatable: true,
            files_checked: 3,
            violations: vec![],
            unknown_files: vec![],
            overridden_files: vec![],
        }
    }

    fn text(r: &isolation_validation::Result, json: bool) -> String {
        let mut out = vec![];
        write_output(&mut out, r, json).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn verdicts() {
        let r = result();
        assert_eq!(
            text(&r, false),
            "Isolatable: no package boundary violated, over the 3 files checked.\n"
        );
        assert!(matches!(status(&r), exit_status::T::NoError));
        let r = isolation_validation::Result {
            isolatable: false,
            files_checked: 1,
            violations: vec![Violation {
                referrer: "a/b.php".to_string(),
                line: 4,
                message: "m".to_string(),
            }],
            unknown_files: vec!["x.php".to_string()],
            overridden_files: vec!["y.php".to_string()],
            ..result()
        };
        assert_eq!(
            text(&r, false),
            "Not isolatable: 1 package violation, from 1 file checked.\n\
             Unknown to the naming table, so nothing was checked for them:\n  x.php\n\
             Carry a __PackageOverride, so the candidate package cannot claim them:\n  y.php\n\
             \x20 a/b.php:4  m\n"
        );
        assert!(matches!(status(&r), exit_status::T::InputError));
        assert!(matches!(
            status(&isolation_validation::Result {
                unknown_files: vec![],
                overridden_files: vec![],
                ..r.clone()
            }),
            exit_status::T::TypeError
        ));
        assert_eq!(
            text(&r, true),
            "{\"refused\":null,\"isolatable\":false,\"files_checked\":1,\"violations\":[{\"referrer\":\"a/b.php\",\"line\":4,\"message\":\"m\"}],\"unknown_files\":[\"x.php\"],\"overridden_files\":[\"y.php\"]}\n"
        );
        let r = isolation_validation::Result {
            refused: Some("no".to_string()),
            ..result()
        };
        assert_eq!(text(&r, false), "Did not run: no\n");
        assert!(matches!(status(&r), exit_status::T::ConfigError));
    }
}
