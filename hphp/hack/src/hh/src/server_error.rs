// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_error.ml`. See `hh/PORTING.md`.
//!
//! `Out_channel.t` is `&mut dyn std::io::Write`; a write that fails panics,
//! as `Out_channel.output_string` raises `Sys_error`.

use crate::diagnostics;
use crate::diagnostics::Format;
use crate::extended_diagnostic_formatter;
use crate::hh_version;
use crate::pos::Absolute;
use crate::telemetry;
use crate::user_diagnostic;
use crate::user_diagnostic::Severity;
use crate::yojson::safe as yojson;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// `Out_channel.output_string`
fn output_string(oc: &mut dyn std::io::Write, s: &str) {
    if let Err(e) = oc.write_all(s.as_bytes()) {
        panic!("Sys_error: {}", e)
    }
}

/// `Out_channel.flush`
fn flush(oc: &mut dyn std::io::Write) {
    if let Err(e) = oc.flush() {
        panic!("Sys_error: {}", e)
    }
}

// ****************************************************************************
// Error module
// ****************************************************************************

fn get_error_list_json(
    error_format: Option<Format>,
    error_list: &[FinalizedDiagnostic],
    save_state_result: Option<&crate::save_state_service_types::SaveStateResult>,
    recheck_stats: Option<&telemetry::T>,
) -> yojson::T {
    let error_format = diagnostics::format_or_default(error_format);
    // for extended reasons, we produce a human-readable format.
    let human_formatter: Option<&dyn Fn(&FinalizedDiagnostic) -> String> = match error_format {
        Format::Extended => Some(&extended_diagnostic_formatter::to_string),
        Format::Context
        | Format::Agent
        | Format::Raw
        | Format::Highlighted
        | Format::Plain
        | Format::PlainHighlighted => None,
    };
    let (error_list, did_pass) = match error_list {
        [] => (vec![], true),
        error_list => {
            let passed = !error_list.iter().any(|error| match error.severity {
                Severity::Err => true,
                Severity::Warning { .. } => false,
            });
            (
                error_list
                    .iter()
                    .map(|e| user_diagnostic::to_json(human_formatter, |s| s, e))
                    .collect(),
                passed,
            )
        }
    };
    let properties = vec![
        ("passed".to_string(), yojson::T::Bool(did_pass)),
        ("errors".to_string(), yojson::T::List(error_list)),
        ("version".to_string(), hh_version::version_json()),
    ];
    // (`save_state_result`: as the OCaml had it with `--save-state`, for the
    // saved-state producer.)
    let properties = match save_state_result {
        None => properties,
        Some(save_state_result) => {
            let mut l = vec![(
                "save_state_result".to_string(),
                yojson::T::Assoc(vec![(
                    "dep_table_edges_added".to_string(),
                    yojson::T::Int(save_state_result.dep_table_edges_added),
                )]),
            )];
            l.extend(properties);
            l
        }
    };
    let properties = match recheck_stats {
        None => properties,
        Some(telemetry) => {
            let mut l = vec![("last_recheck".to_string(), telemetry::to_yojson(telemetry))];
            l.extend(properties);
            l
        }
    };
    yojson::T::Assoc(properties)
}

fn print_error_list_json(
    oc: &mut dyn std::io::Write,
    error_format: Option<Format>,
    error_list: &[FinalizedDiagnostic],
    save_state_result: Option<&crate::save_state_service_types::SaveStateResult>,
    recheck_stats: Option<&telemetry::T>,
) {
    let res = get_error_list_json(error_format, error_list, save_state_result, recheck_stats);
    // `Yojson.Safe.to_channel`: the compact form, with no newline.
    output_string(oc, &yojson::to_string(&res));
    flush(oc);
}

pub fn print_error_list(
    oc: &mut dyn std::io::Write,
    stale_msg: Option<&str>,
    output_json: bool,
    error_format: Option<Format>,
    error_list: &[FinalizedDiagnostic],
    recheck_stats: Option<&telemetry::T>,
) {
    print_error_list_with_save_state_result(oc, stale_msg, output_json, error_format, error_list, None, recheck_stats)
}

/// `print_error_list oc ~stale_msg ~output_json ~error_format ~error_list
/// ~save_state_result ~recheck_stats`, as the OCaml had it before
/// `--save-state` was removed (the saved-state producer uses it).
pub fn print_error_list_with_save_state_result(
    oc: &mut dyn std::io::Write,
    stale_msg: Option<&str>,
    output_json: bool,
    error_format: Option<Format>,
    error_list: &[FinalizedDiagnostic],
    save_state_result: Option<&crate::save_state_service_types::SaveStateResult>,
    recheck_stats: Option<&telemetry::T>,
) {
    if output_json {
        print_error_list_json(oc, error_format, error_list, save_state_result, recheck_stats)
    } else if error_list.is_empty() {
        output_string(oc, "No errors!\n")
    } else {
        let sl: Vec<String> = error_list.iter().map(user_diagnostic::to_string).collect();
        let sl = crate::rt::ocaml_list::dedup_and_sort(sl, |a, b| a.as_bytes().cmp(b.as_bytes()));
        for s in sl {
            output_string(oc, &s);
            output_string(oc, "\n");
        }
    }
    if let Some(msg) = stale_msg {
        output_string(oc, msg)
    }
    flush(oc);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    fn print(
        stale_msg: Option<&str>,
        output_json: bool,
        error_format: Option<Format>,
        error_list: &[FinalizedDiagnostic],
        recheck_stats: Option<&telemetry::T>,
    ) -> String {
        let mut out: Vec<u8> = vec![];
        print_error_list(
            &mut out,
            stale_msg,
            output_json,
            error_format,
            error_list,
            recheck_stats,
        );
        String::from_utf8(out).unwrap()
    }

    fn diag(severity: Severity, line: usize, msg: &str) -> FinalizedDiagnostic {
        fx::diagnostic(
            severity,
            4110,
            fx::msg(fx::pos("/nonexistent/a.php", (line, 0), (line, 3)), msg),
            vec![],
        )
    }

    /// Every line of the files is empty for these positions: line `n` starts
    /// at offset 0.
    fn errors() -> Vec<FinalizedDiagnostic> {
        vec![
            diag(Severity::Warning { is_trusted: true }, 1, "w"),
            diag(Severity::Err, 9, "nine"),
            diag(Severity::Err, 10, "ten"),
            diag(Severity::Err, 9, "nine"),
        ]
    }

    #[test]
    fn no_errors() {
        assert_eq!(print(None, false, None, &[], None), "No errors!\n");
        assert_eq!(
            print(Some("stale\n"), false, Some(Format::Raw), &[], None),
            "No errors!\nstale\n"
        );
    }

    /// `hh_server --check`: `Diagnostics.to_string` blocks, deduplicated and
    /// sorted as strings (`line 10` before `line 9`, `ERROR` before `WARN`),
    /// whatever the error format.
    #[test]
    fn text_is_sorted_as_strings() {
        let block = |sev: &str, line: usize, msg: &str| {
            format!(
                "{sev}: File \"/nonexistent/a.php\", line {line}, characters 1-3:\n{msg} (Typing[4110])\n\n"
            )
        };
        let expected =
            block("ERROR", 10, "ten") + &block("ERROR", 9, "nine") + &block("WARN", 1, "w");
        assert_eq!(print(None, false, None, &errors(), None), expected);
        assert_eq!(
            print(
                Some("stale"),
                false,
                Some(Format::Highlighted),
                &errors(),
                None
            ),
            expected + "stale"
        );
    }

    /// `--json`: no newline at the end; `passed` ignores warnings;
    /// `last_recheck` comes first.
    #[test]
    fn json() {
        let version = yojson::to_string(&hh_version::version_json());
        let error = |line: usize, msg: &str, severity: &str| {
            format!(
                "{{\"severity\":\"{severity}\",\"is_trusted\":true,\"message\":[{{\"descr\":\"{msg}\",\"path\":\"/nonexistent/a.php\",\"line\":{line},\"start\":1,\"end\":3,\"code\":4110}}],\"custom_messages\":[]}}"
            )
        };
        assert_eq!(
            print(None, true, None, &errors()[..1], None),
            format!(
                "{{\"passed\":true,\"errors\":[{}],\"version\":{version}}}",
                error(1, "w", "warning")
            )
        );
        assert_eq!(
            print(Some("stale"), true, None, &errors()[1..2], None),
            format!(
                "{{\"passed\":false,\"errors\":[{}],\"version\":{version}}}stale",
                error(9, "nine", "error")
            )
        );
        let stats = telemetry::int_("k", 1, telemetry::create());
        assert_eq!(
            print(None, true, None, &[], Some(&stats)),
            format!(
                "{{\"last_recheck\":{{\"k\":1}},\"passed\":true,\"errors\":[],\"version\":{version}}}"
            )
        );
    }

    /// With `--error-format extended`, each error has its `human_format`.
    #[test]
    fn json_extended_has_human_format() {
        let out = fx::run_in_suite(
            module_path!(),
            "json_extended_has_human_format",
            "extended_reasons",
            false,
            || {
                let e = fx::err(
                    4110,
                    fx::msg(
                        fx::pos("fn_ret.php", (8, 9), (8, 14)),
                        "Invalid return type",
                    ),
                    vec![],
                );
                let mut out: Vec<u8> = vec![];
                print_error_list(
                    &mut out,
                    None,
                    true,
                    Some(Format::Extended),
                    &[e.clone()],
                    None,
                );
                let human = extended_diagnostic_formatter::to_string(&e);
                let json = String::from_utf8(out).unwrap();
                assert!(json.contains(&yojson::to_string(&yojson::T::String(human))));
                assert!(json.contains("\"human_format\":"));
                "ok".to_string()
            },
        );
        if let Some(out) = out {
            assert_eq!(out, "ok");
        }
    }
}
