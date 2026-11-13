// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_lint_types.ml`. See `hh/PORTING.md`.
//!
//! The type was ported by the client-connection assignment (D1), for the
//! results of `Server_command_types.LINT`, `LINT_STDIN` and `LINT_ALL`;
//! `output_json` and `output_text` by **LINT** (plan §7.3).
//!
//! `oc` is a `std::io::Write`; write errors are ignored (in OCaml they raise
//! `Sys_error`, which nothing catches on these paths).

use std::io::Write;

use crate::diagnostics_state::Format;
use crate::lints_core as lint;
use crate::yojson::safe as yojson;

/// `type result = Pos.absolute Lint.t list`
pub type Result = Vec<crate::lints_core::T<crate::pos::Absolute>>;

/// `output_json ?(from_test = false) ?(pretty = false) oc el`
pub fn output_json(
    from_test: Option<bool>,
    pretty: Option<bool>,
    oc: &mut dyn Write,
    el: &[crate::lints_core::T<crate::pos::Absolute>],
) {
    let from_test = from_test.unwrap_or(false);
    let pretty = pretty.unwrap_or(false);
    let errors_json: Vec<yojson::T> = el.iter().map(lint::to_json).collect();
    let version = if from_test {
        String::new()
    } else {
        crate::hh_version::version()
    };
    let res = yojson::T::Assoc(vec![
        ("errors".to_string(), yojson::T::List(errors_json)),
        ("version".to_string(), yojson::T::String(version)),
    ]);
    let json_str = if pretty {
        format!("{}\n", crate::rt::yojson_ext::pretty_to_string(&res))
    } else {
        yojson::to_string(&res)
    };
    let _ = oc.write_all(json_str.as_bytes());
    let _ = oc.flush();
    let _ = std::io::stderr().flush();
}

/// `output_text oc el format`
pub fn output_text(
    oc: &mut dyn Write,
    el: &[crate::lints_core::T<crate::pos::Absolute>],
    format: Format,
) {
    // Essentially the same as type error output, except that we only have one
    // message per error, and no additional 'typing reasons'
    if el.is_empty() {
        let _ = oc.write_all(b"No lint errors!\n");
    } else {
        let f: fn(&crate::lints_core::T<crate::pos::Absolute>) -> String = match format {
            Format::Extended | Format::Context => lint::to_contextual_string,
            Format::PlainHighlighted => |lint| lint::to_plain_highlighted_string(None, lint),
            Format::Raw | Format::Agent | Format::Plain => lint::to_string,
            Format::Highlighted => lint::to_highlighted_string,
        };
        let sl: Vec<String> = el.iter().map(f).collect();
        for s in sl {
            // `Printf.fprintf oc "%s\n%!" s`
            let _ = oc.write_all(s.as_bytes());
            let _ = oc.write_all(b"\n");
            let _ = oc.flush();
        }
    }
    let _ = oc.flush();
}
