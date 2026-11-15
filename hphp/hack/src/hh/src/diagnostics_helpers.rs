// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: Rust-only helpers that build, order and print
//! diagnostics for the driver modules (`check`, `parse`, `typing_slice`,
//! `naming_phase_error`, ...). This is not the OCaml `Diagnostics`, which is
//! ported in `crate::diagnostics`; [`is_fixmed`] and [`sort_and_dedup`]
//! are simplified forms of its `try_apply_fixme` and `sort`.

use std::fmt::Write;

use bstr::BString;
use bstr::ByteSlice;
use oxidized::diagnostics::Diagnostic;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::user_diagnostic::Severity;
use oxidized::user_diagnostic::UserDiagnostic;

/// The phase an error code belongs to, as printed in `(Typing[4110])`.
pub fn phase_of_code(code: isize) -> &'static str {
    match code / 1000 {
        1 => "Parsing",
        2 => "Naming",
        3 => "NastCheck",
        4 => "Typing",
        5 => "Lint",
        8 => "Init",
        12 => "Warn",
        _ => "Other",
    }
}

/// The code of every syntax error.
pub const PARSING_ERROR: isize = 1002;

pub fn error(code: isize, pos: Pos, msg: impl Into<String>) -> Diagnostic {
    error_with_reasons(code, pos, msg, vec![])
}

pub fn error_with_reasons(
    code: isize,
    pos: Pos,
    msg: impl Into<String>,
    reasons: Vec<(Pos, String)>,
) -> Diagnostic {
    UserDiagnostic::new(
        Severity::Err,
        code,
        Message(pos, BString::from(msg.into())),
        reasons
            .into_iter()
            .map(|(pos, msg)| Message(pos, BString::from(msg)))
            .collect(),
        Explanation::Empty,
        vec![],
        vec![],
    )
}

/// Whether an error with this code at this position is silenced by a
/// `/* HH_FIXME[code] */` comment (`ScouredComments::fixmes`: the comments by
/// the line of the code they apply to).
///
/// This is the lookup of `Fixme_provider.get_fixme_codes_for_pos` only. What
/// `Diagnostics.try_apply_fixme` does with it is not ported: every code can
/// be silenced (`allowed_fixme_codes_strict` and the codes that can never be
/// are not looked at), in every position (the `HH_FIXME`s of declarations,
/// `ScouredComments::misuses`, are not reported), and the error "You cannot
/// use `HH_FIXME` or `HH_IGNORE_ERROR` comments to suppress error N" does not
/// exist.
pub fn is_fixmed(fixmes: &oxidized::scoured_comments::Fixmes, pos: &Pos, code: isize) -> bool {
    let (line, _, _) = pos.info_pos();
    fixmes
        .get(&(line as isize))
        .is_some_and(|codes| codes.contains_key(&code))
}

/// `File "foo.php", line 3, characters 5-7:`
///
/// The file is printed relative to its root, which is what the test suites
/// expect.
fn pos_string(pos: &Pos) -> String {
    let (line, start, end) = pos.info_pos();
    format!(
        "File {:?}, line {}, characters {}-{}:",
        pos.filename().path().display().to_string(),
        line,
        start,
        end
    )
}

/// The `plain` error format of `hh`.
pub fn to_plain_string(d: &Diagnostic) -> String {
    let mut out = String::new();
    let Message(pos, msg) = &d.claim;
    let _ = writeln!(
        out,
        "{}: {}\n{} ({}[{:04}])",
        d.severity.to_all_caps_string(),
        pos_string(pos),
        msg.to_str_lossy(),
        phase_of_code(d.code),
        d.code
    );
    // Only the first line of a reason that spans several is indented.
    for Message(pos, msg) in &d.reasons {
        let _ = writeln!(out, "  {}\n  {}", pos_string(pos), msg.to_str_lossy());
    }
    for msg in &d.custom_msgs {
        let _ = writeln!(out, "  {}", msg);
    }
    out
}

/// Put diagnostics in the order they are reported in, without duplicates.
pub fn sort_and_dedup(diagnostics: &mut Vec<Diagnostic>) {
    diagnostics.sort();
    // Errors that say the same thing at the same place are reported once,
    // even when their codes differ (within a phase): the first one is kept.
    diagnostics.dedup_by(|later, earlier| earlier.cmp_impl(later, true).is_eq());
}
