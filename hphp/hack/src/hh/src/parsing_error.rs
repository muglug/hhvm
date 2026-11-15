// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/parsing_error.ml`: the type is
//! `oxidized::parsing_error::ParsingError`; this module has its
//! `to_user_diagnostic`. (`crate::naming_phase_error`, which is compiled without the
//! `port` feature, has its own copy, without the quickfixes.)

use bstr::BString;
use oxidized::diagnostics::Diagnostic;
use oxidized::parsing_error::ParsingError;
use oxidized::pos::Pos;

/// `to_user_diagnostic`.
///
/// Not `crate::naming_phase_error::to_user_diagnostic` (`Naming_phase_error.Parsing`),
/// which drops the `quickfixes` of a `Parsing_error`: those of the syntax
/// errors are made in `crate::full_fidelity_ast::process_syntax_errors`.
pub fn to_user_diagnostic(error: ParsingError) -> Diagnostic {
    use oxidized::error_codes::Parsing as error_code;
    use oxidized::explanation::Explanation;
    use oxidized::message::Message;
    let claim = |pos: Pos, msg: String| Message(pos, BString::from(msg));
    match error {
        ParsingError::FixmeFormat(pos) => crate::user_diagnostic::make_err(
            error_code::FixmeFormat as isize,
            None,
            None,
            None,
            None,
            claim(
                pos,
                "`HH_FIXME` wrong format, expected `/* HH_FIXME[ERROR_NUMBER] */`".to_string(),
            ),
            vec![],
            Explanation::Empty,
        ),
        ParsingError::HhIgnoreComment(pos) => crate::user_diagnostic::make_err(
            error_code::HhIgnoreComment as isize,
            None,
            None,
            None,
            None,
            claim(
                pos,
                "`HH_IGNORE_ERROR` comments are disabled by configuration and will soon be treated like normal comments, so you cannot use them to suppress errors".to_string(),
            ),
            vec![],
            Explanation::Empty,
        ),
        ParsingError::ParsingError {
            pos,
            msg,
            quickfixes,
        } => crate::user_diagnostic::make_err(
            error_code::ParsingError as isize,
            None,
            Some(quickfixes),
            None,
            None,
            claim(pos, msg),
            vec![],
            Explanation::Empty,
        ),
        ParsingError::XhpParsingError { pos, msg } => crate::user_diagnostic::make_err(
            error_code::XhpParsingError as isize,
            None,
            None,
            None,
            None,
            claim(pos, msg),
            vec![],
            Explanation::Empty,
        ),
        ParsingError::PackageConfigError { pos, msg, reasons } => crate::user_diagnostic::make_err(
            error_code::PackageConfigError as isize,
            None,
            None,
            None,
            None,
            claim(pos, msg),
            reasons,
            Explanation::Empty,
        ),
    }
}
