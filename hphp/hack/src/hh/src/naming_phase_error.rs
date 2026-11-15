// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_phase_error.ml` (`to_user_diagnostic`, `emit`,
//! `emit_experimental_feature`): the messages of the errors found while
//! naming.
//!
//! `elab` reports structured errors (`NamingPhaseError`); this module turns
//! them into diagnostics with the same codes, positions and wording as
//! `hh_server`, with `crate::naming_error_utils`, `crate::nast_check_error`
//! and a copy of `Parsing_error.to_user_diagnostic`. These three and
//! [`render`] (the parts of `Render`, `Markdown_lite` and `Utils` they use)
//! are compiled without the `port` feature too.
//!
//! The errors come from naming (`elab`) and from the checks on the named AST
//! (`crate::nast_check`).
//!
//! What `hh_server` does and this does not: quickfixes, the messages of the
//! custom error config, and `HH_FIXME`s.

pub(crate) mod render;

use bstr::ByteSlice;
use oxidized::diagnostics::Diagnostic;
use oxidized::error_codes::Parsing;
use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::naming_phase_error::ExperimentalFeature;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::parsing_error::ParsingError;
use oxidized::pos::Pos;

use crate::diagnostics_helpers;

/// The diagnostic `hh_server` reports for `error`.
pub fn to_user_diagnostic(error: NamingPhaseError) -> Diagnostic {
    match error {
        NamingPhaseError::Naming(error) => crate::naming_error_utils::to_user_diagnostic(error),
        NamingPhaseError::NastCheck(error) => crate::nast_check_error::to_user_diagnostic(error),
        NamingPhaseError::UnexpectedHint(pos) => {
            internal_error(pos, "Unexpected hint not present on legacy AST")
        }
        NamingPhaseError::MalformedAccess(pos) => internal_error(
            pos,
            "Malformed hint: expected Haccess (Happly ...) from ast_to_nast",
        ),
        NamingPhaseError::ExperimentalFeature(feature) => emit_experimental_feature(feature),
        NamingPhaseError::Parsing(error) => parsing_error_to_user_diagnostic(error),
    }
}

/// `Diagnostics.internal_error`
fn internal_error(pos: Pos, msg: &str) -> Diagnostic {
    diagnostics_helpers::error(
        Typing::InternalError as isize,
        pos,
        format!("Internal error: {}", msg),
    )
}

/// `Naming_phase_error.emit_experimental_feature`
fn emit_experimental_feature(feature: ExperimentalFeature) -> Diagnostic {
    let (pos, msg) = match feature {
        ExperimentalFeature::Supportdyn(pos) => (pos, "supportdyn type hint"),
        ExperimentalFeature::ConstAttr(pos) => (pos, "The __Const attribute is not supported."),
        ExperimentalFeature::ConstStaticProp(pos) => (pos, "Const properties cannot be static."),
    };
    // `Diagnostics.experimental_feature`: these errors have no code.
    diagnostics_helpers::error(0, pos, format!("Cannot use experimental feature: {}", msg))
}

/// `Parsing_error.to_user_diagnostic` (`crate::parsing_error::to_user_diagnostic`,
/// which this module, compiled without the `port` feature, cannot use; this one drops
/// the quickfixes).
fn parsing_error_to_user_diagnostic(error: ParsingError) -> Diagnostic {
    match error {
        ParsingError::FixmeFormat(pos) => diagnostics_helpers::error(
            Parsing::FixmeFormat as isize,
            pos,
            "`HH_FIXME` wrong format, expected `/* HH_FIXME[ERROR_NUMBER] */`",
        ),
        ParsingError::HhIgnoreComment(pos) => diagnostics_helpers::error(
            Parsing::HhIgnoreComment as isize,
            pos,
            "`HH_IGNORE_ERROR` comments are disabled by configuration and will soon be treated like normal comments, so you cannot use them to suppress errors",
        ),
        ParsingError::ParsingError {
            pos,
            msg,
            quickfixes: _,
        } => diagnostics_helpers::error(Parsing::ParsingError as isize, pos, msg),
        ParsingError::XhpParsingError { pos, msg } => {
            diagnostics_helpers::error(Parsing::XhpParsingError as isize, pos, msg)
        }
        ParsingError::PackageConfigError { pos, msg, reasons } => diagnostics_helpers::error_with_reasons(
            Parsing::PackageConfigError as isize,
            pos,
            msg,
            reasons
                .into_iter()
                .map(|Message(pos, msg)| (pos, msg.to_str_lossy().into_owned()))
                .collect(),
        ),
    }
}

/// `Naming_phase_error.emit`: report the errors through `Diagnostics`.
#[cfg(feature = "port")]
pub fn emit(errors: Vec<NamingPhaseError>) {
    for error in errors {
        let diagnostic = to_user_diagnostic(error);
        crate::diagnostics::add_diagnostic(diagnostic);
    }
}

#[cfg(test)]
mod tests {
    use oxidized::naming_error::NamingError;
    use oxidized::nast_check_error::NastCheckError;

    use super::*;

    /// The code, the message and the messages of the reasons.
    fn render(error: impl Into<NamingPhaseError>) -> (isize, String, Vec<String>) {
        let d = to_user_diagnostic(error.into());
        let Message(_, claim) = &d.claim;
        (
            d.code,
            claim.to_string(),
            d.reasons
                .iter()
                .map(|Message(_, msg)| msg.to_string())
                .collect(),
        )
    }

    // The expected messages are those of hphp/hack/test/typecheck.

    #[test]
    fn this_as_lexical_variable() {
        assert_eq!(
            render(NamingError::ThisAsLexicalVariable(Pos::NONE)),
            (
                2077,
                "Cannot use `$this` as lexical variable".to_string(),
                vec![]
            )
        );
    }

    #[test]
    fn did_you_mean() {
        assert_eq!(
            render(NamingError::DidYouMean {
                pos: Pos::NONE,
                name: "\\cAmelCase".to_string(),
                suggest_pos: Pos::NONE,
                suggest_name: "\\CamelCase".to_string(),
            }),
            (
                2006,
                "Could not find `cAmelCase`.".to_string(),
                vec![
                    "Did you mean `~~Ca~~melCase` instead (which only differs by case)?"
                        .to_string()
                ]
            )
        );
        assert_eq!(
            render(NamingError::Undefined {
                pos: Pos::NONE,
                var_name: "$B".to_string(),
                did_you_mean: Some(("$b".to_string(), Pos::NONE)),
            }),
            (
                2050,
                "Variable `$B` is undefined, or not always defined.".to_string(),
                vec!["Did you mean `$~~b~~` instead (which only differs by case)?".to_string()]
            )
        );
        assert_eq!(
            render(NamingError::Undefined {
                pos: Pos::NONE,
                var_name: "$x".to_string(),
                did_you_mean: Some(("$y".to_string(), Pos::NONE)),
            })
            .2,
            vec!["Did you mean `$y` instead?".to_string()]
        );
    }

    #[test]
    fn unbound_name() {
        assert_eq!(
            render(NamingError::UnboundName {
                pos: Pos::NONE,
                name: "\\HH\\Traversable".to_string(),
                kind: oxidized::name_context::NameContext::ClassContext,
            }),
            (
                2049,
                "Unbound name: `Traversable` (an object type)".to_string(),
                vec![]
            )
        );
        assert_eq!(
            render(NamingError::UnboundAttributeName {
                pos: Pos::NONE,
                attr_name: "__Foo".to_string(),
                closest_attr_name: None,
            })
            .1,
            "Unrecognized user attribute: `__Foo` starts with __ but is not a standard attribute"
        );
    }

    #[test]
    fn attribute_arity() {
        // The code depends on the number of arguments given.
        let error = |actual| NastCheckError::AttributeNotExactNumberOfArgs {
            pos: Pos::NONE,
            name: "__Docs".to_string(),
            actual,
            expected: 1,
        };
        let msg = "The attribute `__Docs` expects exactly 1 argument".to_string();
        assert_eq!(render(error(2)), (4126, msg.clone(), vec![]));
        assert_eq!(render(error(0)), (4153, msg, vec![]));
        assert_eq!(
            render(NastCheckError::AttributeTooManyArguments {
                pos: Pos::NONE,
                name: "__Memoize".to_string(),
                expected: 1,
            })
            .1,
            "The attribute `__Memoize` expects at most 1 argument"
        );
    }

    #[test]
    fn without_a_code() {
        assert_eq!(
            render(ExperimentalFeature::Supportdyn(Pos::NONE)),
            (
                0,
                "Cannot use experimental feature: supportdyn type hint".to_string(),
                vec![]
            )
        );
        assert_eq!(
            render(NamingPhaseError::UnexpectedHint(Pos::NONE)).1,
            "Internal error: Unexpected hint not present on legacy AST"
        );
    }
}
