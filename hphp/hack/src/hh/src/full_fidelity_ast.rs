// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/full_fidelity_ast.ml` (the functions the providers need:
//! not `from_file`, `from_file_with_legacy` and `defensive_from_file`). See
//! `hh/PORTING.md`.
//!
//! `rust_from_text_ffi` is the Rust parser itself
//! (`aast_parser::AastParser::from_text`, as `aast_parser_ffi.rs` called
//! it), and `Full_fidelity_parser.parse_mode` is `mode_parser::parse_mode`
//! (as `rust_parser_ffi.rs` called it).
//!
//! The exceptions of the OCaml are panics: `failwith` is `panic!`, and
//! `raise (SyntaxError.ParserFatal (e, p))` raises a [`ParserFatal`].
//! `defensive_program` catches them all, as OCaml does.

use aast_parser::AastParser;
use aast_parser::rust_aast_parser_types;
use aast_parser::rust_aast_parser_types::ParserResult;
use bstr::BString;
use oxidized::diagnostics::Diagnostic;
use oxidized::file_info;
use oxidized::namespace_env;
use oxidized::nast;
use oxidized::parser_options::ParserOptions;
use oxidized::parsing_error::ParsingError;
use oxidized::pos::Pos;
use oxidized::scoured_comments::ScouredComments;
use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::syntax_error::SyntaxError;
use relative_path::RelativePath;

use crate::diagnostics as diagnostics;
use crate::fixme_provider;
use crate::full_fidelity_source_text as source_text_;
// module Lint = Lints_core
use crate::lints_core as lint;
use crate::parser_return;

/// `exception Full_fidelity_syntax_error.ParserFatal of t * Pos.t`: the
/// payload of the panic that [`from_text_rust`] raises when the parser fails.
#[derive(Clone, Debug)]
pub struct ParserFatal(pub SyntaxError, pub Pos);

/// Context of the file being parsed.
///
/// The `env` of the lowerer is "full request." It provides all the settings the
/// lowerer needs to produce an AST.
#[derive(Clone, Debug)]
pub struct Env {
    pub mode: namespace_env::Mode,
    pub php5_compat_mode: bool,
    pub elaborate_namespaces: bool,
    pub include_line_comments: bool,
    pub quick_mode: bool,
    /// Show errors even in quick mode.
    /// Hotfix until we can properly set up saved states to surface parse errors during
    /// typechecking properly.
    pub show_all_errors: bool,
    pub parser_options: ParserOptions,
    pub file: RelativePath,
    pub is_systemlib: bool,
}

pub fn make_env(
    mode: Option<namespace_env::Mode>,
    php5_compat_mode: Option<bool>,
    elaborate_namespaces: Option<bool>,
    include_line_comments: Option<bool>,
    quick_mode: Option<bool>,
    show_all_errors: Option<bool>,
    parser_options: Option<ParserOptions>,
    is_systemlib: Option<bool>,
    file: RelativePath,
) -> Env {
    let mode = mode.unwrap_or(namespace_env::Mode::ForTypecheck);
    let php5_compat_mode = php5_compat_mode.unwrap_or(false);
    let elaborate_namespaces = elaborate_namespaces.unwrap_or(true);
    let include_line_comments = include_line_comments.unwrap_or(false);
    let quick_mode = quick_mode.unwrap_or(false);
    let show_all_errors = show_all_errors.unwrap_or(false);
    let parser_options = parser_options.unwrap_or_default();
    let is_systemlib = is_systemlib.unwrap_or(false);
    let codegen = mode == namespace_env::Mode::ForCodegen;
    let parser_options = ParserOptions {
        codegen,
        ..parser_options
    };
    Env {
        mode,
        php5_compat_mode,
        elaborate_namespaces,
        include_line_comments,
        quick_mode: !codegen && quick_mode,
        show_all_errors,
        parser_options,
        file,
        is_systemlib,
    }
}

fn should_surface_errors(env: &Env) -> bool {
    // env.show_all_errors is a hotfix until we can retool how saved states handle
    // parse errors.
    !env.quick_mode || env.show_all_errors
}

struct AastResult {
    fi_mode: file_info::Mode,
    ast: nast::Program,
    content: BString,
    comments: ScouredComments,
}

/// Creates a relative position out of the error and the given path and source text.
fn pos_of_error(path: &RelativePath, source_text: &source_text_::T, error: &SyntaxError) -> Pos {
    source_text_::relative_pos(
        path,
        source_text,
        error.start_offset as isize,
        error.end_offset as isize,
    )
}

fn process_scour_comments(env: &Env, sc: &ScouredComments) {
    for pos in &sc.error_pos {
        diagnostics::add_diagnostic(crate::parsing_error::to_user_diagnostic(ParsingError::FixmeFormat(
            pos.clone(),
        )));
    }
    for pos in &sc.bad_ignore_pos {
        diagnostics::add_diagnostic(crate::parsing_error::to_user_diagnostic(
            ParsingError::HhIgnoreComment(pos.clone()),
        ));
    }
    // `provide_disallowed_fixmes`, `provide_ignores`, then
    // `provide_decl_hh_fixmes` or `provide_hh_fixmes` (by `quick_mode`); it
    // also makes this thread authoritative for the file's comments.
    fixme_provider::provide_scoured_comments(&env.file, sc, env.quick_mode);
}

fn process_lowerer_parsing_errors(env: &Env, lowerer_parsing_errors: Vec<(Pos, String)>) {
    if should_surface_errors(env) {
        for (pos, msg) in lowerer_parsing_errors {
            diagnostics::add_diagnostic(crate::parsing_error::to_user_diagnostic(
                ParsingError::ParsingError {
                    pos,
                    msg,
                    quickfixes: vec![],
                },
            ))
        }
    }
}

fn process_non_syntax_errors(_env: &Env, errors: Vec<Diagnostic>) {
    for error in errors {
        diagnostics::add_diagnostic(error)
    }
}

/// A lint of the Rust parser, which is a `Lints_core.t` of `lint_rust`.
fn lint_of_lint_rust(error: lint_rust::LintError) -> lint::T<Pos> {
    let lint_rust::LintError {
        code,
        severity,
        pos,
        message,
        bypass_changed_lines,
        autofix,
        check_status,
    } = error;
    lint::T {
        code,
        severity: match severity {
            lint_rust::Severity::LintError => lint::Severity::LintError,
            lint_rust::Severity::LintWarning => lint::Severity::LintWarning,
            lint_rust::Severity::LintAdvice => lint::Severity::LintAdvice,
            lint_rust::Severity::LintDisabled => lint::Severity::LintDisabled,
        },
        pos,
        message,
        bypass_changed_lines,
        autofix,
        check_status,
    }
}

fn process_lint_errors(_env: &Env, errors: Vec<lint_rust::LintError>) {
    for error in errors {
        lint::add_lint(lint_of_lint_rust(error))
    }
}

fn process_syntax_errors(env: &Env, source_text: &source_text_::T, errors: Vec<SyntaxError>) {
    let relative_pos = |e: &SyntaxError| pos_of_error(&env.file, source_text, e);

    let pos_of_offsets = |start_offset: usize, end_offset: usize| {
        source_text_::relative_pos(
            &env.file,
            source_text,
            start_offset as isize,
            end_offset as isize,
        )
    };

    let report_error = |e: SyntaxError| {
        let quickfixes = e
            .quickfixes
            .iter()
            .map(|qf| {
                let parser_core_types::syntax_error::SyntaxQuickfix { title, edits } = qf;
                let edits = crate::quickfix::Edits::Eager(
                    edits
                        .iter()
                        .map(|(start_offset, end_offset, new_text)| {
                            (new_text.clone(), pos_of_offsets(*start_offset, *end_offset))
                        })
                        .collect(),
                );
                crate::quickfix::make(title.clone(), edits, vec![])
            })
            .collect();

        diagnostics::add_diagnostic(crate::parsing_error::to_user_diagnostic(
            ParsingError::ParsingError {
                pos: relative_pos(&e),
                msg: e.message.to_string(),
                quickfixes,
            },
        ))
    };
    for e in errors {
        report_error(e)
    }
}

fn make_rust_env(env: &Env) -> rust_aast_parser_types::Env {
    rust_aast_parser_types::Env {
        mode: env.mode,
        elaborate_namespaces: env.elaborate_namespaces,
        php5_compat_mode: env.php5_compat_mode,
        include_line_comments: env.include_line_comments,
        quick_mode: env.quick_mode,
        show_all_errors: env.show_all_errors,
        is_systemlib: env.is_systemlib,
        for_debugger_eval: false,
        parser_options: env.parser_options.clone(),
        scour_comments: true,
    }
}

/// The exception `Failure` that `unwrap_rust_parser_result` raises for a
/// file that is not a Hack file (its message), which `defensive_program`
/// catches (`Exn.to_string`: `(Failure "...")`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure(pub String);

impl Failure {
    /// `Exn.to_string (Failure msg)`
    pub fn to_exn_string(&self) -> String {
        format!("(Failure {})", crate::rt::ocaml_printf::sprintf_s(&self.0))
    }
}

/// `unwrap_rust_parser_result`, with its `Failure` as an error (the other
/// exceptions it raises stay panics: nothing on the way catches them).
fn try_unwrap_rust_parser_result(
    st: &source_text_::T,
    rust_result: Result<ParserResult, aast_parser::Error>,
) -> Result<ParserResult, Failure> {
    match rust_result {
        Ok(r) => Ok(r),
        Err(aast_parser::Error::NotAHackFile()) => Err(Failure(format!(
            "Not a Hack file: {}",
            crate::relative_path::to_absolute(source_text_::file_path(st))
        ))),
        Err(aast_parser::Error::ParserFatal(e, p)) => std::panic::panic_any(ParserFatal(e, p)),
        Err(aast_parser::Error::Other(msg)) => panic!("{}", msg),
    }
}

fn unwrap_rust_parser_result(
    st: &source_text_::T,
    rust_result: Result<ParserResult, aast_parser::Error>,
) -> ParserResult {
    match try_unwrap_rust_parser_result(st, rust_result) {
        Ok(r) => r,
        Err(Failure(msg)) => panic!("{}", msg),
    }
}

/// from_text_rust are only used for testing
pub fn from_text_rust(env: &Env, source_text: &source_text_::T) -> ParserResult {
    let rust_env = make_rust_env(env);
    // `rust_from_text_ffi rust_env source_text`
    let indexed_source_text = IndexedSourceText::new(source_text_::source_text(source_text));
    let result = AastParser::from_text(&rust_env, &indexed_source_text, Default::default());
    unwrap_rust_parser_result(source_text, result)
}

/// [`from_text_rust`], with the `Failure` of a file that is not a Hack file
/// as an error.
fn try_from_text_rust(env: &Env, source_text: &source_text_::T) -> Result<ParserResult, Failure> {
    let rust_env = make_rust_env(env);
    let indexed_source_text = IndexedSourceText::new(source_text_::source_text(source_text));
    let result = AastParser::from_text(&rust_env, &indexed_source_text, Default::default());
    try_unwrap_rust_parser_result(source_text, result)
}

fn process_lowerer_result(env: &Env, source_text: &source_text_::T, r: ParserResult) -> AastResult {
    let ParserResult {
        file_mode,
        scoured_comments,
        aast,
        lowerer_parsing_errors,
        syntax_errors,
        errors,
        lint_errors,
        ..
    } = r;
    process_scour_comments(env, &scoured_comments);
    process_syntax_errors(env, source_text, syntax_errors);
    process_lowerer_parsing_errors(env, lowerer_parsing_errors);
    process_non_syntax_errors(env, errors);
    process_lint_errors(env, lint_errors);
    AastResult {
        fi_mode: file_mode,
        ast: aast,
        content: match env.mode {
            namespace_env::Mode::ForCodegen => BString::from(""),
            namespace_env::Mode::ForTypecheck => BString::from(source_text_::text(source_text)),
        },
        comments: scoured_comments,
    }
}

fn from_text(env: &Env, source_text: &source_text_::T) -> AastResult {
    process_lowerer_result(env, source_text, from_text_rust(env, source_text))
}

/// [`from_text`], with the `Failure` of a file that is not a Hack file as an
/// error.
fn try_from_text(env: &Env, source_text: &source_text_::T) -> Result<AastResult, Failure> {
    let r = try_from_text_rust(env, source_text)?;
    Ok(process_lowerer_result(env, source_text, r))
}

fn legacy(x: AastResult) -> parser_return::T {
    parser_return::T {
        file_mode: Some(x.fi_mode),
        comments: x.comments.comments,
        ast: x.ast,
        content: x.content,
    }
}

pub fn from_source_text_with_legacy(env: &Env, source_text: &source_text_::T) -> parser_return::T {
    legacy(from_text(env, source_text))
}

pub fn from_text_with_legacy(env: &Env, content: &[u8]) -> parser_return::T {
    let source_text = source_text_::make(&env.file, content);
    from_source_text_with_legacy(env, &source_text)
}

/// `Full_fidelity_parser.parse_mode`
fn full_fidelity_parser_parse_mode(source: &source_text_::T) -> Option<file_info::Mode> {
    let (_, mode) = mode_parser::parse_mode(&source_text_::source_text(source));
    mode.map(Into::into)
}

pub fn defensive_program(
    quick: Option<bool>,
    show_all_errors: Option<bool>,
    elaborate_namespaces: Option<bool>,
    include_line_comments: Option<bool>,
    parser_options: ParserOptions,
    fn_: &RelativePath,
    content: &[u8],
) -> parser_return::T {
    let quick = quick.unwrap_or(false);
    let show_all_errors = show_all_errors.unwrap_or(false);
    let elaborate_namespaces = elaborate_namespaces.unwrap_or(true);
    let include_line_comments = include_line_comments.unwrap_or(false);
    let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let source = source_text_::make(fn_, content);
        let env = make_env(
            None,
            None,
            Some(elaborate_namespaces),
            Some(include_line_comments),
            Some(quick),
            Some(show_all_errors),
            Some(parser_options),
            None,
            fn_.clone(),
        );
        try_from_text(&env, &source).map(legacy)
    }));
    // (`Failure` is an error, the other exceptions are panics.)
    let attempt = match attempt {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(failure)) => Err(failure.to_exn_string()),
        // `Exn.to_string e`
        Err(e) => Err(crate::exception::get_ctor_string(&crate::exception::wrap(e))),
    };
    match attempt {
        Ok(result) => result,
        Err(err) => {
            // `Rust_pointer.free_leaked_pointer ()`: nothing is leaked here.

            // If lowering fails, try to recover the file mode.
            let mode = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let source = source_text_::make(fn_, content);
                full_fidelity_parser_parse_mode(&source)
            })) {
                Ok(mode) => mode,
                Err(_) => None,
            };
            let fn_ = crate::relative_path::suffix(fn_);
            // If we've already found a parsing error, it's okay for lowering to fail
            if !diagnostics::currently_has_errors() {
                crate::hh_logger::log(&format!(
                    "Warning, lowering failed for {}\n  - error: {}\n",
                    fn_, err
                ));
            }

            parser_return::T {
                file_mode: mode,
                comments: vec![],
                ast: nast::Program(vec![]),
                content: BString::from(content),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;

    fn path() -> RelativePath {
        RelativePath::make(Prefix::Root, "a.php".into())
    }

    /// A file whose first line is not a Hack header the lowerer accepts
    /// (`<?/*c*/hh`, `<?php`, `<?`, `<??hh`): `Failure "Not a Hack file"`,
    /// which `defensive_program` turns into an empty program (the OCaml
    /// logs "Warning, lowering failed" and reports nothing), without a panic.
    #[test]
    fn not_a_hack_file_is_a_failure_not_a_panic() {
        crate::relative_path::set_path_prefix(
            crate::relative_path::Prefix::Root,
            std::path::Path::new("/"),
        );
        for header in ["<?/*c*/hh", "<?php", "<?", "<??hh"] {
            let content = format!("{header}\nfunction f(): void {{}}\n");
            let env = make_env(None, None, None, None, None, None, None, None, path());
            let source = source_text_::make(&path(), content.as_bytes());
            match diagnostics::do_(None, || try_from_text(&env, &source)).1 {
                Err(failure) => {
                    assert_eq!(failure, Failure("Not a Hack file: /a.php".to_string()));
                    assert_eq!(failure.to_exn_string(), "(Failure \"Not a Hack file: /a.php\")");
                }
                Ok(_) => panic!("{header}: lowered"),
            }
            let (errors, result) = diagnostics::do_(None, || {
                defensive_program(
                    None,
                    None,
                    None,
                    None,
                    ParserOptions::default(),
                    &path(),
                    content.as_bytes(),
                )
            });
            assert!(result.ast.0.is_empty(), "{header}");
            assert!(!diagnostics::has_errors(None, &errors), "{header}");
        }
        // `</*c*/?hh` is lowered (with a parsing error).
        let env = make_env(None, None, None, None, None, None, None, None, path());
        let source = source_text_::make(&path(), b"</*c*/?hh\nfunction f(): void {}\n");
        assert!(diagnostics::do_(None, || try_from_text(&env, &source)).1.is_ok());
    }

    #[test]
    fn quick_mode_and_codegen() {
        let env = make_env(None, None, None, None, Some(true), None, None, None, path());
        assert!(env.quick_mode);
        assert!(env.elaborate_namespaces);
        assert!(!should_surface_errors(&env));
        let env = make_env(
            Some(namespace_env::Mode::ForCodegen),
            None,
            None,
            None,
            Some(true),
            None,
            None,
            None,
            path(),
        );
        assert!(!env.quick_mode);
        assert!(env.parser_options.codegen);
    }

    #[test]
    fn parses_without_naming() {
        let (errors, result) = diagnostics::do_(None, || {
            defensive_program(
                None,
                None,
                None,
                None,
                ParserOptions::default(),
                &path(),
                b"<?hh\nclass C { public function f(): int { return 1; } }\nfunction g(): void {}\n",
            )
        });
        assert!(diagnostics::has_no_errors(None, &errors));
        assert_eq!(result.file_mode, Some(file_info::Mode::Mstrict));
        let names: Vec<&str> = result
            .ast
            .0
            .iter()
            .filter_map(|def| match def {
                nast::Def::Class(c) => Some(c.name.1.as_str()),
                nast::Def::Fun(f) => Some(f.name.1.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(names, vec!["\\C", "\\g"]);
    }

    #[test]
    fn reports_syntax_errors() {
        let (errors, result) = diagnostics::do_(None, || {
            defensive_program(
                None,
                None,
                None,
                None,
                ParserOptions::default(),
                &path(),
                b"<?hh\nfunction f( {}\n",
            )
        });
        assert!(diagnostics::has_errors(None, &errors));
        assert_eq!(result.file_mode, Some(file_info::Mode::Mstrict));
    }
}
