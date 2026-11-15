// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: from the text of a file to its named AST, what the
//! OCaml does through `Ast_provider` (`Full_fidelity_ast`) and
//! `Naming.program`.

use std::sync::Arc;

use aast_parser::AastParser;
use oxidized::diagnostics::Diagnostic;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::scoured_comments::ScouredComments;
use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::source_text::SourceText;
use relative_path::RelativePath;

use crate::ctx::Ctx;
use crate::diagnostics_helpers;

pub struct NamedFile {
    pub path: Arc<RelativePath>,
    /// The named AST. Empty if the file could not be parsed at all.
    pub program: nast::Program,
    /// Parsing errors, and the errors found while lowering.
    pub diagnostics: Vec<Diagnostic>,
    /// Errors found while naming.
    pub naming_errors: Vec<NamingPhaseError>,
    /// The `HH_FIXME` comments of the file, among others.
    pub comments: ScouredComments,
}

/// `Parsing[1001]`, `Parsing_error.Fixme_format`.
const FIXME_FORMAT: isize = 1001;
/// `Parsing[1008]`, `Parsing_error.Hh_ignore_comment`.
const HH_IGNORE_COMMENT: isize = 1008;

/// Parse and name one file.
pub fn parse_and_name(ctx: &Ctx, path: &Arc<RelativePath>, text: &[u8]) -> NamedFile {
    let source = SourceText::make(Arc::clone(path), text);
    let indexed = IndexedSourceText::new(source);
    let mut out = NamedFile {
        path: Arc::clone(path),
        program: nast::Program(vec![]),
        diagnostics: vec![],
        naming_errors: vec![],
        comments: Default::default(),
    };

    let result = match AastParser::from_text(&ctx.parser_env, &indexed, Default::default()) {
        Ok(result) => result,
        // Not a Hack file (no `<?hh`, say): nothing to check.
        Err(_) => return out,
    };

    // `Full_fidelity_ast.from_text_rust`: the comments first, then the
    // syntax errors, the lowerer's errors and the other errors.
    for pos in &result.scoured_comments.error_pos {
        out.diagnostics.push(diagnostics_helpers::error(
            FIXME_FORMAT,
            pos.clone(),
            "`HH_FIXME` wrong format, expected `/* HH_FIXME[ERROR_NUMBER] */`",
        ));
    }
    for pos in &result.scoured_comments.bad_ignore_pos {
        out.diagnostics.push(diagnostics_helpers::error(
            HH_IGNORE_COMMENT,
            pos.clone(),
            "`HH_IGNORE_ERROR` comments are disabled by configuration and will soon be treated like normal comments, so you cannot use them to suppress errors",
        ));
    }
    for error in &result.syntax_errors {
        let pos = indexed.relative_pos(error.start_offset, error.end_offset);
        out.diagnostics.push(diagnostics_helpers::error(
            diagnostics_helpers::PARSING_ERROR,
            Pos::from_lnum_bol_offset(pos.path, pos.start, pos.end),
            error.message.to_string(),
        ));
    }
    for (pos, msg) in result.lowerer_parsing_errors {
        out.diagnostics
            .push(diagnostics_helpers::error(diagnostics_helpers::PARSING_ERROR, pos, msg));
    }
    out.diagnostics.extend(result.errors);
    out.comments = result.scoured_comments;

    let mut program = result.aast;
    out.naming_errors = elab::elaborate_program(
        &ctx.tco,
        path,
        &mut program,
        result.active_experimental_features,
    );
    out.program = program;
    out
}
