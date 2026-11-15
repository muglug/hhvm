// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linting_main.ml`. See `hh/PORTING.md`.
//!
//! The linters are the `linter_*.rs` modules, one per `lints/linter_*.ml`. `Linting_service` is the open-source stub
//! (`stubs/linting_service.ml`): it has no linters.
//!
//! The lints are collected by `Lints_core.do_` around [`lint`] (see
//! `crate::lints_core`).

use std::sync::Arc;
use std::sync::atomic::Ordering;

use crate::ctx::Ctx;
use crate::diagnostics;
use crate::linter_async_lambda;
use crate::linter_branches_return_same_value;
use crate::linter_class_overrides_trait;
use crate::linter_clone;
use crate::linter_comparing_booleans;
use crate::linter_expr_tree_types;
use crate::linter_foreach_shadow;
use crate::linter_internal_class;
use crate::linter_invariant_violation;
use crate::linter_missing_override_attribute;
use crate::linter_pointless_booleans;
use crate::linter_redundant_cast;
use crate::linter_redundant_generics;
use crate::linter_unconditional_recursion;
use crate::linting_visitors;
use crate::parser_return;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_visitor;

/// An untyped linter: `go tcopt fn pr` (the `tcopt` of OCaml is the context).
pub type UntypedLinter = fn(&Arc<Ctx>, &RelativePath, &parser_return::T);

/// `Tast_visitor.handler`
type Handler<'a> = Box<dyn tast_visitor::Handler<'a> + 'a>;

pub fn untyped_linters() -> Vec<UntypedLinter> {
    let mut linters: Vec<UntypedLinter> = vec![
        linter_clone::go,
        linter_foreach_shadow::go,
        linter_invariant_violation::go,
    ];
    linters.extend(crate::linting_service::untyped_linters());
    linters
}

pub fn typed_linters<'a>(tcopt: &crate::typechecker_options::T) -> Vec<Handler<'a>> {
    let warning_handlers: Vec<Handler<'a>> = crate::tast_check::warning_checks()
        .into_iter()
        .filter_map(|m| {
            if
            // We only deactivate if all codes for this lint are checked as warnings
            // and warnings are turned on by default
            tcopt.warnings_default_all
                && (m.error_codes)()
                    .into_iter()
                    .all(|code| crate::typing_warning_utils::code_is_enabled(tcopt, code))
            {
                None
            } else {
                Some((m.handler)(true))
            }
        })
        .collect();
    let mut handlers: Vec<Handler<'a>> = vec![
        linter_missing_override_attribute::handler(),
        linter_redundant_generics::handler(),
        linter_class_overrides_trait::handler(),
        linter_expr_tree_types::handler(),
        linter_redundant_cast::handler(),
        linter_pointless_booleans::handler(),
        linter_comparing_booleans::handler(),
        linter_unconditional_recursion::handler(),
        linter_branches_return_same_value::handler(),
        linter_internal_class::handler(),
        linter_async_lambda::handler(),
    ];
    handlers.extend(warning_handlers);
    handlers.extend(crate::linting_service::typed_linters());
    handlers
}

pub fn lint_tast(ctx: &Arc<Ctx>, tast: &[tast::Def]) {
    let tcopt = provider_context::get_tcopt(ctx);
    tast_visitor::iter_with(None, typed_linters(&tcopt)).go(ctx, tast)
}

/// Most lint rules are easier to write against the named AST. However, some
/// things that we want to lint for are discarded / simplified by the time we
/// reach that stage, so we have a few lint rules that get checked during or
/// right after parsing.
pub fn parse_and_lint(fn_: &RelativePath, content: &[u8], ctx: &Arc<Ctx>) -> parser_return::T {
    let parser_result = diagnostics::ignore_(|| {
        crate::full_fidelity_ast::defensive_program(
            None,
            None,
            Some(true),
            None,
            provider_context::get_popt(ctx).clone(),
            fn_,
            content,
        )
    });
    crate::linter_ast::go(&parser_result.ast);
    parser_result
}

pub fn lint_nast(ctx: &Arc<Ctx>, fn_: &RelativePath, pr: &parser_return::T) {
    linting_visitors::reset();
    for go in untyped_linters() {
        go(ctx, fn_, pr)
    }

    // Run Nast visitors
    linting_visitors::FileVisitor::on_file(
        &mut linting_visitors::body_visitor_invoker(),
        (),
        ctx,
        fn_,
        pr,
    );
}

/// The lints of `fn_`, whose contents are `content`, for `Lints_core.do_`
/// to collect.
///
/// `Typing_deps.trace` is a global of the process in OCaml, and an atomic of
/// the process here: [`crate::server_lint`], which lints on several threads,
/// turns it off around them, so that each thread finds it off and leaves it
/// off.
pub fn lint(ctx: &Arc<Ctx>, fn_: &RelativePath, content: &[u8]) {
    let orig_trace = crate::typing_deps::TRACE.load(Ordering::Relaxed);
    crate::typing_deps::TRACE.store(false, Ordering::Relaxed);
    diagnostics::ignore_(|| {
        let parser_return = parse_and_lint(fn_, content, ctx);
        // naming and typing currently don't produce any lint errors
        // PHP files generate declarations via some fairly error-prone regexps,
        // so only try to lint Hack files
        match parser_return.file_mode {
            None => {}
            Some(_) => {
                // Note that the named ASTs that we lint here aren't generated from the
                // unnamed ASTs that parse_and_lint generated; we're using the ones
                // already in the naming heap, which hh_server keeps up-to-date based
                // on inotify events. This is a little ugly, and might be worth
                // cleaning up at some point.
                lint_nast(ctx, fn_, &parser_return);

                // Get Typed AST and run TAST linters
                let full_ast = parser_return.ast;
                let (_, tast) =
                    crate::typing_check_job::calc_errors_and_tast(ctx, None, fn_, full_ast);
                // collect both the dynamic TAST and non-dynamic TAST in a big list,
                // that's what linting expects!
                let tasts: Vec<tast::Def> = crate::tast_with_dynamic::all(
                    crate::tast_with_dynamic::collect(tast::tasts_as_list(tast)),
                )
                .concat();
                lint_tast(ctx, &tasts)
            }
        }
    });
    crate::typing_deps::TRACE.store(orig_trace, Ordering::Relaxed)
}
