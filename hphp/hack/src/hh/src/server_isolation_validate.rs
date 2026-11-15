// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_isolation_validate.ml`. See `hh/PORTING.md`.
//!
//! Check whether `files` could be a strict-isolation package, by making them
//! one in memory and typechecking.
//!
//! Nothing is written to disk: the package is synthesized into a
//! `Provider_context`, so neither the repository nor `PACKAGES.toml` is
//! touched. This exercises the typechecker's own enforcement rather than a
//! model of it.
//!
//! It is not free of effect on the server, though. Making the candidate a
//! package means rebuilding its decls under a configuration the repository
//! does not have, in heaps the whole process shares — see
//! [`crate::server_isolation_decls::with_repackaged_decls`]. Run this on a
//! server given over to the analysis, not one also answering a developer's
//! typechecks, and restart that server when the run is done.
//!
//! Only files the dependency graph says might reference the candidate are
//! checked, so a reference it does not record is invisible. This can show a
//! candidate is not isolatable; it cannot show that nothing was missed.
//!
//! A candidate path the naming table does not know is reported in
//! `unknown_files` rather than skipped, which would read as a clean result.

use std::sync::Arc;

use oxidized::package::Package;
use oxidized::package::PosId;
use oxidized::pos::Pos;
use oxidized::user_diagnostic::Severity;

use crate::diagnostics;
use crate::naming_provider;
use crate::naming_table;
use crate::package_info;
use crate::package_provider;
use crate::provider_backend;
use crate::provider_context;
use crate::provider_utils;
use crate::relative_path;
use crate::server_command_types::isolation_validation;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_isolation_decls;
use crate::tast_provider;
use crate::typechecker_options;
use crate::typing_deps;
use crate::user_diagnostic;

/// [`package_info::add_package`] raises on a name already configured, so this
/// has to be one no repository would use.
pub const CANDIDATE_PACKAGE_NAME: &str = "hh_isolation_candidate";

/// `candidate_package`: the candidate as a package the typechecker will
/// enforce.
///
/// Membership is a string prefix test, so listing files individually assigns
/// exactly this set — and also claims a path that merely extends a candidate
/// path, `a/B.php.expect` beside `a/B.php`.
///
/// `is_implicit` must stay false, or resolution treats the entry as a family
/// and answers with a synthesized member instead.
fn candidate_package(files: &[relative_path::T]) -> Package {
    Package {
        name: PosId(Pos::NONE, CANDIDATE_PACKAGE_NAME.to_string()),
        includes: vec![],
        soft_includes: vec![],
        include_paths: files
            .iter()
            .map(|f| PosId(Pos::NONE, relative_path::suffix(f)))
            .collect(),
        enable_strict_isolation: true,
        // Contradicts the strict isolation the candidate opts into.
        allow_deployed_packages_checking: false,
        is_implicit: false,
    }
}

/// `with_candidate_package ctx files`: `ctx` with the candidate added to the
/// packages already configured.
///
/// Both the parser and the typechecker options carry a copy and both must be
/// updated: a candidate in only one resolves to nothing, which reads as a
/// symbol in no package — accessible from anywhere.
///
/// (`Provider_context.empty_for_tool ~popt ~tcopt ~backend ~deps_mode`: a
/// clone of `ctx`, which shares its stores, without entries. The decl
/// parser of a `Ctx` holds a third copy of the parser options, so it is
/// made again with the new ones.)
fn with_candidate_package(
    ctx: &provider_context::T,
    files: &[relative_path::T],
) -> provider_context::T {
    let popt = provider_context::get_popt(ctx);
    let package_info = package_info::add_package(&popt.package_info, candidate_package(files));
    let popt = oxidized::parser_options::ParserOptions {
        package_info: package_info.clone(),
        ..popt.clone()
    };
    let tcopt = typechecker_options::set_package_info(
        oxidized::typechecker_options::TypecheckerOptions::clone(provider_context::get_tcopt(ctx)),
        package_info,
    );
    let mut new_ctx = crate::ctx::Ctx::clone(ctx);
    new_ctx.decl_parser = decl_parser::DeclParser::new(
        Arc::clone(&ctx.files) as Arc<dyn ::file_provider::FileProvider>,
        oxidized::decl_parser_options::DeclParserOptions::from_parser_options(&popt),
    );
    new_ctx.parser_env.parser_options = popt;
    new_ctx.tco = Arc::new(tcopt);
    new_ctx.entries = Default::default();
    Arc::new(new_ctx)
}

/// `dependents_of_file`: every file the dependency graph says depends on a
/// symbol `file` defines.
fn dependents_of_file(
    ctx: &provider_context::T,
    deps_mode: &typing_deps::mode::T,
    naming_table: &naming_table::T,
    file: &relative_path::T,
) -> relative_path::set::T {
    match naming_table::get_file_info(naming_table, file) {
        None => relative_path::set::T::new(),
        Some(file_info) => {
            let symbols = typing_deps::deps_of_file_info(&file_info);
            symbols
                .into_iter()
                .fold(relative_path::set::T::new(), |acc, symbol| {
                    let dependent_symbols = typing_deps::get_ideps_from_hash(deps_mode, symbol);
                    let dependent_files = naming_provider::get_files(ctx, &dependent_symbols);
                    acc.union(dependent_files)
                })
        }
    }
}

/// `referrers ctx naming_table files`: files outside `files` that could hold
/// a reference into it, per the dependency graph.
///
/// Trusting the graph is the premise the cluster itself rests on, so this
/// cannot catch a reference the graph does not record. The independent
/// alternative costs a full check per candidate.
fn referrers(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    files: &[relative_path::T],
) -> relative_path::set::T {
    let deps_mode = provider_context::get_deps_mode(ctx);
    let candidate: relative_path::set::T = files.iter().cloned().collect();
    let dependents = files
        .iter()
        .fold(relative_path::set::T::new(), |acc, file| {
            acc.union(dependents_of_file(ctx, &deps_mode, naming_table, file))
        });
    dependents.relative_complement(candidate)
}

/// `is_violation ~candidate error`: whether `error` is a reason the candidate
/// could not be this package.
///
/// Any error that refers to the candidate counts, whatever its code:
/// enumerating the package error codes instead would answer "isolatable" for
/// any way of breaking a package we had not thought to list.
///
/// Warnings do not count. The repository typechecks clean, which is what lets
/// an error be attributed to the synthesized package — but that holds for the
/// errors the repository is configured to see, and the filter used here turns
/// on every warning besides. Those fire on code that was already there:
/// "this null coalesce will always evaluate to its left-hand side" is a fair
/// remark about a candidate's file and no reason it cannot be a package.
///
/// Referring to the candidate means some reason inside it: a diagnostic's
/// reasons sit at what is referred to, so this is what distinguishes a
/// reference into the candidate from a checked file's own unrelated complaint.
/// The claim may be inside or outside — outside is the reference in that a
/// cluster must not have, and inside is the candidate reaching into its own
/// `__tests__`, which strict isolation no longer exempts. Both disqualify it.
fn is_violation(candidate: &relative_path::set::T, error: &diagnostics::Diagnostic) -> bool {
    match error.severity {
        Severity::Warning { .. } => false,
        Severity::Err => user_diagnostic::reason_messages(error)
            .iter()
            .any(|reason| candidate.contains(&crate::pos_or_decl::filename(&reason.0))),
    }
}

/// `violation_of_error`
fn violation_of_error(error: &diagnostics::Diagnostic) -> isolation_validation::Violation {
    let pos = user_diagnostic::get_pos(error);
    let message = String::from_utf8_lossy(&user_diagnostic::claim_message(error).1)
        // The package the check synthesizes has a name only it knows.
        .replace(
            &format!("package `{}`", CANDIDATE_PACKAGE_NAME),
            "the candidate package",
        );
    isolation_validation::Violation {
        referrer: relative_path::suffix(&crate::pos::filename(&pos)),
        line: crate::pos::line_column(&pos).0,
        message,
    }
}

/// `violations_in ctx ~candidate path`: typecheck `path` under `ctx` and keep
/// the errors that say `candidate` could not be a package.
fn violations_in(
    ctx: &provider_context::T,
    candidate: &relative_path::set::T,
    path: &relative_path::T,
) -> Vec<isolation_validation::Violation> {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
    let tast_provider::ComputeTastAndErrors { diagnostics, .. } =
        tast_provider::compute_tast_and_errors_unquarantined(
            &ctx,
            &entry,
            &tast_provider::ErrorFilter::default(),
        );
    diagnostics::get_diagnostic_list(None, diagnostics)
        .iter()
        .filter(|error| is_violation(candidate, error))
        .map(violation_of_error)
        .collect()
}

/// `overridden_files ctx files`: paths the candidate cannot actually claim,
/// because the file names a package of its own with
/// `<<file: __PackageOverride(...)>>`.
///
/// An override wins over include-path matching, so the synthesized package
/// never takes the file and the answer would be about a candidate missing it.
/// Reported like an unknown path rather than worked around: the cluster asked
/// about is not one this command can construct.
///
/// The override-aware resolver is documented as too slow for the typechecker;
/// it is used here over the candidate's own files only, which we are about to
/// read and typecheck anyway.
fn overridden_files(ctx: &provider_context::T, files: &[relative_path::T]) -> Vec<String> {
    files
        .iter()
        .filter_map(|file| {
            match crate::file_provider::rust_provider_backend::file::get_contents(ctx, file) {
                None => None,
                Some(content) => {
                    let (_, is_overridden) =
                        package_provider::get_package_with_override_for_file_no_env(
                            ctx,
                            &relative_path::suffix(file),
                            &content,
                        );
                    if is_overridden {
                        Some(relative_path::suffix(file))
                    } else {
                        None
                    }
                }
            }
        })
        .collect()
}

/// `refused allow_repackaging uses_rust_backend`: why this server cannot
/// answer, if it cannot.
fn refused(allow_repackaging: bool, uses_rust_backend: bool) -> Option<String> {
    let problems: Vec<(&str, &str)> = [
        (
            !allow_repackaging,
            "this server does not permit decl repackaging",
            "isolation_allow_decl_repackaging=true",
        ),
        (
            uses_rust_backend,
            "the Rust provider backend keeps its own copy of the package configuration, which a synthesized package cannot reach",
            "rust_provider_backend=false",
        ),
    ]
    .into_iter()
    .filter_map(|(applies, reason, setting)| applies.then_some((reason, setting)))
    .collect();
    if problems.is_empty() {
        None
    } else {
        Some(format!(
            "{}; restart the server with {}. Do this on a server nothing else uses: the check rebuilds declarations in the server's shared memory.",
            problems
                .iter()
                .map(|(reason, _)| *reason)
                .collect::<Vec<_>>()
                .join(", and "),
            problems
                .iter()
                .map(|(_, setting)| *setting)
                .collect::<Vec<_>>()
                .join(" and "),
        ))
    }
}

/// `go genv env ~files`
pub fn go(genv: &Genv, env: &Env, files: &[relative_path::T]) -> isolation_validation::Result {
    let ctx = provider_utils::ctx_from_server_env(env);
    let allow_repackaging = genv.local_config.isolation_allow_decl_repackaging;
    // Two ways this server cannot answer, both reported at once since each takes
    // a restart to fix. Raising would take the server down and reach the caller
    // as a bare disconnection, so the reason is returned instead.
    let uses_rust_backend = match ctx.get_backend() {
        // The Rust backend copies the package configuration when it initialises,
        // so a candidate added to [ctx] never reaches the code that enforces
        // packages: every file stays where it was and the run reports violations
        // that are not there.
        provider_backend::T::RustProviderBackend => true,
        provider_backend::T::SharedMemory | provider_backend::T::LocalMemory(_) => false,
    };
    let refused = refused(allow_repackaging, uses_rust_backend);
    match refused {
        Some(_) => isolation_validation::Result {
            refused,
            isolatable: false,
            files_checked: 0,
            violations: vec![],
            unknown_files: vec![],
            overridden_files: vec![],
        },
        None => {
            let naming_table = &env.naming_table;
            let candidate: relative_path::set::T = files.iter().cloned().collect();
            let (known, unknown): (Vec<relative_path::T>, Vec<relative_path::T>) = files
                .iter()
                .cloned()
                .partition(|file| naming_table::get_file_info(naming_table, file).is_some());
            let unknown_files: Vec<String> = unknown.iter().map(relative_path::suffix).collect();
            let overridden_files = overridden_files(&ctx, &known);
            // One source per kind of violation.
            let to_check = relative_path::set::T::union(
                // A reference into the candidate is reported at the referring file.
                referrers(&ctx, naming_table, files),
                // The excluded-path violation is reported inside the candidate — a
                // package using its own [__tests__] — so it surfaces only by checking
                // the candidate's own files. [known] alone: an unknown path has nothing
                // to typecheck, and is answered through [unknown_files].
                known.iter().cloned().collect(),
            );
            let ctx = with_candidate_package(&ctx, files);
            let violations = server_isolation_decls::with_repackaged_decls(
                &ctx,
                naming_table,
                files,
                allow_repackaging,
                || {
                    to_check
                        .iter()
                        .flat_map(|path| violations_in(&ctx, &candidate, path))
                        .collect::<Vec<_>>()
                },
            );
            isolation_validation::Result {
                refused: None,
                // A candidate we could not construct in full is not reported isolatable.
                // A path we had to set aside contributes no referrers, so answering from
                // the rest would answer about a smaller candidate than the one asked
                // about.
                isolatable: violations.is_empty()
                    && unknown_files.is_empty()
                    && overridden_files.is_empty(),
                files_checked: to_check.len() as isize,
                violations,
                unknown_files,
                overridden_files,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refusals() {
        assert_eq!(refused(true, false), None);
        assert_eq!(
            refused(false, false).as_deref(),
            Some(
                "this server does not permit decl repackaging; restart the server with isolation_allow_decl_repackaging=true. Do this on a server nothing else uses: the check rebuilds declarations in the server's shared memory."
            )
        );
        assert_eq!(
            refused(false, true).as_deref(),
            Some(
                "this server does not permit decl repackaging, and the Rust provider backend keeps its own copy of the package configuration, which a synthesized package cannot reach; restart the server with isolation_allow_decl_repackaging=true and rust_provider_backend=false. Do this on a server nothing else uses: the check rebuilds declarations in the server's shared memory."
            )
        );
    }

    #[test]
    fn candidate_package_claims_exactly_its_paths() {
        let files = [
            relative_path::from_root("a/B.php"),
            relative_path::from_root("c.php"),
        ];
        let pkg = candidate_package(&files);
        assert_eq!(pkg.name.1, CANDIDATE_PACKAGE_NAME);
        assert!(
            pkg.enable_strict_isolation
                && !pkg.is_implicit
                && !pkg.allow_deployed_packages_checking
        );
        let info = package_info::add_package(&package_info::empty(), pkg);
        let name_of =
            |path: &str| package_info::get_package_for_file(&info, path).map(|p| p.name.1);
        assert_eq!(name_of("a/B.php").as_deref(), Some(CANDIDATE_PACKAGE_NAME));
        // A path that extends a candidate path is claimed too.
        assert_eq!(
            name_of("a/B.php.expect").as_deref(),
            Some(CANDIDATE_PACKAGE_NAME)
        );
        assert_eq!(name_of("a/C.php"), None);
    }
}
