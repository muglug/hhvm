// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_package_lint.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: the candidates are checked in one job.

use std::collections::BTreeSet;

use oxidized::aast;

use crate::nast;
use crate::package;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::symbol_occurrence as so;
use crate::tast_provider;
use crate::typing_deps;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

/// The files that may depend on a definition of `file`: a set of candidate
/// file paths.
pub fn go_fast(_genv: &Genv, env: &Env, file: &str) -> relative_path::set::T {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let path = relative_path::create_detect_prefix(file);
    let (ctx, entry) = provider_context::add_entry_if_missing(&ctx, path);
    let ast = crate::ast_provider::compute_ast(&provider_context::get_popt(&ctx), &entry);
    // Phase 1: Collect all dep hashes from AST definitions
    let deps = ast.0.iter().fold(dep_set::make(), |deps, def| match def {
        aast::Def::Class(c) => dep_set::add(&deps, dep::make(&dep::Variant::Type(c.name.1.clone()))),
        aast::Def::Typedef(t) => dep_set::add(&deps, dep::make(&dep::Variant::Type(t.name.1.clone()))),
        aast::Def::Fun(fd) => dep_set::add(&deps, dep::make(&dep::Variant::Fun(fd.name.1.clone()))),
        aast::Def::Constant(cst) => dep_set::add(&deps, dep::make(&dep::Variant::GConst(cst.name.1.clone()))),
        _ => deps,
    });
    // Phase 2: Single batched dep graph lookup + single file resolution
    let deps_mode = provider_context::get_deps_mode(&ctx);
    let all_ideps = typing_deps::add_typing_deps(&deps_mode, &deps);
    crate::naming_provider::get_files(&ctx, &all_ideps)
}

/// The names of the top-level definitions of the AST (classes, typedefs,
/// functions, constants). These are the names that [`references_target`]
/// checks symbol occurrences against. Names are already fully qualified
/// (with leading backslash) because `Ast_provider.compute_ast` returns a
/// named AST (NAST).
fn target_names_of_ast(ast: &nast::Program) -> BTreeSet<String> {
    ast.0
        .iter()
        .filter_map(|def| match def {
            aast::Def::Class(c) => Some(c.name.1.clone()),
            aast::Def::Typedef(t) => Some(t.name.1.clone()),
            aast::Def::Fun(fd) => Some(fd.name.1.clone()),
            aast::Def::Constant(cst) => Some(cst.name.1.clone()),
            _ => None,
        })
        .collect()
}

/// Class, Function, and GConst occurrences — these are the top-level
/// definition kinds that [`target_names_of_ast`] collects. Member-level
/// kinds (Method, Property, ClassConst, Typeconst) are skipped because
/// any member access implies a Class occurrence on the same receiver,
/// so the class-level match is sufficient.
fn references_target(names: &BTreeSet<String>, sym: &so::T<crate::pos::Pos>) -> bool {
    match sym.type_ {
        so::Kind::Class(_) | so::Kind::Function | so::Kind::GConst => names.contains(&sym.name),
        _ => false,
    }
}

/// Does `cand` have a production-affecting reference to any of
/// `target_names`? Computes the TAST for `cand` and checks symbol
/// occurrences. `affects_prod_build` filters out occurrences that don't
/// trigger package enforcement at runtime — nameof expressions, `::class`
/// constants, attribute references, etc.
fn has_prod_ref_to(ctx: &provider_context::T, target_names: &BTreeSet<String>, cand: &RelativePath) -> bool {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, cand.clone());
    // Use unquarantined because this is a batch operation across multiple
    // files via Multi_worker, not a single-file IDE request.  Quarantined
    // mode is only appropriate for single-file IDE operations.
    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_unquarantined(&ctx, &entry);
    crate::identify_symbol_service::all_symbols(&ctx, &tast.under_normal_assumptions)
        .iter()
        .any(|sym| sym.affects_prod_build && references_target(target_names, sym))
}

/// "If I removed the `__PackageOverride` from `file`, which of
/// `candidate_files` would lose access to its symbols?"
///
/// For each candidate, computes its TAST and checks whether any
/// production-affecting symbol occurrence (i.e. `affects_prod_build =
/// true`) references a definition from `file`. This filters out
/// nameof expressions, ::class references, attributes, and other
/// non-package-enforced edges. Then filters by package relationship:
/// keeps only candidates whose package cannot access the target's
/// natural (path-based) package.
///
/// If the returned set is empty the override is redundant.
pub fn go(_genv: &Genv, env: &Env, file: &str, candidate_files: &[String]) -> relative_path::set::T {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let path = relative_path::create_detect_prefix(file);
    let (ctx, entry) = provider_context::add_entry_if_missing(&ctx, path.clone());
    let ast = crate::ast_provider::compute_ast(&provider_context::get_popt(&ctx), &entry);
    let target_names = target_names_of_ast(&ast);
    // For each candidate file, check if it contains at least one
    // production-affecting reference to any of the target's definitions.
    let ref_files: relative_path::set::T = candidate_files
        .iter()
        .map(|f| relative_path::create_detect_prefix(f))
        .filter(|cand| has_prod_ref_to(&ctx, &target_names, cand))
        .collect();
    // Target uses its natural (path-based) package because the question is
    // "what if the override on the target were removed?". Dependents use
    // their *effective* package (override-honored) — they're not part of
    // that hypothetical.
    let target_suffix = relative_path::suffix(&path);
    let natural_pkg = crate::package_provider::get_package_for_file(&ctx, &target_suffix);
    match natural_pkg {
        // Target file has no natural package (not covered by PACKAGES.toml).
        // We can't reason about access, so return all refs conservatively.
        None => ref_files,
        Some(natural_pkg) => ref_files
            .into_iter()
            .filter(|dep_path| {
                // Same-file access is always allowed; matches
                // [Typing_packages.can_access_by_package_rules].
                if *dep_path == path {
                    false
                } else {
                    let dep_pkg = match crate::file_provider::rust_provider_backend::file::get_contents(&ctx, dep_path) {
                        None => None,
                        Some(text) => {
                            let (pkg, _has_override) =
                                crate::package_provider::get_package_with_override_for_file_no_env(
                                    &ctx,
                                    &relative_path::suffix(dep_path),
                                    &String::from_utf8_lossy(&text),
                                );
                            pkg
                        }
                    };
                    match dep_pkg {
                        // Dep has no package — conservatively assume it needs
                        // the override (we can't prove it doesn't).
                        None => true,
                        // Check whether dep_pkg can access natural_pkg:
                        // - Equal:         same package, always has access
                        // - Includes:      dep_pkg hard-includes natural_pkg
                        // - Soft_includes: not enforced, would break
                        // - Unrelated:     no include path, would break
                        Some(dep_pkg) => match package::relationship(&dep_pkg, &natural_pkg) {
                            package::PackageRelationship::Equal | package::PackageRelationship::Includes => false,
                            package::PackageRelationship::SoftIncludes | package::PackageRelationship::Unrelated => {
                                true
                            }
                        },
                    }
                }
            })
            .collect(),
    }
}
