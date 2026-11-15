// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_package_lint.ml` (the `PACKAGE_LINT`
//! and `PACKAGE_LINT_FULL` commands). See `hh/PORTING.md`.

use oxidized::aast;

use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;

/// `go_fast` uses the dependency graph to find files that *might*
/// depend on definitions in `file`. This is over-approximate: it
/// includes any file whose dependency-table entry touches a name
/// defined here, even for edges (like type annotations) that the
/// package checker doesn't enforce.
pub fn go_fast(_genv: &Genv, env: Env, file: &str) -> (Env, relative_path::set::T) {
    let ctx = crate::provider_utils::ctx_from_server_env(&env);
    let path = relative_path::create_detect_prefix(file);
    let (ctx, entry) = provider_context::add_entry_if_missing(&ctx, path);
    let ast = crate::ast_provider::compute_ast(provider_context::get_popt(&ctx), &entry);
    // Phase 1: Collect all dep hashes from AST definitions
    let mut deps = dep_set::make();
    for def in &ast.0 {
        let d = match def {
            aast::Def::Class(c) => Some(dep::Variant::Type(c.name.1.clone())),
            aast::Def::Typedef(t) => Some(dep::Variant::Type(t.name.1.clone())),
            aast::Def::Fun(fd) => Some(dep::Variant::Fun(fd.name.1.clone())),
            aast::Def::Constant(cst) => Some(dep::Variant::GConst(cst.name.1.clone())),
            _ => None,
        };
        if let Some(d) = d {
            deps = dep_set::add(&deps, dep::make(&d))
        }
    }
    // Phase 2: Single batched dep graph lookup + single file resolution
    let deps_mode = provider_context::get_deps_mode(&ctx);
    let all_ideps = crate::typing_deps::add_typing_deps(&deps_mode, &deps);
    let files = crate::naming_provider::get_files(&ctx, &all_ideps);
    (env, files)
}

/// Fully-qualified names of every top-level definition in `ast`.
fn target_names_of_ast(ast: &oxidized::nast::Program) -> std::collections::BTreeSet<String> {
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

/// Does `sym` reference any name in `names`? Only Class, Function and
/// GConst occurrences.
fn references_target(
    names: &std::collections::BTreeSet<String>,
    sym: &crate::symbol_occurrence::T<oxidized::pos::Pos>,
) -> bool {
    use crate::symbol_occurrence::Kind;
    match sym.type_ {
        Kind::Class(_) | Kind::Function | Kind::GConst => names.contains(&sym.name),
        _ => false,
    }
}

/// Does `cand` contain at least one production-affecting reference to any of
/// `target_names`?
fn has_prod_ref_to(
    ctx: &provider_context::T,
    target_names: &std::collections::BTreeSet<String>,
    cand: &RelativePath,
) -> bool {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, cand.clone());
    let crate::tast_provider::ComputeTast { tast, .. } =
        crate::tast_provider::compute_tast_unquarantined(&ctx, &entry);
    crate::identify_symbol_service::all_symbols(&ctx, &tast.under_normal_assumptions)
        .iter()
        .any(|sym| sym.affects_prod_build && references_target(target_names, sym))
}

/// `go _genv env file candidate_files` answers: "If we removed the
/// __PackageOverride from `file`, which of `candidate_files` would lose
/// access to its symbols?"
pub fn go(genv: &Genv, env: Env, file: &str, candidate_files: &[String]) -> (Env, relative_path::set::T) {
    let ctx = crate::provider_utils::ctx_from_server_env(&env);
    let path = relative_path::create_detect_prefix(file);
    let (ctx, entry) = provider_context::add_entry_if_missing(&ctx, path.clone());
    let ast = crate::ast_provider::compute_ast(provider_context::get_popt(&ctx), &entry);
    let target_names = target_names_of_ast(&ast);
    let candidate_paths: Vec<RelativePath> = candidate_files
        .iter()
        .map(|f| relative_path::create_detect_prefix(f))
        .collect();
    let job = |acc: relative_path::set::T, candidates: Vec<RelativePath>| {
        let mut acc = acc;
        for cand in candidates {
            if has_prod_ref_to(&ctx, &target_names, &cand) {
                acc.insert(cand);
            }
        }
        acc
    };
    let ref_files = crate::find_refs_service::multi_worker_call(
        Some(genv.num_workers as usize),
        &candidate_paths,
        job,
        relative_path::set::T::new,
        |b: relative_path::set::T, mut c: relative_path::set::T| {
            c.extend(b);
            c
        },
        || false,
    );
    // Target uses its natural (path-based) package because the question is
    // "what if the override on the target were removed?". Dependents use
    // their *effective* package (override-honored).
    let target_suffix = relative_path::suffix(&path);
    let natural_pkg = crate::package_provider::get_package_for_file(&ctx, &target_suffix);
    match natural_pkg {
        // Target file has no natural package (not covered by PACKAGES.toml).
        // We can't reason about access, so return all refs conservatively.
        None => (env, ref_files),
        Some(natural_pkg) => {
            let filtered = ref_files
                .into_iter()
                .filter(|dep_path| {
                    // Same-file access is always allowed.
                    if *dep_path == path {
                        false
                    } else {
                        let dep_pkg = match crate::file_provider::rust_provider_backend::file::get_contents(&ctx, dep_path) {
                            None => None,
                            Some(text) => {
                                crate::package_provider::get_package_with_override_for_file_no_env(&ctx, &relative_path::suffix(dep_path), &text).0
                            }
                        };
                        match dep_pkg {
                            // Dep has no package — conservatively assume it needs
                            // the override (we can't prove it doesn't).
                            None => true,
                            Some(dep_pkg) => {
                                use oxidized::package::PackageRelationship;
                                match crate::package::relationship(&dep_pkg, &natural_pkg) {
                                    PackageRelationship::Equal | PackageRelationship::Includes => false,
                                    PackageRelationship::SoftIncludes | PackageRelationship::Unrelated => true,
                                }
                            }
                        }
                    }
                })
                .collect();
            (env, filtered)
        }
    }
}
