// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/remote_old_decl_client.ml`: getting old decls remotely.
//! See `hh/PORTING.md`.
//!
//! The saved-state load reaches it (`fetch_remote_old_decls` is true by
//! default). The open-source build links
//! `stubs/remote_old_decls_ffi.stubs.ml`, whose `get_decls_via_file_hashes`
//! fails ("get_decls_via_file_hashes not implemented"): so does
//! [`remote_old_decls_ffi::get_decls_via_file_hashes`], raised as the
//! OCaml's `Failure` (a panic with [`Failure`] as its payload).

use oxidized::decl_parser_options::DeclParserOptions;
use ty::decl::shallow::NamedDecl;

use crate::ctx::R;
use crate::hh_logger;
use crate::naming_sqlite;
use crate::provider_context;
use crate::relative_path;
use crate::typing_deps;

/// `Failure s` (`Printexc.to_string`).
pub struct Failure(pub String);

impl std::fmt::Debug for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failure({})", crate::rt::ocaml_printf::sprintf_s(&self.0))
    }
}

/// `Remote_old_decls_ffi` (`stubs/remote_old_decls_ffi.stubs.ml`)
pub mod remote_old_decls_ffi {
    use super::*;

    /// `get_decls_via_file_hashes _ _`
    pub fn get_decls_via_file_hashes(
        _opts: &DeclParserOptions,
        _file_hashes: &[(relative_path::T, String)],
    ) -> Result<Vec<NamedDecl<R>>, String> {
        std::panic::panic_any(Failure("get_decls_via_file_hashes not implemented".to_string()))
    }
}

pub const TEST_FIXTURE_DIRECTORY: &str = ".hh_remote_old_decls_test";

/// Load fixture files at the same paths supplied to the remote file parser.
/// Return every declaration kind; selection belongs to the calling client.
fn fetch_old_decls_from_test_fixture(
    ctx: &provider_context::T,
    file_hashes: &[(relative_path::T, String)],
) -> Option<Vec<NamedDecl<R>>> {
    match (std::env::var("HH_TEST_MODE").ok(), std::env::var("HH_LOCALCONF_PATH").ok()) {
        (Some(mode), Some(root)) if mode == "1" => {
            let directory = crate::rt::ocaml_filename::concat(&root, TEST_FIXTURE_DIRECTORY);
            if crate::disk::file_exists(&directory) {
                // (`Decl_parser_options.from_parser_options popt` and
                // `popt.deregister_php_stdlib`: the options of the decl parser
                // of the context.)
                let parse_file = |path: &relative_path::T| -> Vec<NamedDecl<R>> {
                    let fixture =
                        crate::rt::ocaml_filename::concat(&directory, &relative_path::suffix(path));
                    if crate::disk::file_exists(&fixture) {
                        let contents = match crate::sys_utils::cat(&fixture) {
                            Ok(c) => c,
                            Err(e) => std::panic::panic_any(e),
                        };
                        let parsed_file = ctx
                            .decl_parser
                            .parse_impl(pos::RelativePath::from(path), &contents);
                        // `pfh_decls`: in reverse lexical order.
                        parsed_file
                            .decls
                            .into_iter()
                            .map(|(name, decl, _)| NamedDecl::<R>::from((name, decl)))
                            .collect()
                    } else {
                        vec![]
                    }
                };
                let paths: relative_path::set::T =
                    file_hashes.iter().map(|(path, _)| path.clone()).collect();
                Some(paths.iter().flat_map(parse_file).collect())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn dep_of_named_decl(decl: &NamedDecl<R>) -> typing_deps::dep::T {
    use typing_deps::dep;
    match decl {
        NamedDecl::Class(name, _) | NamedDecl::Typedef(name, _) => {
            dep::make(&dep::Variant::Type(name.as_str().to_string()))
        }
        NamedDecl::Fun(name, _) => dep::make(&dep::Variant::Fun(name.as_str().to_string())),
        NamedDecl::Const(name, _) => dep::make(&dep::Variant::GConst(name.as_str().to_string())),
        NamedDecl::Module(name, _) => dep::make(&dep::Variant::Module(name.as_str().to_string())),
    }
}

/// `Utils`
pub mod utils {
    use super::*;

    /// `db_path_of_ctx ~ctx`
    pub fn db_path_of_ctx(ctx: &provider_context::T) -> Option<naming_sqlite::DbPath> {
        crate::db_path_provider::get_naming_db_path(ctx)
    }

    /// `dep_to_decl_hash_opt ~dep ~db_path`
    pub fn dep_to_decl_hash_opt(
        dep: &typing_deps::dep::Variant,
        db_path: &naming_sqlite::DbPath,
    ) -> Option<String> {
        let dep = typing_deps::dep::make(dep);
        match naming_sqlite::get_decl_hash_by_64bit_dep(db_path, dep) {
            Ok(decl_hash) => decl_hash,
            Err(e) => std::panic::panic_any(e),
        }
    }

    /// `dep_to_file_hash_opt ~dep ~db_path`
    pub fn dep_to_file_hash_opt(
        dep: &typing_deps::dep::Variant,
        db_path: &naming_sqlite::DbPath,
    ) -> Option<(relative_path::T, String)> {
        let dep = typing_deps::dep::make(dep);
        match naming_sqlite::get_file_hash_by_64bit_dep(db_path, dep) {
            Ok(file_hash) => file_hash,
            Err(e) => std::panic::panic_any(e),
        }
    }
}

/// `fetch_old_decls_via_file_hashes ~ctx ~db_path deps`
fn fetch_old_decls_via_file_hashes(
    ctx: &provider_context::T,
    db_path: &naming_sqlite::DbPath,
    deps: &[typing_deps::dep::Variant],
) -> Vec<NamedDecl<R>> {
    // `List.fold deps ~init:([], Typing_deps.DepMap.empty) ~f:add_requested_file`
    // (the file hashes are consed: in the reverse order of `deps`).
    let mut file_hashes: Vec<(relative_path::T, String)> = vec![];
    let mut owners: typing_deps::dep_map::T<relative_path::T> = typing_deps::dep_map::T::new();
    for dep in deps {
        let name = typing_deps::dep::extract_name(dep);
        match utils::dep_to_file_hash_opt(dep, db_path) {
            Some((path, hash)) => {
                hh_logger::log(&format!(
                    "Fetching decl for {} defined in {} from blob {}",
                    name,
                    relative_path::suffix(&path),
                    hash
                ));
                owners.insert(typing_deps::dep::make(dep), path.clone());
                file_hashes.push((path, hash));
            }
            None => hh_logger::log(&format!("Missing entry for {}", name)),
        }
    }
    file_hashes.reverse();
    let is_requested_owner = |decl: &NamedDecl<R>| -> bool {
        let pos = match decl {
            NamedDecl::Class(_, decl) => decl.name.pos(),
            NamedDecl::Fun(_, decl) => &decl.pos,
            NamedDecl::Typedef(_, decl) => &decl.pos,
            NamedDecl::Const(_, decl) => &decl.pos,
            NamedDecl::Module(_, decl) => &decl.pos,
        };
        match owners.get(&dep_of_named_decl(decl)) {
            None => false,
            // `Pos_or_decl.filename pos`
            Some(path) => relative_path::equal(path, &pos.file().into()),
        }
    };
    let popt = provider_context::get_popt(ctx);
    let opts = DeclParserOptions::from_parser_options(popt);
    let result = match fetch_old_decls_from_test_fixture(ctx, &file_hashes) {
        Some(decls) => Ok(decls),
        None => remote_old_decls_ffi::get_decls_via_file_hashes(&opts, &file_hashes),
    };
    match result {
        Ok(named_old_decls) => {
            // Loading whole files also returns declarations we did not request.
            // Keep only requested dependencies whose declaration comes from the owner
            // file recorded in the saved-state naming DB. A duplicate in another loaded
            // file must not replace that owner's declaration. This applies equally to
            // fixture files and files downloaded from CAS.
            named_old_decls
                .into_iter()
                .filter(is_requested_owner)
                .collect()
        }
        Err(msg) => {
            hh_logger::log(&format!("Error fetching remote decls: {}", msg));
            vec![]
        }
    }
}

/// `fetch_old_decls ~ctx deps`
pub fn fetch_old_decls(
    ctx: &provider_context::T,
    deps: &[typing_deps::dep::Variant],
) -> Vec<NamedDecl<R>> {
    let db_path_opt = utils::db_path_of_ctx(ctx);
    match db_path_opt {
        None => vec![],
        Some(db_path) => {
            let decl_hashes: Vec<String> = deps
                .iter()
                .filter_map(|dep| utils::dep_to_decl_hash_opt(dep, &db_path))
                .collect();
            let start_t = crate::rt::ocaml_unix::gettimeofday();
            let old_decls = fetch_old_decls_via_file_hashes(ctx, &db_path, deps);
            let to_fetch = decl_hashes.len();
            // (`Hack_event_logger.remote_old_decl_end telemetry start_t`: a no-op.)
            let _ = start_t;
            hh_logger::log(&format!(
                "Fetched {}/{} decls remotely",
                old_decls.len(),
                to_fetch
            ));
            old_decls
        }
    }
}
