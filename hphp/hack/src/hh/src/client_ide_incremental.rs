// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_incremental.ml`.
//!
//! `batch_index_hackrs_ffi_root_relative_paths_only` (the Rust FFI of
//! `rust_batch_index_ffi.rs`) is [`batch_index_root_relative_paths_only`]:
//! the same parse (the decl parser of the context, with its options), on the
//! rayon pool. The OCaml's test-disk branch (`Disk.is_real_disk` false: the
//! contents read by OCaml) has no counterpart: the tests here write real
//! files. The `pfh_hash` of a file is only compared with
//! `decls_reflect_this_file`, which this version never sets: it is 0.

use rayon::prelude::*;

use crate::file_info;
use crate::file_info::SiAddendum;
use crate::hh_logger;
use crate::naming_provider;
use crate::naming_table;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::search_utils;
use crate::symbol_index_core;
use crate::telemetry;

fn log(s: &str) {
    hh_logger::log(&format!("[ide-incremental] {}", s))
}

fn should_update_changed_file(path: &RelativePath) -> bool {
    relative_path::is_root(relative_path::prefix(path)) && crate::find_utils::path_filter(path)
}

/// What the batch index gives for a file that exists: its file info, its
/// `pfh_hash`, its symbol-index addenda.
pub type IndexResult = (file_info::T, file_info::PfhHash, Vec<SiAddendum>);

/// `batch_index_hackrs_ffi_root_relative_paths_only parser_options
/// deregister_php_stdlib root paths` (see the module doc): for each path
/// (relative to the root), `None` if the file does not exist.
fn batch_index_root_relative_paths_only(
    ctx: &provider_context::T,
    paths: Vec<RelativePath>,
) -> Vec<(RelativePath, Option<IndexResult>)> {
    let root = relative_path::path_of_prefix(relative_path::Prefix::Root).unwrap_or_default();
    paths
        .into_par_iter()
        .map(|relpath| {
            let abspath = std::path::Path::new(&root).join(relpath.path());
            let contents = match std::fs::read(&abspath) {
                Ok(text) => text,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => return (relpath, None),
                Err(e) => panic!("{}", e),
            };
            let path = pos::RelativePath::from(&relpath);
            let decls = match ctx.decl_parser.parse_with_text(path, &contents) {
                Ok(decls) => decls,
                Err(e) => panic!("{}", e),
            };
            let addenda = symbol_index_core::get_si_addenda(&decls);
            let mode = full_fidelity_parser_parse_mode(&relpath, &contents);
            let file_info = crate::direct_decl_service::file_info_of_decls(path, &decls, mode);
            (relpath, Some((file_info, 0, addenda)))
        })
        .collect()
}

/// The mode of a file (`ParsedFileWithHashes.mode`).
fn full_fidelity_parser_parse_mode(path: &RelativePath, contents: &[u8]) -> Option<file_info::Mode> {
    let source = crate::full_fidelity_source_text::make(path, contents);
    let (_, mode) = mode_parser::parse_mode(&crate::full_fidelity_source_text::source_text(&source));
    mode.map(Into::into)
}

pub struct UpdateResult {
    pub naming_table: naming_table::T,
    pub sienv: search_utils::SiEnv,
    pub changes: Vec<file_info::Change>,
}

/// For each path, direct decl parse to compute the names and positions in
/// the file. If the file at the path doesn't exist, return [None].
fn compute_file_info_batch_root_relative_paths_only(
    ctx: &provider_context::T,
    paths: Vec<RelativePath>,
) -> Vec<(RelativePath, Option<IndexResult>)> {
    batch_index_root_relative_paths_only(ctx, paths)
}

/// Updates the reverse-naming-table (which is inside ctx for the local
/// memory backend, and is a sharedmem heap for the sharedmem backend).
/// Returns an updated forward-naming-table in 'naming_table', and updated
/// symbol-search index in 'sienv'. It does this by by parsing the file at
/// the given path and reading their declarations. If the file could not be
/// read, it's assumed to be deleted, and so the old forward-naming-table
/// indicates which caches will have to be deleted by the caller.
///
/// Note: this function ignores non-root files, and those that fail
/// Find_utils.path_filter.
///
/// IO: this function uses File_provider to read the file. (Here the files
/// are read from disk, as the OCaml's real-disk branch does.)
pub fn update_naming_tables_and_si(
    ctx: &provider_context::T,
    naming_table: &naming_table::T,
    sienv: &search_utils::SiEnv,
    changes: &relative_path::set::T,
) -> UpdateResult {
    log(&format!(
        "Batch change {} files, e.g. {}",
        changes.len(),
        changes
            .iter()
            .next()
            .map_or_else(|| "[none]".to_string(), relative_path::suffix)
    ));
    // Do a fast parallel decl-parse of all changes
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    // NOTE: our batch index/file info computation expects only files relative to root.
    let parse_results = compute_file_info_batch_root_relative_paths_only(
        ctx,
        changes
            .iter()
            .filter(|p| should_update_changed_file(p))
            .cloned()
            .collect(),
    );
    let changed_ids: Vec<file_info::Change> = parse_results
        .iter()
        .map(|(path, new_info)| {
            let old_file_info = naming_table::get_file_info(naming_table, path);
            file_info::Change {
                path: path.clone(),
                new_ids: new_info.as_ref().map(|(fi, _, _)| fi.ids.clone()),
                new_pfh_hash: new_info.as_ref().map(|(_, hash, _)| *hash),
                old_ids: old_file_info.map(|fi| fi.ids),
            }
        })
        .collect();
    // update the reverse-naming-table, which is mutable storage owned by backend
    let t_update_reverse_nt = crate::rt::ocaml_unix::gettimeofday();
    for file_info::Change {
        path,
        new_ids,
        old_ids,
        ..
    } in &changed_ids
    {
        naming_provider::update(ctx, path, old_ids.as_ref(), new_ids.as_ref());
    }
    // update the forward-naming-table (file -> symbols)
    // remove old, then add new
    let t_update_forward_nt = crate::rt::ocaml_unix::gettimeofday();
    let naming_table = changed_ids.iter().fold(
        naming_table.clone(),
        |naming_table, file_info::Change { path, old_ids, .. }| match old_ids {
            None => naming_table,
            Some(_) => naming_table::remove(&naming_table, path),
        },
    );
    // update new
    let paths_with_new_file_info: relative_path::map::T<file_info::T> = parse_results
        .iter()
        .filter_map(|(path, new_info)| new_info.as_ref().map(|(fi, _, _)| (path.clone(), fi.clone())))
        .collect();
    let naming_table = naming_table::update_many(&naming_table, &paths_with_new_file_info);
    // update search index
    // remove paths without new file info
    let t_si = crate::rt::ocaml_unix::gettimeofday();
    let paths_without_new_ids: relative_path::set::T = changed_ids
        .iter()
        .filter(|c| c.new_ids.is_none())
        .map(|c| c.path.clone())
        .collect();
    let sienv = symbol_index_core::remove_files(sienv, &paths_without_new_ids);
    // now update paths with new file info
    let paths_with_addenda: symbol_index_core::PathsWithAddenda = parse_results
        .into_iter()
        .filter_map(|(path, new_ids_with_addenda_opt)| {
            new_ids_with_addenda_opt.map(|(_new_ids, _pfh_hash, addenda)| {
                (path, addenda, search_utils::FileSource::TypeChecker)
            })
        })
        .collect();
    let sienv = symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda);

    let end_time = crate::rt::ocaml_unix::gettimeofday();
    let telemetry = telemetry::create();
    let telemetry = telemetry::duration(Some("parse_duration"), start_time, Some(t_update_reverse_nt), telemetry);
    let telemetry = telemetry::duration(
        Some("update_reverse_nt_duration"),
        t_update_reverse_nt,
        Some(t_update_forward_nt),
        telemetry,
    );
    let telemetry = telemetry::duration(
        Some("update_forward_nt_duration"),
        t_update_forward_nt,
        Some(t_si),
        telemetry,
    );
    let telemetry = telemetry::duration(Some("update_si_duration"), t_si, Some(end_time), telemetry);
    log(&format!(
        "Update_naming_tables_and_si: {}",
        telemetry::to_string(None, &telemetry)
    ));
    UpdateResult {
        naming_table,
        sienv,
        changes: changed_ids,
    }
}
