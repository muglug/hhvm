// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart in this version: the producer of a complete saved
//! state. The OCaml of this version cannot write a saved state: upstream
//! removed `hh_server --save-state` (and `hh_client --save-state`,
//! `--gen-saved-ignore-type-errors`) in f6cc06f5b6e ("Remove hh_client
//! --save-state and hh_server --save-state", January 2026, just before
//! this version), Meta makes them with `hh_distc`. This module is the
//! OCaml as it was just before that commit: `Server_init.save_state`
//! ([`save_state`]) and `SaveStateService.save_state`,
//! `dump_naming_and_errors`, `dump_errors_json`,
//! `saved_state_build_revision_write`, `dump_dep_graph_64bit`
//! ([`save_state_service_save_state`]), which write
//!
//! - `<FILE>_naming.sql`: the naming table (`Naming_table.save`);
//! - `<FILE>.err`: the files with diagnostics (Marshal of a
//!   `Relative_path.Set.t`; not written when there are none);
//! - `<FILE>.err.json`: the same, as a JSON list of suffixes;
//! - `<FILE>_info.json`: `{"build_revision": ...}`;
//! - `<FILE>_64bit_dep_graph.delta` and `<FILE>_incremental_info.json`: the
//!   dependency edges discovered (`Typing_deps.save_discovered_edges`) and
//!   the base graph they extend.
//!
//! plus, what the OCaml left to Meta's tools and the loader of this version
//! reads (`Server_args.saved_state_target_info`, `Save_state_service.
//! load_saved_state_exn`):
//!
//! - `<FILE>.hhdg`: the dependency graph (base graph + edges), in the
//!   format `depgraph_reader` reads (the `deptable` of the
//!   `--with-mini-state` spec);
//! - `<FILE>.warn`: the hashes of the warnings
//!   (`Diagnostics.make_warning_saved_state`, Marshal of a
//!   `Warnings_saved_state.t`), which the loader reads to hide pre-existing
//!   warnings.
//!
//! So `hh_server --check --save-state FILE ROOT` (or `--save-mini`, `-s`)
//! then `hh_server --with-mini-state '{"data_dump": {"state": FILE,
//! "deptable": FILE.hhdg, "changes": [...], "corresponding_base_revision":
//! "..."}}' ROOT` (with `--ignore-hh-version` across implementations: the
//! build revision is checked, as between two OCaml builds).

use std::collections::HashMap;
use std::io::Write;

use depgraph_reader::compress::UncompressedHeader;

use crate::diagnostics;
use crate::exit;
use crate::exit_status;
use crate::hh_logger;
use crate::naming_sqlite;
use crate::naming_table;
use crate::relative_path;
use crate::save_state_service;
use crate::save_state_service_types::SaveStateResult;
use crate::server_args;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::typing_deps;
use crate::yojson::safe as json;

/// What `SaveStateService.save_state` raises (`failwith`), and the I/O
/// errors (`Sys_error`).
#[derive(Debug)]
pub enum SaveStateError {
    Failure(String),
    SysError(String),
    NamingSqlite(naming_sqlite::Error),
}

impl std::fmt::Display for SaveStateError {
    /// `Printexc.to_string`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SaveStateError::Failure(s) => write!(f, "Failure({})", crate::rt::ocaml_printf::sprintf_s(s)),
            SaveStateError::SysError(s) => write!(f, "Sys_error({})", crate::rt::ocaml_printf::sprintf_s(s)),
            SaveStateError::NamingSqlite(e) => write!(f, "{:?}", e),
        }
    }
}

fn sys_error(what: &str, e: std::io::Error) -> SaveStateError {
    let msg = e.to_string();
    let msg = match msg.rfind(" (os error ") {
        Some(i) => msg[..i].to_string(),
        None => msg,
    };
    SaveStateError::SysError(format!("{}: {}", what, msg))
}

/// `Server_init.save_state genv env output_filename`: refuses (on stderr)
/// to save a state with diagnostics unless `--gen-saved-ignore-type-errors`.
pub fn save_state(
    genv: &Genv,
    env: &Env,
    output_filename: &str,
) -> Result<Option<SaveStateResult>, SaveStateError> {
    let ignore_errors = server_args::gen_saved_ignore_type_errors(&genv.options);
    // (`Errors.is_empty` of the OCaml of that time is
    // `Diagnostics.has_no_errors_or_warnings`: warnings count.)
    let has_errors = !diagnostics::has_no_errors_or_warnings(None, &env.diagnostics);
    let do_save_state = if ignore_errors {
        if has_errors {
            eprint!("WARNING: BROKEN SAVED STATE! Generating saved state. Ignoring type errors.\n");
        } else {
            eprint!("Generating saved state and ignoring type errors, but there were none.\n");
        }
        true
    } else if has_errors {
        eprint!("Refusing to generate saved state. There are type errors\n");
        eprint!("and --gen-saved-ignore-type-errors was not provided.\n");
        false
    } else {
        true
    };
    if !do_save_state {
        Ok(None)
    } else {
        let result = save_state_service_save_state(env, output_filename)?;
        Ok(Some(result))
    }
}

/// `SaveStateService.dump_naming_and_errors output_filename naming_table
/// errors`: dumps the naming-table (a saveable form of FileInfo), and
/// errors if any.
fn dump_naming_and_errors(
    output_filename: &str,
    naming_table: &naming_table::T,
    errors: &diagnostics::T,
) -> Result<(), SaveStateError> {
    let naming_sql_filename = format!("{}_naming.sql", output_filename);
    let save_result =
        naming_table::save(naming_table, &naming_sql_filename).map_err(SaveStateError::NamingSqlite)?;
    hh_logger::log(&format!(
        "Inserted symbols into the naming table:\n{}",
        naming_sqlite::show_save_result(&save_result)
    ));
    hh_logger::log(&format!(
        "Finished saving naming table with {} errors.",
        save_result.errors.len()
    ));
    if !save_result.errors.is_empty() {
        exit::exit(None, None, None, None, exit_status::T::SqlAssertionFailure)
    }
    assert!(std::path::Path::new(&naming_sql_filename).exists());
    hh_logger::log(&format!("Saved naming table sqlite to '{}'", naming_sql_filename));
    // Let's not write empty error files.
    if diagnostics::has_no_errors_or_warnings(None, errors) {
    } else {
        let error_files: relative_path::set::T =
            diagnostics::get_failed_files(errors).into_iter().collect();
        let filename = save_state_service::get_errors_filename(output_filename);
        save_state_service::save_contents(
            &filename,
            &save_state_service::saved_state_errors_to_ocaml(&error_files),
        )
        .map_err(|e| sys_error(&filename, e))?;
    }
    Ok(())
}

/// `Hh_json.json_to_output` to a new file.
fn write_json(filename: &str, j: &json::T) -> Result<(), SaveStateError> {
    std::fs::write(filename, json::to_string(j)).map_err(|e| sys_error(filename, e))
}

/// Sorts and dumps the error relative paths in JSON format.
/// An empty JSON list will be dumped if there are no errors.
/// (`dump_errors_json output_filename errors`)
fn dump_errors_json(output_filename: &str, errors: &diagnostics::T) -> Result<(), SaveStateError> {
    let error_files = diagnostics::get_failed_files(errors);
    let errors_json = json::T::List(
        error_files
            .iter()
            .map(|p| json::T::String(relative_path::suffix(p)))
            .collect(),
    );
    write_json(&save_state_service::get_errors_filename_json(output_filename), &errors_json)
}

/// `saved_state_build_revision_write ~base_file_name`
fn saved_state_build_revision_write(base_file_name: &str) -> Result<(), SaveStateError> {
    let info_file = save_state_service::saved_state_info_file_name(base_file_name);
    write_json(
        &info_file,
        &json::T::Assoc(vec![(
            "build_revision".to_string(),
            json::T::String(crate::build_id::build_revision()),
        )]),
    )
}

/// `dump_dep_graph_64bit ~mode ~db_name ~incremental_info_file`
fn dump_dep_graph_64bit(
    mode: &typing_deps::mode::T,
    db_name: &str,
    incremental_info_file: &str,
) -> Result<SaveStateResult, SaveStateError> {
    let t = crate::rt::ocaml_unix::gettimeofday();
    let base_dep_graph = base_dep_graph_of_mode(mode);
    write_json(
        incremental_info_file,
        &json::T::Assoc(vec![(
            "base_dep_graph".to_string(),
            match base_dep_graph {
                Some(s) => json::T::String(s),
                None => json::T::Null,
            },
        )]),
    )?;
    let dep_table_edges_added = typing_deps::save_discovered_edges(mode, db_name, false);
    let _: f64 = hh_logger::log_duration(None, None, "Writing discovered edges took", t);
    Ok(SaveStateResult { dep_table_edges_added })
}

fn base_dep_graph_of_mode(mode: &typing_deps::mode::T) -> Option<String> {
    match mode {
        typing_deps::mode::T::InMemoryMode(base_dep_graph) => base_dep_graph.clone(),
        typing_deps::mode::T::SaveToDiskMode { graph, .. } => graph.clone(),
    }
}

/// `SaveStateService.save_state env output_filename`: saves the saved
/// state to the given path. Returns number of dependency edges dumped into
/// the database. Then writes what the loader also reads (`.hhdg`, `.warn`).
pub fn save_state_service_save_state(env: &Env, output_filename: &str) -> Result<SaveStateResult, SaveStateError> {
    let dir = crate::path::dirname(&output_filename.to_string());
    crate::sys_utils::mkdir_p(&dir).map_err(|e| sys_error(&dir, e))?;
    let db_name = format!("{}_64bit_dep_graph.delta", output_filename);
    if std::path::Path::new(output_filename).exists() {
        return Err(SaveStateError::Failure(format!(
            "Cowardly refusing to overwrite '{}'.",
            output_filename
        )));
    }
    if std::path::Path::new(&db_name).exists() {
        return Err(SaveStateError::Failure(format!(
            "Cowardly refusing to overwrite '{}'.",
            db_name
        )));
    }
    {
        let t = crate::rt::ocaml_unix::gettimeofday();
        dump_naming_and_errors(output_filename, &env.naming_table, &env.diagnostics)?;
        let _: f64 = hh_logger::log_duration(None, None, "Saving saved-state naming+errors took", t);
    }
    let result = match &env.deps_mode {
        typing_deps::mode::T::InMemoryMode(_) => {
            let incremental_info_file = format!("{}_incremental_info.json", output_filename);
            dump_errors_json(output_filename, &env.diagnostics)?;
            saved_state_build_revision_write(output_filename)?;
            dump_dep_graph_64bit(&env.deps_mode, &db_name, &incremental_info_file)?
        }
        typing_deps::mode::T::SaveToDiskMode {
            graph: _,
            new_edges_dir,
            human_readable_dep_map_dir,
        } => {
            dump_errors_json(output_filename, &env.diagnostics)?;
            saved_state_build_revision_write(output_filename)?;
            hh_logger::warn(
                None,
                None,
                &format!(
                    "saveStateService: not saving 64-bit dep graph edges to disk, because they are already in {}",
                    new_edges_dir
                ),
            );
            if let Some(dir) = human_readable_dep_map_dir {
                hh_logger::warn(
                    None,
                    None,
                    &format!("saveStateService: human readable dep map dir: {}", dir),
                );
            }
            SaveStateResult {
                dep_table_edges_added: 0,
            }
        }
    };
    // What the loader reads that the OCaml left to other tools.
    write_warnings(output_filename, &env.diagnostics)?;
    write_hhdg_of_state(output_filename, &env.deps_mode, &db_name)?;
    Ok(result)
}

/// `<FILE>.warn`: `Diagnostics.make_warning_saved_state`, marshalled.
fn write_warnings(output_filename: &str, errors: &diagnostics::T) -> Result<(), SaveStateError> {
    let t = crate::rt::ocaml_unix::gettimeofday();
    let filename = format!("{}.warn", output_filename);
    let warnings = diagnostics::make_warning_saved_state(errors);
    save_state_service::save_contents(&filename, &save_state_service::warnings_saved_state_to_ocaml(&warnings))
        .map_err(|e| sys_error(&filename, e))?;
    let _: f64 = hh_logger::log_duration(
        None,
        None,
        &format!("Saved {} warning hashes to '{}'", warnings.len(), filename),
        t,
    );
    Ok(())
}

/// `<FILE>.hhdg`: the edges of the base graph of `mode` (if any) and those
/// discovered (the delta just written, or the files of `--save-64bit`).
fn write_hhdg_of_state(
    output_filename: &str,
    mode: &typing_deps::mode::T,
    db_name: &str,
) -> Result<(), SaveStateError> {
    let t = crate::rt::ocaml_unix::gettimeofday();
    let mut edges: Vec<(u64, u64)> = vec![];
    if let Some(base) = base_dep_graph_of_mode(mode) {
        let g = depgraph_reader::DepGraph::from_path(&base).map_err(|e| sys_error(&base, e))?;
        add_edges_of_graph(&g, &mut edges);
    }
    match mode {
        typing_deps::mode::T::InMemoryMode(_) => add_edges_of_delta_file(db_name, &mut edges)?,
        typing_deps::mode::T::SaveToDiskMode { new_edges_dir, .. } => {
            let mut files: Vec<_> = std::fs::read_dir(new_edges_dir)
                .map_err(|e| sys_error(new_edges_dir, e))?
                .filter_map(|e| e.ok())
                .map(|e| e.path())
                .filter(|p| p.extension().is_some_and(|x| x == "bin"))
                .collect();
            files.sort();
            for f in files {
                add_edges_of_delta_file(&f.to_string_lossy(), &mut edges)?;
            }
        }
    }
    let filename = format!("{}.hhdg", output_filename);
    let n = write_hhdg(std::path::Path::new(&filename), edges).map_err(|e| sys_error(&filename, e))?;
    let _: f64 = hh_logger::log_duration(
        None,
        None,
        &format!("Wrote dependency graph of {} edges to '{}'", n, filename),
        t,
    );
    Ok(())
}

/// The edges of a graph `depgraph_reader` reads, as (dependency, dependent).
pub fn add_edges_of_graph(g: &depgraph_reader::DepGraph, edges: &mut Vec<(u64, u64)>) {
    for dependency in g.all_hashes() {
        if let Some(list) = g.hash_list_for(dependency) {
            for dependent in g.hash_list_hashes(list) {
                edges.push((dependency.into(), dependent.into()));
            }
        }
    }
}

/// The edges of a file in the format of `Typing_deps.save_discovered_edges`
/// (`DepGraphDelta`'s) as (dependency, dependent).
fn add_edges_of_delta_file(filename: &str, edges: &mut Vec<(u64, u64)>) -> Result<(), SaveStateError> {
    let f = std::fs::File::open(filename).map_err(|e| sys_error(filename, e))?;
    let mut delta = dep_graph_delta::DepGraphDelta::default();
    delta
        .read_added_edges_from(std::io::BufReader::new(f), |_, _| true)
        .map_err(|e| sys_error(filename, e))?;
    for (dependency, dependents) in delta.into_iter_added_edges() {
        for dependent in dependents {
            edges.push((dependency.into(), dependent.into()));
        }
    }
    Ok(())
}

/// The encoding of `vint64` (what `depgraph_reader` decodes): one byte for
/// values below 2^7, `n` bytes for values below 2^(7n) (the length in the
/// trailing zero bits of the first byte), nine for the rest.
fn vint64_encode(value: u64, out: &mut Vec<u8>) {
    let bits = 64 - value.leading_zeros() as usize;
    let len = if bits == 0 { 1 } else { std::cmp::min(9, (bits + 6) / 7) };
    if len == 9 {
        out.push(0);
        out.extend_from_slice(&value.to_le_bytes());
    } else {
        let encoded = ((value << 1) | 1) << (len - 1);
        out.extend_from_slice(&encoded.to_le_bytes()[..len]);
    }
}

/// `ByteApproximatedLen::encode n` then `decode` (`depgraph_reader/
/// compress.rs`): the byte of the largest length <= `n` that one byte
/// represents, and that length.
fn byte_approximated_len(n: u32) -> (u8, u32) {
    let exp_to_shift = |exp: u8| 7 + 5 * exp;
    let v = if n <= 0x7f {
        n as u8
    } else {
        let max_representable: u32 = 0x1f << exp_to_shift(0x3);
        let n = std::cmp::min(n, max_representable);
        let exp = (4 - n.leading_zeros() / 5) as u8;
        let mantissa = (n >> exp_to_shift(exp)) & 0x1f;
        0x80 | (exp << 5) | mantissa as u8
    };
    let decoded = if v <= 0x7f {
        v as u32
    } else {
        let exp = (v >> 5) & 0x3;
        let mantissa = v & 0x1f;
        (mantissa as u32) << exp_to_shift(exp)
    };
    (v, decoded)
}

/// Writes the dependency graph of `edges` ((dependency, dependent) pairs)
/// to `path` in the uncompressed format `depgraph_reader` reads (what
/// `depgraph_decompress` makes of a `.zhhdg`: see
/// `depgraph_reader/compress.rs`): the header, the deps (sorted), their
/// sort order (the identity), the offset of each one's edge list, the edge
/// lists (`num_blocks`, `num_indices` as `vint64`s, then `RleBlock`s).
/// Identical lists are written once. Returns the number of unique edges.
pub fn write_hhdg(path: &std::path::Path, mut edges: Vec<(u64, u64)>) -> std::io::Result<usize> {
    edges.sort_unstable();
    edges.dedup();
    let mut deps: Vec<u64> = Vec::with_capacity(edges.len());
    for &(a, b) in &edges {
        deps.push(a);
        deps.push(b);
    }
    deps.sort_unstable();
    deps.dedup();
    let index_of = |d: u64| deps.binary_search(&d).unwrap() as u32;
    // The adjacency lists, and the (unshifted) offset of each dep's.
    let mut lists: Vec<u8> = vec![];
    // The empty list first, at offset 0.
    vint64_encode(0, &mut lists);
    vint64_encode(0, &mut lists);
    let mut offsets: Vec<u64> = vec![0; deps.len()];
    let mut shared: HashMap<Vec<u32>, u64> = HashMap::new();
    let mut i = 0;
    while i < edges.len() {
        let dependency = edges[i].0;
        let mut indices: Vec<u32> = vec![];
        while i < edges.len() && edges[i].0 == dependency {
            indices.push(index_of(edges[i].1));
            i += 1;
        }
        indices.sort_unstable();
        let offset = match shared.get(&indices) {
            Some(&o) => o,
            None => {
                let o = lists.len() as u64;
                // Runs of consecutive indices, each split into blocks whose
                // approximated lengths add up to the run's.
                // An `RleBlock`: `start` (u32), the approximated length (u8).
                let mut blocks: Vec<(u32, u8)> = vec![];
                let mut j = 0;
                while j < indices.len() {
                    let start = indices[j];
                    let mut end = start + 1;
                    j += 1;
                    while j < indices.len() && indices[j] == end {
                        end += 1;
                        j += 1;
                    }
                    let mut s = start;
                    while s < end {
                        let (encoded_len, len) = byte_approximated_len(end - s);
                        blocks.push((s, encoded_len));
                        s += len;
                    }
                }
                vint64_encode(blocks.len() as u64, &mut lists);
                vint64_encode(indices.len() as u64, &mut lists);
                for (start, encoded_len) in &blocks {
                    lists.extend_from_slice(&start.to_ne_bytes());
                    lists.push(*encoded_len);
                }
                shared.insert(indices, o);
                o
            }
        };
        offsets[index_of(dependency) as usize] = offset;
    }
    // Offsets are u32s, left-shifted by the alignment shift when read.
    let mut shift: u8 = 0;
    while (lists.len() as u64) >> shift > u32::MAX as u64 {
        shift += 1;
    }
    if shift > 0 {
        // Realign every list on a multiple of 1 << shift.
        let mut realigned: Vec<u8> = Vec::with_capacity(lists.len() * 2);
        let mut moved: HashMap<u64, u64> = HashMap::new();
        let mut starts: Vec<u64> = offsets.clone();
        starts.push(0);
        starts.sort_unstable();
        starts.dedup();
        for (k, &start) in starts.iter().enumerate() {
            while realigned.len() % (1usize << shift) != 0 {
                realigned.push(0);
            }
            moved.insert(start, realigned.len() as u64);
            let stop = starts.get(k + 1).copied().unwrap_or(lists.len() as u64);
            realigned.extend_from_slice(&lists[start as usize..stop as usize]);
        }
        for o in offsets.iter_mut() {
            *o = moved[o];
        }
        lists = realigned;
    }
    let mut out = std::io::BufWriter::new(std::fs::File::create(path)?);
    // `UncompressedHeader` (repr(C)): magic, version, num_deps,
    // adjacency_list_alignment_shift, 7 bytes of padding.
    out.write_all(&UncompressedHeader::MAGIC)?;
    out.write_all(&UncompressedHeader::LATEST_VERSION.to_ne_bytes())?;
    out.write_all(&(deps.len() as u64).to_ne_bytes())?;
    out.write_all(&[shift, 0, 0, 0, 0, 0, 0, 0])?;
    for d in &deps {
        out.write_all(&d.to_ne_bytes())?;
    }
    for k in 0..deps.len() as u32 {
        out.write_all(&k.to_ne_bytes())?;
    }
    for o in &offsets {
        out.write_all(&((o >> shift) as u32).to_ne_bytes())?;
    }
    out.write_all(&lists)?;
    out.into_inner().map_err(|e| e.into_error())?;
    Ok(edges.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vint64_is_the_crates_encoding() {
        // The one-byte form, as the reader's test fixtures write it.
        let mut b = vec![];
        vint64_encode(5, &mut b);
        assert_eq!(b, vec![(5 << 1) | 1]);
        for v in [0u64, 1, 127, 128, 300, 1 << 20, (1 << 56) - 1, 1 << 56, u64::MAX] {
            let mut b = vec![];
            vint64_encode(v, &mut b);
            // Decode as `vint64::decode` does.
            let first = b[0];
            let len = if first == 0 { 9 } else { first.trailing_zeros() as usize + 1 };
            assert_eq!(len, b.len(), "{}", v);
            let decoded = if len == 9 {
                u64::from_le_bytes(b[1..9].try_into().unwrap())
            } else {
                let mut buf = [0u8; 8];
                buf[..len].copy_from_slice(&b);
                u64::from_le_bytes(buf) >> len
            };
            assert_eq!(decoded, v);
        }
    }

    #[test]
    fn hhdg_round_trip_through_the_reader() {
        let dir = std::env::temp_dir().join(format!("ss4_hhdg_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("g.hhdg");
        let mut edges = vec![];
        // A long run (more than 0x7f consecutive dependents), shared lists,
        // a dependent with no dependents of its own, duplicates.
        for k in 0..300u64 {
            edges.push((1 << 40, (1 << 41) + k));
        }
        edges.push((7, 9));
        edges.push((8, 9));
        edges.push((8, 9));
        edges.push((9, 1 << 40));
        edges.push((u64::MAX >> 2, 7));
        let n = write_hhdg(&path, edges.clone()).unwrap();
        edges.sort_unstable();
        edges.dedup();
        assert_eq!(n, edges.len());
        let g = depgraph_reader::DepGraph::from_path(&path).unwrap();
        let mut back = vec![];
        add_edges_of_graph(&g, &mut back);
        back.sort_unstable();
        assert_eq!(back, edges);
        assert!(g.dependent_dependency_edge_exists(depgraph_reader::Dep::new(9), depgraph_reader::Dep::new(8)));
        assert!(!g.dependent_dependency_edge_exists(depgraph_reader::Dep::new(8), depgraph_reader::Dep::new(9)));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
