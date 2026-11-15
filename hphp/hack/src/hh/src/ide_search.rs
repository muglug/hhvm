// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/ide_search.ml`: workspace-symbol search for
//! the IDE. See `hh/PORTING.md`.

use crate::autocomplete_service;
use crate::class_method_search;
use crate::file_info::SiKind;
use crate::pos;
use crate::provider_context;
use crate::rt::ocaml_unix;
use crate::search_types::AutocompleteType;
use crate::search_utils;
use crate::search_utils::SiEnv;
use crate::symbol_index;
use crate::symbol_index_core;
use crate::utils;
use crate::yojson::safe as yojson;

pub fn result_to_json(res: &search_utils::Symbol) -> yojson::T {
    let desc_string = search_utils::kind_to_string(res.result_type);
    let p = &res.pos;
    let fn_ = pos::filename(p);
    let (line, start, end_) = pos::info_pos(p);
    yojson::T::Assoc(vec![
        (
            "name".to_string(),
            yojson::T::String(utils::strip_ns(&res.name).to_string()),
        ),
        ("filename".to_string(), yojson::T::String(fn_.to_string())),
        ("desc".to_string(), yojson::T::String(desc_string.to_string())),
        ("line".to_string(), yojson::T::Int(line)),
        ("char_start".to_string(), yojson::T::Int(start)),
        ("char_end".to_string(), yojson::T::Int(end_)),
        ("scope".to_string(), yojson::T::String(String::new())),
    ])
}

/// `Str.split_delim (Str.regexp "::") query_text`
fn split_delim_colon_colon(s: &str) -> Vec<&str> {
    s.split("::").collect()
}

pub fn go(
    ctx: &provider_context::T,
    query_text: &str,
    kind_filter: &str,
    sienv_ref: &mut SiEnv,
) -> search_utils::Result {
    let max_results = 100;
    let start_time = ocaml_unix::gettimeofday();
    let kind_filter = search_utils::string_to_kind(kind_filter);
    let context = AutocompleteType::AcWorkspaceSymbol;
    // If query contains "::", search class methods instead of top level definitions
    let results = match split_delim_colon_colon(query_text).as_slice() {
        [class_name_query, method_query] => {
            // Fixup the kind filter
            let kind_filter = Some(SiKind::SIClass);
            // Get the class with the most similar name to `class_name_query`
            let (candidates, _is_complete) = symbol_index::find_matching_symbols(
                sienv_ref,
                class_name_query,
                1,
                context,
                kind_filter,
            );
            let class_ = candidates.into_iter().next().map(|r| r.name);
            match class_ {
                Some(name) => {
                    class_method_search::query_class_methods(ctx, &utils::add_ns(&name), method_query)
                }
                None => {
                    // When we can't find a class with a name similar to the given one,
                    // just return no search results.
                    vec![]
                }
            }
        }
        _ => {
            let (temp_results, _is_complete) = symbol_index::find_matching_symbols(
                sienv_ref,
                query_text,
                max_results,
                context,
                kind_filter,
            );
            autocomplete_service::add_position_to_results(ctx, &temp_results)
        }
    };
    symbol_index_core::log_symbol_index_search(
        sienv_ref,
        query_text,
        max_results,
        results.len() as isize,
        kind_filter,
        start_time,
        "Ide_search.go",
    );
    results
}

/// The comparison with the OCaml (not a unit test: `#[ignore]`, run by
/// hand). With `HH_IDE_SEARCH_CMP_ROOT` (a root with a `.hhconfig`), `HH_IDE_SEARCH_CMP_QUERIES` (one JSON
/// string per line) and `HH_IDE_SEARCH_CMP_OUT`: indexes every file of the root and the hhi
/// files as the IDE daemon does when it builds its naming table
/// (`Client_ide_init.init_via_build`: the addenda of `get_si_addenda`), then
/// writes, for each query, the `workspace/symbol` result that `Client_lsp`
/// makes of `Ide_search.go` (`hack_symbol_to_lsp`), one JSON line per query,
/// in the form the OCaml's answers are recorded in for the comparison.
#[cfg(all(test, feature = "server"))]
mod compare_with_ocaml {
    use rayon::prelude::*;

    use super::*;
    use crate::search_utils::FileSource;

    /// The physical footprint and resident size of this process (0 where
    /// the OS does not say).
    fn footprint() -> (u64, u64) {
        #[cfg(target_os = "macos")]
        unsafe {
            let mut info: libc::rusage_info_v4 = std::mem::zeroed();
            libc::proc_pid_rusage(
                libc::getpid(),
                libc::RUSAGE_INFO_V4,
                &mut info as *mut _ as *mut libc::rusage_info_t,
            );
            (info.ri_phys_footprint, info.ri_resident_size)
        }
        #[cfg(not(target_os = "macos"))]
        (0, 0)
    }

    fn lsp_kind(k: SiKind) -> i64 {
        match k {
            SiKind::SIClass => 5,
            SiKind::SIInterface | SiKind::SITrait => 11,
            SiKind::SIEnum => 10,
            SiKind::SIClassMethod => 6,
            SiKind::SIFunction => 12,
            SiKind::SITypedef => 5,
            SiKind::SIGlobalConstant => 14,
            SiKind::SINamespace => 3,
            SiKind::SIMixed => 13,
            SiKind::SIXHP => 5,
            SiKind::SILiteral => 13,
            SiKind::SIClassConstant => 14,
            SiKind::SIProperty => 7,
            SiKind::SILocalVariable => 13,
            SiKind::SIConstructor => 9,
            SiKind::SIKeyword | SiKind::SIUnknown => panic!("Unknown symbol kind"),
        }
    }

    #[test]
    #[ignore]
    fn workspace_symbol_queries() {
        let root = std::env::var("HH_IDE_SEARCH_CMP_ROOT").unwrap();
        let queries = std::fs::read_to_string(std::env::var("HH_IDE_SEARCH_CMP_QUERIES").unwrap()).unwrap();
        let out_path = std::env::var("HH_IDE_SEARCH_CMP_OUT").unwrap();
        let hhi_root = std::path::PathBuf::from(std::env::var("HH_IDE_SEARCH_CMP_HHI").unwrap());
        let t0 = std::time::Instant::now();
        let r = crate::check::discover_root(std::path::Path::new(&root), &[]).unwrap();
        let mut stats = crate::check::Stats::default();
        crate::check::declare_files(&r.ctx, &r.paths, &mut stats);
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Root, &r.root);
        crate::relative_path::set_path_prefix(crate::relative_path::Prefix::Hhi, &hhi_root);
        let ctx = std::sync::Arc::new(r.ctx);
        crate::hh_single_type_check::install(&ctx);
        eprintln!("declared {} files in {:?}", r.paths.len(), t0.elapsed());

        // Symbol index: `Symbol_index.initialize` with the local config's
        // `ide_symbolindex_search_provider` (default "LocalIndex") and
        // `symbolindex_quiet` (default false), then `update_from_addenda`.
        let (fp0, rss0) = footprint();
        let t1 = std::time::Instant::now();
        // The naming-table builder walks the root with `jwalk`, which skips
        // hidden files and directories (`find_utils::find_hack_files`).
        let paths: Vec<_> = r
            .paths
            .iter()
            .filter(|p| {
                p.prefix() != ::pos::Prefix::Root
                    || !p.path().components().any(|c| c.as_os_str().to_string_lossy().starts_with('.'))
            })
            .copied()
            .collect();
        let paths_with_addenda: Vec<_> = paths
            .par_iter()
            .map(|path| {
                let decls = ctx.decl_parser.parse(*path).unwrap();
                (
                    crate::relative_path::RelativePath::from(*path),
                    crate::symbol_index_core::get_si_addenda(&decls),
                    FileSource::TypeChecker,
                )
            })
            .collect();
        let parse_time = t1.elapsed();
        let n_items: usize = paths_with_addenda.iter().map(|(_, a, _)| a.len()).sum();
        let t2 = std::time::Instant::now();
        let sienv = crate::symbol_index::initialize(
            &ctx.tco,
            &ctx.tco.po.auto_namespace_map,
            "LocalIndex",
            false,
        );
        let sienv = crate::symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda);
        let index_time = t2.elapsed();
        drop(paths_with_addenda);
        let (fp1, rss1) = footprint();
        let est: usize = sienv
            .lss_fullitems
            .iter()
            .map(|(p, items)| {
                std::mem::size_of_val(p)
                    + p.path_str().len()
                    + 16
                    + items.capacity() * std::mem::size_of::<crate::search_utils::SiFullitem>()
                    + items.iter().map(|i| i.name.capacity()).sum::<usize>()
                    + items.first().map_or(0, |i| i.filepath.len() + 16)
                    + 64
            })
            .sum();
        eprintln!(
            "index: {} files, {} items; addenda (parse) {:?}, index build {:?}; footprint {} -> {} MB, rss {} -> {} MB; estimated index heap {} MB",
            sienv.lss_fullitems.len(),
            n_items,
            parse_time,
            index_time,
            fp0 >> 20,
            fp1 >> 20,
            rss0 >> 20,
            rss1 >> 20,
            est >> 20
        );

        let mut out = String::new();
        let mut total = std::time::Duration::ZERO;
        for line in queries.lines() {
            let q: String = serde_json::from_str(line).unwrap();
            let mut sienv_ref = sienv.clone();
            let t = std::time::Instant::now();
            let results = go(&ctx, &q, "", &mut sienv_ref);
            total += t.elapsed();
            let result: Vec<serde_json::Value> = results
                .iter()
                .map(|symbol| {
                    let range = crate::lsp_helpers::hack_pos_to_lsp_range(|a: &String, b: &String| a == b, &symbol.pos);
                    serde_json::json!({
                        "name": utils::strip_ns(&symbol.name),
                        "kind": lsp_kind(symbol.result_type),
                        "location": {
                            "uri": format!("file://{}", pos::filename(&symbol.pos)),
                            "range": {
                                "start": {"line": range.start.line, "character": range.start.character},
                                "end": {"line": range.end_.line, "character": range.end_.character},
                            },
                        },
                    })
                })
                .collect();
            out.push_str(&serde_json::json!({"query": q, "result": result}).to_string());
            out.push('\n');
        }
        eprintln!("queries: {:?} total", total);
        std::fs::write(out_path, out).unwrap();
    }
}
