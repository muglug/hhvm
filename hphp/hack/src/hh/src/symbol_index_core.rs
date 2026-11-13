// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/symbol_index_core.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).
//!
//! Also here, because the crate has no module of their OCaml homes:
//!
//! - [`decls_to_addenda`]: `Direct_decl_parser.decls_to_addenda`
//!   (`decl/direct_decl_parser.ml`; the crate's port of the rest of that
//!   module's file-info function is `direct_decl_service::file_info_of_decls`),
//!   which the OCaml uses on every parse it feeds to the index
//!   (`hh_single_complete`, `Client_ide_incremental`);
//! - [`get_si_addenda`]: the Rust `si_addendum::get_si_addenda`
//!   (`utils/si_addendum.rs`), which the naming-table builder uses, i.e.
//!   what the IDE daemon feeds to the index at init when it builds its
//!   naming table (`Client_ide_init.init_via_build`).
//!
//! Both give the addenda of a file in forward lexical order (the OCaml's
//! `pfh_decls` come through the FFI as `OcamlReverseParsedFileWithHashes`,
//! which turns the parser's reverse-order vector into a forward-order list;
//! checked against the OCaml IDE daemon, whose index answers the same before
//! and after a file is re-indexed by `Client_ide_incremental`). The order is
//! observable: `Local_search_service.search_local_symbols` stops at the
//! first file that alone has `max_results` matches.
//!
//! `Naming_global.GEnv.get_*_full_pos` (N1's `naming_global`, not ported
//! yet) are ported privately here ([`genv`]) for `get_position_for_symbol`.

use ty::decl::shallow::NamedDecl;

use crate::ctx::R;
use crate::file_content;
use crate::file_info;
use crate::file_info::SiAddendum;
use crate::file_info::SiKind;
use crate::hack_event_logger;
use crate::hh_logger;
use crate::local_search_service;
use crate::pos;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::rt::ocaml_unix;
use crate::search_types::SiItem;
use crate::search_utils;
use crate::search_utils::FileSource;
use crate::search_utils::SearchProvider;
use crate::search_utils::SiEnv;
use crate::utils;

/// Log information about calls to the symbol index service
pub fn log_symbol_index_search(
    sienv: &SiEnv,
    query_text: &str,
    max_results: isize,
    results: isize,
    kind_filter: Option<SiKind>,
    start_time: f64,
    caller: &str,
) {
    // In quiet mode we don't log anything to either scuba or console
    if sienv.sie_quiet_mode {
    } else {
        // Calculate duration
        let end_time = ocaml_unix::gettimeofday();
        let duration = end_time - start_time;
        // Clean up strings
        let kind_filter_str = match kind_filter {
            None => "None".to_string(),
            Some(kind) => file_info::show_si_kind(kind),
        };
        let search_provider = search_utils::descriptive_name_of_provider(&sienv.sie_provider);
        // Send information to remote logging system
        if sienv.sie_log_timings {
            hh_logger::log(&format!(
                "[symbolindex] Search [{}] for [{}] found {} results in [{:.3}]",
                search_provider, query_text, results, duration
            ));
        }
        hack_event_logger::search_symbol_index(
            query_text,
            max_results,
            results,
            &kind_filter_str,
            duration,
            caller,
            search_provider,
        )
    }
}

/// `paths_with_addenda`
pub type PathsWithAddenda = Vec<(RelativePath, Vec<SiAddendum>, FileSource)>;

/// FASTER: update from addenda directly
pub fn update_from_addenda(
    sienv: &SiEnv,
    paths_with_addenda: &[(RelativePath, Vec<SiAddendum>, FileSource)],
) -> SiEnv {
    match sienv.sie_provider {
        SearchProvider::NoIndex | SearchProvider::MockIndex { .. } => sienv.clone(),
        SearchProvider::CustomIndex | SearchProvider::LocalIndex => {
            let mut sienv = sienv.clone();
            for (path, addenda, detector) in paths_with_addenda {
                match detector {
                    FileSource::TypeChecker => {
                        local_search_service::update_file_from_addenda_in_place(
                            &mut sienv, path, addenda,
                        )
                    }
                    _ => {}
                }
            }
            sienv
        }
    }
}

/// This method is called when the typechecker is about to re-check a file.
/// Any local caches should be cleared of values for this file.
pub fn remove_files(sienv: &SiEnv, paths: &relative_path::set::T) -> SiEnv {
    match sienv.sie_provider {
        SearchProvider::NoIndex | SearchProvider::MockIndex { .. } => sienv.clone(),
        SearchProvider::CustomIndex | SearchProvider::LocalIndex => {
            // `Relative_path.Set.fold`: in increasing order.
            let mut sienv = sienv.clone();
            for path in paths.iter() {
                local_search_service::remove_file_in_place(&mut sienv, path);
            }
            sienv
        }
    }
}

/// `Naming_global.GEnv`: the functions `get_position_for_symbol` uses.
pub mod genv {
    use std::sync::Arc;

    use oxidized::pos::Pos;

    use crate::ctx::Ctx;
    use crate::file_info;
    use crate::file_provider::FileProviderStale;
    use crate::hh_logger;
    use crate::naming_provider;
    use crate::relative_path;

    /// This function logs and error and raises an exception, ultimately
    /// causing the typechecker to terminate. (`File_provider_stale` is a
    /// panic with that payload, as elsewhere in the crate.)
    pub fn file_disappeared_under_our_feet((pos, name): (&file_info::Pos, &str)) -> ! {
        let fn_ = file_info::get_pos_filename(pos);
        hh_logger::log(&format!("File missing: {}", relative_path::to_absolute(&fn_)));
        hh_logger::log(&format!("Name missing: {}", name));
        std::panic::panic_any(FileProviderStale)
    }

    pub fn get_fun_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> (Pos, String) {
        match naming_provider::get_fun_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => (pos, name.to_string()),
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn get_type_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> (Pos, String) {
        match naming_provider::get_type_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => (pos, name.to_string()),
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }

    pub fn get_const_full_pos(ctx: &Arc<Ctx>, (pos, name): (&file_info::Pos, &str)) -> (Pos, String) {
        match naming_provider::get_const_full_pos_by_parsing_file(ctx, (pos, name)) {
            Some(pos) => (pos, name.to_string()),
            None => file_disappeared_under_our_feet((pos, name)),
        }
    }
}

/// Fetch best available position information for a symbol
pub fn get_position_for_symbol(
    ctx: &provider_context::T,
    symbol: &str,
    kind: SiKind,
) -> Option<(RelativePath, file_content::position::T)> {
    // Symbols can only be found if they are properly namespaced.
    // Even XHP classes must start with a backslash.
    let name_with_ns = utils::add_ns(symbol);

    let helper = |get_pos: &dyn Fn(&provider_context::T, &str) -> Option<file_info::Pos>,
                  resolve_pos: &dyn Fn(
        &provider_context::T,
        (&file_info::Pos, &str),
    ) -> (oxidized::pos::Pos, String)| {
        // get_pos only gives us filename+nametype
        let fileinfo_pos = get_pos(ctx, &name_with_ns);
        // we have to resolve that into a proper position
        fileinfo_pos.map(|fileinfo_pos| {
            let (pos, _) = resolve_pos(ctx, (&fileinfo_pos, &name_with_ns));
            let relpath = file_info::get_pos_filename(&fileinfo_pos);
            let (line, col, _) = pos::info_pos(&pos);
            let pos = file_content::position::from_one_based(line, col);
            (relpath, pos)
        })
    };
    match kind {
        SiKind::SIXHP
        | SiKind::SIInterface
        | SiKind::SITrait
        | SiKind::SIEnum
        | SiKind::SITypedef
        | SiKind::SIClass
        | SiKind::SIConstructor => {
            helper(
                &|ctx, name| crate::naming_provider::get_type_pos(ctx, name),
                &|ctx, x| genv::get_type_full_pos(ctx, x),
            )
        }
        SiKind::SIFunction => helper(
                &|ctx, name| crate::naming_provider::get_fun_pos(ctx, name),
                &|ctx, x| genv::get_fun_full_pos(ctx, x),
            ),
        SiKind::SIGlobalConstant => {
            helper(
                &|ctx, name| crate::naming_provider::get_const_pos(ctx, name),
                &|ctx, x| genv::get_const_full_pos(ctx, x),
            )
        }
        // Items below this are not global symbols and cannot be 'position'ed
        SiKind::SIUnknown
        | SiKind::SINamespace
        | SiKind::SIClassMethod
        | SiKind::SILiteral
        | SiKind::SIClassConstant
        | SiKind::SIProperty
        | SiKind::SILocalVariable
        | SiKind::SIKeyword
        | SiKind::SIMixed => None,
    }
}

/// `absolute_none = Pos.none |> Pos.to_absolute`
pub fn absolute_none() -> pos::Absolute {
    pos::to_absolute(&oxidized::pos::Pos::NONE)
}

/// Shortcut to use the above method to get an absolute pos
pub fn get_pos_for_item_opt(ctx: &provider_context::T, item: &SiItem) -> Option<pos::Absolute> {
    let result = get_position_for_symbol(ctx, &item.fullname, item.kind);
    match result {
        None => None,
        Some((relpath, pos)) => {
            let symbol_len = item.fullname.len() as isize;
            let (line, col) = file_content::position::line_column_one_based(&pos);
            let pos = pos::make_from_lnum_bol_offset(
                relpath,
                (line, 1, col),
                (line, 1, col + symbol_len),
            );
            Some(pos::to_absolute(&pos))
        }
    }
}

/// Shortcut to use the above method to get an absolute pos
pub fn get_pos_for_item(ctx: &provider_context::T, item: &SiItem) -> pos::Absolute {
    let result = get_pos_for_item_opt(ctx, item);
    match result {
        None => absolute_none(),
        Some(pos) => pos,
    }
}

/// The addendum of one decl (`None` for a module, which the symbol index
/// does not represent), as both `decls_to_addenda` and `get_si_addenda`
/// compute it.
fn addendum_of_decl(decl: &NamedDecl<R>) -> Option<SiAddendum> {
    use oxidized::ast_defs::ClassishKind;
    let (name, sia_kind) = match decl {
        NamedDecl::Class(name, c) => (
            name.as_str(),
            match c.kind {
                ClassishKind::Cclass(_) => SiKind::SIClass,
                ClassishKind::Cinterface => SiKind::SIInterface,
                ClassishKind::Ctrait => SiKind::SITrait,
                ClassishKind::Cenum | ClassishKind::CenumClass(_) => SiKind::SIEnum,
            },
        ),
        NamedDecl::Fun(name, _) => (name.as_str(), SiKind::SIFunction),
        NamedDecl::Typedef(name, _) => (name.as_str(), SiKind::SITypedef),
        NamedDecl::Const(name, _) => (name.as_str(), SiKind::SIGlobalConstant),
        NamedDecl::Module(..) => return None,
    };
    let sia_name = utils::strip_ns(name).to_string();
    let (sia_is_abstract, sia_is_final) = match decl {
        NamedDecl::Class(_, c) => (c.is_abstract, c.is_final),
        _ => (false, false),
    };
    Some(SiAddendum {
        name: sia_name,
        kind: sia_kind,
        is_abstract: sia_is_abstract,
        is_final: sia_is_final,
    })
}

/// `Direct_decl_parser.decls_to_addenda`. `decls` are in forward lexical
/// order (as `decl_parser::DeclParser::parse` gives them, and as the OCaml's
/// `pfh_decls` are), and so is the result.
pub fn decls_to_addenda(decls: &[NamedDecl<R>]) -> Vec<SiAddendum> {
    // NB: Must be manually kept in sync with Rust function `si_addenum::get_si_addenda`
    decls.iter().filter_map(addendum_of_decl).collect()
}

/// `si_addendum::get_si_addenda` (the naming-table builder's): `decls` in
/// forward lexical order, and so is the result.
pub fn get_si_addenda(decls: &[NamedDecl<R>]) -> Vec<SiAddendum> {
    decls.iter().filter_map(addendum_of_decl).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The order the OCaml IDE daemon has (see the module doc): with 101
    /// classes in a file, the query "zz" (at most 100 results) stops in that
    /// file before the last class, both from the builder's addenda and from
    /// `decls_to_addenda`.
    #[test]
    fn addenda_in_forward_lexical_order() {
        let mut text = String::from("<?hh\n");
        for i in 0..101 {
            text.push_str(&format!("class Zz{:03} {{}}\n", i));
        }
        let ctx = crate::provider_context::empty_for_test(
            Default::default(),
            Default::default(),
            crate::typing_deps::mode::T::InMemoryMode(None),
        );
        let path = ::pos::RelativePath::new(::pos::Prefix::Root, "a.php");
        let decls = ctx.decl_parser.parse_with_text(path, text.as_bytes()).unwrap();
        for addenda in [decls_to_addenda(&decls), get_si_addenda(&decls)] {
            assert_eq!(addenda.first().unwrap().name, "Zz000");
            let sienv = crate::symbol_index::initialize(&Default::default(), &[], "LocalIndex", true);
            let mut sienv = update_from_addenda(
                &sienv,
                &[(path.into(), addenda, FileSource::TypeChecker)],
            );
            let (r, _) = crate::symbol_index::find_matching_symbols(
                &mut sienv,
                "zz",
                100,
                crate::search_types::AutocompleteType::AcWorkspaceSymbol,
                None,
            );
            assert_eq!(r.len(), 100);
            assert_eq!(r.first().unwrap().name, "Zz099");
            assert_eq!(r.last().unwrap().name, "Zz000");
        }
    }
}
