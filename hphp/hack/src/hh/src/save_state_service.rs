// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/save_state_service.ml` (the load side).
//!
//! Owned by **SS3** (plan §7.3). Created empty by W0b.

/// `go_naming naming_table output_filename`
pub fn go_naming(
    naming_table: &crate::naming_table::T,
    output_filename: &str,
) -> Result<crate::save_state_service_types::SaveNamingResult, String> {
    // `Utils.try_with_stack` and `Exception.get_ctor_string`
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let save_result = match crate::naming_table::save(naming_table, output_filename) {
            Ok(save_result) => save_result,
            Err(e) => panic!("{:?}", e),
        };
        crate::hh_logger::log(&format!(
            "Inserted symbols into the naming table:\n{}",
            crate::naming_sqlite::show_save_result(&save_result)
        ));
        if !save_result.errors.is_empty() {
            let _ = std::fs::remove_dir_all(output_filename).or_else(|_| std::fs::remove_file(output_filename));
            panic!("Failure(\"Naming table state had errors - deleting output file!\")")
        } else {
            crate::save_state_service_types::SaveNamingResult {
                nt_files_added: save_result.files_added,
                nt_symbols_added: save_result.symbols_added,
            }
        }
    }));
    result.map_err(|payload| crate::exception::get_ctor_string(&crate::exception::wrap(payload)))
}

/// The naming table to save: `naming_table`, whose file infos get the hashes
/// of their decls.
///
/// (Not in the OCaml, whose file infos always have them. The daemon's are
/// made by `Direct_decl_service.file_info_of_decls`, from decls without
/// hashes: each such file is parsed again here.)
pub fn naming_table_with_decl_hashes(
    ctx: &crate::provider_context::T,
    naming_table: &crate::naming_table::T,
) -> crate::naming_table::T {
    let has_hashes = |info: &crate::file_info::T| {
        let crate::file_info::Ids {
            funs,
            classes,
            typedefs,
            consts,
            modules,
        } = &info.ids;
        funs.iter()
            .chain(classes)
            .chain(typedefs)
            .chain(consts)
            .chain(modules)
            .all(|id| id.decl_hash.is_some())
    };
    crate::naming_table::fold(naming_table, crate::naming_table::empty(), |path, info, acc| {
        let info = if has_hashes(info) {
            info.clone()
        } else {
            match crate::direct_decl_service::direct_decl_parse(ctx, path) {
                Some(parsed_file) => crate::direct_decl_service::decls_to_fileinfo(path, &parsed_file),
                None => info.clone(),
            }
        };
        crate::naming_table::update(&acc, path.clone(), info)
    })
}
