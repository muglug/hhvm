// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Write_symbol_info.Index_batch` (`write_symbol_info/index_batch.ml`).
//!
//! Indexing a Hack file consists in three distinct passes
//! 1. Indexing source text (regex matching for extracting gencode info from comments
//!    and package information)
//! 2. Indexing declarations, done in [index_decls]
//! 3. Indexing xrefs and filecalls, done in [index_refs]

use super::add_fact;
use super::file_info;
use super::gencode_utils;
use super::glean::hack::package_;
use super::index_decls;
use super::index_xrefs;
use super::predicate::Failure;
use super::predicate::fact_acc;
use crate::full_fidelity_source_text;
use crate::package_provider;
use crate::provider_context;
use crate::yojson::safe as yojson;

type Fa = fact_acc::T;

fn strip_root_if_possible(path: &str, root: &str) -> String {
    let root_len = root.len();
    if !path.starts_with(root) {
        path.to_string()
    } else {
        // (`String.sub ~pos:(root_len + 1)`: raises when [path] is [root].)
        path.get(root_len + 1..)
            .unwrap_or_else(|| panic!("Invalid_argument \"String.sub / Bytes.sub\""))
            .to_string()
    }
}

/// side-effect: updates the generated status in [Fact_acc.t]
fn process_source_text(ctx: &provider_context::T, fa: &mut Fa, file_info: &file_info::T) {
    let file_info::T {
        path,
        root_path,
        source_text,
        ..
    } = file_info;
    fact_acc::set_generated_from(fa, None);
    let text = full_fidelity_source_text::text(source_text);
    match gencode_utils::get_gencode_status(text) {
        gencode_utils::T {
            is_generated: true,
            fully_generated,
            source,
            command,
            class_,
            signature,
        } => {
            fact_acc::set_generated_from(fa, source.clone());
            add_fact::gen_code(path, fully_generated, &signature, &source, &command, &class_, fa);
        }
        _ => {}
    }
    let (package_opt, has_package_override) = package_provider::get_package_with_override_for_file_no_env(
        ctx,
        &strip_root_if_possible(path, root_path),
        text,
    );
    let package_name = match package_opt {
        Some(pkg) => pkg.name.1,
        None => "".to_string(),
    };
    add_fact::file_package(path, package_::T::key(package_name), has_package_override, fa);
}

pub fn build_json(
    ctx: &provider_context::T,
    files_info: &[&file_info::T],
    ownership: bool,
) -> Result<Vec<yojson::T>, Failure> {
    let index_file = |fa: &mut Fa, file_info: &file_info::T| -> Result<(), Failure> {
        let path = &file_info.path;
        fact_acc::set_ownership_unit(fa, Some(path.clone()));
        process_source_text(ctx, fa, file_info);
        let xrefs = index_xrefs::process_xrefs_and_calls(ctx, fa, file_info)?;
        fact_acc::set_pos_map(fa, xrefs.pos_map);
        let mod_xrefs = index_decls::process_decls(ctx, fa, file_info)?;
        let fact_map_xrefs = xrefs.fact_map;
        let fact_map_module_xrefs = mod_xrefs.fact_map;
        // `Fact_id.Map.union (fun _ x _ -> Some x) fact_map_module_xrefs
        // fact_map_xrefs`: the module xrefs win.
        let mut all_xrefs = fact_map_xrefs;
        for (k, v) in fact_map_module_xrefs {
            all_xrefs.insert(k, v);
        }
        if all_xrefs.is_empty() {
        } else {
            add_fact::file_xrefs(path, &all_xrefs, fa);
        }
        Ok(())
    };
    let mut fa = fact_acc::init(ownership);
    for file_info in files_info {
        index_file(&mut fa, file_info)?
    }
    Ok(fact_acc::to_json(&fa))
}
