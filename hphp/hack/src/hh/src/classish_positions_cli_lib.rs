// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/classish_positions_cli_lib.ml` (`hh single
//! --dump-classish-positions`). See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::io::Write;

use crate::classish_positions;
use crate::classish_positions::ClassishPositions;
use crate::code_actions::code_actions_utils::Patch;
use crate::code_actions::code_actions_utils::apply_patches_to_string;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;

fn pos_to_patches(pos: &Pos) -> Vec<Patch> {
    // (`Pos.to_absolute`: the offsets are the same.)
    vec![
        Patch::Replace {
            pos: crate::pos::shrink_to_start(pos),
            text: ">".to_string(),
        },
        Patch::Replace {
            pos: crate::pos::shrink_to_end(pos),
            text: "<".to_string(),
        },
    ]
}

fn classish_positions_for_class_to_patches(cp: &ClassishPositions<Pos>) -> BTreeMap<String, Vec<Patch>> {
    let ClassishPositions {
        start_of_body,
        end_of_body,
        closing_brace,
        body_elements,
    } = cp;
    [
        ("classish_start_of_body", pos_to_patches(start_of_body)),
        ("classish_end_of_body", pos_to_patches(end_of_body)),
        ("classish_closing_brace", pos_to_patches(closing_brace)),
        (
            "classish_body_elements",
            body_elements.iter().flat_map(pos_to_patches).collect(),
        ),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect()
}

fn classish_positions_to_patches(cps: &classish_positions::T<Pos>) -> BTreeMap<String, Vec<Patch>> {
    cps.values().fold(BTreeMap::new(), |mut acc, cp| {
        // `S_map.merge merge_map_entry acc (...)`: `xs @ ys`
        for (k, ys) in classish_positions_for_class_to_patches(cp) {
            acc.entry(k).or_insert_with(Vec::new).extend(ys);
        }
        acc
    })
}

fn apply_patch_for(out: &mut impl Write, source_text: &[u8], positional_category: &str, patches: &[Patch]) {
    let _ = writeln!(out, "{}", positional_category);
    let _ = writeln!(out, "{}", "-".repeat(positional_category.len()));
    let _ = out.write_all(&apply_patches_to_string(source_text, patches.to_vec()));
    let _ = out.write_all(b"\n\n");
}

fn run_exn(
    _ctx: &provider_context::T,
    entry: &provider_context::Entry,
    path: &RelativePath,
) -> std::io::Result<()> {
    let (source_text, tree) = crate::ast_provider::compute_cst(entry);
    let classish_positions = classish_positions::extract(&tree, &source_text, &entry.path);
    let named_patches = classish_positions_to_patches(&classish_positions);
    let source_text = std::fs::read(crate::relative_path::to_absolute(path))?;
    let mut out = std::io::stdout().lock();
    for (k, v) in &named_patches {
        apply_patch_for(&mut out, &source_text, k, v)
    }
    Ok(())
}

/// - Dump classish positional information.
/// - Solely used for testing purposes in hh_single_type_check
pub fn dump(ctx: &provider_context::T, entry: &provider_context::Entry, path: &RelativePath) {
    match run_exn(ctx, entry, path) {
        // `Exn.to_string` of the `Sys_error` of `Sys_utils.cat`.
        Err(exn) => println!("(Sys_error \"{}: {}\")", crate::relative_path::to_absolute(path), exn),
        Ok(()) => {}
    }
}
