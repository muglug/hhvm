// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The requests of `test_serverless_ide_type_definition`
//! (`hphp/hack/test/integration/test_lsp.py`) on its file
//! (`data/lsp_exchanges/type_definition.php`), through [`go_quarantined`],
//! with a context made as `hh single` makes it.

use std::path::Path;
use std::sync::Arc;

use super::*;
use crate::hh_single_type_check as hstc;

/// `go_quarantined` at the zero-based LSP position `line`, `character`:
/// each result as (zero-based start line, start character, end character,
/// title), as the LSP prints them.
fn type_definition(line: isize, character: isize) -> Vec<(isize, isize, isize, String)> {
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../test/integration/data/lsp_exchanges/type_definition.php");
    let flags = crate::hh_single_type_check_flags::Flags::default();
    let hstc::Options {
        mut tcopt,
        packages_config_path,
        enable_implicit_packages,
    } = hstc::make_tcopt(&flags).unwrap();
    let root = hstc::root(packages_config_path.as_deref()).unwrap();
    hstc::set_path_prefixes(&root);
    let (_errors, package_info) =
        hstc::load_package_info(packages_config_path.as_deref(), enable_implicit_packages);
    tcopt.po.package_info = package_info;
    let dir = file.parent().unwrap().to_path_buf();
    let ctx = crate::ctx::Ctx::new(&dir, tcopt).unwrap();
    let contents = std::fs::read(&file).unwrap();
    let path = pos::RelativePath::new(pos::Prefix::Dummy, "type_definition.php");
    ctx.files.set(path, contents.clone());
    let mut decl_paths = ctx.hhi_paths.clone();
    decl_paths.push(path);
    let mut stats = crate::check::Stats::default();
    crate::check::declare_files(&ctx, &decl_paths, &mut stats);
    // (The daemon's reverse naming table, which `Naming_global.GEnv` reads.)
    ctx.build_reverse_naming_table();
    let ctx = Arc::new(ctx);
    hstc::install(&ctx);
    let ox: Vec<crate::relative_path::T> = decl_paths.iter().map(|&p| p.into()).collect();
    let _ = hstc::parse_name_and_decl(&ctx, &ox);
    let (ctx, entry) =
        provider_context::add_or_overwrite_entry_contents(&ctx, path.into(), bstr::BString::from(contents));
    let pos = file_content::position::from_one_based(line + 1, character + 1);
    let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
        go_quarantined(&ctx, &entry, &pos)
    });
    result
        .into_iter()
        .map(|(p, title)| {
            let (l, c) = crate::pos::line_column_absolute(&p);
            let (_, ec) = crate::pos::end_line_column_absolute(&p);
            (l - 1, c, ec, title)
        })
        .collect()
}

#[test]
fn serverless_ide_type_definition() {
    // Conditional Type Definition of HH or II
    assert_eq!(
        type_definition(32, 2),
        vec![(2, 6, 8, "\\HH".to_string()), (12, 6, 8, "\\LL".to_string())]
    );
    // Standard Class Definition
    assert_eq!(type_definition(40, 2), vec![(2, 6, 8, "\\HH".to_string())]);
    // Class Type Definition with Casting
    assert_eq!(type_definition(41, 2), vec![(2, 6, 8, "\\HH".to_string())]);
    // Primitive Type Definition
    assert_eq!(type_definition(42, 2), vec![]);
    // Function Return Type Definition
    assert_eq!(type_definition(43, 2), vec![(12, 6, 8, "\\LL".to_string())]);
    // Function definition with primitive return type
    assert_eq!(
        type_definition(44, 2),
        vec![(22, 9, 29, "(function(): int)".to_string())]
    );
}
