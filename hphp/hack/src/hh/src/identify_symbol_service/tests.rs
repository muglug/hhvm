// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The suite `hphp/hack/test/identify_symbol` (each `.exp` byte for byte),
//! with a context made as `hh single` makes it and the glue of its
//! `--identify-symbol` mode, until F0's mode and P0's `Tast_provider` land.
//! The TAST is `Typing_check_job.calc_errors_and_tast`'s (no top-level
//! statements), not `Tast_provider`'s.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use super::*;
use crate::hh_single_type_check as hstc;

/// The suite's directory, or `$F1_DIR` (a directory of the same layout).
fn test_dir() -> PathBuf {
    match std::env::var("F1_DIR") {
        Ok(dir) => PathBuf::from(dir),
        Err(_) => Path::new(env!("CARGO_MANIFEST_DIR")).join("../../test/identify_symbol"),
    }
}

/// `hh single --identify-symbol line col file`: the symbols at `line`, `col`
/// of `file`, as `Server_identify_function.go_quarantined_absolute` gives
/// them, printed as `hh single` prints them.
fn identify(file: &Path, line: isize, col: isize, config_overrides: Vec<String>) -> String {
    let flags = crate::hh_single_type_check_flags::Flags {
        config_overrides,
        ..Default::default()
    };
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
    let name = file.file_name().unwrap().to_string_lossy().into_owned();
    let mut ctx = crate::ctx::Ctx::new(&dir, tcopt).unwrap();
    ctx.add_magic_builtins();
    let contents = std::fs::read(file).unwrap();
    let mut decl_paths = ctx.hhi_paths.clone();
    let mut paths = vec![];
    let mut texts = vec![];
    for (part, text) in crate::multifile::file_to_file_list(&name, &contents) {
        let path = pos::RelativePath::new(pos::Prefix::Dummy, &part);
        texts.push(text.clone());
        ctx.files.set(path, text);
        paths.push(path);
    }
    decl_paths.extend(paths.iter().copied());
    let mut stats = crate::check::Stats::default();
    crate::check::declare_files(&ctx, &decl_paths, &mut stats);
    let ctx = Arc::new(ctx);
    hstc::install(&ctx);
    let to_ox = |paths: &[pos::RelativePath]| -> Vec<relative_path::T> {
        paths.iter().map(|&p| p.into()).collect()
    };
    let _ = hstc::parse_name_and_decl(&ctx, &to_ox(&decl_paths));
    let path: relative_path::T = paths[0].into();
    // (The entry's file is the test's: `hh single` reads it from the
    // current directory.)
    let part_contents = texts[0].clone();
    let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
        &ctx,
        path.clone(),
        bstr::BString::from(part_contents.to_vec()),
    );
    let full_ast = ast_provider::get_ast(true, &ctx, &path);
    let (_, by_names) = crate::typing_check_job::calc_errors_and_tast(&ctx, None, &path, full_ast);
    let mut tast: Vec<tast::Def> = vec![];
    for (_, t) in by_names.fun_tasts {
        tast.push(t.under_normal_assumptions)
    }
    for (_, t) in by_names.class_tasts {
        tast.push(t.under_normal_assumptions)
    }
    tast.extend(by_names.typedef_tasts.into_iter().map(|(_, d)| d));
    tast.extend(by_names.gconst_tasts.into_iter().map(|(_, d)| d));
    tast.extend(by_names.module_tasts.into_iter().map(|(_, d)| d));

    let (source_text, tree) = compute_cst(&entry);
    let positions = CstPositions {
        file_path: Arc::new(full_fidelity_source_text::file_path(&source_text).clone()),
        indexed: IndexedSourceText::new(full_fidelity_source_text::source_text(&source_text)),
    };
    let mut symbols = fixmes(&positions, &tree);
    symbols.extend(keywords(&positions, &tree));
    symbols.extend(all_symbols(&ctx, &tast));
    let cursor = file_content::position::from_one_based(line, col);
    let symbols: Vec<Elt> = symbols
        .into_iter()
        .filter(|x| is_target(false, &cursor, x))
        .collect();
    let symbols = crate::server_identify_function::best_symbols(symbols);
    let result: Vec<_> = symbols
        .into_iter()
        .map(|symbol| {
            let ast = ast_provider::compute_ast(provider_context::get_popt(&ctx), &entry);
            let def = crate::server_symbol_definition::go(&ctx, Some(&ast), &symbol);
            (
                symbol_occurrence::to_absolute(&symbol),
                def.as_ref().map(crate::symbol_definition::to_absolute),
            )
        })
        .collect();
    if result.is_empty() {
        "None\n".to_string()
    } else {
        crate::client_get_definition::print_readable_to_string(Some(true), &result)
    }
}

#[test]
#[ignore = "runs the identify_symbol suite; run with --ignored"]
fn identify_symbol_suite() {
    let dir = test_dir();
    let mut names: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "php"))
        .collect();
    names.sort();
    let only = std::env::var("F1_ONLY").ok();
    let mut failures = vec![];
    for file in &names {
        let stem = file.file_stem().unwrap().to_string_lossy().into_owned();
        if only.as_ref().is_some_and(|o| *o != stem) {
            continue;
        }
        let flags = std::fs::read_to_string(file.with_extension("flags")).unwrap();
        let mut words = flags.split_whitespace();
        let line: isize = words.next().unwrap().parse().unwrap();
        let col: isize = words.next().unwrap().parse().unwrap();
        let mut configs = vec![];
        while let Some(w) = words.next() {
            if w == "--config" {
                configs.push(words.next().unwrap().to_string())
            }
        }
        let exp = std::fs::read_to_string(file.with_extension("php.exp")).unwrap();
        let got = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            identify(file, line, col, configs)
        })) {
            Ok(got) => got,
            Err(e) => {
                let msg = e
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "<panic>".to_string());
                format!("PANIC: {}\n", msg)
            }
        };
        let want = exp;
        // `verify.py`'s comparison (`strip_lines`).
        // (The trailing blank lines of the `.exp` files differ; the OCaml
        // prints what this prints.)
        let strip_lines = |t: &str| t.trim_end().lines().map(|l| l.trim()).collect::<Vec<_>>().join("\n");
        if strip_lines(&got) != strip_lines(&want) {
            failures.push(format!("== {}\n-- want\n{}-- got\n{}", stem, want, got));
        }
    }
    let report = failures.join("");
    std::fs::write("/tmp/hh-port/f1_identify_report.txt", &report).unwrap();
    assert!(
        failures.is_empty(),
        "{} of {} failed (see /tmp/hh-port/f1_identify_report.txt)",
        failures.len(),
        names.len()
    );
}
