// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/diff_naming_table.ml` (the diff of two saved states'
//! naming tables and errors, for `hh_saved_state_verifier`). See
//! `hh/PORTING.md`.

use crate::file_info;
use crate::hh_logger;
use crate::naming_table;
use crate::relative_path;
use crate::save_state_service;
use crate::save_state_service_types::OldIssues;

/// `get_default_provider_context ()`: the `Local_memory` backend with its
/// test defaults, roots `root` and `hhi`.
pub fn get_default_provider_context() -> crate::provider_context::T {
    relative_path::set_path_prefix(relative_path::Prefix::Root, std::path::Path::new("root"));
    relative_path::set_path_prefix(relative_path::Prefix::Hhi, std::path::Path::new("hhi"));
    let tco = oxidized::global_options::GlobalOptions::default();
    match crate::ctx::Ctx::new_local_memory_with_defaults_for_test(std::path::Path::new("root"), tco) {
        Ok(ctx) => std::sync::Arc::new(ctx),
        Err(e) => panic!("{:#}", e),
    }
}

/// `get_naming_table_and_errors provider_context path`
pub fn get_naming_table_and_errors(
    provider_context: &crate::provider_context::T,
    path: &str,
) -> Result<(naming_table::T, OldIssues), save_state_service::LoadError> {
    let sqlite_path = Some(path);
    // `Str.replace_first (Str.regexp "_naming.sql") ".err" path` (the `.`
    // of the regexp matches any character)
    let replace_first = |with: &str| -> String {
        let bytes = path.as_bytes();
        let pat = b"_naming";
        for i in 0..bytes.len() {
            if bytes[i..].starts_with(pat) && bytes.len() >= i + pat.len() + 4 && &bytes[i + pat.len() + 1..i + pat.len() + 4] == b"sql" {
                return format!("{}{}{}", &path[..i], with, &path[i + pat.len() + 4..]);
            }
        }
        path.to_string()
    };
    let errors_path = replace_first(".err");
    let warning_hashes_path = replace_first(".warn");
    save_state_service::load_saved_state_exn(sqlite_path, &errors_path, &warning_hashes_path, provider_context)
}

/// `diff`
#[derive(Clone, Debug, Default)]
pub struct Diff {
    pub added_files: Vec<relative_path::T>,
    pub removed_files: Vec<relative_path::T>,
    pub changed_files: Vec<(relative_path::T, file_info::Diff)>,
    pub removed_errors: Vec<relative_path::T>,
    pub added_errors: Vec<relative_path::T>,
}

/// `empty_diff`
pub fn empty_diff() -> Diff {
    Diff::default()
}

/// `is_nonempty diff`
pub fn is_nonempty(d: &Diff) -> bool {
    !(d.added_files.is_empty()
        && d.removed_files.is_empty()
        && d.changed_files.is_empty()
        && d.removed_errors.is_empty()
        && d.added_errors.is_empty())
}

/// `calculate_diff naming_table1 naming_table2 errors1 errors2` (the lists
/// are built by consing in fold order, as the OCaml's)
pub fn calculate_diff(
    naming_table1: &naming_table::T,
    naming_table2: &naming_table::T,
    errors1: &relative_path::set::T,
    errors2: &relative_path::set::T,
) -> Diff {
    let diff = naming_table::fold(None, naming_table1, empty_diff(), |path, fileinfo1, mut acc| {
        match naming_table::get_file_info(naming_table2, path) {
            None => acc.removed_files.insert(0, path.clone()),
            Some(fileinfo2) => {
                if let Some(file_diff) = file_info::diff(fileinfo1, &fileinfo2) {
                    acc.changed_files.insert(0, (path.clone(), file_diff))
                }
            }
        }
        acc
    });
    let diff = naming_table::fold(None, naming_table2, diff, |path, _, mut acc| {
        if naming_table::get_file_info(naming_table1, path).is_none() {
            acc.added_files.insert(0, path.clone())
        }
        acc
    });
    let removed_errors = errors1.clone().relative_complement(errors2.clone()).into_iter().collect();
    let added_errors = errors2.clone().relative_complement(errors1.clone()).into_iter().collect();
    Diff {
        removed_errors,
        added_errors,
        ..diff
    }
}

/// `file_info_diff_to_string path d`
pub fn file_info_diff_to_string(path: &relative_path::T, d: &file_info::Diff) -> String {
    let set_to_string = |sset: &std::collections::BTreeSet<String>| sset.iter().cloned().collect::<Vec<_>>().join(", ");
    let mut t: Vec<String> = vec![];
    for (description, s) in [
        ("Removed consts:", &d.removed_consts),
        ("Added consts:", &d.added_consts),
        ("Removed types:", &d.removed_types),
        ("Added types:", &d.added_types),
        ("Removed classes:", &d.removed_classes),
        ("Added classes:", &d.added_classes),
        ("Removed functions:", &d.removed_funs),
        ("Added functions", &d.added_funs),
    ] {
        // `helper acc (description, s)`: `description :: set_to_string s :: acc`
        if !s.is_empty() {
            t.insert(0, set_to_string(s));
            t.insert(0, description.to_string());
        }
    }
    let mut all = vec![relative_path::storage_to_string(path)];
    all.extend(t);
    all.join("\n")
}

/// `print_diff print_count diff`
pub fn print_diff(print_count: bool, diff: &Diff) {
    hh_logger::log("Diffing the naming tables...");
    let no_difference = diff.added_files.is_empty() && diff.removed_files.is_empty() && diff.changed_files.is_empty();
    if no_difference {
        hh_logger::log("The naming tables are identical!")
    } else if print_count {
        let print_category = |description: &str, len: usize| {
            if len > 0 {
                hh_logger::log(&format!("{}: {}", description, len))
            }
        };
        print_category("Added files", diff.added_files.len());
        print_category("Removed files", diff.removed_files.len());
        print_category("Changed files", diff.changed_files.len());
        print_category("Added errors", diff.added_errors.len());
        print_category("Removed errors", diff.removed_errors.len());
    } else {
        let concat_paths = |paths: &[relative_path::T]| {
            paths.iter().map(relative_path::storage_to_string).collect::<Vec<_>>().join("\n")
        };
        let print_category = |description: &str, change: &[relative_path::T]| {
            if !change.is_empty() {
                hh_logger::log(&format!("{}:\n{}", description, concat_paths(change)))
            }
        };
        print_category("Added files", &diff.added_files);
        print_category("Removed files", &diff.removed_files);
        if !diff.changed_files.is_empty() {
            hh_logger::log("Changed files");
            for (path, d) in &diff.changed_files {
                hh_logger::log(&file_info_diff_to_string(path, d))
            }
        }
        print_category("Added errors", &diff.added_errors);
        print_category("Removed errors", &diff.removed_errors);
    }
}

/// Prints the diff of test and control (naming table, error) pairs, and
/// returns whether test and control differ. (`diff control_path
/// test_path`)
pub fn diff(control_path: &str, test_path: &str) -> Result<bool, save_state_service::LoadError> {
    let provider_context = get_default_provider_context();
    let (control_naming_table, OldIssues {
        old_errors: control_errors,
        ..
    }) = get_naming_table_and_errors(&provider_context, control_path)?;
    let (test_naming_table, OldIssues {
        old_errors: test_errors,
        ..
    }) = get_naming_table_and_errors(&provider_context, test_path)?;
    let diff = calculate_diff(&control_naming_table, &test_naming_table, &control_errors, &test_errors);
    print_diff(false, &diff);
    Ok(is_nonempty(&diff))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diffs_two_states() {
        let dir = std::env::temp_dir().join(format!("diff_naming_table_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let ctx = get_default_provider_context();
        let info = |classes: &[&str]| file_info::T {
            ids: file_info::Ids {
                classes: classes
                    .iter()
                    .map(|c| file_info::Id {
                        pos: file_info::Pos::File(file_info::NameType::Class, std::sync::Arc::new(relative_path::from_root("x.php"))),
                        name: c.to_string(),
                        decl_hash: Some(1),
                    })
                    .collect(),
                ..file_info::empty_ids()
            },
            position_free_decl_hash: file_info::HashType(Some(classes.len() as i64)),
            file_mode: Some(file_info::Mode::Mstrict),
            comments: None,
        };
        let save = |name: &str, files: &[(&str, &[&str])]| {
            let nt = naming_table::create(
                files.iter().map(|(p, cs)| (relative_path::from_root(p), info(cs))).collect(),
            );
            let p = dir.join(format!("{}_naming.sql", name)).display().to_string();
            let _ = std::fs::remove_file(&p);
            naming_table::save(&nt, &p).unwrap();
            save_state_service::save_contents(
                &dir.join(format!("{}.err", name)).display().to_string(),
                &save_state_service::saved_state_errors_to_ocaml(&Default::default()),
            )
            .unwrap();
            save_state_service::save_contents(
                &dir.join(format!("{}.warn", name)).display().to_string(),
                &save_state_service::warnings_saved_state_to_ocaml(&Default::default()),
            )
            .unwrap();
            p
        };
        let a = save("a", &[("x.php", &["\\X"]), ("y.php", &["\\Y"]), ("w.php", &["\\W"])]);
        let b = save("b", &[("x.php", &["\\X", "\\X2"]), ("z.php", &["\\Z"]), ("w.php", &["\\W"])]);
        let ctx_ = &ctx;
        let (nt_a, ia) = get_naming_table_and_errors(ctx_, &a).unwrap();
        let (nt_b, ib) = get_naming_table_and_errors(ctx_, &b).unwrap();
        let d = calculate_diff(&nt_a, &nt_b, &ia.old_errors, &ib.old_errors);
        assert_eq!(d.added_files, vec![relative_path::from_root("z.php")]);
        assert_eq!(d.removed_files, vec![relative_path::from_root("y.php")]);
        // (`File_info.diff` is `None` when the names differ: its `is_empty`
        // is true when some set is NOT empty, in the OCaml too. So only a
        // file whose hash changed with the same names is "changed", with
        // an empty diff.)
        assert_eq!(d.changed_files.len(), 0);
        assert!(is_nonempty(&d));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
