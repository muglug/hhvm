// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `search/symbol_index.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).
//!
//! `sienv_ref: si_env ref` is `&mut SiEnv`.

use oxidized::global_options::GlobalOptions;

use crate::custom_search_service;
use crate::file_info::SiKind;
use crate::hh_logger;
use crate::local_search_service;
use crate::relative_path::RelativePath;
use crate::search_types::AutocompleteType;
use crate::search_types::SiComplete;
use crate::search_types::SiFile;
use crate::search_types::SiItem;
use crate::search_types::find_refs::Action;
use crate::search_utils;
use crate::search_utils::MockOnFind;
use crate::search_utils::SearchProvider;
use crate::search_utils::SiEnv;
use crate::string_utils;
use crate::utils;

/// Get or set the currently selected search provider
pub fn initialize(
    gleanopt: &GlobalOptions,
    namespace_map: &[(String, String)],
    provider_name: &str,
    quiet: bool,
) -> SiEnv {
    // Create the object
    let sienv = SiEnv {
        sie_provider: search_utils::provider_of_string(provider_name),
        sie_quiet_mode: quiet,
        sie_namespace_map: namespace_map.to_vec(),
        // `Glean_options.reponame gleanopt`
        glean_reponame: gleanopt.glean_reponame.clone(),
        ..search_utils::default_si_env()
    };
    // Basic initialization
    let sienv = match sienv.sie_provider {
        SearchProvider::CustomIndex => custom_search_service::initialize(sienv),
        SearchProvider::NoIndex | SearchProvider::MockIndex { .. } | SearchProvider::LocalIndex => {
            sienv
        }
    };

    // Here's the initialized environment
    if !sienv.sie_quiet_mode {
        hh_logger::log(&format!(
            "Search provider set to [{}] based on configuration value [{}]",
            search_utils::descriptive_name_of_provider(&sienv.sie_provider),
            provider_name
        ));
    }
    sienv
}

/// Constructs+returns a mockable symbol-index
pub fn mock(on_find: MockOnFind) -> SiEnv {
    SiEnv {
        sie_provider: SearchProvider::MockIndex {
            mock_on_find: on_find,
        },
        sie_quiet_mode: true,
        ..search_utils::default_si_env()
    }
}

/// Core search function
/// - Uses both global and local indexes
/// - Can search for specific kinds or all kinds
/// - Goal is to route ALL searches through one function for consistency
///
/// This is the proper search function everyone should use.
/// The caller is expected to have done any namespace aliasing already,
/// e.g. if .hhconfig has auto_namespace_map={"Vec":"FlibSL\\Vec"}
/// then this function will give answers for query_text="FLibSL\Vec\ch" but not "Vec\ch".
pub fn find_matching_symbols(
    sienv_ref: &mut SiEnv,
    query_text: &str,
    max_results: isize,
    context: AutocompleteType,
    kind_filter: Option<SiKind>,
) -> (Vec<SiItem>, SiComplete) {
    let mut is_complete = SiComplete::Complete;
    // Nuclide often sends this exact request to verify that HH is working.
    // Let's capture it and avoid doing unnecessary work.
    if query_text == "this_is_just_to_check_liveness_of_hh_server" {
        (
            vec![SiItem {
                name: "Yes_hh_server_is_alive".to_string(),
                kind: SiKind::SIUnknown,
                file: SiFile::SIFilehash("0".to_string()),
                fullname: String::new(),
            }],
            is_complete,
        )
    } else {
        // Namespace aliases. For instance, if File is an alias for \FlibSL\File,
        // then "Fi|" will definitely show File.
        let namespace_results: Vec<SiItem> = match context {
            AutocompleteType::AcWorkspaceSymbol => vec![],
            AutocompleteType::Acid
            | AutocompleteType::Acnew
            | AutocompleteType::Acclassish
            | AutocompleteType::Actype
            | AutocompleteType::ActraitOnly => sienv_ref
                .sie_namespace_map
                .iter()
                .filter_map(|(alias, map)| {
                    if alias.starts_with(query_text) {
                        Some(SiItem {
                            name: alias.clone(),
                            kind: SiKind::SINamespace,
                            file: SiFile::SIFilehash("0".to_string()),
                            fullname: map.clone(),
                        })
                    } else {
                        None
                    }
                })
                .collect(),
        };
        // The local index captures symbols in files that have been changed on disk.
        // Search it first for matches, then search global and add any elements
        // that we haven't seen before
        let local_results = match sienv_ref.sie_provider {
            SearchProvider::NoIndex | SearchProvider::MockIndex { .. } => vec![],
            SearchProvider::CustomIndex | SearchProvider::LocalIndex => {
                local_search_service::search_local_symbols(
                    sienv_ref,
                    query_text,
                    max_results,
                    context,
                    kind_filter,
                )
            }
        };
        // Next search globals
        let global_results = match sienv_ref.sie_provider.clone() {
            SearchProvider::CustomIndex => {
                let (r, custom_is_complete) = custom_search_service::search_symbols(
                    sienv_ref,
                    query_text,
                    max_results,
                    context,
                    kind_filter,
                );
                is_complete = custom_is_complete;
                local_search_service::extract_dead_results(sienv_ref, r)
            }
            SearchProvider::MockIndex { mock_on_find } => {
                mock_on_find(query_text, context, kind_filter)
            }
            SearchProvider::LocalIndex | SearchProvider::NoIndex => vec![],
        };
        // Merge and deduplicate results
        let mut all_results = local_results;
        all_results.extend(global_results);
        let mut dedup_results = all_results;
        // `List.sort ~compare:(fun a b -> String.compare b.si_name a.si_name)`:
        // a stable merge sort, by byte order, descending.
        dedup_results.sort_by(|a, b| b.name.as_bytes().cmp(a.name.as_bytes()));
        // Strip namespace already typed from the results
        let (ns, _) = utils::split_ns_from_name(query_text);
        let results: Vec<SiItem> = if ns.is_empty() || ns == "\\" {
            dedup_results
        } else {
            dedup_results
                .into_iter()
                .map(|s| SiItem {
                    name: string_utils::lstrip(&s.name, ns).to_string(),
                    ..s
                })
                .collect()
        };
        // Namespaces should always appear first
        let mut all = namespace_results;
        all.extend(results);
        // `List.take results max_results`
        all.truncate(max_results.max(0) as usize);
        (all, is_complete)
    }
}

/// Does an approximate search for find-all-refs candidates.
/// If it returns None, then this functionality isn't available from this provider,
/// or isn't working for some reason.
/// If it returns Some, then these are best-guess candidates to check.
pub fn find_refs(
    sienv_ref: &mut SiEnv,
    action: &Action,
    max_results: isize,
) -> Option<Vec<RelativePath>> {
    match sienv_ref.sie_provider {
        SearchProvider::NoIndex | SearchProvider::LocalIndex | SearchProvider::MockIndex { .. } => {
            None
        }
        SearchProvider::CustomIndex => {
            custom_search_service::find_refs(sienv_ref, action, max_results)
        }
    }
}

#[cfg(test)]
mod tests {
    use relative_path::Prefix;

    use super::*;
    use crate::file_info::SiAddendum;
    use crate::search_utils::FileSource;
    use crate::symbol_index_core;

    fn add(name: &str, kind: SiKind, is_abstract: bool) -> SiAddendum {
        SiAddendum {
            name: name.to_string(),
            kind,
            is_abstract,
            is_final: false,
        }
    }

    fn rp(s: &str) -> RelativePath {
        RelativePath::make(Prefix::Root, s.into())
    }

    fn env(files: Vec<(&str, Vec<SiAddendum>)>) -> SiEnv {
        let sienv = initialize(
            &Default::default(),
            &[("Vec".to_string(), "HH\\Lib\\Vec".to_string())],
            "LocalIndex",
            true,
        );
        let paths_with_addenda: Vec<_> = files
            .into_iter()
            .map(|(p, a)| (rp(p), a, FileSource::TypeChecker))
            .collect();
        symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda)
    }

    fn names(r: &(Vec<SiItem>, SiComplete)) -> Vec<&str> {
        r.0.iter().map(|i| i.name.as_str()).collect()
    }

    #[test]
    fn liveness() {
        let mut sienv = env(vec![]);
        let r = find_matching_symbols(
            &mut sienv,
            "this_is_just_to_check_liveness_of_hh_server",
            10,
            AutocompleteType::AcWorkspaceSymbol,
            None,
        );
        assert_eq!(names(&r), vec!["Yes_hh_server_is_alive"]);
    }

    #[test]
    fn sorted_descending_case_insensitive_prefix() {
        let mut sienv = env(vec![
            ("a.php", vec![add("FooA", SiKind::SIClass, false), add("fooB", SiKind::SIFunction, false)]),
            ("b.php", vec![add("Bar", SiKind::SIClass, false), add("FOOC", SiKind::SITrait, false)]),
        ]);
        let r = find_matching_symbols(&mut sienv, "foo", 10, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["fooB", "FooA", "FOOC"]);
        let r = find_matching_symbols(
            &mut sienv,
            "foo",
            10,
            AutocompleteType::AcWorkspaceSymbol,
            Some(SiKind::SIClass),
        );
        assert_eq!(names(&r), vec!["FooA"]);
        // `Acid` excludes nothing here, and namespace aliases come first.
        let r = find_matching_symbols(&mut sienv, "", 3, AutocompleteType::Acid, None);
        assert_eq!(names(&r), vec!["Vec", "fooB", "FooA"]);
        assert_eq!(r.0[0].fullname, "HH\\Lib\\Vec");
        // `Actrait_only`
        let r = find_matching_symbols(&mut sienv, "f", 10, AutocompleteType::ActraitOnly, None);
        assert_eq!(names(&r), vec!["FOOC"]);
    }

    #[test]
    fn break_out_of_scan_keeps_only_the_file_that_filled_up() {
        let mut sienv = env(vec![
            ("a.php", vec![add("Xa", SiKind::SIClass, false)]),
            (
                "b.php",
                vec![
                    add("X1", SiKind::SIClass, false),
                    add("X2", SiKind::SIClass, false),
                    add("X3", SiKind::SIClass, false),
                ],
            ),
            ("c.php", vec![add("Xc", SiKind::SIClass, false)]),
        ]);
        let r = find_matching_symbols(&mut sienv, "x", 2, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["X2", "X1"]);
        let r = find_matching_symbols(&mut sienv, "x", 4, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["Xc", "Xa", "X3", "X2"]);
    }

    #[test]
    fn namespace_already_typed_is_stripped() {
        let mut sienv = env(vec![(
            "a.php",
            vec![add("NS\\Sub\\Foo", SiKind::SIClass, false), add("NS\\Other", SiKind::SIClass, false)],
        )]);
        let r = find_matching_symbols(&mut sienv, "ns\\sub\\f", 10, AutocompleteType::AcWorkspaceSymbol, None);
        // `lstrip` is case-sensitive: the typed namespace is "ns\\sub\\".
        assert_eq!(names(&r), vec!["NS\\Sub\\Foo"]);
        let r = find_matching_symbols(&mut sienv, "NS\\", 10, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["Sub\\Foo", "Other"]);
        assert_eq!(r.0[0].fullname, "NS\\Sub\\Foo");
    }

    #[test]
    fn acnew_skips_abstract_and_remove_files() {
        let sienv = env(vec![
            ("a.php", vec![add("Abs", SiKind::SIClass, true), add("Conc", SiKind::SIClass, false)]),
            ("b.php", vec![add("Other", SiKind::SIClass, false)]),
        ]);
        let mut s = sienv.clone();
        let r = find_matching_symbols(&mut s, "", 10, AutocompleteType::Acnew, None);
        assert_eq!(names(&r), vec!["Vec", "Other", "Conc"]);
        let removed = symbol_index_core::remove_files(&sienv, &[rp("a.php")].into_iter().collect());
        let mut s = removed.clone();
        let r = find_matching_symbols(&mut s, "", 10, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["Other"]);
        assert!(removed.lss_tombstones.contains(&rp("a.php")));
        let dead = crate::local_search_service::extract_dead_results(
            &removed,
            vec![
                SiItem {
                    name: "Abs".into(),
                    kind: SiKind::SIClass,
                    file: SiFile::SIPath(rp("a.php")),
                    fullname: "Abs".into(),
                },
                SiItem {
                    name: "Other".into(),
                    kind: SiKind::SIClass,
                    // (Every file updated or removed has its tombstone, b.php
                    // too: a hash of a file never seen.)
                    file: SiFile::SIFilehash(
                        crate::local_search_service::get_tombstone(&rp("c.php")).to_string(),
                    ),
                    fullname: "Other".into(),
                },
                SiItem {
                    name: "Gone".into(),
                    kind: SiKind::SIClass,
                    file: SiFile::SIFilehash(
                        crate::local_search_service::get_tombstone(&rp("a.php")).to_string(),
                    ),
                    fullname: "Gone".into(),
                },
            ],
        );
        assert_eq!(dead.iter().map(|i| i.name.as_str()).collect::<Vec<_>>(), vec!["Other"]);
        // The original environment is unchanged (persistent value).
        assert_eq!(crate::local_search_service::count_local_fileinfos(&sienv), 2);
    }

    #[test]
    fn providers() {
        let no = initialize(&Default::default(), &[], "NoIndex", true);
        let no = symbol_index_core::update_from_addenda(
            &no,
            &[(rp("a.php"), vec![add("Foo", SiKind::SIClass, false)], FileSource::TypeChecker)],
        );
        let mut no2 = no.clone();
        assert!(find_matching_symbols(&mut no2, "f", 10, AutocompleteType::AcWorkspaceSymbol, None).0.is_empty());
        let mut mock_env = mock(std::sync::Arc::new(|q: &str, _c, _k| {
            vec![SiItem {
                name: format!("{q}Mock"),
                kind: SiKind::SIClass,
                file: SiFile::SIFilehash("0".into()),
                fullname: String::new(),
            }]
        }));
        let r = find_matching_symbols(&mut mock_env, "Z", 10, AutocompleteType::AcWorkspaceSymbol, None);
        assert_eq!(names(&r), vec!["ZMock"]);
        let mut custom = initialize(&Default::default(), &[], "CustomIndex", true);
        let r = find_matching_symbols(&mut custom, "Z", 10, AutocompleteType::AcWorkspaceSymbol, None);
        assert!(r.0.is_empty() && r.1 == SiComplete::Complete);
        assert_eq!(
            find_refs(&mut custom, &crate::search_types::find_refs::Action::Function("f".into()), 10),
            None
        );
        // Updates from `Init` are ignored.
        let init_only = symbol_index_core::update_from_addenda(
            &custom,
            &[(rp("a.php"), vec![add("Foo", SiKind::SIClass, false)], FileSource::Init)],
        );
        assert_eq!(crate::local_search_service::count_local_fileinfos(&init_only), 0);
        assert!(std::panic::catch_unwind(|| initialize(&Default::default(), &[], "Bogus", true)).is_err());
    }
}
