// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the error mode of `hh_single_type_check.ml` (`Errors`): parse,
//! name and declare the files and the builtins (`parse_name_and_decl`), then
//! typecheck each file (`check_file`) and print the sorted diagnostics
//! (`print_error_list`). See `hh/PORTING.md`.
//!
//! The command line is parsed by `main.rs` into [`Flags`]; [`make_tcopt`]
//! makes the options of them as `parse_options` does. The other modes of
//! the OCaml (`--hover`, `--identify-symbol`, ...) are not here yet.

use std::sync::Arc;

use ::file_provider::FileProvider as _;
use oxidized::global_options::GlobalOptions;
use oxidized::parser_options::ParserOptions;

use crate::config_file_common;
use crate::ctx::Ctx;
use crate::diagnostics_state;
use crate::relative_path;
use crate::relative_path::Prefix;

/// The root of `parse_options` (there is no `--root` here): the current
/// directory when `--config packages_config_path` is given (the path is
/// relative to it), else the dummy `/`.
pub fn root(packages_config_path: Option<&str>) -> std::io::Result<std::path::PathBuf> {
    match packages_config_path {
        Some(_) => std::env::current_dir(),
        None => Ok(std::path::PathBuf::from("/")),
    }
}

/// `Relative_path.set_path_prefix` as `main_hack` does it: the root is
/// [`root`], the hhi files are under `/hhi` (where `Ctx` keeps them, in
/// memory), and `Tmp` is `tmp`. The test files themselves are `Dummy`
/// paths, whose prefix is always empty.
pub fn set_path_prefixes(root: &std::path::Path) {
    relative_path::set_path_prefix(Prefix::Root, root);
    relative_path::set_path_prefix(Prefix::Hhi, std::path::Path::new("/hhi"));
    relative_path::set_path_prefix(Prefix::Tmp, std::path::Path::new("tmp"));
}

// ~~ The options (`parse_options`) ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub use crate::hh_single_type_check_flags::Flags;

/// What [`make_tcopt`] gives: the options, and what the rest of the
/// program reads from the `--config` keys.
#[derive(Clone, Debug)]
pub struct Options {
    pub tcopt: GlobalOptions,
    /// `packages_config_path` of `--config`
    pub packages_config_path: Option<String>,
    /// `enable_implicit_packages` of `--config`
    pub enable_implicit_packages: bool,
}

/// The `--config` overrides, folded in their order (`parse_options`): a
/// later one wins.
pub fn config_of_overrides(config_overrides: &[String]) -> config_file_common::T {
    config_overrides
        .iter()
        .fold(config_file_common::empty(), |config, setting| {
            let c = config_file_common::parse_contents(setting.as_bytes());
            config_file_common::apply_overrides(&config, &c, None)
        })
}

/// `exit_if_invalid_config_keys`, without the exit: the message of the
/// first key of `config` (in increasing order) that is not a config key.
pub fn invalid_config_key_message(config: &config_file_common::T) -> Option<String> {
    config_file_common::keys(config).into_iter().find_map(|key| {
        match crate::config_keys::validate(&key) {
            Ok(()) => None,
            Err(crate::config_keys::DidYouMean(suggestion)) => Some(match suggestion {
                None => format!("Unknown config option: {}\n", key),
                Some(s) => format!("Unknown config option: {}. Did you mean {}?\n", key, s),
            }),
        }
    })
}

/// `exit_if_invalid_config_keys`: prints the message on stderr and exits
/// with `Input_error`.
fn exit_if_invalid_config_keys(config: &config_file_common::T) {
    if let Some(msg) = invalid_config_key_message(config) {
        use std::io::Write;
        eprint!("{}", msg);
        let _ = std::io::stderr().flush();
        std::process::exit(crate::exit_status::exit_code(&crate::exit_status::T::InputError) as i32)
    }
}

/// `load_and_parse_custom_error_config path`
fn load_and_parse_custom_error_config(path: &str) -> Option<crate::custom_error_config::T> {
    match crate::custom_error_config::initialize(crate::custom_error_config::Path::Absolute(
        path.to_string(),
    )) {
        Ok(cfg) => {
            if !cfg.invalid.is_empty() {
                eprint!(
                    "Encountered invalid rules with loading custom error config: \n {}\n",
                    cfg.invalid
                        .iter()
                        .map(|rule| rule.name.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
            Some(cfg)
        }
        Err(msg) => {
            eprint!(
                "Encountered and error when loading custom error config: \n {}\n",
                msg
            );
            None
        }
    }
}

/// The options of `parse_options`: the parser options and typechecker
/// options that the flags set (on `Global_options.default`), then
/// `Server_config.load_config` of the `--config` keys (so a key wins over a
/// flag), then the experimental features of the flags and the custom error
/// config. An unknown `--config` key exits (`exit_if_invalid_config_keys`);
/// the `Err` is the `Yojson.Json_error` of a value that is not JSON (which
/// the OCaml lets through).
pub fn make_tcopt(flags: &Flags) -> Result<Options, crate::yojson::JsonError> {
    let config = config_of_overrides(&flags.config_overrides);
    exit_if_invalid_config_keys(&config);
    // (`rust_provider_backend` is read here too: it chooses the provider
    // backend and the shared memory, not the options.)
    let packages_config_path =
        crate::config_file::getters::string_opt(crate::config_keys::hhconfig::packages_config_path, &config);
    let enable_implicit_packages = crate::config_file::getters::bool_(
        crate::config_keys::hhconfig::enable_implicit_packages,
        false,
        &config,
    );
    let default = GlobalOptions::default();
    let po = ParserOptions {
        // These are set specifically for single type check
        use_legacy_experimental_feature_config: false,
        allow_unstable_features: true,
        // The remainder are set by the command line options
        disable_xhp_element_mangling: flags.disable_xhp_element_mangling,
        enable_xhp_class_modifier: flags.enable_xhp_class_modifier,
        interpret_soft_types_as_like_types: flags.interpret_soft_types_as_like_types,
        keep_user_attributes: flags.keep_user_attributes,
        auto_namespace_map: flags
            .auto_namespace_map
            .clone()
            .unwrap_or_else(|| default.po.auto_namespace_map.clone()),
        deregister_php_stdlib: flags
            .deregister_attributes
            .unwrap_or(default.po.deregister_php_stdlib),
        everything_sdt: true,
        allowed_decl_fixme_codes: flags.allowed_decl_fixme_codes.clone().unwrap_or_default(),
        disallow_non_annotated_memoize: flags.disallow_non_annotated_memoize,
        treat_non_annotated_memoize_as_kbic: flags.treat_non_annotated_memoize_as_kbic,
        // These don't have command-line flags: their defaults.
        ..default.po.clone()
    };
    // `Global_options.set ~po ... Global_options.default` (on the default,
    // `set` changes nothing besides the fields given).
    let tcopt = GlobalOptions {
        po,
        tco_saved_state: default.tco_saved_state.clone(),
        tco_log_inference_constraints: flags
            .log_inference_constraints
            .unwrap_or(default.tco_log_inference_constraints),
        tco_timeout: flags.timeout.unwrap_or(default.tco_timeout),
        allowed_fixme_codes_strict: flags.allowed_fixme_codes_strict.clone().unwrap_or_default(),
        tco_skip_hierarchy_checks: flags.skip_hierarchy_checks,
        tco_skip_tast_checks: flags.skip_tast_checks,
        tco_strict_contexts: flags.strict_contexts,
        tco_like_casts: false,
        log_levels: flags.log_levels.clone(),
        glean_reponame: flags.glean_reponame.clone(),
        tco_skip_check_under_dynamic: flags.skip_check_under_dynamic,
        tco_global_access_check_enabled: flags.enable_global_access_check,
        tco_meth_caller_only_public_visibility: flags.meth_caller_only_public_visibility,
        tco_explicit_consistent_constructors: flags.explicit_consistent_constructors,
        tco_require_types_class_consts: flags.require_types_class_consts,
        tco_type_printer_fuel: flags.type_printer_fuel,
        tco_profile_top_level_definitions: flags.profile_top_level_definitions,
        tco_allow_all_files_for_module_declarations: flags.allow_all_files_for_module_declarations,
        tco_loop_iteration_upper_bound: flags.loop_iteration_upper_bound,
        ..default
    };
    let mut tcopt = crate::server_config::load_config(&config, &tcopt)?;
    // (`Diagnostics.allowed_fixme_codes_strict :=` is done by [`install`],
    // from the options of the context.)
    if flags.enable_supportdyn_hint {
        tcopt
            .tco_legacy_experimental_features
            .insert(crate::typechecker_options::experimental_supportdynamic_type_hint.to_string());
    }
    if flags.consider_type_const_enforceable {
        tcopt.tco_legacy_experimental_features.insert(
            crate::typechecker_options::experimental_consider_type_const_enforceable.to_string(),
        );
    }
    tcopt.tco_custom_error_config = flags
        .custom_error_config_path
        .as_deref()
        .and_then(load_and_parse_custom_error_config)
        .unwrap_or(crate::custom_error_config::empty);
    Ok(Options {
        tcopt,
        packages_config_path,
        enable_implicit_packages,
    })
}

/// The packages of `main_hack`: those of `packages_config_path` (relative
/// to the root), not strict, with the diagnostics recorded while they are
/// loaded (merged before those of parsing and naming).
pub fn load_package_info(
    packages_config_path: Option<&str>,
    enable_implicit_packages: bool,
) -> (diagnostics_state::T, crate::package_info::T) {
    diagnostics_state::do_(None, || match packages_config_path {
        None => crate::package_info::empty(),
        Some(pkgs_config_relpath) => crate::package_config::load_and_parse(
            false,
            enable_implicit_packages,
            &relative_path::to_absolute(&relative_path::from_root(pkgs_config_relpath)),
        ),
    })
}

/// Makes `ctx` the context of the process's providers: the decl store reads
/// from it (`Provider_backend.set_rust_backend`), and the fixme settings of
/// its options are the process-wide ones of `Diagnostics`.
pub fn install(ctx: &Arc<Ctx>) {
    crate::decl_store::set(crate::decl_store::rust_provider_backend_decl_store(
        Arc::clone(ctx),
    ));
    diagnostics_state::set_allowed_fixme_codes_strict(ctx.tco.allowed_fixme_codes_strict.clone());
    diagnostics_state::set_code_agnostic_fixme(ctx.tco.code_agnostic_fixme);
}

/// `parse_name_and_decl` (the parsing half: `parse_and_name`): parses each
/// file, which records its parse errors and its fixmes, and gives the AST to
/// the AST provider. The shallow declarations are already in the `Ctx`;
/// then the classes of each file are folded (`Decl.make_env`).
///
/// (`Naming_global.ndecl_file_and_get_conflict_files`, which reports names
/// defined twice, is not ported yet.)
pub fn parse_name_and_decl(ctx: &Arc<Ctx>, files: &[relative_path::T]) -> diagnostics_state::T {
    let (errors, ()) = diagnostics_state::do_(None, || {
        for fn_ in files {
            diagnostics_state::run_in_context(fn_.clone(), || {
                let popt = crate::provider_context::get_popt(ctx).clone();
                let contents = ctx
                    .files
                    .get(pos::RelativePath::from(fn_))
                    .unwrap_or_default();
                let parsed_file = crate::full_fidelity_ast::defensive_program(
                    None, None, None, None, popt, fn_, &contents,
                );
                crate::ast_provider::provide_ast_hint(
                    fn_,
                    parsed_file.ast,
                    crate::ast_provider::ParseType::Full,
                );
            })
        }
        // Relative_path.Map.iter files_info ~f:(fun fn _ ->
        //     Decl.make_env ~sh:Shared_mem.Uses ctx fn)
        let mut files_info: Vec<&relative_path::T> = files.iter().collect();
        files_info.sort_by(|p1, p2| relative_path::compare(p1, p2));
        files_info.dedup();
        for fn_ in files_info {
            crate::decl::make_env(ctx, fn_);
        }
    });
    errors
}

/// `check_file`: typechecks each file, and merges its diagnostics into
/// `errors`.
pub fn check_file(
    ctx: &Arc<Ctx>,
    errors: diagnostics_state::T,
    files: &[relative_path::T],
) -> diagnostics_state::T {
    let mut errors = errors;
    for fn_ in files {
        let full_ast = crate::ast_provider::get_ast(true, ctx, fn_);
        let (new_errors, _tast) =
            crate::typing_check_job::calc_errors_and_tast(ctx, None, fn_, full_ast);
        errors = diagnostics_state::merge(errors, new_errors);
    }
    errors
}

/// `print_error format ?oc l`: renders `l` in `format` on `oc`.
pub fn print_error(
    format: diagnostics_state::Format,
    oc: &mut dyn std::io::Write,
    l: &diagnostics_state::Diagnostic,
) {
    use diagnostics_state::Format;
    let formatter: fn(&crate::user_diagnostic::T<crate::pos::Absolute, crate::pos::Absolute>) -> String =
        match format {
            Format::Context => |e| crate::contextual_diagnostic_formatter::to_string(None, e),
            Format::Raw => crate::raw_diagnostic_formatter::to_string,
            Format::Agent => crate::agent_diagnostic_formatter::to_string,
            Format::Plain => crate::user_diagnostic::to_string,
            Format::Highlighted => crate::highlighted_diagnostic_formatter::to_string,
            Format::Extended => crate::extended_diagnostic_formatter::to_string,
            Format::PlainHighlighted => crate::plain_highlighted_diagnostic_formatter::to_string,
        };
    let absolute_errors = crate::user_diagnostic::to_absolute(l);
    let _ = oc.write_all(formatter(&absolute_errors).as_bytes());
}

/// `write_error_list format errors oc max_errors`: the sorted diagnostics
/// (at most `max_errors` of them) and the summary of `format` on `oc`, or
/// `No errors`. This is the output of the batch mode (`--batch-files`),
/// with which the test suites are run, so it is what `hh single` prints
/// (on stdout). Returns whether there were errors (`Diagnostics.has_errors`).
pub fn write_error_list(
    format: diagnostics_state::Format,
    errors: diagnostics_state::T,
    oc: &mut dyn std::io::Write,
    max_errors: Option<usize>,
) -> bool {
    let has_errors = diagnostics_state::has_errors(None, &errors);
    let errors = diagnostics_state::get_sorted_diagnostic_list(None, errors);
    let (shown_errors, dropped_errors) = match max_errors {
        Some(max_errors) => errors.split_at(max_errors.min(errors.len())),
        None => (&errors[..], &[][..]),
    };
    if !errors.is_empty() {
        for e in shown_errors {
            print_error(format, oc, e);
        }
        if let Some(summary) = diagnostics_state::format_summary(
            format,
            errors.len() as isize,
            0,
            Some(dropped_errors.len() as isize),
            max_errors.map(|n| n as isize),
        ) {
            let _ = oc.write_all(summary.as_bytes());
        }
    } else {
        let _ = oc.write_all(b"No errors\n");
    }
    let _ = oc.flush();
    has_errors
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tcopt(flags: Flags) -> GlobalOptions {
        make_tcopt(&flags).unwrap().tcopt
    }

    fn with_config(l: &[&str]) -> Flags {
        Flags {
            config_overrides: l.iter().map(|s| s.to_string()).collect(),
            ..Flags::default()
        }
    }

    #[test]
    fn defaults() {
        let opts = make_tcopt(&Flags::default()).unwrap();
        let t = &opts.tcopt;
        assert!(t.po.everything_sdt);
        assert!(t.po.allow_unstable_features);
        assert!(!t.po.use_legacy_experimental_feature_config);
        assert!(!t.tco_like_casts);
        assert!(t.tco_strict_contexts);
        assert!(t.tco_meth_caller_only_public_visibility);
        assert!(!t.tco_disallow_discarded_nullable_awaitables);
        assert_eq!(opts.packages_config_path, None);
        assert!(!opts.enable_implicit_packages);
    }

    /// Keys that the `hh_config` crate does not read reach the options.
    #[test]
    fn config_keys_are_read() {
        let t = tcopt(with_config(&[
            "disallow_discarded_nullable_awaitables=true",
            "meth_caller_only_public_visibility=false",
            "disable_physical_equality=true",
            "keep_user_attributes=true",
            "implicit_inherit_sdt=true",
            "typecheck_if_name_matches_regexp=^foo",
            r#"auto_namespace_map={"Vec": "HH\\Lib\\Vec"}"#,
        ]));
        assert!(t.tco_disallow_discarded_nullable_awaitables);
        assert!(!t.tco_meth_caller_only_public_visibility);
        assert!(t.tco_disable_physical_equality);
        assert!(t.po.keep_user_attributes);
        assert!(t.tco_implicit_inherit_sdt);
        assert_eq!(t.tco_typecheck_if_name_matches_regexp.as_deref(), Some("^foo"));
        assert_eq!(
            t.po.auto_namespace_map,
            vec![("Vec".to_string(), "HH\\Lib\\Vec".to_string())]
        );
    }

    /// `Server_config.load_config` comes after the flags: a key wins over a
    /// flag; and a later `--config` over an earlier one.
    #[test]
    fn config_wins_over_flags() {
        let t = tcopt(Flags {
            keep_user_attributes: true,
            enable_global_access_check: true,
            meth_caller_only_public_visibility: false,
            ..with_config(&[
                "keep_user_attributes=false",
                "meth_caller_only_public_visibility=false",
                "meth_caller_only_public_visibility=true",
            ])
        });
        assert!(!t.po.keep_user_attributes);
        assert!(t.tco_meth_caller_only_public_visibility);
        assert!(t.tco_global_access_check_enabled);
        // What a key does not set stays as the flag set it.
        let t = tcopt(Flags {
            keep_user_attributes: true,
            strict_contexts: false,
            ..Flags::default()
        });
        assert!(t.po.keep_user_attributes);
        assert!(!t.tco_strict_contexts);
    }

    /// The experimental features of the flags are added to those of the
    /// config.
    #[test]
    fn experimental_features_after_the_config() {
        let t = tcopt(Flags {
            enable_supportdyn_hint: true,
            consider_type_const_enforceable: true,
            ..with_config(&["enable_experimental_tc_features=upcast_expression"])
        });
        let features = &t.tco_legacy_experimental_features;
        assert!(features.contains("upcast_expression"));
        assert!(features.contains(crate::typechecker_options::experimental_supportdynamic_type_hint));
        assert!(features.contains(
            crate::typechecker_options::experimental_consider_type_const_enforceable
        ));
    }

    #[test]
    fn packages_keys() {
        let opts = make_tcopt(&with_config(&[
            "packages_config_path=PACKAGES.toml",
            "enable_implicit_packages=true",
        ]))
        .unwrap();
        assert_eq!(opts.packages_config_path.as_deref(), Some("PACKAGES.toml"));
        assert!(opts.enable_implicit_packages);
        assert_eq!(root(None).unwrap(), std::path::PathBuf::from("/"));
    }

    #[test]
    fn invalid_keys() {
        assert_eq!(
            invalid_config_key_message(&config_of_overrides(&["everything_sdt=true".to_string()])),
            None
        );
        let msg = invalid_config_key_message(&config_of_overrides(&[
            "everything_sdt=true".to_string(),
            "evrything_sdt=true".to_string(),
        ]))
        .unwrap();
        assert!(msg.starts_with("Unknown config option: evrything_sdt"), "{msg}");
        // Not a key for the OCaml (`hh_config` reads it): `hh_single_type_check`
        // exits.
        assert_eq!(
            invalid_config_key_message(&config_of_overrides(&[
                "tco_global_access_check_enabled=true".to_string()
            ])),
            Some("Unknown config option: tco_global_access_check_enabled\n".to_string())
        );
    }
}
