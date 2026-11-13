// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `hh single [FLAGS] FILE`: the command line of `hh_single_type_check`
//! (`hh_single_type_check.ml`, `parse_options` and the dispatch of its modes).
//!
//! Moved out of `main.rs` unchanged by W0b (plan §8 item 7). Owned by **F0**
//! (plan §7.3): the flags of the modes are parsed here into a
//! `hh_single_modes::Mode`; the `Errors` mode (the default) is checked here
//! as before, every other mode is run by `hh_single_modes::handle_mode`.
//! `hh single-complete` is `hh_single_complete.ml` ([`complete_single`]).

use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::Context;
use anyhow::Result;
use anyhow::bail;
use hh::check;
use hh::check::Stats;
use hh::ctx::Ctx;
use pos::Prefix;
use pos::RelativePath;

use super::print_diagnostics;

/// The flags of `hh_single_type_check` that take a value. Flags that are not
/// understood are accepted and ignored, so that the test suites' flag files
/// can be passed as they are.
const FLAGS_WITH_VALUE: &[&str] = &[
    "--config",
    "--error-format",
    "--extra-builtin",
    "--allowed-fixme-codes-strict",
    "--allowed-decl-fixme-codes",
    "--root",
    "--packages-config-path",
    "--custom-hhi-path",
    "--out-extension",
    "--max-errors",
    "--log-levels",
    "--simple-pessimize",
    "--union-intersection-type-hints",
];

/// The `--error-format` flags of `hh_single_type_check`, in order: the last
/// format that is recognised wins, and the others print a warning.
#[cfg(feature = "port")]
fn error_format_of_args(args: &[String]) -> Option<hh::diagnostics_state::Format> {
    use hh::diagnostics_state::Format;
    let mut error_format = None;
    for s in args {
        match s.as_str() {
            "raw" => error_format = Some(Format::Raw),
            "agent" => error_format = Some(Format::Agent),
            "context" => error_format = Some(Format::Context),
            "highlighted" => error_format = Some(Format::Highlighted),
            "plain" => error_format = Some(Format::Plain),
            "extended" => error_format = Some(Format::Extended),
            "plain_highlighted" => error_format = Some(Format::PlainHighlighted),
            _ => print!("Warning: unrecognized error format.\n"),
        }
    }
    error_format
}

/// `comma_string_to_iset` of `hh_single_type_check`: `"1, 2,3"`.
fn comma_string_to_iset(s: &str) -> Result<oxidized::i_set::ISet> {
    s.split(',')
        .map(|c| c.trim_start_matches(' '))
        .filter(|c| !c.is_empty())
        .map(|c| Ok(c.parse::<isize>()?))
        .collect()
}

/// `bool_of_string`, as `Arg.Bool` parses its argument.
fn ocaml_bool(s: &str) -> Result<bool> {
    match s {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => bail!("wrong argument `{s}`; expected a boolean"),
    }
}

/// `set_mode x ()`: a second mode is an error.
#[cfg(feature = "port")]
fn set_mode(mode: &mut hh::hh_single_modes::Mode, x: hh::hh_single_modes::Mode) -> Result<()> {
    match mode {
        hh::hh_single_modes::Mode::Errors => {
            *mode = x;
            Ok(())
        }
        _ => bail!("only a single mode should be specified"),
    }
}

pub fn check_single(args: &[String]) -> Result<ExitCode> {
    #[cfg(feature = "port")]
    use hh::hh_single_modes::Mode;
    // `fn_ref`: the files, the last one first.
    let mut fn_ref: Vec<PathBuf> = vec![];
    #[cfg(feature = "port")]
    let mut mode = Mode::Errors;
    #[cfg(feature = "port")]
    let mut batch_mode = false;
    #[cfg(feature = "port")]
    let mut out_extension = ".out".to_string();
    #[cfg(feature = "port")]
    let mut should_print_position = true;
    #[cfg(feature = "port")]
    let mut get_some_file_deps_full_hierarchy = false;
    let mut flags = hh::hh_single_type_check_flags::Flags::default();
    let mut extra_builtins = vec![];
    let mut error_format_args: Vec<String> = vec![];
    let mut max_errors: Option<usize> = None;
    let mut it = args.iter();
    // The flags of `parse_options` that make the options; its other modes
    // and flags are not here (a flag that is not understood is ignored).
    while let Some(arg) = it.next() {
        // `Arg` also accepts `--flag=value` for a flag that takes a value.
        let (arg, inline) = match arg.split_once('=') {
            Some((flag, value)) if arg.starts_with("--") => (flag, Some(value.to_string())),
            _ => (arg.as_str(), None),
        };
        let mut inline = inline;
        let mut next = |what: &str| {
            inline
                .take()
                .or_else(|| it.next().cloned())
                .with_context(|| format!("{arg} needs {what}"))
        };
        let int = |s: String| -> Result<isize> { Ok(s.parse::<isize>()?) };
        match arg {
            "--config" => flags.config_overrides.push(next("key=value")?),
            "--extra-builtin" => extra_builtins.push(PathBuf::from(next("a path")?)),
            "--deregister-attributes" => flags.deregister_attributes = Some(true),
            "--auto-namespace-map" => {
                #[cfg(feature = "port")]
                {
                    flags.auto_namespace_map = Some(
                        hh::server_config::convert_auto_namespace_to_map(&next("a JSON object")?)
                            .map_err(|e| anyhow::anyhow!("{:?}", e))?,
                    )
                }
                #[cfg(not(feature = "port"))]
                {
                    let json = next("a JSON object")?;
                    let map: std::collections::BTreeMap<String, String> =
                        serde_json::from_str(&json)?;
                    flags.auto_namespace_map = Some(map.into_iter().collect())
                }
            }
            "--no-call-coeffects" => flags.call_coeffects = false,
            "--no-local-coeffects" => flags.local_coeffects = false,
            "--no-strict-contexts" => flags.strict_contexts = false,
            "--run-simplihack" => {
                flags.skip_tast_checks = true;
                #[cfg(feature = "port")]
                set_mode(&mut mode, Mode::RunSimpliHack)?
            }
            "--error-format" => {
                // Interpreted, in order, by `error_format_of_args` (with `port`).
                error_format_args.push(next("a format")?)
            }
            "--max-errors" => max_errors = Some(next("a number")?.parse()?),
            "--log-inference-constraints" => flags.log_inference_constraints = Some(true),
            "--timeout" => flags.timeout = Some(int(next("a number")?)?),
            "--hh-log-level" => {
                let key = next("a key and a level")?;
                let level = int(it.next().context("--hh-log-level needs a level")?.clone())?;
                flags.log_levels.insert(key, level);
            }
            "--skip-hierarchy-checks" => flags.skip_hierarchy_checks = true,
            "--skip-tast-checks" => flags.skip_tast_checks = true,
            "--skip-check-under-dynamic" => flags.skip_check_under_dynamic = true,
            "--implicit-pess" | "--enable-supportdyn-hint" => flags.enable_supportdyn_hint = true,
            "--explicit-pess" => {
                // (The directory is the `--custom-hhi-path`, not ported.)
                next("a directory")?;
                flags.enable_supportdyn_hint = true
            }
            "--glean-reponame" => flags.glean_reponame = next("a name")?,
            "--disable-xhp-element-mangling" => flags.disable_xhp_element_mangling = true,
            "--keep-user-attributes" => flags.keep_user_attributes = true,
            "--enable-xhp-class-modifier" => flags.enable_xhp_class_modifier = true,
            "--allowed-fixme-codes-strict" => {
                flags.allowed_fixme_codes_strict = Some(comma_string_to_iset(&next("codes")?)?)
            }
            "--allowed-decl-fixme-codes" => {
                flags.allowed_decl_fixme_codes = Some(comma_string_to_iset(&next("codes")?)?)
            }
            "--consider-type-const-enforceable" => flags.consider_type_const_enforceable = true,
            "--interpret-soft-types-as-like-types" => {
                flags.interpret_soft_types_as_like_types = true
            }
            "--meth-caller-only-public-visibility" => {
                flags.meth_caller_only_public_visibility = ocaml_bool(&next("a bool")?)?
            }
            // `Arg.Int (( := ) explicit_consistent_constructors)`: 1 for
            // traits, 2 for all.
            "--explicit-consistent-constructors" => {
                flags.explicit_consistent_constructors = int(next("a level")?)?
            }
            // 1 for abstract constants, 2 for all.
            "--require-types-class-consts" => {
                flags.require_types_class_consts = int(next("a number")?)?
            }
            "--profile-top-level-definitions" => flags.profile_top_level_definitions = true,
            "--type-printer-fuel" => flags.type_printer_fuel = int(next("a number")?)?,
            "--enable-global-access-check" => flags.enable_global_access_check = true,
            "--overwrite-loop-iteration-upper-bound" => {
                flags.loop_iteration_upper_bound = Some(int(next("a number")?)?)
            }
            "--custom-error-config-path" => flags.custom_error_config_path = Some(next("a path")?),
            "--enable-class-pointer-hint" => {
                flags.enable_class_pointer_hint = ocaml_bool(&next("a bool")?)?
            }
            // The modes (`set_mode`) and the flags only they read.
            #[cfg(feature = "port")]
            "--refactor-sound-dynamic" => {
                let analysis_mode = next("an analysis mode")?;
                let refactor_mode = it.next().context("--refactor-sound-dynamic needs a mode")?;
                let x = it.next().context("--refactor-sound-dynamic needs an element")?;
                batch_mode = true;
                set_mode(
                    &mut mode,
                    Mode::RefactorSoundDynamic(analysis_mode, refactor_mode.clone(), x.clone()),
                )?
            }
            #[cfg(feature = "port")]
            "--cst-search" => set_mode(&mut mode, Mode::CstSearch)?,
            #[cfg(feature = "port")]
            "--dump-symbol-info" => set_mode(&mut mode, Mode::DumpSymbolInfo)?,
            #[cfg(feature = "port")]
            "--glean-index" => set_mode(&mut mode, Mode::GleanIndex(next("a directory")?))?,
            #[cfg(feature = "port")]
            "--glean-sym-hash" => set_mode(&mut mode, Mode::GleanSymHash)?,
            #[cfg(feature = "port")]
            "--lint" => set_mode(&mut mode, Mode::Lint)?,
            #[cfg(feature = "port")]
            "--lint-json" => set_mode(&mut mode, Mode::LintJson)?,
            #[cfg(feature = "port")]
            "--out-extension" => out_extension = next("an extension")?,
            #[cfg(feature = "port")]
            "--dump-deps" => set_mode(&mut mode, Mode::DumpDeps)?,
            #[cfg(feature = "port")]
            "--dump-dep-hashes" => set_mode(&mut mode, Mode::DumpDepHashes)?,
            #[cfg(feature = "port")]
            "--dump-inheritance" => set_mode(&mut mode, Mode::DumpInheritance)?,
            #[cfg(feature = "port")]
            "--get-some-file-deps" => {
                let depth = int(next("a depth")?)?;
                set_mode(
                    &mut mode,
                    Mode::GetSomeFileDeps {
                        depth,
                        full_hierarchy: false,
                    },
                )?
            }
            #[cfg(feature = "port")]
            "--get-some-file-deps-full-hierarchy" => get_some_file_deps_full_hierarchy = true,
            #[cfg(feature = "port")]
            "--ide-code-actions" => {
                let title_prefix = next("a title prefix")?;
                set_mode(
                    &mut mode,
                    Mode::IdeCodeActions {
                        title_prefix,
                        use_snippet_edits: true,
                    },
                )?
            }
            #[cfg(feature = "port")]
            "--ide-code-actions-no-experimental-capabilities" => {
                let title_prefix = next("a title prefix")?;
                set_mode(
                    &mut mode,
                    Mode::IdeCodeActions {
                        title_prefix,
                        use_snippet_edits: false,
                    },
                )?
            }
            #[cfg(feature = "port")]
            "--ide-diagnostics" => set_mode(&mut mode, Mode::IdeDiagnostics)?,
            #[cfg(feature = "port")]
            "--ide-signature-help" => set_mode(&mut mode, Mode::IdeSignatureHelp)?,
            #[cfg(feature = "port")]
            "--dump-classish-positions" => set_mode(&mut mode, Mode::DumpClassishPositions)?,
            // `Arg.Tuple [Arg.Int line; Arg.Int column]`, then
            // `File_content.Position.from_one_based line column`.
            #[cfg(feature = "port")]
            "--identify-symbol" | "--find-local" | "--find-refs" | "--go-to-impl"
            | "--highlight-refs" | "--hover" | "--enforcement" => {
                use hh::file_content::position;
                let line = int(next("a line")?)?;
                let column = int(it.next().with_context(|| format!("{arg} needs a column"))?.clone())?;
                let pos = position::from_one_based(line, column);
                let x = match arg {
                    "--identify-symbol" => Mode::IdentifySymbol(pos),
                    "--find-local" => Mode::FindLocal(pos),
                    "--find-refs" => Mode::FindRefs(pos),
                    "--go-to-impl" => Mode::GoToImpl(pos),
                    "--highlight-refs" => Mode::HighlightRefs(pos),
                    "--hover" => Mode::Hover(Some(pos)),
                    _ => Mode::Enforcement(Some(pos)),
                };
                set_mode(&mut mode, x)?
            }
            #[cfg(feature = "port")]
            "--outline" => set_mode(&mut mode, Mode::Outline)?,
            #[cfg(feature = "port")]
            "--outline-for-agents" => set_mode(&mut mode, Mode::OutlineForAgents)?,
            #[cfg(feature = "port")]
            "--nast" => set_mode(&mut mode, Mode::DumpNast)?,
            #[cfg(feature = "port")]
            "--tast" => set_mode(&mut mode, Mode::DumpTast)?,
            #[cfg(feature = "port")]
            "--infer-dynamic" => {
                set_mode(&mut mode, Mode::DumpDynamicInference { as_data: false })?
            }
            #[cfg(feature = "port")]
            "--infer-dynamic-as-data" => {
                set_mode(&mut mode, Mode::DumpDynamicInference { as_data: true })?
            }
            #[cfg(feature = "port")]
            "--stripped-tast" => set_mode(&mut mode, Mode::DumpStrippedTast)?,
            #[cfg(feature = "port")]
            "--get-member" => set_mode(&mut mode, Mode::GetMember(next("an ID")?))?,
            #[cfg(feature = "port")]
            "--batch-files" => batch_mode = true,
            #[cfg(feature = "port")]
            "--no-print-position" => should_print_position = false,
            #[cfg(feature = "port")]
            "--hover-at-caret" => set_mode(&mut mode, Mode::Hover(None))?,
            #[cfg(feature = "port")]
            "--enforcement-at-caret" => set_mode(&mut mode, Mode::Enforcement(None))?,
            #[cfg(feature = "port")]
            "--enforcement-at-caret-batch" => set_mode(&mut mode, Mode::EnforcementBatch)?,
            #[cfg(feature = "port")]
            "--fix" => set_mode(&mut mode, Mode::ApplyQuickfixes)?,
            #[cfg(feature = "port")]
            "--remove-dead-unsafe-casts" => set_mode(&mut mode, Mode::RemoveDeadUnsafeCasts)?,
            #[cfg(feature = "port")]
            "--count-imprecise-types" => set_mode(&mut mode, Mode::CountImpreciseTypes)?,
            #[cfg(feature = "port")]
            "--map-reduce" => set_mode(&mut mode, Mode::MapReduceMode)?,
            _ if FLAGS_WITH_VALUE.contains(&arg) => {
                next("a value")?;
            }
            // A flag without a value, or `--flag=value`.
            _ if arg.starts_with("--") => {}
            _ => fn_ref.insert(0, PathBuf::from(arg)),
        }
    }
    #[cfg(feature = "port")]
    if let Mode::GetSomeFileDeps { depth, .. } = mode {
        // (`--get-some-file-deps requires --root`: `--root` is not
        // understood here, see FLAGS_WITH_VALUE.)
        mode = Mode::GetSomeFileDeps {
            depth,
            full_hierarchy: get_some_file_deps_full_hierarchy,
        };
    }
    // The `Errors` mode checks the last file of the command line, as before;
    // the other modes take all the files (`fns`).
    #[cfg(feature = "port")]
    let is_errors = mode == Mode::Errors;
    #[cfg(not(feature = "port"))]
    let is_errors = true;
    let files: Vec<PathBuf> = if is_errors {
        fn_ref.first().cloned().into_iter().collect()
    } else {
        fn_ref.clone()
    };
    #[cfg(feature = "port")]
    if files.is_empty() && matches!(mode, Mode::GetMember(_)) {
        // `([], Get_member _) -> []`: not ported (it needs no file).
        return Err(hh::hh_single_modes::not_ported("F0", "--get-member"));
    }
    let file = files.first().cloned().context("no file given")?;
    // The contents of each file (the first one is `file`).
    let mut contents_of_files = vec![];
    for file in &files {
        contents_of_files
            .push(std::fs::read(file).with_context(|| format!("reading {}", file.display()))?);
    }

    // Errors name files relative to the directory of the test.
    let dir = file.parent().unwrap_or(Path::new("")).to_path_buf();
    // `hh_single_type_check` names the files it checks with `Dummy` paths
    // (their prefix is empty); the placeholder checker reads them from the
    // directory of the test as `Root` paths.
    let mut names = vec![];
    for file in &files {
        let name = PathBuf::from(file.file_name().context("not a file")?);
        names.push(if cfg!(feature = "port") {
            (Prefix::Dummy, name)
        } else {
            (Prefix::Root, name)
        });
    }
    #[allow(unused_mut)]
    let mut ctx_root = dir.clone();
    #[cfg(feature = "port")]
    let (tco, package_config_errors) = {
        use hh::hh_single_type_check as hstc;
        let hstc::Options {
            mut tcopt,
            packages_config_path,
            enable_implicit_packages,
        } = hstc::make_tcopt(&flags).map_err(|e| anyhow::anyhow!("{:?}", e))?;
        let root = hstc::root(packages_config_path.as_deref())?;
        hstc::set_path_prefixes(&root);
        // `use_canonical_filenames ()`: with a root other than `/`, the file
        // is named by its real path, `Relative_path.create_detect_prefix`
        // (a `Root` path under the root).
        if root != Path::new("/") {
            for (file, name) in files.iter().zip(names.iter_mut()) {
                let real = std::fs::canonicalize(file)
                    .with_context(|| format!("Couldn't resolve realpath of {}", file.display()))?;
                let root_s = format!("{}/", root.canonicalize()?.display());
                let real_s = real.to_string_lossy().into_owned();
                *name = match real_s.strip_prefix(&root_s) {
                    Some(suffix) => (Prefix::Root, PathBuf::from(suffix)),
                    None => (Prefix::Dummy, real),
                };
            }
            ctx_root = root.clone();
        }
        let (package_config_errors, package_info) =
            hstc::load_package_info(packages_config_path.as_deref(), enable_implicit_packages);
        // `Typechecker_options.set_package_info`
        tcopt.po.package_info = package_info;
        (tcopt, package_config_errors)
    };
    // Without the port: the keys that the `hh_config` crate reads, on what
    // `hh_single_type_check` sets before it applies `--config`.
    #[cfg(not(feature = "port"))]
    let tco = {
        let mut tco =
            check::hh_config(None, &["everything_sdt=true"], &flags.config_overrides)?.opts;
        tco.po.allow_unstable_features = true;
        tco
    };
    let mut ctx = Ctx::new(&ctx_root, tco)?;
    ctx.add_magic_builtins();

    let mut decl_paths = ctx.hhi_paths.clone();
    for builtin in &extra_builtins {
        // Extra builtins are declared like hhi files.
        let path = RelativePath::new(Prefix::Hhi, builtin.file_name().context("not a file")?);
        let builtin_path = if builtin.is_absolute() {
            builtin.clone()
        } else {
            dir.join(builtin)
        };
        if let Ok(text) = std::fs::read(&builtin_path) {
            ctx.files.set(path, text);
            decl_paths.push(path);
        }
    }
    #[cfg(feature = "port")]
    let builtins = decl_paths.clone();

    // The files the multifiles simulate (`files_contents`).
    let mut paths = vec![];
    #[cfg(feature = "port")]
    let mut files_contents = vec![];
    for ((file_prefix, name), contents) in names.iter().zip(contents_of_files.iter()) {
        for (part, text) in hh::multifile::file_to_file_list(&name.to_string_lossy(), contents) {
            let path = RelativePath::new(*file_prefix, &part);
            #[cfg(feature = "port")]
            files_contents.push((path, bstr::BString::from(text.clone())));
            ctx.files.set(path, text);
            paths.push(path);
        }
    }
    decl_paths.extend(paths.iter().copied());

    let mut stats = Stats::default();
    check::declare_files(&ctx, &decl_paths, &mut stats);

    #[cfg(feature = "port")]
    {
        use hh::hh_single_type_check as hstc;
        let ctx = std::sync::Arc::new(ctx);
        hstc::install(&ctx);
        let to_ox = |paths: &[RelativePath]| -> Vec<relative_path::RelativePath> {
            paths.iter().map(|&p| p.into()).collect()
        };
        let errors = hh::diagnostics_state::merge(
            package_config_errors,
            hstc::parse_name_and_decl(&ctx, &to_ox(&decl_paths)),
        );
        if mode != Mode::Errors {
            let error_format =
                hh::diagnostics_state::format_or_default(error_format_of_args(&error_format_args));
            // `handle_mode`
            let mut files_contents: Vec<(relative_path::RelativePath, bstr::BString)> =
                files_contents.into_iter().map(|(p, c)| (p.into(), c)).collect();
            files_contents.sort_by(|(p1, _), (p2, _)| hh::relative_path::compare(p1, p2));
            files_contents.dedup_by(|(p1, _), (p2, _)| p1 == p2);
            let input = hh::hh_single_modes::Input {
                ctx,
                filenames: names
                    .iter()
                    .map(|(prefix, name)| RelativePath::new(*prefix, name).into())
                    .collect(),
                builtins: to_ox(&builtins),
                files_contents,
                files_info: {
                    let mut files_info = to_ox(&decl_paths);
                    files_info.sort_by(hh::relative_path::compare);
                    files_info.dedup();
                    files_info
                },
                parse_errors: errors,
                max_errors,
                error_format,
                batch_mode,
                out_extension,
                should_print_position,
            };
            let code = hh::hh_single_modes::handle_mode(&mode, input)?;
            return Ok(ExitCode::from(code));
        }
        let errors = hstc::check_file(&ctx, errors, &to_ox(&paths));
        // The test suites run `hh_single_type_check` in batch mode, which
        // writes the errors with `write_error_list`; here it writes them on
        // stdout.
        let error_format =
            hh::diagnostics_state::format_or_default(error_format_of_args(&error_format_args));
        let has_errors =
            hstc::write_error_list(error_format, errors, &mut std::io::stdout().lock(), max_errors);
        return Ok(if has_errors {
            ExitCode::from(2)
        } else {
            ExitCode::SUCCESS
        });
    }
    // (The placeholder checker prints in the plain format.)
    #[allow(unreachable_code)]
    let _ = (error_format_args, max_errors);
    #[allow(unreachable_code)]
    let diagnostics = check::check_files(&ctx, &paths, &mut stats);
    print_diagnostics(&diagnostics);
    Ok(ExitCode::SUCCESS)
}

/// `hh single-complete [FLAGS] FILE`: the command line of
/// `hh_single_complete` (`hh_single_complete.ml`, `parse_options`), then
/// `handle_mode`. Its modes are F3's (autocomplete) and F4's (search,
/// autoclose); until they land, every mode is "not ported". An option that
/// `hh_single_complete` does not have is an error, as for `Arg.parse`.
#[cfg(feature = "port")]
pub fn complete_single(args: &[String]) -> Result<ExitCode> {
    use hh::hh_single_modes::complete::Mode;
    let mut fn_ref: Vec<String> = vec![];
    let mut mode = Mode::NoMode;
    let mut set_mode = |x: Mode| -> Result<()> {
        match mode {
            Mode::NoMode => {
                mode = x;
                Ok(())
            }
            _ => bail!("only a single mode should be specified"),
        }
    };
    let mut extra_builtins: Vec<String> = vec![];
    let mut no_builtins = false;
    let mut disable_xhp_element_mangling = false;
    let mut disable_xhp_children_declarations = false;
    let mut enable_xhp_class_modifier = false;
    let mut auto_namespace_map = None;
    let mut log_levels = std::collections::BTreeMap::new();
    let mut saved_state_manifold_api_key: Option<String> = None;
    let mut naming_table: Option<String> = None;
    let mut root: Option<String> = None;
    let mut glean_reponame = String::new();
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let (arg, inline) = match arg.split_once('=') {
            Some((flag, value)) if arg.starts_with("--") => (flag, Some(value.to_string())),
            _ => (arg.as_str(), None),
        };
        let mut inline = inline;
        let mut next = |what: &str| {
            inline
                .take()
                .or_else(|| it.next().cloned())
                .with_context(|| format!("{arg} needs {what}"))
        };
        match arg {
            "--extra-builtin" => extra_builtins.insert(0, next("a path")?),
            "--no-builtins" => no_builtins = true,
            "--disable-xhp-element-mangling" => disable_xhp_element_mangling = true,
            "--disable-xhp-children-declarations" => disable_xhp_children_declarations = true,
            "--enable-xhp-class-modifier" => enable_xhp_class_modifier = true,
            "--auto-namespace-map" => {
                auto_namespace_map = Some(
                    hh::server_config::convert_auto_namespace_to_map(&next("a JSON object")?)
                        .map_err(|e| anyhow::anyhow!("{:?}", e))?,
                )
            }
            "--auto-complete" => set_mode(Mode::Autocomplete {
                is_manually_invoked: false,
            })?,
            "--hh-log-level" => {
                let key = next("a key and a level")?;
                let level = it.next().context("--hh-log-level needs a level")?;
                log_levels.insert(key, level.parse::<isize>()?);
            }
            "--auto-complete-manually-invoked" => set_mode(Mode::Autocomplete {
                is_manually_invoked: true,
            })?,
            "--auto-complete-show-glean" => set_mode(Mode::AutocompleteGlean { dry_run: true })?,
            "--auto-complete-glean" => set_mode(Mode::AutocompleteGlean { dry_run: false })?,
            "--search-show-glean" => set_mode(Mode::Search {
                glean_only: true,
                dry_run: true,
            })?,
            "--search-glean" => set_mode(Mode::Search {
                glean_only: true,
                dry_run: false,
            })?,
            "--search" => set_mode(Mode::Search {
                glean_only: false,
                dry_run: false,
            })?,
            "--find-refs-show-glean" => set_mode(Mode::FindrefsGlean { dry_run: true })?,
            "--find-refs-glean" => set_mode(Mode::FindrefsGlean { dry_run: false })?,
            "--manifold-api-key" => {
                let key = next("a key")?;
                // `set "manifold api key"`
                if saved_state_manifold_api_key.is_some() {
                    bail!("Attempted to set manifold api key twice")
                }
                saved_state_manifold_api_key = Some(key)
            }
            "--naming-table" => naming_table = Some(next("a path")?),
            "--resolve" => set_mode(Mode::Resolve {
                is_manually_invoked: false,
            })?,
            "--xhp-close" => set_mode(Mode::XhpClose)?,
            "--root" => root = Some(next("a path")?),
            "--glean-reponame" => glean_reponame = next("a name")?,
            _ if arg.starts_with('-') => bail!("unknown option '{arg}'"),
            _ => fn_ref.insert(0, arg.to_string()),
        }
    }
    if fn_ref.is_empty() {
        // `die usage`
        bail!("Usage: hh single-complete filename")
    }
    if naming_table.is_some() && root.is_none() {
        bail!("--naming-table needs --root")
    }
    if let Mode::Search {
        glean_only: false, ..
    } = mode
    {
        if !glean_reponame.is_empty() && (root.is_none() || naming_table.is_none()) {
            bail!("--search --glean-reponame needs --naming-table and --root")
        }
    }
    // `decl_and_run_mode`
    use hh::hh_single_modes::complete;
    let tcopt = complete::make_tcopt(&complete::Flags {
        disable_xhp_element_mangling,
        disable_xhp_children_declarations,
        enable_xhp_class_modifier,
        auto_namespace_map,
        saved_state_manifold_api_key,
        glean_reponame,
        log_levels,
    });
    // (`--root`/`--naming-table` need SS1's SQLite naming table.)
    if root.is_some() {
        return Err(hh::hh_single_modes::not_ported("SS1", "--root"));
    }
    hh::hh_single_type_check::set_path_prefixes(Path::new("/"));
    let namespace_map = tcopt.po.auto_namespace_map.clone();
    let mut ctx = Ctx::new(Path::new("."), tcopt)?;
    // The builtins: unless --no-builtins, the magic builtin of
    // hh_single_complete, the extra builtins (each part of each, by its
    // base name) and the hhi files.
    let mut to_decl = vec![];
    if !no_builtins {
        let magic = RelativePath::new(Prefix::Hhi, "hh_single_type_check_magic.hhi");
        ctx.files.set(magic, COMPLETE_MAGIC_BUILTIN.as_bytes().to_vec());
        let mut builtins = vec![magic];
        for filename in &extra_builtins {
            let content = std::fs::read(filename)
                .with_context(|| format!("reading {}", filename))?;
            for (part, text) in hh::multifile::file_to_file_list(filename, &content) {
                let base = Path::new(&part).file_name().context("not a file")?.to_owned();
                let path = RelativePath::new(Prefix::Hhi, &base);
                if builtins.contains(&path) {
                    // `die "Multiple magic builtins share the same base name.\n"`
                    bail!("Multiple magic builtins share the same base name.")
                }
                ctx.files.set(path, text);
                builtins.push(path);
            }
        }
        to_decl.extend(builtins);
        to_decl.extend(ctx.hhi_paths.iter().copied());
    }
    // `hh_files_contents`: the parts that start with `<?hh`.
    let mut hh_files = vec![];
    for filename in &fn_ref {
        let content = std::fs::read(filename).with_context(|| format!("reading {}", filename))?;
        for (part, text) in hh::multifile::file_to_file_list(filename, &content) {
            if text.starts_with(b"<?hh") {
                let path = RelativePath::new(Prefix::Dummy, &part);
                ctx.files.set(path, text);
                hh_files.push(path);
            }
        }
    }
    to_decl.extend(hh_files.iter().copied());
    let mut stats = Stats::default();
    check::declare_files(&ctx, &to_decl, &mut stats);
    let ctx = std::sync::Arc::new(ctx);
    hh::hh_single_type_check::install(&ctx);
    let to_ox: Vec<relative_path::RelativePath> = to_decl.iter().map(|&p| p.into()).collect();
    let _errors = hh::hh_single_type_check::parse_name_and_decl(&ctx, &to_ox);
    // SYMBOL INDEX: initialize, then update from the addenda of each file
    // (in the order of the paths: a `Relative_path.Map`).
    let provider_name = if ctx.tco.glean_reponame.is_empty() {
        "LocalIndex"
    } else {
        "CustomIndex"
    };
    let sienv = hh::symbol_index::initialize(&ctx.tco, &namespace_map, provider_name, true);
    let sienv = hh::search_utils::SiEnv {
        sie_quiet_mode: false,
        sie_resolve_positions: true,
        sie_resolve_local_decl: true,
        ..sienv
    };
    let mut paths_with_addenda = vec![];
    let mut files_info = hh::relative_path::map::T::new();
    use ::file_provider::FileProvider as _;
    for &path in &to_decl {
        let text = ctx.files.get(path).unwrap_or_default();
        let decls = ctx.decl_parser.parse_with_text(path, &text).unwrap_or_default();
        // NAMING PHASE 4: the forward naming table (F3)
        files_info.insert(
            relative_path::RelativePath::from(path),
            complete::file_info_of_decls(&relative_path::RelativePath::from(path), &decls),
        );
        paths_with_addenda.push((
            relative_path::RelativePath::from(path),
            complete::addenda_of_parse(&decls),
            hh::search_utils::FileSource::TypeChecker,
        ));
    }
    paths_with_addenda.sort_by(|(p1, _, _), (p2, _, _)| hh::relative_path::compare(p1, p2));
    paths_with_addenda.dedup_by(|(p1, _, _), (p2, _, _)| p1 == p2);
    let sienv = hh::symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda);
    let input = complete::Input {
        ctx,
        filenames: fn_ref
            .iter()
            .map(|f| RelativePath::new(Prefix::Dummy, f).into())
            .collect(),
        sienv,
        naming_table: hh::naming_table::create(files_info),
    };
    let code = complete::handle_mode(&mode, input)?;
    Ok(ExitCode::from(code))
}

/// `magic_builtins` of `hh_single_complete.ml`.
#[cfg(feature = "port")]
const COMPLETE_MAGIC_BUILTIN: &str = concat!(
    "<?hh\n",
    "namespace {\n",
    "async function gena<Tk as arraykey, Tv>(\n",
    "  KeyedTraversable<Tk, Awaitable<Tv>> $awaitables,\n",
    "): Awaitable<darray<Tk, Tv>>;\n",
    "function hh_show(<<__AcceptDisposable>> $val) {}\n",
    "function hh_expect<T>(<<__AcceptDisposable>> $val) {}\n",
    "function hh_expect_equivalent<T>(<<__AcceptDisposable>> $val) {}\n",
    "function hh_show_env() {}\n",
    "function hh_log_level($key, $level) {}\n",
    "function hh_force_solve () {}",
    "}\n",
    "namespace HH\\Lib\\Tuple{\n",
    "function gen();\n",
    "function from_async();\n",
    "}\n",
);
