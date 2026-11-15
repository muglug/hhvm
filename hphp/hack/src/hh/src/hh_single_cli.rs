// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hh_single_type_check.ml`'s `parse_options` and `main_hack` (and
//! of those of `hh_single_complete.ml`): the command line of `hh single
//! [FLAGS] FILE`. The flags of the modes are parsed here into a
//! `hh_single_type_check::modes::Mode`; the `Errors` mode (the default) is checked here
//! as before, every other mode is run by `hh_single_type_check::modes::handle_mode`.
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

/// Without the port, the flags that take a value: flags that are not
/// understood are accepted and ignored. (With the port, `Arg.parse` of
/// `hh_single_type_check::args` has rejected any flag that the OCaml does not
/// have before this parser runs, and every flag of the OCaml is interpreted
/// below, or refused as not ported.)
const FLAGS_WITH_VALUE: &[&str] = &[
    "--config",
    "--error-format",
    "--extra-builtin",
    "--allowed-fixme-codes-strict",
    "--allowed-decl-fixme-codes",
    "--packages-config-path",
    "--out-extension",
    "--max-errors",
    "--log-levels",
    "--simple-pessimize",
    "--union-intersection-type-hints",
];

/// The `--error-format` flags of `hh_single_type_check`, in order: the last
/// format that is recognised wins, and the others print a warning.
#[cfg(feature = "port")]
fn error_format_of_args(args: &[String]) -> Option<hh::diagnostics::Format> {
    use hh::diagnostics::Format;
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
fn bool_of_string(s: &str) -> Result<bool> {
    match s {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => bail!("wrong argument `{s}`; expected a boolean"),
    }
}

/// `set_mode x ()`: a second mode is an error.
#[cfg(feature = "port")]
fn set_mode(mode: &mut hh::hh_single_type_check::modes::Mode, x: hh::hh_single_type_check::modes::Mode) -> Result<()> {
    match mode {
        hh::hh_single_type_check::modes::Mode::Errors => {
            *mode = x;
            Ok(())
        }
        _ => bail!("only a single mode should be specified"),
    }
}

/// `usage` of `parse_options`.
#[cfg(feature = "port")]
fn usage() -> String {
    format!(
        "Usage: {} filename\n",
        std::env::args().next().unwrap_or_else(|| "hh".to_string())
    )
}

/// `die str` of `hh_single_type_check.ml`: `str` on stderr, exit 2.
#[cfg(feature = "port")]
fn die(s: &str) -> ExitCode {
    hh::hh_single_type_check::die(s)
}

/// An exception that `hh_single_type_check` does not catch (see
/// `hh_single_type_check::handle_uncaught`).
#[cfg(feature = "port")]
fn uncaught(exn: hh::rt::ocaml_exn::Uncaught) -> anyhow::Error {
    exn.into()
}

/// The contents of a file (`Sys_utils.cat`), or the `Sys_error` it raises.
fn read_file(path: &str) -> Result<Vec<u8>> {
    #[cfg(feature = "port")]
    return Ok(hh::sys_utils::cat(path)?);
    #[cfg(not(feature = "port"))]
    std::fs::read(path).with_context(|| format!("reading {path}"))
}

/// A file of `--batch-files` in the `Errors` mode: it is checked alone, and
/// its output written to `<file><out_extension>`.
#[cfg(feature = "port")]
struct BatchFile {
    file: PathBuf,
}

pub fn check_single(args: &[String]) -> Result<ExitCode> {
    #[cfg(feature = "port")]
    return hh::hh_single_type_check::handle_uncaught(|| check_single_exn(args, None));
    #[cfg(not(feature = "port"))]
    check_single_exn(args)
}

fn check_single_exn(
    args: &[String],
    #[cfg(feature = "port")] batch_file: Option<&BatchFile>,
) -> Result<ExitCode> {
    // `Arg.parse` of `parse_options`: unknown options, missing or wrong
    // arguments, a second mode and `--help` are reported as the OCaml's
    // `Arg` reports them (it exits).
    #[cfg(feature = "port")]
    hh::hh_single_type_check::args::parse(
        &std::env::args().next().unwrap_or_else(|| "hh".to_string()),
        args,
    );
    #[cfg(feature = "port")]
    use hh::hh_single_type_check::modes::Mode;
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
    let mut no_builtins = false;
    let mut error_format_args: Vec<String> = vec![];
    let mut max_errors: Option<usize> = None;
    // `--root`, `--naming-table`, `--custom-hhi-path` (also set by
    // `--explicit-pess`) and `--force-allow-builtins-in-custom-hhi-path-FLAKEY`.
    let mut root_flag: Option<String> = None;
    let mut naming_table_flag: Option<String> = None;
    let mut custom_hhi_path: Option<String> = None;
    let mut force_allow_builtins_in_custom_hhi_path = false;
    // The flags of the OCaml that are not ported (they are refused once the
    // command line is parsed, as nothing must silently ignore them).
    let mut not_ported_flags: Vec<&'static str> = vec![];
    let mut it = args.iter();
    // The flags of `parse_options`, in its order.
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
            "--no-builtins" => no_builtins = true,
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
                flags.enable_supportdyn_hint = true;
                custom_hhi_path = Some(next("a directory")?)
            }
            "--root" => root_flag = Some(next("a path")?),
            "--naming-table" => naming_table_flag = Some(next("a path")?),
            "--custom-hhi-path" => custom_hhi_path = Some(next("a directory")?),
            "--force-allow-builtins-in-custom-hhi-path-FLAKEY" => {
                force_allow_builtins_in_custom_hhi_path = true
            }
            // `Arg.Set report_pos_from_reason`: the OCaml never reads it.
            "--report-pos-from-reason" => {}
            "--profile-type-check-twice" => not_ported_flags.push("--profile-type-check-twice"),
            "--profile-type-check-multi" => {
                int(next("a number")?)?;
                not_ported_flags.push("--profile-type-check-multi")
            }
            "--memtrace" => {
                next("a file")?;
                not_ported_flags.push("--memtrace")
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
                flags.meth_caller_only_public_visibility = bool_of_string(&next("a bool")?)?
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
    // `fns`: all the files, the last one first. (The placeholder checker
    // checks the last one.) A file of `--batch-files` is checked alone.
    #[cfg(feature = "port")]
    let files: Vec<PathBuf> = match batch_file {
        Some(BatchFile { file }) => vec![file.clone()],
        None => fn_ref.clone(),
    };
    #[cfg(not(feature = "port"))]
    let files: Vec<PathBuf> = fn_ref.first().cloned().into_iter().collect();
    // `([], Get_member _) -> []`: no file (the directory is the current one).
    #[cfg(feature = "port")]
    let get_member_without_file = files.is_empty() && matches!(mode, Mode::GetMember(_));
    #[cfg(not(feature = "port"))]
    let get_member_without_file = false;
    let file = if get_member_without_file {
        PathBuf::from("./")
    } else {
        match files.first() {
            Some(file) => file.clone(),
            // `([], _) -> die usage`
            #[cfg(feature = "port")]
            None => return Ok(die(&usage())),
            #[cfg(not(feature = "port"))]
            None => bail!("no file given"),
        }
    };
    // The checks of `parse_options` after `Arg.parse`, in its order.
    #[cfg(feature = "port")]
    {
        if matches!(mode, Mode::GetSomeFileDeps { .. }) && root_flag.is_none() {
            return Err(uncaught(hh::rt::ocaml_exn::Uncaught::arg_bad(
                "--get-some-file-deps requires --root",
            )));
        }
        if naming_table_flag.is_some() && root_flag.is_none() {
            return Err(uncaught(hh::rt::ocaml_exn::Uncaught::failure("--naming-table needs --root")));
        }
        if custom_hhi_path.is_some() && !no_builtins && !force_allow_builtins_in_custom_hhi_path {
            return Err(uncaught(hh::rt::ocaml_exn::Uncaught::failure(
                "--custom-hhi-path needs --no-builtins",
            )));
        }
        if root_flag.is_some() {
            // (`--root`, with or without `--naming-table`: the naming table
            // of a repository, as `hh single-complete`'s.)
            return Err(hh::hh_single_type_check::modes::not_ported("--root"));
        }
        if custom_hhi_path.is_some() && !no_builtins {
            // (The builtins of a custom hhi directory, read from it.)
            return Err(hh::hh_single_type_check::modes::not_ported(
                "--force-allow-builtins-in-custom-hhi-path-FLAKEY",
            ));
        }
        if let Some(flag) = not_ported_flags.first() {
            return Err(hh::hh_single_type_check::modes::not_ported(flag));
        }
        // `Errors when batch_mode`: for each file of the batch, typecheck it
        // serially (`iter_over_files`); each one is checked from scratch, as
        // the OCaml resets the heaps in between (it keeps the builtins
        // declared: here they are declared again for each file).
        if mode == Mode::Errors && batch_mode && batch_file.is_none() {
            for file in &files {
                // (What this thread derived from the declarations of the
                // previous file is forgotten.)
                hh::rt::decl_epoch::bump();
                hh::rt::decl_epoch::sync_thread();
                check_single_exn(args, Some(&BatchFile { file: file.clone() }))?;
            }
            return Ok(ExitCode::SUCCESS);
        }
    }
    #[cfg(not(feature = "port"))]
    let _ = (
        root_flag,
        naming_table_flag,
        force_allow_builtins_in_custom_hhi_path,
        not_ported_flags,
        custom_hhi_path,
    );
    // The contents of each file (the first one is `file`).
    let mut contents_of_files = vec![];
    for file in &files {
        contents_of_files
            .push(read_file(&file.to_string_lossy())?);
    }

    // Errors name files relative to the directory of the test.
    let dir = file.parent().unwrap_or(Path::new("")).to_path_buf();
    // `hh_single_type_check` names the files it checks with `Dummy` paths
    // (their prefix is empty); the placeholder checker reads them from the
    // directory of the test as `Root` paths.
    // With the port, the `Dummy` path is the file as given on the command
    // line (`Relative_path.create Relative_path.Dummy filename`), as the
    // OCaml names it (in errors, `hh_show`, and the services that read the
    // file back from disk).
    let mut names = vec![];
    for file in &files {
        names.push(if cfg!(feature = "port") {
            let _ = file.file_name().context("not a file")?;
            (Prefix::Dummy, file.clone())
        } else {
            (Prefix::Root, PathBuf::from(file.file_name().context("not a file")?))
        });
    }
    #[allow(unused_mut)]
    let mut ctx_root = dir.clone();
    // `Tempfile.with_tempdir (fun hhi_root -> ...)` of `main_hack`.
    #[cfg(feature = "port")]
    let hhi_root = match &custom_hhi_path {
        None => hh::hh_single_type_check::HhiRoot::make()?,
        Some(dir) => match hh::hh_single_type_check::HhiRoot::custom(dir) {
            Ok(root) => root,
            Err(msg) => return Ok(die(&msg)),
        },
    };
    #[cfg(feature = "port")]
    let (tco, package_config_errors) = {
        use hh::hh_single_type_check as hstc;
        let hstc::Options {
            mut tcopt,
            packages_config_path,
            enable_implicit_packages,
        } = hstc::make_tcopt(&flags).map_err(|e| anyhow::anyhow!("{:?}", e))?;
        let root = hstc::root(packages_config_path.as_deref())?;
        hstc::set_path_prefixes_with_hhi_root(&root, &hhi_root.dir);
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
            check::hh_config(None, &["everything_sdt=true"], &flags.config_overrides)?.common.opts;
        tco.po.allow_unstable_features = true;
        tco
    };
    let mut ctx = Ctx::new(&ctx_root, tco)?;
    // `--no-builtins`: `builtins` is empty (no hhi file, no magic builtin, no
    // extra builtin is declared).
    if no_builtins {
        extra_builtins.clear();
    } else {
        ctx.add_magic_builtins();
        // (`decl_and_run_mode` writes the magic builtins into the hhi root.)
        #[cfg(feature = "port")]
        {
            use file_provider::FileProvider as _;
            let path = *ctx.hhi_paths.last().context("no magic builtin")?;
            let contents = ctx.files.get(path)?;
            hhi_root.write_builtin(&path.path().to_string_lossy(), &contents)?;
        }
    }
    // The hhi files are named under the hhi root.
    #[cfg(feature = "port")]
    {
        ctx.path_ctx = std::sync::Arc::new(pos::RelativePathCtx {
            hhi: hhi_root.dir.clone(),
            ..(*ctx.path_ctx).clone()
        });
    }

    let mut decl_paths = if no_builtins { vec![] } else { ctx.hhi_paths.clone() };
    for builtin in &extra_builtins {
        // Extra builtins are declared like hhi files.
        let path = RelativePath::new(Prefix::Hhi, builtin.file_name().context("not a file")?);
        let builtin_path = if builtin.is_absolute() {
            builtin.clone()
        } else {
            dir.join(builtin)
        };
        if let Ok(text) = std::fs::read(&builtin_path) {
            #[cfg(feature = "port")]
            hhi_root.write_builtin(&path.path().to_string_lossy(), &text)?;
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
        for (rooted, part, text) in hh::multifile::file_to_file_list_rooted(&name.to_string_lossy(), contents) {
            // (`~root/` parts: `Relative_path.from_root ~suffix`.)
            let path = RelativePath::new(if rooted { Prefix::Root } else { *file_prefix }, &part);
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
        if mode == Mode::DumpDeps {
            hh::hh_single_type_check::modes::add_debug_trace_callback();
        }
        if let Some(BatchFile { .. }) = batch_file {
            // `Errors when batch_mode`, for one file: only the builtins are
            // declared first ("Don't declare all the filenames in
            // batch_errors mode"); the file's output goes to
            // `<file><out_extension>`, through a process-unique temporary
            // file renamed into place.
            let parse_errors = hh::diagnostics::merge(
                package_config_errors,
                hstc::parse_name_and_decl(&ctx, &to_ox(&builtins)),
            );
            let error_format =
                hh::diagnostics::format_or_default(error_format_of_args(&error_format_args));
            let filename = names
                .first()
                .map(|(prefix, name)| relative_path::RelativePath::from(RelativePath::new(*prefix, name)))
                .context("no file")?;
            let out_path = format!("{}{}", hh::relative_path::to_absolute(&filename), out_extension);
            let tmp_path = format!("{}.{}.tmp", out_path, std::process::id());
            let mut oc = std::fs::File::create(&tmp_path).map_err(|e| {
                hh::sys_utils::SysError::of_io_error(&tmp_path, &e)
            })?;
            // This means builtins had errors, so lets just print those if we see them
            if !hh::diagnostics::has_no_errors_or_warnings(None, &parse_errors) {
                hstc::write_error_list(error_format, parse_errors, &mut oc, max_errors);
            } else {
                // `Typing_log.out_channel := oc`
                let log_oc = oc.try_clone()?;
                hh::typing_log::OUT_CHANNEL.with(|c| *c.borrow_mut() = Box::new(log_oc));
                let parse_errors = hstc::parse_name_and_decl(&ctx, &to_ox(&paths));
                let errors = hstc::check_file(&ctx, parse_errors, &to_ox(&paths));
                hstc::write_error_list(error_format, errors, &mut oc, max_errors);
                hh::typing_log::OUT_CHANNEL
                    .with(|c| *c.borrow_mut() = Box::new(std::io::stdout()));
            }
            drop(oc);
            std::fs::rename(&tmp_path, &out_path)
                .map_err(|e| hh::sys_utils::SysError::of_io_error(&tmp_path, &e))?;
            return Ok(ExitCode::SUCCESS);
        }
        let errors = hh::diagnostics::merge(
            package_config_errors,
            hstc::parse_name_and_decl(&ctx, &to_ox(&decl_paths)),
        );
        if mode != Mode::Errors {
            let error_format =
                hh::diagnostics::format_or_default(error_format_of_args(&error_format_args));
            // `handle_mode`
            let mut files_contents: Vec<(relative_path::RelativePath, bstr::BString)> =
                files_contents.into_iter().map(|(p, c)| (p.into(), c)).collect();
            files_contents.sort_by(|(p1, _), (p2, _)| hh::relative_path::compare(p1, p2));
            files_contents.dedup_by(|(p1, _), (p2, _)| p1 == p2);
            let input = hh::hh_single_type_check::modes::Input {
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
            let code = hh::hh_single_type_check::modes::handle_mode(&mode, input)?;
            return Ok(ExitCode::from(code));
        }
        // `Errors`: "Don't typecheck builtins"
        let errors = hstc::check_file(&ctx, errors, &to_ox(&paths));
        let error_format =
            hh::diagnostics::format_or_default(error_format_of_args(&error_format_args));
        let has_errors = hstc::print_error_list(error_format, errors, max_errors);
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
/// `handle_mode` (`hh_single_complete::handle_mode`). An option that
/// `hh_single_complete` does not have is an error, as for `Arg.parse`.
#[cfg(feature = "port")]
pub fn complete_single(args: &[String]) -> Result<ExitCode> {
    hh::hh_single_type_check::handle_uncaught(|| complete_single_exn(args))
}

#[cfg(feature = "port")]
fn complete_single_exn(args: &[String]) -> Result<ExitCode> {
    use hh::hh_single_complete::Mode;
    // `Arg.parse` of `parse_options`: unknown options, missing or wrong
    // arguments, a second mode, `--help` and the exceptions the options
    // raise are as the OCaml's.
    hh::hh_single_complete::args::parse_options(
        &std::env::args().next().unwrap_or_else(|| "hh".to_string()),
        args,
    )?;
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
        // `([], _) -> die usage`
        return Ok(die(&usage()));
    }
    if naming_table.is_some() && root.is_none() {
        return Err(uncaught(hh::rt::ocaml_exn::Uncaught::failure("--naming-table needs --root")));
    }
    if let Mode::Search {
        glean_only: false, ..
    } = mode
    {
        if !glean_reponame.is_empty() && (root.is_none() || naming_table.is_none()) {
            // --search --glean-reponame looks up glean to find symbol names, but then
            // uses reverse-naming-table and root to fetch the AST and find its position.
            return Err(uncaught(hh::rt::ocaml_exn::Uncaught::failure(
                "--search --glean-reponame needs --naming-table and --root",
            )));
        }
    }
    // `decl_and_run_mode`
    use hh::hh_single_complete;
    let tcopt = hh_single_complete::make_tcopt(&hh_single_complete::Flags {
        disable_xhp_element_mangling,
        disable_xhp_children_declarations,
        enable_xhp_class_modifier,
        auto_namespace_map,
        saved_state_manifold_api_key,
        glean_reponame,
        log_levels,
    });
    // (`--root`/`--naming-table`: the SQLite naming table.)
    if root.is_some() {
        return Err(hh::hh_single_type_check::modes::not_ported("--root"));
    }
    // `Tempfile.with_tempdir (fun hhi_root -> ...)`
    let hhi_root = hh::hh_single_type_check::HhiRoot::make()?;
    hh::hh_single_type_check::set_path_prefixes_with_hhi_root(Path::new("/"), &hhi_root.dir);
    let namespace_map = tcopt.po.auto_namespace_map.clone();
    let mut ctx = Ctx::new(Path::new("."), tcopt)?;
    ctx.path_ctx = std::sync::Arc::new(pos::RelativePathCtx {
        hhi: hhi_root.dir.clone(),
        ..(*ctx.path_ctx).clone()
    });
    // The builtins: unless --no-builtins, the magic builtin of
    // hh_single_complete, the extra builtins (each part of each, by its
    // base name) and the hhi files.
    let mut to_decl = vec![];
    if !no_builtins {
        let magic = RelativePath::new(Prefix::Hhi, "hh_single_type_check_magic.hhi");
        ctx.files.set(magic, hh_single_complete::MAGIC_BUILTINS.as_bytes().to_vec());
        hhi_root.write_builtin("hh_single_type_check_magic.hhi", hh_single_complete::MAGIC_BUILTINS.as_bytes())?;
        let mut builtins = vec![magic];
        for filename in &extra_builtins {
            let content = read_file(filename)?;
            for (part, text) in hh::multifile::file_to_file_list(filename, &content) {
                let base = Path::new(&part).file_name().context("not a file")?.to_owned();
                let path = RelativePath::new(Prefix::Hhi, &base);
                if builtins.contains(&path) {
                    // `die "Multiple magic builtins share the same base name.\n"`
                    return Ok(die("Multiple magic builtins share the same base name.\n"));
                }
                hhi_root.write_builtin(&base.to_string_lossy(), &text)?;
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
        let content = read_file(filename)?;
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
        // NAMING PHASE 4: the forward naming table
        files_info.insert(
            relative_path::RelativePath::from(path),
            hh_single_complete::file_info_of_decls(&relative_path::RelativePath::from(path), &decls),
        );
        paths_with_addenda.push((
            relative_path::RelativePath::from(path),
            hh_single_complete::addenda_of_parse(&decls),
            hh::search_utils::FileSource::TypeChecker,
        ));
    }
    paths_with_addenda.sort_by(|(p1, _, _), (p2, _, _)| hh::relative_path::compare(p1, p2));
    paths_with_addenda.dedup_by(|(p1, _, _), (p2, _, _)| p1 == p2);
    let sienv = hh::symbol_index_core::update_from_addenda(&sienv, &paths_with_addenda);
    let input = hh_single_complete::Input {
        ctx,
        filenames: fn_ref
            .iter()
            .map(|f| RelativePath::new(Prefix::Dummy, f).into())
            .collect(),
        sienv,
        naming_table: hh::naming_table::create(files_info),
    };
    let code = hh_single_complete::handle_mode(&mode, input)?;
    Ok(ExitCode::from(code))
}

