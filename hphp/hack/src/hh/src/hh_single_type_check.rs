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
use crate::diagnostics;
use crate::relative_path;
use crate::relative_path::Prefix;

pub mod args;
pub mod modes;

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
/// [`root`], the hhi files are under `hhi_root` (see [`HhiRoot`]), and `Tmp`
/// is `tmp`. The test files themselves are `Dummy` paths, whose prefix is
/// always empty.
pub fn set_path_prefixes_with_hhi_root(root: &std::path::Path, hhi_root: &std::path::Path) {
    relative_path::set_path_prefix(Prefix::Root, root);
    relative_path::set_path_prefix(Prefix::Hhi, hhi_root);
    relative_path::set_path_prefix(Prefix::Tmp, std::path::Path::new("tmp"));
}

/// [`set_path_prefixes_with_hhi_root`] with the hhi files under `/hhi`
/// (where `Ctx` names them, in memory, when nothing is extracted): for the
/// tests that make a context without an [`HhiRoot`].
pub fn set_path_prefixes(root: &std::path::Path) {
    set_path_prefixes_with_hhi_root(root, std::path::Path::new("/hhi"))
}

/// The hhi directory of `main_hack`: `Tempfile.with_tempdir` (a directory
/// named by `Random_id.short_string` under the real path of `/tmp`) into
/// which `Hhi.set_hhi_root_for_unit_test` extracts the hhi files, and
/// `decl_and_run_mode` writes the magic and extra builtins. Every path that
/// names an hhi file is under it, and the files are there to be read (code
/// fragments of errors, services that read a file back), as in the OCaml.
/// (The checker itself reads the hhi files from the `Ctx`, in memory.) The
/// directory is removed when the guard is dropped (`try_finally`).
pub struct HhiRoot {
    pub dir: std::path::PathBuf,
    /// `--custom-hhi-path`: the directory is the user's (not extracted to,
    /// not removed).
    custom: bool,
}

impl HhiRoot {
    /// `Tempfile.mkdtemp ~skip_mocking:false` (under `Path.make
    /// Sys_utils.temp_dir_name`) and `extract_hhis` (directories made by
    /// `Sys_utils.mkdir_p`, mode 0o777, as the OCaml's).
    pub fn make() -> std::io::Result<Self> {
        let tmp = std::fs::canonicalize("/tmp")?;
        let mut retries = 30;
        let dir = loop {
            let dir = tmp.join(crate::random_id::short_string());
            match crate::sys_utils::mkdir_p(&dir.to_string_lossy()) {
                Ok(()) => break dir,
                Err(e) if retries == 0 => return Err(e),
                Err(_) => retries -= 1,
            }
        };
        let root = HhiRoot { dir, custom: false };
        // `extract_hhis dir`: `write_hhi dir (filename, contents)`.
        for (filename, contents) in hhi::HHI_CONTENTS {
            let file = root.dir.join(filename);
            if let Some(parent) = file.parent() {
                crate::sys_utils::mkdir_p(&parent.to_string_lossy())?;
            }
            std::fs::write(&file, contents.as_bytes())?;
        }
        Ok(root)
    }

    /// `Sys_utils.write_file ~file:(Path.concat hhi_root file_name)`: a magic
    /// or extra builtin (named by its base name).
    pub fn write_builtin(&self, file_name: &str, contents: &[u8]) -> std::io::Result<()> {
        std::fs::write(self.dir.join(file_name), contents)
    }

    /// `process true (Path.make hhi_root)` of `main_hack`, for
    /// `--custom-hhi-path`: `Err` with the message of its `die` when the
    /// directory does not exist.
    pub fn custom(dir: &str) -> Result<Self, String> {
        let path = std::fs::canonicalize(dir).unwrap_or_else(|_| std::path::PathBuf::from(dir));
        if path.is_dir() {
            Ok(HhiRoot { dir: path, custom: true })
        } else {
            Err(format!("Custom hhi directory {} not found", path.display()))
        }
    }
}

impl Drop for HhiRoot {
    fn drop(&mut self) {
        // `Sys_utils.rm_dir_tree`
        if !self.custom {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }
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
        crate::config_file::getters::string_opt(crate::config_keys::hhconfig::PACKAGES_CONFIG_PATH, &config);
    let enable_implicit_packages = crate::config_file::getters::bool_(
        crate::config_keys::hhconfig::ENABLE_IMPLICIT_PACKAGES,
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
            .insert(crate::typechecker_options::EXPERIMENTAL_SUPPORTDYNAMIC_TYPE_HINT.to_string());
    }
    if flags.consider_type_const_enforceable {
        tcopt.tco_legacy_experimental_features.insert(
            crate::typechecker_options::EXPERIMENTAL_CONSIDER_TYPE_CONST_ENFORCEABLE.to_string(),
        );
    }
    tcopt.tco_custom_error_config = flags
        .custom_error_config_path
        .as_deref()
        .and_then(load_and_parse_custom_error_config)
        .unwrap_or(crate::custom_error_config::EMPTY);
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
) -> (diagnostics::T, crate::package_info::T) {
    diagnostics::do_(None, || match packages_config_path {
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
    crate::decl_store::set(crate::decl_store::shared_memory_store_of_ctx(
        Arc::clone(ctx),
    ));
    diagnostics::set_allowed_fixme_codes_strict(ctx.tco.allowed_fixme_codes_strict.clone());
    diagnostics::set_code_agnostic_fixme(ctx.tco.code_agnostic_fixme);
}

/// `parse_name_and_decl` (the parsing half: `parse_and_name`): parses each
/// file, which records its parse errors and its fixmes, and gives the AST to
/// the AST provider. The shallow declarations are already in the `Ctx`;
/// then the classes of each file are folded (`Decl.make_env`).
///
/// (`Naming_global.ndecl_file_and_get_conflict_files` is not called: it
/// only binds the names in the reverse naming table and returns the conflict
/// files, which the OCaml ignores here; the names are bound by
/// `Ctx::declare_file`.)
pub fn parse_name_and_decl(ctx: &Arc<Ctx>, files: &[relative_path::T]) -> diagnostics::T {
    let (errors, ()) = diagnostics::do_(None, || {
        for fn_ in files {
            diagnostics::run_in_context(fn_.clone(), || {
                let popt = crate::provider_context::get_popt(ctx).clone();
                let contents = ctx
                    .files
                    .get(pos::RelativePath::from(fn_))
                    .unwrap_or_default();
                let parsed_file = crate::full_fidelity_ast::defensive_program(
                    None, None, None, None, popt, fn_, &contents,
                );
                crate::ast_provider::provide_ast_hint(
                    ctx,
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
    errors: diagnostics::T,
    files: &[relative_path::T],
) -> diagnostics::T {
    let mut errors = errors;
    for fn_ in files {
        let full_ast = crate::ast_provider::get_ast(true, ctx, fn_);
        let (new_errors, _tast) =
            crate::typing_check_job::calc_errors_and_tast(ctx, None, fn_, full_ast);
        errors = diagnostics::merge(errors, new_errors);
    }
    errors
}

/// `print_error format ?oc l`: renders `l` in `format` on `oc`.
pub fn print_error(
    format: diagnostics::Format,
    oc: &mut dyn std::io::Write,
    l: &diagnostics::Diagnostic,
) {
    use diagnostics::Format;
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
/// with which the test suites are run. Returns whether there were errors
/// (`Diagnostics.has_errors`).
pub fn write_error_list(
    format: diagnostics::Format,
    errors: diagnostics::T,
    oc: &mut dyn std::io::Write,
    max_errors: Option<usize>,
) -> bool {
    let has_errors = diagnostics::has_errors(None, &errors);
    let errors = diagnostics::get_sorted_diagnostic_list(None, errors);
    let (shown_errors, dropped_errors) = match max_errors {
        Some(max_errors) => errors.split_at(max_errors.min(errors.len())),
        None => (&errors[..], &[][..]),
    };
    if !errors.is_empty() {
        for e in shown_errors {
            print_error(format, oc, e);
        }
        if let Some(summary) = diagnostics::format_summary(
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

/// `print_error_list format errors max_errors`: as [`write_error_list`],
/// but the diagnostics and the summary go to stderr, and `No errors` to
/// stdout. Returns whether there were errors (`Diagnostics.has_errors`).
pub fn print_error_list(
    format: diagnostics::Format,
    errors: diagnostics::T,
    max_errors: Option<usize>,
) -> bool {
    let has_errors = diagnostics::has_errors(None, &errors);
    let errors = diagnostics::get_sorted_diagnostic_list(None, errors);
    let (shown_errors, dropped_errors) = match max_errors {
        Some(max_errors) => errors.split_at(max_errors.min(errors.len())),
        None => (&errors[..], &[][..]),
    };
    if !errors.is_empty() {
        let mut stderr = Stderr;
        for e in shown_errors {
            print_error(format, &mut stderr, e);
        }
        if let Some(summary) = diagnostics::format_summary(
            format,
            errors.len() as isize,
            0,
            Some(dropped_errors.len() as isize),
            max_errors.map(|n| n as isize),
        ) {
            output_string_stderr(summary.as_bytes());
        }
    } else {
        use std::io::Write as _;
        let _ = std::io::stdout().write_all(b"No errors\n");
    }
    has_errors
}

/// `print_errors format errors max_errors`
pub fn print_errors(
    format: diagnostics::Format,
    errors: diagnostics::T,
    max_errors: Option<usize>,
) -> bool {
    print_error_list(format, errors, max_errors)
}

// `Stdlib.stderr` is a buffered channel, flushed when the program exits after
// `stdout` (`Stdlib.flush_std_buffers`): when both go to the same pipe, what
// `hh_single_type_check` writes on stderr comes after everything it wrote on
// stdout. Rust's stderr is unbuffered, so the diagnostics written with
// `Out_channel.output_string stderr` are kept here until
// [`flush_std_buffers`].
static STDERR_BUFFER: std::sync::Mutex<Vec<u8>> = std::sync::Mutex::new(Vec::new());

/// `Out_channel.output_string stderr s` (buffered: see [`flush_std_buffers`]).
pub fn output_string_stderr(s: &[u8]) {
    STDERR_BUFFER
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .extend_from_slice(s)
}

/// `Stdlib.stderr` as an output channel (see [`output_string_stderr`]).
pub struct Stderr;

impl std::io::Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        output_string_stderr(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        flush_stderr();
        Ok(())
    }
}

/// `Out_channel.flush stderr`
pub fn flush_stderr() {
    use std::io::Write as _;
    let buffer = std::mem::take(&mut *STDERR_BUFFER.lock().unwrap_or_else(|e| e.into_inner()));
    let mut stderr = std::io::stderr().lock();
    let _ = stderr.write_all(&buffer);
    let _ = stderr.flush();
}

/// `Stdlib.flush_std_buffers` (what `exit` and the end of the program do):
/// stdout, then stderr.
pub fn flush_std_buffers() {
    use std::io::Write as _;
    let _ = std::io::stdout().flush();
    flush_stderr()
}

/// `die str`: `str` on stderr (the channel is closed, so flushed), then
/// `exit 2` (which flushes stdout).
pub fn die(s: &str) -> std::process::ExitCode {
    output_string_stderr(s.as_bytes());
    flush_stderr();
    flush_std_buffers();
    std::process::ExitCode::from(2)
}

/// The OCaml exception that a panic payload stands for, if it stands for
/// one (see `hh/PORTING.md`: `failwith` is a panic with a message), as the
/// uncaught-exception handler shows it. The panics of parts that are not
/// ported (`todo!`, `unimplemented!`) stand for none.
pub(crate) fn uncaught_of_payload(payload: &(dyn std::any::Any + Send)) -> Option<crate::rt::ocaml_exn::Uncaught> {
    use crate::rt::ocaml_exn::Uncaught;
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied());
    if let Some(msg) = message {
        if msg.starts_with("not yet implemented") || msg.starts_with("not implemented") {
            None
        } else {
            Some(Uncaught::failure(msg))
        }
    } else if let Some(u) = payload.downcast_ref::<Uncaught>() {
        Some(u.clone())
    } else if let Some(crate::full_fidelity_ast::Failure(msg)) = payload.downcast_ref() {
        Some(Uncaught::failure(msg.clone()))
    } else if let Some(crate::sys_utils::SysError(msg)) = payload.downcast_ref() {
        Some(Uncaught::sys_error(msg.clone()))
    } else if let Some(p) = payload.downcast_ref::<crate::full_fidelity_source_text::PositionNotFound>() {
        Some(Uncaught::Printexc(format!(
            "Line_break_map.Position_not_found({}, {}, {})",
            p.line, p.column, p.num_lines_in_file
        )))
    } else if let Some(e) = payload.downcast_ref::<crate::decl_defs::DeclNotFound>() {
        Some(Uncaught::Printexc(e.to_string()))
    } else {
        None
    }
}

/// The top level of `hh_single_type_check` and `hh_single_complete`: an
/// exception that nothing catches (an error value of [`Uncaught`], or a
/// panic that stands for an OCaml exception) is printed by Base's handler
/// (`Exn.print_with_backtrace`, after `Stdlib.do_at_exit`), and the program
/// exits with 2; `die`'s error ([`Die`]) prints its message and exits with
/// 2. The OCaml's backtrace (its own call stack) is not printed.
///
/// [`Uncaught`]: crate::rt::ocaml_exn::Uncaught
/// [`Die`]: crate::rt::ocaml_exn::Die
pub fn handle_uncaught(
    f: impl FnOnce() -> anyhow::Result<std::process::ExitCode>,
) -> anyhow::Result<std::process::ExitCode> {
    use crate::rt::ocaml_exn::Die;
    use crate::rt::ocaml_exn::Uncaught;
    let reported = |payload: &(dyn std::any::Any + Send)| uncaught_of_payload(payload).is_some();
    let exn = match crate::rt::quiet_panic::catch_reported(reported, f) {
        Ok(Ok(code)) => {
            flush_std_buffers();
            return Ok(code);
        }
        Ok(Err(err)) => {
            if let Some(exn) = err.downcast_ref::<Uncaught>() {
                exn.clone()
            } else if let Some(Die(msg)) = err.downcast_ref::<Die>() {
                return Ok(die(msg));
            } else if let Some(crate::sys_utils::SysError(msg)) = err.downcast_ref() {
                Uncaught::sys_error(msg.clone())
            } else {
                flush_std_buffers();
                return Err(err);
            }
        }
        Err(payload) => match uncaught_of_payload(&*payload) {
            Some(exn) => exn,
            None => {
                flush_std_buffers();
                std::panic::resume_unwind(payload)
            }
        },
    };
    flush_std_buffers();
    crate::rt::ocaml_exn::print_with_backtrace(&exn, &mut std::io::stderr());
    Ok(std::process::ExitCode::from(2))
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
        assert!(features.contains(crate::typechecker_options::EXPERIMENTAL_SUPPORTDYNAMIC_TYPE_HINT));
        assert!(features.contains(
            crate::typechecker_options::EXPERIMENTAL_CONSIDER_TYPE_CONST_ENFORCEABLE
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

    /// The panics that stand for an OCaml exception (`failwith`, the
    /// exceptions with a payload type of their own), and those that do not.
    #[test]
    fn uncaught_exceptions() {
        use crate::rt::ocaml_exn::Uncaught;
        let of = |p: Box<dyn std::any::Any + Send>| uncaught_of_payload(&*p);
        assert_eq!(
            of(Box::new("Not a Hack file: a.php".to_string())),
            Some(Uncaught::failure("Not a Hack file: a.php"))
        );
        assert_eq!(of(Box::new("msg")), Some(Uncaught::failure("msg")));
        assert_eq!(
            of(Box::new(crate::sys_utils::SysError("a: No such file or directory".to_string()))),
            Some(Uncaught::sys_error("a: No such file or directory"))
        );
        assert_eq!(of(Box::new(Uncaught::not_found())), Some(Uncaught::not_found()));
        assert_eq!(of(Box::new("not yet implemented: X".to_string())), None);
        assert_eq!(of(Box::new(3)), None);
        // An error value of `Uncaught` or a panic: exit 2 (the message is
        // on stderr).
        assert_eq!(
            handle_uncaught(|| Err(Uncaught::failure("x").into())).unwrap(),
            std::process::ExitCode::from(2)
        );
        assert_eq!(
            handle_uncaught(|| std::panic::panic_any(Uncaught::failure("x"))).unwrap(),
            std::process::ExitCode::from(2)
        );
        // Other errors go on.
        assert!(handle_uncaught(|| Err(anyhow::anyhow!("other"))).is_err());
    }

    /// What goes to stderr waits for stdout, as with OCaml's buffered
    /// channels.
    #[test]
    fn stderr_is_buffered_until_flushed() {
        output_string_stderr(b"");
        let before = STDERR_BUFFER.lock().unwrap().len();
        output_string_stderr(b"x");
        assert_eq!(STDERR_BUFFER.lock().unwrap().len(), before + 1);
        flush_stderr();
        assert!(STDERR_BUFFER.lock().unwrap().is_empty());
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
