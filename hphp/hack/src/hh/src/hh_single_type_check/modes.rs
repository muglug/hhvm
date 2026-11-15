// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the mode dispatch of `hh_single_type_check.ml` (`type mode`,
//! `handle_mode`, the caret helpers): one arm per mode, calling the owner's
//! `pub fn`. The command lines are `src/hh_single_cli.rs` (a module of the
//! `hh` binary), which parses the flags into a [`Mode`], sets up the context
//! as `decl_and_run_mode` does and calls [`handle_mode`] (or
//! `crate::hh_single_complete::handle_mode`) for every mode but `Errors`.
//!
//! A mode whose service is not ported yet fails with "mode not ported:
//! FLAG" on stderr and exit code 2 (as an unknown option of
//! `hh single` would fail), see [`not_ported`]; its glue (how the context
//! and the entry are made, how the result is printed) is already written,
//! inside a `#[cfg(any())]` block that is enabled when its service is
//! ported. [`MODES`] lists the modes and their suites.

use crate::rt::ocaml_exn::Die;
use crate::rt::ocaml_exn::Sexp;
use crate::rt::ocaml_exn::Uncaught;
use crate::diagnostics;
use crate::file_content::Range;
use crate::file_content::position;
use crate::provider_context;
use crate::relative_path;

/// `type mode` of `hh_single_type_check.ml`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    CstSearch,
    DumpSymbolInfo,
    RunSimpliHack,
    GleanIndex(String),
    GleanSymHash,
    DumpInheritance,
    Errors,
    Lint,
    LintJson,
    DumpDeps,
    DumpDepHashes,
    GetSomeFileDeps {
        depth: isize,
        full_hierarchy: bool,
    },
    IdentifySymbol(position::T),
    IdeCodeActions {
        title_prefix: String,
        use_snippet_edits: bool,
    },
    IdeDiagnostics,
    IdeSignatureHelp,
    FindLocal(position::T),
    GetMember(String),
    Outline,
    OutlineForAgents,
    DumpNast,
    DumpStrippedTast,
    DumpTast,
    FindRefs(position::T),
    HighlightRefs(position::T),
    GoToImpl(position::T),
    Hover(Option<position::T>),
    Enforcement(Option<position::T>),
    EnforcementBatch,
    ApplyQuickfixes,
    RefactorSoundDynamic(String, String, String),
    RemoveDeadUnsafeCasts,
    CountImpreciseTypes,
    MapReduceMode,
    DumpClassishPositions,
    DumpDynamicInference {
        as_data: bool,
    },
}

/// One row of the table of modes: the flag that selects the mode (the first
/// one, for modes with several), the suite under `hphp/hack/test` that tests
/// it, and the functions the glue calls.
pub struct ModeInfo {
    pub flag: &'static str,
    pub suite: &'static str,
    pub calls: &'static str,
}

/// The modes of `hh_single_type_check` and `hh_single_complete`, in the
/// order of their options.
pub const MODES: &[ModeInfo] = &[
    ModeInfo { flag: "--refactor-sound-dynamic", suite: "refactor_sd", calls: "Refactor_sd.do_" },
    ModeInfo { flag: "--cst-search", suite: "cst_search", calls: "Cst_search_service.{compile_pattern,search,result_to_json}" },
    ModeInfo { flag: "--dump-symbol-info", suite: "dumpsymbolinfo", calls: "Symbol_info_service_utils.{helper,format_result}" },
    ModeInfo { flag: "--run-simplihack", suite: "simplihack", calls: "Simplihack_prompt.find" },
    ModeInfo { flag: "--glean-index", suite: "", calls: "Write_symbol_info.Entrypoint.index_files" },
    ModeInfo { flag: "--glean-sym-hash", suite: "", calls: "Write_symbol_info.Entrypoint.sym_hashes" },
    ModeInfo { flag: "--lint", suite: "lint", calls: "Linting_main.lint, Server_lint_types.output_text" },
    ModeInfo { flag: "--lint-json", suite: "quickfix_lint", calls: "Linting_main.lint, Server_lint_types.output_json" },
    ModeInfo { flag: "--dump-deps", suite: "deps", calls: "Typing_deps.add_dependency_callback" },
    ModeInfo { flag: "--dump-dep-hashes", suite: "", calls: "Dep_hash_to_symbol.dump" },
    ModeInfo { flag: "--dump-inheritance", suite: "dump_inheritance", calls: "Method_jumps.get_inheritance, print_readable" },
    ModeInfo { flag: "--get-some-file-deps", suite: "", calls: "File_deps.traverse_file_dependencies" },
    ModeInfo { flag: "--ide-code-actions", suite: "ide_code_actions", calls: "Code_actions_cli_lib.run" },
    ModeInfo { flag: "--ide-diagnostics", suite: "ide_diagnostics", calls: "Ide_diagnostics_cli_lib.run" },
    ModeInfo { flag: "--ide-signature-help", suite: "ide_signature_help", calls: "Server_signature_help.go_quarantined, Lsp_fmt.print_signatureHelp" },
    ModeInfo { flag: "--dump-classish-positions", suite: "classish_positions", calls: "Classish_positions_cli_lib.dump" },
    ModeInfo { flag: "--identify-symbol", suite: "identify_symbol", calls: "Server_identify_function.go_quarantined_absolute, File_outline.print_def" },
    ModeInfo { flag: "--find-local", suite: "find_local", calls: "Server_find_locals.go" },
    ModeInfo { flag: "--outline", suite: "outline", calls: "File_outline.{outline,print}" },
    ModeInfo { flag: "--outline-for-agents", suite: "outline_for_agents", calls: "Outline_for_agents.outline" },
    ModeInfo { flag: "--nast", suite: "nast", calls: "Naming.program, Naming_ast_print.print_nast" },
    ModeInfo { flag: "--tast", suite: "tast, holes", calls: "Typing_toplevel.nast_to_tast, Tast_expand, Typing_ast_print.print_tast" },
    ModeInfo { flag: "--infer-dynamic", suite: "infer_dynamic", calls: "Typing_shadow_solver.{solve,solution_to_json}" },
    ModeInfo { flag: "--stripped-tast", suite: "", calls: "Tast.to_nast, Nast.show_program" },
    ModeInfo { flag: "--find-refs", suite: "find_refs", calls: "Server_find_refs.{go_from_file_ctx,go,to_absolute}, Find_refs_wire_format.CliHumanReadable.print_results" },
    ModeInfo { flag: "--go-to-impl", suite: "go_to_impl", calls: "Server_find_refs.go_from_file_ctx, Server_go_to_impl.go" },
    ModeInfo { flag: "--highlight-refs", suite: "highlight_refs", calls: "Ide_highlight_refs.go_quarantined" },
    ModeInfo { flag: "--get-member", suite: "", calls: "Decl_provider.get_class, Typing_print.full_strip_ns_decl" },
    ModeInfo { flag: "--hover", suite: "hover", calls: "Ide_hover.go_quarantined, Hover_service.as_marked_string_list" },
    ModeInfo { flag: "--enforcement", suite: "enforcement", calls: "Server_enforcement_at_pos.go_ctx" },
    ModeInfo { flag: "--enforcement-at-caret-batch", suite: "enforcement_batch", calls: "Server_enforcement_at_pos.go_ctx" },
    ModeInfo { flag: "--fix", suite: "quickfixes", calls: "Eager_quickfix_test_util.{of_quickfix,apply_all}" },
    ModeInfo { flag: "--remove-dead-unsafe-casts", suite: "remove_dead_unsafe_casts", calls: "Remove_dead_unsafe_casts.get_patches, codemod" },
    ModeInfo { flag: "--count-imprecise-types", suite: "count_imprecise_types", calls: "Count_imprecise_types.{count,json_of_results}" },
    ModeInfo { flag: "--map-reduce", suite: "map_reduce", calls: "Map_reduce.{map,reduce,to_ffi}" },
    // hh_single_complete (`hh single-complete`)
    ModeInfo { flag: "--auto-complete", suite: "autocomplete", calls: "Server_auto_complete.{get_autocomplete_context,go_at_auto332_ctx}" },
    ModeInfo { flag: "--resolve", suite: "", calls: "Server_auto_complete.{go_at_auto332_ctx,get_signature}" },
    ModeInfo { flag: "--xhp-close", suite: "autoclose", calls: "Autoclose_tags.go_xhp_close_tag" },
    ModeInfo { flag: "--search", suite: "", calls: "Ide_search.go" },
    ModeInfo { flag: "--auto-complete-show-glean", suite: "", calls: "Glean_autocomplete_query.make_symbols_query" },
    ModeInfo { flag: "--search-show-glean", suite: "", calls: "Glean_autocomplete_query.make_symbols_query" },
    ModeInfo { flag: "--find-refs-show-glean", suite: "", calls: "Glean_autocomplete_query.make_refs_query" },
];

/// The flag of a mode, for [`not_ported`].
fn flag_of_mode(mode: &Mode) -> &'static str {
    let flag = match mode {
        Mode::RefactorSoundDynamic(..) => "--refactor-sound-dynamic",
        Mode::CstSearch => "--cst-search",
        Mode::DumpSymbolInfo => "--dump-symbol-info",
        Mode::RunSimpliHack => "--run-simplihack",
        Mode::GleanIndex(_) => "--glean-index",
        Mode::GleanSymHash => "--glean-sym-hash",
        Mode::Errors => "",
        Mode::Lint => "--lint",
        Mode::LintJson => "--lint-json",
        Mode::DumpDeps => "--dump-deps",
        Mode::DumpDepHashes => "--dump-dep-hashes",
        Mode::DumpInheritance => "--dump-inheritance",
        Mode::GetSomeFileDeps { .. } => "--get-some-file-deps",
        Mode::IdeCodeActions { .. } => "--ide-code-actions",
        Mode::IdeDiagnostics => "--ide-diagnostics",
        Mode::IdeSignatureHelp => "--ide-signature-help",
        Mode::DumpClassishPositions => "--dump-classish-positions",
        Mode::IdentifySymbol(_) => "--identify-symbol",
        Mode::FindLocal(_) => "--find-local",
        Mode::Outline => "--outline",
        Mode::OutlineForAgents => "--outline-for-agents",
        Mode::DumpNast => "--nast",
        Mode::DumpTast => "--tast",
        Mode::DumpDynamicInference { .. } => "--infer-dynamic",
        Mode::DumpStrippedTast => "--stripped-tast",
        Mode::FindRefs(_) => "--find-refs",
        Mode::GoToImpl(_) => "--go-to-impl",
        Mode::HighlightRefs(_) => "--highlight-refs",
        Mode::GetMember(_) => "--get-member",
        Mode::Hover(_) => "--hover",
        Mode::Enforcement(_) => "--enforcement",
        Mode::EnforcementBatch => "--enforcement-at-caret-batch",
        Mode::ApplyQuickfixes => "--fix",
        Mode::RemoveDeadUnsafeCasts => "--remove-dead-unsafe-casts",
        Mode::CountImpreciseTypes => "--count-imprecise-types",
        Mode::MapReduceMode => "--map-reduce",
    };
    flag
}

/// The error of a mode whose service is not ported yet: `hh` prints it as
/// `hh: mode not ported: FLAG` on stderr and exits with 2, as for a flag it
/// cannot parse. The suite runner (`hh/suite.py`) counts the tests that end
/// so as "not-ported".
pub fn not_ported(flag: &str) -> anyhow::Error {
    anyhow::anyhow!("mode not ported: {flag}")
}

fn mode_not_ported(mode: &Mode) -> anyhow::Error {
    not_ported(flag_of_mode(mode))
}

// ---------------------------------------------------------------------------
// Positions given by markers in the source (`caret_pos` and friends)

fn is_substring(line: &[u8], marker: &str) -> bool {
    let marker = marker.as_bytes();
    marker.is_empty() || line.windows(marker.len()).any(|w| w == marker)
}

/// `caret_pos src marker`: the position the `^` of the first line that
/// contains `marker` points at. The line is the 0-based index of the marker
/// line, given as one-based: the line *above* the marker. (The OCaml raises
/// `Option.value_exn` when the line has no `^`.)
pub fn caret_pos(src: &[u8], marker: &str) -> Option<position::T> {
    let (line_num, line_src) = crate::rt::ocaml_string::split_lines_bytes(src)
        .into_iter()
        .enumerate()
        .find(|(_, line)| is_substring(line, marker))?;
    let col_num = line_src
        .iter()
        .position(|&c| c == b'^')
        .unwrap_or_else(|| {
            // `Option.value_exn` (no message)
            std::panic::panic_any(Uncaught::Sexp(Sexp::List(vec![
                Sexp::Atom("Not_found_s".to_string()),
                Sexp::Atom("Option.value_exn None".to_string()),
            ])))
        });
    Some(position::from_one_based(line_num as isize, col_num as isize + 1))
}

/// `caret_pos_exn`: given source code containing a caret marker (e.g.
/// `"^ hover-at-caret"`), the line and column of the position indicated.
pub fn caret_pos_exn(src: &[u8], marker: &str) -> anyhow::Result<position::T> {
    caret_pos(src, marker).ok_or_else(|| {
        // `Option.value_exn ~message`
        Uncaught::error(format!(
            "Could not find any occurrence of '{}' in source code",
            marker
        ))
        .into()
    })
}

/// `all_caret_positions`: like [`caret_pos`], for every line that contains
/// the marker (and a `^`).
pub fn all_caret_positions(src: &[u8], marker: &str) -> Vec<position::T> {
    crate::rt::ocaml_string::split_lines_bytes(src)
        .into_iter()
        .enumerate()
        .filter_map(|(line_num, line_src)| {
            if is_substring(line_src, marker) {
                line_src
                    .iter()
                    .position(|&c| c == b'^')
                    .map(|col| position::from_one_based(line_num as isize, col as isize + 1))
            } else {
                None
            }
        })
        .collect()
}

/// `find_ide_range_exn`: the range between `/*range-start*/` and
/// `/*range-end*/`, else the empty range at `^ at-caret`. (`Ide_api_types`
/// `range` is `File_content.range`, the same record.)
pub fn find_ide_range_exn(src: &[u8]) -> anyhow::Result<Range> {
    let start_marker = "/*range-start*/";
    let end_marker = "/*range-end*/";
    let hover_at_caret_marker = "^ at-caret";
    let lines = crate::rt::ocaml_string::split_lines_bytes(src);
    let find_marker = |marker: &str, after: bool| -> Option<position::T> {
        let (line, src) = lines
            .iter()
            .enumerate()
            .find(|(_, l)| is_substring(l, marker))?;
        let m = marker.as_bytes();
        // `Str.search_forward (Str.regexp_string marker) start_line_src 0`
        let marker_start = src.windows(m.len()).position(|w| w == m)?;
        let column = if after {
            marker_start + m.len()
        } else {
            marker_start
        };
        Some(position::from_zero_based(line as isize, column as isize))
    };
    let from_comments = find_marker(start_marker, true)
        .and_then(|st| find_marker(end_marker, false).map(|ed| Range { st, ed }));
    match from_comments {
        Some(r) => Ok(r),
        None => caret_pos(src, hover_at_caret_marker)
            .map(|st| Range { st, ed: st })
            .ok_or_else(|| {
                anyhow::Error::from(Uncaught::error(format!(
                    "could not find pair '{}','{}' nor '{}'",
                    start_marker,
                    end_marker,
                    hover_at_caret_marker
                )))
            }),
    }
}

// ---------------------------------------------------------------------------
// handle_mode

/// What `decl_and_run_mode` gives `handle_mode`.
pub struct Input {
    /// `ctx`, after `parse_name_and_decl` of `to_decl`.
    pub ctx: provider_context::T,
    /// `filenames`: the files of the command line (as `Relative_path`s), in
    /// the order of `fn_ref` (the reverse of the command line).
    pub filenames: Vec<relative_path::T>,
    /// The keys of `builtins` (the hhi files, the magic builtins and the
    /// extra builtins).
    pub builtins: Vec<relative_path::T>,
    /// `files_contents`: the files the multifiles of `filenames` simulate,
    /// with their contents, sorted by path (a `Relative_path.Map`).
    pub files_contents: Vec<(relative_path::T, bstr::BString)>,
    /// The keys of `files_info`: the files `parse_name_and_decl` declared
    /// (the builtins and the files), sorted (a `Relative_path.Map`).
    pub files_info: Vec<relative_path::T>,
    /// `parse_errors`: the errors of `parse_name_and_decl` (and of the
    /// package config).
    pub parse_errors: diagnostics::T,
    pub max_errors: Option<usize>,
    pub error_format: diagnostics::Format,
    pub batch_mode: bool,
    pub out_extension: String,
    pub should_print_position: bool,
}

/// The exit code of a mode that does not `exit` itself.
pub const OK: u8 = 0;

impl Input {
    /// `expect_single_file ()`
    fn expect_single_file(&self) -> anyhow::Result<relative_path::T> {
        match self.filenames.as_slice() {
            [x] => Ok(x.clone()),
            // `die "Only single file expected"`: no newline, exit 2.
            _ => Err(Die("Only single file expected".to_string()).into()),
        }
    }
}

/// `handle_mode`: runs a mode other than `Errors` (which `hh_single_cli.rs`
/// runs itself, unchanged), and gives the exit code.
pub fn handle_mode(mode: &Mode, input: Input) -> anyhow::Result<u8> {
    #[allow(unused_variables)]
    let Input {
        ref ctx,
        ref filenames,
        ref builtins,
        ref files_contents,
        ref files_info,
        ref parse_errors,
        max_errors,
        error_format,
        batch_mode,
        ref out_extension,
        should_print_position,
    } = input;
    match mode {
        Mode::Errors => unreachable!("hh_single_cli runs the Errors mode"),
        Mode::IdentifySymbol(pos) => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            {
                // TODO(ljw): surely this doesn't need quarantine?
                let result = crate::provider_utils::respect_but_quarantine_unsaved_changes(
                    &ctx,
                    || crate::server_identify_function::go_quarantined_absolute(&ctx, &entry, pos),
                );
                if result.is_empty() {
                    println!("None")
                } else {
                    crate::client_get_definition::print_readable(Some(true), &result)
                }
                return Ok(OK);
            }
        }
        Mode::IdeCodeActions {
            title_prefix,
            use_snippet_edits,
        } => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let src = provider_context::read_file_contents_exn(&entry);
            let range = find_ide_range_exn(&src)?;
            // (The code actions are `server`-only, as the `Lsp` types.)
            #[cfg(feature = "server")]
            {
                crate::code_actions::code_actions_cli_lib::run(
                    &ctx,
                    crate::tast_provider::ErrorFilter::default(),
                    &entry,
                    crate::ide_api_types::ide_range_from_fc(&range),
                    title_prefix,
                    *use_snippet_edits,
                );
                Ok(OK)
            }
            #[cfg(not(feature = "server"))]
            {
                let _ = (ctx, entry, range, title_prefix, use_snippet_edits);
                Err(mode_not_ported(mode))
            }
        }
        Mode::IdeSignatureHelp => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let src = provider_context::read_file_contents_exn(&entry);
            let pos = caret_pos_exn(&src, "^ at-caret")?;
            {
                let result = crate::server_signature_help::go_quarantined(&ctx, &entry, &pos);
                println!("textDocument/signatureHelp response:\n");
                println!(
                    "{}",
                    crate::yojson::safe::pretty_to_string(&crate::lsp_fmt::print_signature_help(
                        &result
                    ))
                );
                Ok(OK)
            }
        }
        Mode::FindLocal(pos) => {
            let filename = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, filename);
            let result = crate::server_find_locals::go(&ctx, &entry, pos);
            for pos in result {
                println!("{}", crate::pos::string_no_file(&pos));
            }
            Ok(OK)
        }
        Mode::Outline => {
            for filename in filenames {
                // `cat (Relative_path.to_absolute filename)`
                let file = std::fs::read(relative_path::to_absolute(filename))?;
                let results = crate::file_outline::outline(provider_context::get_popt(ctx), &file);
                crate::file_outline::print(Some(true), &results);
            }
            Ok(OK)
        }
        Mode::OutlineForAgents => {
            for filename in filenames {
                let file = std::fs::read(relative_path::to_absolute(filename))?;
                let result = crate::outline_for_agents::outline(&file);
                // `print_string result` (the bytes of the outline)
                {
                    use std::io::Write as _;
                    std::io::stdout().write_all(&result)?;
                }
            }
            Ok(OK)
        }
        Mode::HighlightRefs(pos) => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let results = crate::ide_highlight_refs::go_quarantined(&ctx, &entry, pos);
            crate::client_highlight_refs::go(&results, false);
            Ok(OK)
        }
        Mode::Hover(pos_given) if batch_mode && pos_given.is_none() => {
            // `Hover None when batch_mode`: each file's hover is written to
            // `<file><out_extension>`.
            for filename in filenames {
                let out = format!("{}{}", relative_path::to_absolute(filename), out_extension);
                let mut oc = std::fs::File::create(out)?;
                // `Typing_log.out_channel := oc`
                let log_oc = oc.try_clone()?;
                crate::typing_log::OUT_CHANNEL.with(|c| *c.borrow_mut() = Box::new(log_oc));
                crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, || {
                    do_hover(ctx, filename.clone(), &mut oc, None)
                })?;
            }
            Ok(OK)
        }
        Mode::Hover(pos_given) => {
            let filename = input.expect_single_file()?;
            do_hover(ctx, filename, &mut std::io::stdout().lock(), *pos_given)?;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::FindRefs(pos) => {
            let path = input.expect_single_file()?;
            find_refs_modes::find_refs(&input, path, pos)?;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::GoToImpl(pos) => {
            let filename = input.expect_single_file()?;
            find_refs_modes::go_to_impl(&input, filename, pos)?;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::DumpInheritance => {
            find_refs_modes::dump_inheritance(&input)?;
            Ok(OK)
        }
        #[cfg(not(feature = "server"))]
        Mode::FindRefs(_) | Mode::GoToImpl(_) => {
            // (`Server_find_refs` and `Server_go_to_impl` are behind `server`.)
            let _ = input.expect_single_file()?;
            Err(mode_not_ported(mode))
        }
        Mode::Lint | Mode::LintJson => {
            // `Linting_main.lint ctx fn content` for each of
            // `files_contents`, in `Lints_core.do_`; sorted by position;
            // `Server_lint_types.output_text stdout lint_errors error_format`
            // and `exit 2` (or "No lint errors"); `--lint-json`:
            // `output_json ~from_test:true ~pretty:true` and `exit 2`.
            // (`Server_lint_types` is behind `server`.)
            #[cfg(feature = "server")]
            {
                let files_contents: Vec<(relative_path::T, Vec<u8>)> = files_contents
                    .iter()
                    .map(|(fn_, content)| (fn_.clone(), content.to_vec()))
                    .collect();
                let code = hh_single_lint(
                    ctx,
                    &files_contents,
                    matches!(mode, Mode::LintJson),
                    error_format,
                    &mut std::io::stdout().lock(),
                );
                return Ok(code as u8);
            }
            #[allow(unreachable_code)]
            Err(mode_not_ported(mode))
        }
        Mode::Enforcement(None) if batch_mode => {
            for filename in filenames {
                let out = format!("{}{}", relative_path::to_absolute(filename), out_extension);
                let mut oc = std::fs::File::create(out)?;
                // `Typing_log.out_channel := oc`
                let log_oc = oc.try_clone()?;
                crate::typing_log::OUT_CHANNEL.with(|c| *c.borrow_mut() = Box::new(log_oc));
                crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, || {
                    do_enforcement(ctx, filename.clone(), &mut oc, None)
                })?;
            }
            Ok(OK)
        }
        Mode::Enforcement(pos_given) => {
            let filename = input.expect_single_file()?;
            do_enforcement(ctx, filename, &mut std::io::stdout().lock(), *pos_given)?;
            Ok(OK)
        }
        Mode::EnforcementBatch if batch_mode => {
            for filename in filenames {
                let out = format!("{}{}", relative_path::to_absolute(filename), out_extension);
                let mut oc = std::fs::File::create(out)?;
                // `Typing_log.out_channel := oc`
                let log_oc = oc.try_clone()?;
                crate::typing_log::OUT_CHANNEL.with(|c| *c.borrow_mut() = Box::new(log_oc));
                crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, || {
                    do_enforcement_batch(ctx, filename.clone(), &mut oc)
                })?;
            }
            Ok(OK)
        }
        Mode::EnforcementBatch => {
            let filename = input.expect_single_file()?;
            do_enforcement_batch(ctx, filename, &mut std::io::stdout().lock())?;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::DumpClassishPositions => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            crate::classish_positions_cli_lib::dump(&ctx, &entry, &path);
            Ok(OK)
        }
        Mode::ApplyQuickfixes => {
            let path = input.expect_single_file()?;
            let (ctx, _entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let (errors, _) = compute_tasts(Some(false), &ctx, files_info, files_contents);
            // `Relative_path.Map.find files_contents path`
            let src = match files_contents.iter().find(|(p, _)| *p == path) {
                Some((_, src)) => src.clone(),
                None => return Err(Uncaught::not_found().into()),
            };
            let quickfixes: Vec<_> = diagnostics::get_diagnostic_list(Some(false), errors)
                .iter()
                // If an error has multiple possible quickfixes, take the first.
                .filter_map(|e| crate::user_diagnostic::quickfixes(e).into_iter().next())
                .collect();
            // Print the title of each quickfix, so we can see text changes in tests.
            for qf in &quickfixes {
                println!("{}", qf.title);
            }
            let mut eagers = vec![];
            let mut rejected_titles = vec![];
            for qf in &quickfixes {
                match eager_quickfix_test_util::of_quickfix(qf) {
                    Some(eager_qf) => eagers.push(eager_qf),
                    None => rejected_titles.push(qf.title.clone()),
                }
            }
            if !rejected_titles.is_empty() {
                print!(
                    "The following quickfixes could not be applied with --fix.\n{}\n{}",
                    rejected_titles.join("\n"),
                    " Use hh_single_type_check --ide-code-actions to handle non-eager quickfixes"
                );
            }
            // Print the source code after applying all these quickfixes.
            use std::io::Write;
            let mut out = std::io::stdout().lock();
            out.write_all(b"\n")?;
            out.write_all(&eager_quickfix_test_util::apply_all(&src, eagers)?)?;
            Ok(OK)
        }
        Mode::CstSearch => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            // `Sys_utils.read_stdin_to_string () |> Yojson.Safe.from_string`
            let mut stdin = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut stdin)?;
            let json = crate::yojson::safe::from_string(&stdin)
                .map_err(|e| Uncaught::Printexc(e.to_string()))?;
            let result = crate::cst_search_service::compile_pattern(&ctx, &json).map(|pattern| {
                let result = crate::cst_search_service::search(&ctx, &entry, &pattern);
                crate::yojson::safe::pretty_to_string(&crate::cst_search_service::result_to_json(
                    true,
                    result.as_ref(),
                ))
            });
            match result {
                Ok(result) => {
                    println!("{}", result);
                    Ok(OK)
                }
                Err(message) => {
                    println!("{}", message);
                    Ok(1)
                }
            }
        }
        Mode::DumpDynamicInference { as_data } => {
            let ctx = &provider_context::map_tcopt(ctx, |mut tcopt| {
                tcopt.tco_dynamic_inference = true;
                tcopt
            });
            let (_errors, tasts) = compute_tasts(None, ctx, files_info, files_contents);
            let print_json = |json: &crate::yojson::safe::T| {
                println!("{}", crate::yojson::safe::pretty_to_string(json))
            };
            let solve_def = |name: String, env: &crate::tast_env::Env| {
                let inf_env = &env.inference_env;
                let dynamic_locals: &[crate::tast::DynamicLocalInfo] = match &env.fun_tast_info {
                    Some(info) => &info.dynamic_locals,
                    None => &[],
                };
                let solutions =
                    crate::typing_shadow_solver::solve(*as_data, env, inf_env, dynamic_locals);
                print_json(&crate::yojson::safe::T::Assoc(vec![
                    ("function".to_string(), crate::yojson::safe::T::String(name)),
                    (
                        "solutions".to_string(),
                        crate::yojson::safe::T::List(
                            solutions
                                .iter()
                                .map(|s| crate::typing_shadow_solver::solution_to_json(env, s))
                                .collect(),
                        ),
                    ),
                ]))
            };
            for (_fn, tast) in &tasts {
                for def in tast {
                    match def {
                        oxidized::aast::Def::Fun(fd) => {
                            let env = crate::tast_env::def_env(ctx, def);
                            solve_def(fd.name.1.clone(), &env)
                        }
                        oxidized::aast::Def::Class(c) => {
                            let class_env = crate::tast_env::def_env(ctx, def);
                            let class_name = &c.name.1;
                            for m in &c.methods {
                                let mut env = class_env.clone();
                                crate::tast_env::restore_method_env(&mut env, m);
                                let name = format!("{}::{}", class_name, m.name.1);
                                solve_def(name, &env)
                            }
                        }
                        _ => {}
                    }
                }
            }
            Ok(OK)
        }
        Mode::DumpNast => {
            let (errors, nasts) =
                diagnostics::do_(None, || create_nasts(ctx, files_info));
            print_errors_if_present(errors);
            print_nasts(
                should_print_position,
                &nasts,
                // `Relative_path.Map.keys` (a fold that conses: the keys in
                // decreasing order)
                files_contents.iter().rev().map(|(p, _)| p),
            );
            Ok(OK)
        }
        Mode::DumpTast => {
            let (errors, tasts) = compute_tasts_expand_types(ctx, files_info, files_contents);
            print_errors_if_present(diagnostics::merge(parse_errors.clone(), errors));
            print_tasts(should_print_position, tasts, ctx);
            Ok(OK)
        }
        Mode::DumpStrippedTast => {
            for filename in filenames {
                let files_contents: Vec<(relative_path::T, bstr::BString)> = files_contents
                    .iter()
                    .filter(|(k, _)| k == filename)
                    .cloned()
                    .collect();
                let (_, tasts) = compute_tasts(None, ctx, files_info, &files_contents);
                // `Relative_path.Map.find tasts filename`
                let tast = match tasts.into_iter().find(|(k, _)| k == filename) {
                    Some((_, tast)) => tast,
                    None => return Err(Uncaught::not_found().into()),
                };
                let nast = crate::tast::to_nast(oxidized::aast::Program(tast));
                // `Nast.show_program nast`: `Format.asprintf "%a"`, so the
                // default margin.
                let shown = crate::format::asprintf(|fmt| {
                    let unit = |fmt: &mut crate::format::Formatter, _: &()| {
                        crate::format::pp_print_string(fmt, "()")
                    };
                    let mut p = crate::ast_show::P::new(fmt, &unit, &unit);
                    crate::ast_show::aast_defs::pp_program(&mut p, &nast)
                });
                println!("{}", shown);
            }
            Ok(OK)
        }
        Mode::RefactorSoundDynamic(analysis_mode, refactor_mode, element_name) => {
            use crate::refactor_sd;
            let opts = match (
                refactor_sd::refactor_sd_options::parse_analysis_mode(analysis_mode),
                refactor_sd::refactor_sd_options::parse_refactor_mode(refactor_mode),
            ) {
                (Some(analysis_mode), Some(refactor_mode)) => refactor_sd::refactor_sd_options::mk(analysis_mode, refactor_mode),
                (None, _) => return Err(Die("invalid refactor_sd analysis mode".to_string()).into()),
                (_, None) => return Err(Die("invalid refactor_sd refactor mode".to_string()).into()),
            };
            handle_constraint_mode(
                |opts, ctx, tast| refactor_sd::do_(element_name, opts, ctx, tast),
                "Sound Dynamic",
                &opts,
                ctx,
                error_format,
                filenames,
            )?;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::MapReduceMode => {
            if crate::map_reduce::not_ported(&provider_context::get_tcopt(ctx)).is_some() {
                return Err(mode_not_ported(mode));
            }
            // `compute_tasts_by_name ctx files_info files_contents`
            let (nast_errors, nasts) =
                diagnostics::do_(Some(true), || compute_nasts(ctx, files_info, files_contents));
            let mut errors = nast_errors;
            let mut tasts = vec![];
            for (fn_, full_ast) in nasts {
                let (tast_errors, by_names) =
                    crate::typing_check_job::calc_errors_and_tast(ctx, Some(true), &fn_, full_ast);
                errors = diagnostics::merge(errors, tast_errors);
                tasts.push((fn_, by_names));
            }
            print_errors_if_present(diagnostics::merge(parse_errors.clone(), errors.clone()));
            let reduced = tasts
                .iter()
                .map(|(fn_, tasts)| crate::map_reduce::map(ctx, fn_, tasts, &errors))
                .fold(crate::map_reduce::empty(), crate::map_reduce::reduce);
            let json = crate::map_reduce::yojson_of_t(&reduced);
            print!("{}", crate::yojson::safe::pretty_to_string(&json));
            Ok(OK)
        }
        Mode::DumpDeps => {
            for fn_ in files_info {
                let full_ast = crate::ast_provider::get_ast(true, ctx, fn_);
                let _ = crate::typing_check_job::calc_errors_and_tast(ctx, None, fn_, full_ast);
            }
            let is_empty = DBG_DEPS.lock().unwrap_or_else(|e| e.into_inner()).is_empty();
            if !is_empty {
                dump_debug_deps()
            }
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::RemoveDeadUnsafeCasts => {
            let ctx = provider_context::map_tcopt(ctx, |mut tcopt| {
                tcopt.tco_populate_dead_unsafe_cast_heap = true;
                tcopt
            });
            codemod(files_info, files_contents, &ctx, |ctx, files_info| {
                crate::remove_dead_unsafe_casts::get_patches(ctx, Some(true), files_info)
            });
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::IdeDiagnostics => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let (errors, _tasts) = compute_tasts_expand_types(&ctx, files_info, files_contents);
            crate::ide_diagnostics_cli_lib::run(&ctx, &entry, errors);
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::DumpSymbolInfo => {
            for filename in filenames {
                // `Relative_path.Map.find_opt files_info filename`
                if files_info.contains(filename) {
                    let raw_result =
                        crate::symbol_info_service_utils::helper(ctx, vec![], std::slice::from_ref(filename));
                    let result = crate::symbol_info_service_utils::format_result(raw_result);
                    let result_json = crate::server_command_types::symbol_info_service::to_json(&result);
                    println!("{}", crate::yojson::safe::pretty_to_string(&result_json));
                }
            }
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::CountImpreciseTypes => {
            let (errors, tasts) = compute_tasts_expand_types(ctx, files_info, files_contents);
            if diagnostics::has_errors(None, &errors) {
                crate::hh_single_type_check::print_errors(error_format, errors, input.max_errors);
                print!("Did not count imprecise types because there are typing errors.");
                Ok(2)
            } else {
                let results = tasts
                    .iter()
                    .map(|(_, tast)| crate::count_imprecise_types::count(ctx, tast))
                    .fold(crate::count_imprecise_types::Results::new(), |acc, r| {
                        crate::count_imprecise_types::union(acc, r, "Clash at ")
                    });
                let json = crate::count_imprecise_types::json_of_results(&results);
                print!("{}", crate::yojson::safe::to_string(&json));
                Ok(OK)
            }
        }
        #[cfg(feature = "server")]
        Mode::RunSimpliHack => {
            let (errors, tasts) = compute_tasts(None, ctx, files_info, files_contents);
            crate::hh_single_type_check::print_error_list(error_format, errors, input.max_errors);
            for (fn_, tast) in &tasts {
                let prompts = crate::simplihack_prompt::find(ctx, tast);
                println!("{}", relative_path::to_absolute(fn_));
                for prompt in prompts {
                    // `Printf.printf "  %s\n"` of an OCaml string: its bytes.
                    let msg = match (prompt.derive_prompt)() {
                        Some(p) => p,
                        None => "<no prompt derived>".into(),
                    };
                    let mut line = format!("  {} ", crate::ast_show::show_pos(&prompt.param_pos)).into_bytes();
                    line.extend_from_slice(&msg);
                    line.push(b'\n');
                    use std::io::Write;
                    std::io::stdout().write_all(&line).expect("stdout");
                }
            }
            Ok(OK)
        }
        Mode::DumpDepHashes => {
            for _ in filenames {
                let nasts = create_nasts(ctx, files_info);
                for (_, nast) in &nasts {
                    crate::dep_hash_to_symbol::dump(nast)
                }
            }
            Ok(OK)
        }
        Mode::GetMember(class_and_member_id) => {
            get_member(ctx, class_and_member_id)?;
            Ok(OK)
        }
        Mode::GleanIndex(out_dir) => {
            // `Disk.is_directory`, `Sys.readdir`
            let is_dir = std::fs::metadata(out_dir).is_ok_and(|m| m.is_dir());
            if !is_dir || std::fs::read_dir(out_dir).is_ok_and(|mut d| d.next().is_some()) {
                print!("{} should be an empty dir\n", out_dir);
                return Ok(1);
            }
            crate::write_symbol_info::entrypoint::index_files(ctx, out_dir, filenames);
            Ok(OK)
        }
        Mode::GleanSymHash => {
            // (Nothing catches the exceptions of `sym_hashes`: Core's handler
            // of uncaught exceptions prints them, with their backtrace, which
            // is not printed here, and the program exits with 2.)
            let uncaught = |exn: String| {
                eprint!("Uncaught exception:\n  \n  {}\n\n", exn);
                Ok(2)
            };
            let res = crate::rt::quiet_panic::catch_reported(
                |_| true,
                || crate::write_symbol_info::entrypoint::sym_hashes(ctx, filenames),
            );
            match res {
                Ok(Ok(hashes)) => {
                    for (path, hash) in hashes {
                        print!(
                            "{} {}\n",
                            path,
                            crate::write_symbol_info::entrypoint::md5_to_hex(&hash)
                        )
                    }
                    Ok(OK)
                }
                Ok(Err(e)) => uncaught(e.exn_to_string()),
                Err(payload) => uncaught(crate::write_symbol_info::entrypoint::exn_to_string_or_reraise(payload)),
            }
        }
        _ => Err(mode_not_ported(mode)),
    }
}

/// The `Get_member class_and_member_id` arm of `handle_mode`.
fn get_member(ctx: &provider_context::T, class_and_member_id: &str) -> anyhow::Result<()> {
    use crate::decl_entry;
    use crate::folded_class as cls;
    // `Str.split (Str.regexp "::")` (empty parts are dropped)
    let parts: Vec<&str> = class_and_member_id.split("::").filter(|s| !s.is_empty()).collect();
    let (cid, mid) = match parts.as_slice() {
        [cid, mid] => (*cid, *mid),
        _ => {
            return Err(Uncaught::failure(format!(
                "Invalid --get-member ID: {}",
                crate::rt::ocaml_printf::sprintf_s(class_and_member_id)
            ))
            .into());
        }
    };
    let cid = crate::utils::add_ns(cid);
    match crate::decl_provider::get_class(None, ctx, &cid) {
        decl_entry::T::Found(cls) => {
            let env = crate::typing_env_types::empty(
                None,
                None,
                ctx.clone(),
                std::sync::Arc::new(crate::relative_path::DEFAULT),
                None,
            );
            let ty_to_string = |ty: &crate::typing_defs::DeclTy| {
                { use pos::ToOxidized as _; crate::typing_print::full_strip_ns_decl(None, false, &env, &ty.clone().to_oxidized()) }
            };
            let from = |origin: &str| {
                if origin == cid {
                    "".to_string()
                } else {
                    format!(" from {}", crate::utils::strip_ns(origin))
                }
            };
            let print_class_element = |member_type: &str, ce: Option<crate::folded_class::ClassElt>| {
                if let Some(ce) = ce {
                    let abstract_ = if crate::typing_defs::get_ce_abstract(&ce) {
                        "abstract "
                    } else {
                        ""
                    };
                    println!(
                        "  {}{}{}: {}",
                        abstract_,
                        member_type,
                        from(&ce.ce_origin),
                        ty_to_string(&ce.ce_type)
                    )
                }
            };
            println!("{}::{}", cid, mid);
            print_class_element("method", cls::get_method(&cls, mid));
            print_class_element("static method", cls::get_smethod(&cls, mid));
            print_class_element("property", cls::get_prop(&cls, mid));
            print_class_element("static property", cls::get_sprop(&cls, mid));
            print_class_element("static property", cls::get_sprop(&cls, &format!("${}", mid)));
            if let Some(cc) = cls::get_const(&cls, mid) {
                let abstract_ = match cc.kind {
                    oxidized::typing_defs::ClassConstKind::CCAbstract(_) => "abstract ",
                    oxidized::typing_defs::ClassConstKind::CCConcrete => "",
                };
                println!("  {}const{}: {}", abstract_, from(cc.origin.as_str()), ty_to_string(&cc.ty));
            }
            if let Some(ttc) = cls::get_typeconst(&cls, mid) {
                use ty::decl::ty::Typeconst;
                let ty = match &ttc.kind {
                    Typeconst::TCConcrete(c) => format!("= {}", ty_to_string(&c.ty)),
                    Typeconst::TCAbstract(a) => [
                        a.as_constraint.as_ref().map(|ty| format!("as {}", ty_to_string(ty))),
                        a.default.as_ref().map(|ty| format!("= {}", ty_to_string(ty))),
                    ]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>()
                    .join(" "),
                };
                let abstract_ = match &ttc.kind {
                    Typeconst::TCConcrete(_) => "",
                    Typeconst::TCAbstract(_) => "abstract ",
                };
                println!("  {}typeconst{}: {} {}", abstract_, from(ttc.origin.as_str()), mid, ty);
            }
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => println!("No class named {}", cid),
    }
    Ok(())
}


/// The line `do_enforcement` prints for a result.
fn print_enforcement(
    oc: &mut dyn std::io::Write,
    result: &crate::enforcement_at_pos_service::Result,
) -> std::io::Result<()> {
    use crate::enforcement_at_pos_service::Enforcement;
    match result {
        Some(Enforcement::Enforced(types)) => {
            let ty_strs: Vec<&str> = types.iter().map(|t| t.ty_str.as_str()).collect();
            writeln!(oc, "{}: Enforced", ty_strs.join(", "))
        }
        Some(Enforcement::Unenforced) => writeln!(oc, "Unenforced"),
        None => writeln!(oc, "(unknown)"),
    }
}

/// `do_enforcement ~ctx ~filename oc pos_given`
fn do_enforcement(
    ctx: &provider_context::T,
    filename: relative_path::T,
    oc: &mut dyn std::io::Write,
    pos_given: Option<position::T>,
) -> anyhow::Result<()> {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, filename);
    let pos = match pos_given {
        Some(pos) => pos,
        None => {
            let src = provider_context::read_file_contents_exn(&entry);
            caret_pos_exn(&src, "^ enforcement-at-caret")?
        }
    };
    let result = crate::server_enforcement_at_pos::go_ctx(&ctx, &entry, &pos);
    print_enforcement(oc, &result)?;
    Ok(())
}

/// `do_enforcement_batch ~ctx ~filename oc`
fn do_enforcement_batch(
    ctx: &provider_context::T,
    filename: relative_path::T,
    oc: &mut dyn std::io::Write,
) -> anyhow::Result<()> {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, filename);
    let src = provider_context::read_file_contents_exn(&entry);
    let positions = all_caret_positions(&src, "^ enforcement-at-caret");
    for pos in positions {
        let result = crate::server_enforcement_at_pos::go_ctx(&ctx, &entry, &pos);
        print_enforcement(oc, &result)?;
    }
    Ok(())
}

/// `decl_parse_typecheck_and_then ctx files_contents f`: whether there was
/// no error (`f` is then applied to the files that were declared).
///
/// (`parse_name_and_decl`: the files are declared in the context first, as
/// `hh_single_cli` does for the files of the command line.)
#[cfg(feature = "server")]
fn decl_parse_typecheck_and_then(
    ctx: &provider_context::T,
    files_contents: &[(relative_path::T, bstr::BString)],
) -> Option<Vec<relative_path::T>> {
    let files_info: Vec<relative_path::T> = files_contents.iter().map(|(p, _)| p.clone()).collect();
    let decl_paths: Vec<pos::RelativePath> = files_info.iter().map(pos::RelativePath::from).collect();
    let mut stats = crate::check::Stats::default();
    crate::check::declare_files(ctx, &decl_paths, &mut stats);
    let parse_errors = crate::hh_single_type_check::parse_name_and_decl(ctx, &files_info);
    let (errors, _tasts) = compute_tasts_expand_types(ctx, &files_info, files_contents);
    let errors = diagnostics::merge(parse_errors, errors);
    if diagnostics::has_no_errors(None, &errors) {
        Some(files_info)
    } else {
        print_errors_if_present(errors);
        None
    }
}

/// `Server_rename_types.apply_patches_to_file_contents`
#[cfg(feature = "server")]
fn apply_patches_to_file_contents(
    file_contents: &[(relative_path::T, bstr::BString)],
    patches: &[crate::remove_dead_unsafe_casts::Patch],
) -> Vec<(relative_path::T, bstr::BString)> {
    use crate::code_actions::code_actions_utils as cu;
    file_contents
        .iter()
        .map(|(fn_, old_contents)| {
            // `map_patches_to_filename`: `patch :: lst`, the last patch first
            let file_patches: Vec<cu::Patch> = patches
                .iter()
                .rev()
                .filter(|(pos, _)| pos.filename() == fn_)
                .map(|(pos, text)| cu::Patch::Replace {
                    pos: pos.clone(),
                    text: text.clone(),
                })
                .collect();
            if file_patches.is_empty() {
                (fn_.clone(), old_contents.clone())
            } else {
                (
                    fn_.clone(),
                    bstr::BString::from(cu::apply_patches_to_string(old_contents, file_patches)),
                )
            }
        })
        .collect()
}

/// `codemod ~files_info ~files_contents ctx get_patches`
#[cfg(feature = "server")]
fn codemod(
    files_info: &[relative_path::T],
    files_contents: &[(relative_path::T, bstr::BString)],
    ctx: &provider_context::T,
    get_patches: impl Fn(&provider_context::T, &[relative_path::T]) -> crate::remove_dead_unsafe_casts::Patches,
) {
    // Because we repeatedly apply the codemod, positions change. So we need to
    // re-parse, decl, and typecheck the file to generated accurate patches as
    // well as amend the patched test files in memory. This involves
    // invalidating a number of shared heaps and providing in memory
    // replacements after patching files.
    let invalidate_heaps_and_update_files =
        |files_info: &[relative_path::T], files_contents: &[(relative_path::T, bstr::BString)]| {
            let paths_to_purge: relative_path::set::T = files_contents.iter().map(|(p, _)| p.clone()).collect();
            // (`file_info.ids`: the names the file defines, from its AST.)
            let mut names_to_purge = crate::file_info::empty_names();
            let mut ids_to_purge = vec![];
            for path in files_info {
                // Don't invalidate builtins, otherwise, we can't find them.
                if !relative_path::is_hhi(path.prefix()) {
                    let ast = diagnostics::ignore_(|| crate::ast_provider::get_ast(true, ctx, path));
                    let ids = crate::nast::get_def_names(&ast);
                    names_to_purge =
                        crate::file_info::merge_names(&names_to_purge, &crate::file_info::ids_to_names(&ids));
                    ids_to_purge.push(ids);
                }
            }
            ctx.remove_defs(&names_to_purge);
            // (The decls a thread has read are cached: the OCaml heaps drop
            // theirs from their local caches when they are removed.)
            crate::rt::decl_epoch::invalidate_local_caches();
            // Purge the file, then provide its replacement, otherwise the
            // replacement is dropped on the floor.
            for (path, contents) in files_contents {
                crate::file_provider::rust_provider_backend::file::provide_file_for_tests(ctx, path, contents.clone())
            }
            crate::ast_provider::remove_batch(&paths_to_purge);
            for ids in &ids_to_purge {
                crate::naming_global::remove_decls_using_file_info(ctx, ids)
            }
        };
    let mut final_files_info = files_info.to_vec();
    let mut final_files_contents = files_contents.to_vec();
    // `go files_info files_contents`
    let mut files_info = files_info.to_vec();
    let mut files_contents = files_contents.to_vec();
    loop {
        invalidate_heaps_and_update_files(&files_info, &files_contents);
        match decl_parse_typecheck_and_then(ctx, &files_contents) {
            None => break,
            Some(new_files_info) => {
                let patches = get_patches(ctx, &new_files_info);
                let new_files_contents = apply_patches_to_file_contents(&files_contents, &patches);
                if patches.is_empty() {
                    crate::multifile::print_files_as_multifile(&new_files_contents);
                    final_files_info = new_files_info;
                    final_files_contents = new_files_contents;
                    break;
                } else {
                    files_info = new_files_info;
                    files_contents = new_files_contents;
                }
            }
        }
    }

    // Typecheck after the codemod is fully applied to confirm that what we
    // produce is not garbage.
    print!("\nTypechecking after the codemod... (no output after this is good news)\n");
    invalidate_heaps_and_update_files(&final_files_info, &final_files_contents);
    let _ = decl_parse_typecheck_and_then(ctx, &final_files_contents);
}

/// `handle_constraint_mode ~do_ name opts ctx error_format ~iter_over_files`
/// (without the profiling and the memory trace).
fn handle_constraint_mode<O>(
    do_: impl Fn(&O, &provider_context::T, &[crate::tast::Def]),
    name: &str,
    opts: &O,
    ctx: &provider_context::T,
    error_format: diagnostics::Format,
    filenames: &[relative_path::T],
) -> anyhow::Result<()> {
    // Process a single typechecked file
    let process_file = |path: &relative_path::T, file_mode: Option<crate::file_info::Mode>| {
        match file_mode {
            Some(crate::file_info::Mode::Mstrict) => {
                let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
                let crate::tast_provider::ComputeTast { tast, .. } =
                    crate::tast_provider::compute_tast_unquarantined(&ctx, &entry);
                let tast = crate::tast_with_dynamic::all(tast).concat();
                do_(opts, &ctx, &tast)
            }
            // We are not interested in partial files and there is nothing in HHI
            // files to analyse
            _ => {}
        }
    };
    // Process a multifile that is not typechecked
    for filename in filenames {
        crate::provider_utils::respect_but_quarantine_unsaved_changes(ctx, || -> anyhow::Result<()> {
            println!(
                "=== {} analysis results for {}",
                name,
                relative_path::to_absolute(filename)
            );
            // `Multifile.file_to_files filename`: the parts are files of the
            // context already (`hh_single_cli` declared them).
            let abs = relative_path::to_absolute(filename);
            let content = std::fs::read(&abs)?;
            let files: Vec<relative_path::T> = crate::multifile::file_to_file_list_rooted(&abs, &content)
                .into_iter()
                .map(|(rooted, part, _)| {
                    if rooted {
                        relative_path::from_root(&part)
                    } else {
                        relative_path::create(filename.prefix(), &part)
                    }
                })
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            let parse_errors = crate::hh_single_type_check::parse_name_and_decl(ctx, &files);
            let check_errors = crate::hh_single_type_check::check_file(ctx, parse_errors, &files);
            if !diagnostics::has_no_errors_or_warnings(None, &check_errors) {
                let mut stdout = std::io::stdout().lock();
                for e in diagnostics::get_sorted_diagnostic_list(None, check_errors) {
                    crate::hh_single_type_check::print_error(error_format, &mut stdout, &e)
                }
            } else {
                for path in &files {
                    let contents = crate::file_provider::rust_provider_backend::file::get_contents(ctx, path)
                        .unwrap_or_default();
                    let popt = provider_context::get_popt(ctx).clone();
                    let file_mode =
                        crate::full_fidelity_ast::defensive_program(None, None, None, None, popt, path, &contents)
                            .file_mode;
                    process_file(path, file_mode)
                }
            }
            Ok(())
        })?
    }
    Ok(())
}

/// `dbg_deps`: for each dependency, its dependents (`--dump-deps`).
static DBG_DEPS: std::sync::Mutex<std::collections::BTreeMap<String, std::collections::BTreeSet<String>>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// In addition to actually recording the dependencies in shared memory,
/// we build a non-hashed respresentation of the dependency graph
/// for printing.
pub fn add_debug_trace_callback() {
    let get_debug_trace = |root: &crate::typing_deps::dep::Variant, obj: &crate::typing_deps::dep::Variant| {
        let root = crate::typing_deps::dep::variant_to_string(root);
        let obj = crate::typing_deps::dep::variant_to_string(obj);
        DBG_DEPS
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .entry(obj)
            .or_default()
            .insert(root);
    };
    crate::typing_deps::add_dependency_callback("get_debug_trace", get_debug_trace)
}

/// `pp_debug_deps`
fn pp_debug_deps(fmt: &mut crate::format::Formatter, entries: &[(String, Vec<String>)]) {
    use crate::format;
    format::pp_open_vbox(fmt, 0);
    let mut sep = false;
    for (obj, roots) in entries {
        if sep {
            format::pp_print_cut(fmt)
        }
        format::pp_print_string(fmt, &format!("{} -> ", obj));
        format::pp_open_hvbox(fmt, 0);
        let mut root_sep = false;
        for root in roots {
            if root_sep {
                format::pp_print_string(fmt, ",");
                format::pp_print_space(fmt)
            }
            format::pp_print_string(fmt, root);
            root_sep = true
        }
        format::pp_close_box(fmt);
        sep = true
    }
    format::pp_close_box(fmt)
}

/// `dump_debug_deps dbg_deps` (`sort_debug_deps`, `show_debug_deps`).
///
/// Note: this prints dependency graph edges in the same direction as the mapping
/// which is actually stored in the shared memory table. The line "X -> Y" can be
/// read, "X is used by Y", or "X is a dependency of Y", or "when X changes, Y
/// must be rechecked".
fn dump_debug_deps() {
    let entries: Vec<(String, Vec<String>)> = DBG_DEPS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .iter()
        .map(|(obj, roots)| (obj.clone(), roots.iter().cloned().collect()))
        .collect();
    println!("{}", crate::format::asprintf(|fmt| pp_debug_deps(fmt, &entries)))
}

/// `print_errors_if_present`
fn print_errors_if_present(errors: diagnostics::T) {
    if !diagnostics::has_no_errors_or_warnings(None, &errors) {
        let errors_output =
            crate::diagnostics::convert_errors_to_string(&diagnostics::get_sorted_diagnostic_list(None, errors));
        println!("Errors:");
        for err_output in errors_output {
            println!("  {}", err_output);
        }
    }
}

/// `compute_tasts_expand_types`: the TASTs of [`compute_tasts`], with all
/// type variables expanded (`Tast_expand.expand_program`).
fn compute_tasts_expand_types(
    ctx: &provider_context::T,
    files_info: &[relative_path::T],
    interesting_files: &[(relative_path::T, bstr::BString)],
) -> (
    diagnostics::T,
    Vec<(relative_path::T, Vec<crate::tast::Def>)>,
) {
    let (errors, tasts) = compute_tasts(None, ctx, files_info, interesting_files);
    let tasts = tasts
        .into_iter()
        .map(|(fn_, tast)| (fn_, crate::tast_expand::expand_program(ctx, tast)))
        .collect();
    (errors, tasts)
}

/// `print_nasts ~should_print_position nasts filenames`
fn print_nasts<'a>(
    should_print_position: bool,
    nasts: &[(relative_path::T, oxidized::nast::Program)],
    filenames: impl Iterator<Item = &'a relative_path::T>,
) {
    for filename in filenames {
        match nasts.iter().find(|(k, _)| k == filename) {
            None => {
                eprintln!(
                    "Could not find nast for file {}",
                    relative_path::show(filename)
                );
                eprintln!("Available nasts:");
                for (path, _) in nasts {
                    eprintln!("  {}", relative_path::show(path));
                }
            }
            Some((_, nast)) => {
                if should_print_position {
                    crate::naming_ast_print::print_nast(nast)
                } else {
                    crate::naming_ast_print::print_nast_without_position(nast)
                }
            }
        }
    }
}

/// `print_tasts ~should_print_position tasts ctx`
fn print_tasts(
    should_print_position: bool,
    tasts: Vec<(relative_path::T, Vec<crate::tast::Def>)>,
    ctx: &provider_context::T,
) {
    for (_k, tast) in tasts {
        let tast = oxidized::aast::Program(tast);
        if should_print_position {
            crate::typing_ast_print::print_tast(ctx.clone(), &tast)
        } else {
            crate::typing_ast_print::print_tast_without_position(ctx.clone(), &tast)
        }
    }
}


/// `create_nasts ctx files_info`: the parse errors of each file are added
/// to the current diagnostics, and each AST is named.
fn create_nasts(
    ctx: &provider_context::T,
    files_info: &[relative_path::T],
) -> Vec<(relative_path::T, oxidized::nast::Program)> {
    files_info
        .iter()
        .map(|fn_| {
            let (syntax_errors, ast) = crate::ast_provider::get_ast_with_error(true, ctx, fn_);
            for e in diagnostics::get_sorted_diagnostic_list(None, syntax_errors) {
                diagnostics::add_diagnostic(e);
            }
            (fn_.clone(), crate::naming::program(ctx, ast))
        })
        .collect()
}

/// `compute_nasts ctx files_info interesting_files`: the NASTs of the
/// interesting files (all files are named).
fn compute_nasts(
    ctx: &provider_context::T,
    files_info: &[relative_path::T],
    interesting_files: &[(relative_path::T, bstr::BString)],
) -> Vec<(relative_path::T, oxidized::nast::Program)> {
    create_nasts(ctx, files_info)
        .into_iter()
        .filter(|(fn_, _)| interesting_files.iter().any(|(p, _)| p == fn_))
        .collect()
}

/// `compute_tasts ?drop_fixmed ctx files_info interesting_files`: the
/// diagnostics of naming and typing the interesting files, and their TASTs.
fn compute_tasts(
    drop_fixmed: Option<bool>,
    ctx: &provider_context::T,
    files_info: &[relative_path::T],
    interesting_files: &[(relative_path::T, bstr::BString)],
) -> (
    diagnostics::T,
    Vec<(relative_path::T, Vec<crate::tast::Def>)>,
) {
    diagnostics::do_(drop_fixmed, || {
        let nasts = compute_nasts(ctx, files_info, interesting_files);
        nasts
            .into_iter()
            .map(|(fn_, nast)| {
                let tast = crate::typing_toplevel::nast_to_tast(true, ctx, &nast);
                (fn_, crate::tast_with_dynamic::all(tast).concat())
            })
            .collect()
    })
}

/// `Eager_quickfix_test_util`: enables testing of eager quickfixes
/// (`Quickfix.Eager`). Prefer using `--ide-code-actions` for more realistic
/// tests that don't care about eagerness.
mod eager_quickfix_test_util {
    use crate::pos::Pos;
    use crate::rt::ocaml_exn::Uncaught;

    type Edit = (String, Pos);

    /// corresponds to a `Quickfix.Eager`
    pub struct T {
        _title: String,
        edits: Vec<Edit>,
    }

    /// convert `Quickfix.Eager` to a `Some t`, otherwise `None`
    pub fn of_quickfix(qf: &crate::quickfix::Quickfix<Pos>) -> Option<T> {
        match &qf.edits {
            crate::quickfix::Edits::Eager(eager_edits) => Some(T {
                _title: qf.title.clone(),
                edits: eager_edits.clone(),
            }),
            _ => None,
        }
    }

    fn offset((_, pos): &Edit) -> isize {
        crate::pos::info_raw(pos).1
    }

    /// Sort `quickfixes` with their edit positions in descending order. This
    /// allows us to iteratively apply the quickfixes without messing up
    /// positions earlier in the file.
    fn sort_for_application(mut quickfixes: Vec<T>) -> Vec<T> {
        let first_qf_offset = |quickfix: &T| -> isize {
            match quickfix.edits.first() {
                Some((_, pos)) => crate::pos::info_raw(pos).1,
                None => crate::pos::info_raw(&crate::pos::NONE).1,
            }
        };
        // `List.rev (List.sort ~compare quickfixes)` (a stable sort)
        quickfixes.sort_by_key(first_qf_offset);
        quickfixes.reverse();
        quickfixes
    }

    fn sort_edits_for_application(edits: &[Edit]) -> Vec<Edit> {
        let mut edits = edits.to_vec();
        edits.sort_by_key(offset);
        edits.reverse();
        edits
    }

    /// Apply `edit` to `src`, replacing the text at the position specified.
    fn apply_edit(src: &[u8], (new_text, pos): &Edit) -> anyhow::Result<Vec<u8>> {
        if crate::pos::equal_none(pos) {
            return Err(Uncaught::failure(format!(
                "tried to apply quickfix edit with invalid pos 'Pos.none' and text '{}'",
                new_text
            ))
            .into());
        }
        let (start_offset, end_offset) = crate::pos::info_raw(pos);
        let mut res = src[..start_offset as usize].to_vec();
        res.extend_from_slice(new_text.as_bytes());
        res.extend_from_slice(&src[end_offset as usize..]);
        Ok(res)
    }

    fn apply_quickfix(src: Vec<u8>, eager_quickfix: &T) -> anyhow::Result<Vec<u8>> {
        sort_edits_for_application(&eager_quickfix.edits)
            .iter()
            .try_fold(src, |src, edit| apply_edit(&src, edit))
    }

    /// For testing, with `--fix`, apply all eager quickfixes by
    /// replacing/inserting the new text in `src`.
    pub fn apply_all(src: &[u8], eager_quickfixes: Vec<T>) -> anyhow::Result<Vec<u8>> {
        sort_for_application(eager_quickfixes)
            .iter()
            .try_fold(src.to_vec(), apply_quickfix)
    }
}

/// `do_hover ~ctx ~filename oc pos_given`
fn do_hover(
    ctx: &provider_context::T,
    filename: relative_path::T,
    oc: &mut dyn std::io::Write,
    pos_given: Option<position::T>,
) -> anyhow::Result<()> {
    let (ctx, entry) = provider_context::add_entry_if_missing(ctx, filename);
    let pos = match pos_given {
        Some(pos) => pos,
        None => {
            let src = provider_context::read_file_contents_exn(&entry);
            caret_pos_exn(&src, "^ hover-at-caret")?
        }
    };
    {
        let results = crate::ide_hover::go_quarantined(&ctx, &entry, &pos);
        let formatted_results = crate::hover_service::as_marked_string_list(&results)
            .into_iter()
            .map(|r| match r {
                crate::lsp::MarkedString::MarkedCode(_, s) => s,
                crate::lsp::MarkedString::MarkedString(s) => s,
            })
            .collect::<Vec<_>>()
            .join("\n");
        writeln!(oc, "{}", formatted_results)?;
        Ok(())
    }
}

/// The modes `--find-refs`, `--go-to-impl` and `--dump-inheritance`: the
/// glue of `hh_single_type_check.ml`'s `handle_mode` around
/// `Server_find_refs`, `Server_go_to_impl` and `Method_jumps`.
#[cfg(feature = "server")]
mod find_refs_modes {
    use super::*;
    use crate::server_command_types::done_or_retry::T::Done;
    use crate::server_command_types::done_or_retry::T::Retry;
    use crate::server_env::Env;
    use crate::server_env::Genv;

    /// `files_info`: the `File_info.t` of each file of `to_decl` (the
    /// builtins and `files_contents`), `Direct_decl_utils.decls_to_fileinfo`
    /// of its decls (`parse_and_name`).
    fn files_info(input: &Input) -> crate::relative_path::map::T<crate::file_info::T> {
        let mut m = crate::relative_path::map::T::new();
        let paths = input
            .builtins
            .iter()
            .chain(input.files_contents.iter().map(|(p, _)| p));
        for fn_ in paths {
            match crate::direct_decl_service::direct_decl_parse(&input.ctx, fn_) {
                None => panic!("Failure: no file contents"),
                Some(decls) => {
                    m.insert(
                        fn_.clone(),
                        crate::direct_decl_service::decls_to_fileinfo(fn_, &decls),
                    );
                }
            }
        }
        m
    }


    /// The `genv` and `env` of `Find_refs` and `Go_to_impl`:
    /// `Server_env_build.default_genv`, and `make_env ~init_id
    /// ~deps_mode:(InMemoryMode None)` with the naming table of `files_info`
    /// and the context's options (the OCaml's context is global, so the
    /// environment's context is `ctx`).
    fn genv_and_env(input: &Input) -> (Genv, Env) {
        let ctx = &input.ctx;
        // `Naming_provider.get_files` (a lookup by dependency hash) answers
        // from the reverse naming table, as the OCaml's naming heap does.
        if !ctx.has_reverse_naming_table() {
            ctx.build_reverse_naming_table();
        }
        let naming_table = crate::naming_table::create(files_info(input));
        let genv = crate::server_env_build::default_genv();
        let init_id = crate::random_id::short_string();
        let mut env = crate::server_env_build::make_env(
            &init_id,
            crate::typing_deps::mode::T::InMemoryMode(None),
            None,
            &genv.config,
            std::path::Path::new("/"),
        );
        env.naming_table = naming_table;
        env.ctx = ctx.clone();
        (genv, env)
    }

    pub fn find_refs(input: &Input, path: relative_path::T, pos: &position::T) -> anyhow::Result<()> {
        let (genv, env) = genv_and_env(input);
        let include_defs = true;
        let (ctx, entry) = provider_context::add_entry_if_missing(
            &crate::provider_utils::ctx_from_server_env(&env),
            path,
        );
        crate::provider_utils::respect_but_quarantine_unsaved_changes(&ctx, || {
            match crate::server_find_refs::go_from_file_ctx(&ctx, &entry, pos) {
                None => Ok(()),
                Some((name, action)) => {
                    let results = match crate::server_find_refs::go(
                        &ctx,
                        &action,
                        include_defs,
                        None,
                        &[],
                        &genv,
                        env,
                    ) {
                        (_env, Done(r)) => crate::server_find_refs::to_absolute(&r),
                        (_env, Retry) => return Err(Uncaught::failure("didn't expect retry").into()),
                    };
                    println!("{}", name);
                    let results: Vec<_> = results.into_iter().rev().collect();
                    crate::find_refs_wire_format::cli_human_readable::print_results(&results);
                    Ok(())
                }
            }
        })
    }

    pub fn go_to_impl(
        input: &Input,
        filename: relative_path::T,
        pos: &position::T,
    ) -> anyhow::Result<()> {
        let (genv, env) = genv_and_env(input);
        let filename = relative_path::to_absolute(&filename);
        let contents = std::fs::read(&filename)?;
        let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
            &crate::provider_utils::ctx_from_server_env(&env),
            relative_path::create_detect_prefix(&filename),
            contents.into(),
        );
        match crate::server_find_refs::go_from_file_ctx(&ctx, &entry, pos) {
            None => {}
            Some((name, action)) => {
                let results = match crate::server_go_to_impl::go(&action, &genv, env) {
                    (_env, Done(r)) => crate::server_find_refs::to_absolute(&r),
                    (_env, Retry) => return Err(Uncaught::failure("didn't expect retry").into()),
                };
                println!("{}", name);
                let results: Vec<_> = results.into_iter().rev().collect();
                crate::find_refs_wire_format::cli_human_readable::print_results(&results);
            }
        }
        Ok(())
    }

    pub fn dump_inheritance(input: &Input) -> anyhow::Result<()> {
        use crate::server_command_types::method_jumps;
        let ctx = &input.ctx;
        if !ctx.has_reverse_naming_table() {
            ctx.build_reverse_naming_table();
        }
        let naming_table = crate::naming_table::create(files_info(input));
        let builtins: std::collections::BTreeSet<&relative_path::T> = input.builtins.iter().collect();
        let mut result = Ok(());
        crate::naming_table::iter(&naming_table, |fn_, fileinfo| {
            if result.is_err() || builtins.contains(fn_) {
                return;
            }
            let go = |find_children: bool| -> Result<(), crate::naming_table::FileInfoNotFound> {
                for id in &fileinfo.ids.classes {
                    if find_children {
                        println!("Children of {} and the methods they override:", id.name);
                    } else {
                        println!("Ancestors of {} and their overridden methods:", id.name);
                    }
                    // Might raise {!Naming_table.File_info_not_found}
                    let res = crate::method_jumps::get_inheritance(
                        ctx,
                        &id.name,
                        method_jumps::Filter::NoFilter,
                        find_children,
                        &naming_table,
                        None,
                    )?;
                    method_jumps::print_readable(&res, find_children);
                    println!();
                }
                Ok(())
            };
            result = go(false).and_then(|()| {
                println!();
                go(true)
            });
        });
        result.map_err(|crate::naming_table::FileInfoNotFound| {
            anyhow::Error::from(Uncaught::Printexc("Naming_table.File_info_not_found".to_string()))
        })
    }
}

/// The `Lint` (`json = false`) and `Lint_json` (`json = true`) branches of
/// `handle_mode` in `hh_single_type_check.ml`: lints `files_contents` (the
/// files of the test, in the order of `Relative_path.Map.fold`) and prints
/// the lints on `oc`. Returns the exit code: 2 when it calls `exit 2`, 0
/// otherwise.
#[cfg(feature = "server")]
pub fn hh_single_lint(
    ctx: &std::sync::Arc<crate::ctx::Ctx>,
    files_contents: &[(crate::relative_path::T, Vec<u8>)],
    json: bool,
    error_format: crate::diagnostics::Format,
    oc: &mut dyn std::io::Write,
) -> i32 {
    // `Relative_path.Map.fold files_contents ~init:[] ~f:(fun fn content
    // lint_errors -> lint_errors @ fst (Lints_core.do_ ...))`
    let mut lint_errors: Vec<crate::lints_core::T<oxidized::pos::Pos>> = vec![];
    for (fn_, content) in files_contents {
        lint_errors.extend(crate::lints_core::do_(|| crate::linting_main::lint(ctx, fn_, content)).0);
    }
    if !json {
        if !lint_errors.is_empty() {
            match error_format {
                crate::diagnostics::Format::PlainHighlighted => {
                    // `List.sort` is stable.
                    lint_errors.sort_by(|x, y| {
                        crate::pos::compare(
                            &crate::lints_core::get_pos(x),
                            &crate::lints_core::get_pos(y),
                        )
                    });
                    for lint in lint_errors {
                        // `Relative_path.Map.find_opt files_contents
                        // (Pos.filename (Lints_core.get_pos lint))`
                        let lint_file = crate::pos::filename(&crate::lints_core::get_pos(&lint));
                        let source = files_contents
                            .iter()
                            .find(|(fn_, _)| *fn_ == lint_file)
                            .map(|(_, content)| String::from_utf8_lossy(content).into_owned());
                        let text = crate::lints_core::to_plain_highlighted_string(
                            source,
                            &crate::lints_core::to_absolute(lint),
                        );
                        let _ = oc.write_all(text.as_bytes());
                        let _ = oc.write_all(b"\n");
                        let _ = oc.flush();
                    }
                }
                format => {
                    let lint_errors = crate::server_lint::prepare_errors_for_output(lint_errors);
                    crate::server_lint_types::output_text(oc, &lint_errors, format);
                }
            }
            2
        } else {
            let _ = oc.write_all(b"No lint errors\n");
            0
        }
    } else {
        let json_errors = crate::server_lint::prepare_errors_for_output(lint_errors);
        crate::server_lint_types::output_json(Some(true), Some(true), oc, &json_errors);
        2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The two orders of a file's addenda in the symbol index, and why the
    /// `.exp` of test/autocomplete (`def.php`: the last 100 symbols of
    /// `ext_sodium.hhi`) need `hh_single_complete`'s: with 101 classes in
    /// a file, the scan stops in that file after 100 matches
    /// (`Local_search_service.search_local_symbols`, `BreakOutOfScan`).
    /// - `hh_single_complete.ml:315`: `decls_to_addenda` of `pfh_decls`,
    ///   reverse lexical order: `Zz000` (the first class) is left out.
    /// - IDE daemon (`client_ide_init.ml:144-148`, `client_ide_incremental.ml:132-140`):
    ///   Rust `si_addendum::get_si_addenda`, forward order: `Zz100` is left out.
    #[test]
    fn complete_and_ide_addenda_orders() {
        let mut text = String::from("<?hh\n");
        for i in 0..101 {
            text.push_str(&format!("class Zz{:03} {{}}\n", i));
        }
        let ctx = crate::provider_context::empty_for_test(
            Default::default(),
            Default::default(),
            crate::typing_deps::mode::T::InMemoryMode(None),
        );
        let path = ::pos::RelativePath::new(::pos::Prefix::Dummy, "a.php");
        let decls = ctx.decl_parser.parse_with_text(path, text.as_bytes()).unwrap();
        let search = |addenda: Vec<crate::file_info::SiAddendum>| {
            let sienv = crate::symbol_index::initialize(&Default::default(), &[], "LocalIndex", true);
            let mut sienv = crate::symbol_index_core::update_from_addenda(
                &sienv,
                &[(path.into(), addenda, crate::search_utils::FileSource::TypeChecker)],
            );
            let (r, _) = crate::symbol_index::find_matching_symbols(
                &mut sienv,
                "zz",
                100,
                crate::search_types::AutocompleteType::Acid,
                None,
            );
            r.into_iter().map(|i| i.name).collect::<Vec<_>>()
        };
        let complete = crate::hh_single_complete::addenda_of_parse(&decls);
        assert_eq!(complete.first().unwrap().name, "Zz100");
        let r = search(complete);
        assert_eq!(r.len(), 100);
        assert!(!r.contains(&"Zz000".to_string()) && r.contains(&"Zz100".to_string()));
        let ide = crate::symbol_index_core::get_si_addenda(&decls);
        assert_eq!(ide.first().unwrap().name, "Zz000");
        let r = search(ide);
        assert!(r.contains(&"Zz000".to_string()) && !r.contains(&"Zz100".to_string()));
    }

    fn pos(line: isize, column: isize) -> position::T {
        position::from_one_based(line, column)
    }

    #[test]
    fn caret_points_at_the_line_above() {
        let src = b"<?hh\nfunction f(): void {\n  g();\n//^ hover-at-caret\n}\n";
        // The marker is on 0-based line 3: one-based line 3 is the line above.
        assert_eq!(caret_pos(src, "^ hover-at-caret"), Some(pos(3, 3)));
        assert_eq!(caret_pos(src, "^ at-caret"), None);
        assert!(caret_pos_exn(src, "^ nothing").is_err());
    }

    #[test]
    fn all_carets() {
        let src = b"a\n  ^ e-at-caret\nb\n     ^ e-at-caret\n";
        assert_eq!(
            all_caret_positions(src, "^ e-at-caret"),
            vec![pos(1, 3), pos(3, 6)]
        );
    }

    #[test]
    fn ide_range_from_comments_or_caret() {
        let src = b"<?hh\nfunction f(): void {\n  $x = /*range-start*/1 + 2/*range-end*/;\n}\n";
        let r = find_ide_range_exn(src).unwrap();
        assert_eq!(r.st, position::from_zero_based(2, 22));
        assert_eq!(r.ed, position::from_zero_based(2, 27));
        let src = b"<?hh\nf(1, 2);\n//  ^ at-caret\n";
        let r = find_ide_range_exn(src).unwrap();
        assert_eq!((r.st, r.ed), (pos(2, 5), pos(2, 5)));
        // (`Error.raise`: the exception's sexp is the message, an atom.)
        assert_eq!(
            find_ide_range_exn(b"<?hh\n").unwrap_err().to_string(),
            "\"could not find pair '/*range-start*/','/*range-end*/' nor '^ at-caret'\""
        );
    }

}
