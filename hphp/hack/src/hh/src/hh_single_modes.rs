// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the mode dispatch of `hh_single_type_check.ml` (`type mode`,
//! `handle_mode`, the caret helpers) and of `hh_single_complete.ml`
//! (`type mode`, `handle_mode`): one arm per mode, calling the owner's
//! `pub fn`. The command lines are `src/hh_single_cli.rs` (a module of the
//! `hh` binary), which parses the flags into a [`Mode`], sets up the context
//! as `decl_and_run_mode` does and calls [`handle_mode`] (or
//! [`complete::handle_mode`]) for every mode but `Errors`.
//!
//! A mode whose service is not ported yet fails with "mode not ported:
//! OWNER (FLAG)" on stderr and exit code 2 (as an unknown option of
//! `hh single` would fail), see [`not_ported`]; its glue (how the context
//! and the entry are made, how the result is printed) is already written,
//! inside a `#[cfg(any())]` block that is enabled when the owner's function
//! lands. [`MODES`] lists the modes, their suites and owners.
//!
//! Owned by **F0** (plan §7.3).

use crate::diagnostics_state;
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
/// it, the assignment that owns its service (plan §7.3), and the functions
/// the glue calls (the signatures are in `/tmp/hh-port/incr/notes.md`).
pub struct ModeInfo {
    pub flag: &'static str,
    pub suite: &'static str,
    pub owner: &'static str,
    pub calls: &'static str,
}

/// The modes of `hh_single_type_check` and `hh_single_complete`, in the
/// order of their options.
pub const MODES: &[ModeInfo] = &[
    ModeInfo { flag: "--refactor-sound-dynamic", suite: "refactor_sd", owner: "unassigned", calls: "Refactor_sd.do_" },
    ModeInfo { flag: "--cst-search", suite: "cst_search", owner: "E3", calls: "Cst_search_service.{compile_pattern,search,result_to_json}" },
    ModeInfo { flag: "--dump-symbol-info", suite: "dumpsymbolinfo", owner: "E3", calls: "Symbol_info_service_utils.{helper,format_result}" },
    ModeInfo { flag: "--run-simplihack", suite: "simplihack", owner: "unassigned", calls: "Simplihack_prompt.find" },
    ModeInfo { flag: "--glean-index", suite: "", owner: "unassigned (Glean)", calls: "Write_symbol_info.Entrypoint.index_files" },
    ModeInfo { flag: "--glean-sym-hash", suite: "", owner: "unassigned (Glean)", calls: "Write_symbol_info.Entrypoint.sym_hashes" },
    ModeInfo { flag: "--lint", suite: "lint", owner: "LINT", calls: "Linting_main.lint, Server_lint_types.output_text" },
    ModeInfo { flag: "--lint-json", suite: "quickfix_lint", owner: "LINT", calls: "Linting_main.lint, Server_lint_types.output_json" },
    ModeInfo { flag: "--dump-deps", suite: "deps", owner: "unassigned (deps)", calls: "Typing_deps.add_dependency_callback" },
    ModeInfo { flag: "--dump-dep-hashes", suite: "", owner: "unassigned (deps)", calls: "Dep_hash_to_symbol.dump" },
    ModeInfo { flag: "--dump-inheritance", suite: "dump_inheritance", owner: "F6", calls: "Method_jumps.get_inheritance, print_readable" },
    ModeInfo { flag: "--get-some-file-deps", suite: "", owner: "unassigned (needs --root/--naming-table: SS1)", calls: "File_deps.traverse_file_dependencies" },
    ModeInfo { flag: "--ide-code-actions", suite: "ide_code_actions", owner: "F7/F8", calls: "Code_actions_cli_lib.run" },
    ModeInfo { flag: "--ide-diagnostics", suite: "ide_diagnostics", owner: "G1", calls: "Ide_diagnostics_cli_lib.run" },
    ModeInfo { flag: "--ide-signature-help", suite: "ide_signature_help", owner: "F2", calls: "Server_signature_help.go_quarantined, Lsp_fmt.print_signatureHelp" },
    ModeInfo { flag: "--dump-classish-positions", suite: "classish_positions", owner: "F7", calls: "Classish_positions_cli_lib.dump" },
    ModeInfo { flag: "--identify-symbol", suite: "identify_symbol", owner: "F1", calls: "Server_identify_function.go_quarantined_absolute, File_outline.print_def" },
    ModeInfo { flag: "--find-local", suite: "find_local", owner: "F5", calls: "Server_find_locals.go" },
    ModeInfo { flag: "--outline", suite: "outline", owner: "F5", calls: "File_outline.{outline,print}" },
    ModeInfo { flag: "--outline-for-agents", suite: "outline_for_agents", owner: "F5", calls: "Outline_for_agents.outline" },
    ModeInfo { flag: "--nast", suite: "nast", owner: "unassigned (Naming_ast_print)", calls: "Naming.program, Naming_ast_print.print_nast" },
    ModeInfo { flag: "--tast", suite: "tast, holes", owner: "unassigned (Typing_ast_print)", calls: "Typing_toplevel.nast_to_tast, Tast_expand, Typing_ast_print.print_tast" },
    ModeInfo { flag: "--infer-dynamic", suite: "infer_dynamic", owner: "E3", calls: "Typing_shadow_solver.{solve,solution_to_json}" },
    ModeInfo { flag: "--stripped-tast", suite: "", owner: "unassigned (Typing_ast_print)", calls: "Tast.to_nast, Nast.show_program" },
    ModeInfo { flag: "--find-refs", suite: "find_refs", owner: "F6", calls: "Server_find_refs.{go_from_file_ctx,go,to_absolute}, Find_refs_wire_format.CliHumanReadable.print_results" },
    ModeInfo { flag: "--go-to-impl", suite: "go_to_impl", owner: "F6", calls: "Server_find_refs.go_from_file_ctx, Server_go_to_impl.go" },
    ModeInfo { flag: "--highlight-refs", suite: "highlight_refs", owner: "F5", calls: "Ide_highlight_refs.go_quarantined" },
    ModeInfo { flag: "--get-member", suite: "", owner: "F0", calls: "Decl_provider.get_class, Typing_print.full_strip_ns_decl" },
    ModeInfo { flag: "--hover", suite: "hover", owner: "F2", calls: "Ide_hover.go_quarantined, Hover_service.as_marked_string_list" },
    ModeInfo { flag: "--enforcement", suite: "enforcement", owner: "E3", calls: "Server_enforcement_at_pos.go_ctx" },
    ModeInfo { flag: "--enforcement-at-caret-batch", suite: "enforcement_batch", owner: "E3", calls: "Server_enforcement_at_pos.go_ctx" },
    ModeInfo { flag: "--fix", suite: "quickfixes", owner: "F7", calls: "Eager_quickfix_test_util.{of_quickfix,apply_all}" },
    ModeInfo { flag: "--remove-dead-unsafe-casts", suite: "remove_dead_unsafe_casts", owner: "E3", calls: "Remove_dead_unsafe_casts.get_patches, codemod" },
    ModeInfo { flag: "--count-imprecise-types", suite: "count_imprecise_types", owner: "unassigned", calls: "Count_imprecise_types.{count,json_of_results}" },
    ModeInfo { flag: "--map-reduce", suite: "map_reduce", owner: "unassigned", calls: "Map_reduce.{map,reduce,to_ffi}" },
    // hh_single_complete (`hh single-complete`)
    ModeInfo { flag: "--auto-complete", suite: "autocomplete", owner: "F3", calls: "Server_auto_complete.{get_autocomplete_context,go_at_auto332_ctx}" },
    ModeInfo { flag: "--resolve", suite: "", owner: "F3", calls: "Server_auto_complete.{go_at_auto332_ctx,get_signature}" },
    ModeInfo { flag: "--xhp-close", suite: "autoclose", owner: "F4", calls: "Autoclose_tags.go_xhp_close_tag" },
    ModeInfo { flag: "--search", suite: "", owner: "F4", calls: "Ide_search.go" },
    ModeInfo { flag: "--auto-complete-show-glean", suite: "", owner: "unassigned (Glean)", calls: "Glean_autocomplete_query.make_symbols_query" },
    ModeInfo { flag: "--search-show-glean", suite: "", owner: "unassigned (Glean)", calls: "Glean_autocomplete_query.make_symbols_query" },
    ModeInfo { flag: "--find-refs-show-glean", suite: "", owner: "unassigned (Glean)", calls: "Glean_autocomplete_query.make_refs_query" },
];

/// The flag and the owner of a mode, for [`not_ported`].
fn flag_and_owner(mode: &Mode) -> (&'static str, &'static str) {
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
    owner_of_flag(flag)
}

fn owner_of_flag(flag: &'static str) -> (&'static str, &'static str) {
    let owner = MODES
        .iter()
        .find(|m| m.flag == flag)
        .map_or("unassigned", |m| m.owner);
    (flag, owner)
}

/// The error of a mode whose service is not ported yet: `hh` prints it as
/// `hh: mode not ported: OWNER (FLAG)` on stderr and exits with 2, as for a
/// flag it cannot parse. The suite runner (`hh/suite.py`) counts the tests
/// that end so as "not-ported".
pub fn not_ported(owner: &str, flag: &str) -> anyhow::Error {
    anyhow::anyhow!("mode not ported: {owner} ({flag})")
}

fn mode_not_ported(mode: &Mode) -> anyhow::Error {
    let (flag, owner) = flag_and_owner(mode);
    not_ported(owner, flag)
}

// ---------------------------------------------------------------------------
// Positions given by markers in the source (`caret_pos` and friends)

/// `String.split_lines`: the lines of `src`, without their `\n` (or `\r\n`);
/// no last empty line after a final newline.
fn split_lines(src: &[u8]) -> Vec<&[u8]> {
    if src.is_empty() {
        return vec![];
    }
    let src = src.strip_suffix(b"\n").unwrap_or(src);
    src.split(|&c| c == b'\n')
        .map(|l| l.strip_suffix(b"\r").unwrap_or(l))
        .collect()
}

fn is_substring(line: &[u8], marker: &str) -> bool {
    let marker = marker.as_bytes();
    marker.is_empty() || line.windows(marker.len()).any(|w| w == marker)
}

/// `caret_pos src marker`: the position the `^` of the first line that
/// contains `marker` points at. The line is the 0-based index of the marker
/// line, given as one-based: the line *above* the marker. (The OCaml raises
/// `Option.value_exn` when the line has no `^`.)
pub fn caret_pos(src: &[u8], marker: &str) -> Option<position::T> {
    let (line_num, line_src) = split_lines(src)
        .into_iter()
        .enumerate()
        .find(|(_, line)| is_substring(line, marker))?;
    let col_num = line_src
        .iter()
        .position(|&c| c == b'^')
        .expect("Option.value_exn: no '^' on the caret line");
    Some(position::from_one_based(line_num as isize, col_num as isize + 1))
}

/// `caret_pos_exn`: given source code containing a caret marker (e.g.
/// `"^ hover-at-caret"`), the line and column of the position indicated.
pub fn caret_pos_exn(src: &[u8], marker: &str) -> anyhow::Result<position::T> {
    caret_pos(src, marker).ok_or_else(|| {
        anyhow::anyhow!(
            "Could not find any occurrence of '{}' in source code",
            marker
        )
    })
}

/// `all_caret_positions`: like [`caret_pos`], for every line that contains
/// the marker (and a `^`).
pub fn all_caret_positions(src: &[u8], marker: &str) -> Vec<position::T> {
    split_lines(src)
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
    let lines = split_lines(src);
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
                anyhow::anyhow!(
                    "could not find pair '{}','{}' nor '{}'",
                    start_marker,
                    end_marker,
                    hover_at_caret_marker
                )
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
    pub parse_errors: diagnostics_state::T,
    pub max_errors: Option<usize>,
    pub error_format: diagnostics_state::Format,
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
            _ => anyhow::bail!("Only single file expected"),
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
            // (F7: the code actions are `server`-only, as the `Lsp` types.)
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
                    crate::rt::yojson_ext::pretty_to_string(&crate::lsp_fmt::print_signatureHelp(
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
                crate::typing_log::out_channel.with(|c| *c.borrow_mut() = Box::new(log_oc));
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
            f6::with_hhi_root(&input, || f6::find_refs(&input, path, pos))??;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::GoToImpl(pos) => {
            let filename = input.expect_single_file()?;
            f6::with_hhi_root(&input, || f6::go_to_impl(&input, filename, pos))??;
            Ok(OK)
        }
        #[cfg(feature = "server")]
        Mode::DumpInheritance => {
            f6::dump_inheritance(&input)?;
            Ok(OK)
        }
        #[cfg(not(feature = "server"))]
        Mode::FindRefs(_) | Mode::GoToImpl(_) => {
            // (F6's services are behind `server`.)
            let _ = input.expect_single_file()?;
            Err(mode_not_ported(mode))
        }
        Mode::Lint | Mode::LintJson => {
            // LINT: `Linting_main.lint ctx fn content` for each of
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
                let code = crate::server_lint::hh_single_lint(
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
        // ---- E3: --enforcement* ----
        Mode::Enforcement(None) if batch_mode => {
            for filename in filenames {
                let out = format!("{}{}", relative_path::to_absolute(filename), out_extension);
                let mut oc = std::fs::File::create(out)?;
                // `Typing_log.out_channel := oc`
                let log_oc = oc.try_clone()?;
                crate::typing_log::out_channel.with(|c| *c.borrow_mut() = Box::new(log_oc));
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
                crate::typing_log::out_channel.with(|c| *c.borrow_mut() = Box::new(log_oc));
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
        // ---- end E3 ----
        // ---- F7: --dump-classish-positions ----
        #[cfg(feature = "server")]
        Mode::DumpClassishPositions => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            crate::classish_positions_cli_lib::dump(&ctx, &entry, &path);
            Ok(OK)
        }
        // ---- end F7 ----
        Mode::ApplyQuickfixes => {
            let path = input.expect_single_file()?;
            let (ctx, _entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let (errors, _) = compute_tasts(Some(false), &ctx, files_info, files_contents);
            // `Relative_path.Map.find files_contents path`
            let src = match files_contents.iter().find(|(p, _)| *p == path) {
                Some((_, src)) => src.clone(),
                None => anyhow::bail!("Not_found"),
            };
            let quickfixes: Vec<_> = diagnostics_state::get_diagnostic_list(Some(false), errors)
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
        // ---- E3: --cst-search ----
        Mode::CstSearch => {
            let path = input.expect_single_file()?;
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            // `Sys_utils.read_stdin_to_string () |> Yojson.Safe.from_string`
            let mut stdin = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut stdin)?;
            let json = crate::rt::yojson_ext::from_string(&stdin)
                .map_err(|e| anyhow::anyhow!("Yojson.Json_error: {:?}", e))?;
            let result = crate::cst_search_service::compile_pattern(&ctx, &json).map(|pattern| {
                let result = crate::cst_search_service::search(&ctx, &entry, &pattern);
                crate::rt::yojson_ext::pretty_to_string(&crate::cst_search_service::result_to_json(
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
        // ---- end E3 ----
        // ---- E3: --infer-dynamic[-as-data] ----
        Mode::DumpDynamicInference { as_data } => {
            let ctx = &provider_context::map_tcopt(ctx, |mut tcopt| {
                tcopt.tco_dynamic_inference = true;
                tcopt
            });
            let (_errors, tasts) = compute_tasts(None, ctx, files_info, files_contents);
            let print_json = |json: &crate::yojson::safe::T| {
                println!("{}", crate::rt::yojson_ext::pretty_to_string(json))
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
        // ---- end E3 ----
        // ---- E3: --nast, --tast, --stripped-tast ----
        Mode::DumpNast => {
            let (errors, nasts) =
                diagnostics_state::do_(None, || create_nasts(ctx, files_info));
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
            print_errors_if_present(diagnostics_state::merge(parse_errors.clone(), errors));
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
                    None => anyhow::bail!("Not_found"),
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
        // ---- end E3 ----
        _ => Err(mode_not_ported(mode)),
    }
}

// ---- E3: helpers of the AST printing modes ----

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

/// `print_errors_if_present`
fn print_errors_if_present(errors: diagnostics_state::T) {
    if !diagnostics_state::has_no_errors_or_warnings(None, &errors) {
        let errors_output =
            convert_errors_to_string(&diagnostics_state::get_sorted_diagnostic_list(None, errors));
        println!("Errors:");
        for err_output in errors_output {
            println!("  {}", err_output);
        }
    }
}

/// `Diagnostics.convert_errors_to_string` (without `~include_filename`):
/// for each error, its claim and reasons as `Pos.pp pos` and the message,
/// then its custom messages.
fn convert_errors_to_string(errors: &[oxidized::diagnostics::Diagnostic]) -> Vec<String> {
    let mut res = vec![];
    for err in errors {
        let msgs = std::iter::once(&err.claim).chain(err.reasons.iter());
        for oxidized::message::Message(pos, msg) in msgs {
            res.push(format!(
                "{} {}",
                crate::ast_show::show_pos(pos),
                String::from_utf8_lossy(msg)
            ));
        }
        res.extend(err.custom_msgs.iter().cloned());
    }
    res
}

/// `compute_tasts_expand_types`: the TASTs of [`compute_tasts`], with all
/// type variables expanded (`Tast_expand.expand_program`).
fn compute_tasts_expand_types(
    ctx: &provider_context::T,
    files_info: &[relative_path::T],
    interesting_files: &[(relative_path::T, bstr::BString)],
) -> (
    diagnostics_state::T,
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

// ---- end E3 ----

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
            for e in diagnostics_state::get_sorted_diagnostic_list(None, syntax_errors) {
                diagnostics_state::add_diagnostic(e);
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
    diagnostics_state::T,
    Vec<(relative_path::T, Vec<crate::tast::Def>)>,
) {
    diagnostics_state::do_(drop_fixmed, || {
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
                None => crate::pos::info_raw(&crate::pos::none).1,
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
            anyhow::bail!(
                "Failure(\"tried to apply quickfix edit with invalid pos 'Pos.none' and text '{}'\")",
                new_text
            )
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

/// F6's modes (`--find-refs`, `--go-to-impl`, `--dump-inheritance`): the
/// glue of `hh_single_type_check.ml`'s `handle_mode` around
/// `Server_find_refs`, `Server_go_to_impl` and `Method_jumps`.
#[cfg(feature = "server")]
mod f6 {
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

    /// `Hhi.get_hhi_root ()` of `hh_single_type_check`'s `main_hack`, and
    /// the magic and extra builtins it writes there: the services read the
    /// builtins as files (an entry of the context reads its file), so they
    /// are written to a new directory, which the `Hhi` prefix names while
    /// `f` runs. (This `hh single` reads them from the binary otherwise;
    /// `Pos.string` strips the directory, so the output is the same.)
    pub fn with_hhi_root<A>(input: &Input, f: impl FnOnce() -> A) -> anyhow::Result<A> {
        use ::file_provider::FileProvider as _;
        let dir = std::env::temp_dir().join(format!("hh_single_hhi_{}", std::process::id()));
        std::fs::create_dir_all(&dir)?;
        for path in &input.builtins {
            if path.prefix() != relative_path::Prefix::Hhi {
                continue;
            }
            let contents = input
                .ctx
                .files
                .get(::pos::RelativePath::from(path))
                .unwrap_or_default();
            let file = dir.join(path.path());
            if let Some(parent) = file.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&file, &contents)?;
        }
        let old = relative_path::path_of_prefix(relative_path::Prefix::Hhi);
        relative_path::set_path_prefix(relative_path::Prefix::Hhi, &dir);
        let r = f();
        if let Ok(old) = old {
            relative_path::set_path_prefix(relative_path::Prefix::Hhi, std::path::Path::new(&old));
        }
        let _ = std::fs::remove_dir_all(&dir);
        Ok(r)
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
            ctx.build_dep_hash_index();
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
                        (_env, Retry) => anyhow::bail!("Failure: didn't expect retry"),
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
                    (_env, Retry) => anyhow::bail!("Failure: didn't expect retry"),
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
            ctx.build_dep_hash_index();
        }
        let naming_table = crate::naming_table::create(files_info(input));
        let builtins: std::collections::BTreeSet<&relative_path::T> = input.builtins.iter().collect();
        let mut result = Ok(());
        crate::naming_table::iter(&naming_table, |fn_, fileinfo| {
            if result.is_err() || builtins.contains(fn_) {
                return;
            }
            let mut go = |find_children: bool| -> Result<(), crate::naming_table::FileInfoNotFound> {
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
            anyhow::anyhow!("Naming_table.File_info_not_found")
        })
    }
}

/// `hh_single_complete.ml`: `type mode` and `handle_mode`. (F3: the
/// autocomplete and resolve handlers and the forward naming table.)
pub mod complete {
    /// `type mode` of `hh_single_complete.ml`.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Mode {
        NoMode,
        Autocomplete { is_manually_invoked: bool },
        AutocompleteGlean { dry_run: bool },
        Search { glean_only: bool, dry_run: bool },
        FindrefsGlean { dry_run: bool },
        Resolve { is_manually_invoked: bool },
        XhpClose,
    }

    fn flag(mode: &Mode) -> &'static str {
        match mode {
            Mode::NoMode => "",
            Mode::Autocomplete { .. } => "--auto-complete",
            Mode::AutocompleteGlean { .. } => "--auto-complete-show-glean",
            Mode::Search {
                glean_only: false, ..
            } => "--search",
            Mode::Search { .. } => "--search-show-glean",
            Mode::FindrefsGlean { .. } => "--find-refs-show-glean",
            Mode::Resolve { .. } => "--resolve",
            Mode::XhpClose => "--xhp-close",
        }
    }

    /// The options `parse_options` of `hh_single_complete.ml` makes:
    /// `Global_options.set` on the default, with the parser options of its
    /// flags (no `Server_config.load_config`: it has no `--config`).
    pub struct Flags {
        pub disable_xhp_element_mangling: bool,
        pub disable_xhp_children_declarations: bool,
        pub enable_xhp_class_modifier: bool,
        pub auto_namespace_map: Option<Vec<(String, String)>>,
        pub saved_state_manifold_api_key: Option<String>,
        pub glean_reponame: String,
        pub log_levels: std::collections::BTreeMap<String, isize>,
    }

    pub fn make_tcopt(flags: &Flags) -> oxidized::global_options::GlobalOptions {
        use oxidized::global_options::GlobalOptions;
        let default = GlobalOptions::default();
        let po = oxidized::parser_options::ParserOptions {
            disable_xhp_element_mangling: flags.disable_xhp_element_mangling,
            disable_xhp_children_declarations: flags.disable_xhp_children_declarations,
            enable_xhp_class_modifier: flags.enable_xhp_class_modifier,
            everything_sdt: true,
            auto_namespace_map: flags
                .auto_namespace_map
                .clone()
                .unwrap_or_else(|| default.po.auto_namespace_map.clone()),
            ..default.po.clone()
        };
        let mut tco_saved_state = default.tco_saved_state.clone();
        // `Global_options.with_saved_state_manifold_api_key`
        tco_saved_state.loading.saved_state_manifold_api_key =
            flags.saved_state_manifold_api_key.clone();
        GlobalOptions {
            po,
            tco_saved_state,
            allowed_fixme_codes_strict: Default::default(),
            glean_reponame: flags.glean_reponame.clone(),
            log_levels: flags.log_levels.iter().map(|(k, v)| (k.clone(), *v)).collect(),
            ..default
        }
    }

    /// What `decl_and_run_mode` gives `handle_mode`.
    pub struct Input {
        pub ctx: crate::provider_context::T,
        /// The files of the command line (`fn_ref`, the last one first).
        pub filenames: Vec<crate::relative_path::T>,
        pub sienv: crate::search_utils::SiEnv,
        /// The forward naming table (NAMING PHASE 4: `Naming_table.create
        /// files_info`, an unbacked table).
        pub naming_table: crate::naming_table::T,
    }

    /// The addenda `hh_single_complete.ml` feeds its symbol index with
    /// (`parse_and_name`, line 315: `Direct_decl_parser.decls_to_addenda decls`
    /// on `Direct_decl_utils.direct_decl_parse`): a `filter_map` over
    /// `pfh_decls`, the list the FFI (`hh_parse_and_hash_decls_ffi`) makes of
    /// `ParsedFileWithHashes`, which keeps its decls in REVERSE lexical order
    /// for the OCaml (`oxidized/manual/direct_decl_parser.rs`, "so that as
    /// `OcamlReverseParsedFileWithHashes` we ffi correctly to ocaml"). So:
    /// reverse lexical order. (The IDE daemon does not use this function: it
    /// indexes the Rust `si_addendum::get_si_addenda`, forward order:
    /// `client_ide_init.ml:144-148`, `client_ide_incremental.ml:132-140`.)
    /// `decls` are `decl_parser`'s, in forward lexical order.
    pub fn addenda_of_parse(
        decls: &[ty::decl::shallow::NamedDecl<crate::ctx::R>],
    ) -> Vec<crate::file_info::SiAddendum> {
        let mut addenda = crate::symbol_index_core::get_si_addenda(decls);
        addenda.reverse();
        addenda
    }

    /// The `File_info.t` of a file, as `Direct_decl_parser.decls_to_fileinfo`
    /// makes it, as far as the modes read it (the names). (F3, until N1's
    /// `direct_decl_service::file_info_of_decls` is in.)
    pub fn file_info_of_decls(
        path: &crate::relative_path::T,
        decls: &[ty::decl::shallow::NamedDecl<crate::ctx::R>],
    ) -> crate::file_info::T {
        use std::sync::Arc;

        use ty::decl::shallow::NamedDecl;

        use crate::file_info::Id;
        use crate::file_info::NameType;
        let path = Arc::new(path.clone());
        let id = |name_type: NameType, name: &str| Id {
            pos: crate::file_info::Pos::File(name_type, Arc::clone(&path)),
            name: name.to_string(),
            decl_hash: None,
        };
        let mut ids = crate::file_info::Ids {
            funs: vec![],
            classes: vec![],
            typedefs: vec![],
            consts: vec![],
            modules: vec![],
        };
        // (`decls_to_fileinfo` folds `pfh_decls`, in reverse lexical order,
        // by prepending: the ids are in forward lexical order, as here.)
        for decl in decls {
            match decl {
                NamedDecl::Class(name, _) => ids.classes.push(id(NameType::Class, name.as_str())),
                NamedDecl::Fun(name, _) => ids.funs.push(id(NameType::Fun, name.as_str())),
                NamedDecl::Typedef(name, _) => {
                    ids.typedefs.push(id(NameType::Typedef, name.as_str()))
                }
                NamedDecl::Const(name, _) => ids.consts.push(id(NameType::Const, name.as_str())),
                NamedDecl::Module(name, _) => ids.modules.push(id(NameType::Module, name.as_str())),
            }
        }
        crate::file_info::FileInfo {
            position_free_decl_hash: crate::file_info::HashType(None),
            file_mode: None,
            ids,
            comments: None,
        }
    }

    /// `Multifile.short_suffix`
    fn short_suffix(path: &crate::relative_path::T) -> String {
        crate::multifile::strip_multifile_prefix(&path.path_str())
    }

    /// This helper invokes ServerAutoComplete, with the additional arguments
    /// it needs to describe the "context" of the AUTO332 i.e. surrounding
    /// characters. (F3)
    fn do_auto332(
        ctx: &crate::provider_context::T,
        is_manually_invoked: bool,
        sienv_ref: &mut crate::search_utils::SiEnv,
        naming_table: &crate::naming_table::T,
        path: &crate::relative_path::T,
        contents: &[u8],
    ) -> crate::utils::with_complete_flag::T<Vec<crate::autocomplete_types::AutocompleteItem>> {
        use bstr::ByteSlice;
        // Search backwards: there should only be one /real/ case. If there's multiple,
        // guess that the others are preceding explanation comments
        let offset = contents
            .rfind(crate::autocomplete_types::autocomplete_token)
            .expect("Not_found") as isize;
        let pos = crate::file_content::offset_to_position(&contents.to_str_lossy(), offset);
        let (ctx, entry) = crate::provider_context::add_or_overwrite_entry_contents(
            ctx,
            path.clone(),
            bstr::BString::from(contents.to_vec()),
        );
        let autocomplete_context = crate::server_auto_complete::get_autocomplete_context(
            contents,
            &pos,
            is_manually_invoked,
        );
        crate::server_auto_complete::go_at_auto332_ctx(
            &ctx,
            &entry,
            sienv_ref,
            &autocomplete_context,
            naming_table,
        )
    }

    /// Sort for plausible behavior of a to-spec LSP client - doesn't include
    /// all VSCode behavior.
    fn sort_autocomplete_results(
        mut results: Vec<crate::autocomplete_types::AutocompleteItem>,
    ) -> Vec<crate::autocomplete_types::AutocompleteItem> {
        use crate::autocomplete_types::sort_text;
        // `List.stable_sort`
        results.sort_by(|left, right| {
            let l = sort_text(left).to_ascii_lowercase();
            let r = sort_text(right).to_ascii_lowercase();
            l.as_bytes()
                .cmp(r.as_bytes())
                .then_with(|| left.res_label.as_bytes().cmp(right.res_label.as_bytes()))
        });
        results
    }

    /// The lines after the label, common to `handle_autocomplete` and
    /// `handle_resolve`.
    fn print_item_rest(out: &mut String, r: &crate::autocomplete_types::AutocompleteItem) {
        use crate::autocomplete_types::InsertText;
        for (s, _) in &r.res_additional_edits {
            out.push_str(&format!("  INSERT {}\n", s));
        }
        let insert = match &r.res_insert_text {
            InsertText::InsertLiterally(s) => s,
            InsertText::InsertAsSnippet(s) => &s.snippet,
        };
        out.push_str(&format!("  INSERT {}\n", insert));
        out.push_str(&format!("  {}\n", r.res_detail));
        if let Some(doc) = &r.res_documentation {
            for line in super::split_lines(doc.as_bytes()) {
                out.push_str(&format!("  {}\n", String::from_utf8_lossy(line)));
            }
        }
    }

    fn print_out(out: String) -> anyhow::Result<()> {
        use std::io::Write;
        let mut stdout = std::io::stdout();
        stdout.write_all(out.as_bytes())?;
        stdout.flush()?;
        Ok(())
    }

    fn files_with_token(
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<Vec<(crate::relative_path::T, Vec<u8>)>> {
        use bstr::ByteSlice;
        Ok(file_to_file_list(filename)?
            .into_iter()
            .filter(|(_, contents)| contents.find(crate::autocomplete_types::autocomplete_token).is_some())
            .collect())
    }

    /// This handles "--auto-complete" and "--auto-complete-manually-invoked".
    /// (F3)
    fn handle_autocomplete(
        input: &Input,
        is_manually_invoked: bool,
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<()> {
        let files_with_token = files_with_token(filename)?;
        let show_file_titles = files_with_token.len() > 1;
        for (path, contents) in &files_with_token {
            let mut sienv_ref = input.sienv.clone();
            let result = do_auto332(
                &input.ctx,
                is_manually_invoked,
                &mut sienv_ref,
                &input.naming_table,
                path,
                contents,
            );
            let results = sort_autocomplete_results(result.value);
            let mut out = String::new();
            if show_file_titles {
                out.push_str(&format!("//// {}\n", short_suffix(path)));
            }
            for r in &results {
                out.push_str(&format!("{}\n", r.res_label));
                print_item_rest(&mut out, r);
            }
            print_out(out)?
        }
        Ok(())
    }

    /// This handles "--resolve" which for now, just autocomplete and shows
    /// the results and the signature (next up - docblock!), AKA whatever is
    /// already done in ClientIdeDaemon in response to Completion_resolve
    /// requests. (F3)
    fn handle_resolve(
        input: &Input,
        is_manually_invoked: bool,
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<()> {
        let files_with_token = files_with_token(filename)?;
        let show_file_titles = files_with_token.len() > 1;
        for (path, contents) in &files_with_token {
            let mut sienv_ref = input.sienv.clone();
            let result = do_auto332(
                &input.ctx,
                is_manually_invoked,
                &mut sienv_ref,
                &input.naming_table,
                path,
                contents,
            );
            let mut out = String::new();
            if show_file_titles {
                out.push_str(&format!("//// {}\n", short_suffix(path)));
            }
            for r in &result.value {
                out.push_str(&format!(
                    "{}\n",
                    crate::server_auto_complete::get_signature(&input.ctx, &r.res_fullname)
                        .unwrap_or_else(|| "none".to_string())
                ));
                out.push_str(&format!("{}\n", r.res_fullname));
                out.push_str(&format!("{}\n", r.res_label));
                print_item_rest(&mut out, r);
            }
            print_out(out)?
        }
        Ok(())
    }

    /// `extract_nonblank_lines`: the lines of a file of queries, trimmed,
    /// without blank and `//` lines; a line with a space fails.
    fn extract_nonblank_lines(contents: &[u8]) -> anyhow::Result<Vec<String>> {
        let contents = String::from_utf8_lossy(contents);
        let mut res = vec![];
        for s in crate::string_utils::split_on_newlines(&contents) {
            // `String.strip`: whitespace on both sides.
            let s = s.trim_matches(|c: char| c == ' ' || c == '\t' || c == '\n' || c == '\r');
            if s.is_empty() || s.starts_with("//") {
                continue;
            }
            if s.contains(' ') {
                // `failwith`
                anyhow::bail!(
                    "Failure(\"Files must be either hack with <?hh, or lists of query_text; not {}\")",
                    s
                )
            }
            res.push(s.to_string());
        }
        Ok(res)
    }

    /// `Multifile.file_to_file_list filename` (the file read from disk).
    fn file_to_file_list(
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<Vec<(crate::relative_path::T, Vec<u8>)>> {
        let abs = crate::relative_path::to_absolute(filename);
        let content = std::fs::read(&abs)?;
        Ok(crate::multifile::file_to_file_list(&abs, &content)
            .into_iter()
            .map(|(p, c)| (crate::relative_path::create(filename.prefix(), &p), c))
            .collect())
    }

    /// `handle_xhp_close`
    fn handle_xhp_close(
        ctx: &crate::provider_context::T,
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<()> {
        use crate::provider_context;
        let files_contents = file_to_file_list(filename)?;
        let marker = b"AUTOCLOSE332";
        for (path, contents) in files_contents {
            let Some(offset) = contents.windows(marker.len()).position(|w| w == marker) else {
                continue;
            };
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                path,
                bstr::BString::from(contents.clone()),
            );
            let position = crate::file_content::offset_to_position(
                &String::from_utf8_lossy(&contents),
                offset as isize,
            );
            match crate::autoclose_tags::go_xhp_close_tag(&ctx, &entry, &position) {
                Some(close_tag) => println!("Close Tag: {}", close_tag),
                None => print!("Close Tag: None"),
            }
        }
        Ok(())
    }

    /// `handle_search` (`--search`; the Glean variants are not here).
    fn handle_search(
        ctx: &crate::provider_context::T,
        sienv: &crate::search_utils::SiEnv,
        filename: &crate::relative_path::T,
    ) -> anyhow::Result<()> {
        use std::io::Write;
        let mut queries = vec![];
        for (_path, contents) in file_to_file_list(filename)? {
            if !contents.starts_with(b"<?hh") {
                queries.extend(extract_nonblank_lines(&contents)?);
            }
        }
        for query in queries {
            println!("query: {}", query);
            let mut sienv_ref = sienv.clone();
            let results = crate::ide_search::go(ctx, &query, "", &mut sienv_ref);
            for crate::search_utils::Term {
                name,
                pos,
                result_type,
            } in results
            {
                let filename = crate::pos::filename(&pos);
                let filename = std::path::Path::new(&filename)
                    .file_name()
                    .map(|f| f.to_string_lossy().into_owned())
                    .unwrap_or_default();
                let (line, start_, end_) = crate::pos::info_pos(&pos);
                println!(
                    "  {}:{} - {}:{}:{}-{}",
                    name,
                    crate::file_info::show_si_kind(result_type),
                    filename,
                    line,
                    start_,
                    end_
                );
            }
            std::io::stdout().flush()?;
        }
        Ok(())
    }

    /// `handle_mode mode filenames ctx sienv naming_table`
    pub fn handle_mode(mode: &Mode, input: Input) -> anyhow::Result<u8> {
        let filename = match input.filenames.as_slice() {
            [x] => x.clone(),
            _ => anyhow::bail!("Only single file expected"),
        };
        match mode {
            Mode::NoMode => anyhow::bail!("Exactly one mode must be set up"),
            Mode::XhpClose => {
                handle_xhp_close(&input.ctx, &filename)?;
                Ok(super::OK)
            }
            Mode::Autocomplete {
                is_manually_invoked,
            } => {
                handle_autocomplete(&input, *is_manually_invoked, &filename)?;
                Ok(super::OK)
            }
            Mode::Resolve {
                is_manually_invoked,
            } => {
                handle_resolve(&input, *is_manually_invoked, &filename)?;
                Ok(super::OK)
            }
            Mode::Search {
                glean_only: false, ..
            } => {
                handle_search(&input.ctx, &input.sienv, &filename)?;
                Ok(super::OK)
            }
            _ => {
                let (flag, owner) = super::owner_of_flag(flag(mode));
                Err(super::not_ported(owner, flag))
            }
        }
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
        let complete = complete::addenda_of_parse(&decls);
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
        assert_eq!(
            find_ide_range_exn(b"<?hh\n").unwrap_err().to_string(),
            "could not find pair '/*range-start*/','/*range-end*/' nor '^ at-caret'"
        );
    }

    #[test]
    fn split_lines_as_ocaml() {
        assert_eq!(split_lines(b""), Vec::<&[u8]>::new());
        assert_eq!(split_lines(b"a\n"), vec![b"a" as &[u8]]);
        assert_eq!(split_lines(b"a\n\nb"), vec![b"a" as &[u8], b"", b"b"]);
        assert_eq!(split_lines(b"a\r\nb\n"), vec![b"a" as &[u8], b"b"]);
    }
}
