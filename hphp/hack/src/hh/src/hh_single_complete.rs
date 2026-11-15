// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `hh_single_complete.ml`: `type mode` and `handle_mode`, the
//! autocomplete and resolve handlers and the forward naming table.

use crate::rt::ocaml_exn::Die;
use crate::rt::ocaml_exn::Uncaught;

pub mod args;

/// `magic_builtins`
pub const MAGIC_BUILTINS: &str = concat!(
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
/// makes it, as far as the modes read it (the names). (A copy of
/// `direct_decl_service::file_info_of_decls`.)
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

/// This helper invokes ServerAutoComplete, with the additional arguments
/// it needs to describe the "context" of the AUTO332 i.e. surrounding
/// characters.
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
        .rfind(crate::autocomplete_types::AUTOCOMPLETE_TOKEN)
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
        for line in crate::rt::ocaml_string::split_lines_bytes(doc.as_bytes()) {
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
        .filter(|(_, contents)| contents.find(crate::autocomplete_types::AUTOCOMPLETE_TOKEN).is_some())
        .collect())
}

/// This handles "--auto-complete" and "--auto-complete-manually-invoked".
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
            out.push_str(&format!("//// {}\n", crate::multifile::short_suffix(path)));
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
/// requests.
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
            out.push_str(&format!("//// {}\n", crate::multifile::short_suffix(path)));
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
            return Err(Uncaught::failure(format!(
                "Files must be either hack with <?hh, or lists of query_text; not {}",
                s
            ))
            .into());
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
        _ => return Err(Die("Only single file expected".to_string()).into()),
    };
    match mode {
        Mode::NoMode => return Err(Die("Exactly one mode must be set up".to_string()).into()),
        Mode::XhpClose => {
            handle_xhp_close(&input.ctx, &filename)?;
            Ok(crate::hh_single_type_check::modes::OK)
        }
        Mode::Autocomplete {
            is_manually_invoked,
        } => {
            handle_autocomplete(&input, *is_manually_invoked, &filename)?;
            Ok(crate::hh_single_type_check::modes::OK)
        }
        Mode::Resolve {
            is_manually_invoked,
        } => {
            handle_resolve(&input, *is_manually_invoked, &filename)?;
            Ok(crate::hh_single_type_check::modes::OK)
        }
        Mode::Search {
            glean_only: false, ..
        } => {
            handle_search(&input.ctx, &input.sienv, &filename)?;
            Ok(crate::hh_single_type_check::modes::OK)
        }
        _ => {
            Err(crate::hh_single_type_check::modes::not_ported(flag(mode)))
        }
    }
}
