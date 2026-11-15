// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_docblock_at.ml`.

use std::collections::BTreeMap;
use std::sync::Arc;
use std::sync::LazyLock;

use oxidized::ast_defs::ClassishKind;
use oxidized::file_info::SiKind;
use parser_core_types::positioned_syntax::PositionedSyntax;

use crate::ast_provider;
use crate::decl_entry;
use crate::decl_provider;
use crate::docblock_finder;
use crate::docblock_service;
use crate::file_content::position;
use crate::file_info;
use crate::folded_class as cls;
use crate::full_fidelity_source_text;
use crate::naming_provider;
use crate::pos;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::server_symbol_definition;
use crate::symbol_definition;
use crate::symbol_index_core;
use crate::utils;

/// `Docblock_finder.get_docblock` of a node of the CST of `entry`.
fn get_docblock_of_entry(entry: &provider_context::Entry, node: &PositionedSyntax) -> Option<String> {
    let source_text = ast_provider::compute_source_text(entry);
    docblock_finder::get_docblock(&full_fidelity_source_text::source_text(&source_text), node)
}

fn get_all_ancestors(ctx: &provider_context::T, class_name: &str) -> Vec<cls::T> {
    let get_cinfo = |cname: &str| decl_entry::to_option(decl_provider::get_class(None, ctx, cname));
    match get_cinfo(class_name) {
        None => vec![],
        Some(cinfo) => cls::all_ancestor_names(&cinfo)
            .iter()
            .filter_map(|n| get_cinfo(n))
            .collect(),
    }
}

fn get_docblock_for_member(
    ctx: &provider_context::T,
    class_info: &cls::T,
    member_name: &str,
) -> Option<String> {
    let member = cls::get_method(class_info, member_name)?;
    match member.ce_type.node_ref() {
        ty::decl::Ty_::Tfun(_) if cls::name(class_info) == member.ce_origin => {
            let pos = naming_provider::resolve_position(ctx, &member.ce_pos);
            let path = pos.filename().clone();
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path);
            let node = server_symbol_definition::get_definition_cst_node_ctx(
                &ctx,
                &entry,
                &symbol_definition::Kind::<Pos>::Member {
                    member_kind: symbol_definition::MemberKind::Method,
                    class_name: String::new(),
                },
                &pos,
            )?;
            get_docblock_of_entry(&entry, &node)
        }
        _ => None,
    }
}

fn render_ancestor_docblocks(docblocks: Vec<(String, String)>) -> Option<String> {
    let mut docblocks_to_ancestor: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (class_name, docblock) in docblocks {
        // `class_name :: existing_ancestors`
        docblocks_to_ancestor
            .entry(docblock)
            .or_default()
            .insert(0, class_name);
    }
    // `S_map.elements`: in decreasing order of the keys.
    let pairs: Vec<(String, Vec<String>)> = docblocks_to_ancestor.into_iter().rev().collect();
    match pairs.as_slice() {
        [] => None,
        [(docblock, _)] => Some(docblock.clone()),
        docblock_ancestors_pairs => Some(
            docblock_ancestors_pairs
                .iter()
                .map(|(docblock, ancestors)| {
                    let ancestors_str = ancestors
                        .iter()
                        .map(|a| utils::strip_ns(a))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}\n(from {})", docblock, ancestors_str)
                })
                .collect::<Vec<_>>()
                .join("\n\n---\n\n"),
        ),
    }
}

fn fallback(ctx: &provider_context::T, class_name: &str, member_name: &str) -> Option<String> {
    let ancestors = get_all_ancestors(ctx, class_name);
    // `all_interfaces_or_first_class_docblock [] ancestors`
    let mut seen_interfaces: Vec<(String, String)> = vec![];
    let mut result = None;
    for ancestor in &ancestors {
        match get_docblock_for_member(ctx, ancestor, member_name) {
            None => {}
            Some(docblock) => match cls::kind(ancestor) {
                ClassishKind::Cclass(_) => {
                    result = Some(vec![(cls::name(ancestor), docblock)]);
                    break;
                }
                ClassishKind::Ctrait
                | ClassishKind::Cinterface
                | ClassishKind::Cenum
                | ClassishKind::CenumClass(_) => {
                    // `(name, docblock) :: seen_interfaces`
                    seen_interfaces.insert(0, (cls::name(ancestor), docblock));
                }
            },
        }
    }
    render_ancestor_docblocks(result.unwrap_or(seen_interfaces))
}

/// `Str.regexp` of the OCaml, as a multi-line `regex` (`^`/`$` at line
/// boundaries, `.` not matching '\n', as in `Str`).
fn str_regex(re: &str) -> regex::Regex {
    regex::Regex::new(&format!("(?m){}", re)).unwrap()
}

static RE_GENERATED: LazyLock<regex::Regex> =
    LazyLock::new(|| str_regex(r"^This file is generated\.(?:.*\n)*^@generated.*$"));

static RE_PARTIALLY_GENERATED: LazyLock<regex::Regex> = LazyLock::new(|| {
    str_regex(r"^This file is partially generated\.(?:.*\n)*^@partially-generated.*$")
});

static RE_COPYRIGHT1: LazyLock<regex::Regex> = LazyLock::new(|| str_regex(r"^\(c\) Facebook.*$"));

static RE_COPYRIGHT2: LazyLock<regex::Regex> =
    LazyLock::new(|| str_regex(r"^Copyright [0-9][0-9][0-9][0-9].*$"));

static RE_COPYRIGHT3: LazyLock<regex::Regex> = LazyLock::new(|| str_regex(r"^Copyright \(c\).*$"));

/// `String.strip` (Core): drops what `Char.is_whitespace` says at both ends.
fn core_string_strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\x0b' | '\x0c' | '\r'))
}

/// strips boilerplate copyright/codegen comments
pub fn clean_comments(s: &str) -> String {
    let s = RE_GENERATED.replace_all(s, "");
    let s = RE_PARTIALLY_GENERATED.replace_all(&s, "");
    let s = RE_COPYRIGHT1.replace_all(&s, "");
    let s = RE_COPYRIGHT2.replace_all(&s, "");
    let s = RE_COPYRIGHT3.replace_all(&s, "");
    core_string_strip(&s).to_string()
}

fn go_comments_from_source_text(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
    kind: &symbol_definition::Kind<Pos>,
) -> Option<String> {
    // `{ pos_fname = filename; pos_lnum; pos_cnum; pos_bol = 0 }`, start and
    // end: only its line and column are read (`Pos.info_pos`).
    let (pos_lnum, pos_cnum) = position::line_column_one_based(pos);
    let pos = pos::make_from_lnum_bol_offset(
        entry.path.clone(),
        (pos_lnum, 0, pos_cnum),
        (pos_lnum, 0, pos_cnum),
    );
    let ffps = server_symbol_definition::get_definition_cst_node_ctx(ctx, entry, kind, &pos)?;
    get_docblock_of_entry(entry, &ffps).map(|db| clean_comments(&db))
}

/// Returns the documentation comments for the given symbol or expression.
pub fn go_comments_for_symbol_ctx<P: pos::APos>(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    def: &symbol_definition::T<P>,
    base_class_name: Option<&str>,
) -> Option<String> {
    match &def.docblock {
        Some(db) => Some(clean_comments(db)),
        None => {
            let ffps =
                server_symbol_definition::get_definition_cst_node_ctx(ctx, entry, &def.kind, &def.pos)?;
            match get_docblock_of_entry(entry, &ffps) {
                Some(db) => Some(clean_comments(&db)),
                None => match (&def.kind, base_class_name) {
                    (
                        symbol_definition::Kind::Member {
                            member_kind: symbol_definition::MemberKind::Method,
                            ..
                        },
                        Some(base_class_name),
                    ) => fallback(ctx, base_class_name, &def.name),
                    _ => None,
                },
            }
        }
    }
}

/// Locate a symbol and return file, line, column, and base_class
fn go_locate_symbol(
    ctx: &provider_context::T,
    symbol: &str,
    kind: SiKind,
) -> docblock_service::DbsSymbolLocationResult {
    // Look up this class name
    let (path, pos) = symbol_index_core::get_position_for_symbol(ctx, symbol, kind)?;
    let filename = relative_path::to_absolute(&path);
    // Determine base class properly
    let base_class_name = match kind {
        SiKind::SIClass
        | SiKind::SIEnum
        | SiKind::SIFunction
        | SiKind::SIGlobalConstant
        | SiKind::SIInterface
        | SiKind::SITrait
        | SiKind::SITypedef => Some(utils::add_ns(symbol)),
        _ => None,
    };
    // Here are the results
    Some(docblock_service::DbsSymbolLocation {
        dbs_filename: filename,
        dbs_pos: pos,
        dbs_base_class: base_class_name,
    })
}

fn symboldefinition_kind_from_si_kind(kind: SiKind) -> symbol_definition::Kind<Pos> {
    use symbol_definition::ClassishKind as CK;
    use symbol_definition::Kind as K;
    use symbol_definition::MemberKind as MK;
    let classish = |classish_kind| K::Classish {
        members: vec![],
        classish_kind,
    };
    let member = |member_kind| K::Member {
        class_name: String::new(),
        member_kind,
    };
    match kind {
        SiKind::SIClass | SiKind::SIUnknown | SiKind::SIXHP => classish(CK::Class),
        SiKind::SIInterface => classish(CK::Interface),
        SiKind::SIEnum => classish(CK::Enum),
        SiKind::SITrait => classish(CK::Trait),
        SiKind::SIMixed => K::LocalVar,
        SiKind::SIFunction => K::Function,
        SiKind::SITypedef => K::Typedef,
        SiKind::SIGlobalConstant => K::GlobalConst,
        SiKind::SIClassMethod => member(MK::Method),
        SiKind::SILiteral => K::LocalVar,
        SiKind::SIClassConstant => member(MK::ClassConst),
        SiKind::SIProperty => member(MK::Property),
        SiKind::SILocalVariable => K::LocalVar,
        SiKind::SIConstructor => member(MK::Method),
        SiKind::SIKeyword => panic!("Cannot look up a keyword"),
        SiKind::SINamespace => panic!("Cannot look up a namespace"),
    }
}

/// Returns the docblock from these file contents
pub fn go_docblock_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &position::T,
    kind: SiKind,
) -> docblock_service::Result {
    let def_kind = symboldefinition_kind_from_si_kind(kind);
    match go_comments_from_source_text(ctx, entry, pos, &def_kind) {
        None => {
            // Special case: Classes with an assumed default constructor
            if file_info::equal_si_kind(kind, SiKind::SIConstructor) {
                go_docblock_ctx(ctx, entry, pos, SiKind::SIClass)
            } else {
                vec![]
            }
        }
        Some(comments) if comments.is_empty() => vec![],
        Some(comments) => vec![docblock_service::DocblockElement::Markdown(comments)],
    }
}

/// Simplified one-step symbol/docblock
pub fn go_docblock_for_symbol(
    ctx: &provider_context::T,
    symbol: &str,
    kind: SiKind,
) -> docblock_service::Result {
    // Shortcut for namespaces, since they don't have locations
    if file_info::equal_si_kind(kind, SiKind::SINamespace) {
        let namespace_declaration = format!("namespace {};", symbol);
        vec![docblock_service::DocblockElement::HackSnippet(namespace_declaration)]
    } else if file_info::equal_si_kind(kind, SiKind::SIKeyword) {
        let txt = format!("Hack language keyword: {};", symbol);
        vec![docblock_service::DocblockElement::HackSnippet(txt)]
    } else {
        match go_locate_symbol(ctx, symbol, kind) {
            None => {
                let msg = format!(
                    "Could not find the symbol '{}' (expected to be a {}). This symbol may need namespace information (e.g. HH\\a\\b\\c) to resolve correctly. You can also consider rebasing.",
                    symbol,
                    file_info::show_si_kind(kind)
                );
                vec![docblock_service::DocblockElement::Markdown(msg)]
            }
            Some(location) => {
                let (ctx, entry) = provider_context::add_entry_if_missing(
                    ctx,
                    relative_path::create_detect_prefix(&location.dbs_filename),
                );
                go_docblock_ctx(&ctx, &entry, &location.dbs_pos, kind)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean() {
        assert_eq!(clean_comments("Copyright 2015 Foo\nHello"), "Hello");
        assert_eq!(
            clean_comments("This file is generated.\nmore\n@generated SignedSource\nDoc"),
            "Doc"
        );
        assert_eq!(clean_comments("  (c) Facebook x\nkeep"), "(c) Facebook x\nkeep");
    }
}
