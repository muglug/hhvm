// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/outline_for_agents.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F5** (plan §7.3).
//!
//! Generate a compact outline of a Hack file with line range annotations,
//! for AI agents. Helpful for determining which ranges of the file to read.
//!
//! The concrete syntax tree is the Rust parser's (`positioned_parser`, with
//! the default environment, as `Full_fidelity_syntax_tree.make`). The text
//! is bytes, as an OCaml string: the outline is a [`BString`]. The OCaml's
//! exhaustive matches over all the syntax kinds (there to make the compiler
//! catch new constructors) are `_ => ()` here.

use bstr::BString;
use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::lexable_token::LexablePositionedToken;
use parser_core_types::lexable_trivia::LexableTrivium;
use parser_core_types::parser_env::ParserEnv;
use parser_core_types::positioned_syntax::PositionedSyntax as Syn;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;
use parser_core_types::trivia_kind::TriviaKind;
use relative_path::Prefix;

use crate::full_fidelity_source_text;
use crate::relative_path;

/// The source text with its line-break map (`Full_fidelity_source_text.t`
/// has both).
struct Src<'a> {
    text: &'a full_fidelity_source_text::T,
    indexed: IndexedSourceText<'a>,
}

/// `Full_fidelity_source_text.offset_to_position`
fn offset_to_position(src: &Src<'_>, offset: usize) -> (isize, isize) {
    src.indexed.offset_to_position(offset as isize)
}

/// `Base.Char.is_whitespace`
fn is_whitespace(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\x0b' | b'\x0c' | b'\r')
}

/// `Base.String.strip`
fn strip(s: &[u8]) -> &[u8] {
    let start = s.iter().position(|c| !is_whitespace(*c)).unwrap_or(s.len());
    let end = s.iter().rposition(|c| !is_whitespace(*c)).map_or(start, |i| i + 1);
    &s[start..end.max(start)]
}

/// `String.is_substring ~substring`
fn is_substring(s: &[u8], substring: &[u8]) -> bool {
    substring.is_empty() || s.windows(substring.len()).any(|w| w == substring)
}

/// Include preceding doc comments, but not regular comments
fn line_range(src: &Src<'_>, node: &Syn) -> (isize, isize) {
    let trivia_list = match node.leading_token() {
        None => &[][..],
        Some(t) => t.positioned_leading(),
    };
    let source_text = src.indexed.source_text();
    let doc_comment_offset = trivia_list.iter().fold(None, |acc, t| {
        if t.kind() == TriviaKind::DelimitedComment && t.text_raw(source_text).starts_with(b"/**") {
            Some(t.start_offset())
        } else {
            acc
        }
    });
    let start_offset = match doc_comment_offset {
        Some(off) => off,
        None => node.start_offset(),
    };
    let start_line = offset_to_position(src, start_offset).0;
    let end_line = offset_to_position(src, node.end_offset()).0;
    (start_line, end_line)
}

/// Source text of [node] excluding leading/trailing trivia.
fn node_text(src: &Src<'_>, node: &Syn) -> BString {
    full_fidelity_source_text::sub(src.text, node.start_offset() as isize, node.width() as isize)
}

fn stripped_text(src: &Src<'_>, node: &Syn) -> Vec<u8> {
    strip(&node_text(src, node)).to_vec()
}

fn to_line_range_annotation((start_line, end_line): (isize, isize)) -> String {
    if start_line == end_line {
        format!(" | line {}", start_line)
    } else {
        format!(" | lines {}-{}", start_line, end_line)
    }
}

fn is_private(src: &Src<'_>, modifiers: &Syn) -> bool {
    is_substring(&node_text(src, modifiers), b"private")
}

/// Extract just the names from a list of declarators, stripping initializers.
fn declarator_names(src: &Src<'_>, node: &Syn) -> Vec<u8> {
    let name_of_declarator = |d: &Syn| -> Vec<u8> {
        match &d.syntax {
            SyntaxVariant::ConstantDeclarator(c) => stripped_text(src, &c.constant_declarator_name),
            SyntaxVariant::PropertyDeclarator(c) => stripped_text(src, &c.property_name),
            _ => stripped_text(src, d),
        }
    };
    match &node.syntax {
        SyntaxVariant::SyntaxList(items) => {
            let names: Vec<Vec<u8>> = items
                .iter()
                .map(|item| match &item.syntax {
                    SyntaxVariant::ListItem(c) => name_of_declarator(&c.list_item),
                    _ => name_of_declarator(item),
                })
                .collect();
            names.join(&b", "[..])
        }
        _ => stripped_text(src, node),
    }
}

/// `Printf.bprintf buf "%s...%s\n"` with byte-string arguments.
fn bprintf(buf: &mut Vec<u8>, parts: &[&[u8]]) {
    for p in parts {
        buf.extend_from_slice(p);
    }
    buf.push(b'\n');
}

fn write_member(buf: &mut Vec<u8>, indent: &str, src: &Src<'_>, node: &Syn) {
    let suffix = to_line_range_annotation(line_range(src, node));
    let indent = indent.as_bytes();
    let suffix = suffix.as_bytes();
    match &node.syntax {
        SyntaxVariant::MethodishDeclaration(c) => match &c.methodish_function_decl_header.syntax {
            SyntaxVariant::FunctionDeclarationHeader(h) => {
                if !is_private(src, &h.function_modifiers) {
                    bprintf(
                        buf,
                        &[indent, b"function ", &stripped_text(src, &h.function_name), suffix],
                    )
                }
            }
            _ => {}
        },
        SyntaxVariant::PropertyDeclaration(c) => {
            if !is_private(src, &c.property_modifiers) {
                bprintf(
                    buf,
                    &[indent, &declarator_names(src, &c.property_declarators), suffix],
                )
            }
        }
        SyntaxVariant::ConstDeclaration(c) => {
            if !is_private(src, &c.const_modifiers) {
                bprintf(
                    buf,
                    &[indent, b"const ", &declarator_names(src, &c.const_declarators), suffix],
                )
            }
        }
        SyntaxVariant::TypeConstDeclaration(c) => {
            if !is_private(src, &c.type_const_modifiers) {
                bprintf(
                    buf,
                    &[indent, b"const type ", &stripped_text(src, &c.type_const_name), suffix],
                )
            }
        }
        // TraitUse, RequireClause, MethodishTraitResolution,
        // ContextConstDeclaration, RequireClauseConstraint,
        // XHPClassAttributeDeclaration, XHPChildrenDeclaration,
        // XHPCategoryDeclaration, and everything that is not a class body
        // declaration.
        _ => {}
    }
}

fn write_members(buf: &mut Vec<u8>, indent: &str, src: &Src<'_>, elements_node: &Syn) {
    match &elements_node.syntax {
        SyntaxVariant::SyntaxList(items) => {
            for item in items {
                write_member(buf, indent, src, item)
            }
        }
        _ => {}
    }
}

fn write_top_level(buf: &mut Vec<u8>, indent: &str, src: &Src<'_>, node: &Syn) {
    let suffix = to_line_range_annotation(line_range(src, node));
    let indent_b = indent.as_bytes();
    let suffix = suffix.as_bytes();
    match &node.syntax {
        SyntaxVariant::FunctionDeclaration(c) => match &c.function_declaration_header.syntax {
            SyntaxVariant::FunctionDeclarationHeader(h) => bprintf(
                buf,
                &[indent_b, b"function ", &stripped_text(src, &h.function_name), suffix],
            ),
            _ => {}
        },
        SyntaxVariant::ClassishDeclaration(c) => {
            let mods = node_text(src, &c.classish_modifiers);
            let kw = stripped_text(src, &c.classish_keyword);
            let kind = if is_substring(&mods, b"abstract") {
                [&b"abstract "[..], &kw].concat()
            } else {
                kw
            };
            let name = stripped_text(src, &c.classish_name);
            bprintf(buf, &[indent_b, &kind, b" ", &name, suffix]);
            let member_indent = format!("{}  ", indent);
            match &c.classish_body.syntax {
                SyntaxVariant::ClassishBody(b) => {
                    write_members(buf, &member_indent, src, &b.classish_body_elements)
                }
                _ => {}
            }
        }
        SyntaxVariant::EnumDeclaration(c) => {
            let name = stripped_text(src, &c.enum_name);
            bprintf(buf, &[indent_b, b"enum ", &name, suffix]);
            let member_indent = format!("{}  ", indent);
            match &c.enum_enumerators.syntax {
                SyntaxVariant::SyntaxList(items) => {
                    for item in items {
                        match &item.syntax {
                            SyntaxVariant::Enumerator(e) => bprintf(
                                buf,
                                &[member_indent.as_bytes(), &stripped_text(src, &e.enumerator_name)],
                            ),
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        SyntaxVariant::EnumClassDeclaration(c) => {
            let name = stripped_text(src, &c.enum_class_name);
            bprintf(buf, &[indent_b, b"enum class ", &name, suffix]);
            let member_indent = format!("{}  ", indent);
            match &c.enum_class_elements.syntax {
                SyntaxVariant::SyntaxList(items) => {
                    for item in items {
                        match &item.syntax {
                            SyntaxVariant::EnumClassEnumerator(e) => bprintf(
                                buf,
                                &[
                                    member_indent.as_bytes(),
                                    &stripped_text(src, &e.enum_class_enumerator_name),
                                ],
                            ),
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        SyntaxVariant::AliasDeclaration(c) => {
            let kw = stripped_text(src, &c.alias_keyword);
            let name = stripped_text(src, &c.alias_name);
            bprintf(buf, &[indent_b, &kw, b" ", &name, suffix])
        }
        SyntaxVariant::ConstDeclaration(c) => {
            let names = declarator_names(src, &c.const_declarators);
            bprintf(buf, &[indent_b, b"const ", &names, suffix])
        }
        SyntaxVariant::NamespaceDeclaration(c) => {
            let header_text = stripped_text(src, &c.namespace_header);
            bprintf(buf, &[indent_b, &header_text, suffix]);
            match &c.namespace_body.syntax {
                SyntaxVariant::NamespaceBody(b) => {
                    let body_indent = format!("{}  ", indent);
                    match &b.namespace_declarations.syntax {
                        SyntaxVariant::SyntaxList(items) => {
                            for item in items {
                                write_top_level(buf, &body_indent, src, item)
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        SyntaxVariant::ModuleDeclaration(c) => {
            let name = stripped_text(src, &c.module_declaration_name);
            bprintf(buf, &[indent_b, b"module ", &name, suffix])
        }
        SyntaxVariant::ModuleMembershipDeclaration(c) => {
            let name = stripped_text(src, &c.module_membership_declaration_name);
            bprintf(buf, &[indent_b, b"module ", &name, suffix])
        }
        SyntaxVariant::CaseTypeDeclaration(c) => {
            let name = stripped_text(src, &c.case_type_name);
            bprintf(buf, &[indent_b, b"case type ", &name, suffix])
        }
        SyntaxVariant::ContextAliasDeclaration(c) => {
            let name = stripped_text(src, &c.ctx_alias_name);
            bprintf(buf, &[indent_b, b"newctx ", &name, suffix])
        }
        SyntaxVariant::ClassAliasDeclaration(c) => {
            let kw = stripped_text(src, &c.class_alias_keyword);
            let name = stripped_text(src, &c.class_alias_name);
            let orig = stripped_text(src, &c.class_alias_original_name);
            bprintf(buf, &[indent_b, &kw, b" ", &name, b" = ", &orig, suffix])
        }
        // Not top-level declarations.
        _ => {}
    }
}

/// Generate a compact outline of a Hack source file with line range annotations.
pub fn outline(content: &[u8]) -> BString {
    let src_text = full_fidelity_source_text::make(
        &relative_path::create(Prefix::Dummy, "<outline>"),
        content,
    );
    let source_text = full_fidelity_source_text::source_text(&src_text);
    let (root, errors, _state) = positioned_parser::parse_script(&source_text, ParserEnv::default());
    let src = Src {
        text: &src_text,
        indexed: IndexedSourceText::new(source_text.clone()),
    };
    let mut buf: Vec<u8> = Vec::with_capacity(4096 /* getconf PAGE_SIZE */);
    // Check for parse errors and add warning if present
    // (`Syntax_tree.errors tree`: the parser's errors, without the cascading
    // ones; there is one if the parser reported any.)
    if !errors.is_empty() {
        buf.extend_from_slice(b"WARNING: File contains syntax errors. Outline is best-effort.\n\n");
    }
    match &root.syntax {
        SyntaxVariant::Script(s) => match &s.script_declarations.syntax {
            SyntaxVariant::SyntaxList(items) => {
                for item in items {
                    write_top_level(&mut buf, "", &src, item)
                }
            }
            _ => {}
        },
        _ => {}
    }
    BString::from(buf)
}
