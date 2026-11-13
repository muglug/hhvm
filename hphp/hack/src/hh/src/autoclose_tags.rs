// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/autoclose_tags.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F4** (plan §7.3).
//!
//! `Ast_provider.compute_cst` is not in the crate (the entry has no `cst`,
//! see `crate::provider_context`): [`go_xhp_tags`] parses the entry's source
//! text with the Rust parser (`positioned_parser`, with the default parser
//! environment, as `Provider_context.PositionedSyntaxTree.make source_text`)
//! each time.

use std::sync::Arc;

use parser_core_types::parser_env::ParserEnv;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::source_text::SourceText;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::ast_provider;
use crate::file_content;
use crate::full_fidelity_source_text;
use crate::hack_event_logger;
use crate::provider_context;

pub mod autoclose_tag {
    use parser_core_types::positioned_syntax::PositionedSyntax;

    /// `AutocloseTag.result`
    #[derive(Clone, Debug)]
    pub struct Result {
        pub xhp_open: PositionedSyntax,
        pub xhp_open_right_angle: PositionedSyntax,
        pub xhp_close: PositionedSyntax,
        pub insert_text: String,
    }
}

/// `Full_fidelity_positioned_syntax.text`: the bytes of the node (without
/// its trivia), as a string.
fn text(source_text: &SourceText<'_>, node: &PositionedSyntax) -> String {
    String::from_utf8_lossy(source_text.sub(node.start_offset(), node.width())).into_owned()
}

/// Get xhp positions from the FFP for every xhp that is an
/// xhp open tag.
fn all_tags(source_text: &SourceText<'_>, tree: &PositionedSyntax) -> Vec<autoclose_tag::Result> {
    // Walk FFP syntax node [s], tracking the current context [ctx]
    // and accumulate xhp tags.
    fn aux(
        source_text: &SourceText<'_>,
        ctx: Option<()>,
        acc: &mut Vec<autoclose_tag::Result>,
        s: &PositionedSyntax,
    ) {
        match &s.syntax {
            SyntaxVariant::XHPExpression(x) => {
                let xhp_open = &x.xhp_open;
                let xhp_close = &x.xhp_close;
                match &xhp_open.syntax {
                    SyntaxVariant::XHPOpen(o) => {
                        let insert_text =
                            format!("$0</{}>", text(source_text, &o.xhp_open_name));
                        // (`::` prepends: the order of the list is reversed
                        // from the OCaml's; only its length is used.)
                        acc.push(autoclose_tag::Result {
                            xhp_open: xhp_open.clone(),
                            xhp_open_right_angle: o.xhp_open_right_angle.clone(),
                            xhp_close: xhp_close.clone(),
                            insert_text,
                        })
                    }
                    _ => {}
                }
                for child in s.iter_children() {
                    aux(source_text, ctx, acc, child)
                }
            }
            _ => {
                for child in s.iter_children() {
                    aux(source_text, ctx, acc, child)
                }
            }
        }
    }
    let mut acc = vec![];
    aux(source_text, None, &mut acc, tree);
    acc
}

pub fn go_xhp_tags(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Option<autoclose_tag::Result> {
    let source_text = ast_provider::compute_source_text(entry);
    let target_offset = full_fidelity_source_text::position_to_offset(
        &source_text,
        file_content::position::line_column_one_based(pos),
    );
    // `Ast_provider.compute_cst ~ctx ~entry` (TODO in the OCaml: use parser
    // options inside ctx), `Provider_context.PositionedSyntaxTree.root cst`
    let _ = ctx;
    let parser_source_text = full_fidelity_source_text::source_text(&source_text);
    let (tree, _errors, _state) =
        positioned_parser::parse_script(&parser_source_text, ParserEnv::default());
    let all_tags = all_tags(&parser_source_text, &tree);
    let mut xhp_tags: Vec<autoclose_tag::Result> = all_tags
        .into_iter()
        .filter(
            |autoclose_tag::Result {
                 xhp_open,
                 xhp_open_right_angle,
                 xhp_close,
                 ..
             }| {
                // The target offset should be the position after the end of the
                // open right angle
                target_offset == xhp_open_right_angle.end_offset() as isize + 1
                    && xhp_open.end_offset() > xhp_open.start_offset()
                    && xhp_open.end_offset() < xhp_close.end_offset()
            },
        )
        .collect();
    match xhp_tags.len() {
        1 => xhp_tags.pop(),
        0 => None,
        _ => {
            hack_event_logger::invariant_violation_bug(
                None,
                None,
                None,
                None,
                None,
                "Should only find one close tag, found more than 1",
            );
            None
        }
    }
}

pub fn go_xhp_close_tag(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Option<String> {
    let tags = go_xhp_tags(ctx, entry, pos);
    match tags {
        Some(autoclose_tag::Result {
            xhp_open: _,
            xhp_open_right_angle: _,
            xhp_close: _,
            insert_text,
        }) => Some(insert_text),
        None => None,
    }
}

#[cfg(test)]
mod tests {
    use bstr::BString;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn ctx() -> provider_context::T {
        provider_context::empty_for_test(
            Default::default(),
            Default::default(),
            crate::typing_deps::mode::T::InMemoryMode(None),
        )
    }

    /// `Hh_single_complete.handle_xhp_close` on one file (the `--xhp-close`
    /// mode of `hhvm/hphp/hack/test/autoclose`), returning what it prints.
    fn handle_xhp_close(ctx: &provider_context::T, filename: &str) -> Vec<u8> {
        let content = std::fs::read(filename).unwrap();
        let files_contents = crate::multifile::file_to_file_list(filename, &content);
        let mut out = vec![];
        for (path, contents) in files_contents {
            let contents_s = String::from_utf8(contents.clone()).unwrap();
            let Some(offset) = contents_s.find("AUTOCLOSE332") else {
                continue;
            };
            let path = RelativePath::make(Prefix::Dummy, path.into());
            let (ctx, entry) =
                provider_context::add_or_overwrite_entry_contents(ctx, path, BString::from(contents));
            let position = file_content::offset_to_position(&contents_s, offset as isize);
            match go_xhp_close_tag(&ctx, &entry, &position) {
                Some(close_tag) => out.extend(format!("Close Tag: {}\n", close_tag).into_bytes()),
                None => out.extend(b"Close Tag: None"),
            }
        }
        out
    }

    #[test]
    fn test_autoclose_suite() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../test/autoclose");
        let ctx = ctx();
        let mut n = 0;
        let mut entries: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
        entries.sort();
        for p in entries {
            if p.extension().is_some_and(|e| e == "php") {
                let exp = std::fs::read(format!("{}.exp", p.display())).unwrap();
                let out = handle_xhp_close(&ctx, p.to_str().unwrap());
                assert_eq!(BString::from(out), BString::from(exp), "{}", p.display());
                n += 1;
            }
        }
        assert_eq!(n, 6);
    }
}
