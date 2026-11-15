// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The syntax tree hackfmt works on.
//!
//! OCaml hackfmt parses with the Rust full-fidelity parser (by-ref positioned
//! tokens, which only record trivia widths), rescans each token's trivia on
//! demand (`Full_fidelity_positioned_token.leading`/`trailing`), and converts
//! the tree to an editable one (`Syntax_transforms.editable_from_positioned`)
//! before transforming it. This module builds the same editable tree: every
//! token knows its text and its leading and trailing trivia, and every node is
//! a kind plus its children in schema order.

use std::rc::Rc;
use std::sync::Arc;

use bumpalo::Bump;
use parser_core_types::lexable_token::LexableToken;
use parser_core_types::parser_env::ParserEnv;
use parser_core_types::source_text::SourceText;
use parser_core_types::syntax_by_ref::positioned_token::PositionedToken;
use parser_core_types::syntax_by_ref::positioned_value::PositionedValue;
use parser_core_types::syntax_by_ref::syntax::Syntax;
use parser_core_types::syntax_error::SyntaxError;
use parser_core_types::syntax_kind::SyntaxKind;
use parser_core_types::syntax_trait::SyntaxTrait;
use parser_core_types::token_kind::TokenKind;
use parser_core_types::trivia_kind::TriviaKind;
use relative_path::Prefix;
use relative_path::RelativePath;

#[derive(Clone, Debug)]
pub struct Trivia<'a> {
    pub kind: TriviaKind,
    pub text: &'a [u8],
    /// Offset of the trivium in the parsed source.
    pub offset: usize,
}

impl Trivia<'_> {
    pub fn width(&self) -> usize {
        self.text.len()
    }

    pub fn start_offset(&self) -> usize {
        self.offset
    }

    /// `Full_fidelity_positioned_trivia.end_offset`: the offset of the last
    /// character (inclusive).
    pub fn end_offset(&self) -> usize {
        (self.offset + self.text.len()).wrapping_sub(1)
    }
}

#[derive(Clone, Debug)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub text: &'a [u8],
    pub leading: Vec<Trivia<'a>>,
    pub trailing: Vec<Trivia<'a>>,
}

impl Token<'_> {
    pub fn width(&self) -> usize {
        self.text.len()
    }

    pub fn full_width(&self) -> usize {
        trivia_width(&self.leading) + self.text.len() + trivia_width(&self.trailing)
    }
}

pub fn trivia_width(trivia: &[Trivia<'_>]) -> usize {
    trivia.iter().map(|t| t.text.len()).sum()
}

#[derive(Clone, Debug)]
pub struct Node<'a> {
    /// `SyntaxKind::Token(_)` for tokens, `Missing`, `SyntaxList`, or the kind
    /// of a node with fields.
    pub kind: SyntaxKind,
    pub children: Vec<Rc<Node<'a>>>,
    pub token: Option<Token<'a>>,
}

impl<'a> Node<'a> {
    pub fn make_missing() -> Self {
        Node {
            kind: SyntaxKind::Missing,
            children: vec![],
            token: None,
        }
    }

    /// `Syntax.make_list`: an empty list is Missing.
    pub fn make_list(items: Vec<Rc<Node<'a>>>) -> Self {
        if items.is_empty() {
            Self::make_missing()
        } else {
            Node {
                kind: SyntaxKind::SyntaxList,
                children: items,
                token: None,
            }
        }
    }

    pub fn make_list_item(item: Rc<Node<'a>>, separator: Rc<Node<'a>>) -> Self {
        Node {
            kind: SyntaxKind::ListItem,
            children: vec![item, separator],
            token: None,
        }
    }

    pub fn make_binary_expression(
        left: Rc<Node<'a>>,
        operator: Rc<Node<'a>>,
        right: Rc<Node<'a>>,
    ) -> Self {
        Node {
            kind: SyntaxKind::BinaryExpression,
            children: vec![left, operator, right],
            token: None,
        }
    }

    pub fn is_missing(&self) -> bool {
        self.kind == SyntaxKind::Missing
    }

    pub fn is_list(&self) -> bool {
        self.kind == SyntaxKind::SyntaxList
    }

    pub fn is_token(&self) -> bool {
        self.token.is_some()
    }

    pub fn get_token(&self) -> Option<&Token<'a>> {
        self.token.as_ref()
    }

    pub fn token_kind(&self) -> Option<TokenKind> {
        self.token.as_ref().map(|t| t.kind)
    }

    /// `Syntax.children`: the elements of a list, the fields of a node, and
    /// nothing for tokens and Missing.
    pub fn children(&self) -> &[Rc<Node<'a>>] {
        &self.children
    }

    /// `Syntax.syntax_node_to_list`.
    pub fn syntax_node_to_list(&self) -> Vec<&Node<'a>> {
        match self.kind {
            SyntaxKind::SyntaxList => self.children.iter().map(|c| &**c).collect(),
            SyntaxKind::Missing => vec![],
            _ => vec![self],
        }
    }

    /// The elements of a SyntaxList (`Syntax.SyntaxList l`), if this is one.
    pub fn list_elements(&self) -> Option<Vec<&Node<'a>>> {
        if self.kind == SyntaxKind::SyntaxList {
            Some(self.children.iter().map(|c| &**c).collect())
        } else {
            None
        }
    }

    /// `Syntax.leading_token`: the first token of the subtree.
    pub fn leading_token(&self) -> Option<&Token<'a>> {
        if let Some(t) = &self.token {
            return Some(t);
        }
        self.children.iter().find_map(|c| c.leading_token())
    }

    /// `Syntax.trailing_token`: the last token of the subtree.
    pub fn trailing_token(&self) -> Option<&Token<'a>> {
        if let Some(t) = &self.token {
            return Some(t);
        }
        self.children.iter().rev().find_map(|c| c.trailing_token())
    }

    pub fn leading_trivia(&self) -> &[Trivia<'a>] {
        self.leading_token().map_or(&[], |t| &t.leading)
    }

    pub fn trailing_trivia(&self) -> &[Trivia<'a>] {
        self.trailing_token().map_or(&[], |t| &t.trailing)
    }

    pub fn for_each_token<'n>(&'n self, f: &mut impl FnMut(&'n Token<'a>)) {
        if let Some(t) = &self.token {
            f(t);
        } else {
            for c in &self.children {
                c.for_each_token(f);
            }
        }
    }

    /// `Full_fidelity_editable_syntax.text`: the full text of every token of
    /// the subtree, trivia included.
    pub fn text(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.for_each_token(&mut |t| {
            for tr in &t.leading {
                buf.extend_from_slice(tr.text);
            }
            buf.extend_from_slice(t.text);
            for tr in &t.trailing {
                buf.extend_from_slice(tr.text);
            }
        });
        buf
    }

    /// The width of the node without the leading trivia of its first token
    /// and the trailing trivia of its last token
    /// (`Full_fidelity_positioned_syntax.width`).
    pub fn inner_width(&self) -> usize {
        self.width() - trivia_width(self.leading_trivia()) - trivia_width(self.trailing_trivia())
    }

    /// `Full_fidelity_editable_syntax.width`: the length of `text`.
    pub fn width(&self) -> usize {
        let mut w = 0;
        self.for_each_token(&mut |t| w += t.full_width());
        w
    }

    /// Rebuild this node with `f` applied to its first token, sharing all
    /// other subtrees (the effect of the `Rewriter.rewrite_pre` calls in
    /// hack_format.ml, which replace the token found by `leading_token`).
    fn map_leading_token(&self, f: impl FnOnce(&mut Token<'a>)) -> Node<'a> {
        if self.token.is_some() {
            let mut n = self.clone();
            f(n.token.as_mut().unwrap());
            return n;
        }
        for (i, c) in self.children.iter().enumerate() {
            if c.leading_token().is_some() {
                let mut n = Node {
                    kind: self.kind,
                    children: self.children.clone(),
                    token: None,
                };
                n.children[i] = Rc::new(c.map_leading_token(f));
                return n;
            }
        }
        self.clone()
    }

    fn map_trailing_token(&self, f: impl FnOnce(&mut Token<'a>)) -> Node<'a> {
        if self.token.is_some() {
            let mut n = self.clone();
            f(n.token.as_mut().unwrap());
            return n;
        }
        for (i, c) in self.children.iter().enumerate().rev() {
            if c.trailing_token().is_some() {
                let mut n = Node {
                    kind: self.kind,
                    children: self.children.clone(),
                    token: None,
                };
                n.children[i] = Rc::new(c.map_trailing_token(f));
                return n;
            }
        }
        self.clone()
    }

    /// `replace_leading_trivia` in hack_format.ml.
    pub fn replace_leading_trivia(&self, new_leading: Vec<Trivia<'a>>) -> Node<'a> {
        self.map_leading_token(|t| t.leading = new_leading)
    }

    /// `remove_leading_trivia` in hack_format.ml.
    pub fn remove_leading_trivia(&self) -> (Vec<Trivia<'a>>, Node<'a>) {
        match self.leading_token() {
            None => (vec![], self.clone()),
            Some(t) => {
                let leading = t.leading.clone();
                (leading, self.map_leading_token(|t| t.leading = vec![]))
            }
        }
    }

    /// `remove_trailing_trivia` in hack_format.ml.
    pub fn remove_trailing_trivia(&self) -> (Node<'a>, Vec<Trivia<'a>>) {
        match self.trailing_token() {
            None => (self.clone(), vec![]),
            Some(t) => {
                let trailing = t.trailing.clone();
                (self.map_trailing_token(|t| t.trailing = vec![]), trailing)
            }
        }
    }
}

/// The result of parsing a file: the root of the tree and the syntax errors,
/// sorted the way `Full_fidelity_syntax_tree.process_errors` sorts them.
pub struct SyntaxTree<'a> {
    pub text: &'a [u8],
    pub root: Rc<Node<'a>>,
    pub errors: Vec<SyntaxError>,
}

type PSyntax<'a> = Syntax<'a, PositionedToken<'a>, PositionedValue<'a>>;

struct Converter<'s, 'a> {
    text: &'a [u8],
    source: &'s SourceText<'a>,
    arena: Bump,
    /// Read the text of trivia at the token's own position (Hakana) rather
    /// than at the running offset (OCaml's `editable_from_positioned`). They
    /// differ only where the parser leaves source text out of the tree.
    trivia_at_token_offsets: bool,
}

impl<'s, 'a> Converter<'s, 'a> {
    fn sub(&self, start: usize, len: usize) -> &'a [u8] {
        // Full_fidelity_source_text.sub
        let n = self.text.len();
        if start >= n {
            b""
        } else if start + len > n {
            &self.text[start..]
        } else {
            &self.text[start..start + len]
        }
    }

    fn trivia(&self, scanned: &[(TriviaKind, usize)], mut offset: usize) -> Vec<Trivia<'a>> {
        // Full_fidelity_editable_trivia.from_positioned_list: the text of each
        // trivium is read at the running offset.
        let mut out = Vec::with_capacity(scanned.len());
        for &(kind, width) in scanned {
            out.push(Trivia {
                kind,
                text: self.sub(offset, width),
                offset,
            });
            offset += width;
        }
        out
    }

    fn scan(&mut self, xhp: bool, leading: bool, offset: usize, width: usize) -> Vec<(TriviaKind, usize)> {
        // LazyTrivia.load_trivia: no trivia when the width is zero. Leading
        // trivia are scanned over their width; trailing trivia are scanned
        // the way the lexer scans them (the width is not used).
        if width == 0 {
            return vec![];
        }
        self.arena.reset();
        let arena = &self.arena;
        // The scanners want the arena and the source text to share a lifetime.
        let source: &SourceText<'_> = self.source;
        let trivia = match (xhp, leading) {
            (true, true) => {
                positioned_by_ref_parser::scan_leading_xhp_trivia(arena, source, offset, width)
            }
            (true, false) => {
                positioned_by_ref_parser::scan_trailing_xhp_trivia(arena, source, offset, width)
            }
            (false, true) => {
                positioned_by_ref_parser::scan_leading_php_trivia(arena, source, offset, width)
            }
            (false, false) => {
                positioned_by_ref_parser::scan_trailing_php_trivia(arena, source, offset, width)
            }
        };
        trivia.iter().map(|t| (t.kind, t.width)).collect()
    }

    fn convert(&mut self, node: &PSyntax<'_>, offset: usize) -> Node<'a> {
        if let Some(t) = node.get_token() {
            let kind = t.kind();
            let xhp = kind == TokenKind::XHPBody;
            let leading_start = t.leading_start_offset().unwrap_or(0);
            let width = t.width();
            let leading = self.scan(xhp, true, leading_start, t.leading_width());
            let trailing_start = leading_start + t.leading_width() + width;
            let trailing = self.scan(xhp, false, trailing_start, t.trailing_width());
            let (leading_offset, trailing_offset) = if self.trivia_at_token_offsets {
                (leading_start, trailing_start)
            } else {
                (offset, offset + t.leading_width() + width)
            };
            let leading = self.trivia(&leading, leading_offset);
            let trailing = self.trivia(&trailing, trailing_offset);
            let leading_width = trivia_width(&leading);
            let text = self.sub(leading_start + leading_width, width);
            Node {
                kind: SyntaxKind::Token(kind),
                children: vec![],
                token: Some(Token {
                    kind,
                    text,
                    leading,
                    trailing,
                }),
            }
        } else {
            let mut offset = offset;
            let mut children = vec![];
            for c in node.iter_children() {
                let w = c.full_width();
                children.push(Rc::new(self.convert(c, offset)));
                offset += w;
            }
            Node {
                kind: node.kind(),
                children,
                token: None,
            }
        }
    }
}

/// `SyntaxTree.make ~env source_text` followed by `SyntaxTree.all_errors`.
///
/// `path` is the path of the source text (`Relative_path.Dummy`), which the
/// parser consults: a `.php` file must start with `<?hh`.
///
/// With `hakana_rules`, the text of each trivium is read at its own position,
/// as Hakana does; OCaml reads it at an offset computed from the widths of the
/// nodes before it, which is wrong after source text the parser left out of
/// the tree (the attributes of context constants, for instance).
pub fn parse<'a>(text: &'a [u8], path: &str, enable_xhp_class_modifier: bool, hakana_rules: bool) -> SyntaxTree<'a> {
    let source = SourceText::make(
        Arc::new(RelativePath::make(Prefix::Dummy, path.into())),
        text,
    );
    let env = ParserEnv {
        enable_xhp_class_modifier,
        ..Default::default()
    };
    let arena = Bump::new();
    let (root, errors, _) = positioned_by_ref_parser::parse_script(&arena, &source, env);
    let mut converter = Converter {
        text,
        source: &source,
        arena: Bump::new(),
        trivia_at_token_offsets: hakana_rules,
    };
    let root = converter.convert(&root, 0);
    SyntaxTree {
        text,
        root: Rc::new(root),
        errors: process_errors(errors),
    }
}

/// `Full_fidelity_syntax_tree.process_errors`: reverse, stable-sort by
/// offsets, then drop consecutive duplicates (same offsets and message).
fn process_errors(mut errors: Vec<SyntaxError>) -> Vec<SyntaxError> {
    errors.reverse();
    errors.sort_by(|a, b| {
        a.start_offset
            .cmp(&b.start_offset)
            .then(a.end_offset.cmp(&b.end_offset))
    });
    errors.dedup_by(|later, earlier| {
        later.start_offset == earlier.start_offset
            && later.end_offset == earlier.end_offset
            && later.message == earlier.message
    });
    errors
}

/// `Full_fidelity_positioned_syntax.parentage`, on the converted tree: the
/// nodes whose full span (trivia included) contains `position`, deepest
/// first, each with the offset at which its leading trivia start.
pub fn parentage<'n, 'a>(root: &'n Node<'a>, position: isize) -> Vec<(&'n Node<'a>, isize)> {
    let mut acc = vec![];
    let mut nodes: Vec<&'n Node<'a>> = vec![root];
    let mut position = position;
    let mut base: isize = 0;
    let mut i = 0;
    while i < nodes.len() {
        let h = nodes[i];
        let width = h.width() as isize;
        if position < width {
            acc.push((h, base));
            nodes = h.children.iter().map(|c| &**c).collect();
            i = 0;
        } else {
            position -= width;
            base += width;
            i += 1;
        }
    }
    acc.reverse();
    acc
}
