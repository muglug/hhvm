// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The Doc IR fed to the chunk builder (doc.ml, cost.ml and rule.ml).

use std::fmt::Write;

/// cost.ml
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cost {
    NoCost,
    Base,
    Moderate,
    High,
}

impl Cost {
    pub fn get_cost(self) -> usize {
        match self {
            Cost::NoCost => 0,
            Cost::Base => 1,
            Cost::Moderate => 2,
            Cost::High => 3,
        }
    }

    fn show(self) -> &'static str {
        match self {
            Cost::NoCost => "NoCost",
            Cost::Base => "Base",
            Cost::Moderate => "Moderate",
            Cost::High => "High",
        }
    }
}

/// `Rule.kind`
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuleKind {
    Simple(Cost),
    Always,
    Parental,
}

impl RuleKind {
    pub fn is_always(self) -> bool {
        matches!(self, RuleKind::Always)
    }

    /// `Rule.get_cost`
    pub fn get_cost(self) -> usize {
        match self {
            RuleKind::Simple(c) => c.get_cost(),
            RuleKind::Always => Cost::NoCost.get_cost(),
            RuleKind::Parental => Cost::Base.get_cost(),
        }
    }

    /// `Rule.cares_about_children`
    pub fn cares_about_children(self) -> bool {
        matches!(self, RuleKind::Parental)
    }

    /// `Rule.show_kind`
    pub fn show(self) -> String {
        match self {
            RuleKind::Simple(c) => format!("(Simple {})", c.show()),
            RuleKind::Always => "Always".into(),
            RuleKind::Parental => "Parental".into(),
        }
    }

    /// The kind part of `Rule.to_string`.
    pub fn to_debug_string(self) -> String {
        match self {
            RuleKind::Simple(c) => format!("Simple {}", c.get_cost()),
            RuleKind::Always => "Always".into(),
            RuleKind::Parental => "Parental".into(),
        }
    }
}

pub type Text<'a> = &'a [u8];

#[derive(Clone, Debug)]
pub enum Doc<'a> {
    /// Null case
    Nothing,
    /// List of concatenated nodes
    Concat(Vec<Doc<'a>>),
    /// Text which will appear in the formatted file
    Text(Text<'a>, usize),
    /// A comment which will appear in the formatted file
    Comment(Text<'a>, usize),
    /// A comment which must be followed by a Newline
    SingleLineComment(Text<'a>, usize),
    /// Text from the original source which will not appear in the formatted
    /// file (only its width matters).
    Ignore(usize),
    /// Breaking point for the line solver
    Split,
    /// Allow splitting here, but with the given cost
    SplitWith(Cost),
    /// Always split here
    Newline,
    /// Always split here and leave a blank line
    BlankLine,
    /// Add a space
    Space,
    /// Items in a Span prefer to stay on the same line
    Span(Vec<Doc<'a>>),
    /// Nested items are indented if they break across lines
    Nest(Vec<Doc<'a>>),
    /// All lines in a BlockNest are indented
    BlockNest(Vec<Doc<'a>>),
    WithRule(RuleKind, Box<Doc<'a>>),
    WithLazyRule(RuleKind, Box<Doc<'a>>, Box<Doc<'a>>),
    MultilineString(Vec<Text<'a>>, usize),
    DocLiteral(Box<Doc<'a>>),
    NumericLiteral(Box<Doc<'a>>),
    ConcatOperator(Box<Doc<'a>>),
    ConditionalNest(Vec<Doc<'a>>),
    WithOverridingParentalRule(Box<Doc<'a>>),
    TrailingComma(bool),
}

pub use Doc::*;

impl<'a> Doc<'a> {
    pub fn is_nothing(&self) -> bool {
        matches!(self, Nothing)
    }

    /// `Doc.text`
    pub fn text(s: Text<'a>) -> Doc<'a> {
        Text(s, s.len())
    }

    pub fn with_rule(kind: RuleKind, body: Doc<'a>) -> Doc<'a> {
        WithRule(kind, Box::new(body))
    }

    pub fn with_lazy_rule(kind: RuleKind, before: Doc<'a>, body: Doc<'a>) -> Doc<'a> {
        WithLazyRule(kind, Box::new(before), Box::new(body))
    }

    pub fn has_printable_content(&self) -> bool {
        match self {
            Text(..)
            | Comment(..)
            | SingleLineComment(..)
            | MultilineString(..)
            | DocLiteral(_)
            | NumericLiteral(_)
            | ConcatOperator(_) => true,
            Concat(nodes) | Span(nodes) | Nest(nodes) | ConditionalNest(nodes) | BlockNest(nodes) => {
                nodes.iter().any(|n| n.has_printable_content())
            }
            WithRule(_, body) | WithOverridingParentalRule(body) => body.has_printable_content(),
            WithLazyRule(_, before, body) => {
                before.has_printable_content() || body.has_printable_content()
            }
            Nothing | Ignore(_) | Split | SplitWith(_) | Newline | BlankLine | Space
            | TrailingComma(_) => false,
        }
    }

    pub fn has_split(&self) -> bool {
        match self {
            Split | SplitWith(_) | Newline | BlankLine | MultilineString(..) | DocLiteral(_) => true,
            Concat(nodes) | Span(nodes) | Nest(nodes) | ConditionalNest(nodes) | BlockNest(nodes) => {
                nodes.iter().any(|n| n.has_split())
            }
            WithRule(_, body) | WithOverridingParentalRule(body) => body.has_split(),
            WithLazyRule(_, before, body) => before.has_split() || body.has_split(),
            Text(..) | Comment(..) | SingleLineComment(..) | NumericLiteral(_)
            | ConcatOperator(_) | Nothing | Ignore(_) | Space | TrailingComma(_) => false,
        }
    }

    /// `Doc.dump` (without ignored text): the dump hackfmt --debug --doc
    /// writes to stderr.
    pub fn dump(&self) -> Vec<u8> {
        struct D {
            out: Vec<u8>,
            indent: usize,
        }
        impl D {
            fn print(&mut self, s: &[u8]) {
                self.out.extend(std::iter::repeat_n(b' ', self.indent));
                self.out.extend_from_slice(s);
                self.out.push(b'\n');
            }
            fn quoted(&mut self, prefix: &str, text: &[u8]) {
                let mut s = Vec::from(prefix.as_bytes());
                s.extend_from_slice(b" \"");
                s.extend_from_slice(text);
                s.push(b'"');
                self.print(&s);
            }
            fn list(&mut self, name: &str, nodes: &[&Doc<'_>]) {
                if name.is_empty() {
                    self.print(b"[");
                } else {
                    self.print(format!("{} [", name).as_bytes());
                }
                self.items(nodes);
                self.print(b"]");
            }
            fn items(&mut self, nodes: &[&Doc<'_>]) {
                self.indent += 2;
                for n in nodes {
                    self.aux(n);
                }
                self.indent -= 2;
            }
            fn aux(&mut self, d: &Doc<'_>) {
                match d {
                    Nothing => {}
                    Concat(nodes) => {
                        for n in nodes {
                            self.aux(n);
                        }
                    }
                    Text(t, _) => self.quoted("Text", t),
                    Comment(t, _) => self.quoted("Comment", t),
                    SingleLineComment(t, _) => self.quoted("SingleLineComment", t),
                    Ignore(_) => {}
                    MultilineString(strings, _) => {
                        self.print(b"MultilineString [");
                        self.indent += 2;
                        for s in strings {
                            let mut q = vec![b'"'];
                            q.extend_from_slice(s);
                            q.push(b'"');
                            self.print(&q);
                        }
                        self.indent -= 2;
                        self.print(b"]");
                    }
                    DocLiteral(n) => self.list("DocLiteral", &[n]),
                    NumericLiteral(n) => self.list("NumericLiteral", &[n]),
                    ConcatOperator(n) => self.list("ConcatOperator", &[n]),
                    Split => self.print(b"Split"),
                    SplitWith(cost) => {
                        let mut s = String::new();
                        let _ = write!(s, "SplitWith Cost.{}", cost.show());
                        self.print(s.as_bytes())
                    }
                    Newline => self.print(b"Newline"),
                    BlankLine => self.print(b"BlankLine"),
                    Space => self.print(b"Space"),
                    Span(nodes) => self.list("Span", &nodes.iter().collect::<Vec<_>>()),
                    Nest(nodes) => self.list("Nest", &nodes.iter().collect::<Vec<_>>()),
                    ConditionalNest(nodes) => {
                        self.list("ConditionalNest", &nodes.iter().collect::<Vec<_>>())
                    }
                    BlockNest(nodes) => self.list("BlockNest", &nodes.iter().collect::<Vec<_>>()),
                    WithRule(kind, body) => {
                        self.list(&format!("WithRule {}", kind.show()), &[body])
                    }
                    WithLazyRule(_, before, body) => {
                        self.print(b"WithLazyRule ([");
                        self.items(&[before]);
                        self.print(b"], [");
                        self.items(&[body]);
                        self.print(b"])");
                    }
                    WithOverridingParentalRule(body) => {
                        self.print(b"WithOverridingParentalRule ([");
                        self.items(&[body]);
                        self.print(b"])");
                    }
                    TrailingComma(present) => {
                        self.print(format!("TrailingComma {}", present).as_bytes())
                    }
                }
            }
        }
        let mut d = D {
            out: vec![],
            indent: 0,
        };
        if self.is_nothing() {
            d.print(b"Nothing");
        } else {
            d.aux(self);
        }
        d.out
    }
}

pub fn space<'a>() -> Doc<'a> {
    Space
}

pub fn split<'a>() -> Doc<'a> {
    Split
}

pub fn space_split<'a>() -> Doc<'a> {
    Concat(vec![Space, Split])
}

pub fn newline<'a>() -> Doc<'a> {
    Newline
}
