// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! chunk_builder.ml (with rule_allocator.ml, nesting_allocator.ml and
//! span_allocator.ml).

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::chunk::Chunk;
use crate::chunk::ChunkGroup;
use crate::chunk::NULL_RULE_ID;
use crate::chunk::Nesting;
use crate::chunk::panic_failure;
use crate::doc::Cost;
use crate::doc::Doc;
use crate::doc::RuleKind;
use crate::format_env::Env;

#[derive(Clone, Copy, PartialEq, Eq)]
enum RuleState {
    NoRule,
    RuleKind(RuleKind),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StringType {
    DocStringClose,
    Number,
    ConcatOp,
    LineComment,
    Other,
}

/// rule_allocator.ml
struct RuleAllocator {
    rule_map: Vec<RuleKind>,
    dependency_map: BTreeMap<usize, Vec<usize>>,
}

impl RuleAllocator {
    fn make() -> Self {
        RuleAllocator {
            rule_map: vec![],
            dependency_map: BTreeMap::new(),
        }
    }

    fn make_rule(&mut self, kind: RuleKind) -> usize {
        let id = self.rule_map.len();
        self.rule_map.push(kind);
        id
    }

    fn get_rule_kind(&self, id: usize) -> RuleKind {
        self.rule_map[id]
    }

    fn mark_dependencies(&mut self, lazy_rules: &BTreeSet<usize>, active_rule_ids: &[usize], child_id: usize) {
        // rule_ids = I_set.elements lazy_rules @ active_rule_ids, where the
        // active rules are innermost first.
        let rule_ids = lazy_rules
            .iter()
            .copied()
            .chain(active_rule_ids.iter().rev().copied());
        for id in rule_ids {
            if self.rule_map[id].cares_about_children() {
                self.dependency_map.entry(child_id).or_default().insert(0, id);
            }
        }
    }
}

/// nesting_allocator.ml
struct NestingAllocator {
    nestings: Vec<Nesting>,
    current: usize,
}

impl NestingAllocator {
    fn make() -> Self {
        NestingAllocator {
            nestings: vec![Nesting {
                id: 0,
                indent: false,
                parent: None,
                skip_parent_if_nested: false,
            }],
            current: 0,
        }
    }

    fn nest(&mut self, conditional: bool) {
        let id = self.nestings.len();
        self.nestings.push(Nesting {
            id,
            indent: true,
            parent: Some(self.current),
            skip_parent_if_nested: conditional,
        });
        self.current = id;
    }

    fn unnest(&mut self) {
        match self.nestings[self.current].parent {
            Some(p) => self.current = p,
            None => panic_failure("unnested too far"),
        }
    }

    fn is_nested(&self) -> bool {
        self.nestings[self.current].parent.is_some()
    }
}

struct Builder<'a> {
    env: Env,
    open_spans: Vec<isize>,
    /// Active rules, innermost last (the OCaml list is innermost first).
    rules: Vec<usize>,
    lazy_rules: BTreeSet<usize>,
    /// Chunks of the current group, newest last.
    chunks: Vec<Chunk<'a>>,
    next_split_rule: RuleState,
    next_lazy_rules: BTreeSet<usize>,
    num_pending_spans: usize,
    space_if_not_split: bool,
    pending_comma: Option<(usize, Option<crate::interval::Interval>)>,
    pending_space: bool,
    chunk_groups: Vec<ChunkGroup<'a>>,
    rule_alloc: RuleAllocator,
    nesting_alloc: NestingAllocator,
    next_span_id: usize,
    block_indent: isize,
    seen_chars: isize,
    last_chunk_end: isize,
    last_string_type: StringType,
    /// `after_next_string`: start a Parental rule after the next string.
    after_next_string: bool,
}

impl<'a> Builder<'a> {
    fn new(env: Env) -> Self {
        Builder {
            env,
            open_spans: vec![],
            rules: vec![],
            lazy_rules: BTreeSet::new(),
            chunks: vec![],
            next_split_rule: RuleState::RuleKind(RuleKind::Always),
            next_lazy_rules: BTreeSet::new(),
            num_pending_spans: 0,
            space_if_not_split: false,
            pending_comma: None,
            pending_space: false,
            chunk_groups: vec![],
            rule_alloc: RuleAllocator::make(),
            nesting_alloc: NestingAllocator::make(),
            next_span_id: 0,
            block_indent: 0,
            seen_chars: 0,
            last_chunk_end: 0,
            last_string_type: StringType::Other,
            after_next_string: false,
        }
    }

    fn rules_hd(&self) -> Option<usize> {
        self.rules.last().copied()
    }

    fn rules_hd_exn(&self) -> usize {
        match self.rules.last() {
            Some(r) => *r,
            None => panic_failure("hd"),
        }
    }

    fn add_string(&mut self, is_trivia: bool, multiline: bool, s: &'a [u8], width: usize) {
        if self.last_string_type == StringType::DocStringClose && (is_trivia || s != b";") {
            self.hard_split();
        }

        match self.chunks.last_mut() {
            Some(hd) if hd.is_appendable => {
                let leading_space = self.pending_space;
                self.pending_space = false;
                hd.indentable = hd.indentable && !multiline;
                hd.add_atom(leading_space, s, width, self.seen_chars);
            }
            _ => {
                self.space_if_not_split = self.pending_space;
                self.pending_space = false;
                match self.next_split_rule {
                    RuleState::NoRule => {
                        let nesting = self.nesting_alloc.current;
                        let mut chunk = Chunk::make(self.rules_hd(), nesting, self.last_chunk_end);
                        chunk.add_atom(false, s, width, self.seen_chars);
                        chunk.indentable = !multiline;
                        self.chunks.push(chunk);
                    }
                    RuleState::RuleKind(rule_kind) => {
                        let nesting = self.nesting_alloc.current;
                        self.start_rule_kind(rule_kind);
                        let mut chunk = Chunk::make(self.rules_hd(), nesting, self.last_chunk_end);
                        chunk.add_atom(false, s, width, self.seen_chars);
                        chunk.indentable = !multiline;
                        self.chunks.push(chunk);
                        self.end_rule();
                        self.next_split_rule = RuleState::NoRule;
                    }
                }
            }
        }

        self.advance(width as isize);

        if !is_trivia {
            let next_lazy = std::mem::take(&mut self.next_lazy_rules);
            self.lazy_rules.extend(next_lazy);

            for _ in 0..self.num_pending_spans {
                self.open_spans.push(self.chunks.len() as isize - 1);
            }
            self.num_pending_spans = 0;

            if self.last_string_type == StringType::DocStringClose && s == b";" {
                // Normally, we'd have already counted the newline in the
                // semicolon's trailing trivia before splitting. Since here
                // we're splitting before getting the chance to handle that
                // trailing trivia, we temporarily advance to make sure the
                // new chunk has the correct start_char.
                self.advance(1);
                self.hard_split();
                self.advance(-1);
            }
        }

        self.last_string_type = StringType::Other;

        if self.after_next_string {
            self.start_rule_kind(RuleKind::Parental);
        }
        self.after_next_string = false;
    }

    fn set_pending_comma(&mut self, present_in_original_source: bool) {
        if self.last_string_type != StringType::DocStringClose {
            let range = if !present_in_original_source {
                None
            } else {
                Some((self.seen_chars, self.seen_chars + 1))
            };
            let rule = self.rules_hd_exn();
            match self.chunks.last_mut() {
                Some(hd) if !hd.is_appendable => hd.comma = Some((rule, range)),
                _ => self.pending_comma = Some((rule, range)),
            }
            if self.env.version_gte(3) {
                self.last_string_type = StringType::Other;
            }
        }
    }

    fn add_space(&mut self) {
        self.pending_space = true;
        if self.pending_comma.is_some() {
            self.simple_split_if_unsplit();
        }
    }

    fn split(&mut self) {
        let appendable = matches!(self.chunks.last(), Some(hd) if hd.is_appendable);
        if !appendable {
            return;
        }
        let rule_id = self.chunks.last().unwrap().rule;
        let rule = if rule_id != NULL_RULE_ID {
            rule_id as usize
        } else {
            match self.rules_hd() {
                None => self.create_rule(RuleKind::Simple(Cost::Base)),
                Some(hd) => hd,
            }
        };
        let rule_kind = self.rule_alloc.get_rule_kind(rule);
        let space = self.space_if_not_split;
        let comma = self.pending_comma;
        let seen = self.seen_chars;
        self.chunks
            .last_mut()
            .unwrap()
            .finalize(rule, rule_kind, space, comma, seen);
        self.last_chunk_end = self.seen_chars;
        self.space_if_not_split = self.pending_space;
        self.pending_comma = None;
    }

    fn create_rule(&mut self, kind: RuleKind) -> usize {
        self.rule_alloc.make_rule(kind)
    }

    fn create_lazy_rule(&mut self, kind: RuleKind) -> usize {
        let id = self.create_rule(kind);
        self.next_lazy_rules.insert(id);
        id
    }

    fn simple_split_if_unsplit(&mut self) {
        if matches!(self.chunks.last(), Some(hd) if hd.is_appendable) {
            self.simple_split(Cost::Base);
        }
    }

    fn add_always_empty_chunk(&mut self) {
        // Hakana's rule: never start a file with a blank line.
        if self.env.hakana_rules && self.chunk_groups.is_empty() && self.chunks.is_empty() {
            return;
        }
        let create = match self.chunks.last() {
            None => true,
            Some(hd) => !hd.is_appendable,
        };
        if create {
            let nesting = self.nesting_alloc.current;
            let rule = self.create_rule(RuleKind::Always);
            let mut chunk = Chunk::make(Some(rule), nesting, self.last_chunk_end);
            chunk.add_atom(false, b"", 0, self.last_chunk_end);
            self.last_chunk_end = self.seen_chars;
            chunk.finalize(rule, RuleKind::Always, false, None, self.seen_chars);
            self.chunks.push(chunk);
        }
    }

    fn simple_split(&mut self, cost: Cost) {
        self.split();
        self.set_next_split_rule(RuleState::RuleKind(RuleKind::Simple(cost)));
    }

    fn is_at_chunk_group_boundary(&self) -> bool {
        self.rules.is_empty()
            && self.lazy_rules.is_empty()
            && self.next_lazy_rules.is_empty()
            && !self.nesting_alloc.is_nested()
    }

    fn hard_split(&mut self) {
        if !self.chunks.is_empty() {
            self.split();
            self.set_next_split_rule(RuleState::RuleKind(RuleKind::Always));
        }
        if self.is_at_chunk_group_boundary() && !self.chunks.is_empty() {
            self.push_chunk_group();
        }
    }

    fn set_next_split_rule(&mut self, rule_type: RuleState) {
        if self.next_split_rule != RuleState::RuleKind(RuleKind::Always) {
            self.next_split_rule = rule_type;
        }
    }

    fn nest(&mut self, skip_parent: bool) {
        self.nesting_alloc.nest(skip_parent);
    }

    fn unnest(&mut self) {
        self.nesting_alloc.unnest();
    }

    fn start_rule_id(&mut self, rule_id: usize) {
        self.rule_alloc
            .mark_dependencies(&self.lazy_rules, &self.rules, rule_id);
        self.rules.push(rule_id);
    }

    fn start_rule_kind(&mut self, rule_kind: RuleKind) {
        // Override next_split_rule unless it's an Always rule
        if let RuleState::RuleKind(kind) = self.next_split_rule {
            if !kind.is_always() {
                self.next_split_rule = RuleState::NoRule;
            }
        }
        let rule = self.create_rule(rule_kind);
        self.start_rule_id(rule);
    }

    fn start_lazy_rule(&mut self, lazy_rule_id: usize) {
        if self.next_lazy_rules.remove(&lazy_rule_id) {
            self.start_rule_id(lazy_rule_id);
        } else if self.lazy_rules.remove(&lazy_rule_id) {
            self.start_rule_id(lazy_rule_id);
        } else {
            panic_failure("Called start_lazy_rule with a rule id is not a lazy rule");
        }
    }

    fn end_rule(&mut self) {
        self.rules.pop();
    }

    fn start_span(&mut self) {
        self.num_pending_spans += 1;
    }

    fn end_span(&mut self) {
        if self.num_pending_spans == 0 {
            let os = match self.open_spans.pop() {
                Some(os) => os,
                None => std::panic::panic_any(crate::error::Exn::Other("Stack.Empty".into())),
            };
            let span = self.next_span_id;
            self.next_span_id += 1;
            for (n, chunk) in self.chunks.iter_mut().enumerate() {
                if n as isize > os {
                    chunk.spans.insert(0, span);
                }
            }
        } else {
            self.num_pending_spans -= 1;
        }
    }

    fn start_block_nest(&mut self) {
        if self.is_at_chunk_group_boundary() {
            self.block_indent += 1;
        } else {
            self.nest(false);
        }
    }

    fn end_block_nest(&mut self) {
        if self.is_at_chunk_group_boundary() {
            self.block_indent -= 1;
        } else {
            self.unnest();
        }
    }

    fn push_chunk_group(&mut self) {
        let chunks = std::mem::take(&mut self.chunks);
        let rule_alloc = std::mem::replace(&mut self.rule_alloc, RuleAllocator::make());
        let nesting_alloc = std::mem::replace(&mut self.nesting_alloc, NestingAllocator::make());
        self.chunk_groups.push(ChunkGroup::new(
            chunks,
            rule_alloc.rule_map,
            rule_alloc.dependency_map,
            self.block_indent,
            nesting_alloc.nestings,
        ));
        self.next_span_id = 0;
    }

    fn end(&mut self) {
        self.hard_split();
        if !self.chunks.is_empty() {
            panic_failure(
                "The impossible happened: Chunk_builder attempted to end when not at a chunk group boundary",
            );
        }
    }

    fn advance(&mut self, n: isize) {
        self.seen_chars += n;
    }

    fn consume_doc(&mut self, node: &Doc<'a>) {
        match node {
            Doc::Nothing => {}
            Doc::Concat(nodes) => {
                for n in nodes {
                    self.consume_doc(n);
                }
            }
            Doc::Text(text, width) => self.add_string(false, false, text, *width),
            Doc::Comment(text, width) => self.add_string(true, false, text, *width),
            Doc::SingleLineComment(text, width) => {
                self.add_string(true, false, text, *width);
                self.last_string_type = StringType::LineComment;
            }
            Doc::Ignore(width) => self.advance(*width as isize),
            Doc::MultilineString(strings, width) => {
                let prev_seen = self.seen_chars;
                if let Some((hd, tl)) = strings.split_first() {
                    self.add_string(false, false, hd, hd.len());
                    for s in tl {
                        self.advance(1);
                        self.hard_split();
                        self.add_string(false, true, s, s.len());
                    }
                }
                self.seen_chars = prev_seen + *width as isize;
            }
            Doc::DocLiteral(node) => {
                if !self.env.version_gte(3) {
                    self.set_next_split_rule(RuleState::RuleKind(RuleKind::Simple(Cost::Base)));
                }
                self.consume_doc(node);
                self.last_string_type = StringType::DocStringClose;
            }
            Doc::NumericLiteral(node) => {
                if self.last_string_type == StringType::ConcatOp {
                    self.add_space();
                }
                self.consume_doc(node);
                self.last_string_type = StringType::Number;
            }
            Doc::ConcatOperator(node) => {
                if self.last_string_type == StringType::Number {
                    self.add_space();
                }
                self.consume_doc(node);
                self.last_string_type = StringType::ConcatOp;
            }
            Doc::Split => self.split(),
            Doc::SplitWith(cost) => self.simple_split(*cost),
            Doc::Newline => self.hard_split(),
            Doc::BlankLine => {
                self.hard_split();
                self.add_always_empty_chunk();
            }
            Doc::Space => self.add_space(),
            Doc::Span(nodes) => {
                self.start_span();
                for n in nodes {
                    self.consume_doc(n);
                }
                self.end_span();
            }
            Doc::Nest(nodes) => {
                self.nest(false);
                for n in nodes {
                    self.consume_doc(n);
                }
                self.unnest();
            }
            Doc::ConditionalNest(nodes) => {
                self.nest(true);
                for n in nodes {
                    self.consume_doc(n);
                }
                self.unnest();
            }
            Doc::BlockNest(nodes) => {
                self.start_block_nest();
                for n in nodes {
                    self.consume_doc(n);
                }
                self.end_block_nest();
            }
            Doc::WithRule(rule_kind, body) => {
                self.start_rule_kind(*rule_kind);
                self.consume_doc(body);
                self.end_rule();
            }
            Doc::WithLazyRule(rule_kind, before, body) => {
                let rule = self.create_lazy_rule(*rule_kind);
                self.consume_doc(before);
                self.start_lazy_rule(rule);
                self.consume_doc(body);
                self.end_rule();
            }
            Doc::WithOverridingParentalRule(body) => {
                // If we have a pending split which is not a hard split,
                // replace it with a Parental rule, which will break if the
                // body breaks.
                let override_independent_split = matches!(
                    self.next_split_rule,
                    RuleState::RuleKind(kind) if !kind.is_always()
                );
                // Starting a new rule will override the independent split,
                // controlling that split with the new Parental rule instead.
                if override_independent_split {
                    self.start_rule_kind(RuleKind::Parental);
                }
                // Regardless of whether we intend to override the preceding
                // split, start a new Parental rule to govern the contents of
                // the body.
                self.after_next_string = true;
                self.consume_doc(body);
                self.end_rule();
                if override_independent_split {
                    self.end_rule();
                }
            }
            Doc::TrailingComma(present_in_original_source) => {
                if self.last_string_type != StringType::LineComment {
                    self.set_pending_comma(*present_in_original_source);
                } else {
                    self.add_string(false, false, b",", 1);
                    self.advance(-1);
                }
                if !self.env.version_gte(3) {
                    self.last_string_type = StringType::Other;
                }
            }
        }
    }
}

/// `Chunk_builder.build`
pub fn build<'a>(env: &Env, node: &Doc<'a>) -> Vec<ChunkGroup<'a>> {
    let mut builder = Builder::new(env.clone());
    builder.consume_doc(node);
    builder.end();
    builder.chunk_groups
}
