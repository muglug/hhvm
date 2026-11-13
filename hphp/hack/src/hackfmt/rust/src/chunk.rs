// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! chunk.ml, chunk_group.ml, nesting.ml, rule.ml

use std::collections::BTreeMap;

use crate::doc::RuleKind;
use crate::interval::Interval;

pub const NULL_RULE_ID: isize = -1;

/// nesting.ml. Nestings are stored in their chunk group's arena, indexed by
/// id (`Nesting_allocator` hands out consecutive ids starting at 0).
#[derive(Clone, Debug)]
pub struct Nesting {
    pub id: usize,
    pub indent: bool,
    pub parent: Option<usize>,
    pub skip_parent_if_nested: bool,
}

/// An atom is a substring of the original source which will be exactly
/// represented in the formatted output and is considered indivisible.
#[derive(Clone, Debug)]
pub struct Atom<'a> {
    pub text: &'a [u8],
    pub range: Interval,
    pub leading_space: bool,
}

#[derive(Clone, Debug)]
pub struct Chunk<'a> {
    pub spans: Vec<usize>,
    pub is_appendable: bool,
    pub space_if_not_split: bool,
    /// The rule governing the split after which a trailing comma is added,
    /// and the range of the comma if it was present in the original source.
    pub comma: Option<(usize, Option<Interval>)>,
    pub rule: isize,
    pub nesting: usize,
    pub start_char: isize,
    pub end_char: isize,
    pub indentable: bool,
    pub atoms: Vec<Atom<'a>>,
    pub length: usize,
}

impl<'a> Chunk<'a> {
    /// `Chunk.make`
    pub fn make(rule: Option<usize>, nesting: usize, start_char: isize) -> Self {
        Chunk {
            spans: vec![],
            is_appendable: true,
            space_if_not_split: false,
            comma: None,
            rule: rule.map_or(NULL_RULE_ID, |r| r as isize),
            nesting,
            start_char,
            end_char: -1,
            indentable: true,
            atoms: vec![],
            length: 0,
        }
    }

    /// `Chunk.add_atom`
    pub fn add_atom(&mut self, leading_space: bool, text: &'a [u8], width: usize, source_offset: isize) {
        self.atoms.push(Atom {
            text,
            range: (source_offset, source_offset + width as isize),
            leading_space,
        });
    }

    /// `Chunk.finalize`
    pub fn finalize(
        &mut self,
        rule: usize,
        rule_kind: RuleKind,
        space: bool,
        comma: Option<(usize, Option<Interval>)>,
        end_char: isize,
    ) {
        if self.atoms.is_empty() {
            panic_failure("Cannot finalize empty chunk");
        }
        let end_char = std::cmp::max(self.start_char, end_char);
        if rule_kind.is_always() || self.rule == NULL_RULE_ID {
            self.rule = rule as isize;
        }
        self.length = self
            .atoms
            .iter()
            .map(|a| usize::from(a.leading_space) + a.text.len())
            .sum();
        self.is_appendable = false;
        self.space_if_not_split = space;
        self.comma = comma;
        self.end_char = end_char;
    }

    pub fn rule(&self) -> usize {
        self.rule as usize
    }

    /// `Chunk.get_range`
    pub fn get_range(&self) -> Interval {
        if self.is_appendable {
            panic_failure("Can't get range of non-finalized chunk");
        }
        (
            self.atoms.first().unwrap().range.0,
            self.atoms.last().unwrap().range.1,
        )
    }

    /// `Chunk.is_empty`
    pub fn is_empty(&self) -> bool {
        match self.atoms.as_slice() {
            [] => true,
            [atom] if atom.text.is_empty() => true,
            _ => false,
        }
    }

    /// `Chunk.text`
    pub fn text(&self) -> Vec<u8> {
        let mut buf = vec![];
        for atom in &self.atoms {
            if atom.leading_space {
                buf.push(b' ');
            }
            buf.extend_from_slice(atom.text);
        }
        buf
    }
}

/// chunk_group.ml
#[derive(Clone, Debug)]
pub struct ChunkGroup<'a> {
    pub chunks: Vec<Chunk<'a>>,
    /// Rule ids are dense within a group: `rule_map[id]` is the kind of rule
    /// `id` (the OCaml group keeps an `I_map` with the same keys).
    pub rule_map: Vec<RuleKind>,
    pub rule_dependency_map: BTreeMap<usize, Vec<usize>>,
    /// `rule_dependency_map` as a vector indexed by rule id.
    pub deps: Vec<Vec<usize>>,
    pub block_indentation: isize,
    pub nestings: Vec<Nesting>,
}

impl<'a> ChunkGroup<'a> {
    pub fn new(
        chunks: Vec<Chunk<'a>>,
        rule_map: Vec<RuleKind>,
        rule_dependency_map: BTreeMap<usize, Vec<usize>>,
        block_indentation: isize,
        nestings: Vec<Nesting>,
    ) -> Self {
        let mut deps = vec![vec![]; rule_map.len()];
        for (id, parents) in &rule_dependency_map {
            if *id < deps.len() {
                deps[*id] = parents.clone();
            }
        }
        ChunkGroup {
            chunks,
            rule_map,
            rule_dependency_map,
            deps,
            block_indentation,
            nestings,
        }
    }

    pub fn get_rule_count(&self) -> usize {
        self.rule_map.len()
    }

    pub fn get_rule_kind(&self, id: usize) -> RuleKind {
        self.rule_map[id]
    }

    /// `Chunk_group.get_char_range`
    pub fn get_char_range(&self) -> Interval {
        self.chunks
            .iter()
            .fold((isize::MAX, 0), |(start_char, end_char), chunk| {
                let (chunk_start, chunk_end) = chunk.get_range();
                (
                    std::cmp::min(start_char, chunk_start),
                    std::cmp::max(end_char, chunk_end),
                )
            })
    }

    /// `Chunk_group.propagate_breakage`
    pub fn propagate_breakage(&self, initial: &[Option<bool>]) -> Vec<Option<bool>> {
        let mut acc = initial.to_vec();
        for (rule_id, v) in initial.iter().enumerate() {
            if *v == Some(true) {
                for id in &self.deps[rule_id] {
                    if self.get_rule_kind(*id).cares_about_children() {
                        acc[*id] = Some(true);
                    }
                }
            }
        }
        acc
    }

    /// `Chunk_group.get_always_rules`
    pub fn get_always_rules(&self) -> Vec<usize> {
        (0..self.rule_map.len())
            .filter(|id| self.rule_map[*id].is_always())
            .collect()
    }

    /// `Chunk_group.get_always_rule_bindings`
    pub fn get_always_rule_bindings(&self) -> Vec<Option<bool>> {
        self.rule_map
            .iter()
            .map(|k| if k.is_always() { Some(true) } else { None })
            .collect()
    }

    /// `Chunk_group.get_initial_rule_bindings`
    pub fn get_initial_rule_bindings(&self) -> Vec<Option<bool>> {
        self.propagate_breakage(&self.get_always_rule_bindings())
    }

    /// `Chunk_group.are_rule_bindings_valid`
    pub fn are_rule_bindings_valid(&self, rbm: &[Option<bool>]) -> bool {
        rbm.iter().enumerate().all(|(rule_id, v)| match v {
            None => true,
            Some(child_val) => self.deps[rule_id].iter().all(|parent_id| {
                // When a child rule is broken on, all its parent rules must
                // break too.
                if !self.get_rule_kind(*parent_id).cares_about_children() {
                    true
                } else {
                    !matches!((rbm[*parent_id], *child_val), (Some(false), true))
                }
            }),
        })
    }

    /// `Chunk_group.dependency_map_to_string`
    pub fn dependency_map_to_string(&self) -> String {
        let strs: Vec<String> = self
            .rule_dependency_map
            .iter()
            .map(|(k, vs)| {
                let values: Vec<String> = vs.iter().map(|v| v.to_string()).collect();
                format!("{}: [{}]", k, values.join(", "))
            })
            .collect();
        format!("{{{}}}", strs.join(", "))
    }

    /// `Nesting.get_indent_level`
    pub fn get_indent_level(&self, nesting: usize, nesting_set: &[bool]) -> isize {
        let mut acc = 0;
        let mut n = Some(nesting);
        while let Some(id) = n {
            let nest = &self.nestings[id];
            let in_set = nesting_set.get(id).copied().unwrap_or(false);
            if nest.indent && in_set {
                acc += 1;
            }
            n = if in_set && nest.skip_parent_if_nested {
                nest.parent.and_then(|p| self.nestings[p].parent)
            } else {
                nest.parent
            };
        }
        acc
    }

    /// `Nesting.get_self_and_parent_list`
    pub fn get_self_and_parent_list(&self, nesting: usize) -> Vec<usize> {
        let mut acc = vec![];
        let mut n = Some(nesting);
        while let Some(id) = n {
            acc.insert(0, id);
            n = self.nestings[id].parent;
        }
        acc
    }
}

/// Raise OCaml's `Failure msg`.
pub fn panic_failure(msg: &str) -> ! {
    std::panic::panic_any(crate::error::Exn::Failure(msg.to_string()))
}
