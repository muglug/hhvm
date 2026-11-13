// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! solve_state.ml
//!
//! Rule bindings maps (`rbm`) are vectors indexed by rule id: `None` for an
//! unbound rule, `Some(broken)` for a bound one. Rule ids are dense within a
//! chunk group, so iterating the vector visits rules in the order the OCaml
//! `I_map` does.

use std::cmp::Ordering;

use crate::chunk::Chunk;
use crate::chunk::ChunkGroup;
use crate::format_env::Env;

pub type Rbm = Vec<Option<bool>>;

pub struct SolveState<'g, 'a> {
    pub chunk_group: &'g ChunkGroup<'a>,
    pub rbm: Rbm,
    pub nesting_set: Vec<bool>,
    pub cost: isize,
    pub overflow: isize,
    candidate_rules: Vec<usize>,
    unprocessed_overflow: isize,
    /// Sorted, without duplicates.
    rules_on_partially_bound_lines: Vec<usize>,
}

fn is_broken(rbm: &Rbm, rule: usize) -> bool {
    rbm.get(rule).copied().flatten().unwrap_or(false)
}

pub fn rbm_has_split_before_chunk(c: &Chunk<'_>, rbm: &Rbm) -> bool {
    is_broken(rbm, c.rule())
}

pub fn rbm_has_comma_after_chunk(c: &Chunk<'_>, rbm: &Rbm) -> bool {
    match c.comma {
        None => false,
        Some((rule_id, _)) => is_broken(rbm, rule_id),
    }
}

fn get_overflow(env: &Env, len: isize) -> isize {
    std::cmp::max(len - env.line_width, 0)
}

impl<'g, 'a> SolveState<'g, 'a> {
    pub fn chunks(&self) -> &'g [Chunk<'a>] {
        &self.chunk_group.chunks
    }

    pub fn has_split_before_chunk(&self, chunk: &Chunk<'_>) -> bool {
        rbm_has_split_before_chunk(chunk, &self.rbm)
    }

    pub fn has_comma_after_chunk(&self, chunk: &Chunk<'_>) -> bool {
        rbm_has_comma_after_chunk(chunk, &self.rbm)
    }

    pub fn get_indent_level(&self, chunk: &Chunk<'_>) -> isize {
        compute_indent_level(self.chunk_group, &self.nesting_set, chunk)
    }

    pub fn make(env: &Env, chunk_group: &'g ChunkGroup<'a>, rbm: Rbm) -> Self {
        let chunks = &chunk_group.chunks;
        let mut rbm = rbm;
        rbm.resize(chunk_group.get_rule_count(), None);
        // We only care about the first occurrence of each nesting id
        let mut nesting_set = vec![false; chunk_group.nestings.len()];
        let mut seen = vec![false; chunk_group.nestings.len()];
        for c in chunks {
            let nid = c.nesting;
            if !seen[nid] {
                seen[nid] = true;
                if rbm_has_split_before_chunk(c, &rbm) {
                    nesting_set[nid] = true;
                }
            }
        }
        let lines = build_lines(env, chunk_group, &rbm, &nesting_set);
        let overflow = lines.iter().map(|(o, _)| *o).sum();
        // add to cost the number of spans that are split (implicitly giving
        // each span a cost of 1)
        let mut broken_spans: Vec<usize> = vec![];
        for c in chunks {
            if rbm_has_split_before_chunk(c, &rbm) {
                broken_spans.extend(c.spans.iter().copied());
            }
        }
        broken_spans.sort_unstable();
        broken_spans.dedup();
        let span_cost = broken_spans.len() as isize;
        // add to cost the cost of all rules that are split
        let rule_cost: isize = rbm
            .iter()
            .enumerate()
            .filter(|(_, v)| **v == Some(true))
            .map(|(id, _)| chunk_group.get_rule_kind(id).get_cost() as isize)
            .sum();
        let cost = span_cost + rule_cost;
        // Precompute candidate_rules and update the rbm by binding unbound
        // rules on lines with 0 overflow to false
        let candidate_rules = build_candidate_rules_and_update_rbm(chunk_group, &mut rbm, &lines);
        let (unprocessed_overflow, rules_on_partially_bound_lines) =
            calculate_partially_bound(chunks, &rbm, &lines);
        SolveState {
            chunk_group,
            rbm,
            nesting_set,
            cost,
            overflow,
            candidate_rules,
            unprocessed_overflow,
            rules_on_partially_bound_lines,
        }
    }

    /// `Solve_state.from_source`: when we are unable to find a good solution,
    /// produce a "best-effort" solution based on the original source text.
    pub fn from_source(env: &Env, source_text: &[u8], chunk_group: &'g ChunkGroup<'a>) -> Self {
        let rbm = chunk_group.get_always_rule_bindings();
        let rbm = add_breaks_from_source(rbm, source_text, chunk_group);
        let rbm = chunk_group.propagate_breakage(&rbm);
        Self::make(env, chunk_group, rbm)
    }

    pub fn is_rule_bound(&self, rule_id: usize) -> bool {
        self.rbm[rule_id].is_some()
    }

    pub fn get_candidate_rules(&self) -> &[usize] {
        &self.candidate_rules
    }

    /// `Solve_state.is_overlapping`
    pub fn is_overlapping(&self, s2: &Self) -> bool {
        self.unprocessed_overflow == s2.unprocessed_overflow
            && self.rules_on_partially_bound_lines.len() == s2.rules_on_partially_bound_lines.len()
            && self
                .rules_on_partially_bound_lines
                .iter()
                .all(|k| self.rbm[*k] == s2.rbm[*k])
    }

    fn compare_rule_sets(&self, s2: &Self) -> Ordering {
        for (a, b) in self.rbm.iter().zip(s2.rbm.iter()) {
            let a = a.unwrap_or(false);
            let b = b.unwrap_or(false);
            match a.cmp(&b) {
                Ordering::Equal => {}
                o => return o,
            }
        }
        Ordering::Equal
    }

    /// `Solve_state.compare`
    pub fn compare(&self, s2: &Self) -> Ordering {
        if self.cost != s2.cost {
            self.cost.cmp(&s2.cost)
        } else if self.overflow != s2.overflow {
            self.overflow.cmp(&s2.overflow)
        } else {
            self.compare_rule_sets(s2)
        }
    }

    /// Whether `pick_best_state self s2` picks `self`.
    pub fn is_better_than(&self, s2: &Self) -> bool {
        if self.overflow != s2.overflow {
            self.overflow < s2.overflow
        } else {
            self.compare(s2) == Ordering::Less
        }
    }

    /// `Solve_state.__debug`
    pub fn debug_string(&self) -> String {
        let rule_strings: Vec<String> = self
            .rbm
            .iter()
            .enumerate()
            .filter_map(|(k, v)| v.map(|v| format!("{}: {}", k, v)))
            .collect();
        format!(
            "{},{} {} [{}]",
            self.overflow,
            self.cost,
            self.chunk_group.get_rule_count(),
            rule_strings.join(",")
        )
    }
}

fn compute_indent_level(chunk_group: &ChunkGroup<'_>, nesting_set: &[bool], chunk: &Chunk<'_>) -> isize {
    chunk_group.block_indentation + chunk_group.get_indent_level(chunk.nesting, nesting_set)
}

fn get_indent_columns(env: &Env, chunk_group: &ChunkGroup<'_>, nesting_set: &[bool], chunk: &Chunk<'_>) -> isize {
    env.indent_width * compute_indent_level(chunk_group, nesting_set, chunk)
}

/// `Solve_state.build_lines`: a list of lines, each with its overflow and
/// (as a range of chunks) the rules of its chunks.
fn build_lines(
    env: &Env,
    chunk_group: &ChunkGroup<'_>,
    rbm: &Rbm,
    nesting_set: &[bool],
) -> Vec<(isize, std::ops::Range<usize>)> {
    let chunks = &chunk_group.chunks;
    let mut result = vec![];
    let mut acc_len: isize = 0;
    let mut line_start = 0;
    for (i, hd) in chunks.iter().enumerate() {
        let is_split = rbm_has_split_before_chunk(hd, rbm);
        let has_comma = rbm_has_comma_after_chunk(hd, rbm);
        let text_length = isize::from(has_comma) + hd.length as isize;
        let prefix_whitespace_length = if is_split && hd.indentable {
            get_indent_columns(env, chunk_group, nesting_set, hd)
        } else if hd.space_if_not_split {
            1
        } else {
            0
        };
        let chunk_len = text_length + prefix_whitespace_length;
        if is_split {
            result.push((get_overflow(env, acc_len), line_start..i));
            acc_len = chunk_len;
            line_start = i;
        } else {
            acc_len += chunk_len;
        }
    }
    result.push((get_overflow(env, acc_len), line_start..chunks.len()));
    result
}

fn build_candidate_rules_and_update_rbm(
    chunk_group: &ChunkGroup<'_>,
    rbm: &mut Rbm,
    lines: &[(isize, std::ops::Range<usize>)],
) -> Vec<usize> {
    let chunks = &chunk_group.chunks;
    let n = rbm.len();
    let mut dead_rules = vec![false; n];
    let mut base_candidate_rules = vec![false; n];
    for (overflow, range) in lines {
        let has_unbound = chunks[range.clone()].iter().any(|c| rbm[c.rule()].is_none());
        if *overflow == 0 || !has_unbound {
            for c in &chunks[range.clone()] {
                if rbm[c.rule()].is_none() {
                    dead_rules[c.rule()] = true;
                }
            }
        } else {
            for c in &chunks[range.clone()] {
                base_candidate_rules[c.rule()] = true;
            }
            break;
        }
    }
    // Also add parent rules
    let mut candidate_rules = base_candidate_rules.clone();
    for (id, is_candidate) in base_candidate_rules.iter().enumerate() {
        if *is_candidate {
            for parent in &chunk_group.deps[id] {
                candidate_rules[*parent] = true;
            }
        }
    }
    for id in 0..n {
        if dead_rules[id] && !candidate_rules[id] && rbm[id].is_none() {
            rbm[id] = Some(false);
        }
    }
    (0..n).filter(|id| candidate_rules[*id]).collect()
}

fn calculate_partially_bound(
    chunks: &[Chunk<'_>],
    rbm: &Rbm,
    lines: &[(isize, std::ops::Range<usize>)],
) -> (isize, Vec<usize>) {
    let mut unprocessed = 0;
    let mut rules = vec![];
    for (overflow, range) in lines {
        let line = &chunks[range.clone()];
        if line.iter().any(|c| rbm[c.rule()].is_none()) {
            unprocessed += overflow;
            for c in line {
                if rbm[c.rule()].is_some() {
                    rules.push(c.rule());
                }
            }
        }
    }
    rules.sort_unstable();
    rules.dedup();
    (unprocessed, rules)
}

fn add_breaks_from_source(mut rbm: Rbm, source_text: &[u8], chunk_group: &ChunkGroup<'_>) -> Rbm {
    rbm.resize(chunk_group.get_rule_count(), None);
    let mut prev_chunk_end: isize = 0;
    for chunk in &chunk_group.chunks {
        let (chunk_start, chunk_end) = chunk.get_range();
        let mut i = prev_chunk_end;
        let mut found = false;
        while i < chunk_start {
            match source_text.get(i as usize) {
                Some(b'\n') => {
                    found = true;
                    break;
                }
                Some(_) => {}
                None => crate::error::raise(crate::error::Exn::InvalidArgument(
                    "index out of bounds".into(),
                )),
            }
            i += 1;
        }
        if found {
            rbm[chunk.rule()] = Some(true);
        }
        prev_chunk_end = chunk_end;
    }
    rbm
}

/// `Solve_state.rbm_from_source`
pub fn rbm_from_source(source_text: &[u8], chunk_group: &ChunkGroup<'_>) -> Rbm {
    add_breaks_from_source(vec![], source_text, chunk_group)
}

/// `Solve_state.rbm_broken_everywhere`: every rule is broken.
pub fn rbm_broken_everywhere(chunk_group: &ChunkGroup<'_>) -> Rbm {
    vec![Some(true); chunk_group.get_rule_count()]
}
