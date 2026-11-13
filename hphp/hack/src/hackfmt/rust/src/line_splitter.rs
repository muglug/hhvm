// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! line_splitter.ml, state_queue.ml and priority_queue.ml

use std::cmp::Ordering;

use crate::chunk::ChunkGroup;
use crate::format_env::Env;
use crate::interval;
use crate::interval::Interval;
use crate::solve_state;
use crate::solve_state::SolveState;
use crate::subchunk;

/// `State_queue`: `Priority_queue.Make (Solve_state)` with `push` replaced by
/// one that merges overlapping states.
struct StateQueue<'g, 'a> {
    queue: Vec<SolveState<'g, 'a>>,
}

impl<'g, 'a> StateQueue<'g, 'a> {
    fn new() -> Self {
        StateQueue { queue: vec![] }
    }

    fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn bubble_up(&mut self, index: usize) {
        let mut index = index;
        loop {
            // OCaml's (index - 1) / 2 is 0 for index 0.
            let pindex = if index == 0 { 0 } else { (index - 1) / 2 };
            if self.queue[index].compare(&self.queue[pindex]) == Ordering::Less {
                self.queue.swap(index, pindex);
                index = pindex;
            } else {
                break;
            }
        }
    }

    /// `__bubble_down arr size value index`, where `value` is the state
    /// currently at `index`.
    fn bubble_down(&mut self, index: usize) {
        let size = self.queue.len();
        let mut index = index;
        loop {
            let right = index * 2 + 2;
            let left = right - 1;
            if right < size {
                let smaller = if self.queue[right].compare(&self.queue[left]) == Ordering::Less {
                    right
                } else {
                    left
                };
                if self.queue[index].compare(&self.queue[smaller]) != Ordering::Greater {
                    break;
                }
                self.queue.swap(index, smaller);
                index = smaller;
            } else if left < size {
                if self.queue[index].compare(&self.queue[left]) == Ordering::Greater {
                    self.queue.swap(index, left);
                }
                break;
            } else {
                break;
            }
        }
    }

    fn pop(&mut self) -> SolveState<'g, 'a> {
        let v = self.queue.swap_remove(0);
        if !self.queue.is_empty() {
            self.bubble_down(0);
        }
        v
    }

    fn priority_push(&mut self, state: SolveState<'g, 'a>) {
        self.queue.push(state);
        let i = self.queue.len() - 1;
        self.bubble_up(i);
    }

    /// `State_queue.push`
    fn push(&mut self, state: SolveState<'g, 'a>) {
        for i in 0..self.queue.len() {
            if state.is_overlapping(&self.queue[i]) {
                // Solve_state.pick_best_state state e
                if state.is_better_than(&self.queue[i]) {
                    self.queue[i] = state;
                }
                self.bubble_down(i);
                self.bubble_up(i);
                return;
            }
        }
        self.priority_push(state);
    }
}

fn expand_state<'g, 'a>(env: &Env, state: &SolveState<'g, 'a>) -> Vec<SolveState<'g, 'a>> {
    let chunk_group = state.chunk_group;
    let mut env_rbm = state.rbm.clone();
    let mut next_rbms = vec![];
    for &rule_id in state.get_candidate_rules() {
        if state.is_rule_bound(rule_id) {
            continue;
        }
        let mut next_rbm = env_rbm.clone();
        next_rbm[rule_id] = Some(true);
        if chunk_group.are_rule_bindings_valid(&next_rbm) {
            env_rbm[rule_id] = Some(false);
            next_rbms.push(next_rbm);
        }
    }
    next_rbms
        .into_iter()
        .map(|rbm| SolveState::make(env, chunk_group, rbm))
        .collect()
}

fn find_best_state<'g, 'a>(env: &Env, init_state: SolveState<'g, 'a>) -> Option<SolveState<'g, 'a>> {
    let mut queue = StateQueue::new();
    for s in expand_state(env, &init_state) {
        queue.push(s);
    }
    let mut best = init_state;
    let mut count = 0;
    loop {
        if count > 100 {
            return None;
        } else if queue.is_empty() || best.overflow == 0 {
            return Some(best);
        } else {
            let next_state = queue.pop();
            for s in expand_state(env, &next_state) {
                queue.push(s);
            }
            count += 1;
            if next_state.is_better_than(&best) {
                best = next_state;
            }
        }
    }
}

fn solve_chunk_group<'g, 'a>(
    env: &Env,
    range: Option<Interval>,
    source_text: Option<&[u8]>,
    chunk_group: &'g ChunkGroup<'a>,
) -> SolveState<'g, 'a> {
    let rbm = match range {
        Some(range)
            if {
                let group_range = chunk_group.get_char_range();
                let (st, ed) = range;
                interval::contains(group_range, st) || interval::contains(group_range, ed)
            } =>
        {
            let n = chunk_group.get_rule_count();
            let source_rbm = match source_text {
                Some(st) => solve_state::rbm_from_source(st, chunk_group),
                None => solve_state::rbm_broken_everywhere(chunk_group),
            };
            // Build two sets of rule IDs: the rules associated with at least
            // one split outside of the formatting range, and the rules
            // associated with at least one split inside the formatting range.
            // Contract the range to work around edge cases: if a chunk starts
            // on the first character of the range, we don't want to consider
            // its split to be inside the range.
            let contracted = (range.0 + 1, range.1);
            let mut rules_in_range = vec![false; n];
            let mut rules_out_of_range = vec![false; n];
            for chunk in &chunk_group.chunks {
                if interval::contains(contracted, chunk.start_char) {
                    rules_in_range[chunk.rule()] = true;
                } else {
                    rules_out_of_range[chunk.rule()] = true;
                }
            }
            let mut bindings: solve_state::Rbm = vec![None; n];
            // If we have a rule associated with a split outside of the
            // formatting range which was broken in the original source, the
            // output will look strange if we don't break all of that rule's
            // associated splits inside the formatting range, too.
            for id in 0..n {
                if source_rbm.get(id).copied().flatten() == Some(true) && rules_out_of_range[id] {
                    bindings[id] = Some(true);
                }
            }
            // We should also break any rule which is configured to ALWAYS
            // break and has a split inside the formatting range.
            for id in chunk_group.get_always_rules() {
                if rules_in_range[id] {
                    bindings[id] = Some(true);
                }
            }
            // Break any Parental rules which contain the rules we decided to
            // break above, but only for rules which do not have any
            // associated splits outside of the formatting range.
            let propagated = chunk_group.propagate_breakage(&bindings);
            for id in 0..n {
                if bindings[id].is_none()
                    && propagated[id].is_some()
                    && rules_in_range[id]
                    && !rules_out_of_range[id]
                {
                    bindings[id] = propagated[id];
                }
            }
            bindings
        }
        _ => chunk_group.get_initial_rule_bindings(),
    };
    let init_state = SolveState::make(env, chunk_group, rbm);
    match find_best_state(env, init_state) {
        Some(state) => state,
        None => match source_text {
            Some(s) => SolveState::from_source(env, s, chunk_group),
            None => {
                let rbm = solve_state::rbm_broken_everywhere(chunk_group);
                SolveState::make(env, chunk_group, rbm)
            }
        },
    }
}

pub fn find_solve_states<'g, 'a>(
    env: &Env,
    range: Option<Interval>,
    source_text: Option<&[u8]>,
    chunk_groups: &'g [ChunkGroup<'a>],
) -> Vec<SolveState<'g, 'a>> {
    chunk_groups
        .iter()
        .filter(|chunk_group| match range {
            None => true,
            Some(range) => interval::intervals_overlap(range, chunk_group.get_char_range()),
        })
        .map(|chunk_group| solve_chunk_group(env, range, source_text, chunk_group))
        .collect()
}

pub fn print(
    env: &Env,
    range: Option<Interval>,
    include_leading_whitespace: bool,
    include_trailing_whitespace: bool,
    solve_states: &[SolveState<'_, '_>],
) -> Vec<u8> {
    let mut subchunks = vec![];
    for s in solve_states {
        subchunks.extend(subchunk::subchunks_of_solve_state(s));
    }
    let subchunks = match range {
        None => subchunks,
        Some(range) => subchunk::subchunks_in_range(
            include_leading_whitespace,
            include_trailing_whitespace,
            subchunks,
            range,
        ),
    };
    subchunk::string_of_subchunks(env, &subchunks)
}

/// `Line_splitter.solve`
pub fn solve(
    env: &Env,
    range: Option<Interval>,
    include_leading_whitespace: bool,
    include_trailing_whitespace: bool,
    source_text: Option<&[u8]>,
    chunk_groups: &[ChunkGroup<'_>],
) -> Vec<u8> {
    let states = find_solve_states(env, range, source_text, chunk_groups);
    print(
        env,
        range,
        include_leading_whitespace,
        include_trailing_whitespace,
        &states,
    )
}
