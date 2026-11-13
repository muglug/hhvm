// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! interval.ml: helpers for half-open intervals.

pub type Interval = (isize, isize);

pub fn show((st, ed): Interval) -> String {
    format!("[{}, {})", st, ed)
}

pub fn contains((st, ed): Interval, point: isize) -> bool {
    st <= point && point < ed
}

pub fn contains_interval(a: Interval, b: Interval) -> bool {
    a.0 <= b.0 && a.1 >= b.1
}

pub fn intervals_overlap(a: Interval, b: Interval) -> bool {
    let (a_start, a_end) = a;
    let (b_start, b_end) = b;
    a_start == b_start || (a_start < b_start && b_start < a_end) || (b_start < a_start && a_start < b_end)
}

/// Does not union adjacent intervals
pub fn union(a: Interval, b: Interval) -> Option<Interval> {
    if intervals_overlap(a, b) {
        Some((std::cmp::min(a.0, b.0), std::cmp::max(a.1, b.1)))
    } else {
        None
    }
}

/// Does not union adjacent intervals
pub fn union_consecutive_overlapping(intervals: &[Interval]) -> Vec<Interval> {
    let Some((hd, tl)) = intervals.split_first() else {
        return vec![];
    };
    let mut result = vec![];
    let mut last = *hd;
    for next in tl {
        match union(last, *next) {
            None => {
                result.push(last);
                last = *next;
            }
            Some(u) => last = u,
        }
    }
    result.push(last);
    result
}

pub fn compare(a: Interval, b: Interval) -> std::cmp::Ordering {
    if a.0 == b.0 { a.1.cmp(&b.1) } else { a.0.cmp(&b.0) }
}

fn difference(a: Interval, b: Interval) -> Vec<Interval> {
    let (a_start, a_end) = a;
    let (b_start, b_end) = b;
    if !intervals_overlap(a, b) {
        vec![a]
    } else if contains_interval(b, a) {
        vec![]
    } else if contains(b, a_start) {
        vec![(b_end, a_end)]
    } else if contains(b, a_end) {
        vec![(a_start, b_start)]
    } else if contains_interval(a, b) {
        vec![(a_start, b_start), (b_end, a_end)]
    } else {
        crate::chunk::panic_failure(&format!(
            "Interval.difference: invalid intervals: {} {}",
            show(a),
            show(b)
        ))
    }
}

/// Subtract `subtrahends` from `minuends`.
///
/// Assumes both lists are sorted and non-overlapping.
pub fn diff_sorted_lists(minuends: &[Interval], subtrahends: &[Interval]) -> Vec<Interval> {
    if subtrahends.is_empty() {
        return minuends.to_vec();
    }
    let mut acc = vec![];
    // The remaining minuends, front first.
    let mut minuends: std::collections::VecDeque<Interval> = minuends.iter().copied().collect();
    let mut subtrahends = subtrahends;
    loop {
        let Some(&minuend) = minuends.front() else {
            break;
        };
        let Some(&subtrahend) = subtrahends.first() else {
            acc.extend(minuends.drain(..));
            break;
        };
        if intervals_overlap(minuend, subtrahend) {
            minuends.pop_front();
            for d in difference(minuend, subtrahend).into_iter().rev() {
                minuends.push_front(d);
            }
        } else if minuend.1 <= subtrahend.0 {
            acc.push(minuend);
            minuends.pop_front();
        } else if subtrahend.1 <= minuend.0 {
            subtrahends = &subtrahends[1..];
        } else {
            crate::chunk::panic_failure("Invalid interval lists")
        }
    }
    acc
}
