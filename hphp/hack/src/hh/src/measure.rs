// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/measure.ml`. See `hh/PORTING.md`.
//!
//! Only [`sample`] so far, with what it needs (the records, the global
//! record, the distributions), and [`get_sum`], [`get_count`],
//! [`peek_global`]. Not here: `track_distribution`, `time`, `delete`,
//! `merge`, `push_global`, `pop_global`, the other getters, the printers and
//! `serialize`/`deserialize`.
//!
//! A record is shared (`record_data ref`): [`Record`] is an
//! `Rc<RefCell<RecordData>>`. The global stack of records is kept per thread,
//! as `crate::diagnostics` keeps its state: one file is checked on one
//! thread, as one file is checked by one worker process in OCaml, whose
//! records the master merges.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::Rc;

use crate::s_map;

/// `Float.compare` (Base's, which is the polymorphic compare of OCaml on
/// floats, `caml_float_compare`): `nan` is equal to itself and smaller than
/// any other float, and `-0.` is equal to `0.`.
fn float_compare(f: f64, g: f64) -> Ordering {
    #[allow(clippy::eq_op)]
    let res = (f > g) as isize - (f < g) as isize + (f == f) as isize - (g == g) as isize;
    res.cmp(&0)
}

/// A key of `FloatMap` (`Wrapped_map.Make (struct type t = float let compare
/// = Float.compare end)`), ordered by `Float.compare`.
#[derive(Clone, Copy, Debug)]
pub struct FloatKey(pub f64);

impl PartialEq for FloatKey {
    fn eq(&self, other: &Self) -> bool {
        float_compare(self.0, other.0) == Ordering::Equal
    }
}

impl Eq for FloatKey {}

impl PartialOrd for FloatKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FloatKey {
    fn cmp(&self, other: &Self) -> Ordering {
        float_compare(self.0, other.0)
    }
}

/// `module FloatMap`
pub mod float_map {
    pub type T<A> = im::OrdMap<super::FloatKey, A>;
}

#[derive(Clone, Debug)]
pub struct Distribution {
    pub bucket_size: f64,
    pub buckets: float_map::T<f64>,
}

#[derive(Clone, Debug)]
pub struct RecordEntry {
    pub count: f64,
    pub mean: f64,
    pub variance_sum: f64,
    pub max: f64,
    pub min: f64,
    pub distribution: Option<Distribution>,
}

pub type RecordData = s_map::T<RecordEntry>;

/// `record = record_data ref`
pub type Record = Rc<RefCell<RecordData>>;

/// Creates a new empty record
pub fn create() -> Record {
    Rc::new(RefCell::new(RecordData::new()))
}

thread_local! {
    /// `global : record list ref`, for this thread. The head of the OCaml
    /// list is the last element.
    static GLOBAL: RefCell<Vec<Record>> = RefCell::new(vec![create()]);
}

/// (`Float.min_value` and `Float.max_value` are Base's: `neg_infinity` and
/// `infinity`.)
fn new_entry() -> RecordEntry {
    RecordEntry {
        count: 0.0,
        mean: 0.0,
        variance_sum: 0.0,
        max: f64::NEG_INFINITY,
        min: f64::INFINITY,
        distribution: None,
    }
}

fn get_record(record: Option<&Record>) -> Record {
    match record {
        Some(record) => Rc::clone(record),
        None => match GLOBAL.with(|g| g.borrow().last().cloned()) {
            Some(record) => record,
            None => panic!(
                "{}",
                "No global record available! ".to_string()
                    + "Did you forget to call Measure.push_global?"
            ),
        },
    }
}

/// (`Float.round_down` is `floor`.)
fn round_down(bucket_size: f64, value: f64) -> f64 {
    bucket_size * (value / bucket_size).floor()
}

fn update_distribution(
    weight: f64,
    value: f64,
    distribution: Option<Distribution>,
) -> Option<Distribution> {
    match distribution {
        None => None,
        Some(Distribution {
            bucket_size,
            buckets,
        }) => {
            let bucket = round_down(bucket_size, value);
            let bucket_count = match buckets.get(&FloatKey(bucket)) {
                None => weight,
                Some(count) => count + weight,
            };
            let buckets = buckets.update(FloatKey(bucket), bucket_count);
            Some(Distribution {
                bucket_size,
                buckets,
            })
        }
    }
}

/// `Stdlib.max` on floats: `if a >= b then a else b`.
fn stdlib_max(a: f64, b: f64) -> f64 {
    if a >= b { a } else { b }
}

/// `Stdlib.min` on floats: `if a <= b then a else b`.
fn stdlib_min(a: f64, b: f64) -> f64 {
    if a <= b { a } else { b }
}

/// `weight` defaults to 1.0.
pub fn sample(record: Option<&Record>, weight: Option<f64>, name: &str, value: f64) {
    let weight = weight.unwrap_or(1.0);
    let record = get_record(record);
    let RecordEntry {
        count: old_count,
        mean: old_mean,
        variance_sum,
        max,
        min,
        distribution,
    } = match record.borrow().get(name) {
        None => new_entry(),
        Some(entry) => entry.clone(),
    };
    // Add 1 * weight to the count
    let count = old_count + weight;
    let mean = old_mean + (weight * (value - old_mean) / count);
    // Knuth's online variance approximation algorithm, updated for weights.
    // Weighted version from http://people.ds.cam.ac.uk/fanf2/hermes/doc/antiforgery/stats.pdf
    let variance_sum = variance_sum + (weight * (value - old_mean) * (value - mean));
    let max = stdlib_max(max, value);
    let min = stdlib_min(min, value);
    let distribution = update_distribution(weight, value, distribution);
    let entry = RecordEntry {
        count,
        mean,
        variance_sum,
        max,
        min,
        distribution,
    };
    record.borrow_mut().insert(name.to_string(), entry);
}

fn get_helper(f: impl Fn(&RecordEntry) -> f64, record: Option<&Record>, name: &str) -> Option<f64> {
    let record = get_record(record);
    record.borrow().get(name).map(f)
}

/// `get_sum ?record name`
pub fn get_sum(record: Option<&Record>, name: &str) -> Option<f64> {
    get_helper(|e| e.count * e.mean, record, name)
}

/// `get_count ?record name`
pub fn get_count(record: Option<&Record>, name: &str) -> Option<f64> {
    get_helper(|e| e.count, record, name)
}

/// `peek_global ()`: a copy of the current global record, without modifying
/// it or the stack. (The OCaml also merges in the records of the Rust
/// `measure` crate; the port is Rust, and its samples are all in these
/// records.)
pub fn peek_global() -> Record {
    Rc::new(RefCell::new(get_record(None).borrow().clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn samples() {
        let record = create();
        sample(Some(&record), None, "x", 2.0);
        sample(Some(&record), None, "x", 4.0);
        sample(Some(&record), Some(2.0), "x", 6.0);
        let entry = record.borrow().get("x").cloned().unwrap();
        assert_eq!(entry.count, 4.0);
        assert_eq!(entry.mean, 4.5);
        assert_eq!(entry.max, 6.0);
        assert_eq!(entry.min, 2.0);
        assert!(entry.distribution.is_none());
        // The global record of this thread.
        sample(None, None, "y", 1.0);
        let global_record = get_record(None);
        assert_eq!(global_record.borrow().get("y").unwrap().count, 1.0);
    }

    #[test]
    fn distributions_and_float_order() {
        let d = update_distribution(
            1.0,
            17.0,
            Some(Distribution {
                bucket_size: 10.0,
                buckets: float_map::T::new(),
            }),
        );
        let d = update_distribution(1.0, 12.0, d).unwrap();
        assert_eq!(d.buckets.get(&FloatKey(10.0)), Some(&2.0));
        assert_eq!(float_compare(f64::NAN, f64::NAN), Ordering::Equal);
        assert_eq!(float_compare(f64::NAN, f64::NEG_INFINITY), Ordering::Less);
        assert_eq!(float_compare(-0.0, 0.0), Ordering::Equal);
        assert_eq!(float_compare(1.0, 2.0), Ordering::Less);
    }
}
