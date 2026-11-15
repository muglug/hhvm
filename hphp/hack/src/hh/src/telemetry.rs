// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/telemetry.ml`. See `hh/PORTING.md`.
//!
//! Not ported: `quick_gc_stat` (the statistics of the OCaml garbage
//! collector), `of_yojson_opt`, `string_list_opt`,
//! `float_list`, `with_duration` and `error_with_stack`, which the
//! typechecker does not use.

use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::rt::ocaml_unix::gettimeofday;
use crate::yojson::safe as yojson;

type KeyValuePair = (String, yojson::T);

/// This list is in reverse order (i.e. most recent first)
#[derive(Clone, Debug, PartialEq, Default)]
pub struct T(Vec<KeyValuePair>);

/// `x :: l`
fn cons<A>(x: A, mut l: Vec<A>) -> Vec<A> {
    l.insert(0, x);
    l
}

fn compare(left: &KeyValuePair, right: &KeyValuePair) -> std::cmp::Ordering {
    left.0.as_bytes().cmp(right.0.as_bytes())
}

/// `List.sort ~compare`: a stable sort.
fn sort(mut l: Vec<KeyValuePair>) -> Vec<KeyValuePair> {
    l.sort_by(compare);
    l
}

pub fn create() -> T {
    T(vec![])
}

pub fn to_yojson(telemetry: &T) -> yojson::T {
    yojson::T::Assoc(telemetry.0.iter().rev().cloned().collect())
}

/// `pretty` defaults to `false`.
pub fn to_string(pretty: Option<bool>, telemetry: &T) -> String {
    let pretty = pretty.unwrap_or(false);
    let json = to_yojson(telemetry);
    if pretty {
        todo!("Telemetry.to_string ~pretty:true: Yojson.Safe.pretty_to_string is not ported")
    } else {
        yojson::to_string(&json)
    }
}

pub fn string_(truncate: Option<isize>, key: &str, value: &str, telemetry: T) -> T {
    let value = match truncate {
        None => value.to_string(),
        Some(truncate) => crate::string_utils::truncate(truncate, value),
    };
    T(cons((key.to_string(), yojson::T::String(value)), telemetry.0))
}

pub fn string_opt(truncate: Option<isize>, key: &str, value: Option<&str>, telemetry: T) -> T {
    match value {
        None => T(cons((key.to_string(), yojson::T::Null), telemetry.0)),
        Some(value) => string_(truncate, key, value, telemetry),
    }
}

pub fn object_list(key: &str, value: &[T], telemetry: T) -> T {
    let value = value.iter().map(to_yojson).collect();
    T(cons((key.to_string(), yojson::T::List(value)), telemetry.0))
}

pub fn bool_(key: &str, value: bool, telemetry: T) -> T {
    T(cons((key.to_string(), yojson::T::Bool(value)), telemetry.0))
}

pub fn int_(key: &str, value: isize, telemetry: T) -> T {
    T(cons((key.to_string(), yojson::T::Int(value)), telemetry.0))
}

pub fn int_opt(key: &str, value: Option<isize>, telemetry: T) -> T {
    match value {
        None => T(cons((key.to_string(), yojson::T::Null), telemetry.0)),
        Some(value) => int_(key, value, telemetry),
    }
}

pub fn int_list(truncate_list: Option<isize>, key: &str, value: &[isize], telemetry: T) -> T {
    let value = match truncate_list {
        None => value,
        // `List.take`: the whole list when it is shorter, nothing for a
        // negative length.
        Some(truncate_list) => &value[..(truncate_list.max(0) as usize).min(value.len())],
    };
    let value = value.iter().map(|i| yojson::T::Int(*i)).collect();
    T(cons((key.to_string(), yojson::T::List(value)), telemetry.0))
}

pub fn json(key: &str, value: yojson::T, telemetry: T) -> T {
    T(cons((key.to_string(), value), telemetry.0))
}

pub fn json_opt(key: &str, value: Option<yojson::T>, telemetry: T) -> T {
    let value = match value {
        None => yojson::T::Null,
        Some(v) => v,
    };
    T(cons((key.to_string(), value), telemetry.0))
}

/// The `error ~stack e` pair: `("error", {"stack": .., "message": e})`.
fn error_pair(stack: Option<String>, e: &str) -> KeyValuePair {
    let mut vals = vec![("message".to_string(), yojson::T::String(e.to_string()))];
    if let Some(stack) = stack {
        vals = cons(("stack".to_string(), yojson::T::String(stack)), vals);
    }
    ("error".to_string(), yojson::T::Assoc(vals))
}

/// `exception_ ~e telemetry`
pub fn exception_(e: &crate::exception::T, telemetry: T) -> T {
    let pair = error_pair(
        Some(crate::exception::get_backtrace_string(e)),
        &crate::exception::get_ctor_string(e),
    );
    T(cons(pair, telemetry.0))
}

/// `error ~e telemetry`
pub fn error(e: &str, telemetry: T) -> T {
    T(cons(error_pair(None, e), telemetry.0))
}

pub fn object_(key: &str, value: T, telemetry: T) -> T {
    let value = yojson::T::Assoc(value.0.into_iter().rev().collect());
    T(cons((key.to_string(), value), telemetry.0))
}

pub fn object_opt(key: &str, value: Option<T>, telemetry: T) -> T {
    match value {
        None => T(cons((key.to_string(), yojson::T::Null), telemetry.0)),
        Some(value) => object_(key, value, telemetry),
    }
}

/// `key` defaults to `"duration"` and `end_time` to now. The duration is in
/// milliseconds.
pub fn duration(key: Option<&str>, start_time: f64, end_time: Option<f64>, telemetry: T) -> T {
    let key = key.unwrap_or("duration");
    let end_time = end_time.unwrap_or_else(gettimeofday);
    let seconds = end_time - start_time;
    // `int_of_float`
    let ms = (1000.0 * seconds) as isize;
    T(cons((key.to_string(), yojson::T::Int(ms)), telemetry.0))
}

/// (Added for the file watchers.) Like [`duration`], but adds the integer
/// durations already recorded under `key` (which are removed) to the new one.
/// `key` defaults to `"duration"` and `end_time` to now.
pub fn add_duration(key: Option<&str>, start_time: f64, end_time: Option<f64>, telemetry: T) -> T {
    let key = key.unwrap_or("duration");
    let end_time = end_time.unwrap_or_else(gettimeofday);
    let seconds = end_time - start_time;
    let new_duration_ms = (1000.0 * seconds) as isize;
    // `List.fold_right`: the entries that are not durations of `key` keep
    // their order.
    let mut previous_duration_ms = 0;
    let mut filtered_telemetry = Vec::with_capacity(telemetry.0.len());
    for (cur_key, cur_value) in telemetry.0 {
        match cur_value {
            yojson::T::Int(cur_value) if cur_key == key => previous_duration_ms += cur_value,
            cur_value => filtered_telemetry.push((cur_key, cur_value)),
        }
    }
    let overall_duration_ms = new_duration_ms + previous_duration_ms;
    T(cons(
        (key.to_string(), yojson::T::Int(overall_duration_ms)),
        filtered_telemetry,
    ))
}

/// (Added for the file watchers.)
pub fn string_list(
    truncate_list: Option<isize>,
    truncate_each_string: Option<isize>,
    key: &str,
    value: &[String],
    telemetry: T,
) -> T {
    let value = match truncate_list {
        None => value,
        // `List.take`
        Some(truncate_list) => &value[..(truncate_list.max(0) as usize).min(value.len())],
    };
    let value: Vec<String> = match truncate_each_string {
        None => value.to_vec(),
        Some(truncate_each_string) => value
            .iter()
            .map(|s| crate::string_utils::truncate(truncate_each_string, s))
            .collect(),
    };
    let value = value.into_iter().map(yojson::T::String).collect();
    T(cons((key.to_string(), yojson::T::List(value)), telemetry.0))
}

pub fn float_(key: &str, value: f64, telemetry: T) -> T {
    if value.is_nan() || value.is_infinite() {
        T(cons((key.to_string(), yojson::T::Null), telemetry.0))
    } else {
        T(cons((key.to_string(), yojson::T::Float(value)), telemetry.0))
    }
}

pub fn float_opt(key: &str, value: Option<f64>, telemetry: T) -> T {
    match value {
        None => T(cons((key.to_string(), yojson::T::Null), telemetry.0)),
        Some(value) => float_(key, value, telemetry),
    }
}

/// Extract an int from a Yojson number
fn yojson_to_int_opt(json: &yojson::T) -> Option<isize> {
    match json {
        yojson::T::Int(i) => Some(*i),
        yojson::T::Intlit(s) => int_of_string_opt(s),
        _ => None,
    }
}

/// Extract a float from a Yojson number
fn yojson_to_float_opt(json: &yojson::T) -> Option<f64> {
    match json {
        yojson::T::Int(i) => Some(*i as f64),
        yojson::T::Float(f) => Some(*f),
        // `Float.of_string_opt`. An `Intlit` is an integer that does not fit
        // in an `int`: digits, which Rust reads like OCaml does.
        yojson::T::Intlit(s) => s.replace('_', "").parse().ok(),
        _ => None,
    }
}

/// Check if two Yojson values are equal (shallow, for telemetry diff)
fn yojson_equal(a: &yojson::T, b: &yojson::T) -> bool {
    match (a, b) {
        (yojson::T::Int(a), yojson::T::Int(b)) => a == b,
        (yojson::T::Float(a), yojson::T::Float(b)) => a == b,
        (yojson::T::String(a), yojson::T::String(b)) => a == b,
        (yojson::T::Bool(a), yojson::T::Bool(b)) => a == b,
        (yojson::T::Null, yojson::T::Null) => true,
        _ => false,
    }
}

/// `diff ~all current ~prev` is for when `current` and `prev` have the same
/// structure. It produces a hybrid telemetry object where, element by
/// element, if they're the same then we only see the current element, but if
/// they're different then we see both. (If you pass ~all:true then it hides
/// elements that have remained the same.) It works with nested telemetry
/// objects. In places where the structure differs, only `current` is kept.
///
/// `suffix_keys` defaults to `true`.
pub fn diff(all: bool, suffix_keys: Option<bool>, telemetry: &T, prev: &T) -> T {
    let suffix_keys = suffix_keys.unwrap_or(true);
    let (prev_suffix, diff_suffix) = if suffix_keys {
        ("__prev", "__diff")
    } else {
        ("", "")
    };

    struct Diff {
        all: bool,
        prev_suffix: &'static str,
        diff_suffix: &'static str,
    }

    impl Diff {
        fn diff(&self, telemetry: Vec<KeyValuePair>, prev: Vec<KeyValuePair>) -> Vec<KeyValuePair> {
            let telemetry = sort(telemetry);
            let prev = sort(prev);
            self.diff_already_sorted(&telemetry, &prev, vec![])
        }

        fn diff_already_sorted(
            &self,
            mut current: &[KeyValuePair],
            mut prev: &[KeyValuePair],
            mut acc: Vec<KeyValuePair>,
        ) -> Vec<KeyValuePair> {
            use std::cmp::Ordering;
            loop {
                match (current, prev, self.all) {
                    ([], [], _) => return acc,
                    ([c, cs @ ..], [], true) => {
                        acc = self.diff_no_prev(c, acc);
                        current = cs;
                    }
                    (_, [], false) => return acc,
                    ([], [p, ps @ ..], true) => {
                        acc = self.diff_no_current(p, acc);
                        prev = ps;
                    }
                    ([], _, false) => return acc,
                    ([c, cs @ ..], [p, ..], true) if compare(c, p) == Ordering::Less => {
                        acc = self.diff_no_prev(c, acc);
                        current = cs;
                    }
                    ([c, ..], [p, ps @ ..], false) if compare(c, p) == Ordering::Greater => {
                        acc = self.diff_no_current(p, acc);
                        prev = ps;
                    }
                    ([c, cs @ ..], [p, ps @ ..], _) => {
                        acc = self.diff_both(c, p, acc);
                        current = cs;
                        prev = ps;
                    }
                }
            }
        }

        fn diff_no_prev(
            &self,
            (key, val_c): &KeyValuePair,
            acc: Vec<KeyValuePair>,
        ) -> Vec<KeyValuePair> {
            cons(
                (key.clone(), val_c.clone()),
                cons((format!("{}__prev", key), yojson::T::Null), acc),
            )
        }

        fn diff_no_current(
            &self,
            (key, val_p): &KeyValuePair,
            acc: Vec<KeyValuePair>,
        ) -> Vec<KeyValuePair> {
            match val_p {
                yojson::T::Assoc(elems) => {
                    let elems = elems
                        .iter()
                        .fold(vec![], |acc, e| self.diff_no_current(e, acc));
                    cons(
                        (key.clone(), yojson::T::Null),
                        cons(
                            (
                                format!("{}{}", key, self.prev_suffix),
                                yojson::T::Assoc(elems),
                            ),
                            acc,
                        ),
                    )
                }
                _ => cons(
                    (key.clone(), yojson::T::Null),
                    cons(
                        (format!("{}{}", key, self.prev_suffix), val_p.clone()),
                        acc,
                    ),
                ),
            }
        }

        fn acc_if(&self, b: bool, elem: KeyValuePair, acc: Vec<KeyValuePair>) -> Vec<KeyValuePair> {
            if b { cons(elem, acc) } else { acc }
        }

        fn diff_both(
            &self,
            (key, val_c): &KeyValuePair,
            (_key, val_p): &KeyValuePair,
            acc: Vec<KeyValuePair>,
        ) -> Vec<KeyValuePair> {
            use yojson::T as J;
            match (val_c, val_p) {
                (J::Assoc(elems_c), J::Assoc(elems_p)) => {
                    let elems = self.diff(elems_c.clone(), elems_p.clone());
                    self.acc_if(
                        self.all || !elems.is_empty(),
                        (key.clone(), J::Assoc(elems)),
                        acc,
                    )
                }
                (J::Assoc(_), _) | (_, J::Assoc(_)) | (J::List(_), _) | (_, J::List(_)) => {
                    self.acc_if(self.all, (key.clone(), val_c.clone()), acc)
                }
                _ if yojson_equal(val_c, val_p) => {
                    self.acc_if(self.all, (key.clone(), val_c.clone()), acc)
                }
                _ => {
                    // Try numeric diff
                    match (yojson_to_int_opt(val_c), yojson_to_int_opt(val_p)) {
                        (Some(c), Some(p)) => cons(
                            (
                                format!("{}{}", key, self.diff_suffix),
                                J::Int(c.wrapping_sub(p)),
                            ),
                            self.acc_if(self.all, (key.clone(), J::Int(c)), acc),
                        ),
                        _ => match (yojson_to_float_opt(val_c), yojson_to_float_opt(val_p)) {
                            (Some(c), Some(p)) => cons(
                                (format!("{}{}", key, self.diff_suffix), J::Float(c - p)),
                                self.acc_if(self.all, (key.clone(), J::Float(c)), acc),
                            ),
                            _ => cons(
                                (key.clone(), val_c.clone()),
                                cons(
                                    (format!("{}{}", key, self.prev_suffix), val_p.clone()),
                                    acc,
                                ),
                            ),
                        },
                    }
                }
            }
        }
    }

    T(Diff {
        all,
        prev_suffix,
        diff_suffix,
    }
    .diff(telemetry.0.clone(), prev.0.clone()))
}

/// [merge t1 t2] appends two telemetries, for instance [merge {a->1,b->true}
/// {c->2}] will produce [{a->1,b->true,c->2}]. No matching is done: if an
/// item with the same [key] appears in both [t1] and [t2] then it will be
/// listed twice in the output, similar to if you'd done [t |> int_ ~key
/// ~value |> int_ ~key ~value] twice using the same key. (so don't do it!)
pub fn merge(telemetry1: T, telemetry2: T) -> T {
    // `telemetry2 @ telemetry1`
    let mut l = telemetry2.0;
    l.extend(telemetry1.0);
    T(l)
}

fn add_lists(telemetry1: Vec<KeyValuePair>, telemetry2: Vec<KeyValuePair>) -> Vec<KeyValuePair> {
    let telemetry1 = sort(telemetry1);
    let telemetry2 = sort(telemetry2);
    add_already_sorted(&telemetry1, &telemetry2, vec![])
}

fn add_already_sorted<'a>(
    mut telemetry1: &'a [KeyValuePair],
    mut telemetry2: &'a [KeyValuePair],
    mut acc: Vec<KeyValuePair>,
) -> Vec<KeyValuePair> {
    use std::cmp::Ordering;
    loop {
        match (telemetry1, telemetry2) {
            ([], []) => return acc,
            ([t, telemetry @ ..], []) | ([], [t, telemetry @ ..]) => {
                acc = add_single(t, acc);
                telemetry1 = telemetry;
                telemetry2 = &[];
            }
            ([t1, tl1 @ ..], [t2, ..]) if compare(t1, t2) == Ordering::Less => {
                acc = add_single(t1, acc);
                telemetry1 = tl1;
            }
            ([t1, ..], [t2, tl2 @ ..]) if compare(t1, t2) == Ordering::Greater => {
                acc = add_single(t2, acc);
                telemetry2 = tl2;
            }
            ([t1, tl1 @ ..], [t2, tl2 @ ..]) => {
                acc = add_elems(t1, t2, acc);
                telemetry1 = tl1;
                telemetry2 = tl2;
            }
        }
    }
}

fn add_single((key, value): &KeyValuePair, acc: Vec<KeyValuePair>) -> Vec<KeyValuePair> {
    match value {
        yojson::T::Int(_) | yojson::T::Float(_) => cons((key.clone(), value.clone()), acc),
        yojson::T::Assoc(elems) => {
            let elems = add_lists(elems.clone(), vec![]);
            if !elems.is_empty() {
                cons((key.clone(), yojson::T::Assoc(elems)), acc)
            } else {
                acc
            }
        }
        _ => acc,
    }
}

fn add_elems(
    (key, val1): &KeyValuePair,
    (_key, val2): &KeyValuePair,
    acc: Vec<KeyValuePair>,
) -> Vec<KeyValuePair> {
    use yojson::T as J;
    match (val1, val2) {
        (J::Int(n1), J::Int(n2)) => cons((key.clone(), J::Int(n1.wrapping_add(*n2))), acc),
        (J::Float(n1), J::Float(n2)) => cons((key.clone(), J::Float(n1 + n2)), acc),
        (J::Int(n1), J::Float(n2)) => cons((key.clone(), J::Float(*n1 as f64 + n2)), acc),
        (J::Float(n1), J::Int(n2)) => cons((key.clone(), J::Float(n1 + *n2 as f64)), acc),
        (J::Assoc(elems1), J::Assoc(elems2)) => {
            let elems = add_lists(elems1.clone(), elems2.clone());
            if !elems.is_empty() {
                cons((key.clone(), J::Assoc(elems)), acc)
            } else {
                acc
            }
        }
        _ => acc,
    }
}

/// [add t1 t2] does a key-by-key numeric add, for instance [add {a->1,b->1}
/// {a->3}] will produce [{a->4,b->1}]. It retains only numerics (int, float)
/// and hierarchical objects that contain numerics. It doesn't retain int
/// lists.
pub fn add(telemetry1: &T, telemetry2: &T) -> T {
    T(add_lists(telemetry1.0.clone(), telemetry2.0.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn show(t: &T) -> String {
        to_string(None, t)
    }

    #[test]
    fn builders() {
        let t = create();
        assert_eq!(show(&t), "{}");
        let t = int_("count", 3, t);
        let t = string_(None, "desc", "a \"b\"", t);
        let t = string_(Some(2), "short", "abcdef", t);
        let t = bool_("ok", true, t);
        let t = float_("f", 1.5, t);
        let t = float_("nan", f64::NAN, t);
        let t = int_list(Some(2), "l", &[1, 2, 3], t);
        let t = int_list(None, "l2", &[1, 2, 3], t);
        let t = string_opt(None, "none", None, t);
        let t = int_opt("i", Some(-1), t);
        let t = json("j", yojson::T::List(vec![yojson::T::Null]), t);
        // In the order they were added.
        assert_eq!(
            show(&t),
            r#"{"count":3,"desc":"a \"b\"","short":"ab","ok":true,"f":1.5,"nan":null,"l":[1,2],"l2":[1,2,3],"none":null,"i":-1,"j":[null]}"#
        );
        // The same key twice is two entries.
        assert_eq!(show(&int_("a", 2, int_("a", 1, create()))), r#"{"a":1,"a":2}"#);
    }

    #[test]
    fn objects() {
        let inner = int_("b", 2, int_("a", 1, create()));
        let t = object_("o", inner.clone(), int_("x", 0, create()));
        assert_eq!(show(&t), r#"{"x":0,"o":{"a":1,"b":2}}"#);
        let t = object_list("l", &[inner.clone(), create()], create());
        assert_eq!(show(&t), r#"{"l":[{"a":1,"b":2},{}]}"#);
        let t = object_opt("o", None, create());
        assert_eq!(show(&t), r#"{"o":null}"#);
        assert_eq!(
            show(&merge(inner, int_("c", 3, create()))),
            r#"{"a":1,"b":2,"c":3}"#
        );
    }

    #[test]
    fn durations() {
        let t = duration(None, 1.0, Some(3.5), create());
        assert_eq!(show(&t), r#"{"duration":2500}"#);
        let t = duration(Some("d"), 0., Some(0.0019), create());
        assert_eq!(show(&t), r#"{"d":1}"#);
    }

    #[test]
    fn added_durations_and_string_lists() {
        let t = int_("sync_watcher", 5, create());
        let t = int_("x", 1, t);
        let t = add_duration(Some("sync_watcher"), 1.0, Some(1.5), t);
        assert_eq!(show(&t), r#"{"x":1,"sync_watcher":505}"#);
        let t = string_list(
            Some(2),
            None,
            "l",
            &["a".to_string(), "b".to_string(), "c".to_string()],
            create(),
        );
        assert_eq!(show(&t), r#"{"l":["a","b"]}"#);
    }

    #[test]
    fn int_literals() {
        assert_eq!(int_of_string_opt("12"), Some(12));
        assert_eq!(int_of_string_opt("-12"), Some(-12));
        assert_eq!(int_of_string_opt("+12"), Some(12));
        assert_eq!(int_of_string_opt("1_000"), Some(1000));
        assert_eq!(int_of_string_opt("0x1f"), Some(31));
        assert_eq!(int_of_string_opt("0b101"), Some(5));
        assert_eq!(int_of_string_opt("0o17"), Some(15));
        assert_eq!(int_of_string_opt(""), None);
        assert_eq!(int_of_string_opt("_1"), None);
        assert_eq!(int_of_string_opt("1.5"), None);
        assert_eq!(int_of_string_opt("abc"), None);
        // `max_int` and `min_int` of OCaml.
        assert_eq!(
            int_of_string_opt("4611686018427387903"),
            Some(4611686018427387903)
        );
        assert_eq!(int_of_string_opt("4611686018427387904"), None);
        assert_eq!(
            int_of_string_opt("-4611686018427387904"),
            Some(-4611686018427387904)
        );
        assert_eq!(int_of_string_opt("123456789012345678901234567890"), None);
    }

    #[test]
    fn add_numbers() {
        // [add {a->1,b->1} {a->3}] will produce [{a->4,b->1}]
        let t1 = int_("b", 1, int_("a", 1, create()));
        let t2 = int_("a", 3, create());
        assert_eq!(show(&add(&t1, &t2)), r#"{"a":4,"b":1}"#);
        // Only numbers, and the objects that have numbers.
        let o1 = string_(None, "s", "x", int_("n", 1, create()));
        let o2 = float_("n", 0.5, create());
        let t1 = object_("o", o1, bool_("flag", true, int_("z", 1, create())));
        let t2 = object_("o", o2, string_(None, "z", "not a number", create()));
        assert_eq!(show(&add(&t1, &t2)), r#"{"o":{"n":1.5}}"#);
        let empty = object_("o", string_(None, "s", "x", create()), create());
        assert_eq!(show(&add(&empty, &create())), "{}");
        assert_eq!(
            show(&add(&float_("f", 1.5, create()), &int_("f", 2, create()))),
            r#"{"f":3.5}"#
        );
    }

    #[test]
    fn diff_values() {
        let current = string_(None, "s", "new", int_("b", 5, int_("a", 1, create())));
        let prev = string_(None, "s", "old", int_("b", 2, int_("a", 1, create())));
        // Without `all`: what changed.
        assert_eq!(
            show(&diff(false, None, &current, &prev)),
            r#"{"b__diff":3,"s__prev":"old","s":"new"}"#
        );
        // With `all`: everything, and the differences.
        assert_eq!(
            show(&diff(true, None, &current, &prev)),
            r#"{"a":1,"b":5,"b__diff":3,"s__prev":"old","s":"new"}"#
        );
        assert_eq!(
            show(&diff(false, Some(false), &current, &prev)),
            r#"{"b":3,"s":"old","s":"new"}"#
        );
        // Nested objects, and floats.
        let current = object_("o", float_("f", 2.5, int_("same", 1, create())), create());
        let prev = object_("o", float_("f", 1.0, int_("same", 1, create())), create());
        assert_eq!(
            show(&diff(false, None, &current, &prev)),
            r#"{"o":{"f__diff":1.5}}"#
        );
        // An object without differences is not there, unless `all`.
        assert_eq!(show(&diff(false, None, &current, &current)), "{}");
        // (A nested object is the list as `diff` builds it: last key first.)
        assert_eq!(
            show(&diff(true, None, &current, &current)),
            r#"{"o":{"same":1,"f":2.5}}"#
        );
    }

    #[test]
    fn diff_structure() {
        let a = int_("a", 1, create());
        let ab = int_("b", 2, int_("a", 1, create()));
        // A key that is only in the current telemetry, or only in the
        // previous one, shows with `all`.
        assert_eq!(
            show(&diff(true, None, &ab, &a)),
            r#"{"a":1,"b__prev":null,"b":2}"#
        );
        assert_eq!(
            show(&diff(true, None, &a, &ab)),
            r#"{"a":1,"b__prev":2,"b":null}"#
        );
        assert_eq!(show(&diff(false, None, &ab, &a)), "{}");
        assert_eq!(show(&diff(false, None, &a, &ab)), "{}");
    }
}
