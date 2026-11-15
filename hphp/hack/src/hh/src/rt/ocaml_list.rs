// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the list functions of OCaml's `Stdlib` (`stdlib/list.ml`) and of
//! `Base` (`Core.List`) whose
//! result depends on how they are written, so that the ported modules get the
//! same result as the OCaml whatever comparison they give. See `hh/PORTING.md`,
//! "The server layer".
//!
//! [`stable_sort`] is the merge sort of `stdlib/list.ml`, step by step: with a
//! comparison that is not a total order (the diagnostic formatters have one),
//! the order of the result is the OCaml order. Rust's own sorts may give
//! another order then, or panic.
//!
//! An OCaml list is a `Vec` here, its head at index 0.

use std::cmp::Ordering;

/// `cmp h1 h2 <= 0`
fn le<T>(cmp: &impl Fn(&T, &T) -> Ordering, x: &T, y: &T) -> bool {
    cmp(x, y) != Ordering::Greater
}

/// `cmp h1 h2 > 0`
fn gt<T>(cmp: &impl Fn(&T, &T) -> Ordering, x: &T, y: &T) -> bool {
    cmp(x, y) == Ordering::Greater
}

/// `List.stable_sort cmp l` (= `List.sort`, `List.fast_sort`; `Base`'s
/// `List.sort` and `List.stable_sort` are these).
pub fn stable_sort<T>(l: Vec<T>, cmp: impl Fn(&T, &T) -> Ordering) -> Vec<T> {
    let len = l.len();
    if len < 2 {
        l
    } else {
        let mut l = l.into_iter();
        sort(&cmp, len, &mut l)
    }
}

/// `rev_append l accu` where `accu` is built by pushing (its OCaml head is
/// its last element).
fn rev_append_onto<T>(l: impl Iterator<Item = T>, accu: &mut Vec<T>) {
    for x in l {
        accu.push(x)
    }
}

/// `rev_merge l1 l2 []`: `l1` and `l2` sorted in increasing order, the result
/// in decreasing order.
fn rev_merge<T>(cmp: &impl Fn(&T, &T) -> Ordering, l1: Vec<T>, l2: Vec<T>) -> Vec<T> {
    // The OCaml `accu`, its head last.
    let mut accu = Vec::with_capacity(l1.len() + l2.len());
    let mut l1 = l1.into_iter().peekable();
    let mut l2 = l2.into_iter().peekable();
    loop {
        match (l1.peek(), l2.peek()) {
            (None, _) => {
                rev_append_onto(l2, &mut accu);
                break;
            }
            (_, None) => {
                rev_append_onto(l1, &mut accu);
                break;
            }
            (Some(h1), Some(h2)) => {
                if le(cmp, h1, h2) {
                    accu.push(l1.next().unwrap())
                } else {
                    accu.push(l2.next().unwrap())
                }
            }
        }
    }
    accu.reverse();
    accu
}

/// `rev_merge_rev l1 l2 []`: `l1` and `l2` sorted in decreasing order, the
/// result in increasing order.
fn rev_merge_rev<T>(cmp: &impl Fn(&T, &T) -> Ordering, l1: Vec<T>, l2: Vec<T>) -> Vec<T> {
    let mut accu = Vec::with_capacity(l1.len() + l2.len());
    let mut l1 = l1.into_iter().peekable();
    let mut l2 = l2.into_iter().peekable();
    loop {
        match (l1.peek(), l2.peek()) {
            (None, _) => {
                rev_append_onto(l2, &mut accu);
                break;
            }
            (_, None) => {
                rev_append_onto(l1, &mut accu);
                break;
            }
            (Some(h1), Some(h2)) => {
                if gt(cmp, h1, h2) {
                    accu.push(l1.next().unwrap())
                } else {
                    accu.push(l2.next().unwrap())
                }
            }
        }
    }
    accu.reverse();
    accu
}

/// `sort n l`: the first `n` elements of `l` (consumed), in increasing order.
fn sort<T>(cmp: &impl Fn(&T, &T) -> Ordering, n: usize, l: &mut impl Iterator<Item = T>) -> Vec<T> {
    match n {
        2 => {
            let x1 = l.next().unwrap();
            let x2 = l.next().unwrap();
            if le(cmp, &x1, &x2) {
                vec![x1, x2]
            } else {
                vec![x2, x1]
            }
        }
        3 => {
            let x1 = l.next().unwrap();
            let x2 = l.next().unwrap();
            let x3 = l.next().unwrap();
            if le(cmp, &x1, &x2) {
                if le(cmp, &x2, &x3) {
                    vec![x1, x2, x3]
                } else if le(cmp, &x1, &x3) {
                    vec![x1, x3, x2]
                } else {
                    vec![x3, x1, x2]
                }
            } else if le(cmp, &x1, &x3) {
                vec![x2, x1, x3]
            } else if le(cmp, &x2, &x3) {
                vec![x2, x3, x1]
            } else {
                vec![x3, x2, x1]
            }
        }
        n => {
            let n1 = n >> 1;
            let n2 = n - n1;
            let s1 = rev_sort(cmp, n1, l);
            let s2 = rev_sort(cmp, n2, l);
            rev_merge_rev(cmp, s1, s2)
        }
    }
}

/// `rev_sort n l`: the first `n` elements of `l` (consumed), in decreasing
/// order.
fn rev_sort<T>(
    cmp: &impl Fn(&T, &T) -> Ordering,
    n: usize,
    l: &mut impl Iterator<Item = T>,
) -> Vec<T> {
    match n {
        2 => {
            let x1 = l.next().unwrap();
            let x2 = l.next().unwrap();
            if gt(cmp, &x1, &x2) {
                vec![x1, x2]
            } else {
                vec![x2, x1]
            }
        }
        3 => {
            let x1 = l.next().unwrap();
            let x2 = l.next().unwrap();
            let x3 = l.next().unwrap();
            if gt(cmp, &x1, &x2) {
                if gt(cmp, &x2, &x3) {
                    vec![x1, x2, x3]
                } else if gt(cmp, &x1, &x3) {
                    vec![x1, x3, x2]
                } else {
                    vec![x3, x1, x2]
                }
            } else if gt(cmp, &x1, &x3) {
                vec![x2, x1, x3]
            } else if gt(cmp, &x2, &x3) {
                vec![x2, x3, x1]
            } else {
                vec![x3, x2, x1]
            }
        }
        n => {
            let n1 = n >> 1;
            let n2 = n - n1;
            let s1 = sort(cmp, n1, l);
            let s2 = sort(cmp, n2, l);
            rev_merge(cmp, s1, s2)
        }
    }
}

/// `Base.List.remove_consecutive_duplicates ~which_to_keep:`Last ~equal`
/// (`Last` is `Base`'s default): of consecutive equal elements, the last one
/// is kept.
pub fn remove_consecutive_duplicates<T>(l: Vec<T>, equal: impl Fn(&T, &T) -> bool) -> Vec<T> {
    let mut res: Vec<T> = Vec::with_capacity(l.len());
    for hd in l {
        match res.last_mut() {
            // `equal hd to_keep`, then `to_keep = hd`
            Some(to_keep) if equal(&hd, to_keep) => *to_keep = hd,
            _ => res.push(hd),
        }
    }
    res
}

/// `Base.List.dedup_and_sort ~compare l`: sorted (stably), then of the
/// elements that compare equal only the last is kept.
pub fn dedup_and_sort<T>(l: Vec<T>, compare: impl Fn(&T, &T) -> Ordering) -> Vec<T> {
    if l.len() <= 1 {
        // `[] | [ _ ] -> list`
        l
    } else {
        let sorted = stable_sort(l, &compare);
        remove_consecutive_duplicates(sorted, |x, y| compare(x, y) == Ordering::Equal)
    }
}

/// `Base.List.group l ~break`: the consecutive runs of `l`, a new run
/// starting before `x` whenever `break prev x` (`prev` is the element just
/// before `x`).
pub fn group<T>(l: Vec<T>, break_: impl Fn(&T, &T) -> bool) -> Vec<Vec<T>> {
    let mut groups: Vec<Vec<T>> = vec![];
    for x in l {
        match groups.last_mut() {
            None => groups.push(vec![x]),
            Some(current_group) => {
                if break_(current_group.last().unwrap(), &x) {
                    groups.push(vec![x])
                } else {
                    current_group.push(x)
                }
            }
        }
    }
    groups
}

/// `List.compare`
pub fn compare<T>(mut cmp: impl FnMut(&T, &T) -> Ordering, l1: &[T], l2: &[T]) -> Ordering {
    let mut i1 = l1.iter();
    let mut i2 = l2.iter();
    loop {
        match (i1.next(), i2.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(x), Some(y)) => {
                let n = cmp(x, y);
                if n != Ordering::Equal {
                    return n;
                }
            }
        }
    }
}
/// `List.max_elt ~compare` (Core): the first of the greatest elements.
pub fn max_elt<A>(l: Vec<A>, compare: impl Fn(&A, &A) -> Ordering) -> Option<A> {
    let mut max: Option<A> = None;
    for elt in l {
        max = match max {
            None => Some(elt),
            Some(m) => {
                if compare(&m, &elt) == Ordering::Less {
                    Some(elt)
                } else {
                    Some(m)
                }
            }
        };
    }
    max
}
/// `List.zip_exn l1 l2` (Base): raises `Invalid_argument` when the lengths
/// differ.
pub fn zip_exn<A, B>(l1: Vec<A>, l2: Vec<B>) -> Vec<(A, B)> {
    if l1.len() != l2.len() {
        panic!(
            "Invalid_argument(\"length mismatch in zip_exn: {} <> {}\")",
            l1.len(),
            l2.len()
        )
    }
    l1.into_iter().zip(l2).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn max_elt_keeps_the_first_of_the_greatest() {
        let l = vec![(1, 'a'), (3, 'b'), (2, 'c'), (3, 'd')];
        assert_eq!(max_elt(l, |a, b| a.0.cmp(&b.0)), Some((3, 'b')));
        assert_eq!(
            max_elt(Vec::<(i32, char)>::new(), |a, b| a.0.cmp(&b.0)),
            None
        );
    }

    #[test]
    #[should_panic(expected = "Invalid_argument(\"length mismatch in zip_exn: 1 <> 2\")")]
    fn zip_exn_panics_on_length_mismatch() {
        zip_exn(vec![1], vec![1, 2]);
    }

    /// A straightforward port of the OCaml (on lists), to compare with.
    fn ocaml_stable_sort(
        l: &[(i32, i32)],
        cmp: &dyn Fn(&(i32, i32), &(i32, i32)) -> i32,
    ) -> Vec<(i32, i32)> {
        fn rev_append(l1: &[(i32, i32)], mut accu: Vec<(i32, i32)>) -> Vec<(i32, i32)> {
            // `accu` with its head first.
            for x in l1 {
                accu.insert(0, *x)
            }
            accu
        }
        type C<'a> = &'a dyn Fn(&(i32, i32), &(i32, i32)) -> i32;
        fn rev_merge(
            c: C<'_>,
            l1: &[(i32, i32)],
            l2: &[(i32, i32)],
            accu: Vec<(i32, i32)>,
        ) -> Vec<(i32, i32)> {
            match (l1, l2) {
                ([], l2) => rev_append(l2, accu),
                (l1, []) => rev_append(l1, accu),
                ([h1, t1 @ ..], [h2, t2 @ ..]) => {
                    let mut accu = accu;
                    if c(h1, h2) <= 0 {
                        accu.insert(0, *h1);
                        rev_merge(c, t1, l2, accu)
                    } else {
                        accu.insert(0, *h2);
                        rev_merge(c, l1, t2, accu)
                    }
                }
            }
        }
        fn rev_merge_rev(
            c: C<'_>,
            l1: &[(i32, i32)],
            l2: &[(i32, i32)],
            accu: Vec<(i32, i32)>,
        ) -> Vec<(i32, i32)> {
            match (l1, l2) {
                ([], l2) => rev_append(l2, accu),
                (l1, []) => rev_append(l1, accu),
                ([h1, t1 @ ..], [h2, t2 @ ..]) => {
                    let mut accu = accu;
                    if c(h1, h2) > 0 {
                        accu.insert(0, *h1);
                        rev_merge_rev(c, t1, l2, accu)
                    } else {
                        accu.insert(0, *h2);
                        rev_merge_rev(c, l1, t2, accu)
                    }
                }
            }
        }
        fn sort<'l>(
            c: C<'_>,
            n: usize,
            l: &'l [(i32, i32)],
        ) -> (Vec<(i32, i32)>, &'l [(i32, i32)]) {
            match (n, l) {
                (2, [x1, x2, tl @ ..]) => (
                    if c(x1, x2) <= 0 {
                        vec![*x1, *x2]
                    } else {
                        vec![*x2, *x1]
                    },
                    tl,
                ),
                (3, [x1, x2, x3, tl @ ..]) => {
                    let (x1, x2, x3) = (*x1, *x2, *x3);
                    let s = if c(&x1, &x2) <= 0 {
                        if c(&x2, &x3) <= 0 {
                            vec![x1, x2, x3]
                        } else if c(&x1, &x3) <= 0 {
                            vec![x1, x3, x2]
                        } else {
                            vec![x3, x1, x2]
                        }
                    } else if c(&x1, &x3) <= 0 {
                        vec![x2, x1, x3]
                    } else if c(&x2, &x3) <= 0 {
                        vec![x2, x3, x1]
                    } else {
                        vec![x3, x2, x1]
                    };
                    (s, tl)
                }
                (n, l) => {
                    let n1 = n >> 1;
                    let n2 = n - n1;
                    let (s1, l2) = rev_sort(c, n1, l);
                    let (s2, tl) = rev_sort(c, n2, l2);
                    (rev_merge_rev(c, &s1, &s2, vec![]), tl)
                }
            }
        }
        fn rev_sort<'l>(
            c: C<'_>,
            n: usize,
            l: &'l [(i32, i32)],
        ) -> (Vec<(i32, i32)>, &'l [(i32, i32)]) {
            match (n, l) {
                (2, [x1, x2, tl @ ..]) => (
                    if c(x1, x2) > 0 {
                        vec![*x1, *x2]
                    } else {
                        vec![*x2, *x1]
                    },
                    tl,
                ),
                (3, [x1, x2, x3, tl @ ..]) => {
                    let (x1, x2, x3) = (*x1, *x2, *x3);
                    let s = if c(&x1, &x2) > 0 {
                        if c(&x2, &x3) > 0 {
                            vec![x1, x2, x3]
                        } else if c(&x1, &x3) > 0 {
                            vec![x1, x3, x2]
                        } else {
                            vec![x3, x1, x2]
                        }
                    } else if c(&x1, &x3) > 0 {
                        vec![x2, x1, x3]
                    } else if c(&x2, &x3) > 0 {
                        vec![x2, x3, x1]
                    } else {
                        vec![x3, x2, x1]
                    };
                    (s, tl)
                }
                (n, l) => {
                    let n1 = n >> 1;
                    let n2 = n - n1;
                    let (s1, l2) = sort(c, n1, l);
                    let (s2, tl) = sort(c, n2, l2);
                    (rev_merge(c, &s1, &s2, vec![]), tl)
                }
            }
        }
        if l.len() < 2 {
            l.to_vec()
        } else {
            sort(cmp, l.len(), l).0
        }
    }

    /// A deterministic pseudo-random sequence.
    fn lcg(seed: &mut u64) -> i32 {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((*seed >> 33) % 7) as i32
    }

    #[test]
    fn stable_sort_is_the_ocaml_sort() {
        // The comparison of `Contextual_diagnostic_formatter.format_error`:
        // by line within a file, and 0 between files. It is not an order.
        let weird =
            |a: &(i32, i32), b: &(i32, i32)| -> i32 { if a.0 == b.0 { a.1 - b.1 } else { 0 } };
        let total = |a: &(i32, i32), b: &(i32, i32)| -> i32 { a.1 - b.1 };
        let to_ord = |c: i32| c.cmp(&0);
        let mut seed = 42;
        for len in 0..40 {
            for _ in 0..20 {
                let l: Vec<(i32, i32)> = (0..len)
                    .map(|_| (lcg(&mut seed) % 3, lcg(&mut seed)))
                    .collect();
                for cmp in [&weird as &dyn Fn(&(i32, i32), &(i32, i32)) -> i32, &total] {
                    let expected = ocaml_stable_sort(&l, cmp);
                    let actual = stable_sort(l.clone(), |a, b| to_ord(cmp(a, b)));
                    assert_eq!(actual, expected, "{l:?}");
                }
            }
        }
    }

    #[test]
    fn stable() {
        let l = vec![(1, 'a'), (0, 'b'), (1, 'c'), (0, 'd'), (2, 'e'), (0, 'f')];
        assert_eq!(
            stable_sort(l, |a, b| a.0.cmp(&b.0)),
            vec![(0, 'b'), (0, 'd'), (0, 'f'), (1, 'a'), (1, 'c'), (2, 'e')]
        );
    }

    #[test]
    fn dedup_keeps_the_last() {
        let l = vec![(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd')];
        assert_eq!(
            dedup_and_sort(l, |a, b| a.0.cmp(&b.0)),
            vec![(1, 'd'), (2, 'c')]
        );
        assert_eq!(
            dedup_and_sort(vec![(1, 'a')], |a: &(i32, char), b| a.0.cmp(&b.0)),
            vec![(1, 'a')]
        );
        assert_eq!(
            dedup_and_sort(Vec::<i32>::new(), |a, b| a.cmp(b)),
            Vec::<i32>::new()
        );
    }

    #[test]
    fn group_breaks_between_neighbours() {
        assert_eq!(
            group(vec![1, 2, 4, 5, 7], |prev, x| x - prev > 1),
            vec![vec![1, 2], vec![4, 5], vec![7]]
        );
        assert_eq!(
            group(Vec::<i32>::new(), |_, _| true),
            Vec::<Vec<i32>>::new()
        );
    }
}
