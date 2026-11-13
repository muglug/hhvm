// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_fake_members.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::local_id;
use oxidized::local_id::LocalId;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::typing_reason::Blame;
use oxidized::typing_reason::BlameSource;

use crate::typing_log_value;

/// A set that treats blame as metadata.
///
/// In OCaml this is `Stdlib.Set.Make (S)` where `S.compare` only looks at the
/// local id, with a few functions redefined. Two elements with the same id and
/// different blames are equal for the set, so which of the two blames a
/// `union` keeps depends on the shapes of the balanced trees (`Set.union`
/// keeps the element of the taller tree). The blame ends up in error messages,
/// so the trees and the algorithms of the standard library's `set.ml` are
/// reproduced here (in `tree`) rather than replaced by another ordered set.
pub mod blame_set {
    use std::rc::Rc;

    use super::Blame;
    use super::LocalId;

    /// `S.t`
    pub type Elt = (LocalId, Blame);

    /// `Set.Make (S)`: the functions of `set.ml` that `BlameSet` uses, with
    /// the same names, on the same trees.
    mod tree {
        use std::cmp::Ordering;
        use std::rc::Rc;

        use super::Elt;

        /// `S.compare`
        pub fn compare(a: &Elt, b: &Elt) -> Ordering {
            a.0.cmp(&b.0)
        }

        pub struct Node {
            pub l: Tree,
            pub v: Rc<Elt>,
            pub r: Tree,
            pub h: usize,
        }

        /// A balanced binary tree: the heights of the children differ by at
        /// most 2.
        #[derive(Clone)]
        pub enum Tree {
            Empty,
            Node(Rc<Node>),
        }
        use Tree::Empty;

        /// OCaml's `==` on trees.
        fn phys_equal(a: &Tree, b: &Tree) -> bool {
            match (a, b) {
                (Empty, Empty) => true,
                (Tree::Node(a), Tree::Node(b)) => Rc::ptr_eq(a, b),
                _ => false,
            }
        }

        fn node(l: Tree, v: Rc<Elt>, r: Tree, h: usize) -> Tree {
            Tree::Node(Rc::new(Node { l, v, r, h }))
        }

        fn height(t: &Tree) -> usize {
            match t {
                Empty => 0,
                Tree::Node(n) => n.h,
            }
        }

        fn create(l: Tree, v: Rc<Elt>, r: Tree) -> Tree {
            let hl = height(&l);
            let hr = height(&r);
            node(l, v, r, if hl >= hr { hl + 1 } else { hr + 1 })
        }

        fn bal(l: Tree, v: Rc<Elt>, r: Tree) -> Tree {
            let hl = height(&l);
            let hr = height(&r);
            if hl > hr + 2 {
                match &l {
                    Empty => panic!("Set.bal"),
                    Tree::Node(ln) => {
                        if height(&ln.l) >= height(&ln.r) {
                            create(ln.l.clone(), ln.v.clone(), create(ln.r.clone(), v, r))
                        } else {
                            match &ln.r {
                                Empty => panic!("Set.bal"),
                                Tree::Node(lrn) => create(
                                    create(ln.l.clone(), ln.v.clone(), lrn.l.clone()),
                                    lrn.v.clone(),
                                    create(lrn.r.clone(), v, r),
                                ),
                            }
                        }
                    }
                }
            } else if hr > hl + 2 {
                match &r {
                    Empty => panic!("Set.bal"),
                    Tree::Node(rn) => {
                        if height(&rn.r) >= height(&rn.l) {
                            create(create(l, v, rn.l.clone()), rn.v.clone(), rn.r.clone())
                        } else {
                            match &rn.l {
                                Empty => panic!("Set.bal"),
                                Tree::Node(rln) => create(
                                    create(l, v, rln.l.clone()),
                                    rln.v.clone(),
                                    create(rln.r.clone(), rn.v.clone(), rn.r.clone()),
                                ),
                            }
                        }
                    }
                }
            } else {
                node(l, v, r, if hl >= hr { hl + 1 } else { hr + 1 })
            }
        }

        pub fn add(x: Rc<Elt>, t: &Tree) -> Tree {
            match t {
                Empty => node(Empty, x, Empty, 1),
                Tree::Node(n) => match compare(&x, &n.v) {
                    Ordering::Equal => t.clone(),
                    Ordering::Less => {
                        let ll = add(x, &n.l);
                        if phys_equal(&n.l, &ll) {
                            t.clone()
                        } else {
                            bal(ll, n.v.clone(), n.r.clone())
                        }
                    }
                    Ordering::Greater => {
                        let rr = add(x, &n.r);
                        if phys_equal(&n.r, &rr) {
                            t.clone()
                        } else {
                            bal(n.l.clone(), n.v.clone(), rr)
                        }
                    }
                },
            }
        }

        fn singleton(x: Rc<Elt>) -> Tree {
            node(Empty, x, Empty, 1)
        }

        fn add_min_element(x: Rc<Elt>, t: &Tree) -> Tree {
            match t {
                Empty => singleton(x),
                Tree::Node(n) => bal(add_min_element(x, &n.l), n.v.clone(), n.r.clone()),
            }
        }

        fn add_max_element(x: Rc<Elt>, t: &Tree) -> Tree {
            match t {
                Empty => singleton(x),
                Tree::Node(n) => bal(n.l.clone(), n.v.clone(), add_max_element(x, &n.r)),
            }
        }

        fn join(l: &Tree, v: Rc<Elt>, r: &Tree) -> Tree {
            match (l, r) {
                (Empty, _) => add_min_element(v, r),
                (_, Empty) => add_max_element(v, l),
                (Tree::Node(ln), Tree::Node(rn)) => {
                    if ln.h > rn.h + 2 {
                        bal(ln.l.clone(), ln.v.clone(), join(&ln.r, v, r))
                    } else if rn.h > ln.h + 2 {
                        bal(join(l, v, &rn.l), rn.v.clone(), rn.r.clone())
                    } else {
                        create(l.clone(), v, r.clone())
                    }
                }
            }
        }

        /// Raises `Not_found` on the empty set in OCaml; it is only called on
        /// trees that are not empty.
        fn min_elt(t: &Tree) -> Rc<Elt> {
            match t {
                Empty => panic!("Not_found"),
                Tree::Node(n) => match &n.l {
                    Empty => n.v.clone(),
                    l => min_elt(l),
                },
            }
        }

        pub fn min_elt_opt(t: &Tree) -> Option<Rc<Elt>> {
            match t {
                Empty => None,
                Tree::Node(n) => match &n.l {
                    Empty => Some(n.v.clone()),
                    l => min_elt_opt(l),
                },
            }
        }

        fn max_elt(t: &Tree) -> Rc<Elt> {
            match t {
                Empty => panic!("Not_found"),
                Tree::Node(n) => match &n.r {
                    Empty => n.v.clone(),
                    r => max_elt(r),
                },
            }
        }

        fn remove_min_elt(t: &Tree) -> Tree {
            match t {
                Empty => panic!("Set.remove_min_elt"),
                Tree::Node(n) => match &n.l {
                    Empty => n.r.clone(),
                    l => bal(remove_min_elt(l), n.v.clone(), n.r.clone()),
                },
            }
        }

        fn concat(t1: &Tree, t2: &Tree) -> Tree {
            match (t1, t2) {
                (Empty, t) => t.clone(),
                (t, Empty) => t.clone(),
                (_, _) => join(t1, min_elt(t2), &remove_min_elt(t2)),
            }
        }

        fn split(x: &Elt, t: &Tree) -> (Tree, bool, Tree) {
            match t {
                Empty => (Empty, false, Empty),
                Tree::Node(n) => match compare(x, &n.v) {
                    Ordering::Equal => (n.l.clone(), true, n.r.clone()),
                    Ordering::Less => {
                        let (ll, pres, rl) = split(x, &n.l);
                        (ll, pres, join(&rl, n.v.clone(), &n.r))
                    }
                    Ordering::Greater => {
                        let (lr, pres, rr) = split(x, &n.r);
                        (join(&n.l, n.v.clone(), &lr), pres, rr)
                    }
                },
            }
        }

        pub fn is_empty(t: &Tree) -> bool {
            matches!(t, Empty)
        }

        pub fn union(s1: &Tree, s2: &Tree) -> Tree {
            match (s1, s2) {
                (Empty, t2) => t2.clone(),
                (t1, Empty) => t1.clone(),
                (Tree::Node(n1), Tree::Node(n2)) => {
                    if n1.h >= n2.h {
                        if n2.h == 1 {
                            add(n2.v.clone(), s1)
                        } else {
                            let (l2, _, r2) = split(&n1.v, s2);
                            join(&union(&n1.l, &l2), n1.v.clone(), &union(&n1.r, &r2))
                        }
                    } else if n1.h == 1 {
                        add(n1.v.clone(), s2)
                    } else {
                        let (l1, _, r1) = split(&n2.v, s1);
                        join(&union(&l1, &n2.l), n2.v.clone(), &union(&r1, &n2.r))
                    }
                }
            }
        }

        pub fn inter(s1: &Tree, s2: &Tree) -> Tree {
            match (s1, s2) {
                (Empty, _) => Empty,
                (_, Empty) => Empty,
                (Tree::Node(n1), t2) => match split(&n1.v, t2) {
                    (l2, false, r2) => concat(&inter(&n1.l, &l2), &inter(&n1.r, &r2)),
                    (l2, true, r2) => {
                        join(&inter(&n1.l, &l2), n1.v.clone(), &inter(&n1.r, &r2))
                    }
                },
            }
        }

        pub fn diff(s1: &Tree, s2: &Tree) -> Tree {
            match (s1, s2) {
                (Empty, _) => Empty,
                (t1, Empty) => t1.clone(),
                (Tree::Node(n1), t2) => match split(&n1.v, t2) {
                    (l2, false, r2) => join(&diff(&n1.l, &l2), n1.v.clone(), &diff(&n1.r, &r2)),
                    (l2, true, r2) => concat(&diff(&n1.l, &l2), &diff(&n1.r, &r2)),
                },
            }
        }

        pub fn subset(s1: &Tree, s2: &Tree) -> bool {
            match (s1, s2) {
                (Empty, _) => true,
                (_, Empty) => false,
                (Tree::Node(n1), Tree::Node(n2)) => match compare(&n1.v, &n2.v) {
                    Ordering::Equal => subset(&n1.l, &n2.l) && subset(&n1.r, &n2.r),
                    Ordering::Less => {
                        subset(&node(n1.l.clone(), n1.v.clone(), Empty, 0), &n2.l)
                            && subset(&n1.r, s2)
                    }
                    Ordering::Greater => {
                        subset(&node(Empty, n1.v.clone(), n1.r.clone(), 0), &n2.r)
                            && subset(&n1.l, s2)
                    }
                },
            }
        }

        pub fn exists(p: &mut dyn FnMut(&Elt) -> bool, t: &Tree) -> bool {
            match t {
                Empty => false,
                Tree::Node(n) => p(&n.v) || exists(p, &n.l) || exists(p, &n.r),
            }
        }

        pub fn filter(p: &mut dyn FnMut(&Elt) -> bool, t: &Tree) -> Tree {
            match t {
                Empty => Empty,
                Tree::Node(n) => {
                    // call [p] in the expected left-to-right order
                    let l = filter(p, &n.l);
                    let pv = p(&n.v);
                    let r = filter(p, &n.r);
                    if pv {
                        if phys_equal(&n.l, &l) && phys_equal(&n.r, &r) {
                            t.clone()
                        } else {
                            join(&l, n.v.clone(), &r)
                        }
                    } else {
                        concat(&l, &r)
                    }
                }
            }
        }

        pub fn partition(p: &mut dyn FnMut(&Elt) -> bool, t: &Tree) -> (Tree, Tree) {
            match t {
                Empty => (Empty, Empty),
                Tree::Node(n) => {
                    // call [p] in the expected left-to-right order
                    let (lt, lf) = partition(p, &n.l);
                    let pv = p(&n.v);
                    let (rt, rf) = partition(p, &n.r);
                    if pv {
                        (join(&lt, n.v.clone(), &rt), concat(&lf, &rf))
                    } else {
                        (concat(&lt, &rt), join(&lf, n.v.clone(), &rf))
                    }
                }
            }
        }

        pub fn cardinal(t: &Tree) -> usize {
            match t {
                Empty => 0,
                Tree::Node(n) => cardinal(&n.l) + 1 + cardinal(&n.r),
            }
        }

        /// The elements in increasing order (`Set.elements`).
        pub fn elements(accu: &mut Vec<Elt>, t: &Tree) {
            if let Tree::Node(n) = t {
                elements(accu, &n.l);
                accu.push((*n.v).clone());
                elements(accu, &n.r);
            }
        }

        fn try_join(l: &Tree, v: Rc<Elt>, r: &Tree) -> Tree {
            if (is_empty(l) || compare(&max_elt(l), &v) == Ordering::Less)
                && (is_empty(r) || compare(&v, &min_elt(r)) == Ordering::Less)
            {
                join(l, v, r)
            } else {
                union(l, &add(v, r))
            }
        }

        pub fn map(f: &mut dyn FnMut(&Rc<Elt>) -> Rc<Elt>, t: &Tree) -> Tree {
            match t {
                Empty => Empty,
                Tree::Node(n) => {
                    // enforce left-to-right evaluation order
                    let l = map(f, &n.l);
                    let v = f(&n.v);
                    let r = map(f, &n.r);
                    if phys_equal(&n.l, &l) && Rc::ptr_eq(&n.v, &v) && phys_equal(&n.r, &r) {
                        t.clone()
                    } else {
                        try_join(&l, v, &r)
                    }
                }
            }
        }
    }

    use tree::Tree;

    /// `BlameSet.t`
    #[derive(Clone)]
    pub struct T(Tree);

    pub fn empty() -> T {
        T(Tree::Empty)
    }

    pub fn is_empty(s: &T) -> bool {
        tree::is_empty(&s.0)
    }

    pub fn union(s1: &T, s2: &T) -> T {
        T(tree::union(&s1.0, &s2.0))
    }

    pub fn inter(s1: &T, s2: &T) -> T {
        T(tree::inter(&s1.0, &s2.0))
    }

    pub fn diff(s1: &T, s2: &T) -> T {
        T(tree::diff(&s1.0, &s2.0))
    }

    pub fn subset(s1: &T, s2: &T) -> bool {
        tree::subset(&s1.0, &s2.0)
    }

    pub fn exists(mut p: impl FnMut(&Elt) -> bool, s: &T) -> bool {
        tree::exists(&mut p, &s.0)
    }

    pub fn filter(mut p: impl FnMut(&Elt) -> bool, s: &T) -> T {
        T(tree::filter(&mut p, &s.0))
    }

    pub fn partition(mut p: impl FnMut(&Elt) -> bool, s: &T) -> (T, T) {
        let (yes, no) = tree::partition(&mut p, &s.0);
        (T(yes), T(no))
    }

    pub fn map(mut f: impl FnMut(&Elt) -> Elt, s: &T) -> T {
        T(tree::map(&mut |v: &Rc<Elt>| Rc::new(f(v)), &s.0))
    }

    pub fn cardinal(s: &T) -> usize {
        tree::cardinal(&s.0)
    }

    pub fn elements(s: &T) -> Vec<Elt> {
        let mut accu = Vec::new();
        tree::elements(&mut accu, &s.0);
        accu
    }

    pub fn choose_opt(s: &T) -> Option<Elt> {
        tree::min_elt_opt(&s.0).map(|v| (*v).clone())
    }

    pub fn find_opt(lid: &LocalId, blame_set: &T) -> Option<Elt> {
        choose_opt(&filter(|(lid_, _)| lid == lid_, blame_set))
    }

    pub fn member(lid: &LocalId, blame_set: &T) -> bool {
        exists(|(lid_, _)| lid == lid_, blame_set)
    }

    pub fn add(lid: LocalId, blame: Blame, blame_set: &T) -> T {
        T(tree::add(Rc::new((lid, blame)), &blame_set.0))
    }

    pub fn remove(lid: &LocalId, blame_set: &T) -> T {
        filter(|(lid_, _)| lid != lid_, blame_set)
    }

    pub fn attach_blame(blame: &Blame, blame_set: &T) -> T {
        map(|(lid, _)| (lid.clone(), blame.clone()), blame_set)
    }

    /// Checks the invariants of `Set.Make`'s trees: elements strictly
    /// increasing, heights exact, and the heights of siblings differing by at
    /// most 2.
    #[cfg(test)]
    pub(super) fn check_invariants(s: &T) {
        use std::cmp::Ordering;
        fn go(t: &Tree, lo: Option<&Elt>, hi: Option<&Elt>) -> usize {
            match t {
                Tree::Empty => 0,
                Tree::Node(n) => {
                    if let Some(lo) = lo {
                        assert_eq!(tree::compare(lo, &n.v), Ordering::Less);
                    }
                    if let Some(hi) = hi {
                        assert_eq!(tree::compare(&n.v, hi), Ordering::Less);
                    }
                    let hl = go(&n.l, lo, Some(&n.v));
                    let hr = go(&n.r, Some(&n.v), hi);
                    assert_eq!(n.h, 1 + hl.max(hr));
                    assert!(hl <= hr + 2 && hr <= hl + 2);
                    n.h
                }
            }
        }
        go(&s.0, None, None);
    }

    /// The shape of the tree, written `(left name right)` with `.` for the
    /// empty tree.
    #[cfg(test)]
    pub(super) fn shape(s: &T) -> String {
        fn go(t: &Tree, out: &mut String) {
            match t {
                Tree::Empty => out.push('.'),
                Tree::Node(n) => {
                    out.push('(');
                    go(&n.l, out);
                    out.push(' ');
                    out.push_str(&n.v.0.1);
                    out.push(' ');
                    go(&n.r, out);
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        go(&s.0, &mut out);
        out
    }
}

/// A ledger consisting [valid] and [invalid] fake member sets.
///
/// Those in [invalid] have been invalidated by a call, lambda, assignment, or
/// by going out of scope described by the blame attached to the element, but
/// [valid] are fake members that can still be used in typing. For example
///
/// ```text
///   // { valid = []; invalid = [] }
///   if ($x::f is nonnull) { // P0
///     // { valid = [("$x::f", Blame_out_of_scope P0)]; invalid = [] }
///     foo(); // P1
///     // { valid = []; invalid = [("$x::f", Blame_call P1)] }
///     if ($y::g is nonnull) { // P2
///       // { valid = [("$y::g", Blame_out_of_scope P2)]; invalid = [("$x::f", Blame_call P1)] }
///       $f = () ==> ... // P3
///       // { valid = []; invalid = [("$x::f", Blame_lambda P3); ("$y::g", Blame_lambda P2)] }
///       $y::g = 42; // P4
///       // { valid = [("$y::g", Blame_out_of_scope P4)]; invalid = [("$x::f", Blame_call P1)] }
///   } // { valid = []; invalid = [("$y::g", Blame_out_of_scope P4); ("$x::f", Blame_lambda P3)] }
/// ```
#[derive(Clone)]
pub struct T {
    valid: blame_set::T,
    /// Non-empty and disjoint from valid.
    invalid: blame_set::T,
}

/// An empty validation ledger
pub fn empty() -> T {
    T {
        valid: blame_set::empty(),
        invalid: blame_set::empty(),
    }
}

/// Combine validation ledger information at a join point
pub fn join(ledger1: &T, ledger2: &T) -> T {
    let old_valid = blame_set::union(&ledger1.valid, &ledger2.valid);
    let old_invalid = blame_set::union(&ledger1.invalid, &ledger2.invalid);
    let valid = blame_set::inter(&ledger1.valid, &ledger2.valid);
    let invalid = blame_set::union(&old_invalid, &blame_set::diff(&old_valid, &valid));
    T { valid, invalid }
}

/// Does ledger1 entail ledger2?
pub fn sub(ledger1: &T, ledger2: &T) -> bool {
    blame_set::subset(&ledger2.valid, &ledger1.valid)
        && blame_set::subset(&ledger1.invalid, &ledger2.invalid)
}

/// Is this identifier a fake member that is valid?
pub fn is_valid(ledger: &T, lid: &LocalId) -> bool {
    blame_set::member(lid, &ledger.valid)
}

/// Has this identifier been invalidated? If so, return position of
/// the event that is responsible
pub fn is_invalid(ledger: &T, lid: &LocalId) -> Option<Blame> {
    blame_set::find_opt(lid, &ledger.invalid).map(|(_, blame)| blame)
}

fn conditionally_forget(
    predicate: impl FnMut(&blame_set::Elt) -> bool,
    ledger: T,
    blame: Blame,
) -> T {
    let (to_invalidate, valid) = blame_set::partition(predicate, &ledger.valid);
    // Don't allocate if there is nothing to forget
    if blame_set::is_empty(&to_invalidate) {
        ledger
    } else {
        let to_invalidate = blame_set::attach_blame(&blame, &to_invalidate);
        T {
            valid,
            invalid: blame_set::union(&to_invalidate, &ledger.invalid),
        }
    }
}

/// Invalidate all fake members, and remember the position of the event
/// that is responsible
pub fn forget(ledger: T, blame: Blame) -> T {
    conditionally_forget(|_| true, ledger, blame)
}

/// Invalidate fake members that are prefixed by some identifier, and remember
/// the position of the assignment that is responsible
pub fn forget_prefixed(ledger: T, prefix_lid: &LocalId, blame: Blame) -> T {
    // `Local_id.to_string` is `Local_id.get_name`.
    let prefix = format!("{}->", local_id::get_name(prefix_lid));
    let is_prefixed =
        |(fake_id, _blame): &blame_set::Elt| local_id::get_name(fake_id).starts_with(&prefix);
    conditionally_forget(is_prefixed, ledger, blame)
}

/// Invalidate fake members that are suffixed by some identifier, and remember
/// the position of the assignment that is responsible
pub fn forget_suffixed(ledger: T, suffix: &str, blame: Blame) -> T {
    let suffix = format!("->{}", suffix);
    let is_prefixed =
        |(fake_id, _blame): &blame_set::Elt| local_id::get_name(fake_id).ends_with(&suffix);
    conditionally_forget(is_prefixed, ledger, blame)
}

pub fn forget_static_named(ledger: T, member_name: &str, blame: Blame) -> T {
    let suffix = format!("::{}", member_name);
    let is_named =
        |(fake_id, _blame): &blame_set::Elt| local_id::get_name(fake_id).ends_with(&suffix);
    conditionally_forget(is_named, ledger, blame)
}

/// Add a valid fake member access
pub fn add(ledger: T, lid: LocalId, pos: Pos) -> T {
    let reason = Blame::Blame(pos, BlameSource::BSoutOfScope);
    T {
        valid: blame_set::add(lid.clone(), reason, &ledger.valid),
        invalid: blame_set::remove(&lid, &ledger.invalid),
    }
}

fn blame_as_log_value(blame: &Blame) -> typing_log_value::Value {
    let Blame::Blame(p, blame_source) = blame;
    match blame_source {
        BlameSource::BScall => typing_log_value::make_map(vec![(
            "Blame_call".to_string(),
            typing_log_value::pos_as_value(p),
        )]),
        BlameSource::BSlambda => typing_log_value::make_map(vec![(
            "Blame_lambda".to_string(),
            typing_log_value::pos_as_value(p),
        )]),
        BlameSource::BSassignment => typing_log_value::make_map(vec![(
            "Blame_assigment".to_string(),
            typing_log_value::pos_as_value(p),
        )]),
        BlameSource::BSoutOfScope => typing_log_value::make_map(vec![(
            "Blame_out_of_scope".to_string(),
            typing_log_value::pos_as_value(p),
        )]),
    }
}

/// Convert to a value for logging
pub fn as_log_value(ledger: &T) -> typing_log_value::Value {
    let log_blame_set_as_value = |set: &blame_set::T| {
        typing_log_value::make_map(
            blame_set::elements(set)
                .iter()
                .map(|(lid, blame_opt)| {
                    (
                        typing_log_value::local_id_as_string(lid),
                        blame_as_log_value(blame_opt),
                    )
                })
                .collect(),
        )
    };
    typing_log_value::make_map(vec![(
        "Fake member ledger".to_string(),
        typing_log_value::make_map(vec![
            ("valid".to_string(), log_blame_set_as_value(&ledger.valid)),
            (
                "invalid".to_string(),
                log_blame_set_as_value(&ledger.invalid),
            ),
        ]),
    )])
}

/// Make identifiers
pub fn make_id(obj_name: &nast::Expr, member_name: &str) -> LocalId {
    let obj_name: LocalId = match obj_name {
        aast::Expr(_, _, aast::Expr_::This) => crate::typing_defs::this(),
        aast::Expr(_, _, aast::Expr_::Lvar(lid)) => lid.1.clone(),
        _ => panic!("Typing_fake_members.make_id: assert false"),
    };
    local_id::make_unscoped(format!(
        "{}->{}",
        local_id::get_name(&obj_name),
        member_name
    ))
}

pub fn make_static_id(cid: &nast::ClassId_, member_name: &str) -> LocalId {
    let class_name = crate::nast::class_id_to_str(cid);
    local_id::make_unscoped(format!("{}::{}", class_name, member_name))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn lid(name: &str) -> LocalId {
        local_id::make_unscoped(name)
    }

    /// A position that is different for each `line`.
    fn pos(line: usize) -> Pos {
        Pos::from_lnum_bol_offset(
            Arc::new(RelativePath::make(Prefix::Root, "f.php".into())),
            (line, 0, 0),
            (line, 0, 1),
        )
    }

    fn call(line: usize) -> Blame {
        Blame::Blame(pos(line), BlameSource::BScall)
    }

    fn lambda(line: usize) -> Blame {
        Blame::Blame(pos(line), BlameSource::BSlambda)
    }

    fn out_of_scope(line: usize) -> Blame {
        Blame::Blame(pos(line), BlameSource::BSoutOfScope)
    }

    fn names(set: &blame_set::T) -> Vec<String> {
        blame_set::elements(set)
            .into_iter()
            .map(|(lid, _)| lid.1)
            .collect()
    }

    fn set_of(elts: &[(&str, Blame)]) -> blame_set::T {
        elts.iter().fold(blame_set::empty(), |set, (name, blame)| {
            blame_set::add(lid(name), blame.clone(), &set)
        })
    }

    #[test]
    fn empty_ledger() {
        let ledger = empty();
        assert!(!is_valid(&ledger, &lid("$x->f")));
        assert_eq!(is_invalid(&ledger, &lid("$x->f")), None);
        assert!(sub(&ledger, &ledger));
    }

    #[test]
    fn add_then_forget() {
        let ledger = add(empty(), lid("$x->f"), pos(1));
        assert!(is_valid(&ledger, &lid("$x->f")));
        assert_eq!(is_invalid(&ledger, &lid("$x->f")), None);

        let ledger = forget(ledger, call(2));
        assert!(!is_valid(&ledger, &lid("$x->f")));
        assert_eq!(is_invalid(&ledger, &lid("$x->f")), Some(call(2)));

        // Adding the member again makes it valid and no longer invalid.
        let ledger = add(ledger, lid("$x->f"), pos(3));
        assert!(is_valid(&ledger, &lid("$x->f")));
        assert_eq!(is_invalid(&ledger, &lid("$x->f")), None);
    }

    #[test]
    fn add_keeps_the_blame_of_a_member_that_is_already_valid() {
        // `Set.add` returns the set unchanged when the element is present, and
        // elements are compared by id only.
        let ledger = add(empty(), lid("$x->f"), pos(1));
        let ledger = add(ledger, lid("$x->f"), pos(2));
        assert_eq!(
            blame_set::elements(&ledger.valid),
            vec![(lid("$x->f"), out_of_scope(1))]
        );
    }

    #[test]
    fn forget_with_nothing_valid_keeps_the_ledger() {
        let ledger = forget(add(empty(), lid("$x->f"), pos(1)), call(2));
        // A second event does not replace the blame of what is already
        // invalid.
        let ledger = forget(ledger, lambda(3));
        assert_eq!(is_invalid(&ledger, &lid("$x->f")), Some(call(2)));
    }

    #[test]
    fn forget_prefixed_and_suffixed() {
        let ledger = add(empty(), lid("$x->f"), pos(1));
        let ledger = add(ledger, lid("$x->g"), pos(2));
        let ledger = add(ledger, lid("$xy->f"), pos(3));
        let ledger = add(ledger, lid("C::f"), pos(4));

        let prefixed = forget_prefixed(ledger.clone(), &lid("$x"), call(5));
        assert_eq!(names(&prefixed.valid), vec!["$xy->f", "C::f"]);
        assert_eq!(names(&prefixed.invalid), vec!["$x->f", "$x->g"]);
        assert_eq!(is_invalid(&prefixed, &lid("$x->g")), Some(call(5)));

        let suffixed = forget_suffixed(ledger.clone(), "f", call(6));
        assert_eq!(names(&suffixed.valid), vec!["$x->g", "C::f"]);
        assert_eq!(names(&suffixed.invalid), vec!["$x->f", "$xy->f"]);

        // Nothing matches: the ledger is unchanged.
        let unchanged = forget_suffixed(ledger.clone(), "h", call(7));
        assert_eq!(names(&unchanged.valid), names(&ledger.valid));
        assert!(blame_set::is_empty(&unchanged.invalid));
    }

    #[test]
    fn join_keeps_what_is_valid_on_both_sides() {
        let ledger1 = add(add(empty(), lid("$x->f"), pos(1)), lid("$x->g"), pos(2));
        let ledger2 = add(add(empty(), lid("$x->g"), pos(3)), lid("$x->h"), pos(4));
        let joined = join(&ledger1, &ledger2);
        assert_eq!(names(&joined.valid), vec!["$x->g"]);
        assert_eq!(names(&joined.invalid), vec!["$x->f", "$x->h"]);
        // `inter` keeps the element of its first argument.
        assert_eq!(
            blame_set::elements(&joined.valid),
            vec![(lid("$x->g"), out_of_scope(2))]
        );
        // What is no longer valid keeps the blame it had while valid.
        assert_eq!(is_invalid(&joined, &lid("$x->f")), Some(out_of_scope(1)));
        assert_eq!(is_invalid(&joined, &lid("$x->h")), Some(out_of_scope(4)));

        // If join x y = z then sub x z = true and sub y z = true
        assert!(sub(&ledger1, &joined));
        assert!(sub(&ledger2, &joined));
        assert!(!sub(&joined, &ledger1));
    }

    #[test]
    fn join_of_members_invalidated_on_both_sides() {
        let ledger1 = forget(add(empty(), lid("$x->f"), pos(1)), call(2));
        let ledger2 = forget(add(empty(), lid("$x->f"), pos(1)), lambda(3));
        // Both trees have height 1: `Set.union s1 s2` is `add v2 s1`, which
        // keeps the element of `s1`.
        assert_eq!(
            is_invalid(&join(&ledger1, &ledger2), &lid("$x->f")),
            Some(call(2))
        );
        assert_eq!(
            is_invalid(&join(&ledger2, &ledger1), &lid("$x->f")),
            Some(lambda(3))
        );
    }

    #[test]
    fn union_keeps_the_elements_of_the_taller_tree() {
        // s1 = {b} (height 1), s2 = {a, b, c} (height 2). `Set.union` takes
        // the branch `h1 < h2`, `h1 = 1`: `add v1 s2`, and `b` is already in
        // `s2`, so the blame of `s2` is kept although `s1` comes first.
        let s1 = set_of(&[("b", call(1))]);
        let s2 = set_of(&[("b", call(3)), ("a", call(2)), ("c", call(4))]);
        assert_eq!(blame_set::shape(&s2), "((. a .) b (. c .))");
        let union = blame_set::union(&s1, &s2);
        assert_eq!(
            blame_set::elements(&union),
            vec![
                (lid("a"), call(2)),
                (lid("b"), call(3)),
                (lid("c"), call(4))
            ]
        );
        // The other way round (`h1 >= h2`, `h2 = 1`): `add v2 s1`, which again
        // keeps the blame of the taller tree.
        let union = blame_set::union(&s2, &s1);
        assert_eq!(
            blame_set::find_opt(&lid("b"), &union),
            Some((lid("b"), call(3)))
        );

        // Two trees of height 2 with the same elements: `h1 >= h2` and
        // `h2 <> 1`, so `s2` is split around the root of `s1` and every
        // element comes from `s1`.
        let s3 = set_of(&[("b", lambda(6)), ("a", lambda(5)), ("c", lambda(7))]);
        assert_eq!(blame_set::shape(&s3), blame_set::shape(&s2));
        let union = blame_set::union(&s2, &s3);
        assert_eq!(blame_set::elements(&union), blame_set::elements(&s2));
        let union = blame_set::union(&s3, &s2);
        assert_eq!(blame_set::elements(&union), blame_set::elements(&s3));
    }

    #[test]
    fn trees_are_built_as_set_ml_builds_them() {
        // Insertions in increasing order: the rotations of `bal` only happen
        // when the heights differ by more than 2.
        let names = ["a", "b", "c", "d", "e", "f", "g"];
        let mut set = blame_set::empty();
        let mut shapes = Vec::new();
        for name in names {
            set = blame_set::add(lid(name), call(1), &set);
            blame_set::check_invariants(&set);
            shapes.push(blame_set::shape(&set));
        }
        assert_eq!(
            shapes,
            vec![
                "(. a .)",
                "(. a (. b .))",
                "(. a (. b (. c .)))",
                "((. a .) b (. c (. d .)))",
                "((. a .) b (. c (. d (. e .))))",
                "((. a .) b ((. c .) d (. e (. f .))))",
                "(((. a .) b (. c .)) d (. e (. f (. g .))))",
            ]
        );
    }

    #[test]
    fn attach_blame_rebuilds_the_tree_with_join() {
        // `Set.map` is `try_join (map f l) (f v) (map f r)` at each node, and
        // `join Empty v r` is `add_min_element v r`: the tree that comes out
        // is not always the one that went in.
        let set = set_of(&[("a", call(1)), ("b", call(2))]);
        assert_eq!(blame_set::shape(&set), "(. a (. b .))");
        let attached = blame_set::attach_blame(&lambda(3), &set);
        assert_eq!(blame_set::shape(&attached), "((. a .) b .)");
        assert_eq!(
            blame_set::elements(&attached),
            vec![(lid("a"), lambda(3)), (lid("b"), lambda(3))]
        );
    }

    #[test]
    fn set_operations_keep_the_invariants() {
        // A small deterministic generator, so that the test does not depend
        // on anything else.
        let mut state: u32 = 12345;
        let mut next = move |bound: u32| {
            state = state.wrapping_mul(1103515245).wrapping_add(12345);
            (state >> 16) % bound
        };
        fn make(next: &mut impl FnMut(u32) -> u32, n: u32) -> blame_set::T {
            let mut set = blame_set::empty();
            for _ in 0..n {
                let name = format!("v{:02}", next(40));
                set = blame_set::add(lid(&name), call(next(5) as usize + 1), &set);
            }
            set
        }
        for _ in 0..300 {
            let n1 = next(30);
            let n2 = next(30);
            let s1 = make(&mut next, n1);
            let s2 = make(&mut next, n2);
            blame_set::check_invariants(&s1);
            blame_set::check_invariants(&s2);

            let union = blame_set::union(&s1, &s2);
            let inter = blame_set::inter(&s1, &s2);
            let diff = blame_set::diff(&s1, &s2);
            let (even, odd) = blame_set::partition(
                |(lid, _)| lid.1.as_bytes()[2] % 2 == 0,
                &s1,
            );
            let attached = blame_set::attach_blame(&lambda(9), &s1);
            for set in [&union, &inter, &diff, &even, &odd, &attached] {
                blame_set::check_invariants(set);
            }

            let (n1, n2) = (names(&s1), names(&s2));
            let mut expected: Vec<String> = n1.iter().chain(n2.iter()).cloned().collect();
            expected.sort();
            expected.dedup();
            assert_eq!(names(&union), expected);
            let expected: Vec<String> =
                n1.iter().filter(|n| n2.contains(n)).cloned().collect();
            assert_eq!(names(&inter), expected);
            let expected: Vec<String> =
                n1.iter().filter(|n| !n2.contains(n)).cloned().collect();
            assert_eq!(names(&diff), expected);
            assert_eq!(names(&even).len() + names(&odd).len(), n1.len());
            assert_eq!(blame_set::cardinal(&s1), n1.len());

            // `inter` keeps the elements of its first argument.
            for elt in blame_set::elements(&inter) {
                assert_eq!(blame_set::find_opt(&elt.0, &s1), Some(elt));
            }
            // `map` keeps the elements (the tree is rebuilt with `join`).
            assert_eq!(names(&attached), n1);
            assert!(
                blame_set::elements(&attached)
                    .iter()
                    .all(|(_, blame)| *blame == lambda(9))
            );

            assert!(blame_set::subset(&inter, &s1) && blame_set::subset(&inter, &s2));
            assert!(blame_set::subset(&s1, &union) && blame_set::subset(&s2, &union));
            assert_eq!(blame_set::subset(&s1, &s2), n1.iter().all(|n| n2.contains(n)));
            assert_eq!(
                blame_set::member(&lid("v07"), &s1),
                n1.contains(&"v07".to_string())
            );
            let removed = blame_set::remove(&lid("v07"), &s1);
            blame_set::check_invariants(&removed);
            assert!(!blame_set::member(&lid("v07"), &removed));
        }
    }
}
