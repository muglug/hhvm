// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_set.ml`. See `hh/PORTING.md`.
//!
//! An implementation of a set of types, using compare_locl_ty for a total
//! order. Typing-rule-equivalent types may get duplicated, as the equality
//! induced by compare_locl_ty does not expand Tvars and type aliases.
//!
//! # Why this is not `im::OrdSet`
//!
//! The order ignores reasons, so two types that differ only by their reason
//! are one element, and the set keeps one of the two reasons. Which one ends
//! up in error messages. `Set.add` keeps the element that is already there,
//! `Set.inter` those of its first argument, and `Set.union` the element of
//! whichever *tree* is taller at the point where the two meet: that depends on
//! the shapes of the balanced trees, which no other ordered set has. So
//! [`stdlib_set`] is `Stdlib.Set.Make` itself (`set.ml`), tree for tree, as
//! `crate::typing_fake_members::blame_set` does for the same reason. It is
//! persistent like the OCaml (a clone is a pointer copy, an update shares the
//! rest of the tree), and it iterates in increasing order. The nodes are
//! `Rc`s: the elements (inferred types) never leave the thread that checks
//! a file, and atomic reference counts cost more.
//!
//! [`T`] has the functions of `Set.S` under their OCaml names
//! (`typing_set::add(ty, &set)`), and the methods that callers written
//! against `im::OrdSet`/`BTreeSet` expect (`insert`, `remove`, `contains`,
//! `iter`, `len`, `is_empty`, `is_subset`, `collect()`); both give the trees
//! that the OCaml function named in their documentation gives. `collect()`
//! adds the elements one by one: `TySet.map f s` is [`map`]`(f, &s)` (or
//! [`map_phys`]), not `s.iter().map(f).collect()`, which builds another tree.
//!
//! `Internal_type_set` is the same functor applied to another order: it uses
//! [`stdlib_set`] too.

use std::cmp::Ordering;

use crate::type_force_lazy_values;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::compare_locl_ty;

/// `Stdlib.Set.Make`. The trees and the algorithms are those of `set.ml`.
pub mod stdlib_set {
    use std::cmp::Ordering;
    use std::rc::Rc;

    /// `Set.OrderedType`
    pub trait OrderedType {
        fn compare(a: &Self, b: &Self) -> Ordering;
    }

    /// The functions of `set.ml` on its trees, with the same names.
    mod tree {
        use std::cmp::Ordering;
        use std::rc::Rc;

        use super::OrderedType;

        pub struct Node<A> {
            pub l: Tree<A>,
            pub v: Rc<A>,
            pub r: Tree<A>,
            pub h: usize,
        }

        /// Sets are represented by balanced binary trees (the heights of the
        /// children differ by at most 2
        pub enum Tree<A> {
            Empty,
            Node(Rc<Node<A>>),
        }
        use Tree::Empty;

        impl<A> Clone for Tree<A> {
            fn clone(&self) -> Self {
                match self {
                    Empty => Empty,
                    Tree::Node(n) => Tree::Node(Rc::clone(n)),
                }
            }
        }

        /// OCaml's `==` on trees.
        pub fn phys_equal<A>(a: &Tree<A>, b: &Tree<A>) -> bool {
            match (a, b) {
                (Empty, Empty) => true,
                (Tree::Node(a), Tree::Node(b)) => Rc::ptr_eq(a, b),
                _ => false,
            }
        }

        fn node<A>(l: Tree<A>, v: Rc<A>, r: Tree<A>, h: usize) -> Tree<A> {
            Tree::Node(Rc::new(Node { l, v, r, h }))
        }

        pub fn height<A>(t: &Tree<A>) -> usize {
            match t {
                Empty => 0,
                Tree::Node(n) => n.h,
            }
        }

        /// Creates a new node with left son l, value v and right son r.
        /// We must have all elements of l < v < all elements of r.
        /// l and r must be balanced and | height l - height r | <= 2.
        fn create<A>(l: Tree<A>, v: Rc<A>, r: Tree<A>) -> Tree<A> {
            let hl = height(&l);
            let hr = height(&r);
            node(l, v, r, if hl >= hr { hl + 1 } else { hr + 1 })
        }

        /// Same as create, but performs one step of rebalancing if necessary.
        /// Assumes l and r balanced and | height l - height r | <= 3.
        fn bal<A>(l: Tree<A>, v: Rc<A>, r: Tree<A>) -> Tree<A> {
            let hl = height(&l);
            let hr = height(&r);
            if hl > hr + 2 {
                match &l {
                    Empty => panic!("Set.bal"),
                    Tree::Node(ln) => {
                        let (ll, lv, lr) = (&ln.l, &ln.v, &ln.r);
                        if height(ll) >= height(lr) {
                            create(ll.clone(), lv.clone(), create(lr.clone(), v, r))
                        } else {
                            match lr {
                                Empty => panic!("Set.bal"),
                                Tree::Node(lrn) => create(
                                    create(ll.clone(), lv.clone(), lrn.l.clone()),
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
                        let (rl, rv, rr) = (&rn.l, &rn.v, &rn.r);
                        if height(rr) >= height(rl) {
                            create(create(l, v, rl.clone()), rv.clone(), rr.clone())
                        } else {
                            match rl {
                                Empty => panic!("Set.bal"),
                                Tree::Node(rln) => create(
                                    create(l, v, rln.l.clone()),
                                    rln.v.clone(),
                                    create(rln.r.clone(), rv.clone(), rr.clone()),
                                ),
                            }
                        }
                    }
                }
            } else {
                node(l, v, r, if hl >= hr { hl + 1 } else { hr + 1 })
            }
        }

        /// Insertion of one element
        pub fn add<A: OrderedType>(x: Rc<A>, t: &Tree<A>) -> Tree<A> {
            match t {
                Empty => node(Empty, x, Empty, 1),
                Tree::Node(n) => match A::compare(&x, &n.v) {
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

        pub fn singleton<A>(x: Rc<A>) -> Tree<A> {
            node(Empty, x, Empty, 1)
        }

        // Beware: those two functions assume that the added v is *strictly*
        // smaller (or bigger) than all the present elements in the tree; it
        // does not test for equality with the current min (or max) element.
        // Indeed, they are only used during the "join" operation which
        // respects this precondition.

        fn add_min_element<A>(x: Rc<A>, t: &Tree<A>) -> Tree<A> {
            match t {
                Empty => singleton(x),
                Tree::Node(n) => bal(add_min_element(x, &n.l), n.v.clone(), n.r.clone()),
            }
        }

        fn add_max_element<A>(x: Rc<A>, t: &Tree<A>) -> Tree<A> {
            match t {
                Empty => singleton(x),
                Tree::Node(n) => bal(n.l.clone(), n.v.clone(), add_max_element(x, &n.r)),
            }
        }

        /// Same as create and bal, but no assumptions are made on the
        /// relative heights of l and r.
        fn join<A>(l: &Tree<A>, v: Rc<A>, r: &Tree<A>) -> Tree<A> {
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

        // Smallest and greatest element of a set

        /// `raise Not_found` on the empty set.
        fn min_elt<A>(t: &Tree<A>) -> &Rc<A> {
            match t {
                Empty => panic!("Not_found"),
                Tree::Node(n) => match &n.l {
                    Empty => &n.v,
                    l => min_elt(l),
                },
            }
        }

        pub fn min_elt_opt<A>(t: &Tree<A>) -> Option<&Rc<A>> {
            match t {
                Empty => None,
                Tree::Node(n) => match &n.l {
                    Empty => Some(&n.v),
                    l => min_elt_opt(l),
                },
            }
        }

        /// `raise Not_found` on the empty set.
        fn max_elt<A>(t: &Tree<A>) -> &Rc<A> {
            match t {
                Empty => panic!("Not_found"),
                Tree::Node(n) => match &n.r {
                    Empty => &n.v,
                    r => max_elt(r),
                },
            }
        }

        pub fn max_elt_opt<A>(t: &Tree<A>) -> Option<&Rc<A>> {
            match t {
                Empty => None,
                Tree::Node(n) => match &n.r {
                    Empty => Some(&n.v),
                    r => max_elt_opt(r),
                },
            }
        }

        /// Remove the smallest element of the given set
        fn remove_min_elt<A>(t: &Tree<A>) -> Tree<A> {
            match t {
                Empty => panic!("Set.remove_min_elt"),
                Tree::Node(n) => match &n.l {
                    Empty => n.r.clone(),
                    l => bal(remove_min_elt(l), n.v.clone(), n.r.clone()),
                },
            }
        }

        /// Merge two trees l and r into one.
        /// All elements of l must precede the elements of r.
        /// Assume | height l - height r | <= 2.
        fn merge<A>(t1: &Tree<A>, t2: &Tree<A>) -> Tree<A> {
            match (t1, t2) {
                (Empty, t) => t.clone(),
                (t, Empty) => t.clone(),
                (_, _) => bal(t1.clone(), min_elt(t2).clone(), remove_min_elt(t2)),
            }
        }

        /// Merge two trees l and r into one.
        /// All elements of l must precede the elements of r.
        /// No assumption on the heights of l and r.
        fn concat<A>(t1: &Tree<A>, t2: &Tree<A>) -> Tree<A> {
            match (t1, t2) {
                (Empty, t) => t.clone(),
                (t, Empty) => t.clone(),
                (_, _) => join(t1, min_elt(t2).clone(), &remove_min_elt(t2)),
            }
        }

        /// Splitting.  split x s returns a triple (l, present, r) where
        ///  - l is the set of elements of s that are < x
        ///  - r is the set of elements of s that are > x
        ///  - present is false if s contains no element equal to x,
        ///    or true if s contains an element equal to x.
        fn split<A: OrderedType>(x: &A, t: &Tree<A>) -> (Tree<A>, bool, Tree<A>) {
            match t {
                Empty => (Empty, false, Empty),
                Tree::Node(n) => match A::compare(x, &n.v) {
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

        // Implementation of the set operations

        pub fn is_empty<A>(t: &Tree<A>) -> bool {
            matches!(t, Empty)
        }

        pub fn mem<A: OrderedType>(x: &A, t: &Tree<A>) -> bool {
            match t {
                Empty => false,
                Tree::Node(n) => match A::compare(x, &n.v) {
                    Ordering::Equal => true,
                    Ordering::Less => mem(x, &n.l),
                    Ordering::Greater => mem(x, &n.r),
                },
            }
        }

        pub fn remove<A: OrderedType>(x: &A, t: &Tree<A>) -> Tree<A> {
            match t {
                Empty => Empty,
                Tree::Node(n) => match A::compare(x, &n.v) {
                    Ordering::Equal => merge(&n.l, &n.r),
                    Ordering::Less => {
                        let ll = remove(x, &n.l);
                        if phys_equal(&n.l, &ll) {
                            t.clone()
                        } else {
                            bal(ll, n.v.clone(), n.r.clone())
                        }
                    }
                    Ordering::Greater => {
                        let rr = remove(x, &n.r);
                        if phys_equal(&n.r, &rr) {
                            t.clone()
                        } else {
                            bal(n.l.clone(), n.v.clone(), rr)
                        }
                    }
                },
            }
        }

        pub fn union<A: OrderedType>(s1: &Tree<A>, s2: &Tree<A>) -> Tree<A> {
            match (s1, s2) {
                (Empty, t2) => t2.clone(),
                (t1, Empty) => t1.clone(),
                (Tree::Node(n1), Tree::Node(n2)) => {
                    if n1.h >= n2.h {
                        if n2.h == 1 {
                            add(n2.v.clone(), s1)
                        } else {
                            let (l2, _, r2) = split(&*n1.v, s2);
                            join(&union(&n1.l, &l2), n1.v.clone(), &union(&n1.r, &r2))
                        }
                    } else if n1.h == 1 {
                        add(n1.v.clone(), s2)
                    } else {
                        let (l1, _, r1) = split(&*n2.v, s1);
                        join(&union(&l1, &n2.l), n2.v.clone(), &union(&r1, &n2.r))
                    }
                }
            }
        }

        pub fn inter<A: OrderedType>(s1: &Tree<A>, s2: &Tree<A>) -> Tree<A> {
            match (s1, s2) {
                (Empty, _) => Empty,
                (_, Empty) => Empty,
                (Tree::Node(n1), t2) => match split(&*n1.v, t2) {
                    (l2, false, r2) => concat(&inter(&n1.l, &l2), &inter(&n1.r, &r2)),
                    (l2, true, r2) => join(&inter(&n1.l, &l2), n1.v.clone(), &inter(&n1.r, &r2)),
                },
            }
        }

        pub fn diff<A: OrderedType>(s1: &Tree<A>, s2: &Tree<A>) -> Tree<A> {
            match (s1, s2) {
                (Empty, _) => Empty,
                (t1, Empty) => t1.clone(),
                (Tree::Node(n1), t2) => match split(&*n1.v, t2) {
                    (l2, false, r2) => join(&diff(&n1.l, &l2), n1.v.clone(), &diff(&n1.r, &r2)),
                    (l2, true, r2) => concat(&diff(&n1.l, &l2), &diff(&n1.r, &r2)),
                },
            }
        }

        pub fn subset<A: OrderedType>(s1: &Tree<A>, s2: &Tree<A>) -> bool {
            // A tree is a subset of itself (the order is reflexive): the
            // OCaml compares every element, here a shared tree (the bounds
            // that two continuations both have) is not walked.
            if phys_equal(s1, s2) {
                return true;
            }
            match (s1, s2) {
                (Empty, _) => true,
                (_, Empty) => false,
                (Tree::Node(n1), Tree::Node(n2)) => match A::compare(&n1.v, &n2.v) {
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

        pub fn iter<A>(f: &mut dyn FnMut(&A), t: &Tree<A>) {
            if let Tree::Node(n) = t {
                iter(f, &n.l);
                f(&n.v);
                iter(f, &n.r);
            }
        }

        pub fn fold<A, B>(f: &mut dyn FnMut(&A, B) -> B, s: &Tree<A>, accu: B) -> B {
            match s {
                Empty => accu,
                Tree::Node(n) => {
                    let accu = fold(f, &n.l, accu);
                    let accu = f(&n.v, accu);
                    fold(f, &n.r, accu)
                }
            }
        }

        pub fn for_all<A>(p: &mut dyn FnMut(&A) -> bool, t: &Tree<A>) -> bool {
            match t {
                Empty => true,
                Tree::Node(n) => p(&n.v) && for_all(p, &n.l) && for_all(p, &n.r),
            }
        }

        pub fn exists<A>(p: &mut dyn FnMut(&A) -> bool, t: &Tree<A>) -> bool {
            match t {
                Empty => false,
                Tree::Node(n) => p(&n.v) || exists(p, &n.l) || exists(p, &n.r),
            }
        }

        pub fn filter<A>(p: &mut dyn FnMut(&A) -> bool, t: &Tree<A>) -> Tree<A> {
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

        pub fn partition<A>(p: &mut dyn FnMut(&A) -> bool, t: &Tree<A>) -> (Tree<A>, Tree<A>) {
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

        pub fn cardinal<A>(t: &Tree<A>) -> usize {
            match t {
                Empty => 0,
                Tree::Node(n) => cardinal(&n.l) + 1 + cardinal(&n.r),
            }
        }

        fn find_first_opt_aux<'a, A>(
            v0: &'a Rc<A>,
            f: &mut dyn FnMut(&A) -> bool,
            t: &'a Tree<A>,
        ) -> Option<&'a Rc<A>> {
            match t {
                Empty => Some(v0),
                Tree::Node(n) => {
                    if f(&n.v) {
                        find_first_opt_aux(&n.v, f, &n.l)
                    } else {
                        find_first_opt_aux(v0, f, &n.r)
                    }
                }
            }
        }

        pub fn find_first_opt<'a, A>(
            f: &mut dyn FnMut(&A) -> bool,
            t: &'a Tree<A>,
        ) -> Option<&'a Rc<A>> {
            match t {
                Empty => None,
                Tree::Node(n) => {
                    if f(&n.v) {
                        find_first_opt_aux(&n.v, f, &n.l)
                    } else {
                        find_first_opt(f, &n.r)
                    }
                }
            }
        }

        /// [join l v r] can only be called when (elements of l < v <
        /// elements of r); use [try_join l v r] when this property may
        /// not hold, but you hope it does hold in the common case
        fn try_join<A: OrderedType>(l: &Tree<A>, v: Rc<A>, r: &Tree<A>) -> Tree<A> {
            if (is_empty(l) || A::compare(max_elt(l), &v) == Ordering::Less)
                && (is_empty(r) || A::compare(&v, min_elt(r)) == Ordering::Less)
            {
                join(l, v, r)
            } else {
                union(l, &add(v, r))
            }
        }

        /// `f` gives the element itself (the same pointer) when it does not
        /// change it, as in OCaml (`v == v'`).
        pub fn map<A: OrderedType>(
            f: &mut dyn FnMut(&Rc<A>) -> Rc<A>,
            t: &Tree<A>,
        ) -> Tree<A> {
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

        /// `l` is sorted in strictly increasing order.
        pub fn of_sorted_list<A>(l: Vec<Rc<A>>) -> Tree<A> {
            fn sub<A>(n: usize, l: &mut std::vec::IntoIter<Rc<A>>) -> Tree<A> {
                let mut next = || l.next().expect("assert false");
                match n {
                    0 => Empty,
                    1 => {
                        let x0 = next();
                        node(Empty, x0, Empty, 1)
                    }
                    2 => {
                        let x0 = next();
                        let x1 = next();
                        node(node(Empty, x0, Empty, 1), x1, Empty, 2)
                    }
                    3 => {
                        let x0 = next();
                        let x1 = next();
                        let x2 = next();
                        node(node(Empty, x0, Empty, 1), x1, node(Empty, x2, Empty, 1), 2)
                    }
                    n => {
                        let nl = n / 2;
                        let left = sub(nl, l);
                        let mid = l.next().expect("assert false");
                        let right = sub(n - nl - 1, l);
                        create(left, mid, right)
                    }
                }
            }
            let n = l.len();
            sub(n, &mut l.into_iter())
        }

        pub fn of_list<A: OrderedType>(l: Vec<Rc<A>>) -> Tree<A> {
            if l.len() <= 5 {
                // [] -> empty
                // [x0] -> singleton x0
                // [x0; x1] -> add x1 (singleton x0)
                // ...
                // [x0; x1; x2; x3; x4] ->
                //   add x4 (add x3 (add x2 (add x1 (singleton x0))))
                let mut t = Empty;
                for x in l {
                    t = add(x, &t);
                }
                t
            } else {
                // of_sorted_list (List.sort_uniq Ord.compare l)
                //
                // `List.sort_uniq` is a merge sort that, of the elements that
                // compare equal, keeps the one that comes first in the list
                // (every `c = 0` case of `list.ml` keeps the element of the
                // first half): a stable sort, then the first of each run.
                let mut l = l;
                l.sort_by(|a, b| A::compare(a, b));
                l.dedup_by(|later, earlier| A::compare(earlier, later) == Ordering::Equal);
                of_sorted_list(l)
            }
        }
    }

    use tree::Tree;

    /// `Set.Make(Ord).t`. Persistent: a clone is a pointer copy.
    pub struct Set<A>(Tree<A>);

    impl<A> Clone for Set<A> {
        fn clone(&self) -> Self {
            Set(self.0.clone())
        }
    }

    impl<A> Default for Set<A> {
        /// `empty`
        fn default() -> Self {
            Set(Tree::Empty)
        }
    }

    /// The elements in increasing order.
    pub struct Iter<'a, A> {
        /// The nodes whose element and right subtree are still to be visited,
        /// the next one last.
        stack: Vec<&'a tree::Node<A>>,
    }

    impl<'a, A> Iter<'a, A> {
        fn push_left(&mut self, mut t: &'a Tree<A>) {
            while let Tree::Node(n) = t {
                self.stack.push(n);
                t = &n.l;
            }
        }
    }

    impl<'a, A> Iterator for Iter<'a, A> {
        type Item = &'a A;

        fn next(&mut self) -> Option<&'a A> {
            let n = self.stack.pop()?;
            self.push_left(&n.r);
            Some(&*n.v)
        }
    }

    impl<A> Set<A> {
        /// `empty`
        pub fn new() -> Self {
            Set(Tree::Empty)
        }

        /// The elements in increasing order (the order of `elements`,
        /// `iter` and `fold`).
        pub fn iter(&self) -> Iter<'_, A> {
            let mut iter = Iter { stack: Vec::new() };
            iter.push_left(&self.0);
            iter
        }

        /// `cardinal`
        pub fn len(&self) -> usize {
            tree::cardinal(&self.0)
        }

        /// `is_empty`
        pub fn is_empty(&self) -> bool {
            tree::is_empty(&self.0)
        }
    }

    impl<A: OrderedType> Set<A> {
        /// `s := add x !s`. As `add`, it keeps the element that is already in
        /// the set if one compares equal to `x`. Returns whether `x` was
        /// added.
        pub fn insert(&mut self, x: A) -> bool {
            let t = tree::add(Rc::new(x), &self.0);
            let added = !tree::phys_equal(&t, &self.0);
            self.0 = t;
            added
        }

        /// `s := remove x !s`. Returns whether an element was removed.
        pub fn remove(&mut self, x: &A) -> bool {
            let t = tree::remove(x, &self.0);
            let removed = !tree::phys_equal(&t, &self.0);
            self.0 = t;
            removed
        }

        /// `mem`
        pub fn contains(&self, x: &A) -> bool {
            tree::mem(x, &self.0)
        }

        /// `subset self other`
        pub fn is_subset(&self, other: &Self) -> bool {
            tree::subset(&self.0, &other.0)
        }
    }

    /// `List.fold ~init:empty ~f:(fun s x -> add x s)`: the elements are
    /// added one by one, in the order of the iterator. (That is `of_list` for
    /// up to five elements, and `of_seq`.)
    impl<A: OrderedType> FromIterator<A> for Set<A> {
        fn from_iter<I: IntoIterator<Item = A>>(iter: I) -> Self {
            let mut t = Tree::Empty;
            for x in iter {
                t = tree::add(Rc::new(x), &t);
            }
            Set(t)
        }
    }

    impl<'a, A> IntoIterator for &'a Set<A> {
        type Item = &'a A;
        type IntoIter = Iter<'a, A>;

        fn into_iter(self) -> Iter<'a, A> {
            self.iter()
        }
    }

    impl<A: std::fmt::Debug> std::fmt::Debug for Set<A> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_set().entries(self.iter()).finish()
        }
    }

    /// `equal`
    impl<A: OrderedType> PartialEq for Set<A> {
        fn eq(&self, other: &Self) -> bool {
            equal(self, other)
        }
    }

    impl<A: OrderedType> Eq for Set<A> {}

    /// The elements in increasing order (as `Typing_set.hash_fold_t`).
    impl<A: std::hash::Hash> std::hash::Hash for Set<A> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            state.write_usize(self.len());
            for x in self.iter() {
                x.hash(state)
            }
        }
    }

    // -- The functions of `Set.S`, with their OCaml names --------------------

    pub fn empty<A>() -> Set<A> {
        Set(Tree::Empty)
    }

    pub fn is_empty<A>(s: &Set<A>) -> bool {
        tree::is_empty(&s.0)
    }

    pub fn mem<A: OrderedType>(x: &A, s: &Set<A>) -> bool {
        tree::mem(x, &s.0)
    }

    /// If an element of `s` compares equal to `x`, the result is `s` (with
    /// that element, not `x`).
    pub fn add<A: OrderedType>(x: A, s: &Set<A>) -> Set<A> {
        Set(tree::add(Rc::new(x), &s.0))
    }

    pub fn singleton<A>(x: A) -> Set<A> {
        Set(tree::singleton(Rc::new(x)))
    }

    pub fn remove<A: OrderedType>(x: &A, s: &Set<A>) -> Set<A> {
        Set(tree::remove(x, &s.0))
    }

    /// Of two elements that compare equal, one in each set, the result has
    /// the one that `Set.union` keeps: it depends on the heights of the trees
    /// (when one of the sets is a singleton, the element of the other set).
    pub fn union<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> Set<A> {
        Set(tree::union(&s1.0, &s2.0))
    }

    /// The elements of the result are those of `s1`.
    pub fn inter<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> Set<A> {
        Set(tree::inter(&s1.0, &s2.0))
    }

    pub fn diff<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> Set<A> {
        Set(tree::diff(&s1.0, &s2.0))
    }

    /// The lexicographic order on the increasing sequences of elements.
    pub fn compare<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> Ordering {
        // A tree is equal to itself (the order is reflexive): not walked.
        if tree::phys_equal(&s1.0, &s2.0) {
            return Ordering::Equal;
        }
        // compare_aux (cons_enum s1 End) (cons_enum s2 End)
        let mut e1 = s1.iter();
        let mut e2 = s2.iter();
        loop {
            match (e1.next(), e2.next()) {
                (None, None) => return Ordering::Equal,
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (Some(v1), Some(v2)) => {
                    let c = A::compare(v1, v2);
                    if c != Ordering::Equal {
                        return c;
                    }
                }
            }
        }
    }

    pub fn equal<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> bool {
        compare(s1, s2) == Ordering::Equal
    }

    pub fn subset<A: OrderedType>(s1: &Set<A>, s2: &Set<A>) -> bool {
        tree::subset(&s1.0, &s2.0)
    }

    /// In increasing order.
    pub fn iter<A>(mut f: impl FnMut(&A), s: &Set<A>) {
        tree::iter(&mut f, &s.0)
    }

    /// `Set.map f` with an `f` that makes a new value for every element (as
    /// the type mappers do: they rebuild the type). `f` is applied in
    /// increasing order.
    ///
    /// As in OCaml, every node is then rebuilt with `try_join`, which can
    /// give another tree than the one of `s` even when the order of the
    /// elements does not change (a node with an empty child goes through
    /// `add_min_element`/`add_max_element`). When the OCaml `f` gives some
    /// elements back themselves (`fun x -> x`, `| ity -> ity`), OCaml keeps
    /// the nodes in which nothing changed: use [`map_phys`] for those.
    pub fn map<A: OrderedType>(mut f: impl FnMut(&A) -> A, s: &Set<A>) -> Set<A> {
        Set(tree::map(&mut |v| Rc::new(f(v)), &s.0))
    }

    /// `Set.map f` with an `f` that gives some elements back themselves
    /// (physically: `fun x -> x`, `| ity -> ity`): `f` gives `None` for those
    /// and `Some` of the new value for the others. As in OCaml (`l == l' &&
    /// v == v' && r == r'`), a node in which nothing changed is kept as it is
    /// (`map_phys(|_| None, s)` is `s`, tree included) and the others are
    /// rebuilt as by [`map`]. `f` is applied in increasing order.
    pub fn map_phys<A: OrderedType>(mut f: impl FnMut(&A) -> Option<A>, s: &Set<A>) -> Set<A> {
        Set(tree::map(
            &mut |v| match f(v) {
                None => Rc::clone(v),
                Some(v) => Rc::new(v),
            },
            &s.0,
        ))
    }

    /// In increasing order.
    pub fn fold<A, B>(mut f: impl FnMut(&A, B) -> B, s: &Set<A>, accu: B) -> B {
        tree::fold(&mut f, &s.0, accu)
    }

    /// `p` is applied to an element before the smaller ones, as in OCaml
    /// (root, left subtree, right subtree), until it gives `false`.
    pub fn for_all<A>(mut p: impl FnMut(&A) -> bool, s: &Set<A>) -> bool {
        tree::for_all(&mut p, &s.0)
    }

    /// `p` is applied to an element before the smaller ones, as in OCaml
    /// (root, left subtree, right subtree), until it gives `true`.
    pub fn exists<A>(mut p: impl FnMut(&A) -> bool, s: &Set<A>) -> bool {
        tree::exists(&mut p, &s.0)
    }

    /// `p` is applied in increasing order.
    pub fn filter<A>(mut p: impl FnMut(&A) -> bool, s: &Set<A>) -> Set<A> {
        Set(tree::filter(&mut p, &s.0))
    }

    /// `p` is applied in increasing order.
    pub fn partition<A>(mut p: impl FnMut(&A) -> bool, s: &Set<A>) -> (Set<A>, Set<A>) {
        let (t, f) = tree::partition(&mut p, &s.0);
        (Set(t), Set(f))
    }

    pub fn cardinal<A>(s: &Set<A>) -> isize {
        tree::cardinal(&s.0) as isize
    }

    /// In increasing order.
    pub fn elements<A: Clone>(s: &Set<A>) -> Vec<A> {
        s.iter().cloned().collect()
    }

    pub fn to_list<A: Clone>(s: &Set<A>) -> Vec<A> {
        elements(s)
    }

    pub fn min_elt_opt<A: Clone>(s: &Set<A>) -> Option<A> {
        tree::min_elt_opt(&s.0).map(|v| A::clone(v))
    }

    pub fn max_elt_opt<A: Clone>(s: &Set<A>) -> Option<A> {
        tree::max_elt_opt(&s.0).map(|v| A::clone(v))
    }

    pub fn choose_opt<A: Clone>(s: &Set<A>) -> Option<A> {
        min_elt_opt(s)
    }

    /// `f` is monotonically increasing: the smallest element on which it is
    /// `true`.
    pub fn find_first_opt<A: Clone>(mut f: impl FnMut(&A) -> bool, s: &Set<A>) -> Option<A> {
        tree::find_first_opt(&mut f, &s.0).map(|v| A::clone(v))
    }

    pub fn of_list<A: OrderedType>(l: Vec<A>) -> Set<A> {
        Set(tree::of_list(l.into_iter().map(Rc::new).collect()))
    }

    /// For the tests: the tree, as `(left element right)`, with `.` for the
    /// empty tree, and whether it is a well-formed tree of `set.ml`.
    #[cfg(test)]
    pub(crate) fn dump<A>(show: &dyn Fn(&A) -> String, s: &Set<A>) -> String {
        fn go<A>(show: &dyn Fn(&A) -> String, t: &Tree<A>, out: &mut String) {
            match t {
                Tree::Empty => out.push('.'),
                Tree::Node(n) => {
                    out.push('(');
                    go(show, &n.l, out);
                    out.push(' ');
                    out.push_str(&show(&n.v));
                    out.push(' ');
                    go(show, &n.r, out);
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        go(show, &s.0, &mut out);
        out
    }

    /// For the tests: OCaml's `s1 == s2`.
    #[cfg(test)]
    pub(crate) fn same_tree<A>(s1: &Set<A>, s2: &Set<A>) -> bool {
        tree::phys_equal(&s1.0, &s2.0)
    }

    /// For the tests: the invariants of `set.ml` (heights, balance, order).
    #[cfg(test)]
    pub(crate) fn check_invariants<A: OrderedType>(s: &Set<A>) {
        fn go<A: OrderedType>(t: &Tree<A>) -> usize {
            match t {
                Tree::Empty => 0,
                Tree::Node(n) => {
                    let hl = go(&n.l);
                    let hr = go(&n.r);
                    assert_eq!(n.h, hl.max(hr) + 1, "height");
                    assert!(hl <= hr + 2 && hr <= hl + 2, "balance");
                    hl.max(hr) + 1
                }
            }
        }
        go(&s.0);
        let elts: Vec<&A> = s.iter().collect();
        for w in elts.windows(2) {
            assert_eq!(A::compare(w[0], w[1]), Ordering::Less, "order");
        }
        assert_eq!(elts.len(), s.len());
    }
}

pub use stdlib_set::add;
pub use stdlib_set::cardinal;
pub use stdlib_set::choose_opt;
pub use stdlib_set::diff;
pub use stdlib_set::elements;
pub use stdlib_set::empty;
pub use stdlib_set::equal;
pub use stdlib_set::exists;
pub use stdlib_set::filter;
pub use stdlib_set::find_first_opt;
pub use stdlib_set::fold;
pub use stdlib_set::for_all;
pub use stdlib_set::inter;
pub use stdlib_set::is_empty;
pub use stdlib_set::iter;
pub use stdlib_set::map;
pub use stdlib_set::map_phys;
pub use stdlib_set::max_elt_opt;
pub use stdlib_set::mem;
pub use stdlib_set::min_elt_opt;
pub use stdlib_set::of_list;
pub use stdlib_set::partition;
pub use stdlib_set::remove;
pub use stdlib_set::singleton;
pub use stdlib_set::subset;
pub use stdlib_set::to_list;
pub use stdlib_set::union;

pub mod ty_ {
    use std::cmp::Ordering;

    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::compare_locl_ty;

    /// `Typing_set.Ty_.t`
    pub type T = Ty;

    pub fn compare(r1: &Ty, r2: &Ty) -> Ordering {
        compare_locl_ty(None, r1, r2)
    }
}

/// `Ty_.compare`: `Typing_defs.compare_locl_ty`, which is also `Ty: Ord`.
impl stdlib_set::OrderedType for Ty {
    fn compare(a: &Self, b: &Self) -> Ordering {
        compare_locl_ty(None, a, b)
    }
}

/// `Typing_set.elt`
pub type Elt = Ty;

/// `Typing_set.t`
pub type T = stdlib_set::Set<Ty>;

/// `Set.compare` (the module has no `compare` of its own: `Ty_.compare` is
/// [`ty_::compare`]).
pub fn compare(s1: &T, s2: &T) -> Ordering {
    stdlib_set::compare(s1, s2)
}

/// The elements are printed by `Typing_defs.pp_locl_ty`, in `Format` boxes
/// (`pp`, which takes a `Format.formatter`, is not here: see
/// `crate::typing_defs_core::pp`).
pub fn show(_t: &T) -> String {
    todo!(
        "Typing_set.show: needs a port of OCaml's Format (boxes and break hints) and Typing_defs.pp_locl_ty"
    )
}

// `hash_fold_t` and `hash` are `impl Hash for T`: the hashes of the elements
// in increasing order.

pub fn force_lazy_values(t: T) -> T {
    map(|ty| type_force_lazy_values::locl_ty(ty.clone()), &t)
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::get_reason;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;
    use crate::typing_reason::T as Reason;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn var(n: isize) -> Ty {
        mk((typing_reason::none(), Ty_::Tvar(n)))
    }

    fn generic(name: &str) -> Ty {
        mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    /// The same type with a reason that can be told from `Reason::none()`.
    fn marked(ty: &Ty) -> Ty {
        mk((
            typing_reason::type_variable(Pos::NONE, 42),
            get_node(ty).clone(),
        ))
    }

    fn is_marked(ty: &Ty) -> bool {
        !matches!(&**get_reason(ty), crate::typing_reason::T_::NoReason)
    }

    fn of(tys: &[Ty]) -> T {
        tys.iter().cloned().collect()
    }

    /// A few types of different shapes, and the same types sorted with the
    /// order of the module.
    fn sample() -> (Vec<Ty>, Vec<Ty>) {
        let tys = vec![
            generic("T"),
            prim(Tprim::Tfloat),
            var(3),
            mk((typing_reason::none(), Ty_::Tnonnull)),
            prim(Tprim::Tint),
            var(1),
            mk((typing_reason::none(), Ty_::Toption(prim(Tprim::Tint)))),
            generic("A"),
            mk((typing_reason::none(), Ty_::Tunion(vec![]))),
        ];
        let mut sorted = tys.clone();
        sorted.sort_by(|a, b| compare_locl_ty(None, a, b));
        (tys, sorted)
    }

    #[test]
    fn the_order_is_compare_locl_ty_and_ty_ord() {
        let (tys, _) = sample();
        for a in &tys {
            for b in &tys {
                let c = ty_::compare(a, b);
                assert_eq!(c, compare_locl_ty(None, a, b));
                assert_eq!(c, <Ty as stdlib_set::OrderedType>::compare(a, b));
                // `Ty: Ord` is the same order.
                assert_eq!(c, a.cmp(b));
                assert_eq!(c.reverse(), ty_::compare(b, a));
                // Reasons are ignored.
                assert_eq!(c, ty_::compare(&marked(a), b));
            }
        }
        // A few fixed points of the order of `Typing_defs_core.ty_compare`
        // (constructors in the order of `ty_con_ordinal`, then their
        // arguments).
        assert_eq!(ty_::compare(&var(1), &var(3)), Ordering::Less);
        assert_eq!(ty_::compare(&generic("A"), &generic("T")), Ordering::Less);
        assert_eq!(
            ty_::compare(&prim(Tprim::Tint), &prim(Tprim::Tint)),
            Ordering::Equal
        );
    }

    #[test]
    fn iteration_is_ascending_whatever_the_insertion_order() {
        let (tys, sorted) = sample();
        let mut set = T::default();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
        for ty in &tys {
            assert!(set.insert(ty.clone()));
            stdlib_set::check_invariants(&set);
        }
        assert_eq!(set.len(), tys.len());
        assert_eq!(cardinal(&set), tys.len() as isize);
        assert_eq!(set.iter().cloned().collect::<Vec<Ty>>(), sorted);
        assert_eq!(elements(&set), sorted);
        assert_eq!((&set).into_iter().count(), sorted.len());
        let mut seen = vec![];
        iter(|ty| seen.push(ty.clone()), &set);
        assert_eq!(seen, sorted);
        assert_eq!(fold(|ty, mut acc: Vec<Ty>| { acc.push(ty.clone()); acc }, &set, vec![]), sorted);
        // The same set from the reversed list, and with `of_list` (more than
        // five elements: sorted first).
        let mut rev = tys.clone();
        rev.reverse();
        let set2 = of(&rev);
        assert_eq!(elements(&set2), sorted);
        assert!(equal(&set, &set2));
        assert_eq!(set, set2);
        let set3 = of_list(tys.clone());
        stdlib_set::check_invariants(&set3);
        assert_eq!(elements(&set3), sorted);
        assert_eq!(min_elt_opt(&set), sorted.first().cloned());
        assert_eq!(choose_opt(&set), sorted.first().cloned());
        assert_eq!(max_elt_opt(&set), sorted.last().cloned());
        assert_eq!(choose_opt(&T::default()), None);
        for ty in &tys {
            assert!(set.contains(ty));
            assert!(mem(&marked(ty), &set));
        }
        assert!(!set.contains(&var(99)));
    }

    #[test]
    fn insert_keeps_the_element_that_is_there() {
        let int = prim(Tprim::Tint);
        let mut set = of(&[int.clone(), prim(Tprim::Tfloat)]);
        // `Set.add x s` is `s` when an element compares equal to `x`.
        assert!(!set.insert(marked(&int)));
        assert_eq!(set.len(), 2);
        assert!(set.iter().all(|ty| !is_marked(ty)));
        let set2 = add(marked(&int), &set);
        assert!(set2.iter().all(|ty| !is_marked(ty)));
        // The other way round.
        let mut set = of(&[marked(&int)]);
        assert!(!set.insert(int.clone()));
        assert!(set.iter().all(is_marked));
        // `collect()` adds one by one: the first of two equal types stays.
        let set = of(&[marked(&int), int.clone()]);
        assert_eq!(set.len(), 1);
        assert!(set.iter().all(is_marked));
        // `of_list` on more than five elements keeps the first one too
        // (`List.sort_uniq`).
        let mut l = vec![var(5), var(4), marked(&int), var(3), int.clone(), var(2), var(1)];
        let set = of_list(l.clone());
        assert_eq!(set.len(), 6);
        assert!(set.iter().filter(|ty| is_marked(ty)).count() == 1);
        l.swap(2, 4);
        let set = of_list(l);
        assert_eq!(set.len(), 6);
        assert!(set.iter().all(|ty| !is_marked(ty)));
    }

    #[test]
    fn remove() {
        let (tys, sorted) = sample();
        let mut set = of(&tys);
        assert!(!set.remove(&var(99)));
        // Removing ignores reasons, like every comparison.
        assert!(set.remove(&marked(&prim(Tprim::Tint))));
        assert!(!set.remove(&prim(Tprim::Tint)));
        stdlib_set::check_invariants(&set);
        assert_eq!(set.len(), tys.len() - 1);
        let expected: Vec<Ty> = sorted
            .iter()
            .filter(|ty| **ty != prim(Tprim::Tint))
            .cloned()
            .collect();
        assert_eq!(elements(&set), expected);
        // The functional form leaves its argument alone.
        let set2 = super::remove(&var(1), &set);
        assert_eq!(set2.len(), set.len() - 1);
        assert!(set.contains(&var(1)));
        for ty in &tys {
            set.remove(ty);
            stdlib_set::check_invariants(&set);
        }
        assert!(set.is_empty());
    }

    #[test]
    fn subset_union_inter_diff() {
        let a = of(&[var(1), var(2), var(3)]);
        let b = of(&[var(2), var(3), var(4), var(5)]);
        let empty = T::default();
        assert!(empty.is_subset(&a));
        assert!(!a.is_subset(&empty));
        assert!(a.is_subset(&a));
        assert!(!a.is_subset(&b));
        assert!(of(&[var(3), var(2)]).is_subset(&a));
        assert!(subset(&of(&[var(3), var(2)]), &b));
        assert!(!of(&[var(3), var(9)]).is_subset(&b));

        let u = union(&a, &b);
        stdlib_set::check_invariants(&u);
        assert_eq!(elements(&u), vec![var(1), var(2), var(3), var(4), var(5)]);
        assert_eq!(elements(&union(&a, &empty)), elements(&a));
        assert_eq!(elements(&union(&empty, &b)), elements(&b));

        let i = inter(&a, &b);
        stdlib_set::check_invariants(&i);
        assert_eq!(elements(&i), vec![var(2), var(3)]);
        assert!(inter(&a, &empty).is_empty());
        assert!(inter(&a, &of(&[var(7)])).is_empty());

        let d = diff(&a, &b);
        assert_eq!(elements(&d), vec![var(1)]);
        assert_eq!(elements(&diff(&b, &a)), vec![var(4), var(5)]);

        // The arguments are not modified (the sets are persistent).
        assert_eq!(a.len(), 3);
        assert_eq!(b.len(), 4);
    }

    /// Which of two types that differ only by their reason a `union` and an
    /// `inter` keep: what `set.ml` does.
    #[test]
    fn union_and_inter_keep_the_reasons_that_ocaml_keeps() {
        let int = prim(Tprim::Tint);
        let float = prim(Tprim::Tfloat);
        let m_int = marked(&int);

        // h1 >= h2 and h2 = 1: `add v2 s1`, the element of `s1` stays.
        let u = union(&of(&[int.clone()]), &of(&[m_int.clone()]));
        assert_eq!(u.len(), 1);
        assert!(u.iter().all(|ty| !is_marked(ty)));
        let u = union(&of(&[m_int.clone()]), &of(&[int.clone()]));
        assert!(u.iter().all(is_marked));
        let u = union(&of(&[m_int.clone(), float.clone()]), &of(&[int.clone()]));
        assert_eq!(u.len(), 2);
        assert_eq!(u.iter().filter(|ty| is_marked(ty)).count(), 1);

        // h1 < h2 and h1 = 1: `add v1 s2`, the element of `s2` stays.
        let u = union(&of(&[m_int.clone()]), &of(&[int.clone(), float.clone()]));
        assert_eq!(u.len(), 2);
        assert!(u.iter().all(|ty| !is_marked(ty)));

        // Two trees of height 2: the root of `s1` is kept, and below it the
        // rest of `s1` is a singleton that is added to what is left of `s2`.
        // `s1 = (. int (float))`, `s2 = ((m_int) m_float .)`.
        let m_float = marked(&float);
        let (lo, hi) = if ty_::compare(&int, &float) == Ordering::Less {
            (int.clone(), float.clone())
        } else {
            (float.clone(), int.clone())
        };
        let s1 = of(&[lo.clone(), hi.clone()]);
        let s2 = of(&[marked(&hi), marked(&lo)]);
        let u = union(&s1, &s2);
        assert_eq!(u.len(), 2);
        assert!(u.iter().all(|ty| !is_marked(ty)));
        let u = union(&s2, &s1);
        assert!(u.iter().all(is_marked));
        let _ = (m_float, m_int);

        // `inter s1 s2` has the elements of `s1`.
        let i = inter(
            &of(&[marked(&int), float.clone(), var(1)]),
            &of(&[int.clone(), marked(&float), var(2)]),
        );
        assert_eq!(i.len(), 2);
        let int_of_i = i.iter().find(|ty| **ty == int).unwrap();
        let float_of_i = i.iter().find(|ty| **ty == float).unwrap();
        assert!(is_marked(int_of_i));
        assert!(!is_marked(float_of_i));
    }

    #[test]
    fn filter_map_partition_exists() {
        let set = of(&[var(1), var(2), var(3), var(4), var(5), var(6)]);
        let n = |ty: &Ty| match get_node(ty) {
            Ty_::Tvar(n) => *n,
            _ => panic!(),
        };
        let even = filter(|ty| n(ty) % 2 == 0, &set);
        stdlib_set::check_invariants(&even);
        assert_eq!(elements(&even), vec![var(2), var(4), var(6)]);
        let (small, large) = partition(|ty| n(ty) <= 2, &set);
        assert_eq!(elements(&small), vec![var(1), var(2)]);
        assert_eq!(elements(&large), vec![var(3), var(4), var(5), var(6)]);
        assert!(exists(|ty| n(ty) == 6, &set));
        assert!(!exists(|ty| n(ty) == 7, &set));
        assert!(for_all(|ty| n(ty) > 0, &set));
        assert!(!for_all(|ty| n(ty) > 1, &set));
        assert_eq!(find_first_opt(|ty| n(ty) >= 4, &set), Some(var(4)));
        assert_eq!(find_first_opt(|ty| n(ty) >= 7, &set), None);
        // A map that reverses the order, and one that merges elements.
        let neg = map(|ty| var(-n(ty)), &set);
        stdlib_set::check_invariants(&neg);
        assert_eq!(
            elements(&neg),
            vec![var(-6), var(-5), var(-4), var(-3), var(-2), var(-1)]
        );
        let halves = map(|ty| var(n(ty) / 2), &set);
        stdlib_set::check_invariants(&halves);
        assert_eq!(elements(&halves), vec![var(0), var(1), var(2), var(3)]);
        // The order in which the predicates are called: increasing for
        // `filter`, the tree's (root first) for `exists`.
        let mut order = vec![];
        let _ = filter(
            |ty| {
                order.push(n(ty));
                true
            },
            &set,
        );
        assert_eq!(order, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn hash_and_debug_follow_the_elements() {
        use std::hash::Hash;
        use std::hash::Hasher;
        fn hash(set: &T) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            set.hash(&mut h);
            h.finish()
        }
        let (tys, _) = sample();
        let mut rev = tys.clone();
        rev.reverse();
        // Equal sets with different trees.
        let a = of(&tys);
        let b = of(&rev);
        assert_eq!(a, b);
        assert_eq!(hash(&a), hash(&b));
        assert_ne!(hash(&a), hash(&T::default()));
        assert_eq!(format!("{:?}", T::default()), "{}");
        assert_eq!(compare(&T::default(), &a), Ordering::Less);
        assert_eq!(compare(&a, &b), Ordering::Equal);
    }

    #[test]
    fn force_lazy_values_maps_as_ocaml() {
        let (tys, sorted) = sample();
        let set = of(&tys);
        let show = |ty: &Ty| format!("{:?}", get_node(ty));
        let forced = force_lazy_values(set.clone());
        stdlib_set::check_invariants(&forced);
        assert_eq!(elements(&forced), sorted);
        // The type mapper makes a new type for every element, so this is
        // `Set.map` with a function that allocates: every node is rebuilt
        // with `try_join`, which here gives another tree (as the tests on
        // integers below show OCaml does).
        let copied = map(|ty| ty.clone(), &set);
        assert_eq!(
            stdlib_set::dump(&show, &forced),
            stdlib_set::dump(&show, &copied)
        );
        assert_ne!(stdlib_set::dump(&show, &forced), stdlib_set::dump(&show, &set));
        // A function that gives every element back keeps the tree.
        let kept = map_phys(|_| None, &set);
        assert!(stdlib_set::same_tree(&kept, &set));
    }

    // -- The trees are those of `set.ml` -------------------------------------

    impl stdlib_set::OrderedType for (i32, char) {
        /// Like the order on types: the second component is ignored.
        fn compare(a: &Self, b: &Self) -> Ordering {
            a.0.cmp(&b.0)
        }
    }

    type S = stdlib_set::Set<(i32, char)>;

    fn dump(s: &S) -> String {
        stdlib_set::check_invariants(s);
        stdlib_set::dump(&|(n, c)| format!("{}{}", n, c), s)
    }

    fn s(tag: char, l: &[i32]) -> S {
        l.iter().map(|n| (*n, tag)).collect()
    }

    /// Expected values from OCaml 5 (`Set.Make` over pairs compared on their
    /// first component), printed with the same `dump`.
    #[test]
    fn trees_are_those_of_ocaml() {
        // Successive `add`s: rotations.
        assert_eq!(dump(&s('a', &[1, 2, 3, 4, 5, 6, 7])), OCAML_ADD_1_TO_7);
        assert_eq!(dump(&s('a', &[7, 6, 5, 4, 3, 2, 1])), OCAML_ADD_7_TO_1);
        assert_eq!(dump(&s('a', &[4, 1, 6, 2, 9, 3, 8, 5, 7, 0])), OCAML_ADD_MIXED);
        // `of_list` on more than five elements.
        assert_eq!(
            dump(&stdlib_set::of_list(
                [4, 1, 6, 2, 9, 3, 8, 5, 7, 0, 4, 1]
                    .iter()
                    .enumerate()
                    .map(|(i, n)| (*n, (b'a' + i as u8) as char))
                    .collect()
            )),
            OCAML_OF_LIST
        );
        // `union`: which duplicate survives.
        let a = s('a', &[1, 2, 3, 4, 5, 6, 7, 8]);
        let b = s('b', &[2, 4, 6, 8, 10, 12]);
        assert_eq!(dump(&stdlib_set::union(&a, &b)), OCAML_UNION_A_B);
        assert_eq!(dump(&stdlib_set::union(&b, &a)), OCAML_UNION_B_A);
        let c = s('c', &[5, 3, 9]);
        assert_eq!(dump(&stdlib_set::union(&c, &a)), OCAML_UNION_C_A);
        assert_eq!(dump(&stdlib_set::union(&a, &c)), OCAML_UNION_A_C);
        assert_eq!(dump(&stdlib_set::inter(&a, &b)), OCAML_INTER_A_B);
        assert_eq!(dump(&stdlib_set::inter(&b, &a)), OCAML_INTER_B_A);
        assert_eq!(dump(&stdlib_set::diff(&a, &b)), OCAML_DIFF_A_B);
        assert_eq!(dump(&stdlib_set::diff(&b, &a)), OCAML_DIFF_B_A);
        assert_eq!(
            dump(&stdlib_set::remove(&(4, 'z'), &a)),
            OCAML_REMOVE_4_A
        );
        assert_eq!(
            dump(&stdlib_set::filter(|(n, _)| n % 3 != 0, &a)),
            OCAML_FILTER_A
        );
        assert_eq!(
            dump(&stdlib_set::map(|(n, c)| (n / 2, *c), &a)),
            OCAML_MAP_HALF_A
        );
        assert_eq!(
            dump(&stdlib_set::map(|(n, c)| (10 - n, *c), &a)),
            OCAML_MAP_REV_A
        );
        let (t, f) = stdlib_set::partition(|(n, _)| *n < 4, &a);
        assert_eq!(format!("{} {}", dump(&t), dump(&f)), OCAML_PARTITION_A);
        // `map` and `map_phys`: OCaml keeps the nodes in which `f` gave every
        // element back (`v == v'`), and rebuilds the others with `try_join`.
        assert_eq!(dump(&a), OCAML_A);
        // `fun (n, c) -> (n, c)`: new values, another tree.
        assert_eq!(dump(&stdlib_set::map(|(n, c)| (*n, *c), &a)), OCAML_MAP_COPY_A);
        // `fun x -> x`: the same set.
        let same = stdlib_set::map_phys(|_| None, &a);
        assert_eq!(dump(&same), OCAML_MAP_PHYS_ID_A);
        assert!(stdlib_set::same_tree(&same, &a));
        // `fun ((n, _) as x) -> if n mod 3 = 0 then (n, 'z') else x`
        assert_eq!(
            dump(&stdlib_set::map_phys(
                |(n, _)| if n % 3 == 0 { Some((*n, 'z')) } else { None },
                &a
            )),
            OCAML_MAP_PHYS_MIXED_A
        );
        // `fun ((n, _) as x) -> if n = 4 then (9, 'z') else x`
        assert_eq!(
            dump(&stdlib_set::map_phys(
                |(n, _)| if *n == 4 { Some((9, 'z')) } else { None },
                &a
            )),
            OCAML_MAP_PHYS_MOVE_A
        );
    }

    const OCAML_A: &str = "(((. 1a .) 2a (. 3a .)) 4a ((. 5a .) 6a (. 7a (. 8a .))))";
    const OCAML_MAP_COPY_A: &str = "(((. 1a .) 2a (. 3a .)) 4a ((. 5a .) 6a ((. 7a .) 8a .)))";
    const OCAML_MAP_PHYS_ID_A: &str = OCAML_A;
    const OCAML_MAP_PHYS_MIXED_A: &str =
        "(((. 1a .) 2a (. 3z .)) 4a ((. 5a .) 6z (. 7a (. 8a .))))";
    const OCAML_MAP_PHYS_MOVE_A: &str =
        "(((. 1a .) 2a (. 3a (. 5a .))) 6a (. 7a (. 8a (. 9z .))))";

    const OCAML_ADD_1_TO_7: &str = "(((. 1a .) 2a (. 3a .)) 4a (. 5a (. 6a (. 7a .))))";
    const OCAML_ADD_7_TO_1: &str = "((((. 1a .) 2a .) 3a .) 4a ((. 5a .) 6a (. 7a .)))";
    const OCAML_ADD_MIXED: &str =
        "(((. 0a .) 1a (. 2a (. 3a .))) 4a ((. 5a .) 6a (((. 7a .) 8a .) 9a .)))";
    const OCAML_OF_LIST: &str =
        "((((. 0j .) 1b .) 2d ((. 3f .) 4a .)) 5h (((. 6c .) 7i .) 8g (. 9e .)))";
    const OCAML_UNION_A_B: &str =
        "(((. 1a .) 2a (. 3a .)) 4a ((. 5a .) 6a (((. 7a .) 8b .) 10b (. 12b .))))";
    const OCAML_UNION_B_A: &str =
        "(((. 1a .) 2a (. 3a .)) 4b (((. 5a .) 6a (. 7a .)) 8b (. 10b (. 12b .))))";
    const OCAML_UNION_C_A: &str =
        "(((. 1a .) 2a (. 3a .)) 4a ((. 5c .) 6a (. 7a (. 8a (. 9c .)))))";
    const OCAML_UNION_A_C: &str =
        "(((. 1a .) 2a (. 3a .)) 4a ((. 5a .) 6a (. 7a (. 8a (. 9c .)))))";
    const OCAML_INTER_A_B: &str = "((. 2a .) 4a ((. 6a .) 8a .))";
    const OCAML_INTER_B_A: &str = "((. 2b .) 4b (. 6b (. 8b .)))";
    const OCAML_DIFF_A_B: &str = "((. 1a (. 3a .)) 5a (. 7a .))";
    const OCAML_DIFF_B_A: &str = "(. 10b (. 12b .))";
    const OCAML_REMOVE_4_A: &str = "(((. 1a .) 2a (. 3a .)) 5a (. 6a (. 7a (. 8a .))))";
    const OCAML_FILTER_A: &str = "((. 1a (. 2a .)) 4a ((. 5a .) 7a (. 8a .)))";
    const OCAML_MAP_HALF_A: &str = "((. 0a .) 1a (. 2a (. 3a (. 4a .))))";
    const OCAML_MAP_REV_A: &str = "(((. 2a .) 3a ((. 4a .) 5a .)) 6a ((. 7a .) 8a (. 9a .)))";
    const OCAML_PARTITION_A: &str =
        "((. 1a .) 2a (. 3a .)) (((. 4a .) 5a .) 6a ((. 7a .) 8a .))";

    /// 20000 pseudo-random operations (`add`, `remove`, `union`, `inter`,
    /// `diff`, `filter`, `partition`, `of_list`, `map` with new values, and
    /// `map` with a function that gives some or all elements back) on six sets
    /// of up to 66 elements. After each one, the trees of two of the sets
    /// (elements and shapes) and the results of the queries go into a
    /// checksum, which is compared at four points with the checksum that the
    /// same program gives in OCaml 5 with `Set.Make`.
    #[test]
    fn random_operations_give_the_trees_of_ocaml() {
        let mut state: u64 = 12345;
        let mut rnd = move || {
            state = (state * 1103515245 + 12345) & 0x7fffffff;
            (state >> 8) as usize
        };
        fn mix(h: &mut u64, n: u64) {
            *h = (*h * 131 + n) % 1000000007;
        }
        fn mix_set(h: &mut u64, s: &S) {
            for c in dump(s).bytes() {
                mix(h, c as u64);
            }
            mix(h, stdlib_set::cardinal(s) as u64);
        }
        let mut pool: Vec<S> = vec![S::default(); 6];
        let mut h: u64 = 7;
        let mut checkpoints = vec![];
        for step in 1..=20000usize {
            let op = rnd() % 16;
            let i = rnd() % 6;
            let j = rnd() % 6;
            let k = rnd() % 6;
            let n = (rnd() % 64) as i32;
            let tag = (97 + (step % 26)) as u8 as char;
            match op {
                0..=6 => pool[k] = stdlib_set::add((n, tag), &pool[i]),
                7 => pool[k] = stdlib_set::remove(&(n, tag), &pool[i]),
                8..=10 => pool[k] = stdlib_set::union(&pool[i], &pool[j]),
                11 => pool[k] = stdlib_set::inter(&pool[i], &pool[j]),
                12 => pool[k] = stdlib_set::diff(&pool[i], &pool[j]),
                13 => pool[k] = stdlib_set::filter(|(m, _)| m % 5 != n % 5, &pool[i]),
                _ => match n % 5 {
                    0 => pool[k] = stdlib_set::map(|(m, c)| (m * 7 % 61, *c), &pool[i]),
                    1 => {
                        let (a, b) = stdlib_set::partition(|(m, _)| *m < n, &pool[i]);
                        pool[k] = a;
                        pool[j] = b;
                    }
                    2 => {
                        let mut l = stdlib_set::elements(&pool[i]);
                        l.extend(stdlib_set::elements(&pool[j]));
                        pool[k] = stdlib_set::of_list(
                            l.into_iter().map(|(m, c)| ((m * 3 + n) % 67, c)).collect(),
                        );
                    }
                    // `S.map (fun x -> x)`
                    3 => pool[k] = stdlib_set::map_phys(|_| None, &pool[i]),
                    // `S.map (fun ((m, _) as x) ->
                    //    if m mod 3 = n mod 3 then ((m * 5) mod 67, 'z') else x)`
                    _ => {
                        pool[k] = stdlib_set::map_phys(
                            |(m, _)| {
                                if m % 3 == n % 3 {
                                    Some(((m * 5) % 67, 'z'))
                                } else {
                                    None
                                }
                            },
                            &pool[i],
                        )
                    }
                },
            }
            mix_set(&mut h, &pool[k]);
            mix_set(&mut h, &pool[j]);
            mix(&mut h, stdlib_set::subset(&pool[i], &pool[j]) as u64);
            mix(&mut h, stdlib_set::equal(&pool[i], &pool[k]) as u64);
            mix(
                &mut h,
                match stdlib_set::compare(&pool[j], &pool[k]) {
                    Ordering::Less => 0,
                    Ordering::Equal => 1,
                    Ordering::Greater => 2,
                },
            );
            mix(&mut h, stdlib_set::mem(&(n, 'z'), &pool[i]) as u64);
            match stdlib_set::find_first_opt(|(m, _)| *m >= n, &pool[k]) {
                None => mix(&mut h, 0),
                Some((m, c)) => mix(&mut h, m as u64 + c as u64),
            }
            match (
                stdlib_set::min_elt_opt(&pool[k]),
                stdlib_set::max_elt_opt(&pool[k]),
            ) {
                (Some((m, c)), Some((m2, c2))) => {
                    mix(&mut h, m as u64 + c as u64 + m2 as u64 + c2 as u64)
                }
                _ => mix(&mut h, 0),
            }
            mix(&mut h, stdlib_set::exists(|(m, _)| *m == n, &pool[j]) as u64);
            mix(&mut h, stdlib_set::for_all(|(m, _)| *m != n, &pool[j]) as u64);
            // The methods agree with the functions.
            assert_eq!(pool[i].is_subset(&pool[j]), stdlib_set::subset(&pool[i], &pool[j]));
            assert_eq!(pool[k].len() as isize, stdlib_set::cardinal(&pool[k]));
            if [100, 1000, 5000, 20000].contains(&step) {
                checkpoints.push((step, h));
            }
        }
        assert_eq!(
            checkpoints,
            vec![
                (100, 60129265),
                (1000, 103933321),
                (5000, 607383386),
                (20000, 971664471)
            ]
        );
    }
}
