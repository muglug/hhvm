// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `partition.ml`. See `hh/PORTING.md`.
//!
//! `Partition.Make (Atom)` is the type [`Make<Atom>`] (see
//! `crate::partition_intf` for how the module types map): the type is both
//! the module and its type `t`, and the functions of the module are its
//! associated functions. So
//!
//! ```ignore
//! module Partition = Partition.Make (struct
//!   type t = locl_ty
//!   let compare = Typing_defs.compare_locl_ty ~normalize_lists:true
//! end)
//! ... Partition.join p1 p2 ... Partition.t ...
//! ```
//!
//! is
//!
//! ```ignore
//! struct LoclTyAtom;
//! impl partition::OrderedType for LoclTyAtom {
//!     type T = Ty;
//!     fn compare(t1: &Ty, t2: &Ty) -> Ordering {
//!         typing_defs_core::compare_locl_ty(Some(true), t1, t2)
//!     }
//! }
//! type Partition = partition::Make<LoclTyAtom>;
//! ... Partition::join(&p1, &p2) ... Partition ...
//! ```
//!
//! `Conjunction` and `Disjunction` (`Stdlib.Set.Make`) are
//! `crate::typing_set::stdlib_set`, which is `set.ml` tree for tree:
//! `Atom.compare` can say that two atoms that differ are equal (two types
//! that differ only by their reasons), and then which of the two a set keeps
//! depends on the shapes of the trees `set.ml` builds.

pub use crate::partition_intf::Dnf;
pub use crate::partition_intf::OrderedType;
pub use crate::partition_intf::S;
use crate::typing_set::stdlib_set;

/// Compute the cartesian product of lists
pub fn cartesian<A: Clone>(xss: &[Vec<A>]) -> Vec<Vec<A>> {
    fn aux<A: Clone>(xss: &[Vec<A>], k: &dyn Fn(Vec<Vec<A>>) -> Vec<Vec<A>>) -> Vec<Vec<A>> {
        match xss {
            // Product of the empty list is a single empty list
            [] => k(vec![vec![]]),
            [xs, xss @ ..] => {
                // Get the cartesian product of the tail lists
                aux(xss, &|xss| {
                    // Then, for each element in the head list,
                    // we cons to each list in the product of the tail
                    // e.g. if we had [1;2] :: [3] :: []  then we find the
                    // cartesian product of [3] :: [] === [[3]] then map over
                    // the head list ([1;2]) prepending it to that product,
                    // i.e. [[1;3];[2;3]]
                    k(auxs(xs, &xss))
                })
            }
        }
    }
    // `auxs xs xss []`. The accumulator, a list that the OCaml conses onto
    // and reverses at the end, is a vector pushed onto: it is in the order of
    // the reversed list.
    fn auxs<A: Clone>(xs: &[A], xss: &[Vec<A>]) -> Vec<Vec<A>> {
        let mut acc = Vec::new();
        for x in xs {
            // List.fold_left (fun acc xs -> (x :: xs) :: acc) acc xss
            for xs in xss {
                let mut x_xs = Vec::with_capacity(xs.len() + 1);
                x_xs.push(x.clone());
                x_xs.extend(xs.iter().cloned());
                acc.push(x_xs);
            }
        }
        acc
    }
    aux(xss, &|x| x)
}

/// `module Conjunction = Stdlib.Set.Make (Atom)`: the functions of `Set.S`
/// that are used, on the atoms themselves.
mod conjunction {
    use std::cmp::Ordering;

    use super::OrderedType;
    use super::stdlib_set;

    /// An atom, ordered by `Atom.compare`.
    pub struct Elt<A: OrderedType>(pub A::T);

    impl<A: OrderedType> Clone for Elt<A> {
        fn clone(&self) -> Self {
            Elt(self.0.clone())
        }
    }

    impl<A: OrderedType> stdlib_set::OrderedType for Elt<A> {
        fn compare(a: &Self, b: &Self) -> Ordering {
            A::compare(&a.0, &b.0)
        }
    }

    pub type T<A> = stdlib_set::Set<Elt<A>>;

    pub fn empty<A: OrderedType>() -> T<A> {
        stdlib_set::empty()
    }

    pub fn is_empty<A: OrderedType>(s: &T<A>) -> bool {
        stdlib_set::is_empty(s)
    }

    pub fn singleton<A: OrderedType>(atom: A::T) -> T<A> {
        stdlib_set::singleton(Elt(atom))
    }

    pub fn union<A: OrderedType>(s1: &T<A>, s2: &T<A>) -> T<A> {
        stdlib_set::union(s1, s2)
    }

    /// `union s1 s2`, or `None` when that is `s1` itself (OCaml's `==`, as
    /// `Set.map` tests it). `set.ml`'s `union` gives back `s1` when `s2` is
    /// empty, and when `s2` is a single element (a tree of height 1, which
    /// is not taller than `s1`) that `s1` already has (`add v2 s1`); every
    /// other case builds a new tree.
    pub fn union_phys<A: OrderedType>(s1: &T<A>, s2: &T<A>) -> Option<T<A>> {
        let is_s1 = stdlib_set::is_empty(s2)
            || (stdlib_set::cardinal(s2) == 1
                && !stdlib_set::is_empty(s1)
                && s2.iter().all(|v2| stdlib_set::mem(v2, s1)));
        if is_s1 { None } else { Some(union(s1, s2)) }
    }

    pub fn elements<A: OrderedType>(s: &T<A>) -> Vec<A::T> {
        s.iter().map(|elt| elt.0.clone()).collect()
    }

    pub fn compare<A: OrderedType>(s1: &T<A>, s2: &T<A>) -> Ordering {
        stdlib_set::compare(s1, s2)
    }
}

/// `module Disjunction = Stdlib.Set.Make (Conjunction)`: the functions of
/// `Set.S` that are used, on the conjunctions themselves.
mod disjunction {
    use std::cmp::Ordering;

    use super::OrderedType;
    use super::conjunction;
    use super::stdlib_set;

    /// A conjunction, ordered by `Conjunction.compare`.
    pub struct Elt<A: OrderedType>(pub conjunction::T<A>);

    impl<A: OrderedType> Clone for Elt<A> {
        fn clone(&self) -> Self {
            Elt(self.0.clone())
        }
    }

    impl<A: OrderedType> stdlib_set::OrderedType for Elt<A> {
        fn compare(a: &Self, b: &Self) -> Ordering {
            conjunction::compare(&a.0, &b.0)
        }
    }

    pub type T<A> = stdlib_set::Set<Elt<A>>;

    pub fn empty<A: OrderedType>() -> T<A> {
        stdlib_set::empty()
    }

    pub fn is_empty<A: OrderedType>(s: &T<A>) -> bool {
        stdlib_set::is_empty(s)
    }

    pub fn singleton<A: OrderedType>(conj: conjunction::T<A>) -> T<A> {
        stdlib_set::singleton(Elt(conj))
    }

    pub fn add<A: OrderedType>(conj: conjunction::T<A>, s: &T<A>) -> T<A> {
        stdlib_set::add(Elt(conj), s)
    }

    pub fn union<A: OrderedType>(s1: &T<A>, s2: &T<A>) -> T<A> {
        stdlib_set::union(s1, s2)
    }

    pub fn of_list<A: OrderedType>(l: Vec<conjunction::T<A>>) -> T<A> {
        stdlib_set::of_list(l.into_iter().map(Elt).collect())
    }

    pub fn elements<A: OrderedType>(s: &T<A>) -> Vec<conjunction::T<A>> {
        s.iter().map(|elt| elt.0.clone()).collect()
    }

    /// `map f s`, where `f` gives `None` for an element that it gives back
    /// itself (`==`): as in OCaml, a node in which nothing changed is kept.
    pub fn map_phys<A: OrderedType>(
        mut f: impl FnMut(&conjunction::T<A>) -> Option<conjunction::T<A>>,
        s: &T<A>,
    ) -> T<A> {
        stdlib_set::map_phys(|elt: &Elt<A>| f(&elt.0).map(Elt), s)
    }

    pub fn fold<A: OrderedType, B>(
        mut f: impl FnMut(&conjunction::T<A>, B) -> B,
        s: &T<A>,
        accu: B,
    ) -> B {
        stdlib_set::fold(|elt: &Elt<A>, accu| f(&elt.0, accu), s, accu)
    }
}

/// Represents union and intersection across [atom] in
/// disjunctive normal form (DNF)
mod lattice {
    use super::Dnf;
    use super::OrderedType;
    use super::cartesian;
    use super::conjunction;
    use super::disjunction;

    /// Notable we lack logical negations in our representation
    pub enum T<A: OrderedType> {
        And(conjunction::T<A>),
        Or(disjunction::T<A>),
    }

    impl<A: OrderedType> Clone for T<A> {
        fn clone(&self) -> Self {
            match self {
                T::And(conj) => T::And(conj.clone()),
                T::Or(disj) => T::Or(disj.clone()),
            }
        }
    }

    /// The empty disjunction is the bottom type, i.e. "false"
    pub fn bottom<A: OrderedType>() -> T<A> {
        T::Or(disjunction::empty())
    }

    /// The empty conjunction is the top type, i.e. "true"
    pub fn top<A: OrderedType>() -> T<A> {
        T::And(conjunction::empty())
    }

    pub fn is_bottom<A: OrderedType>(t: &T<A>) -> bool {
        match t {
            T::Or(disjunction) if disjunction::is_empty(disjunction) => true,
            _ => false,
        }
    }

    pub fn singleton<A: OrderedType>(atom: A::T) -> T<A> {
        T::And(conjunction::singleton(atom))
    }

    /// Unions two abstract sets
    pub fn join<A: OrderedType>(set1: &T<A>, set2: &T<A>) -> T<A> {
        match (set1, set2) {
            // Top | A = Top
            (T::And(conj1), T::And(conj2))
                if conjunction::is_empty(conj1) || conjunction::is_empty(conj2) =>
            {
                top()
            }
            (T::And(conj1), T::And(conj2)) => {
                T::Or(disjunction::of_list(vec![conj1.clone(), conj2.clone()]))
            }
            // (A1 | A2) | B = (A1 | A2 | B)
            (T::And(conjunction), T::Or(disjunction))
            | (T::Or(disjunction), T::And(conjunction)) => {
                T::Or(disjunction::add(conjunction.clone(), disjunction))
            }
            // (A1 | A2) | (B1 | B2) = (A1 | A2 | B1 | B2)
            (T::Or(disj1), T::Or(disj2)) => T::Or(disjunction::union(disj1, disj2)),
        }
    }

    /// Intersects two abstract sets
    pub fn meet<A: OrderedType>(set1: &T<A>, set2: &T<A>) -> T<A> {
        let meet = |set1: &T<A>, conj2: &conjunction::T<A>| match set1 {
            T::And(conj1) => T::And(conjunction::union(conj1, conj2)),
            // `Disjunction.map (fun conj -> Conjunction.union conj conj2)`:
            // `Set.map` keeps the nodes whose element the function gives back
            // itself.
            T::Or(disj) => T::Or(disjunction::map_phys(
                |conj| conjunction::union_phys(conj, conj2),
                disj,
            )),
        };
        match set1 {
            T::And(conj) => meet(set2, conj),
            // (A1 | A2) & B = (A1 & B) | (A2 & B)
            T::Or(disj) => {
                // dedupe should occur in join
                disjunction::fold(|conj, set| join(&set, &meet(set2, conj)), disj, bottom())
            }
        }
    }

    /// The operators `( ||| )` and `( &&& )` (see `crate::partition_intf`).
    pub mod infix_ops {
        use super::OrderedType;
        use super::T;

        /// `( ||| )`
        pub fn or<A: OrderedType>(set1: &T<A>, set2: &T<A>) -> T<A> {
            super::join(set1, set2)
        }

        /// `( &&& )`
        pub fn and<A: OrderedType>(set1: &T<A>, set2: &T<A>) -> T<A> {
            super::meet(set1, set2)
        }
    }

    pub fn to_list<A: OrderedType>(t: &T<A>) -> Dnf<A::T> {
        match t {
            T::And(conjunction) => vec![conjunction::elements(conjunction)],
            T::Or(disjunction) => disjunction::elements(disjunction)
                .iter()
                .map(|conj| conjunction::elements(conj))
                .collect(),
        }
    }

    /// This function computes a product of N-lattices by pushing the product
    /// operation through the DNF such that the resulting lattice
    /// is a DNF of N-ary product of atoms
    /// (and each product of atoms is converted into an atom via product_f).
    ///
    /// This pushing and conversion is done by the N-ary extrapolation of the
    /// following:
    ///
    /// A = a_0 | a_1 | ... | a_n
    ///   a_i = a_i_0 & a_i_1 & ... & a_i_xi
    /// B = b_0 | b_1 | ... | b_m
    ///   b_i = b_i_0 & b_i_1 & ... & b_i_yi
    ///
    /// A x B = or(for all i=0..n, j=0..m : a_i x b_j)
    ///   a_i x b_j = and(for all k=0..xi, l=0..yi : product_f [a_i_k; b_j_l])
    pub fn product<A: OrderedType>(product_f: &dyn Fn(Vec<A::T>) -> A::T, tl: &[T<A>]) -> T<A> {
        let product_of_conjunctions = |conjunctions: &[conjunction::T<A>]| {
            let product_elts: Vec<A::T> = cartesian(
                &conjunctions
                    .iter()
                    .map(conjunction::elements)
                    .collect::<Vec<_>>(),
            )
            .into_iter()
            .map(product_f)
            .collect();
            let sets: Vec<T<A>> = product_elts.into_iter().map(singleton).collect();
            sets.iter().fold(top(), |acc, set| meet(&acc, set))
        };
        let product_of_disjunctions = |disjunctions: &[disjunction::T<A>]| {
            let product_elts = cartesian(
                &disjunctions
                    .iter()
                    .map(disjunction::elements)
                    .collect::<Vec<_>>(),
            );
            let products: Vec<T<A>> = product_elts
                .iter()
                .map(|conjunctions| product_of_conjunctions(conjunctions))
                .collect();
            products.iter().fold(bottom(), |acc, t| join(&acc, t))
        };
        let to_disjunction = |t: &T<A>| match t {
            T::And(conjunction) => disjunction::singleton(conjunction.clone()),
            T::Or(disjunction) => disjunction.clone(),
        };
        product_of_disjunctions(&tl.iter().map(to_disjunction).collect::<Vec<_>>())
    }
}

use lattice::infix_ops::and;
use lattice::infix_ops::or;

/// `Make (Atom)`, and its type `t`. [left] is disjoint from [right], while
/// [span] overlaps partitially with [left] and [right]
pub struct Make<A: OrderedType> {
    left: lattice::T<A>,
    span: lattice::T<A>,
    right: lattice::T<A>,
}

impl<A: OrderedType> Clone for Make<A> {
    fn clone(&self) -> Self {
        Make {
            left: self.left.clone(),
            span: self.span.clone(),
            right: self.right.clone(),
        }
    }
}

impl<A: OrderedType> Make<A> {
    pub fn mk_bottom() -> Self {
        Make {
            left: lattice::bottom(),
            span: lattice::bottom(),
            right: lattice::bottom(),
        }
    }

    pub fn mk_left(atom: A::T) -> Self {
        Make {
            left: lattice::singleton(atom),
            span: lattice::bottom(),
            right: lattice::bottom(),
        }
    }

    pub fn mk_right(atom: A::T) -> Self {
        Make {
            left: lattice::bottom(),
            span: lattice::bottom(),
            right: lattice::singleton(atom),
        }
    }

    pub fn mk_span(atom: A::T) -> Self {
        Make {
            left: lattice::bottom(),
            span: lattice::singleton(atom),
            right: lattice::bottom(),
        }
    }

    pub fn join(t1: &Self, t2: &Self) -> Self {
        let Make {
            left: left1,
            span: span1,
            right: right1,
        } = t1;
        let Make {
            left: left2,
            span: span2,
            right: right2,
        } = t2;
        Make {
            left: or(left1, left2),
            span: or(span1, span2),
            right: or(right1, right2),
        }
    }

    // A := Al | As | Ar
    // B := Bl | Bs | Br
    //
    // When computing A & B we have:
    // A & B => // Expand B
    //
    // A & (Bl | Bs | Br) => // Distribute across union
    //
    // (A & Bl) | (A & Bs) | (A & Br) => Expand A
    //
    // ((Al | As | Ar) & Bl) |
    //   ((Al | As | Ar) & Bs) |
    //   ((Al | As | Ar) & Br) => // Distribute across union
    //
    // (Al & Bl) | (As & Bl) | (Ar & Bl) |
    //   (Al & Bs) | (As & Bs) | (Ar & Bs) |
    //   (Al & Br) | (As & Br) | (Ar & Br)
    //     => // Al is disjoint from Br, Bl is disjoint from Ar
    //
    // (Al & Bl) | (As & Bl) | {} |
    //   (Al & Bs) | (As & Bs) | (Ar & Bs) |
    //   {} | (As & Br) | (Ar & Br) => // Simplify {}
    //
    // (Al & Bl) | (As & Bl) | (Al & Bs) | (As & Bs) | (Ar & Bs) | (As & Br) |
    //   (Ar & Br) => // Group Al, Bl together and Ar, Br together
    //
    // left = (Al & Bl) | (Bl & As) | (Al & Bs),
    // span = As & Bs,
    // right = (Ar & Bs) | (Br & As) | (Ar & Br)
    //
    // (`|||` and `&&&` have the same precedence and associate to the left:
    // `a &&& b ||| (c) ||| (d)` is `((a &&& b) ||| c) ||| d`.)
    pub fn meet(t1: &Self, t2: &Self) -> Self {
        let Make {
            left: left1,
            span: span1,
            right: right1,
        } = t1;
        let Make {
            left: left2,
            span: span2,
            right: right2,
        } = t2;
        Make {
            left: or(
                &or(&and(left1, left2), &and(left1, span2)),
                &and(left2, span1),
            ),
            span: and(span1, span2),
            right: or(
                &or(&and(right1, right2), &and(right1, span2)),
                &and(right2, span1),
            ),
        }
    }

    // Combines two partitions using the algebra for union predicates.
    //
    // When combining partitions P1 and P2 for union predicates (P1 | P2):
    // - left: passes at least one predicate = L1 | L2
    // - right: fails both predicates = R1 & R2
    // - span: uncertain (not definitely left or right) = (S1 & S2) | (S1 & R2) | (R1 & S2)
    //
    // This is different from regular join which does component-wise union.
    pub fn union_combine(t1: &Self, t2: &Self) -> Self {
        let Make {
            left: left1,
            span: span1,
            right: right1,
        } = t1;
        let Make {
            left: left2,
            span: span2,
            right: right2,
        } = t2;
        Make {
            left: or(left1, left2),
            span: or(
                &or(&and(span1, span2), &and(span1, right2)),
                &and(right1, span2),
            ),
            right: and(right1, right2),
        }
    }

    /// If the partition is fully within the left, span or right we can
    /// simplify the DNF to be [set], otherwise return [t] unchanged
    pub fn simplify(t: &Self, atom: A::T) -> Self {
        match (
            lattice::is_bottom(&t.left),
            lattice::is_bottom(&t.span),
            lattice::is_bottom(&t.right),
        ) {
            (false, true, true) => Self::mk_left(atom),
            (true, false, true) => Self::mk_span(atom),
            (true, true, false) => Self::mk_right(atom),
            _ => t.clone(),
        }
    }

    pub fn left(t: &Self) -> Dnf<A::T> {
        lattice::to_list(&t.left)
    }

    pub fn span(t: &Self) -> Dnf<A::T> {
        lattice::to_list(&t.span)
    }

    pub fn right(t: &Self) -> Dnf<A::T> {
        lattice::to_list(&t.right)
    }

    pub fn flip(t: &Self) -> Self {
        let Make { left, span, right } = t;
        Make {
            left: right.clone(),
            span: span.clone(),
            right: left.clone(),
        }
    }

    // A := Al | As | Ar
    // B := Bl | Bs | Br
    // c := Cl | Cs | Cr
    //
    // When computing A x B x C we have:
    //
    // left = Al x Bl x Cl
    // span = (As x (B - Br) x (C - Cr)) |
    //        ((A - Ar) x Bs x (C - Cr)) |
    //        ((A - Ar) x (B - Br) x Cs)
    //      = (As x (Bl | Bs) x (Cl | Cs)) |
    //        ((Al | As) x Bs x (Cl | Cs)) |
    //        ((Al | As) x (Bl | Bs) x Cs)
    // right = (Ar x B x C) | (A x Br x C) | (A x B x Cr)
    //
    // This is:
    // - "left if ALL parts are left"
    // - "right if ANY parts are right"
    // - "span otherwise" which is
    //   "span if no parts are right and at least one part is not left"
    pub fn product(product_f: &dyn Fn(Vec<A::T>) -> A::T, tl: &[Self]) -> Self {
        let left_lattices: Vec<lattice::T<A>> = tl.iter().map(|t| t.left.clone()).collect();
        let span_lattices: Vec<lattice::T<A>> = tl.iter().map(|t| t.span.clone()).collect();
        let left_or_span_lattices: Vec<lattice::T<A>> =
            tl.iter().map(|t| lattice::join(&t.left, &t.span)).collect();
        let right_lattices: Vec<lattice::T<A>> = tl.iter().map(|t| t.right.clone()).collect();
        let full_lattices: Vec<lattice::T<A>> = tl
            .iter()
            .map(|t| or(&or(&t.left, &t.span), &t.right))
            .collect();
        let left = lattice::product(product_f, &left_lattices);
        // Given
        //   befores @ current_and_afters = [(a0, b0), (a1, b1) .. (an, bn)]
        // Return
        //   [product(a0, b1 .. bn), product(b0, a1, b2 .. bn) .. product(b0, b1 .. bn-1, an)]
        //
        // (As in the OCaml, `befores` is `List.rev (pair :: befores)` from
        // one element to the next, so from the fourth element on it is not
        // in the order of the list.)
        type Pair<A> = (lattice::T<A>, lattice::T<A>);
        fn helper<A: OrderedType>(
            product_f: &dyn Fn(Vec<A::T>) -> A::T,
            befores: Vec<Pair<A>>,
            current_and_afters: &[Pair<A>],
        ) -> Vec<lattice::T<A>> {
            match current_and_afters {
                [] => vec![],
                [pair, afters @ ..] => {
                    let (curr, _other) = pair;
                    let parts: Vec<lattice::T<A>> = befores
                        .iter()
                        .map(|(_curr, other)| other.clone())
                        .chain(std::iter::once(curr.clone()))
                        .chain(afters.iter().map(|(_curr, other)| other.clone()))
                        .collect();
                    // List.rev (pair :: befores)
                    let mut next_befores = Vec::with_capacity(befores.len() + 1);
                    next_befores.push(pair.clone());
                    next_befores.extend(befores);
                    next_befores.reverse();
                    if parts.iter().any(lattice::is_bottom) {
                        helper(product_f, next_befores, afters)
                    } else {
                        // `Lattice.product product_f parts :: helper ...`:
                        // OCaml evaluates the tail of the list first.
                        let rest = helper(product_f, next_befores, afters);
                        let first = lattice::product(product_f, &parts);
                        let mut result = Vec::with_capacity(rest.len() + 1);
                        result.push(first);
                        result.extend(rest);
                        result
                    }
                }
            }
        }
        let span_pairs: Vec<Pair<A>> = span_lattices
            .into_iter()
            .zip(left_or_span_lattices)
            .collect();
        let span = helper(product_f, vec![], &span_pairs)
            .iter()
            .fold(lattice::bottom(), |acc, t| lattice::join(&acc, t));
        let right_pairs: Vec<Pair<A>> = right_lattices.into_iter().zip(full_lattices).collect();
        let right = helper(product_f, vec![], &right_pairs)
            .iter()
            .fold(lattice::bottom(), |acc, t| lattice::join(&acc, t));
        Make { left, span, right }
    }
}

/// The operators `( ||| )` and `( &&& )` of `Make (Atom)` (see
/// `crate::partition_intf`).
pub mod infix_ops {
    use super::Make;
    use super::OrderedType;

    /// `( ||| )`
    pub fn or<A: OrderedType>(t1: &Make<A>, t2: &Make<A>) -> Make<A> {
        Make::join(t1, t2)
    }

    /// `( &&& )`
    pub fn and<A: OrderedType>(t1: &Make<A>, t2: &Make<A>) -> Make<A> {
        Make::meet(t1, t2)
    }
}

impl<A: OrderedType> S for Make<A> {
    type Atom = A::T;

    fn mk_bottom() -> Self {
        Make::<A>::mk_bottom()
    }

    fn mk_left(atom: A::T) -> Self {
        Make::<A>::mk_left(atom)
    }

    fn mk_right(atom: A::T) -> Self {
        Make::<A>::mk_right(atom)
    }

    fn mk_span(atom: A::T) -> Self {
        Make::<A>::mk_span(atom)
    }

    fn join(t1: &Self, t2: &Self) -> Self {
        Make::<A>::join(t1, t2)
    }

    fn meet(t1: &Self, t2: &Self) -> Self {
        Make::<A>::meet(t1, t2)
    }

    fn union_combine(t1: &Self, t2: &Self) -> Self {
        Make::<A>::union_combine(t1, t2)
    }

    fn simplify(t: &Self, atom: A::T) -> Self {
        Make::<A>::simplify(t, atom)
    }

    fn left(t: &Self) -> Dnf<A::T> {
        Make::<A>::left(t)
    }

    fn span(t: &Self) -> Dnf<A::T> {
        Make::<A>::span(t)
    }

    fn right(t: &Self) -> Dnf<A::T> {
        Make::<A>::right(t)
    }

    fn flip(t: &Self) -> Self {
        Make::<A>::flip(t)
    }

    fn product(product_f: &dyn Fn(Vec<A::T>) -> A::T, tl: &[Self]) -> Self {
        Make::<A>::product(product_f, tl)
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use super::*;

    /// Integers in their usual order.
    struct Int;

    impl OrderedType for Int {
        type T = i32;

        fn compare(t1: &i32, t2: &i32) -> Ordering {
            t1.cmp(t2)
        }
    }

    type P = Make<Int>;

    /// Strings in their usual order.
    struct Str;

    impl OrderedType for Str {
        type T = String;

        fn compare(t1: &String, t2: &String) -> Ordering {
            t1.cmp(t2)
        }
    }

    /// Pairs ordered by their first component only: two atoms can be equal
    /// and differ, as types that differ only by their reasons.
    struct Keyed;

    impl OrderedType for Keyed {
        type T = (i32, &'static str);

        fn compare(t1: &Self::T, t2: &Self::T) -> Ordering {
            t1.0.cmp(&t2.0)
        }
    }

    #[test]
    fn cartesian_products() {
        assert_eq!(cartesian::<i32>(&[]), vec![Vec::<i32>::new()]);
        assert_eq!(
            cartesian(&[vec![1, 2], vec![3]]),
            vec![vec![1, 3], vec![2, 3]]
        );
        assert_eq!(
            cartesian(&[vec![1, 2], vec![3, 4]]),
            vec![vec![1, 3], vec![1, 4], vec![2, 3], vec![2, 4]]
        );
        assert_eq!(cartesian(&[vec![1], vec![]]), Vec::<Vec<i32>>::new());
    }

    #[test]
    fn constructors_and_accessors() {
        let empty: Dnf<i32> = vec![];
        let l = P::mk_left(1);
        assert_eq!(
            (P::left(&l), P::span(&l), P::right(&l)),
            (vec![vec![1]], empty.clone(), empty.clone())
        );
        let r = P::flip(&l);
        assert_eq!(
            (P::left(&r), P::span(&r), P::right(&r)),
            (empty.clone(), empty.clone(), vec![vec![1]])
        );
        let b = P::mk_bottom();
        assert_eq!(
            (P::left(&b), P::span(&b), P::right(&b)),
            (empty.clone(), empty.clone(), empty.clone())
        );
        assert_eq!(P::span(&P::mk_span(2)), vec![vec![2]]);
        assert_eq!(P::right(&P::mk_right(3)), vec![vec![3]]);
    }

    #[test]
    fn join_and_meet() {
        let empty: Dnf<i32> = vec![];
        // Unions of atoms are disjunctions, in the order of the atoms.
        let j = P::join(&P::mk_left(2), &P::mk_left(1));
        assert_eq!(P::left(&j), vec![vec![1], vec![2]]);
        // Intersections of atoms are conjunctions.
        let m = P::meet(&P::mk_left(1), &P::mk_left(2));
        assert_eq!(
            (P::left(&m), P::span(&m), P::right(&m)),
            (vec![vec![1, 2]], empty.clone(), empty.clone())
        );
        // A left part met with a span is left: Al & Bs.
        let m = P::meet(&P::mk_left(1), &P::mk_span(2));
        assert_eq!(
            (P::left(&m), P::span(&m), P::right(&m)),
            (vec![vec![1, 2]], empty.clone(), empty.clone())
        );
        // Two spans meet in the span.
        let m = P::meet(&P::mk_span(1), &P::mk_span(2));
        assert_eq!(P::span(&m), vec![vec![1, 2]]);
        // A union of predicates: the right side is what fails both.
        let u = P::union_combine(&P::mk_right(1), &P::mk_right(2));
        assert_eq!(
            (P::left(&u), P::span(&u), P::right(&u)),
            (empty.clone(), empty.clone(), vec![vec![1, 2]])
        );
        let u = P::union_combine(&P::mk_left(1), &P::mk_right(2));
        assert_eq!(
            (P::left(&u), P::span(&u), P::right(&u)),
            (vec![vec![1]], empty.clone(), empty.clone())
        );
    }

    #[test]
    fn simplify() {
        let j = P::join(&P::mk_left(1), &P::mk_left(2));
        assert_eq!(P::left(&P::simplify(&j, 9)), vec![vec![9]]);
        let m = P::join(&P::mk_left(1), &P::mk_right(2));
        let s = P::simplify(&m, 9);
        assert_eq!(P::left(&s), vec![vec![1]]);
        assert_eq!(P::right(&s), vec![vec![2]]);
    }

    #[test]
    fn product_of_a_left_and_a_span_is_a_span() {
        let sum = |l: Vec<i32>| -> i32 { l.iter().sum() };
        let p = P::product(&sum, &[P::mk_left(1), P::mk_span(2)]);
        let empty: Dnf<i32> = vec![];
        assert_eq!(
            (P::left(&p), P::span(&p), P::right(&p)),
            (empty.clone(), vec![vec![3]], empty.clone())
        );
    }

    #[test]
    fn product_reorders_the_parts_from_the_fourth_on() {
        // `helper` keeps `List.rev (pair :: befores)`: the fourth product
        // takes the other parts as b1, b0, b2.
        let concat = |l: Vec<String>| l.concat();
        let parts: Vec<Make<Str>> = ["a", "b", "c", "d"]
            .iter()
            .map(|s| Make::<Str>::mk_right(s.to_string()))
            .collect();
        let p = Make::<Str>::product(&concat, &parts);
        assert_eq!(
            Make::<Str>::right(&p),
            vec![vec!["abcd".to_string()], vec!["bacd".to_string()]]
        );
        assert!(Make::<Str>::left(&p).is_empty());
        assert!(Make::<Str>::span(&p).is_empty());
    }

    #[test]
    fn equal_atoms_keep_the_ocaml_representative() {
        // `Disjunction.of_list [conj1; conj2]` keeps the first of two equal
        // conjunctions.
        let j = Make::<Keyed>::join(&Make::mk_left((1, "x")), &Make::mk_left((1, "y")));
        assert_eq!(Make::<Keyed>::left(&j), vec![vec![(1, "x")]]);
        // `meet (And conj) set2` is `Conjunction.union conj2 conj`, with the
        // conjunction of `set2` first: `add` keeps its element.
        let m = Make::<Keyed>::meet(&Make::mk_left((1, "x")), &Make::mk_left((1, "y")));
        assert_eq!(Make::<Keyed>::left(&m), vec![vec![(1, "y")]]);
    }

    fn conj(atoms: &[i32]) -> conjunction::T<Int> {
        atoms.iter().fold(conjunction::empty(), |acc, &a| {
            conjunction::union(&acc, &conjunction::singleton(a))
        })
    }

    fn show(c: &disjunction::Elt<Int>) -> String {
        format!("{:?}", conjunction::elements(&c.0))
    }

    #[test]
    fn map_keeps_the_nodes_that_do_not_change() {
        // {1,3} < {2,3}: `of_list` gives the tree (. {1,3} (. {2,3} .)).
        let disj = disjunction::of_list(vec![conj(&[1, 3]), conj(&[2, 3])]);
        assert_eq!(stdlib_set::dump(&show, &disj), "(. [1, 3] (. [2, 3] .))");
        // Both conjunctions already have 3: `Conjunction.union conj {3}` is
        // `conj` itself, and `Set.map` keeps the tree.
        let kept = match lattice::meet(&lattice::singleton::<Int>(3), &lattice::T::Or(disj.clone()))
        {
            lattice::T::Or(d) => d,
            lattice::T::And(_) => panic!("expected a disjunction"),
        };
        assert!(stdlib_set::same_tree(&kept, &disj));
        // With 4 every element changes, and `try_join` rebuilds the nodes
        // whose left child is empty (`add_min_element`).
        let rebuilt =
            match lattice::meet(&lattice::singleton::<Int>(4), &lattice::T::Or(disj.clone())) {
                lattice::T::Or(d) => d,
                lattice::T::And(_) => panic!("expected a disjunction"),
            };
        assert_eq!(
            stdlib_set::dump(&show, &rebuilt),
            "((. [1, 3, 4] .) [2, 3, 4] .)"
        );
    }
}
