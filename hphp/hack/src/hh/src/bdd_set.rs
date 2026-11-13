// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `bdd_set.ml`. See `hh/PORTING.md`.
//!
//! `Bdd_set.Make (Domain)` is the type [`Make<Domain>`] (see
//! `crate::approx_set_intf` for how the module types map): the type is both
//! the module and its type `t`, and the functions of the module are its
//! associated functions (`Make::<D>::union(&s1, &s2)`). It implements the
//! trait `S`, which is what the `.mli` exports (`S with module Domain :=
//! Domain`); the rest (the functor `Bdd`, `check_relation`) is private.
//!
//! `Domain.relation` may have effects (with the typing environment as `ctx`
//! it looks up classes, which records dependencies), so the trees are
//! simplified, and the relations computed, in the order the OCaml computes
//! them: the arguments of a call right to left.

use std::rc::Rc;

pub use crate::approx_set_intf::DomainType;
pub use crate::approx_set_intf::OrderedDomainType;
pub use crate::approx_set_intf::S;
use crate::set_relation;

/// `Bdd (Atom)`. The functor is applied once, to the `Domain` of [`Make`]
/// (`include Bdd (Domain)`), so its argument `Atom` (`sig type t val compare
/// : t -> t -> int end`) is that domain here, of which it uses `compare`.
mod bdd {
    use std::cmp::Ordering;
    use std::rc::Rc;

    use super::OrderedDomainType;

    /// Represents a node in the BDD. [then_] is the branch taken when another
    /// set is a subset of [atom]. [else_] is the branch taken when not a
    /// subset.
    ///
    /// (The atom is shared, as in OCaml: the nodes that `apply` and the
    /// simplifications of `check_relation` build for an atom do not copy it.)
    pub struct Node<A: OrderedDomainType> {
        pub atom: Rc<A::T>,
        pub then_: T<A>,
        pub else_: T<A>,
    }

    pub enum T<A: OrderedDomainType> {
        Bottom,
        Top,
        Select(Rc<Node<A>>),
    }

    impl<A: OrderedDomainType> Clone for T<A> {
        fn clone(&self) -> Self {
            match self {
                T::Bottom => T::Bottom,
                T::Top => T::Top,
                T::Select(node) => T::Select(Rc::clone(node)),
            }
        }
    }

    impl<A: OrderedDomainType> std::fmt::Debug for T<A>
    where
        A::T: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                T::Bottom => f.write_str("Bottom"),
                T::Top => f.write_str("Top"),
                T::Select(node) => f
                    .debug_struct("Select")
                    .field("atom", &*node.atom)
                    .field("then_", &node.then_)
                    .field("else_", &node.else_)
                    .finish(),
            }
        }
    }

    /// Operations supported by the BDD
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Op {
        Meet,
        Join,
        Diff,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Order {
        /// The atoms are semantically the same
        Same,
        /// Lower atoms are closer to the root
        Lower,
        /// Higher atoms are closer to the leaves
        Higher,
    }

    pub fn bdd_order<A: OrderedDomainType>(a: &A::T, b: &A::T) -> Order {
        match A::compare(a, b) {
            Ordering::Equal => Order::Same,
            Ordering::Less => Order::Lower,
            Ordering::Greater => Order::Higher,
        }
    }

    /// OCaml's `t1 == t2`: `Bottom` and `Top` are constants, a `Select` is
    /// the same block only if it is the same node.
    fn phys_equal<A: OrderedDomainType>(t1: &T<A>, t2: &T<A>) -> bool {
        match (t1, t2) {
            (T::Bottom, T::Bottom) | (T::Top, T::Top) => true,
            (T::Select(node1), T::Select(node2)) => Rc::ptr_eq(node1, node2),
            _ => false,
        }
    }

    pub fn equal<A: OrderedDomainType>(t1: &T<A>, t2: &T<A>) -> bool {
        if phys_equal(t1, t2) {
            true
        } else {
            match (t1, t2) {
                (T::Bottom, T::Bottom) | (T::Top, T::Top) => true,
                (T::Select(node1), T::Select(node2)) => {
                    A::compare(&node1.atom, &node2.atom) == Ordering::Equal
                        && equal(&node1.then_, &node2.then_)
                        && equal(&node1.else_, &node2.else_)
                }
                _ => false,
            }
        }
    }

    pub fn node<A: OrderedDomainType>(atom: Rc<A::T>, then_: T<A>, else_: T<A>) -> T<A> {
        if equal(&then_, &else_) {
            then_
        } else {
            T::Select(Rc::new(Node { atom, then_, else_ }))
        }
    }

    /// `let atom = node ~then_:Top ~else_:Bottom`
    pub fn atom<A: OrderedDomainType>(atom: Rc<A::T>) -> T<A> {
        node(atom, T::Top, T::Bottom)
    }

    /// What `apply op` computes before it is given the two trees, and the
    /// functions it then applies to them (`aux`, `aux_meet`, ...).
    struct Apply<A: OrderedDomainType> {
        op: Op,
        op_f_f: T<A>,
        op_f_t: T<A>,
        op_t_f: T<A>,
        op_t_t: T<A>,
    }

    /// `apply op t1 t2`. (`apply op` is applied to the two trees at once: the
    /// four leaves it computes first have no effect.)
    pub fn apply<A: OrderedDomainType>(op: Op, t1: &T<A>, t2: &T<A>) -> T<A> {
        let interp = |op: Op, b1: bool, b2: bool| match op {
            Op::Meet => b1 && b2,
            Op::Join => b1 || b2,
            Op::Diff => b1 && !b2,
        };
        let of_bool = |b: bool| if b { T::Top } else { T::Bottom };
        let op_f_f = of_bool(interp(op, false, false));
        let op_f_t = of_bool(interp(op, false, true));
        let op_t_f = of_bool(interp(op, true, false));
        let op_t_t = of_bool(interp(op, true, true));
        let apply = Apply {
            op,
            op_f_f,
            op_f_t,
            op_t_f,
            op_t_t,
        };
        apply.aux(t1, t2)
    }

    impl<A: OrderedDomainType> Apply<A> {
        fn aux(&self, t1: &T<A>, t2: &T<A>) -> T<A> {
            match self.op {
                Op::Meet => self.aux_meet(t1, t2),
                Op::Join => self.aux_join(t1, t2),
                Op::Diff => self.aux_diff(t1, t2),
            }
        }

        fn aux_meet(&self, t1: &T<A>, t2: &T<A>) -> T<A> {
            match (t1, t2) {
                (T::Top, _) => t2.clone(),
                (_, T::Top) => t1.clone(),
                (T::Bottom, _) | (_, T::Bottom) => T::Bottom,
                _ => self.aux_gen(t1, t2),
            }
        }

        fn aux_join(&self, t1: &T<A>, t2: &T<A>) -> T<A> {
            match (t1, t2) {
                (T::Bottom, _) => t2.clone(),
                (_, T::Bottom) => t1.clone(),
                (T::Top, _) | (_, T::Top) => T::Top,
                _ => self.aux_gen(t1, t2),
            }
        }

        fn aux_diff(&self, t1: &T<A>, t2: &T<A>) -> T<A> {
            match (t1, t2) {
                (T::Bottom, _) => T::Bottom,
                (_, T::Top) => T::Bottom,
                (_, T::Bottom) => t1.clone(),
                _ => self.aux_gen(t1, t2),
            }
        }

        /// The branches of a new node are computed `else_` first: OCaml
        /// evaluates the arguments of `node` right to left.
        fn aux_gen(&self, t1: &T<A>, t2: &T<A>) -> T<A> {
            match (t1, t2) {
                (T::Bottom, T::Bottom) => self.op_f_f.clone(),
                (T::Bottom, T::Top) => self.op_f_t.clone(),
                (T::Top, T::Bottom) => self.op_t_f.clone(),
                (T::Top, T::Top) => self.op_t_t.clone(),
                (T::Select(node1), T::Bottom | T::Top) => {
                    // Push terminal nodes to bottom of tree
                    let else_ = self.aux(&node1.else_, t2);
                    let then_ = self.aux(&node1.then_, t2);
                    node(Rc::clone(&node1.atom), then_, else_)
                }
                (T::Bottom | T::Top, T::Select(node2)) => {
                    // Push terminal nodes to bottom of tree
                    let else_ = self.aux(t1, &node2.else_);
                    let then_ = self.aux(t1, &node2.then_);
                    node(Rc::clone(&node2.atom), then_, else_)
                }
                (T::Select(node1), T::Select(node2)) => {
                    match bdd_order::<A>(&node1.atom, &node2.atom) {
                        Order::Same => {
                            // Atoms are the same, traverse edges of both
                            let else_ = self.aux(&node1.else_, &node2.else_);
                            let then_ = self.aux(&node1.then_, &node2.then_);
                            node(Rc::clone(&node1.atom), then_, else_)
                        }
                        Order::Lower => {
                            // node1 is lower, so push t2 closer to the
                            // leaves
                            let else_ = self.aux(&node1.else_, t2);
                            let then_ = self.aux(&node1.then_, t2);
                            node(Rc::clone(&node1.atom), then_, else_)
                        }
                        Order::Higher => {
                            // node1 is higher, so push t1 closer to the
                            // leaves
                            let else_ = self.aux(t1, &node2.else_);
                            let then_ = self.aux(t1, &node2.then_);
                            node(Rc::clone(&node2.atom), then_, else_)
                        }
                    }
                }
            }
        }
    }
}

use bdd::Node;
use bdd::Op;
use bdd::Order;
use bdd::T as Bdd;

/// `Make (Domain)`, and its type `t` (the BDD of `Bdd (Domain)`).
pub struct Make<D: OrderedDomainType>(Bdd<D>);

impl<D: OrderedDomainType> Clone for Make<D> {
    fn clone(&self) -> Self {
        Make(self.0.clone())
    }
}

impl<D: OrderedDomainType> std::fmt::Debug for Make<D>
where
    D::T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// `exception RelationUnsat of { left; relation; right }`: raised by
/// `check_relation` and caught by `are_disjoint` and `is_subset`, which only
/// look at whether it was raised.
#[allow(dead_code)]
struct RelationUnsat<D: OrderedDomainType> {
    left: Rc<D::T>,
    relation: set_relation::T,
    right: Rc<D::T>,
}

impl<D: OrderedDomainType> Make<D> {
    /// `let singleton = atom`
    pub fn singleton(elt: D::T) -> Self {
        Make(bdd::atom(Rc::new(elt)))
    }

    /// `let union = apply Join`
    pub fn union(set1: &Self, set2: &Self) -> Self {
        Make(bdd::apply(Op::Join, &set1.0, &set2.0))
    }

    /// `let inter = apply Meet`
    pub fn inter(set1: &Self, set2: &Self) -> Self {
        Make(bdd::apply(Op::Meet, &set1.0, &set2.0))
    }

    /// `let diff = apply Diff`
    pub fn diff(set1: &Self, set2: &Self) -> Self {
        Make(bdd::apply(Op::Diff, &set1.0, &set2.0))
    }

    /// `let empty = Bottom`
    pub fn empty() -> Self {
        Make(Bdd::Bottom)
    }

    /// Checks the relationship between two bdds. The algorithm
    /// walks both bdds in similar fashion to [Bdd.apply]. When
    /// reaching the leaves we determine the [SetRelation.t] between
    /// them and return the result, merging as we go back up.
    ///
    /// What's key is that we utilize the [Domain.relation] function
    /// to perform simplifications as we traverse the tree. If [t1] is
    /// lower than [t2] we can simplify any [then_] edges in [t2] that are:
    ///   * disjoint from [t1] when traversing [t1]'s [then_] edge
    ///   * a subset of [t1] when traversing [t1]'s [else_] edge
    ///
    /// [is_sat] is used to break out early from the traversal if we
    /// can no longer meet the condition. When that occurs a [RelationUnsat]
    /// exception is raised (here: returned as the error)
    ///
    /// Ideally we would employ memoization as we traverse to avoid
    /// repeated calls to [Domain.relation] or traversals as we simplify.
    /// Currently we do not to keep the implementation simpler. If
    /// performance becomes a concern then this is an optimization that
    /// can be done.
    ///
    /// `is_sat` defaults to `fun _ -> true`.
    fn check_relation(
        is_sat: Option<&dyn Fn(&set_relation::T) -> bool>,
        t1: &Bdd<D>,
        t2: &Bdd<D>,
        ctx: &D::Ctx,
    ) -> Result<set_relation::T, RelationUnsat<D>> {
        let default_is_sat = |_: &set_relation::T| true;
        let is_sat: &dyn Fn(&set_relation::T) -> bool = match is_sat {
            Some(is_sat) => is_sat,
            None => &default_is_sat,
        };
        let check_relation =
            |t1: &Bdd<D>, t2: &Bdd<D>| Self::check_relation(Some(is_sat), t1, t2, ctx);
        let merge = |rel1: &set_relation::T, rel2: &set_relation::T| {
            set_relation::make(
                set_relation::is_subset(rel1) && set_relation::is_subset(rel2),
                set_relation::is_superset(rel1) && set_relation::is_superset(rel2),
                set_relation::is_disjoint(rel1) && set_relation::is_disjoint(rel2),
            )
        };
        fn erase_then_edges_if<D: OrderedDomainType>(
            ctx: &D::Ctx,
            ground: &D::T,
            bdd: &Bdd<D>,
            f: fn(&set_relation::T) -> bool,
        ) -> Bdd<D> {
            let simplify = |bdd: &Bdd<D>| erase_then_edges_if(ctx, ground, bdd, f);
            match bdd {
                Bdd::Select(node) => {
                    if f(&D::relation(&node.atom, ctx, ground)) {
                        simplify(&node.else_)
                    } else {
                        // `node atom ~then_:(simplify then_) ~else_:(simplify
                        // else_)`: the arguments are evaluated right to left.
                        let else_ = simplify(&node.else_);
                        let then_ = simplify(&node.then_);
                        bdd::node(Rc::clone(&node.atom), then_, else_)
                    }
                }
                Bdd::Top => Bdd::Top,
                Bdd::Bottom => Bdd::Bottom,
            }
        }
        let erase_then_edges_disjoint_from = |ground: &D::T, bdd: &Bdd<D>| {
            erase_then_edges_if(ctx, ground, bdd, set_relation::is_disjoint)
        };
        let erase_then_edges_subset_of = |ground: &D::T, bdd: &Bdd<D>| {
            erase_then_edges_if(ctx, ground, bdd, set_relation::is_subset)
        };
        // In `merge (check_relation a1 b1) (check_relation a2 b2)`, OCaml
        // evaluates `check_relation a2 b2` (`b2` first, then `a2`) before
        // `check_relation a1 b1`, and does not evaluate the latter if the
        // former raises `RelationUnsat`.
        let traverse_t1 = |node1: &Node<D>| -> Result<set_relation::T, RelationUnsat<D>> {
            let b2 = erase_then_edges_subset_of(&node1.atom, t2);
            let a2 = erase_then_edges_subset_of(&node1.atom, &node1.else_);
            let rel2 = check_relation(&a2, &b2)?;
            let b1 = erase_then_edges_disjoint_from(&node1.atom, t2);
            let a1 = erase_then_edges_disjoint_from(&node1.atom, &node1.then_);
            let rel1 = check_relation(&a1, &b1)?;
            Ok(merge(&rel1, &rel2))
        };
        let traverse_t2 = |node2: &Node<D>| -> Result<set_relation::T, RelationUnsat<D>> {
            let b2 = erase_then_edges_subset_of(&node2.atom, &node2.else_);
            let a2 = erase_then_edges_subset_of(&node2.atom, t1);
            let rel2 = check_relation(&a2, &b2)?;
            let b1 = erase_then_edges_disjoint_from(&node2.atom, &node2.then_);
            let a1 = erase_then_edges_disjoint_from(&node2.atom, t1);
            let rel1 = check_relation(&a1, &b1)?;
            Ok(merge(&rel1, &rel2))
        };
        match (t1, t2) {
            (Bdd::Bottom, Bdd::Top) => Ok(set_relation::make(true, false, true)),
            (Bdd::Top, Bdd::Bottom) => Ok(set_relation::make(false, true, true)),
            (Bdd::Bottom, Bdd::Bottom) => Ok(set_relation::all),
            (Bdd::Top, Bdd::Top) => Ok(set_relation::equivalent),
            (Bdd::Select(node1), Bdd::Select(node2)) => {
                let relation = match bdd::bdd_order::<D>(&node1.atom, &node2.atom) {
                    Order::Same => {
                        let b2 = erase_then_edges_subset_of(&node1.atom, &node2.else_);
                        let a2 = erase_then_edges_subset_of(&node1.atom, &node1.else_);
                        let rel2 = check_relation(&a2, &b2)?;
                        let b1 = erase_then_edges_disjoint_from(&node1.atom, &node2.then_);
                        let a1 = erase_then_edges_disjoint_from(&node1.atom, &node1.then_);
                        let rel1 = check_relation(&a1, &b1)?;
                        merge(&rel1, &rel2)
                    }
                    Order::Lower => traverse_t1(node1)?,
                    Order::Higher => traverse_t2(node2)?,
                };
                if !is_sat(&relation) {
                    Err(RelationUnsat {
                        left: Rc::clone(&node1.atom),
                        relation,
                        right: Rc::clone(&node2.atom),
                    })
                } else {
                    Ok(relation)
                }
            }
            (Bdd::Select(node1), Bdd::Bottom | Bdd::Top) => traverse_t1(node1),
            (Bdd::Bottom | Bdd::Top, Bdd::Select(node2)) => traverse_t2(node2),
        }
    }

    pub fn are_disjoint(ctx: &D::Ctx, a: &Self, b: &Self) -> bool {
        let is_sat = set_relation::is_disjoint;
        match Self::check_relation(Some(&is_sat), &a.0, &b.0, ctx) {
            Ok(relation) => is_sat(&relation),
            Err(RelationUnsat { .. }) => false,
        }
    }

    pub fn is_subset(ctx: &D::Ctx, a: &Self, b: &Self) -> bool {
        let is_sat = set_relation::is_subset;
        match Self::check_relation(Some(&is_sat), &a.0, &b.0, ctx) {
            Ok(relation) => is_sat(&relation),
            Err(RelationUnsat { .. }) => false,
        }
    }

    pub fn of_list(elt: Vec<D::T>) -> Self {
        let mut acc = Self::empty();
        for tag in elt {
            acc = Self::union(&acc, &Self::singleton(tag));
        }
        acc
    }
}

impl<D: OrderedDomainType> S for Make<D> {
    type Domain = D;

    fn empty() -> Self {
        Make::<D>::empty()
    }

    fn singleton(elt: D::T) -> Self {
        Make::<D>::singleton(elt)
    }

    fn union(set1: &Self, set2: &Self) -> Self {
        Make::<D>::union(set1, set2)
    }

    fn inter(set1: &Self, set2: &Self) -> Self {
        Make::<D>::inter(set1, set2)
    }

    fn diff(set1: &Self, set2: &Self) -> Self {
        Make::<D>::diff(set1, set2)
    }

    fn of_list(elts: Vec<D::T>) -> Self {
        Make::<D>::of_list(elts)
    }

    fn are_disjoint(ctx: &D::Ctx, set1: &Self, set2: &Self) -> bool {
        Make::<D>::are_disjoint(ctx, set1, set2)
    }

    fn is_subset(ctx: &D::Ctx, set1: &Self, set2: &Self) -> bool {
        Make::<D>::is_subset(ctx, set1, set2)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::cmp::Ordering;

    use super::*;

    /// Sets of the integers 0..32 as bit masks, ordered by decreasing size
    /// (a superset comes first) then by value, with all 32 integers on top.
    /// The context records the pairs that `relation` is asked about, in
    /// order.
    struct Bits;

    impl DomainType for Bits {
        type T = u32;
        type Ctx = RefCell<Vec<(u32, u32)>>;

        fn relation(a: &u32, ctx: &Self::Ctx, b: &u32) -> set_relation::T {
            ctx.borrow_mut().push((*a, *b));
            set_relation::make(a & !b == 0, b & !a == 0, a & b == 0)
        }
    }

    impl OrderedDomainType for Bits {
        fn compare(a: &u32, b: &u32) -> Ordering {
            b.count_ones().cmp(&a.count_ones()).then(a.cmp(b))
        }

        fn top() -> u32 {
            u32::MAX
        }
    }

    type BitSet = Make<Bits>;

    fn ctx() -> RefCell<Vec<(u32, u32)>> {
        RefCell::new(vec![])
    }

    fn s(x: u32) -> BitSet {
        BitSet::singleton(x)
    }

    #[test]
    fn disjointness() {
        let ctx = ctx();
        assert!(BitSet::are_disjoint(&ctx, &s(0b0011), &s(0b1100)));
        assert!(!BitSet::are_disjoint(&ctx, &s(0b0011), &s(0b0110)));
        // The empty set is disjoint from everything.
        assert!(BitSet::are_disjoint(&ctx, &BitSet::empty(), &s(0b0011)));
        // 0111 ∖ 0011 is disjoint from 0011, not from 0100.
        let d = BitSet::diff(&s(0b0111), &s(0b0011));
        assert!(BitSet::are_disjoint(&ctx, &d, &s(0b0011)));
        assert!(!BitSet::are_disjoint(&ctx, &d, &s(0b0100)));
    }

    #[test]
    fn subsets() {
        let ctx = ctx();
        let small = BitSet::of_list(vec![0b0001, 0b0010]);
        assert!(BitSet::is_subset(&ctx, &small, &s(0b0011)));
        assert!(BitSet::is_subset(&ctx, &BitSet::empty(), &s(0b0011)));
        assert!(!BitSet::is_subset(&ctx, &s(0b0011), &BitSet::empty()));
    }

    #[test]
    fn nodes_are_shared_and_reduced() {
        // A ∪ A is A: the node whose branches are equal is dropped.
        let a = s(0b0011);
        let u = BitSet::union(&a, &a);
        assert!(bdd::equal(&u.0, &a.0));
        // {0001} ∪ {0010}: 0001 comes first in the order, so it is the root,
        // with the other atom on its `else_` branch.
        let small = BitSet::of_list(vec![0b0010, 0b0001]);
        match &small.0 {
            Bdd::Select(node) => {
                assert_eq!(*node.atom, 0b0001);
                assert!(matches!(node.then_, Bdd::Top));
                match &node.else_ {
                    Bdd::Select(node) => {
                        assert_eq!(*node.atom, 0b0010);
                        assert!(matches!(node.then_, Bdd::Top));
                        assert!(matches!(node.else_, Bdd::Bottom));
                    }
                    _ => panic!("expected a node"),
                }
            }
            _ => panic!("expected a node"),
        }
        // A ∩ ∅ = ∅, A ∖ A = ∅.
        assert!(matches!(BitSet::inter(&a, &BitSet::empty()).0, Bdd::Bottom));
        assert!(matches!(BitSet::diff(&a, &a).0, Bdd::Bottom));
    }

    #[test]
    fn relations_are_computed_in_the_ocaml_order() {
        let ctx = ctx();
        let small = BitSet::of_list(vec![0b0001, 0b0010]);
        assert!(BitSet::is_subset(&ctx, &small, &s(0b0011)));
        // The `else_` side of `merge` (the subset simplifications) first,
        // and in a simplified node the `else_` branch before the `then_`.
        assert_eq!(
            *ctx.borrow(),
            vec![
                (0b0001, 0b0011),
                (0b0010, 0b0011),
                (0b0001, 0b0011),
                (0b0010, 0b0011),
                (0b0010, 0b0001),
            ]
        );
    }
}
