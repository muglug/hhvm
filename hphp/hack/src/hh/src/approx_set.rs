// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/approx_set/approx_set.ml`. See `hh/PORTING.md`.
//!
//! `Approx_set.Make (Domain)` is the type [`Make<Domain>`] (see
//! `crate::approx_set_intf` for how the module types map): the type is both
//! the module and its type `t`, and the functions of the module are its
//! associated functions. So
//!
//! ```ignore
//! module ApproxTagSet = Approx_set.Make (TagWithReason)
//! ... ApproxTagSet.union s1 s2 ... ApproxTagSet.t ...
//! ```
//!
//! is
//!
//! ```ignore
//! type ApproxTagSet = approx_set::Make<TagWithReason>;
//! ... ApproxTagSet::union(&s1, &s2) ... ApproxTagSet ...
//! ```
//!
//! and the type `disjoint` of the module is `approx_set::Disjoint<Domain>`
//! (`ApproxTagSet.Unsat { left; relation; right }` is
//! `Disjoint::Unsat { left, relation, right }`). `Make<D>` also implements
//! the traits `S` and `SWithWitness`, for code that is generic in the set.
//!
//! `Domain.relation` may have effects (with the typing environment as `ctx`
//! it looks up classes, which records dependencies), so the relations are
//! computed in the order the OCaml computes them: right to left in the
//! arguments of `Set_relation.union`/`inter`.

use std::rc::Rc;

pub use crate::approx_set_intf::Disjoint;
pub use crate::approx_set_intf::DomainType;
pub use crate::approx_set_intf::S;
pub use crate::approx_set_intf::SWithWitness;
use crate::set_relation;

/// Sets over [Domain.t]; representation is in NNF by construction
mod impl_ {
    use std::rc::Rc;

    use super::Disjoint;
    use super::DomainType;
    use crate::set_relation;

    /// Represents an individual atom in our abstract domain. [elt] is the
    /// particular element in the domain that is uniquely indentified by
    /// [Domain.t]. [comp] indicates whether it is the complement of the
    /// [Domain.t]. i.e.
    ///
    ///   {
    ///     comp = false;
    ///     elt = [A]
    ///   }
    /// Means all elements represented by A, while:
    ///   {
    ///     comp = true;
    ///     elt = [A]
    ///   }
    /// Means all elements not represented by A
    ///
    /// (The element is shared, as in OCaml: making the complement of an
    /// atom, or a singleton of its element, does not copy it.)
    pub struct Atom<D: DomainType> {
        pub comp: bool,
        pub elt: Rc<D::T>,
    }

    impl<D: DomainType> Clone for Atom<D> {
        fn clone(&self) -> Self {
            Atom {
                comp: self.comp,
                elt: Rc::clone(&self.elt),
            }
        }
    }

    pub enum T<D: DomainType> {
        Set(Atom<D>),
        Union(Rc<T<D>>, Rc<T<D>>),
        Inter(Rc<T<D>>, Rc<T<D>>),
    }

    impl<D: DomainType> Clone for T<D> {
        fn clone(&self) -> Self {
            match self {
                T::Set(atom) => T::Set(atom.clone()),
                T::Union(l, r) => T::Union(Rc::clone(l), Rc::clone(r)),
                T::Inter(l, r) => T::Inter(Rc::clone(l), Rc::clone(r)),
            }
        }
    }

    impl<D: DomainType> std::fmt::Debug for T<D>
    where
        D::T: std::fmt::Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                T::Set(Atom { comp, elt }) => f
                    .debug_struct("Set")
                    .field("comp", comp)
                    .field("elt", &**elt)
                    .finish(),
                T::Union(l, r) => f.debug_tuple("Union").field(&**l).field(&**r).finish(),
                T::Inter(l, r) => f.debug_tuple("Inter").field(&**l).field(&**r).finish(),
            }
        }
    }

    pub fn singleton<D: DomainType>(elt: Rc<D::T>) -> T<D> {
        T::Set(Atom { comp: false, elt })
    }

    pub fn relate<D: DomainType>(ctx: &D::Ctx, set1: &T<D>, set2: &T<D>) -> set_relation::T {
        match (set1, set2) {
            (
                T::Set(Atom {
                    comp: false,
                    elt: elt1,
                }),
                T::Set(Atom {
                    comp: false,
                    elt: elt2,
                }),
            ) => D::relation(elt1, ctx, elt2),
            (T::Union(left, right), set) => {
                // `Set_relation.union (relate ctx left set) (relate ctx right set)`:
                // the arguments are evaluated right to left.
                let rel_right = relate(ctx, right, set);
                let rel_left = relate(ctx, left, set);
                set_relation::union(&rel_left, &rel_right)
            }
            (T::Inter(left, right), set) => {
                let rel_right = relate(ctx, right, set);
                let rel_left = relate(ctx, left, set);
                set_relation::inter(&rel_left, &rel_right)
            }
            (T::Set(Atom { comp: true, elt }), set) => {
                set_relation::complement(&relate(ctx, &singleton(Rc::clone(elt)), set))
            }
            (
                T::Set(Atom { comp: false, elt }),
                set @ (T::Union(..) | T::Inter(..) | T::Set(Atom { comp: true, .. })),
            ) => set_relation::flip(&relate(ctx, set, &singleton(Rc::clone(elt)))),
        }
    }

    pub fn flip_unsat<D: DomainType>(disjoint: Disjoint<D>) -> Disjoint<D> {
        match disjoint {
            Disjoint::Sat => Disjoint::Sat,
            Disjoint::Unsat {
                left,
                relation,
                right,
            } => Disjoint::Unsat {
                left: right,
                relation: set_relation::flip(&relation),
                right: left,
            },
        }
    }

    pub fn disjoint_atom<D: DomainType>(
        atom1: &Atom<D>,
        atom2: &Atom<D>,
        ctx: &D::Ctx,
    ) -> Disjoint<D> {
        let relation = relate(ctx, &T::Set(atom1.clone()), &T::Set(atom2.clone()));
        if set_relation::is_disjoint(&relation) {
            Disjoint::Sat
        } else {
            Disjoint::Unsat {
                left: D::T::clone(&atom1.elt),
                relation,
                right: D::T::clone(&atom2.elt),
            }
        }
    }

    pub fn disjoint<D: DomainType>(ctx: &D::Ctx, set1: &T<D>, set2: &T<D>) -> Disjoint<D> {
        match (set1, set2) {
            // (L ∪ R) disj S if (L disj S) && (R disj S)
            (T::Union(l, r), set) => match disjoint(ctx, l, set) {
                Disjoint::Sat => disjoint(ctx, r, set),
                unsat @ Disjoint::Unsat { .. } => unsat,
            },
            // (L ∩ R) disj S if (L disj S) || (R disj S)
            (T::Inter(l, r), set) => match disjoint(ctx, l, set) {
                Disjoint::Sat => Disjoint::Sat,
                Disjoint::Unsat { .. } => disjoint(ctx, r, set),
            },
            (T::Set(atom1), T::Set(atom2)) => disjoint_atom(atom1, atom2, ctx),
            (T::Set(_), T::Union(..) | T::Inter(..)) => flip_unsat(disjoint(ctx, set2, set1)),
        }
    }

    pub fn union<D: DomainType>(l: T<D>, r: T<D>) -> T<D> {
        T::Union(Rc::new(l), Rc::new(r))
    }

    pub fn inter<D: DomainType>(l: T<D>, r: T<D>) -> T<D> {
        T::Inter(Rc::new(l), Rc::new(r))
    }

    ///  Keep values in negation normal form by construction
    pub fn comp<D: DomainType>(t: &T<D>) -> T<D> {
        match t {
            // !(!A) = A
            T::Set(atom) => T::Set(Atom {
                comp: !atom.comp,
                elt: Rc::clone(&atom.elt),
            }),
            // De Morgan's Law: !(A ∪ B) = !A ∩ !B
            T::Union(a, b) => {
                let comp_b = comp(b);
                let comp_a = comp(a);
                inter(comp_a, comp_b)
            }
            // De Morgan's Law: !(A ∩ B) = !A ∪ !B
            T::Inter(a, b) => {
                let comp_b = comp(b);
                let comp_a = comp(a);
                union(comp_a, comp_b)
            }
        }
    }

    /// A ∖ B = A ∩ !B
    pub fn diff<D: DomainType>(a: T<D>, b: &T<D>) -> T<D> {
        inter(a, comp(b))
    }
}

/// `Make (Domain)`, and its type `t`: `Impl.t option`. We encode an empty
/// set using [Option.None]
pub struct Make<D: DomainType>(Option<impl_::T<D>>);

impl<D: DomainType> Clone for Make<D> {
    fn clone(&self) -> Self {
        Make(self.0.clone())
    }
}

impl<D: DomainType> std::fmt::Debug for Make<D>
where
    D::T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<D: DomainType> Make<D> {
    pub fn empty() -> Self {
        Make(None)
    }

    pub fn singleton(tag: D::T) -> Self {
        Make(Some(impl_::singleton(Rc::new(tag))))
    }

    pub fn union(set1: &Self, set2: &Self) -> Self {
        match (&set1.0, &set2.0) {
            (_, None) => set1.clone(),
            (None, _) => set2.clone(),
            (Some(a), Some(b)) => Make(Some(impl_::union(a.clone(), b.clone()))),
        }
    }

    pub fn inter(set1: &Self, set2: &Self) -> Self {
        match (&set1.0, &set2.0) {
            (_, None) | (None, _) => Make(None),
            (Some(a), Some(b)) => Make(Some(impl_::inter(a.clone(), b.clone()))),
        }
    }

    pub fn diff(set1: &Self, set2: &Self) -> Self {
        match (&set1.0, &set2.0) {
            (_, None) => set1.clone(),
            (None, _) => Make(None),
            (Some(a), Some(b)) => Make(Some(impl_::diff(a.clone(), b))),
        }
    }

    pub fn of_list(elt: Vec<D::T>) -> Self {
        let mut acc = Self::empty();
        for tag in elt {
            acc = Self::union(&acc, &Self::singleton(tag));
        }
        acc
    }

    pub fn disjoint(ctx: &D::Ctx, set1: &Self, set2: &Self) -> Disjoint<D> {
        match (&set1.0, &set2.0) {
            (None, _) | (_, None) => Disjoint::Sat,
            (Some(set1), Some(set2)) => impl_::disjoint(ctx, set1, set2),
        }
    }

    pub fn are_disjoint(ctx: &D::Ctx, set1: &Self, set2: &Self) -> bool {
        match Self::disjoint(ctx, set1, set2) {
            Disjoint::Sat => true,
            Disjoint::Unsat { .. } => false,
        }
    }

    pub fn is_subset(ctx: &D::Ctx, set1: &Self, set2: &Self) -> bool {
        match (&set1.0, &set2.0) {
            (None, _) => true,
            (Some(_), None) => false,
            (Some(set1), Some(set2)) => set_relation::is_subset(&impl_::relate(ctx, set1, set2)),
        }
    }
}

impl<D: DomainType> S for Make<D> {
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

impl<D: DomainType> SWithWitness for Make<D> {
    fn disjoint(ctx: &D::Ctx, set1: &Self, set2: &Self) -> Disjoint<D> {
        Make::<D>::disjoint(ctx, set1, set2)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    /// Sets of the integers 0..32 as bit masks; the context records the
    /// pairs that `relation` is asked about, in order.
    struct Bits;

    impl DomainType for Bits {
        type T = u32;
        type Ctx = RefCell<Vec<(u32, u32)>>;

        fn relation(a: &u32, ctx: &Self::Ctx, b: &u32) -> set_relation::T {
            ctx.borrow_mut().push((*a, *b));
            set_relation::make(a & !b == 0, b & !a == 0, a & b == 0)
        }
    }

    type BitSet = Make<Bits>;

    fn ctx() -> RefCell<Vec<(u32, u32)>> {
        RefCell::new(vec![])
    }

    #[test]
    fn disjointness() {
        let ctx = ctx();
        let a = BitSet::of_list(vec![0b0011]);
        let b = BitSet::of_list(vec![0b1100]);
        let c = BitSet::of_list(vec![0b0110]);
        assert!(BitSet::are_disjoint(&ctx, &a, &b));
        assert!(!BitSet::are_disjoint(&ctx, &a, &c));
        assert_eq!(
            BitSet::disjoint(&ctx, &a, &c),
            Disjoint::Unsat {
                left: 0b0011,
                relation: set_relation::NONE,
                right: 0b0110,
            }
        );
        // The empty set is disjoint from everything.
        assert!(BitSet::are_disjoint(&ctx, &BitSet::empty(), &a));
        assert!(BitSet::are_disjoint(&ctx, &a, &BitSet::empty()));
        // 0111 ∖ 0011 is disjoint from 0011.
        let d = BitSet::diff(&BitSet::singleton(0b0111), &BitSet::singleton(0b0011));
        assert!(BitSet::are_disjoint(&ctx, &d, &BitSet::singleton(0b0011)));
        assert!(!BitSet::are_disjoint(&ctx, &d, &BitSet::singleton(0b0100)));
        // A union on the right: the witness is flipped back.
        let u = BitSet::of_list(vec![0b1000, 0b0001]);
        assert_eq!(
            BitSet::disjoint(&ctx, &a, &u),
            Disjoint::Unsat {
                left: 0b0011,
                relation: set_relation::SUPERSET,
                right: 0b0001,
            }
        );
    }

    #[test]
    fn subsets() {
        let ctx = ctx();
        let small = BitSet::of_list(vec![0b0001, 0b0010]);
        let big = BitSet::singleton(0b0011);
        assert!(BitSet::is_subset(&ctx, &small, &big));
        assert!(!BitSet::is_subset(&ctx, &BitSet::singleton(0b0111), &big));
        assert!(BitSet::is_subset(&ctx, &BitSet::empty(), &big));
        assert!(!BitSet::is_subset(&ctx, &big, &BitSet::empty()));
        assert!(BitSet::is_subset(
            &ctx,
            &BitSet::inter(&BitSet::singleton(0b0111), &big),
            &big
        ));
    }

    #[test]
    fn relations_are_computed_right_to_left() {
        let ctx = ctx();
        // of_list [A; B] is Union (Set A, Set B).
        let u = BitSet::of_list(vec![0b0001, 0b0010]);
        BitSet::is_subset(&ctx, &u, &BitSet::singleton(0b0100));
        assert_eq!(*ctx.borrow(), vec![(0b0010, 0b0100), (0b0001, 0b0100)]);
    }
}
