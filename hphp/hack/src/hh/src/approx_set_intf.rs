// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/approx_set/approx_set_intf.ml`. See `hh/PORTING.md`.
//!
//! The module types are traits whose functions have no receiver (as in
//! `crate::decl_enforceability`):
//!
//! - `DomainType` (and `OrderedDomainType`) is implemented by a type that
//!   stands for the domain module: its `T` is `Domain.t` and its `Ctx` is
//!   `Domain.ctx`. A marker type will do (`struct TagWithReason;`), or the
//!   element type itself (`type T = Self`).
//! - `S` and `S_with_witness` are implemented by the *set type* `t` of a
//!   module: the module and its type are one Rust type, so `M.t` is `M` and
//!   `M.union` is `M::union`. `S with module Domain := Domain` is
//!   `S<Domain = Domain>`.
//! - the type `disjoint` of `S_with_witness` (which every implementation
//!   defines with the same constructors) is the generic [`Disjoint`].
//! - `ApproxSet` and `BddSet`, the signatures of the modules `Approx_set` and
//!   `Bdd_set`, are what those modules export: `Approx_set.Make (Domain)` is
//!   the type `crate::approx_set::Make<Domain>` (it implements
//!   [`SWithWitness`]), `Bdd_set.Make (Domain)` is `crate::bdd_set::Make<Domain>`
//!   (it implements [`S`]).
//!
//! The sets are taken by reference and returned owned: the implementations
//! share structure, so the copies they make are cheap.

use std::cmp::Ordering;

use crate::set_relation;

/// Specifies the domain that the set will range over. Individual
/// members of the domain can be related to one another via the [relation]
/// function.
pub trait DomainType {
    /// Type of atomic elements of the domain
    type T: Clone;

    /// Contextual data that will be provided to [relation] when determining
    /// [SetRelation] between atomic elements of the domain
    type Ctx: ?Sized;

    /// Determines between atomic elements of the domain based on the given
    /// context (`relation : t -> ctx:ctx -> t -> Set_relation.t`).
    /// A valid implementation of [relation] must satisfy the following
    /// properties for all atoms A and B in the Domain:
    ///   1. `SetRelation.is_subset   @@ relation ctx a b <=>
    ///       SetRelation.is_superset @@ relation ctx b a`
    ///   2. `SetRelation.is_superset @@ relation ctx a b <=>
    ///       SetRelation.is_subset   @@ relation ctx b a`
    ///   3. `SetRelation.is_disjoint @@ relation ctx a b <=>
    ///       SetRelation.is_disjoint @@ relation ctx b a`
    ///
    /// We also require transitively as expected for the given set relations
    fn relation(t1: &Self::T, ctx: &Self::Ctx, t2: &Self::T) -> set_relation::T;
}

/// An abstract representation of a set, designed specifically to determine
/// if two sets are disjoint. Sets consist of atomic elements ([elt]) that
/// can be joined using basic set operations like union, intersection and set
/// difference. This is only an approximate set, because there are ways to
/// construct sets where it isn't possible to determine definitively whether
/// or not they are disjoint.
///
/// Implemented by the type of an instance of the approximate set (`t`).
pub trait S: Sized {
    /// The domain the set ranges over
    type Domain: DomainType;

    fn empty() -> Self;

    /// Create an approximate set from an atomic element in the domain
    fn singleton(elt: <Self::Domain as DomainType>::T) -> Self;

    /// Set union
    fn union(set1: &Self, set2: &Self) -> Self;

    /// Set intersection
    fn inter(set1: &Self, set2: &Self) -> Self;

    /// Set difference. Note that in some cases we cannot determine precisely
    /// if two sets involving [diff] are disjoint. In these cases the result
    /// will be approximated conservatively
    fn diff(set1: &Self, set2: &Self) -> Self;

    fn of_list(elts: Vec<<Self::Domain as DomainType>::T>) -> Self;

    fn are_disjoint(ctx: &<Self::Domain as DomainType>::Ctx, set1: &Self, set2: &Self) -> bool;

    fn is_subset(ctx: &<Self::Domain as DomainType>::Ctx, set1: &Self, set2: &Self) -> bool;
}

/// The result of testing two sets for disjointness (the type `disjoint` of
/// `S_with_witness`)
pub enum Disjoint<D: DomainType> {
    /// The two sets are definitely disjoint
    Sat,
    /// The two sets are not disjoint because of the relation between
    /// the given pair of [Domain.t]s
    Unsat {
        left: D::T,
        relation: set_relation::T,
        right: D::T,
    },
}

impl<D: DomainType> Clone for Disjoint<D> {
    fn clone(&self) -> Self {
        match self {
            Disjoint::Sat => Disjoint::Sat,
            Disjoint::Unsat {
                left,
                relation,
                right,
            } => Disjoint::Unsat {
                left: left.clone(),
                relation: *relation,
                right: right.clone(),
            },
        }
    }
}

impl<D: DomainType> std::fmt::Debug for Disjoint<D>
where
    D::T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Disjoint::Sat => f.write_str("Sat"),
            Disjoint::Unsat {
                left,
                relation,
                right,
            } => f
                .debug_struct("Unsat")
                .field("left", left)
                .field("relation", relation)
                .field("right", right)
                .finish(),
        }
    }
}

impl<D: DomainType> PartialEq for Disjoint<D>
where
    D::T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Disjoint::Sat, Disjoint::Sat) => true,
            (
                Disjoint::Unsat {
                    left: l1,
                    relation: r1,
                    right: rt1,
                },
                Disjoint::Unsat {
                    left: l2,
                    relation: r2,
                    right: rt2,
                },
            ) => l1 == l2 && r1 == r2 && rt1 == rt2,
            _ => false,
        }
    }
}

/// Extends [S] with a witness-producing disjointness check
pub trait SWithWitness: S {
    /// Determines if a pair of sets are disjoint in the given [ctx].
    /// If the sets cannot definitively be proven to be disjoint, will return
    /// [Unsat]
    fn disjoint(
        ctx: &<Self::Domain as DomainType>::Ctx,
        set1: &Self,
        set2: &Self,
    ) -> Disjoint<Self::Domain>;
}

/// A domain whose members can be ordered. The ordering is expected to
/// satisfy the following conditions:
///   1. There must exist a top element in the domain such that
///      `SetRelation.is_superset @@ relation ctx (top ()) atom` is true for
///      all atoms in the domain
///   2. For any two atoms A and B, `SetRelation.is_superset @@ relation ctx a b`
///      implies that `order a b <= 0`
///   3. For any two atoms A and B, `order a b = 0` implies that
///      `SetRelation.is_equivalent @@ relation ctx a b`
pub trait OrderedDomainType: DomainType {
    fn compare(t1: &Self::T, t2: &Self::T) -> Ordering;

    /// `val top : t`
    fn top() -> Self::T;
}
