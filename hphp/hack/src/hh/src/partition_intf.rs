// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `partition_intf.ml`. See `hh/PORTING.md`.
//!
//! The module types are traits whose functions have no receiver (as in
//! `crate::approx_set_intf`):
//!
//! - the argument of `Make` (`sig type t val compare : t -> t -> int end`)
//!   is [`OrderedType`], implemented by a type that stands for the module:
//!   its `T` is `M.t` (a marker type will do: `struct LoclTyAtom;`).
//! - `S` is implemented by the *partition type* `t` of a module: the module
//!   and its type are one Rust type, so `M.t` is `M` and `M.join` is
//!   `M::join`. `S with type atom := M.t` is `S<Atom = M::T>`.
//! - `Partition`, the signature of the module `Partition`, is what that
//!   module exports: `Partition.cartesian` is `crate::partition::cartesian`
//!   and `Partition.Make (M)` the type `crate::partition::Make<M>` (it
//!   implements [`S`]).
//! - The operators of `Infix_ops` have no Rust spelling. As in
//!   `crate::typing_logic_helpers`, `( ||| )` is `or` and `( &&& )` is `and`,
//!   in the module `infix_ops` of the implementation
//!   (`crate::partition::infix_ops`).
//!
//! The partitions are taken by reference and returned owned: the
//! implementation shares structure, so the copies it makes are cheap.

use std::cmp::Ordering;

/// The argument of `Partition.Make`:
/// `sig type t val compare : t -> t -> int end`.
pub trait OrderedType {
    type T: Clone;

    fn compare(t1: &Self::T, t2: &Self::T) -> Ordering;
}

/// Operations on atoms are represented in disjunctive normal form (DNF).
/// This means it is a list of disjunctions (unions) that contain
/// a list of conjunctions (intersections).
///
/// (A & B) | C, where A, B, C are atoms is represented as:
///   [[A; B]; [C]]
pub type Dnf<Atom> = Vec<Vec<Atom>>;

/// Implemented by the abstract representation of a partition (`t`).
pub trait S: Sized {
    /// The set we are partitioning over. Atoms are treated atomically,
    /// meaning we compute partitions without knowing the relationships
    /// between different atoms in the partition.
    type Atom;

    // Smart Constructors for a partition

    /// A completely empty partition where both the left and right are empty
    fn mk_bottom() -> Self;

    /// A partition where the atom is assumed to be fully within the left
    /// side of the partition
    fn mk_left(atom: Self::Atom) -> Self;

    /// A partition where the atom is assumed to be fully within the right
    /// side of the partition
    fn mk_right(atom: Self::Atom) -> Self;

    /// A partition that spans across the left and right partitions
    fn mk_span(atom: Self::Atom) -> Self;

    /// Unions two partitions together producing another partition
    fn join(t1: &Self, t2: &Self) -> Self;

    /// Intersects two partitions together producing another partition
    fn meet(t1: &Self, t2: &Self) -> Self;

    /// Combines two partitions using the algebra for union predicates.
    /// For union predicates (P1 | P2):
    /// - left: passes at least one predicate
    /// - right: fails both predicates
    /// - span: uncertain (may pass either)
    fn union_combine(t1: &Self, t2: &Self) -> Self;

    /// If the partition is fully within the left, span or right we can
    /// simplify the DNF to be just the given atom, otherwise return [t]
    /// unchanged
    fn simplify(t: &Self, atom: Self::Atom) -> Self;

    // Accessors

    /// Returns the component of the partition that
    /// is definitely within the left side of the partition
    fn left(t: &Self) -> Dnf<Self::Atom>;

    /// Returns the component of the partition that is definitely
    /// spans across the left and right side of the partition
    fn span(t: &Self) -> Dnf<Self::Atom>;

    /// Returns the component of the partition that
    /// is definitely within the right side of the partition
    fn right(t: &Self) -> Dnf<Self::Atom>;

    /// Returns the complement of the partition -- left and right are swapped
    fn flip(t: &Self) -> Self;

    /// Given a product function from atoms to an atom and a list of
    /// partitions, Returns a new partition that is the "product" of the
    /// given partitions such that:
    /// A set in the new partition is a set obtained by taking one set from
    /// each given partition and combining them using the given product
    /// function.
    /// There is a set in the new partition for every such combination.
    /// Combinations of sets only from the left side of the input partitions
    /// are on the left of the new partition.
    /// Combinations of sets containing at least one set from the right side
    /// of an input partition are on the right of the new partition.
    /// All other combinations of sets are in the span of the new partition.
    fn product(product_f: &dyn Fn(Vec<Self::Atom>) -> Self::Atom, tl: &[Self]) -> Self;
}
