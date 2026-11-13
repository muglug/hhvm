// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `set_relation.ml`. See `hh/PORTING.md`.
//!
//! The values of the module (`none`, `subset`, `superset`, `disjoint`,
//! `equivalent`, `all`) are constants: `set_relation::disjoint`. The
//! functions take a relation by reference, as values that are only read
//! (`T` is `Copy`, so `&rel` costs nothing).
//!
//! Beware that the constants are in scope wherever the module is
//! glob-imported: a `let disjoint = ...` there is a pattern, not a binding.

#![allow(non_upper_case_globals)]

/// `Set_relation.t`, abstract in the `.mli`. The field `super` of the OCaml
/// is `super_` (a Rust keyword).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct T {
    sub: bool,
    super_: bool,
    disjoint: bool,
}

/// Assume no relations exists
pub const none: T = T {
    sub: false,
    super_: false,
    disjoint: false,
};

/// Assume a subset relationship exists
pub const subset: T = T { sub: true, ..none };

/// Assume a superset relationship exist
pub const superset: T = T {
    super_: true,
    ..none
};

/// Assume a disjoint relationship exist
pub const disjoint: T = T {
    disjoint: true,
    ..none
};

/// Assume the sets are equivalent. This means it is both
/// a subset and a superset
pub const equivalent: T = T {
    sub: true,
    super_: true,
    ..none
};

/// Assume all relations exists (subset, superset & disjoint).
/// This is only valid when relating the empty set to itself.
pub const all: T = T {
    sub: true,
    super_: true,
    disjoint: true,
};

/// `make ~subset ~superset ~disjoint`. (The parameters have a trailing `_`:
/// without it they would be the constants of the same names.)
pub fn make(subset_: bool, superset_: bool, disjoint_: bool) -> T {
    T {
        sub: subset_,
        super_: superset_,
        disjoint: disjoint_,
    }
}

/// Check if the relation implies equivalence. This is
/// true iff [is_subset] and [is_superset] are true.
pub fn is_equivalent(rel: &T) -> bool {
    rel.sub && rel.super_
}

/// Check if the relation implies subset
pub fn is_subset(rel: &T) -> bool {
    rel.sub
}

/// Check if the relation implies superset
pub fn is_superset(rel: &T) -> bool {
    rel.super_
}

/// Check if the relation implies disjointness
pub fn is_disjoint(rel: &T) -> bool {
    rel.disjoint
}

/// Changes a Subset relation to a Superset relation and vice versa
pub fn flip(rel: &T) -> T {
    T {
        sub: rel.super_,
        super_: rel.sub,
        ..*rel
    }
}

// Derived from Alloy model. See wellformed_set.als

/// Let rel be the relation between the sets A and B.
/// [complement] determines what a safe approximation of
/// !A rel B, given we know A rel B
pub fn complement(rel: &T) -> T {
    T {
        sub: false,
        super_: rel.disjoint,
        disjoint: rel.super_,
    }
}

/// Let rel be the relation between sets A and B.
/// [union] determines what a safe approximation of
/// (L ∪ R) rel A, given we know L rel A and R rel A
pub fn union(rel1: &T, rel2: &T) -> T {
    T {
        sub: rel1.sub && rel2.sub,
        super_: rel1.super_ || rel2.super_,
        disjoint: rel1.disjoint && rel2.disjoint,
    }
}

/// Let rel be the relation between sets A and B.
/// [inter] determines what a safe approximation of
/// (L ∩ R) rel A, given we know L rel A and R rel A
pub fn inter(rel1: &T, rel2: &T) -> T {
    T {
        sub: rel1.sub || rel2.sub,
        super_: rel1.super_ && rel2.super_,
        disjoint: rel1.disjoint || rel2.disjoint,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bits(rel: &T) -> (bool, bool, bool) {
        (is_subset(rel), is_superset(rel), is_disjoint(rel))
    }

    #[test]
    fn constants() {
        assert_eq!(bits(&none), (false, false, false));
        assert_eq!(bits(&subset), (true, false, false));
        assert_eq!(bits(&superset), (false, true, false));
        assert_eq!(bits(&disjoint), (false, false, true));
        assert_eq!(bits(&equivalent), (true, true, false));
        assert_eq!(bits(&all), (true, true, true));
        assert_eq!(
            make(true, false, true),
            T {
                sub: true,
                super_: false,
                disjoint: true
            }
        );
        assert!(is_equivalent(&equivalent));
        assert!(is_equivalent(&all));
        assert!(!is_equivalent(&subset));
    }

    #[test]
    fn operations() {
        assert_eq!(flip(&subset), superset);
        assert_eq!(flip(&superset), subset);
        assert_eq!(flip(&make(true, false, true)), make(false, true, true));
        // !A rel B: never a subset, a superset when A and B were disjoint,
        // disjoint when A was a superset of B.
        assert_eq!(complement(&disjoint), superset);
        assert_eq!(complement(&superset), disjoint);
        assert_eq!(complement(&subset), none);
        assert_eq!(complement(&all), make(false, true, true));
        // (L ∪ R) is a subset of A only if both are, a superset if either
        // is, and disjoint from A only if both are.
        assert_eq!(union(&subset, &equivalent), equivalent);
        assert_eq!(union(&subset, &none), none);
        assert_eq!(union(&superset, &none), superset);
        assert_eq!(union(&disjoint, &all), make(false, true, true));
        assert_eq!(union(&disjoint, &disjoint), disjoint);
        // (L ∩ R) is a subset of A if either is, a superset only if both
        // are, and disjoint from A if either is.
        assert_eq!(inter(&subset, &none), subset);
        assert_eq!(inter(&superset, &equivalent), equivalent);
        assert_eq!(inter(&disjoint, &none), disjoint);
    }
}
