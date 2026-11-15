// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/approx_set/set_relation.ml`. See `hh/PORTING.md`.
//!
//! The values of the module (`none`, `subset`, `superset`, `disjoint`,
//! `equivalent`, `all`) are constants: `set_relation::DISJOINT`. The
//! functions take a relation by reference, as values that are only read
//! (`T` is `Copy`, so `&rel` costs nothing).
//!
//! Beware that the constants are in scope wherever the module is
//! glob-imported: a `let disjoint = ...` there is a pattern, not a binding.

/// `Set_relation.t`, abstract in the `.mli`. The field `super` of the OCaml
/// is `super_` (a Rust keyword).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct T {
    sub: bool,
    super_: bool,
    disjoint: bool,
}

/// Assume no relations exists
pub const NONE: T = T {
    sub: false,
    super_: false,
    disjoint: false,
};

/// Assume a subset relationship exists
pub const SUBSET: T = T { sub: true, ..NONE };

/// Assume a superset relationship exist
pub const SUPERSET: T = T {
    super_: true,
    ..NONE
};

/// Assume a disjoint relationship exist
pub const DISJOINT: T = T {
    disjoint: true,
    ..NONE
};

/// Assume the sets are equivalent. This means it is both
/// a subset and a superset
pub const EQUIVALENT: T = T {
    sub: true,
    super_: true,
    ..NONE
};

/// Assume all relations exists (subset, superset & disjoint).
/// This is only valid when relating the empty set to itself.
pub const ALL: T = T {
    sub: true,
    super_: true,
    disjoint: true,
};

/// `make ~subset ~superset ~disjoint`
pub fn make(subset: bool, superset: bool, disjoint: bool) -> T {
    T {
        sub: subset,
        super_: superset,
        disjoint,
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
        assert_eq!(bits(&NONE), (false, false, false));
        assert_eq!(bits(&SUBSET), (true, false, false));
        assert_eq!(bits(&SUPERSET), (false, true, false));
        assert_eq!(bits(&DISJOINT), (false, false, true));
        assert_eq!(bits(&EQUIVALENT), (true, true, false));
        assert_eq!(bits(&ALL), (true, true, true));
        assert_eq!(
            make(true, false, true),
            T {
                sub: true,
                super_: false,
                disjoint: true
            }
        );
        assert!(is_equivalent(&EQUIVALENT));
        assert!(is_equivalent(&ALL));
        assert!(!is_equivalent(&SUBSET));
    }

    #[test]
    fn operations() {
        assert_eq!(flip(&SUBSET), SUPERSET);
        assert_eq!(flip(&SUPERSET), SUBSET);
        assert_eq!(flip(&make(true, false, true)), make(false, true, true));
        // !A rel B: never a subset, a superset when A and B were disjoint,
        // disjoint when A was a superset of B.
        assert_eq!(complement(&DISJOINT), SUPERSET);
        assert_eq!(complement(&SUPERSET), DISJOINT);
        assert_eq!(complement(&SUBSET), NONE);
        assert_eq!(complement(&ALL), make(false, true, true));
        // (L ∪ R) is a subset of A only if both are, a superset if either
        // is, and disjoint from A only if both are.
        assert_eq!(union(&SUBSET, &EQUIVALENT), EQUIVALENT);
        assert_eq!(union(&SUBSET, &NONE), NONE);
        assert_eq!(union(&SUPERSET, &NONE), SUPERSET);
        assert_eq!(union(&DISJOINT, &ALL), make(false, true, true));
        assert_eq!(union(&DISJOINT, &DISJOINT), DISJOINT);
        // (L ∩ R) is a subset of A if either is, a superset only if both
        // are, and disjoint from A if either is.
        assert_eq!(inter(&SUBSET, &NONE), SUBSET);
        assert_eq!(inter(&SUPERSET, &EQUIVALENT), EQUIVALENT);
        assert_eq!(inter(&DISJOINT, &NONE), DISJOINT);
    }
}
