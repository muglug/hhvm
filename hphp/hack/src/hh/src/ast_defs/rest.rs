// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The functions of `Ast_defs` (`ast/ast_defs.ml`) that the typechecker uses
//! and that are not in `ast_defs.rs` (which has `is_c_interface`,
//! `is_c_trait` and `string_of_classish_kind`). `ast_defs.rs` re-exports
//! them, so they are `crate::ast_defs::<name>`.
//!
//! The `[@@deriving]` functions that the typechecker calls by name are here
//! too (`equal_*`, `compare_*`, `show_*`; the types derive
//! `show { with_path = false }`).
//!
//! Not here: `show_id` (the show of a position and a string, laid out by
//! OCaml's `Format`) and the module `ShapeMap`/`ShapeSet`
//! (`oxidized::shape_map` has the map, keyed by `ShapeField`, which compares
//! like `Ast_defs.ShapeField.compare`).

use std::cmp::Ordering;

use oxidized::aast_defs::Contexts;
use oxidized::aast_defs::Hint;
use oxidized::aast_defs::Lid;
use oxidized::aast_defs::Stmt;
use oxidized::ast_defs::Abstraction;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::FunKind;
use oxidized::ast_defs::Id;
use oxidized::ast_defs::Variance;
use oxidized::ast_defs::Visibility;
use oxidized::pos::Pos;

/// `Pos.t * 'a`: the values that `get_pos` takes. In `oxidized` some of them
/// are tuples and others are tuple structs (`Id`, `Hint`, `Lid`...).
pub trait PosPair {
    fn pos_of_pair(&self) -> &Pos;
}

impl<A> PosPair for (Pos, A) {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

impl PosPair for Id {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

impl PosPair for Hint {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

impl PosPair for Lid {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

impl PosPair for Contexts {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

impl<Ex, En> PosPair for Stmt<Ex, En> {
    fn pos_of_pair(&self) -> &Pos {
        &self.0
    }
}

pub fn get_pos<P: PosPair + ?Sized>(p: &P) -> Pos {
    p.pos_of_pair().clone()
}

pub fn get_id(id: &Id) -> String {
    let Id(_p, id) = id;
    id.clone()
}

pub fn is_concrete(a: Abstraction) -> bool {
    match a {
        Abstraction::Concrete => true,
        Abstraction::Abstract => false,
    }
}

pub fn is_abstract(a: Abstraction) -> bool {
    match a {
        Abstraction::Abstract => true,
        Abstraction::Concrete => false,
    }
}

pub fn is_c_class(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(_) => true,
        ClassishKind::Cenum
        | ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface => false,
    }
}

pub fn is_c_concrete(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(k) | ClassishKind::CenumClass(k) => is_concrete(k),
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum => false,
    }
}

pub fn is_c_abstract(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cclass(c) => is_abstract(c),
        ClassishKind::Cinterface
        | ClassishKind::CenumClass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cenum => false,
    }
}

pub fn is_classish_abstract(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::CenumClass(c) | ClassishKind::Cclass(c) => is_abstract(c),
        ClassishKind::Cinterface | ClassishKind::Ctrait | ClassishKind::Cenum => false,
    }
}

pub fn is_c_enum(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::Cenum => true,
        ClassishKind::CenumClass(_)
        | ClassishKind::Cclass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface => false,
    }
}

pub fn is_c_enum_class(kind: ClassishKind) -> bool {
    match kind {
        ClassishKind::CenumClass(_) => true,
        ClassishKind::Cenum
        | ClassishKind::Cclass(_)
        | ClassishKind::Ctrait
        | ClassishKind::Cinterface => false,
    }
}

pub fn swap_variance(v: Variance) -> Variance {
    match v {
        Variance::Covariant => Variance::Contravariant,
        Variance::Contravariant => Variance::Covariant,
        Variance::Invariant => Variance::Invariant,
    }
}

/// `[@@deriving eq]`
pub fn equal_classish_kind(a: ClassishKind, b: ClassishKind) -> bool {
    a == b
}

/// `[@@deriving eq]`
pub fn equal_fun_kind(a: FunKind, b: FunKind) -> bool {
    a == b
}

/// `[@@deriving eq]`: the positions (`Pos.equal`) and the names.
pub fn equal_id(a: &Id, b: &Id) -> bool {
    crate::pos::equal(&a.0, &b.0) && a.1 == b.1
}

/// `[@@deriving ord]`: in the order of the constructors.
pub fn compare_constraint_kind(a: ConstraintKind, b: ConstraintKind) -> Ordering {
    a.cmp(&b)
}

/// `[@@deriving show { with_path = false }]`
pub fn show_variance(v: Variance) -> String {
    match v {
        Variance::Covariant => "Covariant",
        Variance::Contravariant => "Contravariant",
        Variance::Invariant => "Invariant",
    }
    .to_string()
}

/// `[@@deriving show { with_path = false }]`
pub fn show_visibility(v: Visibility) -> String {
    match v {
        Visibility::Private => "Private",
        Visibility::Public => "Public",
        Visibility::Protected => "Protected",
        Visibility::Internal => "Internal",
        Visibility::ProtectedInternal => "ProtectedInternal",
    }
    .to_string()
}

/// `[@@deriving show { with_path = false }]`
pub fn show_abstraction(a: Abstraction) -> String {
    match a {
        Abstraction::Concrete => "Concrete",
        Abstraction::Abstract => "Abstract",
    }
    .to_string()
}

/// `[@@deriving show { with_path = false }]`: a constructor with an argument
/// is `(Constructor argument)`, in a box that only breaks on a line longer
/// than the margin, which these never are.
pub fn show_classish_kind(kind: ClassishKind) -> String {
    match kind {
        ClassishKind::Cclass(a) => format!("(Cclass {})", show_abstraction(a)),
        ClassishKind::Cinterface => "Cinterface".to_string(),
        ClassishKind::Ctrait => "Ctrait".to_string(),
        ClassishKind::Cenum => "Cenum".to_string(),
        ClassishKind::CenumClass(a) => format!("(Cenum_class {})", show_abstraction(a)),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::aast_defs::Hint_;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    const KINDS: [ClassishKind; 7] = [
        ClassishKind::Cclass(Abstraction::Concrete),
        ClassishKind::Cclass(Abstraction::Abstract),
        ClassishKind::Cinterface,
        ClassishKind::Ctrait,
        ClassishKind::Cenum,
        ClassishKind::CenumClass(Abstraction::Concrete),
        ClassishKind::CenumClass(Abstraction::Abstract),
    ];

    #[test]
    fn classish_kinds() {
        let names = |f: fn(ClassishKind) -> bool| {
            KINDS
                .iter()
                .filter(|k| f(**k))
                .map(|k| show_classish_kind(*k))
                .collect::<Vec<_>>()
        };
        assert_eq!(names(is_c_class), ["(Cclass Concrete)", "(Cclass Abstract)"]);
        assert_eq!(
            names(is_c_concrete),
            ["(Cclass Concrete)", "(Cenum_class Concrete)"]
        );
        assert_eq!(names(is_c_abstract), ["(Cclass Abstract)"]);
        assert_eq!(
            names(is_classish_abstract),
            ["(Cclass Abstract)", "(Cenum_class Abstract)"]
        );
        assert_eq!(names(is_c_enum), ["Cenum"]);
        assert_eq!(
            names(is_c_enum_class),
            ["(Cenum_class Concrete)", "(Cenum_class Abstract)"]
        );
        // With those of `ast_defs.rs`.
        assert_eq!(names(super::super::is_c_trait), ["Ctrait"]);
        assert_eq!(names(super::super::is_c_interface), ["Cinterface"]);
        assert!(is_concrete(Abstraction::Concrete) && !is_concrete(Abstraction::Abstract));
        assert!(is_abstract(Abstraction::Abstract) && !is_abstract(Abstraction::Concrete));
        assert!(equal_classish_kind(KINDS[0], KINDS[0]));
        assert!(!equal_classish_kind(KINDS[0], KINDS[1]));
    }

    #[test]
    fn variances_and_shows() {
        assert_eq!(swap_variance(Variance::Covariant), Variance::Contravariant);
        assert_eq!(swap_variance(Variance::Contravariant), Variance::Covariant);
        assert_eq!(swap_variance(Variance::Invariant), Variance::Invariant);
        assert_eq!(show_variance(Variance::Contravariant), "Contravariant");
        assert_eq!(show_visibility(Visibility::ProtectedInternal), "ProtectedInternal");
        assert_eq!(show_visibility(Visibility::Public), "Public");
        assert_eq!(
            compare_constraint_kind(ConstraintKind::ConstraintAs, ConstraintKind::ConstraintEq),
            Ordering::Less
        );
        assert_eq!(
            compare_constraint_kind(
                ConstraintKind::ConstraintSuper,
                ConstraintKind::ConstraintEq
            ),
            Ordering::Greater
        );
        assert!(equal_fun_kind(FunKind::FAsync, FunKind::FAsync));
        assert!(!equal_fun_kind(FunKind::FAsync, FunKind::FSync));
    }

    #[test]
    fn positions_and_ids() {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        let p = Pos::from_lnum_bol_offset(file, (3, 20, 25), (3, 20, 30));
        let id = Id(p.clone(), "\\Foo".to_string());
        assert_eq!(get_pos(&id), p);
        assert_eq!(get_id(&id), "\\Foo");
        assert_eq!(get_pos(&(p.clone(), 3)), p);
        let hint = Hint(p.clone(), Box::new(Hint_::Hmixed));
        assert_eq!(get_pos(&hint), p);
        assert!(equal_id(&id, &id.clone()));
        assert!(!equal_id(&id, &Id(Pos::NONE, "\\Foo".to_string())));
        assert!(!equal_id(&id, &Id(p, "\\Bar".to_string())));
    }
}
