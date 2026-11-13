// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_tag_defs.ml`. See `hh/PORTING.md`.
//!
//! `[@@deriving eq]` is the function [`equal`] (the types do not implement
//! `PartialEq`: the equality of [`Generic`] is `ty_equal`, which ignores
//! reasons, and that of [`ClassKind`] pads the shorter list of generics).

use crate::typing_defs_core::Ty;
use crate::typing_defs_core::ty_equal;

#[derive(Clone, Debug)]
pub enum Generic {
    Reified(Ty),
    Erased,
}

pub fn equal_generic(a: &Generic, b: &Generic) -> bool {
    match (a, b) {
        (Generic::Erased, Generic::Erased) => true,
        (Generic::Reified(a), Generic::Reified(b)) => ty_equal(None, a, b),
        _ => false,
    }
}

#[derive(Clone, Debug)]
pub enum ClassKind {
    Class(Vec<Generic>),
    FinalClass(Vec<Generic>),
    Interface,
}

pub fn equal_class_kind(a: &ClassKind, b: &ClassKind) -> bool {
    match (a, b) {
        (ClassKind::Class(a_generics), ClassKind::Class(b_generics))
        | (ClassKind::FinalClass(a_generics), ClassKind::FinalClass(b_generics)) => {
            // The OCaml defines its own `zip_generics` here (the module-level
            // one comes after this function); it is the same function.
            fn zip_generics(al: &[Generic], bl: &[Generic]) -> Vec<(Generic, Generic)> {
                match (al, bl) {
                    ([], []) => vec![],
                    ([a, al @ ..], [b, bl @ ..]) => {
                        let mut res = vec![(a.clone(), b.clone())];
                        res.extend(zip_generics(al, bl));
                        res
                    }
                    ([a, al @ ..], []) => {
                        let mut res = vec![(a.clone(), Generic::Erased)];
                        res.extend(zip_generics(al, bl));
                        res
                    }
                    ([], [b, bl @ ..]) => {
                        let mut res = vec![(Generic::Erased, b.clone())];
                        res.extend(zip_generics(al, bl));
                        res
                    }
                }
            }
            let pairs = zip_generics(a_generics, b_generics);
            pairs.iter().all(|(a, b)| equal_generic(a, b))
        }
        (ClassKind::Interface, ClassKind::Interface) => true,
        _ => false,
    }
}

/// Modelled after data types in HHVM. See hphp/runtime/base/datatype.h
#[derive(Clone, Debug)]
pub enum T {
    DictData,
    ShapeData,
    VecData,
    TupleData,
    KeysetData,
    StringData,
    ResourceData,
    BoolData,
    IntData,
    FloatData,
    NullData,
    ObjectData,
    InstanceOf {
        name: String,
        kind: ClassKind,
    },
    /// Corresponds to class pointers: KindOfClass / KindOfLazyClass
    ClassData,
    /// Corresponds to EnumClassLabel
    LabelData,
    /// Catch all for data types that are built into the runtime but not
    /// exposed in the type system. Used primarily for soundly representing
    /// the mixed type
    BuiltInData,
    /// An enum value of the given enum
    EnumData(String),
    /// A value matching a runtime-checkable rigid generic (a reified type
    /// parameter, [this::TC] with [<<__Enforceable>>], or [this]). Carries
    /// the localized generic identifier. Treated imprecisely: relations
    /// with all other tags default to [SetRelation.none]. Excluded from
    /// [all_tags] for the same complement-yields-mixed reason as
    /// [EnumData].
    GenericData(String),
}

/// `[@@deriving eq]`
pub fn equal(a: &T, b: &T) -> bool {
    use T::*;
    match (a, b) {
        (DictData, DictData)
        | (ShapeData, ShapeData)
        | (VecData, VecData)
        | (TupleData, TupleData)
        | (KeysetData, KeysetData)
        | (StringData, StringData)
        | (ResourceData, ResourceData)
        | (BoolData, BoolData)
        | (IntData, IntData)
        | (FloatData, FloatData)
        | (NullData, NullData)
        | (ObjectData, ObjectData)
        | (ClassData, ClassData)
        | (LabelData, LabelData)
        | (BuiltInData, BuiltInData) => true,
        (
            InstanceOf {
                name: name1,
                kind: kind1,
            },
            InstanceOf {
                name: name2,
                kind: kind2,
            },
        ) => name1 == name2 && equal_class_kind(kind1, kind2),
        (EnumData(a), EnumData(b)) => a == b,
        (GenericData(a), GenericData(b)) => a == b,
        _ => false,
    }
}

/// Pad with Erased because for Foo<T>, Foo and Foo<_> should be the same;
/// It's also convenient to not check for arity mismatch and failwith
pub fn zip_generics(al: &[Generic], bl: &[Generic]) -> Vec<(Generic, Generic)> {
    match (al, bl) {
        ([], []) => vec![],
        ([a, al @ ..], [b, bl @ ..]) => {
            let mut res = vec![(a.clone(), b.clone())];
            res.extend(zip_generics(al, bl));
            res
        }
        ([a, al @ ..], []) => {
            let mut res = vec![(a.clone(), Generic::Erased)];
            res.extend(zip_generics(al, bl));
            res
        }
        ([], [b, bl @ ..]) => {
            let mut res = vec![(Generic::Erased, b.clone())];
            res.extend(zip_generics(al, bl));
            res
        }
    }
}

pub fn has_reified(kind: &ClassKind) -> bool {
    match kind {
        ClassKind::Interface => false,
        ClassKind::Class(generics) | ClassKind::FinalClass(generics) => {
            generics.iter().any(|g| match g {
                Generic::Reified(_) => true,
                Generic::Erased => false,
            })
        }
    }
}

pub fn get_generics_from_kind(kind: &ClassKind) -> Vec<Generic> {
    match kind {
        ClassKind::Class(generics) | ClassKind::FinalClass(generics) => generics.clone(),
        ClassKind::Interface => vec![],
    }
}

/// `val all_nonnull_tags : t list`
pub fn all_nonnull_tags() -> Vec<T> {
    use T::*;
    vec![
        DictData,
        VecData,
        KeysetData,
        StringData,
        ResourceData,
        BoolData,
        IntData,
        FloatData,
        ObjectData,
        ClassData,
        LabelData,
        BuiltInData,
    ]
}

/// `val all_tags : t list`
pub fn all_tags() -> Vec<T> {
    let mut tags = vec![T::NullData];
    tags.extend(all_nonnull_tags());
    tags
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;
    use crate::typing_reason;

    fn int() -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(Tprim::Tint)))
    }

    fn float() -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(Tprim::Tfloat)))
    }

    #[test]
    fn zip_pads_with_erased() {
        let a = [Generic::Reified(int())];
        let b = [Generic::Erased, Generic::Erased];
        let zipped = zip_generics(&a, &b);
        assert_eq!(zipped.len(), 2);
        assert!(matches!(zipped[1], (Generic::Erased, Generic::Erased)));
    }

    #[test]
    fn class_kinds_compare_modulo_trailing_erased() {
        let foo = ClassKind::Class(vec![]);
        let foo_ = ClassKind::Class(vec![Generic::Erased]);
        assert!(equal_class_kind(&foo, &foo_));
        let foo_int = ClassKind::Class(vec![Generic::Reified(int())]);
        let foo_float = ClassKind::Class(vec![Generic::Reified(float())]);
        assert!(!equal_class_kind(&foo, &foo_int));
        assert!(!equal_class_kind(&foo_int, &foo_float));
        assert!(equal_class_kind(&foo_int, &foo_int.clone()));
        assert!(!equal_class_kind(&foo, &ClassKind::FinalClass(vec![])));
        assert!(equal(
            &T::InstanceOf {
                name: "C".to_string(),
                kind: foo
            },
            &T::InstanceOf {
                name: "C".to_string(),
                kind: foo_
            }
        ));
    }

    #[test]
    fn tags() {
        assert_eq!(all_nonnull_tags().len(), 12);
        let all = all_tags();
        assert_eq!(all.len(), 13);
        assert!(matches!(all[0], T::NullData));
        assert!(has_reified(&ClassKind::FinalClass(vec![
            Generic::Erased,
            Generic::Reified(int())
        ])));
        assert!(!has_reified(&ClassKind::Interface));
    }
}
