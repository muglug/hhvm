// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tast_utils.ml`. See `hh/PORTING.md`.
//!
//! OCaml builds the types of `tclass_is_falsy_when_empty` and
//! `is_traversable` once, when the module is initialised; here they are
//! built at each call (building them has no effect).

use naming_special_names_rust as sn;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Tprim;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::tast_env;
use crate::tast_env::Env;
use crate::typing_defs;
use crate::typing_defs::ShapeType;
use crate::typing_defs::ShapeTypeSimple;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_make_type as make_type;
use crate::typing_reason;
use crate::typing_utils;

/// Return true if ty definitely does not contain null.  I.e., the
/// return value false can mean two things: ty does contain null, e.g.,
/// it is an option type; or we cannot tell, e.g., it is an opaque
/// newtype.
pub fn type_non_nullable(env: &Env, ty: &Ty) -> bool {
    let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tprim(
            Tprim::Tint
            | Tprim::Tbool
            | Tprim::Tfloat
            | Tprim::Tresource
            | Tprim::Tnum
            | Tprim::Tarraykey
            | Tprim::Tnoreturn,
        )
        | Ty_::Tnonnull
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tclass(..) => true,
        Ty_::Tdependent(_, ty) if type_non_nullable(env, ty) => true,
        Ty_::Tnewtype(name, tyl, _) => {
            let ty = typing_utils::get_newtype_super(
                &mut env.clone(),
                get_reason(&ty).clone(),
                name,
                tyl,
            );
            type_non_nullable(env, &ty)
        }
        Ty_::Tunion(tyl) if !tyl.is_empty() => tyl.iter().all(|ty| type_non_nullable(env, ty)),
        _ => false,
    }
}

// Truthiness utilities ******************************************************
// For types other than bool used in condition expressions, boolean binary
// expressions, and casts to bool. An always-truthy type used in a condition is
// always a logic error.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Truthiness {
    Unknown,
    AlwaysTruthy,
    AlwaysFalsy,
    PossiblyFalsy,
}

fn fold_truthiness(acc: Truthiness, truthiness: Truthiness) -> Truthiness {
    use Truthiness::*;
    match (acc, truthiness) {
        (Unknown, _) | (_, Unknown) => Unknown,
        (AlwaysTruthy, AlwaysTruthy) => AlwaysTruthy,
        (AlwaysFalsy, AlwaysFalsy) => AlwaysFalsy,
        (PossiblyFalsy, PossiblyFalsy) => PossiblyFalsy,
        _ => PossiblyFalsy,
    }
}

fn intersect_truthiness(tr1: Truthiness, tr2: Truthiness) -> Truthiness {
    use Truthiness::*;
    match (tr1, tr2) {
        (Unknown, PossiblyFalsy) | (PossiblyFalsy, Unknown) => Unknown,
        (Unknown, tr) | (tr, Unknown) => tr,
        (AlwaysTruthy, _) | (_, AlwaysTruthy) => AlwaysTruthy,
        (AlwaysFalsy, _) | (_, AlwaysFalsy) => AlwaysFalsy,
        (PossiblyFalsy, PossiblyFalsy) => PossiblyFalsy,
    }
}

fn tclass_is_falsy_when_empty(env: &Env, ty: &Ty) -> bool {
    let r = typing_reason::none();
    let mixed = make_type::mixed(r.clone());
    let simple_xml_el = make_type::class_type(r.clone(), "\\SimpleXMLElement".to_string(), vec![]);
    let container_type = make_type::container(r.clone(), mixed.clone());
    let pair_type = make_type::pair(r, mixed.clone(), mixed);
    tast_env::can_subtype(env, ty, &simple_xml_el)
        || tast_env::can_subtype(env, ty, &container_type)
            && !tast_env::can_subtype(env, ty, &pair_type)
}

fn is_traversable(env: &Env, ty: &Ty) -> bool {
    let r = typing_reason::none();
    let mixed = make_type::mixed(r.clone());
    let trv = make_type::traversable(r, mixed);
    tast_env::can_subtype(env, ty, &trv)
}

/// `match List.map tyl ~f with [] -> Unknown | hd :: tl -> List.fold tl ~init:hd ~f:fold_truthiness`
fn fold_truthinesses(tyl: Vec<Truthiness>) -> Truthiness {
    let mut tyl = tyl.into_iter();
    match tyl.next() {
        None => Truthiness::Unknown,
        Some(hd) => tyl.fold(hd, fold_truthiness),
    }
}

/// Return the [`Truthiness`] of `ty`. Only possibly-falsy types are suitable
/// scrutinees in a truthiness test--it is reasonable to test the truthiness of
/// nullable types and container types which are falsy when empty. Other types
/// (e.g. user-defined objects) are always truthy, so testing their truthiness
/// indicates a logic error.
pub fn truthiness(env: &Env, ty: &Ty) -> Truthiness {
    use Truthiness::*;
    let mut env = env.clone();
    let ty = tast_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Tvar(_) => Unknown,
        Ty_::Tnonnull | Ty_::Tneg(_) | Ty_::Toption(_) => PossiblyFalsy,
        Ty_::Tnewtype(id, _, _) if tast_env::is_enum(&env, id) => PossiblyFalsy,
        Ty_::Tclass((_, cid), _, _) => {
            if cid == sn::typehints::HH_STRING {
                PossiblyFalsy
            } else if cid == sn::classes::STRINGISH {
                PossiblyFalsy
            } else if cid == sn::classes::XHP_CHILD {
                PossiblyFalsy
            } else if tclass_is_falsy_when_empty(&env, &ty) {
                PossiblyFalsy
            } else if !is_traversable(&env, &ty) {
                AlwaysTruthy
            } else {
                // Classes which implement Traversable but not Container will always be
                // truthy when empty. If this Tclass is instead an interface type like
                // KeyedTraversable, the value may or may not be truthy when empty.
                match tast_env::get_class(&env, cid) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => Unknown,
                    decl_entry::T::Found(cls) => match cls::kind(&cls) {
                        ClassishKind::Cclass(_) => AlwaysTruthy,
                        ClassishKind::Cinterface
                        | ClassishKind::Cenum
                        | ClassishKind::CenumClass(_) => PossiblyFalsy,
                        ClassishKind::Ctrait => Unknown,
                    },
                }
            }
        }
        Ty_::Tlabel(_) => AlwaysTruthy,
        Ty_::Tprim(Tprim::Tresource) => AlwaysTruthy,
        Ty_::Tprim(Tprim::Tnull) => AlwaysFalsy,
        Ty_::Tprim(Tprim::Tvoid) => AlwaysFalsy,
        Ty_::Tprim(Tprim::Tnoreturn) => Unknown,
        Ty_::Tprim(Tprim::Tint | Tprim::Tbool | Tprim::Tfloat | Tprim::Tnum | Tprim::Tarraykey) => {
            PossiblyFalsy
        }
        Ty_::Tunion(tyl) => fold_truthinesses(tyl.iter().map(|ty| truthiness(&env, ty)).collect()),
        Ty_::Tintersection(tyl) => tyl
            .iter()
            .map(|ty| truthiness(&env, ty))
            .collect::<Vec<_>>()
            .into_iter()
            .fold(PossiblyFalsy, intersect_truthiness),
        Ty_::Tgeneric(_) | Ty_::Tnewtype(..) | Ty_::Tdependent(..) => {
            let tyl = tast_env::get_concrete_supertypes(None, true, &mut env, ty.clone());
            fold_truthinesses(tyl.iter().map(|ty| truthiness(&env, ty)).collect())
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: shape_kind,
            fields,
        })) => {
            if typing_defs::is_nothing(shape_kind) && fields.is_empty() {
                AlwaysFalsy
            } else {
                let has_non_optional_fields = fields
                    .iter()
                    .fold(false, |acc, (_, sft)| !sft.optional || acc);
                if has_non_optional_fields {
                    AlwaysTruthy
                } else {
                    PossiblyFalsy
                }
            }
        }
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => Unknown,
        Ty_::Ttuple(TupleType {
            required,
            optional,
            extra: TupleExtra::Tvariadic(t_variadic),
        }) if required.is_empty() && optional.is_empty() && typing_defs::is_nothing(t_variadic) => {
            AlwaysFalsy
        }
        // A tuple is a vec at runtime, and non-empty vecs are truthy.
        Ty_::Ttuple(TupleType { required, .. }) if !required.is_empty() => AlwaysTruthy,
        Ty_::Ttuple(_) => PossiblyFalsy,
        Ty_::Tfun(_) => AlwaysTruthy,
        Ty_::Taccess(_) => Unknown,
        Ty_::TvecOrDict(..) => PossiblyFalsy,
        Ty_::TclassPtr(_) => AlwaysTruthy,
    }
}

/// When a type represented by one of these variants is used in a truthiness
/// test, it indicates a potential logic error, since the truthiness of some
/// values in the type may be surprising.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SketchyTypeKind {
    String,
    Arraykey,
    Stringish,
    /// Truthiness tests on strings may not behave as expected. The user may not
    /// know that the string "0" is falsy, and may have intended only to check for
    /// emptiness.
    XHPChild,
    /// Interface types which implement Traversable but not Container may be
    /// always truthy, even when empty.
    TraversableInterface(String),
}

/// The list is in the order of the OCaml list (its head first).
pub fn find_sketchy_types(env: &Env, ty: &Ty) -> Vec<SketchyTypeKind> {
    fn cons(x: SketchyTypeKind, mut acc: Vec<SketchyTypeKind>) -> Vec<SketchyTypeKind> {
        acc.insert(0, x);
        acc
    }

    fn find_sketchy_types(
        env: &Env,
        acc: Vec<SketchyTypeKind>,
        ty: &Ty,
    ) -> Vec<SketchyTypeKind> {
        use SketchyTypeKind::*;
        let mut env = env.clone();
        let ety = tast_env::expand_type(&mut env, ty.clone());
        match get_node(&ety) {
            Ty_::Toption(ty) => find_sketchy_types(&env, acc, ty),
            Ty_::Tprim(Tprim::Tarraykey) => cons(Arraykey, acc),
            Ty_::Tclass((_, cid), _, _) => {
                if cid == sn::typehints::HH_STRING {
                    cons(String, acc)
                } else if cid == sn::classes::STRINGISH {
                    cons(Stringish, acc)
                } else if cid == sn::classes::XHP_CHILD {
                    cons(XHPChild, acc)
                } else if tclass_is_falsy_when_empty(&env, ty) || !is_traversable(&env, ty) {
                    acc
                } else {
                    match tast_env::get_class(&env, cid) {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
                        decl_entry::T::Found(cls) => match cls::kind(&cls) {
                            ClassishKind::Cinterface => {
                                cons(TraversableInterface(tast_env::print_ty(&env, ty)), acc)
                            }
                            ClassishKind::Cclass(_)
                            | ClassishKind::Ctrait
                            | ClassishKind::CenumClass(_)
                            | ClassishKind::Cenum => acc,
                        },
                    }
                }
            }
            Ty_::Tunion(tyl) => tyl
                .iter()
                .fold(acc, |acc, ty| find_sketchy_types(&env, acc, ty)),
            Ty_::Tintersection(tyl) => {
                // If one of the types in tyl does not have any sketchy type, then it's ok.
                let sketchy_tys: Vec<Vec<SketchyTypeKind>> = tyl
                    .iter()
                    .map(|ty| find_sketchy_types(&env, vec![], ty))
                    .collect();
                let mut sketchy_tys = if sketchy_tys.iter().any(|l| l.is_empty()) {
                    vec![]
                } else {
                    sketchy_tys.into_iter().fold(vec![], |mut l1, l2| {
                        l1.extend(l2);
                        l1
                    })
                };
                // sketchy_tys @ acc
                sketchy_tys.extend(acc);
                sketchy_tys
            }
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) | Ty_::Tdependent(..) => {
                let tyl = tast_env::get_concrete_supertypes(None, true, &mut env, ty.clone());
                tyl.iter()
                    .fold(acc, |acc, ty| find_sketchy_types(&env, acc, ty))
            }
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tdynamic(_)
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::Tshape(_)
            | Ty_::Tvar(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::Tlabel(_)
            | Ty_::Tneg(_) => acc,
            Ty_::TclassPtr(_) => acc,
        }
    }

    find_sketchy_types(env, vec![], ty)
}

#[cfg(test)]
mod tests {
    use super::Truthiness::*;
    use super::*;

    #[test]
    fn fold_and_intersect() {
        assert_eq!(fold_truthiness(AlwaysTruthy, Unknown), Unknown);
        assert_eq!(fold_truthiness(AlwaysTruthy, AlwaysTruthy), AlwaysTruthy);
        assert_eq!(fold_truthiness(AlwaysTruthy, AlwaysFalsy), PossiblyFalsy);
        assert_eq!(fold_truthiness(AlwaysFalsy, AlwaysFalsy), AlwaysFalsy);
        assert_eq!(intersect_truthiness(Unknown, PossiblyFalsy), Unknown);
        assert_eq!(intersect_truthiness(AlwaysFalsy, Unknown), AlwaysFalsy);
        assert_eq!(intersect_truthiness(PossiblyFalsy, AlwaysTruthy), AlwaysTruthy);
        assert_eq!(intersect_truthiness(AlwaysFalsy, PossiblyFalsy), AlwaysFalsy);
        assert_eq!(intersect_truthiness(AlwaysTruthy, AlwaysFalsy), AlwaysTruthy);
        assert_eq!(
            intersect_truthiness(PossiblyFalsy, PossiblyFalsy),
            PossiblyFalsy
        );
        assert_eq!(fold_truthinesses(vec![]), Unknown);
        assert_eq!(
            fold_truthinesses(vec![AlwaysFalsy, AlwaysFalsy]),
            AlwaysFalsy
        );
    }
}
