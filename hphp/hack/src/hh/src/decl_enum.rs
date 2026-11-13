// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_enum.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use pos::BPos;
use pos::Positioned;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl::ClassConst;
use ty::decl::EnumType;
use ty::decl::Prim;
use ty::decl::TaccessType;
use ty::decl::Ty;
use ty::decl::Ty_;

use crate::ctx::R;
use crate::decl_utils::get_pos;
use crate::decl_utils::reason_to_pos;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct T {
    /// Underlying type of the enum, e.g. int or string.
    /// For subclasses of Enum, this is the type parameter of Enum.
    /// For enum classes, this is HH\MemberOf<E, I>.
    pub base: Ty<R>,
    /// Type containing the enum name.
    /// For subclasses of Enum, this is also the type parameter of Enum.
    pub type_: Ty<R>,
    /// Reflects what's after the [as] keyword in the enum definition.
    pub constraint_: Option<Ty<R>>,
    /// For enum classes, this is the raw interface I, as provided by the user.
    pub interface: Option<Ty<R>>,
}

/// Figures out if a class needs to be treated like an enum.
pub fn enum_kind(
    name: &Positioned<TypeName, BPos>,
    is_enum_class: bool,
    add_like: bool,
    enum_: Option<&EnumType<R>>,
    inner_ty: Option<&Ty<R>>,
    get_ancestor: impl Fn(&str) -> Option<Ty<R>>,
) -> Option<T> {
    match enum_ {
        None => match get_ancestor(sn::fb::ENUM) {
            Some(enum_) => match enum_.node_ref() {
                Ty_::Tapply(id_and_args)
                    if id_and_args.0.id_ref().as_str() == sn::fb::ENUM
                        && id_and_args.1.len() == 1 =>
                {
                    let ty_exp = &id_and_args.1[0];
                    Some(T {
                        base: ty_exp.clone(),
                        type_: ty_exp.clone(),
                        constraint_: None,
                        interface: None,
                    })
                }
                Ty_::Tapply(id_and_args) if id_and_args.0.id_ref().as_str() == sn::fb::ENUM => {
                    let ty_exp =
                        // The fallback if the class does not declare TInner (i.e. it is
                        // abstract) is to use this::TInner
                        match inner_ty {
                            None => {
                                let this = Ty::new(enum_.reason().clone(), Ty_::Tthis);
                                Ty::new(
                                    enum_.reason().clone(),
                                    Ty_::Taccess(Box::new(TaccessType {
                                        ty: this,
                                        type_const: Positioned::new(
                                            get_pos(&enum_),
                                            TypeConstName::new(sn::fb::INNER),
                                        ),
                                    })),
                                )
                            }
                            Some(ty) => ty.clone(),
                        };
                    Some(T {
                        base: ty_exp.clone(),
                        type_: ty_exp,
                        constraint_: None,
                        interface: None,
                    })
                }
                _ => None,
            },
            _ => None,
        },
        Some(enum_) => {
            let reason = enum_.base.reason().clone();
            let pos = reason_to_pos(&reason);
            let enum_type = Ty::new(
                reason.clone(),
                Ty_::Tapply(Box::new((name.clone(), Box::new([])))),
            );
            let (te_base, te_interface) = if is_enum_class {
                let te_interface = enum_.base.clone();
                let te_base = Ty_::Tapply(Box::new((
                    Positioned::new(pos, TypeName::new(sn::classes::MEMBER_OF)),
                    Box::new([
                        enum_type,
                        if add_like {
                            Ty::new(reason.clone(), Ty_::Tlike(enum_.base.clone()))
                        } else {
                            enum_.base.clone()
                        },
                    ]),
                )));
                // TODO(T77095784) make a new reason !
                let te_base = Ty::new(reason, te_base);
                (te_base, Some(te_interface))
            } else {
                (enum_.base.clone(), None)
            };
            Some(T {
                base: te_base,
                type_: Ty::new(
                    enum_.base.reason().clone(),
                    Ty_::Tapply(Box::new((name.clone(), Box::new([])))),
                ),
                constraint_: enum_.constraint.clone(),
                interface: te_interface,
            })
        }
    }
}

/// If a class is an Enum, we give all of the constants in the class the type
/// of the Enum. We don't do this for Enum<mixed> and Enum<arraykey>, since
/// that could *lose* type information.
pub fn rewrite_class(
    name: &Positioned<TypeName, BPos>,
    is_enum_class: bool,
    enum_: Option<&EnumType<R>>,
    inner_ty: Option<&Ty<R>>,
    get_ancestor: impl Fn(&str) -> Option<Ty<R>>,
    consts: im::OrdMap<String, ClassConst<R>>,
) -> im::OrdMap<String, ClassConst<R>> {
    match enum_kind(name, is_enum_class, false, enum_, inner_ty, get_ancestor) {
        None => consts,
        Some(T {
            base: _,
            type_: ty,
            constraint_: _,
            interface: te_interface,
        }) => {
            let te_enum_class = te_interface.is_some();
            match ty.node_ref() {
                Ty_::Tmixed | Ty_::Tprim(Prim::Tarraykey) => consts,
                _ => {
                    // A special constant called "class" gets added, and we don't
                    // want to rewrite its type.
                    // Also for enum class, the type is set in the lowerer.
                    (consts.into_iter())
                        .map(|(k, c)| {
                            if te_enum_class || k == sn::members::M_CLASS {
                                (k, c)
                            } else {
                                let c = ClassConst {
                                    ty: ty.clone(),
                                    ..c
                                };
                                (k, c)
                            }
                        })
                        .collect()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ty::reason::Reason;

    use super::*;

    fn int() -> Ty<R> {
        Ty::prim(R::none(), Prim::Tint)
    }

    fn name(n: &str) -> Positioned<TypeName, BPos> {
        Positioned::new(BPos::none(), TypeName::new(n))
    }

    fn apply(n: &str, args: Vec<Ty<R>>) -> Ty<R> {
        Ty::apply(R::none(), name(n), args.into())
    }

    fn class_const(ty: Ty<R>) -> ClassConst<R> {
        ClassConst {
            is_synthesized: false,
            kind: ty::decl::ClassConstKind::CCConcrete,
            pos: BPos::none(),
            ty,
            origin: TypeName::new("\\E"),
            refs: Box::new([]),
            value: ty::decl::ConstValue::CVAbsent,
        }
    }

    #[test]
    fn not_an_enum() {
        assert_eq!(
            enum_kind(&name("\\C"), false, false, None, None, |_| None),
            None
        );
        // An ancestor that is not `Enum<_>`.
        let kind = enum_kind(&name("\\C"), false, false, None, None, |_| {
            Some(apply("\\D", vec![int()]))
        });
        assert_eq!(kind, None);
    }

    #[test]
    fn subclass_of_enum() {
        let kind = enum_kind(&name("\\C"), false, false, None, None, |ancestor| {
            assert_eq!(ancestor, "\\Enum");
            Some(apply("\\Enum", vec![int()]))
        })
        .unwrap();
        assert_eq!(kind.base, int());
        assert_eq!(kind.type_, int());
        assert_eq!(kind.constraint_, None);
        assert_eq!(kind.interface, None);
    }

    #[test]
    fn subclass_of_enum_without_argument_uses_tinner() {
        let get_ancestor = |_: &str| Some(apply("\\Enum", vec![]));
        let kind = enum_kind(&name("\\C"), false, false, None, None, get_ancestor).unwrap();
        match kind.base.node_ref() {
            Ty_::Taccess(ta) => {
                assert_eq!(ta.ty.node_ref(), &Ty_::Tthis);
                assert_eq!(ta.type_const.id_ref().as_str(), "TInner");
            }
            ty => panic!("{:?}", ty),
        }
        let kind = enum_kind(&name("\\C"), false, false, None, Some(&int()), get_ancestor).unwrap();
        assert_eq!(kind.base, int());
    }

    #[test]
    fn enum_and_enum_class() {
        let arraykey = Ty::prim(R::none(), Prim::Tarraykey);
        let enum_type = EnumType {
            base: int(),
            constraint: Some(arraykey.clone()),
            includes: Box::new([]),
        };
        let no_ancestor =
            |_: &str| -> Option<Ty<R>> { panic!("an enum has no need of its ancestors") };
        let e = name("\\E");
        let kind = enum_kind(&e, false, false, Some(&enum_type), None, no_ancestor).unwrap();
        assert_eq!(kind.base, int());
        assert_eq!(kind.type_, apply("\\E", vec![]));
        assert_eq!(kind.constraint_, Some(arraykey));
        assert_eq!(kind.interface, None);

        let kind = enum_kind(&e, true, false, Some(&enum_type), None, no_ancestor).unwrap();
        assert_eq!(
            kind.base,
            apply("\\HH\\MemberOf", vec![apply("\\E", vec![]), int()])
        );
        assert_eq!(kind.type_, apply("\\E", vec![]));
        assert_eq!(kind.interface, Some(int()));

        let kind = enum_kind(&e, true, true, Some(&enum_type), None, no_ancestor).unwrap();
        let like_int = Ty::new(R::none(), Ty_::Tlike(int()));
        assert_eq!(
            kind.base,
            apply("\\HH\\MemberOf", vec![apply("\\E", vec![]), like_int])
        );
    }

    #[test]
    fn rewrite() {
        let string = Ty::prim(R::none(), Prim::Tfloat);
        let consts: im::OrdMap<String, ClassConst<R>> = [
            ("A".to_string(), class_const(string.clone())),
            ("class".to_string(), class_const(string.clone())),
        ]
        .into_iter()
        .collect();
        let enum_type = EnumType {
            base: int(),
            constraint: None,
            includes: Box::new([]),
        };
        let e = name("\\E");
        let no_ancestor = |_: &str| -> Option<Ty<R>> { None };

        // An enum: every constant but `class` gets the type of the enum.
        let rewritten = rewrite_class(
            &e,
            false,
            Some(&enum_type),
            None,
            no_ancestor,
            consts.clone(),
        );
        assert_eq!(rewritten["A"].ty, apply("\\E", vec![]));
        assert_eq!(rewritten["class"].ty, string);

        // An enum class: the types were set by the lowerer.
        let rewritten = rewrite_class(
            &e,
            true,
            Some(&enum_type),
            None,
            no_ancestor,
            consts.clone(),
        );
        assert_eq!(rewritten, consts);

        // Not an enum.
        let rewritten = rewrite_class(&e, false, None, None, no_ancestor, consts.clone());
        assert_eq!(rewritten, consts);

        // Enum<arraykey> and Enum<mixed> would lose information.
        for ty in [Ty::prim(R::none(), Prim::Tarraykey), Ty::mixed(R::none())] {
            let get_ancestor = |_: &str| Some(apply("\\Enum", vec![ty.clone()]));
            let rewritten = rewrite_class(&e, false, None, None, get_ancestor, consts.clone());
            assert_eq!(rewritten, consts);
        }
        let get_ancestor = |_: &str| Some(apply("\\Enum", vec![int()]));
        let rewritten = rewrite_class(&e, false, None, None, get_ancestor, consts.clone());
        assert_eq!(rewritten["A"].ty, int());
        assert_eq!(rewritten["class"].ty, string);
    }
}
