// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl/decl_instantiate.ml`. See `hh/PORTING.md`.
//!
//! hackrs has an instantiation of its own
//! (`folded_decl_provider::Substitution`), which class folding uses. It is
//! *not* equivalent to `Decl_instantiate.instantiate`, so nothing here
//! delegates to it:
//!
//! - in a function type, it does not rename the function's own type parameters
//!   away from the generics that occur in the substitution's targets (the
//!   `T#0` renaming below);
//! - it instantiates the right-hand side of a function's `where` constraints
//!   with the substitution *before* the function's own type parameters were
//!   removed from it;
//! - it instantiates the type of the unknown fields of a shape, which the
//!   OCaml leaves alone.

use std::collections::BTreeSet;

use pos::Positioned;
use pos::TypeName;
use ty::decl::AbstractTypeconst;
use ty::decl::ClassConst;
use ty::decl::ClassRefinement;
use ty::decl::ConcreteTypeconst;
use ty::decl::FunParam;
use ty::decl::FunType;
use ty::decl::RefinedConst;
use ty::decl::RefinedConstBound;
use ty::decl::RefinedConstBounds;
use ty::decl::ShapeFieldType;
use ty::decl::TaccessType;
use ty::decl::Tparam;
use ty::decl::TrefinementType;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::Typeconst;
use ty::decl::WhereConstraint;
use ty::decl::ty::Capability;
use ty::decl::ty::ShapeType;
use ty::decl::ty::ShapeTypeSimple;
use ty::decl::ty::TupleExtra;
use ty::decl::ty::TupleType;
use ty::reason::Reason;

use crate::ctx::R;
use crate::decl_subst as subst;
use crate::decl_subst::DeclSubst;
use crate::decl_subst::TpName;
use crate::folded_class::ClassElt;

pub fn make_subst<TP: TpName>(tparams: &[TP], tyl: &[Ty<R>]) -> DeclSubst {
    subst::make_decl(tparams, tyl)
}

/// The OCaml is an object that inherits `Type_visitor.decl_type_visitor` and
/// overrides `on_tgeneric`. This is that visitor's traversal, written out: it
/// reaches the same types (the set it computes does not depend on the order).
fn get_tparams_in_ty_and_acc(mut acc: BTreeSet<TypeName>, ty: &Ty<R>) -> BTreeSet<TypeName> {
    let on_types =
        |acc: BTreeSet<TypeName>, tyl: &[Ty<R>]| tyl.iter().fold(acc, get_tparams_in_ty_and_acc);
    match ty.node_ref() {
        Ty_::Tany
        | Ty_::Tmixed
        | Ty_::Twildcard
        | Ty_::Tnonnull
        | Ty_::Tdynamic
        | Ty_::Tthis
        | Ty_::Tprim(_) => acc,
        Ty_::TvecOrDict(tys) => {
            let (ty1, ty2) = &**tys;
            let acc = get_tparams_in_ty_and_acc(acc, ty1);
            get_tparams_in_ty_and_acc(acc, ty2)
        }
        Ty_::Tgeneric(s) => {
            acc.insert(*s);
            acc
        }
        Ty_::Toption(ty) | Ty_::Tlike(ty) | Ty_::TclassPtr(ty) => {
            get_tparams_in_ty_and_acc(acc, ty)
        }
        Ty_::Tfun(ft) => {
            let acc =
                (ft.params.iter()).fold(acc, |acc, fp| get_tparams_in_ty_and_acc(acc, &fp.ty));
            let acc = ft.tparams.iter().fold(acc, |acc, tp| {
                (tp.constraints.iter())
                    .fold(acc, |acc, (_ck, ty)| get_tparams_in_ty_and_acc(acc, ty))
            });
            let acc = match &ft.implicit_params.capability {
                Capability::CapDefaults(_) => acc,
                Capability::CapTy(ty) => get_tparams_in_ty_and_acc(acc, ty),
            };
            let acc =
                (ft.where_constraints.iter()).fold(acc, |acc, WhereConstraint(ty1, _ck, ty2)| {
                    let acc = get_tparams_in_ty_and_acc(acc, ty1);
                    get_tparams_in_ty_and_acc(acc, ty2)
                });
            get_tparams_in_ty_and_acc(acc, &ft.ret)
        }
        Ty_::Tapply(id_and_args) => {
            let (_, tyl) = &**id_and_args;
            on_types(acc, tyl)
        }
        Ty_::Trefinement(tr) => {
            let acc = get_tparams_in_ty_and_acc(acc, &tr.ty);
            // Class_refinement.fold
            tr.refinement
                .consts
                .values()
                .fold(acc, |acc, rc| match &rc.bound {
                    RefinedConstBound::Exact(ty) => get_tparams_in_ty_and_acc(acc, ty),
                    RefinedConstBound::Loose(bounds) => {
                        let acc = on_types(acc, &bounds.lower);
                        on_types(acc, &bounds.upper)
                    }
                })
        }
        Ty_::Taccess(ta) => get_tparams_in_ty_and_acc(acc, &ta.ty),
        Ty_::Ttuple(tuple) => {
            let TupleType(t_required, t_optional, t_extra) = &**tuple;
            let acc = match t_extra {
                TupleExtra::Tsplat(t_splat) => get_tparams_in_ty_and_acc(acc, t_splat),
                TupleExtra::Tvariadic(t_variadic) => get_tparams_in_ty_and_acc(acc, t_variadic),
            };
            let acc = on_types(acc, t_optional);
            on_types(acc, t_required)
        }
        Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => on_types(acc, tyl),
        Ty_::Tshape(shape_ty) => match &**shape_ty {
            ShapeType::Simple(ShapeTypeSimple(kind, fdm)) => {
                let acc = get_tparams_in_ty_and_acc(acc, kind);
                (fdm.values()).fold(acc, |acc, sft| get_tparams_in_ty_and_acc(acc, &sft.ty))
            }
            ShapeType::Splat(ss_elems) => on_types(acc, ss_elems),
        },
    }
}

fn get_tparams_in_subst(subst: &DeclSubst) -> BTreeSet<TypeName> {
    (subst.0.values()).fold(BTreeSet::new(), get_tparams_in_ty_and_acc)
}

//*****************************************************************************
// Code dealing with instantiation.
//*****************************************************************************

pub fn instantiate(subst: &DeclSubst, ty: &Ty<R>) -> Ty<R> {
    // PERF: If subst is empty then instantiation is a no-op. We can save a
    // significant amount of CPU by avoiding recursively deconstructing the ty
    // data type.
    if subst.0.is_empty() {
        ty.clone()
    } else {
        let r = ty.reason().clone();
        match ty.node_ref() {
            Ty_::Tgeneric(x) => match subst.0.get(x) {
                Some(found_ty) => {
                    let found_r = found_ty.reason().clone();
                    let found_ty_ = found_ty.node_ref().clone();
                    let new_r = R::instantiate(found_r, *x, r);
                    Ty::new(new_r, found_ty_)
                }
                None => Ty::new(r, Ty_::Tgeneric(*x)),
            },
            ty => {
                let ty = instantiate_(subst, ty);
                Ty::new(r, ty)
            }
        }
    }
}

fn instantiate_list(subst: &DeclSubst, tyl: &[Ty<R>]) -> Box<[Ty<R>]> {
    tyl.iter().map(|ty| instantiate(subst, ty)).collect()
}

fn instantiate_(subst: &DeclSubst, x: &Ty_<R>) -> Ty_<R> {
    match x {
        Ty_::Tgeneric(_) => panic!("Assert_failure decl_instantiate.ml: instantiate_ of Tgeneric"),
        // IMPORTANT: We cannot expand Taccess during instantiation because this can
        // be called before all type consts have been declared and inherited
        Ty_::Taccess(ta) => {
            let ty = instantiate(subst, &ta.ty);
            Ty_::Taccess(Box::new(TaccessType {
                ty,
                type_const: ta.type_const.clone(),
            }))
        }
        Ty_::Trefinement(tr) => {
            let ty = instantiate(subst, &tr.ty);
            // Class_refinement.map
            let rs = ClassRefinement {
                consts: (tr.refinement.consts.iter())
                    .map(|(id, rc)| {
                        let bound = match &rc.bound {
                            RefinedConstBound::Exact(ty) => {
                                RefinedConstBound::Exact(instantiate(subst, ty))
                            }
                            RefinedConstBound::Loose(bounds) => {
                                RefinedConstBound::Loose(RefinedConstBounds {
                                    lower: instantiate_list(subst, &bounds.lower),
                                    upper: instantiate_list(subst, &bounds.upper),
                                })
                            }
                        };
                        (
                            *id,
                            RefinedConst {
                                bound,
                                is_ctx: rc.is_ctx,
                            },
                        )
                    })
                    .collect(),
            };
            Ty_::Trefinement(Box::new(TrefinementType { ty, refinement: rs }))
        }
        Ty_::TvecOrDict(tys) => {
            let (ty1, ty2) = &**tys;
            let ty1 = instantiate(subst, ty1);
            let ty2 = instantiate(subst, ty2);
            Ty_::TvecOrDict(Box::new((ty1, ty2)))
        }
        Ty_::Tthis
        | Ty_::Tmixed
        | Ty_::Twildcard
        | Ty_::Tdynamic
        | Ty_::Tnonnull
        | Ty_::Tany
        | Ty_::Tprim(_) => x.clone(),
        Ty_::Ttuple(tuple) => {
            let TupleType(t_required, t_optional, t_extra) = &**tuple;
            let t_required = instantiate_list(subst, t_required);
            let t_optional = instantiate_list(subst, t_optional);
            let t_extra = instantiate_tuple_extra(subst, t_extra);
            Ty_::Ttuple(Box::new(TupleType(t_required, t_optional, t_extra)))
        }
        Ty_::Tunion(tyl) => {
            let tyl = instantiate_list(subst, tyl);
            Ty_::Tunion(tyl)
        }
        Ty_::Tintersection(tyl) => {
            let tyl = instantiate_list(subst, tyl);
            Ty_::Tintersection(tyl)
        }
        Ty_::Toption(ty) => {
            let ty = instantiate(subst, ty);
            // we want to avoid double option: ??T
            match ty.node_ref() {
                ty_node @ Ty_::Toption(_) => ty_node.clone(),
                _ => Ty_::Toption(ty),
            }
        }
        Ty_::Tlike(ty) => Ty_::Tlike(instantiate(subst, ty)),
        Ty_::Tfun(ft) => {
            let tparams = &ft.tparams;
            // First remove shadowed type parameters from the substitution.
            // For example, for
            //   class C<T> { public function foo<T>(T $x):void }
            //   class B extends C<int> { }
            // we do not want to replace T by int in foo's signature.
            let mut subst = subst.clone();
            for t in tparams.iter() {
                subst.0.shift_remove(t.name.id_ref());
            }
            // Now collect up all generic parameters that appear in the target of the substitution
            let target_generics = get_tparams_in_subst(&subst);
            // For generic parameters in the function type, rename them "away" from the parameters
            // that appear in the target of the substitituion, and extend the substitution with
            // the renaming.
            //
            // For example, consider
            //    class Base<T> { public function cast<TF>(T $x):TF; }
            //    class Derived<TF> extends Base<TF> { }
            // Now we start with a substitution T:=TF
            // But when going "under" the generic parameter to the cast method,
            // we must rename it to avoid capture: T:=TF, TF:=TF#0
            // and so we end up with
            //   function cast<TF#0>(TF $x):TF#0
            let tparams: Vec<Tparam<R, Ty<R>>> = (ft.tparams.iter())
                .map(|tp| {
                    let (pos, name) = (tp.name.pos(), tp.name.id());
                    if target_generics.contains(&name) {
                        // Fresh only because we don't support nesting of generic function types
                        let fresh_tp_name = TypeName::new(format!("{}#0", name.as_str()));
                        let reason = R::witness_from_decl(pos.clone());
                        subst
                            .0
                            .insert(name, Ty::new(reason, Ty_::Tgeneric(fresh_tp_name)));
                        Tparam {
                            name: Positioned::new(pos.clone(), fresh_tp_name),
                            ..tp.clone()
                        }
                    } else {
                        tp.clone()
                    }
                })
                .collect();
            let subst = &subst;
            let params = (ft.params.iter())
                .map(|param| {
                    let ty = instantiate(subst, &param.ty);
                    FunParam {
                        ty,
                        ..param.clone()
                    }
                })
                .collect();
            let ret = instantiate(subst, &ft.ret);
            let tparams = (tparams.into_iter())
                .map(|t| {
                    let tp_constraints = (t.constraints.iter())
                        .map(|(ck, ty)| (*ck, instantiate(subst, ty)))
                        .collect();
                    Tparam {
                        constraints: tp_constraints,
                        ..t
                    }
                })
                .collect();
            let where_constraints = (ft.where_constraints.iter())
                .map(|WhereConstraint(ty1, ck, ty2)| {
                    WhereConstraint(instantiate(subst, ty1), *ck, instantiate(subst, ty2))
                })
                .collect();
            Ty_::Tfun(Box::new(FunType {
                params,
                ret,
                tparams,
                where_constraints,
                implicit_params: ft.implicit_params.clone(),
                flags: ft.flags,
                instantiated: ft.instantiated,
            }))
        }
        Ty_::Tapply(id_and_args) => {
            let (x, tyl) = &**id_and_args;
            let tyl = instantiate_list(subst, tyl);
            Ty_::Tapply(Box::new((x.clone(), tyl)))
        }
        Ty_::Tshape(shape) => match &**shape {
            ShapeType::Simple(ShapeTypeSimple(shape_kind, fdm)) => {
                let fdm = (fdm.iter())
                    .map(|(name, sft)| {
                        (
                            *name,
                            ShapeFieldType {
                                ty: instantiate(subst, &sft.ty),
                                ..sft.clone()
                            },
                        )
                    })
                    .collect();
                // TODO(shapes) Should this be changing s_origin?
                //
                // (The OCaml resets `s_origin` to `Missing_origin`. hackrs's
                // decl shapes have no origin: `to_oxidized` gives every one of
                // them `MissingOrigin`.)
                Ty_::Tshape(Box::new(ShapeType::Simple(ShapeTypeSimple(
                    instantiate(subst, shape_kind),
                    fdm,
                ))))
            }
            ShapeType::Splat(ss_elems) => Ty_::Tshape(Box::new(ShapeType::Splat(
                ss_elems.iter().map(|ty| instantiate(subst, ty)).collect(),
            ))),
        },
        Ty_::TclassPtr(ty) => Ty_::TclassPtr(instantiate(subst, ty)),
    }
}

fn instantiate_tuple_extra(subst: &DeclSubst, e: &TupleExtra<R>) -> TupleExtra<R> {
    match e {
        TupleExtra::Tsplat(t_splat) => TupleExtra::Tsplat(instantiate(subst, t_splat)),
        TupleExtra::Tvariadic(t_variadic) => TupleExtra::Tvariadic(instantiate(subst, t_variadic)),
    }
}

pub fn instantiate_ce(subst: &DeclSubst, ce: &ClassElt) -> ClassElt {
    let x = ce.ce_type.clone();
    let subst = subst.clone();
    ClassElt {
        ce_type: crate::folded_class::lazy(move || instantiate(&subst, &x)),
        ..ce.clone()
    }
}

pub fn instantiate_cc(subst: &DeclSubst, cc: &ClassConst<R>) -> ClassConst<R> {
    let x = instantiate(subst, &cc.ty);
    ClassConst {
        ty: x,
        ..cc.clone()
    }
}

// TODO(T88552052) is this necessary? Type consts are not allowed to
// reference type parameters, which is the substitution which is happening here
pub fn instantiate_typeconst(subst: &DeclSubst, tc: &Typeconst<R>) -> Typeconst<R> {
    match tc {
        Typeconst::TCAbstract(AbstractTypeconst {
            as_constraint: a,
            super_constraint: s,
            default: d,
        }) => Typeconst::TCAbstract(AbstractTypeconst {
            as_constraint: a.as_ref().map(|ty| instantiate(subst, ty)),
            super_constraint: s.as_ref().map(|ty| instantiate(subst, ty)),
            default: d.as_ref().map(|ty| instantiate(subst, ty)),
        }),
        Typeconst::TCConcrete(ConcreteTypeconst { ty: t }) => {
            Typeconst::TCConcrete(ConcreteTypeconst {
                ty: instantiate(subst, t),
            })
        }
    }
}

pub fn instantiate_typeconst_type(subst: &DeclSubst, tc: &TypeConst<R>) -> TypeConst<R> {
    TypeConst {
        kind: instantiate_typeconst(subst, &tc.kind),
        ..tc.clone()
    }
}

#[cfg(test)]
mod tests {
    use pos::BPos;
    use ty::decl::Prim;
    use ty::decl::subst::Subst;
    use ty::decl::ty::FunImplicitParams;
    use ty::reason::ReasonImpl;

    use super::*;

    fn name(name: &str) -> TypeName {
        TypeName::new(name)
    }

    fn generic(n: &str) -> Ty<R> {
        Ty::generic(R::none(), name(n))
    }

    fn int() -> Ty<R> {
        Ty::prim(R::none(), Prim::Tint)
    }

    fn subst(bindings: &[(&str, Ty<R>)]) -> DeclSubst {
        Subst(
            bindings
                .iter()
                .map(|(n, ty)| (name(n), ty.clone()))
                .collect(),
        )
    }

    fn tparam(n: &str, constraints: Vec<Ty<R>>) -> Tparam<R, Ty<R>> {
        Tparam {
            variance: oxidized::ast_defs::Variance::Invariant,
            name: Positioned::new(BPos::none(), name(n)),
            constraints: constraints
                .into_iter()
                .map(|ty| (oxidized::ast_defs::ConstraintKind::ConstraintAs, ty))
                .collect(),
            reified: oxidized::aast_defs::ReifyKind::Erased,
            user_attributes: Box::new([]),
        }
    }

    fn fun(
        tparams: Vec<Tparam<R, Ty<R>>>,
        params: Vec<Ty<R>>,
        ret: Ty<R>,
        where_constraints: Vec<(Ty<R>, Ty<R>)>,
    ) -> Ty<R> {
        Ty::new(
            R::none(),
            Ty_::Tfun(Box::new(FunType {
                tparams: tparams.into(),
                where_constraints: where_constraints
                    .into_iter()
                    .map(|(ty1, ty2)| {
                        WhereConstraint(ty1, oxidized::ast_defs::ConstraintKind::ConstraintAs, ty2)
                    })
                    .collect(),
                params: params
                    .into_iter()
                    .map(|ty| FunParam {
                        pos: BPos::none(),
                        name: None,
                        ty,
                        flags: ty::decl::ty::FunParamFlags::empty(),
                        def_value: None,
                    })
                    .collect(),
                implicit_params: FunImplicitParams {
                    capability: Capability::CapDefaults(BPos::none()),
                },
                ret,
                flags: ty::decl::ty::FunTypeFlags::empty(),
                instantiated: true,
            })),
        )
    }

    fn fun_type(ty: &Ty<R>) -> &FunType<R, Ty<R>> {
        match ty.node_ref() {
            Ty_::Tfun(ft) => ft,
            ty => panic!("not a function type: {:?}", ty),
        }
    }

    #[test]
    fn empty_substitution_is_the_identity() {
        let ty = Ty::new(R::none(), Ty_::Toption(generic("T")));
        assert_eq!(instantiate(&subst(&[]), &ty), ty);
    }

    #[test]
    fn generic_takes_the_node_of_its_target_and_an_instantiate_reason() {
        let ty = instantiate(&subst(&[("T", int())]), &generic("T"));
        assert_eq!(ty.node_ref(), int().node_ref());
        assert!(matches!(
            ty.reason().as_impl(),
            ReasonImpl::Instantiate(_, n, _) if *n == name("T")
        ));
        // A generic the substitution does not mention is left alone.
        assert_eq!(
            instantiate(&subst(&[("T", int())]), &generic("Tu")),
            generic("Tu")
        );
    }

    #[test]
    fn no_double_option() {
        let nullable_int = Ty::new(R::none(), Ty_::Toption(int()));
        let ty = Ty::new(R::none(), Ty_::Toption(generic("T")));
        let ty = instantiate(&subst(&[("T", nullable_int)]), &ty);
        match ty.node_ref() {
            Ty_::Toption(inner) => assert_eq!(inner.node_ref(), int().node_ref()),
            ty => panic!("{:?}", ty),
        }
    }

    #[test]
    fn function_type_parameters_shadow_the_substitution() {
        // class C<T> { public function foo<T>(T $x): void }
        // class B extends C<int> {}
        let ty = fun(
            vec![tparam("T", vec![])],
            vec![generic("T")],
            Ty::void(R::none()),
            vec![],
        );
        assert_eq!(instantiate(&subst(&[("T", int())]), &ty), ty);
    }

    #[test]
    fn function_type_parameters_are_renamed_away_from_the_targets() {
        // class Base<T> { public function cast<TF>(T $x): TF; }
        // class Derived<TF> extends Base<TF> {}
        let ty = fun(
            vec![tparam("TF", vec![generic("T")])],
            vec![generic("T")],
            generic("TF"),
            vec![(generic("TF"), generic("T"))],
        );
        let ty = instantiate(&subst(&[("T", generic("TF"))]), &ty);
        let ft = fun_type(&ty);
        // function cast<TF#0 as TF>(TF $x): TF#0 where TF#0 as TF
        assert_eq!(ft.tparams[0].name.id(), name("TF#0"));
        assert_eq!(
            ft.tparams[0].constraints[0].1.node_ref(),
            &Ty_::Tgeneric(name("TF"))
        );
        assert_eq!(ft.params[0].ty.node_ref(), &Ty_::Tgeneric(name("TF")));
        assert_eq!(ft.ret.node_ref(), &Ty_::Tgeneric(name("TF#0")));
        let WhereConstraint(ty1, _, ty2) = &ft.where_constraints[0];
        assert_eq!(ty1.node_ref(), &Ty_::Tgeneric(name("TF#0")));
        assert_eq!(ty2.node_ref(), &Ty_::Tgeneric(name("TF")));
    }

    #[test]
    fn where_constraints_do_not_see_shadowed_parameters() {
        // class C<T> { public function foo<T>(): void where int as T }
        // The right-hand side `T` is the function's `T`.
        let ty = fun(
            vec![tparam("T", vec![])],
            vec![],
            Ty::void(R::none()),
            vec![(int(), generic("T"))],
        );
        let string = Ty::prim(R::none(), Prim::Tfloat);
        // A second binding keeps the substitution from being empty once `T`
        // is removed from it.
        let ty2 = instantiate(&subst(&[("T", string.clone()), ("Tu", string)]), &ty);
        let WhereConstraint(_, _, rhs) = &fun_type(&ty2).where_constraints[0];
        assert_eq!(rhs.node_ref(), &Ty_::Tgeneric(name("T")));
    }

    #[test]
    fn shape_fields_and_the_unknown_fields_type_are_instantiated() {
        use ty::decl::ty::ShapeFieldNamePos;
        use ty::decl::ty::TshapeFieldName;
        let field = TshapeFieldName::TSFlitStr(pos::Bytes::new("a"));
        let shape = Ty::new(
            R::none(),
            Ty_::Tshape(Box::new(ShapeType::Simple(ShapeTypeSimple(
                generic("T"),
                [(
                    field,
                    ShapeFieldType {
                        field_name_pos: ShapeFieldNamePos::Simple(BPos::none()),
                        optional: false,
                        ty: generic("T"),
                    },
                )]
                .into_iter()
                .collect(),
            )))),
        );
        let ty = instantiate(&subst(&[("T", int())]), &shape);
        match ty.node_ref() {
            Ty_::Tshape(shape) => match &**shape {
                ShapeType::Simple(ShapeTypeSimple(kind, fdm)) => {
                    assert_eq!(kind.node_ref(), int().node_ref());
                    assert_eq!(fdm[&field].ty.node_ref(), int().node_ref());
                }
                ShapeType::Splat(_) => panic!(),
            },
            ty => panic!("{:?}", ty),
        }
    }

    #[test]
    fn typeconsts_and_class_constants() {
        let s = subst(&[("T", int())]);
        let tc = Typeconst::TCAbstract(AbstractTypeconst {
            as_constraint: Some(generic("T")),
            super_constraint: None,
            default: Some(generic("T")),
        });
        match instantiate_typeconst(&s, &tc) {
            Typeconst::TCAbstract(atc) => {
                assert_eq!(atc.as_constraint.unwrap().node_ref(), int().node_ref());
                assert!(atc.super_constraint.is_none());
                assert_eq!(atc.default.unwrap().node_ref(), int().node_ref());
            }
            Typeconst::TCConcrete(_) => panic!(),
        }
        let tc = Typeconst::TCConcrete(ConcreteTypeconst { ty: generic("T") });
        match instantiate_typeconst(&s, &tc) {
            Typeconst::TCConcrete(tc) => assert_eq!(tc.ty.node_ref(), int().node_ref()),
            Typeconst::TCAbstract(_) => panic!(),
        }
    }
}
