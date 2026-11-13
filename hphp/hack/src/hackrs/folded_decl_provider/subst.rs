// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use std::collections::BTreeMap;
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
use ty::decl::ShapeFieldType;
use ty::decl::TaccessType;
use ty::decl::Tparam;
use ty::decl::TrefinementType;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::Typeconst;
use ty::decl::WhereConstraint;
use ty::decl::subst::Subst;
use ty::decl::ty::Capability;
use ty::decl::ty::ShapeType;
use ty::decl::ty::ShapeTypeSimple;
use ty::decl::ty::TupleExtra;
use ty::decl::ty::TupleType;
use ty::reason::Reason;

// note(sf, 2022-02-14): c.f. `Decl_subst`, `Decl_instantiate`

/// `Decl_instantiate.get_tparams_in_ty_and_acc`: the names of the generics
/// that occur in a type. The OCaml is an object that inherits
/// `Type_visitor.decl_type_visitor` and overrides `on_tgeneric`; this is that
/// visitor's traversal, written out (the set does not depend on its order).
fn get_tparams_in_ty_and_acc<R: Reason>(
    mut acc: BTreeSet<TypeName>,
    ty: &Ty<R>,
) -> BTreeSet<TypeName> {
    fn on_types<R: Reason>(acc: BTreeSet<TypeName>, tyl: &[Ty<R>]) -> BTreeSet<TypeName> {
        tyl.iter().fold(acc, get_tparams_in_ty_and_acc)
    }
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
            (tr.refinement.consts.values()).fold(acc, |acc, rc| match &rc.bound {
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

/// `Decl_instantiate.get_tparams_in_subst`
fn get_tparams_in_subst<R: Reason>(subst: &Subst<R>) -> BTreeSet<TypeName> {
    (subst.0.values()).fold(BTreeSet::new(), get_tparams_in_ty_and_acc)
}

#[derive(Debug, Clone)]
pub struct Substitution<'a, R: Reason> {
    pub subst: &'a Subst<R>,
}

impl<'a, R: Reason> Substitution<'a, R> {
    pub fn instantiate(&self, ty: &Ty<R>) -> Ty<R> {
        // PERF: If subst is empty then instantiation is a no-op. We can save a
        // significant amount of CPU by avoiding recursively deconstructing the
        // `ty` data type.
        if self.subst.0.is_empty() {
            return ty.clone();
        }
        let r = ty.reason().clone();
        let ty_: &Ty_<R> = ty.node();
        match ty_ {
            Ty_::Tgeneric(x) => match self.subst.0.get(x) {
                Some(found_ty) => {
                    let found_r = found_ty.reason();
                    let found_ty_ = found_ty.node_ref();
                    let new_r = R::instantiate(found_r.clone(), *x, r);
                    Ty::new(new_r, found_ty_.clone())
                }
                None => Ty::generic(r, *x),
            },
            _ => Ty::new(r, self.instantiate_(ty_)),
        }
    }

    fn instantiate_(&self, x: &Ty_<R>) -> Ty_<R> {
        match x {
            Ty_::Tgeneric(_) => panic!("subst.rs: instantiate_: impossible!"),
            // IMPORTANT: We cannot expand `Taccess` during instantiation
            // because this can be called before all type consts have been
            // declared and inherited.
            Ty_::Taccess(ta) => Ty_::Taccess(Box::new(TaccessType {
                ty: self.instantiate(&ta.ty),
                type_const: ta.type_const.clone(),
            })),
            Ty_::TvecOrDict(tys) => Ty_::TvecOrDict(Box::new((
                self.instantiate(&tys.0),
                self.instantiate(&tys.1),
            ))),
            Ty_::Tthis
            | Ty_::Tmixed
            | Ty_::Twildcard
            | Ty_::Tdynamic
            | Ty_::Tnonnull
            | Ty_::Tany
            | Ty_::Tprim(_) => x.clone(),
            Ty_::Ttuple(params) => {
                let TupleType(ref required, ref optional, ref extra) = **params;
                Ty_::Ttuple(Box::new(TupleType(
                    required
                        .iter()
                        .map(|t| self.instantiate(t))
                        .collect::<Box<[_]>>(),
                    optional
                        .iter()
                        .map(|t| self.instantiate(t))
                        .collect::<Box<[_]>>(),
                    self.instantiate_tuple_extra(extra),
                )))
            }
            Ty_::Tunion(tys) => Ty_::Tunion(
                tys.iter()
                    .map(|t| self.instantiate(t))
                    .collect::<Box<[_]>>(),
            ),
            Ty_::Tintersection(tys) => Ty_::Tintersection(
                tys.iter()
                    .map(|t| self.instantiate(t))
                    .collect::<Box<[_]>>(),
            ),
            Ty_::Toption(ty) => {
                let ty = self.instantiate(ty);
                // We want to avoid double option: `??T`.
                match ty.node() as &Ty_<R> {
                    ty_node @ Ty_::Toption(_) => ty_node.clone(),
                    _ => Ty_::Toption(ty),
                }
            }
            Ty_::Tlike(ty) => Ty_::Tlike(self.instantiate(ty)),
            Ty_::Tfun(ft) => {
                let tparams = &ft.tparams;
                // First remove shadowed type parameters from the substitution.
                // For example, for
                //   class C<T> { public function foo<T>(T $x):void }
                //   class B extends C<int> { }
                // we do not want to replace T by int in foo's signature.
                let mut subst = self.subst.clone();
                for tp in tparams.iter() {
                    subst.0.shift_remove(tp.name.id_ref());
                }
                // Now collect up all generic parameters that appear in the
                // target of the substitution
                let target_generics = get_tparams_in_subst(&subst);
                // For generic parameters in the function type, rename them
                // "away" from the parameters that appear in the target of the
                // substitituion, and extend the substitution with the
                // renaming.
                //
                // For example, consider
                //    class Base<T> { public function cast<TF>(T $x):TF; }
                //    class Derived<TF> extends Base<TF> { }
                // Now we start with a substitution T:=TF
                // But when going "under" the generic parameter to the cast
                // method, we must rename it to avoid capture: T:=TF, TF:=TF#0
                // and so we end up with
                //   function cast<TF#0>(TF $x):TF#0
                //
                // (c.f. `Decl_instantiate.instantiate_`: this used to keep the
                // names, which captured them.)
                let tparams: Vec<Tparam<R, Ty<R>>> = (tparams.iter())
                    .map(|tp| {
                        let (pos, name) = (tp.name.pos(), tp.name.id());
                        if target_generics.contains(&name) {
                            // Fresh only because we don't support nesting of
                            // generic function types
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
                let subst = Substitution { subst: &subst };
                let params = ft
                    .params
                    .iter()
                    .map(|fp| FunParam {
                        ty: subst.instantiate(&fp.ty),
                        pos: fp.pos.clone(),
                        name: fp.name,
                        flags: fp.flags,
                        def_value: fp.def_value.clone(),
                    })
                    .collect::<Box<[_]>>();
                let ret = subst.instantiate(&ft.ret);
                let tparams = (tparams.into_iter())
                    .map(|tp| Tparam {
                        constraints: tp
                            .constraints
                            .iter()
                            .map(|(ck, ty)| (*ck, subst.instantiate(ty)))
                            .collect::<Box<[_]>>(),
                        ..tp
                    })
                    .collect::<Box<[_]>>();
                // (Both sides of a where constraint are instantiated with the
                // substitution of the function's body, as in
                // `Decl_instantiate`.)
                let where_constraints = ft
                    .where_constraints
                    .iter()
                    .map(|WhereConstraint(ty1, ck, ty2)| {
                        WhereConstraint(subst.instantiate(ty1), *ck, subst.instantiate(ty2))
                    })
                    .collect::<Box<[_]>>();
                Ty_::Tfun(Box::new(FunType {
                    params,
                    ret,
                    tparams,
                    where_constraints,
                    flags: ft.flags,
                    implicit_params: ft.implicit_params.clone(),
                    instantiated: ft.instantiated,
                }))
            }
            Ty_::Tapply(params) => {
                let (name, tys) = &**params;
                Ty_::Tapply(Box::new((
                    name.clone(),
                    tys.iter()
                        .map(|ty| self.instantiate(ty))
                        .collect::<Box<[_]>>(),
                )))
            }
            Ty_::Tshape(params) => match &**params {
                ShapeType::Simple(ShapeTypeSimple(shape_kind, fdm)) => {
                    // TODO(shapes) s_unknown_value should likely be
                    // instantiated (`Decl_instantiate` leaves it alone, and so
                    // does this.)
                    let shape_kind = shape_kind.clone();
                    let fdm = fdm
                        .iter()
                        .map(|(f, sft)| {
                            (
                                *f,
                                ShapeFieldType {
                                    field_name_pos: sft.field_name_pos.clone(),
                                    ty: self.instantiate(&sft.ty),
                                    optional: sft.optional,
                                },
                            )
                        })
                        .collect::<BTreeMap<_, _>>();
                    Ty_::Tshape(Box::new(ShapeType::Simple(ShapeTypeSimple(
                        shape_kind, fdm,
                    ))))
                }
                ShapeType::Splat(elems) => {
                    let elems = elems.iter().map(|ty| self.instantiate(ty)).collect();
                    Ty_::Tshape(Box::new(ShapeType::Splat(elems)))
                }
            },
            Ty_::Trefinement(tr) => Ty_::Trefinement(Box::new(TrefinementType {
                ty: self.instantiate(&tr.ty),
                refinement: ClassRefinement {
                    consts: (tr.refinement.consts.iter())
                        .map(|(k, v)| (*k, self.instantiate_class_type_refinement(v)))
                        .collect(),
                },
            })),
            Ty_::TclassPtr(ty) => Ty_::TclassPtr(self.instantiate(ty)),
        }
    }

    fn instantiate_class_type_refinement(&self, rc: &RefinedConst<Ty<R>>) -> RefinedConst<Ty<R>> {
        use RefinedConstBound::*;
        let bound = match &rc.bound {
            Exact(ty) => Exact(self.instantiate(ty)),
            Loose(bounds) => Loose(ty::decl::RefinedConstBounds {
                lower: bounds.lower.iter().map(|ty| self.instantiate(ty)).collect(),
                upper: bounds.upper.iter().map(|ty| self.instantiate(ty)).collect(),
            }),
        };
        RefinedConst {
            bound,
            is_ctx: rc.is_ctx,
        }
    }

    fn instantiate_tuple_extra(&self, e: &TupleExtra<R>) -> TupleExtra<R> {
        use TupleExtra;
        match &e {
            TupleExtra::Tvariadic(variadic) => TupleExtra::Tvariadic(self.instantiate(variadic)),
            TupleExtra::Tsplat(splat) => TupleExtra::Tsplat(self.instantiate(splat)),
        }
    }

    pub fn instantiate_class_const(&self, cc: &ClassConst<R>) -> ClassConst<R> {
        ClassConst {
            is_synthesized: cc.is_synthesized,
            kind: cc.kind,
            pos: cc.pos.clone(),
            ty: self.instantiate(&cc.ty),
            origin: cc.origin,
            refs: cc.refs.clone(),
            is_shape_key: cc.is_shape_key,
            value: cc.value.clone(),
        }
    }

    fn instantiate_type_const_kind(&self, kind: &Typeconst<R>) -> Typeconst<R> {
        match kind {
            Typeconst::TCAbstract(k) => Typeconst::TCAbstract(AbstractTypeconst {
                as_constraint: k.as_constraint.as_ref().map(|ty| self.instantiate(ty)),
                super_constraint: k.super_constraint.as_ref().map(|ty| self.instantiate(ty)),
                default: k.default.as_ref().map(|ty| self.instantiate(ty)),
            }),
            Typeconst::TCConcrete(k) => Typeconst::TCConcrete(ConcreteTypeconst {
                ty: self.instantiate(&k.ty),
            }),
        }
    }

    pub fn instantiate_type_const(&self, tc: &TypeConst<R>) -> TypeConst<R> {
        TypeConst {
            is_synthesized: tc.is_synthesized,
            name: tc.name.clone(),
            kind: self.instantiate_type_const_kind(&tc.kind),
            origin: tc.origin,
            enforceable: tc.enforceable.clone(),
            reifiable: tc.reifiable.clone(),
            is_concretized: tc.is_concretized,
            is_ctx: tc.is_ctx,
        }
    }
}
