// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_visitor.ml`. See `hh/PORTING.md`.
//!
//! Each OCaml class is a trait whose default methods are the methods of the
//! class, including the ones it inherits (see `type_mapper_generic.rs`); a
//! visitor is a type that implements the trait and overrides methods by
//! defining them:
//!
//! | OCaml | Rust |
//! |---|---|
//! | `class virtual ['a] decl_type_visitor` | [`DeclTypeVisitor<A>`], over `ty::decl::Ty` |
//! | `class virtual ['a] locl_type_visitor` | [`LoclTypeVisitor<A>`] |
//! | `class ['a] internal_type_visitor` | [`InternalTypeVisitor<A>`] |
//!
//! The class types (`decl_type_visitor_type`, ...) are the method lists of
//! these traits. The accumulator is taken and returned by value; types and
//! reasons are borrowed.

use oxidized::ast_defs::Tprim;
use pos::Positioned;
use pos::TypeName;
use ty::decl::ty as d;

use crate::ctx::R;
use crate::typing_defs::*;
use crate::typing_defs_constraints::*;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

/// `decl_phase Reason.t_`
type DeclReason = R;

/// The position type of declarations.
type DeclPos = <R as ty::reason::Reason>::Pos;

/// `class virtual ['a] decl_type_visitor`
#[allow(unused_variables)]
pub trait DeclTypeVisitor<A> {
    fn on_tany(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_tmixed(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_twildcard(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_tnonnull(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_tdynamic(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_tthis(&mut self, acc: A, r: &DeclReason) -> A {
        acc
    }

    fn on_tvec_or_dict(&mut self, acc: A, r: &DeclReason, ty1: &DeclTy, ty2: &DeclTy) -> A {
        let acc = self.on_type(acc, ty1);
        self.on_type(acc, ty2)
    }

    fn on_tgeneric(&mut self, acc: A, r: &DeclReason, name: &str) -> A {
        acc
    }

    fn on_toption(&mut self, acc: A, r: &DeclReason, ty: &DeclTy) -> A {
        self.on_type(acc, ty)
    }

    fn on_tlike(&mut self, acc: A, r: &DeclReason, ty: &DeclTy) -> A {
        self.on_type(acc, ty)
    }

    fn on_tprim(&mut self, acc: A, r: &DeclReason, prim: Tprim) -> A {
        acc
    }

    fn on_tvar(&mut self, acc: A, r: &DeclReason, v: isize) -> A {
        acc
    }

    fn on_tfun(&mut self, acc: A, r: &DeclReason, ft: &DeclFunType) -> A {
        let d::FunType {
            params: ft_params,
            tparams: ft_tparams,
            ret: ft_ret,
            flags: _,
            instantiated: _,
            implicit_params: ft_implicit_params,
            where_constraints: ft_where_constraints,
        } = ft;
        let mut acc = acc;
        for x in ft_params.iter() {
            acc = self.on_type(acc, &x.ty);
        }
        for t in ft_tparams.iter() {
            for (_, ty) in t.constraints.iter() {
                acc = self.on_type(acc, ty);
            }
        }
        let mut acc = match &ft_implicit_params.capability {
            d::Capability::CapDefaults(_) => acc,
            d::Capability::CapTy(ty) => self.on_type(acc, ty),
        };
        for d::WhereConstraint(ty1, _ck, ty2) in ft_where_constraints.iter() {
            acc = self.on_type(acc, ty1);
            acc = self.on_type(acc, ty2);
        }
        self.on_type(acc, ft_ret)
    }

    fn on_tapply(
        &mut self,
        acc: A,
        r: &DeclReason,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> A {
        tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
    }

    fn on_trefinement(
        &mut self,
        acc: A,
        r: &DeclReason,
        ty: &DeclTy,
        rs: &DeclClassRefinement,
    ) -> A {
        let mut acc = self.on_type(acc, ty);
        // Class_refinement.fold rs ~init:acc ~f:this#on_type
        // (S_map.fold: in the order of the names)
        let mut consts: Vec<_> = rs.consts.iter().collect();
        consts.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
        for (_, rc) in consts {
            match &rc.bound {
                d::RefinedConstBound::Exact(ty) => acc = self.on_type(acc, ty),
                d::RefinedConstBound::Loose(d::RefinedConstBounds {
                    lower: ls,
                    upper: us,
                }) => {
                    for ty in ls.iter() {
                        acc = self.on_type(acc, ty);
                    }
                    for ty in us.iter() {
                        acc = self.on_type(acc, ty);
                    }
                }
            }
        }
        acc
    }

    fn on_taccess(&mut self, acc: A, r: &DeclReason, ta: &d::TaccessType<R, DeclTy>) -> A {
        self.on_type(acc, &ta.ty)
    }

    fn on_ttuple(&mut self, acc: A, r: &DeclReason, t: &d::TupleType<R>) -> A {
        let d::TupleType(t_required, t_optional, t_extra) = t;
        let acc = self.on_tuple_extra(acc, t_extra);
        let acc = t_optional.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
        t_required.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
    }

    fn on_tuple_extra(&mut self, acc: A, e: &d::TupleExtra<R>) -> A {
        match e {
            d::TupleExtra::Tsplat(t_splat) => self.on_type(acc, t_splat),
            d::TupleExtra::Tvariadic(t_variadic) => self.on_type(acc, t_variadic),
        }
    }

    fn on_tunion(&mut self, acc: A, r: &DeclReason, tyl: &[DeclTy]) -> A {
        tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
    }

    fn on_tintersection(&mut self, acc: A, r: &DeclReason, tyl: &[DeclTy]) -> A {
        tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
    }

    fn on_tshape(&mut self, acc: A, r: &DeclReason, shape_ty: &d::ShapeType<R>) -> A {
        match shape_ty {
            d::ShapeType::Simple(d::ShapeTypeSimple(kind, fdm)) => {
                let acc = self.on_type(acc, kind);
                // TShapeMap.fold: in the order of the names of the fields
                let mut fdm: Vec<_> = fdm.iter().collect();
                fdm.sort_by(|a, b| decl_tshape_field_name_compare(a.0, b.0));
                fdm.into_iter()
                    .fold(acc, |acc, (_, sft)| self.on_type(acc, &sft.ty))
            }
            d::ShapeType::Splat(ss_elems) => {
                ss_elems.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
            }
        }
    }

    fn on_tclass_ptr(&mut self, acc: A, r: &DeclReason, ty: &DeclTy) -> A {
        self.on_type(acc, ty)
    }

    fn on_type(&mut self, acc: A, ty: &DeclTy) -> A {
        let r = ty.reason();
        match ty.node_ref() {
            d::Ty_::Tany => self.on_tany(acc, r),
            d::Ty_::Tmixed => self.on_tmixed(acc, r),
            d::Ty_::Twildcard => self.on_twildcard(acc, r),
            d::Ty_::Tnonnull => self.on_tnonnull(acc, r),
            d::Ty_::Tdynamic => self.on_tdynamic(acc, r),
            d::Ty_::Tthis => self.on_tthis(acc, r),
            d::Ty_::TvecOrDict(kv) => self.on_tvec_or_dict(acc, r, &kv.0, &kv.1),
            d::Ty_::Tgeneric(s) => self.on_tgeneric(acc, r, s.as_str()),
            d::Ty_::Toption(ty) => self.on_toption(acc, r, ty),
            d::Ty_::Tlike(ty) => self.on_tlike(acc, r, ty),
            d::Ty_::Tprim(prim) => self.on_tprim(acc, r, *prim),
            d::Ty_::Tfun(fty) => self.on_tfun(acc, r, fty),
            d::Ty_::Tapply(s_and_tyl) => self.on_tapply(acc, r, &s_and_tyl.0, &s_and_tyl.1),
            d::Ty_::Trefinement(tr) => self.on_trefinement(acc, r, &tr.ty, &tr.refinement),
            d::Ty_::Taccess(aty) => self.on_taccess(acc, r, aty),
            d::Ty_::Ttuple(t) => self.on_ttuple(acc, r, t),
            d::Ty_::Tunion(tyl) => self.on_tunion(acc, r, tyl),
            d::Ty_::Tintersection(tyl) => self.on_tintersection(acc, r, tyl),
            d::Ty_::Tshape(s) => self.on_tshape(acc, r, s),
            d::Ty_::TclassPtr(ty) => self.on_tclass_ptr(acc, r, ty),
        }
    }
}

/// The body of `on_type` of `locl_type_visitor` (the dispatch on the type),
/// for [`locl_type_visitor_on_type`] and the traits' `on_type`.
macro_rules! locl_on_type_body {
    ($v:ident, $acc:ident, $ty:ident) => {{
            let r = get_reason($ty);
            match get_node($ty) {
                Ty_::Tany(_) => $v.on_tany($acc, r),
                Ty_::Tnonnull => $v.on_tnonnull($acc, r),
                Ty_::Tdynamic(_) => $v.on_tdynamic($acc, r),
                Ty_::Toption(ty) => $v.on_toption($acc, r, ty),
                Ty_::Tprim(prim) => $v.on_tprim($acc, r, *prim),
                Ty_::Tvar(id) => $v.on_tvar($acc, r, *id),
                Ty_::Tfun(fty) => $v.on_tfun($acc, r, fty),
                Ty_::Tgeneric(x) => $v.on_tgeneric($acc, r, x),
                Ty_::Tnewtype(x, tyl, ty) => $v.on_tnewtype($acc, r, x, tyl, ty),
                Ty_::Tdependent(x, ty) => $v.on_tdependent($acc, r, x, ty),
                Ty_::Ttuple(t) => $v.on_ttuple($acc, r, t),
                Ty_::Tunion(tyl) => $v.on_tunion($acc, r, tyl),
                Ty_::Tintersection(tyl) => $v.on_tintersection($acc, r, tyl),
                Ty_::Tshape(s) => $v.on_tshape($acc, r, s),
                Ty_::Tclass(cls, exact, tyl) => $v.on_tclass($acc, r, cls, exact, tyl),
                Ty_::TvecOrDict(ty1, ty2) => $v.on_tvec_or_dict($acc, r, ty1, ty2),
                Ty_::Taccess(ta) => $v.on_taccess($acc, r, ta),
                Ty_::Tneg(tneg) => $v.on_neg_type($acc, r, tneg),
                Ty_::Tlabel(name) => $v.on_tlabel($acc, r, name),
                Ty_::TclassPtr(ty) => $v.on_tclass_ptr($acc, r, ty),
            }
    }};
}
pub(crate) use locl_on_type_body;

/// The methods of `locl_type_visitor`.
macro_rules! locl_type_visitor_methods {
    ($a:ty) => {
        fn on_tany(&mut self, acc: $a, r: &Reason) -> $a {
            acc
        }

        fn on_tnonnull(&mut self, acc: $a, r: &Reason) -> $a {
            acc
        }

        fn on_tdynamic(&mut self, acc: $a, r: &Reason) -> $a {
            acc
        }

        fn on_toption(&mut self, acc: $a, r: &Reason, ty: &Ty) -> $a {
            self.on_type(acc, ty)
        }

        fn on_tprim(&mut self, acc: $a, r: &Reason, prim: Tprim) -> $a {
            acc
        }

        fn on_tvar(&mut self, acc: $a, r: &Reason, id: isize) -> $a {
            acc
        }

        fn on_tfun(&mut self, acc: $a, r: &Reason, ft: &FunType) -> $a {
            let FunType {
                params: ft_params,
                tparams: ft_tparams,
                ret: ft_ret,
                ..
            } = ft;
            let mut acc = acc;
            for x in ft_params {
                acc = self.on_type(acc, &x.type_);
            }
            for t in ft_tparams {
                for (_, ty) in &t.constraints {
                    acc = self.on_type(acc, ty);
                }
            }
            self.on_type(acc, ft_ret)
        }

        fn on_tgeneric(&mut self, acc: $a, r: &Reason, name: &str) -> $a {
            acc
        }

        fn on_tnewtype(&mut self, acc: $a, r: &Reason, name: &str, tyl: &[Ty], ty: &Ty) -> $a {
            let acc = tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
            let acc = self.on_type(acc, ty);
            acc
        }

        fn on_tdependent(&mut self, acc: $a, r: &Reason, dep: &DependentType, ty: &Ty) -> $a {
            let acc = self.on_type(acc, ty);
            acc
        }

        fn on_ttuple(&mut self, acc: $a, r: &Reason, t: &TupleType) -> $a {
            let TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            } = t;
            let acc = self.on_tuple_extra(acc, t_extra);
            let acc = t_optional.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
            t_required.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }

        fn on_tuple_extra(&mut self, acc: $a, e: &TupleExtra) -> $a {
            match e {
                TupleExtra::Tsplat(t_splat) => self.on_type(acc, t_splat),
                TupleExtra::Tvariadic(t_variadic) => self.on_type(acc, t_variadic),
            }
        }

        fn on_tunion(&mut self, acc: $a, r: &Reason, tyl: &[Ty]) -> $a {
            tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }

        fn on_tintersection(&mut self, acc: $a, r: &Reason, tyl: &[Ty]) -> $a {
            tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }

        fn on_tshape(&mut self, acc: $a, r: &Reason, shape_ty: &ShapeType) -> $a {
            match shape_ty {
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: kind,
                    fields: fdm,
                }) => {
                    let acc = self.on_type(acc, kind);
                    fdm.iter()
                        .fold(acc, |acc, (_, ShapeFieldType { ty: sft_ty, .. })| {
                            self.on_type(acc, sft_ty)
                        })
                }
                ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                    ss_elems.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
                }
            }
        }

        fn on_tclass(&mut self, acc: $a, r: &Reason, id: &PosId, exact: &Exact, tyl: &[Ty]) -> $a {
            let acc = match exact {
                Exact::Exact => acc,
                Exact::Nonexact(cr) => self.on_class_refinement(acc, cr),
            };
            tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }

        fn on_class_refinement(&mut self, acc: $a, cr: &ClassRefinement) -> $a {
            let ClassRefinement { cr_consts } = cr;
            // (Most classes have no refinement: not even an iterator then.)
            if cr_consts.is_empty() {
                return acc;
            }
            cr_consts.iter().fold(
                acc,
                |acc,
                 (
                    _const_name,
                    RefinedConst {
                        bound: rc_bound,
                        is_ctx: _,
                    },
                )| {
                    match rc_bound {
                        RefinedConstBound::TRexact(ty) => self.on_type(acc, ty),
                        RefinedConstBound::TRloose(RefinedConstBounds { lower: l, upper: u }) => {
                            let acc = u.iter().fold(acc, |acc, ty| self.on_type(acc, ty));
                            l.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
                        }
                    }
                },
            )
        }

        fn on_tlist(&mut self, acc: $a, r: &Reason, tyl: &[Ty]) -> $a {
            tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }

        fn on_tvec_or_dict(&mut self, acc: $a, r: &Reason, ty1: &Ty, ty2: &Ty) -> $a {
            let acc = self.on_type(acc, ty1);
            self.on_type(acc, ty2)
        }

        fn on_neg_type(&mut self, acc: $a, r: &Reason, neg_ty: &TypePredicate) -> $a {
            match &neg_ty.1 {
                TypePredicate_::IsTag(tag) => match tag {
                    TypeTag::ClassTag(c, args) => {
                        let acc = self.on_tclass(
                            acc,
                            r,
                            &(reason::to_pos(r), c.clone()),
                            &nonexact(),
                            &[],
                        );
                        let tyl: Vec<Ty> = args
                            .iter()
                            .filter_map(|g| match g {
                                TypeTagGeneric::Filled(ty) => Some(ty.clone()),
                                TypeTagGeneric::Wildcard(_) => None,
                            })
                            .collect();
                        self.on_tlist(acc, r, &tyl)
                    }
                    TypeTag::ArraykeyTag
                    | TypeTag::BoolTag
                    | TypeTag::IntTag
                    | TypeTag::FloatTag
                    | TypeTag::NumTag
                    | TypeTag::ResourceTag
                    | TypeTag::NullTag
                    | TypeTag::EnumTag(_)
                    | TypeTag::GenericTag { .. } => acc,
                },
                TypePredicate_::IsTupleOf(_)
                | TypePredicate_::IsShapeOf(_)
                | TypePredicate_::IsUnionOf(_)
                | TypePredicate_::IsNot(_) => acc,
            }
        }

        fn on_tunapplied_alias(&mut self, acc: $a, r: &Reason, name: &str) -> $a {
            acc
        }

        fn on_taccess(&mut self, acc: $a, r: &Reason, ta: &TaccessType) -> $a {
            let TaccessType(ty, _ids) = ta;
            self.on_type(acc, ty)
        }

        fn on_tlabel(&mut self, acc: $a, r: &Reason, name: &str) -> $a {
            acc
        }

        fn on_tclass_ptr(&mut self, acc: $a, r: &Reason, ty: &Ty) -> $a {
            self.on_type(acc, ty)
        }

        fn on_type(&mut self, acc: $a, ty: &Ty) -> $a {
            $crate::type_visitor::locl_on_type_body!(self, acc, ty)
        }
    };
}

/// `class virtual ['a] locl_type_visitor`
#[allow(unused_variables)]
pub trait LoclTypeVisitor<A> {
    locl_type_visitor_methods!(A);
}

/// The `on_type` of `locl_type_visitor`, which a visitor that overrides
/// `on_type` calls as OCaml's `super#on_type`.
pub fn locl_type_visitor_on_type<A, V: LoclTypeVisitor<A> + ?Sized>(v: &mut V, acc: A, ty: &Ty) -> A {
    locl_on_type_body!(v, acc, ty)
}

/// `class ['a] internal_type_visitor`: the methods of `locl_type_visitor`, and
/// the ones for constraint types.
#[allow(unused_variables)]
pub trait InternalTypeVisitor<A> {
    fn on_internal_type(&mut self, acc: A, ty: &InternalType) -> A {
        match ty {
            InternalType::LoclType(ty) => self.on_locl_type(acc, ty),
            InternalType::ConstraintType(ty) => self.on_constraint_type(acc, ty),
        }
    }

    fn on_constraint_type(&mut self, acc: A, ty: &ConstraintType) -> A {
        let ConstraintType(r, ty) = ty;
        match &**ty {
            ConstraintType_::ThasMember(hm) => self.on_thas_member(acc, r, hm),
            ConstraintType_::ThasTypeMember(htm) => self.on_thas_type_member(acc, r, htm),
            ConstraintType_::TcanIndex(ci) => self.on_tcan_index(acc, r, ci),
            ConstraintType_::TcanIndexAssign(cia) => self.on_tcan_index_assign(acc, r, cia),
            ConstraintType_::TcanTraverse(ct) => self.on_tcan_traverse(acc, r, ct),
            ConstraintType_::Tdestructure(des) => self.on_tdestructure(acc, r, des),
            ConstraintType_::TtypeSwitch {
                predicate,
                ty_true,
                ty_false,
            } => self.on_ttype_switch(acc, r, predicate, ty_true, ty_false),
            ConstraintType_::ThasConst { name, ty } => self.on_thas_const(acc, r, name, ty),
        }
    }

    fn on_locl_type(&mut self, acc: A, ty: &Ty) -> A {
        self.on_type(acc, ty)
    }

    fn on_locl_type_list(&mut self, acc: A, tyl: &[Ty]) -> A {
        tyl.iter().fold(acc, |acc, ty| self.on_locl_type(acc, ty))
    }

    fn on_locl_type_option(&mut self, acc: A, ty: Option<&Ty>) -> A {
        match ty {
            None => acc,
            Some(ty) => self.on_locl_type(acc, ty),
        }
    }

    fn on_thas_member(&mut self, acc: A, r: &Reason, hm: &HasMember) -> A {
        self.on_has_member(acc, r, hm)
    }

    fn on_has_member(&mut self, acc: A, r: &Reason, hm: &HasMember) -> A {
        let HasMember {
            name: _,
            type_: hm_type,
            class_id: _,
            method: _,
        } = hm;
        self.on_locl_type(acc, hm_type)
    }

    fn on_thas_type_member(&mut self, acc: A, r: &Reason, htm: &HasTypeMember) -> A {
        self.on_has_type_member(acc, r, htm)
    }

    fn on_has_type_member(&mut self, acc: A, r: &Reason, htm: &HasTypeMember) -> A {
        let HasTypeMember {
            id: _,
            lower: htm_lower,
            upper: htm_upper,
        } = htm;
        let acc = self.on_locl_type(acc, htm_lower);
        let acc = self.on_locl_type(acc, htm_upper);
        acc
    }

    fn on_tcan_index(&mut self, acc: A, r: &Reason, hm: &CanIndex) -> A {
        self.on_can_index(acc, r, hm)
    }

    fn on_tcan_index_assign(&mut self, acc: A, r: &Reason, hm: &CanIndexAssign) -> A {
        self.on_can_index_assign(acc, r, hm)
    }

    fn on_tcan_traverse(&mut self, acc: A, r: &Reason, hm: &CanTraverse) -> A {
        self.on_can_traverse(acc, r, hm)
    }

    fn on_can_index(&mut self, acc: A, r: &Reason, ci: &CanIndex) -> A {
        let acc = self.on_locl_type(acc, &ci.key);
        self.on_locl_type(acc, &ci.val)
    }

    fn on_can_index_assign(&mut self, acc: A, r: &Reason, cia: &CanIndexAssign) -> A {
        let acc = self.on_locl_type(acc, &cia.key);
        let acc = self.on_locl_type(acc, &cia.write);
        self.on_locl_type(acc, &cia.val)
    }

    fn on_can_traverse(&mut self, acc: A, r: &Reason, ct: &CanTraverse) -> A {
        let acc = self.on_locl_type_option(acc, ct.key.as_ref());
        let acc = self.on_locl_type(acc, &ct.val);
        acc
    }

    fn on_tdestructure(&mut self, acc: A, r: &Reason, des: &Destructure) -> A {
        self.on_destructure(acc, r, des)
    }

    fn on_destructure(&mut self, acc: A, r: &Reason, des: &Destructure) -> A {
        let Destructure {
            required: d_required,
            optional: d_optional,
            variadic: d_variadic,
            kind: _,
        } = des;
        let acc = self.on_locl_type_list(acc, d_required);
        let acc = self.on_locl_type_list(acc, d_optional);
        let acc = self.on_locl_type_option(acc, d_variadic.as_ref());
        acc
    }

    fn on_tcunion(&mut self, acc: A, r: &Reason, lty: &Ty, cty: &ConstraintType) -> A {
        let acc = self.on_locl_type(acc, lty);
        let acc = self.on_constraint_type(acc, cty);
        acc
    }

    fn on_tcintersection(&mut self, acc: A, r: &Reason, lty: &Ty, cty: &ConstraintType) -> A {
        let acc = self.on_locl_type(acc, lty);
        let acc = self.on_constraint_type(acc, cty);
        acc
    }

    fn on_ttype_switch(
        &mut self,
        acc: A,
        r: &Reason,
        predicate: &TypePredicate,
        ty_true: &Ty,
        ty_false: &Ty,
    ) -> A {
        let acc = self.on_locl_type(acc, ty_true);
        let acc = self.on_locl_type(acc, ty_false);
        acc
    }

    fn on_thas_const(&mut self, acc: A, r: &Reason, name: &str, ty: &Ty) -> A {
        let acc = self.on_locl_type(acc, ty);
        acc
    }

    locl_type_visitor_methods!(A);
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;
    use pos::Pos as _;
    use ty::reason::Reason as _;

    use super::*;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn generic(n: &str) -> Ty {
        mk((r(), Ty_::Tgeneric(n.to_string())))
    }

    fn class(n: &str, exact: Exact, tyl: Vec<Ty>) -> Ty {
        mk((r(), Ty_::Tclass((Pos::NONE, n.to_string()), exact, tyl)))
    }

    /// Collects the names of the generics and of the classes, in the order
    /// they are visited.
    struct Names;
    impl LoclTypeVisitor<Vec<String>> for Names {
        fn on_tgeneric(&mut self, mut acc: Vec<String>, _r: &Reason, name: &str) -> Vec<String> {
            acc.push(name.to_string());
            acc
        }
        fn on_tclass(
            &mut self,
            mut acc: Vec<String>,
            _r: &Reason,
            id: &PosId,
            exact: &Exact,
            tyl: &[Ty],
        ) -> Vec<String> {
            acc.push(id.1.clone());
            // super#on_tclass
            let acc = match exact {
                Exact::Exact => acc,
                Exact::Nonexact(cr) => self.on_class_refinement(acc, cr),
            };
            tyl.iter().fold(acc, |acc, ty| self.on_type(acc, ty))
        }
    }

    struct InternalNames;
    impl InternalTypeVisitor<Vec<String>> for InternalNames {
        fn on_tgeneric(&mut self, mut acc: Vec<String>, _r: &Reason, name: &str) -> Vec<String> {
            acc.push(name.to_string());
            acc
        }
    }

    fn names(ty: &Ty) -> Vec<String> {
        Names.on_type(vec![], ty)
    }

    #[test]
    fn locl_visit_order() {
        // tuples: the extra part, then the optional ones, then the required ones
        let tuple = mk((
            r(),
            Ty_::Ttuple(TupleType {
                required: vec![generic("R1"), generic("R2")],
                optional: vec![generic("O")],
                extra: TupleExtra::Tvariadic(generic("V")),
            }),
        ));
        assert_eq!(names(&tuple), vec!["V", "O", "R1", "R2"]);

        // classes: the refinement (upper bounds, then lower bounds), then the arguments
        let mut cr_consts = oxidized::s_map::SMap::new();
        cr_consts.insert(
            "TB".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRexact(generic("E")),
                is_ctx: false,
            },
        );
        cr_consts.insert(
            "TA".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: vec![generic("L")],
                    upper: vec![generic("U")],
                }),
                is_ctx: false,
            },
        );
        let c = class(
            "\\C",
            Exact::Nonexact(ClassRefinement {
                cr_consts: cr_consts.into(),
            }),
            vec![generic("A")],
        );
        assert_eq!(names(&c), vec!["\\C", "U", "L", "E", "A"]);

        // newtypes: the arguments, then the bound
        let n = mk((
            r(),
            Ty_::Tnewtype("\\N".to_string(), vec![generic("A")], generic("B")),
        ));
        assert_eq!(names(&n), vec!["A", "B"]);

        // functions: parameters, constraints of the type parameters, return
        // type; neither the where constraints nor the capability
        let ft = FunType {
            tparams: vec![Tparam {
                variance: oxidized::ast_defs::Variance::Invariant,
                name: (Pos::NONE, "T".to_string()),
                constraints: vec![(
                    oxidized::ast_defs::ConstraintKind::ConstraintAs,
                    generic("TC"),
                )],
                reified: oxidized::ast_defs::ReifyKind::Erased,
                user_attributes: vec![],
            }],
            where_constraints: vec![WhereConstraint(
                generic("W1"),
                oxidized::ast_defs::ConstraintKind::ConstraintEq,
                generic("W2"),
            )],
            params: vec![FunParam {
                pos: Pos::NONE,
                name: None,
                type_: generic("P"),
                flags: oxidized::typing_defs_flags::FunParamFlags::empty(),
                def_value: None,
            }],
            implicit_params: FunImplicitParams {
                capability: Capability::CapTy(generic("CAP")),
            },
            ret: generic("RET"),
            flags: oxidized::typing_defs_flags::FunTypeFlags::empty(),
            instantiated: true,
        };
        assert_eq!(names(&mk((r(), Ty_::Tfun(std::rc::Rc::new(ft))))), vec!["P", "TC", "RET"]);
    }

    #[test]
    fn locl_shapes_and_negations() {
        use oxidized::typing_defs_core::PosByteString;
        let field = |s: &str| {
            t_shape_map::TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
                Pos::NONE,
                s.into(),
            )))
        };
        let mut fields = t_shape_map::T::new();
        for (k, ty) in [("b", "B"), ("a", "A")] {
            fields.insert(
                field(k),
                ShapeFieldType {
                    optional: false,
                    ty: generic(ty),
                },
            );
        }
        let shape = mk((
            r(),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: generic("K"),
                fields,
            })),
        ));
        assert_eq!(names(&shape), vec!["K", "A", "B"]);

        // the negation of a class tag is visited as the class, then its
        // filled arguments
        let neg = mk((
            r(),
            Ty_::Tneg(TypePredicate(
                r(),
                TypePredicate_::IsTag(TypeTag::ClassTag(
                    "\\C".to_string(),
                    vec![
                        TypeTagGeneric::Wildcard(0),
                        TypeTagGeneric::Filled(generic("F")),
                    ],
                )),
            )),
        ));
        assert_eq!(names(&neg), vec!["\\C", "F"]);
        let neg_not = mk((
            r(),
            Ty_::Tneg(TypePredicate(
                r(),
                TypePredicate_::IsNot(Box::new(TypePredicate(
                    r(),
                    TypePredicate_::IsTag(TypeTag::ClassTag("\\C".to_string(), vec![])),
                ))),
            )),
        ));
        assert!(names(&neg_not).is_empty());
    }

    #[test]
    fn internal_types() {
        let d = mk_constraint_type((
            r(),
            ConstraintType_::Tdestructure(Destructure {
                required: vec![generic("R")],
                optional: vec![generic("O")],
                variadic: Some(generic("V")),
                kind: DestructureKind::ListDestructure,
            }),
        ));
        assert_eq!(
            InternalNames.on_internal_type(vec![], &InternalType::ConstraintType(d.clone())),
            vec!["R", "O", "V"]
        );
        assert_eq!(
            InternalNames.on_internal_type(
                vec![],
                &InternalType::LoclType(class("\\C", nonexact(), vec![generic("A")]))
            ),
            vec!["A"]
        );
        let s = mk_constraint_type((
            r(),
            ConstraintType_::TtypeSwitch {
                predicate: TypePredicate(r(), TypePredicate_::IsTag(TypeTag::IntTag)),
                ty_true: generic("T"),
                ty_false: generic("F"),
            },
        ));
        assert_eq!(InternalNames.on_constraint_type(vec![], &s), vec!["T", "F"]);
        assert_eq!(
            InternalNames.on_tcunion(vec![], &r(), &generic("L"), &d),
            vec!["L", "R", "O", "V"]
        );
        let htm = mk_constraint_type((
            r(),
            ConstraintType_::ThasTypeMember(HasTypeMember {
                id: "T".to_string(),
                lower: generic("LO"),
                upper: generic("UP"),
            }),
        ));
        assert_eq!(
            InternalNames.on_constraint_type(vec![], &htm),
            vec!["LO", "UP"]
        );
    }

    struct DeclNames;
    impl DeclTypeVisitor<Vec<String>> for DeclNames {
        fn on_tgeneric(
            &mut self,
            mut acc: Vec<String>,
            _r: &DeclReason,
            name: &str,
        ) -> Vec<String> {
            acc.push(name.to_string());
            acc
        }
    }

    #[test]
    fn decl_visit_order() {
        let none = || R::none();
        let generic = |n: &str| DeclTy::generic(none(), TypeName::new(n));
        let pos_id = |n: &str| Positioned::new(pos::BPos::none(), TypeName::new(n));
        let names = |ty: &DeclTy| DeclNames.on_type(vec![], ty);

        let apply = DeclTy::new(
            none(),
            d::Ty_::Tapply(Box::new((
                pos_id("\\C"),
                vec![
                    generic("A"),
                    DeclTy::new(none(), d::Ty_::Tlike(generic("B"))),
                ]
                .into(),
            ))),
        );
        assert_eq!(names(&apply), vec!["A", "B"]);

        let tuple = DeclTy::new(
            none(),
            d::Ty_::Ttuple(Box::new(d::TupleType(
                vec![generic("R")].into(),
                vec![generic("O")].into(),
                d::TupleExtra::Tsplat(generic("S")),
            ))),
        );
        assert_eq!(names(&tuple), vec!["S", "O", "R"]);

        // functions: parameters, constraints of the type parameters,
        // capability, where constraints, return type
        let ft = d::FunType {
            tparams: vec![d::Tparam {
                variance: oxidized::ast_defs::Variance::Invariant,
                name: pos_id("T"),
                constraints: vec![(
                    oxidized::ast_defs::ConstraintKind::ConstraintAs,
                    generic("TC"),
                )]
                .into(),
                reified: oxidized::ast_defs::ReifyKind::Erased,
                user_attributes: Box::new([]),
            }]
            .into(),
            where_constraints: vec![d::WhereConstraint(
                generic("W1"),
                oxidized::ast_defs::ConstraintKind::ConstraintEq,
                generic("W2"),
            )]
            .into(),
            params: vec![d::FunParam {
                pos: pos::BPos::none(),
                name: None,
                ty: generic("P"),
                flags: oxidized::typing_defs_flags::FunParamFlags::empty(),
                def_value: None,
            }]
            .into(),
            implicit_params: d::FunImplicitParams {
                capability: d::Capability::CapTy(generic("CAP")),
            },
            ret: generic("RET"),
            flags: oxidized::typing_defs_flags::FunTypeFlags::empty(),
            instantiated: true,
        };
        let fun = DeclTy::new(none(), d::Ty_::Tfun(Box::new(ft)));
        assert_eq!(names(&fun), vec!["P", "TC", "CAP", "W1", "W2", "RET"]);

        // refinements: the type, then the constants in the order of their
        // names, lower bounds before upper bounds
        let mut consts = std::collections::BTreeMap::new();
        consts.insert(
            pos::TypeConstName::new("TB"),
            d::RefinedConst {
                bound: d::RefinedConstBound::Exact(generic("E")),
                is_ctx: false,
            },
        );
        consts.insert(
            pos::TypeConstName::new("TA"),
            d::RefinedConst {
                bound: d::RefinedConstBound::Loose(d::RefinedConstBounds {
                    lower: vec![generic("L")].into(),
                    upper: vec![generic("U")].into(),
                }),
                is_ctx: false,
            },
        );
        let refinement = DeclTy::new(
            none(),
            d::Ty_::Trefinement(Box::new(d::TrefinementType {
                ty: generic("ROOT"),
                refinement: d::ClassRefinement { consts },
            })),
        );
        assert_eq!(names(&refinement), vec!["ROOT", "L", "U", "E"]);
    }
}
