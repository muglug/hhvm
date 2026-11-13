// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_pos_utils.ml`. See `hh/PORTING.md`.
//!
//! The functor `TraversePos (ImplementPos)` is the generic `TraversePos<I>`
//! over the trait `ImplementPos`; its functions are the associated functions
//! of `TraversePos<I>`. Both are private, as in the `.mli`, which exports
//! only `NormalizeSig`, the only instance: [`normalize_sig`].
//!
//! The declarations are those of `hackrs` (`ty::decl`), whose shapes differ
//! from the OCaml ones in a few places; where they do, the function maps what
//! the `hackrs` type has:
//!
//! - A decl position (`Pos_or_decl.t`) is a `BPos` in the `hackrs` types, and
//!   an `oxidized` `PosOrDecl` in the few `oxidized` types they hold
//!   (`PackageRequirement`). `ImplementPos` therefore has the OCaml
//!   `pos_or_decl` twice: `ImplementPos::pos_or_decl` and
//!   `ImplementPos::pos_or_decl_oxidized`.
//! - `Tany` and `Tdynamic` carry no argument.
//! - A shape has no `s_origin` (the OCaml sets it to `Missing_origin`), and
//!   the positions of its field names are not in the keys of its map but in
//!   the values (`ShapeFieldType::field_name_pos`): `shape_field_name` maps
//!   them there.
//! - `ttc_enforceable` / `stc_enforceable` (`Pos_or_decl.t * bool`) is
//!   `Enforceable(Option<Pos>)`: the position of `Some` is mapped; `None`
//!   (the OCaml `(Pos_or_decl.none, false)`) stays `None`, which is what
//!   `NormalizeSig` gives.
//! - A folded class (`Decl_defs.decl_class_type`) has no `dc_need_init` and
//!   no `dc_abstract` (`hackrs` computes them), and `dc_req_ancestors` is a
//!   list of `Requirement { pos, ty }`.
//!
//! The reasons of declared types are `BReason`s (`crate::ctx::R`):
//! `Typing_reason.map_pos` on them is [`typing_reason_map_pos`] here
//! (`crate::typing_reason::map_pos` is for the reasons of inferred types).

use std::collections::BTreeMap;
use std::marker::PhantomData;

use oxidized::aast_defs::PackageMembership;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::typing_defs::PackageRequirement;
use oxidized::typing_defs_core::PosString;
use pos::Positioned;
use ty::decl::AbstractTypeconst;
use ty::decl::ClassConst;
use ty::decl::ConcreteTypeconst;
use ty::decl::EnumType;
use ty::decl::FoldedClass;
use ty::decl::FunParam;
use ty::decl::FunType;
use ty::decl::Requirement;
use ty::decl::ShallowClass;
use ty::decl::ShallowClassConst;
use ty::decl::ShallowMethod;
use ty::decl::ShallowProp;
use ty::decl::ShallowTypeconst;
use ty::decl::ShapeFieldType;
use ty::decl::SubstContext;
use ty::decl::TaccessType;
use ty::decl::Tparam;
use ty::decl::TrefinementType;
use ty::decl::Ty_;
use ty::decl::TypeConst;
use ty::decl::Typeconst;
use ty::decl::UserAttribute;
use ty::decl::WhereConstraint;
use ty::decl::folded::ConstraintRequirement;
use ty::decl::subst::Subst;
use ty::decl::ty::Capability;
use ty::decl::ty::DeclConstraintRequirement;
use ty::decl::ty::Enforceable;
use ty::decl::ty::FunElt;
use ty::decl::ty::FunImplicitParams;
use ty::decl::ty::ShapeFieldNamePos;
use ty::decl::ty::ShapeType;
use ty::decl::ty::ShapeTypeSimple;
use ty::decl::ty::TshapeFieldName;
use ty::decl::ty::TupleExtra;
use ty::decl::ty::TupleType;
use ty::decl::ty::TypedefCaseTypeVariant;
use ty::decl::ty::TypedefType;
use ty::decl::ty::TypedefTypeAssignment;
use ty::reason::Reason;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::class_refinement;
use crate::ctx::R;
use crate::typing_defs_core::DeclTy;

type BPos = <R as Reason>::Pos;

/// `Typing_reason.map_pos_witness_decl`, on the witnesses of the reasons of
/// declared types (`ty::reason::WitnessDecl<BPos>`).
fn typing_reason_map_pos_witness_decl(
    pos_or_decl: &dyn Fn(&BPos) -> BPos,
    witness: &WitnessDecl<BPos>,
) -> WitnessDecl<BPos> {
    // `positioned_id pos_or_decl (p, x)`
    let positioned_id = |(p, x): &(BPos, pos::Symbol)| (pos_or_decl(p), *x);
    use WitnessDecl::*;
    match witness {
        WitnessFromDecl(p) => WitnessFromDecl(pos_or_decl(p)),
        IdxVectorFromDecl(p) => IdxVectorFromDecl(pos_or_decl(p)),
        IdxStringFromDecl(p) => IdxStringFromDecl(pos_or_decl(p)),
        RetFunKindFromDecl(p, k) => RetFunKindFromDecl(pos_or_decl(p), *k),
        Hint(p) => Hint(pos_or_decl(p)),
        ClassClass(p, s) => ClassClass(pos_or_decl(p), *s),
        VarParamFromDecl(p) => VarParamFromDecl(pos_or_decl(p)),
        TupleFromSplat(p) => TupleFromSplat(pos_or_decl(p)),
        InoutParam(p) => InoutParam(pos_or_decl(p)),
        TconstNoCstr(id) => TconstNoCstr(positioned_id(id)),
        VarrayOrDarrayKey(p) => VarrayOrDarrayKey(pos_or_decl(p)),
        VecOrDictKey(p) => VecOrDictKey(pos_or_decl(p)),
        MissingOptionalField(p, n) => MissingOptionalField(pos_or_decl(p), *n),
        ImplicitUpperBound(p, s) => ImplicitUpperBound(pos_or_decl(p), *s),
        GlobalTypeVariableGenerics(p, t, s) => GlobalTypeVariableGenerics(pos_or_decl(p), *t, *s),
        SolveFail(p) => SolveFail(pos_or_decl(p)),
        CstrOnGenerics(p, sid) => CstrOnGenerics(pos_or_decl(p), positioned_id(sid)),
        Enforceable(p) => Enforceable(pos_or_decl(p)),
        GlobalClassProp(p) => GlobalClassProp(pos_or_decl(p)),
        GlobalFunParam(p) => GlobalFunParam(pos_or_decl(p)),
        GlobalFunRet(p) => GlobalFunRet(pos_or_decl(p)),
        DefaultCapability(p) => DefaultCapability(pos_or_decl(p)),
        SupportDynamicType(p) => SupportDynamicType(pos_or_decl(p)),
        PessimisedInout(p) => PessimisedInout(pos_or_decl(p)),
        PessimisedReturn(p, pr) => PessimisedReturn(pos_or_decl(p), *pr),
        PessimisedProp(p, pr) => PessimisedProp(pos_or_decl(p), *pr),
        PessimisedThis(p) => PessimisedThis(pos_or_decl(p)),
        IllegalRecursiveType(p, name) => IllegalRecursiveType(pos_or_decl(p), *name),
        SupportDynamicTypeAssume(p) => SupportDynamicTypeAssume(pos_or_decl(p)),
        PolymorphicTypeParam(p, new_name, orig_name, rank) => {
            PolymorphicTypeParam(pos_or_decl(p), *new_name, *orig_name, *rank)
        }
        EnforcedType(p) => EnforcedType(pos_or_decl(p)),
    }
}

/// `Typing_reason.map_pos`, on the reasons of declared types (`BReason`,
/// whose constructors are those of the decl phase: `No_reason`,
/// `From_witness_decl` and `Instantiate`).
fn typing_reason_map_pos(
    pos: &dyn Fn(&Pos) -> Pos,
    pos_or_decl: &dyn Fn(&BPos) -> BPos,
    r: &R,
) -> R {
    match r.as_impl() {
        ReasonImpl::NoReason => r.clone(),
        ReasonImpl::FromWitnessDecl(witness) => R::mk(|| {
            ReasonImpl::FromWitnessDecl(typing_reason_map_pos_witness_decl(pos_or_decl, witness))
        }),
        ReasonImpl::Instantiate(type_, var_name, var) => {
            // Record fields are evaluated from right to left.
            let var = typing_reason_map_pos(pos, pos_or_decl, var);
            let type_ = typing_reason_map_pos(pos, pos_or_decl, type_);
            R::mk(|| ReasonImpl::Instantiate(type_, *var_name, var))
        }
    }
}

/// The argument of the functor `TraversePos`:
/// `sig val pos : Pos.t -> Pos.t val pos_or_decl : Pos_or_decl.t -> Pos_or_decl.t end`.
trait ImplementPos {
    fn pos(p: &Pos) -> Pos;

    /// `pos_or_decl`, on the decl positions of the `hackrs` types.
    fn pos_or_decl(p: &BPos) -> BPos;

    /// `pos_or_decl`, on the decl positions that the `hackrs` types keep in
    /// their `oxidized` form (in `PackageRequirement`).
    fn pos_or_decl_oxidized(p: &PosOrDecl) -> PosOrDecl;
}

/// Functor traversing a type, but applies a user defined function for
/// positions. Positions in errors (_decl_errors) are not mapped - entire
/// field is erased instead. This is safe because there exists a completely
/// different system for tracking and updating positions in errors
/// (see ServerTypeCheck.get_files_with_stale_errors)
struct TraversePos<I: ImplementPos>(PhantomData<I>);

impl<I: ImplementPos> TraversePos<I> {
    pub fn pos(p: &Pos) -> Pos {
        I::pos(p)
    }

    pub fn pos_or_decl(p: &BPos) -> BPos {
        I::pos_or_decl(p)
    }

    pub fn positioned_id<S: Copy>(id: &Positioned<S, BPos>) -> Positioned<S, BPos> {
        Positioned::new(Self::pos_or_decl(id.pos()), id.id())
    }

    pub fn ty(t: &DeclTy) -> DeclTy {
        let (r, x) = (t.reason(), t.node_ref());
        // The components of the tuple are evaluated from right to left.
        let x = Self::ty_(x);
        let r = typing_reason_map_pos(&I::pos, &I::pos_or_decl, r);
        DeclTy::new(r, x)
    }

    pub fn ty_(x: &Ty_<R>) -> Ty_<R> {
        match x {
            Ty_::Tany
            | Ty_::Tthis
            | Ty_::Tmixed
            | Ty_::Twildcard
            | Ty_::Tnonnull
            | Ty_::Tdynamic => x.clone(),
            Ty_::TvecOrDict(tys) => {
                let (ty1, ty2) = &**tys;
                let ty2 = Self::ty(ty2);
                let ty1 = Self::ty(ty1);
                Ty_::TvecOrDict(Box::new((ty1, ty2)))
            }
            Ty_::Tprim(_) => x.clone(),
            Ty_::Tgeneric(_) => x.clone(),
            Ty_::Ttuple(tuple) => {
                let TupleType(t_required, t_optional, t_extra) = &**tuple;
                // Record fields are evaluated from right to left.
                let t_extra = Self::tuple_extra(t_extra);
                let t_optional = t_optional.iter().map(Self::ty).collect();
                let t_required = t_required.iter().map(Self::ty).collect();
                Ty_::Ttuple(Box::new(TupleType(t_required, t_optional, t_extra)))
            }
            Ty_::Tunion(tyl) => Ty_::Tunion(tyl.iter().map(Self::ty).collect()),
            Ty_::Tintersection(tyl) => Ty_::Tintersection(tyl.iter().map(Self::ty).collect()),
            Ty_::Toption(x) => Ty_::Toption(Self::ty(x)),
            Ty_::Tlike(x) => Ty_::Tlike(Self::ty(x)),
            Ty_::Tfun(ft) => Ty_::Tfun(Box::new(Self::fun_type(ft))),
            Ty_::Tapply(id_and_args) => {
                let (sid, xl) = &**id_and_args;
                let xl = xl.iter().map(Self::ty).collect();
                let sid = Self::positioned_id(sid);
                Ty_::Tapply(Box::new((sid, xl)))
            }
            Ty_::Taccess(taccess) => {
                let TaccessType {
                    ty: root_ty,
                    type_const: id,
                } = &**taccess;
                let id = Self::positioned_id(id);
                let root_ty = Self::ty(root_ty);
                Ty_::Taccess(Box::new(TaccessType {
                    ty: root_ty,
                    type_const: id,
                }))
            }
            Ty_::Trefinement(trefinement) => {
                let TrefinementType {
                    ty: root_ty,
                    refinement: rs,
                } = &**trefinement;
                let rs = class_refinement::map_decl(|t| Self::ty(&t), rs.clone());
                Ty_::Trefinement(Box::new(TrefinementType {
                    ty: Self::ty(root_ty),
                    refinement: rs,
                }))
            }
            Ty_::Tshape(shape) => match &**shape {
                ShapeType::Simple(s) => {
                    Ty_::Tshape(Box::new(ShapeType::Simple(Self::shape_type(s))))
                }
                ShapeType::Splat(ss_elems) => Ty_::Tshape(Box::new(ShapeType::Splat(
                    ss_elems.iter().map(Self::ty).collect(),
                ))),
            },
            Ty_::TclassPtr(x) => Ty_::TclassPtr(Self::ty(x)),
        }
    }

    pub fn tuple_extra(e: &TupleExtra<R>) -> TupleExtra<R> {
        match e {
            TupleExtra::Tsplat(t_splat) => TupleExtra::Tsplat(Self::ty(t_splat)),
            TupleExtra::Tvariadic(t_variadic) => TupleExtra::Tvariadic(Self::ty(t_variadic)),
        }
    }

    pub fn ty_opt(x: Option<&DeclTy>) -> Option<DeclTy> {
        x.map(Self::ty)
    }

    /// The names of the fields of a `hackrs` shape have no position; their
    /// positions are in the values of the map (`field_name_pos`), which this
    /// maps.
    pub fn shape_field_name(
        name: &TshapeFieldName,
        field_name_pos: &ShapeFieldNamePos<BPos>,
    ) -> (TshapeFieldName, ShapeFieldNamePos<BPos>) {
        match (name, field_name_pos) {
            (TshapeFieldName::TSFregexGroup(_), ShapeFieldNamePos::Simple(p)) => {
                (*name, ShapeFieldNamePos::Simple(Self::pos_or_decl(p)))
            }
            (TshapeFieldName::TSFlitStr(_), ShapeFieldNamePos::Simple(p)) => {
                (*name, ShapeFieldNamePos::Simple(Self::pos_or_decl(p)))
            }
            (TshapeFieldName::TSFclassConst(_, _), ShapeFieldNamePos::ClassConst(p_id, p_s)) => {
                // The components of the tuple are evaluated from right to left.
                let p_s = Self::pos_or_decl(p_s);
                let p_id = Self::pos_or_decl(p_id);
                (*name, ShapeFieldNamePos::ClassConst(p_id, p_s))
            }
            (
                TshapeFieldName::TSFregexGroup(_) | TshapeFieldName::TSFlitStr(_),
                ShapeFieldNamePos::ClassConst(_, _),
            ) => panic!("expected ShapeFieldNamePos::Simple"),
            (TshapeFieldName::TSFclassConst(_, _), ShapeFieldNamePos::Simple(_)) => {
                panic!("expected ShapeFieldNamePos::ClassConst")
            }
        }
    }

    pub fn constraint_<CK: Clone>(x: &[(CK, DeclTy)]) -> Box<[(CK, DeclTy)]> {
        x.iter().map(|(ck, x)| (ck.clone(), Self::ty(x))).collect()
    }

    pub fn capability(c: &Capability<R, DeclTy>) -> Capability<R, DeclTy> {
        match c {
            Capability::CapTy(cap) => Capability::CapTy(Self::ty(cap)),
            Capability::CapDefaults(p) => Capability::CapDefaults(Self::pos_or_decl(p)),
        }
    }

    pub fn fun_implicit_params(
        implicit: &FunImplicitParams<R, DeclTy>,
    ) -> FunImplicitParams<R, DeclTy> {
        FunImplicitParams {
            capability: Self::capability(&implicit.capability),
        }
    }

    pub fn fun_type(ft: &FunType<R, DeclTy>) -> FunType<R, DeclTy> {
        // `{ ft with ... }`; record fields are evaluated from right to left.
        let ft_ret = Self::ty(&ft.ret);
        let ft_implicit_params = Self::fun_implicit_params(&ft.implicit_params);
        let ft_params = ft.params.iter().map(Self::fun_param).collect();
        let ft_where_constraints = ft
            .where_constraints
            .iter()
            .map(Self::where_constraint)
            .collect();
        let ft_tparams = ft.tparams.iter().map(Self::type_param).collect();
        FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags: ft.flags,
            instantiated: ft.instantiated,
        }
    }

    pub fn shape_type(s: &ShapeTypeSimple<R>) -> ShapeTypeSimple<R> {
        // `{ s_origin = _; s_unknown_value = shape_kind; s_fields = fdm }`
        let ShapeTypeSimple(shape_kind, fdm) = s;
        // TODO(shapes) Should this be changing s_origin? (`hackrs` shapes have
        // no `s_origin`; the OCaml sets it to `Missing_origin`.)
        //
        // `ShapeFieldMap.map_and_rekey fdm shape_field_name ty`: a fold that
        // adds each rekeyed binding to an empty map.
        let mut s_fields: BTreeMap<TshapeFieldName, ShapeFieldType<R>> = BTreeMap::new();
        for (k, sft) in fdm.iter() {
            // `add (f1 k) (f2 v) acc`: the arguments are evaluated from right
            // to left.
            let sft_ty = Self::ty(&sft.ty);
            let (k, field_name_pos) = Self::shape_field_name(k, &sft.field_name_pos);
            s_fields.insert(
                k,
                ShapeFieldType {
                    field_name_pos,
                    optional: sft.optional,
                    ty: sft_ty,
                },
            );
        }
        ShapeTypeSimple(
            // TODO(shapes) s_unknown_value is missing a call to ty
            shape_kind.clone(),
            s_fields,
        )
    }

    pub fn fun_elt(fe: &FunElt<R>) -> FunElt<R> {
        // `{ fe with ... }`; record fields are evaluated from right to left.
        let fe_package_requirement = Self::package_requirement(&fe.package_requirement);
        let fe_package = fe.package.as_ref().map(Self::package_membership);
        let fe_pos = Self::pos_or_decl(&fe.pos);
        let fe_type = Self::ty(&fe.ty);
        FunElt {
            deprecated: fe.deprecated,
            module: fe.module.clone(),
            package: fe_package,
            internal: fe.internal,
            ty: fe_type,
            pos: fe_pos,
            php_std_lib: fe.php_std_lib,
            support_dynamic_type: fe.support_dynamic_type,
            no_auto_dynamic: fe.no_auto_dynamic,
            no_auto_likes: fe.no_auto_likes,
            gated_by_feature_flag: fe.gated_by_feature_flag.clone(),
            package_requirement: fe_package_requirement,
        }
    }

    pub fn where_constraint(wc: &WhereConstraint<DeclTy>) -> WhereConstraint<DeclTy> {
        let WhereConstraint(ty1, c, ty2) = wc;
        let ty2 = Self::ty(ty2);
        let ty1 = Self::ty(ty1);
        WhereConstraint(ty1, *c, ty2)
    }

    pub fn fun_param(param: &FunParam<R, DeclTy>) -> FunParam<R, DeclTy> {
        // `{ param with fp_pos = ...; fp_type = ... }`
        let fp_type = Self::ty(&param.ty);
        let fp_pos = Self::pos_or_decl(&param.pos);
        FunParam {
            pos: fp_pos,
            name: param.name,
            ty: fp_type,
            flags: param.flags,
            def_value: param.def_value.clone(),
        }
    }

    pub fn class_const(cc: &ClassConst<R>) -> ClassConst<R> {
        let cc_type = Self::ty(&cc.ty);
        let cc_pos = Self::pos_or_decl(&cc.pos);
        ClassConst {
            is_synthesized: cc.is_synthesized,
            kind: cc.kind,
            pos: cc_pos,
            ty: cc_type,
            origin: cc.origin,
            refs: cc.refs.clone(),
            is_shape_key: cc.is_shape_key,
            value: cc.value.clone(),
        }
    }

    pub fn typeconst(t: &Typeconst<R>) -> Typeconst<R> {
        match t {
            Typeconst::TCAbstract(AbstractTypeconst {
                as_constraint: atc_as_constraint,
                super_constraint: atc_super_constraint,
                default: atc_default,
            }) => {
                let atc_default = Self::ty_opt(atc_default.as_ref());
                let atc_super_constraint = Self::ty_opt(atc_super_constraint.as_ref());
                let atc_as_constraint = Self::ty_opt(atc_as_constraint.as_ref());
                Typeconst::TCAbstract(AbstractTypeconst {
                    as_constraint: atc_as_constraint,
                    super_constraint: atc_super_constraint,
                    default: atc_default,
                })
            }
            Typeconst::TCConcrete(ConcreteTypeconst { ty: tc_type }) => {
                Typeconst::TCConcrete(ConcreteTypeconst {
                    ty: Self::ty(tc_type),
                })
            }
        }
    }

    pub fn typeconst_type(tc: &TypeConst<R>) -> TypeConst<R> {
        // Record fields are evaluated from right to left.
        let ttc_reifiable = tc.reifiable.as_ref().map(Self::pos_or_decl);
        // `Tuple.T2.map_fst ~f:pos_or_decl tc.ttc_enforceable`
        let ttc_enforceable = Enforceable(tc.enforceable.as_ref().map(Self::pos_or_decl));
        let ttc_kind = Self::typeconst(&tc.kind);
        let ttc_name = Self::positioned_id(&tc.name);
        TypeConst {
            is_synthesized: tc.is_synthesized,
            name: ttc_name,
            kind: ttc_kind,
            origin: tc.origin,
            enforceable: ttc_enforceable,
            reifiable: ttc_reifiable,
            is_concretized: tc.is_concretized,
            is_ctx: tc.is_ctx,
        }
    }

    pub fn user_attribute(ua: &UserAttribute<BPos>) -> UserAttribute<BPos> {
        let UserAttribute {
            name: ua_name,
            params: ua_params,
            raw_val: _,
        } = ua;
        UserAttribute {
            name: Self::positioned_id(ua_name),
            params: ua_params.clone(),
            raw_val: None,
        }
    }

    pub fn type_param(t: &Tparam<R, DeclTy>) -> Tparam<R, DeclTy> {
        // Record fields are evaluated from right to left.
        let tp_user_attributes = t.user_attributes.iter().map(Self::user_attribute).collect();
        let tp_constraints = Self::constraint_(&t.constraints);
        let tp_name = Self::positioned_id(&t.name);
        Tparam {
            name: tp_name,
            variance: t.variance.clone(),
            reified: t.reified.clone(),
            constraints: tp_constraints,
            user_attributes: tp_user_attributes,
        }
    }

    pub fn package_membership(m: &PackageMembership) -> PackageMembership {
        match m {
            PackageMembership::PackageOverride(p, name) => {
                PackageMembership::PackageOverride(Self::pos(p), name.clone())
            }
            PackageMembership::PackageConfigAssignment(name) => {
                PackageMembership::PackageConfigAssignment(name.clone())
            }
        }
    }

    pub fn package_requirement(r: &PackageRequirement) -> PackageRequirement {
        match r {
            PackageRequirement::RPRequire(PosString(p, s)) => {
                PackageRequirement::RPRequire(PosString(I::pos_or_decl_oxidized(p), s.clone()))
            }
            PackageRequirement::RPSoft(PosString(p, s)) => {
                PackageRequirement::RPSoft(PosString(I::pos_or_decl_oxidized(p), s.clone()))
            }
            PackageRequirement::RPNormal => PackageRequirement::RPNormal,
        }
    }

    pub fn class_type(dc: &FoldedClass<R>) -> FoldedClass<R> {
        // Record fields are evaluated from right to left.
        let dc_package = dc.package.as_ref().map(Self::package_membership);
        let dc_enum_type = dc.enum_type.as_ref().map(Self::enum_type);
        let dc_ancestors = dc
            .ancestors
            .iter()
            .map(|(name, t)| (*name, Self::ty(t)))
            .collect();
        let dc_typeconsts = dc
            .type_consts
            .iter()
            .map(|(name, tc)| (*name, Self::typeconst_type(tc)))
            .collect();
        let dc_consts = dc
            .consts
            .iter()
            .map(|(name, cc)| (*name, Self::class_const(cc)))
            .collect();
        let dc_substs = dc
            .substs
            .iter()
            .map(|(name, sc)| {
                // `{ sc with sc_subst = S_map.map ty sc_subst }`
                let sc_subst = Subst(sc.subst.0.iter().map(|(n, t)| (*n, Self::ty(t))).collect());
                (
                    *name,
                    SubstContext {
                        subst: sc_subst,
                        class_context: sc.class_context,
                        from_req_extends: sc.from_req_extends,
                    },
                )
            })
            .collect();
        let dc_tparams = dc.tparams.iter().map(Self::type_param).collect();
        let dc_req_constraints_ancestors = dc
            .req_constraints_ancestors
            .iter()
            .map(Self::constraint_requirement)
            .collect();
        let dc_req_ancestors = dc.req_ancestors.iter().map(Self::requirement).collect();
        FoldedClass {
            name: dc.name,
            pos: dc.pos.clone(),
            kind: dc.kind,
            is_final: dc.is_final,
            is_const: dc.is_const,
            is_internal: dc.is_internal,
            tests_bypass_visibility: dc.tests_bypass_visibility,
            allow_unchecked_enum_values: dc.allow_unchecked_enum_values,
            is_xhp: dc.is_xhp,
            has_xhp_keyword: dc.has_xhp_keyword,
            support_dynamic_type: dc.support_dynamic_type,
            enum_type: dc_enum_type,
            module: dc.module.clone(),
            is_module_level_trait: dc.is_module_level_trait,
            tparams: dc_tparams,
            substs: dc_substs,
            ancestors: dc_ancestors,
            props: dc.props.clone(),
            static_props: dc.static_props.clone(),
            methods: dc.methods.clone(),
            static_methods: dc.static_methods.clone(),
            constructor: dc.constructor.clone(),
            consts: dc_consts,
            type_consts: dc_typeconsts,
            xhp_enum_values: dc.xhp_enum_values.clone(),
            xhp_marked_empty: dc.xhp_marked_empty,
            extends: dc.extends.clone(),
            xhp_attr_deps: dc.xhp_attr_deps.clone(),
            req_ancestors: dc_req_ancestors,
            req_ancestors_extends: dc.req_ancestors_extends.clone(),
            req_constraints_ancestors: dc_req_constraints_ancestors,
            sealed_whitelist: dc.sealed_whitelist.clone(),
            deferred_init_members: dc.deferred_init_members.clone(),
            decl_errors: Box::new([]),
            docs_url: dc.docs_url.clone(),
            allow_multiple_instantiations: dc.allow_multiple_instantiations,
            package: dc_package,
        }
    }

    /// `requirement (p, t)`
    pub fn requirement(r: &Requirement<R>) -> Requirement<R> {
        let t = Self::ty(&r.ty);
        let p = Self::pos_or_decl(&r.pos);
        Requirement::new(p, t)
    }

    pub fn constraint_requirement(cr: &ConstraintRequirement<R>) -> ConstraintRequirement<R> {
        match cr {
            ConstraintRequirement::CREqual(r) => {
                ConstraintRequirement::CREqual(Self::requirement(r))
            }
            ConstraintRequirement::CRSubtype(r) => {
                ConstraintRequirement::CRSubtype(Self::requirement(r))
            }
        }
    }

    pub fn enum_type(te: &EnumType<R>) -> EnumType<R> {
        // Record fields are evaluated from right to left.
        let te_includes = te.includes.iter().map(Self::ty).collect();
        let te_constraint = Self::ty_opt(te.constraint.as_ref());
        let te_base = Self::ty(&te.base);
        EnumType {
            base: te_base,
            constraint: te_constraint,
            includes: te_includes,
        }
    }

    pub fn typedef(tdef: &TypedefType<R>) -> TypedefType<R> {
        // Record fields are evaluated from right to left.
        let td_package = tdef.package.as_ref().map(Self::package_membership);
        let td_attributes = tdef.attributes.iter().map(Self::user_attribute).collect();
        let td_type_assignment = match &tdef.type_assignment {
            TypedefTypeAssignment::SimpleTypeDef(vis, t) => {
                TypedefTypeAssignment::SimpleTypeDef(*vis, Self::ty(t))
            }
            TypedefTypeAssignment::CaseType(variant, variants) => {
                let f = |v: &TypedefCaseTypeVariant<R>| {
                    let wcs = v
                        .where_constraints
                        .iter()
                        .map(Self::where_constraint)
                        .collect();
                    TypedefCaseTypeVariant {
                        hint: Self::ty(&v.hint),
                        where_constraints: wcs,
                    }
                };
                let variants = variants.iter().map(f).collect();
                TypedefTypeAssignment::CaseType(f(variant), variants)
            }
        };
        let td_super_constraint = Self::ty_opt(tdef.super_constraint.as_ref());
        let td_as_constraint = Self::ty_opt(tdef.as_constraint.as_ref());
        let td_tparams = tdef.tparams.iter().map(Self::type_param).collect();
        let td_pos = Self::pos_or_decl(&tdef.pos);
        TypedefType {
            module: tdef.module.clone(),
            pos: td_pos,
            tparams: td_tparams,
            as_constraint: td_as_constraint,
            super_constraint: td_super_constraint,
            type_assignment: td_type_assignment,
            is_ctx: tdef.is_ctx,
            attributes: td_attributes,
            internal: tdef.internal,
            docs_url: tdef.docs_url.clone(),
            package: td_package,
        }
    }

    pub fn shallow_class(sc: &ShallowClass<R>) -> ShallowClass<R> {
        // Record fields are evaluated from right to left.
        let sc_package = sc.package.as_ref().map(Self::package_membership);
        let sc_enum_type = sc.enum_type.as_ref().map(Self::enum_type);
        let sc_user_attributes = sc
            .user_attributes
            .iter()
            .map(Self::user_attribute)
            .collect();
        let sc_methods = sc.methods.iter().map(Self::shallow_method).collect();
        let sc_static_methods = sc.static_methods.iter().map(Self::shallow_method).collect();
        let sc_constructor = sc.constructor.as_ref().map(Self::shallow_method);
        let sc_sprops = sc.static_props.iter().map(Self::shallow_prop).collect();
        let sc_props = sc.props.iter().map(Self::shallow_prop).collect();
        let sc_typeconsts = sc.typeconsts.iter().map(Self::shallow_typeconst).collect();
        let sc_consts = sc.consts.iter().map(Self::shallow_class_const).collect();
        let sc_implements = sc.implements.iter().map(Self::ty).collect();
        let sc_req_constraints = sc
            .req_constraints
            .iter()
            .map(Self::shallow_req_constraint)
            .collect();
        let sc_req_implements = sc.req_implements.iter().map(Self::ty).collect();
        let sc_req_extends = sc.req_extends.iter().map(Self::ty).collect();
        let sc_xhp_attr_uses = sc.xhp_attr_uses.iter().map(Self::ty).collect();
        let sc_uses = sc.uses.iter().map(Self::ty).collect();
        let sc_extends = sc.extends.iter().map(Self::ty).collect();
        let sc_tparams = sc.tparams.iter().map(Self::type_param).collect();
        let sc_name = Self::positioned_id(&sc.name);
        ShallowClass {
            mode: sc.mode,
            is_final: sc.is_final,
            is_abstract: sc.is_abstract,
            is_xhp: sc.is_xhp,
            is_internal: sc.is_internal,
            has_xhp_keyword: sc.has_xhp_keyword,
            kind: sc.kind,
            module: sc.module.clone(),
            name: sc_name,
            tparams: sc_tparams,
            extends: sc_extends,
            uses: sc_uses,
            xhp_attr_uses: sc_xhp_attr_uses,
            xhp_enum_values: sc.xhp_enum_values.clone(),
            xhp_marked_empty: sc.xhp_marked_empty,
            req_extends: sc_req_extends,
            req_implements: sc_req_implements,
            req_constraints: sc_req_constraints,
            implements: sc_implements,
            support_dynamic_type: sc.support_dynamic_type,
            consts: sc_consts,
            typeconsts: sc_typeconsts,
            props: sc_props,
            static_props: sc_sprops,
            constructor: sc_constructor,
            static_methods: sc_static_methods,
            methods: sc_methods,
            user_attributes: sc_user_attributes,
            enum_type: sc_enum_type,
            docs_url: sc.docs_url.clone(),
            package: sc_package,
        }
    }

    pub fn shallow_class_const(scc: &ShallowClassConst<R>) -> ShallowClassConst<R> {
        // Record fields are evaluated from right to left.
        let scc_type = Self::ty(&scc.ty);
        let scc_name = Self::positioned_id(&scc.name);
        ShallowClassConst {
            kind: scc.kind,
            name: scc_name,
            ty: scc_type,
            refs: scc.refs.clone(),
            is_shape_key: scc.is_shape_key,
            value: scc.value.clone(),
            const_value: scc.const_value.clone(),
        }
    }

    pub fn shallow_typeconst(stc: &ShallowTypeconst<R>) -> ShallowTypeconst<R> {
        // Record fields are evaluated from right to left.
        let stc_reifiable = stc.reifiable.as_ref().map(Self::pos_or_decl);
        // `(pos_or_decl (fst stc.stc_enforceable), snd stc.stc_enforceable)`
        let stc_enforceable = Enforceable(stc.enforceable.as_ref().map(Self::pos_or_decl));
        let stc_name = Self::positioned_id(&stc.name);
        let stc_kind = Self::typeconst(&stc.kind);
        ShallowTypeconst {
            kind: stc_kind,
            name: stc_name,
            enforceable: stc_enforceable,
            reifiable: stc_reifiable,
            is_ctx: stc.is_ctx,
        }
    }

    pub fn shallow_prop(sp: &ShallowProp<R>) -> ShallowProp<R> {
        // Record fields are evaluated from right to left.
        let sp_type = Self::ty(&sp.ty);
        let sp_name = Self::positioned_id(&sp.name);
        ShallowProp {
            name: sp_name,
            xhp_attr: sp.xhp_attr,
            ty: sp_type,
            visibility: sp.visibility,
            flags: sp.flags,
        }
    }

    pub fn shallow_method(sm: &ShallowMethod<R>) -> ShallowMethod<R> {
        // Record fields are evaluated from right to left.
        let sm_package_requirement = Self::package_requirement(&sm.package_requirement);
        let sm_type = Self::ty(&sm.ty);
        let sm_name = Self::positioned_id(&sm.name);
        ShallowMethod {
            name: sm_name,
            ty: sm_type,
            visibility: sm.visibility,
            deprecated: sm.deprecated,
            flags: sm.flags,
            attributes: sm.attributes.clone(),
            package_requirement: sm_package_requirement,
        }
    }

    pub fn shallow_req_constraint(
        src: &DeclConstraintRequirement<R>,
    ) -> DeclConstraintRequirement<R> {
        match src {
            DeclConstraintRequirement::DCREqual(cr) => {
                DeclConstraintRequirement::DCREqual(Self::ty(cr))
            }
            DeclConstraintRequirement::DCRSubtype(cr) => {
                DeclConstraintRequirement::DCRSubtype(Self::ty(cr))
            }
        }
    }
}

/// Returns a signature with all the positions replaced with Pos.none
pub mod normalize_sig {
    use super::*;

    /// `struct let pos _ = Pos.none let pos_or_decl _ = Pos_or_decl.none end`
    pub(super) struct ImplementPosNone;

    impl ImplementPos for ImplementPosNone {
        fn pos(_: &Pos) -> Pos {
            Pos::NONE
        }

        fn pos_or_decl(_: &BPos) -> BPos {
            BPos::none()
        }

        fn pos_or_decl_oxidized(_: &PosOrDecl) -> PosOrDecl {
            PosOrDecl::NONE
        }
    }

    /// `module NormalizeSig = TraversePos (...)`
    pub(super) type NormalizeSig = TraversePos<ImplementPosNone>;

    pub fn typedef(tdef: &TypedefType<R>) -> TypedefType<R> {
        NormalizeSig::typedef(tdef)
    }

    pub fn fun_elt(fe: &FunElt<R>) -> FunElt<R> {
        NormalizeSig::fun_elt(fe)
    }

    pub fn class_type(dc: &FoldedClass<R>) -> FoldedClass<R> {
        NormalizeSig::class_type(dc)
    }

    pub fn ty(t: &DeclTy) -> DeclTy {
        NormalizeSig::ty(t)
    }

    pub fn shallow_class_const(scc: &ShallowClassConst<R>) -> ShallowClassConst<R> {
        NormalizeSig::shallow_class_const(scc)
    }

    pub fn shallow_typeconst(stc: &ShallowTypeconst<R>) -> ShallowTypeconst<R> {
        NormalizeSig::shallow_typeconst(stc)
    }

    pub fn shallow_method(sm: &ShallowMethod<R>) -> ShallowMethod<R> {
        NormalizeSig::shallow_method(sm)
    }

    pub fn shallow_prop(sp: &ShallowProp<R>) -> ShallowProp<R> {
        NormalizeSig::shallow_prop(sp)
    }

    pub fn shallow_class(sc: &ShallowClass<R>) -> ShallowClass<R> {
        NormalizeSig::shallow_class(sc)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;
    use pos::FunName;
    use pos::TypeName;

    use super::*;
    use crate::decl_provider;
    use crate::decl_provider::testing::ctx_of;

    fn shallow_class(src: &str, name: &str) -> Arc<ShallowClass<R>> {
        let ctx = ctx_of(src, TypecheckerOptions::default());
        decl_provider::get_shallow_class(&ctx, name).unwrap()
    }

    fn fun(src: &str, name: &str) -> Arc<FunElt<R>> {
        let ctx = ctx_of(src, TypecheckerOptions::default());
        ctx.shallow_decls
            .get_fun(FunName::new(name))
            .unwrap()
            .unwrap()
    }

    fn typedef(src: &str, name: &str) -> Arc<TypedefType<R>> {
        let ctx = ctx_of(src, TypecheckerOptions::default());
        ctx.folded_decls
            .get_typedef(TypeName::new(name))
            .unwrap()
            .unwrap()
    }

    #[test]
    fn positions_only_changes_are_normalized_away() {
        let c1 = shallow_class(
            "<?hh\nclass C<T> {\n  const int X = 1;\n  public int $p = 0;\n  public function m(shape('a' => int, ?'b' => T) $x, (int, string) $y): ?vec<T> { return null; }\n  abstract const type TC as num;\n}\n",
            "\\C",
        );
        let c2 = shallow_class(
            "<?hh\n\n\n  class   C<T> {\n\n  const   int X = 1;\n    public int $p = 0;\n  public function m(shape('a' => int, ?'b' => T) $x,\n (int, string) $y): ?vec<T> { return null; }\n    abstract const type TC as num;\n}\n",
            "\\C",
        );
        assert!(*c1 != *c2);
        let n1 = normalize_sig::shallow_class(&c1);
        let n2 = normalize_sig::shallow_class(&c2);
        assert_eq!(n1, n2);
        assert!(n1.name.pos().is_none());
        // Normalizing is idempotent.
        assert_eq!(normalize_sig::shallow_class(&n1), n1);
        assert_eq!(
            normalize_sig::shallow_method(&c1.methods[0]),
            normalize_sig::shallow_method(&c2.methods[0])
        );
        assert_eq!(
            normalize_sig::shallow_prop(&c1.props[0]),
            normalize_sig::shallow_prop(&c2.props[0])
        );
        assert_eq!(
            normalize_sig::shallow_class_const(&c1.consts[0]),
            normalize_sig::shallow_class_const(&c2.consts[0])
        );
        assert_eq!(
            normalize_sig::shallow_typeconst(&c1.typeconsts[0]),
            normalize_sig::shallow_typeconst(&c2.typeconsts[0])
        );
        let ty1 = &c1.methods[0].ty;
        let n = normalize_sig::ty(ty1);
        assert!(n.pos().is_none());
        assert_eq!(n, normalize_sig::ty(&c2.methods[0].ty));
    }

    #[test]
    fn real_changes_survive_normalization() {
        let c1 = shallow_class(
            "<?hh\nclass C { public function m(): int { return 1; } }\n",
            "\\C",
        );
        let c2 = shallow_class(
            "<?hh\nclass C { public function m(): string { return ''; } }\n",
            "\\C",
        );
        assert!(normalize_sig::shallow_class(&c1) != normalize_sig::shallow_class(&c2));
    }

    #[test]
    fn what_is_not_normalized() {
        // The attributes of a method keep their positions (`sm_attributes` is
        // not mapped); those of a class lose their positions and raw values.
        // (`__Sealed` and `__NoAutoDynamic` are attributes that the decl
        // parser always keeps.)
        let src1 = "<?hh\n<<__Sealed(D::class)>>\nclass C { <<__NoAutoDynamic>> public function m(): void {} }\nclass D extends C {}\n";
        let src2 = "<?hh\n\n<<__Sealed(D::class)>>\nclass C {\n <<__NoAutoDynamic>> public function m(): void {} }\nclass D extends C {}\n";
        let c1 = normalize_sig::shallow_class(&shallow_class(src1, "\\C"));
        let c2 = normalize_sig::shallow_class(&shallow_class(src2, "\\C"));
        assert!(!c1.user_attributes.is_empty());
        assert_eq!(c1.user_attributes, c2.user_attributes);
        assert!(c1.user_attributes.iter().all(|ua| ua.raw_val.is_none()));
        assert!(!c1.methods[0].attributes.is_empty());
        assert!(c1.methods[0].attributes != c2.methods[0].attributes);
    }

    #[test]
    fn functions_and_typedefs() {
        let f1 = fun("<?hh\nfunction f(int $x): string { return ''; }\n", "\\f");
        let f2 = fun(
            "<?hh\n\nfunction   f(int $x):\n string { return ''; }\n",
            "\\f",
        );
        assert!(*f1 != *f2);
        assert_eq!(normalize_sig::fun_elt(&f1), normalize_sig::fun_elt(&f2));
        assert!(normalize_sig::fun_elt(&f1).pos.is_none());
        let f3 = fun("<?hh\nfunction f(int $x): int { return 1; }\n", "\\f");
        assert!(normalize_sig::fun_elt(&f1) != normalize_sig::fun_elt(&f3));

        let t1 = typedef("<?hh\ntype T<X> = shape('a' => X);\n", "\\T");
        let t2 = typedef("<?hh\n\ntype   T<X> =\n shape('a' => X);\n", "\\T");
        assert!(*t1 != *t2);
        assert_eq!(normalize_sig::typedef(&t1), normalize_sig::typedef(&t2));
        let t3 = typedef("<?hh\ntype T<X> = shape('b' => X);\n", "\\T");
        assert!(normalize_sig::typedef(&t1) != normalize_sig::typedef(&t3));
    }

    #[test]
    fn package_positions() {
        let r = PackageRequirement::RPRequire(PosString(Pos::NONE, "pkg".to_string()));
        assert_eq!(normalize_sig::NormalizeSig::package_requirement(&r), r);
        assert_eq!(
            normalize_sig::NormalizeSig::package_membership(&PackageMembership::PackageOverride(
                Pos::NONE,
                "pkg".to_string()
            )),
            PackageMembership::PackageOverride(Pos::NONE, "pkg".to_string())
        );
    }
}
