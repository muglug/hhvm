// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/type_mapper_generic.ml`. See `hh/PORTING.md`.
//!
//! # Classes
//!
//! Each OCaml class is a trait whose default methods are the methods of the
//! class, *including the ones it inherits*; a mapper is a type that implements
//! the trait of the class it would inherit from, and overrides methods by
//! defining them:
//!
//! | OCaml | Rust |
//! |---|---|
//! | `class ['env] shallow_type_mapper` | [`ShallowTypeMapper<Env>`] |
//! | `class ['env] deep_type_mapper` | [`DeepTypeMapper<Env>`] |
//! | `class ['env] constraint_type_mapper` | [`ConstraintTypeMapper<Env>`] |
//! | `class ['env] internal_type_mapper` | [`InternalTypeMapper<Env>`] |
//!
//! ```ignore
//! // let mapper = object (this)
//! //   inherit [env] Type_mapper_generic.deep_type_mapper
//! //   method! on_tvar env r n = ...
//! // end
//! struct Mapper;
//! impl DeepTypeMapper<Env> for Mapper {
//!     fn on_tvar(&mut self, env: &mut Env, r: Reason, n: isize) -> Ty { ... }
//! }
//! ```
//!
//! The traits are independent of each other (a trait cannot override a default
//! method of a supertrait, which is what `method!` does), so the class types
//! (`type_mapper_type`, `constraint_type_mapper_type`,
//! `locl_constraint_type_mapper_type`, `internal_type_mapper_type`) have no
//! counterpart: they are the method lists of the four traits.
//!
//! The environment is threaded (`'env -> ... -> 'env * locl_ty` is
//! `&mut Env -> ... -> Ty`), and types are taken and returned by value.
//!
//! The `method private`s of `deep_type_mapper` (`on_tparam`, `on_param`, ...)
//! cannot be seen or overridden outside of the OCaml module (the `.mli` gives
//! the classes the class types): they are functions here.
//!
//! The methods are written once, in the macros below, which `type_mapper.rs`
//! also uses.

use oxidized::ast_defs::Tprim;

use crate::typing_defs_constraints::*;
use crate::typing_defs_core::*;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

pub fn fresh_env<Env>(env: Env) -> Env {
    env
}

/// The private methods of `deep_type_mapper` and of the classes that inherit
/// it. `on_type` is `this#on_type`.
pub(crate) mod private {
    use super::*;

    pub(crate) type OnType<'a, Env> = &'a mut dyn FnMut(&mut Env, Ty) -> Ty;

    pub(crate) fn on_tuple_extra<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        e: TupleExtra,
    ) -> TupleExtra {
        match e {
            TupleExtra::Tsplat(t_splat) => {
                let t_splat = on_type(env, t_splat);
                TupleExtra::Tsplat(t_splat)
            }
            TupleExtra::Tvariadic(t_variadic) => {
                let t_variadic = on_type(env, t_variadic);
                TupleExtra::Tvariadic(t_variadic)
            }
        }
    }

    pub(crate) fn on_tparam<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        tparam: Tparam,
    ) -> Tparam {
        let Tparam {
            variance: tp_variance,
            name: tp_name,
            constraints: tp_constraints,
            reified: tp_reified,
            user_attributes: tp_user_attributes,
        } = tparam;
        let tp_constraints = tp_constraints
            .into_iter()
            .map(|(cstr, ty)| {
                let ty = on_type(env, ty);
                (cstr, ty)
            })
            .collect();
        Tparam {
            variance: tp_variance,
            name: tp_name,
            constraints: tp_constraints,
            reified: tp_reified,
            user_attributes: tp_user_attributes,
        }
    }

    pub(crate) fn on_where_constraint<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        cstr: WhereConstraint,
    ) -> WhereConstraint {
        let WhereConstraint(ty1, kind, ty2) = cstr;
        let ty1 = on_type(env, ty1);
        let ty2 = on_type(env, ty2);
        WhereConstraint(ty1, kind, ty2)
    }

    pub(crate) fn on_param<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        param: FunParam,
    ) -> FunParam {
        let FunParam {
            pos: fp_pos,
            name: fp_name,
            type_: fp_type,
            flags: fp_flags,
            def_value: fp_def_value,
        } = param;
        let fp_type = on_type(env, fp_type);
        FunParam {
            pos: fp_pos,
            name: fp_name,
            type_: fp_type,
            flags: fp_flags,
            def_value: fp_def_value,
        }
    }

    pub(crate) fn on_capability<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        c: Capability,
    ) -> Capability {
        match c {
            Capability::CapDefaults(p) => Capability::CapDefaults(p),
            Capability::CapTy(ty) => {
                let ty = on_type(env, ty);
                Capability::CapTy(ty)
            }
        }
    }

    pub(crate) fn on_fun_implicit_params<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        p: FunImplicitParams,
    ) -> FunImplicitParams {
        let FunImplicitParams { capability } = p;
        let capability = on_capability(on_type, env, capability);
        FunImplicitParams { capability }
    }

    pub(crate) fn on_shape_field_type<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        _sfn: &TshapeFieldName,
        sft: ShapeFieldType,
    ) -> ShapeFieldType {
        let ShapeFieldType {
            optional: sft_optional,
            ty: sft_ty,
        } = sft;
        let sft_ty = on_type(env, sft_ty);
        ShapeFieldType {
            optional: sft_optional,
            ty: sft_ty,
        }
    }

    pub(crate) fn on_opt_type<Env>(
        on_type: OnType<'_, Env>,
        env: &mut Env,
        x: Option<Ty>,
    ) -> Option<Ty> {
        match x {
            None => None,
            Some(x) => {
                let x = on_type(env, x);
                Some(x)
            }
        }
    }
}

/// The methods of `shallow_type_mapper` that `deep_type_mapper` does not
/// override, except `on_tvar`.
///
/// Where these macros are used, `Ty`, `Ty_` and the other types of
/// `typing_defs_core` and `typing_defs_constraints`, `Reason`
/// (`Typing_reason.t`) and `Tprim` have to be in scope.
macro_rules! type_mapper_methods_common {
    ($env:ty) => {
        fn on_tnonnull(&mut self, env: &mut $env, r: Reason) -> Ty {
            mk((r, Ty_::Tnonnull))
        }

        fn on_tdynamic(&mut self, env: &mut $env, r: Reason, sv: Option<isize>) -> Ty {
            mk((r, Ty_::Tdynamic(sv)))
        }

        fn on_tany(&mut self, env: &mut $env, r: Reason) -> Ty {
            // Typing_defs.make_tany ()
            mk((r, Ty_::Tany(oxidized::tany_sentinel::TanySentinel)))
        }

        fn on_tprim(&mut self, env: &mut $env, r: Reason, p: Tprim) -> Ty {
            mk((r, Ty_::Tprim(p)))
        }

        fn on_neg_type(&mut self, env: &mut $env, r: Reason, p: TypePredicate) -> Ty {
            mk((r, Ty_::Tneg(p)))
        }

        fn on_tlabel(&mut self, env: &mut $env, r: Reason, name: String) -> Ty {
            mk((r, Ty_::Tlabel(name)))
        }

        fn on_tclass_ptr(&mut self, env: &mut $env, r: Reason, ty: Ty) -> Ty {
            mk((r, Ty_::TclassPtr(ty)))
        }

        fn on_reason(&mut self, env: &mut $env, r: Reason) -> Reason {
            r
        }

        fn on_type(&mut self, env: &mut $env, ty: Ty) -> Ty {
            let Ty(r, ty) = ty;
            let r = self.on_reason(env, r);
            match crate::typing_defs_core::unwrap_node(ty) {
                Ty_::Tvar(n) => self.on_tvar(env, r, n),
                Ty_::Tnonnull => self.on_tnonnull(env, r),
                Ty_::Tany(_) => self.on_tany(env, r),
                Ty_::Tprim(p) => self.on_tprim(env, r, p),
                Ty_::Ttuple(t) => self.on_ttuple(env, r, t),
                Ty_::Tunion(tyl) => self.on_tunion(env, r, tyl),
                Ty_::Tintersection(tyl) => self.on_tintersection(env, r, tyl),
                Ty_::Toption(ty) => self.on_toption(env, r, ty),
                Ty_::Tfun(fun_type) => self.on_tfun(env, r, std::rc::Rc::unwrap_or_clone(fun_type)),
                Ty_::Tgeneric(x) => self.on_tgeneric(env, r, x),
                Ty_::Tnewtype(x, tyl, ty) => self.on_tnewtype(env, r, x, tyl, ty),
                Ty_::Tdependent(x, ty) => self.on_tdependent(env, r, x, ty),
                Ty_::Tclass(x, e, tyl) => self.on_tclass(env, r, x, e, tyl),
                Ty_::Tdynamic(sv) => self.on_tdynamic(env, r, sv),
                Ty_::Tshape(s) => self.on_tshape(env, r, s),
                Ty_::TvecOrDict(ty1, ty2) => self.on_tvec_or_dict(env, r, ty1, ty2),
                Ty_::Taccess(TaccessType(ty, id)) => self.on_taccess(env, r, ty, id),
                Ty_::Tneg(ty) => self.on_neg_type(env, r, ty),
                Ty_::Tlabel(name) => self.on_tlabel(env, r, name),
                Ty_::TclassPtr(ty) => self.on_tclass_ptr(env, r, ty),
            }
        }

        fn on_locl_ty_list(&mut self, env: &mut $env, tyl: Vec<Ty>) -> Vec<Ty> {
            tyl.into_iter().map(|ty| self.on_type(env, ty)).collect()
        }
    };
}
pub(crate) use type_mapper_methods_common;

/// `shallow_type_mapper#on_tvar`
macro_rules! type_mapper_method_on_tvar {
    ($env:ty) => {
        fn on_tvar(&mut self, env: &mut $env, r: Reason, n: isize) -> Ty {
            mk((r, Ty_::Tvar(n)))
        }
    };
}

/// The methods of `shallow_type_mapper` that `deep_type_mapper` overrides.
macro_rules! type_mapper_methods_shallow {
    ($env:ty) => {
        fn on_ttuple(&mut self, env: &mut $env, r: Reason, t: TupleType) -> Ty {
            mk((r, Ty_::Ttuple(t)))
        }

        fn on_tunion(&mut self, env: &mut $env, r: Reason, tyl: Vec<Ty>) -> Ty {
            mk((r, Ty_::Tunion(tyl)))
        }

        fn on_tintersection(&mut self, env: &mut $env, r: Reason, tyl: Vec<Ty>) -> Ty {
            mk((r, Ty_::Tintersection(tyl)))
        }

        fn on_toption(&mut self, env: &mut $env, r: Reason, ty: Ty) -> Ty {
            mk((r, Ty_::Toption(ty)))
        }

        fn on_tfun(&mut self, env: &mut $env, r: Reason, fun_type: FunType) -> Ty {
            mk((r, Ty_::Tfun(std::rc::Rc::new(fun_type))))
        }

        fn on_tgeneric(&mut self, env: &mut $env, r: Reason, name: String) -> Ty {
            mk((r, Ty_::Tgeneric(name)))
        }

        fn on_tnewtype(
            &mut self,
            env: &mut $env,
            r: Reason,
            name: String,
            tyl: Vec<Ty>,
            ty: Ty,
        ) -> Ty {
            mk((r, Ty_::Tnewtype(name, tyl, ty)))
        }

        fn on_tdependent(&mut self, env: &mut $env, r: Reason, dep: DependentType, ty: Ty) -> Ty {
            mk((r, Ty_::Tdependent(dep, ty)))
        }

        fn on_tclass(&mut self, env: &mut $env, r: Reason, x: PosId, e: Exact, tyl: Vec<Ty>) -> Ty {
            mk((r, Ty_::Tclass(x, e, tyl)))
        }

        fn on_tshape(&mut self, env: &mut $env, r: Reason, shape_ty: ShapeType) -> Ty {
            match shape_ty {
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: shape_kind,
                    fields: fdm,
                }) => mk((
                    r,
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        // TODO(shapes) Should this reset the origin?
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: shape_kind,
                        fields: fdm,
                    })),
                )),
                ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                    let ss_elems = ss_elems
                        .into_iter()
                        .map(|ty| self.on_type(env, ty))
                        .collect();
                    mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })),
                    ))
                }
            }
        }

        fn on_tvec_or_dict(&mut self, env: &mut $env, r: Reason, ty1: Ty, ty2: Ty) -> Ty {
            mk((r, Ty_::TvecOrDict(ty1, ty2)))
        }

        fn on_taccess(&mut self, env: &mut $env, r: Reason, ty: Ty, id: PosId) -> Ty {
            mk((r, Ty_::Taccess(TaccessType(ty, id))))
        }
    };
}

/// The methods that `deep_type_mapper` overrides.
macro_rules! type_mapper_methods_deep {
    ($env:ty) => {
        fn on_tunion(&mut self, env: &mut $env, r: Reason, tyl: Vec<Ty>) -> Ty {
            let tyl = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
            mk((r, Ty_::Tunion(tyl)))
        }

        fn on_tintersection(&mut self, env: &mut $env, r: Reason, tyl: Vec<Ty>) -> Ty {
            let tyl = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
            mk((r, Ty_::Tintersection(tyl)))
        }

        fn on_ttuple(&mut self, env: &mut $env, r: Reason, t: TupleType) -> Ty {
            let TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            } = t;
            let t_required = self.on_locl_ty_list(env, t_required);
            let t_optional = self.on_locl_ty_list(env, t_optional);
            let t_extra = $crate::type_mapper_generic::private::on_tuple_extra(
                &mut |env, ty| self.on_type(env, ty),
                env,
                t_extra,
            );
            let t = TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            };
            mk((r, Ty_::Ttuple(t)))
        }

        fn on_toption(&mut self, env: &mut $env, r: Reason, ty: Ty) -> Ty {
            let ty = self.on_type(env, ty);
            mk((r, Ty_::Toption(ty)))
        }

        fn on_tfun(&mut self, env: &mut $env, r: Reason, ft: FunType) -> Ty {
            let FunType {
                tparams: ft_tparams,
                where_constraints: ft_where_constraints,
                params: ft_params,
                implicit_params: ft_implicit_params,
                ret: ft_ret,
                flags: ft_flags,
                instantiated: ft_instantiated,
            } = ft;
            let ft_tparams = ft_tparams
                .into_iter()
                .map(|tparam| {
                    $crate::type_mapper_generic::private::on_tparam(
                        &mut |env, ty| self.on_type(env, ty),
                        env,
                        tparam,
                    )
                })
                .collect();
            let ft_where_constraints = ft_where_constraints
                .into_iter()
                .map(|cstr| {
                    $crate::type_mapper_generic::private::on_where_constraint(
                        &mut |env, ty| self.on_type(env, ty),
                        env,
                        cstr,
                    )
                })
                .collect();
            let ft_params = ft_params
                .into_iter()
                .map(|param| {
                    $crate::type_mapper_generic::private::on_param(
                        &mut |env, ty| self.on_type(env, ty),
                        env,
                        param,
                    )
                })
                .collect();
            let ft_implicit_params = $crate::type_mapper_generic::private::on_fun_implicit_params(
                &mut |env, ty| self.on_type(env, ty),
                env,
                ft_implicit_params,
            );
            let ft_ret = self.on_type(env, ft_ret);
            let ft = FunType {
                tparams: ft_tparams,
                where_constraints: ft_where_constraints,
                params: ft_params,
                implicit_params: ft_implicit_params,
                ret: ft_ret,
                flags: ft_flags,
                instantiated: ft_instantiated,
            };
            mk((r, Ty_::Tfun(std::rc::Rc::new(ft))))
        }

        fn on_tnewtype(
            &mut self,
            env: &mut $env,
            r: Reason,
            x: String,
            tyl: Vec<Ty>,
            cstr: Ty,
        ) -> Ty {
            let tyl = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
            let cstr = self.on_type(env, cstr);
            mk((r, Ty_::Tnewtype(x, tyl, cstr)))
        }

        fn on_tdependent(&mut self, env: &mut $env, r: Reason, x: DependentType, cstr: Ty) -> Ty {
            let cstr = self.on_type(env, cstr);
            mk((r, Ty_::Tdependent(x, cstr)))
        }

        fn on_tclass(&mut self, env: &mut $env, r: Reason, x: PosId, e: Exact, tyl: Vec<Ty>) -> Ty {
            let tyl = self.on_locl_ty_list(env, tyl);
            mk((r, Ty_::Tclass(x, e, tyl)))
        }

        fn on_tshape(&mut self, env: &mut $env, r: Reason, sh: ShapeType) -> Ty {
            match sh {
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: s_origin,
                    unknown_value: s_unknown_value,
                    fields: s_fields,
                }) => {
                    let s_unknown_value = self.on_type(env, s_unknown_value);
                    let s_fields = t_shape_map::map_fields_env(
                        |env: &mut $env, sfn: &t_shape_map::Key, sft| {
                            $crate::type_mapper_generic::private::on_shape_field_type(
                                &mut |env, ty| self.on_type(env, ty),
                                env,
                                &sfn.0,
                                sft,
                            )
                        },
                        env,
                        s_fields,
                    );
                    let sh = ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: s_origin,
                        unknown_value: s_unknown_value,
                        fields: s_fields,
                    });
                    mk((r, Ty_::Tshape(sh)))
                }
                ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                    let ss_elems = ss_elems
                        .into_iter()
                        .map(|ty| self.on_type(env, ty))
                        .collect();
                    mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })),
                    ))
                }
            }
        }

        fn on_tvec_or_dict(&mut self, env: &mut $env, r: Reason, ty1: Ty, ty2: Ty) -> Ty {
            let ty1 = self.on_type(env, ty1);
            let ty2 = self.on_type(env, ty2);
            mk((r, Ty_::TvecOrDict(ty1, ty2)))
        }

        fn on_taccess(&mut self, env: &mut $env, r: Reason, ty: Ty, id: PosId) -> Ty {
            let ty = self.on_type(env, ty);
            mk((r, Ty_::Taccess(TaccessType(ty, id))))
        }

        fn on_tgeneric(&mut self, env: &mut $env, r: Reason, name: String) -> Ty {
            mk((r, Ty_::Tgeneric(name)))
        }
    };
}
pub(crate) use type_mapper_methods_deep;

/// The methods that `constraint_type_mapper` adds to `deep_type_mapper`.
macro_rules! type_mapper_methods_constraint {
    ($env:ty) => {
        fn on_constraint_type(&mut self, env: &mut $env, ty: ConstraintType) -> ConstraintType {
            let ConstraintType(r, ty) = ty;
            self.on_constraint_type_(env, r, std::rc::Rc::unwrap_or_clone(ty))
        }

        fn on_constraint_type_(
            &mut self,
            env: &mut $env,
            r: Reason,
            ty_: ConstraintType_,
        ) -> ConstraintType {
            match ty_ {
                ConstraintType_::ThasMember(hm) => self.on_Thas_member(env, r, hm),
                ConstraintType_::ThasTypeMember(htm) => self.on_Thas_type_member(env, r, htm),
                ConstraintType_::TcanIndex(ci) => self.on_Tcan_index(env, r, ci),
                ConstraintType_::TcanIndexAssign(cia) => self.on_Tcan_index_assign(env, r, cia),
                ConstraintType_::TcanTraverse(ct) => self.on_Tcan_traverse(env, r, ct),
                ConstraintType_::Tdestructure(tyl) => self.on_Tdestructure(env, r, tyl),
                ConstraintType_::TtypeSwitch {
                    predicate,
                    ty_true,
                    ty_false,
                } => self.on_Ttype_switch(env, r, predicate, ty_true, ty_false),
                ConstraintType_::ThasConst { name, ty } => self.on_Thas_const(env, r, name, ty),
            }
        }

        fn on_Thas_member(&mut self, env: &mut $env, r: Reason, hm: HasMember) -> ConstraintType {
            let HasMember {
                name: hm_name,
                type_: hm_type,
                class_id: hm_class_id,
                method: hm_method,
            } = hm;
            let hm_type = self.on_type(env, hm_type);
            let hm = HasMember {
                name: hm_name,
                type_: hm_type,
                class_id: hm_class_id,
                method: hm_method,
            };
            mk_constraint_type((r, ConstraintType_::ThasMember(hm)))
        }

        fn on_Thas_type_member(
            &mut self,
            env: &mut $env,
            r: Reason,
            htm: HasTypeMember,
        ) -> ConstraintType {
            let HasTypeMember {
                id: htm_id,
                lower: htm_lower,
                upper: htm_upper,
            } = htm;
            let htm_lower = self.on_type(env, htm_lower);
            let htm_upper = self.on_type(env, htm_upper);
            let htm = HasTypeMember {
                id: htm_id,
                lower: htm_lower,
                upper: htm_upper,
            };
            mk_constraint_type((r, ConstraintType_::ThasTypeMember(htm)))
        }

        fn on_Tcan_index(&mut self, env: &mut $env, r: Reason, ci: CanIndex) -> ConstraintType {
            let CanIndex {
                key: ci_key,
                val: ci_val,
                index_expr: ci_index_expr,
                access_kind: ci_access_kind,
                expr_pos: ci_expr_pos,
                array_pos: ci_array_pos,
                index_pos: ci_index_pos,
            } = ci;
            let ci_key = self.on_type(env, ci_key);
            let ci_val = self.on_type(env, ci_val);
            let ci = CanIndex {
                key: ci_key,
                val: ci_val,
                index_expr: ci_index_expr,
                access_kind: ci_access_kind,
                expr_pos: ci_expr_pos,
                array_pos: ci_array_pos,
                index_pos: ci_index_pos,
            };
            mk_constraint_type((r, ConstraintType_::TcanIndex(ci)))
        }

        fn on_Tcan_index_assign(
            &mut self,
            env: &mut $env,
            r: Reason,
            cia: CanIndexAssign,
        ) -> ConstraintType {
            let CanIndexAssign {
                key: cia_key,
                write: cia_write,
                val: cia_val,
                index_expr: cia_index_expr,
                expr_pos: cia_expr_pos,
                array_pos: cia_array_pos,
                index_pos: cia_index_pos,
                write_pos: cia_write_pos,
            } = cia;
            let cia_key = self.on_type(env, cia_key);
            let cia_write = self.on_type(env, cia_write);
            let cia_val = self.on_type(env, cia_val);
            let cia = CanIndexAssign {
                key: cia_key,
                write: cia_write,
                val: cia_val,
                index_expr: cia_index_expr,
                expr_pos: cia_expr_pos,
                array_pos: cia_array_pos,
                index_pos: cia_index_pos,
                write_pos: cia_write_pos,
            };
            mk_constraint_type((r, ConstraintType_::TcanIndexAssign(cia)))
        }

        fn on_Tcan_traverse(
            &mut self,
            env: &mut $env,
            r: Reason,
            ct: CanTraverse,
        ) -> ConstraintType {
            let CanTraverse {
                key: ct_key,
                val: ct_val,
                is_await: ct_is_await,
                reason: ct_reason,
            } = ct;
            let ct_key = $crate::type_mapper_generic::private::on_opt_type(
                &mut |env, ty| self.on_type(env, ty),
                env,
                ct_key,
            );
            let ct_val = self.on_type(env, ct_val);
            let ct = CanTraverse {
                key: ct_key,
                val: ct_val,
                is_await: ct_is_await,
                reason: ct_reason,
            };
            mk_constraint_type((r, ConstraintType_::TcanTraverse(ct)))
        }

        fn on_Tdestructure(&mut self, env: &mut $env, r: Reason, d: Destructure) -> ConstraintType {
            let Destructure {
                required: d_required,
                optional: d_optional,
                variadic: d_variadic,
                kind: d_kind,
            } = d;
            let d_required = self.on_locl_ty_list(env, d_required);
            let d_optional = self.on_locl_ty_list(env, d_optional);
            let d_variadic = $crate::type_mapper_generic::private::on_opt_type(
                &mut |env, ty| self.on_type(env, ty),
                env,
                d_variadic,
            );
            mk_constraint_type((
                r,
                ConstraintType_::Tdestructure(Destructure {
                    required: d_required,
                    optional: d_optional,
                    variadic: d_variadic,
                    kind: d_kind,
                }),
            ))
        }

        fn on_Ttype_switch(
            &mut self,
            env: &mut $env,
            r: Reason,
            predicate: TypePredicate,
            lty_true: Ty,
            lty_false: Ty,
        ) -> ConstraintType {
            let ty_true = self.on_type(env, lty_true);
            let ty_false = self.on_type(env, lty_false);
            mk_constraint_type((
                r,
                ConstraintType_::TtypeSwitch {
                    predicate,
                    ty_true,
                    ty_false,
                },
            ))
        }

        fn on_Thas_const(
            &mut self,
            env: &mut $env,
            r: Reason,
            name: String,
            ty: Ty,
        ) -> ConstraintType {
            let ty = self.on_type(env, ty);
            mk_constraint_type((r, ConstraintType_::ThasConst { name, ty }))
        }
    };
}

/// The methods that `internal_type_mapper` adds to `constraint_type_mapper`.
macro_rules! type_mapper_methods_internal {
    ($env:ty) => {
        fn on_internal_type(&mut self, env: &mut $env, ty: InternalType) -> InternalType {
            match ty {
                InternalType::LoclType(ty) => self.on_LoclType(env, ty),
                InternalType::ConstraintType(ty) => self.on_ConstraintType(env, ty),
            }
        }

        fn on_LoclType(&mut self, env: &mut $env, ty: Ty) -> InternalType {
            let ty = self.on_type(env, ty);
            InternalType::LoclType(ty)
        }

        fn on_ConstraintType(&mut self, env: &mut $env, ty: ConstraintType) -> InternalType {
            let ty = self.on_constraint_type(env, ty);
            InternalType::ConstraintType(ty)
        }
    };
}

/// Base type mapper implementation that doesn't recursively go into the
/// types.
#[allow(unused_variables)]
pub trait ShallowTypeMapper<Env> {
    type_mapper_methods_common!(Env);
    type_mapper_method_on_tvar!(Env);
    type_mapper_methods_shallow!(Env);
}

/// Implementation of type_mapper that recursively visits everything in the
/// type.
/// NOTE: by default it doesn't to anything to Tvars. Include one of the mixins
/// below to specify how you want to treat type variables.
#[allow(unused_variables)]
pub trait DeepTypeMapper<Env> {
    type_mapper_methods_common!(Env);
    type_mapper_method_on_tvar!(Env);
    type_mapper_methods_deep!(Env);
}

#[allow(unused_variables, non_snake_case)]
pub trait ConstraintTypeMapper<Env> {
    type_mapper_methods_common!(Env);
    type_mapper_method_on_tvar!(Env);
    type_mapper_methods_deep!(Env);
    type_mapper_methods_constraint!(Env);
}

#[allow(unused_variables, non_snake_case)]
pub trait InternalTypeMapper<Env> {
    type_mapper_methods_common!(Env);
    type_mapper_method_on_tvar!(Env);
    type_mapper_methods_deep!(Env);
    type_mapper_methods_constraint!(Env);
    type_mapper_methods_internal!(Env);
}

#[cfg(test)]
mod tests {
    use oxidized::pos::Pos;

    use super::*;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn prim(p: Tprim) -> Ty {
        mk((r(), Ty_::Tprim(p)))
    }

    fn var(n: isize) -> Ty {
        mk((r(), Ty_::Tvar(n)))
    }

    fn class(tyl: Vec<Ty>) -> Ty {
        mk((
            r(),
            Ty_::Tclass((Pos::NONE, "\\C".to_string()), nonexact(), tyl),
        ))
    }

    fn fun_type(params: Vec<Ty>, ret: Ty) -> FunType {
        FunType {
            tparams: vec![Tparam {
                variance: oxidized::ast_defs::Variance::Invariant,
                name: (Pos::NONE, "T".to_string()),
                constraints: vec![(oxidized::ast_defs::ConstraintKind::ConstraintAs, var(10))],
                reified: oxidized::ast_defs::ReifyKind::Erased,
                user_attributes: vec![],
            }],
            where_constraints: vec![WhereConstraint(
                var(11),
                oxidized::ast_defs::ConstraintKind::ConstraintEq,
                var(12),
            )],
            params: params
                .into_iter()
                .map(|type_| FunParam {
                    pos: Pos::NONE,
                    name: None,
                    type_,
                    flags: oxidized::typing_defs_flags::FunParamFlags::empty(),
                    def_value: None,
                })
                .collect(),
            implicit_params: FunImplicitParams {
                capability: Capability::CapTy(var(14)),
            },
            ret,
            flags: oxidized::typing_defs_flags::FunTypeFlags::empty(),
            instantiated: true,
        }
    }

    /// The environment records the type variables in the order they are seen.
    type Env = Vec<isize>;

    /// Replaces type variables by int.
    struct Shallow;
    impl ShallowTypeMapper<Env> for Shallow {
        fn on_tvar(&mut self, env: &mut Env, r: Reason, n: isize) -> Ty {
            env.push(n);
            mk((r, Ty_::Tprim(Tprim::Tint)))
        }
    }

    struct Deep;
    impl DeepTypeMapper<Env> for Deep {
        fn on_tvar(&mut self, env: &mut Env, r: Reason, n: isize) -> Ty {
            env.push(n);
            mk((r, Ty_::Tprim(Tprim::Tint)))
        }
    }

    struct Internal;
    impl InternalTypeMapper<Env> for Internal {
        fn on_tvar(&mut self, env: &mut Env, r: Reason, n: isize) -> Ty {
            env.push(n);
            mk((r, Ty_::Tprim(Tprim::Tint)))
        }
    }

    fn has_var(ty: &Ty) -> bool {
        find_locl_ty(ty, &|ty| get_var(ty).is_some()).is_some()
    }

    #[test]
    fn shallow_does_not_go_into_types() {
        let mut env = Env::new();
        let ty = Shallow.on_type(&mut env, var(1));
        assert!(matches!(get_node(&ty), Ty_::Tprim(Tprim::Tint)));
        let ty = Shallow.on_type(&mut env, class(vec![var(2)]));
        assert!(has_var(&ty));
        let ty = Shallow.on_type(&mut env, mk((r(), Ty_::Toption(var(3)))));
        assert!(has_var(&ty));
        assert_eq!(env, vec![1]);
        // ... except into the elements of a shape splat
        let splat = mk((
            r(),
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat {
                ss_elems: vec![var(4), var(5)],
            })),
        ));
        let ty = Shallow.on_type(&mut env, splat);
        assert!(!has_var(&ty));
        assert_eq!(env, vec![1, 4, 5]);
        let tyl = Shallow.on_locl_ty_list(&mut env, vec![var(6), prim(Tprim::Tfloat)]);
        assert!(matches!(get_node(&tyl[0]), Ty_::Tprim(Tprim::Tint)));
        assert!(matches!(get_node(&tyl[1]), Ty_::Tprim(Tprim::Tfloat)));
    }

    #[test]
    fn deep_goes_into_types_in_order() {
        let mut env = Env::new();
        let tuple = mk((
            r(),
            Ty_::Ttuple(TupleType {
                required: vec![var(1)],
                optional: vec![var(2)],
                extra: TupleExtra::Tvariadic(var(3)),
            }),
        ));
        let newtype = mk((r(), Ty_::Tnewtype("\\N".to_string(), vec![var(4)], var(5))));
        let ty = class(vec![
            tuple,
            newtype,
            mk((r(), Ty_::Tunion(vec![var(6), var(7)]))),
            mk((r(), Ty_::TvecOrDict(var(8), var(9)))),
        ]);
        let ty = Deep.on_type(&mut env, ty);
        assert!(!has_var(&ty));
        assert_eq!(env, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);

        // functions: type parameters, where constraints, parameters, capability, return type
        let mut env = Env::new();
        let ft = fun_type(vec![var(13)], var(15));
        let ty = Deep.on_type(&mut env, mk((r(), Ty_::Tfun(std::rc::Rc::new(ft)))));
        assert!(!has_var(&ty));
        assert_eq!(env, vec![10, 11, 12, 13, 14, 15]);
    }

    #[test]
    fn deep_leaves_some_types_alone() {
        // As in OCaml, deep_type_mapper does not override on_tclass_ptr, and
        // does not look into the refinement of a class.
        let mut env = Env::new();
        let ty = Deep.on_type(&mut env, mk((r(), Ty_::TclassPtr(var(1)))));
        assert!(has_var(&ty));
        let mut cr_consts = oxidized::s_map::SMap::new();
        cr_consts.insert(
            "T".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRexact(var(2)),
                is_ctx: false,
            },
        );
        let ty = mk((
            r(),
            Ty_::Tclass(
                (Pos::NONE, "\\C".to_string()),
                Exact::Nonexact(ClassRefinement {
                    cr_consts: cr_consts.into(),
                }),
                vec![],
            ),
        ));
        let ty = Deep.on_type(&mut env, ty);
        assert!(has_var(&ty));
        assert!(env.is_empty());
    }

    #[test]
    fn shapes_and_origins() {
        use oxidized::typing_defs_core::PosByteString;
        let field = |s: &str| {
            t_shape_map::TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
                Pos::NONE,
                s.into(),
            )))
        };
        let shape = || {
            let mut fields = t_shape_map::T::new();
            fields.insert(
                field("b"),
                ShapeFieldType {
                    optional: true,
                    ty: var(3),
                },
            );
            fields.insert(
                field("a"),
                ShapeFieldType {
                    optional: false,
                    ty: var(2),
                },
            );
            mk((
                r(),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: TypeOrigin::FromAlias("\\A".to_string(), None),
                    unknown_value: var(1),
                    fields,
                })),
            ))
        };
        let origin = |ty: &Ty| match get_node(ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => s.origin.clone(),
            _ => panic!(),
        };
        // the shallow mapper resets the origin and does not map the fields
        let mut env = Env::new();
        let ty = Shallow.on_type(&mut env, shape());
        assert_eq!(origin(&ty), TypeOrigin::MissingOrigin);
        assert!(has_var(&ty) && env.is_empty());
        // the deep mapper keeps the origin, and maps the unknown fields' type
        // and then the fields in the order of their names
        let ty = Deep.on_type(&mut env, shape());
        assert_eq!(origin(&ty), TypeOrigin::FromAlias("\\A".to_string(), None));
        assert!(!has_var(&ty));
        assert_eq!(env, vec![1, 2, 3]);
        match get_node(&ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
                assert!(s.fields[&field("b")].optional && !s.fields[&field("a")].optional)
            }
            _ => panic!(),
        }
    }

    #[test]
    fn constraint_and_internal_types() {
        let mut env = Env::new();
        let d = mk_constraint_type((
            r(),
            ConstraintType_::Tdestructure(Destructure {
                required: vec![var(1)],
                optional: vec![var(2)],
                variadic: Some(var(3)),
                kind: DestructureKind::SplatUnpack,
            }),
        ));
        let d = Internal.on_internal_type(&mut env, InternalType::ConstraintType(d));
        assert_eq!(env, vec![1, 2, 3]);
        match d {
            InternalType::ConstraintType(ConstraintType(_, c)) => match std::rc::Rc::unwrap_or_clone(c) {
                ConstraintType_::Tdestructure(Destructure {
                    required,
                    optional,
                    variadic,
                    kind,
                }) => {
                    assert!(!has_var(&required[0]) && !has_var(&optional[0]));
                    assert!(!has_var(&variadic.unwrap()));
                    assert_eq!(kind, DestructureKind::SplatUnpack);
                }
                _ => panic!(),
            },
            _ => panic!(),
        }
        let mut env = Env::new();
        let s = mk_constraint_type((
            r(),
            ConstraintType_::TtypeSwitch {
                predicate: TypePredicate(r(), TypePredicate_::IsTag(TypeTag::IntTag)),
                ty_true: var(1),
                ty_false: var(2),
            },
        ));
        let s = Internal.on_constraint_type(&mut env, s);
        assert_eq!(env, vec![1, 2]);
        assert!(matches!(
            &*s.1,
            ConstraintType_::TtypeSwitch { ty_true, ty_false, .. } if !has_var(ty_true) && !has_var(ty_false)
        ));
        let mut env = Env::new();
        let l = Internal.on_internal_type(&mut env, InternalType::LoclType(class(vec![var(7)])));
        assert!(matches!(&l, InternalType::LoclType(ty) if !has_var(ty)));
        assert_eq!(env, vec![7]);
        assert_eq!(fresh_env(3), 3);
    }
}
