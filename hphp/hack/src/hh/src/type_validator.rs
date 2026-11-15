// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/type_validator.ml`. See `hh/PORTING.md`.
//!
//! # The class
//!
//! `class virtual type_validator`, which inherits
//! `Type_visitor.decl_type_visitor`, is the trait [`TypeValidator`]. As in
//! `type_mapper_generic.rs`, the trait has *all* the methods of the class,
//! the inherited ones included (a Rust trait cannot override the default
//! method of a supertrait, which is what `method!` does), so it does not
//! build on `crate::type_visitor::DeclTypeVisitor`: its default methods are
//! those of `decl_type_visitor`, except the ones `type_validator` overrides
//! (`on_tapply`, `on_taccess`), and the methods `type_validator` adds.
//!
//! A validator (an OCaml object that inherits `type_validator`) is a type that
//! implements the trait and overrides methods by defining them. The bodies of
//! the default methods are the functions of [`inherited`], so that an
//! overriding method can call the method it overrides: `super#on_tapply acc r
//! id tyl` is `inherited::on_tapply(self, acc, r, id, tyl)`.
//!
//! The objects of the OCaml have no instance variables, so the methods take
//! `&self`. The accumulator (`validation_state`) is taken and returned by
//! value; types and reasons are borrowed.
//!
//! # Types
//!
//! The reasons of the validity are those of declared types (`Reason.decl_t`:
//! `crate::ctx::R`). The `error_emitter` receives what `validate_type`
//! computes as `(Pos_or_decl.t * string) list Lazy.t`, which is the type of the
//! fields of the typing errors that report it (`Pos_or_decl.t Message.t list
//! Lazy.t`): `typing_error::Lazy<Vec<Message<PosOrDecl>>>`. It is any
//! `FnMut` (see [`ErrorEmitter`] for the type of the OCaml).

use oxidized::aast;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::Positioned;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl::ty as d;

use crate::class_refinement;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_hint;
use crate::decl_instantiate;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::type_expansions;
use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_phase;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_utils;

/// The position type of declarations.
type DeclPos = <R as ty::reason::Reason>::Pos;

/// `validity` (abstract in the `.mli`)
#[derive(Clone, Debug)]
pub enum Validity {
    Valid,
    Invalid(Vec<(R, String)>),
}

/// `reification`: in hint positions, reified types are not resolved
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reification {
    /// Cases like intrinsics where we're not storing back the generic
    TypeStructure,
    Resolved,
    Unresolved,
}

/// `validation_state`
#[derive(Clone)]
pub struct ValidationState {
    pub env: Env,
    pub ety_env: ExpandEnv,
    pub validity: Validity,
    pub inside_reified_class_generic_position: bool,
    pub reification: Reification,
    pub expanded_typedefs: im::OrdSet<String>,
    /// `Some Klass` if we're traversing a type and have gone through
    /// `Klass::TheTy`.
    pub class_from_taccess_lhs: Option<cls::T>,
}

/// `error_emitter`: `Pos.t -> (Pos_or_decl.t * string) list Lazy.t -> unit`.
///
/// `validate_type` and `validate_hint` take any `FnMut` of this type (a
/// closure, or a `&mut ErrorEmitter`).
pub type ErrorEmitter<'a> =
    dyn FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>) + 'a;

/// `Typing_reason.to_pos` of the reason of a declared type.
fn decl_reason_to_pos(r: &R) -> PosOrDecl {
    decl_utils::reason_to_pos(r).to_oxidized()
}

/// `class virtual type_validator` (with the methods it inherits from
/// `Type_visitor.decl_type_visitor`, in the order of that class).
pub trait TypeValidator {
    // -- Type_visitor.decl_type_visitor -------------------------------------

    fn on_tany(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_tany(self, acc, r)
    }

    fn on_tmixed(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_tmixed(self, acc, r)
    }

    fn on_twildcard(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_twildcard(self, acc, r)
    }

    fn on_tnonnull(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_tnonnull(self, acc, r)
    }

    fn on_tdynamic(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_tdynamic(self, acc, r)
    }

    fn on_tthis(&self, acc: ValidationState, r: &R) -> ValidationState {
        inherited::on_tthis(self, acc, r)
    }

    fn on_tvec_or_dict(
        &self,
        acc: ValidationState,
        r: &R,
        ty1: &DeclTy,
        ty2: &DeclTy,
    ) -> ValidationState {
        inherited::on_tvec_or_dict(self, acc, r, ty1, ty2)
    }

    fn on_tgeneric(&self, acc: ValidationState, r: &R, name: &str) -> ValidationState {
        inherited::on_tgeneric(self, acc, r, name)
    }

    fn on_toption(&self, acc: ValidationState, r: &R, ty: &DeclTy) -> ValidationState {
        inherited::on_toption(self, acc, r, ty)
    }

    fn on_tlike(&self, acc: ValidationState, r: &R, ty: &DeclTy) -> ValidationState {
        inherited::on_tlike(self, acc, r, ty)
    }

    fn on_tprim(&self, acc: ValidationState, r: &R, prim: Tprim) -> ValidationState {
        inherited::on_tprim(self, acc, r, prim)
    }

    fn on_tvar(&self, acc: ValidationState, r: &R, v: isize) -> ValidationState {
        inherited::on_tvar(self, acc, r, v)
    }

    fn on_tfun(&self, acc: ValidationState, r: &R, ft: &DeclFunType) -> ValidationState {
        inherited::on_tfun(self, acc, r, ft)
    }

    fn on_trefinement(
        &self,
        acc: ValidationState,
        r: &R,
        ty: &DeclTy,
        rs: &DeclClassRefinement,
    ) -> ValidationState {
        inherited::on_trefinement(self, acc, r, ty, rs)
    }

    fn on_ttuple(&self, acc: ValidationState, r: &R, t: &d::TupleType<R>) -> ValidationState {
        inherited::on_ttuple(self, acc, r, t)
    }

    fn on_tuple_extra(&self, acc: ValidationState, e: &d::TupleExtra<R>) -> ValidationState {
        inherited::on_tuple_extra(self, acc, e)
    }

    fn on_tunion(&self, acc: ValidationState, r: &R, tyl: &[DeclTy]) -> ValidationState {
        inherited::on_tunion(self, acc, r, tyl)
    }

    fn on_tintersection(&self, acc: ValidationState, r: &R, tyl: &[DeclTy]) -> ValidationState {
        inherited::on_tintersection(self, acc, r, tyl)
    }

    fn on_tshape(&self, acc: ValidationState, r: &R, shape_ty: &d::ShapeType<R>) -> ValidationState {
        inherited::on_tshape(self, acc, r, shape_ty)
    }

    fn on_tclass_ptr(&self, acc: ValidationState, r: &R, ty: &DeclTy) -> ValidationState {
        inherited::on_tclass_ptr(self, acc, r, ty)
    }

    fn on_type(&self, acc: ValidationState, ty: &DeclTy) -> ValidationState {
        inherited::on_type(self, acc, ty)
    }

    // -- type_validator -----------------------------------------------------

    fn on_enum(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
    ) -> ValidationState {
        inherited::on_enum(self, acc, r, id)
    }

    fn on_class(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        inherited::on_class(self, acc, r, id, tyl)
    }

    fn on_newtype(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
        as_cstr: &DeclTy,
        super_cstr: &DeclTy,
        ty: &DeclTy,
    ) -> ValidationState {
        inherited::on_newtype(self, acc, r, id, tyl, as_cstr, super_cstr, ty)
    }

    fn on_alias(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
        ty: &DeclTy,
    ) -> ValidationState {
        inherited::on_alias(self, acc, r, id, tyl, ty)
    }

    fn on_typeconst(
        &self,
        acc: ValidationState,
        class_: &cls::T,
        typeconst: &TypeconstType,
    ) -> ValidationState {
        inherited::on_typeconst(self, acc, class_, typeconst)
    }

    fn on_taccess(
        &self,
        acc: ValidationState,
        r: &R,
        ta: &d::TaccessType<R, DeclTy>,
    ) -> ValidationState {
        inherited::on_taccess(self, acc, r, ta)
    }

    fn on_tapply(
        &self,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        inherited::on_tapply(self, acc, r, id, tyl)
    }

    /// Use_pos is the primary error position
    fn validate_type(
        &self,
        env: &Env,
        use_pos: Pos,
        root_ty: &DeclTy,
        reification: Option<Reification>,
        emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
    ) where
        Self: Sized,
    {
        inherited::validate_type(self, env, use_pos, root_ty, reification, emit_error)
    }

    fn validate_hint(
        &self,
        env: &Env,
        hint: &aast::Hint,
        reification: Option<Reification>,
        emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
    ) where
        Self: Sized,
    {
        inherited::validate_hint(self, env, hint, reification, emit_error)
    }

    /// Takes in and accumulates a list of reasons
    fn invalid_list(&self, state: ValidationState, reasons: Vec<(R, String)>) -> ValidationState {
        inherited::invalid_list(self, state, reasons)
    }

    fn invalid(&self, state: ValidationState, r: &R, msg: &str) -> ValidationState {
        inherited::invalid(self, state, r, msg)
    }
}

/// The methods of `type_validator` (and those it inherits from
/// `Type_visitor.decl_type_visitor`), as functions of the object `this`:
/// `super#m` in a class that inherits `type_validator` is `inherited::m(self,
/// ...)`. `this#m` in them dispatches to the methods of `this`, the overriding
/// ones included.
#[allow(unused_variables)]
pub mod inherited {
    use super::*;

    // -- Type_visitor.decl_type_visitor -------------------------------------

    pub fn on_tany<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_tmixed<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_twildcard<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_tnonnull<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_tdynamic<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_tthis<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
    ) -> ValidationState {
        acc
    }

    pub fn on_tvec_or_dict<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ty1: &DeclTy,
        ty2: &DeclTy,
    ) -> ValidationState {
        let acc = this.on_type(acc, ty1);
        this.on_type(acc, ty2)
    }

    pub fn on_tgeneric<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        name: &str,
    ) -> ValidationState {
        acc
    }

    pub fn on_toption<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ty: &DeclTy,
    ) -> ValidationState {
        this.on_type(acc, ty)
    }

    pub fn on_tlike<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ty: &DeclTy,
    ) -> ValidationState {
        this.on_type(acc, ty)
    }

    pub fn on_tprim<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        prim: Tprim,
    ) -> ValidationState {
        acc
    }

    pub fn on_tvar<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        v: isize,
    ) -> ValidationState {
        acc
    }

    pub fn on_tfun<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ft: &DeclFunType,
    ) -> ValidationState {
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
            acc = this.on_type(acc, &x.ty);
        }
        for t in ft_tparams.iter() {
            for (_, ty) in t.constraints.iter() {
                acc = this.on_type(acc, ty);
            }
        }
        let mut acc = match &ft_implicit_params.capability {
            d::Capability::CapDefaults(_) => acc,
            d::Capability::CapTy(ty) => this.on_type(acc, ty),
        };
        for d::WhereConstraint(ty1, _ck, ty2) in ft_where_constraints.iter() {
            acc = this.on_type(acc, ty1);
            acc = this.on_type(acc, ty2);
        }
        this.on_type(acc, ft_ret)
    }

    /// The `on_tapply` of `decl_type_visitor` (which `type_validator`
    /// overrides: see [`on_tapply`]).
    pub fn decl_type_visitor_on_tapply<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_trefinement<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ty: &DeclTy,
        rs: &DeclClassRefinement,
    ) -> ValidationState {
        let acc = this.on_type(acc, ty);
        // `Class_refinement.fold rs ~init:acc ~f:this#on_type` (the map of
        // `hackrs` is ordered by name, like the `S_map` of the OCaml)
        class_refinement::fold_decl(rs, acc, |acc, ty| this.on_type(acc, ty))
    }

    /// The `on_taccess` of `decl_type_visitor` (which `type_validator`
    /// overrides: see [`on_taccess`]).
    pub fn decl_type_visitor_on_taccess<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ta: &d::TaccessType<R, DeclTy>,
    ) -> ValidationState {
        this.on_type(acc, &ta.ty)
    }

    pub fn on_ttuple<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        t: &d::TupleType<R>,
    ) -> ValidationState {
        let d::TupleType(t_required, t_optional, t_extra) = t;
        let acc = this.on_tuple_extra(acc, t_extra);
        let acc = t_optional.iter().fold(acc, |acc, ty| this.on_type(acc, ty));
        t_required.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_tuple_extra<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        e: &d::TupleExtra<R>,
    ) -> ValidationState {
        match e {
            d::TupleExtra::Tsplat(t_splat) => this.on_type(acc, t_splat),
            d::TupleExtra::Tvariadic(t_variadic) => this.on_type(acc, t_variadic),
        }
    }

    pub fn on_tunion<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        tyl: &[DeclTy],
    ) -> ValidationState {
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_tintersection<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        tyl: &[DeclTy],
    ) -> ValidationState {
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_tshape<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        shape_ty: &d::ShapeType<R>,
    ) -> ValidationState {
        match shape_ty {
            d::ShapeType::Simple(d::ShapeTypeSimple(kind, fdm)) => {
                let acc = this.on_type(acc, kind);
                // TShapeMap.fold: in the order of the names of the fields
                let mut fdm: Vec<_> = fdm.iter().collect();
                fdm.sort_by(|a, b| decl_tshape_field_name_compare(a.0, b.0));
                fdm.into_iter()
                    .fold(acc, |acc, (_, sft)| this.on_type(acc, &sft.ty))
            }
            d::ShapeType::Splat(ss_elems) => {
                ss_elems.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
            }
        }
    }

    pub fn on_tclass_ptr<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ty: &DeclTy,
    ) -> ValidationState {
        this.on_type(acc, ty)
    }

    pub fn on_type<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        ty: &DeclTy,
    ) -> ValidationState {
        let r = ty.reason();
        match ty.node_ref() {
            d::Ty_::Tany => this.on_tany(acc, r),
            d::Ty_::Tmixed => this.on_tmixed(acc, r),
            d::Ty_::Twildcard => this.on_twildcard(acc, r),
            d::Ty_::Tnonnull => this.on_tnonnull(acc, r),
            d::Ty_::Tdynamic => this.on_tdynamic(acc, r),
            d::Ty_::Tthis => this.on_tthis(acc, r),
            d::Ty_::TvecOrDict(kv) => this.on_tvec_or_dict(acc, r, &kv.0, &kv.1),
            d::Ty_::Tgeneric(s) => this.on_tgeneric(acc, r, s.as_str()),
            d::Ty_::Toption(ty) => this.on_toption(acc, r, ty),
            d::Ty_::Tlike(ty) => this.on_tlike(acc, r, ty),
            d::Ty_::Tprim(prim) => this.on_tprim(acc, r, *prim),
            d::Ty_::Tfun(fty) => this.on_tfun(acc, r, fty),
            d::Ty_::Tapply(s_and_tyl) => this.on_tapply(acc, r, &s_and_tyl.0, &s_and_tyl.1),
            d::Ty_::Trefinement(tr) => this.on_trefinement(acc, r, &tr.ty, &tr.refinement),
            d::Ty_::Taccess(aty) => this.on_taccess(acc, r, aty),
            d::Ty_::Ttuple(t) => this.on_ttuple(acc, r, t),
            d::Ty_::Tunion(tyl) => this.on_tunion(acc, r, tyl),
            d::Ty_::Tintersection(tyl) => this.on_tintersection(acc, r, tyl),
            d::Ty_::Tshape(s) => this.on_tshape(acc, r, s),
            d::Ty_::TclassPtr(ty) => this.on_tclass_ptr(acc, r, ty),
        }
    }

    // -- type_validator -----------------------------------------------------

    pub fn on_enum<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
    ) -> ValidationState {
        acc
    }

    pub fn on_class<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_newtype<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
        as_cstr: &DeclTy,
        super_cstr: &DeclTy,
        ty: &DeclTy,
    ) -> ValidationState {
        // List.fold_left (ty :: as_cstr :: super_cstr :: tyl)
        let acc = this.on_type(acc, ty);
        let acc = this.on_type(acc, as_cstr);
        let acc = this.on_type(acc, super_cstr);
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_alias<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
        ty: &DeclTy,
    ) -> ValidationState {
        // List.fold_left (ty :: tyl)
        let acc = this.on_type(acc, ty);
        tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty))
    }

    pub fn on_typeconst<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        class_: &cls::T,
        typeconst: &TypeconstType,
    ) -> ValidationState {
        match &typeconst.kind {
            Typeconst::TCConcrete(ConcreteTypeconst { ty: tc_type }) => this.on_type(acc, tc_type),
            Typeconst::TCAbstract(AbstractTypeconst {
                as_constraint: atc_as_constraint,
                super_constraint: atc_super_constraint,
                default: atc_default,
            }) => {
                let acc = atc_as_constraint
                    .iter()
                    .fold(acc, |acc, ty| this.on_type(acc, ty));
                let acc = atc_super_constraint
                    .iter()
                    .fold(acc, |acc, ty| this.on_type(acc, ty));
                let acc = atc_default.iter().fold(acc, |acc, ty| this.on_type(acc, ty));
                acc
            }
        }
    }

    pub fn on_taccess<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        ta: &d::TaccessType<R, DeclTy>,
    ) -> ValidationState {
        let d::TaccessType {
            ty: root,
            type_const: id,
        } = ta;
        // The environment that localization returns is used below, but never
        // stored in the state.
        let mut env = acc.env.clone();
        let (ty_err_opt, root) = typing_phase::localize(&acc.ety_env, &mut env, root);
        if let Some(err) = &ty_err_opt {
            typing_error_utils::add_typing_error(err, &env)
        }
        let tyl = typing_utils::get_concrete_supertypes(None, None, None, true, &mut env, root);
        let mut acc = acc;
        for ty in tyl {
            // The fold does not thread the environment: each type is expanded
            // in the environment `get_concrete_supertypes` returned.
            let mut env = env.clone();
            let ty = env::expand_type(&mut env, ty);
            acc = match get_node(&ty) {
                Ty_::Tclass((_, receiver_name), _, _) => {
                    // Env.get_class env receiver_name |> Decl_entry.to_option
                    // >>= fun class_ -> ... Typing_env.get_typeconst ...
                    let found = decl_entry::to_option(env::get_class(&env, receiver_name))
                        .and_then(|class_| {
                            let type_const_name = id.id_ref().as_str();
                            env::get_typeconst(&env, &class_, type_const_name)
                                .map(|typeconst| (class_, typeconst))
                        });
                    match found {
                        None => acc,
                        Some((class_, typeconst)) => {
                            let id_pos: PosOrDecl = id.pos().clone().to_oxidized();
                            let type_const_name = id.id_ref().as_str().to_string();
                            match add_type_expansion_check_cycles(
                                &ExpandEnv {
                                    this_ty: ty.clone(),
                                    ..acc.ety_env.clone()
                                },
                                type_expansions::Expansion {
                                    name: type_expansions::expandable::T::TypeConstant {
                                        receiver_name: receiver_name.clone(),
                                        type_const_name,
                                    },
                                    use_pos: id_pos,
                                    def_pos: None,
                                },
                            ) {
                                Err(_) => {
                                    // This type is cyclic, give up checking it. We've
                                    // already reported an error.
                                    acc
                                }
                                Ok(ety_env) => {
                                    // stash and restore `class_from_taccess_lhs`
                                    let class_from_taccess_lhs = acc.class_from_taccess_lhs.clone();
                                    let acc = this.on_typeconst(
                                        ValidationState {
                                            ety_env,
                                            class_from_taccess_lhs: Some(class_.clone()),
                                            ..acc
                                        },
                                        &class_,
                                        &typeconst,
                                    );
                                    ValidationState {
                                        class_from_taccess_lhs,
                                        ..acc
                                    }
                                }
                            }
                        }
                    }
                }
                _ => acc,
            }
        }
        acc
    }

    pub fn on_tapply<V: TypeValidator + ?Sized>(
        this: &V,
        acc: ValidationState,
        r: &R,
        id: &Positioned<TypeName, DeclPos>,
        tyl: &[DeclTy],
    ) -> ValidationState {
        let name = id.id_ref().as_str();
        if env::is_enum(&acc.env, name) && tyl.is_empty() {
            this.on_enum(acc, r, id)
        } else {
            match env::get_class_or_typedef(&acc.env, name) {
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(td)) => {
                    let d::TypedefType {
                        pos: _,
                        module: _,
                        tparams: td_tparams,
                        type_assignment: td_type_assignment,
                        as_constraint: td_as_constraint,
                        super_constraint: td_super_constraint,
                        is_ctx: _,
                        attributes: _,
                        internal: _,
                        docs_url: _,
                        package: _,
                    } = &*td;
                    let td_type = match td_type_assignment {
                        d::TypedefTypeAssignment::SimpleTypeDef(_, td_type) => td_type.clone(),
                        d::TypedefTypeAssignment::CaseType(variant, variants) => {
                            typing_utils::get_case_type_variants_as_type(variant, variants)
                        }
                    };
                    if acc.expanded_typedefs.contains(name) {
                        acc
                    } else {
                        let acc = {
                            let mut expanded_typedefs = acc.expanded_typedefs.clone();
                            expanded_typedefs.insert(name.to_string());
                            ValidationState {
                                expanded_typedefs,
                                ..acc
                            }
                        };
                        let subst = decl_instantiate::make_subst(td_tparams, tyl);
                        let td_type = decl_instantiate::instantiate(&subst, &td_type);
                        if env::is_typedef_visible(&acc.env, name, &td) {
                            this.on_alias(acc, r, id, tyl, &td_type)
                        } else {
                            let td_as_constraint = match td_as_constraint {
                                None => DeclTy::new(r.clone(), d::Ty_::Tmixed),
                                Some(ty) => decl_instantiate::instantiate(&subst, ty),
                            };
                            let td_super_constraint = match td_super_constraint {
                                // `MakeType.nothing r`
                                None => DeclTy::new(r.clone(), d::Ty_::Tunion(Box::new([]))),
                                Some(ty) => decl_instantiate::instantiate(&subst, ty),
                            };
                            this.on_newtype(
                                acc,
                                r,
                                id,
                                tyl,
                                &td_as_constraint,
                                &td_super_constraint,
                                &td_type,
                            )
                        }
                    }
                }
                decl_entry::T::Found(ClassOrTypedefResult::ClassResult(_))
                | decl_entry::T::DoesNotExist
                | decl_entry::T::NotYetAvailable => this.on_class(acc, r, id, tyl),
            }
        }
    }

    pub fn validate_type<V: TypeValidator + ?Sized>(
        this: &V,
        env: &Env,
        use_pos: Pos,
        root_ty: &DeclTy,
        reification: Option<Reification>,
        mut emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
    ) {
        let reification = reification.unwrap_or(Reification::Unresolved);
        let state = this.on_type(
            ValidationState {
                env: env.clone(),
                ety_env: ExpandEnv {
                    this_ty: env::get_self_ty(env)
                        .unwrap_or_else(|| make_type::nothing(reason::none())),
                    ..empty_expand_env()
                },
                expanded_typedefs: im::OrdSet::new(),
                validity: Validity::Valid,
                inside_reified_class_generic_position: false,
                reification,
                class_from_taccess_lhs: None,
            },
            root_ty,
        );
        match state.validity {
            Validity::Invalid(reasons) => emit_error(
                use_pos,
                typing_error::Lazy::new(move || {
                    reasons
                        .iter()
                        .map(|(r, msg)| Message(decl_reason_to_pos(r), msg.as_str().into()))
                        .collect()
                }),
            ),
            Validity::Valid => {}
        }
    }

    pub fn validate_hint<V: TypeValidator>(
        this: &V,
        env: &Env,
        hint: &aast::Hint,
        reification: Option<Reification>,
        emit_error: impl FnMut(Pos, typing_error::Lazy<Vec<Message<PosOrDecl>>>),
    ) {
        let hint_ty = decl_hint::hint(&env.decl_env, hint);
        this.validate_type(env, hint.0.clone(), &hint_ty, reification, emit_error)
    }

    /// Takes in and accumulates a list of reasons
    pub fn invalid_list<V: TypeValidator + ?Sized>(
        this: &V,
        state: ValidationState,
        reasons: Vec<(R, String)>,
    ) -> ValidationState {
        match state.validity {
            Validity::Valid => ValidationState {
                validity: Validity::Invalid(reasons),
                ..state
            },
            Validity::Invalid(prev_reasons) => {
                let mut all = prev_reasons;
                all.extend(reasons);
                ValidationState {
                    validity: Validity::Invalid(all),
                    ..state
                }
            }
        }
    }

    pub fn invalid<V: TypeValidator + ?Sized>(
        this: &V,
        state: ValidationState,
        r: &R,
        msg: &str,
    ) -> ValidationState {
        match state.validity {
            Validity::Valid => ValidationState {
                validity: Validity::Invalid(vec![(r.clone(), msg.to_string())]),
                ..state
            },
            Validity::Invalid(_) => state,
        }
    }
}
