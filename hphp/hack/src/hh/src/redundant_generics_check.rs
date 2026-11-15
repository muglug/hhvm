// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/redundant_generics_check.ml`.
//! See `hh/PORTING.md`.

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::ReifyKind;
use pos::ToOxidized;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::ctx::Ctx;
use crate::ctx::R;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::type_visitor::DeclTypeVisitor;
use crate::typing_defs::attributes;
use crate::typing_defs::*;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_variance;

/// `S_set.t`
type SSet = im::OrdSet<String>;

/// `parent#on_type` in a class that inherits
/// `Type_visitor.decl_type_visitor` and overrides `on_type`: the body of the
/// default [`DeclTypeVisitor::on_type`].
fn decl_type_visitor_on_type<A, V: DeclTypeVisitor<A> + ?Sized>(
    this: &mut V,
    acc: A,
    ty: &DeclTy,
) -> A {
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

fn ft_redundant_generics(env: &Env, tparams: &[DeclTparam], ty: &DeclTy) {
    let tracked = tparams.iter().fold(SSet::new(), |tracked, t| {
        tracked.update(t.name.id_ref().as_str().to_string())
    });
    let (positive, negative) = typing_variance::get_positive_negative_generics(
        &tracked,
        false,
        env,
        (im::OrdMap::new(), im::OrdMap::new()),
        ty,
    );
    // Find the set of generics that appear as part of the type HH\EnumClass\Label
    let label_generics = {
        struct GenericsFinder;
        impl DeclTypeVisitor<SSet> for GenericsFinder {
            fn on_tgeneric(&mut self, acc: SSet, _r: &R, n: &str) -> SSet {
                acc.update(n.to_string())
            }
        }
        struct Finder;
        impl DeclTypeVisitor<SSet> for Finder {
            fn on_type(&mut self, acc: SSet, ty: &DeclTy) -> SSet {
                match ty.node_ref() {
                    d::Ty_::Tapply(id_and_tyl)
                        if id_and_tyl.1.len() == 2
                            && id_and_tyl.0.id_ref().as_str() == sn::classes::ENUM_CLASS_LABEL =>
                    {
                        let generics_finder = &mut GenericsFinder;
                        generics_finder.on_type(acc, &id_and_tyl.1[1])
                    }
                    _ => decl_type_visitor_on_type(self, acc, ty),
                }
            }
        }
        let finder = &mut Finder;
        finder.on_type(SSet::new(), ty)
    };
    tparams.iter().for_each(|t| {
        let (pos, name) = (t.name.pos().clone().to_oxidized(), t.name.id_ref().as_str());
        // It's only redundant if it's erased and inferred
        if t.reified == ReifyKind::Erased
            && !attributes::mem(sn::user_attributes::EXPLICIT, &t.user_attributes)
        {
            let super_bounds: Vec<&(ConstraintKind, DeclTy)> = t
                .constraints
                .iter()
                .filter(|(ck, _)| *ck == ConstraintKind::ConstraintSuper)
                .collect();
            let as_bounds: Vec<&(ConstraintKind, DeclTy)> = t
                .constraints
                .iter()
                .filter(|(ck, _)| *ck == ConstraintKind::ConstraintAs)
                .collect();
            match (positive.get(name), negative.get(name)) {
                (Some(_), Some(_)) => {}
                (Some(_positions), None) => {
                    let bounds_message = if as_bounds.is_empty() {
                        ""
                    } else {
                        " with useless `as` bound"
                    };
                    // If there is more than one `super` bound, we can't replace,
                    // because we don't support explicit union types
                    match super_bounds.as_slice() {
                        [] => typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::RedundantGeneric {
                                pos: pos_or_decl::unsafe_to_raw_pos(pos),
                                variance: primary::RedundantGenericVariance::Co,
                                msg: bounds_message.to_string(),
                                suggest: "nothing".to_string(),
                            }),
                            env,
                        ),
                        [(_, t)] => typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::RedundantGeneric {
                                pos: pos_or_decl::unsafe_to_raw_pos(pos),
                                variance: primary::RedundantGenericVariance::Co,
                                msg: bounds_message.to_string(),
                                suggest: tast_env::print_decl_ty(None, env, t),
                            }),
                            env,
                        ),
                        _ => {}
                    }
                }
                // Only report an error if the generic appears within a enum class label
                (None, Some(_positions)) if label_generics.contains(name) => {
                    let bounds_message = if super_bounds.is_empty() {
                        ""
                    } else {
                        " with useless `super` bound"
                    };
                    let ts: Vec<DeclTy> = as_bounds.iter().map(|(_, t)| t.clone()).collect();
                    match tast_env::as_bounds_to_non_intersection_type(env, &ts) {
                        // We can't denote this in source code so let it be
                        None => {}
                        Some(locl_ty) => typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::RedundantGeneric {
                                pos: pos_or_decl::unsafe_to_raw_pos(pos),
                                variance: primary::RedundantGenericVariance::Contra,
                                msg: bounds_message.to_string(),
                                suggest: tast_env::print_ty(env, &locl_ty),
                            }),
                            env,
                        ),
                    }
                }
                (None, Some(_positions)) => {}
                (None, None) => {}
            }
        }
    })
}

fn check_redundant_generics_class_method(env: &Env, (_method_name, method_): &(String, ClassElt)) {
    // (lazy (ty as ft))
    let ty: &DeclTy = &method_.ce_type;
    let ft = ty;
    match ty.node_ref() {
        d::Ty_::Tfun(fty) => ft_redundant_generics(env, &fty.tparams, ft),
        _ => panic!("assert false"),
    }
}

fn check_redundant_generics_fun(env: &Env, ft: &DeclFunType) {
    ft_redundant_generics(
        env,
        &ft.tparams,
        &DeclTy::new(R::none(), d::Ty_::Tfun(Box::new(ft.clone()))),
    )
}

fn check_redundant_generics_class(env: &Env, class_name: &str, class_type: &cls::T) {
    cls::methods(class_type)
        .iter()
        .filter(|(_, meth)| meth.ce_origin == class_name)
        .for_each(|m| check_redundant_generics_class_method(env, m));
    cls::smethods(class_type)
        .iter()
        .filter(|(_, meth)| meth.ce_origin == class_name)
        .for_each(|m| check_redundant_generics_class_method(env, m))
}

/// `create_handler _ctx`: its `handler` object.
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        if !tast_env::is_hhi(env) {
            match tast_env::get_fun(env, &fd.name.1) {
                decl_entry::T::Found(fe) => match fe.ty.node_ref() {
                    d::Ty_::Tfun(ft) => check_redundant_generics_fun(env, ft),
                    _ => {}
                },
                _ => {}
            }
        }
    }

    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        if !tast_env::is_hhi(env) {
            let cid = &c.name.1;
            match tast_env::get_class(env, cid) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(cls) => check_redundant_generics_class(env, &c.name.1, &cls),
            }
        }
    }
}

/// `val create_handler : Provider_context.t -> Tast_visitor.handler option`
pub fn create_handler(_ctx: &Arc<Ctx>) -> Option<Box<dyn for<'a> tast_visitor::Handler<'a>>> {
    let handler = Handler;
    Some(Box::new(handler))
}
