// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_redundant_generics.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! (linting is not fanout-aware, so it's safe to use non-dep-aware
//! functions here)

use naming_special_names_rust as sn;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::ReifyKind;
use pos::ToOxidized;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
use crate::decl_provider;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::attributes;
use crate::typing_defs::*;
use crate::typing_variance;

/// `S_set.t`
type SSet = im::OrdSet<String>;

fn ft_redundant_tparams(
    env: &Env,
    overlapping: Option<&SSet>,
    tparams: &[DeclTparam],
    ty: &DeclTy,
) {
    let tracked = tparams.iter().fold(SSet::new(), |tracked, t| {
        tracked.update(t.name.id_ref().as_str().to_string())
    });
    let (positive, negative) = typing_variance::get_positive_negative_generics(
        &tracked,
        false,
        tast_env::eq_typing_env(env),
        (im::OrdMap::new(), im::OrdMap::new()),
        ty,
    );
    tparams.iter().for_each(|t| {
        let (pos, name) = (t.name.pos().clone().to_oxidized(), t.name.id_ref().as_str());
        let pos = crate::naming_provider::resolve_position(&tast_env::get_ctx(env), &pos);
        // It's only redundant if it's erased and inferred, and not covered by a non-disjointness check
        if t.reified == ReifyKind::Erased
            && !attributes::mem(sn::user_attributes::NON_DISJOINT, &t.user_attributes)
            && !attributes::mem(sn::user_attributes::EXPLICIT, &t.user_attributes)
            // Don't track generics that are mentioned in an <<__Overlapping>> attribute
            && !(match overlapping {
                Some(s) => s.contains(name),
                None => false,
            })
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
                        [] => crate::lints_diagnostics::redundant_covariant(
                            pos,
                            name,
                            bounds_message,
                            "nothing",
                        ),
                        [(_, t)] => crate::lints_diagnostics::redundant_covariant(
                            pos,
                            name,
                            bounds_message,
                            &tast_env::print_decl_ty(None, env, t),
                        ),
                        _ => {}
                    }
                }
                (None, Some(_positions)) => {
                    let bounds_message = if super_bounds.is_empty() {
                        ""
                    } else {
                        " with useless `super` bound"
                    };
                    // If there is more than one `as` bound, we can't replace,
                    // because we don't support explicit intersection types
                    match as_bounds.as_slice() {
                        [] => crate::lints_diagnostics::redundant_contravariant(
                            pos,
                            name,
                            bounds_message,
                            "mixed",
                        ),
                        [(_, t)] => crate::lints_diagnostics::redundant_contravariant(
                            pos,
                            name,
                            bounds_message,
                            &tast_env::print_decl_ty(None, env, t),
                        ),
                        _ => {
                            let ts: Vec<DeclTy> = as_bounds.iter().map(|(_, t)| t.clone()).collect();
                            match tast_env::as_bounds_to_non_intersection_type(env, &ts) {
                                // We can't denote this in source code so don't emit lint warning
                                None => {}
                                Some(locl_ty) => crate::lints_diagnostics::redundant_contravariant(
                                    pos,
                                    name,
                                    bounds_message,
                                    &tast_env::print_ty(env, &locl_ty),
                                ),
                            }
                        }
                    }
                }
                (None, None) => crate::lints_diagnostics::redundant_generic(pos, name),
            }
        }
    })
}

fn check_redundant_generics_class_method(env: &Env, (_method_name, method_): &(String, ClassElt)) {
    // (lazy (ty as ft))
    let ty: &DeclTy = &method_.ce_type;
    let ft = ty;
    match ty.node_ref() {
        d::Ty_::Tfun(fty) => ft_redundant_tparams(
            env,
            method_.ce_overlapping_tparams.as_ref(),
            &fty.tparams,
            ft,
        ),
        _ => panic!("Assert_failure lints/linter_redundant_generics.ml"),
    }
}

fn check_redundant_generics_fun(env: &Env, ft: &DeclFunType) {
    ft_redundant_tparams(
        env,
        None,
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

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_fun_def(&mut self, env: &Env, fd: &'a tast::FunDef) {
        match decl_provider::get_fun(None, &tast_env::get_ctx(env), &fd.name.1) {
            decl_entry::T::Found(fe) => match fe.ty.node_ref() {
                d::Ty_::Tfun(ft) => check_redundant_generics_fun(env, ft),
                _ => {}
            },
            _ => {}
        }
    }

    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let cid = &c.name.1;
        match decl_provider::get_class(None, &tast_env::get_ctx(env), cid) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => check_redundant_generics_class(env, &c.name.1, &cls),
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
