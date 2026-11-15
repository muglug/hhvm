// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `private_member_variance_check.ml`. See `hh/PORTING.md`.
//!
//! Private members skip variance checks, but they can be reached through
//! receivers other than `$this`, whose type arguments may have been widened
//! (covariant) or narrowed (contravariant). Such a use must respect variance as
//! a public member would: a write needs the property type to be contravariant
//! in the class's variant type parameters, and a call needs the method type to
//! be covariant in them.

use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;
use ty::decl::ty as d;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::CeVisibility;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_defs_core::DeclTy;
use crate::typing_env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_variance;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Use {
    Write,
    Call,
}

/// The first variant type parameter of [cls] that [ty] uses against its
/// variance for [use], with the position of an offending occurrence.
fn violation(
    env: &tast_env::Env,
    cls: &cls::T,
    use_: Use,
    ty: &DeclTy,
) -> Option<(String, ast_defs::Variance, PosOrDecl)> {
    let variant: Vec<(String, ast_defs::Variance)> = cls::tparams(cls)
        .iter()
        .filter_map(|tp| match tp.variance {
            ast_defs::Variance::Invariant => None,
            variance @ (ast_defs::Variance::Covariant | ast_defs::Variance::Contravariant) => {
                Some((tp.name.id_ref().as_str().to_string(), variance))
            }
        })
        .collect();
    let (positive, negative) = typing_variance::get_positive_negative_generics(
        &variant.iter().map(|(name, _)| name.clone()).collect(),
        false,
        env,
        (im::OrdMap::new(), im::OrdMap::new()),
        ty,
    );
    variant.into_iter().find_map(|(name, variance)| {
        let offending = match (use_, variance) {
            (Use::Write, ast_defs::Variance::Covariant)
            | (Use::Call, ast_defs::Variance::Contravariant) => &positive,
            (Use::Write, ast_defs::Variance::Contravariant)
            | (Use::Call, ast_defs::Variance::Covariant)
            | (_, ast_defs::Variance::Invariant) => &negative,
        };
        match offending.get(&name) {
            Some(rs) => match rs.first() {
                Some(r) => {
                    use ty::reason::Reason as _;
                    Some((name, variance, r.pos().clone().to_oxidized()))
                }
                None => None,
            },
            None => None,
        }
    })
}

/// The class of a receiver that is not `$this`, if its private members could be
/// reached with widened or narrowed type arguments.
fn receiver_class(env: &tast_env::Env, recv: &tast::Expr) -> Option<cls::T> {
    match recv {
        aast::Expr(_, _, aast::Expr_::This) => None,
        aast::Expr(ty, _, _) => {
            let mut env = env.clone();
            let env = &mut env;
            let ty = tast_env::expand_type(env, ty.clone());
            let ty = match get_node(&ty) {
                Ty_::Toption(ty) => tast_env::expand_type(env, ty.clone()),
                _ => ty,
            };
            match get_node(&ty) {
                Ty_::Tclass((_, name), _, targs) if !targs.is_empty() => {
                    match decl_entry::to_option(tast_env::get_class(env, name)) {
                        Some(cls)
                            if cls::tparams(&cls)
                                .iter()
                                .any(|tp| tp.variance != ast_defs::Variance::Invariant) =>
                        {
                            Some(cls)
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
    }
}

fn private_member(
    env: &tast_env::Env,
    recv: &tast::Expr,
    get_member: fn(&crate::typing_env_types::Env, &cls::T, &str) -> Option<ClassElt>,
    member_name: &str,
) -> Option<(cls::T, DeclTy)> {
    receiver_class(env, recv).and_then(|cls| match get_member(env, &cls, member_name) {
        Some(ce) if matches!(ce.ce_visibility, CeVisibility::Vprivate(_)) => {
            let ty: DeclTy = (*ce.ce_type).clone();
            Some((cls, ty))
        }
        _ => None,
    })
}

fn check(
    env: &tast_env::Env,
    pos: &Pos,
    cls: &cls::T,
    member_name: &str,
    use_: Use,
    ty: &DeclTy,
) {
    if let Some((tparam_name, variance, use_pos)) = violation(env, cls, use_, ty) {
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::PrivateMemberVariance {
                pos: pos.clone(),
                class_name: cls::name(cls),
                member_name: member_name.to_string(),
                is_write: match use_ {
                    Use::Write => true,
                    Use::Call => false,
                },
                tparam_name,
                variance,
                use_pos,
                decl_pos: cls::pos(cls),
            }),
            env,
        )
    }
}

fn check_write(env: &tast_env::Env, recv: &tast::Expr, pos: &Pos, prop: &str) {
    if let Some((cls, ty)) = private_member(env, recv, typing_env::get_prop, prop) {
        check(env, pos, &cls, prop, Use::Write, &ty)
    }
}

fn check_call(env: &tast_env::Env, recv: &tast::Expr, pos: &Pos, meth: &str) {
    if let Some((cls, ty)) = private_member(env, recv, typing_env::get_method, meth) {
        // The visitor treats an `as` bound of a method type parameter as
        // covariant, but for variance it is contravariant (see
        // [Typing_variance.tparam_constraint]), so bounds are left out.
        let ty = match ty.node_ref() {
            d::Ty_::Tfun(ft) => DeclTy::new(
                ty.reason().clone(),
                d::Ty_::Tfun(Box::new(ty::decl::FunType {
                    tparams: Box::new([]),
                    where_constraints: Box::new([]),
                    ..(**ft).clone()
                })),
            ),
            _ => ty,
        };
        check(env, pos, &cls, meth, Use::Call, &ty)
    }
}

/// The property written by an lvalue such as `$x->p`, `$x->p[0]` or `$x->p[]`
fn written_property(lval: &tast::Expr) -> Option<(&tast::Expr, &Pos, &str)> {
    match &lval.2 {
        aast::Expr_::ObjGet(og) if matches!(og.3, aast::PropOrMethod::IsProp) => match &og.1 {
            aast::Expr(_, pos, aast::Expr_::Id(id)) => Some((&og.0, pos, id.1.as_str())),
            _ => None,
        },
        aast::Expr_::ArrayGet(ag) => written_property(&ag.0),
        _ => None,
    }
}

/// The object `handler`.
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        match &e.2 {
            aast::Expr_::Assign(assign) => {
                if let Some((recv, pos, prop)) = written_property(&assign.0) {
                    check_write(env, recv, pos, prop)
                }
            }
            aast::Expr_::Call(call) => match &call.func.2 {
                aast::Expr_::ObjGet(og) if matches!(og.3, aast::PropOrMethod::IsMethod) => {
                    match &og.1 {
                        aast::Expr(_, pos, aast::Expr_::Id(id)) => {
                            check_call(env, &og.0, pos, id.1.as_str())
                        }
                        _ => {}
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
