// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `no_disjoint_union_check.ml`. See `hh/PORTING.md`.
//!
//! `check` is polymorphic in OCaml: it is given the type parameters of a
//! localized function type (`locl_ty tparam`) or of a class declaration
//! (`decl_ty tparam`). Here these are two types (`typing_defs::Tparam` and
//! `ty::decl::Tparam`), so `check` takes any [`TparamFields`].

use std::cmp::Ordering;
use std::sync::LazyLock;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ctx::R;
use crate::decl_entry;
use crate::folded_class;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::attributes;
use crate::typing_defs::*;
use crate::typing_reason;
use crate::typing_warning;
use crate::typing_warning_utils;

/// The fields of `'ty Typing_defs.tparam` that [`check`] reads.
trait TparamFields {
    type UserAttribute: attributes::UserAttribute;

    /// `tp_user_attributes`
    fn tp_user_attributes(&self) -> &[Self::UserAttribute];

    /// `fst tp_name`
    fn tp_name_pos(&self) -> PosOrDecl;
}

impl TparamFields for Tparam {
    type UserAttribute = UserAttribute;

    fn tp_user_attributes(&self) -> &[UserAttribute] {
        &self.user_attributes
    }

    fn tp_name_pos(&self) -> PosOrDecl {
        self.name.0.clone()
    }
}

impl TparamFields for ty::decl::Tparam<R, DeclTy> {
    type UserAttribute = ty::decl::UserAttribute<<R as ty::reason::Reason>::Pos>;

    fn tp_user_attributes(&self) -> &[Self::UserAttribute] {
        &self.user_attributes
    }

    fn tp_name_pos(&self) -> PosOrDecl {
        self.name.pos().clone().to_oxidized()
    }
}

fn is_no_union<UA: attributes::UserAttribute>(ua: &UA) -> bool {
    ua.ua_name() == sn::user_attributes::NO_DISJOINT_UNION
}

/// Chek for pairwise disjointness of types.
fn is_pairwise_disjoint(env: &Env, tyl: &[Ty]) -> bool {
    match tyl {
        [] | [_] => true,
        [ty, tyl @ ..] => {
            tyl.iter()
                .all(|ty_| match tast_env::is_disjoint(true, env, ty, ty_) {
                    tast_env::IsDisjointResult::Disjoint
                    | tast_env::IsDisjointResult::DisjointIgnoringDynamic(_, _) => true,
                    tast_env::IsDisjointResult::NonDisjoint => false,
                })
                && is_pairwise_disjoint(env, tyl)
        }
    }
}

fn tyl_of_union(env: &Env, ty: &Ty) -> Option<Vec<Ty>> {
    let ty = tast_env::strip_dynamic(env, ty.clone());
    let (_, ty) = tast_env::strip_supportdyn(env, ty);
    match get_node(&ty) {
        Ty_::Tunion(tyl) => Some(tyl.clone()),
        Ty_::Toption(ty) => tyl_of_union(env, ty),
        _ => None,
    }
}

/// `List.dedup_and_sort ~compare` of Base: a stable sort, then, of each run
/// of elements that compare equal, the last one.
fn dedup_and_sort<A>(mut list: Vec<A>, compare: impl Fn(&A, &A) -> Ordering) -> Vec<A> {
    if list.len() <= 1 {
        return list;
    }
    list.sort_by(&compare);
    let mut res: Vec<A> = Vec::with_capacity(list.len());
    for x in list {
        match res.last_mut() {
            Some(to_keep) if compare(to_keep, &x) == Ordering::Equal => *to_keep = x,
            _ => res.push(x),
        }
    }
    res
}

/// Looks for pairwise disjointness of a union in a type argument if the
/// corresponding type parameter is annotated with __NoDisjointUnion. If found,
/// we raise a warning.
fn check<TP: TparamFields>(pos: &Pos, env: &Env, tparams: &[TP], targs: &[tast::Targ]) {
    // List.zip targs tparams
    if targs.len() == tparams.len() {
        let zipped = targs.iter().zip(tparams.iter());
        for (aast::Targ(ty, _), tparam) in zipped {
            let user_attributes = tparam.tp_user_attributes();
            if user_attributes.iter().any(is_no_union) {
                let ty = tast_env::strip_dynamic(env, ty.clone());
                let (_, ty) = tast_env::strip_supportdyn(env, ty);
                match tyl_of_union(env, &ty) {
                    None => {}
                    Some(tyl) if tyl.len() <= 1 => {}
                    Some(tyl) => {
                        if is_pairwise_disjoint(env, &tyl) {
                            let reason_of_ty = |ty: &Ty| {
                                (
                                    typing_reason::to_pos(get_reason(ty)),
                                    tast_env::print_ty(env, ty),
                                )
                            };
                            let disjuncts: typing_warning::Lazy<'_, Vec<(PosOrDecl, String)>> =
                                LazyLock::new(Box::new(move || {
                                    dedup_and_sort(
                                        tyl.iter().map(reason_of_ty).collect(),
                                        |(p, _), (p_, _)| pos_or_decl::compare(p, p_),
                                    )
                                }));
                            let tparam_pos = tparam.tp_name_pos();
                            typing_warning_utils::add(
                                env,
                                (
                                    pos.clone(),
                                    typing_warning::Kind::No_disjoint_union_check,
                                    typing_warning::no_disjoint_union_check::T {
                                        disjuncts,
                                        tparam_pos,
                                    },
                                ),
                            )
                        }
                    }
                }
            }
        }
    }
}

/// Flag violations on __NoDisjointUnion on call and new expressions.
/// (`let handler = object inherit Tast_visitor.handler_base ... end`)
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match e {
            aast::Expr(_, p, aast::Expr_::Call(call)) => {
                let aast::CallExpr {
                    func: aast::Expr(fun_ty, _, _),
                    targs,
                    ..
                } = &**call;
                let (_, fun_ty) = tast_env::strip_supportdyn(env, fun_ty.clone());
                match get_node(&fun_ty) {
                    Ty_::Tfun(ft) => check(p, env, &ft.tparams, targs),
                    _ => {}
                }
            }
            aast::Expr(_, p, aast::Expr_::New(new))
                if matches!(&new.0.2, aast::ClassId_::CI(_)) =>
            {
                let (aast::ClassId(_, _, cid_), targs, _, _, _) = &**new;
                let aast::ClassId_::CI(ast_defs::Id(_, cid)) = cid_ else {
                    unreachable!()
                };
                match tast_env::get_class(env, cid) {
                    decl_entry::T::Found(elt) => {
                        let tparams = folded_class::tparams(&elt);
                        check(p, env, &tparams, targs)
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
            _ => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dedup_and_sort_is_stable_and_keeps_the_last_of_equals() {
        let l = vec![(3, "a"), (1, "b"), (3, "c"), (2, "d"), (1, "e")];
        let res = dedup_and_sort(l, |(x, _), (y, _)| x.cmp(y));
        assert_eq!(res, vec![(1, "e"), (2, "d"), (3, "c")]);
        // `[] | [_] -> list`
        assert_eq!(
            dedup_and_sort(vec![(1, "a")], |(x, _), (y, _)| x.cmp(y)),
            vec![(1, "a")]
        );
        let empty: Vec<(i32, &str)> = vec![];
        assert_eq!(dedup_and_sort(empty, |(x, _), (y, _)| x.cmp(y)), vec![]);
    }
}
