// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_dependent_type.ml`. See `hh/PORTING.md`.

/// `module ExprDepTy`
pub mod expr_dep_ty {
    use naming_special_names_rust as sn;
    use oxidized::aast;
    use oxidized::ast_defs::Id;
    use oxidized::nast;

    use crate::decl_entry;
    use crate::expression_id;
    use crate::pos_or_decl;
    use crate::typing_defs::*;
    use crate::typing_env as env;
    use crate::typing_env_types::Env;
    use crate::typing_reason;
    use crate::typing_reason::ExprDepTypeReason;
    /// `Typing_reason.t`
    use crate::typing_reason::T as Reason;
    use crate::typing_utils as t_utils;

    /// `Naming_special_names.Classes.cString` (which
    /// `naming_special_names_rust` does not have).
    const C_STRING: &str = "\\HH\\string";

    #[derive(Clone, Debug)]
    pub enum Dep {
        DepThis,
        DepCls(String),
        DepExpr(expression_id::T),
    }

    fn new_(env: &Env) -> (ExprDepTypeReason, Dep) {
        let eid = env::make_expression_id(env);
        (ExprDepTypeReason::ERexpr(eid), Dep::DepExpr(eid))
    }

    /// Convert a class_id into a "dependent kind" (dep). This later informs the make_with_dep_kind function
    /// how to translate a type suitable for substituting for `this` in a method signature.
    pub fn from_cid(env: &Env, reason: Reason, cid: &nast::ClassId_) -> (Reason, Dep) {
        let pos = typing_reason::to_pos(&reason);
        let (pos, expr_dep_reason, dep) = match cid {
            aast::ClassId_::CIparent => match env::get_parent_id(env) {
                Some(cls) => (pos, ExprDepTypeReason::ERparent(cls.clone()), Dep::DepCls(cls)),
                None => {
                    let (ereason, dep) = new_(env);
                    (pos, ereason, dep)
                }
            },
            aast::ClassId_::CIself => match env::get_self_id(env) {
                Some(cls) => (pos, ExprDepTypeReason::ERself(cls.clone()), Dep::DepCls(cls)),
                None => {
                    let (ereason, dep) = new_(env);
                    (pos, ereason, dep)
                }
            },
            aast::ClassId_::CI(Id(p, cls)) => (
                pos_or_decl::of_raw_pos(p.clone()),
                ExprDepTypeReason::ERclass(cls.clone()),
                Dep::DepCls(cls.clone()),
            ),
            aast::ClassId_::CIreified(Id(p, cls)) => (
                pos_or_decl::of_raw_pos(p.clone()),
                ExprDepTypeReason::ERclass(cls.clone()),
                Dep::DepCls(cls.clone()),
            ),
            aast::ClassId_::CIstatic => (pos, ExprDepTypeReason::ERstatic, Dep::DepThis),
            aast::ClassId_::CIexpr(aast::Expr(_, p, aast::Expr_::This)) => (
                pos_or_decl::of_raw_pos(p.clone()),
                ExprDepTypeReason::ERstatic,
                Dep::DepThis,
            ),
            // If it is a local variable then we look up the expression id associated
            // with it. If one doesn't exist we generate a new one. We are being
            // conservative here because the new expression id we create isn't
            // added to the local enviornment.
            aast::ClassId_::CIexpr(aast::Expr(_, p, aast::Expr_::Lvar(lid))) => {
                let aast::Lid(_, x) = &**lid;
                let (ereason, dep) = match env::get_local_expr_id(env, x) {
                    Some(eid) => (ExprDepTypeReason::ERexpr(eid), Dep::DepExpr(eid)),
                    None => new_(env),
                };
                (pos_or_decl::of_raw_pos(p.clone()), ereason, dep)
            }
            // If all else fails we generate a new identifier for our expression
            // dependent type.
            aast::ClassId_::CIexpr(aast::Expr(_, p, _)) => {
                let (ereason, dep) = new_(env);
                (pos_or_decl::of_raw_pos(p.clone()), ereason, dep)
            }
        };
        (
            typing_reason::expr_dep_type((reason, pos, expr_dep_reason)),
            dep,
        )
    }

    // A type access "this::T" is translated to "<this>::T" during the
    // naming phase. While typing a body, "<this>" is a type hole that needs to
    // be filled with a final concrete type. Resolution is specified in typing.ml,
    // here is a high level break down:
    //
    // 1) When a class member "bar" is accessed via "[CID]->bar" or "[CID]::bar"
    // we resolve "<this>" in the type of "bar" to "<[CID]>"
    //
    // 2) When typing a method, we resolve "<this>" in the return type to
    // "this"
    //
    // 3) When typing a method, we resolve "<this>" in parameters of the
    // function to "<static>" in static methods or "<$this>" in non-static
    // methods
    //
    // More specific details are explained inline
    pub fn make_with_dep_kind(env: &mut Env, dep_kind: (Reason, Dep), ty: Ty) -> Ty {
        let (r_dep_ty, dep_ty) = dep_kind;
        let apply = |env: &mut Env, ty: Ty| -> Ty {
            match &dep_ty {
                Dep::DepCls(_) => mk((
                    r_dep_ty.clone(),
                    Ty_::Tdependent(DependentType::DTexpr(env::make_expression_id(env)), ty),
                )),
                Dep::DepThis => ty,
                Dep::DepExpr(id) => mk((
                    r_dep_ty.clone(),
                    Ty_::Tdependent(DependentType::DTexpr(*id), ty),
                )),
            }
        };
        fn make(
            r_dep_ty: &Reason,
            dep_ty: &Dep,
            apply: &dyn Fn(&mut Env, Ty) -> Ty,
            seen: &im::OrdSet<String>,
            env: &mut Env,
            ty: Ty,
        ) -> Ty {
            let ty = env::expand_type(env, ty);
            let r = get_reason(&ty).clone();
            match get_node(&ty) {
                Ty_::Tclass(_, Exact::Exact, _) => ty,
                // Special case for known final generic types that don't use this in their API
                Ty_::Tclass((_, x), _, _)
                    if x == sn::collections::VEC
                        || x == sn::collections::DICT
                        || x == sn::collections::KEYSET
                        || x == C_STRING =>
                {
                    ty
                }
                Ty_::Tclass(c, Exact::Nonexact(_), tyl) => {
                    let (_, x) = c;
                    let class_ = env::get_class(env, x);
                    // If a class is both final and variant, we must treat it as non-final
                    // since we can't statically guarantee what the runtime type
                    // will be.
                    if decl_entry::to_option(class_)
                        .map_or(false, |class_ty| t_utils::class_is_final_and_invariant(&class_ty))
                    {
                        ty
                    } else {
                        match dep_ty {
                            Dep::DepCls(n) if n == x => {
                                mk((r_dep_ty.clone(), Ty_::Tclass(c.clone(), Exact::Exact, tyl.clone())))
                            }
                            _ => apply(env, ty),
                        }
                    }
                }
                Ty_::Tgeneric(s) if dependent_kind::is_generic_dep_ty(s) => ty,
                Ty_::Tgeneric(name) => {
                    if seen.contains(name) {
                        ty
                    } else {
                        let tyl: Vec<Ty> =
                            t_utils::get_concrete_supertypes(None, None, None, true, env, ty.clone());
                        let seen = seen.update(name.clone());
                        let tyl_: Vec<Ty> = tyl
                            .iter()
                            .map(|ty| make(r_dep_ty, dep_ty, apply, &seen, env, ty.clone()))
                            .collect();
                        if tyl_equal(&tyl, &tyl_) {
                            ty
                        } else {
                            apply(env, ty)
                        }
                    }
                }
                Ty_::Toption(ty) => {
                    let ty = make(r_dep_ty, dep_ty, apply, seen, env, ty.clone());
                    mk((r, Ty_::Toption(ty)))
                }
                Ty_::Tnewtype(n, p, ty) => {
                    let ty = make(r_dep_ty, dep_ty, apply, seen, env, ty.clone());
                    mk((r, Ty_::Tnewtype(n.clone(), p.clone(), ty)))
                }
                Ty_::Tdependent(_, _) => ty,
                Ty_::Tunion(tyl) => {
                    let tyl = tyl
                        .iter()
                        .map(|ty| make(r_dep_ty, dep_ty, apply, seen, env, ty.clone()))
                        .collect();
                    mk((r, Ty_::Tunion(tyl)))
                }
                Ty_::Tintersection(tyl) => {
                    let tyl = tyl
                        .iter()
                        .map(|ty| make(r_dep_ty, dep_ty, apply, seen, env, ty.clone()))
                        .collect();
                    mk((r, Ty_::Tintersection(tyl)))
                }
                Ty_::Taccess(TaccessType(ty, ids)) => {
                    let ty = make(r_dep_ty, dep_ty, apply, seen, env, ty.clone());
                    mk((r, Ty_::Taccess(TaccessType(ty, ids.clone()))))
                }
                Ty_::TclassPtr(ty) => {
                    let ty = make(r_dep_ty, dep_ty, apply, seen, env, ty.clone());
                    mk((r, Ty_::TclassPtr(ty)))
                }
                Ty_::Tnonnull
                | Ty_::Tprim(_)
                | Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_))
                | Ty_::Ttuple(_)
                | Ty_::Tdynamic(_)
                | Ty_::TvecOrDict(_, _)
                | Ty_::Tfun(_)
                | Ty_::Tany(_)
                | Ty_::Tvar(_)
                | Ty_::Tneg(_)
                | Ty_::Tlabel(_) => ty,
            }
        }
        make(&r_dep_ty, &dep_ty, &apply, &im::OrdSet::new(), env, ty)
    }

    pub fn make(env: &mut Env, cid: &nast::ClassId_, ty: Ty) -> Ty {
        let dep_kind = from_cid(env, get_reason(&ty).clone(), cid);
        make_with_dep_kind(env, dep_kind, ty)
    }
}
