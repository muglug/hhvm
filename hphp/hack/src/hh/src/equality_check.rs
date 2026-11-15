// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/equality_check.ml`. See `hh/PORTING.md`.
//!
//! Warns when comparing two expression whose types are disjoint.

use naming_special_names_rust as sn;
use oxidized::aast::Case;
use oxidized::aast::Expr;
use oxidized::aast::Expr_;
use oxidized::aast::Stmt;
use oxidized::aast::Stmt_;
use oxidized::aast::Targ;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;

use crate::error_codes;
use crate::folded_class as cls;
use crate::tast;
use crate::tast::get_type;
use crate::tast_env;
use crate::tast_visitor;
use crate::type_mapper::TvarExpandingTypeMapper;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::get_node;
use crate::typing_defs::mk;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error_utils;
use crate::typing_phase;
use crate::typing_reason::T as Reason;
use crate::typing_tdef_locl;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning::Migrated;
use crate::typing_warning_utils;

const WARNING_KIND: typing_warning::Kind<typing_warning::equality_check::T, Migrated> =
    typing_warning::Kind::EQUALITY_CHECK;

pub fn error_codes() -> Vec<error_codes::warning::T> {
    typing_warning_utils::codes(&WARNING_KIND)
}

fn enum_base_type(env: &mut Env, cid: &str) -> Option<Ty> {
    match typing_env::get_class(env, cid) {
        crate::decl_entry::T::DoesNotExist | crate::decl_entry::T::NotYetAvailable => None,
        crate::decl_entry::T::Found(cls) => match cls::enum_type(&cls) {
            None => None,
            Some(te) => {
                let (ty_err_opt, ty) = typing_phase::localize_no_subst(env, true, &te.base);
                if let Some(err) = &ty_err_opt {
                    typing_error_utils::add_typing_error(err, env)
                }
                Some(ty)
            }
        },
    }
}

/// `opaque_enum_expander`
struct OpaqueEnumExpander;

fn opaque_enum_expander() -> OpaqueEnumExpander {
    OpaqueEnumExpander
}

impl TvarExpandingTypeMapper for OpaqueEnumExpander {
    fn on_tnewtype(
        &mut self,
        env: &mut Env,
        r: Reason,
        cid: String,
        tyl: Vec<Ty>,
        _cstr: Ty,
    ) -> Ty {
        let cstr = typing_utils::get_newtype_super(env, r.clone(), &cid, &tyl);
        match get_node(&cstr) {
            Ty_::Tprim(Tprim::Tarraykey) if typing_env::is_enum(env, &cid) => {
                let cstr_ = enum_base_type(env, &cid);
                match cstr_ {
                    None => mk((r, Ty_::Tnewtype(cid, tyl, cstr))),
                    Some(ty) => match get_node(&ty) {
                        Ty_::Tprim(Tprim::Tarraykey) => mk((r, Ty_::Tnewtype(cid, tyl, cstr))),
                        _ => ty,
                    },
                }
            }
            _ => {
                // `super#on_tnewtype env r cid tyl cstr` (`deep_type_mapper`)
                let tyl = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
                let cstr = self.on_type(env, cstr);
                mk((r, Ty_::Tnewtype(cid, tyl, cstr)))
            }
        }
    }
}

fn add_warning(
    env: &Env,
    as_lint: bool,
    pos: Pos,
    kind: typing_warning::equality_check::Kind,
    ty1: String,
    ty2: String,
) {
    typing_warning_utils::add_for_migration(
        &tast_env::get_tcopt(env),
        if as_lint { Some(None) } else { None },
        (
            pos,
            WARNING_KIND,
            typing_warning::equality_check::T { kind, ty1, ty2 },
        ),
    )
}

fn error_if_inequatable(env: &Env, ty1: &Ty, ty2: &Ty, err: impl FnOnce(String, String)) {
    // (`~ety_env:empty_expand_env` for both types: made once.)
    let ety_env = empty_expand_env();
    let expand_tydef =
        |env: &mut Env, ty: Ty| typing_tdef_locl::force_expand_typedef(&ety_env, env, ty);
    let expand_enum = |env: &mut Env, ty: Ty| opaque_enum_expander().on_type(env, ty);
    // Break all type abstractions
    let expand = |env: &mut Env, ty: Ty| {
        let ty = expand_enum(env, ty);
        let (_, ty, _) = expand_tydef(env, ty);
        ty
    };
    let mut env = env.clone();
    let ety1 = expand(&mut env, ty1.clone());
    let ety2 = expand(&mut env, ty2.clone());
    // The arguments of `err` are evaluated right to left, as in OCaml.
    match tast_env::is_disjoint(false, &env, &ety1, &ety2) {
        tast_env::IsDisjointResult::NonDisjoint => {}
        tast_env::IsDisjointResult::Disjoint => {
            let s2 = tast_env::print_ty(&env, ty2);
            let s1 = tast_env::print_ty(&env, ty1);
            err(s1, s2)
        }
        tast_env::IsDisjointResult::DisjointIgnoringDynamic(ty1, ty2) => {
            let s2 = tast_env::print_ty(&env, &ty2);
            let s1 = tast_env::print_ty(&env, &ty1);
            err(s1, s2)
        }
    }
}

fn ensure_valid_equality_check(
    env: &Env,
    as_lint: bool,
    p: &Pos,
    bop: &Bop,
    e1: &tast::Expr,
    e2: &tast::Expr,
) {
    let ty1 = get_type(e1);
    let ty2 = get_type(e2);
    error_if_inequatable(env, ty1, ty2, |ty1, ty2| {
        add_warning(
            env,
            as_lint,
            p.clone(),
            // `equal_bop bop Diff2`
            typing_warning::equality_check::Kind::Equality(matches!(bop, Bop::Diff2)),
            ty1,
            ty2,
        )
    })
}

fn ensure_valid_case_check(env: &Env, as_lint: bool, p: &Pos, e1: &tast::Expr, e2: &tast::Expr) {
    let ty1 = get_type(e1);
    let ty2 = get_type(e2);
    error_if_inequatable(env, ty1, ty2, |ty1, ty2| {
        add_warning(
            env,
            as_lint,
            p.clone(),
            typing_warning::equality_check::Kind::Switch,
            ty1,
            ty2,
        )
    })
}

fn ensure_valid_contains_check(env: &Env, as_lint: bool, p: &Pos, trv_val_ty: &Ty, val_ty: &Ty) {
    error_if_inequatable(env, trv_val_ty, val_ty, |ty1, ty2| {
        add_warning(
            env,
            as_lint,
            p.clone(),
            typing_warning::equality_check::Kind::Contains,
            ty1,
            ty2,
        )
    })
}

fn ensure_valid_contains_key_check(
    env: &Env,
    as_lint: bool,
    p: &Pos,
    trv_key_ty: &Ty,
    key_ty: &Ty,
) {
    error_if_inequatable(env, trv_key_ty, key_ty, |ty1, ty2| {
        add_warning(
            env,
            as_lint,
            p.clone(),
            typing_warning::equality_check::Kind::ContainsKey,
            ty1,
            ty2,
        )
    })
}

/// `handler ~as_lint`
struct Handler {
    as_lint: bool,
}

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, Expr(_, p, e): &'a tast::Expr) {
        let as_lint = self.as_lint;
        match e {
            Expr_::Binop(b)
                if matches!(b.bop, Bop::Diff | Bop::Diff2 | Bop::Eqeqeq | Bop::Eqeq) =>
            {
                ensure_valid_equality_check(env, as_lint, p, &b.bop, &b.lhs, &b.rhs)
            }
            Expr_::Call(c) => match (&c.func, c.targs.as_slice()) {
                (Expr(_, _, Expr_::Id(id)), [Targ(tv1, _), Targ(tv2, _)])
                    if id.1 == sn::hh::CONTAINS =>
                {
                    ensure_valid_contains_check(env, as_lint, p, tv1, tv2)
                }
                (Expr(_, _, Expr_::Id(id)), [Targ(tk1, _), Targ(tk2, _), _])
                    if id.1 == sn::hh::CONTAINS_KEY =>
                {
                    ensure_valid_contains_key_check(env, as_lint, p, tk1, tk2)
                }
                _ => {}
            },
            _ => {}
        }
    }

    fn at_stmt(&mut self, env: &Env, Stmt(_, s): &'a tast::Stmt) {
        let as_lint = self.as_lint;
        match s {
            Stmt_::Switch(sw) => {
                let (scrutinee, cases, _default) = &**sw;
                let check_case = |Case(case, _): &tast::Case| {
                    let Expr(_, case_pos, _) = case;
                    ensure_valid_case_check(env, as_lint, case_pos, scrutinee, case)
                };
                cases.iter().for_each(check_case)
            }
            _ => {}
        }
    }
}

pub fn handler<'a>(as_lint: bool) -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler { as_lint })
}
