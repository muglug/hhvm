// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/class_pointer_check.ml`. See `hh/PORTING.md`.
//!
//! A place to consolidate some static class pointer checks before inference
//! takes care of them all.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;

use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_class_pointers as class_pointer;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::get_node;
use crate::typing_print;

/// Report [C::class] in [e], or anywhere in a vec, dict, tuple or shape literal
/// [e], when [e] is compared with a value of [other_ty] that may hold a string:
/// HHVM converts the class pointer to its name there, so [nameof C] says what
/// is meant.
fn check_compared_class_consts(env: &tast_env::Env, other_ty: &Ty, e: &tast::Expr) {
    // `lazy (snd (ClassPointer.may_hold_string env other_ty))`: the
    // environment it returns is dropped.
    let may_hold_string: std::cell::OnceCell<bool> = std::cell::OnceCell::new();
    let force = || {
        *may_hold_string
            .get_or_init(|| class_pointer::may_hold_string(None, &mut env.clone(), other_ty))
    };
    fn check(env: &tast_env::Env, force: &dyn Fn() -> bool, e: &tast::Expr) {
        let aast::Expr(_, pos, e_) = e;
        match e_ {
            aast::Expr_::ClassConst(cc) if cc.1.1 == sn::members::M_CLASS => {
                let aast::ClassId(_, _, cid_) = &cc.0;
                match cid_ {
                    aast::ClassId_::CIreified(_) | aast::ClassId_::CIexpr(_) => {}
                    aast::ClassId_::CIparent
                    | aast::ClassId_::CIself
                    | aast::ClassId_::CIstatic
                    | aast::ClassId_::CI(_) => {
                        if force() {
                            class_pointer::error_at_cls_const_expr(
                                env,
                                pos.clone(),
                                class_pointer::string_of_class_id_(cid_),
                            )
                        }
                    }
                }
            }
            // Keys of dicts and elements of keysets are reported as array keys
            aast::Expr_::ValCollection(vc)
                if matches!(
                    (vc.0).1,
                    aast::VcKind::Vec | aast::VcKind::Vector | aast::VcKind::ImmVector
                ) =>
            {
                for e in &vc.2 {
                    check(env, force, e)
                }
            }
            aast::Expr_::Tuple(exprs) => {
                for e in exprs {
                    check(env, force, e)
                }
            }
            aast::Expr_::KeyValCollection(kvc) => {
                for aast::Field(_key, value) in &kvc.2 {
                    check(env, force, value)
                }
            }
            aast::Expr_::Shape(fields) => {
                for field in fields {
                    match field {
                        aast::ShapeExprField::SFField(_, e) | aast::ShapeExprField::SFSplat(e) => {
                            check(env, force, e)
                        }
                    }
                }
            }
            _ => {}
        }
    }
    check(env, &force, e)
}

/// The object `handler`.
struct ClassPointerCheck;

impl<'a> tast_visitor::Handler<'a> for ClassPointerCheck {
    fn at_class_const(&mut self, env: &tast_env::Env, cc: &'a tast::ClassConst) {
        match &cc.kind {
            aast::ClassConstKind::CCConcrete(aast::Expr(_ty, pos, aast::Expr_::ClassConst(cc)))
                if cc.1.1 == sn::members::M_CLASS =>
            {
                let aast::ClassId(_cty, _cpos, cid_) = &cc.0;
                match tast_env::get_self_id(env) {
                    Some(e) if tast_env::is_enum(env, &e) => {
                        class_pointer::error_at_cls_const_expr(
                            env,
                            pos.clone(),
                            class_pointer::string_of_class_id_(cid_),
                        )
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        let error = |e: &tast::Expr| match e {
            aast::Expr(_ty, pos, aast::Expr_::ClassConst(cc)) if cc.1.1 == sn::members::M_CLASS => {
                let aast::ClassId(_cty, _cpos, cid_) = &cc.0;
                class_pointer::error_at_cls_const_expr(
                    env,
                    pos.clone(),
                    class_pointer::string_of_class_id_(cid_),
                )
            }
            aast::Expr(ty, pos, _) => {
                let ty_str = typing_print::error(None, env, ty);
                match get_node(ty) {
                    Ty_::TclassPtr(_) if env.genv.tcopt.class_pointer_ban_class_array_key => {
                        class_pointer::error_at_cls_ptr_type(env, pos.clone(), ty_str)
                    }
                    _ => {}
                }
            }
        };
        match &e.2 {
            // $d[C::class]
            aast::Expr_::ArrayGet(ag) if ag.1.is_some() => error(ag.1.as_ref().unwrap()),
            // dict[C::class => ...]
            aast::Expr_::KeyValCollection(kvc) => {
                let (_, _, fields) = &**kvc;
                for aast::Field(key, _val) in fields {
                    error(key)
                }
            }
            // keyset[C::class]
            aast::Expr_::ValCollection(vc)
                if matches!(
                    (vc.0).1,
                    aast::VcKind::Set | aast::VcKind::ImmSet | aast::VcKind::Keyset
                ) =>
            {
                let (_, _, exprs) = &**vc;
                for e in exprs {
                    error(e)
                }
            }
            // $s === C::class
            aast::Expr_::Binop(binop)
                if matches!(
                    binop.bop,
                    ast_defs::Bop::Eqeq
                        | ast_defs::Bop::Eqeqeq
                        | ast_defs::Bop::Diff
                        | ast_defs::Bop::Diff2
                ) =>
            {
                let lhs = &binop.lhs;
                let rhs = &binop.rhs;
                check_compared_class_consts(env, &rhs.0, lhs);
                check_compared_class_consts(env, &lhs.0, rhs)
            }
            _ => {}
        }
    }

    // switch ($s) { case C::class: ... } compares with ==
    fn at_stmt(&mut self, env: &tast_env::Env, stmt: &'a tast::Stmt) {
        match &stmt.1 {
            aast::Stmt_::Switch(switch) => {
                let (scrutinee, cases, _) = &**switch;
                for aast::Case(case, _) in cases {
                    check_compared_class_consts(env, &scrutinee.0, case)
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassPointerCheck)
}
