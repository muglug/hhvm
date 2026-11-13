// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `const_write_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Uop;

use crate::aast_utils;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::ValKind;
use crate::typing_defs::get_ce_const;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_set;
use crate::typing_utils;

/// Requires id to be a property
pub fn check_static_const_prop(tenv: &Env, class_: &cls::T, (pos, id): &aast::Pstring) {
    let scprop = typing_env::get_static_member(false, tenv, class_, id);
    if let Some(ce) = scprop {
        if get_ce_const(&ce) {
            typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::Mutating_const_property(
                    pos.clone(),
                )),
                tenv,
            )
        }
    }
}

/// Requires id to be a property
pub fn check_const_prop(
    env: &tast_env::Env,
    tenv: &Env,
    class_: &cls::T,
    (pos, id): &aast::Pstring,
    cty: &Ty,
) {
    let cprop = typing_env::get_prop(tenv, class_, id);
    if let Some(ce) = cprop {
        if get_ce_const(&ce) {
            if !(tast_env::get_inside_constructor(env)
                // expensive call behind short circuiting &&
                && tast_env::is_sub_type(env, &tast_env::get_self_ty_exn(env), cty))
            {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(typing_error::primary::T::Mutating_const_property(
                        pos.clone(),
                    )),
                    tenv,
                )
            }
        }
    }
}

pub fn check_prop(env: &tast_env::Env, c: &str, pid: &aast::Pstring, cty_opt: Option<&Ty>) {
    let class_ = tast_env::get_class(env, c);
    // Check we're in the LHS of an assignment, so we don't get confused
    // by $foo->bar(), which is an Obj_get but not a property.
    if matches!(tast_env::get_val_kind(env), ValKind::Lval) {
        match class_ {
            decl_entry::T::Found(class_) => match cty_opt {
                Some(cty) => check_const_prop(env, env, &class_, pid, cty),
                None => check_static_const_prop(env, &class_, pid),
            },
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
        }
    }
}

pub fn check_expr(env: &tast_env::Env, e: &tast::Expr) {
    let aast::Expr(_, _, e) = e;
    match e {
        aast::Expr_::ClassGet(cg) => {
            let (aast::ClassId(cty, _, _), pid, _) = &**cg;
            let mut env = env.clone();
            let cty = tast_env::expand_type(&mut env, cty.clone());
            let env = &env;
            match get_node(&cty) {
                Ty_::Tclass((_, c), _, _) => check_prop(env, c, pid, None),
                Ty_::Tdependent(_, bound) => match get_node(bound) {
                    Ty_::Tclass((_, c), _, _) => check_prop(env, c, pid, None),
                    _ => {}
                },
                Ty_::Tgeneric(name) => {
                    let upper_bounds = tast_env::get_upper_bounds(env, name);
                    let check_class = |bound: &Ty| match get_node(bound) {
                        Ty_::Tclass((_, c), _, _) => check_prop(env, c, pid, None),
                        _ => {}
                    };
                    typing_set::iter(check_class, &upper_bounds)
                }
                _ => {}
            }
        }
        aast::Expr_::ObjGet(og) if matches!(&og.1.2, aast::Expr_::Id(_)) => {
            let (aast::Expr(cty, _, _), aast::Expr(_, _, member), _, _) = &**og;
            let id: &aast::Sid = match member {
                aast::Expr_::Id(id) => id,
                _ => unreachable!(),
            };
            let id: aast::Pstring = (id.0.clone(), id.1.clone());
            let mut env = env.clone();
            let cty = tast_env::expand_type(&mut env, cty.clone());
            let env = &env;
            // we track already seen types to avoid infinite recursion
            // when dealing with Tgeneric arguments
            fn check_const_cty(
                env: &tast_env::Env,
                id: &aast::Pstring,
                seen: typing_set::T,
                cty: &Ty,
            ) -> typing_set::T {
                if typing_set::mem(cty, &seen) {
                    seen
                } else {
                    let seen = typing_set::add(cty.clone(), &seen);
                    match get_node(cty) {
                        Ty_::Tunion(ty_list) | Ty_::Tintersection(ty_list) => ty_list
                            .iter()
                            .fold(seen, |seen, ty| check_const_cty(env, id, seen, ty)),
                        Ty_::Tclass((_, c), _, _) => {
                            check_prop(env, c, id, Some(cty));
                            seen
                        }
                        Ty_::Tnewtype(name, tyl, _) => {
                            let bound = typing_utils::get_newtype_super(
                                &mut env.clone(),
                                get_reason(cty).clone(),
                                name,
                                tyl,
                            );
                            check_const_cty(env, id, seen, &bound)
                        }
                        Ty_::Tdependent(_, bound) => check_const_cty(env, id, seen, bound),
                        Ty_::Tgeneric(name) => {
                            let upper_bounds = tast_env::get_upper_bounds(env, name);
                            let check_class =
                                |cty: &Ty, seen: typing_set::T| check_const_cty(env, id, seen, cty);
                            typing_set::fold(check_class, &upper_bounds, seen)
                        }
                        _ => seen,
                    }
                }
            }
            let _ = check_const_cty(env, &id, typing_set::empty(), &cty);
        }
        aast::Expr_::Call(call)
            if matches!(&call.func.2, aast::Expr_::Id(id) if id.1 == sn::pseudo_functions::UNSET)
                && call.unpacked_arg.is_none() =>
        {
            fn check_unset_exp(env: &tast_env::Env, e: &tast::Expr) {
                match e {
                    aast::Expr(_, _, aast::Expr_::ArrayGet(ag)) if ag.1.is_some() => {
                        check_unset_exp(env, &ag.0)
                    }
                    _ => {
                        let mut env = env.clone();
                        tast_env::set_val_kind(&mut env, ValKind::Lval);
                        check_expr(&env, e)
                    }
                }
            }
            for arg in &call.args {
                check_unset_exp(env, aast_utils::arg_to_expr(arg))
            }
        }
        aast::Expr_::Unop(unop)
            if matches!(unop.0, Uop::Uincr | Uop::Upincr | Uop::Udecr | Uop::Updecr) =>
        {
            let mut env = env.clone();
            tast_env::set_val_kind(&mut env, ValKind::Lval);
            check_expr(&env, &unop.1)
        }
        _ => {}
    }
}

/// The object `handler`.
struct ConstWriteCheck;

impl<'a> tast_visitor::Handler<'a> for ConstWriteCheck {
    fn at_expr(&mut self, env: &tast_env::Env, e: &'a tast::Expr) {
        check_expr(env, e)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ConstWriteCheck)
}
