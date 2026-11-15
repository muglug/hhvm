// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactor_sd/refactor_sd_walker.ml`.

use std::collections::BTreeMap;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Uop;

use super::refactor_sd_env;
use super::refactor_sd_types::*;
use crate::aast_names_utils as utils;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::typing_continuations as cont;
use crate::typing_defs_core::Ty_;

fn failwithpos(pos: &Pos, msg: String) -> ! {
    refactor_sd_exn(format!("{}: {}", crate::ast_show::show_pos(pos), msg))
}

fn redirect(env: &mut Env, entity_: Entity_) -> Entity_ {
    let var = refactor_sd_env::fresh_var();
    refactor_sd_env::add_constraint(env, Constraint_::Subset(entity_, var.clone()));
    var
}

fn assign(env: &mut Env, lhs: &tast::Expr, rhs: Entity) {
    let aast::Expr(_, pos, lval) = lhs;
    match lval {
        aast::Expr_::Lvar(lid) => refactor_sd_env::set_local(env, lid.1.clone(), rhs),
        aast::Expr_::ArrayGet(x) if matches!((x.0).2, aast::Expr_::Lvar(_)) => {
            let aast::Expr(vc_type, _, base) = &x.0;
            let lid = match base {
                aast::Expr_::Lvar(lid) => lid.1.clone(),
                _ => unreachable!(),
            };
            let entity = refactor_sd_env::get_local(env, &lid);
            let ty = tast_env::expand_type(&mut env.tast_env, vc_type.clone());
            let (_, ty_) = crate::typing_defs_core::deref(&ty);
            let class_name = match &ty_ {
                Ty_::Tclass(id, _, _) => Some(id.1.as_str()),
                _ => None,
            };
            match (entity, class_name) {
                (Some(entity_), Some(x)) if x == sn::collections::VEC || x == sn::collections::DICT => {
                    // Handle copy-on-write by creating a variable indirection
                    let var = redirect(env, entity_);
                    if let Some(rhs) = rhs {
                        refactor_sd_env::add_constraint(env, Constraint_::Subset(rhs, var.clone()))
                    }
                    refactor_sd_env::set_local(env, lid, Some(var))
                }
                (Some(entity_), Some(x)) if x == sn::collections::VECTOR => {
                    if let Some(rhs) = rhs {
                        refactor_sd_env::add_constraint(env, Constraint_::Subset(rhs, entity_.clone()))
                    }
                    refactor_sd_env::set_local(env, lid, Some(entity_))
                }
                (Some(_), _) => failwithpos(pos, format!("Unsupported lvalue: {}", utils::expr_name(lval))),
                (None, _) => {
                    // We might end up here as a result of deadcode, such as a dictionary
                    // assignment after an unconditional break in a loop. In this
                    // situation, it is not meaningful to report a candidate.
                }
            }
        }
        _ => failwithpos(pos, format!("Unsupported lvalue: {}", utils::expr_name(lval))),
    }
}

/// Create a join point entity. It is pretty much Option.marge except that
/// that function doesn't allow threading state (`env`) through
fn join(env: &mut Env, then_entity: Entity, else_entity: Entity) -> Entity {
    match (then_entity, else_entity) {
        (Some(then_entity_), Some(else_entity_)) => {
            let var = refactor_sd_env::fresh_var();
            refactor_sd_env::add_constraint(env, Constraint_::Subset(then_entity_, var.clone()));
            refactor_sd_env::add_constraint(env, Constraint_::Subset(else_entity_, var.clone()));
            Some(var)
        }
        (None, else_entity @ Some(_)) => else_entity,
        (then_entity, _) => then_entity,
    }
}

/// Handle copy-on-write by creating a variable indirection
fn introduction(env: &mut Env, pos: &Pos) -> Entity {
    let entity_ = Entity_::Literal(pos.clone());
    refactor_sd_env::add_constraint(env, Constraint_::Introduction(pos.clone()));
    let var = redirect(env, entity_);
    Some(var)
}

fn expr_(upcasted_info: &ElementInfo, env: &mut Env, expr: &tast::Expr) -> Entity {
    use aast::Expr_ as E;
    let aast::Expr(_ty, pos, e) = expr;
    let unsupported = || -> ! { failwithpos(pos, format!("Unsupported expression: {}", utils::expr_name(e))) };
    match e {
        E::Int(_) | E::Float(_) | E::String(_) | E::Null | E::True | E::False => None,
        // Until interprocedural analaysis has been implemented, this is all incomplete.
        E::Id(_) => None,
        E::Lvar(lid) => refactor_sd_env::get_local(env, &lid.1),
        E::Unop(x)
            if matches!(
                x.0,
                Uop::Utild
                    | Uop::Unot
                    | Uop::Uplus
                    | Uop::Uminus
                    | Uop::Uincr
                    | Uop::Udecr
                    | Uop::Upincr
                    | Uop::Updecr
                    | Uop::Usilence
            ) =>
        {
            // unary operations won't return function pointrs, so we discard the entity.
            let _ = expr_(upcasted_info, env, &x.1);
            None
        }
        E::Assign(x) if x.1.is_none() => {
            let (e1, _, e2) = &**x;
            let entity_rhs = expr_(upcasted_info, env, e2);
            assign(env, e1, entity_rhs);
            None
        }
        E::Binop(x) if matches!(x.bop, Bop::QuestionQuestion) => {
            let entity1 = expr_(upcasted_info, env, &x.lhs);
            let entity2 = expr_(upcasted_info, env, &x.rhs);
            join(env, entity1, entity2)
        }
        E::Assign(x) if matches!(x.1, Some(Bop::QuestionQuestion)) => {
            let (e1, _, e2) = &**x;
            let entity1 = expr_(upcasted_info, env, e1);
            let entity2 = expr_(upcasted_info, env, e2);
            let entity_rhs = join(env, entity1, entity2);
            assign(env, e1, entity_rhs);
            None
        }
        E::Binop(x)
            if matches!(
                x.bop,
                Bop::Plus
                    | Bop::Minus
                    | Bop::Star
                    | Bop::Slash
                    | Bop::Eqeq
                    | Bop::Eqeqeq
                    | Bop::Starstar
                    | Bop::Diff
                    | Bop::Diff2
                    | Bop::Ampamp
                    | Bop::Barbar
                    | Bop::Lt
                    | Bop::Lte
                    | Bop::Gt
                    | Bop::Gte
                    | Bop::Dot
                    | Bop::Amp
                    | Bop::Bar
                    | Bop::Ltlt
                    | Bop::Gtgt
                    | Bop::Percent
                    | Bop::Xor
                    | Bop::Cmp
            ) =>
        {
            // most binary operations won't return function pointers, so we discard the entity.
            let _ = expr_(upcasted_info, env, &x.lhs);
            let _ = expr_(upcasted_info, env, &x.rhs);
            None
        }
        E::KeyValCollection(x) => match (x.0).1 {
            aast::KvcKind::Dict => {
                let var = refactor_sd_env::fresh_var();
                for aast::Field(_e_key, e_val) in &x.2 {
                    if let Some(entity_rhs_) = expr_(upcasted_info, env, e_val) {
                        refactor_sd_env::add_constraint(env, Constraint_::Subset(entity_rhs_, var.clone()))
                    }
                }
                Some(var)
            }
            _ => unsupported(),
        },
        E::ValCollection(x) => match (x.0).1 {
            aast::VcKind::Vector | aast::VcKind::Vec => {
                let var = refactor_sd_env::fresh_var();
                for e_inner in &x.2 {
                    if let Some(entity_rhs_) = expr_(upcasted_info, env, e_inner) {
                        refactor_sd_env::add_constraint(env, Constraint_::Subset(entity_rhs_, var.clone()))
                    }
                }
                Some(var)
            }
            _ => unsupported(),
        },
        E::ArrayGet(x) if matches!((x.0).2, E::Lvar(_)) && x.1.is_some() => {
            let (base, ix) = &**x;
            let entity_exp = expr_(upcasted_info, env, base);
            let _entity_ix = expr_(upcasted_info, env, ix.as_ref().unwrap());
            entity_exp
        }
        E::Upcast(x) => {
            let entity = expr_(upcasted_info, env, &x.0);
            if let Some(entity) = &entity {
                refactor_sd_env::add_constraint(env, Constraint_::Upcast(entity.clone(), pos.clone()))
            }
            entity
        }
        E::Call(call) => {
            // Until interprocedural analaysis has been implemented, this is all incomplete.
            let entity = expr_(upcasted_info, env, &call.func);
            for arg in &call.args {
                let _ = expr_(upcasted_info, env, crate::aast_utils::arg_to_expr(arg));
            }
            if let Some(entity) = entity {
                let location = Entity_::Literal(pos.clone());
                refactor_sd_env::add_constraint(env, Constraint_::Subset(entity, location));
                refactor_sd_env::add_constraint(env, Constraint_::Called(pos.clone()))
            }
            None
        }
        E::ObjGet(x) => {
            let (e_obj, e_meth, _, _) = &**x;
            let entity_obj = expr_(upcasted_info, env, e_obj);
            let _entity_meth = expr_(upcasted_info, env, e_meth);
            match entity_obj {
                Some(entity) => {
                    let location = Entity_::Literal(pos.clone());
                    refactor_sd_env::add_constraint(env, Constraint_::Subset(entity.clone(), location));
                    refactor_sd_env::add_constraint(env, Constraint_::Called(pos.clone()));
                    Some(entity)
                }
                None => None,
            }
        }
        E::FunctionPointer(x) if matches!(x.0, aast::FunctionPtrId::FPId(_)) => {
            let id = match &x.0 {
                aast::FunctionPtrId::FPId(id) => &id.1,
                _ => unreachable!(),
            };
            if &upcasted_info.element_name == id {
                introduction(env, pos)
            } else {
                None
            }
        }
        E::New(x) if matches!((x.0).2, aast::ClassId_::CI(_)) => {
            let (aast::ClassId(_, _, cid), _, arg_list, e, _) = &**x;
            let id = match cid {
                aast::ClassId_::CI(id) => &id.1,
                _ => unreachable!(),
            };
            if &upcasted_info.element_name == id {
                for arg in arg_list {
                    let _entity_rhs = expr_(upcasted_info, env, crate::aast_utils::arg_to_expr(arg));
                }
                if let Some(e) = e {
                    let _ = expr_(upcasted_info, env, e);
                }
                introduction(env, pos)
            } else {
                None
            }
        }
        E::ClassConst(x) if matches!((x.0).2, aast::ClassId_::CI(_)) => {
            let (aast::ClassId(_, _, cid), (_, method_id)) = &**x;
            let id = match cid {
                aast::ClassId_::CI(id) => &id.1,
                _ => unreachable!(),
            };
            let equals_method_id = method_id == "class";
            if &upcasted_info.element_name == id && equals_method_id {
                introduction(env, pos)
            } else {
                None
            }
        }
        // Eventually, we should be able to track method pointers inside a class, i.e.
        // also track the following expression with A.CIexpr (_, _, This).
        E::ClassConst(x) if matches!((x.0).2, aast::ClassId_::CIexpr(_)) => match &(x.0).2 {
            aast::ClassId_::CIexpr(e_obj) => expr_(upcasted_info, env, e_obj),
            _ => unreachable!(),
        },
        E::Eif(x) if x.1.is_some() => {
            let (cond, then_expr, else_expr) = &**x;
            let _cond_entity = expr_(upcasted_info, env, cond);
            let parent_env = env.clone();
            let base_env = refactor_sd_env::reset_constraints(&parent_env);
            let mut then_env = base_env.clone();
            let then_entity = expr_(upcasted_info, &mut then_env, then_expr.as_ref().unwrap());
            let mut else_env = base_env;
            let else_entity = expr_(upcasted_info, &mut else_env, else_expr);
            *env = refactor_sd_env::union(parent_env, then_env, else_env);
            join(env, then_entity, else_entity)
        }
        E::Eif(x) => {
            let (cond, _, else_expr) = &**x;
            let cond_entity = expr_(upcasted_info, env, cond);
            let else_entity = expr_(upcasted_info, env, else_expr);
            join(env, cond_entity, else_entity)
        }
        E::Await(e) => expr_(upcasted_info, env, e),
        E::As(x) => expr_(upcasted_info, env, &x.expr),
        E::Is(x) => {
            // `is` expressions always evaluate to bools, so we discard the entity.
            let _ = expr_(upcasted_info, env, &x.0);
            None
        }
        _ => unsupported(),
    }
}

fn expr(upcasted_info: &ElementInfo, env: &mut Env, e: &tast::Expr) {
    let _ = expr_(upcasted_info, env, e);
}

fn switch(
    upcasted_info: &ElementInfo,
    parent_locals: &Lenv,
    env: &mut Env,
    cases: &[aast::Case<tast::Ty, tast::SavedEnv>],
    dfl: &Option<aast::DefaultCase<tast::Ty, tast::SavedEnv>>,
) {
    let initialize_next_cont = |env: &mut Env| {
        refactor_sd_env::restore_conts_from(env, parent_locals, &[cont::T::Next]);
        refactor_sd_env::update_next_from_conts(env, &[cont::T::Next, cont::T::Fallthrough]);
        refactor_sd_env::drop_cont(env, cont::T::Fallthrough)
    };
    for aast::Case(e, b) in cases {
        initialize_next_cont(env);
        expr(upcasted_info, env, e);
        block(upcasted_info, env, b)
    }
    if let Some(aast::DefaultCase(_, b)) = dfl {
        initialize_next_cont(env);
        block(upcasted_info, env, b)
    }
}

fn stmt(upcasted_info: &ElementInfo, env: &mut Env, s: &tast::Stmt) {
    use aast::Stmt_ as S;
    let aast::Stmt(pos, stmt) = s;
    match stmt {
        S::Expr(e) => expr(upcasted_info, env, e),
        S::Return(e) => {
            if let Some(e) = &**e {
                let _expr = expr_(upcasted_info, env, e);
            }
        }
        S::If(x) => {
            let (cond, then_bl, else_bl) = &**x;
            expr(upcasted_info, env, cond);
            let parent_env = env.clone();
            let base_env = refactor_sd_env::reset_constraints(&parent_env);
            let mut then_env = base_env.clone();
            block(upcasted_info, &mut then_env, then_bl);
            let mut else_env = base_env;
            block(upcasted_info, &mut else_env, else_bl);
            *env = refactor_sd_env::union(parent_env, then_env, else_env)
        }
        S::Switch(x) => {
            let (cond, cases, dfl) = &**x;
            expr(upcasted_info, env, cond);
            // NB: A 'continue' inside a 'switch' block is equivalent to a 'break'.
            // See the note in
            // http://php.net/manual/en/control-structures.continue.php
            refactor_sd_env::stash_and_do(env, &[cont::T::Continue, cont::T::Break], |env| {
                let parent_locals = env.lenv.clone();
                switch(upcasted_info, &parent_locals, env, cases, dfl);
                refactor_sd_env::update_next_from_conts(env, &[cont::T::Continue, cont::T::Break, cont::T::Next])
            })
        }
        S::Fallthrough => refactor_sd_env::move_and_merge_next_in_cont(env, cont::T::Fallthrough),
        S::Continue => refactor_sd_env::move_and_merge_next_in_cont(env, cont::T::Continue),
        S::Break => refactor_sd_env::move_and_merge_next_in_cont(env, cont::T::Break),
        S::While(x) => {
            let (aast::LoopCond(_, _, cond), bl) = &**x;
            refactor_sd_env::stash_and_do(env, &[cont::T::Continue, cont::T::Break], |env| {
                refactor_sd_env::save_and_merge_next_in_cont(env, cont::T::Continue);
                let env_before_iteration = env.clone();
                let env_after_iteration = {
                    let mut env = env.clone();
                    expr(upcasted_info, &mut env, cond);
                    block(upcasted_info, &mut env, bl);
                    env
                };
                *env = refactor_sd_env::loop_continuation(cont::T::Next, &env_before_iteration, env_after_iteration);
                refactor_sd_env::update_next_from_conts(env, &[cont::T::Continue, cont::T::Next]);
                expr(upcasted_info, env, cond);
                refactor_sd_env::update_next_from_conts(env, &[cont::T::Break, cont::T::Next])
            })
        }
        S::Noop | S::Markup(_) => {}
        _ => failwithpos(pos, format!("Unsupported statement: {}", utils::stmt_name(stmt))),
    }
}

fn block(upcasted_info: &ElementInfo, env: &mut Env, b: &tast::Block) {
    for s in &b.0 {
        stmt(upcasted_info, env, s)
    }
}

fn init_params(_tast_env: &tast_env::Env, _params: &[tast::FunParam]) -> (Vec<Constraint_>, LMap<Entity>) {
    (vec![], LMap::new())
}

pub fn callable(
    upcasted_info: &ElementInfo,
    tast_env: &tast_env::Env,
    params: &[tast::FunParam],
    body: &tast::FuncBody,
) -> Vec<Constraint_> {
    let (param_constraints, param_env) = init_params(tast_env, params);
    let mut env = refactor_sd_env::init(tast_env.clone(), param_constraints, param_env);
    block(upcasted_info, &mut env, &body.fb_ast);
    env.constraints
}

/// (`S_map.of_list`: of two bindings of a name, the last one.)
pub fn program(
    upcasted_info: &ElementInfo,
    ctx: &provider_context::T,
    tast: &[tast::Def],
) -> BTreeMap<String, Vec<Constraint_>> {
    let mut map = BTreeMap::new();
    for def in tast {
        let tast_env = tast_env::def_env(ctx, def);
        match def {
            aast::Def::Fun(fd) => {
                let id = fd.name.1.clone();
                map.insert(id, callable(upcasted_info, &tast_env, &fd.fun.params, &fd.fun.body));
            }
            aast::Def::Class(c) => {
                let class_name = &c.name.1;
                for m in &c.methods {
                    let id = format!("{}::{}", class_name, m.name.1);
                    map.insert(id, callable(upcasted_info, &tast_env, &m.params, &m.body));
                }
            }
            _ => panic!("Failure(\"A definition is not yet handled\")"),
        }
    }
    map
}
