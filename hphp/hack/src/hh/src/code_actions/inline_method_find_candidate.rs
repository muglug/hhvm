// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `refactors/inline_method/inline_method_find_candidate.ml`. See
//! `hh/PORTING.md`.
//!
//! The visitor is a `Tast_visitor.iter`: an [`aast_reduce::Reducer`] of
//! `()`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs;

use super::aast_reduce;
use super::aast_reduce::Reducer;
use super::aast_reduce::SNode;
use super::inline_method_types as t;
use crate::aast_utils;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;

fn context_independent_default(e: &tast::Expr) -> bool {
    let aast::Expr(_, _, expr) = e;
    use aast::Expr_;
    match expr {
        Expr_::Null | Expr_::True | Expr_::False | Expr_::Int(_) | Expr_::Float(_) | Expr_::String(_) => true,
        Expr_::Unop(x) if matches!(x.0, ast_defs::Uop::Uplus | ast_defs::Uop::Uminus) => {
            context_independent_default(&x.1)
        }
        Expr_::ValCollection(x) if x.1.is_none() => x.2.iter().all(context_independent_default),
        Expr_::Tuple(exprs) => exprs.iter().all(context_independent_default),
        Expr_::KeyValCollection(x) if x.1.is_none() => {
            x.2.iter()
                .all(|aast::Field(key, value)| context_independent_default(key) && context_independent_default(value))
        }
        Expr_::Shape(fields) => fields.iter().all(|field| match field {
            aast::ShapeExprField::SFField(ast_defs::ShapeFieldName::SFlitStr(_), value) => {
                context_independent_default(value)
            }
            aast::ShapeExprField::SFField(
                ast_defs::ShapeFieldName::SFclassname(_) | ast_defs::ShapeFieldName::SFclassConst(..),
                _,
            )
            | aast::ShapeExprField::SFSplat(_) => false,
        }),
        _ => false,
    }
}

fn argument_evaluation_order(args: &[tast::Argument]) -> Vec<isize> {
    use aast::Expr_;
    let indexed: Vec<(isize, Option<&str>, bool)> = args
        .iter()
        .enumerate()
        .map(|(index, arg)| {
            let (name, aast::Expr(_, _, expr)) = match arg {
                aast::Argument::Anamed(ast_defs::Id(_, name), expr) => (Some(name.as_str()), expr),
                aast::Argument::Anormal(expr) | aast::Argument::Ainout(_, expr) => (None, expr),
            };
            let effectful = !matches!(
                expr,
                Expr_::Int(_)
                    | Expr_::Float(_)
                    | Expr_::String(_)
                    | Expr_::EnumClassLabel(_)
                    | Expr_::Null
                    | Expr_::False
                    | Expr_::True
                    | Expr_::Lvar(_)
                    | Expr_::Id(_)
                    | Expr_::PrefixedString(_)
            );
            (index as isize, name, effectful)
        })
        .collect();
    let named: Vec<isize> = {
        let named: Vec<(&str, isize)> = indexed
            .iter()
            .filter_map(|(index, name, _)| name.map(|name| (name, *index)))
            .collect();
        crate::rt::ocaml_list::stable_sort(named, |(left, _), (right, _)| left.as_bytes().cmp(right.as_bytes()))
            .into_iter()
            .map(|(_, index)| index)
            .collect()
    };
    let positional: Vec<isize> = indexed
        .iter()
        .filter_map(|(index, name, _)| if name.is_none() { Some(*index) } else { None })
        .collect();
    let effectful: Vec<isize> = indexed
        .iter()
        .filter_map(|(index, _, effectful)| if *effectful { Some(*index) } else { None })
        .collect();
    let effectful_set: BTreeSet<isize> = effectful.iter().copied().collect();
    // `take_until index effectful`: the elements up to `index` (included),
    // and the rest.
    fn take_until(index: isize, l: &[isize]) -> (&[isize], &[isize]) {
        match l.iter().position(|current| *current == index) {
            None => panic!("Failure(\"inline_method: missing effectful argument\")"),
            Some(i) => l.split_at(i + 1),
        }
    }
    // `order Int.Set.empty effectful (named @ positional)`
    let mut evaluated: BTreeSet<isize> = BTreeSet::new();
    let mut effectful: &[isize] = &effectful;
    let mut result = vec![];
    for index in named.into_iter().chain(positional) {
        if evaluated.contains(&index) {
            continue;
        } else if !effectful_set.contains(&index) {
            result.push(index)
        } else {
            let (before, rest) = take_until(index, effectful);
            effectful = rest;
            evaluated.extend(before.iter().copied());
            result.extend(before.iter().copied());
        }
    }
    result
}

fn method_info_create(m: &tast::Method_) -> t::MethodInfo {
    let is_private = match m.visibility {
        ast_defs::Visibility::Private => true,
        ast_defs::Visibility::Public
        | ast_defs::Visibility::Protected
        | ast_defs::Visibility::Internal
        | ast_defs::Visibility::ProtectedInternal => false,
    };
    let block = &m.body.fb_ast;
    let last_stmt_is_return = block
        .0
        .last()
        .map(|stmt| matches!(stmt, aast::Stmt(_, aast::Stmt_::Return(_))))
        .unwrap_or(false);
    let is_supported_param = |p: &tast::FunParam| -> bool {
        p.user_attributes.is_empty()
            && p.splat.is_none()
            && match p.callconv {
                ast_defs::ParamKind::Pinout(_) => false,
                ast_defs::ParamKind::Pnormal => true,
            }
    };
    let has_void_return = match &m.ret.1 {
        Some(aast::Hint(_, h)) => matches!(**h, aast::Hint_::Hprim(aast::Tprim::Tvoid)),
        None => false,
    };
    let all_params_are_supported = m.params.iter().all(is_supported_param);
    t::MethodInfo {
        method_pos: m.span.clone(),
        block: block.clone(),
        params: m
            .params
            .iter()
            .map(|p| {
                let default = aast_utils::get_param_default(p).and_then(|expr| {
                    if context_independent_default(expr) {
                        Some(aast_utils::get_expr_pos(expr))
                    } else {
                        None
                    }
                });
                t::ParamInfo {
                    name: p.name.clone(),
                    named: p.named.is_some(),
                    default,
                    variadic: aast_utils::is_param_variadic(p),
                }
            })
            .collect(),
        // only the following two are computed from the body
        var_names: vec![],
        return_cnt: 0,
        has_void_return,
        is_private,
        last_stmt_is_return,
        all_params_are_supported,
    }
}

struct Visitor<'s> {
    cursor: &'s Pos,
    method_use_counts: BTreeMap<String, isize>,
    method_infos: BTreeMap<String, t::MethodInfo>,
    target_class: Option<String>,
    current_method: Option<String>,
    stmt_pos: Pos,
    call_info: Option<t::CallInfo>,
}

impl Visitor<'_> {
    fn method_info_update(&mut self, method_name: &str, f: impl FnOnce(&mut t::MethodInfo)) {
        // method_infos map is guaranteed to have all method names in it
        // since we traverse methods after adding them to the map
        f(self.method_infos.get_mut(method_name).expect("Option.value_exn"))
    }

    fn on_call(
        &mut self,
        current_method: &str,
        expr_pos: &Pos,
        call_id_pos: &Pos,
        callee_name: &str,
        param_kind_arg_pairs: &[tast::Argument],
        unpacked_arg: &Option<tast::Expr>,
    ) {
        *self.method_use_counts.entry(callee_name.to_string()).or_insert(0) += 1;
        if crate::pos::contains(call_id_pos, self.cursor) && unpacked_arg.is_none() {
            let call_args: Option<Vec<t::CallArg>> = param_kind_arg_pairs
                .iter()
                .map(|arg| {
                    let pos = aast_utils::get_argument_pos(arg);
                    match arg {
                        aast::Argument::Anamed(ast_defs::Id(_, name), _) => Some(t::CallArg::Named(name.clone(), pos)),
                        aast::Argument::Anormal(_) => Some(t::CallArg::Positional(pos)),
                        aast::Argument::Ainout(..) => None,
                    }
                })
                .collect();
            self.call_info = call_args.map(|call_args| t::CallInfo {
                callee_name: callee_name.to_string(),
                call_stmt_pos: self.stmt_pos.clone(),
                caller_name: current_method.to_string(),
                call_pos: expr_pos.clone(),
                call_args,
                arg_evaluation_order: argument_evaluation_order(param_kind_arg_pairs),
            })
        }
    }
}

impl<'a> Reducer<'a, IterParams, ()> for Visitor<'_> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, ()> {
        self
    }
    fn zero(&mut self) {}
    fn plus(&mut self, _a: (), _b: ()) {}
    aast_reduce::tast::tast_methods!('a, (); method_, class_var, expression_tree);

    fn visit_stmt(&mut self, env: &mut Env, stmt: &'a tast::Stmt) {
        if self.current_method.is_some() {
            self.stmt_pos = stmt.0.clone()
        }
        stmt.srecurse(env, self)
    }

    /// `on_Return`
    fn visit_stmt_(&mut self, env: &mut Env, stmt_: &'a tast::Stmt_) {
        match stmt_ {
            aast::Stmt_::Return(_) => match self.current_method.clone() {
                Some(current_method) => {
                    self.method_info_update(&current_method, |method_info| method_info.return_cnt += 1);
                    stmt_.srecurse(env, self)
                }
                None => {}
            },
            _ => stmt_.srecurse(env, self),
        }
    }

    /// `on_Lvar` (and the `on_expr_` of `Tast_visitor.iter`)
    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) {
        match expr_ {
            aast::Expr_::Lvar(lvar) => match self.current_method.clone() {
                Some(current_method) => {
                    let var = crate::local_id::get_name(&lvar.1).to_string();
                    self.method_info_update(&current_method, |method_info| method_info.var_names.push(var));
                    expr_.srecurse(env, self)
                }
                None => {}
            },
            _ => aast_reduce::tast::on_expr_(self, env, expr_),
        }
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) {
        match self.current_method.clone() {
            Some(current_method) => {
                expr.srecurse(env, self);
                let aast::Expr(_, expr_pos, expr_) = expr;
                if let aast::Expr_::Call(call) = expr_ {
                    let aast::CallExpr {
                        func: aast::Expr(_, func_pos, func_),
                        args: param_kind_arg_pairs,
                        unpacked_arg,
                        ..
                    } = &**call;
                    match func_ {
                        aast::Expr_::ClassConst(cc)
                            if matches!((cc.0).2, aast::ClassId_::CIself | aast::ClassId_::CIstatic) =>
                        {
                            let callee_name = &(cc.1).1;
                            self.on_call(
                                &current_method,
                                expr_pos,
                                func_pos,
                                callee_name,
                                param_kind_arg_pairs,
                                unpacked_arg,
                            )
                        }
                        aast::Expr_::ObjGet(og) => {
                            let (aast::Expr(_, _, receiver), aast::Expr(_, _, member), _, _) = &**og;
                            if let (aast::Expr_::This, aast::Expr_::Id(id)) = (receiver, member) {
                                let ast_defs::Id(call_id_pos, callee_name) = &**id;
                                self.on_call(
                                    &current_method,
                                    expr_pos,
                                    call_id_pos,
                                    callee_name,
                                    param_kind_arg_pairs,
                                    unpacked_arg,
                                )
                            }
                        }
                        _ => {}
                    }
                }
            }
            None => {}
        }
    }

    fn visit_class_(&mut self, env: &mut Env, class_: &'a tast::Class_) {
        if crate::pos::contains(&class_.span, self.cursor) {
            self.target_class = Some(class_.name.1.clone());
            // `String.Map.of_alist`
            let mut method_infos_: BTreeMap<String, t::MethodInfo> = BTreeMap::new();
            let mut duplicate_key = false;
            for m in &class_.methods {
                if method_infos_.insert(m.name.1.clone(), method_info_create(m)).is_some() {
                    duplicate_key = true
                }
            }
            if !duplicate_key {
                self.method_infos = method_infos_;
                for m in &class_.methods {
                    self.current_method = Some(m.name.1.clone());
                    self.visit_method_(env, m)
                }
            }
        }
    }

    fn visit_fun_(&mut self, _env: &mut Env, _fun_: &'a tast::Fun_) {}
}

pub fn find_candidate(cursor: &Pos, entry: &Arc<provider_context::Entry>, ctx: &provider_context::T) -> Option<t::Candidate> {
    let mut visitor = Visitor {
        cursor,
        method_use_counts: BTreeMap::new(),
        method_infos: BTreeMap::new(),
        target_class: None,
        current_method: None,
        stmt_pos: Pos::NONE,
        call_info: None,
    };

    let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_quarantined(ctx, entry);
    aast_reduce::tast::go(&mut visitor, ctx, &tast.under_normal_assumptions);
    let Visitor {
        method_use_counts,
        method_infos,
        call_info,
        ..
    } = visitor;
    let call = call_info?;
    let callee = method_infos.get(&call.callee_name)?.clone();
    let caller = method_infos.get(&call.caller_name)?.clone();
    let is_inlineable = {
        let has_ok_returns = callee.return_cnt == 0 || (callee.return_cnt == 1 && callee.last_stmt_is_return);
        has_ok_returns && callee.is_private && callee.all_params_are_supported
    };
    let called_count = *method_use_counts.get(&call.callee_name)?;
    if called_count == 1 && is_inlineable {
        Some(t::Candidate { call, callee, caller })
    } else {
        None
    }
}
