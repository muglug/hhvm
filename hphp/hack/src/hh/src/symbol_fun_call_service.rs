// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/symbol_fun_call_service.ml`. See `hh/PORTING.md`.
//!
//! `Result_set` is a set whose union is associative and commutative: the
//! visitor collects the calls in a list, and [`result_set_elements`] sorts
//! them and drops the duplicates.

use std::cmp::Ordering;

use naming_special_names_rust as sn;
use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::code_actions::aast_reduce::SNode;
use crate::pos::Pos;
use crate::provider_context;
use crate::server_command_types::symbol_info_service::SymbolFunCall;
use crate::server_command_types::symbol_info_service::TargetType;
use crate::server_command_types::symbol_info_service::compare_target_type;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;

/// `Result_set`'s `compare`
fn compare(a: &SymbolFunCall, b: &SymbolFunCall) -> Ordering {
    // Descending order, since SymbolInfoService.format_result uses rev_append
    // and will reverse our sorted result list.
    crate::pos::compare_pos(|x: &String, y: &String| x.as_bytes().cmp(y.as_bytes()), &b.pos, &a.pos)
        .then_with(|| b.name.as_bytes().cmp(a.name.as_bytes()))
        .then_with(|| compare_target_type(b.type_, a.type_))
        .then_with(|| b.caller.as_bytes().cmp(a.caller.as_bytes()))
}

/// `Result_set.elements`
fn result_set_elements(v: Vec<SymbolFunCall>) -> Vec<SymbolFunCall> {
    let mut v = crate::rt::ocaml_list::stable_sort(v, compare);
    v.dedup_by(|b, a| compare(a, b) == Ordering::Equal);
    v
}

fn combine_name(cur_class: Option<&str>, cur_caller: Option<&str>) -> String {
    match (cur_class, cur_caller) {
        (_, None) => String::new(), // Top-level function call
        (None, Some(f)) => f.to_string(),
        (Some(c), Some(f)) => format!("{}::{}", c, f),
    }
}

fn is_pseudofunction(name: &str) -> bool {
    [sn::pseudo_functions::ISSET, sn::pseudo_functions::UNSET].contains(&name)
}

type Acc = Vec<SymbolFunCall>;

struct Visitor {
    cur_caller: Option<String>,
}

impl Visitor {
    fn fun_call(&mut self, env: &Env, target_type: TargetType, name: &str, pos: &Pos) -> Acc {
        if is_pseudofunction(name) {
            vec![]
        } else {
            let name = crate::utils::strip_ns(name);
            if name == sn::pre_namespaced_functions::ECHO {
                vec![]
            } else {
                let cur_class = tast_env::get_self_id(env).map(|c| crate::utils::strip_ns(&c).to_string());
                vec![SymbolFunCall {
                    name: name.to_string(),
                    type_: target_type,
                    pos: crate::pos::to_relative_string(pos),
                    caller: combine_name(cur_class.as_deref(), self.cur_caller.as_deref()),
                }]
            }
        }
    }

    fn method_call(&mut self, env: &Env, target_type: TargetType, class_name: &str, method_id: (&Pos, &str)) -> Acc {
        let (pos, method_name) = method_id;
        let method_fullname = combine_name(Some(class_name), Some(method_name));
        self.fun_call(env, target_type, &method_fullname, pos)
    }

    fn method_calls(&mut self, env: &Env, target_type: TargetType, ty: &tast::Ty, mid: (&Pos, &str)) -> Acc {
        let mut acc = vec![];
        for cid in tast_env::get_class_ids(env, ty.clone()) {
            acc.extend(self.method_call(env, target_type, &cid, mid))
        }
        acc
    }
}

impl<'a> Reducer<'a, IterParams, Acc> for Visitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Acc> {
        self
    }
    fn zero(&mut self) -> Acc {
        vec![]
    }
    fn plus(&mut self, mut a: Acc, b: Acc) -> Acc {
        a.extend(b);
        a
    }
    aast_reduce::tast::tast_methods!('a, Acc; fun_, class_var, expression_tree);

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Acc {
        let name = &fd.name.1;
        self.cur_caller = Some(crate::utils::strip_ns(name).to_string());
        let acc = fd.srecurse(env, self);
        self.cur_caller = None;
        acc
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Acc {
        self.cur_caller = Some(m.name.1.clone());
        let acc = aast_reduce::tast::on_method_(self, env, m);
        self.cur_caller = None;
        acc
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Acc {
        let aast::Expr(ty, pos, expr_) = expr;
        let acc = match expr_ {
            aast::Expr_::New(_) => {
                let mid = (pos, sn::members::__CONSTRUCT);
                self.method_calls(env, TargetType::Constructor, ty, mid)
            }
            aast::Expr_::MethodCaller(x) => {
                let (cid, mid) = &**x;
                self.method_call(env, TargetType::Method, &cid.1, (&mid.0, &mid.1))
            }
            _ => vec![],
        };
        let special_fun_acc = match expr_ {
            aast::Expr_::MethodCaller(_) => {
                self.fun_call(env, TargetType::Function, sn::autoimported_functions::METH_CALLER, pos)
            }
            _ => vec![],
        };
        let mut r = special_fun_acc;
        r.extend(acc);
        r.extend(expr.srecurse(env, self));
        r
    }

    /// `on_Call` (and the `on_expr_` of `Tast_visitor.reduce`)
    fn visit_expr_(&mut self, env: &mut Env, e: &'a tast::Expr_) -> Acc {
        match e {
            aast::Expr_::Call(call) => {
                let aast::Expr(_, _, expr_) = &call.func;
                let target_type_of = |mid: &str| {
                    if mid == sn::members::__CONSTRUCT {
                        TargetType::Constructor
                    } else {
                        TargetType::Method
                    }
                };
                let mut acc = match expr_ {
                    aast::Expr_::Id(id) => self.fun_call(env, TargetType::Function, &id.1, &id.0),
                    aast::Expr_::ClassConst(x) => {
                        let (aast::ClassId(ty, _, _), mid) = &**x;
                        self.method_calls(env, target_type_of(&mid.1), ty, (&mid.0, &mid.1))
                    }
                    aast::Expr_::ObjGet(x) => match &**x {
                        (aast::Expr(ty, _, _), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                            self.method_calls(env, target_type_of(&mid.1), ty, (&mid.0, &mid.1))
                        }
                        _ => vec![],
                    },
                    _ => vec![],
                };
                acc.extend(aast_reduce::tast::on_expr_(self, env, e));
                acc
            }
            _ => aast_reduce::tast::on_expr_(self, env, e),
        }
    }
}

pub fn find_fun_calls(ctx: &provider_context::T, tasts: &[&[tast::Def]]) -> Vec<SymbolFunCall> {
    tasts
        .iter()
        .flat_map(|x| {
            let mut visitor = Visitor { cur_caller: None };
            result_set_elements(aast_reduce::tast::go(&mut visitor, ctx, x))
        })
        .collect()
}
