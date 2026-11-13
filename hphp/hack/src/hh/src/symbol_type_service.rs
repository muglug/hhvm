// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/symbol_type_service.ml`. See `hh/PORTING.md`.
//!
//! `Result_set` compares the positions only: the visitor collects the
//! results in a list, and [`generate_types`] sorts them by position and
//! keeps the first of each position.

use std::cmp::Ordering;

use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::code_actions::aast_reduce::SNode;
use crate::provider_context;
use crate::server_command_types::symbol_type::T;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;

/// `Result_set`'s `compare`
fn compare(a: &T, b: &T) -> Ordering {
    crate::pos::compare_pos(|x: &String, y: &String| x.as_bytes().cmp(y.as_bytes()), &a.pos, &b.pos)
}

type Acc = Vec<T>;

struct Visitor;

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
    aast_reduce::tast::tast_methods!('a, Acc; expr_, fun_, method_, class_var, expression_tree);

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Acc {
        let aast::Expr(ty, pos, expr_) = expr;
        let mut acc = match expr_ {
            aast::Expr_::Lvar(lid) | aast::Expr_::Dollardollar(lid) => vec![T {
                pos: crate::pos::to_relative_string(pos),
                type_: tast_env::print_ty(env, ty),
                ident_: crate::local_id::to_int(&lid.1),
            }],
            _ => vec![],
        };
        acc.extend(expr.srecurse(env, self));
        acc
    }

    fn visit_fun_param(&mut self, env: &mut Env, param: &'a tast::FunParam) -> Acc {
        let mut acc = {
            let ty = &param.annotation;
            vec![T {
                pos: crate::pos::to_relative_string(&param.pos),
                type_: tast_env::print_ty(env, ty),
                ident_: crate::local_id::to_int(&crate::local_id::make_unscoped(param.name.clone())),
            }]
        };
        acc.extend(param.srecurse(env, self));
        acc
    }
}

pub fn generate_types(ctx: &provider_context::T, tasts: &[&[tast::Def]]) -> Vec<T> {
    let all: Vec<T> = tasts
        .iter()
        .flat_map(|tast| aast_reduce::tast::go(&mut Visitor, ctx, tast))
        .collect();
    // `Result_set.elements` of the union
    let mut v = crate::rt::ocaml_list::stable_sort(all, compare);
    v.dedup_by(|b, a| compare(a, b) == Ordering::Equal);
    v
}
