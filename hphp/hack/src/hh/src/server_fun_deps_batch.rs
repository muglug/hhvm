// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_fun_deps_batch.ml`. See `hh/PORTING.md`.
//!
//! `Results` is a set: the visitor collects the occurrences in a list, and
//! `results_elements` sorts them and drops the duplicates.

use std::cmp::Ordering;

use naming_special_names_rust as sn;
use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::code_actions::aast_reduce::SNode;
use crate::nast;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::server_env;
use crate::server_rx_api_shared as shared;
use crate::symbol_definition as sd;
use crate::symbol_occurrence as so;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;
use crate::yojson::safe as yojson;

type Occ = so::T<Pos>;
type Results = Vec<Occ>;

/// `Symbol_occurrence.compare Relative_path.compare`
fn compare_occ(a: &Occ, b: &Occ) -> Ordering {
    so::compare(|x, y| relative_path::compare(x, y), a, b)
}

/// `Results.elements`
fn results_elements(v: Results) -> Results {
    let mut v = crate::rt::ocaml_list::stable_sort(v, compare_occ);
    v.dedup_by(|b, a| compare_occ(a, b) == Ordering::Equal);
    v
}

fn process_method_cid(n: (&Pos, &str), cid: &str) -> Results {
    vec![so::T {
        name: format!("{}::{}", cid, n.1),
        type_: so::Kind::Method(so::ReceiverClass::ClassName(cid.to_string()), n.1.to_string()),
        is_declaration: None,
        pos: n.0.clone(),
        affects_prod_build: true,
    }]
}

fn process_method(env: &Env, ty: &tast::Ty, n: (&Pos, &str)) -> Results {
    tast_env::get_class_ids(env, ty.clone())
        .iter()
        .flat_map(|cid| process_method_cid(n, cid))
        .collect()
}

fn process_function(id: (&Pos, &str)) -> Results {
    vec![so::T {
        name: id.1.to_string(),
        type_: so::Kind::Function,
        is_declaration: None,
        pos: id.0.clone(),
        affects_prod_build: true,
    }]
}

fn process_local(id: (&Pos, &str)) -> Results {
    vec![so::T {
        name: id.1.to_string(),
        type_: so::Kind::LocalVar,
        is_declaration: None,
        pos: id.0.clone(),
        affects_prod_build: true,
    }]
}

struct CollectInDecl;

impl<'a> Reducer<'a, IterParams, Results> for CollectInDecl {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Results> {
        self
    }
    fn zero(&mut self) -> Results {
        vec![]
    }
    fn plus(&mut self, mut a: Results, b: Results) -> Results {
        a.extend(b);
        a
    }
    aast_reduce::tast::tast_methods!('a, Results; fun_, method_, class_var, expression_tree);

    /// `on_Call` and `on_New` (and the `on_expr_` of `Tast_visitor.reduce`)
    fn visit_expr_(&mut self, env: &mut Env, e: &'a tast::Expr_) -> Results {
        let acc = match e {
            aast::Expr_::Call(call) => {
                let aast::Expr(_, _, expr_) = &call.func;
                match expr_ {
                    aast::Expr_::ObjGet(x) => match &**x {
                        (aast::Expr(ty, _, _), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                            process_method(env, ty, (&mid.0, &mid.1))
                        }
                        _ => vec![],
                    },
                    aast::Expr_::Id(id) => process_function((&id.0, &id.1)),
                    aast::Expr_::ClassConst(x) => {
                        let (aast::ClassId(ty, _, _), mid) = &**x;
                        process_method(env, ty, (&mid.0, &mid.1))
                    }
                    aast::Expr_::Lvar(lid) => process_local((&lid.0, crate::local_id::get_name(&lid.1))),
                    _ => vec![],
                }
            }
            aast::Expr_::New(x) => {
                let aast::ClassId(ty, p, _) = &x.0;
                process_method(env, ty, (p, sn::members::__CONSTRUCT))
            }
            _ => vec![],
        };
        let mut acc = acc;
        acc.extend(aast_reduce::tast::on_expr_(self, env, e));
        acc
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Results {
        let aast::Expr(_, _, expr_) = expr;
        let mut acc = match expr_ {
            aast::Expr_::MethodCaller(x) => {
                let (cid, mid) = &**x;
                let mut r = process_function((&cid.0, sn::autoimported_functions::METH_CALLER));
                r.extend(process_method_cid((&mid.0, &mid.1), &cid.1));
                r
            }
            aast::Expr_::FunctionPointer(x) => match &x.0 {
                aast::FunctionPtrId::FPId(id) => process_function((&id.0, &id.1)),
                aast::FunctionPtrId::FPClassConst(aast::ClassId(ty, _, _cid), mid) => {
                    process_method(env, ty, (&mid.0, &mid.1))
                }
            },
            _ => vec![],
        };
        acc.extend(expr.srecurse(env, self));
        acc
    }
}

fn result_to_string(result: Result<Option<Vec<Option<sd::T<Pos>>>>, String>, (fn_, line, char): &shared::PosT) -> String {
    let obj = yojson::T::Assoc(vec![
        ("position".to_string(), shared::pos_to_json(fn_, *line, *char)),
        match result {
            Ok(Some(refs)) => {
                let l = refs
                    .iter()
                    .map(|def_opt| match def_opt {
                        None => yojson::T::Null,
                        Some(def) => yojson::T::Assoc(vec![
                            ("name".to_string(), yojson::T::String(sd::full_name(def))),
                            (
                                "kind".to_string(),
                                yojson::T::String(sd::string_of_kind(&def.kind).to_string()),
                            ),
                            (
                                "position".to_string(),
                                crate::pos::json(&crate::pos::to_absolute(&def.pos)),
                            ),
                        ]),
                    })
                    .collect();
                ("deps".to_string(), yojson::T::List(l))
            }
            Ok(None) => (
                "error".to_string(),
                yojson::T::String("Function/method not found".to_string()),
            ),
            Err(e) => ("error".to_string(), yojson::T::String(e)),
        },
    ]);
    yojson::to_string(&obj)
}

fn remove_duplicates_except_none<A>(compare: impl Fn(&Option<A>, &Option<A>) -> Ordering, l: Vec<Option<A>>) -> Vec<Option<A>> {
    let mut accum: Vec<Option<A>> = vec![];
    let mut it = l.into_iter().peekable();
    while let Some(x1) = it.next() {
        match it.peek() {
            None => accum.push(x1),
            Some(x2) => {
                if !(x1.is_some() && compare(&x1, x2) == Ordering::Equal) {
                    accum.push(x1)
                }
            }
        }
    }
    accum
}

/// `Option.compare (Symbol_definition.compare Relative_path.compare)`
fn compare_def_opt(a: &Option<sd::T<Pos>>, b: &Option<sd::T<Pos>>) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => sd::compare(a, b),
    }
}

fn map_result(ctx: &provider_context::T, ast: &nast::Program, refs: Results) -> Vec<Option<sd::T<Pos>>> {
    let defs: Vec<Option<sd::T<Pos>>> = results_elements(refs)
        .iter()
        .map(|occ| crate::server_symbol_definition::go(ctx, Some(ast), occ))
        .collect();
    let defs = crate::rt::ocaml_list::stable_sort(defs, compare_def_opt);
    remove_duplicates_except_none(compare_def_opt, defs)
}

pub fn go(pos_list: Vec<(String, isize, isize)>, env: &server_env::Env) -> Vec<String> {
    let handlers: shared::Handlers<Results, Vec<Option<sd::T<Pos>>>, nast::Program> = shared::Handlers {
        result_to_string,
        walker: shared::Walker {
            plus: |mut a, b| {
                a.extend(b);
                a
            },
            on_method: |env, m| CollectInDecl.visit_method_(env, m),
            on_fun_def: |env, fd| CollectInDecl.visit_fun_def(env, fd),
        },
        get_state: |ctx, fn_| crate::ast_provider::get_ast(true, ctx, fn_),
        map_result,
    };
    shared::go(pos_list, env, &handlers)
}
