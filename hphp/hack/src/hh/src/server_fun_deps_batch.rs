// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_fun_deps_batch.ml` (the
//! `FUN_DEPS_BATCH` command). See `hh/PORTING.md`.
//!
//! `Results` is a set ordered by `Symbol_occurrence.compare`, which
//! compares every field: unions keep the same elements in any order.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs;
use oxidized::pos::Pos;

use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::server_rx_api_shared;
use crate::symbol_definition;
use crate::symbol_occurrence;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::yojson::safe::T as Json;

type Occ = symbol_occurrence::T<Pos>;
type Def = symbol_definition::T<Pos>;

/// An element of `Results`.
#[derive(Clone)]
pub struct Elt(pub Occ);

impl Ord for Elt {
    fn cmp(&self, other: &Self) -> Ordering {
        symbol_occurrence::compare(crate::relative_path::compare, &self.0, &other.0)
    }
}

impl PartialOrd for Elt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Elt {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Elt {}

pub type Results = BTreeSet<Elt>;

fn singleton(occ: Occ) -> Results {
    let mut s = Results::new();
    s.insert(Elt(occ));
    s
}

fn process_method_cid((pos, n): (&Pos, &str), cid: &str) -> Results {
    singleton(symbol_occurrence::T {
        name: format!("{}::{}", cid, n),
        type_: symbol_occurrence::Kind::Method(symbol_occurrence::ReceiverClass::ClassName(cid.to_string()), n.to_string()),
        is_declaration: None,
        pos: pos.clone(),
        affects_prod_build: true,
    })
}

fn process_method(env: &Env, ty: &tast::Ty, n: (&Pos, &str)) -> Results {
    let mut acc = Results::new();
    for cid in tast_env::get_class_ids(env, ty.clone()) {
        acc.extend(process_method_cid(n, &cid));
    }
    acc
}

fn process_function((pos, name): (&Pos, &str)) -> Results {
    singleton(symbol_occurrence::T {
        name: name.to_string(),
        type_: symbol_occurrence::Kind::Function,
        is_declaration: None,
        pos: pos.clone(),
        affects_prod_build: true,
    })
}

fn process_local((pos, name): (&Pos, &str)) -> Results {
    singleton(symbol_occurrence::T {
        name: name.to_string(),
        type_: symbol_occurrence::Kind::LocalVar,
        is_declaration: None,
        pos: pos.clone(),
        affects_prod_build: true,
    })
}

/// `collect_in_decl`
pub struct CollectInDecl {
    acc: Results,
}

impl<'a> Reduce<'a> for CollectInDecl {
    type Acc = Results;

    fn zero(&self) -> Results {
        Results::new()
    }

    fn plus(&self, mut a: Results, b: Results) -> Results {
        a.extend(b);
        a
    }

    fn acc(&mut self) -> &mut Results {
        &mut self.acc
    }
}

impl<'a> Visitor<'a> for CollectInDecl {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; fun_, method_, class_var, expression_tree);

    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> Res {
        let acc = match expr_ {
            aast::Expr_::Call(call) => {
                let aast::Expr(_, _, func_expr_) = &call.func;
                match func_expr_ {
                    aast::Expr_::ObjGet(x) => match &**x {
                        (aast::Expr(ty, _, _), aast::Expr(_, _, aast::Expr_::Id(mid)), _, _) => {
                            process_method(env, ty, (&mid.0, &mid.1))
                        }
                        _ => Results::new(),
                    },
                    aast::Expr_::Id(id) => process_function((&id.0, &id.1)),
                    aast::Expr_::ClassConst(x) => {
                        let (aast::ClassId(ty, _, _), mid) = &**x;
                        process_method(env, ty, (&mid.0, &mid.1))
                    }
                    aast::Expr_::Lvar(lid) => process_local((&lid.0, crate::local_id::get_name(&lid.1))),
                    _ => Results::new(),
                }
            }
            aast::Expr_::New(x) => {
                let (aast::ClassId(ty, p, _), ..) = &**x;
                process_method(env, ty, (p, sn::members::__CONSTRUCT))
            }
            _ => Results::new(),
        };
        reduce::add(self, acc);
        reduce::on_expr_(self, env, expr_)
    }

    fn visit_expr(&mut self, env: &mut Env, expr: &'a tast::Expr) -> Res {
        let aast::Expr(_, _, expr_) = expr;
        let acc = match expr_ {
            aast::Expr_::MethodCaller(x) => {
                let (ast_defs::Id(p, cid), mid) = &**x;
                let mut acc = process_function((p, sn::autoimported_functions::METH_CALLER));
                acc.extend(process_method_cid((&mid.0, &mid.1), cid));
                acc
            }
            aast::Expr_::FunctionPointer(x) => match &x.0 {
                aast::FunctionPtrId::FPId(id) => process_function((&id.0, &id.1)),
                aast::FunctionPtrId::FPClassConst(aast::ClassId(ty, _, _), mid) => {
                    process_method(env, ty, (&mid.0, &mid.1))
                }
            },
            _ => Results::new(),
        };
        reduce::add(self, acc);
        expr.recurse(env, self)
    }
}

/// `Option.compare (Symbol_definition.compare Relative_path.compare)`: the
/// derived orders of `'a Symbol_definition.t` and its `kind`.
fn compare_def_opt(a: &Option<Def>, b: &Option<Def>) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => compare_def(a, b),
    }
}

fn compare_pos(a: &Pos, b: &Pos) -> Ordering {
    crate::pos::compare_pos(crate::relative_path::compare, a, b)
}

fn compare_list<A>(a: &[A], b: &[A], cmp: impl Fn(&A, &A) -> Ordering) -> Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let r = cmp(x, y);
        if r != Ordering::Equal {
            return r;
        }
    }
    a.len().cmp(&b.len())
}

fn compare_kind(a: &symbol_definition::Kind<Pos>, b: &symbol_definition::Kind<Pos>) -> Ordering {
    use symbol_definition::Kind::*;
    let tag = |k: &symbol_definition::Kind<Pos>| match k {
        Function => 0,
        Classish { .. } => 1,
        Member { .. } => 2,
        GlobalConst => 3,
        LocalVar => 4,
        TypeVar => 5,
        Param => 6,
        Typedef => 7,
        Module => 8,
    };
    match (a, b) {
        (
            Classish {
                classish_kind: k1,
                members: m1,
            },
            Classish {
                classish_kind: k2,
                members: m2,
            },
        ) => k1.cmp(k2).then_with(|| compare_list(m1, m2, compare_def)),
        (
            Member {
                member_kind: k1,
                class_name: c1,
            },
            Member {
                member_kind: k2,
                class_name: c2,
            },
        ) => k1.cmp(k2).then_with(|| c1.cmp(c2)),
        _ => tag(a).cmp(&tag(b)),
    }
}

fn compare_def(a: &Def, b: &Def) -> Ordering {
    compare_kind(&a.kind, &b.kind)
        .then_with(|| a.name.cmp(&b.name))
        .then_with(|| compare_pos(&a.pos, &b.pos))
        .then_with(|| compare_pos(&a.span, &b.span))
        .then_with(|| compare_list(&a.modifiers, &b.modifiers, |x, y| x.cmp(y)))
        .then_with(|| match (&a.params, &b.params) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(x), Some(y)) => compare_list(x, y, compare_def),
        })
        .then_with(|| a.docblock.cmp(&b.docblock))
        .then_with(|| a.detail.cmp(&b.detail))
}

pub fn result_to_string(result: Result<Option<Vec<Option<Def>>>, String>, (fn_, line, char): &server_rx_api_shared::Pos) -> String {
    let field = match result {
        Ok(Some(refs)) => (
            "deps".to_string(),
            Json::List(
                refs.iter()
                    .map(|def_opt| match def_opt {
                        None => Json::Null,
                        Some(def) => Json::Assoc(vec![
                            ("name".to_string(), Json::String(symbol_definition::full_name(def))),
                            (
                                "kind".to_string(),
                                Json::String(symbol_definition::string_of_kind(&def.kind).to_string()),
                            ),
                            ("position".to_string(), crate::pos::json(&crate::pos::to_absolute(&def.pos))),
                        ]),
                    })
                    .collect(),
            ),
        ),
        Ok(None) => ("error".to_string(), Json::String("Function/method not found".to_string())),
        Err(e) => ("error".to_string(), Json::String(e)),
    };
    let obj = Json::Assoc(vec![
        ("position".to_string(), server_rx_api_shared::pos_to_json(fn_, *line, *char)),
        field,
    ]);
    crate::yojson::safe::to_string(&obj)
}

fn remove_duplicates_except_none(l: Vec<Option<Def>>) -> Vec<Option<Def>> {
    let mut res: Vec<Option<Def>> = vec![];
    let mut it = l.into_iter().peekable();
    while let Some(x1) = it.next() {
        match it.peek() {
            Some(x2) if x1.is_some() && compare_def_opt(&x1, x2) == Ordering::Equal => {}
            _ => res.push(x1),
        }
    }
    res
}

pub struct FunDepsHandlers;

impl server_rx_api_shared::Handlers for FunDepsHandlers {
    const JOB_NAME: &'static str = "Server_fun_deps_batch.helper";
    fn make() -> Self {
        FunDepsHandlers
    }
    type A = Results;
    type R = Vec<Option<Def>>;
    type S = oxidized::nast::Program;

    fn result_to_string(&self, result: Result<Option<Self::R>, String>, pos: &server_rx_api_shared::Pos) -> String {
        result_to_string(result, pos)
    }

    fn plus(&self, mut a: Results, b: Results) -> Results {
        a.extend(b);
        a
    }

    fn on_method(&self, env: &mut Env, m: &tast::Method_) -> Results {
        let mut v = CollectInDecl { acc: Results::new() };
        let (_, r) = reduce::result(&mut v, |v| v.visit_method_(env, m));
        r
    }

    fn on_fun_def(&self, env: &mut Env, fd: &tast::FunDef) -> Results {
        let mut v = CollectInDecl { acc: Results::new() };
        let (_, r) = reduce::result(&mut v, |v| v.visit_fun_def(env, fd));
        r
    }

    fn get_state(&self, ctx: &provider_context::T, fn_: &RelativePath) -> Self::S {
        crate::ast_provider::get_ast(true, ctx, fn_)
    }

    fn map_result(&self, ctx: &provider_context::T, ast: &Self::S, refs: Results) -> Self::R {
        let defs: Vec<Option<Def>> = refs
            .into_iter()
            .map(|Elt(occ)| crate::server_symbol_definition::go(ctx, Some(ast), &occ))
            .collect();
        let defs = crate::rt::ocaml_list::stable_sort(defs, compare_def_opt);
        remove_duplicates_except_none(defs)
    }
}

/// Entry Point
pub fn go(workers: Option<usize>, pos_list: &[server_rx_api_shared::Spos], env: &crate::server_env::Env) -> Vec<String> {
    server_rx_api_shared::go(workers, pos_list, env, &FunDepsHandlers)
}
