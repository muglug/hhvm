// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `count_imprecise_types/count_imprecise_types.ml`. See
//! `hh/PORTING.md`.

use std::collections::BTreeMap;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::provider_context;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;
use crate::typing_defs_core;
use crate::typing_defs_core::Ty_;
use crate::yojson::safe as yojson;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Result {
    mixed_count: isize,
    nonnull_count: isize,
    dynamic_count: isize,
}

/// `S_map.t` of the results
pub type Results = BTreeMap<String, Result>;

pub fn json_of_results(results: &Results) -> yojson::T {
    let json_of_result = |(id, result): (&String, &Result)| {
        yojson::T::Assoc(vec![
            ("id".to_string(), yojson::T::String(id.clone())),
            ("mixed_count".to_string(), yojson::T::Int(result.mixed_count)),
            ("dynamic_count".to_string(), yojson::T::Int(result.dynamic_count)),
            ("nonnull_count".to_string(), yojson::T::Int(result.nonnull_count)),
        ])
    };
    yojson::T::List(results.iter().map(json_of_result).collect())
}

const ZERO: Result = Result {
    mixed_count: 0,
    nonnull_count: 0,
    dynamic_count: 0,
};

struct BadTypeVisitorPerDef;

impl<'a> Reducer<'a, IterParams, Result> for BadTypeVisitorPerDef {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Result> {
        self
    }
    fn zero(&mut self) -> Result {
        ZERO
    }
    fn plus(&mut self, r1: Result, r2: Result) -> Result {
        Result {
            mixed_count: r1.mixed_count + r2.mixed_count,
            nonnull_count: r1.nonnull_count + r2.nonnull_count,
            dynamic_count: r1.dynamic_count + r2.dynamic_count,
        }
    }
    aast_reduce::tast::tast_methods!('a, Result; expr_, fun_, method_, class_var, expression_tree);

    fn visit_ex(&mut self, _env: &mut Env, ty: &'a tast::Ty) -> Result {
        match typing_defs_core::get_node(ty) {
            Ty_::Tintersection(tyl) if tyl.is_empty() => Result { mixed_count: 1, ..ZERO },
            Ty_::Toption(ty) if matches!(typing_defs_core::get_node(ty), Ty_::Tnonnull) => {
                Result { mixed_count: 1, ..ZERO }
            }
            Ty_::Tdynamic(_) => Result {
                dynamic_count: 1,
                ..ZERO
            },
            Ty_::Tnonnull => Result {
                nonnull_count: 1,
                ..ZERO
            },
            _ => ZERO,
        }
    }
}

/// `S_map.union ~combine:(fun id _ _ -> failwith ("Clash at %s" ^ id))`
pub fn union(mut a: Results, b: Results, clash: &str) -> Results {
    for (id, result) in b {
        if a.contains_key(&id) {
            panic!("Failure(\"{}{}\")", clash, id)
        }
        a.insert(id, result);
    }
    a
}

struct BadTypeVisitor;

impl<'a> Reducer<'a, IterParams, Results> for BadTypeVisitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Results> {
        self
    }
    fn zero(&mut self) -> Results {
        Results::new()
    }
    fn plus(&mut self, a: Results, b: Results) -> Results {
        union(a, b, "Clash at %s")
    }
    aast_reduce::tast::tast_methods!('a, Results; expr_, fun_, class_var, expression_tree);

    fn visit_fun_def(&mut self, env: &mut Env, fun_def: &'a tast::FunDef) -> Results {
        let id = &fun_def.name.1;
        let result = BadTypeVisitorPerDef.visit_fun_def(env, fun_def);
        Results::from([(id.clone(), result)])
    }

    fn visit_method_(&mut self, env: &mut Env, method_def: &'a tast::Method_) -> Results {
        let mid = &method_def.name.1;
        let result = BadTypeVisitorPerDef.visit_method_(env, method_def);
        let cid = crate::tast_env::get_self_id(env).expect("Option.value_exn");
        let id = format!("{}::{}", cid, mid);
        Results::from([(id, result)])
    }
}

pub fn count(ctx: &provider_context::T, tast: &[tast::Def]) -> Results {
    aast_reduce::tast::go(&mut BadTypeVisitor, ctx, tast)
}
