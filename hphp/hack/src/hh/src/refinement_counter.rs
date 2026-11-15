// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/service/refinement_counter.ml`. See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;
use crate::typechecker_options::TypecheckerOptions;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Number of occurrences of a legacy refinement kind
    count: isize,
    /// The set of positions (stored as a string), where the refinement occurs.
    /// This field value is depended on the log level:
    ///   refinement_counter = 3: Include all positions
    ///   refinement_counter = 2: Include all positions, except for class refinements
    ///   otherwise: Do not include positions (will be S_set.empty)
    positions: BTreeSet<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct T {
    legacy_refinements: BTreeMap<String, Summary>,
    new_refinements: isize,
    total_refinements: isize,
}

pub fn yojson_of_t(t: &T) -> yojson::T {
    let yojson_of_summary = |s: &Summary| {
        yojson::T::Assoc(vec![
            ("count".to_string(), yojson::T::Int(s.count)),
            (
                "positions".to_string(),
                yojson::T::List(s.positions.iter().map(|p| yojson::T::String(p.clone())).collect()),
            ),
        ])
    };
    yojson::T::Assoc(vec![
        (
            "legacy_refinements".to_string(),
            yojson::T::Assoc(
                t.legacy_refinements
                    .iter()
                    .map(|(k, s)| (k.clone(), yojson_of_summary(s)))
                    .collect(),
            ),
        ),
        ("new_refinements".to_string(), yojson::T::Int(t.new_refinements)),
        ("total_refinements".to_string(), yojson::T::Int(t.total_refinements)),
    ])
}

mod summary {
    use super::*;

    pub fn zero() -> T {
        T::default()
    }

    pub fn plus(mut a: T, b: T) -> T {
        for (k, c_) in b.legacy_refinements {
            let merged = match a.legacy_refinements.remove(&k) {
                Some(mut c) => {
                    c.count += c_.count;
                    c.positions.extend(c_.positions);
                    c
                }
                None => c_,
            };
            a.legacy_refinements.insert(k, merged);
        }
        a.new_refinements += b.new_refinements;
        a.total_refinements += b.total_refinements;
        a
    }

    pub fn legacy_refinement(err: String, pos_opt: Option<&Pos>) -> T {
        T {
            legacy_refinements: BTreeMap::from([(
                err,
                Summary {
                    count: 1,
                    positions: match pos_opt {
                        None => BTreeSet::new(),
                        Some(pos) => BTreeSet::from([crate::pos::string(&crate::pos::to_relative_string(pos))]),
                    },
                },
            )]),
            new_refinements: 0,
            total_refinements: 1,
        }
    }

    pub fn new_refinement() -> T {
        T {
            legacy_refinements: BTreeMap::new(),
            new_refinements: 1,
            total_refinements: 1,
        }
    }
}

struct Visitor;

impl<'a> Reducer<'a, IterParams, T> for Visitor {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, T> {
        self
    }
    fn zero(&mut self) -> T {
        summary::zero()
    }
    fn plus(&mut self, a: T, b: T) -> T {
        summary::plus(a, b)
    }
    aast_reduce::tast::tast_methods!('a, T; fun_, method_, class_var, expression_tree);

    /// `on_Is` (and the `on_expr_` of `Tast_visitor.reduce`)
    fn visit_expr_(&mut self, env: &mut Env, expr_: &'a tast::Expr_) -> T {
        match expr_ {
            aast::Expr_::Is(x) => {
                let (_e, hint) = &**x;
                let result = match tast_env::supports_new_refinement(env, hint) {
                    Ok(()) => summary::new_refinement(),
                    Err(err) => {
                        let pos_opt = {
                            let log_level = tast_env::get_tcopt(env).log_levels.get("refinement_counter").copied();
                            match log_level {
                                Some(3) => Some(&hint.0),
                                Some(2) if !err.contains("class") => Some(&hint.0),
                                _ => None,
                            }
                        };
                        summary::legacy_refinement(err, pos_opt)
                    }
                };
                let r = aast_reduce::tast::on_expr_(self, env, expr_);
                self.plus(r, result)
            }
            _ => aast_reduce::tast::on_expr_(self, env, expr_),
        }
    }
}

fn count(ctx: &provider_context::T, program: &[tast::Def]) -> T {
    aast_reduce::tast::go(&mut Visitor, ctx, program)
}

pub fn is_enabled(tcopt: &TypecheckerOptions) -> bool {
    tcopt.log_levels.get("refinement_counter").map(|level| *level >= 1).unwrap_or(false)
}

pub fn map(ctx: &provider_context::T, _path: &RelativePath, tasts: tast::ByNames) -> T {
    let program: Vec<tast::Def> = tast::tasts_as_list(tasts)
        .into_iter()
        .map(|t| t.under_normal_assumptions)
        .collect();
    count(ctx, &program)
}

pub fn reduce(a: T, b: T) -> T {
    summary::plus(a, b)
}
