// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/service/type_counter.ml`. See `hh/PORTING.md`.

use std::collections::BTreeMap;

use oxidized::aast;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::code_actions::aast_reduce::SNode;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor::IterParams;
use crate::typechecker_options::TypecheckerOptions;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Entity {
    Class(String),
    Function(String),
}

pub type EntityPos = (Pos, Entity);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LoggedType {
    Like,
    NonLike,
    Mixed,
    SupportdynOfMixed,
    Dynamic,
    Tany,
    CapturedLike,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Category {
    Expression,
    ObjGetReceiver,
    ClassGetReceiver,
    ClassConstReceiver,
    Property,
    Parameter,
    Return,
}

fn dynamic() -> Ty {
    crate::typing_make_type::dynamic(crate::typing_reason::none())
}

fn mixed() -> Ty {
    crate::typing_make_type::mixed(crate::typing_reason::none())
}

fn supportdyn_of_mixed() -> Ty {
    crate::typing_make_type::supportdyn_mixed(crate::typing_reason::none())
}

fn is_exactly(env: &Env, ty: &Ty, ty_: &Ty) -> bool {
    tast_env::is_sub_type(env, ty, ty_) && tast_env::is_sub_type(env, ty_, ty)
}

fn is_like_type(env: &Env, ty: &Ty) -> bool {
    let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
    match crate::typing_defs_core::get_node(&ty) {
        Ty_::Tintersection(tyl) => tyl.iter().any(|ty| is_like_type(env, ty)),
        _ => {
            tast_env::is_sub_type(env, &dynamic(), &ty)
                && !(tast_env::is_sub_type(env, &mixed(), &ty)
                    || tast_env::is_sub_type(env, &supportdyn_of_mixed(), &ty))
        }
    }
}

fn is_tany(ty: &Ty) -> bool {
    crate::typing_defs::is_any(ty)
}

mod counter {
    use super::*;

    pub type T = BTreeMap<LoggedType, isize>;

    pub fn zero() -> T {
        T::new()
    }

    pub fn is_zero(t: &T) -> bool {
        t.is_empty()
    }

    pub fn plus(mut a: T, b: T) -> T {
        for (k, c) in b {
            *a.entry(k).or_insert(0) += c
        }
        a
    }

    fn inc(key: LoggedType, t: &mut T) {
        *t.entry(key).or_insert(0) += 1
    }

    pub fn unit(env: &Env, ty: &Ty) -> T {
        let mut t = T::new();
        if is_like_type(env, ty) {
            if crate::typing_reason::predicates::is_captured_like(crate::typing_defs_core::get_reason(ty)) {
                inc(LoggedType::Like, &mut t);
                inc(LoggedType::CapturedLike, &mut t)
            } else {
                inc(LoggedType::Like, &mut t)
            }
        } else {
            inc(LoggedType::NonLike, &mut t)
        }
        if is_exactly(env, ty, &mixed()) {
            inc(LoggedType::Mixed, &mut t)
        }
        if is_exactly(env, ty, &supportdyn_of_mixed()) {
            inc(LoggedType::SupportdynOfMixed, &mut t)
        }
        if is_exactly(env, ty, &dynamic()) {
            inc(LoggedType::Dynamic, &mut t)
        }
        if is_tany(ty) {
            inc(LoggedType::Tany, &mut t)
        }
        t
    }

    pub fn unpack(t: &T) -> Vec<(LoggedType, isize)> {
        t.iter().map(|(k, c)| (*k, *c)).collect()
    }
}

mod categories {
    use super::*;

    pub type T = BTreeMap<Category, counter::T>;

    pub fn zero() -> T {
        T::new()
    }

    pub fn plus(mut a: T, b: T) -> T {
        for (k, c) in b {
            let merged = match a.remove(&k) {
                Some(c_) => counter::plus(c_, c),
                None => c,
            };
            a.insert(k, merged);
        }
        a
    }

    pub fn singleton(k: Category, c: counter::T) -> T {
        if counter::is_zero(&c) { T::new() } else { T::from([(k, c)]) }
    }

    pub fn unpack(x: &T) -> Vec<(Category, LoggedType, isize)> {
        x.iter()
            .flat_map(|(cg, cnts)| counter::unpack(cnts).into_iter().map(|(t, c)| (*cg, t, c)))
            .collect()
    }
}

fn callable_decl_counter(env: &Env, params: &[tast::FunParam], ret: &tast::TypeHint) -> categories::T {
    let parameter = categories::singleton(
        Category::Parameter,
        params.iter().fold(counter::zero(), |acc, param| {
            let ty = &param.type_hint.0;
            counter::plus(acc, counter::unit(env, ty))
        }),
    );
    let return_ = categories::singleton(Category::Return, counter::unit(env, &ret.0));
    categories::plus(parameter, return_)
}

struct PartitionTypes;

impl<'a> Reducer<'a, IterParams, categories::T> for PartitionTypes {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, categories::T> {
        self
    }
    fn zero(&mut self) -> categories::T {
        categories::zero()
    }
    fn plus(&mut self, a: categories::T, b: categories::T) -> categories::T {
        categories::plus(a, b)
    }
    aast_reduce::tast::tast_methods!('a, categories::T; expr_, class_var, expression_tree);

    fn visit_expr(&mut self, env: &mut Env, e: &'a tast::Expr) -> categories::T {
        let aast::Expr(ty, _, e_) = e;
        let expression = categories::singleton(Category::Expression, counter::unit(env, ty));
        let receiver = match e_ {
            aast::Expr_::ObjGet(x) => {
                categories::singleton(Category::ObjGetReceiver, counter::unit(env, &(x.0).0))
            }
            aast::Expr_::ClassGet(x) => {
                categories::singleton(Category::ClassGetReceiver, counter::unit(env, &(x.0).0))
            }
            aast::Expr_::ClassConst(x) => {
                categories::singleton(Category::ClassConstReceiver, counter::unit(env, &(x.0).0))
            }
            _ => categories::zero(),
        };
        let r = categories::plus(expression, receiver);
        categories::plus(r, e.srecurse(env, self))
    }

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> categories::T {
        let declaration = callable_decl_counter(env, &m.params, &m.ret);
        let expression = aast_reduce::tast::on_method_(self, env, m);
        categories::plus(declaration, expression)
    }

    fn visit_fun_(&mut self, env: &mut Env, f: &'a tast::Fun_) -> categories::T {
        let declaration = callable_decl_counter(env, &f.params, &f.ret);
        let expression = aast_reduce::tast::on_fun_(self, env, f);
        categories::plus(declaration, expression)
    }

    fn visit_class_(&mut self, env: &mut Env, c: &'a tast::Class_) -> categories::T {
        let property = categories::singleton(
            Category::Property,
            c.vars.iter().fold(counter::zero(), |acc, prop| {
                let ty = &prop.type_.0;
                counter::plus(acc, counter::unit(env, ty))
            }),
        );
        let method_ = c.srecurse(env, self);
        categories::plus(property, method_)
    }
}

pub struct Count {
    /// The position of the entity for which this count holds
    pub entity_pos: EntityPos,
    /// The type that this count is for
    pub counted_type: LoggedType,
    /// Program construct that produces this type
    pub category: Category,
    /// The actual count
    pub value: isize,
}

/// `count ctx program` (`reducer#go`: each definition with its environment;
/// only the functions and the classes are counted).
fn count(ctx: &provider_context::T, program: &[tast::Def]) -> Vec<Count> {
    let mut counts = vec![];
    for def in program {
        let mut env = tast_env::def_env(ctx, def);
        let (categories, entity_pos) = match def {
            aast::Def::Fun(f) => (
                PartitionTypes.visit_fun_def(&mut env, f),
                (f.name.0.clone(), Entity::Function(f.name.1.clone())),
            ),
            aast::Def::Class(c) => (
                PartitionTypes.visit_class_(&mut env, c),
                (c.name.0.clone(), Entity::Class(c.name.1.clone())),
            ),
            _ => continue,
        };
        for (category, counted_type, value) in categories::unpack(&categories) {
            counts.push(Count {
                entity_pos: entity_pos.clone(),
                counted_type,
                category,
                value,
            })
        }
    }
    counts
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// Summary for one file, only counting like types.
pub struct Summary {
    num_like_types: isize,
    num_captured_like_types: isize,
    num_non_like_types: isize,
    num_mixed: isize,
    num_supportdyn_of_mixed: isize,
    num_dynamic: isize,
    num_dynamic_obj: isize,
    num_like_obj: isize,
    num_non_like_obj: isize,
    num_tany: isize,
}

/// `summary Relative_path.Map.t`
pub type T = BTreeMap<RelativePath, Summary>;

fn yojson_of_summary(s: &Summary) -> yojson::T {
    let f = |name: &str, v: isize| (name.to_string(), yojson::T::Int(v));
    yojson::T::Assoc(vec![
        f("num_like_types", s.num_like_types),
        f("num_captured_like_types", s.num_captured_like_types),
        f("num_non_like_types", s.num_non_like_types),
        f("num_mixed", s.num_mixed),
        f("num_supportdyn_of_mixed", s.num_supportdyn_of_mixed),
        f("num_dynamic", s.num_dynamic),
        f("num_dynamic_obj", s.num_dynamic_obj),
        f("num_like_obj", s.num_like_obj),
        f("num_non_like_obj", s.num_non_like_obj),
        f("num_tany", s.num_tany),
    ])
}

/// (`Relative_path.Map.yojson_of_t`: the suffixes of the paths are the keys.)
pub fn yojson_of_t(t: &T) -> yojson::T {
    yojson::T::Assoc(
        t.iter()
            .map(|(path, s)| (crate::relative_path::suffix(path), yojson_of_summary(s)))
            .collect(),
    )
}

fn summary_of_count(cnt: &Count) -> Summary {
    let Count {
        counted_type,
        value,
        entity_pos: _,
        category,
    } = cnt;
    let value = *value;
    let empty_summary = Summary::default();
    let is_obj = matches!(category, Category::ObjGetReceiver);
    match counted_type {
        LoggedType::Like => Summary {
            num_like_types: value,
            num_like_obj: if is_obj { value } else { 0 },
            ..empty_summary
        },
        LoggedType::NonLike => Summary {
            num_non_like_types: value,
            num_non_like_obj: if is_obj { value } else { 0 },
            ..empty_summary
        },
        LoggedType::Mixed => Summary {
            num_mixed: value,
            ..empty_summary
        },
        LoggedType::SupportdynOfMixed => Summary {
            num_supportdyn_of_mixed: value,
            ..empty_summary
        },
        LoggedType::Dynamic => Summary {
            num_dynamic: value,
            num_dynamic_obj: if is_obj { value } else { 0 },
            ..empty_summary
        },
        LoggedType::Tany => Summary {
            num_tany: value,
            ..empty_summary
        },
        LoggedType::CapturedLike => Summary {
            num_captured_like_types: value,
            ..empty_summary
        },
    }
}

fn plus_summary(s: Summary, t: Summary) -> Summary {
    Summary {
        num_like_types: s.num_like_types + t.num_like_types,
        num_captured_like_types: s.num_captured_like_types + t.num_captured_like_types,
        num_non_like_types: s.num_non_like_types + t.num_non_like_types,
        num_mixed: s.num_mixed + t.num_mixed,
        num_supportdyn_of_mixed: s.num_supportdyn_of_mixed + t.num_supportdyn_of_mixed,
        num_dynamic: s.num_dynamic + t.num_dynamic,
        num_dynamic_obj: s.num_dynamic_obj + t.num_dynamic_obj,
        num_like_obj: s.num_like_obj + t.num_like_obj,
        num_non_like_obj: s.num_non_like_obj + t.num_non_like_obj,
        num_tany: s.num_tany + t.num_tany,
    }
}

fn summary_of_counts(cnts: &[Count]) -> T {
    let mut m = T::new();
    for c in cnts {
        let fn_ = RelativePath::clone(c.entity_pos.0.filename());
        let c = summary_of_count(c);
        let x = m.remove(&fn_).unwrap_or_default();
        m.insert(fn_, plus_summary(x, c));
    }
    m
}

pub fn is_enabled(tcopt: &TypecheckerOptions) -> bool {
    tcopt.log_levels.get("type_counter").map(|level| *level == 1).unwrap_or(false)
}

pub fn map(ctx: &provider_context::T, _path: &RelativePath, tasts: tast::ByNames) -> T {
    let program: Vec<tast::Def> = tast::tasts_as_list(tasts)
        .into_iter()
        .map(|t| t.under_normal_assumptions)
        .collect();
    summary_of_counts(&count(ctx, &program))
}

pub fn reduce(mut xs: T, ys: T) -> T {
    for (key, y) in ys {
        let merged = match xs.remove(&key) {
            Some(x) => plus_summary(x, y),
            None => y,
        };
        xs.insert(key, merged);
    }
    xs
}
