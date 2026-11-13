// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_infer_dynamic.ml` (the `INFER_DYNAMIC`
//! command; the caller sets `tco_dynamic_inference` on the context). See
//! `hh/PORTING.md`.

use std::sync::Arc;

use oxidized::aast;

use crate::provider_context;
use crate::tast;
use crate::tast_env;
use crate::yojson::safe::T as Json;

pub enum Target {
    TargetFunction(String),
    TargetMethod(String, String),
}

pub fn parse_target(identifier: &str) -> Target {
    let with_backslash = |s: &str| {
        if s.starts_with('\\') {
            s.to_string()
        } else {
            format!("\\{}", s)
        }
    };
    match identifier.find("::") {
        Some(i) => {
            let class_name = &identifier[..i];
            let method_name = &identifier[i + 2..];
            Target::TargetMethod(with_backslash(class_name), method_name.to_string())
        }
        None => Target::TargetFunction(with_backslash(identifier)),
    }
}

fn dynamic_locals(env: &tast_env::Env) -> &[tast::DynamicLocalInfo] {
    match &env.fun_tast_info {
        Some(info) => &info.dynamic_locals,
        None => &[],
    }
}

pub fn solve_and_format(as_data: bool, name: String, env: &tast_env::Env) -> Json {
    let inf_env = &env.inference_env;
    let solutions =
        crate::typing_shadow_solver::solve(as_data, env, inf_env, dynamic_locals(env));
    Json::Assoc(vec![
        ("function".to_string(), Json::String(name)),
        (
            "solutions".to_string(),
            Json::List(
                solutions
                    .iter()
                    .map(|s| crate::typing_shadow_solver::solution_to_json(env, s))
                    .collect(),
            ),
        ),
    ])
}

fn infer_function(
    ctx: &provider_context::T,
    tast: &[tast::Def],
    as_data: bool,
    name: &str,
) -> Option<Json> {
    tast.iter().find_map(|def| match def {
        aast::Def::Fun(fd) if fd.name.1 == name => {
            let env = tast_env::def_env(ctx, def);
            Some(solve_and_format(as_data, name.to_string(), &env))
        }
        _ => None,
    })
}

enum LookupResult<A> {
    Found(A),
    ClassNotInTast,
    MethodNotFound,
}

fn infer_method(
    ctx: &provider_context::T,
    tast: &[tast::Def],
    as_data: bool,
    class_name: &str,
    method_name: &str,
) -> LookupResult<Json> {
    let mut found_class = false;
    let result = tast.iter().find_map(|def| match def {
        aast::Def::Class(c) if c.name.1 == class_name => {
            found_class = true;
            let class_env = tast_env::def_env(ctx, def);
            c.methods.iter().find_map(|m| {
                if m.name.1 == method_name {
                    let mut env = class_env.clone();
                    tast_env::restore_method_env(&mut env, m);
                    let display_name = format!("{}::{}", class_name, method_name);
                    Some(solve_and_format(as_data, display_name, &env))
                } else {
                    None
                }
            })
        }
        _ => None,
    });
    match result {
        Some(json) => LookupResult::Found(json),
        None => {
            if found_class {
                LookupResult::MethodNotFound
            } else {
                LookupResult::ClassNotInTast
            }
        }
    }
}

fn error_json(msg: String) -> Json {
    Json::Assoc(vec![("error".to_string(), Json::String(msg))])
}

pub fn go(ctx: &provider_context::T, identifier: &str, as_data: bool) -> Json {
    let target = parse_target(identifier);
    let path = match &target {
        Target::TargetFunction(name) => crate::naming_provider::get_fun_path(ctx, name),
        Target::TargetMethod(class_name, _) => crate::naming_provider::get_type_path(ctx, class_name),
    };
    match path {
        None => {
            let what = match &target {
                Target::TargetFunction(name) => format!("function {}", name),
                Target::TargetMethod(class_name, _) => format!("class {}", class_name),
            };
            error_json(format!("Could not find {} in the naming table", what))
        }
        Some(path) => {
            let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let crate::tast_provider::ComputeTastResult { tast, .. } =
                crate::tast_provider::compute_tast_quarantined(&ctx, &entry);
            let tast: Vec<tast::Def> = crate::tast_with_dynamic::all(tast).concat();
            match &target {
                Target::TargetFunction(name) => match infer_function(&ctx, &tast, as_data, name) {
                    Some(json) => json,
                    None => error_json(format!("Could not find function {}", name)),
                },
                Target::TargetMethod(class_name, method_name) => {
                    match infer_method(&ctx, &tast, as_data, class_name, method_name) {
                        LookupResult::Found(json) => json,
                        LookupResult::MethodNotFound => error_json(format!(
                            "Method {} not found in class {}",
                            method_name, class_name
                        )),
                        LookupResult::ClassNotInTast => error_json(format!(
                            "Class {} not found in TAST (file: {})",
                            class_name,
                            crate::relative_path::suffix(&path)
                        )),
                    }
                }
            }
        }
    }
}

fn infer_all_methods(
    as_data: bool,
    class_env: &tast_env::Env,
    class_name: &str,
    methods: &[tast::Method_],
) -> Vec<Json> {
    methods
        .iter()
        .filter_map(|m| {
            let mut env = class_env.clone();
            tast_env::restore_method_env(&mut env, m);
            let name = format!("{}::{}", class_name, m.name.1);
            if dynamic_locals(&env).is_empty() {
                None
            } else {
                Some(solve_and_format(as_data, name, &env))
            }
        })
        .collect()
}

pub fn go_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    as_data: bool,
) -> Json {
    let crate::tast_provider::ComputeTastResult { tast, .. } =
        crate::tast_provider::compute_tast_quarantined(ctx, entry);
    let tast: Vec<tast::Def> = crate::tast_with_dynamic::all(tast).concat();
    let results = tast
        .iter()
        .flat_map(|def| match def {
            aast::Def::Fun(fd) => {
                let env = tast_env::def_env(ctx, def);
                let name = fd.name.1.clone();
                if dynamic_locals(&env).is_empty() {
                    vec![]
                } else {
                    vec![solve_and_format(as_data, name, &env)]
                }
            }
            aast::Def::Class(c) => {
                let class_env = tast_env::def_env(ctx, def);
                let class_name = &c.name.1;
                infer_all_methods(as_data, &class_env, class_name, &c.methods)
            }
            _ => vec![],
        })
        .collect();
    Json::List(results)
}
