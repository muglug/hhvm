// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_go_to_impl.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F6** (plan §7.3).
//!
//! `failwith` is a panic with the OCaml's message (`Failure`).
//! `Multi_worker.call` is `find_refs_service::multi_worker_call`.

use crate::ast_provider;
use crate::decl_entry;
use crate::decl_provider;
use crate::file_info;
use crate::find_refs_service;
use crate::folded_class;
use crate::naming_provider;
use crate::naming_table;
use crate::pos;
use crate::provider_context;
use crate::provider_utils;
use crate::relative_path;
use crate::s_set;
use crate::search_types::find_refs as sfr;
use crate::server_command_types::done_or_retry::T::Done;
use crate::server_command_types::find_refs::Action;
use crate::server_command_types::find_refs::Member;
use crate::server_command_types::find_refs::ServerResult;
use crate::server_command_types::find_refs::ServerResultOrRetry;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_find_refs;
use crate::typing_deps::dep;

const PARALLEL_LIMIT: usize = 10;

fn find_positions_of_classes(
    ctx: &provider_context::T,
    acc: Vec<sfr::T>,
    child_classes: &[String],
) -> Vec<sfr::T> {
    let mut acc = acc;
    acc.extend(child_classes.iter().map(|child_class| {
        match naming_provider::get_type_pos(ctx, child_class) {
            None => panic!("Could not find definition of child class: {}", child_class),
            Some(file_info::Pos::Full(pos)) => sfr::Result {
                name: child_class.clone(),
                pos,
            },
            Some(file_info::Pos::File(file_info::NameType::Class, path)) => {
                match ast_provider::find_class_in_file(false, ctx, &path, child_class) {
                    None => panic!(
                        "Could not find class {} in {}",
                        child_class,
                        relative_path::to_absolute(&path)
                    ),
                    Some(c) => sfr::Result {
                        name: child_class.clone(),
                        pos: c.name.0.clone(),
                    },
                }
            }
            Some(file_info::Pos::File(
                file_info::NameType::Fun
                | file_info::NameType::Typedef
                | file_info::NameType::Const
                | file_info::NameType::Module,
                _path,
            )) => panic!(
                "Information for class {} was returned as not a class",
                child_class
            ),
        }
    }));
    acc
}

fn parallel_find_positions_of_classes(
    ctx: &provider_context::T,
    child_classes: &[String],
    workers: Option<usize>,
) -> Vec<sfr::T> {
    find_refs_service::multi_worker_call(
        workers,
        child_classes,
        |acc, classes: Vec<String>| find_positions_of_classes(ctx, acc, &classes),
        Vec::new,
        // `List.append`
        |mut output, acc| {
            output.extend(acc);
            output
        },
        || false,
    )
}

fn add_if_valid_origin(
    ctx: &provider_context::T,
    class_elt: &folded_class::ClassElt,
    child_class: &str,
    method_name: &str,
    mut result: Vec<sfr::T>,
) -> Vec<sfr::T> {
    let pos = || naming_provider::resolve_position(ctx, &**class_elt.ce_pos);
    if class_elt.ce_origin == child_class {
        result.insert(
            0,
            sfr::Result {
                name: method_name.to_string(),
                pos: pos(),
            },
        );
        result
    } else {
        let origin_decl = decl_provider::get_class(None, ctx, &class_elt.ce_origin);
        match origin_decl {
            decl_entry::T::Found(origin_decl) => {
                let origin_kind = folded_class::kind(&origin_decl);
                if crate::ast_defs::is_c_trait(origin_kind) {
                    result.insert(
                        0,
                        sfr::Result {
                            name: method_name.to_string(),
                            pos: pos(),
                        },
                    );
                    result
                } else {
                    result
                }
            }
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => panic!("TODO"),
        }
    }
}

fn find_positions_of_methods(
    ctx: &provider_context::T,
    method_name: &str,
    acc: Vec<sfr::T>,
    child_classes: &[String],
) -> Vec<sfr::T> {
    child_classes.iter().fold(acc, |result, child_class| {
        let class_decl = decl_provider::get_class(None, ctx, child_class);
        match class_decl {
            decl_entry::T::Found(decl) => {
                let method_info = folded_class::get_method(&decl, method_name);
                match method_info {
                    Some(class_elt) => {
                        add_if_valid_origin(ctx, &class_elt, child_class, method_name, result)
                    }
                    None => {
                        let smethod_info = folded_class::get_smethod(&decl, method_name);
                        match smethod_info {
                            Some(class_elt) => add_if_valid_origin(
                                ctx,
                                &class_elt,
                                child_class,
                                method_name,
                                result,
                            ),
                            None => result,
                        }
                    }
                }
            }
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                panic!("Could not find definition of child class: {}", child_class)
            }
        }
    })
}

fn parallel_find_positions_of_methods(
    ctx: &provider_context::T,
    child_classes: &[String],
    method_name: &str,
    workers: Option<usize>,
) -> Vec<sfr::T> {
    find_refs_service::multi_worker_call(
        workers,
        child_classes,
        |acc, classes: Vec<String>| find_positions_of_methods(ctx, method_name, acc, &classes),
        Vec::new,
        // `List.append`
        |mut output, acc| {
            output.extend(acc);
            output
        },
        || false,
    )
}

fn find_child_classes(
    ctx: &provider_context::T,
    class_name: &str,
    genv: &Genv,
    env: &Env,
) -> Vec<String> {
    let files = find_refs_service::get_dependent_files(
        ctx,
        server_find_refs::workers(genv),
        &s_set::T::unit(class_name.to_string()),
    );
    let ctx = provider_utils::ctx_from_server_env(env);
    find_refs_service::find_child_classes_in_files(&ctx, class_name, &env.naming_table, &files)
        .into_iter()
        .collect()
}

fn find_child_classes_in_file(
    ctx: &provider_context::T,
    class_name: &str,
    naming_table: &naming_table::T,
    filename: &relative_path::T,
) -> Vec<String> {
    let fileset = relative_path::set::T::unit(filename.clone());
    find_refs_service::find_child_classes_in_files(ctx, class_name, naming_table, &fileset)
        .into_iter()
        .collect()
}

fn search_class(
    ctx: &provider_context::T,
    class_name: &str,
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    let class_name = server_find_refs::add_ns(class_name);
    server_find_refs::handle_prechecked_files(
        genv,
        env,
        dep::make(&dep::Variant::Type(class_name.clone())),
        |env| {
            let child_classes = find_child_classes(ctx, &class_name, genv, env);
            if child_classes.len() < PARALLEL_LIMIT {
                find_positions_of_classes(ctx, vec![], &child_classes)
            } else {
                parallel_find_positions_of_classes(
                    ctx,
                    &child_classes,
                    server_find_refs::workers(genv),
                )
            }
        },
    )
}

fn search_single_file_for_class(
    ctx: &provider_context::T,
    class_name: &str,
    naming_table: &naming_table::T,
    filename: &relative_path::T,
) -> ServerResult {
    let class_name = server_find_refs::add_ns(class_name);
    let child_classes = find_child_classes_in_file(ctx, &class_name, naming_table, filename);
    find_positions_of_classes(ctx, vec![], &child_classes)
}

/// `List.dedup_and_sort ~compare:(fun { pos = pos1 } { pos = pos2 } ->
/// Pos.compare pos1 pos2)`: a stable sort, then of each run of equal
/// elements the last is kept (Base's `remove_consecutive_duplicates`).
fn dedup_and_sort_by_pos(mut results: Vec<sfr::T>) -> Vec<sfr::T> {
    results.sort_by(|r1, r2| pos::compare(&r1.pos, &r2.pos));
    let mut deduped: Vec<sfr::T> = Vec::with_capacity(results.len());
    for r in results {
        match deduped.last_mut() {
            Some(last) if pos::compare(&last.pos, &r.pos) == std::cmp::Ordering::Equal => {
                *last = r
            }
            _ => deduped.push(r),
        }
    }
    deduped
}

fn search_member(
    ctx: &provider_context::T,
    class_name: &str,
    member: &Member,
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    match member {
        Member::Method(method_name) => {
            let class_name = server_find_refs::add_ns(class_name);
            let class_name = find_refs_service::get_origin_class_name(ctx, &class_name, member);
            server_find_refs::handle_prechecked_files(
                genv,
                env,
                dep::make(&dep::Variant::Type(class_name.clone())),
                |env| {
                    // Find all the classes that extend this one
                    let child_classes = find_child_classes(ctx, &class_name, genv, env);
                    let results = if child_classes.len() < PARALLEL_LIMIT {
                        find_positions_of_methods(ctx, method_name, vec![], &child_classes)
                    } else {
                        parallel_find_positions_of_methods(
                            ctx,
                            &child_classes,
                            method_name,
                            server_find_refs::workers(genv),
                        )
                    };
                    dedup_and_sort_by_pos(results)
                },
            )
        }
        Member::Property(_) | Member::ClassConst(_) | Member::Typeconst(_) => (env, Done(vec![])),
    }
}

fn search_single_file_for_member(
    ctx: &provider_context::T,
    class_name: &str,
    member: &Member,
    naming_table: &naming_table::T,
    filename: &relative_path::T,
) -> ServerResult {
    match member {
        Member::Method(method_name) => {
            let class_name = server_find_refs::add_ns(class_name);
            let class_name = find_refs_service::get_origin_class_name(ctx, &class_name, member);
            // Find all the classes that extend this one
            let child_classes =
                find_child_classes_in_file(ctx, &class_name, naming_table, filename);
            let results = find_positions_of_methods(ctx, method_name, vec![], &child_classes);
            dedup_and_sort_by_pos(results)
        }
        Member::Property(_) | Member::ClassConst(_) | Member::Typeconst(_) => vec![],
    }
}

pub fn is_searchable(action: &Action) -> bool {
    match action {
        Action::Class(_) | Action::ExplicitClass(_) | Action::Member(_, _) => true,
        Action::Function(_) | Action::GConst(_) | Action::LocalVar { .. } => false,
    }
}

pub fn go_for_single_file(
    ctx: &provider_context::T,
    action: &Action,
    naming_table: &naming_table::T,
    filename: &relative_path::T,
) -> ServerResult {
    match action {
        Action::Class(class_name) | Action::ExplicitClass(class_name) => {
            search_single_file_for_class(ctx, class_name, naming_table, filename)
        }
        Action::Member(class_name, member) => {
            search_single_file_for_member(ctx, class_name, member, naming_table, filename)
        }
        Action::Function(_) | Action::GConst(_) | Action::LocalVar { .. } => vec![],
    }
}

pub fn go(action: &Action, genv: &Genv, env: Env) -> (Env, ServerResultOrRetry) {
    let ctx = provider_utils::ctx_from_server_env(&env);
    match action {
        Action::Class(class_name) | Action::ExplicitClass(class_name) => {
            search_class(&ctx, class_name, genv, env)
        }
        Action::Member(class_name, member) => search_member(&ctx, class_name, member, genv, env),
        Action::Function(_) | Action::GConst(_) | Action::LocalVar { .. } => (env, Done(vec![])),
    }
}
