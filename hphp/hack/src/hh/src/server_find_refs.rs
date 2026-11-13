// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_find_refs.ml`. See `hh/PORTING.md`.
//!
//! Owned by **F6** (plan §7.3).
//!
//! `env` is taken and given back (`Server_env.env` is not `Clone`);
//! `genv.workers` is `genv.num_workers` (one worker = `None`: the same
//! buckets and merge order, see `find_refs_service`).

use std::sync::Arc;

use oxidized::pos::Pos;

use crate::ast_provider;
use crate::file_content;
use crate::find_refs_service;
use crate::full_fidelity_source_text;
use crate::hh_logger;
use crate::path;
use crate::pos;
use crate::provider_context;
use crate::relative_path;
use crate::s_set;
use crate::search_types::find_refs as sfr;
use crate::server_command_types::done_or_retry;
use crate::server_command_types::done_or_retry::T::Done;
use crate::server_command_types::done_or_retry::T::Retry;
use crate::server_command_types::find_refs::Action;
use crate::server_command_types::find_refs::Member;
use crate::server_command_types::find_refs::Result as AbsResult;
use crate::server_command_types::find_refs::ServerResult;
use crate::server_command_types::find_refs::ServerResultOrRetry;
use crate::server_env;
use crate::server_env::Env;
use crate::server_env::Genv;
use crate::server_identify_function;
use crate::symbol_definition;
use crate::symbol_occurrence;
use crate::telemetry;
use crate::typing_deps::dep;
use crate::typing_deps::dep_set;
use crate::utils;

/// `genv.workers`: `None` for one worker.
pub fn workers(genv: &Genv) -> Option<usize> {
    if genv.num_workers > 1 {
        Some(genv.num_workers as usize)
    } else {
        None
    }
}

pub fn add_ns(name: &str) -> String {
    if name.starts_with('\\') {
        name.to_string()
    } else {
        format!("\\{}", name)
    }
}

fn strip_ns(results: Vec<sfr::T>) -> Vec<sfr::T> {
    results
        .into_iter()
        .map(|r| sfr::Result {
            name: utils::strip_ns(&r.name).to_string(),
            pos: r.pos,
        })
        .collect()
}

fn search(
    ctx: &provider_context::T,
    target: &find_refs_service::ActionInternal,
    include_defs: bool,
    hints: &[relative_path::T],
    files: Vec<relative_path::T>,
    stream_file: Option<&path::T>,
    genv: &Genv,
) -> Vec<sfr::T> {
    let hints_set: relative_path::set::T = hints.iter().cloned().collect();
    let files = files.into_iter().filter(|file| !hints_set.contains(file));
    let files: Vec<relative_path::T> = hints.iter().cloned().chain(files).collect();
    if hh_logger::level::passes_min_level(hh_logger::level::T::Debug) {
        for file in &files {
            hh_logger::debug(
                None,
                None,
                &format!(
                    "ServerFindRefs.search file {}",
                    relative_path::to_absolute(file)
                ),
            );
        }
    }
    // Get all the references to the provided target in the files
    let res = find_refs_service::find_references(
        ctx,
        workers(genv),
        target,
        include_defs,
        &files,
        None,
        stream_file,
    );
    strip_ns(res)
}

fn search_single_file(
    ctx: &provider_context::T,
    target: &find_refs_service::ActionInternal,
    file: &relative_path::T,
) -> Vec<sfr::T> {
    if hh_logger::level::passes_min_level(hh_logger::level::T::Debug) {
        hh_logger::debug(
            None,
            None,
            &format!(
                "ServerFindRefs.search file {}",
                relative_path::to_absolute(file)
            ),
        );
    }
    // Get all the references to the provided target in the file
    let res = find_refs_service::find_references_single_file(ctx, target, file);
    strip_ns(res)
}

/// `Server_prechecked_files.update_after_local_changes genv env changes
/// ~start_time` (SS3's module, empty yet): prechecked files are not ported
/// (`Prechecked_files_disabled` is the only state), whose branch only builds
/// telemetry.
fn update_after_local_changes(
    _genv: &Genv,
    env: Env,
    changes: &dep_set::T,
    start_time: f64,
) -> (Env, telemetry::T) {
    let telemetry = telemetry::duration(Some("start"), start_time, None, telemetry::create());
    let telemetry = telemetry::int_("changes", dep_set::cardinal(changes), telemetry);
    match env.prechecked_files {
        server_env::PrecheckedFilesStatus::PrecheckedFilesDisabled => {
            let telemetry = telemetry::string_(None, "mode", "disabled", telemetry);
            (env, telemetry)
        }
    }
}

pub fn handle_prechecked_files<A>(
    genv: &Genv,
    env: Env,
    dep: dep::T,
    f: impl FnOnce(&Env) -> A,
) -> (Env, done_or_retry::T<A>) {
    // We need to handle prechecked files here to get accurate results.
    let dep = dep_set::singleton(dep);
    // All the callers of this should be listed in ServerCommand.rpc_command_needs_full_check,
    // and server should never call this before completing full check
    assert!(server_env::is_full_check_done(env.full_check_status));
    let start_time = crate::rt::ocaml_unix::gettimeofday();
    let (env, _telemetry) = update_after_local_changes(genv, env, &dep, start_time);
    // If we added more things to recheck, we can't handle this command now, and
    // tell the client to retry instead.
    if server_env::is_full_check_done(env.full_check_status) {
        hh_logger::debug(None, None, "ServerFindRefs.handle_prechecked_files: Done");
        let callback_result = f(&env);
        (env, Done(callback_result))
    } else {
        hh_logger::debug(None, None, "ServerFindRefs.handle_prechecked_files: Retry");
        (env, Retry)
    }
}

fn search_function(
    ctx: &provider_context::T,
    function_name: &str,
    include_defs: bool,
    stream_file: Option<&path::T>,
    hints: &[relative_path::T],
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    let function_name = add_ns(function_name);
    hh_logger::debug(
        None,
        None,
        &format!("ServerFindRefs.search_function: {}", function_name),
    );
    handle_prechecked_files(
        genv,
        env,
        dep::make(&dep::Variant::Fun(function_name.clone())),
        |_env| {
            let files: Vec<relative_path::T> =
                find_refs_service::get_dependent_files_function(ctx, workers(genv), &function_name)
                    .into_iter()
                    .collect();
            search(
                ctx,
                &find_refs_service::ActionInternal::IFunction(function_name.clone()),
                include_defs,
                hints,
                files,
                stream_file,
                genv,
            )
        },
    )
}

fn search_single_file_for_function(
    ctx: &provider_context::T,
    function_name: &str,
    filename: &relative_path::T,
) -> Vec<sfr::T> {
    let function_name = add_ns(function_name);
    hh_logger::debug(
        None,
        None,
        &format!("ServerFindRefs.search_function: {}", function_name),
    );
    search_single_file(
        ctx,
        &find_refs_service::ActionInternal::IFunction(function_name),
        filename,
    )
}

fn search_member(
    ctx: &provider_context::T,
    class_name: &str,
    member: &Member,
    include_defs: bool,
    stream_file: Option<&path::T>,
    hints: &[relative_path::T],
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    use crate::typing_deps::dep::member;
    let dep_member_of = |member: &Member| match member {
        Member::Method(n) => vec![member::method_(n), member::smethod(n)],
        Member::Property(n) => vec![member::prop(n), member::sprop(n)],
        Member::ClassConst(n) => vec![member::const_(n)],
        Member::Typeconst(n) => vec![member::const_(n)],
    };
    let class_name = add_ns(class_name);
    let origin_class_name = find_refs_service::get_origin_class_name(ctx, &class_name, member);
    handle_prechecked_files(
        genv,
        env,
        dep::make(&dep::Variant::Type(origin_class_name.clone())),
        |env| {
            let (descendant_class_files, member_use_files) =
                find_refs_service::get_files_for_descendants_and_dependents_of_members_in_descendants(
                    ctx,
                    &class_name,
                    None,
                    &dep_member_of(member),
                )
                // ~max_deps:None guarantees Ok
                .expect("Result.get_ok");
            let descendant_classes = find_refs_service::find_child_classes_in_files(
                ctx,
                &origin_class_name,
                &env.naming_table,
                &descendant_class_files,
            );
            let mut class_and_descendants: s_set::T = descendant_classes;
            class_and_descendants.insert(origin_class_name.clone());
            let files: Vec<relative_path::T> = descendant_class_files
                .union(member_use_files)
                .into_iter()
                .collect();
            let target = find_refs_service::ActionInternal::IMember(
                find_refs_service::MemberClass::ClassSet(class_and_descendants),
                member.clone(),
            );
            search(ctx, &target, include_defs, hints, files, stream_file, genv)
        },
    )
}

fn search_single_file_for_member(
    ctx: &provider_context::T,
    class_name: &str,
    member: &Member,
    filename: &relative_path::T,
) -> Vec<sfr::T> {
    let class_name = add_ns(class_name);
    let origin_class_name = find_refs_service::get_origin_class_name(ctx, &class_name, member);
    let target = find_refs_service::ActionInternal::IMember(
        find_refs_service::MemberClass::SubclassesOf(origin_class_name),
        member.clone(),
    );
    search_single_file(ctx, &target, filename)
}

fn search_gconst(
    ctx: &provider_context::T,
    cst_name: &str,
    include_defs: bool,
    stream_file: Option<&path::T>,
    hints: &[relative_path::T],
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    let cst_name = add_ns(cst_name);
    handle_prechecked_files(
        genv,
        env,
        dep::make(&dep::Variant::GConst(cst_name.clone())),
        |_env| {
            let files: Vec<relative_path::T> =
                find_refs_service::get_dependent_files_gconst(ctx, workers(genv), &cst_name)
                    .into_iter()
                    .collect();
            search(
                ctx,
                &find_refs_service::ActionInternal::IGConst(cst_name.clone()),
                include_defs,
                hints,
                files,
                stream_file,
                genv,
            )
        },
    )
}

fn search_single_file_for_gconst(
    ctx: &provider_context::T,
    cst_name: &str,
    filename: &relative_path::T,
) -> Vec<sfr::T> {
    let cst_name = add_ns(cst_name);
    search_single_file(
        ctx,
        &find_refs_service::ActionInternal::IGConst(cst_name),
        filename,
    )
}

fn class_target(class_name: String, include_all_ci_types: bool) -> find_refs_service::ActionInternal {
    if include_all_ci_types {
        find_refs_service::ActionInternal::IClass(class_name)
    } else {
        find_refs_service::ActionInternal::IExplicitClass(class_name)
    }
}

fn search_class(
    ctx: &provider_context::T,
    class_name: &str,
    include_defs: bool,
    include_all_ci_types: bool,
    stream_file: Option<&path::T>,
    hints: &[relative_path::T],
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    let class_name = add_ns(class_name);
    let target = class_target(class_name.clone(), include_all_ci_types);
    handle_prechecked_files(
        genv,
        env,
        dep::make(&dep::Variant::Type(class_name.clone())),
        |_env| {
            let files: Vec<relative_path::T> = find_refs_service::get_dependent_files(
                ctx,
                workers(genv),
                &s_set::T::unit(class_name.clone()),
            )
            .into_iter()
            .collect();
            search(ctx, &target, include_defs, hints, files, stream_file, genv)
        },
    )
}

fn search_single_file_for_class(
    ctx: &provider_context::T,
    class_name: &str,
    filename: &relative_path::T,
    include_all_ci_types: bool,
) -> Vec<sfr::T> {
    let class_name = add_ns(class_name);
    let target = class_target(class_name, include_all_ci_types);
    search_single_file(ctx, &target, filename)
}

fn search_localvar(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Vec<sfr::T> {
    let results = crate::server_find_locals::go(ctx, entry, pos);
    match results.first() {
        Some(first_pos) => {
            let content = provider_context::read_file_contents_exn(entry);
            let content = String::from_utf8_lossy(&content);
            let var_text = pos::get_text_from_pos(&content, first_pos);
            results
                .into_iter()
                .map(|x| sfr::Result {
                    name: var_text.clone(),
                    pos: x,
                })
                .collect()
        }
        None => vec![],
    }
}

pub fn is_local(action: &Action) -> bool {
    matches!(action, Action::LocalVar { .. })
}

/// Given a Find_refs action, returns an updated env
/// and optional list of all positions where this action exists.
/// Wrapped in a Done_or_retry for clientLsp.
pub fn go(
    ctx: &provider_context::T,
    action: &Action,
    include_defs: bool,
    stream_file: Option<&path::T>,
    hints: &[relative_path::T],
    genv: &Genv,
    env: Env,
) -> (Env, ServerResultOrRetry) {
    match action {
        Action::Member(class_name, member) => search_member(
            ctx,
            class_name,
            member,
            include_defs,
            stream_file,
            hints,
            genv,
            env,
        ),
        Action::Function(function_name) => search_function(
            ctx,
            function_name,
            include_defs,
            stream_file,
            hints,
            genv,
            env,
        ),
        Action::Class(class_name) => {
            let include_all_ci_types = true;
            search_class(
                ctx,
                class_name,
                include_defs,
                include_all_ci_types,
                stream_file,
                hints,
                genv,
                env,
            )
        }
        Action::ExplicitClass(class_name) => {
            let include_all_ci_types = false;
            search_class(
                ctx,
                class_name,
                include_defs,
                include_all_ci_types,
                stream_file,
                hints,
                genv,
                env,
            )
        }
        Action::GConst(cst_name) => {
            search_gconst(ctx, cst_name, include_defs, stream_file, hints, genv, env)
        }
        Action::LocalVar {
            filename,
            file_content,
            pos,
        } => {
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                filename.clone(),
                file_content.as_bytes().into(),
            );
            (env, Done(search_localvar(&ctx, &entry, pos)))
        }
    }
}

/// Like `go`, but only looks for references in the cached TAST from the
/// supplied filename. `go` uses ideps to look for references for ALL files.
pub fn go_for_single_file(
    ctx: &provider_context::T,
    action: &Action,
    filename: &relative_path::T,
) -> ServerResult {
    match action {
        Action::Member(class_name, member) => {
            search_single_file_for_member(ctx, class_name, member, filename)
        }
        Action::Function(function_name) => {
            search_single_file_for_function(ctx, function_name, filename)
        }
        Action::Class(class_name) => {
            let include_all_ci_types = true;
            search_single_file_for_class(ctx, class_name, filename, include_all_ci_types)
        }
        Action::ExplicitClass(class_name) => {
            let include_all_ci_types = false;
            search_single_file_for_class(ctx, class_name, filename, include_all_ci_types)
        }
        Action::GConst(cst_name) => search_single_file_for_gconst(ctx, cst_name, filename),
        Action::LocalVar {
            filename,
            file_content,
            pos,
        } => {
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                filename.clone(),
                file_content.as_bytes().into(),
            );
            search_localvar(&ctx, &entry, pos)
        }
    }
}

/// Like go, but only supports LocalVar actions. If supplied a localvar,
/// returns an optional list of all positions of that localvar. If action is
/// not a localvar, returns the same action back wrapped in an error.
pub fn go_for_localvar(ctx: &provider_context::T, action: &Action) -> Result<Vec<sfr::T>, Action> {
    match action {
        Action::LocalVar {
            filename,
            file_content,
            pos,
        } => {
            let (ctx, entry) = provider_context::add_or_overwrite_entry_contents(
                ctx,
                filename.clone(),
                file_content.as_bytes().into(),
            );
            Ok(search_localvar(&ctx, &entry, pos))
        }
        _ => Err(action.clone()),
    }
}

pub fn to_absolute(res: &ServerResult) -> AbsResult {
    res.iter()
        .map(|r| sfr::Result {
            name: r.name.clone(),
            pos: pos::to_absolute(&r.pos),
        })
        .collect()
}

fn get_action(
    symbol: &symbol_occurrence::T<Pos>,
    (filename, file_content, pos): (&relative_path::T, String, &file_content::position::T),
) -> Option<Action> {
    use symbol_occurrence::Kind as SO;
    use symbol_occurrence::ReceiverClass::ClassName;
    use symbol_occurrence::ReceiverClass::UnknownClass;
    let name = &symbol.name;
    match &symbol.type_ {
        SO::Class(_) => Some(Action::Class(name.clone())),
        SO::Function => Some(Action::Function(name.clone())),
        SO::Method(ClassName(class_name), method_name) => Some(Action::Member(
            class_name.clone(),
            Member::Method(method_name.clone()),
        )),
        SO::Property(ClassName(class_name), prop_name)
        | SO::XhpLiteralAttr(class_name, prop_name) => Some(Action::Member(
            class_name.clone(),
            Member::Property(prop_name.clone()),
        )),
        SO::ClassConst(ClassName(class_name), const_name) => Some(Action::Member(
            class_name.clone(),
            Member::ClassConst(const_name.clone()),
        )),
        SO::Typeconst(class_name, tconst_name) => Some(Action::Member(
            class_name.clone(),
            Member::Typeconst(tconst_name.clone()),
        )),
        SO::GConst => Some(Action::GConst(name.clone())),
        SO::LocalVar => Some(Action::LocalVar {
            filename: filename.clone(),
            file_content,
            pos: *pos,
        }),
        SO::TypeVar => None,
        SO::Attribute(_) => Some(Action::Class(name.clone())),
        SO::Keyword(_)
        | SO::PureFunctionContext
        | SO::BuiltInType(_)
        | SO::BestEffortArgument(..)
        | SO::HhFixme
        | SO::HhIgnore
        | SO::Method(UnknownClass, _)
        | SO::Property(UnknownClass, _)
        | SO::ClassConst(UnknownClass, _)
        | SO::Module => None,
        // TODO(toyang): find references doesn't work for enum labels yet
        SO::EnumClassLabel(..) => None,
    }
}

/// Given a position in a file, returns the `SymbolDefinition.t` and data
/// ("action") that represents if it's a class, method, etc. This is the same
/// as `go_from_file_ctx` but sends the entire SymbolDefinition back.
pub fn go_from_file_ctx_with_symbol_definition(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Option<(symbol_definition::T<Pos>, Action)> {
    // Find the symbol at given position
    let mut symbols = server_identify_function::go_quarantined(ctx, entry, pos);
    // If there are few, arbitrarily pick the first
    if symbols.is_empty() {
        return None;
    }
    let (occurrence, definition) = symbols.swap_remove(0);
    // Ignore symbols that lack definitions
    let definition = definition?;
    let source_text = ast_provider::compute_source_text(entry);
    let action = get_action(
        &occurrence,
        (
            &entry.path,
            String::from_utf8_lossy(full_fidelity_source_text::text(&source_text)).into_owned(),
            pos,
        ),
    )?;
    Some((definition, action))
}

/// Given a position in a file, returns the name of the symbol
/// and data ("action") that represents if it's a class, method, etc.
pub fn go_from_file_ctx(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pos: &file_content::position::T,
) -> Option<(String, Action)> {
    go_from_file_ctx_with_symbol_definition(ctx, entry, pos)
        .map(|(def, action)| (symbol_definition::full_name(&def), action))
}
