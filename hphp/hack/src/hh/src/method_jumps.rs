// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/method_jumps.ml`. See `hh/PORTING.md`.
//!
//! "Might raise `Naming_table.File_info_not_found`" is the
//! `Err(FileInfoNotFound)` of the functions that read the naming table.
//! `Multi_worker.call` is `find_refs_service::multi_worker_call`.

use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::decl_provider;
use crate::decl_utils;
use crate::file_info;
use crate::find_refs_service;
use crate::folded_class as cls;
use crate::naming_provider;
use crate::naming_table;
use crate::naming_table::FileInfoNotFound;
use crate::pos;
use crate::provider_context;
use crate::server_command_types::method_jumps::Filter;
use crate::server_command_types::method_jumps::Result as MjResult;
use crate::utils;

pub fn string_filter_to_method_jump_filter(s: &str) -> Option<Filter> {
    match s {
        "No_filter" => Some(Filter::NoFilter),
        "Class" => Some(Filter::Class),
        "Interface" => Some(Filter::Interface),
        "Trait" => Some(Filter::Trait),
        _ => None,
    }
}

/// Used so the given input doesn't need the `\`.
pub fn add_ns(name: &str) -> String {
    if name.starts_with('\\') {
        name.to_string()
    } else {
        format!("\\{}", name)
    }
}

/// `get_or_method`: `Cls.get_method cls` of the origin class.
type GetMethod<'a> = &'a dyn Fn(&str) -> Option<cls::ClassElt>;

fn get_overridden_methods(
    ctx: &provider_context::T,
    origin_class: &str,
    get_or_method: GetMethod<'_>,
    dest_class: &str,
    acc: Vec<MjResult>,
) -> Vec<MjResult> {
    match decl_provider::get_class(None, ctx, dest_class) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
        decl_entry::T::Found(dest_class) => {
            // Check if each destination method exists in the origin
            cls::methods(&dest_class)
                .into_iter()
                .fold(acc, |mut acc, (m_name, de_mthd)| {
                    // Filter out inherited methods
                    if de_mthd.ce_origin != cls::name(&dest_class) {
                        acc
                    } else {
                        let or_mthd = get_or_method(&m_name);
                        match or_mthd {
                            Some(or_mthd) if or_mthd.ce_origin == origin_class => {
                                let get_pos = |ty: &cls::Lazy<ty::decl::Ty<crate::ctx::R>>| {
                                    pos::to_absolute(&naming_provider::resolve_position(
                                        ctx,
                                        &PosOrDecl::from(decl_utils::get_pos(ty)),
                                    ))
                                };
                                acc.insert(
                                    0,
                                    MjResult {
                                        orig_name: m_name.clone(),
                                        orig_pos: get_pos(&or_mthd.ce_type),
                                        dest_name: m_name.clone(),
                                        dest_pos: get_pos(&de_mthd.ce_type),
                                        orig_p_name: origin_class.to_string(),
                                        dest_p_name: cls::name(&dest_class),
                                    },
                                );
                                acc
                            }
                            Some(_) | None => acc,
                        }
                    }
                })
        }
    }
}

fn check_if_extends_class_and_find_methods(
    ctx: &provider_context::T,
    target_class_name: &str,
    get_method: GetMethod<'_>,
    target_class_pos: &PosOrDecl,
    class_name: &str,
    acc: Vec<MjResult>,
) -> Vec<MjResult> {
    let class_ = decl_provider::get_class(None, ctx, class_name);
    match class_ {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => acc,
        decl_entry::T::Found(c) if cls::has_ancestor(&c, target_class_name) => {
            let mut acc = get_overridden_methods(ctx, target_class_name, get_method, class_name, acc);
            acc.insert(
                0,
                MjResult {
                    orig_name: target_class_name.to_string(),
                    orig_pos: pos::to_absolute(&naming_provider::resolve_position(
                        ctx,
                        target_class_pos,
                    )),
                    dest_name: cls::name(&c),
                    dest_pos: pos::to_absolute(&naming_provider::resolve_position(
                        ctx,
                        &cls::pos(&c),
                    )),
                    orig_p_name: "".to_string(),
                    dest_p_name: "".to_string(),
                },
            );
            acc
        }
        _ => acc,
    }
}

fn filter_extended_classes(
    ctx: &provider_context::T,
    target_class_name: &str,
    get_method: GetMethod<'_>,
    target_class_pos: &PosOrDecl,
    acc: Vec<MjResult>,
    classes: &[file_info::Id],
) -> Vec<MjResult> {
    classes.iter().fold(acc, |acc, id| {
        check_if_extends_class_and_find_methods(
            ctx,
            target_class_name,
            get_method,
            target_class_pos,
            &id.name,
            acc,
        )
    })
}

fn find_extended_classes_in_files(
    ctx: &provider_context::T,
    target_class_name: &str,
    get_method: GetMethod<'_>,
    target_class_pos: &PosOrDecl,
    acc: Vec<MjResult>,
    classes: &[Vec<file_info::Id>],
) -> Vec<MjResult> {
    classes.iter().fold(acc, |acc, classes| {
        filter_extended_classes(ctx, target_class_name, get_method, target_class_pos, acc, classes)
    })
}

/// The job of `find_extended_classes_in_files_parallel` on the workers.
#[cfg(feature = "server")]
pub struct MethodJumpsJob;

#[cfg(feature = "server")]
impl crate::multi_worker::ServiceJob for MethodJumpsJob {
    const NAME: &'static str = "Method_jumps.find_extended_classes_in_files";
    type Params = (String, PosOrDecl);
    type Item = Vec<file_info::Id>;
    type Output = Vec<MjResult>;
    fn run(ctx: &provider_context::T, (target_class_name, target_class_pos): &Self::Params, classes: Vec<Vec<file_info::Id>>) -> Self::Output {
        let target = match decl_provider::get_class(None, ctx, target_class_name) {
            decl_entry::T::Found(c) => c,
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                panic!("Method_jumps: class {} not found in a worker", target_class_name)
            }
        };
        let get_method = |name: &str| cls::get_method(&target, name);
        find_extended_classes_in_files(ctx, target_class_name, &get_method, target_class_pos, vec![], &classes)
    }
}

/// Might raise {!Naming_table.File_info_not_found}
fn find_extended_classes_in_files_parallel(
    ctx: &provider_context::T,
    workers: Option<usize>,
    target_class_name: &str,
    get_method: GetMethod<'_>,
    target_class_pos: &PosOrDecl,
    naming_table: &naming_table::T,
    files: &crate::relative_path::set::T,
) -> Result<Vec<MjResult>, FileInfoNotFound> {
    let mut classes: Vec<Vec<file_info::Id>> = vec![];
    for fn_ in files {
        let file_info::FileInfo {
            ids: file_info::Ids { classes: c, .. },
            ..
        } = naming_table::get_file_info_exn(naming_table, fn_)?;
        classes.insert(0, c);
    }
    if classes.len() > 10 {
        // (A folded class cannot cross threads: each job gets the
        // `Cls.get_method` of the target class from its own lookup.)
        let target_class_pos_ = target_class_pos.clone();
        #[cfg(feature = "server")]
        if crate::multi_worker::has_workers() && ctx.worker_snapshot().is_some() {
            return Ok(crate::multi_worker::call_service::<MethodJumpsJob, _>(
                ctx,
                (target_class_name.to_string(), target_class_pos.clone()),
                &classes,
                |output: Vec<MjResult>, acc: Vec<MjResult>| {
                    let mut r: Vec<MjResult> = output.into_iter().rev().collect();
                    r.extend(acc);
                    r
                },
                vec![],
                || false,
                |acc| acc,
            ));
        }
        Ok(find_refs_service::multi_worker_call(
            workers,
            &classes,
            |acc, classes: Vec<Vec<file_info::Id>>| {
                let target = match decl_provider::get_class(None, ctx, target_class_name) {
                    decl_entry::T::Found(c) => c,
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        panic!("Method_jumps: class {} not found in a worker", target_class_name)
                    }
                };
                let get_method = |name: &str| cls::get_method(&target, name);
                find_extended_classes_in_files(
                    ctx,
                    target_class_name,
                    &get_method,
                    &target_class_pos_,
                    acc,
                    &classes,
                )
            },
            Vec::new,
            // `List.rev_append`
            |output, acc| {
                let mut r: Vec<MjResult> = output.into_iter().rev().collect();
                r.extend(acc);
                r
            },
            || false,
        ))
    } else {
        Ok(find_extended_classes_in_files(
            ctx,
            target_class_name,
            get_method,
            target_class_pos,
            vec![],
            &classes,
        ))
    }
}

/// Find child classes.
/// Might raise {!Naming_table.File_info_not_found}
fn get_child_classes_and_methods(
    ctx: &provider_context::T,
    cls_: &cls::T,
    filter: Filter,
    naming_table: &naming_table::T,
    workers: Option<usize>,
) -> Result<Vec<MjResult>, FileInfoNotFound> {
    match filter {
        Filter::NoFilter => {}
        _ => panic!("Method jump filters not implemented for finding children"),
    }
    let files = find_refs_service::get_child_classes_files(ctx, &cls::name(cls_));
    let get_method = |name: &str| cls::get_method(cls_, name);
    find_extended_classes_in_files_parallel(
        ctx,
        workers,
        &cls::name(cls_),
        &get_method,
        &cls::pos(cls_),
        naming_table,
        &files,
    )
}

fn class_passes_filter(filter: Filter, cls_: &cls::T) -> bool {
    use oxidized::ast_defs::ClassishKind;
    match (filter, cls::kind(cls_)) {
        (Filter::NoFilter, _) => true,
        (Filter::Class, ClassishKind::Cclass(_)) => true,
        (Filter::Interface, ClassishKind::Cinterface) => true,
        (Filter::Trait, ClassishKind::Ctrait) => true,
        _ => false,
    }
}

/// Find ancestor classes
pub fn get_ancestor_classes_and_methods(
    ctx: &provider_context::T,
    cls_: &cls::T,
    filter: Filter,
    acc: Vec<MjResult>,
) -> Vec<MjResult> {
    let class_ = decl_provider::get_class(None, ctx, &cls::name(cls_));
    match class_ {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
        decl_entry::T::Found(cls_) => {
            let get_method = |name: &str| cls::get_method(&cls_, name);
            cls::all_ancestor_names(&cls_)
                .into_iter()
                .fold(acc, |acc, k| {
                    let class_ = decl_provider::get_class(None, ctx, &k);
                    match class_ {
                        decl_entry::T::Found(c) if class_passes_filter(filter, &c) => {
                            let mut acc = get_overridden_methods(
                                ctx,
                                &cls::name(&cls_),
                                &get_method,
                                &cls::name(&c),
                                acc,
                            );
                            acc.insert(
                                0,
                                MjResult {
                                    orig_name: utils::strip_ns(&cls::name(&cls_)).to_string(),
                                    orig_pos: pos::to_absolute(&naming_provider::resolve_position(
                                        ctx,
                                        &cls::pos(&cls_),
                                    )),
                                    dest_name: utils::strip_ns(&cls::name(&c)).to_string(),
                                    dest_pos: pos::to_absolute(&naming_provider::resolve_position(
                                        ctx,
                                        &cls::pos(&c),
                                    )),
                                    orig_p_name: "".to_string(),
                                    dest_p_name: "".to_string(),
                                },
                            );
                            acc
                        }
                        _ => acc,
                    }
                })
        }
    }
}

/// Returns a list of the ancestor or child
/// classes and methods for a given class.
/// Might raise {!Naming_table.File_info_not_found}
pub fn get_inheritance(
    ctx: &provider_context::T,
    class_: &str,
    filter: Filter,
    find_children: bool,
    naming_table: &naming_table::T,
    workers: Option<usize>,
) -> Result<Vec<MjResult>, FileInfoNotFound> {
    let class_ = add_ns(class_);
    let class_ = decl_provider::get_class(None, ctx, &class_);
    match class_ {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => Ok(vec![]),
        decl_entry::T::Found(c) => {
            if find_children {
                get_child_classes_and_methods(ctx, &c, filter, naming_table, workers)
            } else {
                Ok(get_ancestor_classes_and_methods(ctx, &c, filter, vec![]))
            }
        }
    }
}
