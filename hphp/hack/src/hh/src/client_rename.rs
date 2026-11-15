// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_rename.ml`. See `hh/PORTING.md`.

use crate::client_connect;
use crate::client_env;
use crate::client_env::RenameMode;
use crate::hh_client::Exn;
use crate::server_command_types;
use crate::server_rename_types;
use crate::server_rename_types::Patch;
use crate::yojson::safe as yojson;

pub fn apply_patches_to_string(old_content: &[u8], patch_list: &[Patch]) -> Vec<u8> {
    server_rename_types::apply_patches_to_string(old_content, patch_list)
}

pub fn apply_patches_to_file(fn_: &str, patch_list: &[Patch]) {
    let old_content = match crate::sys_utils::cat(fn_) {
        Ok(c) => c,
        Err(e) => std::panic::panic_any(format!("Sys_error({:?})", e.0)),
    };
    let new_file_contents = apply_patches_to_string(&old_content, patch_list);
    server_rename_types::write_string_to_file(fn_, &new_file_contents)
}

fn plural(count: usize, one: &str, many: &str) -> String {
    let obj = if count == 1 { one } else { many };
    format!("{} {}", count, obj)
}

pub fn apply_patches(patches: &[Patch]) {
    let file_map = server_rename_types::list_to_file_map(patches);
    for (fn_, patch_list) in &file_map {
        apply_patches_to_file(fn_, patch_list)
    }
    println!("Rewrote {}.", plural(file_map.len(), "file", "files"));
}

pub fn patch_to_json(res: &Patch) -> yojson::T {
    let (type_, replacement) = match res {
        Patch::Insert(patch) => ("insert", patch.text.clone()),
        Patch::Replace(patch) => ("replace", patch.text.clone()),
        Patch::Remove(_) => ("remove", String::new()),
    };
    let pos = server_rename_types::get_pos(res);
    let (char_start, char_end) = crate::pos::info_raw(pos);
    let (line, start, end_) = crate::pos::info_pos(pos);
    yojson::T::Assoc(vec![
        ("char_start".to_string(), yojson::T::Int(char_start)),
        ("char_end".to_string(), yojson::T::Int(char_end)),
        ("line".to_string(), yojson::T::Int(line)),
        ("col_start".to_string(), yojson::T::Int(start)),
        ("col_end".to_string(), yojson::T::Int(end_)),
        ("patch_type".to_string(), yojson::T::String(type_.to_string())),
        ("replacement".to_string(), yojson::T::String(replacement)),
    ])
}

pub fn patches_to_json_string(patches: &[Patch]) -> String {
    let file_map = server_rename_types::list_to_file_map(patches);
    // `S_map.fold ... (fun fn patch_list acc -> .. :: acc) file_map []`: the
    // files in decreasing order.
    let entries: Vec<yojson::T> = file_map
        .iter()
        .rev()
        .map(|(fn_, patch_list)| {
            yojson::T::Assoc(vec![
                ("filename".to_string(), yojson::T::String(fn_.clone())),
                (
                    "patches".to_string(),
                    yojson::T::List(patch_list.iter().map(patch_to_json).collect()),
                ),
            ])
        })
        .collect();
    yojson::to_string(&yojson::T::List(entries))
}

pub fn print_patches_json(patches: &[Patch]) {
    println!("{}", patches_to_json_string(patches))
}

pub fn go_ide_from_patches(patches: &[Patch], json: bool) {
    if json { print_patches_json(patches) } else { apply_patches(patches) }
}

/// `failwith msg`: `Failure msg`, uncaught.
fn failwith(msg: &str) -> Exn {
    let payload: Box<dyn std::any::Any + Send> = Box::new(format!("Failure({:?})", msg));
    Exn::Other(crate::exception::wrap(payload))
}

pub fn go(
    conn: impl FnMut() -> Result<client_connect::Conn, Exn>,
    desc: &str,
    args: &client_env::ClientCheckEnv,
    mode: &RenameMode,
    before: &str,
    after: &str,
) -> Result<(), Exn> {
    let command = match mode {
        RenameMode::Class => server_rename_types::Action::ClassRename(before.to_string(), after.to_string()),
        RenameMode::Function => server_rename_types::Action::FunctionRename {
            old_name: before.to_string(),
            new_name: after.to_string(),
        },
        RenameMode::Method => {
            let befores = crate::rt::ocaml_str::split("::", before);
            if befores.len() != 2 {
                return Err(failwith("Before string should be of the format class::method"));
            }
            let afters = crate::rt::ocaml_str::split("::", after);
            if afters.len() != 2 {
                return Err(failwith("After string should be of the format class::method"));
            }
            let (before_class, before_method) = (&befores[0], &befores[1]);
            let (after_class, after_method) = (&afters[0], &afters[1]);
            if before_class != after_class {
                print!("{} {}\n", before_class, after_class);
                return Err(failwith("Before and After classname must match"));
            } else {
                server_rename_types::Action::MethodRename {
                    class_name: before_class.clone(),
                    old_name: before_method.clone(),
                    new_name: after_method.clone(),
                }
            }
        }
        RenameMode::Unspecified => return Err(failwith("Unexpected Mode")),
    };
    let patches: Vec<Patch> = crate::client_check::rpc_with_retry(conn, desc, server_command_types::T::Rename(command))?;
    if args.output_json {
        print_patches_json(&patches)
    } else {
        apply_patches(&patches)
    }
    Ok(())
}
