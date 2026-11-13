// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_rename.ml`. See `hh/PORTING.md`.

use std::collections::BTreeMap;

use crate::client_connect;
use crate::client_connect::ClientConnectError;
use crate::client_env::ClientCheckEnv;
use crate::client_env::RenameMode;
use crate::server_command_types;
use crate::server_rename_types;
use crate::server_rename_types::Patch;
use crate::yojson::safe as yojson;

fn apply_patches_to_string(old_content: &[u8], patch_list: Vec<Patch>) -> Vec<u8> {
    let mut buf = Vec::with_capacity(old_content.len());
    let patch_list = crate::rt::ocaml_list::stable_sort(patch_list, |a, b| {
        server_rename_types::compare_result(a, b).cmp(&0)
    });
    server_rename_types::write_patches_to_buffer(&mut buf, old_content, &patch_list);
    buf
}

fn apply_patches_to_file(fn_: &str, patch_list: Vec<Patch>) {
    let old_content = match crate::sys_utils::cat(fn_) {
        Ok(content) => content,
        Err(e) => panic!("{:?}", e),
    };
    let new_file_contents = apply_patches_to_string(&old_content, patch_list);
    if let Err(e) = server_rename_types::write_string_to_file(fn_, &new_file_contents) {
        panic!("Sys_error({:?})", e.to_string())
    }
}

fn list_to_file_map(patches: Vec<Patch>) -> BTreeMap<String, Vec<Patch>> {
    patches
        .into_iter()
        .fold(BTreeMap::new(), server_rename_types::map_patches_to_filename)
}

fn plural(count: usize, one: &str, many: &str) -> String {
    let obj = if count == 1 { one } else { many };
    format!("{} {}", count, obj)
}

pub fn apply_patches(patches: Vec<Patch>) {
    let file_map = list_to_file_map(patches);
    let cardinal = file_map.len();
    for (fn_, patch_list) in file_map {
        apply_patches_to_file(&fn_, patch_list)
    }
    println!("Rewrote {}.", plural(cardinal, "file", "files"))
}

fn patch_to_json(res: &Patch) -> yojson::T {
    let (type_, replacement) = match res {
        Patch::Insert(patch) => ("insert", patch.text.as_str()),
        Patch::Replace(patch) => ("replace", patch.text.as_str()),
        Patch::Remove(_) => ("remove", ""),
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
        ("replacement".to_string(), yojson::T::String(replacement.to_string())),
    ])
}

pub fn patches_to_json_string(patches: Vec<Patch>) -> String {
    let file_map = list_to_file_map(patches);
    // (`S_map.fold` conses: the last file first.)
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

pub fn print_patches_json(patches: Vec<Patch>) {
    println!("{}", patches_to_json_string(patches))
}

pub fn go_ide_from_patches(patches: Vec<Patch>, json: bool) {
    if json {
        print_patches_json(patches)
    } else {
        apply_patches(patches)
    }
}

pub fn go(
    conn: impl FnMut() -> Result<client_connect::Conn, ClientConnectError>,
    desc: &str,
    args: &ClientCheckEnv,
    mode: &RenameMode,
    before: &str,
    after: &str,
) -> Result<(), ClientConnectError> {
    let command = match mode {
        RenameMode::Class => server_rename_types::Action::ClassRename(before.to_string(), after.to_string()),
        RenameMode::Function => server_rename_types::Action::FunctionRename {
            old_name: before.to_string(),
            new_name: after.to_string(),
        },
        RenameMode::Method => {
            let befores = crate::rt::ocaml_str::split_literal("::", before);
            if befores.len() != 2 {
                panic!("Failure(\"Before string should be of the format class::method\")")
            }
            let afters = crate::rt::ocaml_str::split_literal("::", after);
            if afters.len() != 2 {
                panic!("Failure(\"After string should be of the format class::method\")")
            }
            let (before_class, before_method) = (befores[0], befores[1]);
            let (after_class, after_method) = (afters[0], afters[1]);
            if before_class != after_class {
                println!("{} {}", before_class, after_class);
                panic!("Failure(\"Before and After classname must match\")")
            } else {
                server_rename_types::Action::MethodRename {
                    class_name: before_class.to_string(),
                    old_name: before_method.to_string(),
                    new_name: after_method.to_string(),
                }
            }
        }
        _ => panic!("Failure(\"Unexpected Mode\")"),
    };
    let patches: Vec<Patch> = client_connect::rpc_with_retry(conn, desc, server_command_types::T::RENAME(command))?;
    if args.output_json {
        print_patches_json(patches)
    } else {
        apply_patches(patches)
    }
    Ok(())
}
