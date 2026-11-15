// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_rename_types.ml`. See `hh/PORTING.md`.
//!
//! `Server_command_types` (`RENAME`, `IDE_RENAME_BY_SYMBOL`,
//! `REMOVE_DEAD_FIXMES`, ...) carries the types over the socket, so they are
//! `serde` (`Pos.absolute` and `File_content.Position.t` get theirs in
//! `crate::rt::protocol`). `apply_patches_to_file_contents` is not here (a
//! private copy is in `hh_single_type_check::modes`).

use serde::Deserialize;
use serde::Serialize;

use crate::file_content;
use crate::pos::Absolute;
use crate::relative_path::RelativePath;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct InsertPatch {
    pub pos: Absolute,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Patch {
    Insert(InsertPatch),
    Remove(Absolute),
    Replace(InsertPatch),
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Action {
    /// old_name * new_name
    ClassRename(String, String),
    /// class_name * old_name * new_name
    ClassConstRename(String, String, String),
    MethodRename {
        class_name: String,
        old_name: String,
        new_name: String,
    },
    FunctionRename {
        old_name: String,
        new_name: String,
    },
    LocalVarRename {
        filename: RelativePath,
        file_content: String,
        pos: file_content::position::T,
        new_name: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeprecatedWrapperFunctionRef {
    DeprecatedStaticMethodRef,
    DeprecatedNonStaticMethodRef,
    DeprecatedFunctionRef,
}

// ~~ The functions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `get_pos`
pub fn get_pos(p: &Patch) -> &Absolute {
    match p {
        Patch::Insert(patch) | Patch::Replace(patch) => &patch.pos,
        Patch::Remove(p) => p,
    }
}

/// `compare_pos pos1 pos2` (not a total order: overlapping positions are
/// equal)
pub fn compare_pos(pos1: &Absolute, pos2: &Absolute) -> std::cmp::Ordering {
    let (char_start1, char_end1) = crate::pos::info_raw(pos1);
    let (char_start2, char_end2) = crate::pos::info_raw(pos2);
    if char_end1 <= char_start2 {
        std::cmp::Ordering::Less
    } else if char_end2 <= char_start1 {
        std::cmp::Ordering::Greater
    } else {
        std::cmp::Ordering::Equal
    }
}

/// Compare the positions of two patches. Any texts are ignored.
pub fn compare_result(res1: &Patch, res2: &Patch) -> std::cmp::Ordering {
    compare_pos(get_pos(res1), get_pos(res2))
}

/// [write_string_to_file filename content] (`Out_channel.create` raises
/// `Sys_error`: a panic)
pub fn write_string_to_file(fn_: &str, str: &[u8]) {
    if let Err(e) = std::fs::write(fn_, str) {
        std::panic::panic_any(format!("Sys_error({:?})", format!("{}: {}", fn_, e)))
    }
}

fn is_whitespace(c: u8) -> bool {
    matches!(c, b'\n' | b' ' | b'\x0c' | b'\r' | b'\t')
}

/// [write_patches_to_buffer buffer content patches] applies the [patches] to
/// [content] and dump the result in [buffer]
pub fn write_patches_to_buffer(buf: &mut Vec<u8>, original_content: &[u8], patch_list: &[Patch]) {
    let len = original_content.len() as isize;
    let advance_skip_whitespaces = |mut i: isize| -> isize {
        while i < len && is_whitespace(original_content[i as usize]) {
            i += 1
        }
        i
    };
    // Takes the substring of original_content between `i` and `j`
    // and add it to the `buf` buffer.
    // Advance cursor `i` to `j`.
    let add_original_content = |buf: &mut Vec<u8>, i: isize, j: isize| -> isize {
        if j <= i {
            i
        } else {
            let size = j - i;
            let size = std::cmp::min(std::cmp::max(0, std::cmp::max(len - i, 0)), size);
            buf.extend_from_slice(&original_content[i as usize..(i + size) as usize]);
            i + size
        }
    };
    let mut i = 0;
    for patch in patch_list {
        let pos = get_pos(patch);
        let (char_start, char_end) = crate::pos::info_raw(pos);
        i = add_original_content(buf, i, char_start);
        i = match patch {
            Patch::Insert(InsertPatch { text, .. }) => {
                buf.extend_from_slice(text.as_bytes());
                i
            }
            Patch::Replace(InsertPatch { text, .. }) => {
                buf.extend_from_slice(text.as_bytes());
                char_end
            }
            Patch::Remove(_) => advance_skip_whitespaces(char_end),
        };
    }
    let _i = add_original_content(buf, i, len);
}

/// [map_patches_to_filename patches patch] adds [patch] to the
/// filename-indexed [patches] based off of the patch's position filename.
/// (`S_map`: a `BTreeMap`, each list consed.)
pub fn map_patches_to_filename(
    mut acc: std::collections::BTreeMap<String, Vec<Patch>>,
    patch: &Patch,
) -> std::collections::BTreeMap<String, Vec<Patch>> {
    let fn_ = crate::pos::filename(get_pos(patch));
    acc.entry(fn_).or_default().insert(0, patch.clone());
    acc
}

pub fn apply_patches_to_string(old_content: &[u8], patch_list: &[Patch]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(old_content.len());
    let patch_list = crate::rt::ocaml_list::stable_sort(patch_list.to_vec(), compare_result);
    write_patches_to_buffer(&mut buf, old_content, &patch_list);
    buf
}

pub fn list_to_file_map(patches: &[Patch]) -> std::collections::BTreeMap<String, Vec<Patch>> {
    patches.iter().fold(Default::default(), map_patches_to_filename)
}
