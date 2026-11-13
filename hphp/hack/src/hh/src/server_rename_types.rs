// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_rename_types.ml`. See `hh/PORTING.md`.
//!
//! Only the types are ported so far, by the client-connection assignment
//! (D1): `Server_command_types` (`RENAME`, `IDE_RENAME_BY_SYMBOL`,
//! `REMOVE_DEAD_FIXMES`, ...) carries them over the socket, so they are
//! `serde` (`Pos.absolute` and `File_content.Position.t` get theirs in
//! `crate::rt::protocol`). The functions (`get_pos`, `compare_result`,
//! `write_string_to_file`, `write_patches_to_buffer`,
//! `map_patches_to_filename`, `apply_patches_to_file_contents`) belong to the
//! find-refs/rename assignment (F6), which keeps these types.

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
