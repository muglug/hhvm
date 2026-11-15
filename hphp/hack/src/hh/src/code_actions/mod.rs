// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the directory `client/ide_service/code_actions_services/`: its
//! OCaml modules (`Code_actions_services`, `Code_action_types`, the
//! refactors of `refactors/`, …) are the modules registered here. The
//! directory is kept because it mirrors that OCaml source directory; the
//! module names inside are the OCaml module names. (`aast_reduce`,
//! `aast_reduce_gen` and `code_actions_utils` have no OCaml counterpart.)

pub mod code_actions_services;
pub mod code_action_types;
pub mod code_actions_quickfixes;
pub mod quickfixes_from_refactors;
pub mod code_actions_edits_add_attribute;
pub mod code_actions_refactors;
pub mod add_doc_comment;
pub mod flip_around_comma;
pub mod await_expression;
pub mod override_method;
pub mod inline_variable;
pub mod extract_variable;
pub mod extract_shape_type;
pub mod code_actions_utils;
pub mod aast_reduce;
mod aast_reduce_gen;
pub mod code_actions_commands;
pub mod code_actions_cli_lib;
pub mod extract_method_types;
pub mod extract_method_traverse;
pub mod extract_method_to_refactor;
pub mod extract_method;
pub mod extract_method_plugins;
pub mod inline_method_types;
pub mod inline_method_rename;
pub mod inline_method_rewrite_block;
pub mod inline_method_find_candidate;
pub mod inline_method_to_refactor;
pub mod inline_method;
pub mod extract_classish;
pub mod extract_classish_find_candidate;
pub mod extract_classish_to_refactors;
pub mod extract_classish_types;
