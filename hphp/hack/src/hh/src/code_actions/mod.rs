// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of the directory `client/ide_service/code_actions_services/` (its
//! modules are registered here, F7's and F8's in their own blocks).
//!
//! Owned by **F7** (plan §7.3); F8 registers its modules in its own block.
//! Created by W0b. Each assignment appends `pub mod` lines at the end of its
//! block (before its `end` line); do not edit the other blocks.

// ---- F7: code actions I ----
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
// ---- end F7 ----
//
//
// ---- F8: code actions II ----
pub mod code_actions_commands;
pub mod code_actions_cli_lib;
pub mod extract_method;
pub mod inline_method;
pub mod extract_classish;
// ---- end F8 ----
