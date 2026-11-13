// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/docblock_service.ml`.
//!
//! Owned by **F2** (plan §7.3).

use crate::file_content::position;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DocblockElement {
    HackSnippet(String),
    XhpSnippet(String),
    Markdown(String),
}

pub type Result = Vec<DocblockElement>;

/// Represents a symbol location determined by the docblock service
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DbsSymbolLocation {
    pub dbs_filename: String,
    pub dbs_pos: position::T,
    pub dbs_base_class: Option<String>,
}

pub type DbsSymbolLocationResult = Option<DbsSymbolLocation>;
