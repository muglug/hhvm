// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/full_fidelity_parse_service.ml` (and of
//! `Full_fidelity_schema.schema_as_json`). See `hh/PORTING.md`.
//!
//! `SyntaxTree.to_json` of the positioned syntax tree is the JSON that the
//! Rust parser's `positioned_full_trivia_parser::parse_script_to_json` writes
//! (the same tree, the same fields: OCaml's tree is made by this parser);
//! it is read back and printed by `Yojson.Safe.to_string` (`yojson.rs`), so
//! that the escapes and the numbers are Yojson's.
//!
//! `Full_fidelity_schema.schema_as_json ()` is the generated
//! `parser/js/full_fidelity_schema.json`, which the build of the schema
//! checks in (byte for byte what the OCaml prints).

use std::sync::Arc;

use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::parser_env::ParserEnv;
use parser_core_types::source_text::SourceText;

use crate::yojson::safe as yojson;

/// `Full_fidelity_schema.schema_as_json ()`
pub const SCHEMA_AS_JSON: &str = include_str!("../../parser/js/full_fidelity_schema.json");

/// Entry Point: `go filename`. (`Full_fidelity_source_text.from_file` raises
/// `Sys_error` if the file cannot be read: a panic.)
pub fn go(filename: &str) -> String {
    match go_result(filename) {
        Ok(s) => s,
        Err(e) => std::panic::panic_any(e),
    }
}

/// [`go`], with the `Sys_error` (its `Printexc.to_string`) as an `Err`.
pub fn go_result(filename: &str) -> Result<String, String> {
    let file = relative_path::RelativePath::make(relative_path::Prefix::Dummy, filename.into());
    let content = match crate::sys_utils::cat(filename) {
        Ok(content) => content,
        Err(e) => return Err(format!("Sys_error({:?})", e.0)),
    };
    let source_text = SourceText::make(Arc::new(file), &content);
    let indexed = IndexedSourceText::new(source_text);
    let arena = bumpalo::Bump::new();
    let mut out = vec![];
    {
        let mut s = serde_json::Serializer::new(&mut out);
        positioned_full_trivia_parser::parse_script_to_json(&arena, &mut s, &indexed, ParserEnv::default())
            .expect("SyntaxTree.to_json");
    }
    let json = yojson::from_string(&String::from_utf8_lossy(&out)).expect("SyntaxTree.to_json");
    Ok(yojson::to_string(&json))
}
