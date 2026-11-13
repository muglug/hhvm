// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/full_fidelity_parse_service.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::source_text::SourceText;

/// `SyntaxTree.to_json (SyntaxTree.make source_text) |> Yojson.Safe.to_string`
/// of the file `filename` (a `Dummy` path): the parse tree with all its
/// trivia, the text of the program and the version of the schema.
pub fn go(filename: &str) -> String {
    let file = relative_path::RelativePath::make(relative_path::Prefix::Dummy, filename.into());
    // `Full_fidelity_source_text.from_file file`
    let content = match crate::sys_utils::cat(filename) {
        Ok(content) => content,
        Err(e) => panic!("{:?}", e),
    };
    let source_text = SourceText::make(Arc::new(file), &content);
    let indexed = IndexedSourceText::new(source_text);
    let arena = bumpalo::Bump::new();
    let mut buf = vec![];
    let mut serializer = serde_json::Serializer::new(&mut buf);
    if let Err(e) = positioned_full_trivia_parser::parse_script_to_json(
        &arena,
        &mut serializer,
        &indexed,
        parser_core_types::parser_env::ParserEnv::default(),
    ) {
        panic!("Failure({:?})", e.to_string())
    }
    String::from_utf8_lossy(&buf).into_owned()
}
