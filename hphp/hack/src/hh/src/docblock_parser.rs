// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `parser/docblock_parser.ml`.

use std::collections::BTreeMap;
use std::sync::LazyLock;

use crate::docblock_finder::stdlib_string_trim;

/// `param_doc_re`: `@param[ ]+\([^ ]+\)[ ]+\(.+\)`, matched at the start
/// (`Str.string_match`, which does not need to reach the end).
static PARAM_DOC_RE: LazyLock<regex::Regex> =
    LazyLock::new(|| regex::Regex::new(r"\A@param[ ]+([^ \n]+)[ ]+(.+)").unwrap());

pub struct ParamInfo {
    pub param_name: String,
    pub param_desc: String,
}

pub fn parse_param_docs(line: &str) -> Option<ParamInfo> {
    let caps = PARAM_DOC_RE.captures(line)?;
    Some(ParamInfo {
        param_name: caps[1].to_string(),
        param_desc: caps[2].to_string(),
    })
}

/// convert all multiline @attribute descriptions to singleline ones
pub fn parse_documentation_attributes(documentation_lines: &[String]) -> Vec<String> {
    // `documentation_attributes` is built by consing: newest first.
    let mut documentation_attributes: Vec<String> = vec![];
    let mut current_attribute: Option<String> = None;
    for line in documentation_lines {
        let trimmed_line = stdlib_string_trim(line);
        // `Str.string_match (Str.regexp "@.*") trimmed_line 0`
        if trimmed_line.starts_with('@') {
            // new attribute
            if let Some(current) = current_attribute.take() {
                // add previous attribute to the list and start building up this one
                documentation_attributes.push(current);
            }
            current_attribute = Some(trimmed_line.to_string());
        } else {
            // either continuing attribute or not related to attributes
            if let Some(current) = current_attribute.as_mut() {
                current.push(' ');
                current.push_str(trimmed_line);
            }
        }
    }
    if let Some(current) = current_attribute {
        // add final attribute
        documentation_attributes.push(current);
    }
    documentation_attributes.reverse();
    documentation_attributes
}

/// Takes a docblock with asterisks and leading/ending slashes removed.
/// Returns the parameters mentioned in the docblock (with @param) and their
/// descriptions with newlines removed.
/// Parameters can be mentioned with the leading '$' or not: they will be
/// indexed in the map with the '$' regardless.
pub fn get_param_docs(docblock: &str) -> BTreeMap<String, String> {
    let documentation_lines = crate::rt::ocaml_str::split("\n", docblock);
    let documentation_attributes = parse_documentation_attributes(&documentation_lines);
    let mut param_docs = BTreeMap::new();
    for line in &documentation_attributes {
        if let Some(param_info) = parse_param_docs(line) {
            let param_name = if param_info.param_name.starts_with('$') {
                param_info.param_name
            } else {
                format!("${}", param_info.param_name)
            };
            param_docs.insert(param_name, param_info.param_desc);
        }
    }
    param_docs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn params() {
        let docs = get_param_docs("Does a thing.\n@param x the x\n  continued\n@param $y why\n@return int");
        assert_eq!(docs.get("$x").map(String::as_str), Some("the x continued"));
        assert_eq!(docs.get("$y").map(String::as_str), Some("why"));
        assert_eq!(crate::rt::ocaml_str::split("\n", "\na\n\nb\n"), vec!["a", "", "b"]);
    }
}
