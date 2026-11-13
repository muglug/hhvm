// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! format_env.ml

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Env {
    pub add_trailing_commas: bool,
    pub indent_width: isize,
    pub indent_with_tabs: bool,
    pub line_width: isize,
    pub format_generated_code: bool,
    pub version: Option<isize>,
    /// Hakana's formatting rules, which Slack's code is formatted with (on by
    /// default). Off, the output is exactly OCaml hackfmt's. They are:
    /// - a file never starts with a blank line;
    /// - `|?>` is laid out like other binary operators (OCaml lays it out
    ///   like `|>`, which starts its line when the expression splits);
    /// - trivia text is read at the trivium's own position (see
    ///   `syntax::parse`; the parse takes the option separately).
    pub hakana_rules: bool,
}

impl Default for Env {
    fn default() -> Self {
        Env {
            add_trailing_commas: true,
            indent_width: 2,
            indent_with_tabs: false,
            line_width: 80,
            format_generated_code: false,
            version: None,
            hakana_rules: true,
        }
    }
}

impl Env {
    /// If no version is specified, use latest.
    pub fn version_gte(&self, min_version: isize) -> bool {
        match self.version {
            None => true,
            Some(v) => v >= min_version,
        }
    }
}
