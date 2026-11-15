// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! hackfmt, the Hack code formatter: a Rust port of hphp/hack/src/hackfmt
//! (the OCaml sources are the reference) and of its command line,
//! hphp/hack/src/hackfmt.ml.

pub mod boundaries;
pub mod chunk;
pub mod chunk_builder;
pub mod cli;
mod config_file;
pub mod debug;
pub mod doc;
pub mod error;
pub mod format_env;
pub mod hack_format;
pub mod interval;
pub mod libhackfmt;
pub mod line_splitter;
pub mod noformat;
pub mod solve_state;
pub mod subchunk;
pub mod syntax;
mod syntax_fields;

pub use error::Exn;
pub use format_env::Env;
pub use interval::Interval;
pub use syntax::SyntaxTree;

/// Parse `text` (the parser sees it as a file named `path`) and return the
/// tree and the syntax errors. `hakana_rules` should match
/// [`Env::hakana_rules`] of the formatting.
pub fn parse<'a>(text: &'a [u8], path: &str, enable_xhp_class_modifier: bool, hakana_rules: bool) -> SyntaxTree<'a> {
    syntax::parse(text, path, enable_xhp_class_modifier, hakana_rules)
}

/// `Libhackfmt.format_tree`. Raises (panics with) an [`Exn`] on failure; use
/// [`error::catch`] to get it as a `Result`.
pub fn format_tree(config: Option<&Env>, tree: &SyntaxTree<'_>) -> Vec<u8> {
    libhackfmt::format_tree(config, tree)
}

/// `Libhackfmt.format_range`: format a half-open byte range.
pub fn format_range(config: Option<&Env>, range: Interval, tree: &SyntaxTree<'_>) -> Vec<u8> {
    libhackfmt::format_range(config, range, tree)
}

/// `Libhackfmt.format_intervals`: format 1-based, inclusive line intervals.
pub fn format_intervals(config: Option<&Env>, intervals: &[Interval], tree: &SyntaxTree<'_>) -> Vec<u8> {
    libhackfmt::format_intervals(config, intervals, tree)
}

/// `Libhackfmt.format_at_offset`
pub fn format_at_offset(config: Option<&Env>, tree: &SyntaxTree<'_>, offset: isize) -> (Interval, Vec<u8>) {
    libhackfmt::format_at_offset(config, tree, offset)
}
