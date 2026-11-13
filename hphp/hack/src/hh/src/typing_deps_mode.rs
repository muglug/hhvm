// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_deps_mode.ml`. See `hh/PORTING.md`.
//!
//! `Typing_deps.Mode` (`module Mode = Typing_deps_mode`) is
//! `crate::typing_deps::mode`, a re-export of this module.

use crate::yojson::safe as yojson;

// CAUTION: This type must be kept in sync with typing_deps.rs
/// Which dependency graph format are we using?
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum T {
    /// Keep track of newly discovered edges in an in-memory delta.
    /// Optionally, the in-memory delta is backed by a pre-computed
    /// Dependency graph stored using a custom file format (.hhdg).
    /// The optional string is the path to that pre-computed depgraph.
    InMemoryMode(Option<String>),
    /// Mode that writes newly discovered edges to binary files on disk
    /// (one file per disk). Those binary files can then be post-processed
    /// using a tool of choice.
    /// The first parameter is (optionally) a path to an existing custom 64-bit
    /// dependency graph. If it is present, only new edges will be written,
    /// of not, all edges will be written.
    SaveToDiskMode {
        graph: Option<String>,
        new_edges_dir: String,
        human_readable_dep_map_dir: Option<String>,
    },
}

/// The mode, as JSON for telemetry, without the paths it holds.
///
/// (The `[@@deriving show]` that follows this function in the OCaml is
/// attached to the `let`, so it derives nothing.)
pub fn to_opaque_json(t: &T) -> yojson::T {
    let string_ = |s: &str| yojson::T::String(s.to_string());
    let string_opt = |o: Option<&str>| match o {
        Some(s) => yojson::T::String(s.to_string()),
        None => yojson::T::Null,
    };
    let opaque = |opt: &Option<String>| opt.as_ref().map(|_| "<opaque>");
    match t {
        T::InMemoryMode(base) => yojson::T::Assoc(vec![
            ("mode".to_string(), string_("InMemoryMode")),
            (
                "props".to_string(),
                yojson::T::Assoc(vec![("base".to_string(), string_opt(opaque(base)))]),
            ),
        ]),
        T::SaveToDiskMode {
            graph,
            new_edges_dir: _,
            human_readable_dep_map_dir,
        } => yojson::T::Assoc(vec![
            ("mode".to_string(), string_("SaveToDiskMode")),
            (
                "props".to_string(),
                yojson::T::Assoc(vec![
                    ("graph".to_string(), string_opt(opaque(graph))),
                    (
                        "human_readable_dep_map_dir".to_string(),
                        string_opt(opaque(human_readable_dep_map_dir)),
                    ),
                ]),
            ),
        ]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opaque_json_hides_the_paths() {
        assert_eq!(
            yojson::to_string(&to_opaque_json(&T::InMemoryMode(Some(
                "/tmp/x.hhdg".to_string()
            )))),
            r#"{"mode":"InMemoryMode","props":{"base":"<opaque>"}}"#
        );
        assert_eq!(
            yojson::to_string(&to_opaque_json(&T::InMemoryMode(None))),
            r#"{"mode":"InMemoryMode","props":{"base":null}}"#
        );
        assert_eq!(
            yojson::to_string(&to_opaque_json(&T::SaveToDiskMode {
                graph: None,
                new_edges_dir: "/tmp/edges".to_string(),
                human_readable_dep_map_dir: Some("/tmp/map".to_string()),
            })),
            r#"{"mode":"SaveToDiskMode","props":{"graph":null,"human_readable_dep_map_dir":"<opaque>"}}"#
        );
    }
}
