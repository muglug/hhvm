// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/hover_service.ml`.
//!
//! Owned by **F2** (plan §7.3).

use crate::lsp::MarkedString;
use crate::pos::Pos;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoverInfo {
    pub snippet: Vec<MarkedString>,
    pub addendum: Vec<MarkedString>,
    /// Position of this result.
    pub pos: Option<Pos>,
}

/// `equal_hover_info` (`[@@deriving eq]`)
pub fn equal_hover_info(a: &HoverInfo, b: &HoverInfo) -> bool {
    a == b
}

pub type Result = Vec<HoverInfo>;

pub fn info_as_marked_string_list(info: &HoverInfo) -> Vec<MarkedString> {
    let HoverInfo {
        snippet, addendum, ..
    } = info;
    if snippet.is_empty() {
        // Hack server uses None to indicate absence of a result.
        // We're also catching the non-result [] just in case...
        return vec![];
    }
    let mut res = snippet.clone();
    if !addendum.is_empty() {
        res.push(MarkedString::MarkedString("---".to_string()));
        res.extend(addendum.iter().cloned());
    }
    res
}

pub fn as_marked_string_list(l: &[HoverInfo]) -> Vec<MarkedString> {
    let mut res = vec![];
    for (i, info) in l.iter().enumerate() {
        if i > 0 {
            // `List.intersperse ~sep:[Lsp.MarkedString "---"]`
            res.push(MarkedString::MarkedString("---".to_string()));
        }
        res.extend(info_as_marked_string_list(info));
    }
    res
}

pub fn string_of_result(info: &HoverInfo) -> String {
    let show = |l: &[MarkedString]| {
        l.iter()
            .map(crate::lsp::show_markedString)
            .collect::<Vec<_>>()
            .join("; ")
    };
    format!(
        "{{ snippet = [{}]; addendum = [{}]; pos = {} }}",
        show(&info.snippet),
        show(&info.addendum),
        match &info.pos {
            None => "None".to_string(),
            Some(p) => format!(
                "Some {}",
                crate::rt::ocaml_printf::sprintf_S(&crate::pos::multiline_string_no_file(p))
            ),
        }
    )
}
