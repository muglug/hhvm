// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `ide_rpc/nuclide_rpc_message_printer.ml`. See `hh/PORTING.md`.
//!
//! Ported so far (by F5, for the outline and highlight-refs printers):
//! `opt_field`, `string_opt`, `definition_to_json`,
//! `outline_response_to_json`, `highlight_references_response_to_json`,
//! `print_json`. Not yet: `deprecated_pos_field`,
//! `infer_type_response_to_json`, `infer_type_error_response_to_json`,
//! `tast_holes_response_to_json` (the assignments that need them add them
//! here). `identify_symbol_response_to_json`: added by F1.

use std::io::Write as _;

use crate::file_content::position;
use crate::ide_api_types;
use crate::pos;
use crate::pos::Absolute;
use crate::symbol_definition;
use crate::symbol_definition::Kind;
use crate::yojson::safe as yojson;

pub fn opt_field<A>(
    v_opt: Option<A>,
    label: &str,
    f: impl FnOnce(A) -> yojson::T,
) -> Vec<(String, yojson::T)> {
    match v_opt {
        Some(x) => vec![(label.to_string(), f(x))],
        None => vec![],
    }
}

pub fn string_opt(s: Option<String>) -> yojson::T {
    match s {
        Some(s) => yojson::T::String(s),
        None => yojson::T::Null,
    }
}

pub fn identify_symbol_response_to_json(
    results: &[(
        crate::symbol_occurrence::T<Absolute>,
        Option<symbol_definition::T<Absolute>>,
    )],
) -> yojson::T {
    let get_definition_data = |x: &Option<symbol_definition::T<Absolute>>| match x {
        Some(x) => {
            let pos = pos::json(&x.pos);
            let span = pos::multiline_json(&x.span);
            let id = string_opt(symbol_definition::identifier(x));
            (pos, span, id)
        }
        None => (yojson::T::Null, yojson::T::Null, yojson::T::Null),
    };
    let symbol_to_json = |(occurrence, definition): &(
        crate::symbol_occurrence::T<Absolute>,
        Option<symbol_definition::T<Absolute>>,
    )| {
        let (definition_pos, definition_span, definition_id) = get_definition_data(definition);
        yojson::T::Assoc(vec![
            ("name".to_string(), yojson::T::String(occurrence.name.clone())),
            (
                "result_type".to_string(),
                yojson::T::String(crate::symbol_occurrence::kind_to_string(&occurrence.type_).to_string()),
            ),
            ("pos".to_string(), pos::json(&occurrence.pos)),
            ("definition_pos".to_string(), definition_pos),
            ("definition_span".to_string(), definition_span),
            ("definition_id".to_string(), definition_id),
        ])
    };
    yojson::T::List(results.iter().map(symbol_to_json).collect())
}

pub fn definition_to_json(def: &symbol_definition::T<Absolute>) -> yojson::T {
    let modifiers = yojson::T::List(
        def.modifiers
            .iter()
            .map(|x| yojson::T::String(symbol_definition::string_of_modifier(x).to_string()))
            .collect(),
    );
    let children = opt_field(
        match &def.kind {
            Kind::Classish { members, .. } => Some(members),
            _ => None,
        },
        "children",
        |x| outline_response_to_json(x),
    );
    let params = opt_field(def.params.as_ref(), "params", |x| outline_response_to_json(x));
    let docblock = opt_field(def.docblock.as_ref(), "docblock", |x| {
        yojson::T::String(x.clone())
    });
    let mut fields = vec![
        (
            "kind".to_string(),
            yojson::T::String(symbol_definition::string_of_kind(&def.kind).to_string()),
        ),
        ("name".to_string(), yojson::T::String(def.name.clone())),
        ("id".to_string(), string_opt(symbol_definition::identifier(def))),
        ("position".to_string(), pos::json(&def.pos)),
        ("span".to_string(), pos::multiline_json(&def.span)),
        ("modifiers".to_string(), modifiers),
    ];
    fields.extend(children);
    fields.extend(params);
    fields.extend(docblock);
    yojson::T::Assoc(fields)
}

pub fn outline_response_to_json(x: &[symbol_definition::T<Absolute>]) -> yojson::T {
    yojson::T::List(x.iter().map(definition_to_json).collect())
}

pub fn highlight_references_response_to_json(l: &[ide_api_types::Range]) -> yojson::T {
    yojson::T::List(
        l.iter()
            .map(|ide_api_types::Range { st, ed }| {
                let (line, char_start) = position::line_column_one_based(st);
                let (_, char_end) = position::line_column_one_based(ed);
                yojson::T::Assoc(vec![
                    ("line".to_string(), yojson::T::Int(line)),
                    ("char_start".to_string(), yojson::T::Int(char_start)),
                    ("char_end".to_string(), yojson::T::Int(char_end)),
                ])
            })
            .collect(),
    )
}

pub fn print_json(json: &yojson::T) {
    let mut stdout = std::io::stdout().lock();
    let _ = writeln!(stdout, "{}", yojson::to_string(json));
}
