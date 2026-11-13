// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_deps_out_batch.ml`. See `hh/PORTING.md`.

use std::sync::Arc;

use crate::nast;
use crate::provider_context;
use crate::server_deps_util::Def;
use crate::server_deps_util::Occ;
use crate::server_deps_util::body_symbols;
use crate::server_deps_util::get_def;
use crate::server_deps_util::get_def_setup;
use crate::server_deps_util::is_target;
use crate::symbol_definition;
use crate::symbol_occurrence::Kind;
use crate::yojson::safe as yojson;

fn multiline_json(pos: &crate::pos::Pos) -> yojson::T {
    crate::pos::multiline_json(&crate::pos::to_absolute(pos))
}

fn build_json_def(def: &Def) -> yojson::T {
    yojson::T::Assoc(vec![
        (
            "kind".to_string(),
            yojson::T::String(symbol_definition::string_of_kind(&def.kind).to_string()),
        ),
        ("name".to_string(), yojson::T::String(symbol_definition::full_name(def))),
        ("position".to_string(), multiline_json(&def.pos)),
    ])
}

fn build_json_entry(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    total_occ_list: &[Occ],
    ast: &nast::Program,
    occ: &Occ,
) -> yojson::T {
    let def_opt = get_def(ctx, ast, occ);
    let depends_json = match &def_opt {
        None => yojson::T::String("None".to_string()),
        Some(def) => {
            if occ.is_declaration.is_none() {
                build_json_def(def)
            } else {
                let body_list = body_symbols(ctx, entry, total_occ_list, occ, def);
                yojson::T::List(
                    body_list
                        .into_iter()
                        .map(|occ| build_json_entry(ctx, entry, total_occ_list, ast, occ))
                        .collect(),
                )
            }
        }
    };
    yojson::T::Assoc(vec![
        (
            "kind".to_string(),
            yojson::T::String(crate::symbol_occurrence::kind_to_string(&occ.type_).to_string()),
        ),
        ("name".to_string(), yojson::T::String(occ.name.clone())),
        (
            "declaration".to_string(),
            match &occ.is_declaration {
                None => yojson::T::Null,
                Some(p) => multiline_json(p),
            },
        ),
        ("position".to_string(), multiline_json(&occ.pos)),
        ("depends_on".to_string(), depends_json),
    ])
}

fn interesting_occ(occ: &Occ) -> bool {
    !matches!(
        occ.type_,
        Kind::Keyword(_) | Kind::LocalVar | Kind::BuiltInType(_) | Kind::BestEffortArgument(..)
    )
}

pub fn go_json(server_ctx: &provider_context::T, pos_list: &[(String, isize, isize)]) -> Vec<yojson::T> {
    let mut acc_ctx = server_ctx.clone();
    let mut json_list = vec![];
    for (file, line, column) in pos_list {
        let (acc_ctx_out, entry, ast) = get_def_setup(&acc_ctx, file);
        let total_occ_list: Vec<Occ> = crate::identify_symbol_service::all_symbols_ctx(&acc_ctx_out, &entry)
            .into_iter()
            .filter(interesting_occ)
            .collect();
        let json = yojson::T::List(
            total_occ_list
                .iter()
                .filter(|occ| is_target(*line, *column, occ))
                .map(|occ| build_json_entry(&acc_ctx_out, &entry, &total_occ_list, &ast, occ))
                .collect(),
        );
        json_list.push(json);
        acc_ctx = acc_ctx_out;
    }
    json_list
}

pub fn go(ctx: &provider_context::T, pos_list: &[(String, isize, isize)]) -> Vec<String> {
    go_json(ctx, pos_list)
        .iter()
        .map(crate::rt::yojson_ext::pretty_to_string)
        .collect()
}
