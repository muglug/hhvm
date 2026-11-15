// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_deps_out_batch.ml` (the
//! `DEPS_OUT_BATCH` command). See `hh/PORTING.md`.

use std::sync::Arc;

use crate::provider_context;
use crate::server_deps_util::Def;
use crate::server_deps_util::Occ;
use crate::server_deps_util::body_symbols;
use crate::server_deps_util::get_def_setup;
use crate::server_deps_util::is_target;
use crate::symbol_occurrence::Kind;
use crate::yojson::safe::T as Json;

fn build_json_def(def: &Def) -> Json {
    Json::Assoc(vec![
        (
            "kind".to_string(),
            Json::String(crate::symbol_definition::string_of_kind(&def.kind).to_string()),
        ),
        ("name".to_string(), Json::String(crate::symbol_definition::full_name(def))),
        (
            "position".to_string(),
            crate::pos::multiline_json(&crate::pos::to_absolute(&def.pos)),
        ),
    ])
}

fn build_json_entry(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    total_occ_list: &[Occ],
    get_def: &dyn Fn(&Occ) -> Option<Def>,
    occ: &Occ,
) -> Json {
    let def_opt = get_def(occ);
    let depends_json = match def_opt {
        None => Json::String("None".to_string()),
        Some(def) => {
            if occ.is_declaration.is_none() {
                build_json_def(&def)
            } else {
                let body_list = body_symbols(ctx, entry, total_occ_list, occ, &def);
                Json::List(
                    body_list
                        .into_iter()
                        .map(|o| build_json_entry(ctx, entry, total_occ_list, get_def, o))
                        .collect(),
                )
            }
        }
    };
    Json::Assoc(vec![
        (
            "kind".to_string(),
            Json::String(crate::symbol_occurrence::kind_to_string(&occ.type_).to_string()),
        ),
        ("name".to_string(), Json::String(occ.name.clone())),
        (
            "declaration".to_string(),
            match &occ.is_declaration {
                None => Json::Null,
                Some(p) => crate::pos::multiline_json(&crate::pos::to_absolute(p)),
            },
        ),
        (
            "position".to_string(),
            crate::pos::multiline_json(&crate::pos::to_absolute(&occ.pos)),
        ),
        ("depends_on".to_string(), depends_json),
    ])
}

fn interesting_occ(occ: &Occ) -> bool {
    !matches!(
        occ.type_,
        Kind::Keyword(_) | Kind::LocalVar | Kind::BuiltInType(_) | Kind::BestEffortArgument(..)
    )
}

pub fn go_json(server_ctx: &provider_context::T, pos_list: &[(String, isize, isize)]) -> Vec<Json> {
    let mut acc_ctx = server_ctx.clone();
    let mut json_list = vec![];
    for (file, line, column) in pos_list {
        let (acc_ctx_out, entry, ast) = get_def_setup(&acc_ctx, file);
        let get_def = |occ: &Occ| crate::server_symbol_definition::go(&acc_ctx_out, Some(&ast), occ);
        let total_occ_list: Vec<Occ> = crate::identify_symbol_service::all_symbols_ctx(&acc_ctx_out, &entry)
            .into_iter()
            .filter(interesting_occ)
            .collect();
        let symbols: Vec<&Occ> = total_occ_list.iter().filter(|o| is_target(*line, *column, o)).collect();
        let json = Json::List(
            symbols
                .into_iter()
                .map(|o| build_json_entry(&acc_ctx_out, &entry, &total_occ_list, &get_def, o))
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
        .map(crate::yojson::safe::pretty_to_string)
        .collect()
}
