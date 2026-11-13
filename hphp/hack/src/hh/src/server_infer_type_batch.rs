// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_infer_type_batch.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: the positions are all handled by
//! `helper`, as the OCaml handles fewer than ten (with workers, the order of
//! the OCaml results depends on the buckets).

use std::collections::BTreeMap;

use crate::file_content::position;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env;
use crate::server_infer_type;
use crate::tast;
use crate::tast_env;
use crate::tast_provider;
use crate::tast_with_dynamic;
use crate::yojson::safe as yojson;

pub type Pos = (RelativePath, position::T, Option<position::T>);

type Spos = (String, position::T, Option<position::T>);

type Tast = tast_with_dynamic::T<tast::Program>;

fn recheck_typing(
    ctx: &provider_context::T,
    path_list: &[RelativePath],
) -> (provider_context::T, Vec<(RelativePath, Tast)>) {
    let mut files_to_check: Vec<RelativePath> = path_list.to_vec();
    files_to_check.sort_by(relative_path::compare);
    files_to_check.dedup();
    let mut ctx = ctx.clone();
    let mut paths_and_tasts = vec![];
    for path in files_to_check {
        let (ctx_, entry) = provider_context::add_entry_if_missing(&ctx, path.clone());
        ctx = ctx_;
        // (`| exception Sys_error _ -> (ctx, paths_and_tasts)`: a file that
        // cannot be read has no TAST.)
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tast_provider::compute_tast_unquarantined(&ctx, &entry)
        }));
        match result {
            Ok(tast_provider::ComputeTastResult { tast, .. }) => paths_and_tasts.insert(0, (path, tast)),
            Err(payload) => {
                if payload.downcast_ref::<crate::sys_utils::SysError>().is_none() {
                    std::panic::resume_unwind(payload)
                }
            }
        }
    }
    (ctx, paths_and_tasts)
}

pub fn get_tast_map(
    ctx: &provider_context::T,
    path_list: &[RelativePath],
) -> (provider_context::T, BTreeMap<RelativePath, Tast>) {
    let (ctx, paths_and_tasts) = recheck_typing(ctx, path_list);
    (ctx, paths_and_tasts.into_iter().collect())
}

fn result_to_string(result: Result<Option<yojson::T>, String>, (fn_, range_start, range_end): &Pos) -> String {
    let (line, char) = position::line_column_one_based(range_start);
    let mut position_fields = vec![(
        "file".to_string(),
        yojson::T::String(relative_path::to_absolute(fn_)),
    )];
    match range_end {
        None => {
            position_fields.push(("line".to_string(), yojson::T::Int(line)));
            position_fields.push(("character".to_string(), yojson::T::Int(char)));
        }
        Some(range_end) => {
            let (end_line, end_char) = position::line_column_one_based(range_end);
            let pos = |l, c| {
                yojson::T::Assoc(vec![
                    ("line".to_string(), yojson::T::Int(l)),
                    ("character".to_string(), yojson::T::Int(c)),
                ])
            };
            position_fields.push(("start".to_string(), pos(line, char)));
            position_fields.push(("end".to_string(), pos(end_line, end_char)));
        }
    }
    let obj = yojson::T::Assoc(vec![
        ("position".to_string(), yojson::T::Assoc(position_fields)),
        match result {
            Ok(ty) => ("type".to_string(), ty.unwrap_or(yojson::T::Null)),
            Err(e) => ("error".to_string(), yojson::T::String(e)),
        },
    ]);
    yojson::to_string(&obj)
}

fn ty_json(info: &server_infer_type::T) -> yojson::T {
    tast_env::ty_to_json(
        server_infer_type::get_env(info),
        None,
        server_infer_type::get_type(info),
    )
}

fn helper(ctx: &provider_context::T, acc: Vec<String>, pos_list: &[Pos]) -> Vec<String> {
    // (`data :: acc`: the positions of a file, the last one first.)
    let mut at_pos_map: BTreeMap<RelativePath, Vec<position::T>> = BTreeMap::new();
    let mut at_range_map: BTreeMap<RelativePath, Vec<(position::T, position::T)>> = BTreeMap::new();
    for (fn_, range_start, range_end) in pos_list {
        match range_end {
            Some(range_end) => at_range_map
                .entry(fn_.clone())
                .or_default()
                .insert(0, (range_start.clone(), range_end.clone())),
            None => at_pos_map.entry(fn_.clone()).or_default().insert(0, range_start.clone()),
        }
    }
    // (`Relative_path.Map.keys`: a fold that conses, the last key first.)
    let path_list: Vec<RelativePath> = at_pos_map.keys().rev().chain(at_range_map.keys().rev()).cloned().collect();
    let (ctx, tasts) = get_tast_map(ctx, &path_list);
    let mut type_at_range_results: Vec<String> = vec![];
    for (fn_, pos_list) in &at_range_map {
        match tasts.get(fn_) {
            None => {
                for (range_start, range_end) in pos_list {
                    let pos = (fn_.clone(), range_start.clone(), Some(range_end.clone()));
                    type_at_range_results.push(result_to_string(Err("No such file or directory".to_string()), &pos))
                }
            }
            Some(tast) => {
                let results = server_infer_type::type_at_range_fused(&ctx, tast, pos_list);
                if results.len() != pos_list.len() {
                    panic!("Invalid_argument(\"List.map2_exn\")")
                }
                for ((range_start, range_end), info_opt) in pos_list.iter().zip(&results) {
                    let result = info_opt.as_ref().map(ty_json);
                    let pos = (fn_.clone(), range_start.clone(), Some(range_end.clone()));
                    type_at_range_results.push(result_to_string(Ok(result), &pos))
                }
            }
        }
    }
    // `List.concat (Relative_path.Map.values type_at_range_results) @ acc`
    // (`values`: a fold that conses, the last file first.)
    let acc = concat_values_rev(type_at_range_results, &at_range_map.values().map(Vec::len).collect::<Vec<_>>(), acc);
    let mut type_at_pos_results: Vec<String> = vec![];
    for (fn_, pos_list) in &at_pos_map {
        match tasts.get(fn_) {
            None => {
                for range_start in pos_list {
                    let pos = (fn_.clone(), range_start.clone(), None);
                    type_at_pos_results.push(result_to_string(Err("No such file or directory".to_string()), &pos))
                }
            }
            Some(tast) => {
                let results = server_infer_type::type_at_pos_fused(&ctx, tast, pos_list);
                if results.len() != pos_list.len() {
                    panic!("Invalid_argument(\"List.map2_exn\")")
                }
                for (range_start, info_opt) in pos_list.iter().zip(&results) {
                    let result = info_opt.as_ref().map(ty_json);
                    let pos = (fn_.clone(), range_start.clone(), None);
                    type_at_pos_results.push(result_to_string(Ok(result), &pos))
                }
            }
        }
    }
    concat_values_rev(type_at_pos_results, &at_pos_map.values().map(Vec::len).collect::<Vec<_>>(), acc)
}

/// `List.concat (Relative_path.Map.values m) @ acc` where the lists of `m`
/// are `flat` cut into `lens` (in the order of the keys): `values` gives the
/// last key first.
fn concat_values_rev(flat: Vec<String>, lens: &[usize], acc: Vec<String>) -> Vec<String> {
    let mut groups: Vec<Vec<String>> = vec![];
    let mut it = flat.into_iter();
    for len in lens {
        groups.push(it.by_ref().take(*len).collect())
    }
    let mut result: Vec<String> = groups.into_iter().rev().flatten().collect();
    result.extend(acc);
    result
}

pub fn go(pos_list: Vec<Spos>, env: &server_env::Env) -> Vec<String> {
    let mut pos_list = pos_list;
    // Sort, so that many queries on the same file will (generally) be
    // dispatched to the same worker.
    pos_list.sort_by(|a, b| {
        a.0.as_bytes()
            .cmp(b.0.as_bytes())
            .then_with(|| position::compare(&a.1, &b.1).cmp(&0))
            .then_with(|| match (&a.2, &b.2) {
                (None, None) => std::cmp::Ordering::Equal,
                (None, Some(_)) => std::cmp::Ordering::Less,
                (Some(_), None) => std::cmp::Ordering::Greater,
                (Some(x), Some(y)) => position::compare(x, y).cmp(&0),
            })
    });
    // Dedup identical queries
    pos_list.dedup();
    let pos_list: Vec<Pos> = pos_list
        .into_iter()
        .map(|(fn_, range_start, range_end)| (relative_path::create_detect_prefix(&fn_), range_start, range_end))
        .collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    // (`Hack_event_logger.type_at_pos_batch`: a no-op in the OSS build.)
    helper(&ctx, vec![], &pos_list)
}
