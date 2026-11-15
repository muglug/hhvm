// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_infer_type_batch.ml`.

use crate::file_content::position;
use crate::provider_context;
use crate::provider_utils;
use crate::relative_path;
use crate::server_env;
use crate::server_infer_type;
use crate::tast;
use crate::tast_env;
use crate::tast_provider;
use crate::tast_with_dynamic;
use crate::yojson::safe as yojson;

pub type Pos = (relative_path::T, position::T, Option<position::T>);

/// `spos` (`[@@deriving eq, ord]`: the derived order of the tuple)
pub type Spos = (String, position::T, Option<position::T>);

/// Whether a panic payload is OCaml's `Sys_error _`.
fn is_sys_error(e: &(dyn std::any::Any + Send)) -> bool {
    let message = if let Some(s) = e.downcast_ref::<String>() {
        s.as_str()
    } else if let Some(s) = e.downcast_ref::<&str>() {
        s
    } else {
        ""
    };
    message.starts_with("Sys_error")
}

pub fn recheck_typing(
    ctx: &provider_context::T,
    path_list: &[relative_path::T],
) -> (provider_context::T, Vec<(relative_path::T, tast_with_dynamic::T<tast::Program>)>) {
    let mut files_to_check = path_list.to_vec();
    files_to_check.sort_by(relative_path::compare);
    files_to_check.dedup_by(|a, b| relative_path::equal(a, b));
    let mut ctx = ctx.clone();
    let mut paths_and_tasts = vec![];
    for path in files_to_check {
        let (new_ctx, entry) = provider_context::add_entry_if_missing(&ctx, path.clone());
        ctx = new_ctx;
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tast_provider::compute_tast_unquarantined(&ctx, &entry)
        })) {
            Ok(tast_provider::ComputeTast { tast, .. }) => {
                // `(path, tast) :: paths_and_tasts`
                paths_and_tasts.insert(0, (path, tast))
            }
            Err(e) if is_sys_error(&*e) => {}
            Err(e) => std::panic::resume_unwind(e),
        }
    }
    (ctx, paths_and_tasts)
}

pub fn get_tast_map(
    ctx: &provider_context::T,
    path_list: &[relative_path::T],
) -> (provider_context::T, relative_path::map::T<tast_with_dynamic::T<tast::Program>>) {
    let (ctx, paths_and_tasts) = recheck_typing(ctx, path_list);
    let mut tasts = relative_path::map::T::new();
    for (key, data) in paths_and_tasts {
        tasts.insert(key, data);
    }
    (ctx, tasts)
}

fn result_to_string(
    result: Result<Option<yojson::T>, String>,
    (fn_, range_start, range_end): (&relative_path::T, &position::T, Option<&position::T>),
) -> String {
    let (line, char) = position::line_column_one_based(range_start);
    let mut position = vec![(
        "file".to_string(),
        yojson::T::String(relative_path::to_absolute(fn_)),
    )];
    match range_end {
        None => {
            position.push(("line".to_string(), yojson::T::Int(line)));
            position.push(("character".to_string(), yojson::T::Int(char)));
        }
        Some(range_end) => {
            let (end_line, end_char) = position::line_column_one_based(range_end);
            let pos = |l, c| {
                yojson::T::Assoc(vec![
                    ("line".to_string(), yojson::T::Int(l)),
                    ("character".to_string(), yojson::T::Int(c)),
                ])
            };
            position.push(("start".to_string(), pos(line, char)));
            position.push(("end".to_string(), pos(end_line, end_char)));
        }
    }
    let obj = yojson::T::Assoc(vec![
        ("position".to_string(), yojson::T::Assoc(position)),
        match result {
            Ok(ty) => ("type".to_string(), ty.unwrap_or(yojson::T::Null)),
            Err(e) => ("error".to_string(), yojson::T::String(e)),
        },
    ]);
    yojson::to_string(&obj)
}

/// `Relative_path.Map.update fn (function None -> Some [data] | Some acc ->
/// Some (data :: acc)) map`
fn add<A>(map: &mut relative_path::map::T<Vec<A>>, fn_: &relative_path::T, data: A)
where
    A: Clone,
{
    match map.get_mut(fn_) {
        None => {
            map.insert(fn_.clone(), vec![data]);
        }
        Some(acc) => acc.insert(0, data),
    }
}

fn helper(ctx: &provider_context::T, acc: Vec<String>, pos_list: &[Pos]) -> Vec<String> {
    let mut at_pos_map: relative_path::map::T<Vec<position::T>> = relative_path::map::T::new();
    let mut at_range_map: relative_path::map::T<Vec<(position::T, position::T)>> = relative_path::map::T::new();
    for (fn_, range_start, range_end) in pos_list {
        match range_end {
            Some(range_end) => add(&mut at_range_map, fn_, (*range_start, *range_end)),
            None => add(&mut at_pos_map, fn_, *range_start),
        }
    }
    let path_list: Vec<relative_path::T> = at_pos_map.keys().chain(at_range_map.keys()).cloned().collect();
    let (ctx, tasts) = get_tast_map(ctx, &path_list);
    // (`Relative_path.Map.values` is `WrappedMap.values`, a fold that
    // conses: the values in decreasing order of the keys.)
    let type_at_range_results: Vec<Vec<String>> = at_range_map
        .iter()
        .rev()
        .map(|(fn_, pos_list)| match tasts.get(fn_) {
            None => pos_list
                .iter()
                .map(|(range_start, range_end)| {
                    let result = "No such file or directory".to_string();
                    result_to_string(Err(result), (fn_, range_start, Some(range_end)))
                })
                .collect(),
            Some(tast) => {
                let results = server_infer_type::type_at_range_fused(&ctx, tast, pos_list);
                pos_list
                    .iter()
                    .zip(results)
                    .map(|((range_start, range_end), info_opt)| {
                        let result = info_opt.map(|info| {
                            tast_env::ty_to_json(
                                server_infer_type::get_env(&info),
                                None,
                                server_infer_type::get_type(&info),
                            )
                        });
                        result_to_string(Ok(result), (fn_, range_start, Some(range_end)))
                    })
                    .collect()
            }
        })
        .collect();
    let mut acc_ = type_at_range_results.into_iter().flatten().collect::<Vec<_>>();
    acc_.extend(acc);
    let acc = acc_;
    let type_at_pos_results: Vec<Vec<String>> = at_pos_map
        .iter()
        .rev()
        .map(|(fn_, pos_list)| match tasts.get(fn_) {
            None => pos_list
                .iter()
                .map(|range_start| {
                    let result = "No such file or directory".to_string();
                    result_to_string(Err(result), (fn_, range_start, None))
                })
                .collect(),
            Some(tast) => {
                let results = server_infer_type::type_at_pos_fused(&ctx, tast, pos_list);
                pos_list
                    .iter()
                    .zip(results)
                    .map(|(range_start, info_opt)| {
                        let result = info_opt.map(|info| {
                            tast_env::ty_to_json(
                                server_infer_type::get_env(&info),
                                None,
                                server_infer_type::get_type(&info),
                            )
                        });
                        result_to_string(Ok(result), (fn_, range_start, None))
                    })
                    .collect()
            }
        })
        .collect();
    let mut acc_ = type_at_pos_results.into_iter().flatten().collect::<Vec<_>>();
    acc_.extend(acc);
    acc_
}

/// `Multi_worker.call workers ~job ~merge:List.rev_append ~neutral:[]
/// ~next:(Multi_worker.next workers buckets)`, over the buckets of
/// `Hh_bucket.make ~num_workers`: the buckets are done in parallel (each from
/// `neutral`), and merged in the order of the buckets, which is the order of
/// the OCaml when its workers finish in the order they started.
pub fn multi_worker_call_rev_append<Job: Clone + Send + 'static, R: Send>(
    num_workers: isize,
    jobs: Vec<Job>,
    job: impl Fn(Vec<R>, Vec<Job>) -> Vec<R> + Sync,
) -> Vec<R> {
    use rayon::prelude::*;
    let mut next = crate::bucket::make_list(num_workers, None, None, jobs);
    let mut buckets = vec![];
    loop {
        let bucket = next();
        if bucket.is_empty() {
            // `Hh_bucket.Done`
            break;
        }
        buckets.push(bucket);
    }
    let results: Vec<Vec<R>> = buckets
        .into_par_iter()
        .map(|bucket| {
            // (A pool thread forgets its memos if the decls moved:
            // `decl_epoch`'s rule for work items.)
            crate::rt::decl_epoch::sync_thread();
            job(vec![], bucket)
        })
        .collect();
    let mut acc: Vec<R> = vec![];
    for res in results {
        // `List.rev_append res acc`
        let mut merged: Vec<R> = res.into_iter().rev().collect();
        merged.extend(acc);
        acc = merged;
    }
    acc
}

/// This divides files amongst all the workers.
/// No file is handled by more than one worker.
fn parallel_helper(num_workers: isize, ctx: &provider_context::T, pos_list: Vec<Pos>) -> Vec<String> {
    let mut map: relative_path::map::T<Vec<Pos>> = relative_path::map::T::new();
    for pos in pos_list {
        let path = pos.0.clone();
        add(&mut map, &path, pos);
    }
    // (`Relative_path.Map.values`: decreasing order of the keys.)
    let pos_by_file: Vec<Vec<Pos>> = map.into_iter().rev().map(|(_, v)| v).collect();
    // pos_by_file is a list-of-lists [[posA1;posA2;...];[posB1;...];...]
    // where each inner list [posA1;posA2;...] is all for the same file.
    // This is so that a given file is only ever processed by a single worker.
    let buckets = {
        let mut next = crate::bucket::make_list(num_workers, None, None, pos_by_file.clone());
        let mut buckets = vec![];
        loop {
            let bucket = next();
            if bucket.is_empty() {
                break;
            }
            buckets.push(bucket);
        }
        buckets
    };
    crate::multi_worker::call_service_buckets::<InferTypeJob, _>(
        ctx,
        (),
        buckets,
        |res: Vec<String>, acc: Vec<String>| {
            let mut merged: Vec<String> = res.into_iter().rev().collect();
            merged.extend(acc);
            merged
        },
        vec![],
        |_, _| {
            multi_worker_call_rev_append(num_workers, pos_by_file, |acc, pos_by_file| {
                helper(ctx, acc, &pos_by_file.concat())
            })
        },
    )
}

/// The job of [`parallel_helper`] on the workers.
pub struct InferTypeJob;

impl crate::multi_worker::ServiceJob for InferTypeJob {
    const NAME: &'static str = "Server_infer_type_batch.helper";
    type Params = ();
    type Item = Vec<Pos>;
    type Output = Vec<String>;
    fn run(ctx: &provider_context::T, (): &(), pos_by_file: Vec<Vec<Pos>>) -> Self::Output {
        helper(ctx, vec![], &pos_by_file.concat())
    }
}

/// Entry Point
pub fn go(num_workers: isize, pos_list: Vec<Spos>, env: &server_env::Env) -> Vec<String> {
    let mut pos_list = pos_list;
    // Sort, so that many queries on the same file will (generally) be
    // dispatched to the same worker.
    pos_list.sort();
    // Dedup identical queries
    pos_list.dedup();
    let pos_list: Vec<Pos> = pos_list
        .into_iter()
        .map(|(fn_, range_start, range_end)| {
            let fn_ = relative_path::create_detect_prefix(&fn_);
            (fn_, range_start, range_end)
        })
        .collect();
    let num_files = pos_list
        .iter()
        .map(|(path, _, _)| path.clone())
        .collect::<std::collections::BTreeSet<_>>()
        .len();
    let num_positions = pos_list.len();
    let ctx = provider_utils::ctx_from_server_env(env);
    // Just for now, as a rollout telemetry defense against crashes, we'll log at the start
    // (`Hack_event_logger.type_at_pos_batch`: a no-op in the OSS build.)
    let _ = num_files;
    if num_positions < 10 {
        helper(&ctx, vec![], &pos_list)
    } else {
        parallel_helper(num_workers, &ctx, pos_list)
    }
}
