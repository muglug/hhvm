// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_tast_holes_batch.ml` (the `TAST_HOLES_BATCH`
//! command). See `hh/PORTING.md`.

use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::server_command_types::tast_hole::Filter;
use crate::tast_holes_service;

pub fn helper(
    ctx: &provider_context::T,
    acc: tast_holes_service::Result,
    path_list: &[RelativePath],
) -> tast_holes_service::Result {
    let (ctx, tasts) = crate::server_infer_type_batch::get_tast_map(ctx, path_list);
    let mut holes: tast_holes_service::Result = path_list
        .iter()
        .flat_map(|path| {
            // `Relative_path.Map.find tasts path` (raises `Not_found` for a
            // file that could not be read)
            let tast = tasts.get(path).expect("Not_found");
            crate::server_collect_tast_holes::tast_holes(&ctx, &tast.under_normal_assumptions, Filter::Typing)
        })
        .collect();
    holes.extend(acc);
    holes
}

pub fn go(workers: Option<usize>, file_list: &[String], env: &crate::server_env::Env) -> tast_holes_service::Result {
    let mut file_list: Vec<String> = file_list.to_vec();
    file_list.sort();
    file_list.dedup();
    let file_list: Vec<RelativePath> = file_list
        .iter()
        .map(|f| crate::relative_path::create_detect_prefix(f))
        .collect();
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    if file_list.len() < 10 {
        helper(&ctx, vec![], &file_list)
    } else {
        crate::multi_worker::call_service::<TastHolesJob, _>(
            &ctx,
            (),
            &file_list,
            |b: tast_holes_service::Result, c: tast_holes_service::Result| {
                let mut r: tast_holes_service::Result = b.into_iter().rev().collect();
                r.extend(c);
                r
            },
            vec![],
            || false,
            |_| threads(workers, &file_list, &ctx),
        )
    }
}

/// The job of [`go`] on the workers.
pub struct TastHolesJob;

impl crate::multi_worker::ServiceJob for TastHolesJob {
    const NAME: &'static str = "Server_tast_holes_batch.helper";
    type Params = ();
    type Item = RelativePath;
    type Output = tast_holes_service::Result;
    fn run(ctx: &crate::provider_context::T, (): &(), files: Vec<RelativePath>) -> Self::Output {
        helper(ctx, vec![], &files)
    }
}

/// [`go`] without workers.
fn threads(workers: Option<usize>, file_list: &[RelativePath], ctx: &crate::provider_context::T) -> tast_holes_service::Result {
    {
        crate::find_refs_service::multi_worker_call(
            workers,
            file_list,
            |acc: tast_holes_service::Result, files: Vec<RelativePath>| helper(ctx, acc, &files),
            Vec::new,
            // `List.rev_append`
            |b: tast_holes_service::Result, c: tast_holes_service::Result| {
                let mut r: tast_holes_service::Result = b.into_iter().rev().collect();
                r.extend(c);
                r
            },
            || false,
        )
    }
}
