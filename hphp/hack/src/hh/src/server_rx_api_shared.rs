// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_rx_api_shared.ml`. See `hh/PORTING.md`.
//!
//! The record of handlers is a trait; `find_in_tree` is a reduce visitor
//! over the option monoid whose `merge` is the walker's `plus`.

use std::collections::BTreeMap;

use oxidized::aast_visitor::Visitor;

use crate::provider_context;
use crate::relative_path::RelativePath;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::IterParams;
use crate::tast_visitor::Reduce;
use crate::tast_visitor::Res;
use crate::tast_visitor::reduce;
use crate::yojson::safe::T as Json;

pub type Pos = (RelativePath, isize, isize);

pub type Spos = (String, isize, isize);

pub fn pos_to_json(fn_: &RelativePath, line: isize, char: isize) -> Json {
    Json::Assoc(vec![
        ("file".to_string(), Json::String(crate::relative_path::to_absolute(fn_))),
        ("line".to_string(), Json::Int(line)),
        ("character".to_string(), Json::Int(char)),
    ])
}

pub fn compute_tasts(
    ctx: &provider_context::T,
    pos_list: &[Pos],
) -> Vec<(RelativePath, crate::tast_with_dynamic::T<tast::Program>)> {
    let mut files_to_check: Vec<&RelativePath> = pos_list.iter().map(|(path, _, _)| path).collect();
    files_to_check.dedup();
    files_to_check
        .into_iter()
        .map(|path| {
            let (_ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let crate::tast_provider::ComputeTast { tast, .. } =
                crate::tast_provider::compute_tast_unquarantined(ctx, &entry);
            (path.clone(), tast)
        })
        .collect()
}

pub fn pos_contains_line_char(pos: &oxidized::pos::Pos, line: isize, char: isize) -> bool {
    let (l, start, end_) = crate::pos::info_pos(pos);
    l == line && start <= char && char - 1 <= end_
}

/// `('a, 'r, 's) handlers` (with `'a walker`)
pub trait Handlers: Sync {
    /// The name of the job of these handlers on the workers
    /// (`crate::worker_jobs`), and the handlers a clone uses.
    const JOB_NAME: &'static str;
    fn make() -> Self;
    type A;
    type R;
    type S;
    fn result_to_string(&self, result: Result<Option<Self::R>, String>, pos: &Pos) -> String;
    fn plus(&self, a: Self::A, b: Self::A) -> Self::A;
    fn on_method(&self, env: &mut Env, m: &tast::Method_) -> Self::A;
    fn on_fun_def(&self, env: &mut Env, fd: &tast::FunDef) -> Self::A;
    fn get_state(&self, ctx: &provider_context::T, fn_: &RelativePath) -> Self::S;
    fn map_result(&self, ctx: &provider_context::T, s: &Self::S, a: Self::A) -> Self::R;
}

struct FindInTree<'h, H: Handlers> {
    h: &'h H,
    line: isize,
    char: isize,
    acc: Option<H::A>,
}

impl<'a, H: Handlers> Reduce<'a> for FindInTree<'_, H> {
    type Acc = Option<H::A>;

    fn zero(&self) -> Self::Acc {
        None
    }

    fn plus(&self, a: Self::Acc, b: Self::Acc) -> Self::Acc {
        match (a, b) {
            (None, b) => b,
            (a, None) => a,
            (Some(a), Some(b)) => Some(self.h.plus(a, b)),
        }
    }

    fn acc(&mut self) -> &mut Self::Acc {
        &mut self.acc
    }
}

impl<'a, H: Handlers> Visitor<'a> for FindInTree<'_, H> {
    type Params = IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    tast_visitor::reduce_methods!('a; expr_, fun_, class_var, expression_tree);

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Res {
        if pos_contains_line_char(&m.name.0, self.line, self.char) {
            let r = Some(self.h.on_method(env, m));
            reduce::add(self, r)
        }
        Ok(())
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Res {
        if pos_contains_line_char(&fd.name.0, self.line, self.char) {
            let r = Some(self.h.on_fun_def(env, fd));
            reduce::add(self, r)
        }
        Ok(())
    }
}

/// `prepare_pos_infos`
pub fn prepare_pos_infos(pos_list: &[Spos]) -> Vec<Pos> {
    // Sort, so that many queries on the same file will (generally) be
    // dispatched to the same worker.
    let mut pos_list = pos_list.to_vec();
    pos_list.sort();
    // Dedup identical queries
    pos_list.dedup();
    pos_list
        .into_iter()
        .map(|(path, line, char)| (crate::relative_path::create_detect_prefix(&path), line, char))
        .collect()
}

pub fn helper<H: Handlers>(h: &H, ctx: &provider_context::T, acc: Vec<String>, pos_list: &[Pos]) -> Vec<String> {
    let tasts: BTreeMap<RelativePath, _> = compute_tasts(ctx, pos_list).into_iter().collect();
    let mut acc = acc;
    for pos in pos_list {
        let (fn_, line, char) = pos;
        let s = h.get_state(ctx, fn_);
        let result = match tasts.get(fn_) {
            None => Err("No such file or directory".to_string()),
            Some(tast) => {
                let mut v = FindInTree {
                    h,
                    line: *line,
                    char: *char,
                    acc: None,
                };
                Ok(reduce::go(&mut v, ctx, &tast.under_normal_assumptions).map(|a| h.map_result(ctx, &s, a)))
            }
        };
        acc.insert(0, h.result_to_string(result, pos));
    }
    acc
}

/// The job of [`go`] on the workers, for the handlers `H`.
pub struct RxApiJob<H>(std::marker::PhantomData<H>);

impl<H: Handlers + 'static> crate::multi_worker::ServiceJob for RxApiJob<H> {
    const NAME: &'static str = H::JOB_NAME;
    type Params = ();
    type Item = Pos;
    type Output = Vec<String>;
    fn run(ctx: &provider_context::T, (): &(), positions: Vec<Pos>) -> Self::Output {
        helper(&H::make(), ctx, vec![], &positions)
    }
}

/// Entry Point
pub fn go<H: Handlers + 'static>(
    workers: Option<usize>,
    pos_list: &[Spos],
    env: &crate::server_env::Env,
    h: &H,
) -> Vec<String> {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let pos_list = prepare_pos_infos(pos_list);
    if pos_list.len() < 10 {
        helper(h, &ctx, vec![], &pos_list)
    } else if crate::multi_worker::has_workers() && ctx.worker_snapshot().is_some() {
        crate::multi_worker::call_service::<RxApiJob<H>, _>(
            &ctx,
            (),
            &pos_list,
            |b: Vec<String>, c: Vec<String>| {
                let mut r: Vec<String> = b.into_iter().rev().collect();
                r.extend(c);
                r
            },
            vec![],
            || false,
            |acc| acc,
        )
    } else {
        crate::find_refs_service::multi_worker_call(
            workers,
            &pos_list,
            |acc: Vec<String>, positions: Vec<Pos>| helper(h, &ctx, acc, &positions),
            Vec::new,
            // `List.rev_append`
            |b: Vec<String>, c: Vec<String>| {
                let mut r: Vec<String> = b.into_iter().rev().collect();
                r.extend(c);
                r
            },
            || false,
        )
    }
}
