// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `server/server_rx_api_shared.ml`. See `hh/PORTING.md`.
//!
//! `Multi_worker.call` is not used: the positions are all handled by
//! `helper`.

use std::collections::BTreeMap;

use crate::code_actions::aast_reduce;
use crate::code_actions::aast_reduce::Reducer;
use crate::pos::Pos;
use crate::provider_context;
use crate::relative_path;
use crate::relative_path::RelativePath;
use crate::server_env;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_provider;
use crate::tast_visitor::IterParams;
use crate::tast_with_dynamic;
use crate::yojson::safe as yojson;

pub type PosT = (RelativePath, isize, isize);

pub type Spos = (String, isize, isize);

pub fn pos_to_json(fn_: &RelativePath, line: isize, char: isize) -> yojson::T {
    yojson::T::Assoc(vec![
        ("file".to_string(), yojson::T::String(relative_path::to_absolute(fn_))),
        ("line".to_string(), yojson::T::Int(line)),
        ("character".to_string(), yojson::T::Int(char)),
    ])
}

fn compute_tasts(
    ctx: &provider_context::T,
    pos_list: &[PosT],
) -> Vec<(RelativePath, tast_with_dynamic::T<tast::Program>)> {
    let mut files_to_check: Vec<RelativePath> = pos_list.iter().map(|(path, _, _)| path.clone()).collect();
    files_to_check.dedup();
    files_to_check
        .into_iter()
        .map(|path| {
            let (_ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
            let tast_provider::ComputeTastResult { tast, .. } = tast_provider::compute_tast_unquarantined(ctx, &entry);
            (path, tast)
        })
        .collect()
}

fn pos_contains_line_char(pos: &Pos, line: isize, char: isize) -> bool {
    let (l, start, end_) = crate::pos::info_pos(pos);
    l == line && start <= char && char - 1 <= end_
}

pub struct Walker<A> {
    pub plus: fn(A, A) -> A,
    pub on_method: fn(&mut Env, &tast::Method_) -> A,
    pub on_fun_def: fn(&mut Env, &tast::FunDef) -> A,
}

struct FindInTree<'w, A> {
    walker: &'w Walker<A>,
    line: isize,
    char: isize,
}

impl<'a, A> Reducer<'a, IterParams, Option<A>> for FindInTree<'_, A> {
    fn object(&mut self) -> &mut dyn Reducer<'a, IterParams, Option<A>> {
        self
    }
    // `Visitors_runtime.option_monoid` with `merge = walker.plus`
    fn zero(&mut self) -> Option<A> {
        None
    }
    fn plus(&mut self, a: Option<A>, b: Option<A>) -> Option<A> {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some((self.walker.plus)(a, b)),
        }
    }
    aast_reduce::tast::tast_methods!('a, Option<A>; expr_, fun_, class_var, expression_tree);

    fn visit_method_(&mut self, env: &mut Env, m: &'a tast::Method_) -> Option<A> {
        if pos_contains_line_char(&m.name.0, self.line, self.char) {
            Some((self.walker.on_method)(env, m))
        } else {
            None
        }
    }

    fn visit_fun_def(&mut self, env: &mut Env, fd: &'a tast::FunDef) -> Option<A> {
        if pos_contains_line_char(&fd.name.0, self.line, self.char) {
            Some((self.walker.on_fun_def)(env, fd))
        } else {
            None
        }
    }
}

pub struct Handlers<A, R, S> {
    pub result_to_string: fn(Result<Option<R>, String>, &PosT) -> String,
    pub walker: Walker<A>,
    pub get_state: fn(&provider_context::T, &RelativePath) -> S,
    pub map_result: fn(&provider_context::T, &S, A) -> R,
}

fn prepare_pos_infos(pos_list: Vec<Spos>) -> Vec<PosT> {
    let mut pos_list = pos_list;
    // Sort, so that many queries on the same file will (generally) be
    // dispatched to the same worker.
    pos_list.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)));
    // Dedup identical queries
    pos_list.dedup();
    pos_list
        .into_iter()
        .map(|(path, line, char)| (relative_path::create_detect_prefix(&path), line, char))
        .collect()
}

fn helper<A, R, S>(
    h: &Handlers<A, R, S>,
    ctx: &provider_context::T,
    mut acc: Vec<String>,
    pos_list: &[PosT],
) -> Vec<String> {
    let tasts: BTreeMap<RelativePath, tast_with_dynamic::T<tast::Program>> =
        compute_tasts(ctx, pos_list).into_iter().collect();
    for pos in pos_list {
        let (fn_, line, char) = pos;
        let s = (h.get_state)(ctx, fn_);
        let result = match tasts.get(fn_) {
            None => Err("No such file or directory".to_string()),
            Some(tast) => {
                let mut visitor = FindInTree {
                    walker: &h.walker,
                    line: *line,
                    char: *char,
                };
                Ok(aast_reduce::tast::go(&mut visitor, ctx, &tast.under_normal_assumptions)
                    .map(|a| (h.map_result)(ctx, &s, a)))
            }
        };
        acc.insert(0, (h.result_to_string)(result, pos))
    }
    acc
}

pub fn go<A, R, S>(pos_list: Vec<Spos>, env: &server_env::Env, h: &Handlers<A, R, S>) -> Vec<String> {
    let ctx = crate::provider_utils::ctx_from_server_env(env);
    let pos_list = prepare_pos_infos(pos_list);
    helper(h, &ctx, vec![], &pos_list)
}
