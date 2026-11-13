// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_try.ml`. See `hh/PORTING.md`.
//!
//! The functions are generic in the environment and the continuation, as in
//! the `.ml`; the `.mli` instantiates them at `Typing_env_types.env` and
//! `Typing_per_cont_env.per_cont_entry` (`finally_merge` returns a
//! `Typing_per_cont_env.t` then).

use crate::typing_cont_key;
use crate::typing_continuations as c;

/// `module CMap = Typing_continuations.Map`
pub mod c_map {
    pub use crate::typing_continuations::map::*;
}

// See the type system specs for try for what's going on here

/// `type ('env, 'continuation) union_function`: the environment is threaded
/// (`&mut`), the continuation option is the result.
trait UnionFunction<Env, Continuation>:
    FnMut(&mut Env, c::T, Option<Continuation>, Option<Continuation>) -> Option<Continuation>
{
}

impl<Env, Continuation, F> UnionFunction<Env, Continuation> for F where
    F: FnMut(&mut Env, c::T, Option<Continuation>, Option<Continuation>) -> Option<Continuation>
{
}

fn get_cont_cont<A: Clone>(
    cont_cont_map: &c::map::T<c::map::T<A>>,
    cont1: c::T,
    cont2: c::T,
) -> Option<A> {
    match cont_cont_map.get(&cont1) {
        None => None,
        Some(cont_map) => cont_map.get(&cont2).cloned(),
    }
}

fn make_new_cont<Env, Continuation: Clone>(
    union: &mut impl UnionFunction<Env, Continuation>,
    locals_map: &c::map::T<c::map::T<Continuation>>,
    env: &mut Env,
    cont: c::T,
) -> Option<Continuation> {
    let ctx_cont_next = get_cont_cont(locals_map, cont, c::T::Next);
    // `CMap.map (CMap.find_opt cont) locals_map`
    let ctxs_x_cont: c::map::T<Option<Continuation>> = locals_map
        .iter()
        .map(|(key, cont_map)| (*key, cont_map.get(&cont).cloned()))
        .collect();
    // `CMap.fold_env env union ctxs_x_cont ctx_cont_next`: in the order of
    // the keys, `union env key value acc`.
    let mut acc = ctx_cont_next;
    for (key, ctxopt) in ctxs_x_cont {
        acc = union(env, key, ctxopt, acc);
    }
    acc
}

pub fn finally_merge<Env, Continuation: Clone>(
    mut union: impl FnMut(
        &mut Env,
        c::T,
        Option<Continuation>,
        Option<Continuation>,
    ) -> Option<Continuation>,
    env: &mut Env,
    locals_map: &c::map::T<c::map::T<Continuation>>,
) -> c::map::T<Continuation> {
    let mut make_and_add_new_cont = |env: &mut Env, mut locals: c::map::T<Continuation>, cont| {
        let ctxopt = make_new_cont(&mut union, locals_map, env, cont);
        match ctxopt {
            None => {
                locals.remove(&cont);
            }
            Some(ctx) => {
                locals.insert(cont, ctx);
            }
        }
        locals
    };
    let mut locals = c::map::T::new();
    for cont in typing_cont_key::all() {
        locals = make_and_add_new_cont(env, locals, cont);
    }
    locals
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each union records its call, and keeps the first value it is given.
    #[test]
    fn finally_merge_unions_each_continuation_over_the_continuations_in_key_order() {
        let mut locals_map: c::map::T<c::map::T<&'static str>> = c::map::T::new();
        let mut next = c::map::T::new();
        next.insert(c::T::Next, "next/next");
        next.insert(c::T::Break, "next/break");
        let mut brk = c::map::T::new();
        brk.insert(c::T::Next, "break/next");
        locals_map.insert(c::T::Break, brk);
        locals_map.insert(c::T::Next, next);
        let mut calls: Vec<(c::T, Option<&str>, Option<&str>)> = vec![];
        let res = finally_merge(
            |calls: &mut Vec<_>, key, x: Option<&'static str>, acc: Option<&'static str>| {
                calls.push((key, x, acc));
                acc.or(x)
            },
            &mut calls,
            &locals_map,
        );
        // For `Next`: the initial value is `locals_map[Next][Next]`, then the
        // union over the keys of `locals_map` in order (Next, Break).
        assert_eq!(
            &calls[0..2],
            &[
                (c::T::Next, Some("next/next"), Some("next/next")),
                (c::T::Break, Some("break/next"), Some("next/next")),
            ]
        );
        assert_eq!(res.get(&c::T::Next), Some(&"next/next"));
        // For `Break`: the initial value is `locals_map[Break][Next]`, then the
        // union with `locals_map[Next][Break]` and `locals_map[Break][Break]`.
        assert_eq!(
            &calls[4..6],
            &[
                (c::T::Next, Some("next/break"), Some("break/next")),
                (c::T::Break, None, Some("break/next")),
            ]
        );
        assert_eq!(res.get(&c::T::Break), Some(&"break/next"));
        // Continuations that appear nowhere are absent.
        assert_eq!(res.get(&c::T::Catch), None);
        // Two unions for each of the eight continuations.
        assert_eq!(calls.len(), 16);
    }
}
