// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_per_cont_ops.ml`. See `hh/PORTING.md`.
//!
//! Functions dealing with continuation based flow typing of local variables.
//!
//! `'a locals_merge_fn`, the function that's used to merge locals from two
//! environments (`'a -> local -> local -> 'a * local`, where `'a` is always
//! the typing environment), is
//! `impl FnMut(&mut Env, &Local, &Local) -> Local`.
//!
//! As in `typing_per_cont_env`, the map of continuations that a function
//! updates is taken by value and returned.

use crate::type_parameter_env_ops;
use crate::typing_continuations as c;
use crate::typing_defs_core::Ty;
use crate::typing_env_types::Env;
use crate::typing_fake_members;
use crate::typing_local_packages;
use crate::typing_local_types;
use crate::typing_local_types::Local;
use crate::typing_per_cont_env as lenvc;
use crate::typing_per_cont_env::PerContEntry;

fn union(
    mut union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    env: &mut Env,
    context1: &PerContEntry,
    context2: &PerContEntry,
) -> PerContEntry {
    // `LMap.merge`, with a function that keeps the locals that are in both
    // contexts. `Map.merge` is
    //   concat_or_join (merge f l1 l2) v (f v d1 d2) (merge f r1 r2)
    // and OCaml evaluates the arguments of an application from right to left,
    // so the types are merged from the greatest local id to the smallest.
    //
    // `union_types` is `Typing_lenv.union`: given the same local twice, it
    // gives back an equal local and has no effect (`Typing_union.union` of a
    // type with itself is that type, without logging when no log level is
    // set). So a local that the two contexts share (the same entry, unchanged
    // since they were copied from one another) is kept as it is, without the
    // call, and two maps that are the same tree give that tree.
    let can_share = env.log_levels.is_empty();
    let local_types = if can_share && context1.local_types.ptr_eq(&context2.local_types) {
        context1.local_types.clone()
    } else {
        let mut local_types = typing_local_types::empty();
        for entry1 in context1.local_types.entries().rev() {
            let (key, ty1) = &**entry1;
            if let Some(entry2) = context2.local_types.get_entry(key) {
                if can_share && std::rc::Rc::ptr_eq(entry1, entry2) {
                    local_types.insert_entry(std::rc::Rc::clone(entry1));
                } else {
                    let ty = union_types(env, ty1, &entry2.1);
                    local_types.insert(key.clone(), ty);
                }
            }
        }
        local_types
    };
    // TODO: we could do better here in case only in one side.
    let tpenv = type_parameter_env_ops::join(env, &context1.tpenv, &context2.tpenv);
    let fake_members = typing_fake_members::join(&context1.fake_members, &context2.fake_members);
    let loaded_packages =
        typing_local_packages::join(&context1.loaded_packages, &context2.loaded_packages);
    PerContEntry {
        fake_members,
        local_types,
        tpenv,
        loaded_packages,
    }
}

/// Unions two context options. We call "context" here a map from locals to
/// types.
/// Intersect the set of keys, and for each key in both contexts, union their
/// associated types.
/// More formally, the union c1 & c2 of contexts
/// c1 and c2 is defined as:
/// (x: T) belongs to c1 & c2 iif there exist T1, T2 such that:
///   - (x: T1) belongs to c1
///   - (x: T2) belongs to c2
///   - T = T1 | T2
///
/// Example:
///   context1 = { x: A, y: B }
///   context2 = { z: C, y: D }
///   union context1 context2 = { y: (B|D) }
pub fn union_opts(
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    env: &mut Env,
    ctxopt1: Option<PerContEntry>,
    ctxopt2: Option<PerContEntry>,
) -> Option<PerContEntry> {
    match (ctxopt1, ctxopt2) {
        (None, opt) | (opt, None) => opt,
        (Some(ctx1), Some(ctx2)) => Some(union(union_types, env, &ctx1, &ctx2)),
    }
}

/// Does per-cont entry ctx1 entail ctx2?
///   For locals, for each x:t2 in ctx2 we require x:t1 in ctx1 with t1 <: t2
///   For fake member info, we delegate to Typing_fake_members.sub
///   TODO: tpenv. Not clear what to do here, as we generate fresh type parameter names
///     and so use of is_sub_entry for loop iteration would return false even if safe
fn is_sub_entry(
    mut is_subtype: impl FnMut(&Env, &Ty, &Ty) -> bool,
    env: &Env,
    ctx1: &PerContEntry,
    ctx2: &PerContEntry,
) -> bool {
    // `LMap.for_all2` builds the map of the results with `LMap.merge` before
    // it looks at any of them: `is_subtype` is called for every local that is
    // in both contexts, from the greatest id to the smallest (see `union`). A
    // local that is only in `ctx1` gives `true`, one that is only in `ctx2`
    // gives `false`.
    let mut locals = true;
    for (key, local2) in ctx2.local_types.iter().rev() {
        let b = match ctx1.local_types.get(key) {
            None => false,
            Some(local1) => is_subtype(env, &local1.ty, &local2.ty),
        };
        locals = locals && b;
    }
    locals
        && typing_fake_members::sub(&ctx1.fake_members, &ctx2.fake_members)
        && typing_local_packages::sub(&ctx1.loaded_packages, &ctx2.loaded_packages)
}

pub fn is_sub_opt_entry(
    is_subtype: impl FnMut(&Env, &Ty, &Ty) -> bool,
    env: &Env,
    ctxopt1: Option<&PerContEntry>,
    ctxopt2: Option<&PerContEntry>,
) -> bool {
    match (ctxopt1, ctxopt2) {
        (_, None) => true,
        (None, _) => false,
        (Some(ctx1), Some(ctx2)) => is_sub_entry(is_subtype, env, ctx1, ctx2),
    }
}

/// Union a list of continuations
fn union_conts(
    env: &mut Env,
    mut union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    local_types: &lenvc::T,
    cont_list: &[c::T],
) -> Option<PerContEntry> {
    let mut locals = None;
    for cont in cont_list {
        locals = union_opts(
            &mut union_types,
            env,
            locals,
            local_types.get(cont).cloned(),
        );
    }
    locals
}

/// Union a list of source continuations and store the result in a
/// destination continuation.
fn union_conts_and_update(
    env: &mut Env,
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    local_types: lenvc::T,
    from_conts: &[c::T],
    to_cont: c::T,
) -> lenvc::T {
    let unioned = union_conts(env, union_types, &local_types, from_conts);
    lenvc::replace_cont(to_cont, unioned, local_types)
}

/// Merge all continuations in the provided list and update the next
/// continuation with the result.
///
/// This is used at certain merge points in the control flow. For example,
/// after a loop, we want to merge the 'break' continuation into the 'next'
/// continuation, or at the beginning of a loop block, we merge the 'continue'
/// continuation into the 'next' continuation.
pub fn update_next_from_conts(
    env: &mut Env,
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    local_types: lenvc::T,
    cont_list: &[c::T],
) -> lenvc::T {
    union_conts_and_update(env, union_types, local_types, cont_list, c::T::Next)
}

/// After this call, the provided continuation will be the union of
/// itself and the next continuation.
///
/// This is used at split points in the control flow.
/// For example, if we encounter a function call that may throw an exception,
/// we "save" the 'next' continuation by "merging" it into the 'catch'
/// continuation.
pub fn save_and_merge_next_in_cont(
    env: &mut Env,
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    local_types: lenvc::T,
    cont: c::T,
) -> lenvc::T {
    union_conts_and_update(env, union_types, local_types, &[c::T::Next, cont], cont)
}

/// union the provided continuation with the next continuation and store
/// the result in the provided continuation. Finally, remove the next
/// continuation.
///
/// This is used at jump points in the control flow.
/// For example, when we encounter a 'continue' statement, we "move" the 'next'
/// continuation by "merging" it into the 'continue' continuation.
pub fn move_and_merge_next_in_cont(
    env: &mut Env,
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    local_types: lenvc::T,
    cont: c::T,
) -> lenvc::T {
    let locals = save_and_merge_next_in_cont(env, union_types, local_types, cont);
    lenvc::drop_cont(c::T::Next, locals)
}

/// union all continuations pairwise from two continuation maps.
/// This is used at certain merge points in the control flow,
/// typically after an `if` or a `switch` statement.
///
/// Example:
///   locals1 = {
///     Next:     { x: A, y: B },
///     Continue: { x: A, y: B },
///     Break:    { x: A, y: B },
///   }
///   locals2 = {
///     Next:     { z: C, y: D },
///     Continue: { z: C, y: D },
///     Catch:    { z: C, y: D },
///   }
///   union_by_cont locals1 locals2 = {
///     Next:     { y: (B|D) },
///     Continue: { y: (B|D) },
///     Break:    { x: A, y: B },
///     Catch:    { z: C, y: D },
///   }
pub fn union_by_cont(
    env: &mut Env,
    mut union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    locals1: &lenvc::T,
    locals2: &lenvc::T,
) -> lenvc::T {
    // `CMap.union_env` is `merge_env`: first the bindings of `locals2`, in
    // increasing order, combined with those of `locals1`; then the bindings
    // that are only in `locals1`.
    let mut map = lenvc::T::new();
    for (key, cont2) in locals2.iter() {
        let ctx = match locals1.get(key) {
            None => cont2.clone(),
            Some(cont1) => union(&mut union_types, env, cont1, cont2),
        };
        map.insert(*key, ctx);
    }
    for (key, cont1) in locals1.iter() {
        if !locals2.contains_key(key) {
            map.insert(*key, cont1.clone());
        }
    }
    map
}

fn restore_cont_from(locals: lenvc::T, from: &lenvc::T, cont: c::T) -> lenvc::T {
    let ctxopt = lenvc::get_cont_option(cont, from);
    lenvc::replace_cont(cont, ctxopt, locals)
}

/// Takes two continuation maps m1 (`locals`) and m2 (`source_locals`) and
/// a continuation c (`cont`) and basically perform m1[c] <= m2[c].
///
/// When entering certain control flow structures, certain
/// preexisting continuations must be stashed away and then _restored_
/// via this function on exiting those control flow structures.
///
/// For example, on entering a loop, preexisting 'break' and 'continue'
/// continuations from any enclosing loops must be stashed away so as not to
/// interfere with them.
pub fn restore_conts_from(locals: lenvc::T, from: &lenvc::T, conts: &[c::T]) -> lenvc::T {
    conts
        .iter()
        .fold(locals, |locals, cont| restore_cont_from(locals, from, *cont))
}

fn restore_and_merge_cont_from(
    env: &mut Env,
    union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    locals: lenvc::T,
    from: &lenvc::T,
    cont: c::T,
) -> lenvc::T {
    let ctxfromopt = lenvc::get_cont_option(cont, from);
    let ctxtoopt = lenvc::get_cont_option(cont, &locals);
    let newctxopt = union_opts(union_types, env, ctxfromopt, ctxtoopt);
    lenvc::replace_cont(cont, newctxopt, locals)
}

/// Same as restore_conts_from, except continuations from the 'from' locals
/// are unioned with the continuations from the current environment. This is
/// used after typechecking a try-catch-finally statement, as continuations
/// may be used outside of this statement
pub fn restore_and_merge_conts_from(
    env: &mut Env,
    mut union_types: impl FnMut(&mut Env, &Local, &Local) -> Local,
    locals: lenvc::T,
    from: &lenvc::T,
    conts: &[c::T],
) -> lenvc::T {
    let mut locals = locals;
    for cont in conts {
        locals = restore_and_merge_cont_from(env, &mut union_types, locals, from, *cont);
    }
    locals
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::local_id;
    use oxidized::local_id::LocalId;
    use oxidized::pos::Pos;
    use oxidized::typing_reason::Blame;
    use oxidized::typing_reason::BlameSource;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::mk;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    fn lid(name: &str) -> LocalId {
        local_id::make_unscoped(name)
    }

    /// The type `Tgeneric name`: enough to tell the types of the tests apart.
    fn ty(name: &str) -> Ty {
        mk((
            crate::typing_reason::none(),
            Ty_::Tgeneric(name.to_string()),
        ))
    }

    fn name_of(ty: &Ty) -> String {
        match get_node(ty) {
            Ty_::Tgeneric(name) => name.clone(),
            _ => panic!("the tests only make Tgeneric"),
        }
    }

    fn local(env: &Env, ty_name: &str) -> Local {
        Local {
            ty: ty(ty_name),
            pos: Pos::NONE,
            eid: crate::typing_env::make_expression_id(env),
            macro_splice_vars: None,
        }
    }

    fn entry(env: &Env, locals: &[(&str, &str)]) -> PerContEntry {
        let mut entry = lenvc::empty_entry();
        for (name, ty_name) in locals {
            entry.local_types.insert(lid(name), local(env, ty_name));
        }
        entry
    }

    /// `(local, type)` for each local of a continuation.
    fn locals_of(cont: c::T, m: &lenvc::T) -> Vec<(String, String)> {
        match m.get(&cont) {
            None => vec![],
            Some(entry) => entry
                .local_types
                .iter()
                .map(|(lid, local)| (lid.1.clone(), name_of(&local.ty)))
                .collect(),
        }
    }

    fn pairs(l: &[(&str, &str)]) -> Vec<(String, String)> {
        l.iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect()
    }

    /// Merges `A` and `B` into `(A|B)`, and records the order of the calls.
    fn merge<'a>(
        calls: &'a mut Vec<String>,
    ) -> impl FnMut(&mut Env, &Local, &Local) -> Local + 'a {
        move |_env, local1, local2| {
            let name = format!("({}|{})", name_of(&local1.ty), name_of(&local2.ty));
            calls.push(name.clone());
            Local {
                ty: ty(&name),
                ..local1.clone()
            }
        }
    }

    #[test]
    fn union_opts_keeps_the_locals_of_both_contexts() {
        let mut env = env();
        let ctx1 = entry(&env, &[("$x", "A"), ("$y", "B"), ("$z", "E")]);
        let ctx2 = entry(&env, &[("$w", "C"), ("$y", "D"), ("$z", "F")]);
        let mut calls = vec![];
        let ctx = union_opts(merge(&mut calls), &mut env, Some(ctx1.clone()), Some(ctx2))
            .expect("the union of two contexts is a context");
        let m = lenvc::initial_locals(ctx);
        assert_eq!(
            locals_of(c::T::Next, &m),
            pairs(&[("$y", "(B|D)"), ("$z", "(E|F)")])
        );
        // From the greatest local id to the smallest.
        assert_eq!(calls, vec!["(E|F)", "(B|D)"]);

        // With a missing context, the other one is the result.
        let mut calls = vec![];
        let ctx = union_opts(merge(&mut calls), &mut env, None, Some(ctx1.clone())).unwrap();
        assert_eq!(ctx.local_types.len(), 3);
        let ctx = union_opts(merge(&mut calls), &mut env, Some(ctx1), None).unwrap();
        assert_eq!(ctx.local_types.len(), 3);
        assert!(union_opts(merge(&mut calls), &mut env, None, None).is_none());
        assert!(calls.is_empty());
    }

    #[test]
    fn union_joins_the_fake_members() {
        let mut env = env();
        let call = |line| {
            Blame::Blame(
                Pos::from_lnum_bol_offset(
                    Arc::new(RelativePath::make(Prefix::Root, "f.php".into())),
                    (line, 0, 0),
                    (line, 0, 1),
                ),
                BlameSource::BScall,
            )
        };
        let mut ctx1 = lenvc::empty_entry();
        ctx1.fake_members = typing_fake_members::add(ctx1.fake_members, lid("$x->f"), Pos::NONE);
        ctx1.fake_members = typing_fake_members::add(ctx1.fake_members, lid("$x->g"), Pos::NONE);
        let mut ctx2 = ctx1.clone();
        ctx2.fake_members = typing_fake_members::forget_suffixed(ctx2.fake_members, "g", call(3));
        let mut calls = vec![];
        let ctx = union_opts(merge(&mut calls), &mut env, Some(ctx1), Some(ctx2)).unwrap();
        assert!(typing_fake_members::is_valid(
            &ctx.fake_members,
            &lid("$x->f")
        ));
        assert!(!typing_fake_members::is_valid(
            &ctx.fake_members,
            &lid("$x->g")
        ));
        assert_eq!(
            typing_fake_members::is_invalid(&ctx.fake_members, &lid("$x->g")),
            Some(call(3))
        );
    }

    #[test]
    fn union_by_cont_example() {
        // The example of the documentation of `union_by_cont`.
        let mut env = env();
        let e1 = entry(&env, &[("$x", "A"), ("$y", "B")]);
        let e2 = entry(&env, &[("$z", "C"), ("$y", "D")]);
        let locals1: lenvc::T = [
            (c::T::Next, e1.clone()),
            (c::T::Continue, e1.clone()),
            (c::T::Break, e1.clone()),
        ]
        .into_iter()
        .collect();
        let locals2: lenvc::T = [
            (c::T::Next, e2.clone()),
            (c::T::Continue, e2.clone()),
            (c::T::Catch, e2.clone()),
        ]
        .into_iter()
        .collect();
        let mut calls = vec![];
        let m = union_by_cont(&mut env, merge(&mut calls), &locals1, &locals2);
        assert_eq!(
            lenvc::all_continuations(&m),
            vec![c::T::Catch, c::T::Break, c::T::Continue, c::T::Next]
        );
        assert_eq!(locals_of(c::T::Next, &m), pairs(&[("$y", "(B|D)")]));
        assert_eq!(locals_of(c::T::Continue, &m), pairs(&[("$y", "(B|D)")]));
        assert_eq!(
            locals_of(c::T::Break, &m),
            pairs(&[("$x", "A"), ("$y", "B")])
        );
        assert_eq!(
            locals_of(c::T::Catch, &m),
            pairs(&[("$y", "D"), ("$z", "C")])
        );
        // One merge for `Next` and one for `Continue`.
        assert_eq!(calls.len(), 2);
    }

    #[test]
    fn merging_next_in_a_continuation() {
        let mut env = env();
        let m = lenvc::initial_locals(entry(&env, &[("$x", "A"), ("$y", "B")]));

        // `Break` does not exist yet: it becomes a copy of `Next`.
        let mut calls = vec![];
        let saved = save_and_merge_next_in_cont(&mut env, merge(&mut calls), m.clone(), c::T::Break);
        assert_eq!(
            lenvc::all_continuations(&saved),
            vec![c::T::Break, c::T::Next]
        );
        assert_eq!(
            locals_of(c::T::Break, &saved),
            pairs(&[("$x", "A"), ("$y", "B")])
        );
        assert!(calls.is_empty());

        // It exists: the locals of both are merged, `Next` first.
        let m2 = lenvc::replace_cont(
            c::T::Next,
            Some(entry(&env, &[("$x", "C"), ("$z", "D")])),
            saved,
        );
        let mut calls = vec![];
        let moved = move_and_merge_next_in_cont(&mut env, merge(&mut calls), m2, c::T::Break);
        assert_eq!(lenvc::all_continuations(&moved), vec![c::T::Break]);
        assert_eq!(locals_of(c::T::Break, &moved), pairs(&[("$x", "(C|A)")]));

        // `update_next_from_conts` with continuations that do not exist
        // removes `Next`.
        let mut calls = vec![];
        let updated = update_next_from_conts(
            &mut env,
            merge(&mut calls),
            m.clone(),
            &[c::T::Continue, c::T::Catch],
        );
        assert!(lenvc::all_continuations(&updated).is_empty());
        let updated = update_next_from_conts(
            &mut env,
            merge(&mut calls),
            moved,
            &[c::T::Continue, c::T::Break],
        );
        assert_eq!(locals_of(c::T::Next, &updated), pairs(&[("$x", "(C|A)")]));
    }

    #[test]
    fn restoring_continuations() {
        let mut env = env();
        let parent: lenvc::T = [
            (c::T::Next, entry(&env, &[("$x", "A")])),
            (c::T::Break, entry(&env, &[("$x", "B")])),
        ]
        .into_iter()
        .collect();
        let inner: lenvc::T = [
            (c::T::Next, entry(&env, &[("$x", "C")])),
            (c::T::Break, entry(&env, &[("$x", "D")])),
            (c::T::Continue, entry(&env, &[("$x", "E")])),
        ]
        .into_iter()
        .collect();

        // `Break` is taken from `parent`; `Continue`, which `parent` does not
        // have, is dropped; `Next` is not touched.
        let restored =
            restore_conts_from(inner.clone(), &parent, &[c::T::Break, c::T::Continue]);
        assert_eq!(
            lenvc::all_continuations(&restored),
            vec![c::T::Break, c::T::Next]
        );
        assert_eq!(locals_of(c::T::Break, &restored), pairs(&[("$x", "B")]));
        assert_eq!(locals_of(c::T::Next, &restored), pairs(&[("$x", "C")]));

        // Merging: the continuation of `from` comes first.
        let mut calls = vec![];
        let merged = restore_and_merge_conts_from(
            &mut env,
            merge(&mut calls),
            inner,
            &parent,
            &[c::T::Break, c::T::Continue],
        );
        assert_eq!(locals_of(c::T::Break, &merged), pairs(&[("$x", "(B|D)")]));
        assert_eq!(locals_of(c::T::Continue, &merged), pairs(&[("$x", "E")]));
        assert_eq!(calls, vec!["(B|D)"]);
    }

    #[test]
    fn is_sub_opt_entry_checks_the_locals_of_the_second_context() {
        let env = env();
        let ctx1 = entry(&env, &[("$x", "A"), ("$y", "B")]);
        let ctx2 = entry(&env, &[("$y", "B")]);
        let same = |_: &Env, ty1: &Ty, ty2: &Ty| name_of(ty1) == name_of(ty2);
        assert!(is_sub_opt_entry(same, &env, Some(&ctx1), Some(&ctx2)));
        // `$x` is not in `ctx2`.
        assert!(!is_sub_opt_entry(same, &env, Some(&ctx2), Some(&ctx1)));
        assert!(is_sub_opt_entry(same, &env, Some(&ctx1), None));
        assert!(is_sub_opt_entry(same, &env, None, None));
        assert!(!is_sub_opt_entry(same, &env, None, Some(&ctx1)));

        // The function is called for every local of both contexts, even after
        // one of them failed, from the greatest id to the smallest.
        let ctx3 = entry(&env, &[("$x", "Z"), ("$y", "B")]);
        let mut calls = vec![];
        let res = is_sub_opt_entry(
            |_: &Env, ty1: &Ty, ty2: &Ty| {
                calls.push(name_of(ty1));
                name_of(ty1) == name_of(ty2)
            },
            &env,
            Some(&ctx1),
            Some(&ctx3),
        );
        assert!(!res);
        assert_eq!(calls, vec!["B", "A"]);
    }
}
