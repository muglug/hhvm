// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_lenv.ml`. See `hh/PORTING.md`.
//!
//! Module dealing with local environments.

use oxidized::pos::Pos;

use crate::typing_continuations as c;
use crate::typing_defs_core::Ty;
use crate::typing_env as env_;
use crate::typing_env_types::Env;
use crate::typing_env_types::LocalEnv;
use crate::typing_fake_members;
use crate::typing_local_packages;
use crate::typing_local_types::Local;
use crate::typing_per_cont_env as lenvc;
use crate::typing_per_cont_env::PerContEntry;
use crate::typing_per_cont_ops as lenv_ops;
use crate::typing_reason;
use crate::typing_union as union_;

pub fn get_all_locals(env: &Env) -> lenvc::T {
    env.lenv.per_cont_env.clone()
}

// ---------------------------------------------------------------------------
// Functions dealing with old style local environment
// ---------------------------------------------------------------------------

/// `phys_equal ty ty'`, where `ty` is the result of `Typing_union.union` and
/// `ty'` one of its arguments: whether the union is that argument itself.
/// The arguments are passed to the union as clones, which share their node
/// with `ty'` (see `typing_defs_core::phys_equal`).
fn phys_equal(ty: &Ty, arg: &Ty) -> bool {
    crate::typing_defs_core::phys_equal(ty, arg)
}

pub fn union(env: &mut Env, join_pos: &Pos, local1: &Local, local2: &Local) -> Local {
    let Local {
        ty: ty1,
        pos: pos1,
        eid: eid1,
        macro_splice_vars: macro_splice_vars1,
    } = local1;
    let Local {
        ty: ty2,
        pos: pos2,
        eid: eid2,
        macro_splice_vars: macro_splice_vars2,
    } = local2;
    // TODO(mjt) Use a more specific reason here provided as an argument
    let reason = Some(typing_reason::join_point(join_pos.clone()));
    let ty = union_::union(env, reason.clone(), Some(true), ty1.clone(), ty2.clone());
    // TODO(mjt) Determin if this need updating to if the change to reasons will
    // be sufficient
    //
    // The OCaml is
    //   if phys_equal ty ty1 || Pos.equal Pos.none pos2 then pos1
    //   else if phys_equal ty ty2 || Pos.equal Pos.none pos1 then pos2
    //   else Pos.none
    // Both sides of each `||` are pure, so the cheap position test is done
    // first.
    let pos = if crate::pos::equal_none(pos2) || phys_equal(&ty, ty1) {
        pos1.clone()
    } else if crate::pos::equal_none(pos1) || phys_equal(&ty, ty2) {
        pos2.clone()
    } else {
        Pos::NONE
    };
    let eid = if eid1 == eid2 {
        eid1.clone()
    } else {
        env_::make_expression_id(env)
    };
    let macro_splice_vars = match (macro_splice_vars1, macro_splice_vars2) {
        (x, None) => x.clone(),
        (None, x) => x.clone(),
        (Some(map1), Some(map2)) => {
            // `Local_id.Map.union_env` is `merge_env`: first the bindings of
            // `map2`, in increasing order, combined with those of `map1`;
            // then the bindings that are only in `map1`.
            let mut map = im::OrdMap::new();
            for (key, v2) in map2.iter() {
                let v = match map1.get(key) {
                    None => v2.clone(),
                    Some((p1, t1)) => {
                        let (_p2, t2) = v2;
                        let t =
                            union_::union(env, reason.clone(), Some(true), t1.clone(), t2.clone());
                        (p1.clone(), t)
                    }
                };
                map.insert(key.clone(), v);
            }
            for (key, v1) in map1.iter() {
                if !map2.contains_key(key) {
                    map.insert(key.clone(), v1.clone());
                }
            }
            Some(map)
        }
    };
    Local {
        ty,
        pos,
        eid,
        macro_splice_vars,
    }
}

pub fn get_cont_option(env: &Env, cont: c::T) -> Option<PerContEntry> {
    lenvc::get_cont_option(cont, &env.lenv.per_cont_env)
}

pub fn drop_cont(env: &mut Env, cont: c::T) {
    let local_types = get_all_locals(env);
    let local_types = lenvc::drop_cont(cont, local_types);
    env_::env_with_locals(env, local_types)
}

pub fn drop_conts(env: &mut Env, conts: &[c::T]) {
    let local_types = get_all_locals(env);
    let local_types = lenvc::drop_conts(conts, local_types);
    env_::env_with_locals(env, local_types)
}

pub fn replace_cont(env: &mut Env, cont: c::T, ctxopt: Option<PerContEntry>) {
    let local_types = get_all_locals(env);
    let local_types = lenvc::replace_cont(cont, ctxopt, local_types);
    env_::env_with_locals(env, local_types)
}

pub fn restore_conts_from(env: &mut Env, fromlocals: &lenvc::T, conts: &[c::T]) {
    let local_types = get_all_locals(env);
    let local_types = lenv_ops::restore_conts_from(local_types, fromlocals, conts);
    env_::env_with_locals(env, local_types)
}

pub fn restore_and_merge_conts_from(
    env: &mut Env,
    join_pos: &Pos,
    fromlocals: &lenvc::T,
    conts: &[c::T],
) {
    let local_types = get_all_locals(env);
    let local_types = lenv_ops::restore_and_merge_conts_from(
        env,
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        local_types,
        fromlocals,
        conts,
    );
    env_::env_with_locals(env, local_types)
}

/// Merge all continuations in the provided list and update the 'next'
/// continuation with the result.
pub fn update_next_from_conts(env: &mut Env, join_pos: &Pos, cont_list: &[c::T]) {
    let local_types = get_all_locals(env);
    let local_types = lenv_ops::update_next_from_conts(
        env,
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        local_types,
        cont_list,
    );
    env_::env_with_locals(env, local_types)
}

/// After this call, the provided continuation will be the union of itself and
/// the next continuation
pub fn save_and_merge_next_in_cont(env: &mut Env, join_pos: &Pos, cont: c::T) {
    let local_types = get_all_locals(env);
    let local_types = lenv_ops::save_and_merge_next_in_cont(
        env,
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        local_types,
        cont,
    );
    env_::env_with_locals(env, local_types)
}

pub fn move_and_merge_next_in_cont(env: &mut Env, join_pos: &Pos, cont: c::T) {
    let local_types = get_all_locals(env);
    let local_types = lenv_ops::move_and_merge_next_in_cont(
        env,
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        local_types,
        cont,
    );
    env_::env_with_locals(env, local_types)
}

pub fn union_contextopts(
    join_pos: &Pos,
    env: &mut Env,
    ctxopt1: Option<PerContEntry>,
    ctxopt2: Option<PerContEntry>,
) -> Option<PerContEntry> {
    lenv_ops::union_opts(
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        env,
        ctxopt1,
        ctxopt2,
    )
}

pub fn union_by_cont(env: &mut Env, join_pos: &Pos, lenv1: &LocalEnv, lenv2: &LocalEnv) {
    let locals1 = &lenv1.per_cont_env;
    let locals2 = &lenv2.per_cont_env;
    let locals = lenv_ops::union_by_cont(
        env,
        |env: &mut Env, local1: &Local, local2: &Local| union(env, join_pos, local1, local2),
        locals1,
        locals2,
    );
    env_::env_with_locals(env, locals)
}

fn join_fake(lenv1: &LocalEnv, lenv2: &LocalEnv) -> typing_fake_members::T {
    let nextctxopt1 = lenv1.per_cont_env.get(&c::T::Next);
    let nextctxopt2 = lenv2.per_cont_env.get(&c::T::Next);
    match (nextctxopt1, nextctxopt2) {
        (Some(c1), Some(c2)) => typing_fake_members::join(&c1.fake_members, &c2.fake_members),
        (None, None) => typing_fake_members::empty(),
        (Some(c1), None) => c1.fake_members.clone(),
        (None, Some(c2)) => c2.fake_members.clone(),
    }
}

/// Returns the local environment of the updated environment.
/// (The OCaml returns `({ env with lenv }, lenv)`: the `lenv` is `env.lenv`
/// here, so it is not returned: [`union_lenvs`] drops it, and
/// [`union_lenv_list`] reads it in `env`.)
fn union_lenvs_(
    env: &mut Env,
    join_pos: &Pos,
    parent_lenv: &LocalEnv,
    lenv1: &LocalEnv,
    lenv2: &LocalEnv,
) {
    let fake_members = join_fake(lenv1, lenv2);
    let local_using_vars = parent_lenv.local_using_vars.clone();
    union_by_cont(env, join_pos, lenv1, lenv2);
    env.lenv.local_using_vars = local_using_vars;
    let per_cont_env = std::mem::take(&mut env.lenv.per_cont_env);
    env.lenv.per_cont_env = lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
        entry.fake_members = fake_members;
        entry
    });
}

/// Used when we want the new local environment to be the union
/// of 2 local environments. Typical use case is an if statement.
/// $x = 0;
/// if(...) { $x = ''; } else { $x = 'foo'; }
/// We want $x to be a string past this point.
/// We check that the locals are defined in both branches
/// when that is the case, their type becomes the union (least upper bound)
/// of the types it had in each branch.
pub fn union_lenvs(
    env: &mut Env,
    join_pos: &Pos,
    parent_lenv: &LocalEnv,
    lenv1: &LocalEnv,
    lenv2: &LocalEnv,
) {
    union_lenvs_(env, join_pos, parent_lenv, lenv1, lenv2)
}

pub fn union_lenv_list(
    env: &mut Env,
    join_pos: &Pos,
    parent_lenv: &LocalEnv,
    lenvs: &[LocalEnv],
) {
    match lenvs {
        [] | [_] => {}
        [lenv1, lenv2, lenvlist @ ..] => {
            union_lenvs_(env, join_pos, parent_lenv, lenv1, lenv2);
            // `union_lenv_list env ~join_pos parent_lenv (lenv :: lenvlist)`
            for lenv2 in lenvlist {
                let lenv = env.lenv.clone();
                union_lenvs_(env, join_pos, parent_lenv, &lenv, lenv2);
            }
        }
    }
}

/// When entering control flow structures, some
/// preexisting continuations must be stashed away and then restored
/// on exiting those control flow structures.
///
/// For example, on entering a loop, preexisting 'break' and 'continue'
/// continuations from any enclosing loops must be stashed away so as not to
/// interfere with them.
pub fn stash_and_do<A>(env: &mut Env, conts: &[c::T], f: impl FnOnce(&mut Env) -> A) -> A {
    let parent_locals = get_all_locals(env);
    drop_conts(env, conts);
    let res = f(env);
    restore_conts_from(env, &parent_locals, conts);
    res
}

pub fn env_with_empty_fakes(env: &mut Env) {
    let per_cont_env = std::mem::take(&mut env.lenv.per_cont_env);
    env.lenv.per_cont_env = lenvc::update_cont_entry(c::T::Next, per_cont_env, |mut entry| {
        entry.fake_members = typing_fake_members::empty();
        entry
    });
}

pub fn has_next(env: &Env) -> bool {
    match get_cont_option(env, c::T::Next) {
        None => false,
        Some(_) => true,
    }
}

pub fn assert_package_loaded(
    env: &mut Env,
    pos: Pos,
    pkg: String,
    status: typing_local_packages::LocalPackageRequirement,
) {
    let tcopt = std::sync::Arc::clone(env_::get_tcopt(env));
    // `Typechecker_options.package_info`
    let package_info = &tcopt.po.package_info;
    let per_cont_env = std::mem::take(&mut env.lenv.per_cont_env);
    env.lenv.per_cont_env = lenvc::assert_package_loaded_in_cont(
        package_info,
        c::T::Next,
        pos,
        pkg,
        status,
        per_cont_env,
    );
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::local_id;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn env() -> Env {
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    #[test]
    fn continuations() {
        let mut env = env();
        assert!(has_next(&env));
        assert_eq!(env_::all_continuations(&env), vec![c::T::Next]);

        replace_cont(&mut env, c::T::Break, Some(lenvc::empty_entry()));
        replace_cont(&mut env, c::T::Continue, Some(lenvc::empty_entry()));
        assert_eq!(
            env_::all_continuations(&env),
            vec![c::T::Break, c::T::Continue, c::T::Next]
        );
        assert!(get_cont_option(&env, c::T::Break).is_some());
        assert!(get_cont_option(&env, c::T::Catch).is_none());

        drop_cont(&mut env, c::T::Next);
        assert!(!has_next(&env));
        drop_conts(&mut env, &[c::T::Break, c::T::Continue, c::T::Exit]);
        assert!(env_::all_continuations(&env).is_empty());
    }

    #[test]
    fn stash_and_do_restores_the_stashed_continuations() {
        let mut env = env();
        replace_cont(&mut env, c::T::Break, Some(lenvc::empty_entry()));
        let seen = stash_and_do(&mut env, &[c::T::Break, c::T::Continue], |env| {
            // Stashed away while `f` runs.
            let seen = env_::all_continuations(env);
            // What `f` leaves in the stashed continuations is replaced by
            // what was there before: `Continue` did not exist.
            replace_cont(env, c::T::Continue, Some(lenvc::empty_entry()));
            replace_cont(env, c::T::Catch, Some(lenvc::empty_entry()));
            seen
        });
        assert_eq!(seen, vec![c::T::Next]);
        assert_eq!(
            env_::all_continuations(&env),
            vec![c::T::Catch, c::T::Break, c::T::Next]
        );
    }

    #[test]
    fn empty_fakes() {
        let mut env = env();
        let id = local_id::make_unscoped("$x->f");
        let fakes = typing_fake_members::add(env_::get_fake_members(&env), id.clone(), Pos::NONE);
        env_::set_fake_members(&mut env, fakes);
        assert!(typing_fake_members::is_valid(
            &env_::get_fake_members(&env),
            &id
        ));
        env_with_empty_fakes(&mut env);
        assert!(!typing_fake_members::is_valid(
            &env_::get_fake_members(&env),
            &id
        ));
    }
}
