// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/ancestor_route.ml`. See `hh/PORTING.md`.
//!
//! Find dependency routes between classish types.
//!
//! This is used in error reporting, to show how a class ultimately
//! inherited something (e.g. an abstract method) that caused a type
//! error.

use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::s_set;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::utils;

fn get_class(env: &Env, name: &str) -> decl_entry::T<cls::T> {
    typing_env::get_class(env, name)
}

/// All the parent classes, used traits, and implemented interfaces of
/// [type_name]. This is the flattened inheritance tree.
fn all_ancestor_names(env: &Env, type_name: &str) -> Vec<String> {
    let decl = get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => cls::all_ancestor_names(&decl),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    }
}

fn has_ancestor(env: &Env, classish_name: &str, ancestor_name: &str) -> bool {
    match get_class(env, classish_name) {
        decl_entry::T::Found(decl) => cls::has_ancestor(&decl, ancestor_name),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// Return the ancestors of [classish_name] that also depend on [ancestor_name].
fn find_ancestors_using(env: &Env, classish_name: &str, ancestor_name: &str) -> Vec<String> {
    let ancestors = all_ancestor_names(env, classish_name);
    ancestors
        .into_iter()
        .filter(|name| has_ancestor(env, name, ancestor_name))
        .collect()
}

/// Sort a list of classish names according to how many ancestors they
/// have, in ascending order.
///
/// (`List.dedup_and_sort ~compare`: a stable sort, then, of consecutive
/// elements that compare equal, only the last is kept, as
/// `Base.List.remove_consecutive_duplicates` does by default. Two classes
/// with as many ancestors compare equal, so only one of them stays.)
///
/// The number of ancestors of each name is computed once, before sorting,
/// where OCaml computes it at each comparison: it only reads declarations
/// (recording the same dependencies).
fn sort_by_num_ancestors(env: &Env, names: Vec<String>) -> Vec<String> {
    let num_ancestors = |cls_name: &str| all_ancestor_names(env, cls_name).len();
    if names.len() <= 1 {
        // `[] | [ _ ] -> list`
        return names;
    }
    let mut names: Vec<(usize, String)> =
        names.into_iter().map(|n| (num_ancestors(&n), n)).collect();
    // `sort_by` is stable, like `List.sort`.
    names.sort_by(|(x, _), (y, _)| x.cmp(y));
    let mut result: Vec<(usize, String)> = Vec::with_capacity(names.len());
    for hd in names {
        match result.last_mut() {
            Some(to_keep) if to_keep.0 == hd.0 => *to_keep = hd,
            _ => result.push(hd),
        }
    }
    result.into_iter().map(|(_, n)| n).collect()
}

/// Return a list showing a route from [classish] name to [ancestor]
/// name. If multiple routes exist, return the longest one.
///
/// ```text
/// trait One {}
/// trait Two { use One; }
/// class Three { use Two; }
/// ```
///
/// The route from Three to One in this example is
/// ["Three"; "Two"; "One"].
pub fn find_route(env: &Env, classish: &str, ancestor: &str) -> Vec<String> {
    fn classish_between(env: &Env, classish: &str, ancestor: &str, seen: &s_set::T) -> Vec<String> {
        if seen.contains(classish) {
            // The class hierarchy is bad: it contains a cycle. Ensure we
            // still terminate.
            vec![]
        } else {
            // Find all the ancestors that use this trait.
            let ancestors = find_ancestors_using(env, classish, ancestor);
            // Choose the ancestor closest to [classish] by taking the ancestor
            // that has the most ancestors itself.
            let mut sorted_ancestors = sort_by_num_ancestors(env, ancestors);
            sorted_ancestors.reverse();
            match sorted_ancestors.as_slice() {
                [] => vec![],
                [ancestor] => vec![ancestor.clone()],
                [anc, ..] => {
                    let mut seen = seen.clone();
                    seen.insert(classish.to_string());
                    let mut route = vec![anc.clone()];
                    route.extend(classish_between(env, anc, ancestor, &seen));
                    route
                }
            }
        }
    }
    let mut route = vec![classish.to_string()];
    route.extend(classish_between(env, classish, ancestor, &s_set::T::new()));
    route.push(ancestor.to_string());
    route
}

/// Find the position in [classish_name] that means it depends on
/// [ancestor_name].
///
/// For example, if [ancestor_name] is a trait, this will return the
/// `use Foo;` position.
fn reason_pos(env: &Env, classish_name: &str, ancestor_name: &str) -> PosOrDecl {
    match get_class(env, classish_name) {
        decl_entry::T::Found(decl) => match cls::get_ancestor(&decl, ancestor_name) {
            // `Typing_defs_core.get_pos trait_ty`
            Some(trait_ty) => PosOrDecl::from(decl_utils::get_pos(&trait_ty)),
            None => PosOrDecl::NONE,
        },
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => PosOrDecl::NONE,
    }
}

/// Given a list of [items], apply the function [f] to every two
/// adjacent items.
///
/// E.g. for [1; 2; 3] we return [(f 1 2); (f 2 3)].
fn pairwise_map<A, B>(items: &[A], f: &mut impl FnMut(&A, &A) -> B) -> Vec<B> {
    match items {
        [] => vec![],
        [_] => vec![],
        [x, y, ..] => {
            // `f x y :: pairwise_map (y :: rest) f`: the head is computed last.
            let rest = pairwise_map(&items[1..], f);
            let head = f(x, y);
            let mut result = vec![head];
            result.extend(rest);
            result
        }
    }
}

/// Return a list of positions from [classish] name to [ancestor] name.
pub fn describe_route(env: &Env, classish: &str, ancestor: &str) -> Vec<(PosOrDecl, String)> {
    let route = find_route(env, classish, ancestor);
    pairwise_map(&route, &mut |classish: &String, parent: &String| {
        (
            reason_pos(env, classish, parent),
            format!(
                "`{}` uses `{}`",
                utils::strip_ns(classish),
                utils::strip_ns(parent)
            ),
        )
    })
}

/// Show that [classish] uses [via], and the full path from [via] to
/// [ancestor].
pub fn describe_route_via(
    env: &Env,
    classish: &str,
    ancestor: &str,
    via: &str,
) -> Vec<(PosOrDecl, String)> {
    let result = if via == ancestor {
        vec![]
    } else {
        describe_route(env, via, ancestor)
    };
    let mut route = vec![(
        reason_pos(env, classish, via),
        format!(
            "`{}` uses `{}`",
            utils::strip_ns(classish),
            utils::strip_ns(via)
        ),
    )];
    route.extend(result);
    route
}
