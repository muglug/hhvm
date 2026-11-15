// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_dynamic_utils.ml`. See `hh/PORTING.md`.
//!
//! - Where OCaml drops the environment that `Env.expand_type` returns
//!   (`let (_, t) = Env.expand_type env t`), the type is expanded in a copy of
//!   the environment ([`expand_type_in_copy`]).
//! - `partition_union` looks at the elements from the first to the last (see
//!   [`partition_union_into`]).

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;

use crate::typing_defs;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_solver;
use crate::typing_utils;

/// `let (_, ty) = Env.expand_type env ty`: the environment that
/// `Env.expand_type` returns is dropped, so expand in a copy. (Only a type
/// variable is expanded, and only that can change the environment.)
fn expand_type_in_copy(env: &Env, ty: Ty) -> Ty {
    match get_node(&ty) {
        Ty_::Tvar(_) => env::expand_type(&mut env.clone(), ty),
        _ => ty,
    }
}

/// Whether [`partition_union`] would put anything in its first list: an
/// element of the flattened union satisfies `f`, or is a `supportdyn` whose
/// argument has such an element.
fn has_element_satisfying(f: &dyn Fn(&Ty) -> bool, env: &Env, tyl: &[Ty]) -> bool {
    tyl.iter().any(|t| {
        let t = expand_type_in_copy(env, t.clone());
        match get_node(&t) {
            Ty_::Tunion(tyl_) if !tyl_.is_empty() => has_element_satisfying(f, env, tyl_),
            Ty_::Tnewtype(n, tyl1, _) if tyl1.len() == 1 && n == sn::classes::SUPPORT_DYN => {
                has_element_satisfying(f, env, &tyl1[..1])
            }
            _ => f(&t),
        }
    })
}

/// Search through the input list, and any unions directly-recursively contained in the input list,
/// and return those that satisfy f, and those that do not, separately.
pub fn partition_union(f: &dyn Fn(&Ty) -> bool, env: &Env, tyl: &[Ty]) -> (Vec<Ty>, Vec<Ty>) {
    let mut dyns: Vec<Ty> = vec![];
    let mut nondyns: Vec<Ty> = Vec::with_capacity(tyl.len());
    partition_union_into(f, env, tyl, &mut Dyns::All(&mut dyns), &mut nondyns);
    (dyns, nondyns)
}

/// Where [`partition_union_into`] puts the elements that satisfy `f`: all of
/// them, or only the first (for callers that drop the others; as nothing is
/// done but building them, the others are not built).
enum Dyns<'a> {
    All(&'a mut Vec<Ty>),
    First(&'a mut Option<Ty>),
}

impl Dyns<'_> {
    fn wants_more(&self) -> bool {
        match self {
            Dyns::All(_) => true,
            Dyns::First(first) => first.is_none(),
        }
    }

    fn push(&mut self, ty: Ty) {
        match self {
            Dyns::All(dyns) => dyns.push(ty),
            Dyns::First(first) => {
                if first.is_none() {
                    **first = Some(ty)
                }
            }
        }
    }
}

/// `partition_union`, adding to `dyns` and `nondyns`. The OCaml's `aux`
/// walks the flattened list from the first element to the last, consing onto
/// accumulators that it reverses at the end: the elements end up in the
/// order of the flattened list. Here the elements are pushed in that order,
/// and a nested union is walked in place rather than appended to the rest of
/// the list (`tyl' @ tyl`), which looks at the same elements in the same
/// order without building the flattened list.
fn partition_union_into(
    f: &dyn Fn(&Ty) -> bool,
    env: &Env,
    tyl: &[Ty],
    dyns: &mut Dyns<'_>,
    nondyns: &mut Vec<Ty>,
) {
    for t in tyl {
        let t = expand_type_in_copy(env, t.clone());
        let supportdyn_arg = match get_node(&t) {
            Ty_::Tunion(tyl_) if !tyl_.is_empty() => {
                // `partition_union ~f env (tyl' @ tyl)`
                partition_union_into(f, env, tyl_, dyns, nondyns);
                continue;
            }
            Ty_::Tnewtype(n, tyl1, _) if tyl1.len() == 1 && n == sn::classes::SUPPORT_DYN => {
                Some(tyl1[0].clone())
            }
            _ => None,
        };
        match supportdyn_arg {
            Some(ty1) => match strip_union(f, env, std::slice::from_ref(&ty1)) {
                None => nondyns.push(t),
                Some((sub_dyns, sub_non_dyns)) => {
                    let sd = |tyl: Vec<Ty>| {
                        make_type::supportdyn(
                            get_reason(&ty1).clone(),
                            make_type::union(get_reason(&ty1).clone(), tyl),
                        )
                    };
                    let sd_non_dyns = sd(sub_non_dyns);
                    if dyns.wants_more() {
                        let sd_dyns = sd(sub_dyns);
                        dyns.push(sd_dyns);
                    }
                    nondyns.push(sd_non_dyns);
                }
            },
            None => {
                if f(&t) {
                    dyns.push(t)
                } else {
                    nondyns.push(t)
                }
            }
        }
    }
}

fn strip_union(f: &dyn Fn(&Ty) -> bool, env: &Env, tyl: &[Ty]) -> Option<(Vec<Ty>, Vec<Ty>)> {
    // Not in the OCaml: the partition has an element that satisfies `f` iff
    // one of the elements it looks at does, so look for one first, without
    // building the partition (most unions have none). `f` only reads.
    if !has_element_satisfying(f, env, tyl) {
        return None;
    }
    let (dyns, nondyns) = partition_union(f, env, tyl);
    if dyns.is_empty() {
        None
    } else {
        Some((dyns, nondyns))
    }
}

fn is_dynamic_or_intersection_with_dynamic(accept_intersections: bool, env: &Env, ty: &Ty) -> bool {
    let ty = expand_type_in_copy(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tintersection(tyl) if accept_intersections => tyl
            .iter()
            .any(|ty| is_dynamic_or_intersection_with_dynamic(accept_intersections, env, ty)),
        Ty_::Tdynamic(None) => true,
        _ => false,
    }
}

pub fn try_strip_dynamic_from_union(
    accept_intersections: Option<bool>,
    env: &Env,
    tyl: &[Ty],
) -> Option<(Ty, Vec<Ty>)> {
    let accept_intersections = accept_intersections.unwrap_or(false);
    // `strip_union`, of which only the first element that satisfies `f` is
    // used: the partition is built with that element only (see [`Dyns`]),
    // in one pass (most of these unions have one: `~t` is `dynamic | t`).
    let f = |ty: &Ty| is_dynamic_or_intersection_with_dynamic(accept_intersections, env, ty);
    let mut first = None;
    let mut nondyns: Vec<Ty> = Vec::with_capacity(tyl.len());
    partition_union_into(&f, env, tyl, &mut Dyns::First(&mut first), &mut nondyns);
    first.map(|ty| (ty, nondyns))
}

/// Strip dynamic off a union, and push supportdyn through. So
///   try_strip_dynamic(~t) = t
///   try_strip_dynamic(supportdyn<~t>) = supportdyn<t>
/// Otherwise return None.
pub fn try_strip_dynamic(
    accept_intersections: Option<bool>,
    do_not_solve_likes: Option<bool>,
    env: &mut Env,
    ty: &Ty,
) -> Option<Ty> {
    let accept_intersections = accept_intersections.unwrap_or(false);
    let do_not_solve_likes = do_not_solve_likes.unwrap_or(false);
    let ty = if do_not_solve_likes {
        env::expand_type(env, ty.clone())
    } else {
        typing_solver::expand_type_for_strip_dynamic(env, ty.clone())
    };
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            let ty_opt = try_strip_dynamic(Some(accept_intersections), None, env, &tyargs[0]);
            match ty_opt {
                None => None,
                Some(stripped_ty) => {
                    Some(make_type::supportdyn(get_reason(&ty).clone(), stripped_ty))
                }
            }
        }
        Ty_::Tunion(tyl) => {
            let ty_opt = try_strip_dynamic_from_union(Some(accept_intersections), env, tyl);
            match ty_opt {
                None => None,
                Some((_, tyl)) => Some(make_type::union(get_reason(&ty).clone(), tyl)),
            }
        }
        _ => None,
    }
}

/// If input is dynamic | t or t | dynamic then return t,
/// otherwise return type unchanged.
pub fn strip_dynamic(env: &mut Env, ty: Ty) -> Ty {
    let ty_opt = try_strip_dynamic(None, None, env, &ty);
    match ty_opt {
        None => ty,
        Some(ty) => ty,
    }
}

fn is_inter_dyn(env: &mut Env, ty: &Ty) -> Option<(Ty, Ty)> {
    let ty = env::expand_type(env, ty.clone());
    match get_node(&ty) {
        Ty_::Tintersection(tyl)
            if tyl.len() == 2
                && (typing_defs::is_dynamic(&tyl[0]) || typing_defs::is_dynamic(&tyl[1])) =>
        {
            Some((tyl[0].clone(), tyl[1].clone()))
        }
        _ => None,
    }
}

/// `find_inter_dyn env acc tyl`. As in OCaml, `acc` is a list of elements
/// already looked at, the last one first: each element that is not an
/// intersection with dynamic is consed onto it.
fn find_inter_dyn(env: &mut Env, acc: Vec<Ty>, tyl: &[Ty]) -> Option<((Ty, Ty), Vec<Ty>)> {
    for (i, ty) in tyl.iter().enumerate() {
        if let Some(ty_inter) = is_inter_dyn(env, ty) {
            // `acc @ tyl`, where `acc` is now the elements before this one,
            // the last one first, consed onto the `acc` given.
            let mut res: Vec<Ty> = tyl[..i].iter().rev().cloned().collect();
            res.extend(acc);
            res.extend(tyl[i + 1..].iter().cloned());
            return Some((ty_inter, res));
        }
    }
    None
}

/// Detect types that look like (t1 & dynamic) | t2 and convert to
/// ~t2 & (t1 | t2). Also in function returns.
pub fn recompose_like_type(env: &mut Env, orig_ty: Ty) -> Ty {
    let ty = env::expand_type(env, orig_ty.clone());
    match get_node(&ty) {
        Ty_::Tunion(tys) => match find_inter_dyn(env, vec![], tys) {
            Some(((ty1, ty2), rest)) if rest.len() == 1 => {
                let ty_sub = rest.into_iter().next().unwrap();
                let ty_union1 = typing_utils::union(env, None, None, ty1, ty_sub.clone());
                let ty_union2 = typing_utils::union(env, None, None, ty2, ty_sub);
                make_type::intersection(get_reason(&ty).clone(), vec![ty_union1, ty_union2])
            }
            _ => {
                let ty_opt = try_strip_dynamic(None, None, env, &ty);
                match ty_opt {
                    None => ty,
                    Some(ty1) => {
                        let ty2 = recompose_like_type(env, ty1);
                        // Not in the OCaml: when `ty` is already the union
                        // that `MakeType.locl_like` would build (`dynamic`
                        // first, with the reason of the union, then `ty2`
                        // itself), it is given back instead of an equal
                        // copy (the usual `~t` with nothing to recompose).
                        // This saves an allocation per call; the result is
                        // equal to the OCaml's and differs only by its address.
                        let r = get_reason(&ty);
                        let same_as_like = match &tys[..] {
                            [d, t] => {
                                matches!(get_node(d), Ty_::Tdynamic(None))
                                    && get_reason(d) == r
                                    && crate::typing_defs_core::phys_equal(t, &ty2)
                                    && !matches!(get_node(&ty2), Ty_::Tprim(Tprim::Tnoreturn))
                                    && !make_type::is_locl_supertype_of_dynamic(&ty2)
                            }
                            _ => false,
                        };
                        if same_as_like {
                            return ty.clone();
                        }
                        make_type::locl_like(r.clone(), ty2)
                    }
                }
            }
        },
        Ty_::Tfun(ft) => {
            let ft_ret = recompose_like_type(env, ft.ret.clone());
            // Not in the OCaml: an unchanged return type gives back the
            // function type itself, instead of an equal copy (no allocation;
            // the result differs from the OCaml's only by its address).
            if crate::typing_defs_core::phys_equal(&ft_ret, &ft.ret) {
                return ty.clone();
            }
            let mut ft = ft.clone();
            std::rc::Rc::make_mut(&mut ft).ret = ft_ret;
            mk((get_reason(&ty).clone(), Ty_::Tfun(ft)))
        }
        Ty_::Tnewtype(n, tyl, _) if tyl.len() == 1 && n == sn::classes::SUPPORT_DYN => {
            let ty1 = recompose_like_type(env, tyl[0].clone());
            typing_utils::simple_make_supportdyn(get_reason(&ty).clone(), env, ty1)
        }
        _ => orig_ty,
    }
}
