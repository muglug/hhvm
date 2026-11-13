// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `type_parameter_env.ml`. See `hh/PORTING.md`.
//!
//! `oxidized::type_parameter_env::TypeParameterEnv` is not re-exported: its
//! bounds are sets of `oxidized::typing_defs::Ty`, which has the constructors
//! of declared types only, whereas the OCaml bounds are `locl_ty` (see
//! `typing_kinding_defs.rs`). `T` is defined here instead, over a persistent
//! map, so that it is cheap to clone.

use std::hash::Hash;
use std::hash::Hasher;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::typing_defs::attributes;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::LoclTparam;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::UserAttribute;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_kinding_defs;
use crate::typing_kinding_defs::Kind;
use crate::typing_reason;
use crate::typing_set as ty_set;

/// `S_map.t`: persistent, with versions that share their entries
/// (`crate::pmap`); the environment copies it with every continuation.
pub type SMap<V> = crate::pmap::Map<String, V>;

pub type TparamName = String;

pub type TparamBounds = ty_set::T;

fn empty_bounds() -> TparamBounds {
    ty_set::T::default()
}

fn singleton_bound(ty: Ty) -> TparamBounds {
    std::iter::once(ty).collect()
}

pub type TparamInfo = typing_kinding_defs::Kind;

fn tparam_info_size(tpinfo: &TparamInfo) -> isize {
    (tpinfo.lower_bounds.len() + tpinfo.upper_bounds.len()) as isize
}

#[derive(Clone, Debug)]
pub struct T {
    /// The position indicates where the type parameter was defined.
    /// It may be Pos.none if the type parameter denotes a fresh type variable
    /// (i.e., without a source location that defines it)
    tparams: SMap<(PosOrDecl, TparamInfo)>,
    consistent: bool,
}

/// The name `oxidized` gives to `Type_parameter_env.t`.
pub type TypeParameterEnv = T;

/// `[@@deriving hash]`, with `[@hash.ignore]` on the positions.
impl Hash for T {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let T {
            tparams,
            consistent,
        } = self;
        tparams.len().hash(state);
        for (name, (_pos, tpinfo)) in tparams {
            name.hash(state);
            tpinfo.hash(state);
        }
        consistent.hash(state);
    }
}

pub fn bindings(tpenv: &T) -> Vec<(TparamName, TparamInfo)> {
    tpenv
        .tparams
        .iter()
        .map(|(k, (_, v))| (k.clone(), v.clone()))
        .collect()
}

pub fn empty() -> T {
    T {
        // `SMap.empty`, a constant.
        tparams: SMap::new(),
        consistent: true,
    }
}

pub fn mem(name: &str, tpenv: &T) -> bool {
    tpenv.tparams.contains_key(name)
}

pub fn get_with_pos(name: &str, tpenv: &T) -> Option<(PosOrDecl, TparamInfo)> {
    tpenv.tparams.get(name).cloned()
}

pub fn get(name: &str, tpenv: &T) -> Option<TparamInfo> {
    get_with_pos(name, tpenv).map(|(_, tpinfo)| tpinfo)
}

pub fn get_tparams(tpenv: &T) -> SMap<(PosOrDecl, TparamInfo)> {
    tpenv.tparams.clone()
}

pub fn add(def_pos: PosOrDecl, name: TparamName, tpinfo: TparamInfo, tpenv: &mut T) {
    tpenv.tparams.insert(name, (def_pos, tpinfo));
}

pub fn union(tpenv1: &T, tpenv2: &T) -> T {
    T {
        // `S_map.union` without `~combine`: the binding of the first map wins.
        tparams: tpenv1.tparams.clone().union(tpenv2.tparams.clone()),
        consistent: tpenv1.consistent && tpenv2.consistent,
    }
}

pub fn size(tpenv: &T) -> isize {
    let mut count = 0;
    for (_, (_, tpinfo)) in &tpenv.tparams {
        count = tparam_info_size(tpinfo) + count;
    }
    count
}

pub fn fold<A>(mut f: impl FnMut(&str, &TparamInfo, A) -> A, tpenv: &T, accu: A) -> A {
    let mut acc = accu;
    for (name, (_, tparam_info)) in &tpenv.tparams {
        acc = f(name, tparam_info, acc);
    }
    acc
}

/// What the `combine` function of [`merge_env`] makes of a binding: the
/// OCaml function returns `Some v` or `None`; `First` and `Second` say that
/// `v` is the binding of the first or of the second map, which the merge then
/// keeps without copying it.
pub enum Merged {
    First,
    Second,
    New((PosOrDecl, TparamInfo)),
    Neither,
}

/// `S_map.merge_env`, for a `combine` that gives `Merged::First`, and does
/// nothing else, on a binding that both maps share and on a binding that only
/// the first map has: these are not passed to it.
pub fn merge_env<E>(
    env: &mut E,
    tpenv1: &T,
    tpenv2: &T,
    mut combine: impl FnMut(
        &mut E,
        &str,
        Option<&(PosOrDecl, TparamInfo)>,
        Option<&(PosOrDecl, TparamInfo)>,
    ) -> Merged,
) -> T {
    // The OCaml calls `combine` on the bindings of the second map, in key
    // order, then on the bindings of the first map that the second does not
    // have, and builds the map of its results from the empty map. The two
    // maps are usually versions of one map (the continuations of one
    // function, which accumulate the fresh type parameters of its
    // refinements) that differ in a few bindings: rebuilding the result, or
    // even walking both maps, at every merge point made the merges cost the
    // size of the map each time. Here the result is built from the first
    // map, and `combine` sees, in key order, only the bindings of the second
    // map that the first does not share (`pmap::for_each_difference` skips
    // the subtrees that the maps share). The calls that are skipped give back
    // the first binding without effect (see above), and the order of the
    // others does not change.
    let s1 = &tpenv1.tparams;
    let s2 = &tpenv2.tparams;
    let mut map = s1.clone();
    if !s1.ptr_eq(s2) {
        crate::pmap::for_each_difference(s1, s2, |entry2, v1opt| {
            let (key, v2) = &**entry2;
            match combine(env, key, v1opt, Some(v2)) {
                Merged::First => assert!(v1opt.is_some(), "merge_env: no first binding"),
                Merged::Second => map.insert_entry(std::rc::Rc::clone(entry2)),
                Merged::New(v) => map.insert(key.clone(), v),
                Merged::Neither => {
                    if v1opt.is_some() {
                        map.remove_key(key);
                    }
                }
            }
        });
    }
    let tparams = map;
    T {
        tparams,
        consistent: tpenv1.consistent || tpenv2.consistent,
    }
}

pub fn get_lower_bounds(tpenv: &T, name: &str) -> TparamBounds {
    match get(name, tpenv) {
        None => empty_bounds(),
        Some(Kind { lower_bounds, .. }) => lower_bounds,
    }
}

pub fn get_upper_bounds(tpenv: &T, name: &str) -> TparamBounds {
    match get(name, tpenv) {
        None => empty_bounds(),
        Some(Kind { upper_bounds, .. }) => upper_bounds,
    }
}

pub fn get_reified(tpenv: &T, name: &str) -> aast::ReifyKind {
    match get(name, tpenv) {
        None => aast::ReifyKind::Erased,
        Some(Kind { reified, .. }) => reified,
    }
}

pub fn get_enforceable(tpenv: &T, name: &str) -> bool {
    match get(name, tpenv) {
        None => false,
        Some(Kind { enforceable, .. }) => enforceable,
    }
}

pub fn get_newable(tpenv: &T, name: &str) -> bool {
    match get(name, tpenv) {
        None => false,
        Some(Kind { newable, .. }) => newable,
    }
}

pub fn get_require_dynamic(tpenv: &T, name: &str) -> bool {
    match get(name, tpenv) {
        None => false,
        Some(Kind {
            require_dynamic, ..
        }) => require_dynamic,
    }
}

fn get_pos(tpenv: &T, name: &str) -> PosOrDecl {
    match get_with_pos(name, tpenv) {
        None => PosOrDecl::NONE,
        Some((pos, _)) => pos,
    }
}

pub fn get_rank(tpenv: &T, name: &str) -> isize {
    match get(name, tpenv) {
        None => 0,
        Some(Kind { rank, .. }) => rank,
    }
}

/// The names of `get_tparam_names`, in the same (decreasing) order, without
/// copying them.
pub fn iter_tparam_names(tpenv: &T) -> impl Iterator<Item = &TparamName> {
    tpenv.tparams.keys().rev()
}

pub fn get_tparam_names(tpenv: &T) -> Vec<TparamName> {
    // `S_map.keys` is `fold (fun k _ acc -> k :: acc) m []`: the names come
    // out in decreasing order.
    tpenv.tparams.keys().rev().cloned().collect()
}

pub fn is_consistent(tpenv: &T) -> bool {
    tpenv.consistent
}

/// When we detect that the set of constraints on the type parameters cannot be
/// satisfied, we can mark the env as inconsistent using this.
pub fn mark_inconsistent(tpenv: &mut T) {
    tpenv.consistent = false;
}

/// This assumes that [name] is a nullary generic parameter
fn is_generic_param(elide_nullable: bool, ty: &Ty, name: &str) -> bool {
    match get_node(ty) {
        Ty_::Tgeneric(name_) => name == name_,
        Ty_::Toption(ty) if elide_nullable => is_generic_param(elide_nullable, ty, name),
        _ => false,
    }
}

/// Add a single new upper bound [ty] to generic parameter [name] in [tpenv]
fn add_upper_bound_(tpenv: &mut T, name: &str, ty: Ty) {
    // Don't add superfluous T <: T or T <: ?T to environment
    if is_generic_param(true, &ty, name) {
    } else {
        let (def_pos, tpinfo) = match get_with_pos(name, tpenv) {
            None => (
                PosOrDecl::NONE,
                Kind {
                    lower_bounds: empty_bounds(),
                    upper_bounds: singleton_bound(ty),
                    reified: aast::ReifyKind::Erased,
                    enforceable: false,
                    newable: false,
                    require_dynamic: false,
                    rank: 0,
                },
            ),
            Some((pos, mut tp)) => {
                tp.upper_bounds.insert(ty);
                (pos, tp)
            }
        };
        add(def_pos, name.to_string(), tpinfo, tpenv)
    }
}

/// Add a single new lower bound [ty] to generic parameter [name] in [tpenv]
fn add_lower_bound_(tpenv: &mut T, name: &str, ty: Ty) {
    // Don't add superfluous T <: T to environment
    if is_generic_param(false, &ty, name) {
    } else {
        let (def_pos, tpinfo) = match get_with_pos(name, tpenv) {
            None => (
                PosOrDecl::NONE,
                Kind {
                    lower_bounds: singleton_bound(ty),
                    upper_bounds: empty_bounds(),
                    reified: aast::ReifyKind::Erased,
                    enforceable: false,
                    newable: false,
                    require_dynamic: false,
                    rank: 0,
                },
            ),
            Some((pos, mut tp)) => {
                tp.lower_bounds.insert(ty);
                (pos, tp)
            }
        };
        add(def_pos, name.to_string(), tpinfo, tpenv)
    }
}

/// Add a single new upper bound [ty] to generic parameter [name].
/// If the optional [intersect] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of upper bounds
///   (T <: t1) /\ ... /\ (T <: tn)
/// is equivalent to a single upper bound
///   T <: (t1 & ... & tn)
pub fn add_upper_bound(
    intersect: Option<&mut dyn FnMut(Ty, &[Ty]) -> Vec<Ty>>,
    env_tpenv: &mut T,
    name: TparamName,
    ty: Ty,
) {
    // The OCaml goes on reading `env_tpenv` after it has made `tpenv` from it
    // (and returns a value made from `env_tpenv` alone when there is no
    // [intersect]), so `tpenv` is a copy.
    let mut tpenv = env_tpenv.clone();
    match get_node(&ty) {
        Ty_::Tgeneric(formal_super) => add_lower_bound_(
            &mut tpenv,
            formal_super,
            mk((get_reason(&ty).clone(), Ty_::Tgeneric(name.clone()))),
        ),
        _ => {}
    }
    match intersect {
        None => add_upper_bound_(env_tpenv, &name, ty),
        Some(intersect) => {
            let tyl = intersect(
                ty,
                &get_upper_bounds(env_tpenv, &name)
                    .iter()
                    .cloned()
                    .collect::<Vec<Ty>>(),
            );
            let add_generic = |ty: Ty, tys: &mut ty_set::T| {
                if is_generic_param(true, &ty, &name) {
                } else {
                    tys.insert(ty);
                }
            };

            let def_pos = get_pos(env_tpenv, &name);
            let mut upper_bounds = empty_bounds();
            for ty in tyl.into_iter().rev() {
                add_generic(ty, &mut upper_bounds);
            }
            let lower_bounds = get_lower_bounds(env_tpenv, &name);
            let reified = get_reified(env_tpenv, &name);
            let enforceable = get_enforceable(env_tpenv, &name);
            let newable = get_newable(env_tpenv, &name);
            let require_dynamic = get_require_dynamic(env_tpenv, &name);
            let rank = get_rank(env_tpenv, &name);
            add(
                def_pos,
                name,
                Kind {
                    lower_bounds,
                    upper_bounds,
                    reified,
                    enforceable,
                    newable,
                    require_dynamic,
                    rank,
                },
                &mut tpenv,
            );
            *env_tpenv = tpenv;
        }
    }
}

/// Add a single new upper lower [ty] to generic parameter [name].
/// If the optional [union] operation is supplied, then use this to avoid
/// adding redundant bounds by merging the type with existing bounds. This makes
/// sense because a conjunction of lower bounds
///   (t1 <: T) /\ ... /\ (tn <: T)
/// is equivalent to a single lower bound
///   (t1 | ... | tn) <: T
pub fn add_lower_bound(
    union: Option<&mut dyn FnMut(Ty, &[Ty]) -> Vec<Ty>>,
    env_tpenv: &mut T,
    name: TparamName,
    ty: Ty,
) {
    // As in `add_upper_bound`: `tpenv` is a copy, `env_tpenv` stays in use.
    let mut tpenv = env_tpenv.clone();
    match get_node(&ty) {
        Ty_::Tgeneric(formal_sub) => add_upper_bound_(
            &mut tpenv,
            formal_sub,
            mk((get_reason(&ty).clone(), Ty_::Tgeneric(name.clone()))),
        ),
        _ => {}
    }
    match union {
        None => add_lower_bound_(env_tpenv, &name, ty),
        Some(union) => {
            let tyl = union(
                ty,
                &get_lower_bounds(env_tpenv, &name)
                    .iter()
                    .cloned()
                    .collect::<Vec<Ty>>(),
            );
            let def_pos = get_pos(env_tpenv, &name);
            let mut lower_bounds = empty_bounds();
            for ty in tyl.into_iter().rev() {
                lower_bounds.insert(ty);
            }
            let upper_bounds = get_upper_bounds(env_tpenv, &name);
            let reified = get_reified(env_tpenv, &name);
            let enforceable = get_enforceable(env_tpenv, &name);
            let newable = get_newable(env_tpenv, &name);
            let require_dynamic = get_require_dynamic(env_tpenv, &name);
            let rank = get_rank(env_tpenv, &name);
            add(
                def_pos,
                name,
                Kind {
                    lower_bounds,
                    upper_bounds,
                    reified,
                    enforceable,
                    newable,
                    require_dynamic,
                    rank,
                },
                &mut tpenv,
            );
            *env_tpenv = tpenv;
        }
    }
}

fn remove_upper_bound(tpenv: &mut T, name: &str, bound: &Ty) {
    match get_with_pos(name, tpenv) {
        None => {}
        Some((def_pos, mut tparam_info)) => {
            let mut bounds = tparam_info.upper_bounds;
            bounds.remove(bound);
            tparam_info.upper_bounds = bounds;
            add(def_pos, name.to_string(), tparam_info, tpenv)
        }
    }
}

fn remove_lower_bound(tpenv: &mut T, name: &str, bound: &Ty) {
    match get_with_pos(name, tpenv) {
        None => {}
        Some((def_pos, mut tparam_info)) => {
            let mut bounds = tparam_info.lower_bounds;
            bounds.remove(bound);
            tparam_info.lower_bounds = bounds;
            add(def_pos, name.to_string(), tparam_info, tpenv)
        }
    }
}

pub fn remove(tpenv: &mut T, name: &str) {
    let tparam = mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())));
    let lower_bounds = get_lower_bounds(tpenv, name);
    for ty in lower_bounds.iter() {
        match get_node(ty) {
            Ty_::Tgeneric(name) => remove_upper_bound(tpenv, name, &tparam),
            _ => {}
        }
    }
    let upper_bounds = get_upper_bounds(tpenv, name);
    for ty in upper_bounds.iter() {
        match get_node(ty) {
            Ty_::Tgeneric(name) => remove_lower_bound(tpenv, name, &tparam),
            _ => {}
        }
    }
    tpenv.tparams.remove_key(name);
}

/// `make_param_info` and `add_top` of `add_generic_parameters`, for one type
/// parameter. OCaml applies `add_generic_parameters` to declared type
/// parameters (the `.mli`) and to localized ones
/// (`add_generic_parameters_with_bounds`); here the two are different types,
/// and this is what the two have in common.
fn add_top(
    tpenv: &mut T,
    tp_name: PosId,
    tp_reified: aast::ReifyKind,
    tp_user_attributes: &[UserAttribute],
) {
    let make_param_info = || {
        let enforceable = attributes::mem(sn::user_attributes::ENFORCEABLE, tp_user_attributes);
        let newable = attributes::mem(sn::user_attributes::NEWABLE, tp_user_attributes);
        let require_dynamic =
            attributes::mem(sn::user_attributes::REQUIRE_DYNAMIC, tp_user_attributes);

        Kind {
            lower_bounds: empty_bounds(),
            upper_bounds: empty_bounds(),
            reified: tp_reified,
            enforceable,
            newable,
            require_dynamic,
            rank: 0,
        }
    };

    let (pos, name) = tp_name;
    add(pos, name, make_param_info(), tpenv)
}

/// Add type parameters to environment, initially with no bounds.
/// Existing type parameters with the same name will be overridden.
pub fn add_generic_parameters(tpenv: &mut T, tparaml: &[DeclTparam]) {
    for ast_tparam in tparaml {
        add_top(
            tpenv,
            ast_tparam.name.clone().to_oxidized(),
            ast_tparam.reified,
            &ast_tparam.user_attributes.clone().to_oxidized(),
        )
    }
}

fn add_bounds(t: &mut T, name: &str, cstrs: &[(ast_defs::ConstraintKind, Ty)]) {
    for (kind, ty) in cstrs {
        match kind {
            ast_defs::ConstraintKind::ConstraintAs => {
                add_upper_bound(None, t, name.to_string(), ty.clone())
            }
            ast_defs::ConstraintKind::ConstraintSuper => {
                add_lower_bound(None, t, name.to_string(), ty.clone())
            }
            ast_defs::ConstraintKind::ConstraintEq => {
                add_upper_bound(None, t, name.to_string(), ty.clone());
                add_lower_bound(None, t, name.to_string(), ty.clone())
            }
        }
    }
}

/// Add type parameters to environment with their bounds.
/// Existing type parameters with the same name will be overridden.
pub fn add_generic_parameters_with_bounds(t: &mut T, tparams: &[LoclTparam]) {
    // `add_generic_parameters t tparams`
    for ast_tparam in tparams {
        add_top(
            t,
            ast_tparam.name.clone(),
            ast_tparam.reified,
            &ast_tparam.user_attributes,
        )
    }
    for LoclTparam {
        name: (_, name),
        constraints: tp_constraints,
        ..
    } in tparams
    {
        add_bounds(t, name, tp_constraints)
    }
}

/// The `.mli` has `_ Typing_defs.tparam list`; the declared and the localized
/// type parameters are different types here, and this is called on the type
/// parameters of a localized function type only.
pub fn unbind_generic_parameters(t: &mut T, tparams: &[LoclTparam]) {
    for LoclTparam {
        name: (_, name), ..
    } in tparams
    {
        remove(t, name)
    }
}

fn force_lazy_values_tparam_info(info: TparamInfo) -> TparamInfo {
    typing_kinding_defs::force_lazy_values(info)
}

pub fn force_lazy_values(env: &mut T) {
    let T {
        tparams,
        consistent: _,
    } = env;
    *tparams = tparams
        .iter()
        .map(|(name, (p, info))| {
            (
                name.clone(),
                (p.clone(), force_lazy_values_tparam_info(info.clone())),
            )
        })
        .collect();
}

fn map_over_tparam_info(f: &mut impl FnMut(&Ty) -> Ty, info: &TparamInfo) -> TparamInfo {
    // Lower bounds first, then upper bounds, each in the order of the set.
    // `TySet.map`, which builds the tree OCaml builds.
    let lower_bounds = ty_set::map(&mut *f, &info.lower_bounds);
    let upper_bounds = ty_set::map(&mut *f, &info.upper_bounds);
    Kind {
        lower_bounds,
        upper_bounds,
        ..info.clone()
    }
}

pub fn map(mut f: impl FnMut(&Ty) -> Ty, env: &mut T) {
    env.tparams = env
        .tparams
        .iter()
        .map(|(name, (p, info))| {
            (
                name.clone(),
                (p.clone(), map_over_tparam_info(&mut f, info)),
            )
        })
        .collect();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn generic(name: &str) -> Ty {
        mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    fn option(ty: Ty) -> Ty {
        mk((typing_reason::none(), Ty_::Toption(ty)))
    }

    fn info() -> TparamInfo {
        Kind {
            lower_bounds: empty_bounds(),
            upper_bounds: empty_bounds(),
            reified: aast::ReifyKind::Erased,
            enforceable: false,
            newable: false,
            require_dynamic: false,
            rank: 0,
        }
    }

    fn bounds(tys: &[Ty]) -> Vec<Ty> {
        tys.to_vec()
    }

    fn lower(tpenv: &T, name: &str) -> Vec<Ty> {
        get_lower_bounds(tpenv, name).iter().cloned().collect()
    }

    fn upper(tpenv: &T, name: &str) -> Vec<Ty> {
        get_upper_bounds(tpenv, name).iter().cloned().collect()
    }

    #[test]
    fn empty_env() {
        let tpenv = empty();
        assert!(is_consistent(&tpenv));
        assert!(!mem("T", &tpenv));
        assert!(get("T", &tpenv).is_none());
        assert_eq!(size(&tpenv), 0);
        assert!(get_tparam_names(&tpenv).is_empty());
        assert!(lower(&tpenv, "T").is_empty());
        assert!(upper(&tpenv, "T").is_empty());
        assert!(matches!(get_reified(&tpenv, "T"), aast::ReifyKind::Erased));
        assert!(!get_enforceable(&tpenv, "T"));
        assert!(!get_newable(&tpenv, "T"));
        assert!(!get_require_dynamic(&tpenv, "T"));
        assert_eq!(get_rank(&tpenv, "T"), 0);
    }

    #[test]
    fn names_come_out_in_decreasing_order() {
        let mut tpenv = empty();
        add(PosOrDecl::NONE, "Tb".to_string(), info(), &mut tpenv);
        add(PosOrDecl::NONE, "Ta".to_string(), info(), &mut tpenv);
        add(PosOrDecl::NONE, "Tc".to_string(), info(), &mut tpenv);
        assert_eq!(get_tparam_names(&tpenv), vec!["Tc", "Tb", "Ta"]);
        let names: Vec<_> = bindings(&tpenv).into_iter().map(|(k, _)| k).collect();
        assert_eq!(names, vec!["Ta", "Tb", "Tc"]);
    }

    #[test]
    fn upper_bound_without_intersect() {
        let mut tpenv = empty();
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("U"));
        assert_eq!(upper(&tpenv, "T"), bounds(&[generic("U")]));
        // Without [intersect] the symmetric bound `T <: U` is not recorded
        // on U: the OCaml returns a value made from the original environment.
        assert!(!mem("U", &tpenv));
        assert_eq!(size(&tpenv), 1);
    }

    #[test]
    fn upper_bound_with_intersect_records_symmetric_bound() {
        let mut tpenv = empty();
        let mut seen = None;
        let mut intersect = |ty: Ty, tys: &[Ty]| {
            seen = Some(tys.len());
            let mut tys = tys.to_vec();
            tys.push(ty);
            tys
        };
        add_upper_bound(
            Some(&mut intersect),
            &mut tpenv,
            "T".to_string(),
            generic("U"),
        );
        assert_eq!(seen, Some(0));
        assert_eq!(upper(&tpenv, "T"), bounds(&[generic("U")]));
        assert_eq!(lower(&tpenv, "U"), bounds(&[generic("T")]));
    }

    #[test]
    fn superfluous_bounds_are_not_added() {
        let mut tpenv = empty();
        // T <: T and T <: ?T
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("T"));
        add_upper_bound(None, &mut tpenv, "T".to_string(), option(generic("T")));
        assert!(!mem("T", &tpenv));
        // T <: T, but ?T <: T is kept
        add_lower_bound(None, &mut tpenv, "T".to_string(), generic("T"));
        assert!(!mem("T", &tpenv));
        add_lower_bound(None, &mut tpenv, "T".to_string(), option(generic("T")));
        assert_eq!(lower(&tpenv, "T"), bounds(&[option(generic("T"))]));
        // With [intersect], generic bounds equal to the parameter are dropped
        // from the result of the operation.
        let mut intersect = |ty: Ty, _tys: &[Ty]| vec![ty, generic("T"), option(generic("T"))];
        add_upper_bound(
            Some(&mut intersect),
            &mut tpenv,
            "T".to_string(),
            generic("U"),
        );
        assert_eq!(upper(&tpenv, "T"), bounds(&[generic("U")]));
        // ... but with [union] they are kept.
        let mut union = |ty: Ty, _tys: &[Ty]| vec![ty, generic("T")];
        add_lower_bound(Some(&mut union), &mut tpenv, "T".to_string(), generic("V"));
        let mut expected = bounds(&[generic("T"), generic("V")]);
        expected.sort();
        assert_eq!(lower(&tpenv, "T"), expected);
    }

    #[test]
    fn intersect_replaces_the_bounds_and_keeps_the_rest() {
        let mut tpenv = empty();
        add(
            PosOrDecl::NONE,
            "T".to_string(),
            Kind {
                enforceable: true,
                rank: 3,
                ..info()
            },
            &mut tpenv,
        );
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("A"));
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("B"));
        assert_eq!(size(&tpenv), 2);
        let mut intersect = |ty: Ty, tys: &[Ty]| {
            assert_eq!(tys.len(), 2);
            vec![ty]
        };
        add_upper_bound(
            Some(&mut intersect),
            &mut tpenv,
            "T".to_string(),
            option(generic("C")),
        );
        assert_eq!(upper(&tpenv, "T"), bounds(&[option(generic("C"))]));
        assert!(get_enforceable(&tpenv, "T"));
        assert_eq!(get_rank(&tpenv, "T"), 3);
    }

    #[test]
    fn remove_also_removes_the_parameter_from_the_bounds_of_others() {
        let mut tpenv = empty();
        // T <: U recorded on both sides, plus an unrelated bound on U.
        let mut keep = |ty: Ty, tys: &[Ty]| {
            let mut tys = tys.to_vec();
            tys.push(ty);
            tys
        };
        add_upper_bound(Some(&mut keep), &mut tpenv, "T".to_string(), generic("U"));
        add_lower_bound(None, &mut tpenv, "U".to_string(), generic("V"));
        assert_eq!(upper(&tpenv, "T"), bounds(&[generic("U")]));
        assert_eq!(lower(&tpenv, "U").len(), 2);
        remove(&mut tpenv, "T");
        assert!(!mem("T", &tpenv));
        assert_eq!(lower(&tpenv, "U"), bounds(&[generic("V")]));
    }

    #[test]
    fn union_prefers_the_first_and_merge_env_visits_second_then_first() {
        let mut tpenv1 = empty();
        let mut tpenv2 = empty();
        add(
            PosOrDecl::NONE,
            "T".to_string(),
            Kind { rank: 1, ..info() },
            &mut tpenv1,
        );
        add(
            PosOrDecl::NONE,
            "A".to_string(),
            Kind { rank: 1, ..info() },
            &mut tpenv1,
        );
        add(
            PosOrDecl::NONE,
            "T".to_string(),
            Kind { rank: 2, ..info() },
            &mut tpenv2,
        );
        add(
            PosOrDecl::NONE,
            "U".to_string(),
            Kind { rank: 2, ..info() },
            &mut tpenv2,
        );
        mark_inconsistent(&mut tpenv2);

        let u = union(&tpenv1, &tpenv2);
        assert_eq!(get_rank(&u, "T"), 1);
        assert_eq!(get_rank(&u, "U"), 2);
        assert_eq!(get_rank(&u, "A"), 1);
        assert!(!is_consistent(&u));

        let mut order: Vec<String> = vec![];
        let merged = merge_env(&mut order, &tpenv1, &tpenv2, |order, name, i1, i2| {
            order.push(format!("{}:{}{}", name, i1.is_some(), i2.is_some()));
            if name == "U" {
                Merged::Neither
            } else if i1.is_some() {
                Merged::First
            } else {
                Merged::Second
            }
        });
        // The bindings of the second map that the first does not share, in
        // key order (see `merge_env`).
        assert_eq!(order, vec!["T:truetrue", "U:falsetrue"]);
        assert_eq!(get_tparam_names(&merged), vec!["T", "A"]);
        // `merge_env` is consistent as soon as one side is.
        assert!(is_consistent(&merged));
    }

    #[test]
    fn map_applies_to_all_bounds() {
        let mut tpenv = empty();
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("A"));
        add_lower_bound(None, &mut tpenv, "T".to_string(), generic("B"));
        map(|ty| option(ty.clone()), &mut tpenv);
        assert_eq!(upper(&tpenv, "T"), bounds(&[option(generic("A"))]));
        assert_eq!(lower(&tpenv, "T"), bounds(&[option(generic("B"))]));
    }

    #[test]
    fn clones_are_independent() {
        let mut tpenv = empty();
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("A"));
        let old = tpenv.clone();
        add_upper_bound(None, &mut tpenv, "T".to_string(), generic("B"));
        mark_inconsistent(&mut tpenv);
        assert_eq!(upper(&old, "T"), bounds(&[generic("A")]));
        assert!(is_consistent(&old));
        assert_eq!(upper(&tpenv, "T").len(), 2);
    }
}
