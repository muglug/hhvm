// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 8857-9374): module `Can_index_assign`.
//! See `hh/PORTING.md`.
//!
//! - `simplify` and `simplify_` have the signature of every constraint
//!   handler (see `prelude.rs`).
//! - `check_arraykey_index error env pos container_ty index_ty` returns
//!   `(env, ty_mismatch)`: here the `(locl_ty, locl_ty * locl_ty) result`,
//!   the environment being updated in place. `check_arraykey_index_write` is
//!   its partial application to `mk_err`.
//! - The local `invalid ~fail env = invalid ~fail env` of `simplify_` is the
//!   function itself, which is called directly.
//! - `TShapeMap.add` replaces the key of an equal binding (and so its
//!   position) as well as the value; `BTreeMap::insert` would keep the old
//!   key, so the binding is removed first.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::s_set::SSet;

use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::tast;
use crate::typechecker_options;
use crate::typing_coercion;
use crate::typing_defs_constraints::CanIndexAssign;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::t_shape_map::TShapeField;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::ReadOrWrite;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_intersection;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_set;
use crate::typing_shape_normalize;
use crate::typing_shapes;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_union;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// `type rhs = { reason_super: Reason.t; can_index_assign: can_index_assign }`
#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub can_index_assign: CanIndexAssign,
}

/// `List.split_n l n`: the first `n` elements and the rest (all of `l` and
/// nothing if `n` is larger than its length, nothing and all of `l` if `n` is
/// negative).
fn split_n(l: &[Ty], n: isize) -> (&[Ty], &[Ty]) {
    let n = n.clamp(0, l.len() as isize) as usize;
    l.split_at(n)
}

/// Check that an index to a map-like collection passes the basic test of
/// being a subtype of arraykey
pub(crate) fn check_arraykey_index(
    error: impl FnOnce(Pos, (PosOrDecl, Lazy<String>), (PosOrDecl, Lazy<String>)) -> primary::T,
    env: &mut Env,
    pos: Pos,
    container_ty: Ty,
    index_ty: Ty,
) -> Result<Ty, (Ty, Ty)> {
    let container_ty = env::expand_type(env, container_ty);
    let reason = match get_node(&container_ty) {
        Ty_::Tclass((_, cn), _, _) => reason::index_class(cn),
        _ => reason::index_array(),
    };
    let info_of_type = |env: &Env, ty: &Ty| -> (PosOrDecl, Lazy<String>) {
        let env = env.clone();
        let ty = ty.clone();
        (
            get_pos(&ty),
            Lazy::new(move || typing_print::error(None, &env, &ty)),
        )
    };
    let container_info = info_of_type(env, &container_ty);
    let index_info = info_of_type(env, &index_ty);
    let ty_arraykey = make_type::arraykey(reason::idx_dict(pos.clone()));
    // If we have an error in coercion here, we will add a `Hole` indicating the
    // actual and expected type. The `Hole` may then be used in a codemod to
    // add a call to `UNSAFE_CAST` so we need to consider what type we expect.
    // There is a somewhat common pattern in older parts of www to do something like:
    //
    // ```
    // function keyset_issue(?string $x): keyset<string> {
    //   $xs = keyset<string>[];
    //   ...
    //   /* HH_FIXME[4435] keyset values must be arraykeys */
    //   $xs[] = $x;
    //   return Keyset\filter_nulls($xs);
    // }
    // ```
    // (even though it is impossible for keysets to contain nulls).
    //
    // If we were to add an expected type of 'arraykey' here it would be
    // correct but adding an `UNSAFE_CAST<?string,arraykey>($x)` means we
    // get cascading errors; here, we now have the wrong return type.
    //
    // To try and prevent this, if this is an optional type where the nonnull
    // part can be coerced to arraykey, we prefer that type as our expected type.
    let base_error = error(pos.clone(), container_info, index_info);
    let (ty_actual, is_option) = match get_node(&index_ty) {
        Ty_::Toption(inner_ty) => (inner_ty.clone(), true),
        _ => (index_ty.clone(), false),
    };
    let e1 = typing_coercion::coerce_type(
        Some(true),
        None,
        None,
        pos,
        reason,
        env,
        ty_actual.clone(),
        ty_arraykey.clone(),
        Enforcement::Enforced,
        callback::always(base_error.clone()),
    );
    let (ty_mismatch, e2) = match &e1 {
        None if is_option => (
            Err((index_ty, ty_actual)),
            Some(typing_error::primary(base_error)),
        ),
        None => (Ok(index_ty), None),
        Some(_) => (Err((index_ty, ty_arraykey)), None),
    };
    // `Option.merge e1 e2 ~f:Typing_error.both`
    let err = match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e1), None) => Some(e1),
        (None, e2) => e2,
    };
    if let Some(err) = &err {
        typing_error_utils::add_typing_error(err, env);
    }
    ty_mismatch
}

pub(crate) fn check_arraykey_index_write(
    env: &mut Env,
    pos: Pos,
    container_ty: Ty,
    index_ty: Ty,
) -> Result<Ty, (Ty, Ty)> {
    let mk_err = |pos: Pos,
                  (container_pos, container_ty_name): (PosOrDecl, Lazy<String>),
                  (key_pos, key_ty_name): (PosOrDecl, Lazy<String>)| {
        primary::T::InvalidArraykey {
            pos,
            ctxt: ReadOrWrite::Write,
            container_pos,
            container_ty_name,
            key_pos,
            key_ty_name,
        }
    };
    check_arraykey_index(mk_err, env, pos, container_ty, index_ty)
}

/// Since array update constraint solving is under development,
/// it is an experimental feature and will only be turned on
/// if the flag constraint_array_index_assign is set.
pub fn simplify(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let ty_sub = env::expand_type(env, lhs.ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        rhs.reason_super.clone(),
        ConstraintType_::TcanIndexAssign(rhs.can_index_assign.clone()),
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // The arguments are printed in the environment as it is before the
        // continuation runs.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Can_index_assign.simplify",
            &log_env,
            &ty_sub,
            &ty_super,
            || simplify_(subtype_env, this_ty, lhs, rhs, env),
        )
    } else {
        simplify_(subtype_env, this_ty, lhs, rhs, env)
    }
}

/// The local `let rec loop` of the case of an intersection in `simplify_`
/// (its free variables are the parameters before `ty_subs`). `tys` and `errs`
/// are in the order of the OCaml lists (the last one added first).
#[allow(clippy::too_many_arguments)]
fn loop_(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    sub_supportdyn: &Option<Reason>,
    reason_super: &Reason,
    cia: &CanIndexAssign,
    r_sub: &Reason,
    update_reason: &dyn Fn(&Env, Ty) -> Ty,
    simplify_val: &dyn Fn(Ty, &mut Env) -> tl::SubtypeProp,
    ty_subs: &[Ty],
    tys: Vec<Ty>,
    errs: Vec<Option<typing_error::T>>,
    env: &mut Env,
) -> tl::SubtypeProp {
    match ty_subs {
        [] => match &tys[..] {
            [] => {
                let err = typing_error::intersect_opt(errs.into_iter().flatten().collect());
                invalid(err, env)
            }
            _ => {
                let ty = typing_intersection::intersect_list(env, r_sub.clone(), &tys);
                simplify_val(ty, env)
            }
        },
        [ty_sub, ty_subs @ ..] => {
            let ty_sub = update_reason(env, ty_sub.clone());
            let val_ty = env::fresh_type(env, cia.array_pos.clone());
            let prop = simplify_(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: sub_supportdyn.as_ref(),
                    ty_sub: &ty_sub,
                },
                Rhs {
                    reason_super: reason_super.clone(),
                    can_index_assign: CanIndexAssign {
                        val: val_ty.clone(),
                        ..cia.clone()
                    },
                },
                env,
            );
            match tl::get_error_if_unsat(&prop) {
                Some(err) => {
                    let mut errs_ = vec![err];
                    errs_.extend(errs);
                    loop_(
                        subtype_env,
                        this_ty,
                        sub_supportdyn,
                        reason_super,
                        cia,
                        r_sub,
                        update_reason,
                        simplify_val,
                        ty_subs,
                        tys,
                        errs_,
                        env,
                    )
                }
                _ => {
                    if true {
                        and(env, prop, |env| {
                            let mut tys_ = vec![val_ty];
                            tys_.extend(tys);
                            loop_(
                                subtype_env,
                                this_ty,
                                sub_supportdyn,
                                reason_super,
                                cia,
                                r_sub,
                                update_reason,
                                simplify_val,
                                ty_subs,
                                tys_,
                                errs,
                                env,
                            )
                        })
                    } else {
                        //I sm dropping errors here. Is that ok?
                        loop_(
                            subtype_env,
                            this_ty,
                            sub_supportdyn,
                            reason_super,
                            cia,
                            r_sub,
                            update_reason,
                            simplify_val,
                            ty_subs,
                            tys,
                            errs,
                            env,
                        )
                    }
                }
            }
        }
    }
}

/// The local `get_transitive_upper_bounds` of the case of a generic in
/// `simplify_`.
fn get_transitive_upper_bounds(env: &mut Env, ty: Ty) -> Vec<Ty> {
    // `let rec iter seen env acc tyl`, whose recursive calls are all
    // tail calls: `tyl` is the list still to visit, its head at the front.
    fn iter(mut seen: SSet, env: &mut Env, mut acc: typing_set::T, tyl: Vec<Ty>) -> typing_set::T {
        let mut tyl: std::collections::VecDeque<Ty> = tyl.into();
        loop {
            match tyl.pop_front() {
                None => return acc,
                Some(ty) => {
                    let ety = env::expand_type(env, ty.clone());
                    match get_node(&ety) {
                        Ty_::Tgeneric(n) => {
                            if seen.contains(n) {
                                continue;
                            } else {
                                seen.insert(n.clone());
                                // `Typing_set.elements (Env.get_upper_bounds env n) @ tyl`
                                let bounds = typing_set::elements(&env::get_upper_bounds(env, n));
                                for bound in bounds.into_iter().rev() {
                                    tyl.push_front(bound);
                                }
                            }
                        }
                        _ => acc = typing_set::add(ty, &acc),
                    }
                }
            }
        }
    }
    let resl = iter(SSet::new(), env, typing_set::empty(), vec![ty]);
    typing_set::elements(&resl)
}

pub(crate) fn simplify_(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    Lhs {
        ty_sub,
        sub_supportdyn,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Rhs {
        reason_super,
        can_index_assign: cia,
    } = rhs.clone();
    let maybe_make_supportdyn = |r: Reason, env: &mut Env, ty: Ty| -> Ty {
        if sub_supportdyn.is_some() {
            t_utils::make_supportdyn(r, env, ty)
        } else {
            ty
        }
    };
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let subtype_env = subtype_env::possibly_add_violated_constraint(
        subtype_env.clone(),
        get_reason(&ty_sub).clone(),
        reason_super.clone(),
    );
    let fail = subtype_env::fail(
        &subtype_env,
        InternalType::LoclType(ty_sub.clone()),
        InternalType::ConstraintType(mk_constraint_type((
            reason_super.clone(),
            ConstraintType_::TcanIndexAssign(cia.clone()),
        ))),
    );
    let arity_error = |r: &Reason, name: &str, env: &mut Env| -> tl::SubtypeProp {
        invalid(
            Some(typing_error::primary(primary::T::ArrayGetArity {
                pos: cia.expr_pos.clone(),
                name: name.to_string(),
                decl_pos: reason::to_pos(r),
            })),
            env,
        )
    };
    let simplify_default =
        |subtype_env: &subtype_env::T, lhs: Ty, rhs: Ty, env: &mut Env| -> tl::SubtypeProp {
            subtype::simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: sub_supportdyn.clone(),
                    ty_sub: &lhs,
                },
                subtype::Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &rhs,
                },
                env,
            )
        };
    let simplify_key = |tk: Ty, env: &mut Env| -> tl::SubtypeProp {
        let tk = make_type::locl_like(reason::dynamic_coercion(get_reason(&tk).clone()), tk);
        simplify_default(&subtype_env, cia.key.clone(), tk, env)
    };
    let simplify_val = |tv: Ty, env: &mut Env| -> tl::SubtypeProp {
        simplify_default(&subtype_env, tv, cia.val.clone(), env)
    };
    let pessimise_type = |env: &mut Env, ty: Ty| -> Ty {
        let dynamic = make_type::dynamic(get_reason(&ty).clone());
        typing_union::union(env, None, None, ty, dynamic)
    };
    let maybe_pessimise_type = |env: &mut Env, ty: Ty| -> Ty {
        if typechecker_options::pessimise_builtins(&env::get_tcopt(env)) {
            pessimise_type(env, ty)
        } else {
            ty
        }
    };
    let mk_prop = simplify;
    let supports_dynamic = |ty: Ty, env: &mut Env| -> tl::SubtypeProp {
        let r = get_reason(&ty).clone();
        simplify_default(&subtype_env, ty, make_type::supportdyn_mixed(r), env)
    };
    let got_dynamic = |env: &mut Env| -> tl::SubtypeProp {
        let tv = make_type::dynamic(get_reason(&ty_sub).clone());
        let prop = supports_dynamic(cia.key.clone(), env);
        let prop = and(env, prop, |env| supports_dynamic(cia.write.clone(), env));
        and(env, prop, |env| simplify_val(tv, env))
    };
    let r_sub = get_reason(&ty_sub).clone();
    match get_node(&ty_sub) {
        Ty_::Tvar(_) => mk_issubtype_prop(
            sub_supportdyn.clone(),
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            InternalType::ConstraintType(mk_constraint_type((
                reason_super.clone(),
                ConstraintType_::TcanIndexAssign(cia.clone()),
            ))),
        ),
        Ty_::Tclass((_, n), _, argl) if n == sn::collections::VECTOR => match &argl[..] {
            [tv] => {
                let tk = make_type::int(reason::idx_vector(cia.index_pos.clone()));
                let tv = maybe_pessimise_type(env, tv.clone());
                let tv = maybe_make_supportdyn(r_sub.clone(), env, tv);
                let prop = simplify_key(tk, env);
                let prop = and(env, prop, |env| {
                    simplify_default(&subtype_env, cia.write.clone(), tv, env)
                });
                and(env, prop, |env| simplify_val(ty_sub.clone(), env))
            }
            _ => arity_error(&r_sub, n, env),
        },
        Ty_::Tclass(id, e, argl) if id.1 == sn::collections::VEC => match &argl[..] {
            [tv] => {
                let tk = make_type::int(reason::idx_vector(cia.index_pos.clone()));
                let prop = simplify_key(tk, env);
                and(env, prop, |env| {
                    let tv = maybe_make_supportdyn(r_sub.clone(), env, tv.clone());
                    let tv_ = typing_union::union(env, None, None, tv, cia.write.clone());
                    let ty = mk((r_sub.clone(), Ty_::Tclass(id.clone(), e.clone(), vec![tv_])));
                    simplify_val(ty, env)
                })
            }
            _ => arity_error(&r_sub, &id.1, env),
        },
        Ty_::Tclass(id, e, argl) if id.1 == sn::collections::DICT => {
            let idx_err = check_arraykey_index_write(
                env,
                cia.expr_pos.clone(),
                ty_sub.clone(),
                cia.key.clone(),
            );
            match &argl[..] {
                [tk, tv] => {
                    let tv = maybe_make_supportdyn(r_sub.clone(), env, tv.clone());
                    let tk_ = {
                        let ak_t = make_type::arraykey(reason::idx_dict(cia.index_pos.clone()));
                        match idx_err {
                            Ok(_) => {
                                let tkey_new = typing_intersection::intersect(
                                    env,
                                    reason::idx_dict(cia.index_pos.clone()),
                                    cia.key.clone(),
                                    ak_t,
                                );
                                typing_union::union(env, None, None, tk.clone(), tkey_new)
                            }
                            _ => typing_union::union(env, None, None, tk.clone(), cia.key.clone()),
                        }
                    };
                    let tv_ = typing_union::union(env, None, None, tv, cia.write.clone());
                    let ty = mk((
                        r_sub.clone(),
                        Ty_::Tclass(id.clone(), e.clone(), vec![tk_, tv_]),
                    ));
                    simplify_val(ty, env)
                }
                _ => arity_error(&r_sub, &id.1, env),
            }
        }
        Ty_::Tclass((_, n), _, argl) if n == sn::collections::MAP => match &argl[..] {
            [tk, tv] => {
                let tv = maybe_pessimise_type(env, tv.clone());
                let tv = maybe_make_supportdyn(r_sub.clone(), env, tv);
                let tk = maybe_pessimise_type(env, tk.clone());
                let prop = simplify_key(tk, env);
                let prop = and(env, prop, |env| {
                    simplify_default(&subtype_env, cia.write.clone(), tv, env)
                });
                and(env, prop, |env| simplify_val(ty_sub.clone(), env))
            }
            _ => arity_error(&r_sub, n, env),
        },
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: TupleExtra::Tvariadic(_),
        }) if t_optional.is_empty() => {
            let fail = |reason: Ureason, env: &mut Env| -> tl::SubtypeProp {
                invalid(
                    Some(typing_error::primary(primary::T::GenericUnify {
                        pos: cia.index_pos.clone(),
                        msg: reason::string_of_ureason(&reason),
                    })),
                    env,
                )
            };
            match &cia.index_expr {
                nast::Expr(_, _, nast::Expr_::Int(n)) => {
                    let idx = int_of_string_opt(n);
                    match idx.map(|idx| split_n(t_required, idx)) {
                        Some((tyl_, [_, tyl__ @ ..])) => {
                            // `tyl' @ (cia.cia_write :: tyl'')`
                            let mut tyl = tyl_.to_vec();
                            tyl.push(cia.write.clone());
                            tyl.extend(tyl__.iter().cloned());
                            let ty = make_type::tuple(r_sub.clone(), tyl);
                            let ty = maybe_make_supportdyn(r_sub.clone(), env, ty);
                            simplify_val(ty, env)
                        }
                        _ => fail(reason::index_tuple(), env),
                    }
                }
                _ => fail(Ureason::URtupleAccess, env),
            }
        }
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: shape_kind,
            fields: fdm,
        })) => match typing_shapes::tshape_field_name_with_ty_err(env, &cia.index_expr) {
            Err(ty_err) => invalid(Some(ty_err), env),
            Ok(field) => {
                let fdm = if sub_supportdyn.is_some() {
                    let f = |env: &mut Env,
                             _name: &t_shape_map::Key,
                             ShapeFieldType {
                                 optional: sft_optional,
                                 ty: sft_ty,
                             }: ShapeFieldType| {
                        let sft_ty = t_utils::make_supportdyn(r_sub.clone(), env, sft_ty);
                        ShapeFieldType {
                            optional: sft_optional,
                            ty: sft_ty,
                        }
                    };
                    t_shape_map::map_env(f, env, fdm.clone())
                } else {
                    fdm.clone()
                };
                // `TShapeMap.add field ... fdm`
                let mut fdm_ = fdm;
                let field = TShapeField(field);
                fdm_.remove(&field);
                fdm_.insert(
                    field,
                    ShapeFieldType {
                        optional: false,
                        ty: cia.write.clone(),
                    },
                );
                let ty = mk((
                    r_sub.clone(),
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: shape_kind.clone(),
                        fields: fdm_,
                    })),
                ));
                simplify_val(ty, env)
            }
        },
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            // A field write is a runtime dict write: it adds a new field or overwrites
            // an existing one, and under rightmost-wins the written field must win over
            // every element. [set_rightmost_field] sets it on the rightmost concrete
            // element in place, or appends a new closed single-field element when the
            // rightmost element is opaque matching the direct write path in
            // [typing_array_access].
            match typing_shapes::tshape_field_name_with_ty_err(env, &cia.index_expr) {
                Err(ty_err) => invalid(Some(ty_err), env),
                Ok(field) => {
                    // `snd (Env.expand_type env ty)`: each element is expanded in
                    // the environment of `simplify_`, which is not changed.
                    let ss_elems: Vec<Ty> = ss_elems
                        .iter()
                        .map(|ty| env::expand_type(&mut env.clone(), ty.clone()))
                        .collect();
                    let (_err, ty) = typing_shape_normalize::set_rightmost_field(
                        &ss_elems,
                        field,
                        ShapeFieldType {
                            optional: false,
                            ty: cia.write.clone(),
                        },
                        sub_supportdyn.is_some(),
                        r_sub.clone(),
                        env,
                    );
                    simplify_val(ty, env)
                }
            }
        }
        Ty_::Tclass((_, n), _, _)
            if n == sn::collections::ANY_ARRAY
                && tast::is_under_dynamic_assumptions(env.checked) =>
        {
            got_dynamic(env)
        }
        Ty_::Tclass((_, n), _, _)
            if n == sn::collections::KEYED_CONTAINER
                || n == sn::collections::ANY_ARRAY
                || n == sn::collections::PAIR
                || n == sn::collections::CONST_VECTOR
                || n == sn::collections::IMM_VECTOR
                || n == sn::collections::CONST_MAP
                || n == sn::collections::IMM_MAP =>
        {
            let ty_name = {
                let env = env.clone();
                let ty_sub = ty_sub.clone();
                Lazy::new(move || typing_print::error(None, &env, &ty_sub))
            };
            invalid(
                Some(typing_error::primary(primary::T::ConstMutation {
                    pos: cia.expr_pos.clone(),
                    decl_pos: reason::to_pos(&r_sub),
                    ty_name,
                })),
                env,
            )
        }
        Ty_::Tintersection(ty_subs) => {
            // A & B <: C iif A <: C | !B
            //
            // The second case does not bind the environment that
            // `find_type_with_exact_negation` returns: it goes on with the
            // one from before.
            match subtype_negation::find_type_with_exact_negation_opt(env, ty_subs) {
                Some((non_ty, tyl)) => {
                    let ty_sub = make_type::intersection(r_sub.clone(), tyl);
                    let lift_rhs = |Rhs {
                                        reason_super,
                                        can_index_assign,
                                    }: Rhs| {
                        mk_constraint_type((
                            reason_super,
                            ConstraintType_::TcanIndexAssign(can_index_assign),
                        ))
                    };
                    let lhs = (sub_supportdyn, &ty_sub);
                    let rhs_subtype = subtype::Rhs {
                        super_supportdyn: false,
                        super_like: false,
                        ty_super: &non_ty,
                    };
                    let rhs_can_index_assign = Rhs {
                        reason_super: reason_super.clone(),
                        can_index_assign: cia.clone(),
                    };
                    let rhs = (reason_super.clone(), rhs_subtype, rhs_can_index_assign);
                    common::simplify_disj_r(
                        &subtype_env,
                        this_ty,
                        fail,
                        mk_prop,
                        lift_rhs,
                        lhs,
                        rhs,
                        env,
                    )
                }
                None => {
                    let update_reason = |env: &Env, ty: Ty| {
                        env::update_reason(env, ty, |r_sub_prj| {
                            reason::prj_inter_sub(r_sub.clone(), r_sub_prj)
                        })
                    };
                    loop_(
                        &subtype_env,
                        this_ty,
                        &sub_supportdyn.cloned(),
                        &reason_super,
                        &cia,
                        &r_sub,
                        &update_reason,
                        &simplify_val,
                        ty_subs,
                        vec![],
                        vec![],
                        env,
                    )
                }
            }
        }
        Ty_::Tgeneric(_generic_nm) => {
            let tyl = get_transitive_upper_bounds(env, ty_sub.clone());
            if tyl.is_empty() {
                invalid(fail, env)
            } else {
                let ty = typing_intersection::intersect_list(env, r_sub.clone(), &tyl);
                simplify_(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: sub_supportdyn.clone(),
                        ty_sub: &ty,
                    },
                    rhs,
                    env,
                )
            }
        }
        Ty_::Tdynamic(_) => got_dynamic(env),
        Ty_::Tany(_) => simplify_val(ty_sub.clone(), env),
        Ty_::Tprim(Tprim::Tnull) if tast::is_under_dynamic_assumptions(env.checked) => {
            got_dynamic(env)
        }
        Ty_::Tclass((_, id), _, _) if C_STRING == id => {
            let tk = make_type::int(reason::idx((cia.index_pos.clone(), r_sub.clone())));
            let tv = make_type::string(reason::witness(cia.expr_pos.clone()));
            let tv = maybe_pessimise_type(env, tv);
            let prop = simplify_key(tk, env);
            let prop = and(env, prop, |env| {
                simplify_default(&subtype_env, cia.write.clone(), tv, env)
            });
            and(env, prop, |env| simplify_val(ty_sub.clone(), env))
        }
        Ty_::Tunion(ty_subs) => common::simplify_union_l(
            &subtype_env,
            this_ty,
            mk_prop,
            |env: &Env, ty: Ty| {
                env::update_reason(env, ty, |r_sub_prj| {
                    reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                })
            },
            (sub_supportdyn.clone(), ty_subs),
            rhs,
            env,
        ),
        Ty_::Tnewtype(name_sub, tyl, _) => {
            let ty_newtype = t_utils::get_newtype_super(env, r_sub.clone(), name_sub, tyl);
            common::simplify_newtype_l(
                &subtype_env,
                this_ty,
                simplify_,
                (
                    sub_supportdyn.clone(),
                    r_sub.clone(),
                    name_sub.clone(),
                    ty_newtype,
                ),
                rhs,
                env,
            )
        }
        Ty_::Tdependent(dep_ty, ty_inner) => common::simplify_dependent_l(
            &subtype_env,
            this_ty,
            simplify_,
            (
                sub_supportdyn.clone(),
                r_sub.clone(),
                dep_ty.clone(),
                ty_inner.clone(),
            ),
            rhs,
            env,
        ),
        _ => invalid(fail, env),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_n_() {
        let l: Vec<Ty> = (0..3).map(|_| make_type::int(reason::none())).collect();
        // `Some (tyl', _ :: tyl'')` matches only when the index is in range.
        assert!(matches!(split_n(&l, 1), ([_], [_, _])));
        assert!(matches!(split_n(&l, 3), ([_, _, _], [])));
        assert!(matches!(split_n(&l, -2), ([], [_, _, _])));
    }
}
