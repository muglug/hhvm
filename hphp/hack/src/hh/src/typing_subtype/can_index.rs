// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 8126-8855): module `Can_index`.
//! See `hh/PORTING.md`.
//!
//! - `type with_hint = { env; prop; likely }` is [`WithHint`] without its
//!   `env` field: the environment is `&mut Env`, updated in place, so a
//!   function that returns a `with_hint` returns `{ prop; likely }` and leaves
//!   the environment of the record in `*env`. `with_hint (env, prop) likely`
//!   is `with_hint(prop, likely)`, and `with_hint_and r f` (which threads
//!   `r.env`) is `with_hint_and(env, r, f)`.
//! - `simplify_` returns a [`WithHint`]; `simplify` has the signature of every
//!   constraint handler (see `prelude.rs`).
//! - The local functions of `simplify_` that use the environment it has after
//!   `expand_type_and_narrow` without taking it as an argument (`do_tuple`,
//!   `do_tuple_general`, `do_shape`) take it as their last parameter here;
//!   where the OCaml calls them with an environment other than the one in
//!   scope, the environment is restored first (see the case of
//!   `Shape_splat`).
//! - `Common.simplify_newtype_l` and `Common.simplify_dependent_l` are
//!   polymorphic in the result of `~mk_prop`: here they get `simplify_`, which
//!   returns a [`WithHint`].

use std::collections::VecDeque;

use naming_special_names_rust as sn;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::s_set::SSet;

use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::tast;
use crate::typechecker_options;
use crate::typing_array_access_util;
use crate::typing_corners;
use crate::typing_defs_constraints::CanIndex;
use crate::typing_defs_constraints::CiAccessKind;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_dynamic_utils;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::reasons_callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_intersection;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_set;
use crate::typing_shapes;
use crate::typing_solver;
use crate::typing_structure;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
use crate::typing_union;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// `type rhs = { reason_super: Reason.t; can_index: can_index }`
#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub can_index: CanIndex,
}

// We need to handle intersection type with special care.
// In particular, indexing an /\C... should return /\V... where V is the result of indexing C that succeed.
// Lets look at three examples:
// Indexing KeyedContainer<arraykey, nonnull> & Vector[?int] should return nonnull & ?int - the intersection of both type.
// Indexing dynamic & nonnull, should return the index type of dynamic only (which is a dynamic), because only dynamic is indexable.
// Indexing mixed & nonnull should be an error, because both type is not indexable.
//
// As you can see, we need to behave differently depending on whether a type is indexable or not.
// However, as we are in subtyping world, we cannot invoke Subtype_ask to determine indexability anymore.
// So, we make a guess with the below with_hint type.
//
// There are multiple cases:
// - If there are errors for whatever reason, it is likely unsolvable.
// - If it is a container/tuple/shape/etc, without any obvious error (arity missmatch, index out of bound), it is likely solvable
// - If the type is complex (union type/intersection type/type variable/etc), recurse to find out
// - If it is a unexpandable variable, it is likely unsolvable.
// -- The above rules could go both way.

/// `type with_hint = { env; prop; likely }`, the environment being `&mut Env`
/// (see the module documentation).
#[derive(Clone, Debug)]
pub(crate) struct WithHint {
    pub prop: tl::SubtypeProp,
    /// A guess whether this simplification is good or not. we will be using this to guide the solving of intersection
    pub likely: bool,
}

/// `with_hint (env, prop) likely`
pub(crate) fn with_hint(prop: tl::SubtypeProp, likely: bool) -> WithHint {
    WithHint { prop, likely }
}

/// `likely_solvable (env, prop)`
pub(crate) fn likely_solvable(prop: tl::SubtypeProp) -> WithHint {
    with_hint(prop, true)
}

/// `likely_unsolvable (env, prop)`
pub(crate) fn likely_unsolvable(prop: tl::SubtypeProp) -> WithHint {
    with_hint(prop, false)
}

/// `un_with_hint { env; prop; _ }`: the proposition (the environment is
/// already in `*env`).
pub(crate) fn un_with_hint(WithHint { prop, .. }: WithHint) -> tl::SubtypeProp {
    prop
}

/// `with_hint_and { env; prop = p1; likely = l1 } f`: `f` is called with the
/// environment of the record, which is `*env`.
pub(crate) fn with_hint_and(
    env: &mut Env,
    WithHint {
        prop: p1,
        likely: l1,
    }: WithHint,
    f: impl FnOnce(&mut Env) -> WithHint,
) -> WithHint {
    match tl::get_error_if_unsat(&p1) {
        Some(ty_err_opt1) => {
            let p2 = un_with_hint(f(env));
            likely_unsolvable(match tl::get_error_if_unsat(&p2) {
                Some(ty_err_opt2) => {
                    let ty_err_opt = typing_error::multiple_opt(
                        vec![ty_err_opt1, ty_err_opt2]
                            .into_iter()
                            .flatten()
                            .collect(),
                    );
                    tl::SubtypeProp::Disj(ty_err_opt, vec![])
                }
                None => p1,
            })
        }
        None => {
            let WithHint {
                prop: p2,
                likely: l2,
            } = f(env);
            with_hint(tl::conj(p1, p2), l1 && l2)
        }
    }
}

/// `List.nth l n` (`None` if `n` is negative or too large).
fn list_nth(l: &[Ty], n: isize) -> Option<&Ty> {
    if n < 0 { None } else { l.get(n as usize) }
}

/// `Reason.to_string` gives the `(Pos_or_decl.t * string) list` that is a
/// `Pos_or_decl.t Message.t list`.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

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
        ConstraintType_::TcanIndex(rhs.can_index.clone()),
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // The arguments are printed in the environment as it is before the
        // continuation runs.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Can_index.simplify",
            &log_env,
            &ty_sub,
            &ty_super,
            || un_with_hint(simplify_(subtype_env, this_ty, lhs, rhs, env)),
        )
    } else {
        un_with_hint(simplify_(subtype_env, this_ty, lhs, rhs, env))
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
    can_index: &CanIndex,
    r_sub: &Reason,
    update_reason: &dyn Fn(&Env, Ty) -> Ty,
    invalid: &dyn Fn(Option<typing_error::T>, &mut Env) -> WithHint,
    return_val: &dyn Fn(Ty, &mut Env) -> WithHint,
    ty_subs: &[Ty],
    tys: Vec<Ty>,
    errs: Vec<Option<typing_error::T>>,
    env: &mut Env,
) -> WithHint {
    match ty_subs {
        [] => match &tys[..] {
            [] => {
                let err = typing_error::intersect_opt(errs.into_iter().flatten().collect());
                invalid(err, env)
            }
            _ => {
                let ty = typing_intersection::intersect_list(env, r_sub.clone(), &tys);
                return_val(ty, env)
            }
        },
        [ty_sub, ty_subs @ ..] => {
            let ty_sub = update_reason(env, ty_sub.clone());
            let val_ty = env::fresh_type(env, can_index.array_pos.clone());
            let WithHint { prop, likely } = simplify_(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: sub_supportdyn.as_ref(),
                    ty_sub: &ty_sub,
                },
                Rhs {
                    reason_super: reason_super.clone(),
                    can_index: CanIndex {
                        val: val_ty.clone(),
                        ..can_index.clone()
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
                        can_index,
                        r_sub,
                        update_reason,
                        invalid,
                        return_val,
                        ty_subs,
                        tys,
                        errs_,
                        env,
                    )
                }
                _ => {
                    if likely {
                        with_hint_and(env, WithHint { prop, likely }, |env| {
                            let mut tys_ = vec![val_ty];
                            tys_.extend(tys);
                            loop_(
                                subtype_env,
                                this_ty,
                                sub_supportdyn,
                                reason_super,
                                can_index,
                                r_sub,
                                update_reason,
                                invalid,
                                return_val,
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
                            can_index,
                            r_sub,
                            update_reason,
                            invalid,
                            return_val,
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
        let mut tyl: VecDeque<Ty> = tyl.into();
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
        sub_supportdyn,
        ty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> WithHint {
    let Rhs {
        reason_super,
        can_index,
    } = rhs.clone();
    // This call to expand_type_and_narrow is not needed for correctness reasons.
    // However, without it, the typechecker will be significantly slower,
    // And cannot complete typechecking in expected time.
    // It will be good to investigate the root cause and remove this code.
    let (ty_err, ty_sub) = typing_solver::expand_type_and_narrow(
        env,
        None,
        None,
        Some(false),
        "an array or collection",
        |env: &mut Env, ty: Ty| {
            typing_array_access_util::widen_for_array_get_ci(&can_index, env, ty)
        },
        can_index.array_pos.clone(),
        ty_sub.clone(),
    );
    if let Some(ty_err) = &ty_err {
        typing_error_utils::add_typing_error(ty_err, env);
    }
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
            ConstraintType_::TcanIndex(can_index.clone()),
        ))),
    );
    let invalid = |fail: Option<typing_error::T>, env: &mut Env| -> WithHint {
        likely_unsolvable(invalid(fail, env))
    };
    let arity_error = |r: &Reason, name: &str, env: &mut Env| -> WithHint {
        invalid(
            Some(typing_error::primary(primary::T::ArrayGetArity {
                pos: can_index.expr_pos.clone(),
                name: name.to_string(),
                decl_pos: reason::to_pos(r),
            })),
            env,
        )
    };
    let mk_prop = simplify;
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
        simplify_default(&subtype_env, can_index.key.clone(), tk, env)
    };
    let simplify_val = |tv: Ty, env: &mut Env| -> tl::SubtypeProp {
        let tv = match &sub_supportdyn {
            None => tv,
            Some(r) => make_type::supportdyn((*r).clone(), tv),
        };
        simplify_default(&subtype_env, tv, can_index.val.clone(), env)
    };
    let return_val = |tv: Ty, env: &mut Env| -> WithHint { likely_solvable(simplify_val(tv, env)) };
    let is_container = |tk: Ty, tv: Ty, env: &mut Env| -> WithHint {
        let prop = simplify_key(tk, env);
        likely_solvable(and(env, prop, |env| simplify_val(tv, env)))
    };
    let is_vec_like = |tv: Ty, env: &mut Env| -> WithHint {
        let tk = make_type::int(reason::idx_vector(can_index.array_pos.clone()));
        is_container(tk, tv, env)
    };
    let is_dict_like = |tv: Ty, env: &mut Env| -> WithHint {
        let tk = make_type::arraykey(reason::idx_dict(can_index.array_pos.clone()));
        is_container(tk, tv, env)
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
    let tuple_oob = |env: &mut Env| -> WithHint {
        invalid(
            Some(typing_error::primary(primary::T::GenericUnify {
                pos: can_index.index_pos.clone(),
                msg: reason::string_of_ureason(&Ureason::URtupleOOB),
            })),
            env,
        )
    };
    // `rest_k i ie_ctx`, where `ie_ctx` puts a node in the place of the one of
    // the index expression.
    let do_tuple =
        |required: &[Ty],
         rest_k: &dyn Fn(isize, &dyn Fn(nast::Expr_) -> nast::Expr, &mut Env) -> WithHint,
         env: &mut Env|
         -> WithHint {
            match &can_index.index_expr {
                nast::Expr(a, b, nast::Expr_::Int(i)) => match int_of_string_opt(i) {
                    None => tuple_oob(env),
                    Some(i) => match list_nth(required, i) {
                        Some(ty) => return_val(ty.clone(), env),
                        None => {
                            let i = i - required.len() as isize;
                            if i >= 0 {
                                rest_k(i, &|c| nast::Expr(a.clone(), b.clone(), c), env)
                            } else {
                                tuple_oob(env)
                            }
                        }
                    },
                },
                _ => invalid(
                    Some(typing_error::primary(primary::T::GenericUnify {
                        pos: can_index.index_pos.clone(),
                        msg: reason::string_of_ureason(&Ureason::URtupleAccess),
                    })),
                    env,
                ),
            }
        };
    let do_tuple_general =
        |required: &[Ty], optional: &[Ty], extra: &TupleExtra, env: &mut Env| -> WithHint {
            do_tuple(
                required,
                &|i, ie_ctx, env| match list_nth(optional, i) {
                    Some(ty) => {
                        if match can_index.access_kind {
                            CiAccessKind::CiLhsOfNullCoalesce
                            | CiAccessKind::CiDestructureOptional => true,
                            CiAccessKind::CiNormal => false,
                        } {
                            return_val(ty.clone(), env)
                        } else {
                            tuple_oob(env)
                        }
                    }
                    None => {
                        let i = i - optional.len() as isize;
                        match extra {
                            TupleExtra::Tvariadic(ty) => {
                                if i >= 0
                                    && (!t_utils::is_nothing(env, ty))
                                    && match can_index.access_kind {
                                        CiAccessKind::CiLhsOfNullCoalesce
                                        | CiAccessKind::CiDestructureOptional => true,
                                        CiAccessKind::CiNormal => false,
                                    }
                                {
                                    return_val(ty.clone(), env)
                                } else {
                                    tuple_oob(env)
                                }
                            }
                            TupleExtra::Tsplat(ty) => simplify_(
                                &subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn: sub_supportdyn.clone(),
                                    ty_sub: &ty,
                                },
                                Rhs {
                                    reason_super: reason_super.clone(),
                                    can_index: CanIndex {
                                        index_expr: ie_ctx(nast::Expr_::Int(i.to_string())),
                                        ..can_index.clone()
                                    },
                                },
                                env,
                            ),
                        }
                    }
                },
                env,
            )
        };
    let do_tuple_basic = |tup: &[Ty], env: &mut Env| -> WithHint {
        do_tuple_general(
            tup,
            &[],
            &TupleExtra::Tvariadic(make_type::nothing(reason::none())),
            env,
        )
    };
    let do_shape = |r_sub: &Reason,
                    ShapeTypeSimple {
                        fields: fdm,
                        origin: s_origin,
                        unknown_value: s_unknown_value,
                    }: &ShapeTypeSimple,
                    env: &mut Env|
     -> WithHint {
        let nast::Expr(_, p, _) = &can_index.index_expr;
        match typing_shapes::tshape_field_name_with_ty_err(env, &can_index.index_expr) {
            Err(ty_err) => invalid(Some(ty_err), env),
            Ok(field) => {
                let field: TshapeFieldName = field;
                if match can_index.access_kind {
                    CiAccessKind::CiLhsOfNullCoalesce => true,
                    CiAccessKind::CiNormal | CiAccessKind::CiDestructureOptional => false,
                } {
                    // The expression $s['x'] ?? $y is semantically equivalent to
                    // Shapes::idx ($s, 'x') ?? $y.  I.e., if $s['x'] occurs on
                    // the left of a coalesce operator, then for type checking it
                    // can be treated as if it evaluated to null instead of
                    // throwing an exception if the field 'x' doesn't exist in $s.
                    let ty = typing_shapes::idx_without_default(
                        env,
                        can_index.expr_pos.clone(),
                        can_index.array_pos.clone(),
                        ty_sub.clone(),
                        field,
                    );
                    return_val(ty, env)
                } else {
                    match fdm.get(&TShapeField(field.clone())) {
                        None => {
                            let decl_pos = match s_origin {
                                TypeOrigin::FromAlias(_, Some(pos)) => pos.clone(),
                                _ => reason::to_pos(r_sub),
                            };
                            // Don't generate an error under dynamic assumptions because we can implicit upcast to dynamic
                            if tast::is_under_dynamic_assumptions(env.checked) {
                                return_val(s_unknown_value.clone(), env)
                            } else {
                                invalid(
                                    Some(typing_error::primary(primary::T::UndefinedField {
                                        pos: p.clone(),
                                        name: t_utils::get_printable_shape_field_name(&field)
                                            .to_string(),
                                        decl_pos,
                                    })),
                                    env,
                                )
                            }
                        }
                        Some(ShapeFieldType {
                            optional: sft_optional,
                            ty: sft_ty,
                        }) => {
                            if *sft_optional
                                && match can_index.access_kind {
                                    CiAccessKind::CiNormal => true,
                                    CiAccessKind::CiLhsOfNullCoalesce
                                    | CiAccessKind::CiDestructureOptional => false,
                                }
                            {
                                // `List.find_exn ~f:(fun x -> TShapeField.equal field x) (TShapeMap.keys fdm)`
                                let declared_field =
                                    match fdm.keys().find(|x| t_shape_field::equal(&field, &x.0)) {
                                        Some(declared_field) => declared_field,
                                        None => panic!("List.find_exn: not found"),
                                    };
                                invalid(
                                    Some(typing_error::primary(
                                        primary::T::ArrayGetWithOptionalField {
                                            recv_pos: can_index.array_pos.clone(),
                                            field_pos: p.clone(),
                                            field_name: t_utils::get_printable_shape_field_name(
                                                &field,
                                            )
                                            .to_string(),
                                            decl_pos: t_shape_field::pos(&declared_field.0),
                                        },
                                    )),
                                    env,
                                )
                            } else {
                                return_val(sft_ty.clone(), env)
                            }
                        }
                    }
                }
            }
        }
    };
    let got_dynamic = |env: &mut Env| -> WithHint {
        let prop = simplify_default(
            &subtype_env,
            make_type::dynamic(reason_super.clone()),
            can_index.val.clone(),
            env,
        );
        likely_solvable(and(env, prop, |env| {
            simplify_default(
                &subtype_env::T {
                    is_dynamic_aware: true,
                    ..subtype_env.clone()
                },
                can_index.key.clone(),
                make_type::dynamic(get_reason(&ty_sub).clone()),
                env,
            )
        }))
    };
    let is_nullable = (match can_index.access_kind {
        CiAccessKind::CiLhsOfNullCoalesce => true,
        CiAccessKind::CiNormal | CiAccessKind::CiDestructureOptional => false,
    }) || tast::is_under_dynamic_assumptions(env.checked);
    let r_sub = get_reason(&ty_sub).clone();
    match get_node(&ty_sub) {
        Ty_::Tvar(_) => likely_unsolvable(mk_issubtype_prop(
            sub_supportdyn.clone(),
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            InternalType::ConstraintType(mk_constraint_type((
                reason_super.clone(),
                ConstraintType_::TcanIndex(can_index.clone()),
            ))),
        )),
        Ty_::Tdynamic(_) => got_dynamic(env),
        Ty_::Tclass((_, cn), _, _)
            if cn == sn::collections::ANY_ARRAY
                && tast::is_under_dynamic_assumptions(env.checked) =>
        {
            got_dynamic(env)
        }
        _ if sub_supportdyn.is_some() && tast::is_under_dynamic_assumptions(env.checked) => {
            got_dynamic(env)
        }
        Ty_::Tclass((_, n), _, targs)
            if n == sn::collections::CONST_MAP
                || n == sn::collections::IMM_MAP
                || n == sn::collections::KEYED_CONTAINER
                || n == sn::collections::ANY_ARRAY =>
        {
            match &targs[..] {
                [_tk, tv] => {
                    let tv = maybe_pessimise_type(env, tv.clone());
                    is_dict_like(tv, env)
                }
                _ => arity_error(&r_sub, n, env),
            }
        }
        Ty_::Tclass((_, n), _, targs)
            if n == sn::collections::MAP || n == sn::collections::MUTABLE_MAP =>
        {
            match &targs[..] {
                [tk, tv] => {
                    let tv = maybe_pessimise_type(env, tv.clone());
                    is_container(tk.clone(), tv, env)
                }
                _ => arity_error(&r_sub, n, env),
            }
        }
        Ty_::Tclass((_, n), _, targs) if n == sn::collections::VEC => match &targs[..] {
            [tv] => is_vec_like(tv.clone(), env),
            _ => arity_error(&r_sub, n, env),
        },
        Ty_::Tclass((_, n), _, targs)
            if n == sn::collections::IMM_VECTOR
                || n == sn::collections::CONST_VECTOR
                || n == sn::collections::VECTOR
                || n == sn::collections::MUTABLE_VECTOR =>
        {
            match &targs[..] {
                [tv] => {
                    let tv = maybe_pessimise_type(env, tv.clone());
                    is_vec_like(tv, env)
                }
                _ => arity_error(&r_sub, n, env),
            }
        }
        // dict and keyset are covariant in the key type, so subsumption
        // lets you upcast the key type beyond ty2 to arraykey.
        Ty_::Tclass((_, n), _, targs) if n == sn::collections::DICT => match &targs[..] {
            [_, tv] => is_dict_like(tv.clone(), env),
            _ => arity_error(&r_sub, n, env),
        },
        Ty_::Tclass((_, n), _, targs) if n == sn::collections::KEYSET => match &targs[..] {
            [tkv] => is_dict_like(tkv.clone(), env),
            _ => arity_error(&r_sub, n, env),
        },
        Ty_::TvecOrDict(_, tv) => {
            let tv = maybe_pessimise_type(env, tv.clone());
            is_dict_like(tv, env)
        }
        Ty_::Tclass((_, n), _, _) if n == C_STRING => {
            let pos = get_pos(&ty_sub);
            let tk = make_type::int(reason::idx_string_from_decl(pos));
            let tv = make_type::string(reason_super.clone());
            let tv = maybe_pessimise_type(env, tv);
            is_container(tk, tv, env)
        }
        Ty_::Tprim(Tprim::Tnull) => {
            let pos = get_pos(&ty_sub);
            if is_nullable {
                return_val(make_type::null(reason::idx_string_from_decl(pos)), env)
            } else {
                let r_sub = r_sub.clone();
                invalid(
                    Some(typing_error::primary(primary::T::NullContainer {
                        pos: can_index.expr_pos.clone(),
                        null_witness: Lazy::new(move || {
                            messages(reason::to_string(
                                "This is what makes me believe it can be `null`",
                                &r_sub,
                            ))
                        }),
                    })),
                    env,
                )
            }
        }
        Ty_::Toption(t) => {
            if is_nullable {
                simplify_(
                    &subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: sub_supportdyn.clone(),
                        ty_sub: &t,
                    },
                    rhs,
                    env,
                )
            } else {
                let r_sub = r_sub.clone();
                invalid(
                    Some(typing_error::primary(primary::T::NullContainer {
                        pos: can_index.expr_pos.clone(),
                        null_witness: Lazy::new(move || {
                            messages(reason::to_string(
                                "This is what makes me believe it can be `null`",
                                &r_sub,
                            ))
                        }),
                    })),
                    env,
                )
            }
        }
        Ty_::Tunion(ty_subs) => {
            let simplify_union_l = |subtype_env: &subtype_env::T,
                                    this_ty: Option<&Ty>,
                                    update_reason: &dyn Fn(&Env, Ty) -> Ty,
                                    (sub_supportdyn, ty_subs): (Option<Reason>, Vec<Ty>),
                                    rhs: Rhs,
                                    env: &mut Env|
             -> WithHint {
                let f = |env: &mut Env, res: WithHint, ty_sub: Ty| -> WithHint {
                    let ty_sub = update_reason(env, ty_sub);
                    with_hint_and(env, res, |env| {
                        simplify_(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn: sub_supportdyn.as_ref(),
                                ty_sub: &ty_sub,
                            },
                            rhs.clone(),
                            env,
                        )
                    })
                };
                // Prioritize types that aren't dynamic or intersections with dynamic
                // to get better error messages
                let (last_tyl, first_tyl) = typing_dynamic_utils::partition_union(
                    &common::contains_dynamic_through_intersection,
                    env,
                    &ty_subs,
                );
                let mut init = likely_solvable(valid(env));
                for ty_sub in first_tyl {
                    init = f(env, init, ty_sub);
                }
                let mut res = init;
                for ty_sub in last_tyl {
                    res = f(env, res, ty_sub);
                }
                res
            };
            simplify_union_l(
                &subtype_env,
                this_ty,
                &|env: &Env, ty: Ty| {
                    env::update_reason(env, ty, |r_sub_prj| {
                        reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                    })
                },
                (sub_supportdyn.cloned(), ty_subs.clone()),
                rhs,
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
                                        can_index,
                                    }: Rhs| {
                        mk_constraint_type((reason_super, ConstraintType_::TcanIndex(can_index)))
                    };
                    let lhs = (sub_supportdyn, &ty_sub);
                    let rhs_subtype = subtype::Rhs {
                        super_supportdyn: false,
                        super_like: false,
                        ty_super: &non_ty,
                    };
                    let rhs_can_index = Rhs {
                        reason_super: reason_super.clone(),
                        can_index: can_index.clone(),
                    };
                    let rhs = (reason_super.clone(), rhs_subtype, rhs_can_index);
                    likely_solvable(common::simplify_disj_r(
                        &subtype_env,
                        this_ty,
                        fail,
                        mk_prop,
                        lift_rhs,
                        lhs,
                        rhs,
                        env,
                    ))
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
                        &can_index,
                        &r_sub,
                        &update_reason,
                        &invalid,
                        &return_val,
                        ty_subs,
                        vec![],
                        vec![],
                        env,
                    )
                }
            }
        }
        Ty_::Tclass((_, id), _, tup) if id == sn::collections::PAIR => do_tuple_basic(tup, env),
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => do_tuple_general(t_required, t_optional, t_extra, env),
        Ty_::Tshape(ShapeType::ShapeSimple(ts)) => do_shape(&r_sub, ts, env),
        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
            // For field access on Shape_splat, merge all elements using rightmost-wins
            // (expand tvars, recurse nested splats, resolve generics via bounds). A
            // distributed union operand yields a union type here: re-dispatch so the
            // [Tunion] arm above reads each member (a single shape).
            //
            // `do_shape` goes on with the environment it closes over (the one
            // from before `resolve_for_read`), the recursive call with the one
            // `resolve_for_read` returns.
            let env_do_shape = env.clone();
            let result = typing_corners::resolve_for_read(env, r_sub.clone(), ss_elems);
            match result {
                Err(missing) => {
                    let subtype_env = subtype_env::map_on_error(subtype_env.clone(), |on_error| {
                        let position =
                            typing_corners::missing_assignment::position(&missing).clone();
                        reasons_callback::prepend_reason(
                            on_error,
                            Lazy::new(move || {
                                Message(
                                    position,
                                    "Shape-splat dependency analysis failed before projection"
                                        .into(),
                                )
                            }),
                        )
                    });
                    let fail = subtype_env::fail(
                        &subtype_env,
                        InternalType::LoclType(ty_sub.clone()),
                        InternalType::ConstraintType(mk_constraint_type((
                            reason_super.clone(),
                            ConstraintType_::TcanIndex(can_index.clone()),
                        ))),
                    );
                    invalid(fail, env)
                }
                Ok(read_ty) => match get_node(&read_ty) {
                    Ty_::Tshape(ShapeType::ShapeSimple(ts)) => {
                        *env = env_do_shape;
                        do_shape(&r_sub, ts, env)
                    }
                    _ => simplify_(
                        &subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: sub_supportdyn.clone(),
                            ty_sub: &read_ty,
                        },
                        rhs,
                        env,
                    ),
                },
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
        Ty_::Tnewtype(name_sub, tyl, _)
            if tyl.len() == 1 && name_sub == sn::classes::SUPPORT_DYN =>
        {
            let ty_sub = tyl[0].clone();
            simplify_(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: Some(&r_sub),
                    ty_sub: &ty_sub,
                },
                rhs,
                env,
            )
        }
        Ty_::Tnewtype(name_sub, tyl, _) if tyl.len() == 1 && name_sub == sn::fb::TYPE_STRUCTURE => {
            let ty = tyl[0].clone();
            let ty_newtype =
                t_utils::get_newtype_super(env, r_sub.clone(), name_sub, std::slice::from_ref(&ty));
            match get_node(&ty_newtype) {
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: shape_kind,
                    fields,
                })) => {
                    let r = get_reason(&ty_newtype).clone();
                    let fields = typing_structure::transform_shapemap(
                        None,
                        env,
                        can_index.array_pos.clone(),
                        ty.clone(),
                        fields.clone(),
                    );
                    let ty = mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: shape_kind.clone(),
                            fields,
                        })),
                    ));
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
                _ => common::simplify_newtype_l(
                    &subtype_env,
                    this_ty,
                    simplify_,
                    (
                        sub_supportdyn.clone(),
                        r_sub.clone(),
                        name_sub.clone(),
                        ty_newtype.clone(),
                    ),
                    rhs,
                    env,
                ),
            }
        }
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
        Ty_::Tany(_) => return_val(ty_sub.clone(), env),
        _ => invalid(fail, env),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_nth_() {
        let l = vec![
            make_type::int(reason::none()),
            make_type::null(reason::none()),
        ];
        assert!(list_nth(&l, -1).is_none());
        assert!(matches!(
            list_nth(&l, 1).map(get_node),
            Some(Ty_::Tprim(Tprim::Tnull))
        ));
        assert!(list_nth(&l, 2).is_none());
    }

    fn sub(n: isize) -> tl::SubtypeProp {
        tl::SubtypeProp::IsSubtype(
            false,
            InternalType::LoclType(mk((reason::none(), Ty_::Tvar(n)))),
            InternalType::LoclType(make_type::int(reason::none())),
        )
    }

    fn err() -> typing_error::T {
        typing_error::T::Multiple(vec![])
    }

    fn env() -> Env {
        use std::path::Path;
        use std::sync::Arc;

        use relative_path::Prefix;
        use relative_path::RelativePath;
        let ctx = crate::ctx::Ctx::new(Path::new("/"), Default::default()).unwrap();
        let file = Arc::new(RelativePath::make(Prefix::Root, "f.php".into()));
        crate::typing_env_types::empty(None, None, Arc::new(ctx), file, None)
    }

    #[test]
    fn with_hint_and_() {
        let mut env = env();
        // Satisfiable: the conjunction, likely if both are.
        let r = with_hint_and(&mut env, likely_solvable(sub(1)), |_| {
            likely_unsolvable(sub(2))
        });
        assert!(matches!(r.prop, tl::SubtypeProp::Conj(ref ps) if ps.len() == 2));
        assert!(!r.likely);
        let r = with_hint_and(&mut env, likely_solvable(sub(1)), |_| {
            likely_solvable(sub(2))
        });
        assert!(r.likely);
        // Unsatisfiable: unlikely, whatever the continuation says.
        let r = with_hint_and(&mut env, likely_solvable(tl::invalid(Some(err()))), |_| {
            likely_solvable(sub(2))
        });
        assert!(!r.likely);
        assert!(matches!(
            tl::get_error_if_unsat(&r.prop),
            Some(Some(typing_error::T::Multiple(_)))
        ));
        // Both unsatisfiable: both errors.
        let r = with_hint_and(&mut env, likely_solvable(tl::invalid(Some(err()))), |_| {
            likely_solvable(tl::invalid(Some(err())))
        });
        assert!(matches!(
            tl::get_error_if_unsat(&r.prop),
            Some(Some(typing_error::T::Multiple(ref es))) if es.len() == 2
        ));
    }
}
