// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing_subtype.ml` (lines 7659-8124): module `Destructure`.
//! See `hh/PORTING.md`.
//!
//! - `simplify` has the signature of every constraint handler (see
//!   `prelude.rs`); the other functions take `~subtype_env` as
//!   `&subtype_env::T`, `~this_ty` as `Option<&Ty>`, their tuple argument by
//!   value and the [`Rhs`] by value, with the environment last, as in OCaml.
//! - A chain `a &&& fun env -> b &&& fun env -> c` nests to the right (the
//!   `fun` extends as far as it can): it is `and(env, a, |env| { ..
//!   and(env, b, |env| c) })`, which groups the errors of `b` and `c` before
//!   those of `a`.
//! - `Common`'s functions get `simplify` itself as `~mk_prop`.

use naming_special_names_rust as sn;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::pos_or_decl;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::Destructure;
use crate::typing_defs_constraints::DestructureKind;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

/// `type rhs = { reason_super: Reason.t; destructure: destructure }`
#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub destructure: Destructure,
}

/// `List.split_n l n`: the first `n` elements and the rest (all of `l` and
/// nothing if `n` is larger than its length, nothing and all of `l` if `n` is
/// negative).
fn split_n(l: &[Ty], n: isize) -> (&[Ty], &[Ty]) {
    let n = n.clamp(0, l.len() as isize) as usize;
    l.split_at(n)
}

/// The length check of `List.fold2_exn`, which raises before folding.
fn check_length2_exn(l1: &[Ty], l2: &[Ty]) {
    if l1.len() != l2.len() {
        panic!("length mismatch in fold2_exn: {} <> {}", l1.len(), l2.len())
    }
}

pub(crate) fn destructure_array(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    (sub_supportdyn, ty_sub_inner): (Option<Reason>, Ty),
    Rhs {
        reason_super: r_super,
        destructure:
            Destructure {
                kind: d_kind,
                required: d_required,
                optional: d_optional,
                variadic: d_variadic,
            },
    }: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // If this is a splat, there must be a variadic box to receive the elements
    // but for list(...) destructuring this is not required. Example:
    //
    // function f(int $i): void {}
    // function g(vec<int> $v): void {
    //   list($a) = $v; // ok (but may throw)
    //   f(...$v); // error
    // }
    let fpos = match reason::predicates::unpack_unpack_param_opt(&r_super) {
        Some((_, fpos, _)) => fpos,
        None => reason::to_pos(&r_super),
    };
    match (d_kind, &d_required[..], &d_variadic) {
        (DestructureKind::SplatUnpack, [_, ..], _) => {
            // return the env so as not to discard the type variable that might
            // have been created for the Traversable type created below.
            invalid(
                subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::UnpackArrayRequiredArgument {
                            pos: reason::to_pos(&r_super),
                            decl_pos: fpos,
                        },
                        on_error,
                    )
                }),
                env,
            )
        }
        (DestructureKind::SplatUnpack, [], None) => invalid(
            subtype_env.on_error.clone().map(|on_error| {
                typing_error::apply_reasons(
                    secondary::T::UnpackArrayVariadicArgument {
                        pos: reason::to_pos(&r_super),
                        decl_pos: fpos,
                    },
                    on_error,
                )
            }),
            env,
        ),
        (DestructureKind::SplatUnpack, [], Some(_)) | (DestructureKind::ListDestructure, _, _) => {
            let mut res = valid(env);
            for ty_dest in &d_required {
                res = and(env, res, |env| {
                    subtype::simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: sub_supportdyn.as_ref(),
                            ty_sub: &ty_sub_inner,
                        },
                        subtype::Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_dest,
                        },
                        env,
                    )
                });
            }
            and(env, res, |env| {
                let mut res = valid(env);
                for ty_dest in &d_optional {
                    res = and(env, res, |env| {
                        subtype::simplify(
                            subtype_env,
                            this_ty,
                            Lhs {
                                sub_supportdyn: sub_supportdyn.as_ref(),
                                ty_sub: &ty_sub_inner,
                            },
                            subtype::Rhs {
                                super_like: false,
                                super_supportdyn: false,
                                ty_super: &ty_dest,
                            },
                            env,
                        )
                    });
                }
                and(env, res, |env| match &d_variadic {
                    None => valid(env),
                    Some(vty) => subtype::simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: sub_supportdyn.as_ref(),
                            ty_sub: &ty_sub_inner,
                        },
                        subtype::Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &vty,
                        },
                        env,
                    ),
                })
            })
        }
    }
}

pub(crate) fn destructure_dynamic(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    (sub_supportdyn, ty_sub): (Option<Reason>, Ty),
    Rhs {
        destructure:
            Destructure {
                required: d_required,
                optional: d_optional,
                variadic: d_variadic,
                ..
            },
        ..
    }: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let mut res = valid(env);
    for ty_dest in &d_required {
        res = and(env, res, |env| {
            subtype::simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: sub_supportdyn.as_ref(),
                    ty_sub: &ty_sub,
                },
                subtype::Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &ty_dest,
                },
                env,
            )
        });
    }
    and(env, res, |env| {
        let mut res = valid(env);
        for ty_dest in &d_optional {
            res = and(env, res, |env| {
                subtype::simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: sub_supportdyn.as_ref(),
                        ty_sub: &ty_sub,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_dest,
                    },
                    env,
                )
            });
        }
        and(env, res, |env| match &d_variadic {
            None => valid(env),
            Some(vty) => subtype::simplify(
                subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: sub_supportdyn.as_ref(),
                    ty_sub: &ty_sub,
                },
                subtype::Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &vty,
                },
                env,
            ),
        })
    })
}

/// `arity_error` returns the environment that `destructure_tuple` was called
/// with (the OCaml closes over it): in the case of too many elements, which
/// is reached after the required and optional elements have been
/// simplified, the environment those simplifications leave is dropped.
pub(crate) fn destructure_tuple(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    (sub_supportdyn, reason_tuple, ty_subs): (Option<Reason>, Reason, Vec<Ty>),
    Rhs {
        reason_super: r_super,
        destructure:
            Destructure {
                required: d_required,
                optional: d_optional,
                variadic: d_variadic,
                ..
            },
    }: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // First fill the required elements. If there are insufficient elements, an error is reported.
    // Fill as many of the optional elements as possible, and the remainder are unioned into the
    // variadic element. Example:
    //
    // (float, bool, string, int) <: Tdestructure(#1, opt#2, ...#3) =>
    // float <: #1 /\ bool <: #2 /\ string <: #3 /\ int <: #3
    //
    // (float, bool) <: Tdestructure(#1, #2, opt#3) =>
    // float <: #1 /\ bool <: #2
    let len_ts = ty_subs.len() as isize;
    let len_required = d_required.len() as isize;
    let env0 = env.clone();
    let arity_error = |env: &mut Env,
                       f: &dyn Fn(
        isize,
        isize,
        PosOrDecl,
        PosOrDecl,
        Option<reasons_callback::T>,
    ) -> Option<typing_error::T>| {
        let (epos, fpos, prefix) = match reason::predicates::unpack_unpack_param_opt(&r_super) {
            Some((epos, fpos, c)) => (pos_or_decl::of_raw_pos(epos), fpos, c),
            None => (reason::to_pos(&r_super), reason::to_pos(&reason_tuple), 0),
        };
        *env = env0.clone();
        invalid(
            f(
                prefix + len_required,
                prefix + len_ts,
                epos,
                fpos,
                subtype_env.on_error.clone(),
            ),
            env,
        )
    };
    if len_ts < len_required {
        arity_error(env, &|expected, actual, pos, decl_pos, on_error_opt| {
            on_error_opt.map(|on_error| {
                let base_err = secondary::T::TypingTooFewArgs {
                    pos,
                    decl_pos,
                    expected,
                    actual,
                };
                typing_error::apply_reasons(base_err, on_error)
            })
        })
    } else {
        let len_optional = d_optional.len() as isize;
        let (ts_required, remain) = split_n(&ty_subs, len_required);
        let (ts_optional, ts_variadic) = split_n(remain, len_optional);
        // `List.fold2_exn ts_required d_required ~init:((env, TL.valid), 0)`
        check_length2_exn(ts_required, &d_required);
        let mut res = valid(env);
        let mut n: isize = 0;
        for (ty_from, ty_into) in ts_required.iter().zip(d_required.iter()) {
            let ty_from = env::update_reason(env, ty_from.clone(), |sub_prj| {
                reason::prj_tuple(reason_tuple.clone(), sub_prj, r_super.clone(), n)
            });
            res = and(env, res, |env| {
                subtype::simplify(
                    subtype_env,
                    this_ty,
                    Lhs {
                        sub_supportdyn: sub_supportdyn.as_ref(),
                        ty_sub: &ty_from,
                    },
                    subtype::Rhs {
                        super_like: false,
                        super_supportdyn: false,
                        ty_super: &ty_into,
                    },
                    env,
                )
            });
            n += 1;
        }

        and(env, res, |env| {
            let len_ts_opt = ts_optional.len() as isize;
            let d_optional_part = if len_ts_opt < len_optional {
                // `List.take d_optional len_ts_opt`
                &d_optional[..len_ts_opt as usize]
            } else {
                &d_optional[..]
            };
            // `List.fold2_exn ts_optional d_optional_part ~init:((env, TL.valid), n)`
            check_length2_exn(ts_optional, d_optional_part);
            let mut res = valid(env);
            let mut n = n;
            for (ty_from, ty_into) in ts_optional.iter().zip(d_optional_part.iter()) {
                let ty_from = env::update_reason(env, ty_from.clone(), |sub_prj| {
                    reason::prj_tuple(reason_tuple.clone(), sub_prj, r_super.clone(), n)
                });
                res = and(env, res, |env| {
                    subtype::simplify(
                        subtype_env,
                        this_ty,
                        Lhs {
                            sub_supportdyn: sub_supportdyn.as_ref(),
                            ty_sub: &ty_from,
                        },
                        subtype::Rhs {
                            super_like: false,
                            super_supportdyn: false,
                            ty_super: &ty_into,
                        },
                        env,
                    )
                });
                n += 1;
            }

            and(env, res, |env| match (ts_variadic, &d_variadic) {
                (vars, Some(ty_into)) => {
                    let mut res = valid(env);
                    for ty_from in vars {
                        let ty_from = env::update_reason(env, ty_from.clone(), |sub_prj| {
                            reason::prj_tuple(
                                reason_tuple.clone(),
                                sub_prj,
                                r_super.clone(),
                                // TODO(mjt) allow different indices here
                                n + 1,
                            )
                        });
                        res = and(env, res, |env| {
                            subtype::simplify(
                                subtype_env,
                                this_ty,
                                Lhs {
                                    sub_supportdyn: sub_supportdyn.as_ref(),
                                    ty_sub: &ty_from,
                                },
                                subtype::Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &ty_into,
                                },
                                env,
                            )
                        });
                    }
                    res
                }
                ([], None) => valid(env),
                (_, None) => {
                    // Elements remain but we have nowhere to put them
                    arity_error(env, &|expected, actual, pos, decl_pos, on_error_opt| {
                        on_error_opt.map(|on_error| {
                            typing_error::apply_reasons(
                                secondary::T::TypingTooManyArgs {
                                    pos,
                                    decl_pos,
                                    expected,
                                    actual,
                                },
                                on_error,
                            )
                        })
                    })
                }
            })
        })
    }
}

pub fn simplify(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    Lhs {
        sub_supportdyn,
        ty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Rhs {
        reason_super: r_super,
        destructure,
    } = rhs.clone();
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let subtype_env = subtype_env::possibly_add_violated_constraint(
        subtype_env.clone(),
        get_reason(&ty_sub).clone(),
        r_super.clone(),
    );
    let fail = subtype_env::fail(
        &subtype_env,
        InternalType::LoclType(ty_sub.clone()),
        InternalType::ConstraintType(mk_constraint_type((
            r_super.clone(),
            ConstraintType_::Tdestructure(destructure.clone()),
        ))),
    );
    match (get_node(&ty_sub), destructure.kind) {
        // TODO optional and variadic components T201398626 T201398652
        (
            Ty_::Ttuple(TupleType {
                required: t_required,
                ..
            }),
            _,
        ) => {
            let r = get_reason(&ty_sub).clone();
            destructure_tuple(
                &subtype_env,
                this_ty,
                (sub_supportdyn.cloned(), r, t_required.clone()),
                rhs,
                env,
            )
        }
        (Ty_::Tclass((_, x), _, tyl), _) if x == sn::collections::PAIR => {
            let r = get_reason(&ty_sub).clone();
            destructure_tuple(
                &subtype_env,
                this_ty,
                (sub_supportdyn.cloned(), r, tyl.clone()),
                rhs,
                env,
            )
        }
        (Ty_::Tclass((_, x), _, tyl), _)
            if tyl.len() == 1
                && (x == sn::collections::VECTOR
                    || x == sn::collections::IMM_VECTOR
                    || x == sn::collections::VEC
                    || x == sn::collections::CONST_VECTOR) =>
        {
            let elt_type = tyl[0].clone();
            destructure_array(&subtype_env, this_ty, (sub_supportdyn.cloned(), elt_type), rhs, env)
        }
        (Ty_::Tdynamic(_), _) => destructure_dynamic(
            &subtype_env,
            this_ty,
            (sub_supportdyn.cloned(), ty_sub.clone()),
            rhs,
            env,
        ),
        (Ty_::Tvar(_), _) => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            InternalType::ConstraintType(mk_constraint_type((
                r_super,
                ConstraintType_::Tdestructure(destructure),
            ))),
        ),
        (Ty_::Tunion(ty_subs), _) => {
            let r_sub = get_reason(&ty_sub).clone();
            common::simplify_union_l(
                &subtype_env,
                this_ty,
                simplify,
                |env: &Env, ty: Ty| {
                    env::update_reason(env, ty, |r_sub_prj| {
                        reason::prj_union_sub(r_sub.clone(), r_sub_prj)
                    })
                },
                (sub_supportdyn, ty_subs),
                rhs,
                env,
            )
        }
        (Ty_::Tintersection(ty_subs), _) => {
            let r_sub = get_reason(&ty_sub).clone();
            // A & B <: C iif A <: C | !B
            //
            // The second case does not bind the environment that
            // `find_type_with_exact_negation` returns: it goes on with the
            // one from before.
            match subtype_negation::find_type_with_exact_negation_opt(env, ty_subs) {
                Some((non_ty, tyl)) => {
                    let ty_sub = make_type::intersection(r_sub, tyl);
                    let mk_prop = simplify;
                    let lift_rhs = |Rhs {
                                        reason_super,
                                        destructure,
                                    }: Rhs| {
                        mk_constraint_type((
                            reason_super,
                            ConstraintType_::Tdestructure(destructure),
                        ))
                    };
                    let lhs = (sub_supportdyn, &ty_sub);
                    let rhs_subtype = subtype::Rhs {
                        super_supportdyn: false,
                        super_like: false,
                        ty_super: &non_ty,
                    };
                    let rhs_destructure = Rhs {
                        reason_super: r_super.clone(),
                        destructure,
                    };
                    let rhs = (r_super, rhs_subtype, rhs_destructure);
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
                    common::simplify_intersection_l(
                        &subtype_env,
                        this_ty,
                        fail.into(),
                        simplify,
                        |env: &Env, ty: Ty| {
                            env::update_reason(env, ty, |r_sub_prj| {
                                reason::prj_inter_sub(r_sub.clone(), r_sub_prj)
                            })
                        },
                        (sub_supportdyn, ty_subs),
                        rhs,
                        env,
                    )
                }
            }
        }
        (Ty_::Tgeneric(generic_nm), _) => {
            let r_generic = get_reason(&ty_sub).clone();
            common::simplify_generic_l(
                &subtype_env,
                this_ty,
                fail.into(),
                simplify,
                (sub_supportdyn, r_generic, generic_nm.clone()),
                rhs.clone(),
                rhs,
                env,
            )
        }
        (_, DestructureKind::SplatUnpack) => {
            // Allow splatting of arbitrary Traversables
            let ty_inner = env::fresh_type(env, Pos::NONE);
            let traversable = make_type::traversable(r_super, ty_inner.clone());
            let prop = subtype::simplify(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &ty_sub,
                },
                subtype::Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &traversable,
                },
                env,
            );
            and(env, prop, |env| {
                destructure_array(&subtype_env, this_ty, (None, ty_inner), rhs, env)
            })
        }
        (Ty_::Tnewtype(nm, tyl, _), DestructureKind::ListDestructure) => {
            let r_newtype = get_reason(&ty_sub).clone();
            let ty_newtype = t_utils::get_newtype_super(env, r_newtype.clone(), nm, tyl);
            common::simplify_newtype_l(
                &subtype_env,
                this_ty,
                simplify,
                (sub_supportdyn, r_newtype, nm.clone(), ty_newtype),
                rhs,
                env,
            )
        }
        (Ty_::Tdependent(dep_ty, ty_inner_sub), DestructureKind::ListDestructure) => {
            let r_dep = get_reason(&ty_sub).clone();
            common::simplify_dependent_l(
                &subtype_env,
                this_ty,
                simplify,
                (sub_supportdyn, r_dep, dep_ty.clone(), ty_inner_sub.clone()),
                rhs,
                env,
            )
        }
        (
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Toption(_)
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Tshape(_)
            | Ty_::TvecOrDict(_, _)
            | Ty_::Taccess(_)
            | Ty_::Tclass(_, _, _)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_)
            | Ty_::TclassPtr(_),
            DestructureKind::ListDestructure,
        ) => {
            let ty_sub_descr = {
                let env = env.clone();
                let ty_sub = ty_sub.clone();
                Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty_sub))
            };
            invalid(
                subtype_env.on_error.clone().map(|on_error| {
                    typing_error::apply_reasons(
                        secondary::T::InvalidDestructure {
                            pos: reason::to_pos(&r_super),
                            decl_pos: get_pos(&ty_sub),
                            ty_name: ty_sub_descr,
                        },
                        on_error,
                    )
                }),
                env,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tys(n: usize) -> Vec<Ty> {
        (0..n).map(|_| make_type::int(reason::none())).collect()
    }

    #[test]
    fn split_n_() {
        let l = tys(3);
        assert_eq!(split_n(&l, 0).0.len(), 0);
        assert_eq!(split_n(&l, 2).0.len(), 2);
        assert_eq!(split_n(&l, 2).1.len(), 1);
        assert_eq!(split_n(&l, 5).0.len(), 3);
        assert_eq!(split_n(&l, 5).1.len(), 0);
        assert_eq!(split_n(&l, -1).0.len(), 0);
        assert_eq!(split_n(&l, -1).1.len(), 3);
    }

    #[test]
    #[should_panic(expected = "length mismatch in fold2_exn: 1 <> 2")]
    fn check_length2_exn_() {
        check_length2_exn(&tys(2), &tys(2));
        check_length2_exn(&tys(1), &tys(2));
    }
}
