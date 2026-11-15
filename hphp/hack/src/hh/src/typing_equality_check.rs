// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_equality_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Bop;
use oxidized::ast_defs::Tprim;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::aast_defs;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::is_arraykey;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
use crate::typing_print;
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_tdef_locl;
use crate::typing_utils;
use crate::typing_warning;
use crate::typing_warning_utils;

/// `SN.Classes.cString` (`naming_special_names_rust` has it as
/// `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// `Reason.to_string` gives the `(Pos_or_decl.t * string) list` that is a
/// `Pos_or_decl.t Message.t list`.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

// ---------------------------------------------------------------------------
// Check if a comparison is trivially true or false
// ---------------------------------------------------------------------------

fn trivial_result_str(bop: Bop) -> bool {
    match bop {
        Bop::Eqeqeq => false,
        Bop::Diff2 => true,
        _ => panic!("assert false"),
    }
}

fn trivial_comparison_warning(
    env: &Env,
    pos: Pos,
    bop: Bop,
    ty1: &Ty,
    ty2: &Ty,
    left_trail: Vec<PosOrDecl>,
    right_trail: Vec<PosOrDecl>,
) {
    let result = trivial_result_str(bop);
    fn describe_type<'a>(env: &'a Env, ty: &Ty) -> typing_warning::Lazy<'a, Vec<Message<PosOrDecl>>> {
        let ty = ty.clone();
        typing_warning::Lazy::new(Box::new(move || {
            // `lazy (Typing_print.error env ty)`, mapped
            let ty_string = typing_print::error(None, env, &ty);
            messages(reason::to_string(
                &("This is ".to_string() + &ty_string),
                get_reason(&ty),
            ))
        }))
    }
    let left = describe_type(env, ty1);
    let right = describe_type(env, ty2);
    typing_warning_utils::add(
        env,
        (
            pos,
            typing_warning::Kind::SKETCHY_EQUALITY,
            typing_warning::sketchy_equality::T {
                result,
                left,
                right,
                left_trail,
                right_trail,
            },
        ),
    )
}

fn eq_incompatible_types(env: &Env, p: Pos, ty1: &Ty, ty2: &Ty) {
    let tys1 = {
        let env = env.clone();
        let ty1 = ty1.clone();
        Lazy::new(move || typing_print::error(None, &env, &ty1))
    };
    let tys2 = {
        let env = env.clone();
        let ty2 = ty2.clone();
        Lazy::new(move || typing_print::error(None, &env, &ty2))
    };
    let r1: Reason = get_reason(ty1).clone();
    let r2: Reason = get_reason(ty2).clone();
    typing_error_utils::add_typing_error(
        &typing_error::primary(typing_error::primary::T::EqIncompatibleTypes {
            pos: p,
            left: tys1.map(move |tys1| messages(reason::to_string(&("This is ".to_string() + tys1), &r1))),
            right: tys2.map(move |tys2| messages(reason::to_string(&("This is ".to_string() + tys2), &r2))),
        }),
        env,
    )
}

fn bad_compare_to_enum(ty: &Ty_, enum_bound: &Ty) -> bool {
    match (get_node(enum_bound), ty) {
        (Ty_::Tprim(Tprim::Tint), Ty_::Tprim(Tprim::Tint | Tprim::Tarraykey | Tprim::Tnum)) => {
            false
        }
        (Ty_::Tprim(Tprim::Tint), Ty_::Tprim(_)) => true,
        (Ty_::Tprim(Tprim::Tint), Ty_::Tclass((_, id), _, _)) if C_STRING == id => true,
        (Ty_::Tclass((_, id1), _, _), Ty_::Tclass((_, id2), _, _))
            if C_STRING == id1 && C_STRING == id2 =>
        {
            false
        }
        (Ty_::Tclass((_, id), _, _), Ty_::Tprim(Tprim::Tarraykey)) if C_STRING == id => false,
        (Ty_::Tclass((_, id), _, _), Ty_::Tprim(_)) if C_STRING == id => true,
        (
            Ty_::Tprim(Tprim::Tarraykey),
            Ty_::Tprim(Tprim::Tarraykey | Tprim::Tint | Tprim::Tnum),
        ) => false,
        (Ty_::Tprim(Tprim::Tarraykey), Ty_::Tclass((_, id), _, _)) if C_STRING == id => false,
        (Ty_::Tprim(Tprim::Tarraykey), Ty_::Tprim(_)) => true,
        _ => false,
    }
}

pub fn assert_nontrivial(p: Pos, bop: Bop, env: &Env, ty1: Ty, ty2: Ty) {
    let ety_env = empty_expand_env();
    // The environments that `expand_type` and `force_expand_typedef` return
    // are dropped (and so are the errors of `force_expand_typedef`).
    let ty1 = env::expand_type(&mut env.clone(), ty1);
    let (_, ety1, trail1) =
        typing_tdef_locl::force_expand_typedef(&ety_env, &mut env.clone(), ty1.clone());
    let ty2 = env::expand_type(&mut env.clone(), ty2);
    let (_, ety2, trail2) =
        typing_tdef_locl::force_expand_typedef(&ety_env, &mut env.clone(), ty2.clone());
    match (get_node(&ty1), get_node(&ty2)) {
        // Disallow `===` on distinct abstract enum types.
        // Future: consider putting this in typed lint not type checking
        (Ty_::Tnewtype(e1, tyargs1, _), Ty_::Tnewtype(e2, tyargs2, _))
            if env::is_enum(env, e1) && env::is_enum(env, e2) =>
        {
            let mut env = env.clone();
            let env = &mut env;
            let bound1 =
                typing_utils::get_newtype_super(env, get_reason(&ty1).clone(), e1, tyargs1);
            let bound2 =
                typing_utils::get_newtype_super(env, get_reason(&ty2).clone(), e2, tyargs2);
            if is_arraykey(&bound1) && is_arraykey(&bound2) && !(e1 == e2) {
                if e1 == e2 {
                } else {
                    eq_incompatible_types(env, p, &ety1, &ety2)
                }
            }
        }
        _ => match (
            (get_reason(&ety1), get_node(&ety1)),
            (get_reason(&ety2), get_node(&ety2)),
        ) {
            ((_, Ty_::Tprim(Tprim::Tnum)), (_, Ty_::Tprim(Tprim::Tarraykey)))
            | ((_, Ty_::Tprim(Tprim::Tarraykey)), (_, Ty_::Tprim(Tprim::Tnum))) => {}
            ((_, Ty_::Tprim(Tprim::Tnum)), (_, Ty_::Tprim(Tprim::Tint | Tprim::Tfloat)))
            | ((_, Ty_::Tprim(Tprim::Tint | Tprim::Tfloat)), (_, Ty_::Tprim(Tprim::Tnum))) => {}
            ((_, Ty_::Tprim(Tprim::Tarraykey)), (_, Ty_::Tprim(Tprim::Tint)))
            | ((_, Ty_::Tprim(Tprim::Tint)), (_, Ty_::Tprim(Tprim::Tarraykey))) => {}
            ((_, Ty_::Tprim(Tprim::Tarraykey)), (_, Ty_::Tclass((_, id), _, _)))
            | ((_, Ty_::Tclass((_, id), _, _)), (_, Ty_::Tprim(Tprim::Tarraykey)))
                if C_STRING == id => {}
            ((_, Ty_::Tprim(Tprim::Tnull)), _) | (_, (_, Ty_::Tprim(Tprim::Tnull))) => {}
            ((r, Ty_::Tprim(Tprim::Tnoreturn)), _) | (_, (r, Ty_::Tprim(Tprim::Tnoreturn))) => {
                let r: Reason = (*r).clone();
                typing_error_utils::add_typing_error(
                    &typing_error::wellformedness(
                        typing_error::primary::wellformedness::T::NoreturnUsage {
                            pos: p,
                            reason: Lazy::new(move || {
                                messages(reason::to_string("This always throws or exits", &r))
                            }),
                        },
                    ),
                    env,
                )
            }
            ((r, Ty_::Tprim(Tprim::Tvoid)), _) | (_, (r, Ty_::Tprim(Tprim::Tvoid))) => {
                // Ideally we shouldn't hit this case, but well...
                let r: Reason = (*r).clone();
                typing_error_utils::add_typing_error(
                    &typing_error::wellformedness(
                        typing_error::primary::wellformedness::T::VoidUsage {
                            pos: p,
                            reason: Lazy::new(move || {
                                messages(reason::to_string("This is `void`", &r))
                            }),
                        },
                    ),
                    env,
                )
            }
            ((_, a), (_, Ty_::Tnewtype(e, _, bound)))
                if env::is_enum(env, e) && bad_compare_to_enum(a, bound) =>
            {
                trivial_comparison_warning(env, p, bop, &ty1, bound, trail1, trail2)
            }
            ((_, Ty_::Tnewtype(e, _, bound)), (_, a))
                if env::is_enum(env, e) && bad_compare_to_enum(a, bound) =>
            {
                trivial_comparison_warning(env, p, bop, bound, &ty2, trail1, trail2)
            }
            ((_, Ty_::Tprim(a)), (_, Ty_::Tprim(b))) if !aast_defs::equal_tprim(*a, *b) => {
                trivial_comparison_warning(env, p, bop, &ty1, &ty2, trail1, trail2)
            }
            ((_, Ty_::Toption(ty1)), (_, Ty_::Tprim(_))) => {
                assert_nontrivial(p, bop, env, ty1.clone(), ty2.clone())
            }
            ((_, Ty_::Tprim(_)), (_, Ty_::Toption(ty2))) => {
                assert_nontrivial(p, bop, env, ty1.clone(), ty2.clone())
            }
            ((_, Ty_::Toption(ty1)), (_, Ty_::Toption(ty2))) => {
                assert_nontrivial(p, bop, env, ty1.clone(), ty2.clone())
            }
            ((_, Ty_::Tclass((_, id), _, _)), (_, Ty_::Tprim(_)))
            | ((_, Ty_::Tprim(_)), (_, Ty_::Tclass((_, id), _, _)))
                if C_STRING == id =>
            {
                trivial_comparison_warning(env, p, bop, &ty1, &ty2, trail1, trail2)
            }
            ((_, Ty_::Toption(ty1)), (_, Ty_::Tclass((_, id), _, _))) if C_STRING == id => {
                assert_nontrivial(p, bop, env, ty1.clone(), ty2.clone())
            }
            ((_, Ty_::Tclass((_, id), _, _)), (_, Ty_::Toption(ty2))) if C_STRING == id => {
                assert_nontrivial(p, bop, env, ty1.clone(), ty2.clone())
            }
            (
                (
                    _,
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::TvecOrDict(_, _)
                    | Ty_::Tprim(_)
                    | Ty_::Toption(_)
                    | Ty_::Tdynamic(_)
                    | Ty_::Tvar(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tgeneric(_)
                    | Ty_::Tnewtype(_, _, _)
                    | Ty_::Tdependent(_, _)
                    | Ty_::Tclass(_, _, _)
                    | Ty_::Ttuple(_)
                    | Ty_::Tunion(_)
                    | Ty_::Tintersection(_)
                    | Ty_::Tshape(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tlabel(_)
                    | Ty_::TclassPtr(_),
                ),
                _,
            ) => {}
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typing_defs_core::mk;
    use crate::typing_make_type as make_type;

    fn prim(p: Tprim) -> Ty {
        make_type::prim_type(reason::none(), p)
    }

    fn string_class() -> Ty {
        make_type::class_type(reason::none(), C_STRING.to_string(), vec![])
    }

    #[test]
    fn trivial_result_of_strict_comparisons() {
        assert!(!trivial_result_str(Bop::Eqeqeq));
        assert!(trivial_result_str(Bop::Diff2));
        assert!(std::panic::catch_unwind(|| trivial_result_str(Bop::Eqeq)).is_err());
    }

    #[test]
    fn comparisons_to_enums_by_bound() {
        let int = prim(Tprim::Tint);
        let arraykey = prim(Tprim::Tarraykey);
        let string = string_class();
        let node = |t: &Ty| get_node(t).clone();
        // `int` bound
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tint)), &int));
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tarraykey)), &int));
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tnum)), &int));
        assert!(bad_compare_to_enum(&node(&prim(Tprim::Tbool)), &int));
        assert!(bad_compare_to_enum(&node(&string), &int));
        // `string` bound
        assert!(!bad_compare_to_enum(&node(&string), &string));
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tarraykey)), &string));
        assert!(bad_compare_to_enum(&node(&prim(Tprim::Tint)), &string));
        // `arraykey` bound
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tnum)), &arraykey));
        assert!(!bad_compare_to_enum(&node(&string), &arraykey));
        assert!(bad_compare_to_enum(&node(&prim(Tprim::Tfloat)), &arraykey));
        // other bounds, and other types
        assert!(!bad_compare_to_enum(&node(&prim(Tprim::Tint)), &prim(Tprim::Tbool)));
        let dynamic = mk((reason::none(), Ty_::Tdynamic(None)));
        assert!(!bad_compare_to_enum(&node(&dynamic), &int));
    }
}
