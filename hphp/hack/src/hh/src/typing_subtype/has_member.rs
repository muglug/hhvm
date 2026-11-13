// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 9859-10165): module `Has_member`.
//! See `hh/PORTING.md`.
//!
//! `simplify` has the signature of the prelude's `ConstraintHandler`; the
//! functions of `Common` are called as `common.rs` documents.

use naming_special_names_rust as sn;
use oxidized::ast_defs::Id;
use oxidized::nast;

use crate::quickfix;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::HasMember;
use crate::typing_defs_constraints::HasMemberMethod;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::MethodOrProperty;
use crate::typing_error::ReadOrWrite;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::and;
use crate::typing_logic_helpers::invalid;
use crate::typing_logic_helpers::valid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
use crate::typing_object_get;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;
use crate::typing_subtype::subtype;
/// `module TUtils = Typing_utils`
use crate::typing_utils as t_utils;

#[derive(Clone, Debug)]
pub struct Rhs {
    pub reason_super: Reason,
    pub has_member: HasMember,
}

/// This is a duplicate of logic in Typing_error_utils, due to conversion of primary errors to secondary errors
/// on some code paths for Typing_object_get, which throws out quickfix information (unsafe for secondary errors).
pub(crate) fn add_obj_get_quickfixes(
    ty_err: &typing_error::T,
    on_error: Option<reasons_callback::T>,
) -> Option<reasons_callback::T> {
    let prim = match ty_err {
        typing_error::T::Primary(prim) => Some(&**prim),
        _ => None,
    };
    match prim {
        Some(primary::T::Null_member {
            pos, obj_pos_opt, ..
        }) => {
            let quickfixes = match obj_pos_opt {
                Some(obj_pos) => {
                    let (obj_pos_start_line, _) = crate::pos::line_column(obj_pos);
                    let (rhs_pos_start_line, rhs_pos_start_column) = crate::pos::line_column(pos);
                    // heuristic: if the lhs and rhs of the Objget are on the same line, then we assume they are
                    // separated by two characters (`->`). So we do not generate a quickfix for chained Objgets:
                    // ```
                    // obj
                    // ->rhs
                    // ```
                    if obj_pos_start_line == rhs_pos_start_line {
                        let width = 2; // length of "->"
                        let quickfix_pos = crate::pos::set_col_end(
                            rhs_pos_start_column,
                            &crate::pos::set_col_start(rhs_pos_start_column - width, pos),
                        );
                        vec![quickfix::make_eager_default_hint_style(
                            "Add null-safe get".to_string(),
                            "?->".to_string(),
                            quickfix_pos,
                        )]
                    } else {
                        vec![]
                    }
                }
                None => vec![],
            };
            on_error.map(|cb| reasons_callback::add_quickfixes(cb, quickfixes))
        }
        _ => on_error,
    }
}

/// `explicit_targs` is the `hmm_explicit_targs` of the method, if the member
/// is one, and `has_member` its `hm_method`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn typing_obj_get(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    class_id: &nast::ClassId_,
    member_id: &nast::Sid,
    explicit_targs: Option<&[nast::Targ]>,
    member_ty: Ty,
    has_member: Option<&HasMemberMethod>,
    ty_sub: Ty,
    env: &mut Env,
) -> tl::SubtypeProp {
    let (explicit_targs, is_method): (&[nast::Targ], bool) = match explicit_targs {
        None => (&[], false),
        Some(targs) => (targs, true),
    };
    let (res, (obj_get_ty, _tal)) = typing_object_get::obj_get(
        // `~obj_pos:name_pos` is a lie: `name_pos` is the rhs of `->` or `?->`
        member_id.0.clone(),
        is_method,
        None,
        None,
        explicit_targs,
        class_id,
        member_id,
        callback::unify_error(),
        None,
        env,
        ty_sub,
    );
    let prop = match res {
        None => valid(env),
        Some(ty_err) => {
            let on_error = add_obj_get_quickfixes(&ty_err, subtype_env.on_error.clone());
            let discard_outermost = |err: typing_error::T| -> typing_error::T {
                match err {
                    typing_error::T::Apply_reasons(_, snd_err)
                        if is_method && matches!(&*snd_err, secondary::T::Of_error(_)) =>
                    {
                        match std::rc::Rc::unwrap_or_clone(snd_err) {
                            secondary::T::Of_error(err) => *err,
                            _ => unreachable!(),
                        }
                    }
                    err => err,
                }
            };
            let fail = on_error.map(|on_error| {
                discard_outermost(typing_error::apply_reasons(
                    secondary::T::Of_error(Box::new(ty_err)),
                    on_error,
                ))
            });
            invalid(fail, env)
        }
    };
    let subtype_env = match has_member {
        None => subtype_env.clone(),
        Some(has_member) => subtype_env::T {
            has_member_arg_posl: Some(has_member.args_pos.clone()),
            ..subtype_env.clone()
        },
    };
    and(env, prop, |env| {
        subtype::simplify(
            &subtype_env,
            this_ty,
            Lhs {
                sub_supportdyn: None,
                ty_sub: &obj_get_ty,
            },
            subtype::Rhs {
                super_like: false,
                super_supportdyn: false,
                ty_super: &member_ty,
            },
            env,
        )
    })
}

pub fn simplify(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    lhs: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    let Lhs {
        sub_supportdyn: _,
        ty_sub,
    } = lhs;
    let Rhs {
        reason_super: r,
        has_member: has_member_ty,
    } = &rhs;
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        r.clone(),
        ConstraintType_::ThasMember(has_member_ty.clone()),
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // `log_subtype_i` prints in the environment it is given, which the
        // continuation changes: a copy.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Has_member.simplify",
            &log_env,
            &ty_sub,
            &ty_super,
            || simplify_(subtype_env, this_ty, lhs, rhs, env),
        )
    } else {
        simplify_(subtype_env, this_ty, lhs, rhs, env)
    }
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
) -> tl::SubtypeProp {
    // `~rhs:({ reason_super = r; has_member = has_member_ty } as rhs)`
    let r = rhs.reason_super.clone();
    let has_member_ty = rhs.has_member.clone();
    let HasMember {
        name: member_id,
        type_: member_ty,
        class_id,
        method: method_info,
    } = &has_member_ty;
    let Id(name_pos, name_) = member_id;
    let is_method = method_info.is_some();
    let explicit_targs: Option<&[nast::Targ]> = method_info
        .as_ref()
        .map(|HasMemberMethod { explicit_targs, .. }| explicit_targs.as_slice());
    let cty_super = mk_constraint_type((r.clone(), ConstraintType_::ThasMember(has_member_ty.clone())));
    let ity_super = InternalType::ConstraintType(cty_super);
    let ty_sub = env::expand_type(env, ty_sub.clone());

    let subtype_env = subtype_env::possibly_add_violated_constraint(
        subtype_env.clone(),
        get_reason(&ty_sub).clone(),
        r.clone(),
    );
    let fail = subtype_env::fail(
        &subtype_env,
        InternalType::LoclType(ty_sub.clone()),
        ity_super.clone(),
    );

    match get_node(&ty_sub) {
        Ty_::Tvar(_) => mk_issubtype_prop(
            sub_supportdyn,
            subtype_env.is_dynamic_aware,
            env,
            InternalType::LoclType(ty_sub.clone()),
            ity_super,
        ),
        Ty_::Tunion(ty_subs) => {
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
        Ty_::Tintersection(tyl) if tyl.is_empty() => {
            // Tintersection [] = mixed
            let r_inter = get_reason(&ty_sub).clone();
            let ty_name = {
                let env = env.clone();
                let ty_sub = ty_sub.clone();
                Lazy::new(move || typing_print::error(None, &env, &ty_sub))
            };
            invalid(
                Some(typing_error::primary(primary::T::Top_member {
                    pos: name_pos.clone(),
                    name: name_.clone(),
                    is_nullable: true,
                    kind: if is_method {
                        MethodOrProperty::method_
                    } else {
                        MethodOrProperty::property
                    },
                    ctxt: ReadOrWrite::read,
                    decl_pos: reason::to_pos(&r_inter),
                    ty_name,
                    // Subtyping already gives these reasons
                    ty_reasons: Lazy::from_val(vec![]),
                })),
                env,
            )
        }
        Ty_::Tintersection(ty_subs) => {
            let r_sub = get_reason(&ty_sub).clone();
            // A & B <: C iif A <: C | !B
            //
            // The second case matches without binding the environment that
            // `find_type_with_exact_negation` returns: it goes on with the
            // environment from before.
            match subtype_negation::find_type_with_exact_negation_opt(env, ty_subs) {
                Some((non_ty, tyl)) => {
                    let ty_sub = make_type::intersection(r_sub, tyl);
                    let mk_prop = simplify;
                    let lift_rhs = |Rhs {
                                        reason_super,
                                        has_member,
                                    }: Rhs| {
                        mk_constraint_type((reason_super, ConstraintType_::ThasMember(has_member)))
                    };
                    let lhs = (sub_supportdyn, &ty_sub);
                    let rhs_subtype = subtype::Rhs {
                        super_supportdyn: false,
                        super_like: false,
                        ty_super: &non_ty,
                    };
                    let rhs_destructure = Rhs {
                        reason_super: r.clone(),
                        has_member: has_member_ty.clone(),
                    };
                    let rhs = (r.clone(), rhs_subtype, rhs_destructure);
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
                    typing_obj_get(
                        &subtype_env,
                        this_ty,
                        class_id,
                        member_id,
                        explicit_targs,
                        member_ty.clone(),
                        has_member_ty.method.as_ref(),
                        ty_sub.clone(),
                        env,
                    )
                }
            }
        }
        Ty_::Tnewtype(n, tyargs, _) => {
            let r1 = get_reason(&ty_sub).clone();
            let newtype_ty = t_utils::get_newtype_super(env, r1.clone(), n, tyargs);
            let sub_supportdyn = match sub_supportdyn {
                None => {
                    if n == sn::classes::SUPPORT_DYN {
                        Some(&r1)
                    } else {
                        None
                    }
                }
                _ => sub_supportdyn,
            };
            simplify(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn,
                    ty_sub: &newtype_ty,
                },
                Rhs {
                    reason_super: r.clone(),
                    has_member: has_member_ty.clone(),
                },
                env,
            )
        }
        Ty_::Tdynamic(_) if explicit_targs.is_some() => {
            // (`r` is the reason of the dynamic type here.)
            let r = get_reason(&ty_sub).clone();
            let subtype_env = subtype_env::set_is_dynamic_aware(subtype_env.clone(), true);
            subtype::simplify(
                &subtype_env,
                this_ty,
                Lhs {
                    sub_supportdyn: None,
                    ty_sub: &make_type::make_dynamic_tfun(r),
                },
                subtype::Rhs {
                    super_like: false,
                    super_supportdyn: false,
                    ty_super: &member_ty,
                },
                env,
            )
        }
        Ty_::Toption(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tnonnull
        | Ty_::Tany(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tgeneric(_)
        | Ty_::Tdependent(..)
        | Ty_::TvecOrDict(..)
        | Ty_::Taccess(_)
        | Ty_::Tclass(..)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_)
        | Ty_::TclassPtr(_) => typing_obj_get(
            &subtype_env,
            this_ty,
            class_id,
            member_id,
            explicit_targs,
            member_ty.clone(),
            has_member_ty.method.as_ref(),
            ty_sub.clone(),
            env,
        ),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use oxidized::pos::Pos;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    /// Line `line` (which starts at offset `100 * line`), columns `start` to
    /// `end` (counted from 0).
    fn pos(line: usize, start: usize, end: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, PathBuf::from("f.php")));
        let bol = 100 * line;
        Pos::from_lnum_bol_offset(file, (line, bol, bol + start), (line, bol, bol + end))
    }

    fn null_member(pos: Pos, obj_pos_opt: Option<Pos>) -> typing_error::T {
        typing_error::primary(primary::T::Null_member {
            pos,
            obj_pos_opt,
            ctxt: ReadOrWrite::read,
            kind: MethodOrProperty::property,
            member_name: "x".to_string(),
            reason: Lazy::from_val(vec![]),
        })
    }

    fn quickfixes(cb: &Option<reasons_callback::T>) -> Option<Vec<quickfix::Quickfix<Pos>>> {
        match cb {
            Some(reasons_callback::T::Add_quickfixes(_, qfxs)) => Some(Vec::clone(qfxs)),
            _ => None,
        }
    }

    #[test]
    fn add_obj_get_quickfixes_() {
        let on_error = || Some(reasons_callback::unify_error_at(pos(1, 0, 1)));
        // `$obj->x`: the quickfix replaces the `->` before the member.
        let err = null_member(pos(3, 6, 7), Some(pos(3, 0, 4)));
        let qfxs = quickfixes(&add_obj_get_quickfixes(&err, on_error())).unwrap();
        assert_eq!(qfxs.len(), 1);
        assert_eq!(qfxs[0].title, "Add null-safe get");
        match &qfxs[0].edits {
            quickfix::Edits::Eager(edits) => {
                assert_eq!(edits.len(), 1);
                assert_eq!(edits[0].0, "?->");
                assert_eq!(crate::pos::line_column(&edits[0].1), (3, 4));
                assert_eq!(crate::pos::end_line_column(&edits[0].1), (3, 6));
            }
            _ => panic!("expected an eager edit"),
        }
        // Different lines: no quickfix, but the callback still gets the
        // (empty) list.
        let err = null_member(pos(4, 2, 3), Some(pos(3, 0, 4)));
        let qfxs = quickfixes(&add_obj_get_quickfixes(&err, on_error())).unwrap();
        assert!(qfxs.is_empty());
        // No object position: the same.
        let err = null_member(pos(4, 2, 3), None);
        let qfxs = quickfixes(&add_obj_get_quickfixes(&err, on_error())).unwrap();
        assert!(qfxs.is_empty());
        // No callback: none.
        let err = null_member(pos(3, 6, 7), Some(pos(3, 0, 4)));
        assert!(add_obj_get_quickfixes(&err, None).is_none());
        // Other errors: the callback as it is.
        let err = typing_error::primary(primary::T::Nullsafe_property_write_context(pos(1, 0, 1)));
        assert!(quickfixes(&add_obj_get_quickfixes(&err, on_error())).is_none());
        assert!(add_obj_get_quickfixes(&err, on_error()).is_some());
    }
}
