// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 10167-10413): module `Has_const`.
//! See `hh/PORTING.md`.
//!
//! `simplify` has the signature of the prelude's `ConstraintHandler`; the
//! functions of `Common` are called as `common.rs` documents.

use naming_special_names_rust as sn;
use pos::ToOxidized;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::markdown_lite;
use crate::pos_or_decl;
use crate::quickfix;
use crate::string_utils;
use crate::typechecker_options;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_constraints::ConstraintType_;
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
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
/// `module TL = Typing_logic`
use crate::typing_logic as tl;
use crate::typing_logic_helpers::invalid;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
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
    pub name: String,
    pub ty: Ty,
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
        name,
        ty: member_ty,
    } = &rhs;
    let ty_sub = env::expand_type(env, ty_sub.clone());
    let ty_sub = InternalType::LoclType(ty_sub);
    let ty_super = InternalType::ConstraintType(mk_constraint_type((
        r.clone(),
        ConstraintType_::ThasConst {
            name: name.clone(),
            ty: member_ty.clone(),
        },
    )));
    if logging::should_log_subtype_i(env, 2, &ty_sub, &ty_super) {
        // `log_subtype_i` prints in the environment it is given, which the
        // continuation changes: a copy.
        let log_env = env.clone();
        logging::log_subtype_i(
            this_ty,
            "Typing_subtype.Has_const.simplify",
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
    // `~rhs:({ reason_super = r; name; ty = member_ty } as rhs)`
    let cty_super = mk_constraint_type((
        rhs.reason_super.clone(),
        ConstraintType_::ThasConst {
            name: rhs.name.clone(),
            ty: rhs.ty.clone(),
        },
    ));
    let ity_super = InternalType::ConstraintType(cty_super);
    let fail = subtype_env::fail(subtype_env, InternalType::LoclType(ty_sub.clone()), ity_super);
    let this_ty = this_ty.cloned().unwrap_or_else(|| ty_sub.clone());
    simplify_has_const(
        subtype_env,
        &this_ty,
        fail,
        Lhs {
            sub_supportdyn,
            ty_sub,
        },
        rhs,
        env,
    )
}

pub(crate) fn simplify_has_const(
    subtype_env: &subtype_env::T,
    this_ty: &Ty,
    fail: Option<typing_error::T>,
    Lhs {
        sub_supportdyn,
        ty_sub,
    }: Lhs,
    rhs: Rhs,
    env: &mut Env,
) -> tl::SubtypeProp {
    // `~rhs:({ reason_super = r; name; ty = member_ty } as rhs)`
    let r = rhs.reason_super.clone();
    let name = rhs.name.clone();
    let member_ty = rhs.ty.clone();
    let ety_sub = env::expand_type(env, ty_sub.clone());
    match get_node(&ety_sub) {
        Ty_::Tclass((_, enum_name), _, _) => {
            let cls = env::get_class(env, enum_name);
            match cls {
                decl_entry::T::Found(cls) => {
                    let maybe_const = match env::get_typeconst(env, &cls, &name) {
                        Some(_) => None,
                        None => env::get_const(env, &cls, &name),
                    };
                    match maybe_const {
                        Some(const_def) => {
                            let dty = const_def.ty;
                            let ety_env = ExpandEnv {
                                this_ty: this_ty.clone(),
                                ..empty_expand_env()
                            };
                            let (_ty_err_opt, lty) =
                                if typechecker_options::legacy_experimental_feature_enabled(
                                    &env::get_tcopt(env),
                                    typechecker_options::experimental_sound_enum_class_type_const,
                                ) {
                                    phase::localize(&ety_env, env, &dty)
                                } else {
                                    phase::localize_no_subst(env, true, &dty)
                                };
                            subtype::simplify(
                                subtype_env,
                                None,
                                Lhs {
                                    sub_supportdyn,
                                    ty_sub: &lty,
                                },
                                subtype::Rhs {
                                    super_like: false,
                                    super_supportdyn: false,
                                    ty_super: &member_ty,
                                },
                                env,
                            )
                        }
                        None => {
                            let consts: Vec<_> = env::consts(env, &cls)
                                .into_iter()
                                .filter(|(name, _)| {
                                    !(name == sn::members::M_CLASS || cls::has_typeconst(&cls, name))
                                })
                                .collect();
                            let fail = {
                                let pos_opt = pos_or_decl::fill_in_filename_if_in_current_decl(
                                    &env::get_current_decl_and_file(env),
                                    &reason::to_pos(&r),
                                );
                                let (most_similar, quickfixes_opt) =
                                    match string_utils::most_similar(
                                        None,
                                        &name,
                                        &consts,
                                        |(name, _)| name.clone(),
                                    ) {
                                        Some((name, const_)) => {
                                            let new_text = name.clone();
                                            (
                                                Some((new_text.clone(), const_.pos.to_oxidized())),
                                                pos_opt.map(|pos| {
                                                    vec![{
                                                        let (_, start_column) =
                                                            crate::pos::line_column(&pos);
                                                        quickfix::make_eager_default_hint_style(
                                                            "Change to ".to_string()
                                                                + &markdown_lite::md_codify(&name),
                                                            new_text,
                                                            crate::pos::set_col_start(
                                                                start_column + 1,
                                                                &pos,
                                                            ),
                                                        )
                                                    }]
                                                }),
                                            )
                                        }
                                        None => (None, None),
                                    };
                                let subtype_env = match quickfixes_opt {
                                    None => subtype_env.clone(),
                                    Some(quickfixes) => {
                                        subtype_env::map_on_error(subtype_env.clone(), |on_error| {
                                            reasons_callback::add_quickfixes(on_error, quickfixes)
                                        })
                                    }
                                };
                                // The argument of `@@` is evaluated first.
                                let suffix = secondary::T::Unknown_label {
                                    enum_name: enum_name.clone(),
                                    decl_pos: cls::pos(&cls),
                                    most_similar,
                                };
                                subtype_env::fail_with_suffix(
                                    &subtype_env,
                                    InternalType::LoclType(ty_sub.clone()),
                                    InternalType::ConstraintType(mk_constraint_type((
                                        r.clone(),
                                        ConstraintType_::ThasConst {
                                            name: name.clone(),
                                            ty: member_ty.clone(),
                                        },
                                    ))),
                                    suffix,
                                )
                            };
                            invalid(fail, env)
                        }
                    }
                }
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => invalid(fail, env),
            }
        }
        Ty_::Tvar(_) => {
            let cty_super = mk_constraint_type((
                r,
                ConstraintType_::ThasConst {
                    name,
                    ty: member_ty,
                },
            ));
            let ity_super = InternalType::ConstraintType(cty_super);
            mk_issubtype_prop(
                sub_supportdyn,
                subtype_env.is_dynamic_aware,
                env,
                InternalType::LoclType(ty_sub.clone()),
                ity_super,
            )
        }
        Ty_::Tunion(ty_subs) => {
            let r_sub = get_reason(&ety_sub).clone();
            common::simplify_union_l(
                subtype_env,
                None,
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
        Ty_::Tintersection(ty_subs) => {
            let r_sub = get_reason(&ety_sub).clone();
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
                                        name,
                                        ty,
                                    }: Rhs| {
                        mk_constraint_type((reason_super, ConstraintType_::ThasConst { name, ty }))
                    };
                    let lhs = (sub_supportdyn, &ty_sub);
                    let rhs_subtype = subtype::Rhs {
                        super_supportdyn: false,
                        super_like: false,
                        ty_super: &non_ty,
                    };
                    let rhs_destructure = Rhs {
                        reason_super: r.clone(),
                        name,
                        ty: member_ty,
                    };
                    let rhs = (r, rhs_subtype, rhs_destructure);
                    common::simplify_disj_r(
                        subtype_env,
                        None,
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
                        subtype_env,
                        None,
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
        Ty_::Tgeneric(generic_nm) => {
            let r_generic = get_reason(&ety_sub).clone();
            common::simplify_generic_l(
                subtype_env,
                Some(this_ty),
                fail.into(),
                simplify,
                (sub_supportdyn, r_generic, generic_nm.clone()),
                rhs.clone(),
                rhs,
                env,
            )
        }
        Ty_::Tnewtype(nm, tyl, _) => {
            let r_newtype = get_reason(&ety_sub).clone();
            let ty_newtype = t_utils::get_newtype_super(env, r_newtype.clone(), nm, tyl);
            common::simplify_newtype_l(
                subtype_env,
                Some(this_ty),
                simplify,
                (sub_supportdyn, r_newtype, nm.clone(), ty_newtype),
                rhs,
                env,
            )
        }
        Ty_::Tdependent(dep_ty, ty_inner_sub) => {
            let r_dep = get_reason(&ety_sub).clone();
            common::simplify_dependent_l(
                subtype_env,
                Some(this_ty),
                simplify,
                (sub_supportdyn, r_dep, dep_ty.clone(), ty_inner_sub.clone()),
                rhs,
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
        | Ty_::TvecOrDict(..)
        | Ty_::Taccess(_)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_) => invalid(fail, env),
        Ty_::TclassPtr(_) => {
            // TODO(T199606542) Check if this can be used to improve inference for $c::FOO
            invalid(fail, env)
        }
    }
}
