// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_object_get.ml`. See `hh/PORTING.md`.
//!
//! The public surface is that of `typing_object_get.mli`: [`obj_get`],
//! [`obj_get_with_mismatches`] and [`smember_not_found`]. Everything else is
//! private, as the `.mli` hides it.
//!
//! - `internal_result` (`env * error option * (ty * targs) * mismatch *
//!   mismatch option`) is [`InternalResult`] without the environment: the
//!   internal functions take `&mut Env` and return the rest.
//! - `obj_get_args` is [`ObjGetArgs`]; `{ args with f = v }` is
//!   `ObjGetArgs { f: v, ..args.clone() }`. The explicit type arguments are
//!   borrowed from the caller rather than copied with every update.
//! - The polymorphic variant ``[ `concrete | `inner ]`` of `log_obj_get` is
//!   [`ObjGetHelper`].
//! - Public functions take by value what the OCaml stores in what it builds
//!   (positions, the callback, the receiver type) and by reference what it
//!   only reads (`explicit_targs`, `class_id`, `member_id`).

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
use crate::decl_instantiate;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::pos_or_decl;
use crate::quickfix;
use crate::tast;
use crate::typing_coercion;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::HasMember;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::mk_constraint_type;
use crate::typing_defs_core::Capability;
use crate::typing_defs_core::CeVisibility;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclTy_;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::FunImplicitParams;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::nonexact;
use crate::typing_defs_core::string_of_visibility;
use crate::typing_defs_core::with_reason;
use crate::typing_defs_flags;
use crate::typing_dependent_type::expr_dep_ty;
use crate::typing_dynamic;
use crate::typing_dynamic_utils;
use crate::typing_enforceability;
use crate::typing_enum;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::primary::InstanceOrStatic;
use crate::typing_error::primary::MethOrProp;
use crate::typing_error::primary::MethodOrProperty;
use crate::typing_error::primary::NonObjectMemberKind;
use crate::typing_error::primary::ReadOrWrite;
use crate::typing_error::primary::SmemberNotFoundKind;
use crate::typing_intersection;
use crate::typing_log;
use crate::typing_log::LogStructure;
use crate::typing_make_type as make_type;
use crate::typing_ops;
use crate::typing_phase;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_solver;
use crate::typing_union;
use crate::typing_utils as tutils;
use crate::typing_visibility as tvis;
use crate::utils::strip_ns;

/// `ty_mismatch = (locl_ty, locl_ty * locl_ty) result`
type TyMismatch = Result<Ty, (Ty, Ty)>;

/// `internal_result`, without the environment (which the functions that
/// return it take as `&mut Env`).
type InternalResult = (
    Option<typing_error::T>,
    (Ty, Vec<tast::Targ>),
    TyMismatch,
    Option<TyMismatch>,
);

/// The result of [`obj_get_with_mismatches`] (and of its helper), without
/// the environment.
type WithMismatches = (
    Option<typing_error::T>,
    (Ty, Vec<tast::Targ>),
    Option<(Ty, Ty)>,
    Option<(Ty, Ty)>,
);

/// `Option.merge` (Core)
fn option_merge<A>(a: Option<A>, b: Option<A>, f: impl FnOnce(A, A) -> A) -> Option<A> {
    match (a, b) {
        (None, b) => b,
        (a, None) => a,
        (Some(a), Some(b)) => Some(f(a, b)),
    }
}

/// `Pos_or_decl.t Message.t list` from the `(Pos_or_decl.t * string) list`
/// that `Typing_reason.to_string` gives (the same OCaml type).
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter()
        .map(|(pos, msg)| Message(pos, msg.into()))
        .collect()
}

/// `Typing_defs.get_pos` on a decl type.
fn decl_get_pos(ty: &DeclTy) -> PosOrDecl {
    PosOrDecl::from(decl_utils::get_pos(ty))
}

/// `Typing_reason.localize` of the reason of a decl type.
fn localize_decl_reason(ty: &DeclTy) -> Reason {
    typing_reason::localize(&ty.reason().clone().to_oxidized())
}

/// `Naming_special_names.Members.is_special_xhp_attribute`, with the OCaml's
/// `String.is_prefix`. `naming_special_names_rust::members` has it, but it
/// slices `&s[..6]`, which panics when byte 6 of the name falls inside a
/// multibyte character (a property named `aaaaaé`); the OCaml cannot fail.
fn is_special_xhp_attribute(s: &str) -> bool {
    s.starts_with(":data-") || s.starts_with(":aria-")
}

/// `List.max_elt ~compare` (Core): the first of the greatest elements.
fn list_max_elt<A>(l: Vec<A>, compare: impl Fn(&A, &A) -> std::cmp::Ordering) -> Option<A> {
    let mut max: Option<A> = None;
    for elt in l {
        max = match max {
            None => Some(elt),
            Some(m) => {
                if compare(&m, &elt) == std::cmp::Ordering::Less {
                    Some(elt)
                } else {
                    Some(m)
                }
            }
        };
    }
    max
}

fn merge_ty_err(
    ty_err_opt1: Option<typing_error::T>,
    (ty_err_opt2, tals, lval_mismatch, rval_mismatch_opt): InternalResult,
) -> InternalResult {
    let ty_err_opt = option_merge(ty_err_opt1, ty_err_opt2, typing_error::both);
    (ty_err_opt, tals, lval_mismatch, rval_mismatch_opt)
}

/// Common arguments to internal `obj_get_...` functions
#[derive(Clone)]
struct ObjGetArgs<'a> {
    is_method: bool,
    is_nonnull: bool,
    nullsafe: Option<Pos>,
    obj_pos: Pos,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    explicit_targs: &'a [nast::Targ],
    this_ty: Ty,
    this_ty_conjunct: Ty,
    is_parent_call: bool,
    dep_kind: (Reason, expr_dep_ty::Dep),
    seen: im::OrdSet<String>,
}

/// ``[ `concrete | `inner ]``, the `helper` of `log_obj_get`
#[derive(Clone, Copy)]
enum ObjGetHelper {
    Concrete,
    Inner,
}

fn log_obj_get(env: &Env, helper: ObjGetHelper, id: &nast::Sid, ty: &Ty, this_ty: &Ty) {
    let (fn_name, ty_name) = match helper {
        ObjGetHelper::Concrete => ("obj_get_concrete_ty", "concrete_ty"),
        ObjGetHelper::Inner => ("obj_get_inner", "receiver_ty"),
    };
    typing_log::log_with_level(env, "obj_get", 2, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(id.0.clone()),
            env,
            &[LogStructure::LogHead(
                format!("{} (member_id: {})", fn_name, id.1),
                vec![
                    LogStructure::LogType(ty_name.to_string(), ty.clone()),
                    LogStructure::LogType("this_ty".to_string(), this_ty.clone()),
                ],
            )],
        )
    })
}

fn mk_ety_env(class_info: &cls::T, paraml: &[Ty], this_ty: Ty) -> ExpandEnv {
    ExpandEnv {
        this_ty,
        substs: tutils::make_locl_subst_for_class_tparams(class_info, paraml),
        ..typing_defs::empty_expand_env()
    }
}

fn mk_mismatch_intersection(env: &mut Env, errs_res: Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)>) -> TyMismatch {
    match errs_res {
        Ok(tys) => {
            let ty: Ty = typing_intersection::intersect_list(env, typing_reason::none(), &tys);
            Ok(ty)
        }
        Err((actuals, expecteds)) => {
            let ty_actual: Ty = typing_intersection::intersect_list(env, typing_reason::none(), &actuals);
            let ty_expect: Ty =
                typing_intersection::intersect_list(env, typing_reason::none(), &expecteds);
            Err((ty_actual, ty_expect))
        }
    }
}

fn mk_mismatch_union(env: &mut Env, errs_res: Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)>) -> TyMismatch {
    match errs_res {
        Ok(tys) => {
            let ty: Ty = typing_union::union_list(env, None, typing_reason::none(), &tys);
            Ok(ty)
        }
        Err((actuals, expecteds)) => {
            let ty_acutal: Ty = typing_union::union_list(env, None, typing_reason::none(), &actuals);
            let ty_expect: Ty = typing_union::union_list(env, None, typing_reason::none(), &expecteds);
            Err((ty_acutal, ty_expect))
        }
    }
}

/// The OCaml conses each element onto the accumulated lists, so the result
/// lists are in the reverse order of `mismatches`. Here the lists are built
/// by pushing and reversed at the end, which gives the same lists.
fn fold_mismatches(mismatches: Vec<TyMismatch>) -> Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> {
    let mut acc: Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> = Ok(vec![]);
    for err in mismatches {
        acc = match (acc, err) {
            (Ok(mut xs), Ok(x)) => {
                xs.push(x);
                Ok(xs)
            }
            (Ok(xs), Err((x, y))) => {
                let mut ys = xs.clone();
                let mut xs = xs;
                xs.push(x);
                ys.push(y);
                Err((xs, ys))
            }
            (Err((mut xs, mut ys)), Ok(x)) => {
                xs.push(x.clone());
                ys.push(x);
                Err((xs, ys))
            }
            (Err((mut xs, mut ys)), Err((x, y))) => {
                xs.push(x);
                ys.push(y);
                Err((xs, ys))
            }
        }
    }
    match acc {
        Ok(mut xs) => {
            xs.reverse();
            Ok(xs)
        }
        Err((mut xs, mut ys)) => {
            xs.reverse();
            ys.reverse();
            Err((xs, ys))
        }
    }
}

fn fold_mismatch_opts(
    opt_errs: Vec<Option<TyMismatch>>,
) -> Option<Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)>> {
    // `Option.all`
    let all: Option<Vec<TyMismatch>> = opt_errs.into_iter().collect();
    all.map(fold_mismatches)
}

fn get_member(is_method: bool, env: &Env, class_info: &cls::T, member_name: &str) -> Option<ClassElt> {
    if is_method {
        if member_name == sn::members::__CONSTRUCT {
            env::get_construct(env, class_info).0
        } else {
            env::get_method(env, class_info, member_name)
        }
    } else {
        env::get_prop(env, class_info, member_name)
    }
}

pub fn smember_not_found(
    pos: Pos,
    is_const: bool,
    is_method: bool,
    is_function_pointer: bool,
    class_: &cls::T,
    member_name: String,
    on_error: callback::T,
) -> typing_error::T {
    let kind = if is_const {
        SmemberNotFoundKind::class_constant
    } else if is_method {
        SmemberNotFoundKind::static_method
    } else {
        SmemberNotFoundKind::class_variable
    };
    let error = |hint: Option<(InstanceOrStatic, PosOrDecl, String)>| {
        // OCaml evaluates the components of the tuple right to left.
        let class_name = cls::name(class_);
        let class_pos = cls::pos(class_);
        let quickfixes = match &hint {
            None => vec![],
            Some((_, _, new_text)) => vec![quickfix::make_eager_default_hint_style(
                format!("Change to ::{}", new_text),
                new_text.clone(),
                pos.clone(),
            )],
        };
        typing_error::apply(
            typing_error::primary(primary::T::Smember_not_found {
                pos: pos.clone(),
                kind,
                class_name,
                class_pos,
                member_name: member_name.clone(),
                hint,
                quickfixes,
            }),
            on_error.clone(),
        )
    };
    let static_suggestion = env::suggest_static_member(is_method, class_, &member_name);
    let method_suggestion = env::suggest_member(is_method, class_, &member_name);
    match (static_suggestion, method_suggestion) {
        // If there is a normal method of the same name and the
        // syntax is a function pointer, suggest meth_caller
        (_, Some((_, v))) if is_function_pointer && v == member_name => {
            typing_error::primary(primary::T::Consider_meth_caller {
                pos: pos.clone(),
                class_name: cls::name(class_),
                meth_name: member_name.clone(),
            })
        }
        // If there is a normal method of the same name, suggest it
        (Some(_), Some((def_pos, v))) if v == member_name => {
            error(Some((InstanceOrStatic::instance, def_pos, v)))
        }
        // Otherwise suggest a different static method
        (Some((def_pos, v)), _) => error(Some((InstanceOrStatic::static_, def_pos, v))),
        // Fallback to closest normal method
        (None, Some((def_pos, v))) => error(Some((InstanceOrStatic::instance, def_pos, v))),
        (None, None) => error(None),
    }
}

fn member_not_found(
    env: &Env,
    pos: Pos,
    is_method: bool,
    class_: &cls::T,
    member_name: &str,
    r: &Reason,
    on_error: callback::T,
) -> typing_error::T {
    let cls_name = strip_ns(&cls::name(class_)).to_string();
    if env::is_in_expr_tree(env) && is_method && member_name.starts_with("__") {
        typing_error::expr_tree(
            primary::expr_tree::T::Expression_tree_unsupported_operator {
                class_name: cls_name,
                member_name: member_name.to_string(),
                pos,
            },
        )
    } else {
        // OCaml evaluates the components of the tuple right to left.
        let class_name = cls::name(class_);
        let class_pos = cls::pos(class_);
        let reason = {
            let r = r.clone();
            Lazy::new(move || {
                messages(typing_reason::to_string(
                    &format!("This is why I think it is an object of type {}", cls_name),
                    &r,
                ))
            })
        };
        let hint = {
            let class_ = class_.clone();
            let member_name = member_name.to_string();
            Lazy::new(move || {
                let method_suggestion = env::suggest_member(is_method, &class_, &member_name);
                let static_suggestion = env::suggest_static_member(is_method, &class_, &member_name);
                match (method_suggestion, static_suggestion) {
                    // Prefer suggesting a different method, unless there's a
                    // static method whose name matches exactly.
                    (Some(_), Some((def_pos, v))) if v == member_name => {
                        Some((InstanceOrStatic::static_, def_pos, v))
                    }
                    (Some((def_pos, v)), _) => Some((InstanceOrStatic::instance, def_pos, v)),
                    (None, Some((def_pos, v))) => Some((InstanceOrStatic::static_, def_pos, v)),
                    (None, None) => None,
                }
            })
        };
        typing_error::apply(
            typing_error::primary(primary::T::Member_not_found {
                pos,
                kind: if is_method {
                    MethodOrProperty::method_
                } else {
                    MethodOrProperty::property
                },
                class_name,
                class_pos,
                member_name: member_name.to_string(),
                hint,
                reason,
            }),
            on_error,
        )
    }
}

/// The OCaml localizes in an environment that it then drops (it returns no
/// environment): the localization happens in a copy here.
fn sound_dynamic_err_opt(
    args: &ObjGetArgs<'_>,
    env: &Env,
    id: &nast::Sid,
    read_context: bool,
) -> Option<typing_error::T> {
    let ast_defs::Id(id_pos, id_str) = id;
    // Any access to a *private* member through dynamic might potentially
    // be unsound, if the receiver is an instance of a class that implements dynamic,
    // as we do no checks on enforceability or subtype-dynamic at the definition site
    // of private members.
    match env::get_self_class(env) {
        decl_entry::T::Found(self_class)
            if cls::get_support_dynamic_type(&self_class) || !cls::final_(&self_class) =>
        {
            match get_member(args.is_method, env, &self_class, id_str) {
                // `Some { ce_visibility = Vprivate _; ce_type = (lazy ty); _ }
                // when not args.is_method`: OCaml forces the lazy type while
                // matching, so before the guard is tested.
                Some(ClassElt {
                    ce_visibility: CeVisibility::Vprivate(_),
                    ce_type,
                    ..
                }) => {
                    let ty: DeclTy = (**ce_type).clone();
                    if args.is_method {
                        None
                    } else if read_context {
                        let mut env = env.clone();
                        let (lclz_ty_err_opt, locl_ty): (Option<typing_error::T>, Ty) =
                            typing_phase::localize_no_subst(&mut env, true, &ty);
                        let read_err: Option<typing_error::T> =
                            typing_dynamic::check_property_sound_for_dynamic_read(
                            |pos: Pos, prop_name: String, class_name: String, (prop_pos, prop_type): (PosOrDecl, String)| {
                                typing_error::primary(primary::T::Private_property_is_not_dynamic {
                                    pos,
                                    prop_name,
                                    class_name,
                                    prop_pos,
                                    prop_type,
                                })
                            },
                            &env,
                            cls::name(&self_class),
                            (id_pos.clone(), id_str.clone()),
                            &locl_ty,
                        );
                        option_merge(lclz_ty_err_opt, read_err, typing_error::both)
                    } else {
                        typing_dynamic::check_property_sound_for_dynamic_write(
                            Some(&self_class),
                            |pos: Pos, prop_name: String, class_name: String, (prop_pos, prop_type): (PosOrDecl, String)| {
                                typing_error::primary(
                                    primary::T::Private_property_is_not_enforceable {
                                        pos,
                                        prop_name,
                                        class_name,
                                        prop_pos,
                                        prop_type,
                                    },
                                )
                            },
                            env,
                            cls::name(&self_class),
                            (id_pos.clone(), id_str.clone()),
                            &ty,
                            None,
                        )
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn widen_class_for_obj_get(
    is_method: bool,
    nullsafe: Option<&Pos>,
    member_name: &str,
    env: &mut Env,
    ty: Ty,
) -> Option<Ty> {
    match get_node(&ty) {
        Ty_::Tprim(ast_defs::Tprim::Tnull) => {
            if nullsafe.is_some() {
                Some(ty)
            } else {
                None
            }
        }
        Ty_::Tclass(class_id, _, tyl) => {
            let r2 = get_reason(&ty).clone();
            let class_name = &class_id.1;
            let default = || {
                let ty = mk((r2.clone(), Ty_::Tclass(class_id.clone(), nonexact(), tyl.clone())));
                Some(ty)
            };
            match env::get_class(env, class_name) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => default(),
                decl_entry::T::Found(class_info) => {
                    match get_member(is_method, env, &class_info, member_name) {
                        Some(ClassElt { ce_origin, .. }) => {
                            // If this member was inherited then we obtain the type from which
                            // it is inherited as our wider type
                            if ce_origin == *class_name {
                                default()
                            } else {
                                match cls::get_ancestor(&class_info, &ce_origin) {
                                    None => default(),
                                    Some(basety) => {
                                        let ety_env = ExpandEnv {
                                            substs: tutils::make_locl_subst_for_class_tparams(
                                                &class_info,
                                                tyl,
                                            ),
                                            this_ty: ty.clone(),
                                            ..typing_defs::empty_expand_env()
                                        };
                                        let (_, basety): (Option<typing_error::T>, Ty) =
                                            typing_phase::localize(&ety_env, env, &basety);
                                        Some(basety)
                                    }
                                }
                            }
                        }
                        None => None,
                    }
                }
            }
        }
        _ => None,
    }
}

/// `ty` is expected to be the type for a property or method that has been
/// accessed using the nullsafe operatore e.g. $x?->prop or $x?->foo(...).
///
/// For properties, just make the type nullable.
/// For methods, we expect a function type, and make the return type nullable.
/// But in the case that we have type nothing, we just use the type `null`.
/// The `call` helper will deal appropriately with it.
/// Similarly if we have dynamic, or err, or any, we leave as dynamic/err/any respectively.
fn make_nullable_member_type(env: &mut Env, is_method: bool, id_pos: &Pos, pos: &Pos, ty: Ty) -> Ty {
    if is_method {
        tutils::map_supportdyn(env, ty, |env: &mut Env, ty: Ty| {
            let ty = env::expand_type(env, ty);
            let r = get_reason(&ty).clone();
            match get_node(&ty) {
                Ty_::Tfun(tf) => {
                    let ty = make_nullable_member_type(env, false, id_pos, pos, tf.ret.clone());
                    mk((
                        r,
                        Ty_::Tfun(std::rc::Rc::new(FunType {
                            ret: ty,
                            ..FunType::clone(&tf)
                        })),
                    ))
                }
                Ty_::Tunion(tyl) if !tyl.is_empty() => {
                    let tyl: Vec<Ty> = tyl
                        .iter()
                        .map(|ty| make_nullable_member_type(env, is_method, id_pos, pos, ty.clone()))
                        .collect();
                    typing_union::union_list(env, None, r, &tyl)
                }
                Ty_::Tintersection(tyl) => {
                    let tyl: Vec<Ty> = tyl
                        .iter()
                        .map(|ty| make_nullable_member_type(env, is_method, id_pos, pos, ty.clone()))
                        .collect();
                    typing_intersection::intersect_list(env, r, &tyl)
                }
                Ty_::Tdynamic(_) | Ty_::Tany(_) => ty,
                Ty_::Tunion(_) => make_type::null(typing_reason::nullsafe_op(pos.clone())),
                _ => {
                    // Shouldn't happen
                    make_nullable_member_type(env, false, id_pos, pos, ty)
                }
            }
        })
    } else {
        let ty: Ty = typing_intersection::intersect_with_nonnull(
            env,
            pos_or_decl::of_raw_pos(id_pos.clone()),
            ty,
        );
        make_type::nullable(typing_reason::nullsafe_op(pos.clone()), ty)
    }
}

/// Return true if the `this` type appears in a covariant
/// (resp. contravariant, if contra=true) position in ty.
fn this_appears_covariantly(contra: bool, env: &Env, ty: &DeclTy) -> bool {
    fn this_appears_covariantly_params(
        contra: bool,
        env: &Env,
        tparams: &[DeclTparam],
        tyl: &[DeclTy],
    ) -> bool {
        match (tparams, tyl) {
            ([tp, tparams @ ..], [ty, tyl @ ..]) => {
                (match tp.variance {
                    ast_defs::Variance::Covariant => this_appears_covariantly(contra, env, ty),
                    ast_defs::Variance::Contravariant => {
                        this_appears_covariantly(!contra, env, ty)
                    }
                    ast_defs::Variance::Invariant => {
                        this_appears_covariantly(contra, env, ty)
                            || this_appears_covariantly(!contra, env, ty)
                    }
                }) || this_appears_covariantly_params(contra, env, tparams, tyl)
            }
            _ => false,
        }
    }
    match ty.node_ref() {
        DeclTy_::Tthis => !contra,
        DeclTy_::Ttuple(tuple) => {
            // `t_extra = Tvariadic t_vs | Tsplat t_vs`
            let ty::decl::ty::TupleType(t_required, t_optional, t_extra) = &**tuple;
            let t_vs = match t_extra {
                ty::decl::ty::TupleExtra::Tvariadic(t_vs) | ty::decl::ty::TupleExtra::Tsplat(t_vs) => {
                    t_vs
                }
            };
            t_required
                .iter()
                .any(|ty| this_appears_covariantly(contra, env, ty))
                || t_optional
                    .iter()
                    .any(|ty| this_appears_covariantly(contra, env, ty))
                || this_appears_covariantly(contra, env, t_vs)
        }
        DeclTy_::Tunion(tyl) | DeclTy_::Tintersection(tyl) => {
            tyl.iter().any(|ty| this_appears_covariantly(contra, env, ty))
        }
        DeclTy_::Tfun(ft) => {
            this_appears_covariantly(contra, env, &ft.ret)
                || ft
                    .params
                    .iter()
                    .any(|fp| this_appears_covariantly(!contra, env, &fp.ty))
        }
        DeclTy_::Tshape(shape) => match &**shape {
            // `Shape_simple { s_fields = fm; _ }`, `TShapeMap.elements fm`:
            // the hackrs map is ordered as `TShapeField.compare` orders
            // (variant, then names by their strings, without positions), and
            // `Wrapped_map.elements` (`fold (fun k v acc -> (k, v) :: acc) m
            // []`) gives the bindings in decreasing order, so `exists` visits
            // the fields, and records the dependencies of
            // `get_class_or_typedef_tparams`, in the OCaml order.
            ty::decl::ty::ShapeType::Simple(ty::decl::ty::ShapeTypeSimple(_, fm)) => fm
                .values()
                .rev()
                .any(|f| this_appears_covariantly(contra, env, &f.ty)),
            ty::decl::ty::ShapeType::Splat(_) => false,
        },
        DeclTy_::Taccess(taccess) => this_appears_covariantly(contra, env, &taccess.ty),
        DeclTy_::Trefinement(trefinement) => {
            this_appears_covariantly(contra, env, &trefinement.ty)
        }
        DeclTy_::Tlike(ty) | DeclTy_::Toption(ty) => this_appears_covariantly(contra, env, ty),
        DeclTy_::TvecOrDict(tys) => {
            let (ty1, ty2) = &**tys;
            this_appears_covariantly(contra, env, ty1) || this_appears_covariantly(contra, env, ty2)
        }
        DeclTy_::Tapply(pos_name_and_tyl) => {
            let (pos_name, tyl) = &**pos_name_and_tyl;
            let tparams = env::get_class_or_typedef_tparams(env, pos_name.id_ref().as_str());
            this_appears_covariantly_params(contra, env, &tparams, tyl)
        }
        DeclTy_::Tmixed
        | DeclTy_::Twildcard
        | DeclTy_::Tany
        | DeclTy_::Tnonnull
        | DeclTy_::Tdynamic
        | DeclTy_::Tprim(_)
        | DeclTy_::Tgeneric(_) => false,
        DeclTy_::TclassPtr(ty) => this_appears_covariantly(contra, env, ty),
    }
}

/// We know that the receiver is a concrete class, not a generic with
/// bounds, or a Tunion.
///
/// `default` closes over the environment as it is on entry, before
/// `Env.expand_type`: in the branches that use it the result is that
/// environment (saved here) with a fresh type variable.
fn obj_get_concrete_ty(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    concrete_ty: Ty,
    id: &nast::Sid,
    on_error: &callback::T,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    log_obj_get(env, ObjGetHelper::Concrete, id, &concrete_ty, &args.this_ty);
    let dflt_rval_mismatch: Option<TyMismatch> = args
        .coerce_from_ty
        .as_ref()
        .map(|(_, _, ty)| Ok(ty.clone()));
    let dflt_lval_mismatch: TyMismatch = Ok(concrete_ty.clone());

    let env_of_default = env.clone();
    let default = |env: &mut Env,
                   lval_mismatch: Option<TyMismatch>,
                   rval_mismatch: Option<Option<TyMismatch>>,
                   ty_err_opt: Option<typing_error::T>|
     -> InternalResult {
        let lval_mismatch = lval_mismatch.unwrap_or_else(|| dflt_lval_mismatch.clone());
        let rval_mismatch = rval_mismatch.unwrap_or_else(|| dflt_rval_mismatch.clone());
        *env = env_of_default.clone();
        let ty = env::fresh_type_error(env, id_pos.clone());
        (ty_err_opt, (ty, vec![]), lval_mismatch, rval_mismatch)
    };
    let read_context = args.coerce_from_ty.is_none();
    let concrete_ty = env::expand_type(env, concrete_ty);
    let r = get_reason(&concrete_ty).clone();
    match get_node(&concrete_ty) {
        Ty_::Tclass((_, class_name), _, paraml) => {
            // (`default` is not used here: the saved copy is dropped, so
            // that the first write to `env` does not copy it.)
            drop(env_of_default);
            obj_get_concrete_class(
                args,
                env,
                concrete_ty.clone(),
                id,
                r,
                class_name,
                paraml,
                on_error,
            )
        }
        Ty_::Tdynamic(shadow_v_opt) => {
            let err_opt = sound_dynamic_err_opt(args, env, id, read_context);
            // Dynamic inference: when accessing a property on a dynamic with a shadow
            // type variable, create a fresh shadow type variable for the result and
            // record a has_member constraint on the receiver's shadow. This tracks that
            // the dynamic value was used as an object with property `id`.
            let result_shadow = match shadow_v_opt {
                Some(shadow_v) => {
                    let v_prop = env::fresh_shadow_tyvar(env, id_pos.clone());
                    let prop_ty = mk((typing_reason::none(), Ty_::Tdynamic(Some(v_prop))));
                    let hm = HasMember {
                        name: id.clone(),
                        type_: prop_ty,
                        class_id: nast::ClassId_::CI(ast_defs::Id(id_pos.clone(), "".to_string())),
                        method: None,
                    };
                    env::add_tyvar_upper_bound(
                        None,
                        env,
                        *shadow_v,
                        InternalType::ConstraintType(mk_constraint_type((
                            typing_reason::none(),
                            ConstraintType_::ThasMember(hm),
                        ))),
                    );
                    Some(v_prop)
                }
                None => None,
            };
            let ty = mk((
                typing_reason::dynamic_prop(id_pos.clone()),
                Ty_::Tdynamic(result_shadow),
            ));
            (err_opt, (ty, vec![]), dflt_lval_mismatch.clone(), dflt_rval_mismatch.clone())
        }
        Ty_::Tany(_) => (
            None,
            (concrete_ty.clone(), vec![]),
            dflt_lval_mismatch.clone(),
            dflt_rval_mismatch.clone(),
        ),
        Ty_::Tnonnull => {
            let ty_reasons = if typing_reason::predicates::is_opaque_type_from_module(&r) {
                let r = r.clone();
                Lazy::new(move || typing_reason::to_string("This type is mixed", &r))
            } else {
                Lazy::new(Vec::new)
            };
            let ty_name = {
                let env = env.clone();
                let concrete_ty = concrete_ty.clone();
                Lazy::new(move || typing_print::error(None, &env, &concrete_ty))
            };
            let ty_err = typing_error::primary(primary::T::Top_member {
                pos: id_pos.clone(),
                name: id_str.clone(),
                ctxt: if read_context {
                    ReadOrWrite::read
                } else {
                    ReadOrWrite::write
                },
                kind: if args.is_method {
                    MethodOrProperty::method_
                } else {
                    MethodOrProperty::property
                },
                is_nullable: false,
                decl_pos: get_pos(&concrete_ty),
                ty_name,
                ty_reasons,
            });
            let ty_nothing = make_type::nothing(typing_reason::none());
            let lval_mismatch = Err((concrete_ty.clone(), ty_nothing));
            default(env, Some(lval_mismatch), None, Some(ty_err))
        }
        _ => {
            let ty_name = {
                let env = env.clone();
                let concrete_ty = concrete_ty.clone();
                Lazy::new(move || typing_print::error(None, &env, &concrete_ty))
            };
            let ty_err = typing_error::apply(
                typing_error::primary(primary::T::Non_object_member {
                    pos: id_pos.clone(),
                    ctxt: if read_context {
                        ReadOrWrite::read
                    } else {
                        ReadOrWrite::write
                    },
                    kind: if args.is_method {
                        NonObjectMemberKind::method_
                    } else {
                        NonObjectMemberKind::property
                    },
                    member_name: id_str.clone(),
                    ty_name,
                    decl_pos: get_pos(&concrete_ty),
                }),
                on_error.clone(),
            );
            let ty_nothing = make_type::nothing(typing_reason::none());
            let lval_mismatch = Err((concrete_ty.clone(), ty_nothing));
            default(env, Some(lval_mismatch), None, Some(ty_err))
        }
    }
}

fn obj_get_concrete_class(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    concrete_ty: Ty,
    id: &nast::Sid,
    reason: Reason,
    class_name: &str,
    params: &[Ty],
    on_error: &callback::T,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    match env::get_class(env, class_name) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
            let ty = make_type::nothing(typing_reason::missing_class(id_pos.clone()));
            (
                None,
                (ty, vec![]),
                Ok(concrete_ty),
                args.coerce_from_ty
                    .as_ref()
                    .map(|(_, _, ty)| Ok(ty.clone())),
            )
        }
        decl_entry::T::Found(class_info) => {
            let params: Vec<Ty> = if params.len() != cls::tparams(&class_info).len() {
                // We've already generated an arity error so just fill out params
                // with error types
                cls::tparams(&class_info)
                    .iter()
                    .map(|_| env::fresh_type_error(env, id_pos.clone()))
                    .collect()
            } else {
                params.to_vec()
            };
            let old_member_info = get_member(args.is_method, env, &class_info, id_str);
            let self_id = env::get_self_id(env).unwrap_or_default();
            let ancestor_tyargs: Option<Vec<DeclTy>> =
                match cls::get_ancestor(&class_info, &self_id) {
                    Some(self_class_type) => match self_class_type.node_ref() {
                        DeclTy_::Tapply(id_and_tyargs) => Some(id_and_tyargs.1.to_vec()),
                        _ => None,
                    },
                    None => {
                        let all_reqs = cls::all_ancestor_reqs(&class_info);
                        let filtered: Vec<Vec<DeclTy>> = all_reqs
                            .iter()
                            .filter_map(|req| match req.ty.node_ref() {
                                DeclTy_::Tapply(name_and_tyargs)
                                    if name_and_tyargs.0.id_ref().as_str() == self_id =>
                                {
                                    Some(name_and_tyargs.1.to_vec())
                                }
                                _ => None,
                            })
                            .collect();
                        filtered.into_iter().next()
                    }
                };

            let (member_info, shadowed) = match ancestor_tyargs {
                Some(tyargs) => {
                    // We look up the current context to see if there is a field/method with
                    // private visibility. If there is one, that one takes precedence
                    match env::get_self_class(env) {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                            (old_member_info.clone(), false)
                        }
                        decl_entry::T::Found(self_class) => {
                            match get_member(args.is_method, env, &self_class, id_str) {
                                Some(
                                    ce @ ClassElt {
                                        ce_visibility: CeVisibility::Vprivate(_),
                                        ..
                                    },
                                ) => {
                                    let ce = decl_instantiate::instantiate_ce(
                                        &decl_instantiate::make_subst(
                                            &cls::tparams(&self_class),
                                            &tyargs,
                                        ),
                                        &ce,
                                    );
                                    // if a trait T has a require class C constraint, and both T and C
                                    // define a private member with the same name, then the two members
                                    // are aliased, not shadowed.  In this case, self_class is the trait
                                    // and the ancestor is the required class.  We can set the `shadowed`
                                    // bit by checking if self_class is a class or trait, there is
                                    // no need to additionally check if the trait has a require class
                                    // attribute.
                                    (Some(ce), ast_defs::is_c_class(cls::kind(&self_class)))
                                }
                                _ => (old_member_info.clone(), false),
                            }
                        }
                    }
                }
                None => (old_member_info.clone(), false),
            };
            match member_info {
                None => obj_get_concrete_class_without_member_info(
                    args,
                    env,
                    concrete_ty,
                    id,
                    reason,
                    &class_info,
                    on_error,
                ),
                Some(member_info) => obj_get_concrete_class_with_member_info(
                    args,
                    env,
                    concrete_ty,
                    id,
                    &self_id,
                    shadowed,
                    class_name,
                    &class_info,
                    &params,
                    old_member_info,
                    member_info,
                ),
            }
        }
    }
}

fn obj_get_concrete_class_with_member_info(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    concrete_ty: Ty,
    id: &nast::Sid,
    self_id: &str,
    shadowed: bool,
    class_name: &str,
    class_info: &cls::T,
    params: &[Ty],
    old_member_info: Option<ClassElt>,
    member_info: ClassElt,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    let dflt_rval_mismatch: Option<TyMismatch> = args
        .coerce_from_ty
        .as_ref()
        .map(|(_, _, ty)| Ok(ty.clone()));
    let dflt_lval_mismatch: TyMismatch = Ok(concrete_ty.clone());
    let vis = member_info.ce_visibility.clone();
    // `ce_type = (lazy member_)`
    let member_: DeclTy = (*member_info.ce_type).clone();
    let ce_deprecated = member_info.ce_deprecated.clone();
    let ce_package_requirement = member_info.ce_package_requirement.clone();
    let mem_pos = decl_get_pos(&member_);

    // The elements of the list literal, evaluated right to left as in OCaml.
    let expr_tree_err = tvis::check_expression_tree_vis(id_pos.clone(), mem_pos.clone(), env, &vis);
    let parent_abstract_err = if args.is_parent_call && typing_defs::get_ce_abstract(&member_info) {
        Some(typing_error::primary(primary::T::Parent_abstract_call {
            meth_name: id_str.clone(),
            pos: id_pos.clone(),
            decl_pos: mem_pos.clone(),
        }))
    } else {
        None
    };
    let cross_package_err =
        tvis::check_cross_package(id_pos.clone(), &mem_pos, env, ce_package_requirement);
    let deprecated_err = tvis::check_deprecated(id_pos.clone(), mem_pos.clone(), env, ce_deprecated);
    let obj_access_err = typing_error::multiple_opt(tvis::check_obj_access(
        args.is_method,
        ast_defs::is_c_interface(cls::kind(class_info)),
        id_pos.clone(),
        mem_pos.clone(),
        typing_defs::get_ce_tests_bypass_visibility(&member_info),
        env,
        &vis,
    ));
    let ambiguous_err = old_member_info.and_then(|old_member_info| {
        if shadowed && member_info.ce_origin != old_member_info.ce_origin {
            // `let (lazy old_member) = old_member_info.ce_type`
            let old_member: DeclTy = (*old_member_info.ce_type).clone();
            Some(typing_error::primary(primary::T::Ambiguous_object_access {
                pos: id_pos.clone(),
                name: id_str.clone(),
                self_pos: decl_get_pos(&member_),
                vis: string_of_visibility(&old_member_info.ce_visibility).to_string(),
                subclass_pos: decl_get_pos(&old_member),
                class_self: self_id.to_string(),
                class_subclass: class_name.to_string(),
            }))
        } else {
            None
        }
    });
    let ty_err_opts: Vec<Option<typing_error::T>> = vec![
        ambiguous_err,
        obj_access_err,
        deprecated_err,
        cross_package_err,
        parent_abstract_err,
        expr_tree_err,
    ];

    let member_decl_ty: DeclTy = typing_enum::member_type(env, &member_info);
    let widen_this = this_appears_covariantly(true, env, &member_decl_ty);
    let ety_env = mk_ety_env(class_info, params, args.this_ty.clone());
    // `match deref member_decl_ty`; `node_ref` is called by its path so that
    // `ft` is a `&Box<_>` even while the type of `member_decl_ty` cannot be
    // inferred.
    let (lcl_ty_err_opt, member_ty, tal, et_enforced, lval_mismatch): (
        Option<typing_error::T>,
        Ty,
        Vec<tast::Targ>,
        Enforcement,
        TyMismatch,
    ) = match ty::decl::Ty::node_ref(&member_decl_ty) {
        DeclTy_::Tfun(ft) if args.is_method => {
            // We special case function types here to be able to pass explicit type
            // parameters.
            let (lclz_ty_err_opt, explicit_targs): (Option<typing_error::T>, Vec<tast::Targ>) =
                typing_phase::localize_targs(
                true,
                args.is_method,
                mem_pos.clone(),
                id_pos.clone(),
                strip_ns(id_str).to_string(),
                None,
                env,
                &ft.tparams,
                args.explicit_targs
                    .iter()
                    .map(|aast::Targ(_, hint)| hint.clone())
                    .collect(),
            );
            let ft: DeclFunType = typing_enforceability::compute_enforced_and_pessimize_fun_type(
                Some(class_info),
                env,
                (**ft).clone(),
            );
            let (ft1_ty_err_opt, ft1): (Option<typing_error::T>, FunType) = typing_phase::localize_ft(
                Some(typing_phase::MethodInstantiation {
                    use_name: strip_ns(id_str).to_string(),
                    use_pos: id_pos.clone(),
                    explicit_targs: explicit_targs.clone(),
                }),
                &ExpandEnv {
                    on_error: None,
                    ..ety_env.clone()
                },
                mem_pos.clone(),
                env,
                &ft,
            );
            let should_wrap = typing_defs::get_ce_support_dynamic_type(&member_info);
            let (ft_ty1, lval_mismatch): (Ty, TyMismatch) = {
                let lval_mismatch = if should_wrap {
                    // If this is supportdyn, suppress the Hole on the receiver
                    dflt_lval_mismatch.clone()
                } else {
                    // Phase.localize_ft will report an error, generated in
                    // Typing_generic_constraint.check_where_constraint,
                    // if we have a 4323
                    match &ft1_ty_err_opt {
                        Some(_) => Err((concrete_ty.clone(), make_type::nothing(typing_reason::none()))),
                        _ => dflt_lval_mismatch.clone(),
                    }
                };

                (
                    typing_dynamic::maybe_wrap_with_supportdyn(
                        should_wrap,
                        localize_decl_reason(&member_decl_ty),
                        ft1,
                    ),
                    lval_mismatch,
                )
            };
            let (ft_ty_err_opt, ft_ty) = if widen_this {
                let ety_env = ExpandEnv {
                    this_ty: args.this_ty_conjunct.clone(),
                    ..ety_env.clone()
                };
                let (ft2_ty_err_opt, ft2): (Option<typing_error::T>, FunType) = typing_phase::localize_ft(
                    Some(typing_phase::MethodInstantiation {
                        use_name: strip_ns(id_str).to_string(),
                        use_pos: id_pos.clone(),
                        explicit_targs: explicit_targs.clone(),
                    }),
                    &ExpandEnv {
                        on_error: None,
                        ..ety_env.clone()
                    },
                    mem_pos.clone(),
                    env,
                    &ft,
                );
                let ft_ty2: Ty = typing_dynamic::maybe_wrap_with_supportdyn(
                    should_wrap,
                    localize_decl_reason(&member_decl_ty),
                    ft2,
                );
                let ty: Ty = typing_intersection::intersect_list(
                    env,
                    localize_decl_reason(&member_decl_ty),
                    &[ft_ty1, ft_ty2],
                );
                // TODO: should we be taking the intersection of the errors?
                let ty_err_opt = option_merge(ft1_ty_err_opt, ft2_ty_err_opt, |e1, e2| {
                    typing_error::multiple(vec![e1, e2])
                });
                (ty_err_opt, ty)
            } else {
                (ft1_ty_err_opt, ft_ty1)
            };
            let ty_err_opt = option_merge(lclz_ty_err_opt, ft_ty_err_opt, typing_error::both);

            (
                ty_err_opt,
                ft_ty,
                explicit_targs,
                Enforcement::Unenforced,
                lval_mismatch,
            )
        }
        _ => {
            let is_xhp_attr = typing_defs::get_ce_xhp_attr(&member_info).is_some();
            let (et_enforced, et_type) = typing_enforceability::compute_enforced_and_pessimize_ty(
                Some(class_info),
                env,
                Some(is_xhp_attr),
                member_decl_ty.clone(),
            );
            let (lcl_ty_err_opt, member_ty): (Option<typing_error::T>, Ty) =
                typing_phase::localize(&ety_env, env, &et_type);
            // TODO(T52753871): same as for class_get
            (
                lcl_ty_err_opt,
                member_ty,
                vec![],
                et_enforced,
                dflt_lval_mismatch.clone(),
            )
        }
    };
    // TODO: iterate over the returned error rather than side effecting on
    // error evaluation
    //
    // `eff` closes over the environment as it is here; it is only used when
    // there is a `coerce_from_ty`, before the environment changes again, so it
    // is built in that branch.
    let (member_ty, coerce_ty_err_opt, rval_mismatch) = match &args.coerce_from_ty {
        None => (member_ty, None, dflt_rval_mismatch),
        Some((p, ur, ty)) => {
            let eff = {
                let env = env.clone();
                let mem_pos = mem_pos.clone();
                let id_str = id_str.clone();
                move || {
                    if tast::is_under_dynamic_assumptions(env.checked) {
                        typing_log::log_pessimise_prop(
                            &env,
                            &pos_or_decl::unsafe_to_raw_pos(mem_pos.clone()),
                            &id_str,
                        )
                    }
                }
            };
            // `Typing_error.Callback.(with_side_effect ~eff unify_error [@alert "-deprecated"])`
            let err = callback::with_side_effect(callback::unify_error(), eff);
            let lty: Ty = tutils::make_like_if_enforced(env, et_enforced, member_ty.clone());
            let coerce_ty_err_opt = typing_coercion::coerce_type(
                None,
                None,
                None,
                p.clone(),
                ur.clone(),
                env,
                ty.clone(),
                lty.clone(),
                et_enforced,
                err,
            );
            let coerce_ty_mismatch = match &coerce_ty_err_opt {
                None => Ok(ty.clone()),
                _ => Err((ty.clone(), member_ty.clone())),
            };
            (lty, coerce_ty_err_opt, Some(coerce_ty_mismatch))
        }
    };
    let ty_err_opt = typing_error::multiple_opt(
        std::iter::once(lcl_ty_err_opt)
            .chain(std::iter::once(coerce_ty_err_opt))
            .chain(ty_err_opts)
            .flatten()
            .collect(),
    );
    (ty_err_opt, (member_ty, tal), lval_mismatch, rval_mismatch)
}

fn obj_get_concrete_class_without_member_info(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    concrete_ty: Ty,
    id: &nast::Sid,
    reason: Reason,
    class_info: &cls::T,
    on_error: &callback::T,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    let dflt_rval_mismatch: Option<TyMismatch> = args
        .coerce_from_ty
        .as_ref()
        .map(|(_, _, ty)| Ok(ty.clone()));
    let dflt_lval_mismatch: TyMismatch = Ok(concrete_ty.clone());
    let default = |env: &mut Env,
                   lval_mismatch: Option<TyMismatch>,
                   rval_mismatch: Option<Option<TyMismatch>>,
                   ty_err_opt: Option<typing_error::T>|
     -> InternalResult {
        let lval_mismatch = lval_mismatch.unwrap_or_else(|| dflt_lval_mismatch.clone());
        let rval_mismatch = rval_mismatch.unwrap_or_else(|| dflt_rval_mismatch.clone());
        let ty = env::fresh_type_error(env, id_pos.clone());
        (ty_err_opt, (ty, vec![]), lval_mismatch, rval_mismatch)
    };
    if !args.is_method {
        let (lval_mismatch, ty_err_opt) = if !is_special_xhp_attribute(id_str) {
            let err = member_not_found(
                env,
                id_pos.clone(),
                args.is_method,
                class_info,
                id_str,
                &reason,
                on_error.clone(),
            );
            let ty_nothing = make_type::nothing(typing_reason::none());
            (Err((concrete_ty.clone(), ty_nothing)), Some(err))
        } else {
            (dflt_lval_mismatch.clone(), None)
        };
        default(env, Some(lval_mismatch), None, ty_err_opt)
    } else if id_str == sn::members::__CLONE {
        // Create a `public function __clone()[]: void {}` for classes that don't declare __clone
        let ft = FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: vec![],
            implicit_params: FunImplicitParams {
                capability: Capability::CapTy(make_type::intersection(
                    typing_reason::none(),
                    vec![],
                )),
            },
            ret: make_type::void(typing_reason::none()),
            flags: typing_defs_flags::fun::default(),
            instantiated: true,
        };
        (
            None,
            (mk((typing_reason::none(), Ty_::Tfun(std::rc::Rc::new(ft)))), vec![]),
            dflt_lval_mismatch.clone(),
            dflt_rval_mismatch.clone(),
        )
    } else {
        let ty_err = member_not_found(
            env,
            id_pos.clone(),
            args.is_method,
            class_info,
            id_str,
            &reason,
            on_error.clone(),
        );
        let ty_nothing = make_type::nothing(typing_reason::none());
        default(
            env,
            Some(Err((concrete_ty.clone(), ty_nothing))),
            None,
            Some(ty_err),
        )
    }
}

fn nullable_obj_get(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    ety1: &Ty,
    id: &nast::Sid,
    on_error: &callback::T,
    read_context: bool,
    ty: Ty,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    let (rcv_is_option, rcv_is_nothing) = match get_node(ety1) {
        Ty_::Toption(inner) => match get_node(inner) {
            Ty_::Tnonnull => (false, true),
            _ => (true, false),
        },
        _ => (false, false),
    };

    match &args.nullsafe {
        Some(p1) => {
            let (ty_errs, (method_, tal), lval_mismatch, rval_mismatch) =
                obj_get_inner(args, env, ty, id, on_error);
            let ty = make_nullable_member_type(env, args.is_method, id_pos, p1, method_);
            (ty_errs, (ty, tal), lval_mismatch, rval_mismatch)
        }
        None if rcv_is_option => {
            // Try to type this as though it were nullsafe
            let (_ty_errs, (method_, tal), lval_mismatch, rval_mismatch) =
                obj_get_inner(args, env, ty.clone(), id, on_error);
            let r = get_reason(ety1).clone();
            // If this _had_ been a nullsafe access and we would have reported no error
            // we special case the error and type mismatch here to get better
            // suggested types in holes
            let ty_errs = typing_error::primary(primary::T::Null_member {
                pos: id_pos.clone(),
                obj_pos_opt: Some(args.obj_pos.clone()),
                member_name: id_str.clone(),
                reason: Lazy::new(move || messages(typing_reason::to_string("This can be null", &r))),
                kind: if args.is_method {
                    MethodOrProperty::method_
                } else {
                    MethodOrProperty::property
                },
                ctxt: if read_context {
                    ReadOrWrite::read
                } else {
                    ReadOrWrite::write
                },
            });
            let lval_mismatch = match lval_mismatch {
                Ok(_) => Err((ety1.clone(), ty)),
                Err((_, suggest)) => Err((ety1.clone(), suggest)),
            };
            (Some(ty_errs), (method_, tal), lval_mismatch, rval_mismatch)
        }
        None => {
            let (ty_expect, ty_err) = {
                let r = get_reason(ety1).clone();
                if rcv_is_nothing {
                    let ty_reasons = if typing_reason::predicates::is_opaque_type_from_module(&r) {
                        let r = r.clone();
                        Lazy::new(move || typing_reason::to_string("This type is mixed", &r))
                    } else {
                        Lazy::new(Vec::new)
                    };
                    let ty_name = {
                        let env = env.clone();
                        let ety1 = ety1.clone();
                        Lazy::new(move || typing_print::error(None, &env, &ety1))
                    };
                    let ty_err = typing_error::primary(primary::T::Top_member {
                        pos: id_pos.clone(),
                        name: id_str.clone(),
                        ctxt: if read_context {
                            ReadOrWrite::read
                        } else {
                            ReadOrWrite::write
                        },
                        kind: if args.is_method {
                            MethodOrProperty::method_
                        } else {
                            MethodOrProperty::property
                        },
                        is_nullable: true,
                        decl_pos: typing_reason::to_pos(&r),
                        ty_name,
                        ty_reasons,
                    });
                    (make_type::nothing(typing_reason::none()), ty_err)
                } else {
                    let ty_err = typing_error::primary(primary::T::Null_member {
                        pos: id_pos.clone(),
                        obj_pos_opt: Some(args.obj_pos.clone()),
                        member_name: id_str.clone(),
                        reason: Lazy::new(move || {
                            messages(typing_reason::to_string("This can be null", &r))
                        }),
                        kind: if args.is_method {
                            MethodOrProperty::method_
                        } else {
                            MethodOrProperty::property
                        },
                        ctxt: if read_context {
                            ReadOrWrite::read
                        } else {
                            ReadOrWrite::write
                        },
                    });
                    (make_type::nothing(typing_reason::none()), ty_err)
                }
            };
            let ty = env::fresh_type_error(env, id_pos.clone());
            (
                Some(ty_err),
                (ty, vec![]),
                Err((ety1.clone(), ty_expect)),
                args.coerce_from_ty
                    .as_ref()
                    .map(|(_, _, ty)| Ok(ty.clone())),
            )
        }
    }
}

/// Helper method for obj_get that decomposes the type ty1.
/// The additional parameter this_ty represents the type that will be substitued
/// for `this` in the method signature.
///
/// If ty1 is an intersection type, we distribute the member access through the
/// conjuncts but maintain the intersection type for this_ty. For example,
/// a call on (T & I & J) will recurse on T, I and J but with this_ty = (T & I & J),
/// so that we don't "lose" information when substituting for `this`.
///
/// In contrast, if ty1 is a union type, we recurse on the disjuncts but pass these
/// through to this_ty, as the member access must be valid for each disjunct
/// separately. Likewise for nullables (special case of union).
fn obj_get_inner(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    receiver_ty: Ty,
    id: &nast::Sid,
    on_error: &callback::T,
) -> InternalResult {
    let ast_defs::Id(id_pos, id_str) = id;
    log_obj_get(env, ObjGetHelper::Inner, id, &receiver_ty, &args.this_ty);
    let ety1_ = env::expand_type(env, receiver_ty.clone());
    let was_var = typing_defs::is_tyvar(&ety1_);
    let dflt_rval_mismatch: Option<TyMismatch> = args
        .coerce_from_ty
        .as_ref()
        .map(|(_, _, ty)| Ok(ty.clone()));
    let (expand_ty_err_opt, ety1): (Option<typing_error::T>, Ty) = if args.is_method {
        typing_solver::expand_type_and_solve(
            env,
            None,
            "an object",
            args.obj_pos.clone(),
            receiver_ty.clone(),
        )
    } else {
        typing_solver::expand_type_and_narrow(
            env,
            None,
            None,
            None,
            "an object",
            |env: &mut Env, ty: Ty| {
                widen_class_for_obj_get(args.is_method, args.nullsafe.as_ref(), id_str, env, ty)
            },
            args.obj_pos.clone(),
            receiver_ty.clone(),
        )
    };
    let ety1: Ty = if was_var {
        expr_dep_ty::make_with_dep_kind(env, args.dep_kind.clone(), ety1)
    } else {
        ety1
    };
    // The local `nullable_obj_get ~read_context ty`, which closes over the
    // environment as it is here; the branches that call it have not changed
    // it since.
    let local_nullable_obj_get = |env: &mut Env,
                                  expand_ty_err_opt: Option<typing_error::T>,
                                  read_context: bool,
                                  ty: Ty|
     -> InternalResult {
        merge_ty_err(
            expand_ty_err_opt,
            nullable_obj_get(
                &ObjGetArgs {
                    this_ty: ty.clone(),
                    this_ty_conjunct: ty.clone(),
                    ..args.clone()
                },
                env,
                &ety1,
                id,
                on_error,
                read_context,
                ty,
            ),
        )
    };
    // coerce_from_ty is used to store the source type for an assignment, so it
    // is a useful marker for whether we're reading or writing
    let read_context = args.coerce_from_ty.is_none();
    let r = get_reason(&ety1).clone();
    match get_node(&ety1) {
        Ty_::Tunion(tyl) => {
            // Filter out null elements
            let is_null = |ty: &Ty| {
                // The OCaml drops the environment that `strip_supportdyn` returns.
                let (_, ty): (bool, Ty) = tutils::strip_supportdyn(&mut env.clone(), ty.clone());
                matches!(get_node(&ty), Ty_::Tprim(ast_defs::Tprim::Tnull))
            };
            let (tyl_null, tyl_nonnull): (Vec<Ty>, Vec<Ty>) =
                tyl.iter().cloned().partition(|ty| is_null(ty));
            if tyl_null.is_empty() {
                merge_ty_err(
                    expand_ty_err_opt,
                    obj_get_inner_union(args, env, on_error, id, r, tyl),
                )
            } else {
                local_nullable_obj_get(
                    env,
                    expand_ty_err_opt,
                    read_context,
                    make_type::union(r, tyl_nonnull),
                )
            }
        }
        Ty_::Tintersection(tyl) => {
            let (is_nonnull, subty_err_opt): (bool, Option<typing_error::T>) = if args.is_nonnull {
                (true, None)
            } else {
                typing_solver::is_sub_type(
                    env,
                    &receiver_ty,
                    &make_type::nonnull(typing_reason::none()),
                )
            };
            let ty_err_opt = option_merge(expand_ty_err_opt, subty_err_opt, typing_error::both);
            merge_ty_err(
                ty_err_opt,
                obj_get_inner_intersection(
                    &ObjGetArgs {
                        is_nonnull,
                        ..args.clone()
                    },
                    env,
                    on_error,
                    id,
                    r,
                    tyl,
                ),
            )
        }
        Ty_::Tdependent(_, ty) => merge_ty_err(
            expand_ty_err_opt,
            obj_get_inner(args, env, ty.clone(), id, on_error),
        ),
        Ty_::Tnewtype(name, tyl, _) => {
            let ty: Ty = tutils::get_newtype_super(env, r, name, tyl);
            // Unfortunately the bound on a newtype may itself be a type variable
            let (_ty_err_opt, ty): (Option<typing_error::T>, Ty) =
                typing_solver::expand_type_and_solve(env, None, "an object", args.obj_pos.clone(), ty);
            merge_ty_err(expand_ty_err_opt, obj_get_inner(args, env, ty, id, on_error))
        }
        Ty_::Tgeneric(name) if !args.seen.contains(name) => {
            let args = ObjGetArgs {
                seen: args.seen.update(name.clone()),
                ..args.clone()
            };
            let tyl: Vec<Ty> =
                tutils::get_concrete_supertypes(None, None, None, true, env, ety1.clone());
            match tyl.as_slice() {
                [] => {
                    // OCaml `let ... and ...`
                    let ctxt = if read_context {
                        ReadOrWrite::read
                    } else {
                        ReadOrWrite::write
                    };
                    let kind = if args.is_method {
                        NonObjectMemberKind::method_
                    } else {
                        NonObjectMemberKind::property
                    };
                    let ty_name = {
                        let env = env.clone();
                        let ety1 = ety1.clone();
                        Lazy::new(move || typing_print::error(None, &env, &ety1))
                    };
                    let ty_err = typing_error::apply(
                        typing_error::primary(primary::T::Non_object_member {
                            pos: id_pos.clone(),
                            ctxt,
                            kind,
                            member_name: id_str.clone(),
                            ty_name,
                            decl_pos: typing_reason::to_pos(&r),
                        }),
                        on_error.clone(),
                    );
                    let ty_err_opt =
                        option_merge(expand_ty_err_opt, Some(ty_err), typing_error::both);
                    let ty_nothing = make_type::nothing(typing_reason::none());
                    let lval_mismatch = Err((receiver_ty.clone(), ty_nothing));
                    let ty = env::fresh_type_error(env, id_pos.clone());
                    (ty_err_opt, (ty, vec![]), lval_mismatch, dflt_rval_mismatch)
                }
                _ => {
                    let ty: Ty = typing_intersection::intersect_list(env, r, &tyl);
                    let ty: Ty = if args.is_nonnull {
                        typing_intersection::intersect_with_nonnull(
                            env,
                            pos_or_decl::of_raw_pos(args.obj_pos.clone()),
                            ty,
                        )
                    } else {
                        ty
                    };
                    merge_ty_err(expand_ty_err_opt, obj_get_inner(&args, env, ty, id, on_error))
                }
            }
        }
        Ty_::Toption(ty) => local_nullable_obj_get(env, expand_ty_err_opt, read_context, ty.clone()),
        Ty_::Tprim(ast_defs::Tprim::Tnull) => {
            let ty = mk((r, Ty_::Tunion(vec![])));
            local_nullable_obj_get(env, expand_ty_err_opt, read_context, ty)
        }
        // We are trying to access a member through a value of unknown type
        Ty_::Tvar(_) => {
            let ty_err_opt = if tutils::is_tyvar_error(env, &ety1) {
                None
            } else {
                Some(typing_error::primary(primary::T::Unknown_object_member {
                    elt: if args.is_method {
                        MethOrProp::meth
                    } else {
                        MethOrProp::prop
                    },
                    member_name: id_str.clone(),
                    pos: id_pos.clone(),
                    reason: Lazy::new(move || messages(typing_reason::to_string("It is unknown", &r))),
                }))
            };
            let ty_err_opt = option_merge(expand_ty_err_opt, ty_err_opt, typing_error::both);
            let ty_nothing = make_type::nothing(typing_reason::none());
            let ty = env::fresh_type_error(env, id_pos.clone());
            (
                ty_err_opt,
                (ty, vec![]),
                Err((receiver_ty, ty_nothing)),
                dflt_rval_mismatch,
            )
        }
        _ => merge_ty_err(
            expand_ty_err_opt,
            obj_get_concrete_ty(args, env, ety1.clone(), id, on_error),
        ),
    }
}

/// The OCaml folds over `tys`, consing each result onto its lists: the lists
/// end up in the reverse order of `tys`, and the code below works on them in
/// that order (the union of the types, the union of the errors, the choice
/// of the type arguments).
fn obj_get_inner_union(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    on_error: &callback::T,
    id: &nast::Sid,
    reason: Reason,
    tys: &[Ty],
) -> InternalResult {
    let mut ty_errs: Vec<Option<typing_error::T>> = vec![];
    let mut resultl: Vec<(Ty, Vec<tast::Targ>)> = vec![];
    let mut lval_mismatches: Vec<TyMismatch> = vec![];
    let mut rval_mismatch_opts: Vec<Option<TyMismatch>> = vec![];
    for ty in tys {
        let (ty_err, res, lval_mismatch, rval_mismatch_opt) = obj_get_inner(
            &ObjGetArgs {
                this_ty: ty.clone(),
                this_ty_conjunct: ty.clone(),
                ..args.clone()
            },
            env,
            ty.clone(),
            id,
            on_error,
        );
        // Preserve outer reason on dynamic
        let res = if typing_defs::is_dynamic(&res.0) {
            (with_reason(res.0, reason.clone()), res.1)
        } else {
            res
        };
        ty_errs.push(ty_err);
        resultl.push(res);
        lval_mismatches.push(lval_mismatch);
        rval_mismatch_opts.push(rval_mismatch_opt);
    }
    ty_errs.reverse();
    resultl.reverse();
    lval_mismatches.reverse();
    rval_mismatch_opts.reverse();
    let ty_err_opt = typing_error::union_opt(ty_errs.into_iter().flatten().collect());
    let lval_mismatch = mk_mismatch_union(env, fold_mismatches(lval_mismatches));
    let rval_mismatch = match fold_mismatch_opts(rval_mismatch_opts) {
        None => None,
        Some(res) => {
            let r = mk_mismatch_union(env, res);
            Some(r)
        }
    };
    // TODO: decide what to do about methods with differing generic arity.
    // See T55414751
    let tal = list_max_elt(
        resultl.iter().map(|(_, tal)| tal.clone()).collect(),
        |a: &Vec<tast::Targ>, b: &Vec<tast::Targ>| a.len().cmp(&b.len()),
    )
    .unwrap_or_default();
    let tyl: Vec<Ty> = resultl.into_iter().map(|(ty, _)| ty).collect();
    let ty: Ty = typing_union::union_list(env, None, reason, &tyl);
    (ty_err_opt, (ty, tal), lval_mismatch, rval_mismatch)
}

fn obj_get_inner_intersection(
    args: &ObjGetArgs<'_>,
    env: &mut Env,
    on_error: &callback::T,
    id: &nast::Sid,
    reason: Reason,
    tys: &[Ty],
) -> InternalResult {
    #[allow(clippy::type_complexity)]
    let (ty_err_opt, res): (
        Option<typing_error::T>,
        Vec<((Ty, Vec<tast::Targ>), TyMismatch, Option<TyMismatch>)>,
    ) = tutils::run_on_intersection_with_ty_err(
        env,
        |env: &mut Env, ty: &Ty| {
            let (ty_err_opt, res, lval_mismatch, rval_mismatch) = obj_get_inner(
                &ObjGetArgs {
                    this_ty_conjunct: ty.clone(),
                    ..args.clone()
                },
                env,
                ty.clone(),
                id,
                on_error,
            );
            (ty_err_opt, (res, lval_mismatch, rval_mismatch))
        },
        tys,
    );
    // `List.unzip3`
    let mut resultl: Vec<(Ty, Vec<tast::Targ>)> = vec![];
    let mut lval_mismatches: Vec<TyMismatch> = vec![];
    let mut rval_mismatch_opts: Vec<Option<TyMismatch>> = vec![];
    for (res, lval_mismatch, rval_mismatch) in res {
        resultl.push(res);
        lval_mismatches.push(lval_mismatch);
        rval_mismatch_opts.push(rval_mismatch);
    }

    let lval_mismatch = mk_mismatch_intersection(env, fold_mismatches(lval_mismatches));
    let rval_mismatch = match fold_mismatch_opts(rval_mismatch_opts) {
        None => None,
        Some(res) => {
            let err = mk_mismatch_intersection(env, res);
            Some(err)
        }
    };
    // TODO: decide what to do about methods with differing generic arity.
    // See T55414751
    let tal = match resultl.first() {
        None => vec![],
        Some((_, tal)) => tal.clone(),
    };
    let tyl: Vec<Ty> = resultl.into_iter().map(|(ty, _)| ty).collect();
    let ty: Ty = typing_intersection::intersect_list(env, reason, &tyl);
    (ty_err_opt, (ty, tal), lval_mismatch, rval_mismatch)
}

/// Look up the type of the property or method id in the type receiver_ty of the
/// receiver and use the function k to postprocess the result.
/// Return any fresh type variables that were substituted for generic type
/// parameters in the type of the property or method.
///
/// Essentially, if receiver_ty is a concrete type, e.g., class C, then k is applied
/// to the type of the property id in C; and if receiver_ty is an unresolved type,
/// e.g., a union of classes (C1 | ... | Cn), then k is applied to the type
/// of the property id in each Ci and the results are collected into an
/// unresolved type.
fn obj_get_with_mismatches_helper(
    obj_pos: Pos,
    is_method: bool,
    nullsafe: Option<Pos>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    explicit_targs: &[nast::Targ],
    class_id: &nast::ClassId_,
    member_id: &nast::Sid,
    on_error: callback::T,
    parent_ty: Option<Ty>,
    env: &mut Env,
    receiver_ty: Ty,
) -> WithMismatches {
    typing_log::log_with_level(env, "obj_get", 1, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(obj_pos.clone()),
            env,
            &[LogStructure::LogHead(
                format!("obj_get (member_id: {})", member_id.1),
                vec![LogStructure::LogType(
                    "receiver_ty".to_string(),
                    receiver_ty.clone(),
                )],
            )],
        )
    });
    let (e1, receiver_ty): (Option<typing_error::T>, Ty) = if is_method {
        typing_solver::expand_type_and_solve(env, None, "an object", obj_pos.clone(), receiver_ty)
    } else {
        typing_solver::expand_type_and_narrow(
            env,
            None,
            None,
            None,
            "an object",
            |env: &mut Env, ty: Ty| {
                widen_class_for_obj_get(is_method, nullsafe.as_ref(), &member_id.1, env, ty)
            },
            obj_pos.clone(),
            receiver_ty,
        )
    };

    // We will substitute `this` in the function signature with `this_ty`. But first,
    // transform it according to the dependent kind dep_kind that was derived from the
    // class_id in the original call to obj_get. See Typing_dependent_type.ml for
    // more details.
    let dep_kind: (Reason, expr_dep_ty::Dep) =
        expr_dep_ty::from_cid(env, get_reason(&receiver_ty).clone(), class_id);
    let receiver_ty: Ty = expr_dep_ty::make_with_dep_kind(env, dep_kind.clone(), receiver_ty);
    let receiver_or_parent_ty = match parent_ty {
        Some(ty) => ty,
        None => receiver_ty.clone(),
    };
    // `Nast.equal_class_id_ class_id Aast.CIparent`
    let is_parent_call = matches!(class_id, nast::ClassId_::CIparent);
    let args = ObjGetArgs {
        is_method,
        nullsafe,
        obj_pos: obj_pos.clone(),
        explicit_targs,
        coerce_from_ty,
        is_nonnull: false,
        is_parent_call,
        dep_kind,
        this_ty: receiver_ty.clone(),
        this_ty_conjunct: receiver_ty.clone(),
        seen: im::OrdSet::new(),
    };
    let (e2, ty, lval_err, rval_err_opt) = {
        let (e2, ty, lvarl_err, rval_err_opt) =
            obj_get_inner(&args, env, receiver_or_parent_ty.clone(), member_id, &on_error);
        // If we failed on a static receiver type in SDT dynamic method check, try again
        // on dynamic, if the receiver type supports dynamic.
        if e2.is_some()
            && tast::is_under_dynamic_assumptions(env.checked)
            && !typing_defs::is_dynamic(&receiver_or_parent_ty)
            && tutils::is_sub_type(
                env,
                &receiver_or_parent_ty,
                &make_type::dynamic(typing_reason::none()),
            )
        {
            obj_get_inner(
                &args,
                env,
                make_type::dynamic(typing_reason::witness(obj_pos.clone())),
                member_id,
                &on_error,
            )
        } else {
            (e2, ty, lvarl_err, rval_err_opt)
        }
    };
    let from_res = |res: TyMismatch| match res {
        Ok(_) => None,
        Err(tys) => Some(tys),
    };
    let ty_err_opt = option_merge(e1, e2, typing_error::both);
    let lval_err_opt = from_res(lval_err);
    let rval_err_opt = rval_err_opt.and_then(from_res);
    (ty_err_opt, ty, lval_err_opt, rval_err_opt)
}

/// As [`obj_get`] but also return the types at which
/// - we encountered an error based on the receiver's type, if at all
/// - coercion of `coerce_from_ty` to the object type failed, if at all
///
/// When the first attempt fails on a method, the OCaml goes on from the
/// environment it was given (not the one the attempt returned) and returns
/// the environment of the attempt it keeps: the environment is saved before
/// the first attempt and restored accordingly.
pub fn obj_get_with_mismatches(
    obj_pos: Pos,
    is_method: bool,
    nullsafe: Option<Pos>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    explicit_targs: &[nast::Targ],
    class_id: &nast::ClassId_,
    member_id: &nast::Sid,
    on_error: callback::T,
    parent_ty: Option<Ty>,
    env: &mut Env,
    receiver_ty: Ty,
) -> WithMismatches {
    // Only the method case goes back to this environment.
    let env_before = if is_method { Some(env.clone()) } else { None };
    let (ty_err_opt0, (fty0, tal0), lval_err_opt0, rval_err_opt0) = obj_get_with_mismatches_helper(
        obj_pos.clone(),
        is_method,
        nullsafe.clone(),
        coerce_from_ty.clone(),
        explicit_targs,
        class_id,
        member_id,
        on_error.clone(),
        parent_ty.clone(),
        env,
        receiver_ty.clone(),
    );
    match env_before {
        Some(env_before) if ty_err_opt0.is_some() => {
            // Under Sound Dynamic, we might be calling through a receiver whose like-type
            // instantiation doesn't satisfy where constraints on the method. For example,
            // class ExpectObj<T> { public function foo() where T as Container<mixed> ...}
            // might be called through ExpectObj<~vec<int>> for which ~vec<int> is not a
            // subtype of Container<mixed>.
            //
            // But by first like-pushing to a supertype, i.e. ~ExpectObj<vec<int>>, we can
            // type-check the call. We do this by attempting a subtype
            //   ExpectObj<~vec<int>> <: ~ExpectObj<#0> <: suppordyn<dynamic>
            // where #0 is a fresh type variable. Because we are calling through a like, we
            // propagate this to the function type of the method.
            //
            // Compare SDT calling for top-level functions e.g.
            //   function foo<T>(ExpectObj<T>) where T as Container<mixed>
            let env0 = std::mem::replace(env, env_before);
            fn freshen_receiver_ty_and_assert_subtype(obj_pos: &Pos, env: &mut Env, ty: Ty) -> Ty {
                let ty = env::expand_type(env, ty);
                let r = get_reason(&ty).clone();
                // Now produce fresh type variables for type arguments
                match get_node(&ty) {
                    Ty_::Tclass(id, exact, tyargs) => {
                        let freshened_tyargs: Vec<Ty> = tyargs
                            .iter()
                            .map(|_ty| env::fresh_type_invariant(env, obj_pos.clone()))
                            .collect();
                        let freshened_receiver_ty =
                            mk((r.clone(), Ty_::Tclass(id.clone(), exact.clone(), freshened_tyargs)));
                        let like_receiver_ty =
                            make_type::locl_like(r.clone(), freshened_receiver_ty.clone());
                        // Perform the two subtype assertions mentioned in the comment above. We
                        // expect these to succeed because the type variables are unconstrained
                        let _ty_err3: Option<typing_error::T> = typing_ops::sub_type(
                            obj_pos.clone(),
                            Ureason::URnone,
                            env,
                            freshened_receiver_ty.clone(),
                            make_type::supportdyn(r.clone(), make_type::mixed(r.clone())),
                            callback::unify_error(),
                        );
                        let _ty_err2: Option<typing_error::T> = typing_ops::sub_type(
                            obj_pos.clone(),
                            Ureason::URnone,
                            env,
                            ty.clone(),
                            like_receiver_ty,
                            callback::unify_error(),
                        );
                        freshened_receiver_ty
                    }
                    Ty_::Tunion(tyl) => {
                        let tyl: Vec<Ty> = tyl
                            .iter()
                            .map(|ty| freshen_receiver_ty_and_assert_subtype(obj_pos, env, ty.clone()))
                            .collect();
                        mk((r, Ty_::Tunion(tyl)))
                    }
                    _ => ty,
                }
            }
            // First strip off top-level like, so we can see the class (or union of classes) underneath
            let stripped_receiver_ty = typing_dynamic_utils::strip_dynamic(env, receiver_ty);
            let freshened_receiver_ty =
                freshen_receiver_ty_and_assert_subtype(&obj_pos, env, stripped_receiver_ty);
            let (ty_err_opt, (fty, tal), lval_err_opt, rval_err_opt) =
                obj_get_with_mismatches_helper(
                    obj_pos,
                    is_method,
                    nullsafe,
                    coerce_from_ty,
                    explicit_targs,
                    class_id,
                    member_id,
                    on_error,
                    parent_ty,
                    env,
                    freshened_receiver_ty,
                );
            // If calling through both non-like *and* like types had errors, pick the non-like
            // type version because the messages are likely to be more comprehensible
            if ty_err_opt.is_some() {
                *env = env0;
                (ty_err_opt0, (fty0, tal0), lval_err_opt0, rval_err_opt0)
            } else {
                // Otherwise, use the result from the like-type receiver and add
                // a like to the function type
                let fty = make_type::locl_like(get_reason(&fty).clone(), fty);
                (ty_err_opt, (fty, tal), lval_err_opt, rval_err_opt)
            }
        }
        // `Option.is_none ty_err_opt0 || not is_method`
        _ => (ty_err_opt0, (fty0, tal0), lval_err_opt0, rval_err_opt0),
    }
}

/// Check member access, both static and instance.
///   [obj_pos] is position of the object expression i.e. expr in expr->m
///   [is_method] is true if this is a method invocation rather than property access
///   [nullsafe] is Some p for null-safe calls such as expr?->m
///   [parent_ty] is the type of the parent, in the case of a parent call (class_id = CIparent)
///   [explicit_targs]  is a list of explicit type argument expressions, if present
///   [member_id] is positioned identifier for the member i.e. m in expr->m
///   [on_error] is an error callback
pub fn obj_get(
    obj_pos: Pos,
    is_method: bool,
    nullsafe: Option<Pos>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    explicit_targs: &[nast::Targ],
    class_id: &nast::ClassId_,
    member_id: &nast::Sid,
    on_error: callback::T,
    parent_ty: Option<Ty>,
    env: &mut Env,
    receiver_ty: Ty,
) -> (Option<typing_error::T>, (Ty, Vec<tast::Targ>)) {
    let (ty_err_opt, ty, _lval_err_opt, _rval_err_opt) = obj_get_with_mismatches(
        obj_pos,
        is_method,
        nullsafe,
        coerce_from_ty,
        explicit_targs,
        class_id,
        member_id,
        on_error,
        parent_ty,
        env,
        receiver_ty,
    );
    (ty_err_opt, ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prim(p: ast_defs::Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn names(tys: &[Ty]) -> Vec<String> {
        tys.iter()
            .map(|ty| match get_node(ty) {
                Ty_::Tprim(ast_defs::Tprim::Tint) => "int".to_string(),
                Ty_::Tprim(ast_defs::Tprim::Tnum) => "num".to_string(),
                Ty_::Tprim(ast_defs::Tprim::Tbool) => "bool".to_string(),
                Ty_::Tprim(ast_defs::Tprim::Tfloat) => "float".to_string(),
                _ => "?".to_string(),
            })
            .collect()
    }

    #[test]
    fn fold_mismatches_all_ok_reverses() {
        let int = prim(ast_defs::Tprim::Tint);
        let num = prim(ast_defs::Tprim::Tnum);
        match fold_mismatches(vec![Ok(int), Ok(num)]) {
            Ok(xs) => assert_eq!(names(&xs), vec!["num", "int"]),
            Err(_) => panic!("expected Ok"),
        }
    }

    #[test]
    fn fold_mismatches_mixed() {
        // [Ok int; Error (num, bool); Ok float]
        //   Ok [] -> Ok [int] -> Error ([num; int], [bool; int])
        //   -> Error ([float; num; int], [float; bool; int])
        let int = prim(ast_defs::Tprim::Tint);
        let num = prim(ast_defs::Tprim::Tnum);
        let bool_ = prim(ast_defs::Tprim::Tbool);
        let float = prim(ast_defs::Tprim::Tfloat);
        match fold_mismatches(vec![Ok(int), Err((num, bool_)), Ok(float)]) {
            Ok(_) => panic!("expected Error"),
            Err((xs, ys)) => {
                assert_eq!(names(&xs), vec!["float", "num", "int"]);
                assert_eq!(names(&ys), vec!["float", "bool", "int"]);
            }
        }
    }

    #[test]
    fn fold_mismatch_opts_needs_all() {
        let int = prim(ast_defs::Tprim::Tint);
        assert!(fold_mismatch_opts(vec![Some(Ok(int.clone())), None]).is_none());
        assert!(fold_mismatch_opts(vec![Some(Ok(int))]).is_some());
        assert!(fold_mismatch_opts(vec![]).is_some());
    }

    #[test]
    fn list_max_elt_keeps_first_of_ties() {
        let l = vec![(1, 'a'), (3, 'b'), (2, 'c'), (3, 'd')];
        assert_eq!(list_max_elt(l, |a, b| a.0.cmp(&b.0)), Some((3, 'b')));
        assert_eq!(list_max_elt(Vec::<(i32, char)>::new(), |a, b| a.0.cmp(&b.0)), None);
    }

    #[test]
    fn special_xhp_attribute_prefixes() {
        assert!(is_special_xhp_attribute(":data-foo"));
        assert!(is_special_xhp_attribute(":aria-label"));
        assert!(is_special_xhp_attribute(":data-"));
        assert!(!is_special_xhp_attribute(":data"));
        assert!(!is_special_xhp_attribute("data-foo"));
        assert!(!is_special_xhp_attribute(""));
        // Byte 6 is inside `é` (bytes 5 and 6): must not panic.
        assert!(!is_special_xhp_attribute("aaaaaé"));
        assert!(!is_special_xhp_attribute("ééé:data-"));
    }

    #[test]
    fn option_merge_cases() {
        assert_eq!(option_merge(None, None, |a: i32, b| a + b), None);
        assert_eq!(option_merge(Some(1), None, |a, b| a + b), Some(1));
        assert_eq!(option_merge(None, Some(2), |a, b| a + b), Some(2));
        assert_eq!(option_merge(Some(1), Some(2), |a, b| a * 10 + b), Some(12));
    }
}
