// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 11871-12507): module `Class_id`.
//! See `hh/PORTING.md`.
//!
//! - `classname_expr_error` is [`ClassnameExprError`].
//! - `class_expr` returns `(tal, te, ty)`, `class_id_for_new` and
//!   `instantiable_cid` return `NewableClassInfo` (the prelude's
//!   `newable_class_info` without the environment); `this_for_method` returns
//!   the type.
//! - The polymorphic variant that `class_expr` computes for the package check
//!   is `typing_packages::CheckReason`, which `typing_visibility` takes.

use std::collections::VecDeque;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics;
// module Cls = Folded_class
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::rt::ocaml_option;
use crate::tast;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_defs::*;
// module ExprDepTy = Typing_dependent_type.ExprDepTy
use crate::typing_dependent_type::expr_dep_ty;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error::primary::package::TargetSymbolSpec;
use crate::typing_error_utils;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
use crate::typing_packages::CheckReason;
// module Phase = Typing_phase
use crate::typing_phase as phase;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;

/// `classname_expr_error`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassnameExprError {
    Pass,
    Warning,
    Error,
}

/// Resolve class expressions:
///     self    CIself       lexically enclosing class
///     parent  CIparent     lexically enclosing `extends` class
///     static  CIstatic     late-static-bound class (i.e. runtime receiver)
///     <id>    CI id        literal class name
///     <expr>  CIexpr expr  expression that evaluates to an object or classname
pub(crate) fn class_expr(
    check_targs_integrity: Option<bool>,
    attribute_check_policy: Option<expr::AttributeCheckPolicy>,
    exact: Option<Exact>,
    check_explicit_targs: Option<bool>,
    inside_nameof: Option<bool>,
    is_const: Option<bool>,
    is_classptr: Option<bool>,
    is_attribute: Option<bool>,
    is_catch: Option<bool>,
    require_class_ptr: Option<ClassnameExprError>,
    env: &mut Env,
    tal: &[nast::Targ],
    aast::ClassId(_, p, cid_): &nast::ClassId,
) -> (Vec<tast::Targ>, tast::ClassId, Ty) {
    let check_targs_integrity = check_targs_integrity.unwrap_or(false);
    let attribute_check_policy =
        attribute_check_policy.unwrap_or(expr::AttributeCheckPolicy::CheckAll);
    let exact = exact.unwrap_or_else(nonexact);
    let check_explicit_targs = check_explicit_targs.unwrap_or(false);
    let inside_nameof = inside_nameof.unwrap_or(false);
    let is_const = is_const.unwrap_or(false);
    let is_classptr = is_classptr.unwrap_or(false);
    let is_attribute = is_attribute.unwrap_or(false);
    let is_catch = is_catch.unwrap_or(false);
    let require_class_ptr = require_class_ptr.unwrap_or(ClassnameExprError::Pass);
    let make_result = |tal: Vec<tast::Targ>, te: aast::ClassId_<Ty, tast::SavedEnv>, ty: Ty| {
        (tal, aast::ClassId(ty.clone(), p.clone(), te), ty)
    };
    match cid_ {
        aast::ClassId_::CIparent => match env::get_self_id(env) {
            Some(self_) => match env::get_class(env, &self_) {
                decl_entry::T::Found(trait_) if ast_defs::is_c_trait(cls::kind(&trait_)) => {
                    use trait_most_concrete_parent::T::Found;
                    use trait_most_concrete_parent::T::NotFound;
                    match trait_most_concrete_parent(&trait_, env) {
                        None => {
                            typing_error_utils::add_typing_error(
                                &typing_error::primary(primary::T::ParentInTrait(p.clone())),
                                env,
                            );
                            let ty = env::fresh_type_error(env, p.clone());
                            make_result(vec![], aast::ClassId_::CIparent, ty)
                        }
                        Some(NotFound) => {
                            let trait_reqs = Some(
                                cls::all_ancestor_req_class_requirements(&trait_)
                                    .into_iter()
                                    .chain(cls::all_ancestor_req_this_as_requirements(&trait_))
                                    .map(|req| -> PosOrDecl { req.pos.to_oxidized() })
                                    .collect(),
                            );
                            typing_error_utils::add_typing_error(
                                &typing_error::primary(primary::T::ParentUndefined {
                                    pos: p.clone(),
                                    trait_reqs,
                                }),
                                env,
                            );
                            let ty = env::fresh_type_error(env, p.clone());
                            make_result(vec![], aast::ClassId_::CIparent, ty)
                        }
                        Some(Found(_, parent_ty)) => {
                            // inside a trait, parent is SN.Typehints.this, but with the
                            // type of the most concrete class that the trait has
                            // "require extend"-ed
                            let (ty_err_opt, parent_ty) =
                                phase::localize_no_subst(env, true, &parent_ty);
                            if let Some(err) = &ty_err_opt {
                                typing_error_utils::add_typing_error(err, env)
                            }
                            make_result(vec![], aast::ClassId_::CIparent, parent_ty)
                        }
                    }
                }
                _ => match env::get_parent_ty(env) {
                    None => {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(primary::T::ParentUndefined {
                                pos: p.clone(),
                                trait_reqs: None,
                            }),
                            env,
                        );
                        let ty = env::fresh_type_error(env, p.clone());
                        make_result(vec![], aast::ClassId_::CIparent, ty)
                    }
                    Some(parent) => {
                        let (ty_err_opt, parent) = phase::localize_no_subst(env, true, &parent);
                        if let Some(err) = &ty_err_opt {
                            typing_error_utils::add_typing_error(err, env)
                        }
                        // parent is still technically the same object.
                        make_result(vec![], aast::ClassId_::CIparent, parent)
                    }
                },
            },
            None => match env::get_parent_ty(env) {
                None => {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::ParentUndefined {
                            pos: p.clone(),
                            trait_reqs: None,
                        }),
                        env,
                    );
                    let ty = env::fresh_type_error(env, p.clone());
                    make_result(vec![], aast::ClassId_::CIparent, ty)
                }
                Some(parent) => {
                    let (ty_err_opt, parent) = phase::localize_no_subst(env, true, &parent);
                    if let Some(err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    // parent is still technically the same object.
                    make_result(vec![], aast::ClassId_::CIparent, parent)
                }
            },
        },
        aast::ClassId_::CIstatic => {
            let this = if env::next_cont_opt(env).is_some() {
                make_type::this(reason::witness(p.clone()))
            } else {
                make_type::nothing(reason::witness(p.clone()))
            };
            make_result(vec![], aast::ClassId_::CIstatic, this)
        }
        aast::ClassId_::CIself => {
            let ty = match env::get_self_class_type(env) {
                Some((c, _, tyl)) => mk((
                    reason::witness(p.clone()),
                    Ty_::Tclass(c, exact.clone(), tyl),
                )),
                None => {
                    // Naming phase has already checked and replaced CIself with CI if outside a class
                    diagnostics::internal_error(p.clone(), "Unexpected CIself");
                    env::fresh_type_error(env, p.clone())
                }
            };
            make_result(vec![], aast::ClassId_::CIself, ty)
        }
        aast::ClassId_::CI(c) => {
            // `CI ((p, id) as c)`: this `p` (the position of the name) shadows
            // the one of the class id.
            let ast_defs::Id(p, id) = c;
            let class_ = env::get_class(env, id);
            match class_ {
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
                    let ty = env::fresh_type_error(env, p.clone());
                    make_result(vec![], aast::ClassId_::CI(c.clone()), ty)
                }
                decl_entry::T::Found(class_) => {
                    match attribute_check_policy {
                        expr::AttributeCheckPolicy::SkipAllAccess => {}
                        expr::AttributeCheckPolicy::CheckAll
                        | expr::AttributeCheckPolicy::SkipPackage => {
                            let should_check_package_boundary = {
                                // Some reference contexts are exempt from the package boundary check
                                // by default (nameof, catch, ::class), but a strict-isolation target
                                // opts them back in: its classes must not be statically referenced
                                // from outside its package. Reuses the already-fetched decl, so no
                                // extra heap access.
                                let exempt_unless_strict_isolation = |spec: TargetSymbolSpec| {
                                    if crate::typing_packages::is_strict_isolation_target(
                                        env,
                                        cls::get_package(&class_).as_ref(),
                                    ) {
                                        CheckReason::Yes(spec)
                                    } else {
                                        CheckReason::No
                                    }
                                };
                                if match attribute_check_policy {
                                    expr::AttributeCheckPolicy::SkipPackage => true,
                                    _ => false,
                                } {
                                    CheckReason::No
                                } else if is_attribute {
                                    // `<<C>>` references the attribute class C.
                                    exempt_unless_strict_isolation(TargetSymbolSpec::Attribute)
                                } else if is_catch {
                                    // `catch (C $e)` references the exception class C.
                                    exempt_unless_strict_isolation(TargetSymbolSpec::Class)
                                } else if inside_nameof {
                                    // `nameof C` yields C's name without loading its package.
                                    exempt_unless_strict_isolation(TargetSymbolSpec::Class)
                                } else if is_const {
                                    if env::package_allow_classconst_violations(env) {
                                        if is_classptr {
                                            // `Foo::class` is normally only a migration-era classptr lint,
                                            // but a strict-isolation target makes it a hard package
                                            // violation.
                                            if crate::typing_packages::is_strict_isolation_target(
                                                env,
                                                cls::get_package(&class_).as_ref(),
                                            ) {
                                                CheckReason::Yes(TargetSymbolSpec::Class)
                                            } else {
                                                CheckReason::ClassPtrLinterOnly
                                            }
                                        } else {
                                            // Non-::class constants: skip the class-level check
                                            // here and let class_const handle it
                                            CheckReason::No
                                        }
                                    } else {
                                        CheckReason::Yes(TargetSymbolSpec::Class)
                                    }
                                } else {
                                    CheckReason::Yes(TargetSymbolSpec::Class)
                                }
                            };
                            let (access_errs, access_linter_errs) = tvis::check_top_level_access(
                                should_check_package_boundary,
                                false,
                                p.clone(),
                                cls::pos(&class_),
                                cls::tests_bypass_visibility(&class_),
                                true,
                                env,
                                cls::internal(&class_),
                                cls::get_module(&class_),
                                cls::get_package(&class_).as_ref(),
                                id.clone(),
                            );
                            for (pos, w) in access_linter_errs {
                                let crate::typing_packages::PackageWarningInfo {
                                    current_package,
                                    current_package_before_override,
                                    caller_has_package_override,
                                    target_package,
                                    target_package_before_override,
                                    callee_has_package_override,
                                    classptr_reference_warning,
                                } = w;
                                crate::lints_diagnostics::crosspackage_linter(
                                    pos,
                                    current_package.as_ref(),
                                    current_package_before_override.as_deref(),
                                    caller_has_package_override,
                                    target_package.as_ref(),
                                    target_package_before_override.as_deref(),
                                    callee_has_package_override,
                                    classptr_reference_warning,
                                )
                            }
                            for err in &access_errs {
                                typing_error_utils::add_typing_error(err, env)
                            }
                        }
                    };

                    // Don't add Exact superfluously to class type if it's final
                    let exact = if cls::final_(&class_) {
                        nonexact()
                    } else {
                        exact
                    };
                    let (ty_err_opt, ty, tal) = phase::localize_targs_and_check_constraints(
                        exact,
                        check_targs_integrity,
                        cls::pos(&class_),
                        p.clone(),
                        Some(check_explicit_targs),
                        env,
                        c,
                        reason::witness(c.0.clone()),
                        &cls::tparams(&class_),
                        tal.iter().map(|aast::Targ(_, h)| h.clone()).collect(),
                    );
                    if let Some(err) = &ty_err_opt {
                        typing_error_utils::add_typing_error(err, env)
                    }
                    crate::typing_needs_concrete::check_reified_targs(
                        env,
                        &cls::tparams(&class_),
                        &tal,
                    );
                    make_result(tal, aast::ClassId_::CI(c.clone()), ty)
                }
            }
        }
        aast::ClassId_::CIreified(c) => {
            // `CIreified ((p, id) as c)`: this `p` shadows the one of the
            // class id.
            let ast_defs::Id(p, id) = c;
            let r = reason::hint(pos_or_decl::of_raw_pos(p.clone()));
            let tgeneric = make_type::generic(r, id.clone());
            make_result(vec![], aast::ClassId_::CIreified(c.clone()), tgeneric)
        }
        aast::ClassId_::CIexpr(e) => {
            // `CIexpr ((_, p, _) as e)`: this `p` (the position of the
            // expression) shadows the one of the class id.
            let p = &e.1;
            let (te, ty) = expr::expr(None, &expr::context::default(), env, e);
            fn fold_errs(
                errs: Vec<Result<Ty, (Ty, Ty)>>,
            ) -> Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> {
                // OCaml conses each element onto the front of the lists: they
                // are kept reversed here (`x :: xs` is a push) and turned
                // around at the end.
                let mut acc: Result<Vec<Ty>, (Vec<Ty>, Vec<Ty>)> = Ok(vec![]);
                for err in errs {
                    acc = match (acc, err) {
                        (Ok(mut xs), Ok(x)) => {
                            xs.push(x);
                            Ok(xs)
                        }
                        // `Error (x :: xs, y :: xs)`: both lists start from `xs`.
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
            /// `resolve_ety env ty`, with the `p` and `require_class_ptr` it
            /// captures in OCaml. It returns what the OCaml returns besides
            /// the environment: `(ty_err, (ty, err_res))`.
            fn resolve_ety(
                p: &Pos,
                require_class_ptr: ClassnameExprError,
                env: &mut Env,
                ty: Ty,
            ) -> (Option<typing_error::T>, (Ty, Result<Ty, (Ty, Ty)>)) {
                let (ty_err1, ty) = crate::typing_solver::expand_type_and_solve(
                    env,
                    None,
                    "an object",
                    p.clone(),
                    ty,
                );
                let resolve_class_pointer =
                    |env: &mut Env, wrap: &dyn Fn(Ty) -> Ty, the_cls: Ty, ty_err1: Option<typing_error::T>| {
                        let (ty_err2, (ty, err_res)) =
                            resolve_ety(p, require_class_ptr, env, the_cls);
                        let err_res = match err_res {
                            Ok(ty) => Ok(wrap(ty)),
                            Err((ty_act, ty_exp)) => Err((wrap(ty_act), wrap(ty_exp))),
                        };
                        (ocaml_option::merge(ty_err1, ty_err2, typing_error::both), (ty, err_res))
                    };
                let base_ty = tutils::get_base_type(None, env, ty.clone());
                // Unfortunately base_ty might itself be a tyvar, in the case of newtype with a naked generic bound
                let (_, base_ty) = crate::typing_solver::expand_type_and_solve(
                    env,
                    None,
                    "an object",
                    p.clone(),
                    base_ty,
                );
                let expected_class_error =
                    |env: &mut Env, r: Reason, ty_err1: Option<typing_error::T>| {
                        let ty_err2 = Some(typing_error::primary(primary::T::ExpectedClass {
                            suffix: Some({
                                // The lazy value prints with the environment
                                // of this point.
                                let env = env.clone();
                                let base_ty = base_ty.clone();
                                Lazy::new(move || {
                                    format!(
                                        "{}{}",
                                        ", but got ",
                                        typing_print::error(None, &env, &base_ty)
                                    )
                                })
                            }),
                            pos: p.clone(),
                        }));
                        let ty_nothing = make_type::nothing(reason::none());
                        let ty = make_type::dynamic(r);
                        let ty_expect = make_type::classname(reason::none(), vec![ty_nothing]);
                        (
                            ocaml_option::merge(ty_err1, ty_err2, typing_error::both),
                            (ty, Err((base_ty.clone(), ty_expect))),
                        )
                    };
                let r = get_reason(&base_ty).clone();
                match get_node(&base_ty) {
                    Ty_::Tnewtype(classname, tyl, as_ty)
                        if tyl.len() == 1 && classname == sn::classes::CLASS_NAME =>
                    {
                        let the_cls = tyl[0].clone();
                        let wrap = |ty: Ty| {
                            mk((
                                reason::none(),
                                Ty_::Tnewtype(classname.clone(), vec![ty], as_ty.clone()),
                            ))
                        };
                        let (ty_err, (cls_ty, err_res)) =
                            resolve_class_pointer(env, &wrap, the_cls, ty_err1);
                        let cls_name = typing_print::full_strip_ns(true, env, &cls_ty);
                        match require_class_ptr {
                            ClassnameExprError::Error => {
                                crate::typing_class_pointers::error_at_classname_type(
                                    env,
                                    p.clone(),
                                    cls_name,
                                    get_pos(&ty),
                                )
                            }
                            ClassnameExprError::Warning => {
                                crate::typing_class_pointers::warning_at_classname_type(
                                    env,
                                    p.clone(),
                                    cls_name,
                                    get_pos(&ty),
                                )
                            }
                            ClassnameExprError::Pass => {}
                        };
                        (ty_err, (cls_ty, err_res))
                    }
                    Ty_::TclassPtr(the_cls) => {
                        let wrap = |ty: Ty| mk((reason::none(), Ty_::TclassPtr(ty)));
                        resolve_class_pointer(env, &wrap, the_cls.clone(), ty_err1)
                    }
                    // `SN.Classes.cString`
                    Ty_::Tclass((_, id), _, _) if sn::typehints::HH_STRING == id => {
                        if tast::is_under_dynamic_assumptions(env.checked) {
                            // We allow a call through a string in dynamic check mode, as string <:D dynamic
                            (
                                None,
                                (make_type::dynamic(r.clone()), Ok(make_type::dynamic(r))),
                            )
                        } else {
                            expected_class_error(env, r, ty_err1)
                        }
                    }
                    Ty_::Tgeneric(_) | Ty_::Tclass(..) => (ty_err1, (ty.clone(), Ok(ty))),
                    Ty_::Tunion(tyl) => {
                        let (ty_err2, res) = crate::common::list::map_env_ty_err_opt(
                            env,
                            tyl,
                            |env, ty| resolve_ety(p, require_class_ptr, env, ty.clone()),
                            typing_error::union_opt,
                        );
                        let (tyl, errs): (Vec<Ty>, Vec<Result<Ty, (Ty, Ty)>>) =
                            res.into_iter().unzip();
                        let ty = make_type::union(r, tyl);
                        let err = match fold_errs(errs) {
                            Ok(_) => Ok(ty.clone()),
                            Err((ty_actuals, ty_expects)) => {
                                let ty_actual = make_type::union(reason::none(), ty_actuals);
                                let ty_expect = make_type::union(reason::none(), ty_expects);
                                Err((ty_actual, ty_expect))
                            }
                        };
                        (ocaml_option::merge(ty_err1, ty_err2, typing_error::both), (ty, err))
                    }
                    Ty_::Tintersection(tyl) => {
                        let (ty_err2, res) = tutils::run_on_intersection_with_ty_err(
                            env,
                            |env, ty| resolve_ety(p, require_class_ptr, env, ty.clone()),
                            tyl,
                        );
                        let (tyl, errs): (Vec<Ty>, Vec<Result<Ty, (Ty, Ty)>>) =
                            res.into_iter().unzip();
                        let ty = inter::intersect_list(env, r, &tyl);
                        let err = match fold_errs(errs) {
                            Ok(_) => Ok(ty.clone()),
                            Err((ty_actuals, ty_expects)) => {
                                let ty_actual =
                                    inter::intersect_list(env, reason::none(), &ty_actuals);
                                let ty_expect =
                                    inter::intersect_list(env, reason::none(), &ty_expects);
                                Err((ty_actual, ty_expect))
                            }
                        };
                        (ocaml_option::merge(ty_err1, ty_err2, typing_error::both), (ty, err))
                    }
                    Ty_::Tdynamic(_) => (None, (base_ty.clone(), Ok(base_ty.clone()))),
                    Ty_::Tvar(_) => {
                        let ty_err2 = if tutils::is_tyvar_error(env, &base_ty) {
                            None
                        } else {
                            Some(typing_error::primary(primary::T::UnknownType {
                                expected: "an object".to_string(),
                                pos: p.clone(),
                                reason: {
                                    let r = r.clone();
                                    Lazy::new(move || {
                                        // `Reason.to_string` gives the
                                        // `(pos, string)` pairs of the messages.
                                        reason::to_string("It is unknown", &r)
                                            .into_iter()
                                            .map(|(pos, msg)| {
                                                oxidized::message::Message(pos, msg.into())
                                            })
                                            .collect()
                                    })
                                },
                            }))
                        };
                        let ty = env::fresh_type_error(env, p.clone());
                        (
                            ocaml_option::merge(ty_err1, ty_err2, typing_error::both),
                            (ty.clone(), Ok(ty)),
                        )
                    }
                    Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::TvecOrDict(..)
                    | Ty_::Toption(_)
                    | Ty_::Tprim(_)
                    | Ty_::Tfun(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tnewtype(..)
                    | Ty_::Tdependent(..)
                    | Ty_::Tshape(_)
                    | Ty_::Taccess(_)
                    | Ty_::Tneg(_)
                    | Ty_::Tlabel(_) => expected_class_error(env, r, ty_err1),
                }
            }
            let (ty_err_opt, (result_ty, err_res)) = resolve_ety(p, require_class_ptr, env, ty);
            let ty_mismatch_opt = match err_res {
                Ok(_) => None,
                Err((ty_act, ty_expect)) => Some((ty_act, ty_expect)),
            };
            let te = hole_on_ty_mismatch(te, ty_mismatch_opt);
            let x = make_result(vec![], aast::ClassId_::CIexpr(te), result_ty);
            if let Some(err) = &ty_err_opt {
                typing_error_utils::add_typing_error(err, env)
            }
            x
        }
    }
}

/// Computes class information for the class id in an instance.
/// When `is_attribute` is true, this is used for the attribute
/// instantiation as in `<<MyAtrr()>> class C` (note that attributes are classes).
/// When `is_catch` is true, this is used for the exception pattern
/// inside a catch arm, as in `catch (MyException $e)`.
pub(crate) fn class_id_for_new(
    exact: Exact,
    is_attribute: bool,
    is_catch: bool,
    p: &Pos,
    env: &mut Env,
    cid: &nast::ClassId_,
    explicit_targs: &[nast::Targ],
) -> NewableClassInfo {
    let (tal, te, cid_ty) = class_expr(
        Some(true),
        None,
        Some(exact),
        Some(true),
        None,
        None,
        None,
        Some(is_attribute),
        Some(is_catch),
        Some(ClassnameExprError::Error),
        env,
        explicit_targs,
        &aast::ClassId((), p.clone(), cid.clone()),
    );
    // Need to deal with union case
    //
    // `get_info` does not thread the environment: each element works from the
    // environment `class_expr` returned (the one `get_info` returns at the
    // end), and what `get_base_type` does to it is dropped.
    let mut res: Vec<ClassOrDynamic> = vec![];
    let mut tyl: VecDeque<Ty> = VecDeque::from([cid_ty.clone()]);
    while let Some(ty) = tyl.pop_front() {
        match get_node(&ty) {
            Ty_::Tunion(tyl_) | Ty_::Tintersection(tyl_) => {
                // `tyl' @ tyl`
                for t in tyl_.iter().rev() {
                    tyl.push_front(t.clone())
                }
            }
            _ => {
                // Instantiation on an abstract class (e.g. from classname<T>) is
                // via the base type (to check constructor args), but the actual
                // type `ty` must be preserved.
                let mut env = env.clone();
                let base_type = tutils::get_base_type(None, &mut env, ty.clone());
                match get_node(&base_type) {
                    Ty_::Tdynamic(_) => res.insert(0, ClassOrDynamic::Dynamic),
                    Ty_::Tclass(sid, _, _) => {
                        let class_ = env::get_class(&env, &sid.1);
                        match class_ {
                            decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {}
                            decl_entry::T::Found(class_info) => match (&te, &cid_ty) {
                                // When computing the classes for a new T() where T is a generic,
                                // the class must be consistent (final, final constructor, or
                                // <<__ConsistentConstruct>>) for its constructor to be considered
                                (aast::ClassId(_, _, aast::ClassId_::CI(ast_defs::Id(_, c))), ty)
                                    if is_generic_equal_to(c, ty) =>
                                {
                                    // Only have this choosing behavior for new T(), not all generic types
                                    // i.e. new classname<T>, TODO: T41190512
                                    if env::valid_newable_class(&env, &class_info) {
                                        res.insert(
                                            0,
                                            ClassOrDynamic::Class(
                                                sid.clone(),
                                                class_info,
                                                ty.clone(),
                                            ),
                                        )
                                    }
                                }
                                _ => res.insert(
                                    0,
                                    ClassOrDynamic::Class(sid.clone(), class_info, ty.clone()),
                                ),
                            },
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    (tal, te, res)
}

/// When invoking a method, the class_id is used to determine what class we
/// lookup the method in, but the type of 'this' will be the late bound type.
/// For example:
///
///  class C {
///    public static function get(): this { return new static(); }
///
///    public static function alias(): this { return self::get(); }
///  }
///
///  In C::alias, when we invoke self::get(), 'self' is resolved to the class
///  in the lexical scope (C), so call C::get. However the method is executed in
///  the current context, so static inside C::get will be resolved to the late
///  bound type (get_called_class() within C::alias).
///
///  This means when determining the type of this, CIparent and CIself should be
///  changed to CIstatic. For the other cases of C::get() or $c::get(), we only
///  look at the left hand side of the '::' and use the type associated
///  with it.
///
///  Thus C::get() will return a type C, while $c::get() will return the same
///  type as $c.
pub(crate) fn this_for_method(
    env: &mut Env,
    aast::ClassId(_, p, cid): &nast::ClassId,
    default_ty: Ty,
) -> Ty {
    match cid {
        aast::ClassId_::CIparent | aast::ClassId_::CIself | aast::ClassId_::CIstatic => {
            let (_tal, _te, ty) = class_expr(
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                env,
                &[],
                &aast::ClassId((), p.clone(), aast::ClassId_::CIstatic),
            );
            expr_dep_ty::make(env, &aast::ClassId_::CIstatic, ty)
        }
        _ => default_ty,
    }
}

/// Get class infos for a class expression (e.g. `parent`, `self` or
/// regular classnames) - which might resolve to a union or intersection
/// of classes - and check they are instantiable.
///
/// FIXME: we need to separate our instantiability into two parts. Currently,
/// all this function is doing is checking if a given type is inhabited --
/// that is, whether there are runtime values of type Aast. However,
/// instantiability should be the stricter notion that T has a runtime
/// constructor; that is, `new T()` should be valid. In particular, interfaces
/// are inhabited, but not instantiable.
/// To make this work with classname, we likely need to add something like
/// concrete_classname<T>, where T cannot be an interface.
pub(crate) fn instantiable_cid(
    exact: Option<Exact>,
    is_attribute: Option<bool>,
    is_catch: Option<bool>,
    p: &Pos,
    env: &mut Env,
    cid: &nast::ClassId_,
    explicit_targs: &[nast::Targ],
) -> NewableClassInfo {
    let exact = exact.unwrap_or_else(nonexact);
    let is_attribute = is_attribute.unwrap_or(false);
    let is_catch = is_catch.unwrap_or(false);
    let (tal, te, classes) =
        class_id_for_new(exact, is_attribute, is_catch, p, env, cid, explicit_targs);
    crate::typing_needs_concrete::check_instantiation(env, p, cid);
    for c in &classes {
        match c {
            ClassOrDynamic::Dynamic => {}
            ClassOrDynamic::Class((pos, name), class_info, c_ty) => {
                let pos = pos_or_decl::unsafe_to_raw_pos(pos.clone());
                let kind = cls::kind(class_info);
                // `SN.Classes.cString`
                if sn::typehints::HH_STRING == cls::name(class_info) {
                    uninstantiable_error(env, p, cid, &cls::pos(class_info), name, &pos, c_ty)
                } else if ast_defs::is_c_trait(kind)
                    || ast_defs::is_c_enum(kind)
                    || ast_defs::is_c_enum_class(kind)
                {
                    match cid {
                        aast::ClassId_::CIexpr(_)
                        | aast::ClassId_::CI(_)
                        | aast::ClassId_::CIreified(_) => uninstantiable_error(
                            env,
                            p,
                            cid,
                            &cls::pos(class_info),
                            name,
                            &pos,
                            c_ty,
                        ),
                        aast::ClassId_::CIstatic
                        | aast::ClassId_::CIparent
                        | aast::ClassId_::CIself => {}
                    }
                } else if ast_defs::is_c_abstract(kind) && cls::final_(class_info) {
                    uninstantiable_error(env, p, cid, &cls::pos(class_info), name, &pos, c_ty)
                } else {
                }
            }
        }
    }
    (tal, te, classes)
}
