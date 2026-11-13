// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing.ml` (lines 13575-14187): module `Class_get_expr`.
//! See `hh/PORTING.md`.
//!
//! Signatures:
//!
//! - `transform_fty:(decl_fun_type -> decl_fun_type) option` is
//!   `Option<&dyn Fn(DeclFunType) -> DeclFunType>` (the functions are
//!   recursive and pass it on).
//! - `coerce_from_ty` is `Option<(Pos, Ureason, Ty)>`, as in
//!   `Typing_object_get`.
//! - The optional arguments (`?attribute_check_policy`, `?explicit_targs`,
//!   `?incl_tc`, `?is_function_pointer`) are `Option`s, in the order of the
//!   OCaml; the default is applied inside.
//! - `(p, mid) : pos * byte_string` is `&aast::Pstring`.
//! - The result `env * (locl_ty * Tast.targ list) * rval` is
//!   `((Ty, Vec<tast::Targ>), rval)`; in `class_get_res` and
//!   `class_get_inner` the rval is `Option<Result<Ty, (Ty, Ty)>>` (OCaml's
//!   `(locl_ty, locl_ty * locl_ty) result option`).

use std::sync::LazyLock;

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::ast_defs;
use crate::decl_entry;
// module Cls = Folded_class
use crate::folded_class as cls;
use crate::tast;
use crate::typing::class_id;
use crate::typing::expr;
use crate::typing::prelude::*;
use crate::typing_coercion;
use crate::typing_defs::*;
// module ExprDepTy = Typing_dependent_type.ExprDepTy
use crate::typing_dependent_type::expr_dep_ty;
use crate::typing_dynamic;
use crate::typing_enforceability;
// module Env = Typing_env
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::MethOrProp;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
// module Inter = Typing_intersection
use crate::typing_intersection as inter;
// module MakeType = Typing_make_type
use crate::typing_make_type as make_type;
// module TOG = Typing_object_get
use crate::typing_object_get as tog;
// module Phase = Typing_phase
use crate::typing_phase as phase;
use crate::typing_print;
// module Reason = Typing_reason
use crate::typing_reason as reason;
use crate::typing_reason::Ureason;
// module Union = Typing_union
use crate::typing_union as union;
// module TUtils = Typing_utils
use crate::typing_utils as tutils;
// module TVis = Typing_visibility
use crate::typing_visibility as tvis;
use crate::utils::strip_ns;

/// The rval part of the result of `class_get_res` and `class_get_inner`.
pub(crate) type RvalRes = Option<Result<Ty, (Ty, Ty)>>;

fn add_typing_error_opt(ty_err_opt: &Option<typing_error::T>, env: &Env) {
    if let Some(err) = ty_err_opt {
        typing_error_utils::add_typing_error(err, env)
    }
}

/// `lazy (Typing_print.error env ty)`, on the environment as it is now.
fn lazy_print_error(env: &Env, ty: &Ty) -> Lazy<String> {
    let env = env.clone();
    let ty = ty.clone();
    Lazy::new(move || typing_print::error(None, &env, &ty))
}

/// `Typing_defs.get_pos` on a decl type.
fn decl_get_pos(ty: &DeclTy) -> PosOrDecl {
    PosOrDecl::from(crate::decl_utils::get_pos(ty))
}

/// `Option.all` (Core)
fn option_all<A>(l: Vec<Option<A>>) -> Option<Vec<A>> {
    l.into_iter().collect()
}

/// `List.max_elt ~compare` (Core): the first of the greatest elements.
fn list_max_elt<A>(l: Vec<A>, compare: impl Fn(&A, &A) -> std::cmp::Ordering) -> Option<A> {
    let mut max: Option<A> = None;
    for x in l {
        max = match max {
            None => Some(x),
            Some(m) => {
                if compare(&m, &x) == std::cmp::Ordering::Less {
                    Some(x)
                } else {
                    Some(m)
                }
            }
        }
    }
    max
}

/// `List.map_env_ty_err_opt` (of `Common.List`): `f` is applied to the
/// elements from left to right, and `combine_ty_errs` gets the errors in the
/// order the OCaml builds them: the elements are taken five at a time, the
/// errors of each group in order and the groups from the last to the first
/// (after 1001 groups, the errors of the rest of the elements from the last
/// to the first, before the groups).
fn list_map_env_ty_err_opt<E: ?Sized, X, Y, Err, Errs>(
    env: &mut E,
    xs: &[X],
    mut f: impl FnMut(&mut E, &X) -> (Option<Err>, Y),
    combine_ty_errs: impl FnOnce(Vec<Err>) -> Errs,
) -> (Errs, Vec<Y>) {
    // The OCaml list of errors, last element first.
    let mut rev_errs: Vec<Err> = Vec::new();
    let mut ys = Vec::with_capacity(xs.len());
    let mut rest = xs;
    let mut counter = 0;
    loop {
        if rest.is_empty() {
            break;
        }
        let (group, tail) = rest.split_at(std::cmp::min(5, rest.len()));
        let errs: Vec<Option<Err>> = group
            .iter()
            .map(|x| {
                let (err, y) = f(env, x);
                ys.push(y);
                err
            })
            .collect();
        // `ty_err_opt1 :: ... :: ty_err_opt5 :: ty_err_opts`
        rev_errs.extend(errs.into_iter().rev().flatten());
        if tail.is_empty() {
            break;
        }
        if counter > 1000 {
            // `rev_map_env_ty_err_opt env ys ~f ~err:(...)`
            for x in tail {
                let (err, y) = f(env, x);
                ys.push(y);
                rev_errs.extend(err);
            }
            break;
        }
        counter += 1;
        rest = tail;
    }
    rev_errs.reverse();
    (combine_ty_errs(rev_errs), ys)
}

pub(crate) fn class_get_res(
    is_method: bool,
    is_const: bool,
    transform_fty: Option<&dyn Fn(DeclFunType) -> DeclFunType>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    attribute_check_policy: Option<expr::AttributeCheckPolicy>,
    explicit_targs: Option<&[nast::Targ]>,
    incl_tc: Option<bool>,
    is_function_pointer: Option<bool>,
    env: &mut Env,
    cty: Ty,
    pm: &aast::Pstring,
    cid: &nast::ClassId,
) -> ((Ty, Vec<tast::Targ>), RvalRes) {
    let attribute_check_policy =
        attribute_check_policy.unwrap_or(expr::AttributeCheckPolicy::CheckAll);
    let explicit_targs = explicit_targs.unwrap_or(&[]);
    let incl_tc = incl_tc.unwrap_or(false);
    let is_function_pointer = is_function_pointer.unwrap_or(false);
    let this_ty = if is_method {
        class_id::this_for_method(env, cid, cty.clone())
    } else {
        cty.clone()
    };
    class_get_inner(
        is_method,
        is_const,
        this_ty,
        coerce_from_ty,
        transform_fty,
        Some(explicit_targs),
        Some(incl_tc),
        Some(is_function_pointer),
        Some(attribute_check_policy),
        env,
        cid,
        cty,
        pm,
    )
}

pub fn class_get_err(
    is_method: bool,
    is_const: bool,
    transform_fty: Option<&dyn Fn(DeclFunType) -> DeclFunType>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    explicit_targs: Option<&[nast::Targ]>,
    incl_tc: Option<bool>,
    is_function_pointer: Option<bool>,
    env: &mut Env,
    cty: Ty,
    pm: &aast::Pstring,
    cid: &nast::ClassId,
) -> ((Ty, Vec<tast::Targ>), Option<(Ty, Ty)>) {
    let (tys, rval_res_opt) = class_get_res(
        is_method,
        is_const,
        transform_fty,
        coerce_from_ty,
        None,
        explicit_targs,
        incl_tc,
        is_function_pointer,
        env,
        cty,
        pm,
        cid,
    );
    let rval_err_opt = rval_res_opt.and_then(Result::err);
    (tys, rval_err_opt)
}

pub fn class_get(
    is_method: bool,
    is_const: bool,
    transform_fty: Option<&dyn Fn(DeclFunType) -> DeclFunType>,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    attribute_check_policy: Option<expr::AttributeCheckPolicy>,
    explicit_targs: Option<&[nast::Targ]>,
    incl_tc: Option<bool>,
    is_function_pointer: Option<bool>,
    env: &mut Env,
    cty: Ty,
    pm: &aast::Pstring,
    cid: &nast::ClassId,
) -> (Ty, Vec<tast::Targ>) {
    let attribute_check_policy =
        attribute_check_policy.unwrap_or(expr::AttributeCheckPolicy::CheckAll);
    let (tys, _) = class_get_res(
        is_method,
        is_const,
        transform_fty,
        coerce_from_ty,
        Some(attribute_check_policy),
        explicit_targs,
        incl_tc,
        is_function_pointer,
        env,
        cty,
        pm,
        cid,
    );
    tys
}

pub(crate) fn class_get_inner(
    is_method: bool,
    is_const: bool,
    this_ty: Ty,
    coerce_from_ty: Option<(Pos, Ureason, Ty)>,
    transform_fty: Option<&dyn Fn(DeclFunType) -> DeclFunType>,
    explicit_targs: Option<&[nast::Targ]>,
    incl_tc: Option<bool>,
    is_function_pointer: Option<bool>,
    attribute_check_policy: Option<expr::AttributeCheckPolicy>,
    env: &mut Env,
    cid: &nast::ClassId,
    cty: Ty,
    pm: &aast::Pstring,
) -> ((Ty, Vec<tast::Targ>), RvalRes) {
    let explicit_targs = explicit_targs.unwrap_or(&[]);
    let incl_tc = incl_tc.unwrap_or(false);
    let is_function_pointer = is_function_pointer.unwrap_or(false);
    let attribute_check_policy =
        attribute_check_policy.unwrap_or(expr::AttributeCheckPolicy::CheckAll);
    let (p, mid) = pm;
    let aast::ClassId(_, _cid_pos, cid_) = cid;
    let cty = env::expand_type(env, cty);
    let dflt_rval_err: RvalRes = coerce_from_ty.as_ref().map(|(_, _, ty)| Ok(ty.clone()));
    let elt = if is_method {
        MethOrProp::meth
    } else {
        MethOrProp::prop
    };
    let r = get_reason(&cty).clone();
    match get_node(&cty) {
        Ty_::Tdynamic(_) | Ty_::Tany(_) => ((cty.clone(), vec![]), dflt_rval_err),
        Ty_::Tunion(tyl) => {
            // `List.fold_left` consing onto `pairs` and `rval_err_opts`: they
            // end up in the reverse order of `tyl`.
            let mut pairs = vec![];
            let mut rval_err_opts = vec![];
            for ty in tyl {
                let (pair, rval_err_opt) = class_get_res(
                    is_method,
                    is_const,
                    transform_fty,
                    coerce_from_ty.clone(),
                    None,
                    Some(explicit_targs),
                    Some(incl_tc),
                    Some(is_function_pointer),
                    env,
                    ty.clone(),
                    pm,
                    cid,
                );
                pairs.push(pair);
                rval_err_opts.push(rval_err_opt);
            }
            pairs.reverse();
            rval_err_opts.reverse();

            let rval_err = option_all(rval_err_opts).map(union_coercion_errs);
            let tys: Vec<Ty> = pairs.iter().map(|(ty, _)| ty.clone()).collect();
            let ty = union::union_list(env, None, r, &tys);
            // Pick up the maximal number of type arguments to put in the TAST, so that
            // TAST checks such as the reified checks can check the type arguments
            // against the spec.
            let tal = list_max_elt(
                pairs.into_iter().map(|(_, tal)| tal).collect(),
                |a: &Vec<tast::Targ>, b: &Vec<tast::Targ>| a.len().cmp(&b.len()),
            )
            .unwrap_or_default();
            ((ty, tal), rval_err)
        }
        Ty_::Tintersection(tyl) => {
            let (pairs, rval_err_opts) = tutils::run_on_intersection_res(
                env,
                |env: &mut Env, ty: &Ty| {
                    class_get_inner(
                        is_method,
                        is_const,
                        this_ty.clone(),
                        coerce_from_ty.clone(),
                        transform_fty,
                        Some(explicit_targs),
                        Some(incl_tc),
                        Some(is_function_pointer),
                        Some(attribute_check_policy.clone()),
                        env,
                        cid,
                        ty.clone(),
                        pm,
                    )
                },
                tyl,
            );
            let rval_err = option_all(rval_err_opts).map(intersect_coercion_errs);
            let tys: Vec<Ty> = pairs.iter().map(|(ty, _)| ty.clone()).collect();
            let ty = inter::intersect_list(env, r, &tys);
            ((ty, vec![]), rval_err)
        }
        Ty_::Tnewtype(n, tyargs, _) => {
            let ty = tutils::get_newtype_super(env, r, n, tyargs);
            class_get_inner(
                is_method,
                is_const,
                this_ty,
                coerce_from_ty,
                transform_fty,
                Some(explicit_targs),
                Some(incl_tc),
                Some(is_function_pointer),
                Some(attribute_check_policy),
                env,
                cid,
                ty,
                pm,
            )
        }
        Ty_::Tdependent(_, ty) => class_get_inner(
            is_method,
            is_const,
            this_ty,
            coerce_from_ty,
            transform_fty,
            Some(explicit_targs),
            Some(incl_tc),
            Some(is_function_pointer),
            Some(attribute_check_policy),
            env,
            cid,
            ty.clone(),
            pm,
        ),
        Ty_::Tgeneric(_) => {
            let tyl = tutils::get_concrete_supertypes(None, None, None, true, env, cty.clone());
            let has_no_bound = tutils::no_upper_bound(true, env, &tyl);
            if has_no_bound {
                let ty = env::fresh_type_error(env, p.clone());
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Non_class_member {
                        elt,
                        member_name: mid.clone(),
                        pos: p.clone(),
                        ty_name: lazy_print_error(env, &cty),
                        decl_pos: get_pos(&cty),
                    }),
                    env,
                );

                ((ty, vec![]), dflt_rval_err)
            } else {
                let ty = inter::intersect_list(env, r, &tyl);
                class_get_inner(
                    is_method,
                    is_const,
                    this_ty,
                    coerce_from_ty,
                    transform_fty,
                    Some(explicit_targs),
                    Some(incl_tc),
                    Some(is_function_pointer),
                    Some(attribute_check_policy),
                    env,
                    cid,
                    ty,
                    pm,
                )
            }
        }
        Ty_::Tclass((_, c), _, paraml) => {
            let class_ = env::get_class(env, c);
            match class_ {
                decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => {
                    let ty = make_type::nothing(reason::missing_class(p.clone()));
                    ((ty, vec![]), dflt_rval_err)
                }
                decl_entry::T::Found(class_) => {
                    // TODO akenn: Should we move this to the class_get original call?
                    let this_ty = expr_dep_ty::make(env, cid_, this_ty);
                    // When accessing a class constant via `self` in a trait with
                    // `require class C` or `require this as C`, resolve `this_ty` to C
                    // rather than the trait.
                    let this_ty = if is_const
                        && ast_defs::is_c_trait(cls::kind(&class_))
                        && matches!(cid_, aast::ClassId_::CIself)
                    {
                        match cls::all_ancestor_req_constraints_requirements(&class_)
                            .into_iter()
                            .next()
                        {
                            Some(cr) => {
                                let req_ty = to_requirement(cr).ty;
                                let (_, locl_ty) = phase::localize_no_subst(env, true, &req_ty);
                                locl_ty
                            }
                            None => this_ty,
                        }
                    } else {
                        this_ty
                    };
                    // We need to instantiate generic parameters in the method signature
                    let ety_env = ExpandEnv {
                        this_ty: this_ty.clone(),
                        substs: tutils::make_locl_subst_for_class_tparams(&class_, paraml),
                        ..empty_expand_env()
                    };
                    let get_smember_from_constraints = |env: &mut Env, class_info: &cls::T| {
                        // Extract the upper bounds on this from `require class` and `require this as`
                        // constraints.
                        let upper_bounds_from_require_class_constraints: Vec<DeclTy> =
                            cls::all_ancestor_req_constraints_requirements(class_info)
                                .into_iter()
                                .map(|cr| to_requirement(cr).ty)
                                .collect();
                        let (ty_err_opt, upper_bounds) = {
                            let (ty_err_opt, upper_bounds) = list_map_env_ty_err_opt(
                                env,
                                &upper_bounds_from_require_class_constraints,
                                |env: &mut Env, up: &DeclTy| phase::localize(&ety_env, env, up),
                                typing_error::multiple_opt,
                            );
                            // If class C uses a trait that require class C, then decls for class C
                            // include the require class C constraint.  This must be filtered out to avoid
                            // that resolving a static element on class C enters into an infinite recursion.
                            // Similarly, upper bounds on this equivalent via aliases to class C
                            // introduced via class-level where clauses, must be filtered out; this is done
                            // by localizing the bounds before comparing them with the current class name.
                            let upper_bounds: Vec<Ty> = upper_bounds
                                .into_iter()
                                .filter(|ty| match get_node(ty) {
                                    Ty_::Tclass((_, cn), _, _) => *cn != cls::name(class_info),
                                    _ => true,
                                })
                                .collect();
                            (ty_err_opt, upper_bounds)
                        };
                        add_typing_error_opt(&ty_err_opt, env);
                        if upper_bounds.is_empty() {
                            // there are no upper bounds, raise an error
                            typing_error_utils::add_typing_error(
                                &tog::smember_not_found(
                                    p.clone(),
                                    is_const,
                                    is_method,
                                    is_function_pointer,
                                    class_info,
                                    mid.clone(),
                                    callback::unify_error(),
                                ),
                                env,
                            );
                            let ty = env::fresh_type_error(env, p.clone());
                            ((ty, vec![]), dflt_rval_err.clone())
                        } else {
                            // since there are upper bounds on this, repeat the search on their intersection
                            let inter_ty =
                                inter::intersect_list(env, reason::witness(p.clone()), &upper_bounds);
                            class_get_inner(
                                is_method,
                                is_const,
                                this_ty.clone(),
                                coerce_from_ty.clone(),
                                transform_fty,
                                Some(explicit_targs),
                                Some(incl_tc),
                                Some(is_function_pointer),
                                Some(attribute_check_policy.clone()),
                                env,
                                cid,
                                inter_ty,
                                pm,
                            )
                        }
                    };
                    if is_const {
                        let const_ = if incl_tc {
                            env::get_const(env, &class_, mid)
                        } else {
                            match env::get_typeconst(env, &class_, mid) {
                                Some(_) => {
                                    typing_error_utils::add_typing_error(
                                        &typing_error::primary(
                                            primary::T::Illegal_typeconst_direct_access(p.clone()),
                                        ),
                                        env,
                                    );
                                    None
                                }
                                None => env::get_const(env, &class_, mid),
                            }
                        };
                        match const_ {
                            None => get_smember_from_constraints(env, &class_),
                            Some(cc) => {
                                let (ty_err_opt, cc_locl_type) =
                                    phase::localize(&ety_env, env, &cc.ty);
                                add_typing_error_opt(&ty_err_opt, env);
                                match cc.kind {
                                    ty::decl::ClassConstKind::CCAbstract(has_default) => {
                                    // A default resolves at runtime even when `static` is abstract.
                                    // A type constant's synthesized constant is checked by
                                    // [Typing_needs_concrete.check_abstract_tconst_via_static]
                                    if !has_default
                                        && (!cc.is_synthesized
                                            || env::get_typeconst(env, &class_, mid).is_none())
                                    {
                                        crate::typing_needs_concrete::check_abstract_access_via_static(
                                            env,
                                            p,
                                            &PosOrDecl::from(cc.pos.clone()),
                                            &cls::name(&class_),
                                            mid,
                                            cid_,
                                        );
                                    }
                                    match cid_ {
                                        aast::ClassId_::CIstatic | aast::ClassId_::CIexpr(_) => {}
                                        _ => {
                                            let cc_name = format!("{}::{}", cls::name(&class_), mid);
                                            let err = typing_error::primary(
                                                primary::T::Abstract_const_usage {
                                                    pos: p.clone(),
                                                    decl_pos: PosOrDecl::from(cc.pos.clone()),
                                                    name: cc_name,
                                                },
                                            );
                                            typing_error_utils::add_typing_error(&err, env)
                                        }
                                    }
                                    }
                                    ty::decl::ClassConstKind::CCConcrete => {}
                                }
                                ((cc_locl_type, vec![]), dflt_rval_err)
                            }
                        }
                    } else {
                        let static_member_opt = env::get_static_member(is_method, env, &class_, mid);
                        match static_member_opt {
                            // Before raising an error, check if the classish has upper bounds on this
                            // (via class-level where clauses or require class constraints); if yes, repeat
                            // the search on all the upper bounds, if not raise an error.
                            None => get_smember_from_constraints(env, &class_),
                            Some(ce) => {
                                // `ce_type = (lazy member_decl_ty)` forces it here.
                                let member_decl_ty: DeclTy = LazyLock::force(&ce.ce_type).clone();
                                let def_pos = decl_get_pos(&member_decl_ty);
                                let has_tests_bypass_visibility =
                                    get_ce_tests_bypass_visibility(&ce);
                                let tests_bypass_visibility_static_properties_blocked =
                                    has_tests_bypass_visibility
                                        && (!is_method)
                                        && !env::get_tcopt(env)
                                            .tco_tests_bypass_visibility_static_properties;
                                let tests_bypass_visibility = has_tests_bypass_visibility
                                    && !tests_bypass_visibility_static_properties_blocked;
                                // Don't need to check visibilty on class constants in an attribute
                                match attribute_check_policy {
                                    expr::AttributeCheckPolicy::SkipAllAccess => {}
                                    expr::AttributeCheckPolicy::CheckAll
                                    | expr::AttributeCheckPolicy::SkipPackage => {
                                        for err in tvis::check_class_access(
                                            is_method,
                                            p.clone(),
                                            def_pos.clone(),
                                            tests_bypass_visibility,
                                            tests_bypass_visibility_static_properties_blocked,
                                            env,
                                            (&ce.ce_visibility, get_ce_lsb(&ce)),
                                            cid_,
                                            &class_,
                                        ) {
                                            typing_error_utils::add_typing_error(&err, env)
                                        }
                                    }
                                }
                                add_typing_error_opt(
                                    &tvis::check_deprecated(
                                        p.clone(),
                                        def_pos.clone(),
                                        env,
                                        ce.ce_deprecated.clone(),
                                    ),
                                    env,
                                );
                                check_class_get(
                                    env,
                                    p,
                                    &def_pos,
                                    c,
                                    mid,
                                    &ce,
                                    cid,
                                    is_function_pointer,
                                    is_method,
                                );
                                let (member_ty, et_enforced, tal) = match member_decl_ty.node_ref() {
                                    // We special case Tfun here to allow passing in explicit tparams to localize_ft.
                                    ty::decl::Ty_::Tfun(ft) if is_method => {
                                        let r = member_decl_ty.reason();
                                        let ft: DeclFunType = (**ft).clone();
                                        let ft = match transform_fty {
                                            None => ft,
                                            Some(f) => f(ft),
                                        };
                                        add_typing_error_opt(
                                            &tvis::check_cross_package(
                                                p.clone(),
                                                &def_pos,
                                                env,
                                                ce.ce_package_requirement.clone(),
                                            ),
                                            env,
                                        );

                                        let (ty_err_opt1, explicit_targs) = phase::localize_targs(
                                            true,
                                            true,
                                            def_pos.clone(),
                                            p.clone(),
                                            strip_ns(mid).to_string(),
                                            None,
                                            env,
                                            &ft.tparams,
                                            explicit_targs
                                                .iter()
                                                .map(|aast::Targ(_, hint)| hint.clone())
                                                .collect(),
                                        );
                                        add_typing_error_opt(&ty_err_opt1, env);
                                        crate::typing_needs_concrete::check_reified_targs(
                                            env,
                                            &ft.tparams,
                                            &explicit_targs,
                                        );
                                        let ft = typing_enforceability::compute_enforced_and_pessimize_fun_type(
                                            Some(&class_),
                                            env,
                                            ft,
                                        );

                                        let (ty_err_opt2, ft) = phase::localize_ft(
                                            Some(phase::MethodInstantiation {
                                                use_name: strip_ns(mid).to_string(),
                                                use_pos: p.clone(),
                                                explicit_targs: explicit_targs.clone(),
                                            }),
                                            &ety_env,
                                            def_pos.clone(),
                                            env,
                                            &ft,
                                        );
                                        add_typing_error_opt(&ty_err_opt2, env);
                                        let fty = typing_dynamic::maybe_wrap_with_supportdyn(
                                            get_ce_support_dynamic_type(&ce),
                                            reason::localize(&r.clone().to_oxidized()),
                                            ft,
                                        );
                                        (fty, Enforcement::Unenforced, explicit_targs)
                                    }
                                    // unused
                                    _ => {
                                        let (et_enforced, et_type) =
                                            typing_enforceability::compute_enforced_and_pessimize_ty(
                                                Some(&class_),
                                                env,
                                                None,
                                                member_decl_ty.clone(),
                                            );
                                        let (ty_err_opt, member_ty) =
                                            phase::localize(&ety_env, env, &et_type);
                                        add_typing_error_opt(&ty_err_opt, env);
                                        (member_ty, et_enforced, vec![])
                                    }
                                };
                                let rval_err = match &coerce_from_ty {
                                    None => None,
                                    Some((p, ur, ty)) => {
                                        let ty_err_opt = typing_coercion::coerce_type(
                                            None,
                                            None,
                                            None,
                                            p.clone(),
                                            ur.clone(),
                                            env,
                                            ty.clone(),
                                            tutils::make_like_if_enforced(
                                                env,
                                                et_enforced,
                                                member_ty.clone(),
                                            ),
                                            et_enforced,
                                            callback::unify_error(),
                                        );
                                        add_typing_error_opt(&ty_err_opt, env);
                                        let ty_mismatch = mk_ty_mismatch_res(
                                            ty.clone(),
                                            member_ty.clone(),
                                            ty_err_opt.as_ref(),
                                        );
                                        Some(ty_mismatch)
                                    }
                                };
                                ((member_ty, tal), rval_err)
                            }
                        }
                    }
                }
            }
        }
        Ty_::Tvar(_)
        | Ty_::Tnonnull
        | Ty_::TvecOrDict(_, _)
        | Ty_::Toption(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Taccess(_)
        | Ty_::Tneg(_)
        | Ty_::Tlabel(_)
        | Ty_::TclassPtr(_) => {
            if !tutils::is_tyvar_error(env, &cty) {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::Non_class_member {
                        elt,
                        member_name: mid.clone(),
                        pos: p.clone(),
                        ty_name: lazy_print_error(env, &cty),
                        decl_pos: get_pos(&cty),
                    }),
                    env,
                );
            }
            let ty = env::fresh_type_error(env, p.clone());
            ((ty, vec![]), dflt_rval_err)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_max_elt_keeps_the_first_of_the_greatest() {
        let l = vec![(1, 'a'), (3, 'b'), (2, 'c'), (3, 'd')];
        assert_eq!(list_max_elt(l, |a, b| a.0.cmp(&b.0)), Some((3, 'b')));
        assert_eq!(
            list_max_elt(Vec::<(i32, char)>::new(), |a, b| a.0.cmp(&b.0)),
            None
        );
    }

    #[test]
    fn option_all_needs_every_element() {
        assert_eq!(option_all(vec![Some(1), Some(2)]), Some(vec![1, 2]));
        assert_eq!(option_all(vec![Some(1), None]), None);
        assert_eq!(option_all::<i32>(vec![]), Some(vec![]));
    }

    #[test]
    fn map_env_ty_err_opt_error_order() {
        // Groups of five: the errors of the last group come first.
        let xs: Vec<i32> = (0..7).collect();
        let (errs, ys) =
            list_map_env_ty_err_opt(&mut (), &xs, |_, x| (Some(*x), x * 10), |errs| errs);
        assert_eq!(ys, vec![0, 10, 20, 30, 40, 50, 60]);
        assert_eq!(errs, vec![5, 6, 0, 1, 2, 3, 4]);
        let (errs, _) = list_map_env_ty_err_opt(
            &mut (),
            &xs,
            |_, x| (if x % 2 == 0 { Some(*x) } else { None }, ()),
            |errs| errs,
        );
        assert_eq!(errs, vec![6, 0, 2, 4]);
    }
}
