// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing/typing.ml` (lines 5017-6892): module `Expr`, middle.
//! See `hh/PORTING.md`.
//!
//! The functions of this part, in the OCaml order: [`class_const`],
//! [`check_et_splice`], [`et_splice`], [`new_object`], [`array_value`],
//! [`arraykey_value`], [`check_parent_construct_receiver`],
//! [`dispatch_call`], [`call_construct`] and [`inout_write_back`].
//!
//! # Signatures
//!
//! As everywhere in `typing/` (see `../mod.rs`):
//!
//! - Labelled and optional arguments come first, in the OCaml order; an
//!   optional one is an `Option` (`None` for the default). `expected` is
//!   `Option<&expected_ty::T>` and `ctxt` is `&context::T`, as for `expr`.
//! - Positions are taken by reference (`p: &Pos`) and cloned where they are
//!   stored, as `call`, `overload_function` (part C), `lambda_expected`
//!   (part A), `Class_id.instantiable_cid` and `Assign.assign_` take them,
//!   and as part A calls the functions of this part.
//! - The results drop the environment: `(env, te, ty)` is `(te, ty)`, and
//!   `((env, te, ty), should_forget_fakes)` (the result of `dispatch_call`)
//!   is `((te, ty), should_forget_fakes)`.
//!
//! # Local functions
//!
//! The local functions of `dispatch_call` (`make_call`, `dispatch_id`,
//! `dispatch_class_const`, `type_structure_impl`, ...) and of `new_object`
//! (`gather`, `check_args`) are closures of the same names, which take the
//! environment as an argument, as in OCaml. `overload_function make_call fpos`
//! (a partial application) is written out at each of its three uses.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::local_id::LocalId;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use super::*;
use crate::aast_utils;
use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_utils;
use crate::diagnostics;
use crate::folded_class as cls;
use crate::folded_class::ClassElt;
use crate::naming_special_names::stdlib_functions;
use crate::pos_or_decl;
use crate::rt::ocaml_option;
use crate::tast;
/// `module TCO = Typechecker_options`
use crate::typechecker_options as tco;
use crate::typing::assign;
use crate::typing::class_get_expr;
use crate::typing::class_id;
use crate::typing::prelude::*;
use crate::typing_array_access;
use crate::typing_class_pointers;
use crate::typing_coeffects;
use crate::typing_coercion;
use crate::typing_defs::*;
use crate::typing_defs_constraints::*;
use crate::typing_defs_flags;
/// `module ExprDepTy = Typing_dependent_type.ExprDepTy`
use crate::typing_dependent_type::expr_dep_ty;
use crate::typing_disposable;
use crate::typing_dynamic;
use crate::typing_dynamic_utils;
use crate::typing_enforceability;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error_utils;
use crate::typing_helpers;
/// `module ExpectedTy = Typing_helpers.ExpectedTy`
use crate::typing_helpers::expected_ty;
use crate::typing_local_ops;
use crate::typing_log;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module TOG = Typing_object_get`
use crate::typing_object_get as tog;
use crate::typing_ops;
use crate::typing_packages;
/// `module Phase = Typing_phase`
use crate::typing_phase as phase;
use crate::typing_print;
/// `module Reason = Typing_reason`
use crate::typing_reason as reason;
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_shapes;
use crate::typing_solver;
use crate::typing_structure;
/// `module SubType = Typing_subtype`
use crate::typing_subtype as sub_type;
/// `module TUtils = Typing_utils`
use crate::typing_utils as tutils;
/// `module TVis = Typing_visibility`
use crate::typing_visibility as tvis;
use crate::utils::strip_ns;

/// `Typing_reason.localize` of the reason of a declared type.
fn localize_reason(r: &R) -> Reason {
    reason::localize(&r.clone().to_oxidized())
}

/// `Typing_defs.get_pos` of a declared type.
fn decl_get_pos(ty: &DeclTy) -> PosOrDecl {
    PosOrDecl::from(decl_utils::get_pos(ty))
}

/// The `(Pos_or_decl.t * string) list` of `Reason.to_string`, as messages.
fn messages(l: Vec<(PosOrDecl, String)>) -> Vec<Message<PosOrDecl>> {
    l.into_iter().map(|(p, s)| Message(p, s.into())).collect()
}

/// `Typing_error_utils.add_typing_error ~env (Typing_error.primary err)`
fn add_primary_error(err: primary::T, env: &Env) {
    typing_error_utils::add_typing_error(&typing_error::primary(err), env)
}

/// `Option.iter ~f:(Typing_error_utils.add_typing_error ~env) ty_err_opt`
fn add_typing_error_opt(ty_err_opt: Option<&typing_error::T>, env: &Env) {
    if let Some(ty_err) = ty_err_opt {
        typing_error_utils::add_typing_error(ty_err, env)
    }
}

/// `class_const ~under_type_structure ?attribute_check_policy ?incl_tc
/// ?require_class_ptr env p (cid, mid)`
pub fn class_const(
    under_type_structure: bool,
    attribute_check_policy: Option<AttributeCheckPolicy>,
    incl_tc: Option<bool>,
    require_class_ptr: Option<class_id::ClassnameExprError>,
    env: &mut Env,
    p: &Pos,
    (cid, mid): (&nast::ClassId, &aast::Pstring),
) -> (tast::Expr, Ty) {
    let attribute_check_policy = attribute_check_policy.unwrap_or(AttributeCheckPolicy::CheckAll);
    let incl_tc = incl_tc.unwrap_or(false);
    let require_class_ptr = require_class_ptr.unwrap_or(class_id::ClassnameExprError::Pass);
    let is_class_ptr = mid.1 == sn::members::M_CLASS;
    let (_tal, ce, cty): (Vec<tast::Targ>, tast::ClassId, Ty) = class_id::class_expr(
        None,                         // check_targs_integrity
        Some(attribute_check_policy), // attribute_check_policy
        None,                         // exact
        None,                         // check_explicit_targs
        None,                         // inside_nameof
        Some(true),                   // is_const
        Some(is_class_ptr),           // is_classptr
        None,                         // is_attribute
        None,                         // is_catch
        Some(require_class_ptr),      // require_class_ptr
        env,
        &[],
        cid,
    );
    let cty = match cid {
        aast::ClassId(_, _, aast::ClassId_::CI(sid)) if is_class_ptr => {
            fresh_generic_targs_for_bare_class(env, sid, cty)
        }
        _ => cty,
    };
    let should_check_packages = {
        let aast::ClassId(_, _, cid_) = cid;
        match cid_ {
            aast::ClassId_::CI(_) if !under_type_structure => true,
            _ => false,
        }
    };
    match get_node(&cty) {
        Ty_::Tclass((_, class_name), _, _) => {
            // Check package constraints on non-::class constants.
            // ::class is handled by class_expr via ClassPtrLinterOnly.
            // NB: this code will be superseded by the package check on CI once
            // the allow_classconst_violation carveout is removed
            if !is_class_ptr && should_check_packages {
                match env::get_class(env, class_name) {
                    decl_entry::T::Found(class_) => {
                        match tvis::check_package_access(
                            typing_packages::CheckReason::Yes(
                                primary::package::TargetSymbolSpec::ClassConst,
                            ),
                            p.clone(),
                            cls::pos(&class_),
                            env,
                            cls::get_package(&class_).as_ref(),
                            class_name.clone(),
                        ) {
                            tvis::PackageAccessResult::PackageAccessError(err) => {
                                typing_error_utils::add_typing_error(&err, env)
                            }
                            tvis::PackageAccessResult::PackageAccessLinterError((pos, w)) => {
                                let typing_packages::PackageWarningInfo {
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
                            tvis::PackageAccessResult::PackageAccessOk => {}
                        }
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
            if env::is_enum_class(env, class_name) && sn::members::M_CLASS != mid.1 {
                typing_local_ops::enforce_enum_class_variant(p.clone(), env)
            }
        }
        _ => {}
    }
    let (const_ty, _tal): (Ty, Vec<tast::Targ>) = class_get_expr::class_get(
        false, // is_method
        true,  // is_const
        None,  // transform_fty
        None,  // coerce_from_ty
        None,  // attribute_check_policy
        None,  // explicit_targs
        Some(incl_tc),
        None, // is_function_pointer
        env,
        cty.clone(),
        mid,
        cid,
    );
    let const_ty = map_reason(const_ty, |def| {
        let use_ = reason::class_const_access(p.clone());
        reason::flow_const_access(def, use_)
    });
    make_result(
        env,
        p.clone(),
        aast::Expr_::ClassConst(Box::new((ce, mid.clone()))),
        const_ty,
    )
}

/// `check_et_splice env p splice`: the result is `(tast, ty, macro_vars)`.
pub fn check_et_splice(
    env: &mut Env,
    p: &Pos,
    splice: &nast::EtSplice,
) -> (tast::Expr, Ty, Option<im::OrdMap<LocalId, (Pos, Ty)>>) {
    let (tast, ty, macro_vars) =
        env::with_outside_expr_tree(env, splice.macro_variables.as_deref(), |env, dsl_name| {
            et_splice(env, dsl_name, p, splice)
        });
    // If we are extracting the client type from a spliced variable, and the binding
    // for that variable indicates that the bound value came from a macro splice,
    // check that the enclosing expression tree has appropriate bindings.
    match splice {
        aast::EtSplice {
            extract_client_type: true,
            contains_await: _,
            macro_variables: _,
            spliced_expr: _,
            temp_lid: Some(v),
        } => {
            let local = env::get_local(env, v);
            match local.macro_splice_vars {
                Some(vars) => {
                    // `Local_id.Map.fold`, in the order of the keys.
                    for (id, (pos, ty_super)) in vars.iter() {
                        let ty_sub =
                            env::get_local_check_defined(env, &aast::Lid(pos.clone(), id.clone()))
                                .ty;
                        let ty_err_opt = sub_type::sub_type(
                            env,
                            None, // is_dynamic_aware
                            None, // is_coeffect
                            None, // ignore_readonly
                            None, // class_sub_classname
                            ty_sub,
                            ty_super.clone(),
                            Some(reasons_callback::unify_error_at(p.clone())),
                        );
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                    }
                    (tast, ty, macro_vars)
                }
                None => (tast, ty, macro_vars),
            }
        }
        _ => (tast, ty, macro_vars),
    }
}

/// `et_splice env dsl_opt p splice`
pub fn et_splice(
    env: &mut Env,
    dsl_opt: Option<aast::ClassName>,
    p: &Pos,
    splice: &nast::EtSplice,
) -> (tast::Expr, Ty) {
    let aast::EtSplice {
        spliced_expr,
        extract_client_type,
        contains_await,
        macro_variables,
        temp_lid,
    } = splice;
    let dsl_opt: Option<String> = dsl_opt.map(|ast_defs::Id(_, dsl_name)| dsl_name);
    // Error Reporting:
    //    The unification error reported by checking against `Spliceable<_, _, _>`
    //    is confusing to users. We improve the error message by including
    //    contextual information we pull from the definition of the DSL class.
    //
    //    Particularly we:
    //      - Use the type specified in the DSL classes splice method
    //      - If there is a docs url attached to the class, use it
    fn contextual_reasons(
        ty: &Ty,
        dsl_opt: &Option<String>,
        env: &Env,
    ) -> Option<Lazy<Vec<Message<PosOrDecl>>>> {
        let dsl_name = dsl_opt.as_ref()?;
        let cls = decl_entry::to_option(env::get_class(env, dsl_name))?;
        let ce = env::get_method(env, &cls, sn::expression_trees::SPLICE)?;
        let fun_ty: &DeclTy = &ce.ce_type;
        // Pull the type of third argument to `MyDsl::splice()`.
        // If we change the number of arguments this method takes, we might need to
        // update this match expression
        let splice_ty: DeclTy = match fun_ty.node_ref() {
            DeclTy_::Tfun(ft) => match &ft.params[..] {
                [_, _, splice_ty, ..] => splice_ty.ty.clone(),
                _ => return None,
            },
            _ => return None,
        };
        let ty = ty.clone();
        let dsl_name = dsl_name.clone();
        let env = env.clone();
        Some(Lazy::new(move || {
            error_reason(&splice_ty, &ty, &dsl_name, &env)
        }))
    }
    fn error_reason(
        splice_ty: &DeclTy,
        ty: &Ty,
        dsl_name: &str,
        env: &Env,
    ) -> Vec<Message<PosOrDecl>> {
        let err_splice_ty = format!(
            "Expected `{}` because you are splicing into a `{}` expression or block",
            typing_print::full_strip_ns_decl(None, false, env, &splice_ty.clone().to_oxidized()),
            strip_ns(dsl_name)
        );
        let err_ty = format!("But got `{}`", typing_print::full_strip_ns(true, env, ty));
        let mut reasons = reason::to_string(&err_splice_ty, &localize_reason(splice_ty.reason()));
        reasons.extend(reason::to_string(&err_ty, get_reason(ty)));
        messages(reasons)
    }
    let docs_url: Lazy<Option<String>> = {
        let env = env.clone();
        let dsl_opt = dsl_opt.clone();
        Lazy::new(move || {
            let dsl_name = dsl_opt.as_ref()?;
            let cls = decl_entry::to_option(env::get_class(&env, dsl_name))?;
            cls::get_docs_url(&cls)
        })
    };

    let (te, ty) = expr(None, &context::default(), env, spliced_expr);
    let ty = if *extract_client_type {
        let ty_visitor = env::fresh_type(env, p.clone());
        let ty_res = env::fresh_type(env, p.clone());
        let ty_infer = env::fresh_type(env, p.clone());
        let r = reason::splice(p.clone());
        let raw_spliceable_type =
            make_type::spliceable(r.clone(), ty_visitor, ty_res, ty_infer.clone());
        let spliceable_type = if tco::pessimise_builtins(&env::get_tcopt(env)) {
            make_type::locl_like(r, raw_spliceable_type)
        } else {
            raw_spliceable_type
        };

        let aast::Expr(_, expr_pos, _) = spliced_expr;
        // The callback is built (and `contextual_reasons` looks up the DSL
        // class) before the subtype check, as OCaml evaluates the arguments
        // before the call.
        let on_error = reasons_callback::expr_tree_splice_error(
            p.clone(),
            pos_or_decl::of_raw_pos(expr_pos.clone()),
            contextual_reasons(&ty, &dsl_opt, env),
            dsl_opt.as_deref(),
            docs_url,
        );
        let ty_err_opt = sub_type::sub_type(
            env,
            None, // is_dynamic_aware
            None, // is_coeffect
            None, // ignore_readonly
            None, // class_sub_classname
            ty,
            spliceable_type,
            Some(on_error),
        );
        add_typing_error_opt(ty_err_opt.as_ref(), env);
        ty_infer
    } else {
        ty
    };
    make_result(
        env,
        p.clone(),
        aast::Expr_::ETSplice(Box::new(aast::EtSplice {
            spliced_expr: te,
            extract_client_type: *extract_client_type,
            contains_await: *contains_await,
            macro_variables: macro_variables.clone(),
            temp_lid: temp_lid.clone(),
        })),
        ty,
    )
}

/// Typechecks a `new` expression.
/// If `is_attribute` is true, it's used for checking an attribute instantiation
/// as in `<<MyAttr()>> class C` (note that attributes are classes)
///
/// `new_object ~expected ~check_not_abstract ~is_using_clause ~is_attribute p
/// env cid explicit_targs el unpacked_element`: the result is `(tcid, tal,
/// tel, typed_unpack_element, new_ty, ctor_fty, should_forget_fakes)`.
pub fn new_object(
    expected: Option<&expected_ty::T>,
    check_not_abstract: bool,
    is_using_clause: bool,
    is_attribute: bool,
    p: &Pos,
    env: &mut Env,
    cid: &nast::ClassId,
    explicit_targs: &[nast::Targ],
    el: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
) -> (
    tast::ClassId,
    Vec<tast::Targ>,
    Vec<tast::Argument>,
    Option<tast::Expr>,
    Ty,
    Ty,
    bool,
) {
    let aast::ClassId(_, _, cid_) = cid;
    // Obtain class info from the cid expression. We get multiple
    // results with a CIexpr that has a union type, e.g. in
    //
    //  $classname = (mycond()? classname<A>: classname<B>);
    //  new $classname();
    let (tal, tcid, classes): NewableClassInfo = class_id::instantiable_cid(
        Some(Exact::Exact), // exact
        Some(is_attribute), // is_attribute
        None,               // is_catch
        p,
        env,
        cid_,
        explicit_targs,
    );
    let allow_abstract_bound_generic = match &tcid {
        aast::ClassId(ty, _, aast::ClassId_::CIreified(ast_defs::Id(_, tn))) => {
            is_generic_equal_to(tn, ty)
        }
        _ => false,
    };
    // The accumulator of the OCaml is `(env, tel, typed_unpack_element,
    // should_forget_fakes_acc)`; the closure takes the environment and the
    // last component, and returns the last three.
    let gather = |env: &mut Env,
                  should_forget_fakes_acc: bool,
                  (cname, class_info, c_ty): (PosId, cls::T, Ty)|
     -> ((Vec<tast::Argument>, Option<tast::Expr>, bool), (Ty, Ty)) {
        if check_not_abstract
            && cls::abstract_(&class_info)
            && !requires_consistent_construct(cid_)
            && !allow_abstract_bound_generic
        {
            uninstantiable_error(
                env,
                p,
                cid_,
                &cls::pos(&class_info),
                &cls::name(&class_info),
                p,
                &c_ty,
            );
        }
        let (obj_ty_, params): (Ty_, Vec<Ty>) = {
            let c_ty = env::expand_type(env, c_ty.clone());
            match (cid_, &tal[..], get_class_type(&c_ty)) {
                // Explicit type arguments
                (aast::ClassId_::CI(_), [_, ..], Some((_, _, tyl))) => {
                    (get_node(&c_ty).clone(), tyl)
                }
                (_, _, class_type_opt) => {
                    let params: Vec<Ty> = cls::tparams(&class_info)
                        .iter()
                        .map(|tparam| {
                            let tvar = env::fresh_type_reason(None, env, p.clone(), |tvid| {
                                reason::type_variable_generics(
                                    (
                                        p.clone(),
                                        tparam.name.id().as_str().to_string(),
                                        strip_ns(&cname.1).to_string(),
                                    ),
                                    tvid,
                                )
                            });
                            typing_log::log_new_tvar_for_new_object(env, p, &tvar, &cname, tparam);
                            tvar
                        })
                        .collect();
                    match class_type_opt {
                        Some((_, Exact::Exact, _)) => (
                            Ty_::Tclass(cname.clone(), Exact::Exact, params.clone()),
                            params,
                        ),
                        _ => (
                            Ty_::Tclass(cname.clone(), nonexact(), params.clone()),
                            params,
                        ),
                    }
                }
            }
        };
        if !is_using_clause && typing_disposable::is_disposable_class(env, &class_info) {
            add_primary_error(primary::T::InvalidNewDisposable(p.clone()), env);
        }
        let r_witness = reason::witness(p.clone());
        let obj_ty = mk((r_witness.clone(), obj_ty_));
        // `c_ty` is the one `gather` was given, not its expansion above.
        let c_ty = match cid_ {
            aast::ClassId_::CIstatic => mk((r_witness, get_node(&c_ty).clone())),
            aast::ClassId_::CIexpr(_) => {
                let c_ty = mk((r_witness, get_node(&c_ty).clone()));
                // When constructing from a (classname) variable, the variable
                // dictates what the constructed object is going to be. This allows
                // for generic and dependent types to be correctly carried
                // through the 'new $foo()' iff the constructed obj_ty is a
                // supertype of the variable-dictated c_ty
                let ty_err_opt = typing_ops::sub_type(None, 
                    p.clone(),
                    Ureason::URnone,
                    env,
                    c_ty.clone(),
                    obj_ty.clone(),
                    callback::unify_error(),
                );
                add_typing_error_opt(ty_err_opt.as_ref(), env);
                c_ty
            }
            _ => obj_ty.clone(),
        };
        let new_ty = {
            let aast::ClassId(cid_ty, _, _) = &tcid;
            let cid_ty = env::expand_type(env, cid_ty.clone());
            if is_generic(&cid_ty) {
                cid_ty
            } else {
                expr_dep_ty::make(env, cid_, c_ty.clone())
            }
        };
        // Set variance according to type of `new` expression now. Lambda arguments
        // to the constructor might depend on it, and `call_construct` only uses
        // `ctor_fty` to set the variance which has void return type
        env::set_tyvar_variance(env, None, None, &new_ty);
        let (tel, typed_unpack_element, ctor_fty, should_forget_fakes) = {
            check_expected_ty("New", env, &new_ty, expected);
            let attribute_check_policy = if is_attribute {
                AttributeCheckPolicy::SkipPackage
            } else {
                AttributeCheckPolicy::CheckAll
            };
            call_construct(
                Some(attribute_check_policy),
                p,
                env,
                &class_info,
                &params,
                el,
                unpacked_element,
                cid,
                new_ty,
            )
        };
        let should_forget_fakes_acc = should_forget_fakes_acc || should_forget_fakes;
        if env::get_construct(env, &class_info).1 == ConsistentKind::Inconsistent {
            match cid_ {
                aast::ClassId_::CIstatic => {
                    let (class_pos, class_name) = &cname;
                    add_primary_error(
                        primary::T::NewInconsistentConstruct {
                            pos: p.clone(),
                            class_name: class_name.clone(),
                            class_pos: class_pos.clone(),
                            kind: primary::NewInconsistentConstructKind::Static,
                        },
                        env,
                    )
                }
                aast::ClassId_::CIexpr(_) => {
                    let (class_pos, class_name) = &cname;
                    add_primary_error(
                        primary::T::NewInconsistentConstruct {
                            pos: p.clone(),
                            class_name: class_name.clone(),
                            class_pos: class_pos.clone(),
                            kind: primary::NewInconsistentConstructKind::Classname,
                        },
                        env,
                    )
                }
                _ => {}
            }
        }
        match cid_ {
            aast::ClassId_::CIparent => {
                let ctor_fty = match env::get_construct(env, &class_info).0 {
                    Some(ce) => {
                        let ty: &DeclTy = &ce.ce_type;
                        let ety_env = ExpandEnv {
                            substs: tutils::make_locl_subst_for_class_tparams(&class_info, &params),
                            this_ty: obj_ty.clone(),
                            ..empty_expand_env()
                        };
                        if get_ce_abstract(&ce) {
                            add_primary_error(
                                primary::T::ParentAbstractCall {
                                    meth_name: sn::members::__CONSTRUCT.to_string(),
                                    pos: p.clone(),
                                    decl_pos: get_pos(&ctor_fty),
                                },
                                env,
                            );
                        }
                        let (ty_err_opt, ctor_fty) = phase::localize(&ety_env, env, ty);
                        add_typing_error_opt(ty_err_opt.as_ref(), env);
                        ctor_fty
                    }
                    None => ctor_fty,
                };
                (
                    (tel, typed_unpack_element, should_forget_fakes_acc),
                    (obj_ty, ctor_fty),
                )
            }
            aast::ClassId_::CIstatic
            | aast::ClassId_::CI(_)
            | aast::ClassId_::CIself
            | aast::ClassId_::CIreified(_) => (
                (tel, typed_unpack_element, should_forget_fakes_acc),
                (c_ty, ctor_fty),
            ),
            aast::ClassId_::CIexpr(_) => (
                (tel, typed_unpack_element, should_forget_fakes_acc),
                (c_ty, ctor_fty),
            ),
        }
    };
    let (had_dynamic, classes) = {
        let mut seen_dynamic = false;
        let mut acc: Vec<(PosId, cls::T, Ty)> = vec![];
        for class_or_dynamic in classes {
            match class_or_dynamic {
                ClassOrDynamic::Dynamic => seen_dynamic = true,
                ClassOrDynamic::Class(cname, class_info, c_ty) => {
                    acc.push((cname, class_info, c_ty))
                }
            }
        }
        // The OCaml conses each class onto the accumulator: the list it
        // folds over next is in the reverse order.
        acc.reverse();
        (seen_dynamic, acc)
    };
    // `List.fold_map classes ~init:(env, [], None, false) ~f:gather`
    let mut tel: Vec<tast::Argument> = vec![];
    let mut typed_unpack_element: Option<tast::Expr> = None;
    let mut should_forget_fakes = false;
    let mut class_types_and_ctor_types: Vec<(Ty, Ty)> = vec![];
    for class in classes {
        let ((tel_, typed_unpack_element_, should_forget_fakes_), tys) =
            gather(env, should_forget_fakes, class);
        tel = tel_;
        typed_unpack_element = typed_unpack_element_;
        should_forget_fakes = should_forget_fakes_;
        class_types_and_ctor_types.push(tys);
    }
    let class_types_and_ctor_types = {
        let r = reason::dynamic_construct(p.clone());
        let dyn_ = (
            mk((r.clone(), Ty_::Tdynamic(None))),
            mk((r, Ty_::Tdynamic(None))),
        );
        if had_dynamic {
            let mut l = vec![dyn_];
            l.extend(class_types_and_ctor_types);
            l
        } else {
            class_types_and_ctor_types
        }
    };
    let check_args = |env: &mut Env| -> (Vec<tast::Argument>, Option<tast::Expr>) {
        let attribute_check_policy = if is_attribute {
            AttributeCheckPolicy::SkipPackage
        } else {
            AttributeCheckPolicy::CheckAll
        };
        let ctxt = context::T {
            attribute_check_policy,
            ..context::default()
        };
        let (tel, _): (Vec<tast::Argument>, Vec<Ty>) = argument_list_exprs(
            |env: &mut Env, e: &nast::Expr| expr(None, &ctxt, env, e),
            env,
            el,
        );
        let (typed_unpack_element, _) = match unpacked_element {
            None => (None, make_type::nothing(reason::none())),
            Some(unpacked_element) => {
                let (e, ty) = expr(None, &ctxt, env, unpacked_element);
                (Some(e), ty)
            }
        };
        (tel, typed_unpack_element)
    };
    let (tel, typed_unpack_element, ty, ctor_fty) = match &class_types_and_ctor_types[..] {
        [] => {
            let (tel, typed_unpack_element) = check_args(env);
            let ty = env::fresh_type_error(env, p.clone());
            (tel, typed_unpack_element, ty.clone(), ty)
        }
        [(ty, ctor_fty)] if is_dynamic(ty) => {
            let (tel, typed_unpack_element) = check_args(env);
            (tel, typed_unpack_element, ty.clone(), ctor_fty.clone())
        }
        [(ty, ctor_fty)] => (tel, typed_unpack_element, ty.clone(), ctor_fty.clone()),
        l => {
            let (tyl, ctyl): (Vec<Ty>, Vec<Ty>) = l.iter().cloned().unzip();
            let r = reason::witness(p.clone());
            (
                tel,
                typed_unpack_element,
                mk((r.clone(), Ty_::Tunion(tyl))),
                mk((r, Ty_::Tunion(ctyl))),
            )
        }
    };
    let new_ty = {
        let aast::ClassId(cid_ty, _, _) = &tcid;
        let cid_ty = env::expand_type(env, cid_ty.clone());
        // The OCaml drops the environment `strip_dynamic` returns.
        let stripped_cid_ty = typing_dynamic_utils::strip_dynamic(&mut env.clone(), cid_ty.clone());
        if is_generic(&stripped_cid_ty) {
            cid_ty
        } else {
            expr_dep_ty::make(env, cid_, ty)
        }
    };
    (
        tcid,
        tal,
        tel,
        typed_unpack_element,
        new_ty,
        ctor_fty,
        should_forget_fakes,
    )
}

/// `array_value ~expected env x`
pub fn array_value(
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    x: &nast::Expr,
) -> (tast::Expr, Ty) {
    let (te, ty) = expr(expected, &context::default(), env, x);
    (te, ty)
}

/// `arraykey_value p class_name is_set ~expected env x`
pub fn arraykey_value(
    p: &Pos,
    class_name: &str,
    is_set: bool,
    expected: Option<&expected_ty::T>,
    env: &mut Env,
    x: &nast::Expr,
) -> (tast::Expr, Ty) {
    let aast::Expr(_, pos, _) = x;
    let (te, ty) = array_value(expected, env, x);
    // A class pointer in a key position is used for its name.
    let ty = typing_class_pointers::coerce_to_name(env, ty);
    let (ty_arraykey, reason) = if is_set {
        (
            make_type::arraykey(reason::idx_set_element(pos.clone())),
            reason::set_element(class_name),
        )
    } else {
        (
            make_type::arraykey(reason::idx_dict(pos.clone())),
            reason::index_class(class_name),
        )
    };
    let ty_expected = ty_arraykey;
    let (ty_err_opt, te) = {
        // If we have an error in coercion here, we will add a `Hole` indicating the
        //   actual and expected type. The `Hole` may then be used in a codemod to
        //   add a call to `UNSAFE_CAST` so we need to consider what type we expect.
        //
        //   If we were to add an expected type of 'arraykey' here it would be
        //   correct but adding an `UNSAFE_CAST<?string,arraykey>($x)` means we
        //   get cascading errors if we have e.g. a return type of keyset<string>.
        //
        //   To try and prevent this, if this is an optional type where the nonnull
        //   part can be coerced to arraykey, we prefer that type as our expected type.
        let (ty_actual, is_option) = match get_node(&ty) {
            Ty_::Toption(ty_inner) => (ty_inner.clone(), true),
            _ => (ty.clone(), false),
        };
        let e1 = typing_coercion::coerce_type(
            Some(true), // coerce_for_op
            None,       // is_dynamic_aware
            None,       // ignore_readonly
            p.clone(),
            reason.clone(),
            env,
            ty_actual.clone(),
            ty_expected,
            Enforcement::Enforced, // TODO akenn: flow in
            callback::unify_error(),
        );
        let (ty_mismatch_opt, e2) = match &e1 {
            None if is_option => {
                let ty_str: Lazy<String> = {
                    let env = env.clone();
                    let ty_actual = ty_actual.clone();
                    Lazy::new(move || typing_print::full_strip_ns(true, &env, &ty_actual))
                };
                let reasons_opt = Some({
                    let pos = pos.clone();
                    let ty = ty.clone();
                    ty_str.map(move |ty_str| {
                        let mut reasons = messages(reason::to_string(
                            "Expected `arraykey`",
                            &reason::idx_dict(pos),
                        ));
                        reasons.push(Message(
                            get_pos(&ty),
                            format!("But got `?{}`", ty_str).into(),
                        ));
                        reasons
                    })
                });
                // We actually failed so generate the error we should
                // have seen
                let ty_err = typing_error::primary(primary::T::UnifyError {
                    pos: pos.clone(),
                    msg_opt: Some(reason::string_of_ureason(&reason)),
                    reasons_opt,
                });
                (Some((ty.clone(), ty_actual.clone())), Some(ty_err))
            }
            Some(_) | None => (None, None),
        };
        let ty_err_opt = ocaml_option::merge(e1, e2, typing_error::both);
        (ty_err_opt, hole_on_ty_mismatch(te, ty_mismatch_opt))
    };

    add_typing_error_opt(ty_err_opt.as_ref(), env);

    (te, ty)
}

/// Check that the parent exists in a parent::__construct call
pub fn check_parent_construct_receiver(pos: &Pos, env: &Env) {
    match env::get_parent_ty(env) {
        // Direct parent, so ok
        Some(_parent) => {}
        None => match env::get_self_id(env) {
            Some(self_) => {
                use trait_most_concrete_parent::T::Found;
                use trait_most_concrete_parent::T::NotFound;
                match env::get_class(env, &self_) {
                    // Self is a trait, so look at trait's parents
                    decl_entry::T::Found(trait_) if ast_defs::is_c_trait(cls::kind(&trait_)) => {
                        match trait_most_concrete_parent(&trait_, env) {
                            None => add_primary_error(primary::T::ParentInTrait(pos.clone()), env),
                            Some(NotFound) => {
                                let trait_reqs = Some(
                                    cls::all_ancestor_req_class_requirements(&trait_)
                                        .into_iter()
                                        .chain(cls::all_ancestor_req_this_as_requirements(&trait_))
                                        .map(|req| PosOrDecl::from(req.pos))
                                        .collect(),
                                );
                                add_primary_error(
                                    primary::T::ParentUndefined {
                                        pos: pos.clone(),
                                        trait_reqs,
                                    },
                                    env,
                                )
                            }
                            Some(Found(c, _parent_ty)) => match env::get_construct(env, &c) {
                                (_, ConsistentKind::Inconsistent) => add_primary_error(
                                    primary::T::TraitParentConstructInconsistent {
                                        pos: pos.clone(),
                                        decl_pos: cls::pos(&c),
                                    },
                                    env,
                                ),
                                _ => {}
                            },
                        }
                    }
                    _ => {}
                }
            }
            None => {
                // We're not even inside a class
                add_primary_error(primary::T::ParentOutsideClass(pos.clone()), env)
            }
        },
    }
}

/// Depending on the kind of expression we are dealing with
/// The typing of call is different.
///
/// `dispatch_call ?require_readonly_this ~expected ~ctxt p env e
/// explicit_targs el unpacked_element`: the result is `((te, ty),
/// should_forget_fakes)`.
pub fn dispatch_call(
    require_readonly_this: Option<bool>,
    expected: Option<&expected_ty::T>,
    ctxt: &context::T,
    p: &Pos,
    env: &mut Env,
    e: &nast::Expr,
    explicit_targs: &[nast::Targ],
    el: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
) -> ((tast::Expr, Ty), bool) {
    let require_readonly_this = require_readonly_this.unwrap_or(false);
    let aast::Expr(_, fpos, fun_expr) = e;
    let make_call = |env: &mut Env,
                     func: tast::Expr,
                     targs: Vec<tast::Targ>,
                     args: Vec<tast::Argument>,
                     unpacked_arg: Option<tast::Expr>,
                     ty: Ty|
     -> (tast::Expr, Ty) {
        make_result(
            env,
            p.clone(),
            aast::Expr_::Call(Box::new(aast::CallExpr {
                func,
                targs,
                args,
                unpacked_arg,
            })),
            ty,
        )
    };
    let matches_auto_complete_suffix =
        |x: &str| x.ends_with(crate::autocomplete_types::AUTOCOMPLETE_TOKEN);
    // When autocompleting a call such as
    //   foo(#AUTO332
    // to a function whose signature is similar to
    //   function foo<Targs as (mixed...)>(HH\EnumClass\Label<C, Targs> $label, ...Targs $args): void
    // we filter the possible values for $label according to the type, which includes a Targs generic.
    // Unfortunately, in the absence of any arguments, we end up inferring () for Targs, and so we lose
    // enum constants that make sense if there are other arguments.
    //
    // A somewhat hacky fix is to pretend that there may be more arguments by adding a bogus
    // unpacked element. This stops type inference from eagerly filling in
    // an empty tuple for a splat parameter.
    let omitted: nast::Expr;
    let unpacked_element: Option<&nast::Expr> = if unpacked_element.is_none()
        && el.iter().any(|arg| match arg {
            aast::Argument::Anormal(aast::Expr(_, _, aast::Expr_::EnumClassLabel(label))) => {
                match &**label {
                    (None, n) if matches_auto_complete_suffix(n) => true,
                    _ => false,
                }
            }
            _ => false,
        }) {
        omitted = aast::Expr((), p.clone(), aast::Expr_::Omitted);
        Some(&omitted)
    } else {
        unpacked_element
    };
    // For special functions and pseudofunctions with a definition in an HHI
    // file.
    let make_call_special_from_def = |env: &mut Env,
                                      id: &nast::Sid,
                                      tel: Vec<tast::Argument>,
                                      ty_: fn(Reason) -> Ty|
     -> (tast::Expr, Ty) {
        let (fty, tal) = fun_id::synth_for_call(id, explicit_targs, el.len() as isize, env);
        let ty = match get_node(&fty) {
            Ty_::Tfun(ft) => ft.ret.clone(),
            _ => ty_(reason::witness(p.clone())),
        };
        let te = typing_helpers::make_simplify_typed_expr(
            env,
            fpos.clone(),
            fty,
            aast::Expr_::Id(Box::new(id.clone())),
        );
        make_call(env, te, tal, tel, None, ty)
    };
    // Require [get_idisposable_value()] function calls to be inside a [using]
    // statement.
    let check_disposable_in_return = |env: &Env, fty: &Ty| {
        if is_return_disposable_fun_type(env, fty) && !ctxt.is_using_clause {
            add_primary_error(primary::T::InvalidNewDisposable(p.clone()), env)
        }
    };

    let dispatch_id = |env: &mut Env, id: &nast::Sid| -> ((tast::Expr, Ty), bool) {
        let (fty, tal) = fun_id::synth_for_call(id, explicit_targs, el.len() as isize, env);
        check_disposable_in_return(env, &fty);
        let (tel, typed_unpack_element, ty, should_forget_fakes): (
            Vec<tast::Argument>,
            Option<tast::Expr>,
            Ty,
            bool,
        ) = call(
            expected,
            None, // nullsafe
            None, // attribute_check_policy
            None, // in_await
            None, // dynamic_func
            p,
            &id.0,
            &id.0,
            env,
            fty.clone(),
            el,
            unpacked_element,
        );
        // Dynamic inference: special-case idx()/Readonly\idx() on dynamic
        // containers with shadow type variables. Create a shadow for the result
        // value and emit a can_index constraint, mirroring what array_get does
        // for $d['key']. idx() goes through function dispatch rather than
        // array_get, so we handle it here.
        let ty = if env::get_tcopt(env).tco_dynamic_inference
            && (id.1 == sn::fb::IDX || id.1 == sn::readonly::IDX)
        {
            match (&tel[..], el) {
                (
                    [
                        aast::Argument::Anormal(aast::Expr(container_ty, _, _)),
                        aast::Argument::Anormal(aast::Expr(key_ty, _, _)),
                        ..,
                    ],
                    [
                        _,
                        aast::Argument::Anormal(aast::Expr(_, key_pos, key_expr_)),
                        ..,
                    ],
                ) => match get_node(container_ty) {
                    Ty_::Tdynamic(Some(shadow_v)) => {
                        let shadow_v = *shadow_v;
                        let v_val = env::fresh_shadow_tyvar(env, p.clone());
                        let ci_val = mk((get_reason(&ty).clone(), Ty_::Tdynamic(Some(v_val))));
                        let ci = CanIndex {
                            key: key_ty.clone(),
                            val: ci_val.clone(),
                            index_expr: aast::Expr((), key_pos.clone(), key_expr_.clone()),
                            access_kind: CiAccessKind::CiLhsOfNullCoalesce,
                            expr_pos: p.clone(),
                            array_pos: fpos.clone(),
                            index_pos: key_pos.clone(),
                        };
                        env::add_tyvar_upper_bound(
                            None,
                            env,
                            shadow_v,
                            InternalType::ConstraintType(mk_constraint_type((
                                reason::witness(p.clone()),
                                ConstraintType_::TcanIndex(ci),
                            ))),
                        );
                        ci_val
                    }
                    _ => ty,
                },
                _ => ty,
            }
        } else {
            ty
        };
        let inner_te = typing_helpers::make_simplify_typed_expr(
            env,
            fpos.clone(),
            fty,
            aast::Expr_::Id(Box::new(id.clone())),
        );
        let result = make_call(env, inner_te, tal, tel, typed_unpack_element, ty);
        (result, should_forget_fakes)
    };
    // The optional transform_fty parameter is used to transform function
    // type decls for special static methods, currently just Shapes::at
    // and Shapes::idx
    let dispatch_class_const = |env: &mut Env,
                                e1: &nast::ClassId,
                                m: &aast::Pstring,
                                transform_fty: Option<&dyn Fn(DeclFunType) -> DeclFunType>|
     -> ((tast::Expr, Ty), bool) {
        let aast::ClassId(_, pos, e1_) = e1;
        let require_class_ptr = class_id::ClassnameExprError::Error;
        let (_tal, tcid, ty1): (Vec<tast::Targ>, tast::ClassId, Ty) = class_id::class_expr(
            None,                    // check_targs_integrity
            None,                    // attribute_check_policy
            None,                    // exact
            None,                    // check_explicit_targs
            None,                    // inside_nameof
            None,                    // is_const
            None,                    // is_classptr
            None,                    // is_attribute
            None,                    // is_catch
            Some(require_class_ptr), // require_class_ptr
            env,
            &[],
            e1,
        );
        let this_ty = make_type::this(reason::witness(fpos.clone()));
        // In static context, you can only call parent::foo() on static methods.
        // In instance context, you can call parent:foo() on static
        // methods as well as instance methods
        let is_static = !matches!(e1_, aast::ClassId_::CIparent)
            || env::is_static(env)
            || class_contains_smethod(env, &ty1, m);
        let (ty_err_opt, (fty, tal)) = if !is_static {
            // parent::nonStaticFunc() is really weird. It's calling a method
            // defined on the parent class, but $this is still the child class.
            tog::obj_get(
                pos.clone(),
                true, // is_method
                None, // nullsafe
                None, // coerce_from_ty
                explicit_targs,
                e1_,
                &ast_defs::Id(m.0.clone(), m.1.clone()),
                callback::unify_error(),
                Some(ty1.clone()), // parent_ty
                env,
                this_ty,
            )
        } else {
            let res: (Ty, Vec<tast::Targ>) = class_get_expr::class_get(
                true,  // is_method
                false, // is_const
                transform_fty,
                None, // coerce_from_ty
                None, // attribute_check_policy
                Some(explicit_targs),
                None, // incl_tc
                None, // is_function_pointer
                env,
                ty1.clone(),
                m,
                e1,
            );
            (None, res)
        };
        add_typing_error_opt(ty_err_opt.as_ref(), env);
        check_disposable_in_return(env, &fty);
        let (tel, typed_unpack_element, ty, should_forget_fakes): (
            Vec<tast::Argument>,
            Option<tast::Expr>,
            Ty,
            bool,
        ) = call(
            expected,
            None, // nullsafe
            None, // attribute_check_policy
            None, // in_await
            None, // dynamic_func
            p,
            fpos,
            fpos,
            env,
            fty.clone(),
            el,
            unpacked_element,
        );
        let te = typing_helpers::make_simplify_typed_expr(
            env,
            fpos.clone(),
            fty,
            aast::Expr_::ClassConst(Box::new((tcid, m.clone()))),
        );
        let result = make_call(env, te, tal, tel, typed_unpack_element, ty);
        (result, should_forget_fakes)
    };
    // The OCaml closure captures the environment `dispatch_call` was given
    // (it has no `env` parameter); it is only called before anything changes
    // that environment, so here it takes it as an argument.
    let type_structure_impl = |env: &mut Env,
                               fn_: &str,
                               pos: &Pos,
                               e1: &nast::Argument,
                               e2: &nast::Argument|
     -> (tast::Expr, Ty) {
        match aast_utils::arg_to_expr(e2) {
            aast::Expr(_, p, aast::Expr_::String(cst)) => {
                // find the class constant implicitly defined by the typeconst
                let e1 = aast_utils::arg_to_expr(e1);
                let cid_of_expr: nast::ClassId;
                let cid: &nast::ClassId = match &e1.2 {
                    aast::Expr_::ClassConst(cc) if cc.1.1 == sn::members::M_CLASS => &cc.0,
                    aast::Expr_::ClassGet(cg) if cg.1.1 == sn::members::M_CLASS => &cg.0,
                    _ => {
                        let e1_ = e1;
                        let aast::Expr(_, p1, _) = e1_;
                        cid_of_expr =
                            aast::ClassId((), p1.clone(), aast::ClassId_::CIexpr(e1_.clone()));
                        &cid_of_expr
                    }
                };
                // `TUtils.is_tyvar_error env ty` and the error below use the
                // environment from before `class_const`, as in OCaml.
                let env_before = env.clone();
                let mid: aast::Pstring = (p.clone(), cst.to_string());
                let result = class_const(
                    true,                                      // under_type_structure
                    None,                                      // attribute_check_policy
                    Some(true),                                // incl_tc
                    Some(class_id::ClassnameExprError::Error), // require_class_ptr
                    env,
                    p,
                    (cid, &mid),
                );
                match &result {
                    (aast::Expr(ty, _, _), _) if tutils::is_tyvar_error(&env_before, ty) => {
                        add_primary_error(
                            primary::T::IllegalTypeStructure {
                                pos: pos.clone(),
                                msg: "Could not resolve the type constant".to_string(),
                                fn_: fn_.to_string(),
                            },
                            &env_before,
                        )
                    }
                    _ => {}
                }
                match cid {
                    aast::ClassId(_, _, aast::ClassId_::CIstatic) => {
                        crate::typing_needs_concrete::check_abstract_tconst_via_static(
                            env,
                            pos,
                            &cst.to_string(),
                        )
                    }
                    _ => {}
                }
                result
            }
            _ => {
                add_primary_error(
                    primary::T::IllegalTypeStructure {
                        pos: pos.clone(),
                        msg: "Second argument is not a string".to_string(),
                        fn_: fn_.to_string(),
                    },
                    env,
                );
                expr_error(env, pos.clone(), e)
            }
        }
    };
    let type_structure_class_impl = |env: &mut Env,
                                     fn_: &str,
                                     make_ty: fn(Reason, Ty) -> Ty,
                                     pos: &Pos|
     -> ((tast::Expr, Ty), bool) {
        let should_forget_fakes = false;
        match el {
            [e1, e2] => {
                let (te, const_ty) = type_structure_impl(env, fn_, pos, e1, e2);
                let const_ty = env::expand_type(env, const_ty);
                let const_ty = typing_dynamic_utils::strip_dynamic(env, const_ty);
                let result = match get_node(&const_ty) {
                    Ty_::Tnewtype(name, tyl, _)
                        if tyl.len() == 1 && name == sn::fb::TYPE_STRUCTURE =>
                    {
                        let ty_arg = &tyl[0];
                        if typing_structure::is_enum_or_classish(env, ty_arg) {
                            let ty = make_ty(get_reason(&const_ty).clone(), ty_arg.clone());
                            let aast::Expr(_, te_pos, te_) = te;
                            make_result(env, te_pos, te_, ty)
                        } else {
                            add_primary_error(
                                primary::T::IllegalTypeStructure {
                                    pos: pos.clone(),
                                    msg: "The type constant does not resolve to a classish type"
                                        .to_string(),
                                    fn_: fn_.to_string(),
                                },
                                env,
                            );
                            expr_error(env, pos.clone(), e)
                        }
                    }
                    _ => expr_error(env, pos.clone(), e),
                };
                (result, should_forget_fakes)
            }
            _ => panic!("assert false"),
        }
    };
    match fun_expr {
        // Special top-level function
        aast::Expr_::Id(id) if stdlib_functions::needs_special_dispatch(&id.1) => {
            let id: &nast::Sid = id;
            let ast_defs::Id(pos, x) = id;
            if x == sn::pseudo_functions::UNSAFE_CAST
                || x == sn::pseudo_functions::UNSAFE_NONNULL_CAST
            {
                // `unsafe_cast`
                let unsafe_cast = x;
                let result = match el {
                    _ => {
                        // first type the `unsafe_cast` as a call, handling arity errors
                        let (fty, tal) =
                            fun_id::synth_for_call(id, explicit_targs, el.len() as isize, env);
                        check_disposable_in_return(env, &fty);
                        let (tel, _, ty, _should_forget_fakes): (
                            Vec<tast::Argument>,
                            Option<tast::Expr>,
                            Ty,
                            bool,
                        ) = call(
                            expected,
                            None, // nullsafe
                            None, // attribute_check_policy
                            None, // in_await
                            None, // dynamic_func
                            p,
                            fpos,
                            pos,
                            env,
                            fty,
                            el,
                            unpacked_element,
                        );
                        // construct the `Hole` using default value and type arguments
                        // if necessary
                        let dflt_ty = env::fresh_type_invariant(env, p.clone());
                        let el = match tel.first() {
                            Some(arg) => aast_utils::arg_to_expr(arg).clone(),
                            None => tast::make_typed_expr(
                                fpos.clone(),
                                dflt_ty.clone(),
                                aast::Expr_::Null,
                            ),
                        };
                        let (ty_from, ty_to) = match &tal[..] {
                            [aast::Targ(ty_from, _), aast::Targ(ty_to, _), ..] => {
                                (ty_from.clone(), ty_to.clone())
                            }
                            [aast::Targ(ty, _), ..] => (ty.clone(), ty.clone()),
                            _ => (dflt_ty.clone(), dflt_ty.clone()),
                        };
                        // Dynamic inference: subtype the input against the cast target so
                        // that the target type is recorded as an upper bound on any shadow
                        // type variables, capturing "this dynamic was cast to T".
                        if env::get_tcopt(env).tco_dynamic_inference {
                            match tel.first() {
                                Some(aast::Argument::Anormal(aast::Expr(input_ty, _, _))) => {
                                    match get_node(input_ty) {
                                        Ty_::Tdynamic(Some(v)) => env::add_tyvar_upper_bound(
                                            None,
                                            env,
                                            *v,
                                            InternalType::LoclType(ty_to.clone()),
                                        ),
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                        let hole_source = if unsafe_cast == sn::pseudo_functions::UNSAFE_CAST {
                            aast::HoleSource::UnsafeCast(
                                explicit_targs
                                    .iter()
                                    .map(|aast::Targ(_, h)| h.clone())
                                    .collect(),
                            )
                        } else {
                            aast::HoleSource::UnsafeNonnullCast
                        };
                        let te = aast::Expr_::Hole(Box::new((el, ty_from, ty_to, hole_source)));
                        // Add special reason to the type under the like, so that type mismatches
                        // underneath the like are reported as "dynamic because the expression went
                        // through an UNSAFE_CAST"
                        let ty = match typing_dynamic_utils::try_strip_dynamic(None, None, env, &ty)
                        {
                            None => ty,
                            Some(ty) => {
                                let r = reason::unsafe_cast(p.clone());
                                make_type::locl_like(r.clone(), with_reason(ty, r))
                            }
                        };
                        make_result(env, p.clone(), te, ty)
                    }
                };
                let should_forget_fakes = false;
                (result, should_forget_fakes)
            } else if x == sn::pseudo_functions::ISSET {
                // Special function `isset`
                let isset = x;
                let ctxt = context::T {
                    accept_using_var: true,
                    check_defined: false,
                    ..context::default()
                };
                let (tel, _): (Vec<tast::Argument>, Vec<Ty>) = argument_list_exprs(
                    |env: &mut Env, e: &nast::Expr| expr(None, &ctxt, env, e),
                    env,
                    el,
                );
                if unpacked_element.is_some() {
                    add_primary_error(
                        primary::T::UnpackingDisallowedBuiltinFunction {
                            pos: p.clone(),
                            fn_name: isset.clone(),
                        },
                        env,
                    )
                }
                let should_forget_fakes = false;
                let result = make_call_special_from_def(env, id, tel, make_type::bool);
                (result, should_forget_fakes)
            } else if x == sn::pseudo_functions::UNSET {
                // Special function `unset`
                let unset = x;
                let (tel, _): (Vec<tast::Argument>, Vec<Ty>) = argument_list_exprs(
                    |env: &mut Env, e: &nast::Expr| expr(None, &context::default(), env, e),
                    env,
                    el,
                );
                if unpacked_element.is_some() {
                    add_primary_error(
                        primary::T::UnpackingDisallowedBuiltinFunction {
                            pos: p.clone(),
                            fn_name: unset.clone(),
                        },
                        env,
                    )
                }
                typing_local_ops::check_unset_target(env, &tel);
                let ty_err_opt = match (el, unpacked_element) {
                    (
                        [
                            aast::Argument::Anormal(aast::Expr(
                                _,
                                _,
                                aast::Expr_::ArrayGet(array_get),
                            )),
                        ],
                        None,
                    ) => match &**array_get {
                        (ea, Some(_)) => {
                            let (_te, ty) = expr(None, &context::default(), env, ea);
                            let r = reason::witness(p.clone());
                            let tmixed = make_type::mixed(r.clone());
                            let super_ = mk((
                                r.clone(),
                                Ty_::Tunion(vec![
                                    make_type::dynamic(r.clone()),
                                    make_type::dict(r.clone(), tmixed.clone(), tmixed.clone()),
                                    make_type::keyset(r, tmixed),
                                ]),
                            ));
                            let reason = {
                                let env = env.clone();
                                let ty = ty.clone();
                                Lazy::new(move || {
                                    messages(reason::to_string(
                                        &format!(
                                            "This is {}",
                                            typing_print::error(Some(true), &env, &ty)
                                        ),
                                        get_reason(&ty),
                                    ))
                                })
                            };
                            sub_type::sub_type_or_fail(
                                env,
                                ty,
                                super_,
                                Some(typing_error::primary(primary::T::UnsetNonidxInStrict {
                                    pos: p.clone(),
                                    reason,
                                })),
                            )
                        }
                        (_, None) => {
                            let ty_err = typing_error::primary(primary::T::UnsetNonidxInStrict {
                                pos: p.clone(),
                                reason: Lazy::from_val(vec![]),
                            });
                            Some(ty_err)
                        }
                    },
                    // A single argument that isn't an element access is already a parse
                    // error, so don't pile on a second diagnostic.
                    ([_], None) => None,
                    _ => {
                        let ty_err = typing_error::primary(primary::T::UnsetNonidxInStrict {
                            pos: p.clone(),
                            reason: Lazy::from_val(vec![]),
                        });
                        Some(ty_err)
                    }
                };
                add_typing_error_opt(ty_err_opt.as_ref(), env);
                let should_forget_fakes = false;
                let result = make_call_special_from_def(env, id, tel, make_type::void);
                (result, should_forget_fakes)
            } else if x == stdlib_functions::TYPE_STRUCTURE
                && el.len() == 2
                && unpacked_element.is_none()
            {
                let type_structure = x;
                let should_forget_fakes = false;
                match el {
                    [e1, e2] => {
                        let result = type_structure_impl(env, type_structure, pos, e1, e2);
                        (result, should_forget_fakes)
                    }
                    _ => panic!("assert false"),
                }
            } else if x == stdlib_functions::TYPE_STRUCTURE_CLASSNAME
                && el.len() == 2
                && unpacked_element.is_none()
            {
                let type_structure_classname = x;
                fn make_ty(r: Reason, ty_arg: Ty) -> Ty {
                    make_type::classname(r, vec![ty_arg])
                }
                type_structure_class_impl(env, type_structure_classname, make_ty, pos)
            } else if x == stdlib_functions::TYPE_STRUCTURE_CLASS
                && el.len() == 2
                && unpacked_element.is_none()
            {
                let type_structure_class = x;
                fn make_ty(r: Reason, ty_arg: Ty) -> Ty {
                    mk((r, Ty_::TclassPtr(ty_arg)))
                }
                type_structure_class_impl(env, type_structure_class, make_ty, pos)
            } else {
                dispatch_id(env, id)
            }
        }
        // Special Shapes:: function
        aast::Expr_::ClassConst(class_const_)
            if match &class_const_.0 {
                aast::ClassId(_, _, aast::ClassId_::CI(ast_defs::Id(_, shapes))) => {
                    shapes == sn::shapes::SHAPES
                        || shapes == crate::naming_special_names::shapes::C_READONLY_SHAPES
                }
                _ => false,
            } =>
        {
            let (class_id, method_id) = &**class_const_;
            let (_, x) = method_id;
            if x == sn::shapes::AT || x == sn::shapes::IDX || x == sn::shapes::KEY_EXISTS {
                // Special functions `Shapes::at`, `Shapes::idx` and `Shapes::keyExists`.
                // We implement these by transforming the function type decl that's fetched
                // from the hhi
                let transform_fty: Option<Box<dyn Fn(DeclFunType) -> DeclFunType>> = match el {
                    // We expect the second argument to at, idx and keyExists to be a literal field name
                    [_, field, ..] => typing_shapes::do_with_field_expr(
                        env,
                        aast_utils::arg_to_expr(field),
                        None, // with_error
                        |field_name: TshapeFieldName| {
                            let method_id = ast_defs::Id(method_id.0.clone(), method_id.1.clone());
                            let nargs = el.len() as isize;
                            Some(Box::new(move |fty: DeclFunType| {
                                typing_shapes::transform_special_shapes_fun_ty(
                                    &field_name,
                                    &method_id,
                                    nargs,
                                    fty,
                                )
                            })
                                as Box<dyn Fn(DeclFunType) -> DeclFunType>)
                        },
                    ),
                    _ => None,
                };
                dispatch_class_const(env, class_id, method_id, transform_fty.as_deref())
            } else if x == crate::naming_special_names::shapes::PUT {
                // Special function `Shapes::put`
                // `overload_function make_call fpos p env class_id method_id el
                // unpacked_element f`
                overload_function(
                    &make_call,
                    fpos,
                    p,
                    env,
                    class_id,
                    method_id,
                    el,
                    unpacked_element,
                    |env: &mut Env,
                     _fty: &Ty,
                     res: Ty,
                     el: &[nast::Argument],
                     _tel: &[tast::Argument]|
                     -> Ty {
                        match el {
                            [
                                aast::Argument::Anormal(shape),
                                aast::Argument::Anormal(field),
                                aast::Argument::Anormal(value),
                            ] => {
                                let aast::Expr(_, shapepos, _) = shape;
                                let aast::Expr(_, fieldpos, _) = field;
                                let aast::Expr(_, valuepos, _) = value;
                                // infer the input shape type
                                let (_tes, tshape) = expr(None, &context::default(), env, shape);
                                // compute field type
                                let (_tef, tfield) = expr(None, &context::default(), env, field);
                                // compute value type
                                let (_tev, tvalue) = expr(None, &context::default(), env, value);
                                // compute assignment type
                                if env.genv.tcopt.tco_constraint_array_index_assign {
                                    let val_ty = env::fresh_type_invariant(env, p.clone());
                                    let ty_err_opt = sub_type::sub_type_i(
                                        env,
                                        None, // is_coeffect
                                        None, // class_sub_classname
                                        InternalType::LoclType(tshape),
                                        InternalType::ConstraintType(mk_constraint_type((
                                            reason::witness(p.clone()),
                                            ConstraintType_::TcanIndexAssign(CanIndexAssign {
                                                key: tfield,
                                                write: tvalue,
                                                val: val_ty.clone(),
                                                index_expr: field.clone(),
                                                expr_pos: shapepos.clone(),
                                                array_pos: p.clone(),
                                                index_pos: fieldpos.clone(),
                                                write_pos: valuepos.clone(),
                                            }),
                                        ))),
                                        Some(reasons_callback::unify_error_at(p.clone())),
                                    );
                                    add_typing_error_opt(ty_err_opt.as_ref(), env);
                                    val_ty
                                } else {
                                    let (
                                        res,
                                        _arr_ty_mismatch_opt,
                                        _key_ty_mismatch_opt,
                                        _val_ty_mismatch_opt,
                                    ) = typing_array_access::assign_array_get(
                                        p.clone(),        // array_pos
                                        shapepos.clone(), // expr_pos
                                        Ureason::URassign,
                                        env,
                                        tshape,
                                        field,
                                        tfield,
                                        tvalue,
                                    );
                                    res
                                }
                            }
                            _ => res,
                        }
                    },
                )
            } else if x == sn::shapes::REMOVE_KEY {
                // Special function `Shapes::removeKey`
                overload_function(
                    &make_call,
                    fpos,
                    p,
                    env,
                    class_id,
                    method_id,
                    el,
                    unpacked_element,
                    |env: &mut Env,
                     _fty: &Ty,
                     res: Ty,
                     el: &[nast::Argument],
                     _tel: &[tast::Argument]|
                     -> Ty {
                        match el {
                            [aast::Argument::Ainout(_, shape), field] => {
                                let lvar: Option<&LocalId> = match &shape.2 {
                                    aast::Expr_::Lvar(lid) => Some(&lid.1),
                                    aast::Expr_::Hole(hole) => match &hole.0.2 {
                                        aast::Expr_::Lvar(lid) => Some(&lid.1),
                                        _ => None,
                                    },
                                    _ => None,
                                };
                                match lvar {
                                    Some(lvar) => {
                                        // We reevaluate the shape instead of using the shape type
                                        // evaluated during typechecking against the HHI signature
                                        // because this argument is inout and bidirectional
                                        // typechecking causes a union with the open shape type
                                        // which defeats the purpose of this extra-logical function.
                                        let (_te, shape_ty) =
                                            expr(None, &context::default(), env, shape);
                                        let shape_ty = typing_shapes::remove_key(
                                            p.clone(),
                                            env,
                                            shape_ty,
                                            aast_utils::arg_to_expr(field),
                                        );
                                        set_valid_rvalue(
                                            None,
                                            p.clone(),
                                            env,
                                            lvar.clone(),
                                            None,
                                            shape_ty,
                                        );
                                        res
                                    }
                                    None => {
                                        let aast::Expr(_, shape_pos, _) = shape;
                                        typing_error_utils::add_typing_error(
                                            &typing_error::shape(
                                                primary::shape::T::InvalidShapeRemoveKey(
                                                    shape_pos.clone(),
                                                ),
                                            ),
                                            env,
                                        );
                                        res
                                    }
                                }
                            }
                            _ => res,
                        }
                    },
                )
            } else if x == sn::shapes::TO_DICT || x == sn::shapes::TO_ARRAY {
                // Special functions `Shapes::toDict` and `Shapes::toArray`
                overload_function(
                    &make_call,
                    fpos,
                    p,
                    env,
                    class_id,
                    method_id,
                    el,
                    unpacked_element,
                    |env: &mut Env,
                     _fty: &Ty,
                     res: Ty,
                     _el: &[nast::Argument],
                     tel: &[tast::Argument]|
                     -> Ty {
                        match tel {
                            [arg] => {
                                let aast::Expr(shape_ty, _, _) = aast_utils::arg_to_expr(arg);
                                typing_shapes::to_dict(env, p.clone(), shape_ty.clone(), res)
                            }
                            _ => res,
                        }
                    },
                )
            } else {
                dispatch_class_const(env, class_id, method_id, None)
            }
        }
        // Calling parent / class method
        aast::Expr_::ClassConst(class_const_) => {
            let (class_id, m) = &**class_const_;
            match (class_id, m) {
                (aast::ClassId(_, pos, aast::ClassId_::CIparent), (_, construct))
                    if construct == sn::members::__CONSTRUCT =>
                {
                    check_parent_construct_receiver(pos, env)
                }
                _ => {}
            }
            dispatch_class_const(env, class_id, m, None)
        }
        // Readonly Expressions do not affect the type, but need to be threaded through when they're part of a call
        aast::Expr_::ReadonlyExpr(r) => {
            env::set_readonly(env, true);
            // Recurse onto the inner call
            let ((te, ty), s) = dispatch_call(
                Some(true), // require_readonly_this
                expected,
                ctxt,
                p,
                env,
                r,
                explicit_targs,
                el,
                unpacked_element,
            );
            match te {
                aast::Expr(ty, _, aast::Expr_::Call(call_expr)) => {
                    let aast::CallExpr {
                        func,
                        targs,
                        args,
                        unpacked_arg,
                    } = *call_expr;
                    let aast::Expr(caller_ty, caller_pos, _) = &func;
                    let (caller_ty, caller_pos) = (caller_ty.clone(), caller_pos.clone());
                    // Rewrap the caller in the readonly expression after we're done
                    let wrapped_caller = typing_helpers::make_simplify_typed_expr(
                        env,
                        caller_pos,
                        caller_ty,
                        aast::Expr_::ReadonlyExpr(Box::new(func)),
                    );
                    let result = make_call(env, wrapped_caller, targs, args, unpacked_arg, ty);
                    (result, s)
                }
                te => ((te, ty), s),
            }
        }
        // Call instance method
        aast::Expr_::ObjGet(obj_get)
            if matches!(
                &**obj_get,
                (
                    _,
                    aast::Expr(_, _, aast::Expr_::Id(_)),
                    _,
                    ast_defs::PropOrMethod::IsMethod
                )
            ) =>
        {
            let (e1, member, nullflavor, _) = &**obj_get;
            let aast::Expr(_, pos_id, member_) = member;
            let aast::Expr_::Id(m) = member_ else {
                unreachable!("matched by the guard")
            };
            let m: &nast::Sid = m;
            // We should use the constraint only if we're sure that immediately doing
            // obj_get will fail to get to concrete types.
            fn should_use_constraint(seen: &im::OrdSet<String>, env: &mut Env, ty: Ty) -> bool {
                let ty = env::expand_type(env, ty);
                match get_node(&ty) {
                    Ty_::Tdynamic(_)
                    | Ty_::Tprim(_)
                    | Ty_::Ttuple(_)
                    | Ty_::Tfun(_)
                    | Ty_::Tshape(_)
                    | Ty_::Toption(_)
                    | Ty_::Tclass(..)
                    | Ty_::TvecOrDict(..)
                    | Ty_::TclassPtr(_)
                    | Ty_::Tlabel(_)
                    | Ty_::Tany(_)
                    | Ty_::Tnonnull
                    | Ty_::Tneg(_)
                    | Ty_::Taccess(_) => {
                        // All of these can be handled by obj_get
                        false
                    }
                    Ty_::Tvar(var) => {
                        let bounds = env::get_tyvar_lower_bounds(env, *var);
                        should_use_constraint_for_inter(
                            seen,
                            env,
                            crate::internal_type_set::to_list(&bounds)
                                .into_iter()
                                .filter_map(|ity| match ity {
                                    InternalType::LoclType(ty) => Some(ty),
                                    _ => None,
                                })
                                .collect(),
                        )
                    }
                    Ty_::Tunion(ts) => {
                        // If one of the branches of the union won't resolve,
                        // then obj_get will end up with a 4297 from trying to force solve
                        // `List.exists_env`
                        for ty in ts.clone() {
                            if should_use_constraint(seen, env, ty) {
                                return true;
                            }
                        }
                        false
                    }
                    Ty_::Tintersection(ts) => {
                        should_use_constraint_for_inter(seen, env, ts.clone())
                    }
                    Ty_::Tdependent(_, ty) => should_use_constraint(seen, env, ty.clone()),
                    Ty_::Tgeneric(name) | Ty_::Tnewtype(name, _, _) => {
                        if !seen.contains(name) {
                            let ts = tutils::get_concrete_supertypes(
                                None, // cache
                                None, // expand_supportdyn
                                None, // include_case_types
                                true, // abstract_enum
                                env,
                                ty.clone(),
                            );
                            should_use_constraint_for_inter(&seen.update(name.clone()), env, ts)
                        } else {
                            false
                        }
                    }
                }
            }
            fn should_use_constraint_for_inter(
                seen: &im::OrdSet<String>,
                env: &mut Env,
                ts: Vec<Ty>,
            ) -> bool {
                match &ts[..] {
                    [] => true,
                    [ty] => should_use_constraint(seen, env, ty.clone()),
                    _ => false,
                }
                // The constraint doesn't work well with intersections, so don't bother
            }
            let (te1, ty1) = expr(
                None,
                &context::T {
                    accept_using_var: true,
                    ..context::default()
                },
                env,
                e1,
            );
            let nullsafe = match nullflavor {
                ast_defs::OperatorNullFlavor::Regular => None,
                ast_defs::OperatorNullFlavor::Nullsafe => Some(p.clone()),
            };
            // These are the only kinds of calls that we support with constraint inference
            let maybe_use_constraint_inference =
                explicit_targs.is_empty() && unpacked_element.is_none() && nullsafe.is_none();
            let use_constraint_inference =
                if maybe_use_constraint_inference && env.genv.tcopt.tco_constraint_method_call {
                    // Config tells us to use it for all supported functions
                    true
                } else if maybe_use_constraint_inference
                    && env.in_expr_tree.is_some()
                    && tco::legacy_experimental_feature_enabled(
                        &env::get_tcopt(env),
                        tco::EXPERIMENTAL_TRY_CONSTRAINT_METHOD_INFERENCE,
                    )
                {
                    // Inside of an expression tree, we can use constraint inference if the appropriate experimental_tc_feature is enabled.
                    // Many of the features that constraint inference doesn't support are not allowed in expression trees: inout, disposable, etc.
                    should_use_constraint(&im::OrdSet::new(), env, ty1.clone())
                } else {
                    false
                };
            if use_constraint_inference {
                // Construct a function type from the types of the arguments, and check
                // that the receiver has a method that is a subtype of it. Since function parameters
                // are contravariant, this will check that the arguments are subtypes of the
                // parameters
                let duplicate_arg_names: Vec<String> = {
                    let mut acc: im::OrdSet<String> = im::OrdSet::new();
                    // Consed in OCaml: the last duplicate first.
                    let mut dupes: Vec<String> = vec![];
                    for arg in el {
                        match crate::typing_defs::named_params::name_of_arg(arg) {
                            Some(name) => {
                                // `S_set.add pre_existing_key` preserves physical equality
                                // https://ocaml.org/manual/5.3/api/Set.S.html
                                // (which is how the OCaml sees that the name is already
                                // in the set)
                                if acc.contains(&name) {
                                    dupes.push(name)
                                } else {
                                    acc.insert(name);
                                }
                            }
                            None => {}
                        }
                    }
                    dupes.reverse();
                    dupes
                };
                if !duplicate_arg_names.is_empty() {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::DuplicateNamedArgs {
                            duplicate_names: duplicate_arg_names,
                            pos: crate::pos::btw(pos_id, p),
                        }),
                        env,
                    )
                }
                let expr_with_edt = |env: &mut Env, e: &nast::Expr| -> (tast::Expr, Ty) {
                    let (tast, ty) = expr(None, &context::default(), env, e);
                    let ty = expr_dep_ty::make(env, &aast::ClassId_::CIexpr(e.clone()), ty);
                    (tast, ty)
                };
                let (args_tast, arg_tys): (Vec<tast::Argument>, Vec<Ty>) =
                    argument_list_exprs(expr_with_edt, env, el);
                let arg_posl: Vec<(Pos, Option<nast::Sid>, bool, bool)> = el
                    .iter()
                    .map(|arg| {
                        let (e, pos, name, is_inout) = match arg {
                            aast::Argument::Ainout(_, aast::Expr(_, pos, e)) => {
                                (e, pos, None, true)
                            }
                            aast::Argument::Anamed(n, aast::Expr(_, pos, e)) => {
                                (e, pos, Some(n.clone()), false)
                            }
                            aast::Argument::Anormal(aast::Expr(_, pos, e)) => (e, pos, None, false),
                        };
                        match e {
                            aast::Expr_::ReadonlyExpr(_) => (pos.clone(), name, true, is_inout),
                            _ => (pos.clone(), name, false, is_inout),
                        }
                    })
                    .collect();
                let make_param =
                    |(pos, name, is_readonly, is_inout): &(Pos, Option<nast::Sid>, bool, bool),
                     ty: Ty|
                     -> FunParam {
                        FunParam {
                            pos: pos_or_decl::of_raw_pos(pos.clone()),
                            name: name.as_ref().map(|ast_defs::Id(_, n)| n.clone()),
                            type_: ty,
                            flags: typing_defs_flags::fun_param::set_named(
                                name.is_some(),
                                typing_defs_flags::fun_param::set_inout(
                                    *is_inout,
                                    typing_defs_flags::fun_param::set_readonly(
                                        *is_readonly,
                                        typing_defs_flags::fun_param::default(),
                                    ),
                                ),
                            ),
                            def_value: None,
                        }
                    };
                let ty = env::fresh_type(env, p.clone());
                // `List.map2_exn`
                assert!(
                    arg_posl.len() == arg_tys.len(),
                    "List.map2_exn: lists have different lengths"
                );
                let ft_params: Vec<FunParam> = arg_posl
                    .iter()
                    .zip(arg_tys)
                    .map(|(arg_pos, ty)| make_param(arg_pos, ty))
                    .collect();
                let capability = Capability::CapTy(
                    env::get_local_check_defined(
                        env,
                        &aast::Lid(p.clone(), typing_coeffects::capability_id()),
                    )
                    .ty,
                );
                let tfty = mk((
                    reason::witness(p.clone()),
                    Ty_::Tfun(std::rc::Rc::new(FunType {
                        tparams: vec![],
                        where_constraints: vec![],
                        params: ft_params,
                        implicit_params: FunImplicitParams { capability },
                        ret: ty.clone(),
                        flags: typing_defs_flags::fun::set_readonly_this(
                            require_readonly_this,
                            typing_defs_flags::fun::set_returns_readonly(
                                ctxt.support_readonly_return,
                                typing_defs_flags::fun::default(),
                            ),
                        ),
                        instantiated: true,
                    })),
                ));
                let has_member_ty = make_type::has_member(
                    reason::witness(pos_id.clone()),
                    m.clone(),
                    tfty.clone(),
                    aast::ClassId_::CIexpr(e1.clone()),
                    Some(HasMemberMethod {
                        explicit_targs: vec![],
                        args_pos: arg_posl.iter().map(|(pos, _, _, _)| pos.clone()).collect(),
                    }),
                );
                let ty_err_opt = tutils::sub_type_i(
                    env,
                    None,
                    None, // is_coeffect
                    InternalType::LoclType(ty1.clone()),
                    has_member_ty,
                    Some(reasons_callback::unify_error_at(p.clone())),
                );
                add_typing_error_opt(ty_err_opt.as_ref(), env);
                let ty_mismatch_opt = mk_ty_mismatch_opt(
                    ty1,
                    make_type::nothing(reason::none()),
                    ty_err_opt.as_ref(),
                );
                let inner_te = typing_helpers::make_simplify_typed_expr(
                    env,
                    pos_id.clone(),
                    tfty.clone(),
                    aast::Expr_::Id(Box::new(m.clone())),
                );
                let te = typing_helpers::make_simplify_typed_expr(
                    env,
                    fpos.clone(),
                    tfty,
                    aast::Expr_::ObjGet(Box::new((
                        hole_on_ty_mismatch(te1, ty_mismatch_opt),
                        inner_te,
                        ast_defs::OperatorNullFlavor::Regular,
                        ast_defs::PropOrMethod::IsMethod,
                    ))),
                );
                let result = make_call(env, te, vec![], args_tast, None, ty);
                (result, true)
            } else {
                let aast::Expr(_, p1, _) = e1;
                let (ty_err_opt, (tfty, tal), lval_ty_mismatch_opt, _rval_ty_mismatch_opt) =
                    tog::obj_get_with_mismatches(
                        p1.clone(),       // obj_pos
                        true,             // is_method
                        nullsafe.clone(), // nullsafe
                        None,             // coerce_from_ty
                        explicit_targs,
                        &aast::ClassId_::CIexpr(e1.clone()),
                        m,
                        callback::unify_error(),
                        None, // parent_ty
                        env,
                        ty1,
                    );
                add_typing_error_opt(ty_err_opt.as_ref(), env);
                check_disposable_in_return(env, &tfty);
                let (tel, typed_unpack_element, ty, should_forget_fakes): (
                    Vec<tast::Argument>,
                    Option<tast::Expr>,
                    Ty,
                    bool,
                ) = call(
                    expected,
                    Some(nullsafe), // nullsafe
                    None,           // attribute_check_policy
                    None,           // in_await
                    None,           // dynamic_func
                    p,
                    p1,
                    pos_id,
                    env,
                    tfty.clone(),
                    el,
                    unpacked_element,
                );
                let inner_te = typing_helpers::make_simplify_typed_expr(
                    env,
                    pos_id.clone(),
                    tfty.clone(),
                    aast::Expr_::Id(Box::new(m.clone())),
                );
                let te = typing_helpers::make_simplify_typed_expr(
                    env,
                    fpos.clone(),
                    tfty,
                    aast::Expr_::ObjGet(Box::new((
                        hole_on_ty_mismatch(te1, lval_ty_mismatch_opt),
                        inner_te,
                        nullflavor.clone(),
                        ast_defs::PropOrMethod::IsMethod,
                    ))),
                );
                let result = make_call(env, te, tal, tel, typed_unpack_element, ty);
                (result, should_forget_fakes)
            }
        }
        // Function invocation
        aast::Expr_::Id(id) => dispatch_id(env, id),
        _ => {
            let fun_opt = aast_utils::get_fun_expr(e);
            // If we are immediately calling an lambda, then we don't want to conservatively
            // invalidate the refinements, because it won't escape. However, we do need to
            // invalidate any refinements that the argument expressions would invalidate.
            // Ideally, we'd check all non-lambda args before checking the function, but
            // that's a large refactor. Instead, we'll not invalidate when the arguments
            // are constant or variables, and so obviously don't need to invalidate.
            let ctxt = context::T {
                immediately_called_lambda: fun_opt.is_some()
                    && el
                        .iter()
                        .all(|e| aast_utils::is_const_expr(aast_utils::arg_to_expr(e))),
                ..context::default()
            };
            env::open_tyvars(env, p.clone());
            let fun_expected = match fun_opt {
                Some(fun_) => {
                    let ty = lambda_expected(p, env, fun_, el);
                    Some(expected_ty::make(
                        None,
                        None,
                        p.clone(),
                        Ureason::URparam,
                        ty,
                    ))
                }
                None => None,
            };
            let (te, fty) = expr(fun_expected.as_ref(), &ctxt, env, e);
            let ty_err_opt = typing_solver::close_tyvars_and_solve(env);
            add_typing_error_opt(ty_err_opt.as_ref(), env);
            let (ty_err_opt1, fty) = typing_solver::expand_type_and_solve(
                env,
                None,
                "a function value",
                fpos.clone(),
                fty,
            );
            check_disposable_in_return(env, &fty);
            let (tel, typed_unpack_element, ty, should_forget_fakes): (
                Vec<tast::Argument>,
                Option<tast::Expr>,
                Ty,
                bool,
            ) = call(
                expected,
                None, // nullsafe
                None, // attribute_check_policy
                None, // in_await
                None, // dynamic_func
                p,
                fpos,
                fpos,
                env,
                fty,
                el,
                unpacked_element,
            );
            // The error of `expand_type_and_solve` is reported after
            // `make_call`, with the environment of `call`.
            let env_of_call = env.clone();
            let result = make_call(
                env,
                te,
                // tal: no type arguments to function values, as they are non-generic
                vec![],
                tel,
                typed_unpack_element,
                ty,
            );
            add_typing_error_opt(ty_err_opt1.as_ref(), &env_of_call);
            (result, should_forget_fakes)
        }
    }
}

/// `call_construct ?attribute_check_policy p env class_ params el
/// unpacked_element cid cid_ty`: the result is `(tel, typed_unpack_element,
/// ctor_fty, should_forget_fakes)`.
pub fn call_construct(
    attribute_check_policy: Option<AttributeCheckPolicy>,
    p: &Pos,
    env: &mut Env,
    class_: &cls::T,
    params: &[Ty],
    el: &[nast::Argument],
    unpacked_element: Option<&nast::Expr>,
    cid: &nast::ClassId,
    cid_ty: Ty,
) -> (Vec<tast::Argument>, Option<tast::Expr>, Ty, bool) {
    let attribute_check_policy = attribute_check_policy.unwrap_or(AttributeCheckPolicy::CheckAll);
    let aast::ClassId(_, cid_pos, cid_) = cid;
    let r = reason::witness(p.clone());
    let cid_ty = if matches!(cid_, aast::ClassId_::CIparent) {
        make_type::this(r.clone())
    } else {
        cid_ty
    };
    let ety_env = ExpandEnv {
        this_ty: cid_ty,
        substs: tutils::make_locl_subst_for_class_tparams(class_, params),
        on_error: Some(reasons_callback::unify_error_at(p.clone())),
        ..empty_expand_env()
    };
    let cstr = env::get_construct(env, class_);
    match cstr.0 {
        None => {
            if !el.is_empty() || unpacked_element.is_some() {
                add_primary_error(primary::T::ConstructorNoArgs(p.clone()), env)
            }
            let ctxt = context::T {
                attribute_check_policy,
                ..context::default()
            };
            let (tel, _tyl): (Vec<tast::Argument>, Vec<Ty>) = argument_list_exprs(
                |env: &mut Env, e: &nast::Expr| expr(None, &ctxt, env, e),
                env,
                el,
            );
            let should_forget_fakes = true;
            let ty = make_type::default_construct(r);
            (tel, None, ty, should_forget_fakes)
        }
        Some(ClassElt {
            ce_visibility: vis,
            ce_type,
            ce_deprecated,
            ce_flags,
            ce_package_requirement,
            ..
        }) => {
            let m: &DeclTy = &ce_type;
            let def_pos = decl_get_pos(m);
            for ty_err in tvis::check_obj_access(
                true,  // is_method
                false, // is_receiver_interface
                p.clone(),
                def_pos.clone(),
                typing_defs_flags::class_elt::is_tests_bypass_visibility(ce_flags),
                env,
                &vis,
            ) {
                typing_error_utils::add_typing_error(&ty_err, env)
            }
            add_typing_error_opt(
                tvis::check_deprecated(p.clone(), def_pos.clone(), env, ce_deprecated).as_ref(),
                env,
            );
            // Obtain the type of the constructor
            let m: Ty = {
                let _r = localize_reason(m.reason());
                match m.node_ref() {
                    DeclTy_::Tfun(ft) => {
                        let ft = typing_enforceability::compute_enforced_and_pessimize_fun_type(
                            Some(class_),
                            env,
                            (**ft).clone(),
                        );
                        add_typing_error_opt(
                            tvis::check_cross_package(
                                p.clone(),
                                &def_pos,
                                env,
                                ce_package_requirement,
                            )
                            .as_ref(),
                            env,
                        );

                        // This creates type variables for non-denotable type parameters on constructors.
                        // These are notably different from the tparams on the class, which are handled
                        // at the top of this function. User-written type parameters on constructors
                        // are still a parse error. This is a no-op if ft.ft_tparams is empty.
                        let (ty_err_opt1, implicit_constructor_targs) = phase::localize_targs(
                            true, // check_type_integrity
                            true, // is_method
                            def_pos.clone(),
                            p.clone(),
                            "constructor".to_string(),
                            None, // check_explicit_targs
                            env,
                            &ft.tparams,
                            vec![],
                        );
                        add_typing_error_opt(ty_err_opt1.as_ref(), env);
                        let (ty_err_opt2, ft) = phase::localize_ft(
                            Some(phase::MethodInstantiation {
                                use_name: "constructor".to_string(),
                                use_pos: p.clone(),
                                explicit_targs: implicit_constructor_targs,
                            }),
                            &ety_env,
                            def_pos.clone(),
                            env,
                            &ft,
                        );
                        add_typing_error_opt(ty_err_opt2.as_ref(), env);
                        let should_wrap =
                            typing_defs_flags::class_elt::supports_dynamic_type(ce_flags)
                                || cls::get_support_dynamic_type(class_);
                        typing_dynamic::maybe_wrap_with_supportdyn(
                            should_wrap,
                            localize_reason(m.reason()),
                            ft,
                        )
                    }
                    _ => {
                        diagnostics::internal_error(
                            p.clone(),
                            "Expected function type for constructor",
                        );
                        env::fresh_type_error(env, p.clone())
                    }
                }
            };
            let (tel, typed_unpack_element, _ty, should_forget_fakes): (
                Vec<tast::Argument>,
                Option<tast::Expr>,
                Ty,
                bool,
            ) = call(
                None, // expected
                None, // nullsafe
                Some(attribute_check_policy),
                None, // in_await
                None, // dynamic_func
                p,
                cid_pos,
                cid_pos,
                env,
                m.clone(),
                el,
                unpacked_element,
            );
            (tel, typed_unpack_element, m, should_forget_fakes)
        }
    }
}

/// `inout_write_back env { fp_type; _ } arg`
pub fn inout_write_back(env: &mut Env, fp: &FunParam, arg: &nast::Argument) {
    let FunParam { type_: fp_type, .. } = fp;
    match arg {
        aast::Argument::Ainout(_, e) => {
            // Translate the write-back semantics of inout parameters.
            //
            // This matters because we want to:
            // (1) make sure we can write to the original argument
            //     (modifiable lvalue check)
            // (2) allow for growing of locals / Tunions (type side effect)
            //     but otherwise unify the argument type with the parameter hint
            let pos = aast_utils::get_expr_pos(e);
            let (_te, _ty): (tast::Expr, Ty) = assign::assign_(
                None, // expr_for_string_check
                &pos,
                Ureason::URparamInout,
                env,
                e,
                &pos,
                fp_type.clone(),
            );
        }
        aast::Argument::Anamed(..) => {}
        aast::Argument::Anormal(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value of `let <name> = "<value>"` in the module `<module>` of
    /// `naming_special_names.ml`, as it is written there.
    fn ocaml_string(module: &str, name: &str) -> &'static str {
        let ml = include_str!("../../../../naming/naming_special_names.ml");
        let module_start = ml
            .find(&format!("\nmodule {} = struct", module))
            .unwrap_or_else(|| panic!("module {}", module));
        let ml = &ml[module_start..];
        let def = format!("\n  let {} =", name);
        let start = ml
            .find(&def)
            .unwrap_or_else(|| panic!("{}.{}", module, name))
            + def.len();
        let rest = &ml[start..];
        let open = rest.find('"').unwrap();
        let rest = &rest[open + 1..];
        &rest[..rest.find('"').unwrap()]
    }

    #[test]
    fn shapes_names_are_the_ocaml_ones() {
        // The names of `Shapes` that `dispatch_call` uses and that
        // `naming_special_names_rust` has (`crate::naming_special_names` tests
        // the others).
        assert_eq!(
            sn::shapes::SHAPES.replace('\\', "\\\\"),
            ocaml_string("Shapes", "cShapes")
        );
        for (name, value) in [
            ("at", sn::shapes::AT),
            ("idx", sn::shapes::IDX),
            ("keyExists", sn::shapes::KEY_EXISTS),
            ("removeKey", sn::shapes::REMOVE_KEY),
            ("toDict", sn::shapes::TO_DICT),
            ("toArray", sn::shapes::TO_ARRAY),
        ] {
            assert_eq!(value, ocaml_string("Shapes", name), "{}", name);
        }
        assert_eq!(
            sn::fb::TYPE_STRUCTURE.replace('\\', "\\\\"),
            ocaml_string("FB", "cTypeStructure")
        );
    }

    #[test]
    fn messages_keep_order() {
        let p1 = Pos::NONE;
        let l = vec![(p1.clone(), "a".to_string()), (p1, "b".to_string())];
        let m = messages(l);
        assert_eq!(m.len(), 2);
        assert_eq!(m[0].1, "a");
        assert_eq!(m[1].1, "b");
    }
}
