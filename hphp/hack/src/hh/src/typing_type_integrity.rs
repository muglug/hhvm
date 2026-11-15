// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_type_integrity.ml`. See `hh/PORTING.md`.
//!
//! `typing_type_integrity.ml` defines `check_type_integrity` twice: the first
//! (with `~allow_missing_targs`, recursive with `check_targs_integrity` and
//! `check_targ_well_formed`) is [`check_type_integrity_rec`] here; the second,
//! which the `.mli` exports, keeps the name.
//!
//! `should_check_package_boundary` (`Typing_packages.check_reason`, a
//! polymorphic variant) is `crate::typing_packages::CheckReason`, with the
//! OCaml tags (`Yes`, `LintOnly`, `ClassPtrLinterOnly`, `No`), as
//! `typing_visibility.rs` uses it.

use oxidized::aast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;
use ty::decl::ty as d;

use crate::ast_defs;
use crate::class_refinement;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_hint;
use crate::decl_utils;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::lints_diagnostics;
use crate::pos_or_decl;
use crate::typing_defs::*;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::primary::package::TargetSymbolSpec;
use crate::typing_error_utils;
use crate::typing_packages;
use crate::typing_packages::CheckReason;
use crate::typing_reason;
use crate::typing_visibility;

/// `module Locl_Inst`
pub mod locl_inst {
    use super::*;

    pub fn instantiate(subst: &im::OrdMap<String, Ty>, ty: &Ty) -> Ty {
        fn merge_hk_type(orig_r: Reason, orig_var: &str, ty: &Ty, args: Vec<Ty>) -> Ty {
            let (r, ty_) = deref(ty);
            let res_ty_ = match ty_ {
                Ty_::Tclass(n, exact, existing_args) => {
                    // We could insist on existing_args = [] here unless we want to support partial application.
                    let mut tyl = existing_args;
                    tyl.extend(args);
                    Ty_::Tclass(n, exact, tyl)
                }
                Ty_::Tnewtype(n, existing_args, bound) => {
                    let mut tyl = existing_args;
                    tyl.extend(args);
                    Ty_::Tnewtype(n, tyl, bound)
                }
                Ty_::Tgeneric(n) => {
                    // Same here
                    Ty_::Tgeneric(n)
                }
                ty_ => {
                    // We could insist on args = [] here, everything else is a kinding error
                    ty_
                }
            };
            mk((
                typing_reason::instantiate(r, orig_var.to_string(), orig_r),
                res_ty_,
            ))
        }

        // PERF: If subst is empty then instantiation is a no-op. We can save a
        // significant amount of CPU by avoiding recursively deconstructing the ty
        // data type.
        if subst.is_empty() {
            ty.clone()
        } else {
            match deref(ty) {
                (r, Ty_::Tgeneric(x)) => {
                    let args = vec![];
                    match subst.get(&x) {
                        Some(x_ty) => merge_hk_type(r, &x, x_ty, args),
                        None => mk((r, Ty_::Tgeneric(x))),
                    }
                }
                (r, ty) => {
                    let ty = instantiate_(subst, ty);
                    mk((r, ty))
                }
            }
        }
    }

    pub(super) fn instantiate_(subst: &im::OrdMap<String, Ty>, x: Ty_) -> Ty_ {
        match x {
            Ty_::Tgeneric(_) => panic!("assert false"),
            Ty_::TvecOrDict(ty1, ty2) => {
                let ty1 = instantiate(subst, &ty1);
                let ty2 = instantiate(subst, &ty2);
                Ty_::TvecOrDict(ty1, ty2)
            }
            x @ (Ty_::Tvar(_)
            | Ty_::Tdynamic(_)
            | Ty_::Tnonnull
            | Ty_::Tany(_)
            | Ty_::Tprim(_)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_)) => x,
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            }) => {
                let t_extra = instantiate_tuple_extra(subst, t_extra);
                let t_required = t_required.iter().map(|ty| instantiate(subst, ty)).collect();
                let t_optional = t_optional.iter().map(|ty| instantiate(subst, ty)).collect();
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: t_extra,
                })
            }
            Ty_::Tunion(tyl) => {
                let tyl = tyl.iter().map(|ty| instantiate(subst, ty)).collect();
                Ty_::Tunion(tyl)
            }
            Ty_::Tintersection(tyl) => {
                let tyl = tyl.iter().map(|ty| instantiate(subst, ty)).collect();
                Ty_::Tintersection(tyl)
            }
            Ty_::Toption(ty) => {
                let ty = instantiate(subst, &ty);
                // we want to avoid double option: ??T
                match get_node(&ty) {
                    ty_node @ Ty_::Toption(_) => ty_node.clone(),
                    _ => Ty_::Toption(ty),
                }
            }
            Ty_::Tfun(ft) => {
                let tparams = &ft.tparams;
                let outer_subst = subst;
                let subst = tparams.iter().fold(subst.clone(), |subst, t| {
                    let mut subst = subst;
                    subst.remove(&t.name.1);
                    subst
                });
                let params = ft
                    .params
                    .iter()
                    .map(|param| {
                        let ty = instantiate(&subst, &param.type_);
                        FunParam {
                            type_: ty,
                            ..param.clone()
                        }
                    })
                    .collect();
                let ret = instantiate(&subst, &ft.ret);
                let tparams = tparams
                    .iter()
                    .map(|t| Tparam {
                        constraints: t
                            .constraints
                            .iter()
                            .map(|(ck, ty)| (*ck, instantiate(&subst, ty)))
                            .collect(),
                        ..t.clone()
                    })
                    .collect();
                let where_constraints = ft
                    .where_constraints
                    .iter()
                    .map(|WhereConstraint(ty1, ck, ty2)| {
                        // OCaml evaluates the components of the tuple from right
                        // to left (instantiation has no effect).
                        let ty2 = instantiate(outer_subst, ty2);
                        let ty1 = instantiate(&subst, ty1);
                        WhereConstraint(ty1, *ck, ty2)
                    })
                    .collect();
                Ty_::Tfun(std::rc::Rc::new(FunType {
                    params,
                    ret,
                    tparams,
                    where_constraints,
                    ..std::rc::Rc::unwrap_or_clone(ft)
                }))
            }
            Ty_::Tnewtype(x, tyl, bound) => {
                let tyl = tyl.iter().map(|ty| instantiate(subst, ty)).collect();
                let bound = instantiate(subst, &bound);
                Ty_::Tnewtype(x, tyl, bound)
            }
            Ty_::Tclass(x, exact, tyl) => {
                let tyl = tyl.iter().map(|ty| instantiate(subst, ty)).collect();
                Ty_::Tclass(x, exact, tyl)
            }
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: kind,
                fields: fdm,
            })) => {
                let fdm = shape_field_map::map(|ty| instantiate(subst, &ty), fdm);
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: TypeOrigin::MissingOrigin,
                    unknown_value: kind,
                    // TODO(shapes) instantiate s_unknown_value
                    fields: fdm,
                }))
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                let ss_elems = ss_elems.iter().map(|ty| instantiate(subst, ty)).collect();
                Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))
            }
            Ty_::Tdependent(dep, ty) => {
                let ty = instantiate(subst, &ty);
                Ty_::Tdependent(dep, ty)
            }
            Ty_::Taccess(TaccessType(ty, ids)) => {
                let ty = instantiate(subst, &ty);
                Ty_::Taccess(TaccessType(ty, ids))
            }
            Ty_::TclassPtr(ty) => {
                let ty = instantiate(subst, &ty);
                Ty_::TclassPtr(ty)
            }
        }
    }

    pub(super) fn instantiate_tuple_extra(
        subst: &im::OrdMap<String, Ty>,
        e: TupleExtra,
    ) -> TupleExtra {
        match e {
            TupleExtra::Tvariadic(t_variadic) => {
                let t_variadic = instantiate(subst, &t_variadic);
                TupleExtra::Tvariadic(t_variadic)
            }
            TupleExtra::Tsplat(t_splat) => {
                let t_splat = instantiate(subst, &t_splat);
                TupleExtra::Tsplat(t_splat)
            }
        }
    }
}

/// `Typing_reason.t`
type Reason = typing_reason::T;

/// `Typing_reason.to_pos` of the reason of a declared type.
fn decl_reason_to_pos(r: &R) -> PosOrDecl {
    decl_utils::reason_to_pos(r).to_oxidized()
}

/// True iff the typedef ultimately resolves to a name-enforced type — a
/// class or interface — whose name HHVM looks up at runtime. False for
/// structural types (shape, tuple, primitive, vec<...>) that unfold and
/// are enforced by shape, for traits (not legal in type positions), for
/// regular enums (HHVM enforces the underlying base type, not the enum
/// name), and for enum classes (cannot appear as typehints directly).
fn typedef_resolves_to_class_like(
    env: &Env,
    seen: Option<im::OrdSet<String>>,
    typedef: &TypedefType,
) -> bool {
    let seen = seen.unwrap_or_default();
    match &typedef.type_assignment {
        d::TypedefTypeAssignment::CaseType(..) => false,
        d::TypedefTypeAssignment::SimpleTypeDef(_, ty) => match ty.node_ref() {
            d::Ty_::Tapply(id_and_argl) => {
                let name = id_and_argl.0.id_ref().as_str();
                if seen.contains(name) {
                    false
                } else {
                    let mut seen = seen;
                    seen.insert(name.to_string());
                    match env::get_class_or_typedef(env, name) {
                        decl_entry::T::Found(ClassOrTypedefResult::ClassResult(cls)) => {
                            let kind = cls::kind(&cls);
                            ast_defs::is_c_class(kind) || ast_defs::is_c_interface(kind)
                        }
                        decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(
                            nested_typedef,
                        )) => typedef_resolves_to_class_like(env, Some(seen), &nested_typedef),
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
                    }
                }
            }
            _ => false,
        },
    }
}

/// Check for arity mismatch between type params and type arguments
/// then check that each type argument is well-formed.
fn check_targs_integrity(
    allow_missing_targs: bool,
    in_signature: bool,
    def_pos: PosOrDecl,
    use_pos: Pos,
    env: &Env,
    tyargs: &[DeclTy],
    tparams: &[DeclTparam],
) {
    let exp_len = tparams.len();
    let act_len = tyargs.len();
    let arity_mistmatch_okay = act_len == 0 && allow_missing_targs;
    if exp_len != act_len && !arity_mistmatch_okay {
        typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::TypeArityMismatch {
                pos: use_pos,
                decl_pos: def_pos,
                expected: exp_len as isize,
                actual: act_len as isize,
            }),
            env,
        );
    }
    let length = std::cmp::min(exp_len, act_len);
    let (tyargs, tparams) = (&tyargs[..length], &tparams[..length]);
    for (tyarg, tparam) in tyargs.iter().zip(tparams.iter()) {
        check_targ_well_formed(in_signature, env, tyarg, tparam)
    }
}

/// Checks that a type argument is well-kinded against its corresponding
/// type parameter. Also checks that the wildcard type argument is not used
/// if the type parameter is higher kinded (i.e. it expected type arguments itself)
fn check_targ_well_formed(in_signature: bool, env: &Env, tyarg: &DeclTy, tparam: &DeclTparam) {
    // `Aast.is_erased`
    let in_reified = !matches!(tparam.reified, aast::ReifyKind::Erased);
    let should_check_package_boundary = if in_reified {
        CheckReason::Yes(TargetSymbolSpec::ReifiedGeneric)
    } else {
        CheckReason::No
    };
    check_type_integrity_rec(false, in_signature, should_check_package_boundary, env, tyarg)
}

/// The lints of a cross-package access (`List.iter linter_errs ~f:(fun (pos,
/// w) -> Lints_diagnostics.crosspackage_linter pos ~current_package:...)`).
fn report_crosspackage_linter_errs(linter_errs: Vec<(Pos, typing_packages::PackageWarningInfo)>) {
    for (pos, w) in linter_errs {
        let typing_packages::PackageWarningInfo {
            current_package,
            current_package_before_override,
            caller_has_package_override,
            target_package,
            target_package_before_override,
            callee_has_package_override,
            classptr_reference_warning,
        } = w;
        lints_diagnostics::crosspackage_linter(
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
}

/// The first `check_type_integrity` of the OCaml (see the module
/// documentation).
fn check_type_integrity_rec(
    allow_missing_targs: bool,
    in_signature: bool,
    should_check_package_boundary: CheckReason,
    env: &Env,
    ty: &DeclTy,
) {
    let r = ty.reason();
    let use_pos = pos_or_decl::unsafe_to_raw_pos(decl_reason_to_pos(r));
    // `check ?(should_check_package_boundary = should_check_package_boundary) ty`
    let check = |should: Option<CheckReason>, ty: &DeclTy| {
        let should_check_package_boundary =
            should.unwrap_or_else(|| should_check_package_boundary.clone());
        check_type_integrity_rec(false, in_signature, should_check_package_boundary, env, ty)
    };
    let check_targs_integrity_ =
        |in_signature: bool, def_pos: PosOrDecl, tyargs: &[DeclTy], tparams: &[DeclTparam]| {
            check_targs_integrity(
                allow_missing_targs,
                in_signature,
                def_pos,
                use_pos.clone(),
                env,
                tyargs,
                tparams,
            )
        };
    match ty.node_ref() {
        // Boring recursive cases first----------------------
        d::Ty_::Tany
        | d::Ty_::Tnonnull
        | d::Ty_::Tprim(_)
        | d::Ty_::Tdynamic
        | d::Ty_::Tmixed
        | d::Ty_::Twildcard
        | d::Ty_::Tthis => {}
        d::Ty_::TvecOrDict(tk_tv) => {
            let (tk, tv) = &**tk_tv;
            check(Some(CheckReason::No), tk);
            check(Some(CheckReason::No), tv)
        }
        d::Ty_::Tlike(ty) | d::Ty_::Toption(ty) => check(None, ty),
        d::Ty_::Ttuple(t) => {
            let d::TupleType(t_required, t_optional, t_extra) = &**t;
            let t_vs = match t_extra {
                d::TupleExtra::Tvariadic(t_vs) | d::TupleExtra::Tsplat(t_vs) => t_vs,
            };
            // HHVM enforces a tuple hint structurally as a vec of the right arity, but
            // does not enforce the element types. So skip the enforceable_type_alias
            // check on tuple elements.
            let should_check_package_boundary = match &should_check_package_boundary {
                CheckReason::Yes(TargetSymbolSpec::EnforceableTypeAlias) => CheckReason::No,
                other => other.clone(),
            };
            let check = |ty: &DeclTy| check(Some(should_check_package_boundary.clone()), ty);
            for ty in t_required.iter() {
                check(ty)
            }
            for ty in t_optional.iter() {
                check(ty)
            }
            check(t_vs)
        }
        d::Ty_::Tunion(tyl) | d::Ty_::Tintersection(tyl) => {
            for ty in tyl.iter() {
                check(None, ty)
            }
        }
        d::Ty_::Taccess(ta) => {
            // Because type constants cannot depend on type parameters,
            // we allow Foo::the_type even if Foo has type parameters
            check_type_integrity_rec(
                true,
                in_signature,
                should_check_package_boundary.clone(),
                env,
                &ta.ty,
            )
        }
        d::Ty_::Trefinement(tr) => {
            check(None, &tr.ty);
            // Refinement bodies (`Foo with {type TC = X}`) are typechecker-only;
            // HHVM enforces only the base class at runtime. Skip package checks on
            // the refinement members entirely.
            class_refinement::iter_decl(|ty| check(Some(CheckReason::No), ty), &tr.refinement)
        }
        d::Ty_::Tshape(st) => match &**st {
            d::ShapeType::Simple(d::ShapeTypeSimple(_, map)) => {
                // Shape field types are runtime-enforced under `as` (modulo `enforce_deep`),
                // so propagate the boundary reason for as-expression contexts. Other
                // contexts continue to skip field-type checking to preserve prior behavior.
                let should_check_package_boundary = match &should_check_package_boundary {
                    CheckReason::Yes(TargetSymbolSpec::AsExpression) | CheckReason::LintOnly => {
                        should_check_package_boundary.clone()
                    }
                    _ => CheckReason::No,
                };
                // TShapeMap.iter: in the order of the names of the fields
                let mut fields: Vec<_> = map.iter().collect();
                fields.sort_by(|a, b| decl_tshape_field_name_compare(a.0, b.0));
                for (_, sft) in fields {
                    check(Some(should_check_package_boundary.clone()), &sft.ty)
                }
            }
            d::ShapeType::Splat(ss_elems) => {
                // Splat elements are shapes whose field types are runtime-enforced under
                // `as` just like simple shapes, so propagate the boundary reason the same
                // way (see the `Shape_simple` case above) to keep the same guarantees.
                let should_check_package_boundary = match &should_check_package_boundary {
                    CheckReason::Yes(TargetSymbolSpec::AsExpression) | CheckReason::LintOnly => {
                        should_check_package_boundary.clone()
                    }
                    _ => CheckReason::No,
                };
                for ty in ss_elems.iter() {
                    check(Some(should_check_package_boundary.clone()), ty)
                }
            }
        },
        d::Ty_::Tfun(ft) => {
            let d::FunType {
                params: ft_params,
                ret: ft_ret,
                ..
            } = &**ft;
            // FIXME shall we inspect tparams and where_constraints?
            check(Some(CheckReason::No), ft_ret);
            for p in ft_params.iter() {
                check(Some(CheckReason::No), &p.ty)
            }
        }
        // Interesting cases---------------------------------
        d::Ty_::Tgeneric(_) => {}
        d::Ty_::Tapply(id_and_argl) => {
            let (id, argl) = &**id_and_argl;
            let cid = id.id_ref().as_str();
            match env::get_class_or_typedef(env, cid) {
                decl_entry::T::Found(ClassOrTypedefResult::ClassResult(class_info)) => {
                    let should_check_package_boundary = if typing_packages::is_strict_isolation_target(
                        env,
                        cls::get_package(&class_info).as_ref(),
                    ) {
                        // A strict-isolation package is enforced at every type position,
                        // including ones the rollout carve-outs normally skip (bare
                        // class/interface hints, nested type arguments, function-type
                        // parameters, refinement members).
                        CheckReason::Yes(TargetSymbolSpec::TypeHint)
                    } else {
                        match &should_check_package_boundary {
                            // Class/interface are covered by the class-name access check, so carve
                            // them out (and enums too when enum violations are allowed).
                            CheckReason::Yes(TargetSymbolSpec::EnforceableTypeAlias)
                                if env::package_allow_enforceable_enum_violations(env)
                                    || ast_defs::is_c_class(cls::kind(&class_info))
                                    || ast_defs::is_c_interface(cls::kind(&class_info)) =>
                            {
                                CheckReason::No
                            }
                            // An enum is enforced by its base type, not its name, so the
                            // class-name check does not cover it; report it specifically. Any
                            // other kind (e.g. a trait or enum class reaching here) keeps the
                            // generic diagnostic.
                            CheckReason::Yes(TargetSymbolSpec::EnforceableTypeAlias)
                                if ast_defs::is_c_enum(cls::kind(&class_info)) =>
                            {
                                CheckReason::Yes(TargetSymbolSpec::EnforceableEnum)
                            }
                            other => other.clone(),
                        }
                    };
                    {
                        let target_package = cls::get_package(&class_info);
                        let (errs, linter_errs) = typing_visibility::check_top_level_access(
                            should_check_package_boundary,
                            in_signature,
                            use_pos.clone(),
                            cls::pos(&class_info),
                            cls::tests_bypass_visibility(&class_info),
                            true,
                            env,
                            cls::internal(&class_info),
                            cls::get_module(&class_info),
                            target_package.as_ref(),
                            cid.to_string(),
                        );
                        report_crosspackage_linter_errs(linter_errs);
                        for err in &errs {
                            typing_error_utils::add_typing_error(err, env)
                        }
                    }
                    // Note: class gating via __GatedByFeatureFlag is not yet supported
                    // because folded classes don't carry user attributes. If needed,
                    // add a gc_gated_by_feature_flag field to folded class decls.
                    let tparams = cls::tparams(&class_info);
                    check_targs_integrity_(in_signature, cls::pos(&class_info), argl, &tparams)
                }
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(typedef)) => {
                    let should_check_package_boundary =
                        if typing_packages::is_strict_isolation_target(env, typedef.package.as_ref())
                        {
                            CheckReason::Yes(TargetSymbolSpec::TypeHint)
                        } else {
                            match &should_check_package_boundary {
                                CheckReason::Yes(TargetSymbolSpec::EnforceableTypeAlias)
                                    if typedef_resolves_to_class_like(env, None, &typedef) =>
                                {
                                    CheckReason::No
                                }
                                other => other.clone(),
                            }
                        };
                    let td_pos: PosOrDecl = typedef.pos.clone().to_oxidized();
                    {
                        let (errs, linter_errs) = typing_visibility::check_top_level_access(
                            should_check_package_boundary,
                            in_signature,
                            use_pos.clone(),
                            td_pos.clone(),
                            false,
                            false,
                            env,
                            typedef.internal,
                            typedef
                                .module
                                .as_ref()
                                .map(|m| m.id_ref().as_str().to_string()),
                            typedef.package.as_ref(),
                            cid.to_string(),
                        );
                        report_crosspackage_linter_errs(linter_errs);
                        for err in &errs {
                            typing_error_utils::add_typing_error(err, env)
                        }
                    }
                    typing_visibility::check_gated_by_feature_flag(
                        env,
                        pos_or_decl::of_raw_pos(use_pos.clone()),
                        cid.to_string(),
                        &typedef.attributes,
                    );
                    check_targs_integrity_(in_signature, td_pos, argl, &typedef.tparams)
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            }
        }
        d::Ty_::TclassPtr(ty) => check(None, ty),
    }
}

/// Check that the given type is a well-formed. This includes recursively checking that whenever
/// a paramterized type is used, we provide the right number of arguments.
/// Otherwise, reports errors.
///
/// Also check that classes mentioned in types are accessible from the current
/// module, and accessible also from outside if in_signature=true.
///
/// Finally, check that classes and type aliases mentioned in types are accessible
/// from the current package. We however ignore package errors when
/// `should_check_package_boundary` is `No. This is usually the case when
/// we are inside the following (to model the behavior of SymbolRefs)
///   - type consts
///   - type hints
///   - type params
///   - type param constraints
pub fn check_type_integrity(
    in_signature: bool,
    should_check_package_boundary: CheckReason,
    env: &Env,
    ty: &DeclTy,
) {
    check_type_integrity_rec(false, in_signature, should_check_package_boundary, env, ty)
}

/// Check that the given type hint is a well-formed. This includes recursively checking that
/// whenever a paramterized type is used, we provide the right number of arguments.
/// Otherwise, reports errors.
///
/// Also check that classes mentioned in hints are accessible from the current
/// module, and accessible also from outside if `in_signature` is true.
///
/// Finally, check that classes and type aliases mentioned in types are accessible
/// from the current package (see [`check_type_integrity`]).
pub fn check_hint_integrity(
    in_signature: bool,
    should_check_package_boundary: CheckReason,
    env: &Env,
    hint: &aast::Hint,
) {
    let decl_ty = decl_hint::hint(&env.decl_env, hint);
    check_type_integrity(in_signature, should_check_package_boundary, env, &decl_ty)
}

/// Shortcut for check_well_formed_hint with
/// ~should_check_package_boundary:`No
pub fn check_context_hint_integrity(in_signature: bool, env: &Env, hint: &aast::Hint) {
    let decl_ty = decl_hint::context_hint(&env.decl_env, hint);
    check_type_integrity(in_signature, CheckReason::No, env, &decl_ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r() -> Reason {
        typing_reason::none()
    }

    fn generic(n: &str) -> Ty {
        mk((r(), Ty_::Tgeneric(n.to_string())))
    }

    fn class(n: &str, tyl: Vec<Ty>) -> Ty {
        mk((r(), Ty_::Tclass((Pos::NONE, n.to_string()), nonexact(), tyl)))
    }

    #[test]
    fn locl_inst_instantiate() {
        let ty = mk((r(), Ty_::Toption(generic("T"))));

        // T := C
        let subst = im::OrdMap::unit("T".to_string(), class("\\C", vec![]));
        let res = locl_inst::instantiate(&subst, &ty);
        match get_node(&res) {
            Ty_::Toption(t) => match get_node(t) {
                Ty_::Tclass((_, n), _, tyl) => {
                    assert_eq!(n, "\\C");
                    assert!(tyl.is_empty())
                }
                _ => panic!("expected a class"),
            },
            _ => panic!("expected an option"),
        }

        // T := ?C gives ?C, not ??C
        let subst = im::OrdMap::unit(
            "T".to_string(),
            mk((r(), Ty_::Toption(class("\\C", vec![])))),
        );
        let res = locl_inst::instantiate(&subst, &ty);
        match get_node(&res) {
            Ty_::Toption(t) => assert!(matches!(get_node(t), Ty_::Tclass(..))),
            _ => panic!("expected an option"),
        }

        // An unbound generic stays; an empty substitution returns the same type.
        let subst = im::OrdMap::unit("U".to_string(), class("\\C", vec![]));
        let res = locl_inst::instantiate(&subst, &ty);
        match get_node(&res) {
            Ty_::Toption(t) => assert!(matches!(get_node(t), Ty_::Tgeneric(n) if n == "T")),
            _ => panic!("expected an option"),
        }
        let res = locl_inst::instantiate(&im::OrdMap::new(), &ty);
        assert!(phys_equal(&res, &ty));
    }
}
