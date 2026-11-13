// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/attribute_nast_checks.ml`.

use oxidized::ast_defs::Bop;
use oxidized::ast_defs::ClassishKind;
use oxidized::ast_defs::Visibility;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;
use pos::TypeName;

use super::Errors;
use super::attrs;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;
use super::sn::user_attributes as ua;

fn check_soft_internal_without_internal(
    internal: bool,
    attrs: &nast::UserAttributes,
    errors: &mut Errors,
) {
    if let Some(attr) = attrs::find(ua::SOFT_INTERNAL, attrs) {
        if !internal {
            errors.add(NastCheckError::SoftInternalWithoutInternal(
                attr.name.0.clone(),
            ));
        }
    }
}

fn check_soft_internal_on_param(fp: &nast::FunParam, errors: &mut Errors) {
    if let Some(attr) = attrs::find(ua::SOFT_INTERNAL, &fp.user_attributes) {
        let nast::Id(pos, attr_name) = &attr.name;
        match fp.visibility {
            Some(Visibility::Internal) => {}
            Some(_) => errors.add(NastCheckError::SoftInternalWithoutInternal(pos.clone())),
            None => errors.add(NastCheckError::WrongExpressionKindBuiltinAttribute {
                expr_kind: "a parameter".to_string(),
                pos: pos.clone(),
                attr_name: attr_name.clone(),
            }),
        }
    }
}

enum ArgSpec {
    Range(usize, usize),
    Exact(usize),
}

fn check_attribute_arity(
    attrs: &nast::UserAttributes,
    attr_name: &str,
    arg_spec: ArgSpec,
    errors: &mut Errors,
) {
    let Some(attr) = attrs::find(attr_name, attrs) else {
        return;
    };
    let pos = attr.name.0.clone();
    let name = attr_name.to_string();
    let actual = attr.params.len();
    match arg_spec {
        ArgSpec::Range(min_args, _) if actual < min_args => {
            errors.add(NastCheckError::AttributeTooFewArguments {
                pos,
                name,
                expected: min_args as isize,
            })
        }
        ArgSpec::Range(_, max_args) if actual > max_args => {
            errors.add(NastCheckError::AttributeTooManyArguments {
                pos,
                name,
                expected: max_args as isize,
            })
        }
        ArgSpec::Exact(expected_args) if actual != expected_args => {
            errors.add(NastCheckError::AttributeNotExactNumberOfArgs {
                pos,
                name,
                expected: expected_args as isize,
                actual: actual as isize,
            })
        }
        _ => {}
    }
}

/// Ban methods having both `__Memoize` and `__MemoizeLSB`.
fn check_duplicate_memoize(attrs: &nast::UserAttributes, errors: &mut Errors) {
    let memoize = attrs::find(ua::MEMOIZE, attrs);
    let memoize_lsb = attrs::find(ua::MEMOIZE_LSB, attrs);
    if let (Some(memoize), Some(memoize_lsb)) = (memoize, memoize_lsb) {
        errors.add(NastCheckError::AttributeConflictingMemoize {
            pos: memoize.name.0.clone(),
            second_pos: memoize_lsb.name.0.clone(),
        });
    }
}

/// `Nast_eval.static_string`: the position of what is not a static string.
fn static_string(expr: &nast::Expr) -> Result<(), &Pos> {
    match &expr.2 {
        nast::Expr_::Binop(binop) if matches!(binop.bop, Bop::Dot) => {
            static_string(&binop.lhs)?;
            static_string(&binop.rhs)
        }
        nast::Expr_::String(_) => Ok(()),
        _ => Err(&expr.1),
    }
}

fn check_deprecated_static(attrs: &nast::UserAttributes, errors: &mut Errors) {
    if let Some(attr) = attrs::find(ua::DEPRECATED, attrs) {
        if let [msg] | [msg, _] = attr.params.as_slice() {
            if let Err(p) = static_string(msg) {
                errors.add(NastCheckError::AttributeParamType {
                    pos: p.clone(),
                    x: "static string literal".to_string(),
                });
            }
        }
    }
}

fn check_no_auto_dynamic(env: &Env<'_>, attrs: &nast::UserAttributes, errors: &mut Errors) {
    if env.ctx.tco.tco_enable_no_auto_dynamic {
        return;
    }
    if let Some(attr) = attrs::find(ua::NO_AUTO_DYNAMIC, attrs) {
        let pos = &attr.name.0;
        if !pos.filename().is_hhi() {
            errors.add(NastCheckError::AttributeNoAutoDynamic(pos.clone()));
        }
    }
}

fn check_implemented_by(env: &Env<'_>, attrs: &nast::UserAttributes, errors: &mut Errors) {
    let Some(attr) = attrs::find(IMPLEMENTED_BY, attrs) else {
        return;
    };
    let nast::Id(pos, name) = &attr.name;
    // Check file extension
    let is_hhi = pos.filename().path_str().ends_with(".hhi");
    if !is_hhi {
        errors.add(NastCheckError::AttributeImplementedByRestriction {
            restriction: ".hhi files".to_string(),
            pos: pos.clone(),
        });
    }
    // Check it is in a final class
    match (env.classish_kind, env.is_final) {
        (Some(ClassishKind::Cclass(_)), true) => {}
        _ => errors.add(NastCheckError::AttributeImplementedByRestriction {
            restriction: "final classes".to_string(),
            pos: pos.clone(),
        }),
    }
    // Check parameter count and type
    match attr.params.as_slice() {
        [] => errors.add(NastCheckError::AttributeTooFewArguments {
            pos: pos.clone(),
            name: name.clone(),
            expected: 1,
        }),
        // Valid: one string parameter
        [nast::Expr(_, _, nast::Expr_::String(_))] => {}
        [nast::Expr(_, p, _)] => errors.add(NastCheckError::AttributeParamType {
            pos: p.clone(),
            x: "a string literal".to_string(),
        }),
        _ => errors.add(NastCheckError::AttributeTooManyArguments {
            pos: pos.clone(),
            name: name.clone(),
            expected: 1,
        }),
    }
}

fn check_dynamically_referenced(attrs: &nast::UserAttributes, errors: &mut Errors) {
    let Some(attr) = attrs::find(ua::DYNAMICALLY_REFERENCED, attrs) else {
        return;
    };
    let nast::Id(pos, name) = &attr.name;
    match attr.params.as_slice() {
        [] => {}
        [nast::Expr(_, _, nast::Expr_::Int(_))] => {}
        [nast::Expr(_, p, _)] => errors.add(NastCheckError::AttributeParamType {
            pos: p.clone(),
            x: "an integer literal".to_string(),
        }),
        _ => errors.add(NastCheckError::AttributeTooManyArguments {
            pos: pos.clone(),
            name: name.clone(),
            expected: 1,
        }),
    }
}

/// Check that a sealed attribute on a class does not refer to a trait.
fn check_no_class_sealed_with_trait(env: &Env<'_>, c: &nast::Class_, errors: &mut Errors) {
    // Only check classes, not interfaces or traits
    if !matches!(c.kind, ClassishKind::Cclass(_)) {
        return;
    }
    let Some(sealed_attr) = attrs::find(ua::SEALED, &c.user_attributes) else {
        return;
    };
    let class_name = &c.name.1;
    for nast::Expr(_, pos, expr_) in &sealed_attr.params {
        let nast::Expr_::ClassConst(cc) = expr_ else {
            continue;
        };
        let nast::ClassId_::CI(nast::Id(_, name)) = &cc.0.2 else {
            continue;
        };
        // Look up the referenced class to check if it's a trait.
        // (`Naming_provider.get_type_path`, then
        // `Ast_provider.find_class_in_file`: the kind of the class of that
        // name, if the name is that of a class.)
        if let Ok(Some(cls)) = env.ctx.shallow_decls.get_class(TypeName::new(name)) {
            if matches!(cls.kind, ClassishKind::Ctrait) {
                errors.add(NastCheckError::ClassSealedWithTrait {
                    pos: pos.clone(),
                    class_name: class_name.clone(),
                    trait_name: name.to_string(),
                });
            }
        }
    }
}

fn wrong_expression_kind(attr: &nast::UserAttribute, expr_kind: &str, errors: &mut Errors) {
    let nast::Id(pos, attr_name) = &attr.name;
    errors.add(NastCheckError::WrongExpressionKindBuiltinAttribute {
        expr_kind: expr_kind.to_string(),
        pos: pos.clone(),
        attr_name: attr_name.clone(),
    });
}

fn check_no_sealed_on_constructors(m: &nast::Method_, errors: &mut Errors) {
    if m.name.1 == sn::members::__CONSTRUCT {
        if let Some(attr) = attrs::find(ua::SEALED, &m.user_attributes) {
            wrong_expression_kind(attr, "a constructor", errors);
        }
    }
}

fn check_no_sealed_on_private_methods(m: &nast::Method_, errors: &mut Errors) {
    if m.visibility == Visibility::Private {
        if let Some(attr) = attrs::find(ua::SEALED, &m.user_attributes) {
            wrong_expression_kind(attr, "a private method", errors);
        }
    }
}

fn check_no_sealed_on_interface_methods(env: &Env<'_>, m: &nast::Method_, errors: &mut Errors) {
    let inside_interface = matches!(env.classish_kind, Some(ClassishKind::Cinterface));
    if inside_interface {
        if let Some(attr) = attrs::find(ua::SEALED, &m.user_attributes) {
            wrong_expression_kind(attr, "a method declaration in an interface", errors);
        }
    }
}

fn report_variadic_memoize(variadic_param: Option<&nast::FunParam>, errors: &mut Errors) {
    if let Some(p) = variadic_param {
        errors.add(NastCheckError::VariadicMemoize(p.pos.clone()));
    }
}

fn report_named_memoize(params: &[nast::FunParam], errors: &mut Errors) {
    if let Some(p) = params.iter().find(|fp| fp.named.is_some()) {
        errors.add(NastCheckError::NamedParamsMemoize(p.pos.clone()));
    }
}

/// The first parameter that is variadic (`Aast_utils.is_param_variadic`) or a
/// splat (`Aast_utils.is_param_splat`).
fn variadic_param(params: &[nast::FunParam]) -> Option<&nast::FunParam> {
    params
        .iter()
        .find(|fp| matches!(fp.info, nast::FunParamInfo::ParamVariadic) || fp.splat.is_some())
}

/// `Naming_special_names.UserAttributes.uaImplementedBy`
const IMPLEMENTED_BY: &str = "__ImplementedBy";

pub struct AttributeNastChecks;

impl<'a> Handler<'a> for AttributeNastChecks {
    fn at_fun_(&mut self, env: &Env<'a>, f: &'a nast::Fun_, errors: &mut Errors) {
        let variadic_param = variadic_param(&f.params);
        // Ban arguments on functions with the __EntryPoint attribute.
        if attrs::mem(ua::ENTRY_POINT, &f.user_attributes) {
            if let Some(param) = f.params.first() {
                errors.add(NastCheckError::EntrypointArguments(param.pos.clone()));
            }
            if let Some(p) = variadic_param {
                errors.add(NastCheckError::EntrypointArguments(p.pos.clone()));
            }
        }

        // Ban variadic and named arguments on memoized functions.
        if attrs::mem(ua::MEMOIZE, &f.user_attributes) {
            report_variadic_memoize(variadic_param, errors);
            report_named_memoize(&f.params, errors);
        }
        check_attribute_arity(
            &f.user_attributes,
            ua::POLICIED,
            ArgSpec::Range(0, 1),
            errors,
        );
        check_attribute_arity(
            &f.user_attributes,
            ua::INFERFLOWS,
            ArgSpec::Exact(0),
            errors,
        );
        check_attribute_arity(
            &f.user_attributes,
            ua::DEPRECATED,
            ArgSpec::Range(1, 2),
            errors,
        );
        check_deprecated_static(&f.user_attributes, errors);
        check_no_auto_dynamic(env, &f.user_attributes, errors);
        for fp in &f.params {
            check_attribute_arity(&fp.user_attributes, ua::EXTERNAL, ArgSpec::Exact(0), errors);
            check_attribute_arity(&fp.user_attributes, ua::CAN_CALL, ArgSpec::Exact(0), errors);
            check_soft_internal_on_param(fp, errors);
        }
    }

    fn at_fun_def(&mut self, _env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        // Ban generics on functions with the __EntryPoint attribute.
        if attrs::mem(ua::ENTRY_POINT, &fd.fun.user_attributes) {
            if let Some(tparam) = fd.tparams.first() {
                errors.add(NastCheckError::EntrypointGenerics(tparam.name.0.clone()));
            }
        }

        check_soft_internal_without_internal(fd.internal, &fd.fun.user_attributes, errors);
    }

    fn at_method_(&mut self, env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        let variadic_param = variadic_param(&m.params);
        check_attribute_arity(
            &m.user_attributes,
            ua::POLICIED,
            ArgSpec::Range(0, 1),
            errors,
        );
        check_attribute_arity(
            &m.user_attributes,
            ua::INFERFLOWS,
            ArgSpec::Exact(0),
            errors,
        );
        check_attribute_arity(
            &m.user_attributes,
            ua::DEPRECATED,
            ArgSpec::Range(1, 2),
            errors,
        );
        check_soft_internal_without_internal(
            m.visibility == Visibility::Internal,
            &m.user_attributes,
            errors,
        );
        check_deprecated_static(&m.user_attributes, errors);
        check_duplicate_memoize(&m.user_attributes, errors);
        check_no_auto_dynamic(env, &m.user_attributes, errors);
        check_implemented_by(env, &m.user_attributes, errors);
        check_no_sealed_on_constructors(m, errors);
        check_no_sealed_on_private_methods(m, errors);
        check_no_sealed_on_interface_methods(env, m, errors);
        for fp in &m.params {
            check_soft_internal_on_param(fp, errors);
        }
        // Ban variadic and named arguments on memoized methods.
        if attrs::mem(ua::MEMOIZE, &m.user_attributes)
            || attrs::mem(ua::MEMOIZE_LSB, &m.user_attributes)
        {
            report_variadic_memoize(variadic_param, errors);
            report_named_memoize(&m.params, errors);
        }
    }

    fn at_class_(&mut self, env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        check_no_auto_dynamic(env, &c.user_attributes, errors);
        check_soft_internal_without_internal(c.internal, &c.user_attributes, errors);
        check_dynamically_referenced(&c.user_attributes, errors);
        check_no_class_sealed_with_trait(env, c, errors);
        check_attribute_arity(&c.user_attributes, ua::DOCS, ArgSpec::Exact(1), errors);
        for cv in &c.vars {
            check_soft_internal_without_internal(
                cv.visibility == Visibility::Internal,
                &cv.user_attributes,
                errors,
            );
        }
    }
}
