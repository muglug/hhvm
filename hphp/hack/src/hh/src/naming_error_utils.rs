// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `naming/naming_error_utils.ml` (`to_user_diagnostic`,
//! `render_custom_error`).
//!
//! The custom error messages of `to_user_diagnostic` (`Custom_error_eval`) are
//! not ported.

use oxidized::ast_defs::ClassishKind;
use oxidized::diagnostics::Diagnostic;
use oxidized::error_codes::Naming as Code;
use oxidized::error_codes::Typing;
use oxidized::name_context::NameContext;
use oxidized::naming_error::NamingError;
use oxidized::naming_error::ReturnOnlyHint;
use oxidized::naming_error::Visibility;
use oxidized::pos::Pos;

use crate::naming_phase_error::render::md_codify;
use crate::naming_phase_error::render::name_context_to_string;
use crate::naming_phase_error::render::strip_all_ns;
use crate::naming_phase_error::render::strip_ns;
use crate::naming_phase_error::render::suggestion_message;
use crate::naming_phase_error::render::utils_strip_ns;
use crate::diagnostics_helpers::error_with_reasons;

/// `Quickfix` (`crate::quickfix` is `port`-only: its constructor here).
mod quickfix {
    use oxidized::pos::Pos;
    pub use oxidized::quickfix::Quickfix;

    /// `Quickfix.make_eager_default_hint_style ~title ~new_text pos`
    pub fn make_eager_default_hint_style(title: String, new_text: String, pos: Pos) -> Quickfix<Pos> {
        Quickfix {
            title,
            edits: oxidized::quickfix::Edits::Eager(vec![(new_text, pos)]),
            hint_styles: vec![],
        }
    }
}

/// `User_diagnostic.make_err ~quickfixes`
fn with_quickfixes(mut d: Diagnostic, quickfixes: Vec<quickfix::Quickfix<Pos>>) -> Diagnostic {
    d.quickfixes = quickfixes;
    d
}

fn err(code: Code, pos: Pos, msg: impl Into<String>) -> Diagnostic {
    error_with_reasons(code as isize, pos, msg, vec![])
}

fn err_with_reasons(
    code: Code,
    pos: Pos,
    msg: impl Into<String>,
    reasons: Vec<(Pos, String)>,
) -> Diagnostic {
    error_with_reasons(code as isize, pos, msg, reasons)
}

fn typing_err(code: Typing, pos: Pos, msg: impl Into<String>) -> Diagnostic {
    error_with_reasons(code as isize, pos, msg, vec![])
}

fn visibility_to_string(vis: Visibility) -> &'static str {
    match vis {
        Visibility::Vpublic => "public",
        Visibility::Vprivate => "private",
        Visibility::Vinternal => "internal",
        Visibility::Vprotected => "protected",
        Visibility::VprotectedInternal => "protected internal",
    }
}

fn unbound_name_kind(kind: NameContext) -> &'static str {
    match kind {
        NameContext::ConstantNamespace => " (a global constant)",
        NameContext::FunctionNamespace => " (a global function)",
        NameContext::TypeNamespace => "",
        NameContext::ClassContext => " (an object type)",
        NameContext::TraitContext => " (a trait)",
        NameContext::ModuleNamespace => " (a module)",
        NameContext::PackageNamespace => " (a package)",
    }
}

fn error_name_already_bound(pos: Pos, name: &str, prev_pos: Pos) -> Diagnostic {
    let name = strip_ns(name);
    let hhi_msg = "This appears to be defined in an hhi file included in your project \
                   root. The hhi files for the standard library are now a part of the \
                   typechecker and must be removed from your project. Typically, you can \
                   do this by deleting the \"hhi\" directory you copied into your \
                   project when first starting with Hack.";
    let mut reasons = vec![(prev_pos.clone(), "Previous definition is here".to_string())];
    if pos.filename().is_hhi() {
        reasons.push((prev_pos, hhi_msg.to_string()));
    } else if prev_pos.filename().is_hhi() {
        reasons.push((pos.clone(), hhi_msg.to_string()));
    }
    err_with_reasons(
        Code::ErrorNameAlreadyBound,
        pos,
        format!("Name already bound: {}", md_codify(strip_ns(name))),
        reasons,
    )
}

pub fn to_user_diagnostic(error: NamingError) -> Diagnostic {
    use NamingError::*;
    match error {
        UnexpectedArrow { pos, cname } => err(
            Code::UnexpectedArrow,
            pos,
            format!("Keys may not be specified for {} initialization", cname),
        ),
        MissingArrow { pos, cname } => err(
            Code::MissingArrow,
            pos,
            format!(
                "Keys must be specified for {} initialization",
                md_codify(&cname)
            ),
        ),
        DisallowedXhpType { pos, ty_name } => err(
            Code::DisallowedXhpType,
            pos,
            format!(
                "{} is not a valid type. Use `:xhp` or `XHPChild`.",
                md_codify(&ty_name)
            ),
        ),
        NameIsReserved { pos, name } => err(
            Code::NameIsReserved,
            pos,
            format!(
                "{} cannot be used as it is reserved.",
                md_codify(strip_all_ns(&name))
            ),
        ),
        DollardollarUnused(pos) => err(
            Code::DollardollarUnused,
            pos,
            "This expression does not contain a \
             usage of the special pipe variable. Did you forget to use the `$$` \
             variable?",
        ),
        AlreadyBound { pos, name } => err(
            Code::NameAlreadyBound,
            pos,
            format!("Argument already bound: {}", md_codify(&name)),
        ),
        MethodNameAlreadyBound { pos, meth_name } => err(
            Code::MethodNameAlreadyBound,
            pos,
            format!("Method name already bound: {}", md_codify(&meth_name)),
        ),
        ErrorNameAlreadyBound {
            pos,
            name,
            prev_pos,
        } => error_name_already_bound(pos, &name, prev_pos),
        InvalidFunPointer { pos, name } => err(
            Code::InvalidFunPointer,
            pos,
            format!(
                "{} cannot be used as a function pointer",
                md_codify(strip_ns(&name))
            ),
        ),
        Undefined {
            pos,
            var_name,
            did_you_mean,
        } => {
            let (reasons, quickfixes) = match did_you_mean {
                Some((did_you_mean, did_you_mean_pos)) => (
                    vec![suggestion_message(
                        &var_name,
                        &did_you_mean,
                        did_you_mean_pos,
                    )],
                    vec![quickfix::make_eager_default_hint_style(
                        format!("Change to {}", did_you_mean),
                        did_you_mean.clone(),
                        pos.clone(),
                    )],
                ),
                None => (vec![], vec![]),
            };
            with_quickfixes(
                err_with_reasons(
                    Code::Undefined,
                    pos,
                    format!(
                        "Variable {} is undefined, or not always defined.",
                        md_codify(&var_name)
                    ),
                    reasons,
                ),
                quickfixes,
            )
        }
        UndefinedInExprTree {
            pos,
            var_name,
            dsl,
            did_you_mean,
        } => {
            let (reasons, quickfixes) = match did_you_mean {
                Some((did_you_mean, did_you_mean_pos)) => (
                    vec![(
                        did_you_mean_pos,
                        format!("Did you forget to splice in `{}`?", did_you_mean),
                    )],
                    vec![quickfix::make_eager_default_hint_style(
                        format!("Splice in {}", did_you_mean),
                        format!("${{{}}}", did_you_mean),
                        pos.clone(),
                    )],
                ),
                None => (vec![], vec![]),
            };
            let dsl = match dsl {
                Some(dsl) => format!("`{}` expression tree", utils_strip_ns(&dsl)),
                None => "expression tree".to_string(),
            };
            with_quickfixes(
                err_with_reasons(
                    Code::Undefined,
                    pos,
                    format!(
                        "Variable {} is undefined in this {}.",
                        md_codify(&var_name),
                        dsl
                    ),
                    reasons,
                ),
                quickfixes,
            )
        }
        ThisReserved(pos) => err(
            Code::ThisReserved,
            pos,
            "The type parameter `this` is reserved",
        ),
        StartWithT(pos) => err(
            Code::StartWithT,
            pos,
            "Please make your type parameter start with the letter `T` (capital)",
        ),
        UnexpectedTypedef {
            pos,
            decl_pos,
            expected_kind,
        } => err_with_reasons(
            Code::UnexpectedTypedef,
            pos,
            format!(
                "Expected a {} but got a type alias.",
                md_codify(name_context_to_string(expected_kind))
            ),
            vec![(decl_pos, "Alias definition is here.".to_string())],
        ),
        FieldNameAlreadyBound(pos) => {
            err(Code::FdNameAlreadyBound, pos, "Field name already bound")
        }
        TypedOpenShapeDisallowed(pos) => err(
            Code::TypedOpenShapeDisallowed,
            pos,
            "Typed open shapes (e.g. `shape('x' => int, string...)`) are not enabled. Use plain `...` for unknown fields.",
        ),
        NamedVariadicTypeDisallowed(pos) => err(
            Code::NamedVariadicTypeDisallowed,
            pos,
            "Named variadic parameters in function types (e.g. `(function(named int...): void)`) are not enabled.",
        ),
        VariadicNamedParameterDisallowed(pos) => err(
            Code::VariadicNamedParameterDisallowed,
            pos,
            "Variadic named parameters (e.g. `named int...`) are not enabled.",
        ),
        TraitSelfShapeKey { pos, key_name } => err(
            Code::TraitSelfShapeKey,
            pos,
            format!(
                "`{}` cannot be used as a shape key inside a trait; qualify the declaring class, trait, or interface explicitly",
                key_name
            ),
        ),
        PrimitiveTopLevel(pos) => err(
            Code::PrimitiveToplevel,
            pos,
            "Primitive type annotations are always available and may no longer be referred to in the toplevel namespace.",
        ),
        PrimitiveInvalidAlias {
            pos,
            ty_name_used,
            ty_name_canon,
        } => err(
            Code::PrimitiveInvalidAlias,
            pos,
            format!(
                "Invalid Hack type. Using {} in Hack is considered an error. Use {} instead, to keep the codebase consistent.",
                md_codify(&ty_name_used),
                md_codify(&ty_name_canon)
            ),
        ),
        DynamicNewInStrictMode(pos) => err(
            Code::DynamicNewInStrictMode,
            pos,
            "Cannot use dynamic `new`.",
        ),
        InvalidTypeAccessRoot { pos, id } => {
            let msg = match id {
                Some(id) => format!(
                    "{} must be an identifier for a class, `self`, or `this`",
                    md_codify(&id)
                ),
                None => "Type access is only valid for a class, `self`, or `this`".to_string(),
            };
            err(Code::InvalidTypeAccessRoot, pos, msg)
        }
        InvalidTypeAccessInWhere(pos) => err(
            Code::InvalidTypeAccessInWhere,
            pos,
            "Type access is only valid for a class, `self`, or `this`. \
             To relate type parameters and type constants, \
             you likely want to use the 'with refinement' feature instead.",
        ),
        DuplicateUserAttribute {
            pos,
            attr_name,
            prev_pos,
        } => err_with_reasons(
            Code::DuplicateUserAttribute,
            pos,
            format!("You cannot reuse the attribute {}", md_codify(&attr_name)),
            vec![(
                prev_pos,
                format!("{} was already used here", md_codify(&attr_name)),
            )],
        ),
        InvalidMemoizeLabel { pos, attr_name } => err(
            Code::InvalidMemoizeLabel,
            pos,
            format!(
                "{} can only be used with items from MemoizeOption.",
                md_codify(&attr_name)
            ),
        ),
        UnboundName { pos, name, kind } => err(
            Code::UnboundName,
            pos,
            format!(
                "Unbound name: {}{}",
                md_codify(strip_ns(&name)),
                unbound_name_kind(kind)
            ),
        ),
        UnboundAttributeName {
            pos,
            attr_name,
            closest_attr_name,
        } => {
            let reason = if attr_name.starts_with("__") {
                "starts with __ but is not a standard attribute"
            } else {
                "does not have a class. Please declare a class for the attribute."
            };
            let quickfixes = if attr_name.starts_with("__") {
                match closest_attr_name {
                    None => vec![],
                    Some(close_name) => vec![quickfix::make_eager_default_hint_style(
                        format!("Change to {}", md_codify(&close_name)),
                        close_name,
                        pos.clone(),
                    )],
                }
            } else {
                vec![]
            };
            with_quickfixes(
                err(
                    Code::UnboundName,
                    pos,
                    format!(
                        "Unrecognized user attribute: {} {}",
                        md_codify(strip_ns(&attr_name)),
                        reason
                    ),
                ),
                quickfixes,
            )
        }
        ThisNoArgument(pos) => err(Code::ThisNoArgument, pos, "`this` type takes no arguments"),
        ObjectCast(pos) => err(
            Code::ObjectCast,
            pos,
            "Casts are only supported for `bool`, `int`, `float` and `string`.",
        ),
        ThisHintOutsideClass(pos) => err(
            Code::ThisHintOutsideClass,
            pos,
            "Cannot use `this` outside of a class",
        ),
        ParentOutsideClass(pos) => typing_err(
            Typing::ParentOutsideClass,
            pos,
            "`parent` is undefined outside of a class",
        ),
        SelfOutsideClass(pos) => typing_err(
            Typing::SelfOutsideClass,
            pos,
            "`self` is undefined outside of a class",
        ),
        StaticOutsideClass(pos) => typing_err(
            Typing::StaticOutsideClass,
            pos,
            "`static` is undefined outside of a class",
        ),
        ThisTypeForbidden {
            pos,
            in_extends,
            in_req_extends,
        } => {
            let msg = if in_extends {
                "This type `this` cannot be used in an `extends` clause"
            } else if in_req_extends {
                "This type `this` cannot be used in a `require extends` clause"
            } else {
                "The type `this` cannot be used as a constraint on a class generic, or as the type of a static member variable"
            };
            err(Code::ThisMustBeReturn, pos, msg)
        }
        NonstaticPropertyWithLsb(pos) => err(
            Code::NonstaticPropertyWithLSB,
            pos,
            "`__LSB` attribute may only be used on static properties",
        ),
        ClassnameParam(pos) => err(
            Code::ClassnameParam,
            pos,
            "Missing type parameter to `classname`; `classname` is entirely \
             meaningless without one",
        ),
        TparamAppliedToType { pos, tparam_name } => err(
            Code::HigherKindedTypesUnsupportedFeature,
            pos,
            format!(
                "`{}` is a type parameter. Type parameters cannot take type arguments (e.g. `{}<int>` isn't allowed)",
                tparam_name, tparam_name
            ),
        ),
        ShadowedTparam {
            pos,
            tparam_name,
            prev_pos,
        } => err_with_reasons(
            Code::ShadowedTypeParam,
            pos,
            format!(
                "You cannot re-bind the type parameter {}",
                md_codify(&tparam_name)
            ),
            vec![(
                prev_pos,
                format!("{} is already bound here", md_codify(&tparam_name)),
            )],
        ),
        MissingTypehint(pos) => err(Code::MissingTypehint, pos, "Please add a type hint"),
        ExpectedVariable(pos) => err(Code::ExpectedVariable, pos, "Was expecting a variable name"),
        TooManyArguments(pos) => err(Code::NamingTooManyArguments, pos, "Too many arguments"),
        TooFewArguments(pos) => err(Code::NamingTooFewArguments, pos, "Too few arguments"),
        ExpectedCollection { pos, cname } => err(
            Code::ExpectedCollection,
            pos,
            format!("Unexpected collection type {}", md_codify(strip_ns(&cname))),
        ),
        IllegalCLASS(pos) => err(
            Code::IllegalClass,
            pos,
            "Using `__CLASS__` outside a class or trait",
        ),
        IllegalTRAIT(pos) => err(Code::IllegalTrait, pos, "Using `__TRAIT__` outside a trait"),
        IllegalMemberVariableClass(pos) => err(
            Code::IllegalMemberVariableClass,
            pos,
            "Cannot declare a constant named `class`. The name `class` is reserved for the class constant that represents the name of the class",
        ),
        IllegalMethCaller(pos) => err(
            Code::IllegalMethCaller,
            pos,
            "The two arguments to `meth_caller()` must be:\
             \n - first: `ClassOrInterface::class`\
             \n - second: a single-quoted string literal containing the name \
             of a non-static method of that class",
        ),
        IllegalClassMeth(pos) => err(
            Code::IllegalClassMeth,
            pos,
            "The two arguments to `class_meth()` must be:\
             \n - first: `ValidClassname::class`\
             \n - second: a single-quoted string literal containing the name \
             of a static method of that class",
        ),
        IllegalConstant(pos) => err(Code::IllegalConstant, pos, "Illegal constant value"),
        ClassMethNonFinalSelf { pos, class_name } => err(
            Code::ClassMethNonFinalSelf,
            pos,
            format!(
                "`class_meth` with `self::class` does not preserve class calling context.\nUse `static::class`, or `{}::class` explicitly",
                strip_ns(&class_name)
            ),
        ),
        ClassMethNonFinalCLASS {
            pos,
            class_name,
            is_trait,
        } => {
            let msg = if is_trait {
                "`class_meth` with `__CLASS__` in non-final classes is not allowed.\n".to_string()
            } else {
                format!(
                    "`class_meth` with `__CLASS__` in non-final classes is not allowed.\nUse `{}::class` explicitly",
                    strip_ns(&class_name)
                )
            };
            err(Code::ClassMethNonFinalCLASS, pos, msg)
        }
        ConstWithoutTypehint {
            pos,
            const_name,
            ty_name,
        } => {
            let name = strip_all_ns(&const_name);
            let (title, new_text) = match ty_name.as_str() {
                "string" => ("Add string type annotation", format!("string {}", name)),
                "int" => ("Add integer type annotation", format!("int {}", name)),
                "float" => ("Add float type annotation", format!("float {}", name)),
                _ => ("Add mixed type annotation", format!("mixed {}", name)),
            };
            let quickfixes = vec![quickfix::make_eager_default_hint_style(
                title.to_string(),
                new_text,
                pos.clone(),
            )];
            with_quickfixes(
                err(
                    Code::AddATypehint,
                    pos,
                    format!("Please add a type hint `const SomeType {}`", name),
                ),
                quickfixes,
            )
        }
        PropWithoutTypehint {
            pos,
            prop_name,
            vis,
        } => err(
            Code::AddATypehint,
            pos,
            format!(
                "Please add a type hint `{} SomeType ${}`",
                visibility_to_string(vis),
                prop_name
            ),
        ),
        InvalidRequireImplements(pos) => err(
            Code::InvalidReqImplements,
            pos,
            "Only traits may use `require implements`",
        ),
        InvalidRequireExtends(pos) => err(
            Code::InvalidReqExtends,
            pos,
            "Only traits and interfaces may use `require extends`",
        ),
        InvalidRequireClass(pos) => err(
            Code::InvalidReqClass,
            pos,
            "Only traits may use `require class`",
        ),
        InvalidRequireConstraint(pos) => err(
            Code::InvalidReqClass,
            pos,
            "Only traits may use `require this <:`",
        ),
        InvalidWildcardContext(pos) => err(
            Code::InvalidWildcardContext,
            pos,
            "A wildcard can only be used as a context when it is the sole context of a callable parameter in a higher-order function. The parameter must also be referenced with `ctx` in the higher-order function's context list, e.g. `function hof((function ()[_]: void) $f)[ctx $f]: void {}`",
        ),
        DidYouMean {
            pos,
            name,
            suggest_pos,
            suggest_name,
        } => {
            let name = strip_ns(&name);
            let suggest_name = strip_ns(&suggest_name);
            let quickfixes = vec![quickfix::make_eager_default_hint_style(
                format!("Change to {}", suggest_name),
                suggest_name.to_string(),
                pos.clone(),
            )];
            with_quickfixes(
                err_with_reasons(
                    Code::DidYouMeanNaming,
                    pos,
                    format!("Could not find {}.", md_codify(name)),
                    vec![suggestion_message(name, suggest_name, suggest_pos)],
                ),
                quickfixes,
            )
        }
        UsingInternalClass { pos, class_name } => err(
            Code::UsingInternalClass,
            pos,
            format!(
                "{} is an implementation internal class that cannot be used directly",
                md_codify(&class_name)
            ),
        ),
        TooFewTypeArguments(pos) => err(
            Code::TooFewTypeArguments,
            pos,
            "Too few type arguments for this type",
        ),
        DynamicClassNameInStrictMode(pos) => err(
            Code::DynamicClassNameInStrictMode,
            pos,
            "Cannot use dynamic class or method name in strict mode",
        ),
        XhpOptionalRequiredAttr { pos, attr_name } => err(
            Code::XhpOptionalRequiredAttr,
            pos,
            format!(
                "XHP attribute {} cannot be marked as nullable and `@required`",
                md_codify(&attr_name)
            ),
        ),
        WildcardHintDisallowed(pos) => err(
            Code::WildcardHintDisallowed,
            pos,
            "Wildcard typehints are not allowed in this position",
        ),
        WildcardTparamDisallowed(pos) => err(
            Code::WildcardTypeParamDisallowed,
            pos,
            "Cannot use anonymous type parameter in this position.",
        ),
        IllegalUseOfDynamicallyCallable {
            attr_pos,
            meth_pos,
            vis,
        } => err_with_reasons(
            Code::IllegalUseOfDynamicallyCallable,
            attr_pos,
            "`__DynamicallyCallable` can only be used on public methods",
            vec![(
                meth_pos,
                format!(
                    "But this method is {}",
                    md_codify(visibility_to_string(vis))
                ),
            )],
        ),
        ParentInFunctionPointer {
            pos,
            meth_name,
            parent_name,
        } => {
            let msg = match parent_name {
                None => "Cannot use `parent::` in a function pointer due to class context ambiguity. Consider using the name of the parent class explicitly.".to_string(),
                Some(id) => format!(
                    "Cannot use `parent::` in a function pointer due to class context ambiguity. Consider using {} instead",
                    md_codify(&format!("{}::{}", strip_ns(&id), meth_name))
                ),
            };
            err(Code::ParentInFunctionPointer, pos, msg)
        }
        SelfInNonFinalFunctionPointer {
            pos,
            meth_name,
            class_name,
        } => {
            let suggestion = match class_name {
                None => String::new(),
                Some(id) => format!(
                    "Consider using {} instead",
                    md_codify(&format!("{}::{}", strip_ns(&id), meth_name))
                ),
            };
            err(
                Code::SelfInNonFinalFunctionPointer,
                pos,
                format!(
                    "Cannot use `self::` in a function pointer in a non-final class due to class context ambiguity. {}",
                    suggestion
                ),
            )
        }
        ReturnOnlyTypehint { pos, kind } => {
            let kstr = md_codify(match kind {
                ReturnOnlyHint::Hvoid => "void",
                ReturnOnlyHint::Hnoreturn => "noreturn",
            });
            err(
                Code::ReturnOnlyTypehint,
                pos,
                format!(
                    "You can only use the {} type as the return type of a function or method",
                    kstr
                ),
            )
        }
        UnexpectedTypeArguments(pos) => err(
            Code::UnexpectedTypeArguments,
            pos,
            "Type arguments are not expected for this type",
        ),
        TooManyTypeArguments(pos) => err(
            Code::TooManyTypeArguments,
            pos,
            "Too many type arguments for this type",
        ),
        ThisAsLexicalVariable(pos) => err(
            Code::ThisAsLexicalVariable,
            pos,
            "Cannot use `$this` as lexical variable",
        ),
        ExplicitConsistentConstructor { pos, classish_kind } => {
            let classish_kind = match classish_kind {
                ClassishKind::Cclass(_) => "class ",
                ClassishKind::Ctrait => "trait ",
                ClassishKind::Cinterface => "interface ",
                ClassishKind::CenumClass(_) => "enum class ",
                ClassishKind::Cenum => "enum ",
            };
            err(
                Code::ExplicitConsistentConstructor,
                pos,
                format!(
                    "This {}is marked <<__ConsistentConstruct>>, so it must declare a constructor explicitly",
                    classish_kind
                ),
            )
        }
        ModuleDeclarationOutsideAllowedFiles(pos) => err(
            Code::ModuleDeclarationOutsideAllowedFiles,
            pos,
            "This module declaration exists in an unapproved file. \
             The set of approved files is in .hhconfig",
        ),
        InternalModuleLevelTrait(pos) => err(
            Code::InternalModuleLevelTrait,
            pos,
            "Internal modules cannot have the <<__ModuleLevelTrait>> attribute",
        ),
        DynamicMethodAccess(pos) => err(
            Code::DynamicMethodAccess,
            pos,
            "Dynamic method access is not allowed. Please use the method name directly, for example `::myMethodName()`",
        ),
        DeprecatedUse { pos, fn_name } => typing_err(
            Typing::DeprecatedUse,
            pos,
            format!(
                "The builtin {} is deprecated.",
                md_codify(strip_ns(&fn_name))
            ),
        ),
        UnnecessaryAttribute {
            pos,
            attr,
            class_pos,
            class_name,
            suggestion,
        } => {
            let class_name = strip_ns(&class_name);
            let suggestion =
                suggestion.unwrap_or_else(|| "Try deleting this attribute".to_string());
            let reasons = vec![
                (
                    class_pos,
                    format!(
                        "It is unnecessary because the class `{}` is final",
                        class_name
                    ),
                ),
                (pos.clone(), suggestion),
            ];
            error_with_reasons(
                Typing::UnnecessaryAttribute as isize,
                pos,
                format!("The attribute `{}` is unnecessary", strip_ns(&attr)),
                reasons,
            )
        }
        DynamicHintDisallowed(pos) => err(
            Code::DynamicHintDisallowed,
            pos,
            "dynamic typehints are not allowed in this position",
        ),
        ToplevelStatement(pos) => err(
            Code::ToplevelStatement,
            pos,
            "Hack does not support top level statements. Use the `__EntryPoint` attribute on a function instead",
        ),
        AttributeOutsideAllowedFiles(pos) => err(
            Code::AttributeOutsideAllowedFiles,
            pos,
            "This attribute exists in an unapproved file. \
             The set of approved files is in .hhconfig. Please talk to someone from the Hack team before changing this.",
        ),
        PolymorphicLambdaMissingReturnHint(pos) => err(
            Code::AddATypehint,
            pos,
            "Return hints must be given explicitly for polymorphic lambda expressions. Please add a type hint.",
        ),
        PolymorphicLambdaMissingParamHint { pos, name } => err(
            Code::AddATypehint,
            pos,
            format!(
                "Parameter hints must be given explicitly for polymorphic lambda expressions. Please add a type hint for `{}`.",
                name
            ),
        ),
    }
}

/// `render_custom_error` (needs the `port` feature, as `Custom_error_eval`).
#[cfg(feature = "port")]
pub fn render_custom_error(
    t: &[itertools::Either<String, crate::custom_error_eval::value::T>],
) -> String {
    use itertools::Either;

    use crate::custom_error_eval::value;
    // `List.fold_right`: from the last element to the first.
    let mut acc = String::new();
    for v in t.iter().rev() {
        acc = match v {
            Either::Left(str) => format!("{}{}", str, acc),
            Either::Right(value::T::Name(nm)) => {
                format!("{}{}", crate::markdown_lite::md_codify(nm), acc)
            }
            Either::Right(_) => acc,
        }
    }
    acc
}
