// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Nast_check_error.to_user_diagnostic` (`nast_check_error.ml`).
//!
//! Quickfixes are not ported.

use oxidized::ast_defs;
use oxidized::diagnostics::Diagnostic;
use oxidized::error_codes::Naming;
use oxidized::error_codes::NastCheck as Code;
use oxidized::error_codes::Typing;
use oxidized::nast_check_error::NastCheckError;
use oxidized::nast_check_error::PackageConstruct;
use oxidized::nast_check_error::Verb;
use oxidized::pos::Pos;

use super::render::md_codify;
use super::render::pluralize_arguments;
use super::render::strip_ns;
use crate::diagnostics::error_with_reasons;

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

/// `Pos.line_column`, `Pos.set_col_start`, `Pos.set_col_end` (`crate::pos`
/// is `port`-only).
fn pos_line_column(p: &Pos) -> (isize, isize) {
    let (lnum, bol, offset) = p.to_raw_span().start.line_beg_offset();
    (lnum as isize, offset as isize - bol as isize)
}

fn set_column(c: isize, p: oxidized::file_pos_large::FilePosLarge) -> oxidized::file_pos_large::FilePosLarge {
    let (lnum, bol, _) = p.line_beg_offset();
    oxidized::file_pos_large::FilePosLarge::from_lnum_bol_offset(lnum, bol, (bol as isize + c) as usize)
}

fn pos_set_col_start(c: isize, pos: &Pos) -> Pos {
    let oxidized::pos_span_raw::PosSpanRaw { start, end } = pos.to_raw_span();
    pos.with_raw_span(oxidized::pos_span_raw::PosSpanRaw { start: set_column(c, start), end })
}

fn pos_set_col_end(c: isize, pos: &Pos) -> Pos {
    let oxidized::pos_span_raw::PosSpanRaw { start, end } = pos.to_raw_span();
    pos.with_raw_span(oxidized::pos_span_raw::PosSpanRaw { start, end: set_column(c, end) })
}

/// `User_diagnostic.make_err ~quickfixes`
fn with_quickfixes(mut d: Diagnostic, quickfixes: Vec<quickfix::Quickfix<Pos>>) -> Diagnostic {
    d.quickfixes = quickfixes;
    d
}

// `Naming_special_names`
const UA_ENTRY_POINT: &str = "__EntryPoint";
const UA_MEMOIZE: &str = "__Memoize";
const UA_MEMOIZE_LSB: &str = "__MemoizeLSB";
const COEFFECTS_CONTEXTS: &str = "\\HH\\Contexts";

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

/// What both package strict inclusion errors are about.
enum PackageStrictInclusionContext {
    /// The name of the attribute.
    RequirePackage(String),
    PackageExpression,
}

fn package_strict_inclusion(
    pos: Pos,
    pkg: &str,
    def_pos: Pos,
    current: &str,
    current_pos: Pos,
    current_package_assignment_kind: &str,
    ctx: PackageStrictInclusionContext,
) -> Diagnostic {
    let (code, primary_msg, location_msg, pkg_label) = match ctx {
        PackageStrictInclusionContext::RequirePackage(attribute_name) => (
            Code::RequirePackageStrictInclusion,
            format!("Invalid {}", attribute_name),
            format!(
                "This function belongs to package `{}` by this {}",
                current, current_package_assignment_kind
            ),
            "required",
        ),
        PackageStrictInclusionContext::PackageExpression => (
            Code::PackageExpressionStrictInclusion,
            "Invalid package expression".to_string(),
            format!(
                "This code belongs to package `{}` by this {}",
                current, current_package_assignment_kind
            ),
            "checked",
        ),
    };
    err_with_reasons(
        code,
        pos,
        primary_msg,
        vec![
            (current_pos, location_msg),
            (
                def_pos,
                format!(
                    "The {} package `{}` must strictly include (i.e. cannot equal) `{}`",
                    pkg_label, pkg, current
                ),
            ),
        ],
    )
}

pub fn to_diagnostic(error: NastCheckError) -> Diagnostic {
    use NastCheckError::*;
    match error {
        RepeatedRecordFieldName {
            pos,
            name,
            prev_pos,
        } => err_with_reasons(
            Code::RepeatedRecordFieldName,
            pos,
            format!("Duplicate record field {}", md_codify(&name)),
            vec![(prev_pos, "Previous field is here".to_string())],
        ),
        DynamicallyCallableReified(pos) => err(
            Code::DynamicallyCallableReified,
            pos,
            "`__DynamicallyCallable` cannot be used on reified functions or methods",
        ),
        NoConstructParent(pos) => err(
            Code::NoConstructParent,
            pos,
            "You are extending a class that needs to be initialized\n\
             Make sure you call `parent::__construct`.\n",
        ),
        NonstaticMethodInAbstractFinalClass(pos) => err(
            Code::NonstaticMethodInAbstractFinalClass,
            pos,
            "Abstract final classes cannot have nonstatic methods or constructors.",
        ),
        ConstructorRequired {
            pos,
            class_name,
            prop_names,
        } => {
            let props_str = prop_names
                .iter()
                .map(|prop| md_codify(prop))
                .collect::<Vec<_>>()
                .join(" ");
            err(
                Code::ConstructorRequired,
                pos,
                format!(
                    "Lacking `__construct`, class {} does not initialize its private member(s): {}",
                    md_codify(strip_ns(&class_name)),
                    props_str
                ),
            )
        }
        NotInitialized {
            pos,
            class_name,
            props,
        } => {
            let prop_msgs = props
                .into_iter()
                .map(|(pos, prop)| {
                    (
                        pos,
                        format!(
                            "{} is not initialized.",
                            md_codify(&format!("$this->{}", prop))
                        ),
                    )
                })
                .collect();
            err_with_reasons(
                Code::NotInitialized,
                pos,
                format!(
                    "Class {} has properties that cannot be null and aren't always set in `__construct`.",
                    md_codify(strip_ns(&class_name))
                ),
                prop_msgs,
            )
        }
        CallBeforeInit { pos, prop_name } => {
            let reason = if prop_name == "parent::__construct" {
                "you forgot to call `parent::__construct`".to_string()
            } else {
                format!(
                    "{} can still potentially be null",
                    md_codify(&format!("$this->{}", prop_name))
                )
            };
            err(
                Code::CallBeforeInit,
                pos,
                format!(
                    "Until the initialization of `$this` is over, \
                     you can only call private methods that are not exposed with `<<__TestsBypassVisibility>>`\n\
                     The initialization is not over because {}",
                    reason
                ),
            )
        }
        AbstractWithBody(pos) => err(
            Code::AbstractWithBody,
            pos,
            "This method is declared as abstract, but has a body",
        ),
        NotAbstractWithoutTypeconst(pos) => err(
            Code::NotAbstractWithoutTypeconst,
            pos,
            "This type constant is not declared as abstract, it must have \
             an assigned type",
        ),
        TypeconstDependsOnExternalTparam {
            pos,
            ext_pos,
            ext_name,
        } => err_with_reasons(
            Code::TypeconstDependsOnExternalTparam,
            pos,
            "A type constant cannot use type parameters",
            vec![(
                ext_pos,
                format!(
                    "{} was declared as a type parameter here",
                    md_codify(&ext_name)
                ),
            )],
        ),
        InterfaceWithPartialTypeconst(pos) => err(
            Code::InterfaceWithPartialTypeconst,
            pos,
            "An interface cannot contain a partially abstract type constant",
        ),
        PartiallyAbstractTypeconstDefinition(pos) => err(
            Code::PartiallyAbstractTypeconstDefinition,
            pos,
            "`as` constraints are only legal on abstract type constants",
        ),
        RefinementInTypestruct { pos, kind } => err(
            Code::RefinementInTypeStruct,
            pos,
            format!(
                "Type refinements cannot appear on the right-hand side of {}.",
                kind
            ),
        ),
        MultipleXhpCategory(pos) => err(
            Code::MultipleXhpCategory,
            pos,
            "XHP classes can only contain one category declaration",
        ),
        ReturnInFinally(pos) => err(
            Code::ReturnInFinally,
            pos,
            "Don't use `return` in a `finally` block; \
             there's nothing to receive the return value",
        ),
        ToplevelBreak(pos) => err(
            Code::ToplevelBreak,
            pos,
            "`break` can only be used inside loops or `switch` statements",
        ),
        ToplevelContinue(pos) => err(
            Code::ToplevelContinue,
            pos,
            "`continue` can only be used inside loops",
        ),
        ContinueInSwitch(pos) => err(
            Code::ContinueInSwitch,
            pos,
            "In PHP, `continue;` inside a switch statement is equivalent to `break;`. \
             Hack does not support this; use `break` if that is what you meant.",
        ),
        AwaitInSyncFunction {
            pos,
            func_pos,
            keyword,
        } => {
            let quickfixes = match func_pos {
                None => vec![],
                Some(fix_pos) => {
                    let (_, start_col) = pos_line_column(&fix_pos);
                    let fix_pos = pos_set_col_end(start_col - 9, &fix_pos);
                    let fix_pos = pos_set_col_start(start_col - 9, &fix_pos);
                    vec![quickfix::make_eager_default_hint_style(
                        format!("Make function {}", md_codify("async")),
                        "async ".to_string(),
                        fix_pos,
                    )]
                }
            };
            with_quickfixes(
                err(
                    Code::AwaitInSyncFunction,
                    pos,
                    format!("`{}` can only be used inside `async` functions", keyword),
                ),
                quickfixes,
            )
        }
        InterfaceUsesTrait(pos) => err(
            Code::InterfaceUsesTrait,
            pos,
            "Interfaces cannot use traits",
        ),
        Magic { pos, meth_name } => err(
            Code::Magic,
            pos,
            format!(
                "{} is a magic method and cannot be called directly",
                md_codify(&meth_name)
            ),
        ),
        NonInterface { pos, name, verb } => {
            let verb_str = match verb {
                Verb::Vimplement => "implement",
                Verb::VreqImplement => "require implementation of",
            };
            err(
                Code::NonInterface,
                pos,
                format!(
                    "Cannot {} {} - it is not an interface",
                    verb_str,
                    md_codify(strip_ns(&name))
                ),
            )
        }
        ToStringReturnsString(pos) => err(
            Code::ToStringReturnsString,
            pos,
            "`__toString` should return a string",
        ),
        ToStringVisibility(pos) => err(
            Code::ToStringVisibility,
            pos,
            "`__toString` must have public visibility and cannot be static",
        ),
        UsesNonTrait { pos, name, kind } => err(
            Code::UsesNonTrait,
            pos,
            format!(
                "{} is not a trait. It is {}.",
                md_codify(strip_ns(&name)),
                kind
            ),
        ),
        RequiresNonClass {
            pos,
            name,
            kind,
            is_interface,
            is_req_this_as_check,
        } => {
            let reasons = if is_req_this_as_check && is_interface {
                vec![(
                    pos.clone(),
                    "Try using `require implements` instead of `require this as`.".to_string(),
                )]
            } else {
                vec![]
            };
            err_with_reasons(
                Code::RequiresNonClass,
                pos,
                format!(
                    "{} is not a class. It is {}.",
                    md_codify(strip_ns(&name)),
                    kind
                ),
                reasons,
            )
        }
        RequiresFinalClass {
            pos,
            name,
            is_req_this_as_check,
        } => {
            let reasons = if is_req_this_as_check {
                vec![(
                    pos.clone(),
                    "Try using `require class` instead of `require this as`.".to_string(),
                )]
            } else {
                vec![]
            };
            err_with_reasons(
                Code::RequiresFinalClass,
                pos,
                format!(
                    "{} is a `final` class, so it cannot be extended.",
                    md_codify(strip_ns(&name))
                ),
                reasons,
            )
        }
        AbstractBody(pos) => err(Code::AbstractBody, pos, "This method shouldn't have a body"),
        InterfaceWithMemberVariable(pos) => err(
            Code::InterfaceWithMemberVariable,
            pos,
            "Interfaces cannot have member variables",
        ),
        InterfaceWithStaticMemberVariable(pos) => err(
            Code::InterfaceWithStaticMemberVariable,
            pos,
            "Interfaces cannot have static variables",
        ),
        IllegalFunctionName { pos, name } => err(
            Code::IllegalFunctionName,
            pos,
            format!("Illegal function name: {}", md_codify(strip_ns(&name))),
        ),
        EntrypointArguments(pos) => err(
            Code::EntryPointArguments,
            pos,
            format!("`{}` functions cannot take arguments.", UA_ENTRY_POINT),
        ),
        EntrypointGenerics(pos) => err(
            Code::EntryPointGenerics,
            pos,
            format!(
                "`{}` functions cannot have generic parameters.",
                UA_ENTRY_POINT
            ),
        ),
        VariadicMemoize(pos) => err(
            Code::VariadicMemoize,
            pos,
            "Memoized functions cannot be variadic or use the type-splat operator.",
        ),
        NamedParamsMemoize(pos) => err(
            Code::NamedParamsMemoize,
            pos,
            "Memoized functions cannot have named parameters yet. Make this parameter positional or drop the memoization.",
        ),
        AbstractMethodMemoize(pos) => err(
            Code::AbstractMethodMemoize,
            pos,
            "Abstract methods cannot be memoized.",
        ),
        InstancePropertyInAbstractFinalClass(pos) => err(
            Code::InstancePropertyInAbstractFinalClass,
            pos,
            "Abstract final classes cannot have instance properties.",
        ),
        InoutParamsSpecial(pos) => err(
            Code::InoutParamsSpecial,
            pos,
            "Methods with special semantics cannot have `inout` parameters.",
        ),
        InoutParamsMemoize { pos, param_pos } => err_with_reasons(
            Code::InoutParamsMemoize,
            pos,
            "Functions with `inout` parameters cannot be memoized",
            vec![(param_pos, "This is an `inout` parameter".to_string())],
        ),
        InoutInTransformedPseudofunction { pos, fn_name } => err(
            Code::InoutInTransformedPsuedofunction,
            pos,
            format!("Unexpected `inout` argument for `{}`", fn_name),
        ),
        NamedInTransformedPseudofunction { pos, fn_name } => err(
            Code::NamedInTransformedPseudofunction,
            pos,
            format!("Unexpected named argument for `{}`", fn_name),
        ),
        ReadingFromAppend(pos) => err(Code::ReadingFromAppend, pos, "Cannot use `[]` for reading"),
        ListRvalue(pos) => err(
            Code::ListRvalue,
            pos,
            "`list()` can only be used for destructuring assignment. Did you mean `tuple()` or `vec[]`?",
        ),
        IllegalDestructor(pos) => err(
            Code::IllegalDestructor,
            pos,
            "Destructors are not supported in Hack; use other patterns like \
             `IDisposable`/`using` or `try`/`catch` instead.",
        ),
        IllegalContext { pos, name } => err(
            Code::IllegalContext,
            pos,
            format!(
                "Illegal context: {}\nCannot use a context defined outside namespace {}",
                md_codify(&name),
                COEFFECTS_CONTEXTS
            ),
        ),
        CaseFallthrough {
            switch_pos,
            case_pos,
            next_pos,
        } => {
            let quickfixes = match next_pos {
                None => vec![],
                Some(next_pos) => {
                    let (_, start_col) = pos_line_column(&next_pos);
                    let offset = "case ".len() as isize;
                    let new_pos = pos_set_col_end(
                        start_col - offset,
                        &pos_set_col_start(start_col - offset, &next_pos),
                    );
                    let new_text = format!(
                        "  // FALLTHROUGH\n{}",
                        " ".repeat((start_col - offset).max(0) as usize)
                    );
                    vec![quickfix::make_eager_default_hint_style(
                        "Mark this `case` as explicitly falling through".to_string(),
                        new_text,
                        new_pos,
                    )]
                }
            };
            with_quickfixes(
                err_with_reasons(
                    Code::CaseFallthrough,
                    switch_pos,
                    "This `switch` has a `case` that implicitly falls through and is \
                     not annotated with `// FALLTHROUGH`",
                    vec![(
                        case_pos,
                        "This `case` implicitly falls through. Did you forget to add `break` or `return`?"
                            .to_string(),
                    )],
                ),
                quickfixes,
            )
        }
        DefaultFallthrough(pos) => err(
            Code::DefaultFallthrough,
            pos,
            "This `switch` has a default case that implicitly falls \
             through and is not annotated with `// FALLTHROUGH`",
        ),
        PhpLambdaDisallowed(pos) => err(
            Code::PhpLambdaDisallowed,
            pos,
            "PHP style anonymous functions are not allowed.",
        ),
        InternalMethodWithInvalidVisibility { pos, vis } => {
            // `Ast_defs.show_visibility`, lowercased.
            let vis_str = match vis {
                ast_defs::Visibility::Private => "private",
                ast_defs::Visibility::Public => "public",
                ast_defs::Visibility::Protected => "protected",
                ast_defs::Visibility::Internal => "internal",
                ast_defs::Visibility::ProtectedInternal => "protectedinternal",
            };
            err(
                Code::InternalProtectedOrPrivate,
                pos,
                format!(
                    "`__Internal` methods must be public, they cannot be {}",
                    md_codify(vis_str)
                ),
            )
        }
        PrivateAndFinal(pos) => err(
            Code::PrivateAndFinal,
            pos,
            "Class methods cannot be both `private` and `final`.",
        ),
        InternalMemberInsidePublicTrait {
            member_pos,
            trait_pos,
            is_method,
        } => {
            let reason = if is_method {
                "Only `internal` or `<<__ModuleLevelTrait>>` traits can have `internal` methods"
            } else {
                "Only `internal` traits can have `internal` members"
            };
            err_with_reasons(
                Code::InternalMemberInsidePublicTrait,
                member_pos,
                "You cannot make this trait member `internal`",
                vec![(trait_pos, reason.to_string())],
            )
        }
        AttributeConflictingMemoize { pos, second_pos } => err_with_reasons(
            Code::AttributeConflictingMemoize,
            pos,
            format!(
                "Methods cannot be both {} and {}.",
                md_codify(UA_MEMOIZE),
                md_codify(UA_MEMOIZE_LSB)
            ),
            vec![(
                second_pos,
                "Conflicting memoize attribute is here".to_string(),
            )],
        ),
        SoftInternalWithoutInternal(pos) => err(
            Code::SoftInternalWithoutInternal,
            pos,
            "<<__SoftInternal>> can only be used on internal symbols. Try adding internal to this symbol.",
        ),
        WrongExpressionKindBuiltinAttribute {
            pos,
            attr_name,
            expr_kind,
        } => typing_err(
            Typing::WrongExpressionKindAttribute,
            pos,
            format!(
                "The {} attribute cannot be used on {}.",
                md_codify(strip_ns(&attr_name)),
                expr_kind
            ),
        ),
        AttributeTooManyArguments {
            pos,
            name,
            expected,
        } => typing_err(
            Typing::AttributeTooManyArguments,
            pos,
            format!(
                "The attribute {} expects at most {}",
                md_codify(&name),
                pluralize_arguments(expected)
            ),
        ),
        AttributeTooFewArguments {
            pos,
            name,
            expected,
        } => typing_err(
            Typing::AttributeTooFewArguments,
            pos,
            format!(
                "The attribute {} expects at least {}",
                md_codify(&name),
                pluralize_arguments(expected)
            ),
        ),
        AttributeNotExactNumberOfArgs {
            pos,
            name,
            actual,
            expected,
        } => {
            let code = if actual > expected {
                Typing::AttributeTooManyArguments
            } else {
                Typing::AttributeTooFewArguments
            };
            let count = match expected {
                0 => "no arguments".to_string(),
                1 => "exactly 1 argument".to_string(),
                _ => format!("exactly {} arguments", expected),
            };
            typing_err(
                code,
                pos,
                format!("The attribute {} expects {}", md_codify(&name), count),
            )
        }
        AttributeParamType { pos, x } => typing_err(
            Typing::AttributeParamType,
            pos,
            format!("This attribute parameter should be {}", x),
        ),
        AttributeNoAutoDynamic(pos) => typing_err(
            Typing::AttributeNoAutoDynamic,
            pos,
            "This attribute is not yet supported in user code",
        ),
        AttributeImplementedByRestriction { restriction, pos } => error_with_reasons(
            Naming::HhiAttributeRestriction as isize,
            pos,
            format!("This attribute can only be used in {}", restriction),
            vec![],
        ),
        GenericAtRuntime { pos, prefix } => typing_err(
            Typing::ErasedGenericAtRuntime,
            pos,
            format!(
                "{} generics can only be used in type hints because they do not exist at runtime.",
                prefix
            ),
        ),
        GenericsNotAllowed(pos) => typing_err(
            Typing::GenericsNotAllowed,
            pos,
            "Generics are not allowed in this position.",
        ),
        LocalVariableModifiedAndUsed { pos, pos_useds } => error_with_reasons(
            Typing::LocalVariableModifedAndUsed as isize,
            pos,
            "Unsequenced modification and access to local variable. Modified here",
            pos_useds
                .into_iter()
                .map(|pos| (pos, "And accessed here".to_string()))
                .collect(),
        ),
        LocalVariableModifiedTwice { pos, pos_modifieds } => error_with_reasons(
            Typing::LocalVariableModifedTwice as isize,
            pos,
            "Unsequenced modifications to local variable. Modified here",
            pos_modifieds
                .into_iter()
                .map(|pos| (pos, "And also modified here".to_string()))
                .collect(),
        ),
        AssignDuringCase(pos) => typing_err(
            Typing::AssignDuringCase,
            pos,
            "Don't assign to variables inside of case labels",
        ),
        ReadBeforeWrite { pos, member_name } => typing_err(
            Typing::ReadBeforeWrite,
            pos,
            format!(
                "Read access to {} before initialization",
                md_codify(&format!("$this->{}", member_name))
            ),
        ),
        LateinitWithDefault(pos) => typing_err(
            Typing::LateInitWithDefault,
            pos,
            "A late-initialized property cannot have a default value",
        ),
        MissingAssign(pos) => typing_err(Typing::MissingAssign, pos, "Please assign a value"),
        CloneReturnType(pos) => err(
            Code::CloneReturnType,
            pos,
            "The return type of `__clone` should be void. `__clone` is called to mutate the new object side-effect-fully",
        ),
        ClassSealedWithTrait {
            pos,
            class_name: _,
            trait_name,
        } => err_with_reasons(
            Code::ClassSealedWithTrait,
            pos.clone(),
            "Traits cannot appear in sealed allowlists",
            vec![(
                pos,
                format!("{} is a trait", md_codify(strip_ns(&trait_name))),
            )],
        ),
        RequirePackageStrictInclusion {
            required_pos,
            required,
            def_pos,
            current,
            current_pos,
            attribute_name,
            current_package_assignment_kind,
        } => package_strict_inclusion(
            required_pos,
            &required,
            def_pos,
            &current,
            current_pos,
            &current_package_assignment_kind,
            PackageStrictInclusionContext::RequirePackage(attribute_name),
        ),
        PackageExpressionStrictInclusion {
            pkg_pos,
            pkg,
            def_pos,
            current,
            current_pos,
            current_package_assignment_kind,
        } => package_strict_inclusion(
            pkg_pos,
            &pkg,
            def_pos,
            &current,
            current_pos,
            &current_package_assignment_kind,
            PackageStrictInclusionContext::PackageExpression,
        ),
        ObservationNotAllowedForPackage {
            pos,
            pkg,
            def_pos,
            construct,
        } => {
            let construct = match construct {
                PackageConstruct::PackageExpression => {
                    format!("The {} expression", md_codify("package"))
                }
                PackageConstruct::RequirePackageAttribute(name) => md_codify(&name),
            };
            err_with_reasons(
                Code::ObservationNotAllowedForPackage,
                pos,
                format!(
                    "{} is not supported for package `{}`, which does not allow deployed-package checks",
                    construct, pkg
                ),
                vec![(
                    def_pos,
                    format!(
                        "`{}` is declared here without `allow_deployed_packages_checking`",
                        pkg
                    ),
                )],
            )
        }
        OverrideNotAllowedForPackage {
            pos,
            pkg,
            def_pos,
            attr,
        } => err_with_reasons(
            Code::OverrideNotAllowedForPackage,
            pos,
            format!(
                "{} is not supported for package `{}`, which has strict isolation enabled",
                md_codify(&attr),
                pkg
            ),
            vec![(
                def_pos,
                format!("`{}` is declared here with strict isolation", pkg),
            )],
        ),
        PackageOverrideTargetNotIncluded {
            override_pos,
            target,
            path_package,
            path_package_pos,
        } => err_with_reasons(
            Code::PackageOverrideTargetNotIncluded,
            override_pos,
            "Invalid `__PackageOverride`",
            vec![
                (
                    path_package_pos.clone(),
                    format!(
                        "This file belongs to package `{}` by this entry in the package config",
                        path_package
                    ),
                ),
                (
                    path_package_pos,
                    format!(
                        "A file may only be overridden into a package that its own package includes, but `{}` does not include the override target `{}`",
                        path_package, target
                    ),
                ),
            ],
        ),
        RedundantPackageOverride { pos, pkg, def_pos } => err_with_reasons(
            Code::RedundantPackageOverride,
            pos,
            "Redundant `__PackageOverride`",
            vec![(
                def_pos,
                format!(
                    "This file already belongs to package `{}` by this entry in the package config, so this override has no effect and should be removed",
                    pkg
                ),
            )],
        ),
    }
}
