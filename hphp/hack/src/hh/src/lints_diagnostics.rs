// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/lints_diagnostics.ml`. See `hh/PORTING.md`.
//!
//! The messages are built from the same pieces as in OCaml (`concat`), in
//! the same order.

use oxidized::local_id::LocalId;
use oxidized::package::PosId;
use oxidized::pos::Pos;

// module Codes = Lints_codes.Codes
use crate::lints_codes::codes;
// open Lints_core
use crate::lints_core::Severity::LintAdvice;
use crate::lints_core::Severity::LintError;
use crate::lints_core::Severity::LintWarning;
// module Lints = Lints_core
use crate::lints_core as lints;
use crate::markdown_lite::md_codify;
use crate::tast::CheckStatus;
use crate::typing_error::Lazy;
use crate::typing_warning;
use crate::utils::strip_ns;

/// `a ^ b ^ ...`
fn concat(pieces: &[&str]) -> String {
    pieces.concat()
}

pub fn quickfix(
    typing_warning::Quickfix {
        can_be_captured,
        original_pos,
        replacement_pos,
    }: &typing_warning::Quickfix,
) -> (String, Pos) {
    let path = crate::pos::filename(&crate::pos::to_absolute(original_pos));
    let lines = crate::diagnostics::read_lines(&path);
    let content = lines.join("\n");
    let modified = crate::pos::get_text_from_pos(&content, replacement_pos);
    let modified = if *can_be_captured {
        concat(&["(", &modified, ")"])
    } else {
        modified
    };
    (modified, original_pos.clone())
}

pub fn clone_use(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::CLONE_USE,
        LintAdvice,
        p,
        concat(&[
            "Objects created with `clone` will have references to shared ",
            "deep objects. Prefer to implement your own explicit copy ",
            "method to ensure the semantics you want. See ",
            "http://php.net/manual/en/language.oop5.cloning.php",
        ]),
    )
}

pub fn deprecated(p: Pos, msg: String) {
    lints::add(None, None, None, codes::DEPRECATED, LintWarning, p, msg)
}

pub fn include_use(p: Pos, msg: String) {
    lints::add(None, None, None, codes::INCLUDE_USE, LintError, p, msg)
}

pub fn if_literal(p: Pos, msg: String) {
    lints::add(None, None, None, codes::IF_LITERAL, LintWarning, p, msg)
}

pub fn loop_variable_shadows_local_variable(p1: Pos, id: &LocalId, p2: &Pos) {
    lints::add(
        None,
        None,
        None,
        codes::LOOP_VARIABLE_SHADOWS_LOCAL_VARIABLE,
        LintWarning,
        p1,
        format!(
            "Loop variable {} shadows a local variable defined or last assigned here:\n{}",
            md_codify(crate::local_id::get_name(id)),
            crate::pos::string(&crate::pos::to_relative_string(p2))
        ),
    )
}

pub fn bad_virtualized_method(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::BOOL_METHOD_RETURN_HINT,
        LintWarning,
        p,
        "`__bool` methods should return `bool`. They show that an expression tree type can be used in a boolean expression.".to_string(),
    )
}

pub fn class_overrides_all_trait_methods(pos: Pos, class_name: &str, trait_name: &str) {
    lints::add(
        None,
        None,
        None,
        codes::CLASS_OVERRIDES_ALL_TRAIT_METHODS,
        LintWarning,
        pos,
        format!(
            "Unused trait: {} is overriding all the methods in {}",
            md_codify(strip_ns(class_name)),
            md_codify(strip_ns(trait_name))
        ),
    )
}

pub fn trait_requires_class_that_overrides_method(
    pos: Pos,
    class_name: &str,
    trait_name: &str,
    method_name: &str,
) {
    lints::add(
        None,
        None,
        None,
        codes::UNREACHABLE_METHOD_IN_TRAIT,
        LintWarning,
        pos,
        format!(
            "Method {} in trait {} is overridden in class {} and trait {} has `require class {}`. This method is never used.",
            md_codify(strip_ns(method_name)),
            md_codify(strip_ns(trait_name)),
            md_codify(strip_ns(class_name)),
            md_codify(strip_ns(trait_name)),
            strip_ns(class_name)
        ),
    )
}

pub fn invalid_switch_case_value_type(
    case_value_p: Pos,
    case_value_ty: &Lazy<String>,
    scrutinee_ty: &Lazy<String>,
) {
    // The arguments of `Printf.sprintf` are evaluated from right to left:
    // `scrutinee_ty` is forced first.
    let scrutinee_ty = md_codify(scrutinee_ty.force());
    let case_value_ty = md_codify(case_value_ty.force());
    lints::add(
        None,
        None,
        None,
        codes::INVALID_SWITCH_CASE_VALUE_TYPE,
        LintWarning,
        case_value_p,
        format!(
            "Switch statements use `===` equality. Comparing values of type {} with {} may not give the desired result.",
            case_value_ty, scrutinee_ty
        ),
    )
}

pub fn missing_override_attribute(
    meth_pos: &Pos,
    first_attr_pos: Option<&Pos>,
    name_pos: Pos,
    class_name: &str,
    method_name: &str,
) {
    let msg = format!(
        "Method {} is also defined on {}, but this method is missing `<<__Override>>`.",
        md_codify(method_name),
        md_codify(strip_ns(class_name))
    );
    let autofix = match first_attr_pos {
        Some(first_attr_pos) => {
            // The method already has <<Foo, Bar>> attributes, add __Override.
            let fix_pos = crate::pos::shrink_to_start(first_attr_pos);
            Some(("__Override, ".to_string(), fix_pos))
        }
        None => {
            // The method has no attributes.
            let fix_pos = crate::pos::shrink_to_start(meth_pos);
            Some(("<<__Override>>\n  ".to_string(), fix_pos))
        }
    };

    lints::add(
        None,
        None,
        Some(autofix),
        codes::MISSING_OVERRIDE_ATTRIBUTE,
        LintError,
        name_pos,
        msg,
    )
}

pub fn redundant_covariant(pos: Pos, name: &str, msg: &str, suggest: &str) {
    lints::add(
        None,
        None,
        None,
        codes::REDUNDANT_GENERIC,
        LintWarning,
        pos,
        concat(&[
            "The generic parameter ",
            &md_codify(name),
            " is redundant because it only appears in a covariant (output) position",
            msg,
            ". Consider replacing uses of generic parameter with ",
            &md_codify(suggest),
            " or specifying `<<__Explicit>>` on the generic parameter",
        ]),
    )
}

pub fn redundant_contravariant(pos: Pos, name: &str, msg: &str, suggest: &str) {
    lints::add(
        None,
        None,
        None,
        codes::REDUNDANT_GENERIC,
        LintWarning,
        pos,
        concat(&[
            "The generic parameter ",
            &md_codify(name),
            " is redundant because it only appears in a contravariant (input) position",
            msg,
            ". Consider replacing uses of generic parameter with ",
            &md_codify(suggest),
            " or specifying `<<__Explicit>>` on the generic parameter",
        ]),
    )
}

pub fn redundant_generic(pos: Pos, name: &str) {
    lints::add(
        None,
        None,
        None,
        codes::REDUNDANT_GENERIC,
        LintWarning,
        pos,
        format!("The generic parameter {} is unused.", md_codify(name)),
    )
}

pub fn inferred_variance(pos: Pos, name: &str, description: &str, syntax: &str) {
    lints::add(
        None,
        None,
        None,
        codes::INFERRED_VARIANCE,
        LintAdvice,
        pos,
        concat(&[
            "The generic parameter ",
            &md_codify(name),
            " could be marked ",
            description,
            ". Consider prefixing it with ",
            syntax,
        ]),
    )
}

pub fn parse_error(code: isize, pos: Pos, msg: String) {
    lints::add(None, None, None, code, LintError, pos, msg)
}

pub fn prettify_class_list(names: &[String]) -> String {
    match names {
        [] => "".to_string(),
        [c] => c.clone(),
        [c1, c2] => concat(&[c1, " and ", c2]),
        [h, t @ ..] => concat(&[h, ", ", &prettify_class_list(t)]),
    }
}

pub fn duplicate_property_class_constant_init(
    pos: Pos,
    class_name: &str,
    prop_name: &str,
    class_names: &[String],
) {
    let class_names: Vec<String> = class_names
        .iter()
        .map(|n| strip_ns(n).to_string())
        .collect();
    lints::add(
        None,
        None,
        None,
        codes::DUPLICATE_PROPERTY_ENUM_INIT,
        LintError,
        pos,
        concat(&[
            "Property ",
            &md_codify(strip_ns(prop_name)),
            ", defined in ",
            &prettify_class_list(&class_names),
            ", is inherited multiple times by class ",
            &md_codify(strip_ns(class_name)),
            " and one of its instances is initialised with a class or enum constant",
        ]),
    )
}

pub fn duplicate_property(pos: Pos, class_name: &str, prop_name: &str, class_names: &[String]) {
    let class_names: Vec<String> = class_names
        .iter()
        .map(|n| md_codify(strip_ns(n)))
        .collect();
    lints::add(
        None,
        None,
        None,
        codes::DUPLICATE_PROPERTY,
        LintWarning,
        pos,
        concat(&[
            "Duplicated property ",
            &md_codify(strip_ns(prop_name)),
            " in ",
            &md_codify(strip_ns(class_name)),
            " (defined in ",
            &prettify_class_list(&class_names),
            "): all instances will be aliased at runtime",
        ]),
    )
}

pub fn redundant_cast(
    can_be_captured: bool,
    check_status: CheckStatus,
    cast: &str,
    cast_pos: Pos,
    expr_pos: Pos,
) {
    let msg = concat(&[
        "This use of `",
        cast,
        "` is redundant since the type of the expression is a subtype of the type being cast to.",
        " Please consider removing this cast.",
        " This cast is runtime significant and types might occasionally lie.",
        " Please be prudent when acting on this lint.",
    ]);
    let autofix = Some(quickfix(&typing_warning::Quickfix {
        can_be_captured,
        original_pos: cast_pos.clone(),
        replacement_pos: expr_pos,
    }));
    lints::add(
        Some(Some(check_status)),
        None,
        Some(autofix),
        codes::REDUNDANT_CAST,
        LintAdvice,
        cast_pos,
        msg,
    )
}

pub fn switch_nonexhaustive(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::SWITCH_NONEXHAUSTIVE,
        LintWarning,
        p,
        concat(&[
            "This switch statement is not exhaustive.",
            " The expression it scrutinises has a type with infinitely many values and the statement does not have a default case.",
            " If none of the cases match, an exception will be thrown.",
            " Consider adding a default case.",
        ]),
    )
}

pub fn calling_pointless_boolean(p_lint: Pos, p_quickfix: Pos, replacement: String, txt: String) {
    lints::add(
        None,
        None,
        Some(Some((replacement, p_quickfix))),
        codes::POINTLESS_BOOLEANS_EXPRESSION,
        LintWarning,
        p_lint,
        txt,
    )
}

pub fn comparing_booleans(p_expr: Pos, p_var: &Pos, name: &str, value: bool) {
    let msg = if value {
        concat(&[
            "Consider changing this statement to ",
            "(",
            name,
            ") instead",
        ])
    } else {
        concat(&[
            "Consider changing this statement to ",
            "(!",
            name,
            ") instead",
        ])
    };
    let path = crate::pos::filename(&crate::pos::to_absolute(p_var));
    let lines = crate::diagnostics::read_lines(&path);
    let src = lines.join("\n");
    let replacement = if value {
        crate::pos::get_text_from_pos(&src, p_var)
    } else {
        // `String.make 1 '!' ^ ...`
        concat(&["!", &crate::pos::get_text_from_pos(&src, p_var)])
    };
    lints::add(
        None,
        None,
        Some(Some((replacement, p_expr.clone()))),
        codes::COMPARING_BOOLEANS,
        LintAdvice,
        p_expr,
        msg,
    )
}

pub fn unconditional_recursion(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::UNCONDITIONAL_RECURSION,
        LintError,
        p,
        concat(&[
            "This is a recursive function with no base case to terminate. This will result in a Stack Overflow error.",
            " Consider adding a base case.",
        ]),
    )
}

pub fn branches_return_same_value(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::BRANCH_RETURN_SAME_VALUE,
        LintWarning,
        p,
        "There are multiple return statements, but they all return the same value.".to_string(),
    )
}

pub fn internal_classname(p: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::INTERNAL_CLASSNAME,
        LintWarning,
        p,
        concat(&[
            "This is a classname of an `internal` class. Internal classnames are dangerous because they are effectively raw strings. ",
            "Please avoid them, or make sure that they are never used outside of the module.",
        ]),
    )
}

pub fn async_lambda(pos: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::ASYNC_LAMBDA,
        LintAdvice,
        pos,
        "Use `async ... ==> await ...` for lambdas that directly return `Awaitable`s, so stack traces include the lambda position.".to_string(),
    )
}

pub fn awaitable_awaitable(pos: Pos) {
    lints::add(
        None,
        None,
        None,
        codes::AWAITABLE_AWAITABLE,
        LintWarning,
        pos,
        concat(&[
            "This lambda returns an Awaitable of Awaitable.",
            " You probably want to use await inside this async lambda,",
            " so stack traces include the lambda position.",
            " If this is intentional, please annotate the return type.",
        ]),
    )
}

/// Shared by both endpoints, so the message phrases them alike and the reader
/// can compare them.
pub fn package_membership_clause(package_name: &str, has_package_override: bool) -> String {
    if has_package_override {
        concat(&["`__PackageOverride('", package_name, "')`"])
    } else {
        "its entry in the package config".to_string()
    }
}

/// `Option.value_map package ~default:"<none>" ~f:snd`
fn package_name(package: Option<&PosId>) -> &str {
    package.map_or("<none>", |PosId(_, name)| name.as_str())
}

pub fn package_into_override(
    pos: Pos,
    current_package: Option<&PosId>,
    current_package_before_override: Option<&str>,
    caller_has_package_override: bool,
    target_package: Option<&PosId>,
    target_package_before_override: Option<&str>,
    callee_has_package_override: bool,
) {
    let current_package_name = package_name(current_package);
    let target_package_name = package_name(target_package);
    let current_package_before_override_name = current_package_before_override.unwrap_or("<none>");
    let target_package_before_override_name = target_package_before_override.unwrap_or("<none>");
    let both_overridden = caller_has_package_override && callee_has_package_override;
    lints::add(
        None,
        None,
        None,
        codes::PACKAGE_INTO_OVERRIDE,
        LintError,
        pos,
        concat(&[
            "This is a cross-boundary edge. Although the caller is in package ",
            current_package_name,
            " via ",
            &package_membership_clause(current_package_name, caller_has_package_override),
            " and the callee is in package ",
            target_package_name,
            " via ",
            &package_membership_clause(target_package_name, callee_has_package_override),
            // "together": only the pair is provably load-bearing, either override
            // alone may well be removable.
            if both_overridden {
                ", together those package overrides are load-bearing here: without them "
            } else {
                ", that package override is load-bearing here: without it "
            },
            "the caller stays in package ",
            current_package_before_override_name,
            " and the callee stays in package ",
            target_package_before_override_name,
            ", which ",
            current_package_before_override_name,
            " cannot reach, so this edge would be an error. This edge prevents removal of the `__PackageOverride` ",
            if both_overridden {
                "attributes"
            } else {
                "attribute"
            },
            " and SHOULD BE REMOVED. Either move the callee into a package that ",
            current_package_before_override_name,
            " can reach via hg mv, ",
            "use `__RequirePackage` (if the whole function should only be invoked from ",
            target_package_before_override_name,
            ") or gate this reference via a `package` check ",
            "(if this portion of the function is meant to be gated by an environment check).",
        ]),
    )
}

pub fn crosspackage_classptr_reference(
    pos: Pos,
    current_package: Option<&PosId>,
    target_package_before_override: Option<&str>,
    caller_has_package_override: bool,
) {
    let current_package_name = package_name(current_package);
    let target_package_before_override_name = target_package_before_override.unwrap_or("<none>");
    lints::add(
        None,
        None,
        None,
        codes::CROSSPACKAGE_CLASSPTR_REFERENCE,
        LintError,
        pos,
        concat(&[
            "This is a cross-boundary edge from package ",
            current_package_name,
            " into package ",
            target_package_before_override_name,
            ". Consider one of the following:\n",
            "  (1) if this value isn't used to load the class via new $cls(), $cls::meth(), etc, change this to a `nameof` expression;\n",
            "  (2) use `__RequirePackage` (if the function should only be invoked from ",
            target_package_before_override_name,
            ");\n",
            "  (3) gate this reference via a `package` check (if this portion of the function is meant to be gated by an environment check).\n",
            "Alternatively, move the callee into the caller's package via `sl mv`.\n",
            "See https://docs.hhvm.com/hack/packages/cross-package-calls for examples.",
            &if caller_has_package_override {
                concat(&[
                    "\nYou may also consider adding `<<file: __PackageOverride('",
                    current_package_name,
                    "')>>` to the target file to include it in the ",
                    current_package_name,
                    " package for safety.",
                ])
            } else {
                "".to_string()
            },
        ]),
    )
}

/// wrapper around crosspackage_classconst_reference and package_into_override
pub fn crosspackage_linter(
    pos: Pos,
    current_package: Option<&PosId>,
    current_package_before_override: Option<&str>,
    caller_has_package_override: bool,
    target_package: Option<&PosId>,
    target_package_before_override: Option<&str>,
    callee_has_package_override: bool,
    classptr_reference_warning: bool,
) {
    if classptr_reference_warning {
        crosspackage_classptr_reference(
            pos,
            current_package,
            target_package_before_override,
            caller_has_package_override,
        )
    } else {
        package_into_override(
            pos,
            current_package,
            current_package_before_override,
            caller_has_package_override,
            target_package,
            target_package_before_override,
            callee_has_package_override,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::lints_core;

    fn pos(line: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        let bol = line * 100;
        Pos::from_lnum_bol_offset(file, (line, bol, bol + 2), (line, bol, bol + 6))
    }

    #[test]
    fn class_lists() {
        let names = |l: &[&str]| l.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(prettify_class_list(&names(&[])), "");
        assert_eq!(prettify_class_list(&names(&["A"])), "A");
        assert_eq!(prettify_class_list(&names(&["A", "B"])), "A and B");
        assert_eq!(prettify_class_list(&names(&["A", "B", "C"])), "A, B and C");
    }

    #[test]
    fn crosspackage() {
        let pkg = |name: &str| PosId(pos(1), name.to_string());
        let (lints, ()) = lints_core::do_(|| {
            crosspackage_linter(
                pos(1),
                Some(&pkg("a")),
                None,
                true,
                Some(&pkg("b")),
                Some("b0"),
                false,
                true,
            );
            crosspackage_linter(
                pos(2),
                None,
                Some("a0"),
                true,
                Some(&pkg("b")),
                Some("b0"),
                true,
                false,
            );
        });
        assert_eq!(lints.len(), 2);
        assert_eq!(lints[0].code, codes::PACKAGE_INTO_OVERRIDE);
        assert_eq!(
            lints[0].message,
            "This is a cross-boundary edge. Although the caller is in package <none> via `__PackageOverride('<none>')` and the callee is in package b via `__PackageOverride('b')`, together those package overrides are load-bearing here: without them the caller stays in package a0 and the callee stays in package b0, which a0 cannot reach, so this edge would be an error. This edge prevents removal of the `__PackageOverride` attributes and SHOULD BE REMOVED. Either move the callee into a package that a0 can reach via hg mv, use `__RequirePackage` (if the whole function should only be invoked from b0) or gate this reference via a `package` check (if this portion of the function is meant to be gated by an environment check)."
        );
        assert_eq!(lints[1].code, codes::CROSSPACKAGE_CLASSPTR_REFERENCE);
        assert!(lints[1].message.starts_with(
            "This is a cross-boundary edge from package a into package b0. Consider one of the following:\n  (1) "
        ));
        assert!(lints[1].message.ends_with(
            "for examples.\nYou may also consider adding `<<file: __PackageOverride('a')>>` to the target file to include it in the a package for safety."
        ));
    }

    #[test]
    fn override_autofix() {
        let (lints, ()) = lints_core::do_(|| {
            missing_override_attribute(&pos(1), None, pos(1), "\\C", "m");
        });
        let lint = &lints[0];
        assert_eq!(
            lint.message,
            "Method `m` is also defined on `C`, but this method is missing `<<__Override>>`."
        );
        let (text, fix_pos) = lint.autofix.clone().unwrap();
        assert_eq!(text, "<<__Override>>\n  ");
        assert_eq!(fix_pos.info_raw(), (102, 102));
    }
}
