// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `options/experimental_features.ml`: the
//! functions that read the feature statuses of `.hhconfig` (the others are
//! methods of the `oxidized` types). See `hh/PORTING.md`.
//!
//! The types are `oxidized::experimental_features`'s, re-exported. The names
//! of `feature_name_map` are those of `FeatureName` in snake case (its
//! `FromStr`), and those of `feature_status_map` the constructors of
//! `FeatureStatus`, as in OCaml.

use std::str::FromStr;

pub use oxidized::experimental_features::*;

use crate::yojson::safe::T as Json;

pub fn feature_status_from_string(s: &str) -> Option<FeatureStatus> {
    FeatureStatus::from_str(s).ok()
}

pub fn feature_name_from_string(s: &str) -> Option<FeatureName> {
    FeatureName::from_str(s).ok()
}

/// A feature of the JSON object of `enable_experimental_stx_features`.
/// Fails (`failwith`, a panic) on a status that is not a string, an unknown
/// name or an unknown status.
pub fn parse_experimental_feature(
    (name_string, status_json): &(String, Json),
) -> (String, FeatureStatus) {
    let status_string = match status_json {
        Json::String(s) => s,
        _ => panic!("expected string for experimental feature status"),
    };
    match (
        feature_name_from_string(name_string),
        feature_status_from_string(status_string),
    ) {
        (Some(_name), Some(status)) => (name_string.clone(), status),
        (None, _) => panic!("Invalid experimental feature name: {}", name_string),
        (_, None) => panic!("Invalid experimental feature status: {}", status_string),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn feature(name: &str, status: Json) -> (String, Json) {
        (name.to_string(), status)
    }

    #[test]
    fn names_and_statuses() {
        assert_eq!(
            feature_name_from_string("context_alias_declaration_short"),
            Some(FeatureName::ContextAliasDeclarationShort)
        );
        assert_eq!(
            feature_name_from_string("ContextAliasDeclarationShort"),
            None
        );
        assert_eq!(
            feature_status_from_string("OngoingRelease"),
            Some(FeatureStatus::OngoingRelease)
        );
        assert_eq!(feature_status_from_string("ongoing_release"), None);
        assert_eq!(
            parse_experimental_feature(&feature("pipe_await", Json::String("Preview".to_string()))),
            ("pipe_await".to_string(), FeatureStatus::Preview)
        );
    }

    /// Every name of OCaml's `feature_name_map` and `feature_status_map`
    /// (`FeatureName` has 51 constructors too).
    #[test]
    fn all_names_of_the_ocaml_maps() {
        let names = [
            (
                "union_intersection_type_hints",
                FeatureName::UnionIntersectionTypeHints,
            ),
            ("expression_trees", FeatureName::ExpressionTrees),
            ("readonly", FeatureName::Readonly),
            ("module_references", FeatureName::ModuleReferences),
            (
                "context_alias_declaration",
                FeatureName::ContextAliasDeclaration,
            ),
            (
                "context_alias_declaration_short",
                FeatureName::ContextAliasDeclarationShort,
            ),
            (
                "type_const_multiple_bounds",
                FeatureName::TypeConstMultipleBounds,
            ),
            ("type_const_super_bound", FeatureName::TypeConstSuperBound),
            ("class_const_default", FeatureName::ClassConstDefault),
            ("upcast_expression", FeatureName::UpcastExpression),
            ("require_constraint", FeatureName::RequireConstraint),
            ("newtype_super_bounds", FeatureName::NewtypeSuperBounds),
            ("case_types", FeatureName::CaseTypes),
            ("case_type_where_clauses", FeatureName::CaseTypeWhereClauses),
            ("recursive_case_types", FeatureName::RecursiveCaseTypes),
            ("module_level_traits", FeatureName::ModuleLevelTraits),
            (
                "module_level_traits_extensions",
                FeatureName::ModuleLevelTraitsExtensions,
            ),
            ("pipe_await", FeatureName::PipeAwait),
            ("match_statements", FeatureName::MatchStatements),
            ("strict_switch", FeatureName::StrictSwitch),
            ("class_type", FeatureName::ClassType),
            ("function_references", FeatureName::FunctionReferences),
            (
                "function_type_optional_params",
                FeatureName::FunctionTypeOptionalParams,
            ),
            ("await_in_splice", FeatureName::AwaitInSplice),
            ("open_tuples", FeatureName::OpenTuples),
            ("type_splat", FeatureName::TypeSplat),
            (
                "expression_tree_nested_bindings",
                FeatureName::ExpressionTreeNestedBindings,
            ),
            ("like_type_hints", FeatureName::LikeTypeHints),
            (
                "shape_and_tuple_destructuring",
                FeatureName::ShapeAndTupleDestructuring,
            ),
            (
                "expression_tree_shape_creation",
                FeatureName::ExpressionTreeShapeCreation,
            ),
            ("no_disjoint_union", FeatureName::NoDisjointUnion),
            ("simpli_hack", FeatureName::SimpliHack),
            (
                "polymorphic_function_hints",
                FeatureName::PolymorphicFunctionHints,
            ),
            ("polymorphic_lambda", FeatureName::PolymorphicLambda),
            (
                "expression_tree_coalesce_operator",
                FeatureName::ExpressionTreeCoalesceOperator,
            ),
            (
                "expression_tree_nullsafe_obj_get",
                FeatureName::ExpressionTreeNullsafeObjGet,
            ),
            ("named_parameters", FeatureName::NamedParameters),
            ("xhp_type_constants", FeatureName::XhpTypeConstants),
            ("capture_pipe_variables", FeatureName::CapturePipeVariables),
            (
                "allow_extended_await_syntax",
                FeatureName::AllowExtendedAwaitSyntax,
            ),
            (
                "allow_conditional_await_syntax",
                FeatureName::AllowConditionalAwaitSyntax,
            ),
            (
                "expression_tree_hack_arrays",
                FeatureName::ExpressionTreeHackArrays,
            ),
            (
                "expression_tree_subscript",
                FeatureName::ExpressionTreeSubscript,
            ),
            ("shape_field_punning", FeatureName::ShapeFieldPunning),
            ("representable_as", FeatureName::RepresentableAs),
            (
                "class_aliases_everywhere",
                FeatureName::ClassAliasesEverywhere,
            ),
            ("test_feature", FeatureName::TestFeature),
            ("with_refinement_alias", FeatureName::WithRefinementAlias),
            ("shape_splat_concrete", FeatureName::ShapeSplatConcrete),
            (
                "shape_splat_type_parameters",
                FeatureName::ShapeSplatTypeParameters,
            ),
            ("shape_splat_expression", FeatureName::ShapeSplatExpression),
            (
                "named_parameters_meth_caller",
                FeatureName::NamedParametersMethCaller,
            ),
        ];
        for (name, feature) in names {
            assert_eq!(feature_name_from_string(name), Some(feature), "{}", name);
        }
        assert_eq!(names.len(), 52);
        for (name, status) in [
            ("Unstable", FeatureStatus::Unstable),
            ("Preview", FeatureStatus::Preview),
            ("Migration", FeatureStatus::Migration),
            ("Deprecated", FeatureStatus::Deprecated),
            ("OngoingRelease", FeatureStatus::OngoingRelease),
        ] {
            assert_eq!(feature_status_from_string(name), Some(status));
        }
    }

    #[test]
    #[should_panic(expected = "Invalid experimental feature name: no_such_feature")]
    fn unknown_name() {
        parse_experimental_feature(&feature("no_such_feature", Json::String("Bad".to_string())));
    }

    #[test]
    #[should_panic(expected = "Invalid experimental feature status: Bad")]
    fn unknown_status() {
        parse_experimental_feature(&feature("pipe_await", Json::String("Bad".to_string())));
    }

    #[test]
    #[should_panic(expected = "expected string for experimental feature status")]
    fn status_not_a_string() {
        parse_experimental_feature(&feature("pipe_await", Json::Int(1)));
    }
}
