// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The nested modules of `Typing_error_utils.Eval_primary` (`Eval_shape`,
//! `Eval_destructure`, ...). See `../mod.rs`.
//!
//! Conventions of this file:
//!
//! - `to_error t ~env:_` is `to_error(t, _env)`. `Eval_primary.to_error` has
//!   the type `Typing_error.Primary.t -> env:'a -> t`: no function of
//!   `Eval_primary` looks at the environment, so the parameter is generic
//!   here as well.
//! - `Pos_or_decl.of_raw_pos` and `Pos_or_decl.unsafe_to_raw_pos` have no
//!   counterpart: `oxidized::pos_or_decl::PosOrDecl` is `Pos`. The places
//!   where OCaml calls them are marked.
//! - A value that the OCaml captures in a `lazy` is taken by value.

use oxidized::error_codes::Typing;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use super::T;
use super::create;
use crate::naming_errors::render;
use crate::naming_errors::render::md_codify;
use crate::typing_error_utils::common;
use crate::typing_error_utils::common::Lazy;

pub mod eval_shape {
    use super::*;
    use crate::typing_error::primary::shape;

    pub fn invalid_shape_field_type(
        pos: Pos,
        ty_pos: PosOrDecl,
        ty_name: Lazy<String>,
        trail: Vec<PosOrDecl>,
    ) -> T {
        let reasons = Lazy::new(move || {
            let mut reasons = vec![Message(ty_pos, format!("Not {}", ty_name.force()).into())];
            reasons.extend(common::reasons_of_trail(&trail));
            reasons
        });
        let claim = Lazy::new(move || {
            Message(
                pos,
                "A shape field name must be an `int` or `string`".into(),
            )
        });
        create(Typing::InvalidShapeFieldType, claim, Some(reasons), None)
    }

    pub fn invalid_shape_field_name(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Shape access requires a string literal, integer literal, or a class constant"
                    .into(),
            )
        });
        create(Typing::InvalidShapeFieldName, claim, None, None)
    }

    pub fn invalid_shape_field_name_empty(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(pos, "A shape field name cannot be an empty string".into())
        });
        create(Typing::InvalidShapeFieldNameEmpty, claim, None, None)
    }

    pub fn invalid_shape_field_literal(pos: Pos, witness_pos: Pos) -> T {
        let claim =
            Lazy::new(move || Message(pos, "Shape uses literal string as field name".into()));
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                witness_pos,
                "But expected a class constant. Shape fields cannot be a mix of literals and constants."
                    .into(),
            )]
        });
        create(Typing::InvalidShapeFieldLiteral, claim, Some(reasons), None)
    }

    pub fn invalid_shape_field_const(pos: Pos, witness_pos: Pos) -> T {
        let claim =
            Lazy::new(move || Message(pos, "Shape uses class constant as field name".into()));
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                witness_pos,
                "But expected a literal string. Shape fields cannot be a mix of literals and constants."
                    .into(),
            )]
        });
        create(Typing::InvalidShapeFieldConst, claim, Some(reasons), None)
    }

    pub fn abstract_shape_field_const(pos: Pos, decl_pos: PosOrDecl, name: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Abstract constant {} cannot be used as a shape key",
                    md_codify(render::strip_ns(&name))
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || vec![Message(decl_pos, "Declaration is here".into())]);
        create(Typing::AbstractConstUsage, claim, Some(reasons), None)
    }

    pub fn shape_field_class_const_missing_shape_key_attribute(
        pos: Pos,
        decl_pos: PosOrDecl,
        class_name: String,
        const_name: String,
    ) -> T {
        let class_const = format!("{}::{}", class_name, const_name);
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Class constant {} used as a shape key must be annotated with {}. Prefer using an enum constant as a shape key.",
                    md_codify(&class_const),
                    md_codify("<<__ShapeKey>>")
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                "The class constant is declared here".into(),
            )]
        });
        create(
            Typing::ShapeKeyClassConstMissingAttribute,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shape_key_const_value_unresolvable(
        pos: Pos,
        reason_pos: PosOrDecl,
        class_name: String,
        const_name: String,
        const_kind: shape::ShapeKeyConstValueUnresolvableConstKind,
    ) -> T {
        let const_name_coded = md_codify(&format!("{}::{}", class_name, const_name));
        let claim = Lazy::new(move || {
            let subject = match const_kind {
                shape::ShapeKeyConstValueUnresolvableConstKind::Enum => {
                    format!("Enum constant {} used as a shape key", const_name_coded)
                }
                shape::ShapeKeyConstValueUnresolvableConstKind::ClassConst => format!(
                    "Class constant {} marked with `<<__ShapeKey>>`",
                    const_name_coded
                ),
            };
            Message(
                pos,
                format!(
                    "{} must be initialized with a string or integer literal, or a `nameof` expression",
                    subject
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                reason_pos,
                "Class pointers, constant forwarding, and computed expressions are not allowed"
                    .into(),
            )]
        });
        create(
            Typing::ShapeKeyClassConstValueUnresolvable,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shape_key_class_const_nameof_self_in_trait(
        pos: Pos,
        value_pos: Pos,
        class_name: String,
        const_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Class constant {} marked with `<<__ShapeKey>>` cannot be initialized with `nameof self` in a trait",
                    md_codify(&format!("{}::{}", class_name, const_name))
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                value_pos,
                "`nameof self` resolves to the using class; use a literal or an explicit class name with `nameof`"
                    .into(),
            )]
        });
        create(
            Typing::ShapeKeyClassConstValueUnresolvable,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shape_key_class_const_is_abstract(
        pos: Pos,
        decl_pos: Pos,
        class_name: String,
        const_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Abstract class constant {} cannot be used as a shape key",
                    md_codify(&format!("{}::{}", class_name, const_name))
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                decl_pos,
                "The constant must be concrete to use `<<__ShapeKey>>`, even if it has a default value"
                    .into(),
            )]
        });
        create(
            Typing::ShapeKeyClassConstIsAbstract,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shape_field_class_mismatch(
        pos: Pos,
        class_name: String,
        witness_pos: Pos,
        witness_class_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Shape field name is class constant from {}",
                    md_codify(&class_name)
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                witness_pos,
                format!(
                    "But expected constant from {}",
                    md_codify(&witness_class_name)
                )
                .into(),
            )]
        });
        create(Typing::ShapeFieldClassMismatch, claim, Some(reasons), None)
    }

    pub fn shape_field_type_mismatch(
        pos: Pos,
        ty_name: Lazy<String>,
        witness_pos: Pos,
        witness_ty_name: Lazy<String>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!("Shape field name is {} class constant", ty_name.force()).into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                witness_pos,
                format!("But expected {}", witness_ty_name.force()).into(),
            )]
        });
        create(Typing::ShapeFieldTypeMismatch, claim, Some(reasons), None)
    }

    pub fn invalid_shape_remove_key(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "You can only unset fields of **local** variables".into(),
            )
        });
        create(Typing::InvalidShapeRemoveKey, claim, None, None)
    }

    pub fn shapes_key_exists_always_true(pos: Pos, field_name: String, decl_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This `Shapes::keyExists()` check is always true".into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                format!(
                    "The field {} exists because of this definition",
                    md_codify(&field_name)
                )
                .into(),
            )]
        });
        create(
            Typing::ShapesKeyExistsAlwaysTrue,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shape_field_non_existence_reason(
        pos: PosOrDecl,
        name: String,
        reason: shape::NothingOrUndefined,
    ) -> Lazy<Vec<Message<PosOrDecl>>> {
        match reason {
            shape::NothingOrUndefined::Undefined => Lazy::new(move || {
                vec![Message(
                    pos,
                    format!("The field {} is not defined in this shape", md_codify(&name)).into(),
                )]
            }),
            shape::NothingOrUndefined::Nothing(reason) => reason.map(move |reason| {
                let mut reasons = vec![Message(
                    pos,
                    format!(
                        "The type of the field {} in this shape doesn't allow any values",
                        md_codify(&name)
                    )
                    .into(),
                )];
                reasons.extend(reason.iter().cloned());
                reasons
            }),
        }
    }

    pub fn shapes_key_exists_always_false(
        pos: Pos,
        field_name: String,
        decl_pos: PosOrDecl,
        reason: shape::NothingOrUndefined,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This `Shapes::keyExists()` check is always false".into(),
            )
        });
        let reasons = shape_field_non_existence_reason(decl_pos, field_name, reason);
        create(
            Typing::ShapesKeyExistsAlwaysFalse,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shapes_method_access_with_non_existent_field(
        pos: Pos,
        field_name: String,
        method_name: String,
        decl_pos: PosOrDecl,
        reason: shape::NothingOrUndefined,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "You are calling {} on a field known to not exist",
                    md_codify(&format!("Shapes::{}()", method_name))
                )
                .into(),
            )
        });
        let reasons = shape_field_non_existence_reason(decl_pos, field_name, reason);
        create(
            Typing::ShapesMethodAccessWithNonExistentField,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn shapes_access_with_non_existent_field(
        pos: Pos,
        field_name: String,
        decl_pos: PosOrDecl,
        reason: shape::NothingOrUndefined,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(pos, "You are accessing a field known to not exist".into())
        });
        let reasons = shape_field_non_existence_reason(decl_pos, field_name, reason);
        create(
            Typing::ShapeAccessWithNonExistentField,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn to_error<E: ?Sized>(t: shape::T, _env: &E) -> T {
        match t {
            shape::T::Invalid_shape_field_type {
                pos,
                ty_pos,
                ty_name,
                trail,
            } => invalid_shape_field_type(pos, ty_pos, ty_name, trail),
            shape::T::Invalid_shape_field_name {
                pos,
                is_empty: false,
            } => invalid_shape_field_name(pos),
            shape::T::Invalid_shape_field_name {
                pos,
                is_empty: true,
            } => invalid_shape_field_name_empty(pos),
            shape::T::Invalid_shape_field_literal { pos, witness_pos } => {
                invalid_shape_field_literal(pos, witness_pos)
            }
            shape::T::Invalid_shape_field_const { pos, witness_pos } => {
                invalid_shape_field_const(pos, witness_pos)
            }
            shape::T::Abstract_shape_field_const {
                pos,
                decl_pos,
                name,
            } => abstract_shape_field_const(pos, decl_pos, name),
            shape::T::Shape_field_class_const_missing_shape_key_attribute {
                pos,
                decl_pos,
                class_name,
                const_name,
            } => shape_field_class_const_missing_shape_key_attribute(
                pos, decl_pos, class_name, const_name,
            ),
            shape::T::Shape_key_const_value_unresolvable {
                pos,
                reason_pos,
                class_name,
                const_name,
                const_kind,
            } => shape_key_const_value_unresolvable(
                pos, reason_pos, class_name, const_name, const_kind,
            ),
            shape::T::Shape_key_class_const_nameof_self_in_trait {
                pos,
                value_pos,
                class_name,
                const_name,
            } => shape_key_class_const_nameof_self_in_trait(pos, value_pos, class_name, const_name),
            shape::T::Shape_key_class_const_is_abstract {
                pos,
                decl_pos,
                class_name,
                const_name,
            } => shape_key_class_const_is_abstract(pos, decl_pos, class_name, const_name),
            shape::T::Shape_field_class_mismatch {
                pos,
                class_name,
                witness_pos,
                witness_class_name,
            } => shape_field_class_mismatch(pos, class_name, witness_pos, witness_class_name),
            shape::T::Shape_field_type_mismatch {
                pos,
                ty_name,
                witness_pos,
                witness_ty_name,
            } => shape_field_type_mismatch(pos, ty_name, witness_pos, witness_ty_name),
            shape::T::Invalid_shape_remove_key(pos) => invalid_shape_remove_key(pos),
            shape::T::Shapes_key_exists_always_true {
                pos,
                field_name,
                decl_pos,
            } => shapes_key_exists_always_true(pos, field_name, decl_pos),
            shape::T::Shapes_key_exists_always_false {
                pos,
                field_name,
                decl_pos,
                reason,
            } => shapes_key_exists_always_false(pos, field_name, decl_pos, reason),
            shape::T::Shapes_method_access_with_non_existent_field {
                pos,
                field_name,
                method_name,
                decl_pos,
                reason,
            } => shapes_method_access_with_non_existent_field(
                pos,
                field_name,
                method_name,
                decl_pos,
                reason,
            ),
            shape::T::Shapes_access_with_non_existent_field {
                pos,
                field_name,
                decl_pos,
                reason,
            } => shapes_access_with_non_existent_field(pos, field_name, decl_pos, reason),
        }
    }
}

pub mod eval_destructure {
    use super::*;
    use crate::typing_error::primary::shape_and_tuple_destructure;

    pub fn missing_ellipsis(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Missing `...`: the shape type has unknown fields, so the destructuring pattern must end with `...`"
                    .into(),
            )
        });
        create(Typing::DestructureMissingEllipsis, claim, None, None)
    }

    pub fn missing_required_fields(pos: Pos, field_names: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Missing required fields in destructuring pattern: {}",
                    field_names
                )
                .into(),
            )
        });
        create(Typing::DestructureMissingRequiredField, claim, None, None)
    }

    pub fn unknown_field(pos: Pos, field_name: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Field {} does not exist in the shape type",
                    md_codify(&field_name)
                )
                .into(),
            )
        });
        create(Typing::DestructureUnknownField, claim, None, None)
    }

    pub fn plural_s(n: isize) -> &'static str {
        if n == 1 { "" } else { "s" }
    }

    pub fn tuple_arity_mismatch(pos: Pos, pat_arity: isize, tuple_arity: isize) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Tuple arity mismatch: expected {} element{} in destructuring pattern but the tuple type has {}",
                    pat_arity,
                    plural_s(pat_arity),
                    tuple_arity
                )
                .into(),
            )
        });
        create(Typing::DestructureTupleArityMismatch, claim, None, None)
    }

    pub fn tuple_arity_exceeds(pos: Pos, pat_arity: isize, tuple_arity: isize) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Too many entries in tuple destructuring pattern: pattern has {} but the tuple type only has {} element{}",
                    pat_arity,
                    tuple_arity,
                    plural_s(tuple_arity)
                )
                .into(),
            )
        });
        create(Typing::DestructureTupleArityMismatch, claim, None, None)
    }

    pub fn tuple_arity_union_conflict(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Tuple arity mismatch: union members have different arities".into(),
            )
        });
        create(Typing::DestructureTupleArityMismatch, claim, None, None)
    }

    pub fn to_error<E: ?Sized>(t: shape_and_tuple_destructure::T, _env: &E) -> T {
        use shape_and_tuple_destructure::T::*;
        match t {
            Missing_ellipsis(pos) => missing_ellipsis(pos),
            Missing_required_fields { pos, field_names } => {
                missing_required_fields(pos, field_names)
            }
            Unknown_field { pos, field_name } => unknown_field(pos, field_name),
            Tuple_arity_mismatch {
                pos,
                pat_arity,
                tuple_arity,
            } => tuple_arity_mismatch(pos, pat_arity, tuple_arity),
            Tuple_arity_exceeds {
                pos,
                pat_arity,
                tuple_arity,
            } => tuple_arity_exceeds(pos, pat_arity, tuple_arity),
            Tuple_arity_union_conflict(pos) => tuple_arity_union_conflict(pos),
        }
    }
}

pub mod eval_switch {
    use super::*;
    use crate::typing_error::primary::switch;

    pub fn switch_nonexhaustive(
        switch_pos: Pos,
        scrutinee_pos: Pos,
        scrutinee_type: Lazy<String>,
        missing: Lazy<Vec<String>>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                switch_pos,
                format!(
                    "This `switch` statement is nonexhaustive. At least the following cases are missing: {}",
                    missing
                        .force()
                        .iter()
                        .map(|x| md_codify(x))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                scrutinee_pos,
                format!(
                    "The scrutinee has type {}.",
                    md_codify(scrutinee_type.force())
                )
                .into(),
            )]
        });
        create(Typing::EnumSwitchNonexhaustive, claim, Some(reasons), None)
    }

    pub fn switch_needs_default(
        switch_pos: Pos,
        scrutinee_pos: Pos,
        scrutinee_type: Lazy<String>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                switch_pos,
                "This `switch` case cannot be checked for exhaustivity. Please provide a default. Without a default, when none of the cases match, a runtime exception will be thrown."
                    .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                scrutinee_pos,
                format!(
                    "The scrutinee has type {} which is not an enum, enum class, enum class label, null, or nullable or tuples of those types.",
                    md_codify(scrutinee_type.force())
                )
                .into(),
            )]
        });
        create(Typing::SwitchNeedsDefault, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: switch::T, _env: &E) -> T {
        match t {
            switch::T::Switch_nonexhaustive {
                switch_pos,
                scrutinee_pos,
                scrutinee_type,
                missing,
            } => switch_nonexhaustive(switch_pos, scrutinee_pos, scrutinee_type, missing),
            switch::T::Switch_needs_default {
                switch_pos,
                scrutinee_pos,
                scrutinee_type,
            } => switch_needs_default(switch_pos, scrutinee_pos, scrutinee_type),
        }
    }
}

pub mod eval_enum {
    use super::*;
    use crate::typing_error::primary::enum_;
    use crate::typing_error::primary::enum_::const_;

    pub fn enum_class_label_member_mismatch(
        pos: Pos,
        label: String,
        expected_ty_msg_opt: Option<Lazy<Vec<Message<PosOrDecl>>>>,
    ) -> T {
        let claim = {
            let pos = pos.clone();
            Lazy::new(move || Message(pos, "Enum class label/member mismatch".into()))
        };
        let reasons = match expected_ty_msg_opt {
            Some(expected_ty_msg) => expected_ty_msg.map(move |expected_ty_msg| {
                let mut reasons = expected_ty_msg.clone();
                reasons.push(Message(
                    // Pos_or_decl.of_raw_pos
                    pos,
                    format!("But got an enum class label/member: `{}`", label).into(),
                ));
                reasons
            }),
            None => Lazy::new(move || {
                vec![Message(
                    // Pos_or_decl.of_raw_pos
                    pos,
                    format!("Unexpected enum class label/member: `{}`", label).into(),
                )]
            }),
        };
        create(Typing::UnifyError, claim, Some(reasons), None)
    }

    pub fn enum_type_bad(
        pos: Pos,
        is_enum_class: bool,
        ty_name: Lazy<String>,
        trail: Vec<PosOrDecl>,
    ) -> T {
        let claim = ty_name.map(move |ty_name| {
            let ty = md_codify(ty_name);
            let msg = if is_enum_class {
                "Invalid base type for an enum class: "
            } else {
                "Enums must be `int` or `string` or `arraykey`, not "
            };
            Message(pos, format!("{}{}", msg, ty).into())
        });
        let reasons = Lazy::new(move || common::reasons_of_trail(&trail));
        create(Typing::EnumTypeBad, claim, Some(reasons), None)
    }

    pub fn enum_type_bad_case_type(
        pos: Pos,
        ty_name: Lazy<String>,
        case_type_decl_pos: PosOrDecl,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Cannot use a case type as the base type for an enum/enum class".into(),
            )
        });
        let reasons = ty_name.map(move |ty_name| {
            let ty = md_codify(ty_name);
            vec![Message(
                case_type_decl_pos,
                format!("{} is declared as a case type here", ty).into(),
            )]
        });
        create(Typing::EnumTypeBad, claim, Some(reasons), None)
    }

    pub fn enum_constant_type_bad(
        pos: Pos,
        ty_pos: PosOrDecl,
        ty_name: Lazy<String>,
        trail: Vec<PosOrDecl>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(pos, "Enum constants must be an `int` or `string`".into())
        });
        let reasons = ty_name.map(move |ty_name| {
            let mut reasons = vec![Message(
                ty_pos,
                format!("Not {}", md_codify(ty_name)).into(),
            )];
            reasons.extend(common::reasons_of_trail(&trail));
            reasons
        });
        create(Typing::EnumConstantTypeBad, claim, Some(reasons), None)
    }

    pub fn enum_type_typedef_nonnull(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Can't use `typedef` that resolves to nonnull in enum".into(),
            )
        });
        create(Typing::EnumTypeTypedefNonnull, claim, None, None)
    }

    pub fn enum_switch_redundant(pos: Pos, first_pos: Pos, const_name: const_::T) -> T {
        let const_name = const_::to_user_string(&const_name);
        let claim = Lazy::new(move || Message(pos, "Redundant `case` statement".into()));
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                first_pos,
                format!("{} already handled here", md_codify(&const_name)).into(),
            )]
        });
        create(Typing::EnumSwitchRedundant, claim, Some(reasons), None)
    }

    pub fn enum_switch_nonexhaustive(
        pos: Pos,
        kind: Option<String>,
        decl_pos: PosOrDecl,
        missing: Vec<Option<const_::T>>,
    ) -> T {
        // The claim and the reasons both look at `missing`.
        let missing = std::rc::Rc::new(missing);
        let claim = {
            let missing = missing.clone();
            Lazy::new(move || {
                Message(
                    pos,
                    format!(
                        "`switch` statement nonexhaustive; at least the following cases are missing: {}",
                        missing
                            .iter()
                            .map(|x| md_codify(&const_::opt_to_user_string(x)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                    .into(),
                )
            })
        };
        let reasons = Lazy::new(move || match kind {
            Some(kind) => vec![Message(decl_pos, format!("{} declared here", kind).into())],
            None => {
                if missing.iter().any(|x| x.is_none()) {
                    vec![Message(
                        decl_pos,
                        "only unions and intersections of bool, null and enums can be switched on without a default"
                            .into(),
                    )]
                } else {
                    vec![]
                }
            }
        });
        create(Typing::EnumSwitchNonexhaustive, claim, Some(reasons), None)
    }

    pub fn enum_switch_redundant_default(pos: Pos, kind: String, decl_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "All cases already covered; a redundant `default` case prevents detecting future errors. If your goal is to guard against invalid values for this type, do an `is` check before the switch."
                    .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(decl_pos, format!("{} declared here", kind).into())]
        });
        create(
            Typing::EnumSwitchRedundantDefault,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn enum_switch_not_const(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Case in `switch` must be either an enum constant or a literal expression.".into(),
            )
        });
        create(Typing::EnumSwitchNotConst, claim, None, None)
    }

    pub fn enum_switch_wrong_class(
        pos: Pos,
        kind: String,
        expected: Lazy<String>,
        actual: Lazy<String>,
        exp_pos: Option<PosOrDecl>,
    ) -> T {
        let expected = expected.map(|expected| md_codify(expected));
        let claim = expected.clone().bind(move |expected| {
            let expected = expected.clone();
            actual.map(move |actual| {
                Message(
                    pos,
                    format!(
                        "Switching on {}{} but using constant from {}",
                        kind,
                        expected,
                        md_codify(actual)
                    )
                    .into(),
                )
            })
        });
        let reasons = expected.map(move |expected| match exp_pos {
            None => vec![],
            Some(exp_pos) => vec![Message(
                exp_pos,
                format!("expecting {} based on this", expected).into(),
            )],
        });
        create(Typing::EnumSwitchWrongClass, claim, Some(reasons), None)
    }

    pub fn enum_switch_inconsistent_int_literal_format(
        expected: String,
        exp_pos: Pos,
        actual: String,
        pos: Pos,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "This int literal is in {}, but was expecting it to be in {}",
                    md_codify(&actual),
                    md_codify(&expected)
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                // Pos_or_decl.of_raw_pos
                exp_pos,
                "All int literals in this switch must be written in the same base as the first one"
                    .into(),
            )]
        });
        create(Typing::EnumSwitchWrongClass, claim, Some(reasons), None)
    }

    pub fn enum_class_label_as_expr(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Not enough type information to infer the type of this enum class label.".into(),
            )
        });
        create(Typing::EnumClassLabelAsExpression, claim, None, None)
    }

    pub fn incompatible_enum_inclusion_base(
        pos: Pos,
        classish_name: String,
        src_classish_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Enum {} includes enum {} but their base types are incompatible",
                    render::strip_ns(&classish_name),
                    render::strip_ns(&src_classish_name)
                )
                .into(),
            )
        });
        create(Typing::IncompatibleEnumInclusion, claim, None, None)
    }

    pub fn incompatible_enum_inclusion_constraint(
        pos: Pos,
        classish_name: String,
        src_classish_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Enum {} includes enum {} but their constraints are incompatible",
                    render::strip_ns(&classish_name),
                    render::strip_ns(&src_classish_name)
                )
                .into(),
            )
        });
        create(Typing::IncompatibleEnumInclusion, claim, None, None)
    }

    pub fn enum_inclusion_not_enum(
        pos: Pos,
        classish_name: String,
        src_classish_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "Enum {} includes {} which is not an enum",
                    render::strip_ns(&classish_name),
                    render::strip_ns(&src_classish_name)
                )
                .into(),
            )
        });
        create(Typing::IncompatibleEnumInclusion, claim, None, None)
    }

    pub fn to_error<E: ?Sized>(t: enum_::T, _env: &E) -> T {
        use enum_::T::*;
        match t {
            Enum_type_bad {
                pos,
                is_enum_class,
                ty_name,
                trail,
            } => enum_type_bad(pos, is_enum_class, ty_name, trail),
            Enum_type_bad_case_type {
                pos,
                ty_name,
                case_type_decl_pos,
            } => enum_type_bad_case_type(pos, ty_name, case_type_decl_pos),
            Enum_constant_type_bad {
                pos,
                ty_pos,
                ty_name,
                trail,
            } => enum_constant_type_bad(pos, ty_pos, ty_name, trail),
            Enum_type_typedef_nonnull(pos) => enum_type_typedef_nonnull(pos),
            Enum_switch_redundant {
                pos,
                first_pos,
                const_name,
            } => enum_switch_redundant(pos, first_pos, const_name),
            Enum_switch_nonexhaustive {
                pos,
                kind,
                decl_pos,
                missing,
            } => enum_switch_nonexhaustive(pos, kind, decl_pos, missing),
            Enum_switch_redundant_default {
                pos,
                kind,
                decl_pos,
            } => enum_switch_redundant_default(pos, kind, decl_pos),
            Enum_switch_not_const(pos) => enum_switch_not_const(pos),
            Enum_switch_wrong_class {
                pos,
                kind,
                expected,
                actual,
                expected_pos,
            } => enum_switch_wrong_class(pos, kind, expected, actual, expected_pos),
            Enum_switch_inconsistent_int_literal_format {
                expected,
                actual,
                expected_pos,
                pos,
            } => enum_switch_inconsistent_int_literal_format(expected, expected_pos, actual, pos),
            Enum_class_label_as_expr(pos) => enum_class_label_as_expr(pos),
            Enum_class_label_member_mismatch {
                pos,
                label,
                expected_ty_msg_opt,
            } => enum_class_label_member_mismatch(pos, label, expected_ty_msg_opt),
            Incompatible_enum_inclusion_base {
                pos,
                classish_name,
                src_classish_name,
            } => incompatible_enum_inclusion_base(pos, classish_name, src_classish_name),
            Incompatible_enum_inclusion_constraint {
                pos,
                classish_name,
                src_classish_name,
            } => incompatible_enum_inclusion_constraint(pos, classish_name, src_classish_name),
            Enum_inclusion_not_enum {
                pos,
                classish_name,
                src_classish_name,
            } => enum_inclusion_not_enum(pos, classish_name, src_classish_name),
        }
    }
}

pub mod eval_expr_tree {
    use super::*;
    use crate::typing_error::primary::expr_tree;

    pub fn expression_tree_non_public_member(pos: Pos, decl_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Cannot access non-public members within expression trees.".into(),
            )
        });
        let reasons = Lazy::new(move || vec![Message(decl_pos, "Member defined here".into())]);
        create(
            Typing::ExpressionTreeNonPublicProperty,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn reified_static_method_in_expr_tree(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Static method calls on reified generics are not permitted in Expression Trees."
                    .into(),
            )
        });
        create(Typing::ReifiedStaticMethodInExprTree, claim, None, None)
    }

    pub fn this_var_in_expr_tree(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(pos, "`$this` is not bound inside expression trees".into())
        });
        create(Typing::ThisVarOutsideClass, claim, None, None)
    }

    pub fn experimental_expression_trees(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This type is not permitted as an expression tree visitor. It is not included in `allowed_expression_tree_visitors` in `.hhconfig`, and this file does not contain `<<file:__EnableUnstableFeatures('expression_trees')>>`."
                    .into(),
            )
        });
        create(Typing::ExperimentalExpressionTrees, claim, None, None)
    }

    pub fn expression_tree_unsupported_operator(
        pos: Pos,
        member_name: String,
        class_name: String,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                match member_name.as_str() {
                    // If the user writes `if ($not_bool)`, provide a more specific
                    // error rather than a generic missing method error for
                    // `$not_bool->__bool()`.
                    "__bool" => format!(
                        "`{}` cannot be used as a boolean (it has no instance method named `__bool`)",
                        class_name
                    ),
                    // If the user writes `$not_int + ...`, provide a more specific
                    // error rather than a generic missing method error for
                    // `$not_int->__plus(...)`.
                    _ => format!(
                        "`{}` does not support this operator (it has no instance method named `{}`)",
                        class_name, member_name
                    ),
                }
                .into(),
            )
        });
        create(Typing::MemberNotFound, claim, None, None)
    }

    pub fn to_error<E: ?Sized>(t: expr_tree::T, _env: &E) -> T {
        use expr_tree::T::*;
        match t {
            Expression_tree_non_public_member { pos, decl_pos } => {
                expression_tree_non_public_member(pos, decl_pos)
            }
            Reified_static_method_in_expr_tree(pos) => reified_static_method_in_expr_tree(pos),
            This_var_in_expr_tree(pos) => this_var_in_expr_tree(pos),
            Experimental_expression_trees(pos) => experimental_expression_trees(pos),
            Expression_tree_unsupported_operator {
                pos,
                member_name,
                class_name,
            } => expression_tree_unsupported_operator(pos, member_name, class_name),
        }
    }
}

pub mod eval_readonly {
    use super::*;
    use crate::typing_error::primary::readonly;

    pub fn readonly_modified(pos: Pos, reason_opt: Option<Lazy<Message<PosOrDecl>>>) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This value is readonly, its properties cannot be modified".into(),
            )
        });
        let reasons = match reason_opt {
            None => Lazy::new(Vec::new),
            Some(reason) => reason.map(|reason| vec![reason.clone()]),
        };
        create(Typing::ReadonlyValueModified, claim, Some(reasons), None)
    }

    pub fn readonly_mismatch(
        pos: Pos,
        what: readonly::ReadonlyMismatchWhat,
        pos_sub: PosOrDecl,
        pos_super: PosOrDecl,
    ) -> T {
        let (msg, msg_sub, msg_super) = match what {
            readonly::ReadonlyMismatchWhat::prop_assign => (
                "property assignment",
                "readonly",
                "But it's being assigned to a mutable property",
            ),
            readonly::ReadonlyMismatchWhat::collection_mod => (
                "collection modification",
                "readonly",
                "But this value is mutable",
            ),
            readonly::ReadonlyMismatchWhat::arg_readonly => (
                "argument",
                "readonly",
                "It is incompatible with this parameter, which is mutable",
            ),
            readonly::ReadonlyMismatchWhat::arg_mut => (
                "argument",
                "mutable",
                "It is incompatible with this parameter, which is readonly",
            ),
        };
        let claim = Lazy::new(move || Message(pos, format!("Invalid {}", msg).into()));
        let reasons = Lazy::new(move || {
            vec![
                Message(pos_sub, format!("This expression is {}", msg_sub).into()),
                Message(pos_super, msg_super.into()),
            ]
        });
        create(Typing::ReadonlyMismatch, claim, Some(reasons), None)
    }

    pub fn readonly_invalid_as_mut(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Only value types and arrays can be converted to mutable. This value can never be a primitive."
                    .into(),
            )
        });
        create(Typing::ReadonlyInvalidAsMut, claim, None, None)
    }

    pub fn readonly_exception(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This exception is readonly; throwing readonly exceptions is not currently supported."
                    .into(),
            )
        });
        create(Typing::ReadonlyException, claim, None, None)
    }

    pub fn explicit_readonly_cast(pos: Pos, decl_pos: PosOrDecl, kind: readonly::ExplicitReadonlyCastKind) -> T {
        let qf_pos = crate::pos::shrink_to_start(&pos);
        let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
            "Insert `readonly`".to_string(),
            "readonly ".to_string(),
            qf_pos,
        )];
        let kind_str = match kind {
            readonly::ExplicitReadonlyCastKind::fn_call => "function call",
            readonly::ExplicitReadonlyCastKind::property => "property",
            readonly::ExplicitReadonlyCastKind::static_property => "static property",
        };
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "This {} returns a readonly value. It must be explicitly wrapped in a readonly expression.",
                    kind_str
                )
                .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                format!("The {} is defined here.", kind_str).into(),
            )]
        });
        create(
            Typing::ExplicitReadonlyCast,
            claim,
            Some(reasons),
            Some(quickfixes),
        )
    }

    pub fn readonly_method_call(pos: Pos, decl_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This expression is readonly, so it can only call readonly methods".into(),
            )
        });
        let reasons =
            Lazy::new(move || vec![Message(decl_pos, "This method is not readonly".into())]);
        create(Typing::ReadonlyMethodCall, claim, Some(reasons), None)
    }

    pub fn readonly_closure_call(pos: Pos, decl_pos: PosOrDecl, suggestion: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This function is readonly, so it must be marked readonly at declaration time to be called."
                    .into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                format!("Did you mean to {}?", suggestion).into(),
            )]
        });
        create(Typing::ReadonlyClosureCall, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: readonly::T, _env: &E) -> T {
        use readonly::T::*;
        match t {
            Readonly_modified { pos, reason_opt } => readonly_modified(pos, reason_opt),
            Readonly_mismatch {
                pos,
                what,
                pos_sub,
                pos_super,
            } => readonly_mismatch(pos, what, pos_sub, pos_super),
            Readonly_invalid_as_mut(pos) => readonly_invalid_as_mut(pos),
            Readonly_exception(pos) => readonly_exception(pos),
            Explicit_readonly_cast {
                pos,
                decl_pos,
                kind,
            } => explicit_readonly_cast(pos, decl_pos, kind),
            Readonly_method_call { pos, decl_pos } => readonly_method_call(pos, decl_pos),
            Readonly_closure_call {
                pos,
                decl_pos,
                suggestion,
            } => readonly_closure_call(pos, decl_pos, suggestion),
        }
    }
}

pub mod eval_coeffect {
    use super::*;
    use crate::typing_error::primary::coeffect;

    pub fn call_coeffect(
        pos: Pos,
        available_pos: PosOrDecl,
        available_incl_unsafe: Lazy<String>,
        required_pos: PosOrDecl,
        required: Lazy<String>,
    ) -> T {
        let reasons = common::map2(
            move |available_incl_unsafe: &String, required: &String| {
                vec![
                    Message(
                        available_pos,
                        format!(
                            "From this declaration, the context of this function body provides {}",
                            available_incl_unsafe
                        )
                        .into(),
                    ),
                    Message(
                        required_pos,
                        format!("But the function being called requires {}", required).into(),
                    ),
                ]
            },
            available_incl_unsafe,
            required,
        );
        let claim = Lazy::new(move || {
            Message(
                pos,
                "This call is not allowed because its capabilities are incompatible with the context"
                    .into(),
            )
        });
        create(Typing::CallCoeffects, claim, Some(reasons), None)
    }

    pub fn op_coeffect_error(
        pos: Pos,
        op_name: String,
        required: Lazy<String>,
        available_pos: PosOrDecl,
        locally_available: Lazy<String>,
        suggestion: Option<Lazy<Vec<Message<PosOrDecl>>>>,
        code: Typing,
    ) -> T {
        let reasons = common::map2(
            move |suggestion: &Vec<Message<PosOrDecl>>, locally_available: &String| {
                let x = Message(
                    available_pos,
                    format!(
                        "The local (enclosing) context provides {}",
                        locally_available
                    )
                    .into(),
                );
                let mut reasons = vec![x];
                reasons.extend(suggestion.iter().cloned());
                reasons
            },
            suggestion.unwrap_or_else(|| Lazy::new(Vec::new)),
            locally_available,
        );
        let claim = required.map(move |required| {
            Message(
                pos,
                format!(
                    "{} requires {}, which is not provided by the context.",
                    op_name, required
                )
                .into(),
            )
        });
        create(code, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: coeffect::T, _env: &E) -> T {
        use coeffect::T::*;
        match t {
            Op_coeffect_error {
                pos,
                op_name,
                required,
                available_pos,
                locally_available,
                suggestion,
                err_code,
            } => op_coeffect_error(
                pos,
                op_name,
                required,
                available_pos,
                locally_available,
                suggestion,
                err_code,
            ),
            Call_coeffect {
                pos,
                available_pos,
                available_incl_unsafe,
                required_pos,
                required,
            } => call_coeffect(
                pos,
                available_pos,
                available_incl_unsafe,
                required_pos,
                required,
            ),
        }
    }
}

pub mod eval_wellformedness {
    use super::*;
    use crate::typing_error::primary::wellformedness;

    pub fn missing_return(pos: Pos, hint_pos: Option<PosOrDecl>, is_async: bool) -> T {
        let return_type = if is_async { "Awaitable<void>" } else { "void" };

        let quickfixes = match hint_pos {
            None => vec![],
            Some(hint_pos) => vec![crate::quickfix::make_eager_default_hint_style(
                format!("Change to {}", md_codify(return_type)),
                "void".to_string(),
                // Pos_or_decl.unsafe_to_raw_pos
                hint_pos,
            )],
        };
        let reasons = Lazy::new(Vec::new);
        let claim = Lazy::new(move || Message(pos, "Invalid return type".into()));
        create(
            Typing::MissingReturnInNonVoidFunction,
            claim,
            Some(reasons),
            Some(quickfixes),
        )
    }

    pub fn void_usage(pos: Pos, reasons: Lazy<Vec<Message<PosOrDecl>>>) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "You are using the return value of a `void` function".into(),
            )
        });
        create(Typing::VoidUsage, claim, Some(reasons), None)
    }

    pub fn noreturn_usage(pos: Pos, reasons: Lazy<Vec<Message<PosOrDecl>>>) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "You are using the return value of a `noreturn` function".into(),
            )
        });
        create(Typing::NoreturnUsage, claim, Some(reasons), None)
    }

    pub fn returns_with_and_without_value(
        pos: Pos,
        with_value_pos: Pos,
        without_value_pos_opt: Option<Pos>,
    ) -> T {
        let claim = {
            let pos = pos.clone();
            Lazy::new(move || {
                Message(
                    pos,
                    "This function can exit with and without returning a value".into(),
                )
            })
        };
        let reasons = Lazy::new(move || {
            vec![
                // Pos_or_decl.of_raw_pos (here and below)
                Message(with_value_pos, "Returning a value here.".into()),
                match without_value_pos_opt {
                    None => Message(pos, "This function does not always return a value".into()),
                    Some(p) => Message(p, "Returning without a value here".into()),
                },
            ]
        });
        create(
            Typing::ReturnsWithAndWithoutValue,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn non_void_annotation_on_return_void_function(is_async: bool, hint_pos: Pos) -> T {
        let (async_indicator, return_type) = if is_async {
            ("Async f", "Awaitable<void>")
        } else {
            ("F", "void")
        };
        let claim = {
            let hint_pos = hint_pos.clone();
            Lazy::new(move || {
                Message(
                    hint_pos,
                    format!(
                        "{}unctions that do not return a value must have a type of {}",
                        async_indicator, return_type
                    )
                    .into(),
                )
            })
        };
        let quickfixes = vec![crate::quickfix::make_eager_default_hint_style(
            format!("Change to {}", md_codify(return_type)),
            return_type.to_string(),
            hint_pos,
        )];

        create(
            Typing::NonVoidAnnotationOnReturnVoidFun,
            claim,
            None,
            Some(quickfixes),
        )
    }

    pub fn tuple_syntax(p: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                p,
                "Did you want a *tuple*? Try `(X,Y)`, not `tuple<X,Y>`".into(),
            )
        });
        create(Typing::TupleSyntax, claim, None, None)
    }

    pub fn invalid_class_refinement(pos: Pos) -> T {
        let claim = Lazy::new(move || Message(pos, "Invalid class refinement".into()));
        create(Typing::InvalidClassRefinement, claim, None, None)
    }

    pub fn redundant_shape_splat(pos: Pos, operand_pos: Pos, is_dynamic: bool) -> T {
        let (suggestion, quickfix) = if is_dynamic {
            (
                "Use `shape(dynamic...)` instead.",
                crate::quickfix::make_eager_default_hint_style(
                    "Replace with `shape(dynamic...)`".to_string(),
                    "shape(dynamic...)".to_string(),
                    pos.clone(),
                ),
            )
        } else {
            // The elements of a list literal are evaluated from the last to
            // the first; neither has an effect.
            let edits = oxidized::quickfix::Edits::Eager(vec![
                (
                    "".to_string(),
                    Pos::btw_nocheck(pos.clone(), crate::pos::shrink_to_start(&operand_pos)),
                ),
                (
                    "".to_string(),
                    Pos::btw_nocheck(crate::pos::shrink_to_end(&operand_pos), pos.clone()),
                ),
            ]);
            (
                "Use the splatted type directly.",
                crate::quickfix::make(
                    "Remove the redundant shape splat".to_string(),
                    edits,
                    vec![],
                ),
            )
        };
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "A shape containing only one splat is redundant. {}",
                    suggestion
                )
                .into(),
            )
        });
        create(
            Typing::RedundantShapeSplat,
            claim,
            None,
            Some(vec![quickfix]),
        )
    }

    pub fn to_error<E: ?Sized>(t: wellformedness::T, _env: &E) -> T {
        use wellformedness::T::*;
        match t {
            Missing_return {
                pos,
                hint_pos,
                is_async,
            } => missing_return(pos, hint_pos, is_async),
            Void_usage { pos, reason } => void_usage(pos, reason),
            Noreturn_usage { pos, reason } => noreturn_usage(pos, reason),
            Returns_with_and_without_value {
                pos,
                with_value_pos,
                without_value_pos_opt,
            } => returns_with_and_without_value(pos, with_value_pos, without_value_pos_opt),
            Non_void_annotation_on_return_void_function { is_async, hint_pos } => {
                non_void_annotation_on_return_void_function(is_async, hint_pos)
            }
            Tuple_syntax(pos) => tuple_syntax(pos),
            Invalid_class_refinement { pos } => invalid_class_refinement(pos),
            Redundant_shape_splat {
                pos,
                operand_pos,
                is_dynamic,
            } => redundant_shape_splat(pos, operand_pos, is_dynamic),
        }
    }
}

pub mod eval_modules {
    use super::*;
    use crate::typing_error::primary::modules;

    pub fn module_hint(pos: Pos, decl_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "You cannot use this type in a public declaration.".into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                "It is declared as `internal` here".into(),
            )]
        });
        create(Typing::ModuleHintError, claim, Some(reasons), None)
    }

    pub fn module_mismatch(
        pos: Pos,
        current_module_opt: Option<String>,
        decl_pos: PosOrDecl,
        target_module: String,
        tests_bypass_visibility_context: bool,
    ) -> T {
        let claim = {
            let target_module = target_module.clone();
            Lazy::new(move || {
                Message(
                    pos,
                    format!(
                        "Cannot access an internal element from module `{}` {}",
                        target_module,
                        match current_module_opt {
                            Some(m) => format!("in module `{}`", m),
                            None => "in the default module".to_string(),
                        }
                    )
                    .into(),
                )
            })
        };
        let reasons = Lazy::new(move || {
            vec![Message(
                decl_pos,
                format!(
                    "This is from module `{}`{}",
                    target_module,
                    if tests_bypass_visibility_context {
                        ". To allow access from test contexts, add `<<__TestsBypassVisibility>>` to this class"
                    } else {
                        ""
                    }
                )
                .into(),
            )]
        });
        create(Typing::ModuleError, claim, Some(reasons), None)
    }

    pub fn module_unsafe_trait_access(access_pos: Pos, trait_pos: PosOrDecl) -> T {
        let claim = Lazy::new(move || {
            Message(
                access_pos,
                "Cannot access `internal` members inside a non-internal trait".into(),
            )
        });
        let reasons = Lazy::new(move || {
            vec![Message(
                trait_pos,
                "This trait must be made `internal` to access other internal members".into(),
            )]
        });

        create(Typing::ModuleError, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: modules::T, _env: &E) -> T {
        use modules::T::*;
        match t {
            Module_hint { pos, decl_pos } => module_hint(pos, decl_pos),
            Module_mismatch {
                pos,
                current_module_opt,
                decl_pos,
                target_module,
                tests_bypass_visibility_context,
            } => module_mismatch(
                pos,
                current_module_opt,
                decl_pos,
                target_module,
                tests_bypass_visibility_context,
            ),
            Module_unsafe_trait_access {
                access_pos,
                trait_pos,
            } => module_unsafe_trait_access(access_pos, trait_pos),
        }
    }
}

pub mod eval_shape_splat {
    use super::*;
    use crate::typing_error::primary::shape_splat;
    use crate::typing_env_types::Env;

    fn field_reasons(label: &str, positions: Vec<PosOrDecl>) -> Vec<Message<PosOrDecl>> {
        positions
            .into_iter()
            .enumerate()
            .map(|(index, pos)| {
                Message(
                    pos,
                    format!(
                        "Shape field `{}` is {} here",
                        label,
                        if index == 0 { "defined" } else { "also defined" }
                    )
                    .into(),
                )
            })
            .collect()
    }

    fn source_reason(label: &str, source: shape_splat::OverlapSource) -> Message<PosOrDecl> {
        let shape_splat::OverlapSource { pos, origin } = source;
        let message = match origin {
            shape_splat::OverlapSourceOrigin::Shape_field(_) => {
                format!("Shape field `{}` may also be defined here", label)
            }
            shape_splat::OverlapSourceOrigin::Description(description) => {
                format!("Shape field `{}` may also be provided by {}", label, description)
            }
        };
        Message(pos, message.into())
    }

    fn violation_reasons(violation: shape_splat::DisjointnessViolation) -> Vec<Message<PosOrDecl>> {
        use shape_splat::DisjointnessViolation::*;
        match violation {
            Overlapping_field { label, positions } => field_reasons(&label, positions),
            Possible_overlapping_field {
                label,
                positions,
                sources,
            } => {
                let mut reasons = field_reasons(&label, positions);
                reasons.extend(sources.into_iter().map(|source| source_reason(&label, source)));
                reasons
            }
            Unresolved_sources { sources } => sources
                .into_iter()
                .map(|source| {
                    let message = match &source.origin {
                        shape_splat::OverlapSourceOrigin::Shape_field(label) => {
                            format!("Shape field `{}` may be present here", label)
                        }
                        shape_splat::OverlapSourceOrigin::Description(description) => {
                            format!("{} may provide shape fields here", description)
                        }
                    };
                    Message(source.pos, message.into())
                })
                .collect(),
        }
    }

    pub fn disjoint_shape_splat_violation(
        pos: Pos,
        violations: Vec<shape_splat::DisjointnessViolation>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Type alias marked `<<__DisjointShapeSplat>>` may contain overlapping shapes"
                    .into(),
            )
        });
        let reasons = Lazy::new(move || {
            violations
                .iter()
                .cloned()
                .flat_map(violation_reasons)
                .collect()
        });
        create(Typing::InvalidTypeHint, claim, Some(reasons), None)
    }

    pub fn non_denotable_shape_splat_fields(
        env: &Env,
        pos: Pos,
        fields: Vec<shape_splat::NonDenotableField>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Shape splat produces fields with non-denotable types".into(),
            )
        });
        let env = env.clone();
        let reasons = Lazy::new(move || {
            fields
                .iter()
                .map(|shape_splat::NonDenotableField { label, pos, ty }| {
                    let ty = md_codify(&crate::typing_print::full_strip_ns(true, &env, ty));
                    Message(
                        pos.clone(),
                        format!("Shape field `{}` has non-denotable type {}", label, ty).into(),
                    )
                })
                .collect()
        });
        create(Typing::InvalidTypeHint, claim, Some(reasons), None)
    }

    pub fn to_error(t: shape_splat::T, env: &Env) -> T {
        match t {
            shape_splat::T::Disjoint_shape_splat_violation { pos, violations } => {
                disjoint_shape_splat_violation(pos, violations)
            }
            shape_splat::T::Non_denotable_shape_splat_fields { pos, fields } => {
                non_denotable_shape_splat_fields(env, pos, fields)
            }
        }
    }
}

pub mod eval_package {
    use oxidized::package::PosId;
    use relative_path::RelativePath;

    use super::*;
    use crate::typing_error::primary::package;
    use crate::typing_error::primary::package::TargetSymbolSpec;
    use crate::typing_error::primary::package::target_symbol_spec_to_string;

    pub fn get_package_pos_id(p_opt: Option<PosId>) -> (String, Pos) {
        match p_opt {
            Some(PosId(pos, id)) => (format!("package `{}`", id), pos),
            None => ("the default package".to_string(), Pos::NONE),
        }
    }

    pub fn cross_pkg_access(
        pos: Pos,
        decl_pos: PosOrDecl,
        current_package: Option<PosId>,
        current_package_assignment_kind: String,
        target_package: Option<PosId>,
        target_package_assignment_kind: String,
        target_filename: RelativePath,
        target_id: String,
        target_symbol_spec: TargetSymbolSpec,
        loaded_packages: Vec<PosId>,
        included_packages: Vec<(String, String, Pos)>,
        soft: bool,
    ) -> T {
        let (current_pkg_name, current_pkg_pos) = get_package_pos_id(current_package);
        let (target_package_name, target_package_pos) = get_package_pos_id(target_package);
        // Relative_path.suffix
        let target_filename = target_filename.path_str().to_string();
        let target_id = md_codify(render::utils_strip_ns(&target_id));

        let target_symbol_spec_str = target_symbol_spec_to_string(&target_symbol_spec);
        let claim = {
            let target_id = target_id.clone();
            let target_package_name = target_package_name.clone();
            // The claim and the reasons both look at `target_symbol_spec`;
            // this is the `match` of the claim.
            let is_type_const = match &target_symbol_spec {
                TargetSymbolSpec::Type_const | TargetSymbolSpec::Reifiable_type_const { .. } => {
                    true
                }
                _ => false,
            };
            Lazy::new(move || {
                Message(
                    pos,
                    if is_type_const {
                        format!(
                            "Cannot access {} defined in {}, which may not be available, within a {}",
                            target_id, target_package_name, target_symbol_spec_str
                        )
                    } else {
                        format!(
                            "Cannot access {} {} defined in {} which may not be available",
                            target_symbol_spec_str, target_id, target_package_name
                        )
                    }
                    .into(),
                )
            })
        };
        let reasons = Lazy::new(move || {
            let base_reasons = vec![
                Message(
                    decl_pos,
                    format!("{} is defined in {}", target_id, target_filename).into(),
                ),
                Message(
                    // Pos_or_decl.of_raw_pos
                    target_package_pos,
                    format!(
                        "{} belongs to {} by this {}",
                        target_id, target_package_name, target_package_assignment_kind
                    )
                    .into(),
                ),
                Message(
                    // Pos_or_decl.of_raw_pos
                    current_pkg_pos,
                    format!(
                        "{} is available because the current file belongs to it by this {}",
                        current_pkg_name, current_package_assignment_kind
                    )
                    .into(),
                ),
            ];
            let loaded_reasons = loaded_packages.into_iter().map(|PosId(pkg_pos, pkg)| {
                Message(
                    // Pos_or_decl.of_raw_pos
                    pkg_pos,
                    format!("package `{}` is assumed to be deployed here", pkg).into(),
                )
            });
            let included_reasons =
                included_packages
                    .into_iter()
                    .map(|(including_pkg, included_pkg, include_pos)| {
                        Message(
                            // Pos_or_decl.of_raw_pos
                            include_pos,
                            format!(
                                "`{}` includes `{}` via its definition",
                                including_pkg, included_pkg
                            )
                            .into(),
                        )
                    });
            let reifiable_reasons = match target_symbol_spec {
                TargetSymbolSpec::Reifiable_type_const {
                    reifiable_attr_pos,
                    tconst_name,
                } => vec![Message(
                    reifiable_attr_pos,
                    format!(
                        "The type constant {} is declared `<<__Reifiable>>` here",
                        md_codify(&tconst_name)
                    )
                    .into(),
                )],
                _ => vec![],
            };
            base_reasons
                .into_iter()
                .chain(loaded_reasons)
                .chain(included_reasons)
                .chain(reifiable_reasons)
                .collect()
        });
        let code = if soft {
            Typing::InvalidCrossPackageSoft
        } else {
            Typing::InvalidCrossPackage
        };
        create(code, claim, Some(reasons), None)
    }

    pub fn excluded_path_access(
        pos: Pos,
        decl_pos: PosOrDecl,
        package: Option<PosId>,
        target_filename: RelativePath,
        target_id: String,
        target_symbol_spec: TargetSymbolSpec,
    ) -> T {
        let (package_name, package_pos) = get_package_pos_id(package);
        // Relative_path.suffix
        let target_filename = target_filename.path_str().to_string();
        let target_id = md_codify(render::utils_strip_ns(&target_id));
        let target_symbol_spec_str = target_symbol_spec_to_string(&target_symbol_spec);
        let claim = {
            let target_id = target_id.clone();
            let package_name = package_name.clone();
            Lazy::new(move || {
                Message(
                    pos,
                    format!(
                        "Cannot access {} {}: it is defined on an excluded path of the strict-isolation {}, and code outside the excluded path may not reference it",
                        target_symbol_spec_str, target_id, package_name
                    )
                    .into(),
                )
            })
        };
        let reasons = Lazy::new(move || {
            vec![
                Message(
                    decl_pos,
                    format!(
                        "{} is defined here, in {} -- an excluded path (e.g. matching `package_exclude_patterns`)",
                        target_id, target_filename
                    )
                    .into(),
                ),
                Message(
                    // Pos_or_decl.of_raw_pos
                    package_pos,
                    format!(
                        "{} is a strict-isolation package (declared here); code on an excluded path is deployment-only and may not be referenced from outside that path",
                        package_name
                    )
                    .into(),
                ),
            ]
        });
        create(
            Typing::StrictIsolationExcludedPathAccess,
            claim,
            Some(reasons),
            None,
        )
    }

    pub fn cross_pkg_access_with_requirepackage(
        pos: Pos,
        decl_pos: PosOrDecl,
        target_package: String,
        current_package: Option<PosId>,
        loaded_packages: Vec<PosId>,
        included_packages: Vec<(String, String, Pos)>,
    ) -> T {
        let (current_pkg_name, current_pkg_pos) = get_package_pos_id(current_package);
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Cannot reference this __RequirePackage function".into(),
            )
        });
        let reasons = Lazy::new(move || {
            let base_reasons = vec![
                Message(
                    decl_pos,
                    format!(
                        "This function is marked with `__RequirePackage(\"{}\")`",
                        target_package
                    )
                    .into(),
                ),
                Message(
                    // Pos_or_decl.of_raw_pos
                    current_pkg_pos,
                    format!("the current file belongs to {}", current_pkg_name).into(),
                ),
            ];
            let loaded_reasons = loaded_packages.into_iter().map(|PosId(pkg_pos, pkg)| {
                Message(
                    // Pos_or_decl.of_raw_pos
                    pkg_pos,
                    format!("package `{}` is assumed to be deployed here", pkg).into(),
                )
            });
            let included_reasons =
                included_packages
                    .into_iter()
                    .map(|(including_pkg, included_pkg, include_pos)| {
                        Message(
                            // Pos_or_decl.of_raw_pos
                            include_pos,
                            format!(
                                "`{}` includes `{}` via its definition",
                                including_pkg, included_pkg
                            )
                            .into(),
                        )
                    });
            base_reasons
                .into_iter()
                .chain(loaded_reasons)
                .chain(included_reasons)
                .collect()
        });
        create(Typing::InvalidCrossPackage, claim, Some(reasons), None)
    }

    pub fn cross_pkg_access_with_softrequirepackage(
        pos: Pos,
        decl_pos: PosOrDecl,
        current_soft_package_opt: Option<(Pos, String)>,
        target_package: String,
        loaded_packages: Vec<PosId>,
        included_packages: Vec<(String, String, Pos)>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Cannot reference this `__SoftRequirePackage` function".into(),
            )
        });
        let reasons = Lazy::new(move || {
            let mut base_reasons = vec![Message(
                decl_pos,
                format!(
                    "This function is marked with `__SoftRequirePackage(\"{}\")`, which is a transition feature to help move a function to `__RequirePackage(\"{}\")`. It does not allow calling into {} itself, but it can only be called from functions that have access to {}.",
                    target_package, target_package, target_package, target_package
                )
                .into(),
            )];
            match current_soft_package_opt {
                Some((pos, package)) => base_reasons.push(Message(
                    // Pos_or_decl.of_raw_pos
                    pos,
                    format!(
                        "The current function soft-requires package {}, which does not include {}",
                        package, target_package
                    )
                    .into(),
                )),
                None => {}
            }
            let loaded_reasons = loaded_packages.into_iter().map(|PosId(pkg_pos, pkg)| {
                Message(
                    // Pos_or_decl.of_raw_pos
                    pkg_pos,
                    format!("package `{}` is assumed to be deployed here", pkg).into(),
                )
            });
            let included_reasons =
                included_packages
                    .into_iter()
                    .map(|(including_pkg, included_pkg, include_pos)| {
                        Message(
                            // Pos_or_decl.of_raw_pos
                            include_pos,
                            format!(
                                "`{}` includes `{}` via its definition",
                                including_pkg, included_pkg
                            )
                            .into(),
                        )
                    });
            base_reasons
                .into_iter()
                .chain(loaded_reasons)
                .chain(included_reasons)
                .collect()
        });

        create(Typing::InvalidCrossPackage, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: package::T, _env: &E) -> T {
        use package::T::*;
        match t {
            Cross_pkg_access {
                pos,
                decl_pos,
                current_package,
                current_package_assignment_kind,
                target_package,
                target_package_assignment_kind,
                current_filename: _,
                target_filename,
                target_id,
                target_symbol_spec,
                loaded_packages,
                included_packages,
            } => cross_pkg_access(
                pos,
                decl_pos,
                current_package,
                current_package_assignment_kind,
                target_package,
                target_package_assignment_kind,
                target_filename,
                target_id,
                target_symbol_spec,
                loaded_packages,
                included_packages,
                false, // Soft
            ),
            Cross_pkg_access_with_requirepackage {
                pos,
                decl_pos,
                target_package,
                current_package,
                loaded_packages,
                included_packages,
            } => cross_pkg_access_with_requirepackage(
                pos,
                decl_pos,
                target_package,
                current_package,
                loaded_packages,
                included_packages,
            ),
            Cross_pkg_access_with_softrequirepackage {
                pos,
                decl_pos,
                current_soft_package_opt,
                target_package,
                loaded_packages,
                included_packages,
            } => cross_pkg_access_with_softrequirepackage(
                pos,
                decl_pos,
                current_soft_package_opt,
                target_package,
                loaded_packages,
                included_packages,
            ),
            Soft_included_access {
                pos,
                decl_pos,
                current_package,
                current_package_assignment_kind,
                target_package,
                target_package_assignment_kind,
                current_filename: _,
                target_filename,
                target_id,
                target_symbol_spec,
                loaded_packages,
                included_packages,
            } => cross_pkg_access(
                pos,
                decl_pos,
                current_package,
                current_package_assignment_kind,
                target_package,
                target_package_assignment_kind,
                target_filename,
                target_id,
                target_symbol_spec,
                loaded_packages,
                included_packages,
                true, // Soft
            ),
            Excluded_path_access {
                pos,
                decl_pos,
                package,
                target_filename,
                target_id,
                target_symbol_spec,
            } => excluded_path_access(
                pos,
                decl_pos,
                package,
                target_filename,
                target_id,
                target_symbol_spec,
            ),
        }
    }
}

pub mod eval_xhp {
    use super::*;
    use crate::typing_error::primary::xhp;

    pub fn xhp_required(
        pos: Pos,
        why_xhp: String,
        ty_reason_msg: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let claim = {
            let pos = pos.clone();
            Lazy::new(move || Message(pos, "An XHP instance was expected".into()))
        };
        let reasons = ty_reason_msg.map(move |ty_reason_msg| {
            // Pos_or_decl.of_raw_pos
            let mut reasons = vec![Message(pos, why_xhp.into())];
            reasons.extend(ty_reason_msg.iter().cloned());
            reasons
        });
        create(Typing::XhpRequired, claim, Some(reasons), None)
    }

    pub fn illegal_xhp_child(pos: Pos, reasons: Lazy<Vec<Message<PosOrDecl>>>) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "XHP children must be compatible with XHPChild".into(),
            )
        });
        create(Typing::IllegalXhpChild, claim, Some(reasons), None)
    }

    pub fn missing_xhp_required_attr(
        pos: Pos,
        attr: String,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!("Required attribute {} is missing.", md_codify(&attr)).into(),
            )
        });
        create(Typing::MissingXhpRequiredAttr, claim, Some(reasons), None)
    }

    pub fn attribute_value(pos: Pos, attr_name: String, valid_values: Vec<String>) -> T {
        let claim = Lazy::new(move || {
            Message(pos, {
                let valid_values: Vec<String> =
                    valid_values.iter().map(|x| md_codify(x)).collect();
                format!(
                    "Invalid value for {}, expected one of {}.",
                    md_codify(&attr_name),
                    valid_values.join(", ")
                )
                .into()
            })
        });
        create(Typing::InvalidXhpAttributeValue, claim, None, None)
    }

    pub fn to_error<E: ?Sized>(t: xhp::T, _env: &E) -> T {
        use xhp::T::*;
        match t {
            Xhp_required {
                pos,
                why_xhp,
                ty_reason_msg,
            } => xhp_required(pos, why_xhp, ty_reason_msg),
            Illegal_xhp_child { pos, ty_reason_msg } => illegal_xhp_child(pos, ty_reason_msg),
            Missing_xhp_required_attr {
                pos,
                attr,
                ty_reason_msg,
            } => missing_xhp_required_attr(pos, attr, ty_reason_msg),
            Attribute_value {
                pos,
                attr_name,
                valid_values,
            } => attribute_value(pos, attr_name, valid_values),
        }
    }
}

pub mod eval_casetype {
    use super::*;
    use crate::typing_error::primary::casetype;

    pub fn overlapping_variant_types(
        pos: Pos,
        name: String,
        reasons: Lazy<Vec<Message<PosOrDecl>>>,
    ) -> T {
        let claim = Lazy::new(move || {
            Message(pos, {
                let name = render::utils_strip_ns(&name);
                format!(
                    "Invalid case type declaration. More than one variant of {} could contain values with the same runtime tag",
                    md_codify(name)
                )
                .into()
            })
        });
        create(Typing::IllegalCaseTypeVariants, claim, Some(reasons), None)
    }

    pub fn invalid_recursive(pos: Pos, name: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "This recursive case type is not supported. {} should not be at the top-level.",
                    md_codify(render::utils_strip_ns(&name))
                )
                .into(),
            )
        });
        create(Typing::InvalidRecursiveType, claim, None, None)
    }

    pub fn recursive_where_clause(pos: Pos, name: String, mentions: Vec<PosOrDecl>) -> T {
        let reasons = Lazy::new(move || {
            mentions
                .into_iter()
                .map(|mention| {
                    Message(
                        mention,
                        format!(
                            "{} appears here",
                            md_codify(render::utils_strip_ns(&name))
                        )
                        .into(),
                    )
                })
                .collect()
        });
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Recursion is not supported via case type where clauses.".into(),
            )
        });
        create(Typing::InvalidRecursiveType, claim, Some(reasons), None)
    }

    pub fn to_error<E: ?Sized>(t: casetype::T, _env: &E) -> T {
        use casetype::T::*;
        match t {
            Overlapping_variant_types { pos, name, why } => {
                overlapping_variant_types(pos, name, why)
            }
            Invalid_recursive { pos, name } => invalid_recursive(pos, name),
            Recursive_where_clause {
                pos,
                name,
                mentions,
            } => recursive_where_clause(pos, name, mentions),
        }
    }
}

pub mod eval_simplihack {
    use super::*;
    use crate::typing_error::primary::simplihack;

    pub fn run_prompt(pos: Pos) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Run AI Code Action by clicking on this position in the file".into(),
            )
        });
        create(Typing::SimpliHackRunPrompt, claim, None, None)
    }

    pub fn rerun_prompt(pos: Pos, prompt_digest: String, expected_digest: String) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                format!(
                    "The prompt has changed (digest: {}, expected: {}). Please re-run the AI Code Action.",
                    prompt_digest, expected_digest
                )
                .into(),
            )
        });
        create(Typing::SimpliHackRunPrompt, claim, None, None)
    }

    pub fn evaluation_error(pos: Pos, stack_trace: Lazy<Vec<Message<PosOrDecl>>>) -> T {
        let claim = Lazy::new(move || {
            Message(
                pos,
                "Error while evaluating this SimpliHack expression".into(),
            )
        });
        create(Typing::SimpliHackEvalError, claim, Some(stack_trace), None)
    }

    pub fn to_error<E: ?Sized>(t: simplihack::T, _env: &E) -> T {
        use simplihack::T::*;
        match t {
            Run_prompt { pos } => run_prompt(pos),
            Rerun_prompt {
                pos,
                prompt_digest,
                expected_digest,
            } => rerun_prompt(pos, prompt_digest, expected_digest),
            Evaluation_error { pos, stack_trace } => evaluation_error(pos, stack_trace),
        }
    }
}

#[cfg(test)]
mod tests {
    use oxidized::package::PosId;
    use oxidized::quickfix::Edits;
    use oxidized::quickfix::Quickfix;
    use relative_path::RelativePath;

    use super::*;
    use crate::typing_error::primary;
    use crate::typing_error_utils::common::testing::pos;

    /// The error as `hh single` prints it. The expected strings below are
    /// the text of the `.exp` file named above each of them.
    fn render(t: &T) -> String {
        crate::typing_error_utils::common::testing::render(t.code, &t.claim, &t.reasons)
    }

    #[test]
    fn create_defaults() {
        let t = create(
            Typing::UnifyError,
            Lazy::from_val(Message(pos("a.php", 1, 1, 2), "Typing error".into())),
            None,
            None,
        );
        assert_eq!(t.code, Typing::UnifyError);
        assert!(t.reasons.force().is_empty());
        assert!(t.quickfixes.is_empty());
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 1, characters 1-2:\nTyping error (Typing[4110])\n"
        );
    }

    #[test]
    fn shape() {
        use primary::shape;
        // hphp/hack/test/typecheck/key_exists_optional_nothing.php.exp
        let file = "key_exists_optional_nothing.php";
        let t = eval_shape::to_error(
            shape::T::Shapes_key_exists_always_false {
                pos: pos(file, 5, 7, 32),
                field_name: "a".to_string(),
                decl_pos: pos(file, 4, 15, 36),
                reason: shape::NothingOrUndefined::Nothing(Lazy::new(move || {
                    vec![Message(pos(file, 4, 29, 35), "It is nothing".into())]
                })),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"key_exists_optional_nothing.php\", line 5, characters 7-32:\n\
             This `Shapes::keyExists()` check is always false (Typing[4250])\n  \
             File \"key_exists_optional_nothing.php\", line 4, characters 15-36:\n  \
             The type of the field `a` in this shape doesn't allow any values\n  \
             File \"key_exists_optional_nothing.php\", line 4, characters 29-35:\n  \
             It is nothing\n"
        );
        // hphp/hack/test/typecheck/shape_remove_key2.php.exp
        let file = "shape_remove_key2.php";
        let t = eval_shape::to_error(
            shape::T::Shapes_method_access_with_non_existent_field {
                pos: pos(file, 24, 20, 22),
                field_name: "x".to_string(),
                decl_pos: pos(file, 22, 3, 35),
                method_name: "idx".to_string(),
                reason: shape::NothingOrUndefined::Undefined,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"shape_remove_key2.php\", line 24, characters 20-22:\n\
             You are calling `Shapes::idx()` on a field known to not exist (Typing[4251])\n  \
             File \"shape_remove_key2.php\", line 22, characters 3-35:\n  \
             The field `x` is not defined in this shape\n"
        );
        // hphp/hack/test/typecheck/shapes_cc_6.php.exp
        let file = "shapes_cc_6.php";
        let t = eval_shape::to_error(
            shape::T::Shape_field_class_mismatch {
                pos: pos(file, 22, 3, 7),
                class_name: "Y".to_string(),
                witness_pos: pos(file, 21, 3, 7),
                witness_class_name: "X".to_string(),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"shapes_cc_6.php\", line 22, characters 3-7:\n\
             Shape field name is class constant from `Y` (Typing[4085])\n  \
             File \"shapes_cc_6.php\", line 21, characters 3-7:\n  \
             But expected constant from `X`\n"
        );
        // `is_empty` picks the message and the code.
        let name = |is_empty| {
            eval_shape::to_error(
                shape::T::Invalid_shape_field_name {
                    pos: pos("a.php", 1, 1, 2),
                    is_empty,
                },
                &(),
            )
        };
        assert_eq!(name(false).code, Typing::InvalidShapeFieldName);
        assert_eq!(name(true).code, Typing::InvalidShapeFieldNameEmpty);
        assert_eq!(
            name(true).claim.force().1,
            "A shape field name cannot be an empty string"
        );
        // The type name is not put in backticks, and the trail follows.
        let t = eval_shape::to_error(
            shape::T::Invalid_shape_field_type {
                pos: pos("a.php", 3, 1, 2),
                ty_pos: pos("a.php", 2, 1, 2),
                ty_name: Lazy::from_val("a float".to_string()),
                trail: vec![pos("a.php", 1, 1, 2)],
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 1-2:\n\
             A shape field name must be an `int` or `string` (Typing[4052])\n  \
             File \"a.php\", line 2, characters 1-2:\n  \
             Not a float\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             Typedef definition comes from here\n"
        );
    }

    #[test]
    fn destructure() {
        use primary::shape_and_tuple_destructure::T as D;
        // hphp/hack/test/typecheck/destructure/union_bad.php.exp
        let t = eval_destructure::to_error(
            D::Tuple_arity_mismatch {
                pos: pos("union_bad.php", 19, 3, 7),
                pat_arity: 2,
                tuple_arity: 3,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"union_bad.php\", line 19, characters 3-7:\n\
             Tuple arity mismatch: expected 2 elements in destructuring pattern but the tuple type has 3 (Typing[4513])\n"
        );
        // hphp/hack/test/typecheck/destructure/missing_ellipsis_bad.php.exp
        let t = eval_destructure::to_error(
            D::Tuple_arity_mismatch {
                pos: pos("missing_ellipsis_bad.php", 5, 3, 7),
                pat_arity: 1,
                tuple_arity: 2,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"missing_ellipsis_bad.php\", line 5, characters 3-7:\n\
             Tuple arity mismatch: expected 1 element in destructuring pattern but the tuple type has 2 (Typing[4513])\n"
        );
        let t = eval_destructure::to_error(
            D::Missing_ellipsis(pos("missing_ellipsis_bad.php", 10, 3, 7)),
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"missing_ellipsis_bad.php\", line 10, characters 3-7:\n\
             Missing `...`: the shape type has unknown fields, so the destructuring pattern must end with `...` (Typing[4510])\n"
        );
        // The plural is that of the tuple here.
        let t = eval_destructure::to_error(
            D::Tuple_arity_exceeds {
                pos: pos("a.php", 1, 1, 2),
                pat_arity: 2,
                tuple_arity: 1,
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "Too many entries in tuple destructuring pattern: pattern has 2 but the tuple type only has 1 element"
        );
        assert_eq!(t.code, Typing::DestructureTupleArityMismatch);
    }

    #[test]
    fn switch() {
        use primary::switch;
        // hphp/hack/test/typecheck/switch_default.php.exp
        let file = "switch_default.php";
        let t = eval_switch::to_error(
            switch::T::Switch_nonexhaustive {
                switch_pos: pos(file, 11, 3, 88),
                missing: Lazy::from_val(vec!["SwitchEnum::B".to_string()]),
                scrutinee_pos: pos(file, 11, 11, 15),
                scrutinee_type: Lazy::from_val("SwitchEnum".to_string()),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"switch_default.php\", line 11, characters 3-88:\n\
             This `switch` statement is nonexhaustive. At least the following cases are missing: `SwitchEnum::B` (Typing[4019])\n  \
             File \"switch_default.php\", line 11, characters 11-15:\n  \
             The scrutinee has type `SwitchEnum`.\n"
        );
        let t = eval_switch::to_error(
            switch::T::Switch_nonexhaustive {
                switch_pos: pos(file, 11, 3, 88),
                missing: Lazy::from_val(vec!["A".to_string(), "B".to_string()]),
                scrutinee_pos: pos(file, 11, 11, 15),
                scrutinee_type: Lazy::from_val("E".to_string()),
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "This `switch` statement is nonexhaustive. At least the following cases are missing: `A`, `B`"
        );
        let t = eval_switch::to_error(
            switch::T::Switch_needs_default {
                switch_pos: pos(file, 11, 3, 88),
                scrutinee_pos: pos(file, 11, 11, 15),
                scrutinee_type: Lazy::from_val("int".to_string()),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"switch_default.php\", line 11, characters 3-88:\n\
             This `switch` case cannot be checked for exhaustivity. Please provide a default. Without a default, when none of the cases match, a runtime exception will be thrown. (Typing[4489])\n  \
             File \"switch_default.php\", line 11, characters 11-15:\n  \
             The scrutinee has type `int` which is not an enum, enum class, enum class label, null, or nullable or tuples of those types.\n"
        );
    }

    #[test]
    fn enum_() {
        use primary::enum_;
        use primary::enum_::const_;
        // hphp/hack/test/typecheck/fc_enum_4.php.exp
        let t = eval_enum::to_error(
            enum_::T::Enum_type_bad {
                pos: pos("fc_enum_4.php", 4, 6, 8),
                ty_name: Lazy::from_val("bool".to_string()),
                is_enum_class: false,
                trail: vec![],
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"fc_enum_4.php\", line 4, characters 6-8:\n\
             Enums must be `int` or `string` or `arraykey`, not `bool` (Typing[4024])\n"
        );
        // hphp/hack/test/typecheck/case_type/case_type_enum_base_type.php.exp
        let file = "case_type_enum_base_type.php";
        let t = eval_enum::to_error(
            enum_::T::Enum_type_bad_case_type {
                pos: pos(file, 6, 6, 7),
                ty_name: Lazy::from_val("MyInt".to_string()),
                case_type_decl_pos: pos(file, 4, 11, 15),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"case_type_enum_base_type.php\", line 6, characters 6-7:\n\
             Cannot use a case type as the base type for an enum/enum class (Typing[4024])\n  \
             File \"case_type_enum_base_type.php\", line 4, characters 11-15:\n  \
             `MyInt` is declared as a case type here\n"
        );
        // hphp/hack/test/typecheck/enum_class/typing.extends4.bad.php.exp
        let t = eval_enum::to_error(
            enum_::T::Incompatible_enum_inclusion_base {
                pos: pos("typing.extends4.bad.php", 23, 30, 30),
                classish_name: "\\F".to_string(),
                src_classish_name: "\\E".to_string(),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"typing.extends4.bad.php\", line 23, characters 30-30:\n\
             Enum F includes enum E but their base types are incompatible (Typing[4388])\n"
        );
        // The constants that are missing, `default` for `None`; the reason
        // depends on `kind` and on whether a `None` is missing.
        let nonexhaustive = |kind: Option<&str>, missing| {
            eval_enum::to_error(
                enum_::T::Enum_switch_nonexhaustive {
                    pos: pos("a.php", 2, 1, 2),
                    kind: kind.map(|k| k.to_string()),
                    decl_pos: pos("a.php", 1, 1, 2),
                    missing,
                },
                &(),
            )
        };
        let label = const_::T::Label {
            class_: "\\E".to_string(),
            const_: "A".to_string(),
        };
        assert_eq!(
            render(&nonexhaustive(
                Some("Enum"),
                vec![
                    Some(label.clone()),
                    Some(const_::T::Null),
                    Some(const_::T::Bool(true)),
                    Some(const_::T::Int(None)),
                    Some(const_::T::String(Some("'x'".to_string()))),
                    None
                ]
            )),
            "ERROR: File \"a.php\", line 2, characters 1-2:\n\
             `switch` statement nonexhaustive; at least the following cases are missing: `A`, `null`, `true`, `int`, `'x'`, `default` (Typing[4019])\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             Enum declared here\n"
        );
        assert_eq!(
            *nonexhaustive(None, vec![Some(label.clone()), None])
                .reasons
                .force(),
            vec![Message(
                pos("a.php", 1, 1, 2),
                "only unions and intersections of bool, null and enums can be switched on without a default"
                    .into()
            )]
        );
        assert!(
            nonexhaustive(None, vec![Some(label.clone())])
                .reasons
                .force()
                .is_empty()
        );
        // `kind` comes with its trailing space; `expected` is in backticks in
        // the claim and in the reason.
        let t = eval_enum::to_error(
            enum_::T::Enum_switch_wrong_class {
                pos: pos("a.php", 2, 1, 2),
                kind: "enum ".to_string(),
                expected: Lazy::from_val("E".to_string()),
                actual: Lazy::from_val("F".to_string()),
                expected_pos: Some(pos("a.php", 1, 1, 2)),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 2, characters 1-2:\n\
             Switching on enum `E` but using constant from `F` (Typing[4023])\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             expecting `E` based on this\n"
        );
        let t = eval_enum::to_error(
            enum_::T::Enum_switch_redundant {
                pos: pos("a.php", 2, 1, 2),
                first_pos: pos("a.php", 1, 1, 2),
                const_name: label,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 2, characters 1-2:\n\
             Redundant `case` statement (Typing[4021])\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             `A` already handled here\n"
        );
        // The expected type comes first, then the label.
        let mismatch = |expected_ty_msg_opt| {
            eval_enum::to_error(
                enum_::T::Enum_class_label_member_mismatch {
                    pos: pos("a.php", 2, 1, 2),
                    label: "A".to_string(),
                    expected_ty_msg_opt,
                },
                &(),
            )
        };
        assert_eq!(
            render(&mismatch(Some(Lazy::from_val(vec![Message(
                pos("a.php", 1, 1, 2),
                "Expected `int`".into()
            )])))),
            "ERROR: File \"a.php\", line 2, characters 1-2:\n\
             Enum class label/member mismatch (Typing[4110])\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             Expected `int`\n  \
             File \"a.php\", line 2, characters 1-2:\n  \
             But got an enum class label/member: `A`\n"
        );
        assert_eq!(
            mismatch(None).reasons.force()[0].1,
            "Unexpected enum class label/member: `A`"
        );
    }

    #[test]
    fn expr_tree() {
        use primary::expr_tree;
        // hphp/hack/test/typecheck/expression_trees/mismatched_types.php.exp
        let t = eval_expr_tree::to_error(
            expr_tree::T::Expression_tree_unsupported_operator {
                pos: pos("mismatched_types.php", 8, 5, 10),
                member_name: "__plus".to_string(),
                class_name: "ExampleStringOpType".to_string(),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"mismatched_types.php\", line 8, characters 5-10:\n\
             `ExampleStringOpType` does not support this operator (it has no instance method named `__plus`) (Typing[4053])\n"
        );
        let t = eval_expr_tree::to_error(
            expr_tree::T::Expression_tree_unsupported_operator {
                pos: pos("a.php", 1, 1, 2),
                member_name: "__bool".to_string(),
                class_name: "C".to_string(),
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "`C` cannot be used as a boolean (it has no instance method named `__bool`)"
        );
    }

    #[test]
    fn readonly() {
        use primary::readonly;
        // hphp/hack/test/typecheck/readonly/collection_append.php.exp
        let file = "collection_append.php";
        let t = eval_readonly::to_error(
            readonly::T::Readonly_mismatch {
                pos: pos(file, 11, 3, 6),
                what: readonly::ReadonlyMismatchWhat::collection_mod,
                pos_sub: pos(file, 11, 10, 27),
                pos_super: pos(file, 11, 3, 4),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"collection_append.php\", line 11, characters 3-6:\n\
             Invalid collection modification (Typing[4411])\n  \
             File \"collection_append.php\", line 11, characters 10-27:\n  \
             This expression is readonly\n  \
             File \"collection_append.php\", line 11, characters 3-4:\n  \
             But this value is mutable\n"
        );
        let t = eval_readonly::to_error(
            readonly::T::Readonly_modified {
                pos: pos(file, 19, 3, 9),
                reason_opt: None,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"collection_append.php\", line 19, characters 3-9:\n\
             This value is readonly, its properties cannot be modified (Typing[4409])\n"
        );
        let t = eval_readonly::to_error(
            readonly::T::Readonly_mismatch {
                pos: pos("a.php", 3, 1, 2),
                what: readonly::ReadonlyMismatchWhat::arg_mut,
                pos_sub: pos("a.php", 2, 1, 2),
                pos_super: pos("a.php", 1, 1, 2),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 3, characters 1-2:\n\
             Invalid argument (Typing[4411])\n  \
             File \"a.php\", line 2, characters 1-2:\n  \
             This expression is mutable\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             It is incompatible with this parameter, which is readonly\n"
        );
        // hphp/hack/test/typecheck/readonly_shapes_hhi.php.exp
        let t = eval_readonly::to_error(
            readonly::T::Explicit_readonly_cast {
                pos: pos("readonly_shapes_hhi.php", 17, 3, 28),
                decl_pos: pos("stdlib/builtins_readonly.hhi", 55, 28, 33),
                kind: readonly::ExplicitReadonlyCastKind::fn_call,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"readonly_shapes_hhi.php\", line 17, characters 3-28:\n\
             This function call returns a readonly value. It must be explicitly wrapped in a readonly expression. (Typing[4412])\n  \
             File \"stdlib/builtins_readonly.hhi\", line 55, characters 28-33:\n  \
             The function call is defined here.\n"
        );
        // The quickfix inserts at the start of the expression.
        match &t.quickfixes[..] {
            [
                Quickfix {
                    title,
                    edits: Edits::Eager(edits),
                    hint_styles,
                },
            ] => {
                assert_eq!(title, "Insert `readonly`");
                assert!(hint_styles.is_empty());
                let [(new_text, qf_pos)] = &edits[..] else {
                    panic!()
                };
                assert_eq!(new_text, "readonly ");
                assert_eq!(qf_pos.info_raw(), (2, 2));
            }
            _ => panic!(),
        }
    }

    #[test]
    fn coeffect() {
        use primary::coeffect;
        // hphp/hack/test/typecheck/call_in_static_vec.php.exp
        let file = "call_in_static_vec.php";
        let t = eval_coeffect::to_error(
            coeffect::T::Call_coeffect {
                pos: pos(file, 7, 26, 29),
                available_pos: pos(file, 7, 22, 32),
                available_incl_unsafe: Lazy::from_val("the capability set {}".to_string()),
                required_pos: pos(file, 4, 26, 26),
                required: Lazy::from_val(
                    "the capability set {AccessGlobals, IO, ImplicitPolicyLocal, RxLocal, SystemLocal, WriteProperty}"
                        .to_string(),
                ),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"call_in_static_vec.php\", line 7, characters 26-29:\n\
             This call is not allowed because its capabilities are incompatible with the context (Typing[4390])\n  \
             File \"call_in_static_vec.php\", line 7, characters 22-32:\n  \
             From this declaration, the context of this function body provides the capability set {}\n  \
             File \"call_in_static_vec.php\", line 4, characters 26-26:\n  \
             But the function being called requires the capability set {AccessGlobals, IO, ImplicitPolicyLocal, RxLocal, SystemLocal, WriteProperty}\n"
        );
        // hphp/hack/test/typecheck/memoize_obj_policied.php.exp
        let file = "memoize_obj_policied.php";
        let op = |suggestion| {
            eval_coeffect::to_error(
                coeffect::T::Op_coeffect_error {
                    pos: pos(file, 19, 17, 24),
                    op_name: "Memoizing object parameters".to_string(),
                    locally_available: Lazy::from_val("the capability set {}".to_string()),
                    available_pos: pos(file, 19, 29, 30),
                    err_code: Typing::MemoizeObjectWithoutGlobals,
                    required: Lazy::from_val("the capability AccessGlobals".to_string()),
                    suggestion,
                },
                &(),
            )
        };
        assert_eq!(
            render(&op(None)),
            "ERROR: File \"memoize_obj_policied.php\", line 19, characters 17-24:\n\
             Memoizing object parameters requires the capability AccessGlobals, which is not provided by the context. (Typing[4447])\n  \
             File \"memoize_obj_policied.php\", line 19, characters 29-30:\n  \
             The local (enclosing) context provides the capability set {}\n"
        );
        // The suggestion comes after the local context.
        let t = op(Some(Lazy::from_val(vec![Message(
            pos(file, 1, 1, 2),
            "Consider this".into(),
        )])));
        assert_eq!(
            t.reasons
                .force()
                .iter()
                .map(|Message(_, msg)| msg.to_string())
                .collect::<Vec<_>>(),
            vec![
                "The local (enclosing) context provides the capability set {}",
                "Consider this"
            ]
        );
    }

    #[test]
    fn wellformedness() {
        use primary::wellformedness;
        // hphp/hack/test/typecheck/shape_modified5.php.exp
        let file = "shape_modified5.php";
        let t = eval_wellformedness::to_error(
            wellformedness::T::Returns_with_and_without_value {
                pos: pos(file, 17, 1, 163),
                with_value_pos: pos(file, 23, 5, 14),
                without_value_pos_opt: None,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"shape_modified5.php\", line 17, characters 1-163:\n\
             This function can exit with and without returning a value (Typing[4421])\n  \
             File \"shape_modified5.php\", line 23, characters 5-14:\n  \
             Returning a value here.\n  \
             File \"shape_modified5.php\", line 17, characters 1-163:\n  \
             This function does not always return a value\n"
        );
        let t = eval_wellformedness::to_error(
            wellformedness::T::Returns_with_and_without_value {
                pos: pos(file, 17, 1, 163),
                with_value_pos: pos(file, 23, 5, 14),
                without_value_pos_opt: Some(pos(file, 25, 5, 11)),
            },
            &(),
        );
        assert_eq!(
            t.reasons.force()[1],
            Message(
                pos(file, 25, 5, 11),
                "Returning without a value here".into()
            )
        );
        // hphp/hack/test/typecheck/return_mismatch/non_value_return_type_too_general.php.exp
        let file = "non_value_return_type_too_general.php";
        let t = eval_wellformedness::to_error(
            wellformedness::T::Non_void_annotation_on_return_void_function {
                is_async: false,
                hint_pos: pos(file, 4, 21, 25),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"non_value_return_type_too_general.php\", line 4, characters 21-25:\n\
             Functions that do not return a value must have a type of void (Typing[4422])\n"
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: "Change to `void`".to_string(),
                edits: Edits::Eager(vec![("void".to_string(), pos(file, 4, 21, 25))]),
                hint_styles: vec![],
            }]
        );
        let t = eval_wellformedness::to_error(
            wellformedness::T::Non_void_annotation_on_return_void_function {
                is_async: true,
                hint_pos: pos(file, 4, 21, 25),
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "Async functions that do not return a value must have a type of Awaitable<void>"
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: "Change to `Awaitable<void>`".to_string(),
                edits: Edits::Eager(vec![(
                    "Awaitable<void>".to_string(),
                    pos(file, 4, 21, 25)
                )]),
                hint_styles: vec![],
            }]
        );
        // `Missing_return`: the new text is `void` even in an async function.
        let t = eval_wellformedness::to_error(
            wellformedness::T::Missing_return {
                pos: pos(file, 13, 10, 15),
                hint_pos: Some(pos(file, 13, 21, 23)),
                is_async: true,
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"non_value_return_type_too_general.php\", line 13, characters 10-15:\n\
             Invalid return type (Typing[4336])\n"
        );
        assert_eq!(
            t.quickfixes,
            vec![Quickfix {
                title: "Change to `Awaitable<void>`".to_string(),
                edits: Edits::Eager(vec![("void".to_string(), pos(file, 13, 21, 23))]),
                hint_styles: vec![],
            }]
        );
        // hphp/hack/test/typecheck/use_void.php.exp
        let file = "use_void.php";
        let t = eval_wellformedness::to_error(
            wellformedness::T::Void_usage {
                pos: pos(file, 12, 8, 18),
                reason: Lazy::from_val(vec![Message(
                    pos(file, 12, 8, 16),
                    "A `void` function doesn't return a value. because this function does not always return a value"
                        .into(),
                )]),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"use_void.php\", line 12, characters 8-18:\n\
             You are using the return value of a `void` function (Typing[4119])\n  \
             File \"use_void.php\", line 12, characters 8-16:\n  \
             A `void` function doesn't return a value. because this function does not always return a value\n"
        );
    }

    #[test]
    fn modules() {
        use primary::modules;
        // hphp/hack/test/typecheck/tests_bypass_visibility/internal_class_no_attr.php.exp
        let mismatch = |file, line, tests_bypass_visibility_context| {
            eval_modules::to_error(
                modules::T::Module_mismatch {
                    pos: pos(file, line, 9, 22),
                    current_module_opt: None,
                    decl_pos: pos("internal_class_no_attr.php--defs.php", 5, 16, 29),
                    target_module: "m".to_string(),
                    tests_bypass_visibility_context,
                },
                &(),
            )
        };
        assert_eq!(
            render(&mismatch("internal_class_no_attr.php--non_test.php", 5, false)),
            "ERROR: File \"internal_class_no_attr.php--non_test.php\", line 5, characters 9-22:\n\
             Cannot access an internal element from module `m` in the default module (Typing[4444])\n  \
             File \"internal_class_no_attr.php--defs.php\", line 5, characters 16-29:\n  \
             This is from module `m`\n"
        );
        assert_eq!(
            render(&mismatch("internal_class_no_attr.php--test.php", 7, true)),
            "ERROR: File \"internal_class_no_attr.php--test.php\", line 7, characters 9-22:\n\
             Cannot access an internal element from module `m` in the default module (Typing[4444])\n  \
             File \"internal_class_no_attr.php--defs.php\", line 5, characters 16-29:\n  \
             This is from module `m`. To allow access from test contexts, add `<<__TestsBypassVisibility>>` to this class\n"
        );
        let t = eval_modules::to_error(
            modules::T::Module_mismatch {
                pos: pos("a.php", 2, 1, 2),
                current_module_opt: Some("n".to_string()),
                decl_pos: pos("a.php", 1, 1, 2),
                target_module: "m".to_string(),
                tests_bypass_visibility_context: false,
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "Cannot access an internal element from module `m` in module `n`"
        );
    }

    #[test]
    fn package() {
        use primary::package;
        use primary::package::TargetSymbolSpec;
        let file = |path: &str| -> RelativePath { pos(path, 1, 1, 1).filename().clone() };
        let config = |line, start, end| pos("PACKAGES.toml", line, start, end);
        let texts = |t: &T| -> Vec<String> {
            std::iter::once(t.claim.force().1.to_string())
                .chain(t.reasons.force().iter().map(|Message(_, m)| m.to_string()))
                .collect()
        };
        // hphp/hack/test/package/implicit_packages/include_specific_member.php.exp
        let access = |target_symbol_spec| package::T::Cross_pkg_access {
            pos: pos("include_specific_member.php--member_consumer/use.php", 7, 7, 25),
            decl_pos: pos("include_specific_member.php--prototypes/beta/b.php", 2, 7, 25),
            current_package: Some(PosId(config(33, 11, 25), "member_consumer".to_string())),
            current_package_assignment_kind: "entry in the package config".to_string(),
            target_package: Some(PosId(config(18, 20, 29), "prototypes.beta".to_string())),
            target_package_assignment_kind: "entry in the package config".to_string(),
            current_filename: file("include_specific_member.php--member_consumer/use.php"),
            target_filename: file("include_specific_member.php--prototypes/beta/b.php"),
            target_id: "\\ExcludedMemberClass".to_string(),
            target_symbol_spec,
            loaded_packages: vec![],
            included_packages: vec![
                (
                    "member_consumer".to_string(),
                    "prototypes.alpha".to_string(),
                    config(35, 13, 30),
                ),
                (
                    "member_consumer".to_string(),
                    "intern".to_string(),
                    config(35, 33, 40),
                ),
                (
                    "member_consumer".to_string(),
                    "shared".to_string(),
                    config(35, 43, 50),
                ),
            ],
        };
        let t = eval_package::to_error(access(TargetSymbolSpec::Class), &());
        assert_eq!(t.code as isize, 4472);
        assert_eq!(
            texts(&t),
            vec![
                "Cannot access class `ExcludedMemberClass` defined in package `prototypes.beta` which may not be available",
                "`ExcludedMemberClass` is defined in include_specific_member.php--prototypes/beta/b.php",
                "`ExcludedMemberClass` belongs to package `prototypes.beta` by this entry in the package config",
                "package `member_consumer` is available because the current file belongs to it by this entry in the package config",
                "`member_consumer` includes `prototypes.alpha` via its definition",
                "`member_consumer` includes `intern` via its definition",
                "`member_consumer` includes `shared` via its definition",
            ]
        );
        assert_eq!(
            t.reasons
                .force()
                .iter()
                .map(|Message(p, _)| p.clone())
                .collect::<Vec<_>>(),
            vec![
                pos("include_specific_member.php--prototypes/beta/b.php", 2, 7, 25),
                config(18, 20, 29),
                config(33, 11, 25),
                config(35, 13, 30),
                config(35, 33, 40),
                config(35, 43, 50),
            ]
        );
        // A type constant is worded differently, and a reifiable one has a
        // last reason.
        let t = eval_package::to_error(
            access(TargetSymbolSpec::Reifiable_type_const {
                reifiable_attr_pos: pos("a.php", 3, 1, 2),
                tconst_name: "T".to_string(),
            }),
            &(),
        );
        let texts_ = texts(&t);
        assert_eq!(
            texts_[0],
            "Cannot access `ExcludedMemberClass` defined in package `prototypes.beta`, which may not be available, within a reifiable type constant"
        );
        assert_eq!(
            texts_.last().unwrap(),
            "The type constant `T` is declared `<<__Reifiable>>` here"
        );
        assert_eq!(texts_.len(), 8);
        // `Soft_included_access` is the same error with the other code, and
        // without packages the default package is at `Pos.none`.
        let t = eval_package::to_error(
            package::T::Soft_included_access {
                pos: pos("a.php", 7, 7, 25),
                decl_pos: pos("b.php", 2, 7, 25),
                current_package: None,
                current_package_assignment_kind: "k1".to_string(),
                target_package: None,
                target_package_assignment_kind: "k2".to_string(),
                current_filename: file("a.php"),
                target_filename: file("b.php"),
                target_id: "\\f".to_string(),
                target_symbol_spec: TargetSymbolSpec::Func,
                loaded_packages: vec![PosId(config(1, 1, 2), "p".to_string())],
                included_packages: vec![],
            },
            &(),
        );
        assert_eq!(t.code, Typing::InvalidCrossPackageSoft);
        assert_eq!(
            texts(&t),
            vec![
                "Cannot access function `f` defined in the default package which may not be available",
                "`f` is defined in b.php",
                "`f` belongs to the default package by this k2",
                "the default package is available because the current file belongs to it by this k1",
                "package `p` is assumed to be deployed here",
            ]
        );
        assert!(t.reasons.force()[1].0.is_none());
        let t = eval_package::to_error(
            package::T::Cross_pkg_access_with_requirepackage {
                pos: pos("a.php", 7, 7, 25),
                decl_pos: pos("b.php", 2, 7, 25),
                target_package: "pkg2".to_string(),
                current_package: Some(PosId(config(1, 1, 2), "pkg1".to_string())),
                loaded_packages: vec![],
                included_packages: vec![],
            },
            &(),
        );
        assert_eq!(
            texts(&t),
            vec![
                "Cannot reference this __RequirePackage function",
                "This function is marked with `__RequirePackage(\"pkg2\")`",
                "the current file belongs to package `pkg1`",
            ]
        );
        let t = eval_package::to_error(
            package::T::Cross_pkg_access_with_softrequirepackage {
                pos: pos("a.php", 7, 7, 25),
                decl_pos: pos("b.php", 2, 7, 25),
                current_soft_package_opt: Some((pos("a.php", 5, 1, 2), "pkg1".to_string())),
                target_package: "pkg2".to_string(),
                loaded_packages: vec![],
                included_packages: vec![],
            },
            &(),
        );
        assert_eq!(
            texts(&t),
            vec![
                "Cannot reference this `__SoftRequirePackage` function",
                "This function is marked with `__SoftRequirePackage(\"pkg2\")`, which is a transition feature to help move a function to `__RequirePackage(\"pkg2\")`. It does not allow calling into pkg2 itself, but it can only be called from functions that have access to pkg2.",
                "The current function soft-requires package pkg1, which does not include pkg2",
            ]
        );
        let t = eval_package::to_error(
            package::T::Excluded_path_access {
                pos: pos("a.php", 7, 7, 25),
                decl_pos: pos("iso/__tests__/b.php", 2, 7, 25),
                package: Some(PosId(config(14, 11, 18), "isolated".to_string())),
                target_filename: file("iso/__tests__/b.php"),
                target_id: "\\C".to_string(),
                target_symbol_spec: TargetSymbolSpec::Class,
            },
            &(),
        );
        assert_eq!(t.code, Typing::StrictIsolationExcludedPathAccess);
        assert_eq!(
            texts(&t),
            vec![
                "Cannot access class `C`: it is defined on an excluded path of the strict-isolation package `isolated`, and code outside the excluded path may not reference it",
                "`C` is defined here, in iso/__tests__/b.php -- an excluded path (e.g. matching `package_exclude_patterns`)",
                "package `isolated` is a strict-isolation package (declared here); code on an excluded path is deployment-only and may not be referenced from outside that path",
            ]
        );
    }

    #[test]
    fn xhp() {
        use primary::xhp;
        // hphp/hack/test/typecheck/xhp_invalid_attr_value.php.exp
        let t = eval_xhp::to_error(
            xhp::T::Attribute_value {
                pos: pos("xhp_invalid_attr_value.php", 9, 18, 25),
                attr_name: "size".to_string(),
                valid_values: vec!["\"big\"".to_string(), "\"small\"".to_string()],
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"xhp_invalid_attr_value.php\", line 9, characters 18-25:\n\
             Invalid value for `size`, expected one of `\"big\"`, `\"small\"`. (Typing[4483])\n"
        );
        // hphp/hack/test/typecheck/xhp/required_attr/basic.php.exp
        let t = eval_xhp::to_error(
            xhp::T::Missing_xhp_required_attr {
                pos: pos("basic.php", 24, 8, 12),
                attr: "a".to_string(),
                ty_reason_msg: Lazy::from_val(vec![Message(
                    pos("basic.php", 4, 38, 40),
                    "The attribute `a` is declared here.".into(),
                )]),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"basic.php\", line 24, characters 8-12:\n\
             Required attribute `a` is missing. (Typing[4314])\n  \
             File \"basic.php\", line 4, characters 38-40:\n  \
             The attribute `a` is declared here.\n"
        );
        // The reason for requiring XHP is at the position of the claim, first.
        let t = eval_xhp::to_error(
            xhp::T::Xhp_required {
                pos: pos("a.php", 2, 1, 2),
                why_xhp: "XHP is required here".to_string(),
                ty_reason_msg: Lazy::from_val(vec![Message(
                    pos("a.php", 1, 1, 2),
                    "It is an int".into(),
                )]),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"a.php\", line 2, characters 1-2:\n\
             An XHP instance was expected (Typing[4191])\n  \
             File \"a.php\", line 2, characters 1-2:\n  \
             XHP is required here\n  \
             File \"a.php\", line 1, characters 1-2:\n  \
             It is an int\n"
        );
    }

    #[test]
    fn casetype() {
        use primary::casetype;
        // hphp/hack/test/typecheck/case_type/multi_class_bad1.php.exp
        let file = "multi_class_bad1.php";
        let t = eval_casetype::to_error(
            casetype::T::Overlapping_variant_types {
                pos: pos(file, 4, 11, 20),
                name: "\\MultiClass".to_string(),
                why: Lazy::from_val(vec![
                    Message(
                        pos(file, 4, 24, 24),
                        "This is the type `C`, which includes **instances of the class C**".into(),
                    ),
                    Message(
                        pos(file, 4, 32, 32),
                        "It overlaps with `E`, which includes **instances of the class E**".into(),
                    ),
                    Message(
                        pos(file, 4, 11, 20),
                        "Because **instances of the class C** contains **instances of the class E**, `C` and `E` cannot be in the same case type".into(),
                    ),
                ]),
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"multi_class_bad1.php\", line 4, characters 11-20:\n\
             Invalid case type declaration. More than one variant of `MultiClass` could contain values with the same runtime tag (Typing[4475])\n  \
             File \"multi_class_bad1.php\", line 4, characters 24-24:\n  \
             This is the type `C`, which includes **instances of the class C**\n  \
             File \"multi_class_bad1.php\", line 4, characters 32-32:\n  \
             It overlaps with `E`, which includes **instances of the class E**\n  \
             File \"multi_class_bad1.php\", line 4, characters 11-20:\n  \
             Because **instances of the class C** contains **instances of the class E**, `C` and `E` cannot be in the same case type\n"
        );
        // hphp/hack/test/typecheck/case_type/where_clauses/non_fixed_point_recursion_mutual.php.exp
        let file = "non_fixed_point_recursion_mutual.php";
        let t = eval_casetype::to_error(
            casetype::T::Recursive_where_clause {
                pos: pos(file, 3, 11, 24),
                name: "\\NonFixedPointA".to_string(),
                mentions: vec![pos(file, 7, 22, 44)],
            },
            &(),
        );
        assert_eq!(
            render(&t),
            "ERROR: File \"non_fixed_point_recursion_mutual.php\", line 3, characters 11-24:\n\
             Recursion is not supported via case type where clauses. (Typing[4485])\n  \
             File \"non_fixed_point_recursion_mutual.php\", line 7, characters 22-44:\n  \
             `NonFixedPointA` appears here\n"
        );
        // `Utils.strip_ns`, not `Render.strip_ns`: `HH\` stays.
        let t = eval_casetype::to_error(
            casetype::T::Invalid_recursive {
                pos: pos("a.php", 1, 1, 2),
                name: "\\HH\\vec".to_string(),
            },
            &(),
        );
        assert_eq!(
            t.claim.force().1,
            "This recursive case type is not supported. `HH\\vec` should not be at the top-level."
        );
    }

    #[test]
    fn simplihack() {
        use primary::simplihack;
        let t = eval_simplihack::to_error(
            simplihack::T::Rerun_prompt {
                pos: pos("a.php", 1, 1, 2),
                prompt_digest: "abc".to_string(),
                expected_digest: "def".to_string(),
            },
            &(),
        );
        assert_eq!(t.code, Typing::SimpliHackRunPrompt);
        assert_eq!(
            t.claim.force().1,
            "The prompt has changed (digest: abc, expected: def). Please re-run the AI Code Action."
        );
        let t = eval_simplihack::to_error(
            simplihack::T::Evaluation_error {
                pos: pos("a.php", 2, 1, 2),
                stack_trace: Lazy::from_val(vec![Message(pos("a.php", 1, 1, 2), "frame".into())]),
            },
            &(),
        );
        assert_eq!(t.code, Typing::SimpliHackEvalError);
        assert_eq!(t.reasons.force().len(), 1);
    }

    #[test]
    fn nothing_is_computed_before_it_is_forced() {
        use std::cell::Cell;
        use std::rc::Rc;

        use primary::enum_;
        let forced = Rc::new(Cell::new(0));
        let name = |s: &'static str| {
            let forced = forced.clone();
            Lazy::new(move || {
                forced.set(forced.get() + 1);
                s.to_string()
            })
        };
        let t = eval_enum::to_error(
            enum_::T::Enum_switch_wrong_class {
                pos: pos("a.php", 2, 1, 2),
                kind: "enum ".to_string(),
                expected: name("E"),
                actual: name("F"),
                expected_pos: None,
            },
            &(),
        );
        assert_eq!(forced.get(), 0);
        // The reasons need `expected` only; the claim needs both, and
        // `expected` is not computed again.
        assert!(t.reasons.force().is_empty());
        assert_eq!(forced.get(), 1);
        t.claim.force();
        assert_eq!(forced.get(), 2);
    }
}
