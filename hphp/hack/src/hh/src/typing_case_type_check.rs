// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_case_type_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::markdown_lite;
use crate::pos_or_decl;
use crate::set_relation;
use crate::typing_data_type::approx_tag_set;
use crate::typing_data_type::data_type;
use crate::typing_data_type::tag;
use crate::typing_data_type::tag_with_reason;
use crate::typing_defs_core::DeclTy;
use crate::typing_env_types::Env;
use crate::typing_error::Lazy;
use crate::typing_error::primary::casetype;
use crate::typing_print;

/// A runtime data type describes the set of values that can carry a particular
/// set of runtime tags. It is possible to map any type to a particular
/// runtime data type, and based on this, reason about if two types can possibly
/// intersect.
pub type RuntimeDataType = (DeclTy, data_type::T);

/// Maps a type hint to its associated runtime data type. This is intended to
/// be used to only as part of checking if a case type is well-formed.
///
/// When safe_for_are_disjoint is true, do not specially handle interfaces' sealed
/// attribute or required ancestors.
/// Temporary flag to avoid an issue with `are_disjoint` T215053987
pub fn data_type_from_hint(
    safe_for_are_disjoint: bool,
    env: &mut Env,
    hint: &aast::Hint,
) -> RuntimeDataType {
    data_type::fromHint(safe_for_are_disjoint, env, hint)
}

/// The `why` of an overlap between `left` and `right`.
fn why(
    env: &Env,
    pos: &Pos,
    left: &(DeclTy, tag_with_reason::T),
    relation: &set_relation::T,
    right: &(DeclTy, tag_with_reason::T),
) -> Vec<(PosOrDecl, String)> {
    let (ty1, tag_with_reason::T { tag: tag1, .. }) = left;
    let (ty2, tag_with_reason::T { tag: tag2, .. }) = right;
    let primary_why = |f: &dyn Fn(&str) -> String| {
        // `@`: OCaml evaluates the right operand first.
        let right_msg = tag_with_reason::to_message(env, f, right);
        let mut left_msg = tag_with_reason::to_message(
            env,
            |s: &str| format!("This is the type `{}`, which includes ", s),
            left,
        );
        left_msg.extend(right_msg);
        left_msg
    };
    let secondary_why = |f: &dyn Fn(&str, &str) -> String| {
        let describe = |tag: &tag::T| markdown_lite::md_bold(&tag::describe(env, tag));
        let ty_str = |ty: &DeclTy| {
            markdown_lite::md_codify(&typing_print::full_strip_ns_decl(
                None,
                false,
                env,
                &ty.clone().to_oxidized(),
            ))
        };
        // `f (describe tag1) (describe tag2) ^ Printf.sprintf ... (ty_str ty1)
        // (ty_str ty2)`: the operands of `^` and the arguments of each call
        // are evaluated from right to left.
        let ty2_str = ty_str(ty2);
        let ty1_str = ty_str(ty1);
        let tag2_str = describe(tag2);
        let tag1_str = describe(tag1);
        let first = f(&tag1_str, &tag2_str);
        vec![(
            pos_or_decl::of_raw_pos(pos.clone()),
            first
                + &format!(
                    ", {} and {} cannot be in the same case type",
                    ty1_str, ty2_str
                ),
        )]
    };
    if set_relation::is_equivalent(relation) {
        primary_why(&|s: &str| format!("It overlaps with `{}`, which also includes ", s))
    } else if set_relation::is_superset(relation) {
        let secondary =
            secondary_why(&|s1: &str, s2: &str| format!("Because {} contains {}", s1, s2));
        let mut msgs = primary_why(&|s: &str| format!("It overlaps with `{}`, which includes ", s));
        msgs.extend(secondary);
        msgs
    } else if set_relation::is_subset(relation) {
        let secondary =
            secondary_why(&|s1: &str, s2: &str| format!("Because {} are also {}", s1, s2));
        let mut msgs = primary_why(&|s: &str| format!("It overlaps with `{}`, which includes ", s));
        msgs.extend(secondary);
        msgs
    } else {
        let secondary = secondary_why(&|s1: &str, s2: &str| {
            format!(
                "Because it is possible for values to be both {} and {}",
                s1, s2
            )
        });
        let mut msgs =
            primary_why(&|s: &str| format!("It may overlap with `{}`, which includes ", s));
        msgs.extend(secondary);
        msgs
    }
}

/// Checks if two different runtime data types can possibly overlap. Two
/// runtime data types are considered to overlap if there exist a value at
/// runtime that can belong to both data types. If no such value can exist then
/// [None] is returned. Otherwise an error is produced that explains why the
/// two runtime data types are considered to be overlapping.
pub fn check_overlapping(
    env: &Env,
    pos: Pos,
    name: String,
    (ty1, data_type1): &RuntimeDataType,
    (ty2, data_type2): &RuntimeDataType,
) -> Option<casetype::T> {
    match approx_tag_set::disjoint(env, data_type1, data_type2) {
        crate::approx_set::Disjoint::Sat => None,
        crate::approx_set::Disjoint::Unsat {
            left,
            relation,
            right,
        } => {
            let env = env.clone();
            let ty1 = ty1.clone();
            let ty2 = ty2.clone();
            let why_pos = pos.clone();
            let err = casetype::T::Overlapping_variant_types {
                pos,
                name,
                why: Lazy::new(move || {
                    why(&env, &why_pos, &(ty1, left), &relation, &(ty2, right))
                        .into_iter()
                        .map(|(p, s)| oxidized::message::Message(p, s.into()))
                        .collect()
                }),
            };
            Some(err)
        }
    }
}
