// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_case_type_variant.ml`. See `hh/PORTING.md`.

use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
use crate::typing_data_type::approx_tag_set;
use crate::typing_data_type::data_type;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::TypedefCaseTypeVariant;
use crate::typing_defs::TypedefTypeAssignment;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclTy_;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_reason::T as Reason;
use crate::typing_utils;

/// Return whether or not any of the case type variants have a where clause
pub fn has_where_clauses(variants: &[TypedefCaseTypeVariant]) -> bool {
    variants.iter().any(|v| !v.where_constraints.is_empty())
}

/// Given the variants of a case type (encoded as a locl_ty) and another locl_ty [intersecting_ty]
/// produce a new locl_ty containing only the types in the variant that map to an intersecting
/// data type. For example:
///  Given
///
///   [variants] = int | vec<int> | Vector<int>
///   [intersecting_ty] = Container<string>
///
///  This function will return the type `vec<int> | Vector<int>` because both `vec<int>` and
/// `Vector<int>` overlap with the tag associated with `Container<string>`.
///
/// Note that this function only considers the data type associated to each type and not
/// the type itself. So even though `vec<int>` and `Container<string>` do not intersect at
/// the type level, they do intersect when considering only the runtime data types.
///
/// When safe_for_are_disjoint is true, do not specially handle interfaces' sealed
/// attribute or required ancestors.
/// Temporary flag to avoid an issue with `are_disjoint` T215053987
pub fn filter_variants_using_datatype(
    safe_for_are_disjoint: bool,
    env: &mut Env,
    reason: Reason,
    variants: &[Ty],
    intersecting_ty: &Ty,
) -> Ty {
    let tags = data_type::from_ty(safe_for_are_disjoint, env, intersecting_ty);
    // `List.fold_map`: from left to right.
    let vtags: Vec<data_type::T> = variants
        .iter()
        .map(|variant| data_type::from_ty(safe_for_are_disjoint, env, variant))
        .collect();
    let tyl: Vec<Ty> = variants
        .iter()
        .zip(vtags.iter())
        .filter_map(|(variant, variant_tags)| {
            if approx_tag_set::are_disjoint(env, variant_tags, &tags) {
                None
            } else {
                Some(variant.clone())
            }
        })
        .collect();
    typing_utils::union_list(env, None, reason, &tyl)
}

/// `Typing_make_type.union` on declared types.
fn make_type_union_decl(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    if tyl.len() == 1 {
        tyl.pop().unwrap()
    } else {
        DeclTy::new(r, DeclTy_::Tunion(tyl.into_boxed_slice()))
    }
}

/// Look up case type via [name].
/// If the case type exists and all variants are unconditional, returns the list
/// of variant types localized using [ty_args]
/// If the case type doesn't exist or any variant has a where clause, returns
/// [None].
///
/// TODO T201569125 - Note: If we could use the ty_args to "evaluate" the where
/// constraints, we could return the variant hints whose constraints are met, but
/// I'm not sure if that's feasible.
pub fn get_variant_tys(env: &mut Env, name: &str, ty_args: &[Ty]) -> Option<Vec<Ty>> {
    match env::get_typedef(env, name) {
        decl_entry::T::Found(td) => match &td.type_assignment {
            TypedefTypeAssignment::CaseType(variant, variants) => {
                let all_variants: Vec<TypedefCaseTypeVariant> = std::iter::once(variant.clone())
                    .chain(variants.iter().cloned())
                    .collect();
                if has_where_clauses(&all_variants) {
                    None
                } else {
                    let single_or_union = if variants.is_empty() {
                        variant.hint.clone()
                    } else {
                        // we're just going to take this union apart so the reason is irrelevant here
                        make_type_union_decl(
                            R::none(),
                            std::iter::once(variant.hint.clone())
                                .chain(variants.iter().map(|v| v.hint.clone()))
                                .collect(),
                        )
                    };
                    let ety_env = ExpandEnv {
                        substs: if ty_args.is_empty() {
                            crate::pmap::Map::new()
                        } else {
                            crate::decl_subst::make_locl(&td.tparams, ty_args)
                        },
                        ..empty_expand_env()
                    };
                    let (_ty_err_opt, variants) =
                        typing_utils::localize_disjoint_union(&ety_env, env, &single_or_union);
                    let tyl = match get_node(&variants) {
                        Ty_::Tunion(tyl) => tyl.clone(),
                        _ => vec![variants],
                    };
                    Some(tyl)
                }
            }
            TypedefTypeAssignment::SimpleTypeDef(..) => None,
        },
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    }
}
