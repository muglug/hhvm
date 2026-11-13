// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_refinement.ml`. See `hh/PORTING.md`.
//!
//! # Modules and types
//!
//! - `TyPredicate` is [`ty_predicate`], `Uninstantiated_typing_logic` (`UTL`)
//!   [`uninstantiated_typing_logic`], `TyPartition` [`ty_partition`] (its
//!   `Partition`, `Partition.Make` of locl types, is `ty_partition::Partition`).
//! - The record `ty_partition` is [`TyPartition`], `dnf_ty` [`DnfTy`].
//!
//! # Shadowed definitions
//!
//! `TyPredicate.of_ty` and `TyPredicate.to_ty` are defined twice (a recursive
//! one, then the one of the `.mli`, which applies it), and so is
//! `TyPartition.assume`. The first ones are in the private modules
//! `ty_predicate::with_next_wildcard_id`, `ty_predicate::with_lookup_wildcard`
//! and `ty_partition::with_base_ty`.
//!
//! # The environment
//!
//! `TyPredicate.of_ty`, `TyPredicate.to_ty`, `instantiate_prop` and
//! `passes_predicate` take an environment and do not return one: they take
//! `&Env`, and work on a copy where the OCaml goes on with an environment that
//! it then drops (`strip_supportdyn`, `get_newtype_super`, `partition_ty`).
//!
//! The private functions `split_*` keep the order of the OCaml parameters,
//! labelled ones included (the environment is not first in most of them).

use naming_special_names_rust as sn;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::Tprim;
use oxidized::typechecker_options::TypecheckerOptions;

use crate::decl_entry;
use crate::partition;
use crate::tvid;
/// `module DataType = Typing_atomic_data_types`
use crate::typing_atomic_data_types as data_type;
use crate::typing_atomic_data_types::AtomicTy;
use crate::typing_case_type_variant;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::TypedefCaseTypeVariant;
use crate::typing_defs::TypedefTypeAssignment;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::DeclTparam;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::DeclWhereConstraint;
use crate::typing_defs_core::ShapeFieldPredicate;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapePredicate;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TuplePredicate;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypePredicate;
use crate::typing_defs_core::TypePredicate_;
use crate::typing_defs_core::TypeTag;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::show_type_predicate_;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_log;
use crate::typing_log::LogStructure;
use crate::typing_logic;
use crate::typing_make_type as make_type;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_set;
use crate::typing_utils;
use crate::typing_utils::NormalizeShapeTypeResult;

/// `S_set.t`
type SSet = crate::s_set::T;

// ---------------------------------------------------------------------------
// What the port needs from other modules
// ---------------------------------------------------------------------------

/// `Decl_subst.make_locl`, for localized types.
///
/// `crate::decl_subst::make_locl` maps the names to
/// `oxidized::typing_defs_core::Ty`, which has no inferred types (PORTING.md:
/// never use it for one); this is the same function for [`Ty`].
fn decl_subst_make_locl(tparams: &[DeclTparam], tyl: &[Ty]) -> crate::pmap::Map<String, Ty> {
    let mut subst = crate::pmap::Map::new();
    let mut tyl = tyl;
    for t in tparams {
        match tyl {
            [] => {}
            [ty, rl @ ..] => {
                subst.insert(t.name.id_ref().as_str().to_string(), ty.clone());
                tyl = rl;
            }
        }
    }
    subst
}

/// `Typechecker_options.pessimise_builtins`, which `crate::typechecker_options`
/// does not have: `everything_sdt t || t.tco_pessimise_builtins`.
fn typechecker_options_pessimise_builtins(t: &TypecheckerOptions) -> bool {
    t.po.everything_sdt || t.tco_pessimise_builtins
}

/// `List.zip_exn` (Base): raises `Invalid_argument` when the lengths differ.
fn list_zip_exn<'a, A, B>(l1: &'a [A], l2: &'a [B]) -> Vec<(&'a A, &'a B)> {
    if l1.len() != l2.len() {
        panic!(
            "Invalid_argument: length mismatch in zip_exn: {} <> {}",
            l1.len(),
            l2.len()
        )
    }
    l1.iter().zip(l2.iter()).collect()
}

/// `Typing_print.subtype_prop`, which `crate::typing_print` does not have
/// (as in `crate::typing_log`).
fn typing_print_subtype_prop(env: &Env, prop: &typing_logic::SubtypeProp) -> String {
    use typing_logic::SubtypeProp;
    fn subtype_prop(env: &Env, prop: &SubtypeProp) -> String {
        match prop {
            SubtypeProp::Conj(ps) if ps.is_empty() => "TRUE".to_string(),
            SubtypeProp::Conj(ps) => {
                "(".to_string()
                    + &ps
                        .iter()
                        .map(|p| subtype_prop(env, p))
                        .collect::<Vec<String>>()
                        .join(" && ")
                    + ")"
            }
            SubtypeProp::Disj(_, ps) if ps.is_empty() => "FALSE".to_string(),
            SubtypeProp::Disj(_, ps) => {
                "(".to_string()
                    + &ps
                        .iter()
                        .map(|p| subtype_prop(env, p))
                        .collect::<Vec<String>>()
                        .join(" || ")
                    + ")"
            }
            SubtypeProp::IsSubtype(false, ty1, ty2) => {
                typing_print::debug_i(env, ty1) + " <: " + &typing_print::debug_i(env, ty2)
            }
            SubtypeProp::IsSubtype(true, ty1, ty2) => {
                typing_print::debug_i(env, ty1) + " <D: " + &typing_print::debug_i(env, ty2)
            }
            SubtypeProp::AmbiguousShapeSplat(vars) => {
                "ambiguous_shape_splat(".to_string()
                    + &vars
                        .iter()
                        .map(|v| tvid::show(*v))
                        .collect::<Vec<String>>()
                        .join(", ")
                    + ")"
            }
        }
    }
    let p_str = subtype_prop(env, prop);
    p_str
}

// ---------------------------------------------------------------------------

/// given [a..z]
/// return [(a, [b..z]); (b, [a;c..z]); (c, [a..b;d..z]); ... (z, [b..z])]
/// i.e. map each element in the input to a pair of that element and the other
///  elements of the input
fn list_to_list_of_e_and_others<A: Clone>(xs: &[A]) -> Vec<(A, Vec<A>)> {
    fn helper<A: Clone>(prefix: Vec<A>, rest: &[A]) -> Vec<(A, Vec<A>)> {
        match rest {
            [h, tail @ ..] => {
                let others: Vec<A> = prefix.iter().chain(tail.iter()).cloned().collect();
                let mut next_prefix = prefix;
                next_prefix.push(h.clone());
                let mut res = vec![(h.clone(), others)];
                res.extend(helper(next_prefix, tail));
                res
            }
            [] => vec![],
        }
    }
    helper(vec![], xs)
}

/// Under pessimise_builtins, the hint Enum is localized as ~Enum & arraykey
/// to account for intish string cast. This function matches this intersection
/// to extract the Enum
fn match_pessimized_enum_intersection(env: &Env, tys: &[Ty]) -> Option<String> {
    let enum_name = |ty: &Ty| match get_node(ty) {
        Ty_::Tnewtype(name, args, _)
            if args.is_empty()
                && typing_env::is_enum(env, name)
                && !typing_env::is_enum_class(env, name) =>
        {
            Some(name.clone())
        }
        _ => None,
    };
    let enum_name_from_like = |ty: &Ty| match get_node(ty) {
        Ty_::Tunion(tyl) => match tyl.as_slice() {
            [dyn_, enum_] if typing_defs::is_dynamic(dyn_) => enum_name(enum_),
            [enum_, dyn_] if typing_defs::is_dynamic(dyn_) => enum_name(enum_),
            _ => None,
        },
        _ => None,
    };
    match tys {
        [t1, t2] if typing_defs::is_arraykey(t1) => enum_name_from_like(t2),
        [t1, t2] if typing_defs::is_arraykey(t2) => enum_name_from_like(t1),
        _ => None,
    }
}

/// `module TyPredicate`
pub mod ty_predicate {
    use naming_special_names_rust as sn;
    use oxidized::aast;
    use oxidized::pos::Pos;

    use super::list_zip_exn;
    use crate::decl_entry;
    use crate::diagnostics_state;
    use crate::folded_class as cls;
    use crate::i_map;
    use crate::telemetry;
    use crate::typing_defs;
    use crate::typing_defs::ExpandEnv;
    use crate::typing_defs::attributes;
    use crate::typing_defs::empty_expand_env;
    use crate::typing_defs_core::DeclTparam;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::TypePredicate;
    use crate::typing_defs_core::TypeTag;
    use crate::typing_defs_core::TypeTagGeneric;
    use crate::typing_env;
    use crate::typing_env_types::Env;
    use crate::typing_error::reasons_callback;
    use crate::typing_error_utils;
    use crate::typing_make_type as make_type;
    use crate::typing_reason;
    use crate::typing_reason::T as Reason;
    use crate::typing_utils;

    fn is_runtime_checkable_generic(env: &Env, name: &str) -> bool {
        (!typing_env::is_fresh_generic_parameter(name))
            && ((match typing_env::get_reified(env, name) {
                aast::ReifyKind::Reified => true,
                aast::ReifyKind::SoftReified | aast::ReifyKind::Erased => false,
            }) || typing_env::get_enforceable(env, name)
                || typing_defs::dependent_kind::is_generic_dep_ty(name))
    }

    /// Recognize the [dynamic] half and the [this] half of a localized [~this].
    /// [dyn_ty] must be a [Tdynamic _] and [this_ty] must be the runtime-checkable
    /// [Tgeneric "this"] (i.e. it would already produce a [GenericTag] predicate
    /// with [name = "this"] on its own).
    fn is_like_this(env: &Env, dyn_ty: &Ty, this_ty: &Ty) -> bool {
        use crate::typing_defs_core::Ty_;
        use crate::typing_defs_core::get_node;
        match (get_node(dyn_ty), get_node(this_ty)) {
            (Ty_::Tdynamic(_), Ty_::Tgeneric(name)) => {
                name == sn::typehints::THIS && is_runtime_checkable_generic(env, name)
            }
            _ => false,
        }
    }

    /// The first `of_ty`, which the one of the `.mli` shadows.
    mod with_next_wildcard_id {
        use naming_special_names_rust as sn;
        use oxidized::ast_defs::Tprim;

        use super::super::match_pessimized_enum_intersection;
        use super::is_like_this;
        use super::is_runtime_checkable_generic;
        use crate::decl_entry;
        use crate::folded_class as cls;
        use crate::typing_defs;
        use crate::typing_defs_core::Exact;
        use crate::typing_defs_core::ShapeFieldPredicate;
        use crate::typing_defs_core::ShapePredicate;
        use crate::typing_defs_core::ShapeType;
        use crate::typing_defs_core::ShapeTypeSimple;
        use crate::typing_defs_core::TupleExtra;
        use crate::typing_defs_core::TuplePredicate;
        use crate::typing_defs_core::TupleType;
        use crate::typing_defs_core::Ty;
        use crate::typing_defs_core::Ty_;
        use crate::typing_defs_core::TypePredicate;
        use crate::typing_defs_core::TypePredicate_;
        use crate::typing_defs_core::TypeTag;
        use crate::typing_defs_core::TypeTagGeneric;
        use crate::typing_defs_core::get_node;
        use crate::typing_defs_core::get_reason;
        use crate::typing_defs_core::t_shape_map::TShapeField;
        use crate::typing_defs_core::ty_equal;
        use crate::typing_env;
        use crate::typing_env_types::Env;
        use crate::typing_make_type as make_type;
        use crate::typing_reason;
        use crate::typing_utils;

        pub(super) fn of_ty(
            env: &Env,
            next_wildcard_id: isize,
            ty: &Ty,
        ) -> Result<(isize, TypePredicate), String> {
            use TypePredicate_::*;
            use TypeTag::*;
            // The environment `strip_supportdyn` returns is the one of the
            // rest of the function; it is then dropped.
            let mut env = env.clone();
            let (_is_supportdyn, ty) = typing_utils::strip_supportdyn(&mut env, ty.clone());
            let env = &env;
            let res: Result<(isize, TypePredicate_), String> = match get_node(&ty) {
                Ty_::Tprim(Tprim::Tbool) => Ok((next_wildcard_id, IsTag(BoolTag))),
                Ty_::Tprim(Tprim::Tint) => Ok((next_wildcard_id, IsTag(IntTag))),
                Ty_::Tprim(Tprim::Tarraykey) => Ok((next_wildcard_id, IsTag(ArraykeyTag))),
                Ty_::Tprim(Tprim::Tfloat) => Ok((next_wildcard_id, IsTag(FloatTag))),
                Ty_::Tprim(Tprim::Tnum) => Ok((next_wildcard_id, IsTag(NumTag))),
                Ty_::Tprim(Tprim::Tresource) => Ok((next_wildcard_id, IsTag(ResourceTag))),
                Ty_::Tprim(Tprim::Tnull) => Ok((next_wildcard_id, IsTag(NullTag))),
                // TODO: optional and variadic fields T201398626 T201398652
                Ty_::Ttuple(TupleType {
                    required: t_required,
                    optional: t_optional,
                    extra: TupleExtra::Tvariadic(t_variadic),
                }) if t_optional.is_empty() && typing_defs::is_nothing(t_variadic) => {
                    // `List.fold_left` with `let*` on the accumulator: once
                    // it is an error, the rest of the elements are not
                    // looked at. (The OCaml conses the predicates and
                    // reverses them at the end.)
                    let mut acc: Result<(isize, Vec<TypePredicate>), String> =
                        Ok((next_wildcard_id, vec![]));
                    for ty in t_required {
                        let (next_wildcard_id, mut predicates) = match acc {
                            Ok(acc) => acc,
                            Err(_) => break,
                        };
                        acc = match of_ty(env, next_wildcard_id, ty) {
                            Err(err) => Err(err),
                            Ok((next_wildcard_id, predicate)) => {
                                predicates.push(predicate);
                                Ok((next_wildcard_id, predicates))
                            }
                        };
                    }
                    match acc {
                        Err(err) => Err("tuple-".to_string() + &err),
                        Ok((next_wildcard_id, predicates)) => Ok((
                            next_wildcard_id,
                            IsTupleOf(TuplePredicate {
                                required: predicates,
                            }),
                        )),
                    }
                }
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    unknown_value: s_unknown_value,
                    fields: s_fields,
                })) => {
                    // `TShapeMap.fold`: in increasing order of the keys; once
                    // the accumulator is an error, the rest of the fields are
                    // not looked at.
                    let mut acc: Result<(isize, Vec<(TShapeField, ShapeFieldPredicate)>), String> =
                        Ok((next_wildcard_id, vec![]));
                    for (key, s_field) in s_fields {
                        let sfp_optional = s_field.optional;
                        acc = match acc {
                            Err(err) => Err(err),
                            Ok((next_wildcard_id, mut sf_predicates)) => {
                                match of_ty(env, next_wildcard_id, &s_field.ty) {
                                    Err(err) => Err(err),
                                    Ok((next_wildcard_id, sfp_predicate)) => {
                                        sf_predicates.push((
                                            key.clone(),
                                            ShapeFieldPredicate {
                                                optional: sfp_optional,
                                                predicate: sfp_predicate,
                                            },
                                        ));
                                        Ok((next_wildcard_id, sf_predicates))
                                    }
                                }
                            }
                        };
                    }
                    match acc {
                        Err(err) => Err("shape-".to_string() + &err),
                        Ok((next_wildcard_id, elts)) => {
                            let result_is_open = if
                            // this type comes from localizing a hint so a closed shape should have
                            // the canonical form of the nothing type
                            typing_defs::is_nothing(s_unknown_value) {
                                Ok(false)
                            } else if ty_equal(
                                None,
                                s_unknown_value,
                                &make_type::mixed(typing_reason::none()),
                            ) || ty_equal(
                                None,
                                s_unknown_value,
                                &make_type::supportdyn(
                                    typing_reason::none(),
                                    make_type::mixed(typing_reason::none()),
                                ),
                            ) {
                                Ok(true)
                            } else {
                                Err("unexpected s_unknown_value".to_string())
                            };
                            result_is_open.map(|sp_allows_unknown_fields| {
                                (
                                    next_wildcard_id,
                                    IsShapeOf(ShapePredicate {
                                        allows_unknown_fields: sp_allows_unknown_fields,
                                        // `TShapeMap.of_list elts`
                                        fields: elts.into_iter().collect(),
                                    }),
                                )
                            })
                        }
                    }
                }
                Ty_::Tshape(ShapeType::ShapeSplat(_)) => Err("shape_splat".to_string()),
                Ty_::Tclass(_, Exact::Exact, _) => Err("exact class".to_string()),
                Ty_::Tclass((_, name), Exact::Nonexact(_), args) => {
                    // `List.map_env next_wildcard_id args`
                    let mut next_wildcard_id = next_wildcard_id;
                    let generics: Vec<TypeTagGeneric> = args
                        .iter()
                        .map(|ty| match get_node(ty) {
                            Ty_::Tgeneric(name) if typing_env::is_fresh_generic_parameter(name) => {
                                let generic = TypeTagGeneric::Wildcard(next_wildcard_id);
                                next_wildcard_id += 1;
                                generic
                            }
                            _ => TypeTagGeneric::Filled(ty.clone()),
                        })
                        .collect();
                    let (next_wildcard_id, generics) = match typing_env::get_class(env, name) {
                        decl_entry::T::Found(class_info) => {
                            let tparams = cls::tparams(&class_info);
                            let pad_len = tparams.len() as isize - generics.len() as isize;
                            if pad_len > 0 {
                                // if the class's type arguments are underspecified, we need to
                                // fill them in so that when we zip them with the tparams later,
                                // the count matches up
                                let pad_generics: Vec<TypeTagGeneric> = (0..pad_len)
                                    .map(|i| TypeTagGeneric::Wildcard(i + next_wildcard_id))
                                    .collect();
                                let next_wildcard_id = next_wildcard_id + pad_len;
                                let mut generics = generics;
                                generics.extend(pad_generics);
                                (next_wildcard_id, generics)
                            } else {
                                // ignore excess type arguments if the class is known;
                                // if Tclass comes from a localized hint (as is the case for is/as)
                                // then this pruning should already happen, but just in case
                                let mut generics = generics;
                                generics.truncate(tparams.len());
                                (next_wildcard_id, generics)
                            }
                        }
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                            (next_wildcard_id, generics)
                        }
                    };
                    Ok((next_wildcard_id, IsTag(ClassTag(name.clone(), generics))))
                }
                Ty_::Tprim(Tprim::Tvoid) => Err("void".to_string()),
                Ty_::Tprim(Tprim::Tnoreturn) => Err("noreturn".to_string()),
                Ty_::Tnonnull => Ok((
                    next_wildcard_id,
                    IsNot(Box::new(TypePredicate(
                        get_reason(&ty).clone(),
                        IsTag(NullTag),
                    ))),
                )),
                Ty_::Tdynamic(_) => Err("dynamic".to_string()),
                Ty_::Tany(_) => Err("any".to_string()),
                Ty_::Toption(ty_opt) => {
                    // In the OCaml, `|> Result.map_error ~f:(fun err -> "option-" ^ err)`
                    // is inside the body of the `let*` (which extends as far
                    // right as it can), so it applies to the `return` only,
                    // which never fails: an error of the inner `of_ty` is
                    // returned without the "option-" prefix.
                    match of_ty(env, next_wildcard_id, ty_opt) {
                        Err(err) => Err(err),
                        Ok((next_wildcard_id, pred_opt)) => {
                            let pred_null = TypePredicate(get_reason(&ty).clone(), IsTag(NullTag));
                            Ok((next_wildcard_id, IsUnionOf(vec![pred_opt, pred_null])))
                                .map_err(|err: String| "option-".to_string() + &err)
                        }
                    }
                }
                Ty_::Tfun(_) => Err("fun".to_string()),
                Ty_::Tgeneric(name) if is_runtime_checkable_generic(env, name) => Ok((
                    next_wildcard_id,
                    IsTag(GenericTag {
                        name: name.clone(),
                        from_like: false,
                    }),
                )),
                Ty_::Tgeneric(_) => Err("generic".to_string()),
                Ty_::Tunion(tyl)
                    if tyl.len() == 2
                        && (is_like_this(env, &tyl[0], &tyl[1])
                            || is_like_this(env, &tyl[1], &tyl[0])) =>
                {
                    // Recognize [Tunion [dynamic; this]] (in either order) and treat it
                    // as the [this] predicate, tagged so that [to_ty] can reconstruct
                    // the [~this] form. This is the localized shape of an [is ~this]
                    // refinement produced for non-final/generic classes under Sound
                    // Dynamic; see [Typing_phase.localize] [Tthis] arm.
                    Ok((
                        next_wildcard_id,
                        IsTag(GenericTag {
                            name: sn::typehints::THIS.to_string(),
                            from_like: true,
                        }),
                    ))
                }
                Ty_::Tunion(tys) => {
                    // `List.fold_result`: stops at the first error. (The
                    // OCaml conses the predicates and reverses them at the
                    // end.)
                    let mut acc: Result<(isize, Vec<TypePredicate>), String> =
                        Ok((next_wildcard_id, vec![]));
                    for ty in tys {
                        let (next_wildcard_id, mut predicates) = match acc {
                            Ok(acc) => acc,
                            Err(_) => break,
                        };
                        acc = match of_ty(env, next_wildcard_id, ty) {
                            Err(err) => Err(err),
                            Ok((next_wildcard_id, predicate)) => {
                                predicates.push(predicate);
                                Ok((next_wildcard_id, predicates))
                            }
                        };
                    }
                    match acc {
                        Err(err) => Err("union-".to_string() + &err),
                        Ok((next_wildcard_id, predicates)) => {
                            Ok((next_wildcard_id, IsUnionOf(predicates)))
                        }
                    }
                }
                Ty_::Tintersection(tys) => match match_pessimized_enum_intersection(env, tys) {
                    Some(name) => Ok((next_wildcard_id, IsTag(EnumTag(name)))),
                    None => Err("intersection".to_string()),
                },
                Ty_::TvecOrDict(tk, tv) => {
                    let r = get_reason(&ty).clone();
                    let union = make_type::union(
                        r.clone(),
                        vec![
                            make_type::vec(r.clone(), tv.clone()),
                            make_type::dict(r, tk.clone(), tv.clone()),
                        ],
                    );
                    of_ty(env, next_wildcard_id, &union).map(
                        |(next_wildcard_id, TypePredicate(_reason, predicate_))| {
                            (next_wildcard_id, predicate_)
                        },
                    )
                }
                Ty_::Taccess(_) => Err("access".to_string()),
                Ty_::Tvar(_) => Err("tvar".to_string()),
                Ty_::Tnewtype(name, args, _)
                    if args.is_empty()
                        && typing_env::is_enum(env, name)
                        && !typing_env::is_enum_class(env, name) =>
                {
                    Ok((next_wildcard_id, IsTag(EnumTag(name.clone()))))
                }
                Ty_::Tnewtype(s, _, _) => Err("newtype-".to_string() + s),
                Ty_::Tdependent(..) => Err("dependent".to_string()),
                Ty_::Tneg(_) => Err("neg".to_string()),
                Ty_::Tlabel(_) => Err("label".to_string()),
                Ty_::Ttuple(_) => Err("tuple".to_string()),
                Ty_::TclassPtr(_) => Err("class_ptr".to_string()),
            };
            res.map(|(next_wildcard_id, pred_)| {
                (
                    next_wildcard_id,
                    TypePredicate(get_reason(&ty).clone(), pred_),
                )
            })
        }
    }

    pub fn of_ty(env: &Env, ty: &Ty) -> Result<TypePredicate, String> {
        with_next_wildcard_id::of_ty(env, 0, ty).map(|(_next_wildcard_id, ty)| ty)
    }

    fn instantiate_wildcards_for_tag(
        env: &mut Env,
        reason: &Reason,
        tag: &TypeTag,
        p: &Pos,
    ) -> i_map::T<((DeclTparam, String), Ty)> {
        match tag {
            TypeTag::BoolTag
            | TypeTag::IntTag
            | TypeTag::ArraykeyTag
            | TypeTag::FloatTag
            | TypeTag::NumTag
            | TypeTag::ResourceTag
            | TypeTag::NullTag
            | TypeTag::EnumTag(_)
            | TypeTag::GenericTag { .. } => i_map::T::new(),
            TypeTag::ClassTag(id, generics) => {
                let new_tparams = match typing_env::get_class(env, id) {
                    decl_entry::T::Found(class_info) => {
                        let tparams = cls::tparams(&class_info);
                        // if we're only getting ClassTag predicates by calling of_ty on
                        // Tclass localized from is/as hints, then the count should match
                        // since localization will trim excess arguments and of_ty should
                        // fill in when there are too few arguments;
                        // we shouldn't be creating ClassTag just anywhere, so we should
                        // fail when something is unexpected
                        let tparam_generic_pairs = list_zip_exn(&tparams, generics);
                        // (The OCaml conses the types and reverses them at the
                        // end.)
                        let mut tyl: Vec<Ty> = vec![];
                        let mut new_tparams: i_map::T<((DeclTparam, String), Ty)> = i_map::T::new();
                        for (tparam, generic) in tparam_generic_pairs {
                            match generic {
                                TypeTagGeneric::Filled(ty) => tyl.push(ty.clone()),
                                TypeTagGeneric::Wildcard(wildcard_key) => {
                                    let tparam_name = tparam.name.id_ref().as_str();
                                    let reified = tparam.reified;
                                    let tp_user_attributes = &tparam.user_attributes[..];
                                    let enforceable = attributes::mem(
                                        sn::user_attributes::ENFORCEABLE,
                                        tp_user_attributes,
                                    );
                                    let newable = attributes::mem(
                                        sn::user_attributes::NEWABLE,
                                        tp_user_attributes,
                                    );
                                    let new_name = typing_env::add_fresh_generic_parameter(
                                        env,
                                        typing_reason::to_pos(reason),
                                        tparam_name,
                                        reified,
                                        enforceable,
                                        newable,
                                    );
                                    let ty = make_type::generic(reason.clone(), new_name.clone());
                                    let new_tparam = ((tparam.clone(), new_name), ty.clone());
                                    tyl.push(ty);
                                    new_tparams.insert(*wildcard_key, new_tparam);
                                }
                            }
                        }
                        let ety_env = ExpandEnv {
                            substs: super::decl_subst_make_locl(&tparams, &tyl),
                            this_ty: make_type::class_type(reason.clone(), id.clone(), tyl.clone()),
                            ..empty_expand_env()
                        };
                        let add_bounds = |env: &mut Env, (t, ty_fresh): (&DeclTparam, &Ty)| {
                            for (ck, ty) in t.constraints.iter() {
                                // Substitute fresh type parameters for
                                // original formals in constraint
                                let (ty_err_opt, ty) = typing_utils::localize(&ety_env, env, ty);
                                if let Some(ty_err) = ty_err_opt {
                                    typing_error_utils::add_typing_error(&ty_err, env);
                                }
                                typing_utils::add_constraint(
                                    env,
                                    *ck,
                                    ty_fresh.clone(),
                                    ty,
                                    Some(reasons_callback::unify_error_at(p.clone())),
                                );
                            }
                        };
                        for pair in list_zip_exn(&tparams, &tyl) {
                            add_bounds(env, pair);
                        }
                        new_tparams
                    }
                    decl_entry::T::NotYetAvailable | decl_entry::T::DoesNotExist => i_map::T::new(),
                };
                new_tparams
            }
        }
    }

    pub fn instantiate_wildcards_for_predicate(
        env: &mut Env,
        predicate: &TypePredicate,
        p: &Pos,
    ) -> i_map::T<((DeclTparam, String), Ty)> {
        use crate::typing_defs_core::ShapeFieldPredicate;
        use crate::typing_defs_core::ShapePredicate;
        use crate::typing_defs_core::TuplePredicate;
        use crate::typing_defs_core::TypePredicate_::*;
        match predicate {
            TypePredicate(reason, IsTag(tag)) => {
                let new_tparams = instantiate_wildcards_for_tag(env, reason, tag, p);
                new_tparams
            }
            TypePredicate(
                _reason,
                IsTupleOf(TuplePredicate {
                    required: tp_required,
                }),
            ) => {
                let new_tparams: Vec<i_map::T<((DeclTparam, String), Ty)>> = tp_required
                    .iter()
                    .map(|predicate| {
                        let new_tparams = instantiate_wildcards_for_predicate(env, predicate, p);
                        new_tparams
                    })
                    .collect();
                // `List.fold new_tparams ~init:I_map.empty ~f:I_map.union`
                new_tparams
                    .iter()
                    .fold(i_map::T::new(), |acc, m| i_map::union(None, &acc, m))
            }
            TypePredicate(
                _reason,
                IsShapeOf(ShapePredicate {
                    fields: sp_fields,
                    allows_unknown_fields: _,
                }),
            ) => {
                // `TShapeMap.fold_env`: in increasing order of the keys
                let mut new_tparams_acc = i_map::T::new();
                for (
                    _key,
                    ShapeFieldPredicate {
                        predicate: sfp_predicate,
                        optional: _,
                    },
                ) in sp_fields
                {
                    let new_tparams = instantiate_wildcards_for_predicate(env, sfp_predicate, p);
                    new_tparams_acc = i_map::union(None, &new_tparams_acc, &new_tparams);
                }
                new_tparams_acc
            }
            TypePredicate(_reason, IsUnionOf(predicates)) => {
                let new_tparams: Vec<i_map::T<((DeclTparam, String), Ty)>> = predicates
                    .iter()
                    .map(|predicate| {
                        let new_tparams = instantiate_wildcards_for_predicate(env, predicate, p);
                        new_tparams
                    })
                    .collect();
                new_tparams
                    .iter()
                    .fold(i_map::T::new(), |acc, m| i_map::union(None, &acc, m))
            }
            TypePredicate(_reason, IsNot(inner)) => {
                instantiate_wildcards_for_predicate(env, inner, p)
            }
        }
    }

    /// `exception FoundWildcard`
    struct FoundWildcard;

    /// The first `to_ty`, which the one of the `.mli` shadows. `lookup_wildcard`
    /// raises [`FoundWildcard`] in `to_ty_without_instantiation_opt`: here it
    /// returns it, and so does `to_ty`.
    mod with_lookup_wildcard {
        use super::FoundWildcard;
        use crate::typing_defs_core::ShapeFieldPredicate;
        use crate::typing_defs_core::ShapeFieldType;
        use crate::typing_defs_core::ShapePredicate;
        use crate::typing_defs_core::TupleExtra;
        use crate::typing_defs_core::TuplePredicate;
        use crate::typing_defs_core::TupleType;
        use crate::typing_defs_core::Ty;
        use crate::typing_defs_core::Ty_;
        use crate::typing_defs_core::TypePredicate;
        use crate::typing_defs_core::TypePredicate_;
        use crate::typing_defs_core::TypeTag;
        use crate::typing_defs_core::TypeTagGeneric;
        use crate::typing_defs_core::mk;
        use crate::typing_defs_core::t_shape_map::TShapeMap;
        use crate::typing_env;
        use crate::typing_env_types::Env;
        use crate::typing_make_type as make_type;
        use crate::typing_reason::T as Reason;
        use crate::typing_utils;

        pub(super) type LookupWildcard<'a> = &'a mut dyn FnMut(isize) -> Result<Ty, FoundWildcard>;

        fn tag_to_ty(
            env: &Env,
            lookup_wildcard: LookupWildcard<'_>,
            reason: &Reason,
            tag: &TypeTag,
        ) -> Result<Ty, FoundWildcard> {
            Ok(match tag {
                TypeTag::BoolTag => make_type::bool(reason.clone()),
                TypeTag::IntTag => make_type::int(reason.clone()),
                TypeTag::ArraykeyTag => make_type::arraykey(reason.clone()),
                TypeTag::FloatTag => make_type::float(reason.clone()),
                TypeTag::NumTag => make_type::num(reason.clone()),
                TypeTag::ResourceTag => make_type::resource(reason.clone()),
                TypeTag::NullTag => make_type::null(reason.clone()),
                TypeTag::ClassTag(id, generics) => {
                    // `List.map`: from left to right
                    let mut tyargs = Vec::with_capacity(generics.len());
                    for g in generics {
                        tyargs.push(match g {
                            TypeTagGeneric::Filled(ty) => ty.clone(),
                            TypeTagGeneric::Wildcard(key) => lookup_wildcard(*key)?,
                        });
                    }
                    make_type::class_type(reason.clone(), id.clone(), tyargs)
                }
                TypeTag::EnumTag(id) => {
                    // The environment `get_newtype_super` returns is dropped.
                    let cstr =
                        typing_utils::get_newtype_super(&mut env.clone(), reason.clone(), id, &[]);
                    let enum_ty = mk((reason.clone(), Ty_::Tnewtype(id.clone(), vec![], cstr)));
                    if super::super::typechecker_options_pessimise_builtins(&typing_env::get_tcopt(
                        env,
                    )) {
                        // Mirror localization of E to ~E & arraykey
                        make_type::intersection(
                            reason.clone(),
                            vec![
                                make_type::locl_like(reason.clone(), enum_ty),
                                make_type::arraykey(reason.clone()),
                            ],
                        )
                    } else {
                        enum_ty
                    }
                }
                TypeTag::GenericTag {
                    name,
                    from_like: false,
                } => make_type::generic(reason.clone(), name.clone()),
                TypeTag::GenericTag {
                    name,
                    from_like: true,
                } => {
                    // Reconstruct the [~this] form that [of_ty] collapsed into this tag.
                    make_type::locl_like(
                        reason.clone(),
                        make_type::generic(reason.clone(), name.clone()),
                    )
                }
            })
        }

        pub(super) fn to_ty(
            env: &Env,
            lookup_wildcard: LookupWildcard<'_>,
            predicate: &TypePredicate,
        ) -> Result<Ty, FoundWildcard> {
            match predicate {
                TypePredicate(reason, TypePredicate_::IsTag(tag)) => {
                    tag_to_ty(env, lookup_wildcard, reason, tag)
                }
                TypePredicate(
                    reason,
                    TypePredicate_::IsTupleOf(TuplePredicate {
                        required: tp_required,
                    }),
                ) => {
                    let mut t_required = Vec::with_capacity(tp_required.len());
                    for p in tp_required {
                        t_required.push(to_ty(env, &mut *lookup_wildcard, p)?);
                    }
                    Ok(mk((
                        reason.clone(),
                        Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: vec![],
                            extra: TupleExtra::Tvariadic(make_type::nothing(reason.clone())),
                        }),
                    )))
                }
                TypePredicate(
                    reason,
                    TypePredicate_::IsShapeOf(ShapePredicate {
                        fields: sp_fields,
                        allows_unknown_fields: sp_allows_unknown_fields,
                    }),
                ) => {
                    // `TShapeMap.map`: in increasing order of the keys
                    let mut map = TShapeMap::new();
                    for (
                        key,
                        ShapeFieldPredicate {
                            predicate: sfp_predicate,
                            optional: sfp_optional,
                        },
                    ) in sp_fields
                    {
                        let sft_ty = to_ty(env, &mut *lookup_wildcard, sfp_predicate)?;
                        map.insert(
                            key.clone(),
                            ShapeFieldType {
                                optional: *sfp_optional,
                                ty: sft_ty,
                            },
                        );
                    }
                    let kind = if *sp_allows_unknown_fields {
                        // open shape predicates from hints always have supportdyn kinds
                        // https://fburl.com/code/aguo2c7i
                        make_type::supportdyn_mixed(reason.clone())
                    } else {
                        make_type::nothing(reason.clone())
                    };
                    Ok(make_type::shape(reason.clone(), kind, map))
                }
                TypePredicate(reason, TypePredicate_::IsUnionOf(predicates)) => {
                    let (nulls, others): (Vec<&TypePredicate>, Vec<&TypePredicate>) =
                        predicates.iter().partition(|p| {
                            matches!(p, TypePredicate(_, TypePredicate_::IsTag(TypeTag::NullTag)))
                        });
                    match (nulls.as_slice(), others.as_slice()) {
                        ([_, ..], [other]) => {
                            let ty = to_ty(env, lookup_wildcard, other)?;
                            Ok(make_type::nullable(reason.clone(), ty))
                        }
                        ([_, ..], others) => {
                            let mut tyl = Vec::with_capacity(others.len());
                            for p in others {
                                tyl.push(to_ty(env, &mut *lookup_wildcard, p)?);
                            }
                            Ok(make_type::nullable(
                                reason.clone(),
                                make_type::union(reason.clone(), tyl),
                            ))
                        }
                        ([], _) => {
                            let mut tyl = Vec::with_capacity(predicates.len());
                            for p in predicates {
                                tyl.push(to_ty(env, &mut *lookup_wildcard, p)?);
                            }
                            Ok(make_type::union(reason.clone(), tyl))
                        }
                    }
                }
                TypePredicate(reason, TypePredicate_::IsNot(inner)) => {
                    Ok(make_type::neg(reason.clone(), (**inner).clone()))
                }
            }
        }
    }

    pub fn to_ty_without_instantiation_opt(env: &Env, predicate: &TypePredicate) -> Option<Ty> {
        match with_lookup_wildcard::to_ty(env, &mut |_key| Err(FoundWildcard), predicate) {
            Ok(ty) => Some(ty),
            Err(FoundWildcard) => None,
        }
    }

    pub fn to_ty(
        env: &Env,
        instantiation_map: &i_map::T<Ty>,
        p: &Pos,
        predicate: &TypePredicate,
    ) -> Ty {
        let res = with_lookup_wildcard::to_ty(
            env,
            &mut |key| match instantiation_map.get(&key) {
                Some(ty) => Ok(ty.clone()),
                None => {
                    diagnostics_state::invariant_violation(
                        p.clone(),
                        telemetry::create(),
                        "Unexpected failure to instantiate type from predicate",
                        true,
                    );
                    Ok(make_type::nothing(typing_reason::none()))
                }
            },
            predicate,
        );
        match res {
            Ok(ty) => ty,
            // The lookup above never fails.
            Err(FoundWildcard) => unreachable!(),
        }
    }
}

/// `module Uninstantiated_typing_logic`
pub mod uninstantiated_typing_logic {
    use std::rc::Rc;

    use oxidized::pos::Pos;

    use super::ty_predicate;
    use super::typing_print_subtype_prop;
    use crate::diagnostics_state;
    use crate::i_map;
    use crate::telemetry;
    use crate::typing_defs_constraints::InternalType;
    use crate::typing_defs_core::ClassRefinement;
    use crate::typing_defs_core::Exact;
    use crate::typing_defs_core::PosId;
    use crate::typing_defs_core::RefinedConst;
    use crate::typing_defs_core::RefinedConstBound;
    use crate::typing_defs_core::RefinedConstBounds;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::TypePredicate;
    use crate::typing_defs_core::TypePredicate_;
    use crate::typing_defs_core::TypeTag;
    use crate::typing_defs_core::TypeTagGeneric;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::get_reason;
    use crate::typing_defs_core::mk;
    use crate::typing_defs_core::show_type_predicate_;
    use crate::typing_env_types::Env;
    use crate::typing_logic;
    use crate::typing_print;
    use crate::typing_reason::T as Reason;

    /// `type is_subtype_special_class`
    #[derive(Clone, Debug)]
    pub struct IsSubtypeSpecialClass {
        pub sub_reason: Reason,
        pub sub_id: String,
        pub sub_args: Vec<TypeTagGeneric>,
        pub super_reason: Reason,
        pub super_id: PosId,
        pub super_exact: Exact,
        pub super_args: Vec<Ty>,
    }

    /// (Abstract in the `.mli`. The operands of `Conj` and `Disj` are shared,
    /// as in OCaml.)
    #[derive(Clone, Debug)]
    pub enum SubtypeProp {
        Valid,
        Invalid,
        /// The only uninstantiated relation that we produce is for the GADT-style
        /// inference when refining a value of one class type by a predicate of a
        /// descendant class type. We represent this using the components of each
        /// side to (a) represent this assumption and (b) because we need super_exact
        /// when instantiating the proposition.
        /// This prop is instantiated into a TL.IsSubtype of two class types but
        /// where we copy the exact of the super type onto the sub type we get by
        /// converting the predicate.
        /// We do this because otherwise with-refinements on the super type might
        /// cause the subtype relationship to not hold (and not produce any
        /// refinements on generics).
        IsSubtypeSpecialClass(IsSubtypeSpecialClass),
        Conj(Rc<SubtypeProp>, Rc<SubtypeProp>),
        Disj(Rc<SubtypeProp>, Rc<SubtypeProp>),
        Instantiated(typing_logic::SubtypeProp),
    }

    /// `val valid : subtype_prop`
    pub fn valid() -> SubtypeProp {
        SubtypeProp::Valid
    }

    /// `val invalid : subtype_prop`
    pub fn invalid() -> SubtypeProp {
        SubtypeProp::Invalid
    }

    pub fn conj(a: SubtypeProp, b: SubtypeProp) -> SubtypeProp {
        SubtypeProp::Conj(Rc::new(a), Rc::new(b))
    }

    pub fn disj(a: SubtypeProp, b: SubtypeProp) -> SubtypeProp {
        SubtypeProp::Disj(Rc::new(a), Rc::new(b))
    }

    /// This converts any exact with-refinements (e.g. type T = int) into the
    /// equivalent loose refinements (e.g. type T as int super int).
    /// The reason for this is that an exact refinement will shadow any existing
    /// information about the type constant on the class while loose refinements
    /// are added on.
    /// This is used when copying the with-refinements from the super type onto
    /// the sub type for IsSubtypeSpecialClass.
    /// It's relevant in the case that the super class has an exact refinement but
    /// the sub class already has the type constant bounded or assigned.
    fn replace_exact_with_loose(e: &Exact) -> Exact {
        match e {
            Exact::Exact => Exact::Exact,
            Exact::Nonexact(ClassRefinement { cr_consts }) => {
                // `S_map.map`
                let cr_consts = cr_consts
                    .iter()
                    .map(
                        |(
                            name,
                            RefinedConst {
                                bound: rc_bound,
                                is_ctx: rc_is_ctx,
                            },
                        )| {
                            let rc_bound = match rc_bound {
                                RefinedConstBound::TRloose(bounds) => {
                                    RefinedConstBound::TRloose(bounds.clone())
                                }
                                RefinedConstBound::TRexact(ty) => {
                                    RefinedConstBound::TRloose(RefinedConstBounds {
                                        lower: vec![ty.clone()],
                                        upper: vec![ty.clone()],
                                    })
                                }
                            };
                            (
                                name.clone(),
                                RefinedConst {
                                    bound: rc_bound,
                                    is_ctx: *rc_is_ctx,
                                },
                            )
                        },
                    )
                    .collect();
                Exact::Nonexact(ClassRefinement { cr_consts })
            }
        }
    }

    #[cfg(test)]
    pub(super) fn replace_exact_with_loose_for_tests(e: &Exact) -> Exact {
        replace_exact_with_loose(e)
    }

    pub fn instantiate_prop(
        env: &Env,
        map: &i_map::T<Ty>,
        pos: &Pos,
        prop: &SubtypeProp,
    ) -> typing_logic::SubtypeProp {
        match prop {
            SubtypeProp::Valid => typing_logic::valid(),
            SubtypeProp::Invalid => typing_logic::invalid(None),
            SubtypeProp::IsSubtypeSpecialClass(IsSubtypeSpecialClass {
                sub_reason,
                sub_id,
                sub_args,
                super_reason,
                super_id,
                super_exact,
                super_args,
            }) => {
                let sub_ty = ty_predicate::to_ty(
                    env,
                    map,
                    pos,
                    &TypePredicate(
                        sub_reason.clone(),
                        TypePredicate_::IsTag(TypeTag::ClassTag(sub_id.clone(), sub_args.clone())),
                    ),
                );
                let sub_ty = match get_node(&sub_ty) {
                    Ty_::Tclass(sub_id, _, sub_args) => mk((
                        get_reason(&sub_ty).clone(),
                        Ty_::Tclass(
                            sub_id.clone(),
                            replace_exact_with_loose(super_exact),
                            sub_args.clone(),
                        ),
                    )),
                    _ => {
                        diagnostics_state::invariant_violation(
                            pos.clone(),
                            telemetry::create(),
                            "Conversion of a class predicate did not produce a class type",
                            true,
                        );
                        sub_ty
                    }
                };
                let super_ty = mk((
                    super_reason.clone(),
                    Ty_::Tclass(super_id.clone(), super_exact.clone(), super_args.clone()),
                ));
                typing_logic::SubtypeProp::IsSubtype(
                    false,
                    InternalType::LoclType(sub_ty),
                    InternalType::LoclType(super_ty),
                )
            }
            SubtypeProp::Conj(p1, p2) => {
                // `TL.conj (instantiate_prop .. p1) (instantiate_prop .. p2)`:
                // the arguments are evaluated from right to left.
                let p2 = instantiate_prop(env, map, pos, p2);
                let p1 = instantiate_prop(env, map, pos, p1);
                typing_logic::conj(p1, p2)
            }
            SubtypeProp::Disj(p1, p2) => {
                let p2 = instantiate_prop(env, map, pos, p2);
                let p1 = instantiate_prop(env, map, pos, p1);
                typing_logic::disj(None, p1, p2)
            }
            SubtypeProp::Instantiated(prop) => prop.clone(),
        }
    }

    pub(super) fn print_prop(env: &Env, prop: &SubtypeProp) -> String {
        fn print_prop(env: &Env, prop: &SubtypeProp) -> String {
            match prop {
                SubtypeProp::Valid => "TRUE".to_string(),
                SubtypeProp::Invalid => "FALSE".to_string(),
                SubtypeProp::Conj(p1, p2) => {
                    "(".to_string() + &print_prop(env, p1) + " && " + &print_prop(env, p2) + ")"
                }
                SubtypeProp::Disj(p1, p2) => {
                    "(".to_string() + &print_prop(env, p1) + " || " + &print_prop(env, p2) + ")"
                }
                SubtypeProp::IsSubtypeSpecialClass(IsSubtypeSpecialClass {
                    sub_reason: _,
                    sub_id,
                    sub_args,
                    super_reason,
                    super_id,
                    super_exact,
                    super_args,
                }) => {
                    let sub_predicate_ =
                        TypePredicate_::IsTag(TypeTag::ClassTag(sub_id.clone(), sub_args.clone()));
                    let super_ty = mk((
                        super_reason.clone(),
                        Ty_::Tclass(super_id.clone(), super_exact.clone(), super_args.clone()),
                    ));
                    show_type_predicate_(&sub_predicate_)
                        + " <S: "
                        + &typing_print::debug(env, &super_ty)
                }
                SubtypeProp::Instantiated(prop) => typing_print_subtype_prop(env, prop),
            }
        }
        print_prop(env, prop)
    }
}

/// `module UTL = Uninstantiated_typing_logic`
use uninstantiated_typing_logic as utl;

/// `let cartesian = Partition.cartesian`
fn cartesian<A: Clone>(xss: &[Vec<A>]) -> Vec<Vec<A>> {
    partition::cartesian(xss)
}

/// `module TyPartition`
pub mod ty_partition {
    use std::cmp::Ordering;

    use super::DnfTy;
    use super::cartesian;
    use super::utl;
    use crate::partition;
    use crate::typing_defs_core::Exact;
    use crate::typing_defs_core::PosId;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::TypePredicate;
    use crate::typing_defs_core::get_node;
    use crate::typing_defs_core::get_reason;
    use crate::typing_env_types::Env;
    use crate::typing_reason::T as Reason;

    /// The atoms of `Partition`:
    /// `struct type t = locl_ty let compare = Typing_defs.compare_locl_ty ~normalize_lists:true end`
    pub struct LoclTyAtom;

    impl partition::OrderedType for LoclTyAtom {
        type T = Ty;

        fn compare(t1: &Ty, t2: &Ty) -> Ordering {
            crate::typing_defs_core::compare_locl_ty(Some(true), t1, t2)
        }
    }

    /// `module Partition = Partition.Make (...)`
    pub type Partition = partition::Make<LoclTyAtom>;

    /// `type assumptions = UTL.subtype_prop`
    pub type Assumptions = utl::SubtypeProp;

    /// `type t = Partition.t * assumptions * assumptions`
    pub type T = (Partition, Assumptions, Assumptions);

    #[derive(Clone, Debug)]
    pub enum BaseTy {
        ClassTy(Reason, PosId, Exact, Vec<Ty>),
        OtherTy,
    }

    /// `let valid = UTL.valid`
    pub fn valid() -> Assumptions {
        utl::valid()
    }

    /// `let invalid = UTL.invalid`
    pub fn invalid() -> Assumptions {
        utl::invalid()
    }

    /// The first `assume`, which the second one shadows.
    mod with_base_ty {
        use super::Assumptions;
        use super::BaseTy;
        use super::utl;
        use super::valid;
        use crate::decl_entry;
        use crate::folded_class as cls;
        use crate::typing_defs_core::TypePredicate;
        use crate::typing_defs_core::TypePredicate_;
        use crate::typing_defs_core::TypeTag;
        use crate::typing_env;
        use crate::typing_env_types::Env;

        /// Assuming a value `v` is a sub type of [base_ty] and satisifies [predicate], subtyping
        /// relations must hold
        pub(super) fn assume(
            env: &Env,
            base_ty: &BaseTy,
            predicate: &TypePredicate,
        ) -> Assumptions {
            let res: Option<Assumptions> = match (base_ty, &predicate.1) {
                // Given a value `v` of type `C<T>` and a predicate `is D`, search for a class
                // `K<TC>` and `K<TD>` respectively, it must hold that `K<TC> = K<TD>`
                (
                    BaseTy::ClassTy(r, posid, exact, tyargs),
                    TypePredicate_::IsTag(TypeTag::ClassTag(id, pred_args)),
                ) => (|| {
                    let name = &posid.1;
                    // let* cls1 = Decl_entry.to_option (Env.get_class env id1) in
                    let class_info = decl_entry::to_option(typing_env::get_class(env, id))?;
                    if *name == cls::name(&class_info)
                        || cls::has_ancestor(&class_info, name)
                        || cls::requires_ancestor(&class_info, name)
                    {
                        let prop =
                            utl::SubtypeProp::IsSubtypeSpecialClass(utl::IsSubtypeSpecialClass {
                                sub_reason: predicate.0.clone(),
                                sub_id: id.clone(),
                                sub_args: pred_args.clone(),
                                super_reason: r.clone(),
                                super_id: posid.clone(),
                                super_exact: exact.clone(),
                                super_args: tyargs.clone(),
                            });
                        Some(prop)
                    } else {
                        None
                    }
                })(),
                (BaseTy::ClassTy(..) | BaseTy::OtherTy, _) => None,
            };
            res.unwrap_or_else(valid)
        }
    }

    pub fn assume(env: &Env, ty: &Ty, predicate: &TypePredicate) -> Assumptions {
        match get_node(ty) {
            Ty_::Tclass(a, b, c) => with_base_ty::assume(
                env,
                &BaseTy::ClassTy(get_reason(ty).clone(), a.clone(), b.clone(), c.clone()),
                predicate,
            ),
            _ => with_base_ty::assume(env, &BaseTy::OtherTy, predicate),
        }
    }

    pub fn mk_left(env: &Env, predicate: &TypePredicate, ty: Ty) -> T {
        let assumptions = assume(env, &ty, predicate);
        (Partition::mk_left(ty), assumptions, invalid())
    }

    pub fn mk_span(env: &Env, predicate: &TypePredicate, ty: Ty) -> T {
        let assumptions = assume(env, &ty, predicate);
        // the false assumptions is `valid` because `valid` is the value that means
        // "I don't know anything" since it has the property that it is subsumed
        // under the "meet" (conjunction) operation and is the subsumer under the
        // "join" (disjunction) operation.
        // We always use a trivial `valid` here because, unlike with true assumptions,
        // non-trivial false assumptions are filled external to mk_* functions.
        (Partition::mk_span(ty), assumptions, valid())
    }

    pub fn mk_right(_env: &Env, _predicate: &TypePredicate, ty: Ty) -> T {
        (Partition::mk_right(ty), invalid(), valid())
    }

    /// `val mk_bottom : t`
    pub fn mk_bottom() -> T {
        (Partition::mk_bottom(), invalid(), invalid())
    }

    pub fn join((partition1, t1, f1): &T, (partition2, t2, f2): &T) -> T {
        (
            Partition::join(partition1, partition2),
            utl::disj(t1.clone(), t2.clone()),
            utl::disj(f1.clone(), f2.clone()),
        )
    }

    pub fn meet((partition1, t1, f1): &T, (partition2, t2, f2): &T) -> T {
        (
            Partition::meet(partition1, partition2),
            utl::conj(t1.clone(), t2.clone()),
            utl::conj(f1.clone(), f2.clone()),
        )
    }

    pub fn union_combine((partition1, t1, f1): &T, (partition2, t2, f2): &T) -> T {
        (
            Partition::union_combine(partition1, partition2),
            utl::disj(t1.clone(), t2.clone()),
            utl::conj(f1.clone(), f2.clone()),
        )
    }

    pub fn product(f: &dyn Fn(Vec<Ty>) -> Ty, sub_splits_and_assumptions: &[T]) -> T {
        let sub_splits: Vec<Partition> = sub_splits_and_assumptions
            .iter()
            .map(|(p, _, _)| p.clone())
            .collect();
        let assumption_pairs: Vec<Vec<Assumptions>> = sub_splits_and_assumptions
            .iter()
            .map(|(_, t, f)| vec![t.clone(), f.clone()])
            .collect();
        let assumption_sets = cartesian(&assumption_pairs);
        let (true_assumptions, false_assumptions) = match assumption_sets.as_slice() {
            // the split () by () case
            [] => (valid(), invalid()),
            // we rely on the detail that the first element in the result of cartesian
            // is the first element of every input list
            [all_true_assumptions, rest @ ..] => {
                let true_assumptions = all_true_assumptions
                    .iter()
                    .fold(valid(), |acc, a| utl::conj(acc, a.clone()));
                let false_assumptions = rest
                    .iter()
                    .map(|l| l.iter().fold(valid(), |acc, a| utl::conj(acc, a.clone())))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .fold(invalid(), utl::disj);
                (true_assumptions, false_assumptions)
            }
        };
        (
            Partition::product(f, &sub_splits),
            true_assumptions,
            false_assumptions,
        )
    }

    pub fn simplify((partition, true_assumptions, false_assumptions): &T, ty: Ty) -> T {
        (
            Partition::simplify(partition, ty),
            true_assumptions.clone(),
            false_assumptions.clone(),
        )
    }

    pub fn left(p: &Partition) -> DnfTy {
        Partition::left(p)
    }

    pub fn span(p: &Partition) -> DnfTy {
        Partition::span(p)
    }

    pub fn right(p: &Partition) -> DnfTy {
        Partition::right(p)
    }

    pub fn flip((partition, true_assumptions, false_assumptions): &T) -> T {
        (
            Partition::flip(partition),
            false_assumptions.clone(),
            true_assumptions.clone(),
        )
    }
}

/// Represents a type in disjunctive normal form. For example
/// the type (A & B) | C is represented as [[A; B]; [C]]
pub type DnfTy = Vec<Vec<Ty>>;

/// The partition of type over [predicate].
///
/// [left] describes a type that is a subset of the values that
///   pass the predicate
///
/// [right] describes a type that is a subset of the values that
///   fail the predicate
///
/// [span] describes a type whose set of values contain values that
///   both pass and fail the predicate
///
/// [assumptions] a subtype prop that should be considered true when the predicate
///   is satisfied
#[derive(Clone, Debug)]
pub struct TyPartition {
    pub predicate: TypePredicate,
    pub left: DnfTy,
    pub span: DnfTy,
    pub right: DnfTy,
    pub true_assumptions: utl::SubtypeProp,
    pub false_assumptions: utl::SubtypeProp,
}

fn split_ty_by_tuple(
    expansions: &SSet,
    ty_datatype: &data_type::T,
    env: &mut Env,
    ty: &Ty,
    sub_predicates: &[TypePredicate],
    predicate: &TypePredicate,
) -> ty_partition::T {
    match get_node(ty) {
        // TODO: optional and variadic fields T201398626 T201398652
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: TupleExtra::Tvariadic(variadic),
        }) if t_optional.is_empty() && typing_defs::is_nothing(variadic) => {
            let ty_reason = get_reason(ty).clone();
            // `List.zip sub_predicates t_required`
            if sub_predicates.len() != t_required.len() {
                ty_partition::mk_right(env, predicate, ty.clone()) // mismatch arity
            } else {
                let predicate_ty_pairs = sub_predicates.iter().zip(t_required.iter());
                // split each tuple element ty by its respective predicate
                let sub_splits: Vec<ty_partition::T> = predicate_ty_pairs
                    .map(|(predicate, ty)| split_ty(&[], expansions, env, ty, predicate))
                    .collect();
                ty_partition::product(&|tyl| make_type::tuple(ty_reason.clone(), tyl), &sub_splits)
            }
        }
        _ => {
            // Tuples are vecs at runtime, thus if the type's data type is disjoint from a vec
            // we can conclude the type must be in the right partition. Otherwise we do not
            // precisely know the relationship with the [IsTupleOf] predicate so default to
            // spanning
            let predicate_datatype = data_type::of_ty(false, env, &AtomicTy::Tuple);
            if data_type::are_disjoint(env, ty_datatype, &predicate_datatype) {
                ty_partition::mk_right(env, predicate, ty.clone())
            } else {
                ty_partition::mk_span(env, predicate, ty.clone())
            }
        }
    }
}

fn split_ty_by_shape(
    ty_datatype: &data_type::T,
    env: &mut Env,
    ty: &Ty,
    sp_allows_unknown_fields: bool,
    sp_fields: &TShapeMap<ShapeFieldPredicate>,
    predicate: &TypePredicate,
) -> ty_partition::T {
    match get_node(ty) {
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: s_unknown_value,
            fields: s_fields,
        })) => split_shape_fields(
            env,
            ty,
            s_fields,
            s_unknown_value,
            sp_allows_unknown_fields,
            sp_fields,
            predicate,
        ),
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => {
            let r = get_reason(ty).clone();
            // Split a splat scrutinee by over-approximating it as a single simple shape.
            // [get_shape_splat_concrete_supertypes] resolves each splat-position type
            // parameter to its concrete shape bound(s), transitively
            let resolved = typing_utils::get_shape_splat_concrete_supertypes(env, ty.clone());
            match resolved {
                None => {
                    // We could not over-approximate the scrutinee as a concrete shape, so we
                    // conclude nothing about the predicate
                    ty_partition::mk_span(env, predicate, ty.clone())
                }
                Some(ss_elems) => {
                    let normalized = typing_utils::normalize_shape_type(
                        env,
                        r,
                        ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }),
                    );
                    match normalized {
                        NormalizeShapeTypeResult::NormalizedShape(ShapeType::ShapeSimple(
                            ShapeTypeSimple {
                                fields: s_fields,
                                unknown_value: s_unknown_value,
                                ..
                            },
                        )) => split_shape_fields(
                            env,
                            ty,
                            &s_fields,
                            &s_unknown_value,
                            sp_allows_unknown_fields,
                            sp_fields,
                            predicate,
                        ),
                        NormalizeShapeTypeResult::NormalizedShape(ShapeType::ShapeSplat(_))
                        | NormalizeShapeTypeResult::NormalizedDistributed => {
                            ty_partition::mk_span(env, predicate, ty.clone())
                        }
                        NormalizeShapeTypeResult::NormalizedBottom => ty_partition::mk_bottom(),
                    }
                }
            }
        }
        _ => {
            // Shapes are dicts at runtime, thus if the type's data type is disjoint from a dict
            // we can conclude the type must be in the right partition. Otherwise we do not
            // precisely know the relationship with the [IsShapeOf] prediacte so default to
            // spanning
            let predicate_datatype = data_type::of_ty(false, env, &AtomicTy::Shape);
            if data_type::are_disjoint(env, ty_datatype, &predicate_datatype) {
                ty_partition::mk_right(env, predicate, ty.clone())
            } else {
                ty_partition::mk_span(env, predicate, ty.clone())
            }
        }
    }
}

fn split_shape_fields(
    env: &mut Env,
    ty: &Ty,
    s_fields: &TShapeMap<ShapeFieldType>,
    s_unknown_value: &Ty,
    sp_allows_unknown_fields: bool,
    sp_fields: &TShapeMap<ShapeFieldPredicate>,
    predicate: &TypePredicate,
) -> ty_partition::T {
    fn has_class_const_field<V>(map: &TShapeMap<V>) -> bool {
        map.iter().any(|(TShapeField(field), _val)| match field {
            TshapeFieldName::TSFclassConst(..) => true,
            TshapeFieldName::TSFregexGroup(_) | TshapeFieldName::TSFlitStr(_) => false,
        })
    }
    if has_class_const_field(s_fields) || has_class_const_field(sp_fields) {
        // class const field names are unsound, so fall back to SPAN
        ty_partition::mk_span(env, predicate, ty.clone())
    } else {
        // RIGHT if: ty has a required field that is not in the predicate and predicate is closed
        let has_extra_required_field = (!sp_allows_unknown_fields)
            && s_fields.iter().any(
                |(
                    key,
                    ShapeFieldType {
                        optional: sft_optional,
                        ..
                    },
                )| (!sft_optional) && !sp_fields.contains_key(key),
            );
        if has_extra_required_field {
            ty_partition::mk_right(env, predicate, ty.clone())
        } else {
            // Does the predicate require a field not in the type?
            let missing_required_field = sp_fields.iter().any(
                |(
                    key,
                    ShapeFieldPredicate {
                        optional: sfp_optional,
                        ..
                    },
                )| (!sfp_optional) && !s_fields.contains_key(key),
            );

            if missing_required_field && typing_defs::is_nothing(s_unknown_value) {
                // Missing a required field and the type is closed -> RIGHT
                ty_partition::mk_right(env, predicate, ty.clone())
            } else {
                // Split each field that exists in both ty and predicate
                // (`TShapeMap.fold_env`, in increasing order of the keys. The
                // OCaml conses the splits; the list is only searched below.)
                let mut field_splits: Vec<(
                    &TShapeField,
                    &ShapeFieldType,
                    &ShapeFieldPredicate,
                    ty_partition::T,
                )> = vec![];
                for (key, ty_field) in s_fields {
                    match sp_fields.get(key) {
                        Some(pred_field) => {
                            // Split this field's type by the predicate field's predicate
                            let field_split = split_ty(
                                &[],
                                &SSet::new(),
                                env,
                                &ty_field.ty,
                                &pred_field.predicate,
                            );
                            field_splits.push((key, ty_field, pred_field, field_split));
                        }
                        None => {
                            // Field only in ty, not in predicate. Checked above
                        }
                    }
                }

                // Check if any field is fully incompatible (fully right)
                let has_incompatible_field =
                    field_splits
                        .iter()
                        .any(|(_, ty_field, _, (field_partition, _, _))| {
                            let field_left = ty_partition::left(field_partition);
                            let field_span = ty_partition::span(field_partition);
                            let is_fully_right = field_left.is_empty() && field_span.is_empty();
                            // Required field in ty that's fully incompatible
                            (!ty_field.optional) && is_fully_right
                        });

                if has_incompatible_field {
                    ty_partition::mk_right(env, predicate, ty.clone())
                } else if sp_fields.keys().any(|key| !s_fields.contains_key(key))
                    && !typing_defs::is_nothing(s_unknown_value)
                {
                    // predicate specifies a field not in the type and the type is open
                    ty_partition::mk_span(env, predicate, ty.clone())
                } else {
                    // Check if all fields are fully left
                    let all_fields_fully_left =
                        field_splits
                            .iter()
                            .all(|(_, _, _, (field_partition, _, _))| {
                                let field_span = ty_partition::span(field_partition);
                                let field_right = ty_partition::right(field_partition);
                                field_span.is_empty() && field_right.is_empty()
                            });

                    // For left, the predicate must be open or the type must be closed
                    let openness_satisfies_left =
                        sp_allows_unknown_fields || typing_defs::is_nothing(s_unknown_value);

                    // For left, for every shared field: predicate's must be optional or the ty's must be required
                    let optionality_satisfied_left = sp_fields.iter().all(
                        |(
                            key,
                            ShapeFieldPredicate {
                                optional: sfp_optional,
                                ..
                            },
                        )| {
                            *sfp_optional
                                || match s_fields.get(key) {
                                    Some(ShapeFieldType {
                                        optional: sft_optional,
                                        ..
                                    }) => !sft_optional,
                                    None => true,
                                }
                        },
                    );

                    if optionality_satisfied_left
                        && all_fields_fully_left
                        && openness_satisfies_left
                    {
                        ty_partition::mk_left(env, predicate, ty.clone())
                    } else {
                        // Cannot conclude fully left or fully right, fall back to span
                        ty_partition::mk_span(env, predicate, ty.clone())
                    }
                }
            }
        }
    }
}

fn split_ty_by_tag(
    ty_datatype: &data_type::T,
    env: &mut Env,
    ty: &Ty,
    tag: &TypeTag,
    predicate: &TypePredicate,
) -> ty_partition::T {
    let predicate_datatype = data_type::of_tag(true, env, tag);
    let predicate_complement_datatype = data_type::complement(&predicate_datatype);
    if data_type::are_disjoint(env, ty_datatype, &predicate_datatype) {
        ty_partition::mk_right(env, predicate, ty.clone())
    } else if data_type::are_disjoint(env, ty_datatype, &predicate_complement_datatype) {
        ty_partition::mk_left(env, predicate, ty.clone())
    } else {
        ty_partition::mk_span(env, predicate, ty.clone())
    }
}

fn split_ty_by_union(
    other_intersected_tys: &[Ty],
    expansions: &SSet,
    env: &mut Env,
    ty: &Ty,
    predicates: &[TypePredicate],
) -> ty_partition::T {
    // Split the type by each predicate in the union.
    //
    // When splitting T by union predicate (P1 | P2 | ... | Pn):
    // - Left: parts that pass at least one predicate = L1 ∪ L2 ∪ ... ∪ Ln
    // - Right: parts that fail all predicates = R1 ∩ R2 ∩ ... ∩ Rn
    // - Span: parts that may or may not pass = everything else
    //
    // This is NOT the same as joining the partitions (which would give L1∪L2, S1∪S2, R1∪R2).
    let partitions: Vec<ty_partition::T> = predicates
        .iter()
        .map(|pred| split_ty(other_intersected_tys, expansions, env, ty, pred))
        .collect();
    // Combine partitions using the correct algebra for union predicates
    match partitions.split_first() {
        None => ty_partition::mk_bottom(),
        Some((first, rest)) => rest
            .iter()
            .fold(first.clone(), |acc, p| ty_partition::union_combine(&acc, p)),
    }
}

fn split_ty(
    other_intersected_tys: &[Ty],
    expansions: &SSet,
    env: &mut Env,
    ty: &Ty,
    predicate: &TypePredicate,
) -> ty_partition::T {
    let ety = typing_env::expand_type(env, ty.clone());
    // `partition_f predicate (env, ty_datatype)` (with the arguments of
    // `split_ty` it captures first)
    fn partition_f(
        other_intersected_tys: &[Ty],
        expansions: &SSet,
        ety: &Ty,
        predicate: &TypePredicate,
        env: &mut Env,
        ty_datatype: &data_type::T,
    ) -> ty_partition::T {
        match &predicate.1 {
            TypePredicate_::IsTupleOf(TuplePredicate {
                required: sub_predicates,
            }) => split_ty_by_tuple(expansions, ty_datatype, env, ety, sub_predicates, predicate),
            TypePredicate_::IsShapeOf(ShapePredicate {
                allows_unknown_fields: sp_allows_unknown_fields,
                fields: sp_fields,
            }) => split_ty_by_shape(
                ty_datatype,
                env,
                ety,
                *sp_allows_unknown_fields,
                sp_fields,
                predicate,
            ),
            TypePredicate_::IsTag(tag) => split_ty_by_tag(ty_datatype, env, ety, tag, predicate),
            TypePredicate_::IsUnionOf(predicates) => {
                split_ty_by_union(other_intersected_tys, expansions, env, ety, predicates)
            }
            TypePredicate_::IsNot(inner) => {
                let split = partition_f(
                    other_intersected_tys,
                    expansions,
                    ety,
                    inner,
                    env,
                    ty_datatype,
                );
                ty_partition::flip(&split)
            }
        }
    }
    let partition_f = |env: &mut Env, ty_datatype: data_type::T| {
        partition_f(
            other_intersected_tys,
            expansions,
            &ety,
            predicate,
            env,
            &ty_datatype,
        )
    };
    // `split_union` and `split_intersection` capture `predicate`.
    fn split_union(
        predicate: &TypePredicate,
        other_intersected_tys: &[Ty],
        expansions: &SSet,
        env: &mut Env,
        tys: &[Ty],
    ) -> ty_partition::T {
        let partitions: Vec<ty_partition::T> = tys
            .iter()
            .map(|ty| split_ty(other_intersected_tys, expansions, env, ty, predicate))
            .collect();
        partitions.iter().fold(ty_partition::mk_bottom(), |acc, p| {
            ty_partition::join(&acc, p)
        })
    }
    fn split_intersection(
        predicate: &TypePredicate,
        other_intersected_tys: &[Ty],
        init: ty_partition::T,
        env: &mut Env,
        expansions: &SSet,
        tys: &[Ty],
    ) -> ty_partition::T {
        let ty_others_pairs = list_to_list_of_e_and_others(tys);
        let partitions: Vec<ty_partition::T> = ty_others_pairs
            .iter()
            .map(|(ty, others)| {
                let other_intersected_tys: Vec<Ty> = others
                    .iter()
                    .chain(other_intersected_tys.iter())
                    .cloned()
                    .collect();
                split_ty(&other_intersected_tys, expansions, env, ty, predicate)
            })
            .collect();
        partitions
            .iter()
            .fold(init, |acc, p| ty_partition::meet(&acc, p))
    }
    let partition: ty_partition::T = match get_node(&ety) {
        // Types we cannot split, that we know will end up being a part of both
        // partitions.
        Ty_::Tvar(_) | Ty_::Tany(_) | Ty_::Tdynamic(_) | Ty_::Taccess(_) => {
            ty_partition::mk_span(env, predicate, ty.clone())
        }
        Ty_::TclassPtr(_) => {
            // TODO: need a bespoke DataType to model KindOfClass
            ty_partition::mk_span(env, predicate, ty.clone())
        }
        // Types we cannot split
        Ty_::Tprim(
            prim @ (Tprim::Tint
            | Tprim::Tnull
            | Tprim::Tvoid
            | Tprim::Tbool
            | Tprim::Tfloat
            | Tprim::Tresource),
        ) => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Primitive(*prim));
            partition_f(env, dt)
        }
        Ty_::Tfun(_) => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Function);
            partition_f(env, dt)
        }
        Ty_::Tnonnull => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Nonnull);
            partition_f(env, dt)
        }
        Ty_::Ttuple(_) => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Tuple);
            partition_f(env, dt)
        }
        Ty_::Tshape(ShapeType::ShapeSimple(_) | ShapeType::ShapeSplat(_)) => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Shape);
            partition_f(env, dt)
        }
        Ty_::Tlabel(_) => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Label);
            partition_f(env, dt)
        }
        Ty_::Tnewtype(name, _, _) if name == sn::classes::ENUM_CLASS_LABEL => {
            let dt = data_type::of_ty(false, env, &AtomicTy::Label);
            partition_f(env, dt)
        }
        Ty_::Tclass((_, name), _, args) => {
            let dt = data_type::of_ty(true, env, &AtomicTy::Class(name.clone(), args.clone()));
            partition_f(env, dt)
        }
        Ty_::Tneg(TypePredicate(_, predicate)) => {
            fn to_dty(env: &mut Env, predicate: &TypePredicate_) -> data_type::T {
                match predicate {
                    TypePredicate_::IsTag(tag) => data_type::of_tag(false, env, tag),
                    TypePredicate_::IsTupleOf(_) => data_type::of_ty(false, env, &AtomicTy::Tuple),
                    TypePredicate_::IsShapeOf(_) => data_type::of_ty(false, env, &AtomicTy::Shape),
                    TypePredicate_::IsUnionOf(preds) => {
                        // `List.fold_left_env env preds ~init:DataType.empty`
                        let mut dt_acc = data_type::empty();
                        for pred in preds {
                            let dt = to_dty(env, &pred.1);
                            dt_acc = data_type::union(&dt_acc, &dt);
                        }
                        dt_acc
                    }
                    TypePredicate_::IsNot(inner_pred) => {
                        let inner_dt = to_dty(env, &inner_pred.1);
                        data_type::complement(&inner_dt)
                    }
                }
            }
            let dty = to_dty(env, predicate);
            let dty = data_type::complement(&dty);
            partition_f(env, dty)
        }
        Ty_::Tprim(Tprim::Tnoreturn) => ty_partition::mk_bottom(),
        // Types we can split into a union of types
        Ty_::Tunion(tyl) => split_union(predicate, other_intersected_tys, expansions, env, tyl),
        Ty_::Tprim(Tprim::Tnum) => split_union(
            predicate,
            other_intersected_tys,
            expansions,
            env,
            &[
                make_type::int(get_reason(ty).clone()),
                make_type::float(get_reason(ty).clone()),
            ],
        ),
        Ty_::Tprim(Tprim::Tarraykey) => split_union(
            predicate,
            other_intersected_tys,
            expansions,
            env,
            &[
                make_type::int(get_reason(ty).clone()),
                make_type::string(get_reason(ty).clone()),
            ],
        ),
        Ty_::TvecOrDict(tk, tv) => split_union(
            predicate,
            other_intersected_tys,
            expansions,
            env,
            &[
                make_type::vec(get_reason(ty).clone(), tv.clone()),
                make_type::dict(get_reason(ty).clone(), tk.clone(), tv.clone()),
            ],
        ),
        Ty_::Toption(ty_opt) => split_union(
            predicate,
            other_intersected_tys,
            expansions,
            env,
            &[make_type::null(get_reason(ty).clone()), ty_opt.clone()],
        ),
        // Types we need to split across an intersection
        Ty_::Tintersection(tyl) if tyl.is_empty() => split_ty(
            other_intersected_tys,
            expansions,
            env,
            &make_type::mixed(get_reason(ty).clone()),
            predicate,
        ),
        Ty_::Tintersection(tyl) => {
            let (ty, tyl) = (&tyl[0], &tyl[1..]);
            let init = split_ty(
                &[other_intersected_tys, tyl].concat(),
                expansions,
                env,
                ty,
                predicate,
            );
            let other_intersected_tys: Vec<Ty> = std::iter::once(ty)
                .chain(other_intersected_tys.iter())
                .cloned()
                .collect();
            split_intersection(
                predicate,
                &other_intersected_tys,
                init,
                env,
                expansions,
                tyl,
            )
        }
        // Below are types of the form T <: U. We treat these as T & U
        Ty_::Tdependent(_, super_ty) => {
            let partition = split_ty(other_intersected_tys, expansions, env, super_ty, predicate);
            ty_partition::meet(
                &ty_partition::mk_span(env, predicate, ty.clone()),
                &partition,
            )
        }
        Ty_::Tgeneric(name) | Ty_::Tnewtype(name, _, _) if expansions.contains(name) => {
            ty_partition::mk_span(env, predicate, ty.clone())
        }
        Ty_::Tgeneric(name)
            if match &predicate.1 {
                TypePredicate_::IsTag(TypeTag::GenericTag {
                    name: pred_name,
                    from_like: _,
                }) => name == pred_name,
                _ => false,
            } =>
        {
            // [T] trivially satisfies [is T]; without this short-circuit the general
            // Tgeneric case below recurses on upper bounds, where [GenericTag]'s
            // over-approximate DataType collapses the result to [mk_span].
            ty_partition::mk_left(env, predicate, ty.clone())
        }
        Ty_::Tgeneric(name) => {
            let expansions = expansions.update(name.clone());
            let upper_bounds = typing_set::elements(&typing_env::get_upper_bounds(env, name));
            let init = ty_partition::mk_span(env, predicate, ty.clone());
            split_intersection(
                predicate,
                other_intersected_tys,
                init,
                env,
                &expansions,
                &upper_bounds,
            )
        }
        Ty_::Tnewtype(name, ty_args, _)
            if ty_args.len() == 1 && name == sn::classes::REPRESENTABLE_AS =>
        {
            // RepresentableAs<T> shares its runtime data type with T, so a
            // predicate splits RepresentableAs<T> exactly as it splits T.
            let ty_arg = &ty_args[0];
            let expansions = expansions.update(name.clone());
            split_ty(other_intersected_tys, &expansions, env, ty_arg, predicate)
        }
        Ty_::Tnewtype(name, _, _)
            if match &predicate.1 {
                TypePredicate_::IsTag(TypeTag::EnumTag(pred_name)) => name == pred_name,
                _ => false,
            } =>
        {
            ty_partition::mk_left(env, predicate, ty.clone())
        }
        Ty_::Tnewtype(name, tyl, _) => {
            let as_ty = typing_utils::get_newtype_super(env, get_reason(ty).clone(), name, tyl);
            let init = ty_partition::mk_span(env, predicate, ty.clone());
            let expansions = expansions.update(name.clone());
            // `Decl_entry.Found { td_type_assignment = CaseType (variant, variants);
            //   td_tparams; _ }`
            let case_type = match typing_env::get_typedef(env, name) {
                decl_entry::T::Found(td) => match &td.type_assignment {
                    TypedefTypeAssignment::CaseType(variant, variants) => {
                        Some((variant.clone(), variants.to_vec(), td.tparams.to_vec()))
                    }
                    TypedefTypeAssignment::SimpleTypeDef(..) => None,
                },
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            };
            match case_type {
                Some((variant, variants, td_tparams)) => {
                    // The this_ty does not need to be set because case types cannot
                    // appear within classes thus cannot us the this type.
                    // If we ever change that this could needs to be changed
                    let ety_env = ExpandEnv {
                        substs: if tyl.is_empty() {
                            crate::pmap::Map::new()
                        } else {
                            decl_subst_make_locl(&td_tparams, tyl)
                        },
                        ..empty_expand_env()
                    };
                    let localize =
                        |env: &mut Env, ty: &DeclTy| typing_utils::localize(&ety_env, env, ty);
                    let variants: Vec<TypedefCaseTypeVariant> =
                        std::iter::once(variant).chain(variants).collect();
                    let mk_subtype_prop = |sub: Ty, super_: Ty| {
                        typing_logic::SubtypeProp::IsSubtype(
                            false,
                            InternalType::LoclType(sub),
                            InternalType::LoclType(super_),
                        )
                    };
                    let where_constraint_to_prop =
                        |env: &mut Env, wc: &DeclWhereConstraint| -> typing_logic::SubtypeProp {
                            let ty::decl::WhereConstraint(left, ck, right) = wc;
                            let (_err, local_left) = localize(env, left);
                            let (_err, local_right) = localize(env, right);
                            let prop = match ck {
                                ConstraintKind::ConstraintAs => {
                                    mk_subtype_prop(local_left, local_right)
                                }
                                ConstraintKind::ConstraintSuper => {
                                    mk_subtype_prop(local_right, local_left)
                                }
                                ConstraintKind::ConstraintEq => typing_logic::conj(
                                    mk_subtype_prop(local_left.clone(), local_right.clone()),
                                    mk_subtype_prop(local_right, local_left),
                                ),
                            };
                            prop
                        };
                    let where_constraints_to_prop = |env: &mut Env, wcs: &[DeclWhereConstraint]| {
                        let props: Vec<typing_logic::SubtypeProp> = wcs
                            .iter()
                            .map(|wc| where_constraint_to_prop(env, wc))
                            .collect();
                        typing_logic::conj_list(props)
                    };
                    let ty_prop_pairs: Vec<(Ty, typing_logic::SubtypeProp)> = variants
                        .iter()
                        .map(|variant| {
                            let (hint, constraints) = (&variant.hint, &variant.where_constraints);
                            let (_ty_err_opt, ty) = localize(env, hint);
                            let prop = where_constraints_to_prop(env, constraints);
                            (ty, prop)
                        })
                        .collect();
                    let partition_tyl = if
                    // This works for unconditional case types too but its superfluous
                    // to produce the assumptions in that case.
                    typing_case_type_variant::has_where_clauses(&variants) {
                        // filter tyl that are disjoint from &(other_intersected_tys)
                        let filter_ty = make_type::intersection(
                            typing_reason::none(),
                            other_intersected_tys.to_vec(),
                        );
                        let ty_prop_pairs: Vec<(Ty, typing_logic::SubtypeProp)> = ty_prop_pairs
                            .into_iter()
                            .filter(|(ty, _prop)| {
                                !data_type::are_locl_tys_disjoint(env, &filter_ty, ty)
                            })
                            .collect();
                        let partitions: Vec<ty_partition::T> = ty_prop_pairs
                            .into_iter()
                            .map(|(current_ty, current_prop)| {
                                let (partition_, true_assumptions, false_assumptions) = split_ty(
                                    other_intersected_tys,
                                    &expansions,
                                    env,
                                    &current_ty,
                                    predicate,
                                );
                                // Here we conj the where clause with the true and false
                                // assumptions from the split; we do this so that any
                                // FALSE from the split will eliminate the clause
                                let current_prop = utl::SubtypeProp::Instantiated(current_prop);
                                (
                                    partition_,
                                    utl::conj(true_assumptions, current_prop.clone()),
                                    utl::conj(false_assumptions, current_prop),
                                )
                            })
                            .collect();
                        partitions.iter().fold(ty_partition::mk_bottom(), |acc, p| {
                            ty_partition::join(&acc, p)
                        })
                    } else {
                        let tyl: Vec<Ty> = ty_prop_pairs.into_iter().map(|(ty, _)| ty).collect();
                        split_union(predicate, other_intersected_tys, &expansions, env, &tyl)
                    };
                    // For case types without where clauses, the variants alone
                    // fully capture all values — meeting with the upper bound's
                    // partition adds no information and introduces noisy
                    // (X & null) | (X & nonnull) shapes when the bound is the
                    // default mixed. Where-clause case types still need the meet
                    // to apply the bound to the unrefined cases.
                    if typing_case_type_variant::has_where_clauses(&variants) {
                        let partition_as_ty = split_intersection(
                            predicate,
                            other_intersected_tys,
                            init,
                            env,
                            &expansions,
                            &[as_ty],
                        );
                        ty_partition::meet(&partition_tyl, &partition_as_ty)
                    } else {
                        partition_tyl
                    }
                }
                None => split_intersection(
                    predicate,
                    other_intersected_tys,
                    init,
                    env,
                    &expansions,
                    &[as_ty],
                ),
            }
        }
    };
    // If one side of the partition is empty that means [ty] falls completely
    // under the other side. Set the partition equal to the type to avoid
    // computing any unions or intersections
    let partition = ty_partition::simplify(&partition, ty.clone());
    partition
}

/// Given a [Typing_defs.locl_ty] and a [Typing_defs.type_predicate], partition the
/// [Typing_defs.locl_ty] into three types:
///
///   left: For the portition of the type that is a subset of the values that
///     passes the predicate at runtime
///
///   right: For the portition of the type that is a subset of the values that
///     fails the predicate at runtime
///
///   span: For the portition of the type that contains values that both
///     pass and fails the predicate
///
/// As an example consider partition the type (num | arraykey | T) where T is a generic type
///   bounded by nonnull over the predicate (IsTag IntTag)
///
/// This will produce
///   left = int (num & (IsTag IntTag) = int and arraykey & (IsTag IntTag) = int)
///   right = float | string (num & !(IsTag IntTag) = float and arraykey & !(IsTag IntTag) = string)
///   span = T (T can contain values that are ints and values that are not ints)
pub fn partition_ty(env: &mut Env, ty: &Ty, predicate: &TypePredicate) -> TyPartition {
    let (partition, true_assumptions, false_assumptions) =
        split_ty(&[], &SSet::new(), env, ty, predicate);
    let left = ty_partition::left(&partition);
    let span = ty_partition::span(&partition);
    let right = ty_partition::right(&partition);
    let from_list = |kind: &str, tyll: &DnfTy| -> Vec<LogStructure> {
        tyll.iter()
            .map(|tyl| {
                LogStructure::LogType(
                    kind.to_string(),
                    make_type::intersection(typing_reason::none(), tyl.clone()),
                )
            })
            .collect()
    };
    typing_log::log_with_level(env, "partition", 1, || {
        let mut structures = vec![LogStructure::LogType("ty".to_string(), ty.clone())];
        structures.extend(from_list("left", &left));
        structures.extend(from_list("span", &span));
        structures.extend(from_list("right", &right));
        structures.push(LogStructure::LogHead(
            "true_assumptions = ".to_string() + &utl::print_prop(env, &true_assumptions),
            vec![],
        ));
        structures.push(LogStructure::LogHead(
            "false_assumptions = ".to_string() + &utl::print_prop(env, &false_assumptions),
            vec![],
        ));
        typing_log::log_types(
            &typing_reason::to_pos(&predicate.0),
            env,
            &[LogStructure::LogHead(
                "partition ".to_string() + &show_type_predicate_(&predicate.1),
                structures,
            )],
        )
    });
    TyPartition {
        predicate: predicate.clone(),
        left,
        span,
        right,
        true_assumptions,
        false_assumptions,
    }
}

/// Returns true if the type falls entirely on the left of the predicate
pub fn passes_predicate(env: &Env, ty: &Ty, predicate: &TypePredicate) -> bool {
    // The environment `partition_ty` returns is dropped.
    let TyPartition {
        left: _,
        span,
        right,
        ..
    } = partition_ty(&mut env.clone(), ty, predicate);
    span.is_empty() && right.is_empty()
}

#[cfg(test)]
mod tests {
    use oxidized::s_map::SMap;

    use super::*;
    use crate::typing_defs_core::ClassRefinement;
    use crate::typing_defs_core::Exact;
    use crate::typing_defs_core::RefinedConst;
    use crate::typing_defs_core::RefinedConstBound;
    use crate::typing_defs_core::RefinedConstBounds;

    #[test]
    fn each_element_with_the_others() {
        assert_eq!(
            list_to_list_of_e_and_others(&[1, 2, 3]),
            vec![(1, vec![2, 3]), (2, vec![1, 3]), (3, vec![1, 2])]
        );
        assert_eq!(list_to_list_of_e_and_others::<i32>(&[]), vec![]);
    }

    #[test]
    fn exact_refinements_become_loose() {
        let int = make_type::int(typing_reason::none());
        let mut cr_consts = SMap::new();
        cr_consts.insert(
            "T".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRexact(int.clone()),
                is_ctx: false,
            },
        );
        cr_consts.insert(
            "U".to_string(),
            RefinedConst {
                bound: RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: vec![],
                    upper: vec![int],
                }),
                is_ctx: true,
            },
        );
        let e = Exact::Nonexact(ClassRefinement {
            cr_consts: cr_consts.into(),
        });
        match utl::replace_exact_with_loose_for_tests(&e) {
            Exact::Nonexact(ClassRefinement { cr_consts }) => {
                match &cr_consts["T"].bound {
                    RefinedConstBound::TRloose(RefinedConstBounds { lower, upper }) => {
                        assert_eq!((lower.len(), upper.len()), (1, 1))
                    }
                    RefinedConstBound::TRexact(_) => panic!("expected loose bounds"),
                }
                match &cr_consts["U"].bound {
                    RefinedConstBound::TRloose(RefinedConstBounds { lower, upper }) => {
                        assert_eq!((lower.len(), upper.len()), (0, 1))
                    }
                    RefinedConstBound::TRexact(_) => panic!("expected loose bounds"),
                }
                assert!(cr_consts["U"].is_ctx);
            }
            Exact::Exact => panic!("expected a refinement"),
        }
        assert!(matches!(
            utl::replace_exact_with_loose_for_tests(&Exact::Exact),
            Exact::Exact
        ));
    }

    #[test]
    fn assumptions_of_partitions() {
        let int = make_type::int(typing_reason::none());
        let bottom = ty_partition::mk_bottom();
        assert!(matches!(bottom.1, utl::SubtypeProp::Invalid));
        assert!(matches!(bottom.2, utl::SubtypeProp::Invalid));
        // `flip` swaps the assumptions along with the sides.
        let p = (
            ty_partition::Partition::mk_left(int.clone()),
            utl::valid(),
            utl::invalid(),
        );
        let flipped = ty_partition::flip(&p);
        assert!(ty_partition::left(&flipped.0).is_empty());
        assert_eq!(ty_partition::right(&flipped.0).len(), 1);
        assert!(matches!(flipped.1, utl::SubtypeProp::Invalid));
        assert!(matches!(flipped.2, utl::SubtypeProp::Valid));
        // The product of no splits: `valid` / `invalid`.
        let product =
            ty_partition::product(&|tyl| make_type::tuple(typing_reason::none(), tyl), &[]);
        assert!(matches!(product.1, utl::SubtypeProp::Valid));
        assert!(matches!(product.2, utl::SubtypeProp::Invalid));
        // The product of one split: true assumptions are its true assumptions
        // (conjoined with `valid`), false ones its false ones.
        let product = ty_partition::product(
            &|tyl| make_type::tuple(typing_reason::none(), tyl),
            &[p.clone()],
        );
        match &product.1 {
            utl::SubtypeProp::Conj(a, b) => {
                assert!(matches!(**a, utl::SubtypeProp::Valid));
                assert!(matches!(**b, utl::SubtypeProp::Valid));
            }
            _ => panic!("expected a conjunction"),
        }
        match &product.2 {
            utl::SubtypeProp::Disj(a, b) => {
                assert!(matches!(**a, utl::SubtypeProp::Invalid));
                assert!(matches!(**b, utl::SubtypeProp::Conj(..)));
            }
            _ => panic!("expected a disjunction"),
        }
        assert_eq!(ty_partition::left(&product.0).len(), 1);
    }
}
