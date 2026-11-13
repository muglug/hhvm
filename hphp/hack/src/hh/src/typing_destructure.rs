// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_destructure.ml`. See `hh/PORTING.md`.
//!
//! Core typing logic for shape and tuple destructuring.
//!
//! Shape destructuring extracts fields from shapes into local variables:
//! ```text
//!   shape('x' => $x, ?'y' => $y, 'z' => _) = $point;
//!   shape($x, $y) = $point;           // punning
//!   shape('x' => $x, ...) = $point;   // open pattern
//! ```
//!
//! Tuple destructuring does the same for tuples:
//! ```text
//!   tuple($a, $b) = $tup;
//!   tuple($a, optional $b) = $tup;
//!   tuple($a, ...) = $tup;            // open pattern
//! ```
//!
//! Both also work in [foreach]:
//! ```text
//!   foreach ($points as shape('x' => $x, 'y' => $y)) { ... }
//! ```
//!
//! Shapes in Hack can be open or closed. An open shape has unknown fields
//! beyond those listed — written with [...] in type position:
//! ```text
//!   shape('x' => int, ...)   // open: may have other fields
//!   shape('x' => int)        // closed: exactly these fields
//! ```
//!
//! In this file, pattern types are always constructed as open. This avoids
//! incorrectly rejecting valid cases like omitting optional fields from a
//! closed pattern:
//! ```text
//!   $s : shape('a' => int, 'b' => int, ?'c' => int);
//!   shape('a' => $a, 'b' => $b) = $s;   // valid: ?'c' may be omitted
//! ```
//! If we built a closed pattern type [shape('a' => α, 'b' => β)], shape
//! subtyping would reject the optional ['c'] in the RHS. Using an open
//! pattern type avoids this, and structural validation (required field
//! coverage, open/closed enforcement) runs separately in {!Destructure_check}.
//!
//! Dynamic and like-type RHS values need special handling because
//! [dynamic] is not a subtype of shape or tuple types in normal
//! subtyping ([dynamic <: shape(...)] doesn't hold). For example:
//! ```text
//!   function f(dynamic $d): void {
//!     shape('x' => $x, ...) = $d;    // $x should be dynamic
//!   }
//!   function g(~shape('x' => int) $s): void {
//!     shape('x' => $x, ...) = $s;    // $x should be ~int
//!   }
//! ```
//! For like types ([~T = dynamic | T]), union subtyping requires all
//! members to satisfy the constraint. The [dynamic] member would cause
//! the whole constraint to fail, so we strip it out, constrain against
//! the inner type, and separately add [dynamic] as a lower bound on
//! each type variable. The solver combines both lower bounds — e.g.,
//! [int | dynamic] = [~int].
//!
//! Structural validation — required field coverage, open/closed shape
//! enforcement, known-field checks, tuple arity — is handled by
//! {!Destructure_check}, not this file.
//!
//! This file does not handle legacy list destructuring
//! ([list($a, $b) = $vec]), which uses the [Tdestructure] constraint
//! in {!Typing_subtype}.
//!
//! The OCaml lists of the accumulators (`typed_fields_rev`, `field_tys`,
//! ...) are `Vec`s in the OCaml order (element 0 is the head): the order of
//! `field_tys` is the order in which `dynamic` is added as a lower bound.

use std::collections::HashMap;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::local_id::LocalId;
use oxidized::message::Message;
use oxidized::nast;
use oxidized::pos::Pos;

use crate::hack_event_logger;
use crate::local_id;
use crate::pos_or_decl;
use crate::tast;
use crate::typing_defs;
use crate::typing_defs::t_shape_field;
use crate::typing_defs::t_shape_map::TShapeField;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_dynamic_utils;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error_utils;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_subtype;

fn set_valid_rvalue(assign_pos: Pos, env: &mut Env, lvar: &LocalId, ty: Ty) {
    if typing_env::is_using_var(env, lvar) {
        typing_error_utils::add_typing_error(
            &typing_error::primary(typing_error::primary::T::Illegal_disposable {
                pos: assign_pos.clone(),
                verb: typing_error::primary::IllegalDisposableVerb::assigned,
            }),
            env,
        )
    }
    typing_env::set_local(None, None, env, lvar.clone(), ty, assign_pos);
    let eid = typing_env::make_expression_id(env);
    match typing_env::set_local_expr_id(env, lvar, eid) {
        Ok(()) => {}
        Err(err) => typing_error_utils::add_typing_error(&err, env),
    }
}

fn pos_of_target(target: &nast::DestructureTarget) -> Pos {
    let aast::DestructureTarget(_, _, target_) = target;
    match target_ {
        aast::DestructureTarget_::DtLvar(aast::Lid(pos, _)) => pos.clone(),
        aast::DestructureTarget_::DtWildcard(pos) => pos.clone(),
        aast::DestructureTarget_::DtShape(ds) => ds.pos.clone(),
        aast::DestructureTarget_::DtTuple(dt) => dt.pos.clone(),
    }
}

fn field_pos_of_ast_sfn(sfn: &ast_defs::ShapeFieldName) -> Pos {
    match sfn {
        ast_defs::ShapeFieldName::SFlitStr((pos, _)) => pos.clone(),
        ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(pos, _), _) => pos.clone(),
        ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(pos, _)) => pos.clone(),
    }
}

fn collect_target_vars(target: &nast::DestructureTarget) -> Vec<(Pos, LocalId)> {
    let aast::DestructureTarget(_, _, target_) = target;
    match target_ {
        aast::DestructureTarget_::DtLvar(aast::Lid(pos, lid)) => vec![(pos.clone(), lid.clone())],
        aast::DestructureTarget_::DtWildcard(_) => vec![],
        aast::DestructureTarget_::DtShape(shape_pat) => shape_pat
            .fields
            .iter()
            .flat_map(|shape_field| collect_target_vars(&shape_field.target))
            .collect(),
        aast::DestructureTarget_::DtTuple(tuple_pat) => tuple_pat
            .entries
            .iter()
            .flat_map(|tuple_entry| collect_target_vars(&tuple_entry.target))
            .collect(),
    }
}

fn check_duplicate_vars(env: &Env, targets: &[&nast::DestructureTarget]) {
    let all_vars: Vec<(Pos, LocalId)> = targets
        .iter()
        .flat_map(|target| collect_target_vars(target))
        .collect();
    let mut seen: HashMap<String, Pos> = HashMap::new();
    for (pos, lid) in all_vars {
        let name = local_id::get_name(&lid);
        match seen.get(name) {
            Some(first_pos) => typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::Unify_error {
                    pos,
                    msg_opt: Some(format!(
                        "Variable `{}` is bound multiple times in this destructuring pattern",
                        name
                    )),
                    reasons_opt: Some(Lazy::from_val(vec![Message(
                        pos_or_decl::of_raw_pos(first_pos.clone()),
                        "First binding was here".into(),
                    )])),
                }),
                env,
            ),
            None => {
                seen.insert(name.clone(), pos);
            }
        }
    }
}

/// Accumulator for typing a shape destructure pattern.
mod shape_fields {
    use crate::tast;
    use crate::typing_defs::t_shape_map;
    use crate::typing_defs::t_shape_map::TShapeField;
    use crate::typing_defs_core::ShapeFieldType;
    use crate::typing_defs_core::Ty;

    #[derive(Clone, Debug)]
    pub struct T {
        /// TAST nodes, in reverse source order
        pub typed_fields_rev: Vec<tast::DestructureShapeField>,
        /// fresh tyvars keyed by field name, assembled into an open
        /// shape type for the [rhs_ty <: pattern_ty] subtype constraint
        pub shape_map: t_shape_map::T<ShapeFieldType>,
        /// all tyvars (including nested ones from sub-patterns) that
        /// need [dynamic] added as a lower bound when the RHS is dynamic/like
        pub field_tys: Vec<Ty>,
    }

    pub fn empty() -> T {
        T {
            typed_fields_rev: vec![],
            shape_map: t_shape_map::T::new(),
            field_tys: vec![],
        }
    }

    pub fn add(
        t: T,
        typed_field: tast::DestructureShapeField,
        shape_field_name: TShapeField,
        shape_field_type: ShapeFieldType,
        field_ty: Ty,
        inner_field_tys: Vec<Ty>,
    ) -> T {
        let T {
            mut typed_fields_rev,
            mut shape_map,
            field_tys,
        } = t;
        typed_fields_rev.insert(0, typed_field);
        // `TShapeMap.add`: the new key replaces an equal one.
        shape_map.remove(&shape_field_name);
        shape_map.insert(shape_field_name, shape_field_type);
        // `field_ty :: (inner_field_tys @ t.field_tys)`
        let mut new_field_tys = Vec::with_capacity(1 + inner_field_tys.len() + field_tys.len());
        new_field_tys.push(field_ty);
        new_field_tys.extend(inner_field_tys);
        new_field_tys.extend(field_tys);
        T {
            typed_fields_rev,
            shape_map,
            field_tys: new_field_tys,
        }
    }
}

/// Accumulator for typing a tuple destructure pattern.
mod tuple_entries {
    use crate::tast;
    use crate::typing_defs_core::Ty;

    #[derive(Clone, Debug)]
    pub struct T {
        /// TAST nodes, in reverse source order
        pub typed_entries_rev: Vec<tast::DestructureTupleEntry>,
        /// required prefix entry tyvars, in reverse source order
        pub required_tys_rev: Vec<Ty>,
        /// optional suffix entry tyvars, in reverse source order
        pub optional_tys_rev: Vec<Ty>,
        /// all entry tyvars (including nested ones from sub-patterns) that
        /// need [dynamic] added as a lower bound when the RHS is dynamic/like
        pub field_tys: Vec<Ty>,
    }

    pub fn empty() -> T {
        T {
            typed_entries_rev: vec![],
            required_tys_rev: vec![],
            optional_tys_rev: vec![],
            field_tys: vec![],
        }
    }

    pub fn add(
        t: T,
        typed_entry: tast::DestructureTupleEntry,
        optional: bool,
        field_ty: Ty,
        inner_field_tys: Vec<Ty>,
    ) -> T {
        let T {
            mut typed_entries_rev,
            mut required_tys_rev,
            mut optional_tys_rev,
            field_tys,
        } = t;
        typed_entries_rev.insert(0, typed_entry);
        if optional {
            optional_tys_rev.insert(0, field_ty.clone())
        } else {
            required_tys_rev.insert(0, field_ty.clone())
        }
        // `field_ty :: (inner_field_tys @ t.field_tys)`
        let mut new_field_tys = Vec::with_capacity(1 + inner_field_tys.len() + field_tys.len());
        new_field_tys.push(field_ty);
        new_field_tys.extend(inner_field_tys);
        new_field_tys.extend(field_tys);
        T {
            typed_entries_rev,
            required_tys_rev,
            optional_tys_rev,
            field_tys: new_field_tys,
        }
    }
}

/// Add the constraint [rhs_ty <: pattern_ty], handling dynamic and like types.
/// For like types ([~T]), strips dynamic and constrains against [T], then
/// adds [dynamic] as a lower bound for each field tyvar so they resolve
/// to like-wrapped types ([~field_type]). For [dynamic], adds [dynamic]
/// as a lower bound for each field tyvar and skips the shape/tuple
/// constraint. This follows the precedent of [destructure_dynamic] in
/// the [Tdestructure] constraint handler.
fn add_destructure_constraint(
    env: &mut Env,
    pat_pos: &Pos,
    rhs_ty: &Ty,
    pattern_ty: &Ty,
    field_tys: &[Ty],
) {
    let stripped_opt = typing_dynamic_utils::try_strip_dynamic(None, Some(true), env, rhs_ty);
    let is_dynamic = typing_defs::is_dynamic(rhs_ty);
    let rhs_has_dynamic = stripped_opt.is_some() || is_dynamic;
    if is_dynamic {
    } else {
        let effective_rhs = match stripped_opt {
            Some(inner) => inner,
            None => rhs_ty.clone(),
        };
        let ty_err_opt = typing_subtype::sub_type(
            env,
            None,
            None,
            None,
            None,
            effective_rhs,
            pattern_ty.clone(),
            Some(typing_error::reasons_callback::unify_error_at(
                pat_pos.clone(),
            )),
        );
        if let Some(ty_err) = &ty_err_opt {
            typing_error_utils::add_typing_error(ty_err, env)
        }
    }
    if rhs_has_dynamic {
        let dyn_ty = typing_make_type::dynamic(typing_reason::shape_or_tuple_destructure(
            pat_pos.clone(),
        ));
        for field_ty in field_tys {
            let _ty_err_opt = typing_subtype::sub_type(
                env,
                None,
                None,
                None,
                None,
                dyn_ty.clone(),
                field_ty.clone(),
                None,
            );
        }
    }
}

/// `Pos.show_absolute (Pos.to_absolute p)`, for the logger. (`Pos.show_absolute`
/// is the printer that `[@@deriving show]` makes, which is not ported: this is
/// the `Debug` form of the same record. The logger is a stub that ignores it.)
fn show_absolute_pos(p: &Pos) -> String {
    format!("{:?}", crate::pos::to_absolute(p))
}

/// Type a destructure target.
/// @param nullable when true, wraps leaf variable types with [?].
/// Set when any ancestor field is optional.
/// @param field_ty fresh tyvar representing this target's type —
/// the solver resolves it via the subtype constraint emitted by the
/// enclosing shape/tuple.
/// @return [(env, tast_node, inner_field_tys)] where [inner_field_tys]
/// is empty for leaf targets and contains all nested tyvars for
/// shape/tuple targets (used to propagate [dynamic] lower bounds).
fn type_destructure_target(
    nullable: bool,
    assign_pos: &Pos,
    env: &mut Env,
    target: &nast::DestructureTarget,
    field_ty: Ty,
) -> (tast::DestructureTarget, Vec<Ty>) {
    let aast::DestructureTarget(_, _, target_) = target;
    match target_ {
        aast::DestructureTarget_::DtLvar(lid @ aast::Lid(_, x))
            if local_id::get_name(x) == sn::special_idents::PLACEHOLDER =>
        {
            let void_ty = typing_make_type::void(typing_reason::placeholder(lid.0.clone()));
            (
                aast::DestructureTarget(
                    void_ty,
                    tast::dummy_saved_env(),
                    aast::DestructureTarget_::DtLvar(lid.clone()),
                ),
                vec![],
            )
        }
        aast::DestructureTarget_::DtLvar(lid @ aast::Lid(_, x)) => {
            let var_ty = if nullable {
                typing_make_type::nullable(
                    typing_reason::shape_or_tuple_destructure(lid.0.clone()),
                    field_ty,
                )
            } else {
                field_ty
            };
            let var_ty = typing_env::update_reason(env, var_ty, |rhs| {
                typing_reason::flow_assign(rhs, typing_reason::witness(lid.0.clone()))
            });
            set_valid_rvalue(assign_pos.clone(), env, x, var_ty.clone());
            (
                aast::DestructureTarget(
                    var_ty,
                    tast::dummy_saved_env(),
                    aast::DestructureTarget_::DtLvar(lid.clone()),
                ),
                vec![],
            )
        }
        aast::DestructureTarget_::DtWildcard(wpos) => {
            let void_ty = typing_make_type::void(typing_reason::witness(wpos.clone()));
            (
                aast::DestructureTarget(
                    void_ty,
                    tast::dummy_saved_env(),
                    aast::DestructureTarget_::DtWildcard(wpos.clone()),
                ),
                vec![],
            )
        }
        aast::DestructureTarget_::DtShape(shape_pat) => {
            let (te, ty, inner_field_tys) =
                type_shape(nullable, assign_pos, env, &shape_pat.pos, shape_pat, field_ty);
            let typed_shape = match te {
                aast::Expr(_, _, aast::Expr_::DestructureShape(typed_shape)) => *typed_shape,
                _ => {
                    hack_event_logger::invariant_violation_bug(
                        None,
                        Some(&show_absolute_pos(&shape_pat.pos)),
                        None,
                        None,
                        None,
                        "type_shape returned non-DestructureShape expr in DtShape target",
                    );
                    aast::DestructureShape {
                        pos: shape_pat.pos.clone(),
                        fields: vec![],
                        ellipsis: shape_pat.ellipsis,
                    }
                }
            };
            (
                aast::DestructureTarget(
                    ty,
                    tast::dummy_saved_env(),
                    aast::DestructureTarget_::DtShape(typed_shape),
                ),
                inner_field_tys,
            )
        }
        aast::DestructureTarget_::DtTuple(tuple_pat) => {
            let (te, ty, inner_field_tys) =
                type_tuple(nullable, assign_pos, env, &tuple_pat.pos, tuple_pat, field_ty);
            let typed_tuple = match te {
                aast::Expr(_, _, aast::Expr_::DestructureTuple(typed_tuple)) => *typed_tuple,
                _ => {
                    hack_event_logger::invariant_violation_bug(
                        None,
                        Some(&show_absolute_pos(&tuple_pat.pos)),
                        None,
                        None,
                        None,
                        "type_tuple returned non-DestructureTuple expr in DtTuple target",
                    );
                    aast::DestructureTuple {
                        pos: tuple_pat.pos.clone(),
                        entries: vec![],
                        ellipsis: tuple_pat.ellipsis,
                    }
                }
            };
            (
                aast::DestructureTarget(
                    ty,
                    tast::dummy_saved_env(),
                    aast::DestructureTarget_::DtTuple(typed_tuple),
                ),
                inner_field_tys,
            )
        }
    }
}

/// Type a shape destructuring pattern against [rhs_ty].
/// Builds an open shape pattern type with fresh tyvars at the leaves and
/// emits a single [rhs_ty <: pattern_ty] subtype constraint. Structural
/// validation (open/closed, required field coverage, field existence) is
/// deferred to {!Destructure_check} where types are fully resolved.
///
/// Returns [(env, tast_expr, result_ty, field_tys)] where [field_tys]
/// is the list of all tyvars (including those from nested patterns) that
/// need [dynamic] added as a lower bound when the RHS is dynamic or like-typed.
fn type_shape(
    nullable: bool,
    assign_pos: &Pos,
    env: &mut Env,
    pat_pos: &Pos,
    shape_pat: &nast::DestructureShape,
    rhs_ty: Ty,
) -> (tast::Expr, Ty, Vec<Ty>) {
    let r = typing_reason::shape_or_tuple_destructure(pat_pos.clone());
    let mut acc = shape_fields::empty();
    for shape_field in &shape_pat.fields {
        let field_ty = typing_env::fresh_type(env, field_pos_of_ast_sfn(&shape_field.name));
        let (typed_target, inner_field_tys) = type_destructure_target(
            shape_field.optional || nullable,
            assign_pos,
            env,
            &shape_field.target,
            field_ty.clone(),
        );
        acc = shape_fields::add(
            acc,
            aast::DestructureShapeField {
                optional: shape_field.optional,
                name: shape_field.name.clone(),
                target: typed_target,
            },
            TShapeField(t_shape_field::of_ast(
                |p| pos_or_decl::of_raw_pos(p.clone()),
                &shape_field.name,
            )),
            ShapeFieldType {
                optional: shape_field.optional,
                ty: field_ty.clone(),
            },
            field_ty,
            inner_field_tys,
        );
    }
    let shape_fields::T {
        typed_fields_rev,
        shape_map,
        field_tys,
    } = acc;
    // Open with mixed: see comment at the top of this file for why
    let pattern_ty =
        typing_make_type::open_shape(typing_make_type::mixed(r.clone()), r, shape_map);
    // rhs_ty <: pattern_ty
    add_destructure_constraint(env, pat_pos, &rhs_ty, &pattern_ty, &field_tys);
    let mut ds_fields = typed_fields_rev;
    ds_fields.reverse();
    let te = tast::make_typed_expr(
        pat_pos.clone(),
        rhs_ty.clone(),
        aast::Expr_::DestructureShape(Box::new(aast::DestructureShape {
            pos: shape_pat.pos.clone(),
            fields: ds_fields,
            ellipsis: shape_pat.ellipsis,
        })),
    );
    (te, rhs_ty, field_tys)
}

/// Type a tuple destructuring pattern against [rhs_ty].
/// Builds a tuple pattern type with fresh tyvars and a variadic [mixed]
/// tail, then emits a single [rhs_ty <: pattern_ty] subtype constraint.
/// Arity validation is deferred to {!Destructure_check}.
///
/// Returns [(env, tast_expr, result_ty, field_tys)]; see {!type_shape}
/// for the meaning of [field_tys].
fn type_tuple(
    nullable: bool,
    assign_pos: &Pos,
    env: &mut Env,
    pat_pos: &Pos,
    tuple_pat: &nast::DestructureTuple,
    rhs_ty: Ty,
) -> (tast::Expr, Ty, Vec<Ty>) {
    let r = typing_reason::shape_or_tuple_destructure(pat_pos.clone());
    let mut seen_optional = false;
    let mut acc = tuple_entries::empty();
    for tuple_entry in &tuple_pat.entries {
        let entry_ty = typing_env::fresh_type(env, pos_of_target(&tuple_entry.target));
        let optional = seen_optional || tuple_entry.optional;
        let (typed_target, inner_field_tys) = type_destructure_target(
            optional || nullable,
            assign_pos,
            env,
            &tuple_entry.target,
            entry_ty.clone(),
        );
        acc = tuple_entries::add(
            acc,
            aast::DestructureTupleEntry {
                optional,
                target: typed_target,
            },
            optional,
            entry_ty,
            inner_field_tys,
        );
        seen_optional = optional;
    }
    let _seen_optional = seen_optional;
    let tuple_entries::T {
        typed_entries_rev,
        mut required_tys_rev,
        mut optional_tys_rev,
        field_tys,
    } = acc;
    // Variadic mixed tail: permissive for subtyping, arity checks are in {!Destructure_check}
    required_tys_rev.reverse();
    optional_tys_rev.reverse();
    let pattern_ty = crate::typing_defs_core::mk((
        r.clone(),
        Ty_::Ttuple(TupleType {
            required: required_tys_rev,
            optional: optional_tys_rev,
            extra: TupleExtra::Tvariadic(typing_make_type::mixed(r)),
        }),
    ));
    // rhs_ty <: pattern_ty
    add_destructure_constraint(env, pat_pos, &rhs_ty, &pattern_ty, &field_tys);
    let mut dt_entries = typed_entries_rev;
    dt_entries.reverse();
    let te = tast::make_typed_expr(
        pat_pos.clone(),
        rhs_ty.clone(),
        aast::Expr_::DestructureTuple(Box::new(aast::DestructureTuple {
            pos: tuple_pat.pos.clone(),
            entries: dt_entries,
            ellipsis: tuple_pat.ellipsis,
        })),
    );
    (te, rhs_ty, field_tys)
}

/// [shape ~assign_pos ~pat_pos env ds rhs_ty] types shape
/// destructuring pattern [ds] against [rhs_ty]. [assign_pos]
/// is the enclosing assignment/foreach position for variable
/// binding. [pat_pos] is the position of the destructure
/// pattern itself.
pub fn shape(
    assign_pos: Pos,
    pat_pos: Pos,
    env: &mut Env,
    shape_pat: &nast::DestructureShape,
    rhs_ty: Ty,
) -> (tast::Expr, Ty) {
    let targets: Vec<&nast::DestructureTarget> = shape_pat
        .fields
        .iter()
        .map(|shape_field| &shape_field.target)
        .collect();
    check_duplicate_vars(env, &targets);
    let (te, ty, _field_tys) = type_shape(false, &assign_pos, env, &pat_pos, shape_pat, rhs_ty);
    (te, ty)
}

/// [tuple ~assign_pos ~pat_pos env dt rhs_ty] types tuple
/// destructuring pattern [dt] against [rhs_ty].
pub fn tuple(
    assign_pos: Pos,
    pat_pos: Pos,
    env: &mut Env,
    tuple_pat: &nast::DestructureTuple,
    rhs_ty: Ty,
) -> (tast::Expr, Ty) {
    let targets: Vec<&nast::DestructureTarget> = tuple_pat
        .entries
        .iter()
        .map(|tuple_entry| &tuple_entry.target)
        .collect();
    check_duplicate_vars(env, &targets);
    let (te, ty, _field_tys) = type_tuple(false, &assign_pos, env, &pat_pos, tuple_pat, rhs_ty);
    (te, ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(r: &str) -> Ty {
        typing_make_type::generic(typing_reason::none(), r.to_string())
    }

    fn names(tyl: &[Ty]) -> Vec<String> {
        tyl.iter()
            .map(|t| match crate::typing_defs_core::get_node(t) {
                Ty_::Tgeneric(n) => n.clone(),
                _ => panic!("not a generic"),
            })
            .collect()
    }

    /// `field_ty :: (inner_field_tys @ t.field_tys)` at each step, and the
    /// required/optional lists in reverse source order.
    #[test]
    fn tuple_entries_accumulate_as_ocaml_lists() {
        let entry = |optional| aast::DestructureTupleEntry {
            optional,
            target: aast::DestructureTarget(
                ty("x"),
                tast::dummy_saved_env(),
                aast::DestructureTarget_::DtWildcard(Pos::NONE),
            ),
        };
        let acc = tuple_entries::empty();
        let acc = tuple_entries::add(acc, entry(false), false, ty("a"), vec![ty("a1"), ty("a2")]);
        let acc = tuple_entries::add(acc, entry(true), true, ty("b"), vec![]);
        let acc = tuple_entries::add(acc, entry(true), true, ty("c"), vec![ty("c1")]);
        assert_eq!(names(&acc.field_tys), vec!["c", "c1", "b", "a", "a1", "a2"]);
        assert_eq!(names(&acc.required_tys_rev), vec!["a"]);
        assert_eq!(names(&acc.optional_tys_rev), vec!["c", "b"]);
        assert_eq!(
            acc.typed_entries_rev
                .iter()
                .map(|e| e.optional)
                .collect::<Vec<_>>(),
            vec![true, true, false]
        );
    }
}
