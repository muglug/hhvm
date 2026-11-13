// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_shapes.ml`. See `hh/PORTING.md`.
//!
//! # Field names
//!
//! The `.mli` types some field names as `tshape_field_name`
//! ([`TshapeFieldName`]) and some as `TShapeMap.key` ([`t_shape_map::Key`],
//! which wraps it); OCaml has one type for both. The private functions take
//! the one their OCaml uses with `TShapeMap`.
//!
//! # `TShapeMap`
//!
//! `TShapeMap.add` of a new value replaces the key of an existing binding
//! (its positions), which `BTreeMap::insert` does not: see [`tshape_map_add`].
//! `TShapeMap.keys` and `TShapeMap.values` (`Wrapped_map`) give the keys in
//! decreasing order.
//!
//! # Declared types
//!
//! `transform_idx_fun_ty` and `transform_at_fun_ty` build declared types
//! (`hackrs`): `MakeType.mixed`, `generic`, `nullable` and `open_shape` of the
//! declared phase are the `decl_*` functions here (`crate::typing_make_type`
//! builds localized types only), and the field of a declared shape keeps the
//! position of its name in the field rather than in the key
//! ([`decl_shape_field`]).

use std::collections::BTreeMap;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::ast_defs::ShapeFieldName;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::BPos;
use pos::Bytes;
use pos::Symbol;
use pos::ToOxidized;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::ctx::R;
use crate::decl_entry;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::type_mapper;
use crate::type_mapper::TvarExpandingTypeMapper;
use crate::typing_class_pointers;
use crate::typing_coercion;
use crate::typing_defs;
use crate::typing_defs::ClassConstKind;
use crate::typing_defs_core::DeclFunParam;
use crate::typing_defs_core::DeclFunType;
use crate::typing_defs_core::DeclShapeFieldType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::PosByteString;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::PosString;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TaccessType;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::t_shape_map;
use crate::typing_dynamic_utils;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::callback;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_helpers;
use crate::typing_intersection;
use crate::typing_log;
use crate::typing_log::LogStructure;
use crate::typing_make_type as make_type;
use crate::typing_object_get;
use crate::typing_phase;
use crate::typing_print;
use crate::typing_reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;
use crate::typing_reason::Ureason;
use crate::typing_set;
use crate::typing_shape_normalize;
use crate::typing_solver;
use crate::typing_union;
use crate::typing_utils;
use crate::utils;

type TyErr = typing_error::T;

/// `TShapeMap.t`
type TShapeMap<V> = t_shape_map::T<V>;

/// `TShapeMap.add key v m`, for a value `v` that is not the binding of `key`
/// in `m`: the binding, key included, replaces any other one for the field.
fn tshape_map_add<V>(m: &mut TShapeMap<V>, key: t_shape_map::Key, v: V) {
    m.remove(&key);
    m.insert(key, v);
}

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn option_merge_both(e1: Option<TyErr>, e2: Option<TyErr>) -> Option<TyErr> {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// `List.map_env_ty_err_opt` (of `Common.List`), as in `typing_phase.rs`: `f`
/// is applied to the elements from left to right, and `combine_ty_errs` gets
/// the errors in the order the OCaml builds them: the elements are taken five
/// at a time, the errors of each group in order and the groups from the last
/// to the first (after 1001 groups, the errors of the rest of the elements
/// from the last to the first, before the groups).
fn list_map_env_ty_err_opt<X, Y, Errs>(
    env: &mut Env,
    xs: &[X],
    mut f: impl FnMut(&mut Env, &X) -> (Option<TyErr>, Y),
    combine_ty_errs: impl FnOnce(Vec<TyErr>) -> Errs,
) -> (Errs, Vec<Y>) {
    // The OCaml list of errors, last element first.
    let mut rev_errs: Vec<TyErr> = Vec::new();
    let mut ys = Vec::with_capacity(xs.len());
    let mut rest = xs;
    let mut counter = 0;
    loop {
        if rest.is_empty() {
            break;
        }
        let (group, tail) = rest.split_at(std::cmp::min(5, rest.len()));
        let errs: Vec<Option<TyErr>> = group
            .iter()
            .map(|x| {
                let (err, y) = f(env, x);
                ys.push(y);
                err
            })
            .collect();
        // `ty_err_opt1 :: ... :: ty_err_opt5 :: ty_err_opts`
        rev_errs.extend(errs.into_iter().rev().flatten());
        if tail.is_empty() {
            break;
        }
        if counter > 1000 {
            // `rev_map_env_ty_err_opt env ys ~f ~err:(...)`
            for x in tail {
                let (err, y) = f(env, x);
                ys.push(y);
                rev_errs.extend(err);
            }
            break;
        }
        counter += 1;
        rest = tail;
    }
    rev_errs.reverse();
    (combine_ty_errs(rev_errs), ys)
}

/// `Typing_defs.class_const`
type ClassConst = ty::decl::ClassConst<R>;

fn require_shape_key_attribute(cls: &cls::T, class_const: &ClassConst) -> bool {
    (!class_const.is_synthesized)
        && (!class_const.is_shape_key)
        && (!crate::ast_defs::is_c_enum(cls::kind(cls)))
        && !crate::ast_defs::is_c_enum_class(cls::kind(cls))
}

fn shape_key_attribute_error(
    pos: &Pos,
    cls: &cls::T,
    const_name: &str,
    class_const: &ClassConst,
) -> Option<TyErr> {
    if require_shape_key_attribute(cls, class_const) {
        Some(typing_error::shape(
            primary::shape::T::Shape_field_class_const_missing_shape_key_attribute {
                pos: pos.clone(),
                decl_pos: class_const.pos.clone().to_oxidized(),
                class_name: utils::strip_ns(class_const.origin.as_str()).to_string(),
                const_name: const_name.to_string(),
            },
        ))
    } else {
        None
    }
}

fn emit_shape_key_const_value_unresolvable(
    env: &Env,
    pos: &Pos,
    reason_pos: PosOrDecl,
    class_name: String,
    const_name: String,
    const_kind: primary::shape::ShapeKeyConstValueUnresolvableConstKind,
) {
    typing_error_utils::add_typing_error(
        &typing_error::shape(primary::shape::T::Shape_key_const_value_unresolvable {
            pos: pos.clone(),
            reason_pos,
            class_name,
            const_name,
            const_kind,
        }),
        env,
    )
}

fn check_shape_key_value(
    env: &Env,
    pos: &Pos,
    c: &nast::Class_,
    cls: &cls::T,
    cc: &nast::ClassConst,
) {
    let tcopt = typing_env::get_tcopt(env);
    if tcopt.po.include_const_shape_key_values {
        let class_name = utils::strip_ns(&c.name.1).to_string();
        let const_name = cc.id.1.clone();
        let error = match &cc.kind {
            aast::ClassConstKind::CCAbstract(_) => {
                Some(primary::shape::T::Shape_key_class_const_is_abstract {
                    pos: pos.clone(),
                    decl_pos: cc.id.0.clone(),
                    class_name,
                    const_name,
                })
            }
            aast::ClassConstKind::CCConcrete(value)
                if matches!(
                    &value.2,
                    aast::Expr_::Nameof(cid) if matches!(&cid.2, aast::ClassId_::CIself)
                ) && crate::ast_defs::is_c_trait(c.kind) =>
            {
                Some(primary::shape::T::Shape_key_class_const_nameof_self_in_trait {
                    pos: pos.clone(),
                    value_pos: crate::aast_utils::get_expr_pos(value),
                    class_name,
                    const_name,
                })
            }
            aast::ClassConstKind::CCConcrete(value) => {
                let recorded_value = typing_env::get_const(env, cls, &const_name)
                    .and_then(|const_| {
                        typing_defs::const_value::concrete_value(&const_name, &const_.value)
                    });
                match recorded_value {
                    Some(_) => None,
                    None => {
                        emit_shape_key_const_value_unresolvable(
                            env,
                            pos,
                            pos_or_decl::of_raw_pos(crate::aast_utils::get_expr_pos(value)),
                            class_name,
                            const_name,
                            primary::shape::ShapeKeyConstValueUnresolvableConstKind::ClassConst,
                        );
                        None
                    }
                }
            }
        };
        if let Some(error) = error {
            typing_error_utils::add_typing_error(&typing_error::shape(error), env)
        }
    }
}

fn check_shape_key_use(
    env: &Env,
    pos: &Pos,
    cls: &cls::T,
    const_name: &str,
    class_const: &ClassConst,
) {
    if crate::ast_defs::is_c_enum(cls::kind(cls)) {
        let tcopt = typing_env::get_tcopt(env);
        if tcopt.po.include_enum_member_values
            && typing_defs::const_value::concrete_value(const_name, &class_const.value).is_none()
        {
            emit_shape_key_const_value_unresolvable(
                env,
                pos,
                class_const.pos.clone().to_oxidized(),
                utils::strip_ns(class_const.origin.as_str()).to_string(),
                const_name.to_string(),
                primary::shape::ShapeKeyConstValueUnresolvableConstKind::Enum,
            )
        }
    } else if let Some(err) = shape_key_attribute_error(pos, cls, const_name, class_const) {
        typing_error_utils::add_typing_error(&err, env)
    }
}

pub fn check_trait_self_shape_key<Ex, En>(env: &Env, field: &aast::Expr<Ex, En>) {
    let aast::Expr(_, pos, field) = field;
    let key_name = match field {
        aast::Expr_::ClassConst(cc)
            if matches!(&cc.0.2, aast::ClassId_::CIself) && cc.1.1 != "class" =>
        {
            Some(format!("self::{}", cc.1.1))
        }
        aast::Expr_::Nameof(cid) if matches!(&cid.2, aast::ClassId_::CIself) => {
            Some("nameof self".to_string())
        }
        _ => None,
    };
    if let Some(key_name) = key_name {
        match typing_env::get_self_class(env) {
            decl_entry::T::Found(class_) if crate::ast_defs::is_c_trait(cls::kind(&class_)) => {
                let custom_err_config = crate::typechecker_options::custom_error_config(
                    &typing_env::get_tcopt(env),
                );
                crate::typing_attributes::add_naming_error(
                    oxidized::naming_error::NamingError::TraitSelfShapeKey {
                        pos: pos.clone(),
                        key_name,
                    },
                    &custom_err_config,
                )
            }
            decl_entry::T::Found(_)
            | decl_entry::T::DoesNotExist
            | decl_entry::T::NotYetAvailable => {}
        }
    }
}

fn widen_for_refine_shape(
    expr_pos: &Pos,
    field_name: &t_shape_map::Key,
    env: &mut Env,
    ty: Ty,
) -> Option<Ty> {
    typing_log::log_with_level(env, "typing", 1, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(expr_pos.clone()),
            env,
            &[LogStructure::LogHead(
                "widen_for_refine_shape".to_string(),
                vec![LogStructure::LogType("ty".to_string(), ty.clone())],
            )],
        )
    });
    match get_node(&ty) {
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: shape_kind,
            fields,
        })) => match fields.get(field_name) {
            None => {
                let element_ty = typing_env::fresh_type_invariant(env, expr_pos.clone());
                let sft = ShapeFieldType {
                    optional: true,
                    ty: element_ty,
                };
                let mut fields = fields.clone();
                tshape_map_add(&mut fields, field_name.clone(), sft);
                Some(mk((
                    get_reason(&ty).clone(),
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        unknown_value: shape_kind.clone(),
                        fields,
                    })),
                )))
            }
            Some(_) => Some(ty.clone()),
        },
        _ => None,
    }
}

pub fn tshape_field_name_with_ty_err<Ex, En>(
    env: &Env,
    field: &aast::Expr<Ex, En>,
) -> Result<TshapeFieldName, TyErr> {
    let aast::Expr(_, pos, field) = field;
    let resolve_self = |env: &Env| -> Result<PosId, TyErr> {
        let this = match typing_env::get_self_ty(env) {
            None => None,
            Some(c_ty) => match get_node(&c_ty) {
                Ty_::Tclass(sid, _, _) => Some(sid.clone()),
                _ => None,
            },
        };
        match this {
            Some(sid) => Ok(sid),
            None => Err(typing_error::primary(primary::T::Expected_class {
                pos: pos.clone(),
                suffix: None,
            })),
        }
    };
    let p = pos_or_decl::of_raw_pos(pos.clone());
    let map_pos = |(p, x): (&Pos, &String)| (pos_or_decl::of_raw_pos(p.clone()), x.clone());
    let invalid = || {
        let err = primary::shape::T::Invalid_shape_field_name {
            pos: pos.clone(),
            is_empty: false,
        };
        Err(typing_error::shape(err))
    };
    let class_const_field = |sid: PosId, y: &(Pos, String)| -> Result<TshapeFieldName, TyErr> {
        let (yp, y_) = map_pos((&y.0, &y.1));
        match typing_env::get_class(env, &sid.1) {
            decl_entry::T::Found(cls) => match typing_env::get_const(env, &cls, &y.1) {
                None => {}
                Some(class_const) => {
                    // A missing attribute does not prevent resolving the key. Preserve
                    // normal shape typing and refinement even when this diagnostic is
                    // suppressed.
                    check_shape_key_use(env, pos, &cls, &y.1, &class_const)
                }
            },
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
        }
        let field_name = TshapeFieldName::TSFclassConst(sid, PosString(yp, y_));
        Ok(field_name)
    };
    match field {
        aast::Expr_::Int(name) => Ok(TshapeFieldName::TSFregexGroup(PosString(p, name.clone()))),
        aast::Expr_::String(name) => Ok(TshapeFieldName::TSFlitStr(PosByteString(p, name.clone()))),
        aast::Expr_::ClassConst(cc) => {
            let (aast::ClassId(_, _, cid), y) = &**cc;
            match cid {
                aast::ClassId_::CI(_) | aast::ClassId_::CIself if y.1 == "class" => {
                    Err(typing_error::primary(primary::T::Class_const_to_string {
                        pos: pos.clone(),
                        cls_name: typing_class_pointers::string_of_class_id_(cid),
                    }))
                }
                aast::ClassId_::CI(ast_defs::Id(xp, x)) => class_const_field(map_pos((xp, x)), y),
                aast::ClassId_::CIself => {
                    let self_id = resolve_self(env);
                    self_id.and_then(|sid| class_const_field(sid, y))
                }
                aast::ClassId_::CIparent
                | aast::ClassId_::CIstatic
                | aast::ClassId_::CIexpr(_)
                | aast::ClassId_::CIreified(_) => invalid(),
            }
        }
        aast::Expr_::Nameof(cid) => {
            let aast::ClassId(_, _, cid) = &**cid;
            match cid {
                aast::ClassId_::CI(ast_defs::Id(xp, x)) => Ok(TshapeFieldName::TSFclassConst(
                    map_pos((xp, x)),
                    PosString(p, "class".to_string()),
                )),
                aast::ClassId_::CIself => {
                    let self_id = resolve_self(env);
                    self_id.map(|sid| {
                        TshapeFieldName::TSFclassConst(sid, PosString(p, "class".to_string()))
                    })
                }
                aast::ClassId_::CIparent
                | aast::ClassId_::CIstatic
                | aast::ClassId_::CIexpr(_)
                | aast::ClassId_::CIreified(_) => invalid(),
            }
        }
        _ => invalid(),
    }
}

/// Convert an field as Aast.expr into a tshape_field_name then pass the result to the provided function.
/// Handle any conversion error as well.
pub fn do_with_field_expr<Ex, En, Res>(
    env: &Env,
    field: &aast::Expr<Ex, En>,
    with_error: Res,
    do_f: impl FnOnce(TshapeFieldName) -> Res,
) -> Res {
    match tshape_field_name_with_ty_err(env, field) {
        Err(ty_err) => {
            typing_error_utils::add_typing_error(&ty_err, env);
            with_error
        }
        Ok(field_name) => do_f(field_name),
    }
}

fn mixed_for_refinement(env: &Env, r: Reason, ty: &Ty) -> Ty {
    let mixed = make_type::mixed(r.clone());
    if typing_utils::is_supportdyn(env, ty) {
        make_type::supportdyn(r, mixed)
    } else {
        mixed
    }
}

/// Refine a shape with the knowledge that field_name
/// exists. We do this by intersecting with
/// shape(field_name => mixed, ...)
pub fn refine_key_exists(field_name: t_shape_map::Key, pos: Pos, env: &mut Env, shape: Ty) -> Ty {
    let (e1, shape) = typing_solver::expand_type_and_narrow(
        env,
        None,
        None,
        None,
        "a shape",
        |env, ty| widen_for_refine_shape(&pos, &field_name, env, ty),
        pos.clone(),
        shape,
    );
    let mixed = {
        let r = typing_reason::missing_optional_field((
            get_pos(&shape),
            typing_utils::get_printable_shape_field_name(&field_name.0).to_string(),
        ));
        mixed_for_refinement(env, r, &shape)
    };
    if let Some(e1) = e1 {
        typing_error_utils::add_typing_error(&e1, env)
    }
    let mut fields = TShapeMap::new();
    fields.insert(
        field_name,
        ShapeFieldType {
            optional: false,
            ty: mixed.clone(),
        },
    );
    typing_helpers::refine_and_simplify_intersection(
        env,
        false, // is_class
        None,
        typing_reason::witness(pos),
        shape,
        make_type::open_shape(mixed, typing_reason::none(), fields),
    )
}

/// Returns the shape map value for `?'x' => nothing`,
/// which is what we use to signify that x is unset.
fn unset_field_shape_ty_entry(pos: &Pos, field_name: &TshapeFieldName) -> ShapeFieldType {
    ShapeFieldType {
        optional: true,
        ty: make_type::nothing(typing_reason::unset_field((
            pos.clone(),
            typing_utils::get_printable_shape_field_name(field_name).to_string(),
        ))),
    }
}

/// Refine a shape with the knowledge that field_name
/// does not exists. We do this by intersecting with
/// shape(?field_name => nothing, ...)
pub fn refine_not_key_exists(
    field_name: t_shape_map::Key,
    pos: Pos,
    env: &mut Env,
    shape_ty: Ty,
) -> Ty {
    let (e1, shape_ty) = typing_solver::expand_type_and_narrow(
        env,
        None,
        None,
        None,
        "a shape",
        |env, ty| widen_for_refine_shape(&pos, &field_name, env, ty),
        pos.clone(),
        shape_ty,
    );
    if let Some(e1) = e1 {
        typing_error_utils::add_typing_error(&e1, env)
    }
    let r = typing_reason::witness(pos.clone());
    let kind = mixed_for_refinement(env, r.clone(), &shape_ty);
    let entry = unset_field_shape_ty_entry(&pos, &field_name.0);
    let mut fields = TShapeMap::new();
    fields.insert(field_name, entry);
    let shape_reason = get_reason(&shape_ty).clone();
    typing_helpers::refine_and_simplify_intersection(
        env,
        false, // is_class
        None,
        r,
        shape_ty,
        make_type::open_shape(kind, shape_reason, fields),
    )
}

/// `refine_f` is given the environment, the shape type and the field name.
fn refine_handle_errors<Ex, En>(
    env: &mut Env,
    shape_ty: Ty,
    field: &aast::Expr<Ex, En>,
    refine_f: impl FnOnce(&mut Env, Ty, TshapeFieldName) -> (Option<TyErr>, Ty),
) -> Ty {
    // `do_with_field_expr` reads the environment (it reports a bad field
    // name in it); `refine_f` goes on with the same environment.
    let env_for_field = env.clone();
    let (ty_err_opt, res) = do_with_field_expr(
        &env_for_field,
        field,
        (None, shape_ty.clone()),
        |field_name| refine_f(env, shape_ty, field_name),
    );
    if let Some(ty_err) = ty_err_opt {
        typing_error_utils::add_typing_error(&ty_err, env)
    }
    res
}

/// Mark [field_name] absent in a single concrete shape. A closed shape simply
/// drops the field; an open shape gets an explicit [?field => nothing] entry so
/// its unknown tail cannot re-supply the field. Returns [None] when there is
/// nothing to do (a closed shape that doesn't have the field), leaving the
/// element untouched.
fn mark_field_absent(
    pos: &Pos,
    field_name: &t_shape_map::Key,
    s: &ShapeTypeSimple,
) -> Option<ShapeTypeSimple> {
    if typing_defs::is_nothing(&s.unknown_value) {
        if s.fields.contains_key(field_name) {
            let mut s_fields = s.fields.clone();
            s_fields.remove(field_name);
            Some(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: s.unknown_value.clone(),
                fields: s_fields,
            })
        } else {
            None
        }
    } else {
        let mut s_fields = s.fields.clone();
        tshape_map_add(
            &mut s_fields,
            field_name.clone(),
            unset_field_shape_ty_entry(pos, &field_name.0),
        );
        Some(ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: s.unknown_value.clone(),
            fields: s_fields,
        })
    }
}

fn shape_type_proves_field_absent(field_name: &t_shape_map::Key, shape_ty: &ShapeType) -> bool {
    match shape_ty {
        ShapeType::ShapeSimple(ShapeTypeSimple {
            fields: s_fields,
            unknown_value: s_unknown_value,
            ..
        }) => match s_fields.get(field_name) {
            Some(ShapeFieldType {
                optional: true,
                ty: sft_ty,
            }) => typing_defs::is_nothing(sft_ty),
            Some(_) => false,
            None => typing_defs::is_nothing(s_unknown_value),
        },
        ShapeType::ShapeSplat(_) => {
            // A residual splat (unresolved elements) cannot prove absence.
            false
        }
    }
}

/// Whether localized upper bound [bound] proves that [field_name] is absent:
/// viewed as a shape, it either lists the field as [?f => nothing] or omits it
/// while being closed. Since an opaque type is a subtype of its bound, a bound
/// that cannot contain the field means the opaque type cannot either. Ah open shape
/// or one that lists the field as required or optional-and-inhabited, does not
/// prove absence.
fn bound_proves_field_absent(env: &mut Env, bound: Ty, field_name: &t_shape_map::Key) -> bool {
    let bound = typing_env::expand_type(env, bound);
    match get_node(&bound) {
        Ty_::Tshape(shape_ty) => {
            let (_err, view) = typing_shape_normalize::normalize_shape_type(
                None,
                get_reason(&bound).clone(),
                shape_ty.clone(),
                env,
            );
            match view {
                typing_shape_normalize::NormalizeResult::NormalizedShape(shape_ty) => {
                    shape_type_proves_field_absent(field_name, &shape_ty)
                }
                typing_shape_normalize::NormalizeResult::NormalizedUnion(_)
                | typing_shape_normalize::NormalizeResult::NormalizedIntersection(_) => false,
                // An uninhabited bound has no values, so the field is vacuously absent.
                typing_shape_normalize::NormalizeResult::NormalizedBottom => true,
            }
        }
        _ => false,
    }
}

fn generic_bound_proves_field_absent(
    env: &mut Env,
    name: &str,
    field_name: &t_shape_map::Key,
) -> bool {
    let bounds = typing_set::elements(&typing_env::get_upper_bounds(env, name));
    let mut acc = false;
    for b in bounds {
        acc = if acc {
            true
        } else {
            bound_proves_field_absent(env, b, field_name)
        };
    }
    acc
}

/// Remove [field_name] from the elements of a shape splat.
///
/// Merging is rightmost-wins, so marking the field absent on a single element can
/// be undone by another element that supplies it (an [?f => nothing] unions back
/// to required against any [f] on either side); we therefore edit every concrete
/// element. An opaque element (a type parameter, type variable or nested splat)
/// cannot be edited, and because [Shapes::removeKey] takes the shape [inout] its
/// type is invariant, so we may not change that element either. The removal is
/// therefore sound only when every opaque element provably lacks the field (a
/// bound that is a closed shape without it, or lists it as [?f => nothing]).
/// Otherwise the element might contain the field at runtime while the unchanged
/// type still claims it, so we report an error and leave the shape unchanged.
/// Concrete elements are edited as usual.
fn remove_field_from_splat(
    env: &mut Env,
    pos: &Pos,
    ss_elems: &[Ty],
    field_name: &t_shape_map::Key,
) -> (Option<TyErr>, Vec<Ty>) {
    let ss_elems: Vec<Ty> = ss_elems
        .iter()
        .map(|ty| typing_env::expand_type(env, ty.clone()))
        .collect();
    let mut blocked = false;
    for ty in &ss_elems {
        blocked = if blocked {
            true
        } else {
            match get_node(ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(_)) => false,
                Ty_::Tgeneric(name) => {
                    let absent = generic_bound_proves_field_absent(env, name, field_name);
                    !absent
                }
                Ty_::Tnewtype(_, _, bound) => {
                    let absent = bound_proves_field_absent(env, bound.clone(), field_name);
                    !absent
                }
                _ => {
                    // A type variable, nested splat or other non-editable element may
                    // contain the field; we cannot prove otherwise.
                    true
                }
            }
        };
    }
    if blocked {
        let name = typing_utils::get_printable_shape_field_name(&field_name.0);
        let err = typing_error::primary(primary::T::Generic_unify {
            pos: pos.clone(),
            msg: format!(
                "Cannot remove field `{}`: a type parameter spread into this shape may contain it, so the removal cannot be represented (the shape is passed `inout`, making its type invariant). The type parameter's bound must guarantee the field is absent -- a closed shape without it, or `?{} => nothing`",
                name, name
            ),
        });
        (Some(err), ss_elems)
    } else {
        let new_elems = ss_elems
            .iter()
            .map(|ty| match get_node(ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
                    match mark_field_absent(pos, field_name, s) {
                        Some(s) => mk((
                            get_reason(ty).clone(),
                            Ty_::Tshape(ShapeType::ShapeSimple(s)),
                        )),
                        None => ty.clone(),
                    }
                }
                _ => ty.clone(),
            })
            .collect();
        (None, new_elems)
    }
}

/// The `refine_f` of `refine_handle_unions_dyn`: given the stripped shape, the
/// type of its unknown fields, its fields and the field name.
type RefineSimpleShape<'a> =
    &'a dyn Fn(&Ty, &Ty, &TShapeMap<ShapeFieldType>, &TshapeFieldName) -> Ty;

fn refine_handle_unions_dyn(
    pos: &Pos,
    refine_f: RefineSimpleShape<'_>,
    env: &mut Env,
    shape_ty: Ty,
    field_name: TshapeFieldName,
) -> (Option<TyErr>, Ty) {
    fn go(
        pos: &Pos,
        refine_f: RefineSimpleShape<'_>,
        field_name: &TshapeFieldName,
        supportdyn: bool,
        env: &mut Env,
        shape_ty: Ty,
    ) -> (Option<TyErr>, Ty) {
        let (e1, shape) = typing_solver::expand_type_and_solve(
            env,
            Some(false), // freshen
            "a shape",
            pos.clone(),
            shape_ty,
        );
        let (supportdyn2, stripped_shape) = typing_utils::strip_supportdyn(env, shape.clone());
        let supportdyn = supportdyn || supportdyn2;
        match get_node(&stripped_shape) {
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields,
            })) => {
                let result = refine_f(&stripped_shape, shape_kind, fields, field_name);
                (
                    e1,
                    if supportdyn {
                        let r = get_reason(&result).clone();
                        make_type::supportdyn(r, result)
                    } else {
                        result
                    },
                )
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                let (e2, new_elems) = remove_field_from_splat(
                    env,
                    pos,
                    ss_elems,
                    &t_shape_map::TShapeField(field_name.clone()),
                );
                // Removing a field can empty the element it was on, leaving `...shape()`
                // (the merge identity) in the row, so rebuild through the canonical
                // constructor rather than reassembling the splat by hand. Safe to
                // ignore the error since removing a field can't introduce a malformed shape
                let (_e3, result) = typing_shape_normalize::splat(
                    None,
                    typing_reason::witness(pos.clone()),
                    new_elems,
                    env,
                );
                (
                    option_merge_both(e1, e2),
                    if supportdyn {
                        make_type::supportdyn(get_reason(&result).clone(), result)
                    } else {
                        result
                    },
                )
            }
            Ty_::Tunion(tyl) => {
                let (e2, tyl) = list_map_env_ty_err_opt(
                    env,
                    tyl,
                    |env, ty| go(pos, refine_f, field_name, supportdyn, env, ty.clone()),
                    typing_error::multiple_opt,
                );
                let tyl: Vec<Ty> = tyl
                    .into_iter()
                    .filter(|ty| !typing_defs::is_nothing(ty))
                    .collect();
                let result = mk((typing_reason::witness(pos.clone()), Ty_::Tunion(tyl)));
                (option_merge_both(e1, e2), result)
            }
            _ => (
                e1,
                if supportdyn {
                    let r = get_reason(&shape).clone();
                    make_type::supportdyn(r, shape)
                } else {
                    shape
                },
            ),
        }
    }
    go(pos, refine_f, &field_name, false, env, shape_ty)
}

fn refine_handle_errors_unions_dyn<Ex, En>(
    env: &mut Env,
    pos: Pos,
    shape_ty: Ty,
    field: &aast::Expr<Ex, En>,
    refine_f: RefineSimpleShape<'_>,
) -> Ty {
    refine_handle_errors(env, shape_ty, field, |env, shape_ty, field_name| {
        refine_handle_unions_dyn(&pos, refine_f, env, shape_ty, field_name)
    })
}

/// Remove a field from a shape.
pub fn remove_key<Ex, En>(pos: Pos, env: &mut Env, shape_ty: Ty, field: &aast::Expr<Ex, En>) -> Ty {
    let pos_ = pos.clone();
    refine_handle_errors_unions_dyn(
        env,
        pos,
        shape_ty,
        field,
        &move |_stripped_shape: &Ty,
               shape_kind: &Ty,
               fields: &TShapeMap<ShapeFieldType>,
               field_name: &TshapeFieldName| {
            let mut s_fields = fields.clone();
            let key = t_shape_map::TShapeField(field_name.clone());
            if typing_defs::is_nothing(shape_kind) {
                s_fields.remove(&key);
            } else {
                tshape_map_add(&mut s_fields, key, unset_field_shape_ty_entry(&pos_, field_name));
            }
            mk((
                typing_reason::witness(pos_.clone()),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: TypeOrigin::MissingOrigin,
                    unknown_value: shape_kind.clone(),
                    fields: s_fields,
                })),
            ))
        },
    )
}

/// Refine the type of a shape knowing that a call to Shapes::idx is not null.
/// This means that the shape now has the field, and that the type for this
/// field is not nullable.
/// We stay quite liberal here: we add the field to the shape type regardless
/// of whether this field can be here at all. Errors will anyway be raised
/// elsewhere when typechecking the call to Shapes::idx. This allows for more
/// useful typechecking of incomplete code (code in the process of being
/// written).
fn shapes_idx_not_null_with_ty_err(
    field_p: &Pos,
    env: &mut Env,
    shape_ty: Ty,
    field: TshapeFieldName,
) -> (Option<TyErr>, Ty) {
    let field = t_shape_map::TShapeField(field);
    let (e1, shape_ty) = typing_solver::expand_type_and_narrow(
        env,
        None,
        None,
        None,
        "a shape",
        |env, ty| widen_for_refine_shape(field_p, &field, env, ty),
        field_p.clone(),
        shape_ty,
    );
    let refine_type = |env: &mut Env, shape_ty: Ty| -> Ty {
        typing_utils::map_supportdyn(env, shape_ty, |env, shape_ty| {
            let shape_ty = typing_env::expand_type(env, shape_ty);
            match get_node(&shape_ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: _,
                    fields: ftm,
                    unknown_value: shape_kind,
                })) => {
                    let field_type = {
                        let sft_ty = match ftm.get(&field) {
                            Some(ShapeFieldType { ty: sft_ty, .. }) => sft_ty.clone(),
                            None => shape_kind.clone(),
                        };
                        let sft_ty = typing_intersection::intersect_with_nonnull(
                            env,
                            pos_or_decl::of_raw_pos(field_p.clone()),
                            sft_ty,
                        );
                        ShapeFieldType {
                            optional: false,
                            ty: sft_ty,
                        }
                    };
                    let mut ftm = ftm.clone();
                    tshape_map_add(&mut ftm, field.clone(), field_type);
                    mk((
                        get_reason(&shape_ty).clone(),
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            fields: ftm,
                            unknown_value: shape_kind.clone(),
                        })),
                    ))
                }
                _ => {
                    // This should be an error, but it is already raised when
                    // typechecking the call to Shapes::idx
                    shape_ty.clone()
                }
            }
        })
    };
    match get_node(&shape_ty) {
        Ty_::Tunion(tyl) => {
            let r = get_reason(&shape_ty).clone();
            let tyl: Vec<Ty> = tyl.iter().map(|ty| refine_type(env, ty.clone())).collect();
            let ty = typing_union::union_list(env, None, r, &tyl);
            (e1, ty)
        }
        _ => {
            let ty = refine_type(env, shape_ty.clone());
            (None, ty)
        }
    }
}

/// Refine the type of a shape knowing that a call to Shapes::idx is not null.
/// This means that the shape now has the field, and that the type for this
/// field is not nullable.
/// We stay quite liberal here: we add the field to the shape type regardless
/// of whether this field can be here at all. Errors will anyway be raised
/// elsewhere when typechecking the call to Shapes::idx. This allows for more
/// useful typechecking of incomplete code (code in the process of being
/// written).
pub fn shapes_idx_not_null(env: &mut Env, shape_ty: Ty, fld: &nast::Expr) -> Ty {
    let aast::Expr(_, p, _) = fld;
    refine_handle_errors(env, shape_ty, fld, |env, shape_ty, field| {
        shapes_idx_not_null_with_ty_err(p, env, shape_ty, field)
    })
}

/// /!\ This is not used fur typing Shapes::idx anymore,
/// only to type field access on the LHS of ??
///
/// Typing rules for Shapes::idx
///
///     e : ?shape(?sfn => t, ...)
///     ----------------------------
///     Shapes::idx(e, sfn) : ?t
///
///  Typing rules when the shape has a like type:
///
///     e : ~?shape(?sfn => t, ...)
///     ----------------------------
///     Shapes::idx(e, sfn) : ~?t
///
/// [`idx_without_default env shape_type field`] returns the type of
/// Shapes::idx($s) where $s has type [shape_type]
pub fn idx_without_default(
    env: &mut Env,
    expr_pos: Pos,
    shape_pos: Pos,
    shape_ty: Ty,
    field_name: TshapeFieldName,
) -> Ty {
    typing_log::log_with_level(env, "shapes", 1, || {
        typing_log::log_types(
            &pos_or_decl::of_raw_pos(expr_pos.clone()),
            env,
            &[LogStructure::LogHead(
                "Typing_shapes.idx_without_default".to_string(),
                vec![
                    LogStructure::LogType("Shape type".to_string(), shape_ty.clone()),
                    LogStructure::LogHead(
                        format!("Field: {}", t_shape_field::name(&field_name)),
                        vec![],
                    ),
                ],
            )],
        )
    });
    let shape_ty = typing_env::expand_type(env, shape_ty);
    let res = typing_env::fresh_type(env, expr_pos);
    let (ty_err_opt, res) = {
        let fake_super_shape_ty = {
            let r = typing_reason::shape((shape_pos.clone(), "Shapes::idx".to_string()));
            // Since this shape is only used as a supertype, it is safe to use mixed
            // as the kind, regardless of --everything-sdt
            let mut fields = TShapeMap::new();
            fields.insert(
                t_shape_map::TShapeField(field_name),
                ShapeFieldType {
                    optional: true,
                    ty: res.clone(),
                },
            );
            make_type::open_shape(make_type::mixed(r.clone()), r, fields)
        };
        let nullable_super_shape = mk((typing_reason::none(), Ty_::Toption(fake_super_shape_ty)));
        let super_shape =
            make_type::locl_like(typing_reason::witness(shape_pos.clone()), nullable_super_shape);
        let ty_err_opt = typing_coercion::coerce_type(
            None,
            None,
            None,
            shape_pos,
            Ureason::URparam,
            env,
            shape_ty.clone(),
            super_shape,
            Enforcement::Unenforced,
            callback::unify_error(),
        );
        let res = typing_utils::union(env, None, None, res, make_type::null(typing_reason::none()));
        (ty_err_opt, res)
    };
    if let Some(ty_err) = ty_err_opt {
        typing_error_utils::add_typing_error(&ty_err, env)
    }
    let stripped_shape_ty = typing_dynamic_utils::strip_dynamic(env, shape_ty.clone());
    match get_node(&stripped_shape_ty) {
        Ty_::Tnewtype(n, _, _) if n == sn::classes::SUPPORT_DYN => {
            let r = get_reason(&shape_ty).clone();
            typing_utils::make_supportdyn(r, env, res)
        }
        _ => res,
    }
}

/// `super#on_type` in a mapper that inherits
/// `Type_mapper.tvar_expanding_type_mapper` and overrides `on_type`: the
/// dispatch of the inherited `on_type`, which calls the methods of `this` (so
/// the overriding ones too, as `this#...`).
fn tvar_expanding_type_mapper_on_type<M: TvarExpandingTypeMapper + ?Sized>(
    this: &mut M,
    env: &mut Env,
    ty: Ty,
) -> Ty {
    let Ty(r, ty) = ty;
    let r = this.on_reason(env, r);
    match crate::typing_defs_core::unwrap_node(ty) {
        Ty_::Tvar(n) => this.on_tvar(env, r, n),
        Ty_::Tnonnull => this.on_tnonnull(env, r),
        Ty_::Tany(_) => this.on_tany(env, r),
        Ty_::Tprim(p) => this.on_tprim(env, r, p),
        Ty_::Ttuple(t) => this.on_ttuple(env, r, t),
        Ty_::Tunion(tyl) => this.on_tunion(env, r, tyl),
        Ty_::Tintersection(tyl) => this.on_tintersection(env, r, tyl),
        Ty_::Toption(ty) => this.on_toption(env, r, ty),
        Ty_::Tfun(fun_type) => this.on_tfun(env, r, std::rc::Rc::unwrap_or_clone(fun_type)),
        Ty_::Tgeneric(x) => this.on_tgeneric(env, r, x),
        Ty_::Tnewtype(x, tyl, ty) => this.on_tnewtype(env, r, x, tyl, ty),
        Ty_::Tdependent(x, ty) => this.on_tdependent(env, r, x, ty),
        Ty_::Tclass(x, e, tyl) => this.on_tclass(env, r, x, e, tyl),
        Ty_::Tdynamic(sv) => this.on_tdynamic(env, r, sv),
        Ty_::Tshape(s) => this.on_tshape(env, r, s),
        Ty_::TvecOrDict(ty1, ty2) => this.on_tvec_or_dict(env, r, ty1, ty2),
        Ty_::Taccess(TaccessType(ty, id)) => this.on_taccess(env, r, ty, id),
        Ty_::Tneg(ty) => this.on_neg_type(env, r, ty),
        Ty_::Tlabel(name) => this.on_tlabel(env, r, name),
        Ty_::TclassPtr(ty) => this.on_tclass_ptr(env, r, ty),
    }
}

/// The mapper of `to_collection`, with the variables it closes over.
struct ToCollectionMapper<'a> {
    pos: &'a Pos,
    res: &'a Ty,
    return_type: &'a mut dyn FnMut(&mut Env, Reason, Ty, Ty) -> Ty,
}

impl TvarExpandingTypeMapper for ToCollectionMapper<'_> {
    fn on_tshape(&mut self, env: &mut Env, r: Reason, s: ShapeType) -> Ty {
        match s {
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                let (_err, result) = typing_shape_normalize::merge(None, ss_elems, env);
                match result {
                    typing_shape_normalize::MergeResult::Full(ty, _) => self.on_type(env, ty),
                    typing_shape_normalize::MergeResult::EmptyShape(_) => self.on_tshape(
                        env,
                        r.clone(),
                        ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: make_type::nothing(r),
                            fields: TShapeMap::new(),
                        }),
                    ),
                    typing_shape_normalize::MergeResult::Partial(_, _)
                    | typing_shape_normalize::MergeResult::Union(_)
                    | typing_shape_normalize::MergeResult::Intersection(_) => {
                        let value = make_type::mixed(r.clone());
                        let key = make_type::arraykey(r);
                        (self.return_type)(env, get_reason(self.res).clone(), key, value)
                    }
                }
            }
            ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields: fdm,
            }) => {
                // The key type is the union of the types of the known fields,
                // or arraykey if there may be unknown fields (open shape)
                let key = if !typing_utils::is_nothing(env, &shape_kind) {
                    make_type::arraykey(r.clone())
                } else {
                    // `TShapeMap.keys fdm`: in decreasing order.
                    let mut keys = Vec::with_capacity(fdm.len());
                    for key in fdm.keys().rev() {
                        let ty = match &key.0 {
                            TshapeFieldName::TSFregexGroup(PosString(p, _)) => {
                                make_type::int(typing_reason::witness_from_decl(p.clone()))
                            }
                            TshapeFieldName::TSFlitStr(PosByteString(p, _)) => {
                                make_type::string(typing_reason::witness_from_decl(p.clone()))
                            }
                            TshapeFieldName::TSFclassConst((_, cid), PosString(_, mid)) => {
                                match typing_env::get_class(env, cid) {
                                    decl_entry::T::Found(class_) => {
                                        match typing_env::get_const(env, &class_, mid) {
                                            Some(const_) => {
                                                let (ty_err_opt, lty) =
                                                    typing_phase::localize_no_subst(
                                                        env, true, &const_.ty,
                                                    );
                                                if let Some(ty_err) = ty_err_opt {
                                                    typing_error_utils::add_typing_error(
                                                        &ty_err, env,
                                                    )
                                                }
                                                lty
                                            }
                                            None => typing_env::fresh_type_error(
                                                env,
                                                self.pos.clone(),
                                            ),
                                        }
                                    }
                                    decl_entry::T::DoesNotExist
                                    | decl_entry::T::NotYetAvailable => {
                                        typing_env::fresh_type_error(env, self.pos.clone())
                                    }
                                }
                            }
                        };
                        keys.push(ty);
                    }
                    typing_union::union_list(env, None, r.clone(), &keys)
                };
                // The value type is the union of the types of the known fields together
                // with the type of the unknown fields (open shape, typically mixed or supportdyn<mixed>)
                let value = {
                    // If the unknown fields have type mixed then that's the type of values: no need for union
                    if typing_utils::is_mixed(env, &shape_kind) {
                        shape_kind
                    } else {
                        // Otherwise first filter out subtypes (common case,
                        // as unknown fields are likely supportdyn<mixed>)
                        // and then construct the union.
                        // (`TShapeMap.values fdm`: in decreasing order of the keys.)
                        let mut values = vec![shape_kind.clone()];
                        for ShapeFieldType { ty: sft_ty, .. } in fdm.values().rev() {
                            if typing_utils::is_sub_type(env, sft_ty, &shape_kind) {
                            } else {
                                values.push(sft_ty.clone())
                            }
                        }
                        typing_union::union_list(env, None, r, &values)
                    }
                };
                (self.return_type)(env, get_reason(self.res).clone(), key, value)
            }
        }
    }

    fn on_tunion(&mut self, env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
        let tyl: Vec<Ty> = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
        typing_union::union_list(env, None, r, &tyl)
    }

    fn on_tintersection(&mut self, env: &mut Env, r: Reason, tyl: Vec<Ty>) -> Ty {
        let tyl: Vec<Ty> = tyl.into_iter().map(|ty| self.on_type(env, ty)).collect();
        typing_intersection::intersect_list(env, r, &tyl)
    }

    fn on_type(&mut self, env: &mut Env, ty: Ty) -> Ty {
        let (_e1, ty) =
            typing_solver::expand_type_and_solve(env, None, "a shape", self.pos.clone(), ty);
        match get_node(&ty) {
            Ty_::Tdynamic(_) => {
                // This makes it so that to_collection on a dynamic value returns a dynamic
                // value instead of the standard dict<arraykey, mixed> declared in the HHI,
                // which would otherwise subsume any other inferred type due to covariance.
                ty
            }
            Ty_::Tvar(_) | Ty_::Tshape(_) | Ty_::Tunion(_) | Ty_::Tintersection(_) => {
                tvar_expanding_type_mapper_on_type(self, env, ty)
            }
            // Look through bound on newtype, including supportdyn. We assume that
            // supportdyn has already been pushed into the type of unknown fields
            Ty_::Tnewtype(c, tyl, _) => {
                let (c, tyl) = (c.clone(), tyl.clone());
                let r = get_reason(&ty).clone();
                let ty = typing_utils::get_newtype_super(env, r, &c, &tyl);
                tvar_expanding_type_mapper_on_type(self, env, ty)
            }
            _ => self.res.clone(),
        }
    }
}

fn to_collection(
    env: &mut Env,
    pos: &Pos,
    shape_ty: Ty,
    res: &Ty,
    return_type: &mut dyn FnMut(&mut Env, Reason, Ty, Ty) -> Ty,
) -> Ty {
    let mut mapper = ToCollectionMapper {
        pos,
        res,
        return_type,
    };
    type_mapper::fresh_env(env);
    mapper.on_type(env, shape_ty)
}

pub fn to_dict(env: &mut Env, pos: Pos, shape_ty: Ty, res: Ty) -> type_mapper::Result {
    let supports_dynamic = typing_utils::is_supportdyn_use_tyvar_bounds(env, &shape_ty);
    let (e1, shape_ty) =
        typing_solver::expand_type_and_solve(env, None, "a shape", pos.clone(), shape_ty);
    if let Some(e1) = e1 {
        typing_error_utils::add_typing_error(&e1, env)
    }
    let shape_ty = typing_utils::get_base_type(Some(true), env, shape_ty);
    let result = to_collection(env, &pos, shape_ty, &res, &mut |_env, r, key, value| {
        make_type::dict(r, key, value)
    });
    if supports_dynamic {
        typing_utils::make_supportdyn(get_reason(&result).clone(), env, result)
    } else {
        result
    }
}

fn shape_field_pos(sfn: &ShapeFieldName) -> Pos {
    match sfn {
        ShapeFieldName::SFlitStr((p, _)) | ShapeFieldName::SFclassname(ast_defs::Id(p, _)) => {
            p.clone()
        }
        ShapeFieldName::SFclassConst(ast_defs::Id(cls_pos, _), (mem_pos, _)) => {
            crate::pos::btw(cls_pos, mem_pos)
        }
    }
}

/// If the key is a class constant, get its class name and type.
/// (`get_field_info` of `check_shape_keys_validity`.)
fn get_field_info(env: &mut Env, key: &ShapeFieldName) -> (Pos, Option<(String, Ty)>) {
    let key_pos = shape_field_pos(key);
    // Empty strings or literals that start with numbers are not
    // permitted as shape field names.
    match key {
        ShapeFieldName::SFlitStr((_, key_name)) => {
            if key_name.is_empty() {
                typing_error_utils::add_typing_error(
                    &typing_error::shape(primary::shape::T::Invalid_shape_field_name {
                        pos: key_pos.clone(),
                        is_empty: true,
                    }),
                    env,
                )
            }
            (key_pos, None)
        }
        ShapeFieldName::SFclassname(ast_defs::Id(p, cls)) => match typing_env::get_class(env, cls) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                let ty = typing_env::fresh_type_error(env, p.clone());
                (key_pos, Some((cls.clone(), ty)))
            }
            decl_entry::T::Found(cd) => {
                // Match the sketchy Tany logic of C::class keys
                match typing_env::get_const(env, &cd, "class") {
                    None => {
                        let ty = typing_env::fresh_type_error(env, p.clone());
                        (key_pos, Some((cls.clone(), ty)))
                    }
                    Some(cc) => {
                        let (ty_err_opt, ty) = typing_phase::localize_no_subst(env, true, &cc.ty);
                        if let Some(ty_err) = ty_err_opt {
                            typing_error_utils::add_typing_error(&ty_err, env)
                        }
                        (key_pos, Some((cls.clone(), ty)))
                    }
                }
            }
        },
        ShapeFieldName::SFclassConst(ast_defs::Id(_p, cls), (p, y)) => {
            match typing_env::get_class(env, cls) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                    let ty = typing_env::fresh_type_error(env, p.clone());
                    (key_pos, Some((cls.clone(), ty)))
                }
                decl_entry::T::Found(cd) => match typing_env::get_const(env, &cd, y) {
                    None => {
                        let err = typing_object_get::smember_not_found(
                            p.clone(),
                            true,  // is_const
                            false, // is_method
                            false, // is_function_pointer
                            &cd,
                            y.clone(),
                            callback::unify_error(),
                        );
                        typing_error_utils::add_typing_error(&err, env);
                        let ty = typing_env::fresh_type_error(env, p.clone());
                        (key_pos, Some((cls.clone(), ty)))
                    }
                    Some(cc) => {
                        match cc.kind {
                            ClassConstKind::CCAbstract(_) => {
                                typing_error_utils::add_typing_error(
                                    &typing_error::shape(
                                        primary::shape::T::Abstract_shape_field_const {
                                            pos: key_pos.clone(),
                                            decl_pos: cc.pos.clone().to_oxidized(),
                                            name: format!("{}::{}", cls, y),
                                        },
                                    ),
                                    env,
                                )
                            }
                            ClassConstKind::CCConcrete => {}
                        }
                        check_shape_key_use(env, &key_pos, &cd, y, &cc);
                        let (ty_err_opt, ty) = typing_phase::localize_no_subst(env, true, &cc.ty);
                        if let Some(ty_err) = ty_err_opt {
                            typing_error_utils::add_typing_error(&ty_err, env)
                        }
                        let r = typing_reason::witness(key_pos.clone());
                        let on_error = {
                            let env_of_ty_name = env.clone();
                            let ty_of_ty_name = ty.clone();
                            typing_error::reasons_callback::always(typing_error::shape(
                                primary::shape::T::Invalid_shape_field_type {
                                    pos: key_pos.clone(),
                                    ty_pos: get_pos(&ty),
                                    ty_name: Lazy::new(move || {
                                        typing_print::error(None, &env_of_ty_name, &ty_of_ty_name)
                                    }),
                                    trail: vec![],
                                },
                            ))
                        };
                        let e2 = typing_utils::sub_type(
                            env,
                            None,
                            None,
                            None,
                            Some(false),
                            ty.clone(),
                            make_type::arraykey(r),
                            Some(on_error),
                        );
                        if let Some(e2) = e2 {
                            typing_error_utils::add_typing_error(&e2, env)
                        }
                        (key_pos, Some((cls.clone(), ty)))
                    }
                },
            }
        }
    }
}

/// `check_field witness_pos witness_info env key` of
/// `check_shape_keys_validity`.
fn check_field(
    witness_pos: &Pos,
    witness_info: &Option<(String, Ty)>,
    env: &mut Env,
    key: &ShapeFieldName,
) -> Option<TyErr> {
    let (key_pos, key_info) = get_field_info(env, key);
    let ty_errs: Vec<TyErr> = match (witness_info, &key_info) {
        (Some(_), None) => vec![typing_error::shape(
            primary::shape::T::Invalid_shape_field_literal {
                pos: key_pos,
                witness_pos: witness_pos.clone(),
            },
        )],
        (None, Some(_)) => vec![typing_error::shape(
            primary::shape::T::Invalid_shape_field_const {
                pos: key_pos,
                witness_pos: witness_pos.clone(),
            },
        )],
        (None, None) => vec![],
        (Some((cls1, ty1)), Some((cls2, ty2))) => {
            // (The elements of the OCaml list are evaluated from the last to
            // the first.)
            let type_mismatch = if typing_utils::is_tyvar_error(env, ty1)
                || typing_utils::is_tyvar_error(env, ty2)
            {
                None
            } else {
                let (ty1_sub_ty2, e1) = typing_solver::is_sub_type(env, ty1, ty2);
                let (ty2_sub_ty1, e2) = typing_solver::is_sub_type(env, ty2, ty1);
                let e3 = if !(ty1_sub_ty2 && ty2_sub_ty1) {
                    let (env1, ty2_) = (env.clone(), ty2.clone());
                    let (env2, ty1_) = (env.clone(), ty1.clone());
                    Some(typing_error::shape(
                        primary::shape::T::Shape_field_type_mismatch {
                            pos: key_pos.clone(),
                            witness_pos: witness_pos.clone(),
                            ty_name: Lazy::new(move || typing_print::error(None, &env1, &ty2_)),
                            witness_ty_name: Lazy::new(move || {
                                typing_print::error(None, &env2, &ty1_)
                            }),
                        },
                    ))
                } else {
                    None
                };
                typing_error::multiple_opt([e1, e2, e3].into_iter().flatten().collect())
            };
            let class_mismatch = if typing_utils::is_tyvar_error(env, ty1)
                || typing_utils::is_tyvar_error(env, ty2)
            {
                None
            } else if cls1 != cls2 {
                Some(typing_error::shape(
                    primary::shape::T::Shape_field_class_mismatch {
                        pos: key_pos.clone(),
                        witness_pos: witness_pos.clone(),
                        class_name: utils::strip_ns(cls2).to_string(),
                        witness_class_name: utils::strip_ns(cls1).to_string(),
                    },
                ))
            } else {
                None
            };
            [class_mismatch, type_mismatch].into_iter().flatten().collect()
        }
    };
    typing_error::multiple_opt(ty_errs)
}

pub fn check_shape_keys_validity(env: &mut Env, keys: &[ShapeFieldName]) -> Vec<TyErr> {
    // Sort the keys by their positions since the error messages will make
    // more sense if we take the one that appears first as canonical and if
    // they are processed in source order.
    let cmp_keys = |x: &&ShapeFieldName, y: &&ShapeFieldName| {
        crate::pos::compare(&shape_field_pos(x), &shape_field_pos(y))
    };
    let mut keys: Vec<&ShapeFieldName> = keys.iter().collect();
    keys.sort_by(cmp_keys);
    match keys.split_first() {
        None => vec![],
        Some((witness, rest_keys)) => {
            let (pos, info) = get_field_info(env, witness);
            // `ty_err :: ty_errs`: the error of the last key first.
            let mut ty_errs = vec![];
            for k in rest_keys {
                match check_field(&pos, &info, env, k) {
                    Some(ty_err) => ty_errs.push(ty_err),
                    None => {}
                }
            }
            ty_errs.reverse();
            ty_errs
        }
    }
}

pub fn check_shape_key_const<Ex, En>(
    env: &mut Env,
    pos: &Pos,
    c: &nast::Class_,
    cls: &cls::T,
    cc: &nast::ClassConst,
    kind: &aast::ClassConstKind<Ex, En>,
) {
    check_shape_key_value(env, pos, c, cls, cc);
    let key = ShapeFieldName::SFclassConst(
        ast_defs::Id(pos.clone(), c.name.1.clone()),
        (pos.clone(), cc.id.1.clone()),
    );
    match kind {
        aast::ClassConstKind::CCConcrete(expr) => check_trait_self_shape_key(env, expr),
        aast::ClassConstKind::CCAbstract(_) => {}
    }
    let errors = check_shape_keys_validity(env, &[key]);
    for err in &errors {
        typing_error_utils::add_typing_error(err, env)
    }
}

fn update_param(param: DeclFunParam, ty: DeclTy) -> DeclFunParam {
    DeclFunParam { ty, ..param }
}

/// `MakeType.mixed r` of the declared phase: `mk (r, Toption (nonnull r))`.
fn decl_mixed(r: R) -> DeclTy {
    DeclTy::new(r.clone(), d::Ty_::Toption(DeclTy::new(r, d::Ty_::Tnonnull)))
}

/// `MakeType.generic r n` of the declared phase.
fn decl_generic(r: R, n: &str) -> DeclTy {
    DeclTy::generic(r, TypeName::new(n))
}

/// `MakeType.nullable r ty` of the declared phase.
fn decl_nullable(r: R, ty: DeclTy) -> DeclTy {
    // Cheap avoidance of double nullable
    match ty.node_ref() {
        d::Ty_::Toption(_) => DeclTy::new(r, ty.node_ref().clone()),
        d::Ty_::Tunion(tyl) if tyl.is_empty() => DeclTy::prim(r, ast_defs::Tprim::Tnull),
        _ => DeclTy::new(r, d::Ty_::Toption(ty)),
    }
}

/// `{ sft_optional; sft_ty }` for `field_name` in a declared shape: `hackrs`
/// keeps the position of the name in the field and the name alone in the key
/// (the converse of `crate::typing_phase::tshape_field_of_decl`).
fn decl_shape_field(
    field_name: &TshapeFieldName,
    sft_optional: bool,
    sft_ty: DeclTy,
) -> (d::TshapeFieldName, DeclShapeFieldType) {
    let (name, field_name_pos) = match field_name {
        TshapeFieldName::TSFregexGroup(PosString(p, s)) => (
            d::TshapeFieldName::TSFregexGroup(Symbol::new(s)),
            d::ShapeFieldNamePos::Simple(BPos::from(p)),
        ),
        TshapeFieldName::TSFlitStr(PosByteString(p, s)) => (
            d::TshapeFieldName::TSFlitStr(Bytes::new(s)),
            d::ShapeFieldNamePos::Simple(BPos::from(p)),
        ),
        TshapeFieldName::TSFclassConst((p1, c), PosString(p2, m)) => (
            d::TshapeFieldName::TSFclassConst(TypeName::new(c), Symbol::new(m)),
            d::ShapeFieldNamePos::ClassConst(BPos::from(p1), BPos::from(p2)),
        ),
    };
    (
        name,
        DeclShapeFieldType {
            field_name_pos,
            optional: sft_optional,
            ty: sft_ty,
        },
    )
}

/// `MakeType.open_shape r ~kind (TShapeMap.singleton field_name sft)` of the
/// declared phase.
fn decl_open_shape(r: R, kind: DeclTy, field: (d::TshapeFieldName, DeclShapeFieldType)) -> DeclTy {
    DeclTy::new(
        r,
        d::Ty_::Tshape(Box::new(d::ShapeType::Simple(d::ShapeTypeSimple(
            kind,
            BTreeMap::from([field]),
        )))),
    )
}

/// For function Shapes::idx called with a literal
/// field name, transform the decl function type from the hhi file
/// into a type that is specific to the field.
///
/// In the hhi file, the function has type
///   Shapes::idx<Tv>(
///     ?shape(...) $shape,
///     arraykey $index,
///     ?Tv,
///   )[]: ?Tv;
///
/// If there are two arguments, transform it to
///   Shapes::idx<Tv>(
///     ?shape('field_name' => Tv, ...) $shape,
///     arraykey $index,
///   )[]: ?Tv;
///
/// If there are three arguments, transform it to
///   Shapes::idx<Tv>(
///     ?shape('field_name' => Tv, ...) $shape,
///     arraykey $index,
///     Tv $default,
///   )[]: Tv;
fn transform_idx_fun_ty(field_name: &TshapeFieldName, nargs: isize, fty: DeclFunType) -> DeclFunType {
    let (param1, param2, param3) = match &fty.params[..] {
        [param1, param2, param3] => (param1.clone(), param2.clone(), param3.clone()),
        _ => panic!("Expected 3 parameters for Shapes::idx in hhi file"),
    };
    let rret = fty.ret.reason().clone();
    let field_ty: DeclTy = decl_generic(R::witness_from_decl(param1.pos.clone()), "Tv");
    let (params, ret) = {
        let r = R::witness_from_decl(param1.pos.clone());
        let param1 = update_param(
            param1,
            DeclTy::new(
                R::none(),
                // It is safe to use mixed as the kind, regardless of --everything-sdt, since
                // the idx function doesn't look at any of the other fields besides the explicitly
                // specified one
                d::Ty_::Toption(decl_open_shape(
                    r.clone(),
                    decl_mixed(r),
                    decl_shape_field(field_name, true, field_ty),
                )),
            ),
        );
        match nargs {
            2 => {
                // Return type should be ?Tv
                let ret = decl_nullable(rret.clone(), decl_generic(rret, "Tv"));
                (vec![param1, param2], ret)
            }
            3 => {
                // Third parameter should have type Tv
                let param3 = {
                    let r3 = param1.ty.reason().clone();
                    update_param(param3, decl_generic(r3, "Tv"))
                };
                // Return type should be Tv
                let ret = decl_generic(rret, "Tv");
                (vec![param1, param2, param3], ret)
            }
            // Shouldn't happen!
            _ => (fty.params.to_vec(), fty.ret.clone()),
        }
    };
    DeclFunType {
        params: params.into_boxed_slice(),
        ret,
        ..fty
    }
}

/// For function Shapes::at called with a literal
/// field name, transform the decl function type from the hhi file
/// into a type that is specific to the field.
///
/// In the hhi file, the function has type
///    Shapes::at<Tv>(
///      shape(...) $shape,
///      arraykey $index,
///    )[]: Tv;
///
/// Transform it to
///    Shapes::at<Tv>(
///      shape('field_name' => Tv, ...) $shape,
///      arraykey $index,
///    )[]: Tv;
fn transform_at_fun_ty(field_name: &TshapeFieldName, fty: DeclFunType) -> DeclFunType {
    let (param1, param2) = match &fty.params[..] {
        [param1, param2] => (param1.clone(), param2.clone()),
        _ => panic!("Expected 2 parameters for Shapes::at in hhi file"),
    };
    let params = {
        // Return type should be Tv already, but first parameter is just shape(...)
        let field_ty: DeclTy = decl_generic(R::witness_from_decl(param1.pos.clone()), "Tv");
        let r = R::witness_from_decl(param1.pos.clone());
        let param1 = update_param(
            param1,
            // It is safe to use mixed as the kind, regardless of --everything-sdt, since
            // the at function doesn't look at any of the other fields besides the explicitly
            // specified one
            decl_open_shape(
                r.clone(),
                decl_mixed(r),
                decl_shape_field(field_name, true, field_ty),
            ),
        );
        vec![param1, param2]
    };
    DeclFunType {
        params: params.into_boxed_slice(),
        ..fty
    }
}

/// For functions Shapes::idx or Shapes::at called with a literal
/// field name, transform the decl function type from the hhi file
/// into a type that is specific to the field.
pub fn transform_special_shapes_fun_ty(
    field_name: &TshapeFieldName,
    id: &aast::Sid,
    nargs: isize,
    fty: DeclFunType,
) -> DeclFunType {
    if id.1 == sn::shapes::AT {
        transform_at_fun_ty(field_name, fty)
    } else if id.1 == sn::shapes::IDX {
        transform_idx_fun_ty(field_name, nargs, fty)
    } else {
        fty
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typing_defs_flags::FunParamFlags;
    use oxidized::typing_defs_flags::FunTypeFlags;

    use super::*;

    fn lit(name: &str) -> TshapeFieldName {
        TshapeFieldName::TSFlitStr(PosByteString(Pos::NONE, bstr::BString::from(name)))
    }

    fn param(ty: DeclTy) -> DeclFunParam {
        DeclFunParam {
            pos: BPos::from(&Pos::NONE),
            name: None,
            ty,
            flags: FunParamFlags::empty(),
            def_value: None,
        }
    }

    fn fun_type(params: Vec<DeclFunParam>, ret: DeclTy) -> DeclFunType {
        DeclFunType {
            tparams: Box::new([]),
            where_constraints: Box::new([]),
            params: params.into_boxed_slice(),
            implicit_params: ty::decl::ty::FunImplicitParams {
                capability: ty::decl::ty::Capability::CapDefaults(BPos::from(&Pos::NONE)),
            },
            ret,
            flags: FunTypeFlags::empty(),
            instantiated: false,
        }
    }

    fn is_generic_tv(ty: &DeclTy) -> bool {
        matches!(ty.node_ref(), d::Ty_::Tgeneric(n) if n.as_str() == "Tv")
    }

    #[test]
    fn idx_and_at_are_specialised_to_the_field() {
        let mixed = || decl_mixed(R::none());
        let idx = fun_type(vec![param(mixed()), param(mixed()), param(mixed())], mixed());
        let id = ast_defs::Id(Pos::NONE, sn::shapes::IDX.to_string());
        let fty = transform_special_shapes_fun_ty(&lit("a"), &id, 2, idx.clone());
        assert_eq!(fty.params.len(), 2);
        assert!(matches!(fty.ret.node_ref(), d::Ty_::Toption(ty) if is_generic_tv(ty)));
        match fty.params[0].ty.node_ref() {
            d::Ty_::Toption(shape) => match shape.node_ref() {
                d::Ty_::Tshape(s) => match &**s {
                    d::ShapeType::Simple(d::ShapeTypeSimple(_, fields)) => {
                        let (k, sft) = fields.iter().next().unwrap();
                        assert!(matches!(k, d::TshapeFieldName::TSFlitStr(_)));
                        assert!(sft.optional && is_generic_tv(&sft.ty));
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            },
            _ => panic!(),
        }
        let fty = transform_special_shapes_fun_ty(&lit("a"), &id, 3, idx);
        assert_eq!(fty.params.len(), 3);
        assert!(is_generic_tv(&fty.ret) && is_generic_tv(&fty.params[2].ty));
        // The third parameter takes the reason of the new first one (none).
        assert!(matches!(fty.params[2].ty.reason().as_impl(), ty::reason::ReasonImpl::NoReason));
        let at = fun_type(vec![param(mixed()), param(mixed())], mixed());
        let id = ast_defs::Id(Pos::NONE, sn::shapes::AT.to_string());
        let fty = transform_special_shapes_fun_ty(&lit("a"), &id, 2, at);
        assert!(matches!(fty.params[0].ty.node_ref(), d::Ty_::Tshape(_)));
        // Other functions are left alone.
        let other = fun_type(vec![], mixed());
        let id = ast_defs::Id(Pos::NONE, "keyExists".to_string());
        let fty = transform_special_shapes_fun_ty(&lit("a"), &id, 2, other);
        assert!(fty.params.is_empty());
    }
}
