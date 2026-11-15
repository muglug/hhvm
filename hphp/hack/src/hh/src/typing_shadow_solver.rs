// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_shadow_solver.ml`. See `hh/PORTING.md`.
//!
//! The local functions of `solve` that close over its arguments are the
//! methods of [`Solver`]; `solving` (a `ref`) is one of its fields.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;
use oxidized::typing_defs_core::PosByteString;

use crate::internal_type_set;
use crate::tast;
use crate::tast_env;
use crate::tvid;
use crate::typing_defs::is_dynamic;
use crate::typing_defs_constraints::CiAccessKind;
use crate::typing_defs_constraints::ConstraintType_;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::deref_constraint_type;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_env;
use crate::typing_env_types::Env;
/// `module Inf = Typing_inference_env`
use crate::typing_inference_env as inf;
use crate::typing_intersection;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::yojson;

/// `type solution`
#[derive(Clone, Debug)]
pub struct Solution {
    pub local_name: String,
    pub local_pos: Pos,
    pub shadow_tvid: tvid::T,
    pub inferred_ty: Option<Ty>,
}

fn is_uninformative(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tdynamic(_) => true,
        Ty_::Tnonnull => true,
        Ty_::Tprim(Tprim::Tnull) => true,
        Ty_::Toption(ty_) => match get_node(ty_) {
            Ty_::Tnonnull => true,
            _ => is_uninformative(ty_),
        },
        Ty_::Tnewtype(n, _, bound) if n == sn::classes::SUPPORT_DYN => is_uninformative(bound),
        Ty_::Tunion(tyl) => tyl.iter().all(is_uninformative),
        _ => false,
    }
}

fn strip_like(ty: &Ty) -> Ty {
    match get_node(ty) {
        Ty_::Tunion(tyl) => {
            let tyl: Vec<Ty> = tyl.iter().filter(|t| !is_dynamic(t)).cloned().collect();
            if tyl.len() == 1 {
                strip_like(&tyl[0])
            } else {
                mk((get_reason(ty).clone(), Ty_::Tunion(tyl)))
            }
        }
        _ => ty.clone(),
    }
}

/// The context of the local functions of [`solve`].
struct Solver<'a> {
    as_data: bool,
    env: &'a Env,
    inf_env: &'a inf::T,
    r: Reason,
    open_shape_unknown_value: Ty,
    /// Track which shadow tyvars are currently being solved to break cycles.
    /// If solve_shadow is called for a tvid already being solved, we return
    /// mixed rather than recursing infinitely.
    solving: tvid::set::T,
}

impl Solver<'_> {
    /// `shape(<field_name> => sft_ty, ...)`, with `sft_optional`.
    fn open_shape(&self, field_name: TshapeFieldName, sft_optional: bool, sft_ty: Ty) -> Ty {
        mk((
            self.r.clone(),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: self.open_shape_unknown_value.clone(),
                fields: TShapeMap::from([(
                    TShapeField(field_name),
                    ShapeFieldType {
                        optional: sft_optional,
                        ty: sft_ty,
                    },
                )]),
            })),
        ))
    }

    fn constraint_to_type(&self, ity: &InternalType) -> Option<Ty> {
        let r = &self.r;
        match ity {
            InternalType::LoclType(ty) => Some(ty.clone()),
            InternalType::ConstraintType(cty) => {
                let (_, cty_) = deref_constraint_type(cty);
                match cty_ {
                    ConstraintType_::TcanIndex(ci) => {
                        let key_ty = ci.key;
                        let val_ty = ci.val;
                        let as_data_ty = if self.as_data {
                            let aast::Expr(_, _, index_expr) = &ci.index_expr;
                            let is_optional = match ci.access_kind {
                                CiAccessKind::CiLhsOfNullCoalesce
                                | CiAccessKind::CiDestructureOptional => true,
                                CiAccessKind::CiNormal => false,
                            };
                            match index_expr {
                                aast::Expr_::String(s) => {
                                    let field_name =
                                        TshapeFieldName::TSFlitStr(PosByteString(Pos::NONE, s.clone()));
                                    let sft_ty = match get_node(&val_ty) {
                                        Ty_::Tunion(tyl) => {
                                            let tyl: Vec<Ty> =
                                                tyl.iter().filter(|t| !is_dynamic(t)).cloned().collect();
                                            if tyl.len() == 1 {
                                                tyl[0].clone()
                                            } else {
                                                mk((get_reason(&val_ty).clone(), Ty_::Tunion(tyl)))
                                            }
                                        }
                                        _ => val_ty.clone(),
                                    };
                                    Some(self.open_shape(field_name, is_optional, sft_ty))
                                }
                                aast::Expr_::Int(_) => Some(typing_make_type::vec(r.clone(), val_ty.clone())),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        match as_data_ty {
                            Some(ty) => Some(ty),
                            None => Some(typing_make_type::keyed_container(r.clone(), key_ty, val_ty)),
                        }
                    }
                    ConstraintType_::ThasMember(_) => None,
                    ConstraintType_::TcanIndexAssign(cia) => {
                        let key_ty = cia.key;
                        let val_ty = cia.write;
                        let as_data_ty = if self.as_data {
                            let aast::Expr(_, _, index_expr) = &cia.index_expr;
                            match index_expr {
                                aast::Expr_::String(s) => {
                                    let field_name =
                                        TshapeFieldName::TSFlitStr(PosByteString(Pos::NONE, s.clone()));
                                    Some(self.open_shape(field_name, false, val_ty.clone()))
                                }
                                aast::Expr_::Int(_) => Some(typing_make_type::vec(r.clone(), val_ty.clone())),
                                _ => None,
                            }
                        } else {
                            None
                        };
                        match as_data_ty {
                            Some(ty) => Some(ty),
                            None => Some(typing_make_type::keyed_container(r.clone(), key_ty, val_ty)),
                        }
                    }
                    ConstraintType_::TcanTraverse(ct) => {
                        let val_ty = ct.val;
                        match ct.key {
                            Some(key_ty) => {
                                Some(typing_make_type::keyed_traversable(r.clone(), key_ty, val_ty))
                            }
                            None => Some(typing_make_type::traversable(r.clone(), val_ty)),
                        }
                    }
                    ConstraintType_::Tdestructure(d) => {
                        let nothing = typing_make_type::nothing(r.clone());
                        Some(mk((
                            r.clone(),
                            Ty_::Ttuple(TupleType {
                                required: d.required,
                                optional: d.optional,
                                extra: TupleExtra::Tvariadic(d.variadic.unwrap_or(nothing)),
                            }),
                        )))
                    }
                    _ => None,
                }
            }
        }
    }

    fn substitute_shadows(&mut self, ty: &Ty) -> Ty {
        match get_node(ty) {
            Ty_::Tvar(v) => {
                if inf::is_shadow(self.inf_env, *v) {
                    match self.solve_shadow(*v) {
                        Some(solved) => solved,
                        None => typing_make_type::mixed(get_reason(ty).clone()),
                    }
                } else {
                    // The environment of the expansion is dropped.
                    let expanded =
                        typing_env::expand_var(&mut self.env.clone(), get_reason(ty).clone(), *v);
                    match get_node(&expanded) {
                        Ty_::Tvar(_) => typing_make_type::mixed(get_reason(ty).clone()),
                        _ => {
                            if is_uninformative(&expanded) {
                                typing_make_type::mixed(get_reason(ty).clone())
                            } else {
                                self.substitute_shadows(&expanded)
                            }
                        }
                    }
                }
            }
            Ty_::Tdynamic(Some(v)) => match self.solve_shadow(*v) {
                Some(solved) => solved,
                None => typing_make_type::mixed(get_reason(ty).clone()),
            },
            Ty_::Tdynamic(None) => typing_make_type::mixed(get_reason(ty).clone()),
            Ty_::Tfun(ft) => {
                // OCaml evaluates the fields of the record from the last one
                // of the type: `ft_ret` before `ft_params`.
                let ft_ret = self.substitute_shadows(&ft.ret);
                let ft_params: Vec<FunParam> = ft
                    .params
                    .iter()
                    .map(|p| FunParam {
                        type_: self.substitute_shadows(&p.type_),
                        ..p.clone()
                    })
                    .collect();
                mk((
                    get_reason(ty).clone(),
                    Ty_::Tfun(std::rc::Rc::new(FunType {
                        params: ft_params,
                        ret: ft_ret,
                        ..FunType::clone(&ft)
                    })),
                ))
            }
            Ty_::Tshape(ShapeType::ShapeSimple(shape)) => {
                // `s_fields` (in the order of the keys, as `TShapeMap.map`)
                // before `s_unknown_value`, for the same reason.
                let s_fields: TShapeMap<ShapeFieldType> = shape
                    .fields
                    .iter()
                    .map(|(k, sft)| {
                        (
                            k.clone(),
                            ShapeFieldType {
                                ty: self.substitute_shadows(&sft.ty),
                                ..sft.clone()
                            },
                        )
                    })
                    .collect();
                let s_unknown_value = self.substitute_shadows(&shape.unknown_value);
                mk((
                    get_reason(ty).clone(),
                    Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        unknown_value: s_unknown_value,
                        fields: s_fields,
                        ..shape.clone()
                    })),
                ))
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                let ss_elems: Vec<Ty> = ss_elems.iter().map(|ty| self.substitute_shadows(ty)).collect();
                mk((
                    get_reason(ty).clone(),
                    Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })),
                ))
            }
            Ty_::Tclass(name, exact, tyl) => {
                let tyl: Vec<Ty> = tyl.iter().map(|ty| self.substitute_shadows(ty)).collect();
                mk((
                    get_reason(ty).clone(),
                    Ty_::Tclass(name.clone(), exact.clone(), tyl),
                ))
            }
            _ => ty.clone(),
        }
    }

    fn solve_shadow(&mut self, v: tvid::T) -> Option<Ty> {
        if self.solving.contains(&v) {
            Some(typing_make_type::mixed(self.r.clone()))
        } else {
            self.solving.insert(v);
            let result = {
                let upper_bounds = inf::get_tyvar_upper_bounds(self.inf_env, v);
                let bounds = internal_type_set::elements(&upper_bounds);
                let has_structural = bounds.iter().any(|ity| match ity {
                    InternalType::ConstraintType(_) => true,
                    _ => false,
                });
                let bounds: Vec<InternalType> = if has_structural {
                    bounds
                        .into_iter()
                        .filter(|ity| match ity {
                            InternalType::ConstraintType(_) => true,
                            _ => false,
                        })
                        .collect()
                } else {
                    bounds
                };
                let tys: Vec<Ty> = bounds.iter().filter_map(|ity| self.constraint_to_type(ity)).collect();
                let tys: Vec<Ty> = tys.iter().map(strip_like).collect();
                let tys: Vec<Ty> = tys.into_iter().filter(|ty| !is_uninformative(ty)).collect();
                let tys: Vec<Ty> = tys.iter().map(|ty| self.substitute_shadows(ty)).collect();
                match tys.len() {
                    0 => Some(typing_make_type::mixed(self.r.clone())),
                    1 => tys.into_iter().next(),
                    _ => {
                        // The environment of the intersection is dropped.
                        let ty = typing_intersection::intersect_list(
                            &mut self.env.clone(),
                            self.r.clone(),
                            &tys,
                        );
                        Some(ty)
                    }
                }
            };
            result
        }
    }
}

pub fn solve(
    as_data: bool,
    env: &Env,
    inf_env: &inf::T,
    dynamic_locals: &[tast::DynamicLocalInfo],
) -> Vec<Solution> {
    let r = typing_reason::none();
    let open_shape_unknown_value = mk((r.clone(), Ty_::Toption(mk((r.clone(), Ty_::Tnonnull)))));
    let mut solver = Solver {
        as_data,
        env,
        inf_env,
        r,
        open_shape_unknown_value,
        solving: tvid::set::T::new(),
    };
    dynamic_locals
        .iter()
        .map(|dl| {
            let inferred_ty = solver.solve_shadow(dl.shadow_tvid);
            Solution {
                local_name: dl.name.clone(),
                local_pos: dl.pos.clone(),
                shadow_tvid: dl.shadow_tvid,
                inferred_ty,
            }
        })
        .collect()
}

pub fn solution_to_json(env: &tast_env::Env, sol: &Solution) -> yojson::safe::T {
    let ty_str = match &sol.inferred_ty {
        Some(ty) => tast_env::print_ty(env, ty),
        None => "dynamic".to_string(),
    };
    yojson::safe::T::Assoc(vec![
        (
            "name".to_string(),
            yojson::safe::T::String(sol.local_name.clone()),
        ),
        (
            "pos".to_string(),
            yojson::safe::T::String(crate::pos::string(&crate::pos::to_absolute(&sol.local_pos))),
        ),
        ("type".to_string(), yojson::safe::T::String(ty_str)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn dynamic() -> Ty {
        mk((typing_reason::none(), Ty_::Tdynamic(None)))
    }

    fn union(tyl: Vec<Ty>) -> Ty {
        mk((typing_reason::none(), Ty_::Tunion(tyl)))
    }

    #[test]
    fn uninformative_types() {
        assert!(is_uninformative(&dynamic()));
        assert!(is_uninformative(&prim(Tprim::Tnull)));
        assert!(is_uninformative(&union(vec![dynamic(), prim(Tprim::Tnull)])));
        assert!(!is_uninformative(&union(vec![dynamic(), prim(Tprim::Tint)])));
        assert!(!is_uninformative(&prim(Tprim::Tint)));
    }

    #[test]
    fn strip_like_removes_dynamic_from_unions() {
        let like_int = union(vec![dynamic(), prim(Tprim::Tint)]);
        assert_eq!(strip_like(&like_int), prim(Tprim::Tint));
        let like_union = union(vec![dynamic(), prim(Tprim::Tint), prim(Tprim::Tfloat)]);
        assert_eq!(
            strip_like(&like_union),
            union(vec![prim(Tprim::Tint), prim(Tprim::Tfloat)])
        );
        assert_eq!(strip_like(&prim(Tprim::Tint)), prim(Tprim::Tint));
    }
}
