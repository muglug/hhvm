// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tast_expand.ml`. See `hh/PORTING.md`.
//!
//! The order in which the parts of a type are expanded is OCaml's (the
//! arguments of a constructor, the components of a tuple and the fields of a
//! record from the last one to the first), because `var_hook` and the
//! `Unresolved_tyvar` errors see it.

use std::sync::Arc;

use oxidized::aast;
use oxidized::aast_visitor::VisitorMut;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::tast_visitor::Res;
use crate::tvid;
use crate::typing_defs::Capability;
use crate::typing_defs::FunImplicitParams;
use crate::typing_defs::FunParam;
use crate::typing_defs::FunType;
use crate::typing_defs::ShapeFieldType;
use crate::typing_defs::ShapeType;
use crate::typing_defs::ShapeTypeSimple;
use crate::typing_defs::ShapeTypeSplat;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_defs::Tparam;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::TypeOrigin;
use crate::typing_defs::WhereConstraint;
use crate::typing_defs::get_node;
use crate::typing_defs::get_reason;
use crate::typing_defs::mk;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_intersection;
use crate::typing_make_type;
use crate::typing_shape_normalize;
use crate::typing_shape_normalize::MergeResult;
use crate::typing_union;

/// The closure of `exp_ty` and the functions defined with it.
struct Expand<'h, 'e> {
    var_hook: Option<&'h mut dyn FnMut(tvid::T)>,
    pos: Option<&'e Pos>,
    env: &'e Env,
}

impl Expand<'_, '_> {
    fn exp_ty(&mut self, ty: &Ty) -> Ty {
        if let (Ty_::Tvar(var), Some(hook)) = (get_node(ty), self.var_hook.as_mut()) {
            hook(*var)
        }
        let ety = tast_env::expand_type(&mut self.env.clone(), ty.clone());
        let p = get_reason(&ety).clone();
        let ety = match get_node(&ety) {
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tdynamic(_)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_)
            | Ty_::Tgeneric(_) => ety.clone(),
            Ty_::Tclass(n, e, tyl) => {
                let tyl = self.exp_tys(tyl);
                mk((p, Ty_::Tclass(n.clone(), e.clone(), tyl)))
            }
            Ty_::Tunion(tyl) => {
                let tyl = self.exp_tys(tyl);
                mk((p, Ty_::Tunion(tyl)))
            }
            Ty_::Tintersection(tyl) => {
                let tyl = self.exp_tys(tyl);
                mk((p, Ty_::Tintersection(tyl)))
            }
            Ty_::Toption(ty) => {
                let ty = self.exp_ty(ty);
                mk((p, Ty_::Toption(ty)))
            }
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            }) => {
                let t_required = self.exp_tys(t_required);
                let t_optional = self.exp_tys(t_optional);
                let t_extra = match t_extra {
                    TupleExtra::Tvariadic(t_variadic) => {
                        TupleExtra::Tvariadic(self.exp_ty(t_variadic))
                    }
                    TupleExtra::Tsplat(t_splat) => TupleExtra::Tsplat(self.exp_ty(t_splat)),
                };
                mk((
                    p,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: t_optional,
                        extra: t_extra,
                    }),
                ))
            }
            Ty_::Tfun(ft) => {
                let ft = self.exp_fun_type(ft);
                mk((p, Ty_::Tfun(std::rc::Rc::new(ft))))
            }
            Ty_::Tnewtype(n, tyl, ty) => {
                // `Tnewtype (n, exp_tys tyl, exp_ty ty)`, from the last argument
                let ty = self.exp_ty(ty);
                let tyl = self.exp_tys(tyl);
                mk((p, Ty_::Tnewtype(n.clone(), tyl, ty)))
            }
            Ty_::Tdependent(n, ty) => {
                let ty = self.exp_ty(ty);
                mk((p, Ty_::Tdependent(*n, ty)))
            }
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
                let s = self.exp_shape_type(s);
                mk((p, Ty_::Tshape(ShapeType::ShapeSimple(s))))
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                let expanded = self.exp_tys(ss_elems);
                let mut menv = self.env.clone();
                let (_errs, result) = typing_shape_normalize::merge(None, expanded, &mut menv);
                let (ty, sd) = match result {
                    MergeResult::Full(ty, sd) => (ty, sd),
                    MergeResult::EmptyShape(sd) => {
                        let shape = ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: typing_make_type::nothing(p.clone()),
                            fields: TShapeMap::new(),
                        };
                        (mk((p, Ty_::Tshape(ShapeType::ShapeSimple(shape)))), sd)
                    }
                    MergeResult::Partial(ss_elems, sd) => (
                        mk((p, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })))),
                        sd,
                    ),
                    MergeResult::Union(tys) => {
                        // Union operand distributed: members already finalised. This is a
                        // TAST-expansion (display) pass, so use the merge-returned env for
                        // the union and discard it.
                        let ty = typing_union::union_list(&mut menv, None, p, &tys);
                        (ty, false)
                    }
                    MergeResult::Intersection(tys) => {
                        let ty = typing_intersection::intersect_list(&mut menv, p, &tys);
                        (ty, false)
                    }
                };
                if sd {
                    typing_make_type::supportdyn(get_reason(&ty).clone(), ty)
                } else {
                    ty
                }
            }
            Ty_::TvecOrDict(ty1, ty2) => {
                // `Tvec_or_dict (exp_ty ty1, exp_ty ty2)`, from the last argument
                let ty2 = self.exp_ty(ty2);
                let ty1 = self.exp_ty(ty1);
                mk((p, Ty_::TvecOrDict(ty1, ty2)))
            }
            Ty_::Tvar(v) => match self.pos {
                None => mk((p, Ty_::Tvar(*v))),
                Some(pos) => {
                    if tast_env::get_tcopt(self.env).tco_disallow_unresolved_type_variables {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(typing_error::primary::T::Unresolved_tyvar(
                                pos.clone(),
                            )),
                            self.env,
                        )
                    }
                    mk((p, Ty_::Tvar(*v)))
                }
            },
            Ty_::Taccess(_) => ety.clone(),
            Ty_::TclassPtr(ty) => {
                let ty = self.exp_ty(ty);
                mk((p, Ty_::TclassPtr(ty)))
            }
        };
        ety
    }

    fn exp_tys(&mut self, tyl: &[Ty]) -> Vec<Ty> {
        tyl.iter().map(|ty| self.exp_ty(ty)).collect()
    }

    /// The fields of the record are evaluated from the last one of the
    /// definition of `fun_type` (`ft_instantiated`) to the first
    /// (`ft_tparams`).
    fn exp_fun_type(&mut self, ft: &FunType) -> FunType {
        let FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags: ft_flags,
            instantiated: ft_instantiated,
        } = ft;
        let ret = self.exp_ty(ft_ret);
        let implicit_params = self.exp_fun_implicit_params(ft_implicit_params);
        let params = ft_params
            .iter()
            .map(|fp| self.exp_fun_param(fp))
            .collect();
        let where_constraints = ft_where_constraints
            .iter()
            .map(|wc| self.exp_where_constraint(wc))
            .collect();
        let tparams = ft_tparams.iter().map(|t| self.exp_tparam(t)).collect();
        FunType {
            flags: *ft_flags,
            instantiated: *ft_instantiated,
            tparams,
            where_constraints,
            ret,
            params,
            implicit_params,
        }
    }

    fn exp_fun_param(&mut self, fp: &FunParam) -> FunParam {
        let FunParam {
            pos: fp_pos,
            name: fp_name,
            type_: fp_type,
            flags: fp_flags,
            def_value: fp_def_value,
        } = fp;
        FunParam {
            pos: fp_pos.clone(),
            name: fp_name.clone(),
            type_: self.exp_ty(fp_type),
            flags: *fp_flags,
            def_value: fp_def_value.clone(),
        }
    }

    fn exp_fun_implicit_params(&mut self, ip: &FunImplicitParams) -> FunImplicitParams {
        let FunImplicitParams { capability } = ip;
        let capability = match capability {
            Capability::CapTy(ty) => Capability::CapTy(self.exp_ty(ty)),
            Capability::CapDefaults(p) => Capability::CapDefaults(p.clone()),
        };
        FunImplicitParams { capability }
    }

    fn exp_sft(&mut self, sft: &ShapeFieldType) -> ShapeFieldType {
        let ShapeFieldType {
            optional: sft_optional,
            ty: sft_ty,
        } = sft;
        ShapeFieldType {
            optional: *sft_optional,
            ty: self.exp_ty(sft_ty),
        }
    }

    fn exp_shape_type(&mut self, s: &ShapeTypeSimple) -> ShapeTypeSimple {
        let ShapeTypeSimple {
            origin: shape_origin,
            unknown_value: shape_kind,
            fields,
        } = s;
        ShapeTypeSimple {
            origin: shape_origin.clone(),
            unknown_value: shape_kind.clone(),
            // TODO(shapes) exp_ty s_unknown_value
            // `TShapeMap.map exp_sft fields`: in the order of the keys
            fields: fields
                .iter()
                .map(|(k, sft)| (k.clone(), self.exp_sft(sft)))
                .collect(),
        }
    }

    fn exp_tparam(&mut self, t: &Tparam) -> Tparam {
        Tparam {
            constraints: t
                .constraints
                .iter()
                .map(|(ck, ty)| (*ck, self.exp_ty(ty)))
                .collect(),
            ..t.clone()
        }
    }

    fn exp_where_constraint(&mut self, wc: &WhereConstraint) -> WhereConstraint {
        let WhereConstraint(ty1, ck, ty2) = wc;
        // `(exp_ty ty1, ck, exp_ty ty2)`, from the last component
        let ty2 = self.exp_ty(ty2);
        let ty1 = self.exp_ty(ty1);
        WhereConstraint(ty1, *ck, ty2)
    }
}

/// Eliminate residue of type inference:
///   1. Tvars are replaced (deep) by the expanded type
///   2. Singleton unions are eliminated
///
/// TODO TAST:
///   Transform completely unconstrained types to Tmixed
///   Consider using a fresh datatype for TAST types.
pub fn expand_ty(
    var_hook: Option<&mut dyn FnMut(tvid::T)>,
    pos: Option<&Pos>,
    env: &Env,
    ty: Ty,
) -> Ty {
    let mut exp = Expand {
        var_hook,
        pos,
        env,
    };
    exp.exp_ty(&ty)
}

/// The class of `expander`: an `endo` visitor.
struct Expander;

/// `expander`
fn expander() -> Expander {
    Expander
}

impl<'a> VisitorMut<'a> for Expander {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn VisitorMut<'a, Params = Self::Params> {
        self
    }

    tast_visitor::map_methods!(endo, 'a);

    fn visit_expr(&mut self, env: &mut Env, x: &'a mut tast::Expr) -> Res {
        let aast::Expr(ty, pos, expr_) = x;
        // `(expand_ty ~pos env ty, pos, self#on_expr_ env expr_)`: the
        // components of the tuple are evaluated from the last one.
        self.visit_expr_(env, expr_)?;
        *ty = expand_ty(None, Some(pos), env, ty.clone());
        Ok(())
    }

    fn visit_class_id(&mut self, env: &mut Env, x: &'a mut tast::ClassId) -> Res {
        let aast::ClassId(ty, pos, cid_) = x;
        self.visit_class_id_(env, cid_)?;
        *ty = expand_ty(None, Some(pos), env, ty.clone());
        Ok(())
    }

    fn visit_ex(&mut self, env: &mut Env, ty: &'a mut tast::Ty) -> Res {
        *ty = expand_ty(None, None, env, ty.clone());
        Ok(())
    }
}

/// `expander#go`: the definitions of `tast` in place.
fn expander_go(ctx: &Arc<Ctx>, tast: &mut [tast::Def]) {
    tast_visitor::endo::go(&mut expander(), ctx, tast)
}

/// Replace all types in a program AST by their expansions
pub fn expand_program(ctx: &Arc<Ctx>, tast: Vec<tast::Def>) -> Vec<tast::Def> {
    let mut tast = tast;
    expander_go(ctx, &mut tast);
    tast
}

pub fn expand_def(ctx: &Arc<Ctx>, def: tast::Def) -> tast::Def {
    let mut def = def;
    tast_visitor::endo::go_def(&mut expander(), ctx, &mut def);
    def
}
