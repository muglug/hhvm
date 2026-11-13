// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `decl_hint.ml`. See `hh/PORTING.md`.
//!
//! Converts a type hint into a type.
//!
//! The decl types are those of `hackrs` (`ty::decl::Ty<R>`), which differ
//! from `Typing_defs.decl_ty` in two ways that show here: the position of a
//! shape field's name is kept in the field (`ShapeFieldType::field_name_pos`)
//! and not in the key of the map, and `Tdynamic` has no argument.
//!
//! `Decl_env.make_decl_posed env (p, x)` is written
//! `(make_decl_pos(env, p), x)`, which is its definition: the OCaml pair is
//! an `ast_defs::Id` in some places of the Rust AST and a tuple in others.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::aast::Hint;
use oxidized::aast::Hint_;
use oxidized::ast_defs;
use oxidized::nast;
use oxidized::pos::Pos;
use pos::BPos;
use pos::Bytes;
use pos::Positioned;
use pos::Symbol;
use pos::TypeConstName;
use pos::TypeName;
use ty::decl;
use ty::decl::Ty;
use ty::decl::Ty_;
use ty::decl::ty::ShapeFieldNamePos;
use ty::decl::ty::TshapeFieldName;
use ty::reason::Reason;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ctx::R;
use crate::decl_env;
use crate::decl_env::Env;

/// `Decl_env.make_decl_pos env p`, as a position of a decl type.
fn make_decl_pos(env: &Env, p: &Pos) -> BPos {
    BPos::from(decl_env::make_decl_pos(env, p))
}

/// `Decl_env.make_decl_posed env (p, x)`
fn make_decl_posed<S>(env: &Env, p: &Pos, x: S) -> Positioned<S, BPos> {
    Positioned::new(make_decl_pos(env, p), x)
}

/// `Typing_reason.vec_or_dict_key`
fn reason_vec_or_dict_key(p: BPos) -> R {
    R::mk(|| ReasonImpl::FromWitnessDecl(WitnessDecl::VecOrDictKey(p)))
}

/// `TShapeField.of_ast`
fn tshape_field_of_ast(
    convert_pos: impl Fn(&Pos) -> BPos,
    name: &ast_defs::ShapeFieldName,
) -> (ShapeFieldNamePos<BPos>, TshapeFieldName) {
    match name {
        ast_defs::ShapeFieldName::SFlitStr((p, s)) => (
            ShapeFieldNamePos::Simple(convert_pos(p)),
            TshapeFieldName::TSFlitStr(Bytes::new(s)),
        ),
        ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(p, cls)) => (
            ShapeFieldNamePos::ClassConst(convert_pos(p), convert_pos(p)),
            TshapeFieldName::TSFclassConst(TypeName::new(cls), Symbol::new("class")),
        ),
        ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(pcls, cls), (pconst, const_)) => (
            ShapeFieldNamePos::ClassConst(convert_pos(pcls), convert_pos(pconst)),
            TshapeFieldName::TSFclassConst(TypeName::new(cls), Symbol::new(const_)),
        ),
    }
}

fn has_splats(nsi_field_map: &[aast::ShapeElement]) -> bool {
    nsi_field_map.iter().any(|e| match e {
        aast::ShapeElement::SESplat(_) => true,
        aast::ShapeElement::SEField(_) => false,
    })
}

fn make_decl_ty(env: &Env, p: &Pos, ty_: Ty_<R>) -> Ty<R> {
    Ty::new(R::hint(make_decl_pos(env, p)), ty_)
}

/* Unpacking a hint for typing */
pub fn hint(env: &Env, h: &Hint) -> Ty<R> {
    let Hint(p, h) = h;
    let ty_ = hint_(p, env, h);
    make_decl_ty(env, p, ty_)
}

pub fn context_hint(env: &Env, h: &Hint) -> Ty<R> {
    let Hint(p, h_) = h;
    match &**h_ {
        Hint_::HfunContext(n) => make_decl_ty(
            env,
            p,
            Ty_::Tgeneric(TypeName::new(format!("T/[ctx {}]", n))),
        ),
        Hint_::Haccess(Hint(_, root), ids)
            if matches!(&**root, Hint_::Habstr(_) | Hint_::Hvar(_)) =>
        {
            let n = match &**root {
                Hint_::Habstr(n) | Hint_::Hvar(n) => n,
                _ => unreachable!(),
            };
            let name = format!(
                "T/[{}::{}]",
                n,
                ids.iter()
                    .map(|ast_defs::Id(_, id)| id.as_str())
                    .collect::<Vec<_>>()
                    .join("::")
            );
            make_decl_ty(env, p, Ty_::Tgeneric(TypeName::new(name)))
        }
        _ => hint(env, h),
    }
}

/// The type of a shape field, with the key it has in the map of the fields:
/// `(TShapeField.of_ast (Decl_env.make_decl_pos env) i.sfi_name,
/// shape_field_info_to_shape_field_type env i)`.
fn shape_field_info_to_shape_field_type(
    env: &Env,
    sfi: &aast::ShapeFieldInfo,
) -> (TshapeFieldName, decl::ShapeFieldType<R>) {
    let aast::ShapeFieldInfo {
        optional: sfi_optional,
        hint: sfi_hint,
        name: sfi_name,
    } = sfi;
    let (field_name_pos, name) = tshape_field_of_ast(|p| make_decl_pos(env, p), sfi_name);
    (
        name,
        decl::ShapeFieldType {
            field_name_pos,
            optional: *sfi_optional,
            ty: hint(env, sfi_hint),
        },
    )
}

pub fn aast_user_attribute_to_decl_user_attribute(
    env: &Env,
    ua: &nast::UserAttribute,
) -> decl::UserAttribute<BPos> {
    let aast::UserAttribute {
        name: ast_defs::Id(ua_name_pos, ua_name),
        params: ua_params,
    } = ua;
    decl::UserAttribute {
        name: make_decl_posed(env, ua_name_pos, TypeName::new(ua_name)),
        params: ua_params
            .iter()
            .filter_map(|aast::Expr(_, _, e)| match e {
                aast::Expr_::ClassConst(cc) => match &**cc {
                    (aast::ClassId(_, _, aast::ClassId_::CI(ast_defs::Id(_, cls))), (_, name))
                        if name == sn::members::M_CLASS =>
                    {
                        Some(decl::ty::UserAttributeParam::Classname(TypeName::new(cls)))
                    }
                    _ => None,
                },
                aast::Expr_::EnumClassLabel(label) => {
                    let (_, s) = &**label;
                    Some(decl::ty::UserAttributeParam::EnumClassLabel(Symbol::new(s)))
                }
                aast::Expr_::String(s) => Some(decl::ty::UserAttributeParam::String(Bytes::new(s))),
                aast::Expr_::Int(i) => Some(decl::ty::UserAttributeParam::Int(Symbol::new(i))),
                _ => None,
            })
            .collect(),
        raw_val: None,
    }
}

pub fn aast_contexts_to_decl_capability(
    env: &Env,
    ctxs: Option<&aast::Contexts>,
    default_pos: &Pos,
) -> (Pos, decl::ty::Capability<R, Ty<R>>) {
    match ctxs {
        Some(aast::Contexts(pos, hl)) => {
            let mut dtys: Vec<Ty<R>> = hl.iter().map(|h| context_hint(env, h)).collect();
            /* For coeffect contexts, in general we do not simplify empty or singleton
             * intersection, we keep them as is, so we don't use Typing_make_type
             * on purpose.
             * However the direct decl parser removes the intersection when the
             * context was a single Hfun_context. Let's do the same here
             */
            let reason = R::hint(make_decl_pos(env, pos));
            let dty = match &dtys[..] {
                [dty] => match dty.node_ref() {
                    Ty_::Tgeneric(_) => dtys.pop().unwrap(),
                    _ => Ty::new(reason, Ty_::Tintersection(dtys.into())),
                },
                _ => Ty::new(reason, Ty_::Tintersection(dtys.into())),
            };
            (pos.clone(), decl::ty::Capability::CapTy(dty))
        }
        None => (
            default_pos.clone(),
            decl::ty::Capability::CapDefaults(make_decl_pos(env, default_pos)),
        ),
    }
}

pub fn aast_tparam_to_decl_tparam(env: &Env, t: &nast::Tparam) -> decl::Tparam<R, Ty<R>> {
    let ast_defs::Id(tp_name_pos, tp_name) = &t.name;
    decl::Tparam {
        variance: t.variance,
        name: make_decl_posed(env, tp_name_pos, TypeName::new(tp_name)),
        constraints: t
            .constraints
            .iter()
            .map(|(ck, h)| (*ck, hint(env, h)))
            .collect(),
        reified: t.reified,
        user_attributes: t
            .user_attributes
            .0
            .iter()
            .map(|ua| aast_user_attribute_to_decl_user_attribute(env, ua))
            .collect(),
    }
}

fn hint_(p: &Pos, env: &Env, h: &Hint_) -> Ty_<R> {
    match h {
        Hint_::Hmixed => Ty_::Tmixed,
        Hint_::Hwildcard => Ty_::Twildcard,
        Hint_::Hnonnull => Ty_::Tnonnull,
        Hint_::Hthis => Ty_::Tthis,
        Hint_::Hdynamic => Ty_::Tdynamic,
        Hint_::Hnothing => Ty_::Tunion([].into()),
        Hint_::HvecOrDict(h1, h2) => {
            let t1 = match h1 {
                Some(h) => hint(env, h),
                None => Ty::new(
                    reason_vec_or_dict_key(make_decl_pos(env, p)),
                    Ty_::Tprim(aast::Tprim::Tarraykey),
                ),
            };
            Ty_::TvecOrDict(Box::new((t1, hint(env, h2))))
        }
        Hint_::Hprim(p) => Ty_::Tprim(*p),
        Hint_::Habstr(x) => Ty_::Tgeneric(TypeName::new(x)),
        Hint_::HclassPtr(k, h) => {
            let enum_hint;
            let h = match k {
                aast::ClassPtrKind::CKclass => h,
                aast::ClassPtrKind::CKenum => {
                    enum_hint = Hint(
                        p.clone(),
                        Box::new(Hint_::Happly(
                            ast_defs::Id(p.clone(), sn::classes::HH_BUILTIN_ENUM.to_string()),
                            vec![h.clone()],
                        )),
                    );
                    &enum_hint
                }
            };
            Ty_::TclassPtr(hint(env, h))
        }
        Hint_::Hoption(h) => {
            let h = hint(env, h);
            Ty_::Toption(h)
        }
        Hint_::Hlike(h) => Ty_::Tlike(hint(env, h)),
        Hint_::Hfun(aast::HintFun {
            tparams: hf_tparams,
            is_readonly: ro,
            param_tys: hl,
            param_info: pil,
            variadic_ty: vh,
            named_variadic_ty: nvh,
            ctxs,
            return_ty: h,
            is_readonly_return: readonly_ret,
        }) => {
            let make_param = |x: &Hint, param_info: Option<&aast::HfParamInfo>| {
                let Hint(p, _) = x;
                let (is_optional, readonly, splat, kind, named_param_name) = match param_info {
                    Some(p) => {
                        let readonly = match p.readonlyness {
                            Some(ast_defs::ReadonlyKind::Readonly) => true,
                            _ => false,
                        };
                        let is_optional = match p.optional {
                            Some(ast_defs::OptionalKind::Optional) => true,
                            _ => false,
                        };
                        let splat = match p.splat {
                            Some(ast_defs::SplatKind::Splat) => true,
                            _ => false,
                        };
                        let param_kind = get_param_mode(&p.kind);
                        (is_optional, readonly, splat, param_kind, p.named.as_ref())
                    }
                    None => (false, false, false, decl::ty::ParamMode::FPnormal, None),
                };
                decl::FunParam {
                    pos: make_decl_pos(env, p),
                    /* Here `is_some fp_name` iff the param is a named parameter (type-relevant)
                     * Note that in a later pass this field can become populated for unnamed params (not type-relevant)
                     */
                    name: named_param_name.map(Symbol::new),
                    ty: hint(env, x),
                    flags: make_fp_flags(
                        kind,
                        false,
                        is_optional,
                        readonly,
                        false,
                        splat,
                        named_param_name.is_some(),
                    ),
                    def_value: None,
                }
            };
            let readonly_opt = |ro: &Option<ast_defs::ReadonlyKind>| match ro {
                Some(ast_defs::ReadonlyKind::Readonly) => true,
                None => false,
            };
            if hl.len() != pil.len() {
                panic!("length mismatch in map2_exn: {} <> {}", hl.len(), pil.len());
            }
            let mut paraml: Vec<decl::FunParam<R, Ty<R>>> = hl
                .iter()
                .zip(pil.iter())
                .map(|(x, param_info)| make_param(x, param_info.as_ref()))
                .collect();
            let implicit_params = {
                let (_pos, capability) = aast_contexts_to_decl_capability(env, ctxs.as_ref(), p);
                decl::ty::FunImplicitParams { capability }
            };
            let ret = hint(env, h);
            /* Handle positional variadic */
            let variadic = match vh {
                Some(t) => {
                    paraml.push(make_param(t, None));
                    true
                }
                None => false,
            };
            /* Handle named variadic - create a param with named=true */
            let named_variadic_param_info = Some(aast::HfParamInfo {
                kind: ast_defs::ParamKind::Pnormal,
                readonlyness: None,
                optional: None,
                splat: None,
                named: Some("...".to_string()),
            });
            let named_variadic = match nvh {
                Some(t) => {
                    paraml.push(make_param(t, named_variadic_param_info.as_ref()));
                    true
                }
                None => false,
            };
            let everything_sdt = decl_env::tcopt(env).po.everything_sdt;
            let ft_tparams: Vec<decl::Tparam<R, Ty<R>>> = hf_tparams
                .iter()
                .map(
                    |aast::HintTparam {
                         name: htp_name,
                         constraints: htp_constraints,
                         user_attributes: htp_user_attributes,
                     }| {
                        let tp_name = {
                            let ast_defs::Id(pos, id) = htp_name;
                            // `Pos_or_decl.of_raw_pos pos`
                            Positioned::new(BPos::from(pos), TypeName::new(id))
                        };
                        let tp_constraints: Vec<(ast_defs::ConstraintKind, Ty<R>)> =
                            htp_constraints
                                .iter()
                                .map(|(cstr_kind, cstr_hint)| (*cstr_kind, hint(env, cstr_hint)))
                                .collect();

                        let tp_user_attributes: Vec<decl::UserAttribute<BPos>> =
                            htp_user_attributes
                                .iter()
                                .map(|ast_defs::Id(pos, id)| {
                                    let ua_name =
                                        Positioned::new(BPos::from(pos), TypeName::new(id));
                                    decl::UserAttribute {
                                        name: ua_name,
                                        params: [].into(),
                                        raw_val: None,
                                    }
                                })
                                .collect();
                        /* Add an implicit upper-bound if we are decling under implicit pessimisation
                        and `NoAutoBound` isn't set */
                        let tp_constraints = if everything_sdt
                            && !htp_user_attributes
                                .iter()
                                .any(|ast_defs::Id(_, id)| id == sn::user_attributes::NO_AUTO_BOUND)
                        {
                            let pos = tp_name.pos().clone();
                            let reason = R::witness_from_decl(pos.clone());
                            let ub = Ty::new(
                                reason.clone(),
                                Ty_::Tapply(Box::new((
                                    Positioned::new(pos, TypeName::new(sn::classes::SUPPORT_DYN)),
                                    [Ty::new(reason, Ty_::Tmixed)].into(),
                                ))),
                            );
                            let mut constraints =
                                vec![(ast_defs::ConstraintKind::ConstraintAs, ub)];
                            constraints.extend(tp_constraints);
                            constraints
                        } else {
                            tp_constraints
                        };

                        decl::Tparam {
                            variance: ast_defs::Variance::Invariant, /* Meaningless here */
                            name: tp_name,
                            constraints: tp_constraints.into(),
                            reified: aast::ReifyKind::Erased,
                            user_attributes: tp_user_attributes.into(),
                        }
                    },
                )
                .collect();
            let ft_instantiated = ft_tparams.is_empty();
            Ty_::Tfun(Box::new(decl::FunType {
                tparams: ft_tparams.into(),
                where_constraints: [].into(),
                params: paraml.into(),
                implicit_params,
                ret,
                flags: fun_make(
                    ast_defs::FunKind::FSync,
                    false,
                    readonly_opt(readonly_ret),
                    readonly_opt(ro),
                    false,
                    false,
                    variadic,
                    named_variadic,
                ),
                instantiated: ft_instantiated,
            }))
        }
        Hint_::Happly(ast_defs::Id(id_pos, id), argl) => {
            let id = make_decl_posed(env, id_pos, TypeName::new(id));
            let argl = argl.iter().map(|h| hint(env, h)).collect();
            Ty_::Tapply(Box::new((id, argl)))
        }
        Hint_::Haccess(root_ty, ids) => {
            let root_ty = hint_(p, env, &root_ty.1);
            let mut res = root_ty;
            for ast_defs::Id(id_pos, id) in ids {
                res = Ty_::Taccess(Box::new(decl::TaccessType {
                    ty: Ty::new(R::hint(make_decl_pos(env, p)), res),
                    type_const: make_decl_posed(env, id_pos, TypeConstName::new(id)),
                }));
            }
            res
        }
        Hint_::Hrefinement(root_ty, members) => {
            let root_ty = hint(env, root_ty);
            /* We do not err on duplicate refinements as the parser will
             * already have */
            let mut cr_consts = std::collections::BTreeMap::new();
            for r in members {
                let (id, rc) = match r {
                    aast::Refinement::Rctx(
                        ast_defs::Id(_, id),
                        aast::CtxRefinement::CRexact(h),
                    ) => (
                        id,
                        decl::RefinedConst {
                            bound: decl::RefinedConstBound::Exact(context_hint(env, h)),
                            is_ctx: true,
                        },
                    ),
                    aast::Refinement::Rctx(
                        ast_defs::Id(_, id),
                        aast::CtxRefinement::CRloose(aast::CtxRefinementBounds {
                            lower: cr_lower,
                            upper: cr_upper,
                        }),
                    ) => {
                        let decl_bounds = |h: &Option<Hint>| -> Box<[Ty<R>]> {
                            h.iter().map(|h| context_hint(env, h)).collect()
                        };
                        let tr_lower = decl_bounds(cr_lower);
                        let tr_upper = decl_bounds(cr_upper);
                        (
                            id,
                            decl::RefinedConst {
                                bound: decl::RefinedConstBound::Loose(decl::RefinedConstBounds {
                                    lower: tr_lower,
                                    upper: tr_upper,
                                }),
                                is_ctx: true,
                            },
                        )
                    }
                    aast::Refinement::Rtype(
                        ast_defs::Id(_, id),
                        aast::TypeRefinement::TRexact(h),
                    ) => (
                        id,
                        decl::RefinedConst {
                            bound: decl::RefinedConstBound::Exact(hint(env, h)),
                            is_ctx: false,
                        },
                    ),
                    aast::Refinement::Rtype(
                        ast_defs::Id(_, id),
                        aast::TypeRefinement::TRloose(aast::TypeRefinementBounds {
                            lower: tr_lower,
                            upper: tr_upper,
                        }),
                    ) => {
                        let decl_bounds = |hl: &[Hint]| -> Box<[Ty<R>]> {
                            hl.iter().map(|h| hint(env, h)).collect()
                        };
                        let tr_lower = decl_bounds(tr_lower);
                        let tr_upper = decl_bounds(tr_upper);
                        (
                            id,
                            decl::RefinedConst {
                                bound: decl::RefinedConstBound::Loose(decl::RefinedConstBounds {
                                    lower: tr_lower,
                                    upper: tr_upper,
                                }),
                                is_ctx: false,
                            },
                        )
                    }
                };
                cr_consts.insert(TypeConstName::new(id), rc);
            }
            Ty_::Trefinement(Box::new(decl::TrefinementType {
                ty: root_ty,
                refinement: decl::ClassRefinement { consts: cr_consts },
            }))
        }
        Hint_::Htuple(aast::TupleInfo {
            required: tup_required,
            extra: tup_extra,
        }) => {
            let t_required: Box<[Ty<R>]> = tup_required.iter().map(|h| hint(env, h)).collect();
            let (t_optional, t_extra): (Box<[Ty<R>]>, _) = match tup_extra {
                aast::TupleExtra::Hextra(aast::TupleExtraInfo {
                    optional: tup_optional,
                    variadic: tup_variadic,
                }) => {
                    let t_optional = tup_optional.iter().map(|h| hint(env, h)).collect();
                    let t_variadic = match tup_variadic {
                        None => hint(env, &Hint(p.clone(), Box::new(Hint_::Hnothing))),
                        Some(t) => hint(env, t),
                    };
                    (t_optional, decl::ty::TupleExtra::Tvariadic(t_variadic))
                }
                aast::TupleExtra::Hsplat(tup_splat) => (
                    [].into(),
                    decl::ty::TupleExtra::Tsplat(hint(env, tup_splat)),
                ),
            };
            Ty_::Ttuple(Box::new(decl::ty::TupleType(
                t_required, t_optional, t_extra,
            )))
        }
        Hint_::Hunion(hl) => {
            let tyl = hl.iter().map(|h| hint(env, h)).collect();
            Ty_::Tunion(tyl)
        }
        Hint_::Hintersection(hl) => {
            let tyl = hl.iter().map(|h| hint(env, h)).collect();
            Ty_::Tintersection(tyl)
        }
        Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: nsi_allows_unknown_fields,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) if has_splats(nsi_field_map) => {
            /* The shape's openness: a typed open (`T...`) contributes its type, a bare
            `...` contributes `mixed`, and a closed shape contributes nothing. */
            let open_unknown = if *nsi_allows_unknown_fields {
                match nsi_unknown_fields_type {
                    Some(type_hint) => Some(hint(env, type_hint)),
                    None => Some(hint(env, &Hint(p.clone(), Box::new(Hint_::Hmixed)))),
                }
            } else {
                None
            };
            /* A field-run, a sequence of contiguous fields, carries the openness itself
            so its own explicit fields keep their declared types i.e.
            `shape(..., 'y' => string, ...)`
            means
            `shape(..., ...shape('y' => string, ...))`.
            A closed shape uses `nothing`. */
            let field_run_kind = match &open_unknown {
                Some(ty) => ty.clone(),
                None => hint(env, &Hint(p.clone(), Box::new(Hint_::Hnothing))),
            };
            /* In a shape with fields and splats, adjacent fields not interspersed with
            splats are sugar for a simple shape */
            let make_simple_from_fields = |fields: &[&aast::ShapeFieldInfo]| {
                let mut fdm = std::collections::BTreeMap::new();
                for i in fields {
                    let (name, sft) = shape_field_info_to_shape_field_type(env, i);
                    fdm.insert(name, sft);
                }
                make_decl_ty(
                    env,
                    p,
                    Ty_::Tshape(Box::new(decl::ty::ShapeType::Simple(
                        decl::ty::ShapeTypeSimple(field_run_kind.clone(), fdm),
                    ))),
                )
            };
            /* Fold over the elements and accumulate fields; when we encounter a splat
            we lift the fields into a simple shape. [made_field_run] records whether
            any field-run was created, i.e. whether the openness has been captured.
            (`elems` and `pending` are in order here; the OCaml conses and reverses.) */
            let mut elems: Vec<Ty<R>> = vec![];
            let mut pending: Vec<&aast::ShapeFieldInfo> = vec![];
            let mut made_field_run = false;
            for e in nsi_field_map {
                match e {
                    aast::ShapeElement::SEField(sfi) => pending.push(sfi),
                    aast::ShapeElement::SESplat(h) => {
                        if pending.is_empty() {
                        } else {
                            elems.push(make_simple_from_fields(&pending));
                            made_field_run = true;
                        }
                        let splat_ty = hint(env, h);
                        elems.push(splat_ty);
                        pending.clear();
                    }
                }
            }
            if pending.is_empty() {
            } else {
                elems.push(make_simple_from_fields(&pending));
                made_field_run = true;
            }
            /* If the shape is open but no field-run captured the openness (it consists
            only of splats, e.g. `shape(...Base, ...)`), the trailing `...` / `T...`
            would otherwise be lost. Represent it as a standalone open-empty element
            (i.e. `shape(...Base, ...shape(...))`), placed rightmost. */
            match open_unknown {
                Some(unknown_value) if !made_field_run => {
                    let open_empty = make_decl_ty(
                        env,
                        p,
                        Ty_::Tshape(Box::new(decl::ty::ShapeType::Simple(
                            decl::ty::ShapeTypeSimple(
                                unknown_value,
                                std::collections::BTreeMap::new(),
                            ),
                        ))),
                    );
                    elems.push(open_empty)
                }
                _ => {}
            }
            Ty_::Tshape(Box::new(decl::ty::ShapeType::Splat(elems)))
        }
        Hint_::Hshape(aast::NastShapeInfo {
            allows_unknown_fields: nsi_allows_unknown_fields,
            field_map: nsi_field_map,
            unknown_fields_type: nsi_unknown_fields_type,
        }) => {
            let shape_kind = if *nsi_allows_unknown_fields {
                match nsi_unknown_fields_type {
                    Some(type_hint) => hint(env, type_hint),
                    None => hint(env, &Hint(p.clone(), Box::new(Hint_::Hmixed))),
                }
            } else {
                hint(env, &Hint(p.clone(), Box::new(Hint_::Hnothing)))
            };
            let fields = nsi_field_map.iter().filter_map(|e| match e {
                aast::ShapeElement::SEField(sfi) => Some(sfi),
                aast::ShapeElement::SESplat(_) => None,
            });
            let mut fdm = std::collections::BTreeMap::new();
            for i in fields {
                let (name, sft) = shape_field_info_to_shape_field_type(env, i);
                fdm.insert(name, sft);
            }
            Ty_::Tshape(Box::new(decl::ty::ShapeType::Simple(
                decl::ty::ShapeTypeSimple(shape_kind, fdm),
            )))
        }
        Hint_::Hsoft(Hint(p, h_)) => hint_(p, env, h_),
        Hint_::HfunContext(_) | Hint_::Hvar(_) => {
            crate::diagnostics_state::internal_error(p.clone(), "Unexpected context hint");
            Ty_::Tunion([].into())
        }
    }
}

/// `Typing_defs.get_param_mode`
fn get_param_mode(callconv: &ast_defs::ParamKind) -> decl::ty::ParamMode {
    match callconv {
        ast_defs::ParamKind::Pinout(_) => decl::ty::ParamMode::FPinout,
        ast_defs::ParamKind::Pnormal => decl::ty::ParamMode::FPnormal,
    }
}

/// `Typing_defs.make_fp_flags ~mode ~accept_disposable ~is_optional ~readonly
/// ~ignore_readonly_error ~splat ~named`
fn make_fp_flags(
    mode: decl::ty::ParamMode,
    accept_disposable: bool,
    is_optional: bool,
    readonly: bool,
    ignore_readonly_error: bool,
    splat: bool,
    named: bool,
) -> decl::ty::FunParamFlags {
    use decl::ty::FunParamFlags;
    let inout = match mode {
        decl::ty::ParamMode::FPinout => true,
        decl::ty::ParamMode::FPnormal => false,
    };
    let mut flags = FunParamFlags::empty();
    flags.set(FunParamFlags::INOUT, inout);
    flags.set(FunParamFlags::ACCEPT_DISPOSABLE, accept_disposable);
    flags.set(FunParamFlags::IS_OPTIONAL, is_optional);
    flags.set(FunParamFlags::READONLY, readonly);
    flags.set(FunParamFlags::IGNORE_READONLY_ERROR, ignore_readonly_error);
    flags.set(FunParamFlags::SPLAT, splat);
    flags.set(FunParamFlags::NAMED, named);
    flags
}

/// `Typing_defs_flags.Fun.make kind ~return_disposable ~returns_readonly
/// ~readonly_this ~support_dynamic_type ~is_memoized ~variadic
/// ~named_variadic`
fn fun_make(
    kind: ast_defs::FunKind,
    return_disposable: bool,
    returns_readonly: bool,
    readonly_this: bool,
    support_dynamic_type: bool,
    is_memoized: bool,
    variadic: bool,
    named_variadic: bool,
) -> decl::ty::FunTypeFlags {
    use decl::ty::FunTypeFlags;
    // `fun_kind_to_flags`
    let mut flags = match kind {
        ast_defs::FunKind::FSync => FunTypeFlags::empty(),
        ast_defs::FunKind::FAsync => FunTypeFlags::ASYNC,
        ast_defs::FunKind::FGenerator => FunTypeFlags::GENERATOR,
        ast_defs::FunKind::FAsyncGenerator => FunTypeFlags::ASYNC | FunTypeFlags::GENERATOR,
    };
    flags.set(FunTypeFlags::RETURN_DISPOSABLE, return_disposable);
    flags.set(FunTypeFlags::RETURNS_READONLY, returns_readonly);
    flags.set(FunTypeFlags::READONLY_THIS, readonly_this);
    flags.set(FunTypeFlags::SUPPORT_DYNAMIC_TYPE, support_dynamic_type);
    flags.set(FunTypeFlags::IS_MEMOIZED, is_memoized);
    flags.set(FunTypeFlags::VARIADIC, variadic);
    flags.set(FunTypeFlags::NAMED_VARIADIC, named_variadic);
    flags
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::sync::Arc;

    use oxidized::typechecker_options::TypecheckerOptions;
    use pos::FunName;
    use pos::Prefix;
    use pos::RelativePath;

    use super::*;
    use crate::ctx::Ctx;
    use crate::typing_deps::dep::Variant;

    const HEADER: &str = "<?hh\n<<file:__EnableUnstableFeatures('union_intersection_type_hints', 'like_type_hints', 'shape_splat_concrete', 'shape_splat_type_parameters', 'open_tuples', 'named_parameters', 'type_splat', 'polymorphic_function_hints', 'class_type', 'function_type_optional_params')>>\n";

    /// The hints of the parameters and of the return of every function of
    /// `src`, converted by `hint`, next to the types that the direct decl
    /// parser gave them. Each is `(what, from the hint, from the decl)`.
    fn hints_and_decls(src: &str, everything_sdt: bool) -> Vec<(String, Ty<R>, Ty<R>)> {
        let src = format!("{}{}", HEADER, src);
        let mut tco = TypecheckerOptions::default();
        tco.po.allow_unstable_features = true;
        tco.po.everything_sdt = everything_sdt;
        let ctx = Arc::new(Ctx::new(Path::new("/"), tco).unwrap());
        let path = RelativePath::new(Prefix::Root, "test.php");
        ctx.files.set(path, src.as_str());
        let decls = ctx.decl_parser.parse(path).unwrap();
        ctx.declare_file(path, decls);
        let ox_path: Arc<relative_path::RelativePath> = Arc::new(path.into());
        let named = crate::parse::parse_and_name(&ctx, &ox_path, src.as_bytes());
        assert!(named.diagnostics.is_empty(), "{:?}", named.diagnostics);

        let mut out = vec![];
        let mut funs = 0;
        for def in &named.program.0 {
            let fd = match def {
                aast::Def::Fun(fd) => fd,
                _ => continue,
            };
            funs += 1;
            let name = &fd.name.1;
            let env = Env {
                mode: fd.mode,
                droot: Some(Variant::Fun(name.clone())),
                droot_member: None,
                ctx: Arc::clone(&ctx),
            };
            let fun_decl = ctx
                .shallow_decls
                .get_fun(FunName::new(name))
                .unwrap()
                .unwrap_or_else(|| panic!("no decl for {}", name));
            let ft = match fun_decl.ty.node_ref() {
                Ty_::Tfun(ft) => ft,
                ty_ => panic!("not a function type: {:?}", ty_),
            };
            assert_eq!(fd.fun.params.len(), ft.params.len());
            for (param, fp) in fd.fun.params.iter().zip(ft.params.iter()) {
                let h = param.type_hint.1.as_ref().unwrap();
                out.push((
                    format!("{} {}", name, param.name),
                    hint(&env, h),
                    fp.ty.clone(),
                ));
            }
            if let Some(h) = &fd.fun.ret.1 {
                out.push((format!("{} return", name), hint(&env, h), ft.ret.clone()));
            }
        }
        assert!(funs > 0);
        out
    }

    /// Every type inside `ty` (and `ty` itself), each with its reason.
    fn types_with_reasons(ty: &Ty<R>) -> Vec<String> {
        use ty::visitor::Visitor;
        use ty::visitor::Walkable;
        struct Collect(Vec<String>);
        impl Visitor<R> for Collect {
            fn object(&mut self) -> &mut dyn Visitor<R> {
                self
            }
            fn visit_decl_ty(&mut self, o: &Ty<R>) {
                self.0.push(format!("{:?} with reason {:?}", o, o.reason()));
                o.recurse(self)
            }
        }
        let mut collect = Collect(vec![]);
        ty.accept(&mut collect);
        collect.0
    }

    /// `hint` gives what the direct decl parser gives, reasons and positions
    /// included.
    fn check(src: &str) {
        check_(src, true)
    }

    /// The direct decl parser gives the type of the unknown fields of a shape
    /// (`mixed` for `...`, `nothing` for a closed shape) the position of the
    /// `...` (or of where it would be), whereas `decl_hint.ml` gives it the
    /// position of the whole shape: `hint env (p, Hmixed)`. So for shapes,
    /// everything is compared but those reasons.
    fn check_modulo_shape_kind_reasons(src: &str) {
        check_(src, false)
    }

    fn check_(src: &str, shape_kind_reasons: bool) {
        use pos::ToOxidized;
        let results = hints_and_decls(src, false);
        assert!(!results.is_empty());
        for (what, from_hint, from_decl) in results {
            // The structure, and every position that is not in a reason.
            assert_eq!(
                from_hint.clone().to_oxidized(),
                from_decl.clone().to_oxidized(),
                "{}",
                what
            );
            // The reasons, type by type (all but those of the types of the
            // unknown fields of shapes).
            let from_hint_parts = types_with_reasons(&from_hint);
            let from_decl_parts = types_with_reasons(&from_decl);
            for (h, d) in from_hint_parts.iter().zip(from_decl_parts.iter()) {
                assert_eq!(h, d, "{}", what);
            }
            assert_eq!(from_hint_parts.len(), from_decl_parts.len(), "{}", what);
            if shape_kind_reasons {
                assert_eq!(from_hint, from_decl, "{}", what);
            }
        }
    }

    #[test]
    fn prims() {
        check(
            "function f(int $a, bool $b, float $c, string $d, num $e, arraykey $f, resource $g, null $h): void {}
             function g(): noreturn {}
             function h(mixed $a, nonnull $b, dynamic $c, nothing $d): int { return 1; }",
        );
    }

    #[test]
    fn nullable_and_like() {
        check(
            "function f(?int $a, ?string $b, ~int $d, ~?vec<int> $e, ?~C $f): ?C { return null; }",
        );
    }

    #[test]
    fn generics() {
        check(
            "function f<T as arraykey, Tu super int>(
               T $a, vec<T> $b, dict<T, Tu> $c, \\N\\D<C, vec<int>> $d, Traversable<Tu> $e, keyset<T> $f,
             ): Awaitable<vec<Tu>> {}
             function g(vec_or_dict<int> $a, vec_or_dict<string, C> $b, varray_or_darray<int> $c): void {}",
        );
    }

    #[test]
    fn shapes() {
        check_modulo_shape_kind_reasons(
            "function f(
               shape('a' => int, ?'b' => string) $a,
               shape('a' => int, ...) $b,
               shape(...) $c,
               shape() $d,
               shape(C::KEY => int, nameof C => ?string, 'x' => shape('y' => vec<int>)) $e,
             ): shape('r' => C) {}",
        );
    }

    #[test]
    fn tuples() {
        check(
            "function f(
               (int, string) $a,
               (int, (string, ?C)) $b,
               (int, optional string) $c,
               (int, float...) $d,
               (int, optional string, C...) $e,
             ): (C, D) {}",
        );
    }

    #[test]
    fn function_types() {
        check(
            "function f<T, Tu>(
               (function(int, string): bool) $a,
               (function(): void) $b,
               (function(inout int, T...): Tu) $c,
               (function(int, optional string): noreturn) $d,
               (readonly function(readonly C): readonly D) $e,
               (function(int)[]: void) $f,
               (function(int)[io, rx]: void) $g,
               (function((function(int): string)): (function(): C)) $h,
               ?(function(): Awaitable<int>) $i,
             ): (function(T): Tu) {}",
        );
    }

    #[test]
    fn type_constants() {
        check(
            "function f(C::T $a, C::T::U $b, this::T $c, \\N\\D::TFoo::TBar::TBaz $d, vec<C::T> $e): C::T {}
             function g<T as C>(T::TFoo $a, ?T::TFoo::TBar $b): void {}",
        );
    }

    #[test]
    fn unions_and_intersections() {
        check(
            "function f((int | string) $a, (I & J) $b, (int | (I & J) | null) $c, ?(C | D) $d): (I & J) {}",
        );
    }

    #[test]
    fn this_and_wildcard_free_hints() {
        check("function f(this $a, ?this $b, vec<this> $c, (function(this): this) $d): this {}");
    }

    #[test]
    fn refinements() {
        check(
            "function f(
               C with { type T = int } $a,
               C with { type T as arraykey } $b,
               C with { type T super int as arraykey; type U = vec<string> } $c,
               C with { ctx Cx = [io] } $d,
               C with { ctx Cx super [io] as [io, rx] } $e,
               vec<I with { type T = C::U }> $f,
             ): C with { type T = D } {}",
        );
    }

    #[test]
    fn class_pointers() {
        check("function f(class<C> $a, enum<E> $b, classname<C> $c, ?class<C> $d): class<D> {}");
    }

    #[test]
    fn polymorphic_function_types() {
        check(
            "function f(
               (function<T>(T): T) $a,
               (function<T as arraykey, Tu super int>(T, vec<Tu>): dict<T, Tu>) $b,
             ): void {}",
        );
    }

    #[test]
    fn named_and_splat_parameters() {
        check(
            "function f(
               (function(int, named string $s): void) $a,
               (function(int, optional named string $s): void) $b,
             ): void {}",
        );
    }

    #[test]
    fn shape_splats() {
        check_modulo_shape_kind_reasons(
            "function f(
               shape(...S) $a,
               shape('a' => int, ...S) $b,
               shape(...S, 'a' => int, ...T2, 'b' => string, 'c' => C) $c,
               shape(...S, ...) $d,
               shape('a' => int, ...S, ...) $e,
             ): void {}",
        );
    }

    /// Under implicit pessimisation, the type parameters of a polymorphic
    /// function type get the bound `supportdyn<mixed>`.
    #[test]
    fn everything_sdt_polymorphic_function_type() {
        let results = hints_and_decls(
            "function f((function<T, <<__NoAutoBound>> Tu as int>(T): Tu) $a): void {}",
            true,
        );
        let (_, from_hint, _) = &results[0];
        // Naming wraps the function type in `supportdyn`.
        let fun_ty = match from_hint.node_ref() {
            Ty_::Tapply(id_and_args) => {
                assert_eq!(id_and_args.0.id().as_str(), sn::classes::SUPPORT_DYN);
                &id_and_args.1[0]
            }
            _ => from_hint,
        };
        let ft = match fun_ty.node_ref() {
            Ty_::Tfun(ft) => ft,
            ty_ => panic!("{:?}", ty_),
        };
        assert_eq!(ft.tparams.len(), 2);
        let bounds = |i: usize| -> Vec<String> {
            ft.tparams[i]
                .constraints
                .iter()
                .map(|(_, ty)| format!("{:?}", ty.node_ref()))
                .collect()
        };
        assert_eq!(bounds(0).len(), 1);
        assert!(bounds(0)[0].contains("supportdyn"), "{:?}", bounds(0));
        assert_eq!(bounds(1).len(), 1);
        assert!(bounds(1)[0].contains("Tint"), "{:?}", bounds(1));
        assert!(!ft.instantiated);
    }

    /// The type of the unknown fields of a shape has the position of the
    /// shape, as do the types `decl_hint.ml` makes up for the fields that are
    /// next to each other in a shape with splats.
    #[test]
    fn shape_kind_reasons() {
        let results = hints_and_decls(
            "function f(shape('a' => int) $a, shape('a' => int, ...) $b, shape('a' => int, ...S, ...) $c): void {}",
            false,
        );
        let kind_of = |ty: &Ty<R>| -> Ty<R> {
            match ty.node_ref() {
                Ty_::Tshape(shape) => match &**shape {
                    decl::ty::ShapeType::Simple(decl::ty::ShapeTypeSimple(kind, _)) => kind.clone(),
                    shape => panic!("{:?}", shape),
                },
                ty_ => panic!("{:?}", ty_),
            }
        };
        let (_, closed, _) = &results[0];
        let kind = kind_of(closed);
        assert!(matches!(kind.node_ref(), Ty_::Tunion(tys) if tys.is_empty()));
        assert_eq!(kind.reason(), closed.reason());
        let (_, open, _) = &results[1];
        let kind = kind_of(open);
        assert!(matches!(kind.node_ref(), Ty_::Tmixed));
        assert_eq!(kind.reason(), open.reason());
        let (_, splat, _) = &results[2];
        match splat.node_ref() {
            Ty_::Tshape(shape) => match &**shape {
                decl::ty::ShapeType::Splat(elems) => {
                    assert_eq!(elems.len(), 2);
                    assert_eq!(elems[0].reason(), splat.reason());
                    let kind = kind_of(&elems[0]);
                    assert!(matches!(kind.node_ref(), Ty_::Tmixed));
                    assert_eq!(kind.reason(), splat.reason());
                    assert!(matches!(elems[1].node_ref(), Ty_::Tapply(_)));
                }
                shape => panic!("{:?}", shape),
            },
            ty_ => panic!("{:?}", ty_),
        }
    }

    /// (The type of a variadic parameter is left out: the declaration of the
    /// function gives it another reason than the one of its hint.)
    #[test]
    fn soft_and_parameter_kinds() {
        check(
            "function f(<<__Soft>> int $a, inout vec<int> $b, readonly C $c, int $d = 1): <<__Soft>> ?C {}
             function g(<<__Soft>> vec<C::T> $a, ?(function(<<__Soft>> int): void) $b): void {}",
        );
    }

    #[test]
    fn namespaces() {
        check(
            "namespace N;
             function f(C $a, \\M\\D $b, vec<C> $c, namespace\\E $d, int $e, C::T $f): Awaitable<C> {}",
        );
    }

    /// The type parameters of a function, next to those of its declaration.
    #[test]
    fn type_parameters() {
        let src = format!(
            "{}{}",
            HEADER,
            "function f<<<__Enforceable>> reify T as arraykey, Tu super int as num, <<__Soft>> reify Tv, Tw as vec<T>>(): void {}"
        );
        let mut tco = TypecheckerOptions::default();
        tco.po.allow_unstable_features = true;
        let ctx = Arc::new(Ctx::new(Path::new("/"), tco).unwrap());
        let path = RelativePath::new(Prefix::Root, "test.php");
        ctx.files.set(path, src.as_str());
        let decls = ctx.decl_parser.parse(path).unwrap();
        ctx.declare_file(path, decls);
        let ox_path: Arc<relative_path::RelativePath> = Arc::new(path.into());
        let named = crate::parse::parse_and_name(&ctx, &ox_path, src.as_bytes());
        assert!(named.diagnostics.is_empty(), "{:?}", named.diagnostics);
        let fd = named
            .program
            .0
            .iter()
            .find_map(|def| match def {
                aast::Def::Fun(fd) => Some(fd),
                _ => None,
            })
            .unwrap();
        let env = Env {
            mode: fd.mode,
            droot: Some(Variant::Fun(fd.name.1.clone())),
            droot_member: None,
            ctx: Arc::clone(&ctx),
        };
        let fun_decl = ctx
            .shallow_decls
            .get_fun(FunName::new(&fd.name.1))
            .unwrap()
            .unwrap();
        let ft = match fun_decl.ty.node_ref() {
            Ty_::Tfun(ft) => ft,
            ty_ => panic!("not a function type: {:?}", ty_),
        };
        assert_eq!(fd.tparams.len(), 4);
        assert_eq!(ft.tparams.len(), 4);
        for (t, from_decl) in fd.tparams.iter().zip(ft.tparams.iter()) {
            let from_ast = aast_tparam_to_decl_tparam(&env, t);
            assert_eq!(format!("{:?}", from_ast), format!("{:?}", from_decl));
            assert_eq!(&from_ast, from_decl);
        }
    }

    /// Context hints become the generics that stand for them.
    #[test]
    fn context_hints() {
        let mut tco = TypecheckerOptions::default();
        tco.po.allow_unstable_features = true;
        let ctx = Arc::new(Ctx::new(Path::new("/"), tco).unwrap());
        let env = Env {
            mode: oxidized::file_info::Mode::Mstrict,
            droot: Some(Variant::Fun("\\f".to_string())),
            droot_member: None,
            ctx,
        };
        let p = Pos::NONE;
        let h = |h_: Hint_| Hint(p.clone(), Box::new(h_));
        let id = |s: &str| ast_defs::Id(p.clone(), s.to_string());
        let generic = |ty: &Ty<R>| match ty.node_ref() {
            Ty_::Tgeneric(name) => name.as_str().to_string(),
            ty_ => panic!("{:?}", ty_),
        };
        assert_eq!(
            generic(&context_hint(
                &env,
                &h(Hint_::HfunContext("$f".to_string()))
            )),
            "T/[ctx $f]"
        );
        assert_eq!(
            generic(&context_hint(
                &env,
                &h(Hint_::Haccess(
                    h(Hint_::Hvar("$x".to_string())),
                    vec![id("C"), id("D")]
                ))
            )),
            "T/[$x::C::D]"
        );
        assert_eq!(
            generic(&context_hint(
                &env,
                &h(Hint_::Haccess(
                    h(Hint_::Habstr("T".to_string())),
                    vec![id("C")]
                ))
            )),
            "T/[T::C]"
        );
        // A single generic context is not wrapped in an intersection.
        let contexts = aast::Contexts(p.clone(), vec![h(Hint_::HfunContext("$f".to_string()))]);
        match aast_contexts_to_decl_capability(&env, Some(&contexts), &p).1 {
            decl::ty::Capability::CapTy(ty) => assert_eq!(generic(&ty), "T/[ctx $f]"),
            cap => panic!("{:?}", cap),
        }
        let contexts = aast::Contexts(
            p.clone(),
            vec![h(Hint_::Happly(id("\\HH\\Contexts\\io"), vec![]))],
        );
        match aast_contexts_to_decl_capability(&env, Some(&contexts), &p).1 {
            decl::ty::Capability::CapTy(ty) => {
                assert!(matches!(ty.node_ref(), Ty_::Tintersection(tys) if tys.len() == 1))
            }
            cap => panic!("{:?}", cap),
        }
        assert!(matches!(
            aast_contexts_to_decl_capability(&env, None, &p).1,
            decl::ty::Capability::CapDefaults(_)
        ));
    }
}
