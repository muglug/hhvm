// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_json.ml`. See `hh/PORTING.md`.
//!
//! Convert a type to a structured JSON value (`Yojson.Safe.t`,
//! `crate::yojson::safe::T`), and back. See `typing_json.mli` for the
//! format.
//!
//! The JSON strings are Rust strings: the names of shape fields, which are
//! byte strings, are converted as UTF-8 (invalid bytes replaced).

use std::sync::Arc;

use naming_special_names_rust as sn;
use oxidized::ast_defs;
use oxidized::ast_defs::Tprim;
use oxidized::pos_or_decl::PosOrDecl;

use crate::class_refinement;
use crate::ctx::Ctx;
use crate::decl_entry;
use crate::decl_provider;
use crate::folded_class as cls;
use crate::hh_json_helpers::access;
use crate::hh_json_helpers::access::AccessFailure;
use crate::hh_json_helpers::access::Keytrace;
use crate::typing_defs::Capability;
use crate::typing_defs::ClassRefinement;
use crate::typing_defs::DeserializationError;
use crate::typing_defs::Exact;
use crate::typing_defs::FunImplicitParams;
use crate::typing_defs::FunParam;
use crate::typing_defs::FunType;
use crate::typing_defs::ParamMode;
use crate::typing_defs::PosByteString;
use crate::typing_defs::PosString;
use crate::typing_defs::RefinedConst;
use crate::typing_defs::RefinedConstBound;
use crate::typing_defs::RefinedConstBounds;
use crate::typing_defs::ShapeFieldPredicate;
use crate::typing_defs::ShapeFieldType;
use crate::typing_defs::ShapePredicate;
use crate::typing_defs::ShapeType;
use crate::typing_defs::ShapeTypeSimple;
use crate::typing_defs::ShapeTypeSplat;
use crate::typing_defs::TaccessType;
use crate::typing_defs::Tparam;
use crate::typing_defs::TshapeFieldName;
use crate::typing_defs::TuplePredicate;
use crate::typing_defs::TupleExtra;
use crate::typing_defs::TupleType;
use crate::typing_defs::Ty;
use crate::typing_defs::Ty_;
use crate::typing_defs::TypeOrigin;
use crate::typing_defs::TypePredicate;
use crate::typing_defs::TypePredicate_;
use crate::typing_defs::TypeTag;
use crate::typing_defs::TypeTagGeneric;
use crate::typing_defs::UserAttribute;
use crate::typing_defs::get_fp_is_named;
use crate::typing_defs::get_fp_is_optional;
use crate::typing_defs::get_fp_mode;
use crate::typing_defs::get_fp_readonly;
use crate::typing_defs::get_ft_named_variadic;
use crate::typing_defs::get_ft_readonly_this;
use crate::typing_defs::get_ft_returns_readonly;
use crate::typing_defs::get_ft_variadic;
use crate::typing_defs::get_node;
use crate::typing_defs::get_pos;
use crate::typing_defs::get_reason;
use crate::typing_defs::is_dynamic;
use crate::typing_defs::is_nothing;
use crate::typing_defs::make_fp_flags;
use crate::typing_defs::make_tany;
use crate::typing_defs::mk;
use crate::typing_defs::nonexact;
use crate::typing_defs::set_ft_readonly_this;
use crate::typing_defs::set_ft_returns_readonly;
use crate::typing_defs::t_shape_map::TShapeField;
use crate::typing_defs::t_shape_map::TShapeMap;
use crate::typing_defs_flags;
use crate::typing_env_types;
use crate::typing_env_types::Env;
use crate::typing_inference_env;
use crate::typing_make_type;
use crate::typing_reason as reason;
use crate::yojson::safe as yojson;

/// `Yojson.Safe.t`
type J = yojson::T;

/// `Naming_special_names.Classes.cString` (`naming_special_names_rust` has
/// it as `typehints::HH_STRING` only).
const C_STRING: &str = sn::typehints::HH_STRING;

/// `l1 @ l2 @ ...`
fn cat(lists: Vec<Vec<(String, J)>>) -> Vec<(String, J)> {
    lists.into_iter().flatten().collect()
}

fn show_supportdyn(env: &Env) -> bool {
    (!env.genv.tcopt.po.everything_sdt) || typing_env_types::get_log_level(env, "show") >= 1
}

fn param_mode_to_string(mode: &ParamMode) -> String {
    match mode {
        ParamMode::FPnormal => "normal",
        ParamMode::FPinout => "inout",
    }
    .to_string()
}

fn string_to_param_mode(s: &str) -> Option<ParamMode> {
    match s {
        "normal" => Some(ParamMode::FPnormal),
        "inout" => Some(ParamMode::FPinout),
        _ => None,
    }
}

fn is_like(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tunion(tyl) => tyl.iter().any(is_dynamic),
        _ => false,
    }
}

fn cstr_kind(cstr_kind: &ast_defs::ConstraintKind) -> (String, J) {
    let kind_str = match cstr_kind {
        ast_defs::ConstraintKind::ConstraintAs => "as",
        ast_defs::ConstraintKind::ConstraintSuper => "super",
        ast_defs::ConstraintKind::ConstraintEq => "eq",
    };
    ("kind".to_string(), J::String(kind_str.to_string()))
}

fn user_attribute(ua: &UserAttribute) -> J {
    let (_, name) = &ua.name;
    let fields = vec![("name".to_string(), J::String(name.clone()))];
    J::Assoc(fields)
}

fn from_type(env: &Env, show_like_ty: bool, ty: &Ty) -> J {
    // Helpers to construct fields that appear in JSON rendering of type
    fn obj(x: Vec<(String, J)>) -> J {
        J::Assoc(x)
    }
    fn kind(p: &PosOrDecl, k: &str) -> Vec<(String, J)> {
        vec![
            ("src_pos".to_string(), crate::pos_or_decl::json(p)),
            ("kind".to_string(), J::String(k.to_string())),
        ]
    }
    fn name(x: &str) -> Vec<(String, J)> {
        vec![("name".to_string(), J::String(x.to_string()))]
    }
    fn optional(x: bool) -> Vec<(String, J)> {
        vec![("optional".to_string(), J::Bool(x))]
    }
    fn is_array(x: bool) -> Vec<(String, J)> {
        vec![("is_array".to_string(), J::Bool(x))]
    }
    fn shape_field_name_to_json(shape_field: &TshapeFieldName) -> J {
        // TODO: need to update userland tooling?
        match shape_field {
            TshapeFieldName::TSFregexGroup(PosString(_, s)) => J::Intlit(s.clone()),
            TshapeFieldName::TSFlitStr(PosByteString(_, s)) => {
                J::String(String::from_utf8_lossy(s).into_owned())
            }
            TshapeFieldName::TSFclassConst((_, s1), PosString(_, s2)) => {
                J::List(vec![J::String(s1.clone()), J::String(s2.clone())])
            }
        }
    }
    let args = |tys: &[Ty]| {
        vec![(
            "args".to_string(),
            J::List(tys.iter().map(|ty| from_type(env, show_like_ty, ty)).collect()),
        )]
    };
    let optional_args = |tys: &[Ty]| {
        if tys.is_empty() {
            vec![]
        } else {
            vec![(
                "optional_args".to_string(),
                J::List(tys.iter().map(|ty| from_type(env, show_like_ty, ty)).collect()),
            )]
        }
    };
    let variadic_arg = |ty: &Ty| {
        if is_nothing(ty) {
            vec![]
        } else {
            vec![("variadic_arg".to_string(), from_type(env, show_like_ty, ty))]
        }
    };
    let splat_arg = |ty: &Ty| vec![("splat_arg".to_string(), from_type(env, show_like_ty, ty))];
    let extra_arg = |t_extra: &TupleExtra| match t_extra {
        TupleExtra::Tvariadic(t_variadic) => variadic_arg(t_variadic),
        TupleExtra::Tsplat(t_splat) => splat_arg(t_splat),
    };
    let refs = |e: &Exact| match e {
        Exact::Exact => vec![],
        Exact::Nonexact(r) if class_refinement::is_empty(r) => vec![],
        Exact::Nonexact(ClassRefinement { cr_consts }) => {
            let ref_const = |(id, rc): (&String, &RefinedConst)| {
                let RefinedConst {
                    bound: rc_bound,
                    is_ctx: rc_is_ctx,
                } = rc;
                let is_ctx_json = ("is_ctx".to_string(), J::Bool(*rc_is_ctx));
                match rc_bound {
                    RefinedConstBound::TRexact(ty) => obj(vec![
                        ("type".to_string(), J::String(id.clone())),
                        ("equal".to_string(), from_type(env, show_like_ty, ty)),
                        is_ctx_json,
                    ]),
                    RefinedConstBound::TRloose(RefinedConstBounds {
                        lower: tr_lower,
                        upper: tr_upper,
                    }) => {
                        let ty_list = |tys: &[Ty]| {
                            J::List(tys.iter().map(|ty| from_type(env, show_like_ty, ty)).collect())
                        };
                        obj(vec![
                            ("type".to_string(), J::String(id.clone())),
                            ("lower".to_string(), ty_list(tr_lower)),
                            ("upper".to_string(), ty_list(tr_upper)),
                            is_ctx_json,
                        ])
                    }
                }
            };
            vec![(
                "refs".to_string(),
                J::List(cr_consts.iter().map(ref_const).collect()),
            )]
        }
    };
    let typ = |ty: &Ty| vec![("type".to_string(), from_type(env, show_like_ty, ty))];
    let result = |ty: &Ty| vec![("result".to_string(), from_type(env, show_like_ty, ty))];
    let make_field = |(k, v): (&TShapeField, &ShapeFieldType)| {
        obj(cat(vec![
            vec![("name".to_string(), shape_field_name_to_json(&k.0))],
            optional(v.optional),
            typ(&v.ty),
        ]))
    };
    let fields = |fl: Vec<(&TShapeField, &ShapeFieldType)>| {
        vec![(
            "fields".to_string(),
            J::List(fl.into_iter().map(make_field).collect()),
        )]
    };
    let as_type = |ty: &Ty| vec![("as".to_string(), from_type(env, show_like_ty, ty))];
    match (get_pos(ty), get_node(ty)) {
        (_, Ty_::Tvar(n)) => {
            // The environment that `expand_type` returns is dropped.
            let ty = typing_inference_env::expand_type(
                &mut env.inference_env.clone(),
                mk((get_reason(ty).clone(), Ty_::Tvar(*n))),
            );
            match (get_pos(&ty), get_node(&ty)) {
                (p, Ty_::Tvar(_)) => obj(kind(&p, "var")),
                _ => from_type(env, show_like_ty, &ty),
            }
        }
        (
            p,
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: t_extra,
            }),
        ) => obj(cat(vec![
            kind(&p, "tuple"),
            is_array(false),
            args(t_required),
            optional_args(t_optional),
            extra_arg(t_extra),
        ])),
        (p, Ty_::Tany(_)) => obj(kind(&p, "any")),
        (p, Ty_::Tnonnull) => obj(kind(&p, "nonnull")),
        (p, Ty_::Tdynamic(_)) => obj(kind(&p, "dynamic")),
        (p, Ty_::Tgeneric(s)) => obj(cat(vec![kind(&p, "generic"), name(s)])),
        (_, Ty_::Tnewtype(s, tys, _))
            if tys.len() == 1 && s == sn::classes::SUPPORT_DYN && !show_supportdyn(env) =>
        {
            from_type(env, show_like_ty, &tys[0])
        }
        // (`>>| Cls.enum_type` maps the class to `Some _` whether or not it is
        // an enum: the guard holds whenever the class exists.)
        (p, Ty_::Tnewtype(s, _, ty))
            if decl_entry::to_option(decl_provider::get_class(None, &env.decl_env.ctx, s))
                .map(|c| cls::enum_type(&c))
                .is_some() =>
        {
            obj(cat(vec![kind(&p, "enum"), name(s), as_type(ty)]))
        }
        (p, Ty_::Tnewtype(s, tys, ty)) => {
            obj(cat(vec![kind(&p, "newtype"), name(s), args(tys), as_type(ty)]))
        }
        (p, Ty_::Tdependent(crate::typing_defs::DependentType::DTexpr(_), ty)) => obj(cat(vec![
            kind(&p, "path"),
            vec![("type".to_string(), obj(kind(&get_pos(ty), "expr")))],
            as_type(ty),
        ])),
        (p, Ty_::Toption(ty)) => match get_node(ty) {
            Ty_::Tnonnull => obj(kind(&p, "mixed")),
            _ => obj(cat(vec![kind(&p, "nullable"), args(std::slice::from_ref(ty))])),
        },
        (p, Ty_::Tprim(tp)) => obj(cat(vec![
            kind(&p, "primitive"),
            name(&crate::aast_defs::string_of_tprim(*tp)),
        ])),
        (p, Ty_::Tneg(predicate)) => {
            fn tag_json(env: &Env, show_like_ty: bool, tag: &TypeTag) -> Vec<(String, J)> {
                match tag {
                    TypeTag::BoolTag => name("isbool"),
                    TypeTag::IntTag => name("isint"),
                    TypeTag::ArraykeyTag => name("isarraykey"),
                    TypeTag::FloatTag => name("isfloat"),
                    TypeTag::NumTag => name("isnum"),
                    TypeTag::ResourceTag => name("isresource"),
                    TypeTag::NullTag => name("isnull"),
                    TypeTag::ClassTag(s, args) => {
                        if C_STRING == s {
                            name("isstring")
                        } else {
                            let generic_json = |g: &TypeTagGeneric| match g {
                                TypeTagGeneric::Filled(ty) => obj(vec![
                                    (
                                        "generic_kind".to_string(),
                                        J::String("filled".to_string()),
                                    ),
                                    ("type".to_string(), from_type(env, show_like_ty, ty)),
                                ]),
                                TypeTagGeneric::Wildcard(_) => obj(vec![(
                                    "generic_kind".to_string(),
                                    J::String("wildcard".to_string()),
                                )]),
                            };
                            let args_json: Vec<J> = args.iter().map(generic_json).collect();
                            cat(vec![name(s), vec![("args".to_string(), J::List(args_json))]])
                        }
                    }
                    TypeTag::EnumTag(s) => name(s),
                    TypeTag::GenericTag {
                        name: s,
                        from_like: _,
                    } => name(s),
                }
            }
            fn predicate_json(
                env: &Env,
                show_like_ty: bool,
                predicate: &TypePredicate,
            ) -> Vec<(String, J)> {
                let TypePredicate(_, predicate_) = predicate;
                match predicate_ {
                    TypePredicate_::IsTag(tag) => tag_json(env, show_like_ty, tag),
                    TypePredicate_::IsTupleOf(TuplePredicate {
                        required: tp_required,
                    }) => {
                        let predicates_json = tp_required
                            .iter()
                            .map(|p| obj(predicate_json(env, show_like_ty, p)))
                            .collect();
                        cat(vec![
                            name("istuple"),
                            vec![("args".to_string(), J::List(predicates_json))],
                        ])
                    }
                    TypePredicate_::IsShapeOf(ShapePredicate {
                        fields: sp_fields,
                        allows_unknown_fields: sp_allows_unknown_fields,
                    }) => cat(vec![
                        name("isshape"),
                        vec![
                            (
                                "fields".to_string(),
                                J::List(
                                    sp_fields
                                        .iter()
                                        .map(
                                            |(
                                                field,
                                                ShapeFieldPredicate {
                                                    predicate: sfp_predicate,
                                                    optional: sfp_optional,
                                                },
                                            )| {
                                                obj(vec![
                                                    (
                                                        "name".to_string(),
                                                        shape_field_name_to_json(&field.0),
                                                    ),
                                                    (
                                                        "predicate".to_string(),
                                                        obj(predicate_json(
                                                            env,
                                                            show_like_ty,
                                                            sfp_predicate,
                                                        )),
                                                    ),
                                                    ("optional".to_string(), J::Bool(*sfp_optional)),
                                                ])
                                            },
                                        )
                                        .collect(),
                                ),
                            ),
                            (
                                "allows_unknown_fields".to_string(),
                                J::Bool(*sp_allows_unknown_fields),
                            ),
                        ],
                    ]),
                    TypePredicate_::IsUnionOf(predicates) => {
                        let predicates_json = predicates
                            .iter()
                            .map(|p| obj(predicate_json(env, show_like_ty, p)))
                            .collect();
                        cat(vec![
                            name("isunion"),
                            vec![("args".to_string(), J::List(predicates_json))],
                        ])
                    }
                    TypePredicate_::IsNot(inner) => cat(vec![
                        name("isnot"),
                        vec![(
                            "arg".to_string(),
                            obj(predicate_json(env, show_like_ty, inner)),
                        )],
                    ]),
                    // TODO: T196048813 optional, open, fuel?
                }
            }
            obj(cat(vec![
                kind(&p, "negation"),
                predicate_json(env, show_like_ty, predicate),
            ]))
        }
        (p, Ty_::Tclass((_, cid), e, tys)) => {
            if C_STRING == cid {
                obj(cat(vec![kind(&p, "primitive"), name("string")]))
            } else {
                obj(cat(vec![kind(&p, "class"), name(cid), args(tys), refs(e)]))
            }
        }
        (
            p,
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: shape_kind,
                fields: fl,
            })),
        ) => {
            let fields_known = is_nothing(shape_kind);
            let unknown_fields_type = if fields_known
                || crate::typing_defs_core::ty_equal(
                    None,
                    shape_kind,
                    &typing_make_type::mixed(reason::none()),
                ) {
                vec![]
            } else {
                vec![(
                    "unknown_fields_type".to_string(),
                    from_type(env, show_like_ty, shape_kind),
                )]
            };
            obj(cat(vec![
                kind(&p, "shape"),
                is_array(false),
                vec![("fields_known".to_string(), J::Bool(fields_known))],
                unknown_fields_type,
                fields(fl.iter().collect()),
            ]))
        }
        (p, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))) => obj(cat(vec![
            kind(&p, "shape_splat"),
            vec![(
                "elems".to_string(),
                J::List(
                    ss_elems
                        .iter()
                        .map(|ty| from_type(env, show_like_ty, ty))
                        .collect(),
                ),
            )],
        ])),
        (p, Ty_::Tunion(tyl)) if tyl.is_empty() => obj(kind(&p, "nothing")),
        (_, Ty_::Tunion(tyl)) if tyl.len() == 1 => from_type(env, show_like_ty, &tyl[0]),
        (p, Ty_::Tunion(tyl)) => {
            if show_like_ty {
                obj(cat(vec![kind(&p, "union"), args(tyl)]))
            } else {
                let non_dynamic: Vec<&Ty> = tyl.iter().filter(|ty| !is_dynamic(ty)).collect();
                match non_dynamic.as_slice() {
                    [ty] => from_type(env, show_like_ty, ty),
                    _ => obj(cat(vec![kind(&p, "union"), args(tyl)])),
                }
            }
        }
        (p, Ty_::Tintersection(tyl)) if tyl.is_empty() => obj(kind(&p, "mixed")),
        (_, Ty_::Tintersection(tyl)) if tyl.len() == 1 => from_type(env, show_like_ty, &tyl[0]),
        (p, Ty_::Tintersection(tyl)) => {
            if show_like_ty {
                obj(cat(vec![kind(&p, "intersection"), args(tyl)]))
            } else {
                match tyl.iter().find(|ty| is_like(ty)) {
                    None => obj(cat(vec![kind(&p, "intersection"), args(tyl)])),
                    Some(ty) => from_type(env, show_like_ty, ty),
                }
            }
        }
        (p, Ty_::Tfun(ft)) => {
            let fun_kind = |p: &PosOrDecl| kind(p, "function");
            let callconv = |cc: ParamMode| {
                vec![(
                    "callConvention".to_string(),
                    J::String(param_mode_to_string(&cc)),
                )]
            };
            let readonly_param = |ro: bool| {
                if ro {
                    vec![("readonly".to_string(), J::Bool(true))]
                } else {
                    vec![]
                }
            };
            let optional_param = |opt: bool| {
                if opt {
                    vec![("optional".to_string(), J::Bool(true))]
                } else {
                    vec![]
                }
            };
            let named_param = |fp: &FunParam| {
                if get_fp_is_named(fp) {
                    let name_field = match &fp.name {
                        Some(name) => vec![("name".to_string(), J::String(name.clone()))],
                        None => vec![],
                    };
                    let mut l = vec![("named".to_string(), J::Bool(true))];
                    l.extend(name_field);
                    l
                } else {
                    vec![]
                }
            };
            let param = |fp: &FunParam| {
                obj(cat(vec![
                    callconv(get_fp_mode(fp)),
                    readonly_param(get_fp_readonly(fp)),
                    optional_param(get_fp_is_optional(fp)),
                    named_param(fp),
                    typ(&fp.type_),
                ]))
            };
            let member_if_true = |name: &str, value: bool| {
                if value {
                    vec![(name.to_string(), J::Bool(true))]
                } else {
                    vec![]
                }
            };
            let params = |fps: &[FunParam]| {
                vec![(
                    "params".to_string(),
                    J::List(fps.iter().map(param).collect()),
                )]
            };
            // Function type parameters shouldn't be declared with variance annotations
            let tparams = |ft_tparams: &[Tparam]| {
                vec![(
                    "tparams".to_string(),
                    J::List(
                        ft_tparams
                            .iter()
                            .map(
                                |Tparam {
                                     name: tp_name,
                                     constraints: tp_constraints,
                                     user_attributes: tp_user_attributes,
                                     ..
                                 }| {
                                    obj(vec![
                                        ("name".to_string(), J::String(tp_name.1.clone())),
                                        (
                                            "constraints".to_string(),
                                            J::List(
                                                tp_constraints
                                                    .iter()
                                                    .map(|(c, ty)| {
                                                        let mut l = vec![cstr_kind(c)];
                                                        l.extend(typ(ty));
                                                        obj(l)
                                                    })
                                                    .collect(),
                                            ),
                                        ),
                                        (
                                            "user_attributes".to_string(),
                                            J::List(
                                                tp_user_attributes
                                                    .iter()
                                                    .map(user_attribute)
                                                    .collect(),
                                            ),
                                        ),
                                    ])
                                },
                            )
                            .collect(),
                    ),
                )]
            };
            let capability = match &ft.implicit_params.capability {
                Capability::CapDefaults(_) => vec![],
                Capability::CapTy(capty) => {
                    vec![("capability".to_string(), from_type(env, show_like_ty, capty))]
                }
            };
            obj(cat(vec![
                fun_kind(&p),
                member_if_true("readonly_this", get_ft_readonly_this(ft)),
                tparams(&ft.tparams),
                params(&ft.params),
                member_if_true("variadic", get_ft_variadic(ft)),
                member_if_true("named_variadic", get_ft_named_variadic(ft)),
                member_if_true("readonly_return", get_ft_returns_readonly(ft)),
                result(&ft.ret),
                capability,
            ]))
        }
        (p, Ty_::TvecOrDict(ty1, ty2)) => obj(cat(vec![
            kind(&p, "vec_or_dict"),
            args(&[ty1.clone(), ty2.clone()]),
        ])),
        // TODO akenn
        (p, Ty_::Taccess(TaccessType(ty, _id))) => obj(cat(vec![
            kind(&p, "type_constant"),
            args(std::slice::from_ref(ty)),
        ])),
        (p, Ty_::Tlabel(s)) => obj(cat(vec![kind(&p, "label"), name(s)])),
        (p, Ty_::TclassPtr(ty)) => obj(cat(vec![kind(&p, "class_ptr"), typ(ty)])),
    }
}

pub type DeserializedResult = Result<Ty, DeserializationError>;

fn wrap_json_accessor<X, A>(
    f: impl FnOnce(X) -> Result<A, AccessFailure>,
    x: X,
) -> Result<A, DeserializationError> {
    match f(x) {
        Ok(value) => Ok(value),
        Err(access_failure) => Err(DeserializationError::DeserializationError(
            access::access_failure_to_string(&access_failure),
        )),
    }
}

fn wrap_json_accessor_with_default<X, A>(
    default: A,
    f: impl FnOnce(X) -> Result<A, AccessFailure>,
    x: X,
) -> Result<A, DeserializationError> {
    match f(x) {
        Ok(value) => Ok(value),
        Err(AccessFailure::MissingKeyError(..)) => Ok(default),
        Err(access_failure) => Err(DeserializationError::DeserializationError(
            access::access_failure_to_string(&access_failure),
        )),
    }
}

fn wrap_json_accessor_with_opt<X, A>(
    f: impl FnOnce(X) -> Result<A, AccessFailure>,
    x: X,
) -> Result<Option<A>, DeserializationError> {
    match f(x) {
        Ok(value) => Ok(Some(value)),
        Err(AccessFailure::MissingKeyError(..)) => Ok(None),
        Err(access_failure) => Err(DeserializationError::DeserializationError(
            access::access_failure_to_string(&access_failure),
        )),
    }
}

fn get_string(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(String, Keytrace), DeserializationError> {
    wrap_json_accessor(|jk| access::get_string(x, jk), json_keytrace)
}

fn get_bool(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(bool, Keytrace), DeserializationError> {
    wrap_json_accessor(|jk| access::get_bool(x, jk), json_keytrace)
}

fn get_array(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(Vec<J>, Keytrace), DeserializationError> {
    wrap_json_accessor(|jk| access::get_array(x, jk), json_keytrace)
}

fn get_array_opt(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(Vec<J>, Keytrace), DeserializationError> {
    wrap_json_accessor_with_default((vec![], vec![]), |jk| access::get_array(x, jk), json_keytrace)
}

fn get_val(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(J, Keytrace), DeserializationError> {
    wrap_json_accessor(|jk| access::get_val(x, jk), json_keytrace)
}

fn get_obj(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<(J, Keytrace), DeserializationError> {
    wrap_json_accessor(|jk| access::get_obj(x, jk), json_keytrace)
}

fn get_obj_opt(
    x: &str,
    json_keytrace: (&J, &Keytrace),
) -> Result<Option<(J, Keytrace)>, DeserializationError> {
    wrap_json_accessor_with_opt(|jk| access::get_obj(x, jk), json_keytrace)
}

fn deserialization_error<A>(message: &str, keytrace: &Keytrace) -> Result<A, DeserializationError> {
    Err(DeserializationError::DeserializationError(
        message.to_string() + &access::keytrace_to_string(keytrace),
    ))
}

fn not_supported<A>(message: &str, keytrace: &Keytrace) -> Result<A, DeserializationError> {
    Err(DeserializationError::NotSupported(
        message.to_string() + &access::keytrace_to_string(keytrace),
    ))
}

fn get_constraint_kind(
    key: &str,
    (json, keytrace): (&J, &Keytrace),
) -> Result<ast_defs::ConstraintKind, DeserializationError> {
    let (kind_str, keytrace) = get_string(key, (json, keytrace))?;
    match kind_str.as_str() {
        "as" => Ok(ast_defs::ConstraintKind::ConstraintAs),
        "super" => Ok(ast_defs::ConstraintKind::ConstraintSuper),
        "eq" => Ok(ast_defs::ConstraintKind::ConstraintEq),
        _ => deserialization_error("Expected constraint kind", &keytrace),
    }
}

/// `k :: keytrace`
fn cons(k: String, keytrace: &Keytrace) -> Keytrace {
    let mut res = Vec::with_capacity(keytrace.len() + 1);
    res.push(k);
    res.extend(keytrace.iter().cloned());
    res
}

/// `Float.to_string` (Base's): `%.15g`, or `%.17g` if that does not read
/// back as the same float, made a valid OCaml float lexeme (`valid_float_lexem`
/// adds a period to a string of digits and signs).
fn float_to_string(x: f64) -> String {
    /// `format_float "%.<precision>g"` (C's `printf`).
    fn format_float_g(precision: usize, x: f64) -> String {
        if x.is_nan() {
            return (if x.is_sign_negative() { "-nan" } else { "nan" }).to_string();
        }
        if x.is_infinite() {
            return (if x > 0.0 { "inf" } else { "-inf" }).to_string();
        }
        let e = format!("{:.*e}", precision - 1, x);
        let (mantissa, exponent) = e.split_once('e').unwrap();
        let exponent: i32 = exponent.parse().unwrap();
        let strip_zeros = |s: &str| -> String {
            if s.contains('.') {
                s.trim_end_matches('0').trim_end_matches('.').to_string()
            } else {
                s.to_string()
            }
        };
        if -4 <= exponent && exponent < precision as i32 {
            let decimals = (precision as i32 - 1 - exponent) as usize;
            strip_zeros(&format!("{:.*}", decimals, x))
        } else {
            format!(
                "{}e{}{:02}",
                strip_zeros(mantissa),
                if exponent < 0 { '-' } else { '+' },
                exponent.abs()
            )
        }
    }
    fn valid_float_lexem(s: String) -> String {
        if s.bytes().all(|c| c.is_ascii_digit() || c == b'-') {
            s + "."
        } else {
            s
        }
    }
    valid_float_lexem({
        let y = format_float_g(15, x);
        if y.parse::<f64>() == Ok(x) {
            y
        } else {
            format_float_g(17, x)
        }
    })
}

/// Attempt to deserialize a previously-serialized type back into a type we
/// can manipulate. Note that this function accesses the global state in
/// `Decl_provider` to verify that certain type names exist.
///
/// `keytrace` defaults to `[]`.
pub fn to_locl_ty(keytrace: Option<Keytrace>, ctx: &Arc<Ctx>, json: &J) -> DeserializedResult {
    let keytrace = keytrace.unwrap_or_default();
    fn ty(ty: Ty_) -> DeserializedResult {
        Ok(mk((reason::none(), ty)))
    }
    fn aux(ctx: &Arc<Ctx>, json: &J, keytrace: &Keytrace) -> DeserializedResult {
        let (kind, kind_keytrace) = get_string("kind", (json, keytrace))?;
        match kind.as_str() {
            "this" => not_supported("Cannot deserialize 'this' type.", keytrace),
            "any" => ty(make_tany()),
            "mixed" => ty(Ty_::Toption(mk((reason::none(), Ty_::Tnonnull)))),
            "nonnull" => ty(Ty_::Tnonnull),
            "dynamic" => ty(Ty_::Tdynamic(None)),
            "label" => {
                let (name, _name_keytrace) = get_string("name", (json, keytrace))?;
                ty(Ty_::Tlabel(name))
            }
            "generic" => {
                // (see Tgeneric case of serialization logic)
                let (name, _name_keytrace) = get_string("name", (json, keytrace))?;
                ty(Ty_::Tgeneric(name))
            }
            "enum" => {
                let (name, _name_keytrace) = get_string("name", (json, keytrace))?;
                let as_ty = aux_as(ctx, json, keytrace)?;
                ty(Ty_::Tnewtype(name, vec![], as_ty))
            }
            "newtype" => {
                let (name, name_keytrace) = get_string("name", (json, keytrace))?;
                let typedef_name = match decl_provider::get_typedef(None, ctx, &name) {
                    decl_entry::T::Found(_typedef) => {
                        // We end up only needing the name of the typedef.
                        Ok(name)
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        if name == "HackSuggest" {
                            not_supported("HackSuggest types for lambdas are not supported", keytrace)
                        } else {
                            deserialization_error(
                                &("Unknown newtype: ".to_string() + &name),
                                &name_keytrace,
                            )
                        }
                    }
                }?;
                let (args, args_keytrace) = get_array("args", (json, keytrace))?;
                let args = aux_args(ctx, &args, &args_keytrace)?;
                let as_ty = aux_as(ctx, json, keytrace)?;
                ty(Ty_::Tnewtype(typedef_name, args, as_ty))
            }
            "path" => {
                let (type_json, type_keytrace) = get_obj("type", (json, keytrace))?;
                let (path_kind, path_kind_keytrace) =
                    get_string("kind", (&type_json, &type_keytrace))?;
                let (ids_array, ids_keytrace) = get_array("path", (json, keytrace))?;
                let ids = map_array(
                    &ids_array,
                    |id_str, keytrace| match id_str {
                        J::String(id) => Ok(id.clone()),
                        _ => deserialization_error("Expected a string", keytrace),
                    },
                    &ids_keytrace,
                );
                let _ids = ids?;
                match path_kind.as_str() {
                    "expr" => not_supported(
                        "Cannot deserialize path-dependent type involving an expression",
                        keytrace,
                    ),
                    "this" => {
                        let _as_ty = aux_as(ctx, json, keytrace)?;
                        ty(Ty_::Tgeneric("this".to_string()))
                    }
                    path_kind => deserialization_error(
                        &("Unknown path kind: ".to_string() + path_kind),
                        &path_kind_keytrace,
                    ),
                }
            }
            "tuple" => {
                let (args, args_keytrace) = get_array("args", (json, keytrace))?;
                let t_required = aux_args(ctx, &args, &args_keytrace)?;
                let splat_arg_obj_opt = get_obj_opt("splat_arg", (json, keytrace))?;
                match splat_arg_obj_opt {
                    Some((splat_arg_obj, keytrace)) => {
                        let t_splat = aux(ctx, &splat_arg_obj, &keytrace)?;
                        ty(Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: vec![],
                            extra: TupleExtra::Tsplat(t_splat),
                        }))
                    }
                    None => {
                        let (optional_args, optional_args_keytrace) =
                            get_array_opt("optional_args", (json, keytrace))?;
                        let t_optional = aux_args(ctx, &optional_args, &optional_args_keytrace)?;
                        let popt = get_obj_opt("variadic_arg", (json, keytrace))?;
                        let t_variadic = aux_variadic_arg(ctx, popt)?;
                        ty(Ty_::Ttuple(TupleType {
                            required: t_required,
                            optional: t_optional,
                            extra: TupleExtra::Tvariadic(t_variadic),
                        }))
                    }
                }
            }
            "nullable" => {
                let (args, keytrace) = get_array("args", (json, keytrace))?;
                match args.as_slice() {
                    [nullable_ty] => {
                        let nullable_ty = aux(ctx, nullable_ty, &cons("0".to_string(), &keytrace))?;
                        ty(Ty_::Toption(nullable_ty))
                    }
                    _ => deserialization_error(
                        &format!(
                            "Unsupported number of args for nullable type: {}",
                            args.len()
                        ),
                        &keytrace,
                    ),
                }
            }
            "primitive" => {
                let (name, keytrace) = get_string("name", (json, keytrace))?;
                let prim_ty = match name.as_str() {
                    "void" => Ok(Ty_::Tprim(Tprim::Tvoid)),
                    "null" => Ok(Ty_::Tprim(Tprim::Tnull)),
                    "int" => Ok(Ty_::Tprim(Tprim::Tint)),
                    "bool" => Ok(Ty_::Tprim(Tprim::Tbool)),
                    "float" => Ok(Ty_::Tprim(Tprim::Tfloat)),
                    "string" => {
                        let class_pos = match decl_provider::get_class(None, ctx, C_STRING) {
                            decl_entry::T::Found(class_ty) => cls::pos(&class_ty),
                            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                                // Class may not exist (such as in non-strict modes).
                                crate::pos_or_decl::none
                            }
                        };
                        Ok(Ty_::Tclass(
                            (class_pos, C_STRING.to_string()),
                            nonexact(),
                            vec![],
                        ))
                    }
                    "resource" => Ok(Ty_::Tprim(Tprim::Tresource)),
                    "num" => Ok(Ty_::Tprim(Tprim::Tnum)),
                    "arraykey" => Ok(Ty_::Tprim(Tprim::Tarraykey)),
                    "noreturn" => Ok(Ty_::Tprim(Tprim::Tnoreturn)),
                    _ => deserialization_error(
                        &("Unknown primitive type: ".to_string() + &name),
                        &keytrace,
                    ),
                }?;
                ty(prim_ty)
            }
            "class" => {
                let (name, _name_keytrace) = get_string("name", (json, keytrace))?;
                let class_pos = match decl_provider::get_class(None, ctx, &name) {
                    decl_entry::T::Found(class_ty) => cls::pos(&class_ty),
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                        // Class may not exist (such as in non-strict modes).
                        crate::pos_or_decl::none
                    }
                };
                let (args, _args_keytrace) = get_array("args", (json, keytrace))?;
                let tyl = aux_args(ctx, &args, keytrace)?;
                let refs = match get_array("refs", (json, keytrace)) {
                    Ok((l, _)) => l,
                    Err(_) => vec![],
                };
                let rs = aux_refs(ctx, &refs, keytrace)?;
                // NB: "class" could have come from either a `Tapply` or a `Tclass`.
                // Right now, we always return a `Tclass`.
                ty(Ty_::Tclass((class_pos, name), Exact::Nonexact(rs), tyl))
            }
            "shape" => {
                let (fields, fields_keytrace) = get_array("fields", (json, keytrace))?;
                let (is_array, _is_array_keytrace) = get_bool("is_array", (json, keytrace))?;
                let unserialize_field = |field_json: &J,
                                         keytrace: &Keytrace|
                 -> Result<
                    (TshapeFieldName, ShapeFieldType),
                    DeserializationError,
                > {
                    let (name, name_keytrace) = get_val("name", (field_json, keytrace))?;
                    // We don't need position information for shape field names. They're
                    // only used for error messages and the like.
                    let dummy_pos = crate::pos_or_decl::none;
                    let shape_field_name = match &name {
                        J::Int(n) => Ok(TshapeFieldName::TSFregexGroup(PosString(
                            dummy_pos.clone(),
                            n.to_string(),
                        ))),
                        J::Float(f) => Ok(TshapeFieldName::TSFregexGroup(PosString(
                            dummy_pos.clone(),
                            float_to_string(*f),
                        ))),
                        J::Intlit(s) => Ok(TshapeFieldName::TSFregexGroup(PosString(
                            dummy_pos.clone(),
                            s.clone(),
                        ))),
                        J::String(name) => Ok(TshapeFieldName::TSFlitStr(PosByteString(
                            dummy_pos.clone(),
                            name.as_str().into(),
                        ))),
                        J::List(l) => match l.as_slice() {
                            [J::String(name1), J::String(name2)] => {
                                Ok(TshapeFieldName::TSFclassConst(
                                    (dummy_pos.clone(), name1.clone()),
                                    PosString(dummy_pos.clone(), name2.clone()),
                                ))
                            }
                            _ => deserialization_error(
                                "Unexpected format for shape field name",
                                &name_keytrace,
                            ),
                        },
                        _ => deserialization_error(
                            "Unexpected format for shape field name",
                            &name_keytrace,
                        ),
                    }?;
                    // Optional field may be absent for shape-like arrays.
                    let optional = match get_val("optional", (field_json, keytrace)) {
                        Ok(_) => get_bool("optional", (field_json, keytrace))
                            .map(|(optional, _optional_keytrace)| optional),
                        Err(_) => Ok(false),
                    }?;
                    let (shape_type, shape_type_keytrace) =
                        get_obj("type", (field_json, keytrace))?;
                    let shape_field_type = aux(ctx, &shape_type, &shape_type_keytrace)?;
                    let shape_field_type = ShapeFieldType {
                        optional,
                        ty: shape_field_type,
                    };
                    Ok((shape_field_name, shape_field_type))
                };
                let fields = map_array(&fields, unserialize_field, &fields_keytrace)?;
                if is_array {
                    // We don't have enough information to perfectly reconstruct shape-like
                    // arrays. We're missing the keys in the shape map of the shape fields.
                    not_supported("Cannot deserialize shape-like array type", keytrace)
                } else {
                    let (fields_known, _fields_known_keytrace) =
                        get_bool("fields_known", (json, keytrace))?;
                    let unknown_fields_type = get_obj_opt("unknown_fields_type", (json, keytrace))?;
                    let shape_kind = match unknown_fields_type {
                        Some((unknown_fields_type, keytrace)) => {
                            aux(ctx, &unknown_fields_type, &keytrace)?
                        }
                        None => {
                            if fields_known {
                                typing_make_type::nothing(reason::none())
                            } else {
                                typing_make_type::mixed(reason::none())
                            }
                        }
                    };
                    let mut shape_map = TShapeMap::new();
                    for (k, v) in fields {
                        shape_map.insert(TShapeField(k), v);
                    }
                    ty(Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                        origin: TypeOrigin::MissingOrigin,
                        fields: shape_map,
                        unknown_value: shape_kind,
                    })))
                }
            }
            "shape_splat" => {
                let (elems, elems_keytrace) = get_array("elems", (json, keytrace))?;
                let ss_elems = aux_args(ctx, &elems, &elems_keytrace)?;
                ty(Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })))
            }
            "union" => {
                let (args, keytrace) = get_array("args", (json, keytrace))?;
                let tyl = aux_args(ctx, &args, &keytrace)?;
                ty(Ty_::Tunion(tyl))
            }
            "intersection" => {
                let (args, keytrace) = get_array("args", (json, keytrace))?;
                let tyl = aux_args(ctx, &args, &keytrace)?;
                ty(Ty_::Tintersection(tyl))
            }
            "function" => {
                let (tparams, tparams_keytrace) = get_array("tparams", (json, keytrace))?;
                let tparams = map_array(
                    &tparams,
                    |param, keytrace| {
                        let (name, _name_keytrace) = get_string("name", (param, keytrace))?;
                        // (The constraints and the user attributes are read from
                        // the function, with the key trace of the parameter.)
                        let (cstrs, keytrace) = get_array("constraints", (json, keytrace))?;
                        let tp_constraints = map_array(
                            &cstrs,
                            |cstr, keytrace| aux_constraint(ctx, cstr, keytrace),
                            &keytrace,
                        )?;
                        let (attrs, keytrace) = get_array("user_attributes", (json, &keytrace))?;
                        let tp_user_attributes = map_array(&attrs, aux_user_attribute, &keytrace)?;
                        Ok(Tparam {
                            name: (crate::pos_or_decl::none, name),
                            reified: ast_defs::ReifyKind::Erased,
                            constraints: tp_constraints,
                            user_attributes: tp_user_attributes,
                            variance: ast_defs::Variance::Invariant,
                        })
                    },
                    &tparams_keytrace,
                );
                let ft_tparams = tparams?;
                let (params, params_keytrace) = get_array("params", (json, keytrace))?;
                let params = map_array(
                    &params,
                    |param, keytrace| {
                        let (optional, _optional_keytrace) =
                            get_bool("optional", (param, keytrace))?;
                        let (callconv, callconv_keytrace) =
                            get_string("callConvention", (param, keytrace))?;
                        let callconv = match string_to_param_mode(&callconv) {
                            Some(callconv) => Ok(callconv),
                            None => deserialization_error(
                                &("Unknown calling convention: ".to_string() + &callconv),
                                &callconv_keytrace,
                            ),
                        }?;
                        let named = aux_get_bool_with_default("named", false, param, keytrace)?;
                        let fp_name = match access::get_string("name", (param, keytrace)) {
                            Ok((name, _)) => Ok(Some(name)),
                            Err(AccessFailure::MissingKeyError(..)) => Ok(None),
                            Err(access_failure) => deserialization_error(
                                &access::access_failure_to_string(&access_failure),
                                keytrace,
                            ),
                        }?;
                        let (param_type, param_type_keytrace) =
                            get_obj("type", (param, keytrace))?;
                        let param_type = aux(ctx, &param_type, &param_type_keytrace)?;
                        Ok(FunParam {
                            type_: param_type,
                            flags: make_fp_flags(
                                callconv, false, optional, false, false, false, named,
                            ),
                            pos: crate::pos_or_decl::none,
                            name: fp_name,
                            def_value: None,
                        })
                    },
                    &params_keytrace,
                );
                let ft_params = params?;
                let (result, result_keytrace) = get_obj("result", (json, keytrace))?;
                let ft_ret = aux(ctx, &result, &result_keytrace)?;
                let capability = aux_capability(ctx, json, keytrace)?;
                let readonly_this =
                    aux_get_bool_with_default("readonly_this", false, json, keytrace)?;
                let readonly_return =
                    aux_get_bool_with_default("readonly_return", false, json, keytrace)?;
                let named_variadic =
                    aux_get_bool_with_default("named_variadic", false, json, keytrace)?;
                let variadic = aux_get_bool_with_default("variadic", false, json, keytrace)?;
                let ft_instantiated =
                    aux_get_bool_with_default("instantiated", true, json, keytrace)?;
                let ft_flags = typing_defs_flags::fun::set_named_variadic(
                    named_variadic,
                    typing_defs_flags::fun::set_variadic(
                        variadic,
                        typing_defs_flags::fun::default(),
                    ),
                );
                let funty = FunType {
                    params: ft_params,
                    implicit_params: FunImplicitParams { capability },
                    ret: ft_ret,
                    tparams: ft_tparams,
                    // Dummy values: these aren't currently serialized.
                    where_constraints: vec![],
                    flags: ft_flags,
                    instantiated: ft_instantiated,
                };
                let funty = set_ft_returns_readonly(funty, readonly_return);
                let funty = set_ft_readonly_this(funty, readonly_this);
                ty(Ty_::Tfun(std::rc::Rc::new(funty)))
            }
            "nothing" => ty(Ty_::Tunion(vec![])),
            _ => deserialization_error(
                &format!(
                    "Unknown or unsupported kind '{}' to convert to locl phase",
                    kind
                ),
                &kind_keytrace,
            ),
        }
    }
    /// Every element is converted, then the first error (in the order of the
    /// array) is returned, if any (`Result.all` of `List.mapi`).
    fn map_array<A>(
        array: &[J],
        f: impl Fn(&J, &Keytrace) -> Result<A, DeserializationError>,
        keytrace: &Keytrace,
    ) -> Result<Vec<A>, DeserializationError> {
        let array: Vec<Result<A, DeserializationError>> = array
            .iter()
            .enumerate()
            .map(|(i, elem)| f(elem, &cons(i.to_string(), keytrace)))
            .collect();
        array.into_iter().collect()
    }
    fn aux_args(
        ctx: &Arc<Ctx>,
        args: &[J],
        keytrace: &Keytrace,
    ) -> Result<Vec<Ty>, DeserializationError> {
        map_array(args, |arg, keytrace| aux(ctx, arg, keytrace), keytrace)
    }
    fn aux_variadic_arg(ctx: &Arc<Ctx>, arg: Option<(J, Keytrace)>) -> DeserializedResult {
        match arg {
            None => Ok(typing_make_type::nothing(reason::none())),
            Some((ty, keytrace)) => aux(ctx, &ty, &keytrace),
        }
    }
    fn aux_refs(
        ctx: &Arc<Ctx>,
        refs: &[J],
        keytrace: &Keytrace,
    ) -> Result<ClassRefinement, DeserializationError> {
        let of_refined_consts = |consts: Vec<(String, RefinedConst)>| ClassRefinement {
            cr_consts: consts.into_iter().collect(),
        };
        map_array(refs, |r, keytrace| aux_ref(ctx, r, keytrace), keytrace).map(of_refined_consts)
    }
    fn aux_ref(
        ctx: &Arc<Ctx>,
        json: &J,
        keytrace: &Keytrace,
    ) -> Result<(String, RefinedConst), DeserializationError> {
        let (rc_is_ctx, _) = get_bool("is_ctx", (json, keytrace))?;
        let (id, _) = get_string("type", (json, keytrace))?;
        match access::get_obj("equal", (json, keytrace)) {
            Ok((ty_json, ty_keytrace)) => {
                let ty = aux(ctx, &ty_json, &ty_keytrace)?;
                Ok((
                    id,
                    RefinedConst {
                        bound: RefinedConstBound::TRexact(ty),
                        is_ctx: rc_is_ctx,
                    },
                ))
            }
            Err(AccessFailure::MissingKeyError(..)) => {
                let (los_json, los_keytrace) = get_array("lower", (json, keytrace))?;
                let (ups_json, ups_keytrace) = get_array("upper", (json, keytrace))?;
                let tr_lower = map_array(&los_json, |j, kt| aux(ctx, j, kt), &los_keytrace)?;
                let tr_upper = map_array(&ups_json, |j, kt| aux(ctx, j, kt), &ups_keytrace)?;
                Ok((
                    id,
                    RefinedConst {
                        bound: RefinedConstBound::TRloose(RefinedConstBounds {
                            lower: tr_lower,
                            upper: tr_upper,
                        }),
                        is_ctx: rc_is_ctx,
                    },
                ))
            }
            Err(e) => wrap_json_accessor(|_: ()| Err(e), ()),
        }
    }
    fn aux_as(ctx: &Arc<Ctx>, json: &J, keytrace: &Keytrace) -> DeserializedResult {
        // as-constraint is optional, check to see if it exists.
        match access::get_obj("as", (json, keytrace)) {
            Ok((as_json, as_keytrace)) => {
                let as_ty = aux(ctx, &as_json, &as_keytrace)?;
                Ok(as_ty)
            }
            Err(AccessFailure::MissingKeyError(..)) => Ok(mk((
                reason::none(),
                Ty_::Toption(mk((reason::none(), Ty_::Tnonnull))),
            ))),
            Err(access_failure) => deserialization_error(
                &("Invalid as-constraint: ".to_string()
                    + &access::access_failure_to_string(&access_failure)),
                keytrace,
            ),
        }
    }
    fn aux_capability(
        ctx: &Arc<Ctx>,
        json: &J,
        keytrace: &Keytrace,
    ) -> Result<Capability, DeserializationError> {
        match access::get_obj("capability", (json, keytrace)) {
            Ok((cap_json, cap_keytrace)) => {
                let cap_ty = aux(ctx, &cap_json, &cap_keytrace)?;
                Ok(Capability::CapTy(cap_ty))
            }
            // The "capability" key is omitted for CapDefaults during encoding
            Err(AccessFailure::MissingKeyError(..)) => {
                Ok(Capability::CapDefaults(crate::pos_or_decl::none))
            }
            Err(access_failure) => deserialization_error(
                &("Invalid capability: ".to_string()
                    + &access::access_failure_to_string(&access_failure)),
                keytrace,
            ),
        }
    }
    fn aux_get_bool_with_default(
        key: &str,
        default: bool,
        json: &J,
        keytrace: &Keytrace,
    ) -> Result<bool, DeserializationError> {
        match access::get_bool(key, (json, keytrace)) {
            Ok((value, _keytrace)) => Ok(value),
            Err(AccessFailure::MissingKeyError(..)) => Ok(default),
            Err(access_failure) => deserialization_error(
                &access::access_failure_to_string(&access_failure),
                keytrace,
            ),
        }
    }
    fn aux_constraint(
        ctx: &Arc<Ctx>,
        json: &J,
        keytrace: &Keytrace,
    ) -> Result<(ast_defs::ConstraintKind, Ty), DeserializationError> {
        let kind = get_constraint_kind("kind", (json, keytrace))?;
        let (ty_json, keytrace) = get_val("type", (json, keytrace))?;
        let ty = aux(ctx, &ty_json, &keytrace)?;
        Ok((kind, ty))
    }
    fn aux_user_attribute(
        json: &J,
        keytrace: &Keytrace,
    ) -> Result<UserAttribute, DeserializationError> {
        let (name, _keytrace) = get_string("name", (json, keytrace))?;
        Ok(UserAttribute {
            name: (crate::pos_or_decl::none, name),
            params: vec![],
            raw_val: None,
        })
    }
    aux(ctx, json, &keytrace)
}

/// `show_like_ty` defaults to `false`.
pub fn from_locl_ty(env: &Env, show_like_ty: Option<bool>, ty: &Ty) -> J {
    let show_like_ty = show_like_ty.unwrap_or(false);
    from_type(env, show_like_ty, ty)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floats_as_ocaml_prints_them() {
        assert_eq!(float_to_string(1.0), "1.");
        assert_eq!(float_to_string(-3.0), "-3.");
        assert_eq!(float_to_string(1.5), "1.5");
        assert_eq!(float_to_string(0.1), "0.1");
        assert_eq!(float_to_string(0.1 + 0.2), "0.30000000000000004");
        assert_eq!(float_to_string(1e16), "1e+16");
        assert_eq!(float_to_string(1e-5), "1e-05");
        assert_eq!(float_to_string(-0.0), "-0.");
        assert_eq!(float_to_string(f64::INFINITY), "inf");
        assert_eq!(float_to_string(f64::NEG_INFINITY), "-inf");
        assert_eq!(float_to_string(f64::NAN), "nan");
    }

    #[test]
    fn key_traces() {
        let kt = cons("0".to_string(), &vec!["args".to_string()]);
        assert_eq!(kt, vec!["0".to_string(), "args".to_string()]);
        match deserialization_error::<()>("Expected a string", &kt) {
            Err(DeserializationError::DeserializationError(msg)) => {
                assert_eq!(msg, "Expected a string (at field `args.0`)")
            }
            _ => panic!(),
        }
        match not_supported::<()>("Cannot deserialize 'this' type.", &vec![]) {
            Err(DeserializationError::NotSupported(msg)) => {
                assert_eq!(msg, "Cannot deserialize 'this' type.")
            }
            _ => panic!(),
        }
        assert_eq!(string_to_param_mode("inout"), Some(ParamMode::FPinout));
        assert_eq!(string_to_param_mode("x"), None);
        assert_eq!(param_mode_to_string(&ParamMode::FPnormal), "normal");
    }
}
