// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/service/tast_hashes.ml`, with the `[@@deriving hash]`
//! folders of the TAST that it calls (`Tast.hash_def`,
//! `Tast.hash_def_with_dynamic`) and of the types in the TAST that are not
//! the AST's (those are in [`crate::ast_hash`]): the localized types
//! (`Typing_defs_core.hash_fold_ty`, which ignores the reasons), the saved
//! environment (`Tast.hash_fold_saved_env`, which ignores the options and
//! the inference environment), `Type_parameter_env.hash_fold_t`,
//! `Typing_kinding_defs.hash_fold_kind`, `Tast_with_dynamic.hash_fold_t`.
//! See `hh/PORTING.md`.
//!
//! The folders are the ones ppx_hash writes for the OCaml types (their
//! derived code is the reference: constructor indices count every
//! constructor of the OCaml type, the decl-only ones of `ty_` included).

use crate::ast_hash;
use crate::ast_hash::H;
use crate::ast_hash::fold_bool;
use crate::ast_hash::fold_bytes;
use crate::ast_hash::fold_int;
use crate::ast_hash::fold_option;
use crate::ast_hash::fold_string;
use crate::relative_path;
use crate::tast;
use crate::tast_with_dynamic;
use crate::typing_defs_core as tdc;
use crate::yojson::safe as yojson;

/// `S_map.t` (the maps of the hashes)
type SMap<V> = std::collections::BTreeMap<String, V>;

/// The state and the folders of a TAST's annotations.
type TH = H<tast::Ty, tast::SavedEnv>;

/// `Typing_defs_core.hash_fold_ty`: the reason is ignored
/// (`[@hash.ignore]`), then the `ty_`.
fn hash_fold_ty(h: &mut TH, ty: &tast::Ty) {
    hash_fold_ty_(h, tdc::get_node(ty))
}

fn hash_fold_tys(h: &mut TH, tys: &[tast::Ty]) {
    fold_int(&mut h.s, tys.len() as i64);
    for ty in tys {
        hash_fold_ty(h, ty)
    }
}

/// `Typing_defs_core.hash_fold_pos_id` (`Reason.hash_fold_pos_id`): the
/// position is ignored, then the name.
fn hash_fold_pos_id(h: &mut TH, (_, id): &tdc::PosId) {
    fold_string(&mut h.s, id.as_bytes())
}

/// `Typing_defs_core.hash_fold_ty_`, for the constructors of `locl_phase
/// ty_` (the indices are those of the whole type: `Tthis` 0 ... `Tlabel` 25).
fn hash_fold_ty_(h: &mut TH, ty: &tdc::Ty_) {
    use tdc::Ty_::*;
    match ty {
        // `Tany_sentinel.t` is `unit`.
        Tany(_) => fold_int(&mut h.s, 6),
        Tnonnull => fold_int(&mut h.s, 7),
        Tdynamic(v) => {
            fold_int(&mut h.s, 8);
            fold_option(&mut h.s, v.as_ref(), |s, v| fold_int(s, *v as i64))
        }
        Toption(ty) => {
            fold_int(&mut h.s, 9);
            hash_fold_ty(h, ty)
        }
        Tprim(p) => {
            fold_int(&mut h.s, 10);
            ast_hash::ast_defs::hash_fold_tprim(h, p)
        }
        Tfun(ft) => {
            fold_int(&mut h.s, 11);
            hash_fold_fun_type(h, ft)
        }
        Ttuple(t) => {
            fold_int(&mut h.s, 12);
            hash_fold_tuple_type(h, t)
        }
        Tshape(s) => {
            fold_int(&mut h.s, 13);
            hash_fold_shape_type(h, s)
        }
        Tgeneric(name) => {
            fold_int(&mut h.s, 14);
            fold_string(&mut h.s, name.as_bytes())
        }
        Tunion(tys) => {
            fold_int(&mut h.s, 15);
            hash_fold_tys(h, tys)
        }
        Tintersection(tys) => {
            fold_int(&mut h.s, 16);
            hash_fold_tys(h, tys)
        }
        TvecOrDict(k, v) => {
            fold_int(&mut h.s, 17);
            hash_fold_ty(h, k);
            hash_fold_ty(h, v)
        }
        Taccess(tdc::TaccessType(ty, id)) => {
            fold_int(&mut h.s, 18);
            hash_fold_ty(h, ty);
            hash_fold_pos_id(h, id)
        }
        TclassPtr(ty) => {
            fold_int(&mut h.s, 19);
            hash_fold_ty(h, ty)
        }
        Tvar(v) => {
            fold_int(&mut h.s, 20);
            fold_int(&mut h.s, *v as i64)
        }
        Tnewtype(name, tys, bound) => {
            fold_int(&mut h.s, 21);
            fold_string(&mut h.s, name.as_bytes());
            hash_fold_tys(h, tys);
            hash_fold_ty(h, bound)
        }
        Tdependent(tdc::DependentType::DTexpr(id), ty) => {
            fold_int(&mut h.s, 22);
            // (`dependent_type` has a single constructor: no index.)
            fold_int(&mut h.s, *id as i64);
            hash_fold_ty(h, ty)
        }
        Tclass(id, exact, tys) => {
            fold_int(&mut h.s, 23);
            hash_fold_pos_id(h, id);
            match exact {
                tdc::Exact::Exact => fold_int(&mut h.s, 0),
                tdc::Exact::Nonexact(cr) => {
                    fold_int(&mut h.s, 1);
                    hash_fold_class_refinement(h, cr)
                }
            }
            hash_fold_tys(h, tys)
        }
        Tneg(p) => {
            fold_int(&mut h.s, 24);
            hash_fold_type_predicate(h, p)
        }
        Tlabel(name) => {
            fold_int(&mut h.s, 25);
            fold_string(&mut h.s, name.as_bytes())
        }
    }
}

/// `hash_fold_class_refinement`: `S_map.hash_fold_t hash_fold_refined_const`
/// of `cr_consts`.
fn hash_fold_class_refinement(h: &mut TH, cr: &tdc::ClassRefinement) {
    let consts = &cr.cr_consts;
    fold_int(&mut h.s, consts.len() as i64);
    for (name, rc) in consts.iter() {
        fold_string(&mut h.s, name.as_bytes());
        match &rc.bound {
            tdc::RefinedConstBound::TRexact(ty) => {
                fold_int(&mut h.s, 0);
                hash_fold_ty(h, ty)
            }
            tdc::RefinedConstBound::TRloose(bounds) => {
                fold_int(&mut h.s, 1);
                hash_fold_tys(h, &bounds.lower);
                hash_fold_tys(h, &bounds.upper)
            }
        }
        fold_bool(&mut h.s, rc.is_ctx)
    }
}

/// `hash_fold_tshape_field_name` (the positions are ignored)
fn hash_fold_tshape_field_name(h: &mut TH, name: &tdc::TshapeFieldName) {
    use tdc::TshapeFieldName::*;
    match name {
        TSFregexGroup(tdc::PosString(_, s)) => {
            fold_int(&mut h.s, 0);
            fold_string(&mut h.s, s.as_bytes())
        }
        TSFlitStr(tdc::PosByteString(_, s)) => {
            fold_int(&mut h.s, 1);
            fold_bytes(&mut h.s, s)
        }
        TSFclassConst(id, tdc::PosString(_, s)) => {
            fold_int(&mut h.s, 2);
            hash_fold_pos_id(h, id);
            fold_string(&mut h.s, s.as_bytes())
        }
    }
}

/// `hash_fold_shape_type`
fn hash_fold_shape_type(h: &mut TH, s: &tdc::ShapeType) {
    match s {
        tdc::ShapeType::ShapeSimple(s) => {
            fold_int(&mut h.s, 0);
            match &s.origin {
                tdc::TypeOrigin::MissingOrigin => fold_int(&mut h.s, 0),
                // (The position is ignored.)
                tdc::TypeOrigin::FromAlias(name, _) => {
                    fold_int(&mut h.s, 1);
                    fold_string(&mut h.s, name.as_bytes())
                }
            }
            hash_fold_ty(h, &s.unknown_value);
            // `TShapeMap.hash_fold_t hash_fold_shape_field_type`
            fold_int(&mut h.s, s.fields.len() as i64);
            for (name, field) in &s.fields {
                hash_fold_tshape_field_name(h, &name.0);
                fold_bool(&mut h.s, field.optional);
                hash_fold_ty(h, &field.ty)
            }
        }
        tdc::ShapeType::ShapeSplat(s) => {
            fold_int(&mut h.s, 1);
            hash_fold_tys(h, &s.ss_elems)
        }
    }
}

/// `hash_fold_tuple_type`
fn hash_fold_tuple_type(h: &mut TH, t: &tdc::TupleType) {
    hash_fold_tys(h, &t.required);
    hash_fold_tys(h, &t.optional);
    match &t.extra {
        tdc::TupleExtra::Tvariadic(ty) => {
            fold_int(&mut h.s, 0);
            hash_fold_ty(h, ty)
        }
        tdc::TupleExtra::Tsplat(ty) => {
            fold_int(&mut h.s, 1);
            hash_fold_ty(h, ty)
        }
    }
}

/// `hash_fold_type_predicate`: the reason is ignored, then the
/// `type_predicate_`.
fn hash_fold_type_predicate(h: &mut TH, tdc::TypePredicate(_, p): &tdc::TypePredicate) {
    use tdc::TypePredicate_::*;
    match p {
        IsTag(tag) => {
            fold_int(&mut h.s, 0);
            hash_fold_type_tag(h, tag)
        }
        IsTupleOf(t) => {
            fold_int(&mut h.s, 1);
            fold_int(&mut h.s, t.required.len() as i64);
            for p in &t.required {
                hash_fold_type_predicate(h, p)
            }
        }
        IsShapeOf(sp) => {
            fold_int(&mut h.s, 2);
            fold_bool(&mut h.s, sp.allows_unknown_fields);
            fold_int(&mut h.s, sp.fields.len() as i64);
            for (name, field) in &sp.fields {
                hash_fold_tshape_field_name(h, &name.0);
                fold_bool(&mut h.s, field.optional);
                hash_fold_type_predicate(h, &field.predicate)
            }
        }
        IsUnionOf(ps) => {
            fold_int(&mut h.s, 3);
            fold_int(&mut h.s, ps.len() as i64);
            for p in ps {
                hash_fold_type_predicate(h, p)
            }
        }
        IsNot(p) => {
            fold_int(&mut h.s, 4);
            hash_fold_type_predicate(h, p)
        }
    }
}

/// `hash_fold_type_tag`
fn hash_fold_type_tag(h: &mut TH, tag: &tdc::TypeTag) {
    use tdc::TypeTag::*;
    match tag {
        BoolTag => fold_int(&mut h.s, 0),
        IntTag => fold_int(&mut h.s, 1),
        ArraykeyTag => fold_int(&mut h.s, 2),
        FloatTag => fold_int(&mut h.s, 3),
        NumTag => fold_int(&mut h.s, 4),
        ResourceTag => fold_int(&mut h.s, 5),
        NullTag => fold_int(&mut h.s, 6),
        ClassTag(id, generics) => {
            fold_int(&mut h.s, 7);
            fold_string(&mut h.s, id.as_bytes());
            fold_int(&mut h.s, generics.len() as i64);
            for g in generics {
                match g {
                    tdc::TypeTagGeneric::Filled(ty) => {
                        fold_int(&mut h.s, 0);
                        hash_fold_ty(h, ty)
                    }
                    tdc::TypeTagGeneric::Wildcard(i) => {
                        fold_int(&mut h.s, 1);
                        fold_int(&mut h.s, *i as i64)
                    }
                }
            }
        }
        EnumTag(id) => {
            fold_int(&mut h.s, 8);
            fold_string(&mut h.s, id.as_bytes())
        }
        GenericTag { name, from_like } => {
            fold_int(&mut h.s, 9);
            fold_string(&mut h.s, name.as_bytes());
            fold_bool(&mut h.s, *from_like)
        }
    }
}

/// `hash_fold_user_attribute`
fn hash_fold_user_attribute(h: &mut TH, ua: &tdc::UserAttribute) {
    hash_fold_pos_id(h, &ua.name);
    fold_int(&mut h.s, ua.params.len() as i64);
    for p in &ua.params {
        use tdc::UserAttributeParam::*;
        match p {
            Classname(s) => {
                fold_int(&mut h.s, 0);
                fold_string(&mut h.s, s.as_bytes())
            }
            EnumClassLabel(s) => {
                fold_int(&mut h.s, 1);
                fold_string(&mut h.s, s.as_bytes())
            }
            String(s) => {
                fold_int(&mut h.s, 2);
                fold_bytes(&mut h.s, s)
            }
            Int(s) => {
                fold_int(&mut h.s, 3);
                fold_string(&mut h.s, s.as_bytes())
            }
        }
    }
    fold_option(&mut h.s, ua.raw_val.as_ref(), |s, v| {
        fold_string(s, v.as_bytes())
    })
}

/// `hash_fold_fun_type (hash_fold_ty locl_phase)`
fn hash_fold_fun_type(h: &mut TH, ft: &tdc::FunType) {
    // `ft_tparams`: `hash_fold_tparam`
    fold_int(&mut h.s, ft.tparams.len() as i64);
    for tp in &ft.tparams {
        ast_hash::ast_defs::hash_fold_variance(h, &tp.variance);
        hash_fold_pos_id(h, &tp.name);
        fold_int(&mut h.s, tp.constraints.len() as i64);
        for (kind, ty) in &tp.constraints {
            ast_hash::ast_defs::hash_fold_constraint_kind(h, kind);
            hash_fold_ty(h, ty)
        }
        ast_hash::ast_defs::hash_fold_reify_kind(h, &tp.reified);
        fold_int(&mut h.s, tp.user_attributes.len() as i64);
        for ua in &tp.user_attributes {
            hash_fold_user_attribute(h, ua)
        }
    }
    // `ft_where_constraints`: `hash_fold_where_constraint`
    fold_int(&mut h.s, ft.where_constraints.len() as i64);
    for tdc::WhereConstraint(a, kind, b) in &ft.where_constraints {
        hash_fold_ty(h, a);
        ast_hash::ast_defs::hash_fold_constraint_kind(h, kind);
        hash_fold_ty(h, b)
    }
    // `ft_params`: `hash_fold_fun_param` (the position is ignored)
    fold_int(&mut h.s, ft.params.len() as i64);
    for fp in &ft.params {
        fold_option(&mut h.s, fp.name.as_ref(), |s, n| {
            fold_string(s, n.as_bytes())
        });
        hash_fold_ty(h, &fp.type_);
        fold_int(&mut h.s, fp.flags.bits() as i64);
        fold_option(&mut h.s, fp.def_value.as_ref(), |s, v| {
            fold_string(s, v.as_bytes())
        });
    }
    // `ft_implicit_params`: `hash_fold_capability` (the position of
    // `CapDefaults` is ignored)
    match &ft.implicit_params.capability {
        tdc::Capability::CapDefaults(_) => fold_int(&mut h.s, 0),
        tdc::Capability::CapTy(ty) => {
            fold_int(&mut h.s, 1);
            hash_fold_ty(h, ty)
        }
    }
    hash_fold_ty(h, &ft.ret);
    fold_int(&mut h.s, ft.flags.bits() as i64);
    fold_bool(&mut h.s, ft.instantiated)
}

/// `Typing_kinding_defs.hash_fold_kind`
fn hash_fold_kind(h: &mut TH, kind: &crate::typing_kinding_defs::Kind) {
    // `TySet.hash_fold_t`: the elements, sorted by `Ty_.compare` (the order
    // of the set).
    for bounds in [&kind.lower_bounds, &kind.upper_bounds] {
        fold_int(&mut h.s, bounds.len() as i64);
        for ty in bounds.iter() {
            hash_fold_ty(h, ty)
        }
    }
    ast_hash::aast_defs::hash_fold_reify_kind(h, &kind.reified);
    fold_bool(&mut h.s, kind.enforceable);
    fold_bool(&mut h.s, kind.newable);
    fold_bool(&mut h.s, kind.require_dynamic);
    fold_int(&mut h.s, kind.rank as i64)
}

/// `Tast.hash_fold_saved_env`: `tcopt` and `inference_env` are ignored.
fn hash_fold_saved_env(h: &mut TH, env: &tast::SavedEnv) {
    // `Type_parameter_env.hash_fold_t`: the type parameters (their
    // positions ignored), then `consistent`.
    let tparams = crate::type_parameter_env::get_tparams(&env.tpenv);
    fold_int(&mut h.s, tparams.len() as i64);
    for (name, (_, kind)) in &tparams {
        fold_string(&mut h.s, name.as_bytes());
        hash_fold_kind(h, kind)
    }
    fold_bool(
        &mut h.s,
        crate::type_parameter_env::is_consistent(&env.tpenv),
    );
    // `hash_fold_option hash_fold_fun_tast_info`
    match &env.fun_tast_info {
        None => fold_int(&mut h.s, 0),
        Some(info) => {
            fold_int(&mut h.s, 1);
            fold_bool(&mut h.s, info.has_implicit_return);
            fold_bool(&mut h.s, info.has_readonly);
            fold_int(&mut h.s, info.dynamic_locals.len() as i64);
            for dl in &info.dynamic_locals {
                fold_string(&mut h.s, dl.name.as_bytes());
                ast_hash::fold_pos(&mut h.s, &dl.pos);
                fold_int(&mut h.s, dl.shadow_tvid as i64)
            }
        }
    }
    ast_hash::aast_defs::hash_fold_check_status(h, &env.checked)
}

fn new_state() -> TH {
    H::create(hash_fold_ty, hash_fold_saved_env)
}

/// `Tast.hash_def`
pub fn hash_def(def: &tast::Def) -> isize {
    let mut h = new_state();
    ast_hash::aast_defs::hash_fold_def(&mut h, def);
    ast_hash::get_hash_value(h.s)
}

/// `Tast.hash_def_with_dynamic` (`Tast_with_dynamic.hash_fold_t
/// hash_fold_def`)
pub fn hash_def_with_dynamic(def: &tast_with_dynamic::T<tast::Def>) -> isize {
    let mut h = new_state();
    ast_hash::aast_defs::hash_fold_def(&mut h, &def.under_normal_assumptions);
    match &def.under_dynamic_assumptions {
        None => fold_int(&mut h.s, 0),
        Some(def) => {
            fold_int(&mut h.s, 1);
            ast_hash::aast_defs::hash_fold_def(&mut h, def)
        }
    }
    ast_hash::get_hash_value(h.s)
}

/// `Diagnostics.hash_diagnostic` (`[@@deriving hash]` of `(Pos.t,
/// (Pos_or_decl.t [@hash.ignore])) User_diagnostic.t`): the severity (its
/// `is_trusted` ignored), the code, the claim, the reasons (their positions
/// ignored), the custom messages, `is_fixmed` and the function's position;
/// the explanation and the quickfixes are ignored.
fn hash_diagnostic(d: &crate::diagnostics::Diagnostic) -> isize {
    let mut s = 0;
    fold_int(
        &mut s,
        match d.severity {
            crate::user_diagnostic::Severity::Warning { .. } => 0,
            crate::user_diagnostic::Severity::Err => 1,
        },
    );
    fold_int(&mut s, d.code as i64);
    // `Message.hash_fold_t`: the pair.
    ast_hash::fold_pos(&mut s, &d.claim.0);
    fold_bytes(&mut s, &d.claim.1);
    fold_int(&mut s, d.reasons.len() as i64);
    for reason in &d.reasons {
        fold_bytes(&mut s, &reason.1)
    }
    fold_int(&mut s, d.custom_msgs.len() as i64);
    for msg in &d.custom_msgs {
        fold_string(&mut s, msg.as_bytes())
    }
    fold_bool(&mut s, d.is_fixmed);
    fold_option(&mut s, d.function_pos.as_ref(), ast_hash::fold_pos);
    ast_hash::get_hash_value(s)
}

/// `type hash = Hash.hash_value`
pub type Hash = isize;

/// `by_names`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ByNames {
    pub fun_tast_hashes: SMap<Hash>,
    pub class_tast_hashes: SMap<Hash>,
    pub typedef_tast_hashes: SMap<Hash>,
    pub gconst_tast_hashes: SMap<Hash>,
    pub module_tast_hashes: SMap<Hash>,
}

/// `file_info`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct FileInfo {
    pub tast_hashes: ByNames,
    pub error_hashes: std::collections::BTreeSet<isize>,
}

/// `t`
pub type T = relative_path::map::T<FileInfo>;

/// `yojson_of_by_names` (`[@yojson_drop_if S_map.is_empty]` on each field)
pub fn yojson_of_by_names(x: &ByNames) -> yojson::T {
    let mut fields = vec![];
    for (key, map) in [
        ("fun_tast_hashes", &x.fun_tast_hashes),
        ("class_tast_hashes", &x.class_tast_hashes),
        ("typedef_tast_hashes", &x.typedef_tast_hashes),
        ("gconst_tast_hashes", &x.gconst_tast_hashes),
        ("module_tast_hashes", &x.module_tast_hashes),
    ] {
        if !map.is_empty() {
            fields.push((
                key.to_string(),
                yojson::T::Assoc(
                    map.iter()
                        .map(|(k, v)| (k.clone(), yojson::T::Int(*v)))
                        .collect(),
                ),
            ))
        }
    }
    yojson::T::Assoc(fields)
}

/// `yojson_of_file_info`
fn yojson_of_file_info(x: &FileInfo) -> yojson::T {
    yojson::T::Assoc(vec![
        (
            "tast_hashes".to_string(),
            yojson_of_by_names(&x.tast_hashes),
        ),
        (
            "error_hashes".to_string(),
            yojson::T::List(x.error_hashes.iter().map(|h| yojson::T::Int(*h)).collect()),
        ),
    ])
}

/// `yojson_of_t` (`Relative_path.Map.yojson_of_t`: the suffixes as keys)
pub fn yojson_of_t(x: &T) -> yojson::T {
    yojson::T::Assoc(
        x.iter()
            .map(|(path, info)| {
                (
                    relative_path::suffix(path).to_string(),
                    yojson_of_file_info(info),
                )
            })
            .collect(),
    )
}

/// `hash_tasts`
pub fn hash_tasts(tasts: &tast::ByNames) -> ByNames {
    ByNames {
        fun_tast_hashes: tasts
            .fun_tasts
            .iter()
            .map(|(k, v)| (k.clone(), hash_def_with_dynamic(v)))
            .collect(),
        class_tast_hashes: tasts
            .class_tasts
            .iter()
            .map(|(k, v)| (k.clone(), hash_def_with_dynamic(v)))
            .collect(),
        typedef_tast_hashes: tasts
            .typedef_tasts
            .iter()
            .map(|(k, v)| (k.clone(), hash_def(v)))
            .collect(),
        gconst_tast_hashes: tasts
            .gconst_tasts
            .iter()
            .map(|(k, v)| (k.clone(), hash_def(v)))
            .collect(),
        module_tast_hashes: tasts
            .module_tasts
            .iter()
            .map(|(k, v)| (k.clone(), hash_def(v)))
            .collect(),
    }
}

fn union_by_names(x: ByNames, y: ByNames) -> ByNames {
    // `S_map.union` keeps the binding of the first map.
    fn union(mut x: SMap<Hash>, y: SMap<Hash>) -> SMap<Hash> {
        for (k, v) in y {
            x.entry(k).or_insert(v);
        }
        x
    }
    ByNames {
        fun_tast_hashes: union(x.fun_tast_hashes, y.fun_tast_hashes),
        class_tast_hashes: union(x.class_tast_hashes, y.class_tast_hashes),
        typedef_tast_hashes: union(x.typedef_tast_hashes, y.typedef_tast_hashes),
        gconst_tast_hashes: union(x.gconst_tast_hashes, y.gconst_tast_hashes),
        module_tast_hashes: union(x.module_tast_hashes, y.module_tast_hashes),
    }
}

fn union_file_info(x: FileInfo, y: FileInfo) -> FileInfo {
    let mut error_hashes = x.error_hashes;
    error_hashes.extend(y.error_hashes);
    FileInfo {
        tast_hashes: union_by_names(x.tast_hashes, y.tast_hashes),
        error_hashes,
    }
}

/// `is_enabled tcopt`
pub fn is_enabled(tcopt: &crate::typechecker_options::TypecheckerOptions) -> bool {
    tcopt.dump_tast_hashes
}

/// `map ctx path tasts errors`: the hashes of the definitions of `path`,
/// after `Tast_expand.expand_def`, and of its diagnostics that are not
/// fixmed (`Diagnostics.hash_diagnostic`).
///
/// (The OCaml gives up after 10 s, `Timeout.with_timeout`, and then gives
/// every definition the hash -1, `error_while_hashing`: here the hashing
/// always finishes.)
pub fn map(
    ctx: &crate::provider_context::T,
    path: &relative_path::T,
    tasts: &tast::ByNames,
    errors: &crate::diagnostics::T,
) -> T {
    let tasts = tast::map_by_names(tasts.clone(), |def| {
        crate::tast_expand::expand_def(ctx, def)
    });
    let tast_hashes = hash_tasts(&tasts);
    let error_hashes = crate::diagnostics::get_file_diagnostics(Some(true), errors, path)
        .iter()
        .map(hash_diagnostic)
        .collect();
    let mut t = T::new();
    t.insert(
        path.clone(),
        FileInfo {
            tast_hashes,
            error_hashes,
        },
    );
    t
}

/// `reduce`
pub fn reduce(xs: T, ys: T) -> T {
    let mut xs = xs;
    for (k, y) in ys {
        let v = match xs.remove(&k) {
            Some(x) => union_file_info(x, y),
            None => y,
        };
        xs.insert(k, v);
    }
    xs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_drops_empty_maps() {
        let mut by_names = ByNames::default();
        by_names
            .class_tast_hashes
            .insert("\\A".to_string(), 499090279);
        assert_eq!(
            yojson::to_string(&yojson_of_by_names(&by_names)),
            r#"{"class_tast_hashes":{"\\A":499090279}}"#
        );
    }
}
