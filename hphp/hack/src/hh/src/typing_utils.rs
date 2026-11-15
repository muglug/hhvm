// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_utils.ml`. See `hh/PORTING.md`.
//!
//! # The references
//!
//! OCaml reaches the functions of the modules that depend on this one
//! (`Typing_subtype`, `Typing_union`, `Typing_intersection`, `Typing_phase`,
//! `Typing_taccess`, `Typing_shape_normalize`) through references
//! (`sub_type_ref`, ...), which those modules set when they are initialised.
//! Here each reference is a `static <NAME>_REF: fn ...`, as
//! `crate::typing_env::SIMPLIFY_UNIONS_REF`: Rust has no module
//! initialisation, so the reference is the function that the initialisation
//! of its module puts in it (`set_fun_refs` in `crate::typing_subtype`,
//! which only ever assigns those same functions). Nothing assigns them
//! another one, so they are immutable: reading one writes no shared memory
//! (a lock would make each read an atomic write to a cache line shared by
//! all the threads, on the hottest paths). The function of the
//! same name without `_ref` reads the reference and calls what it holds, as
//! in OCaml.
//!
//! # Shadowed definitions
//!
//! The OCaml defines `has_ancestor_including_req`,
//! `has_ancestor_including_req_refl` and `is_supportdyn` twice: a recursive
//! one with `~visited` arguments, then the one of the `.mli`, which applies
//! the first to empty sets. The first ones (and `is_supportdyn_i`, which is
//! recursive with `is_supportdyn`) are in the private module [`with_visited`].

use std::collections::BTreeMap;
use std::collections::VecDeque;

use naming_special_names_rust as sn;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::Tprim;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::user_diagnostic::Severity;
use pos::BPos;
use pos::Positioned;
use pos::Symbol;
use pos::TypeName;
use ty::decl::ty as d;
use ty::reason::Reason as _;
use ty::reason::ReasonImpl;
use ty::reason::WitnessDecl;

use crate::ast_defs;
use crate::ctx::R;
use crate::decl_entry;
use crate::diagnostics;
use crate::folded_class as cls;
/// `module ITySet = Internal_type_set`
use crate::internal_type_set as ity_set;
use crate::naming_special_names::capabilities::PREFIX as CAPABILITIES_PREFIX;
use crate::naming_special_names::classes::C_FUNCTION_REF;
use crate::naming_special_names::coeffects;
use crate::tvid;
use crate::type_expansions;
use crate::type_visitor::DeclTypeVisitor;
use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs;
use crate::typing_defs::ExpandEnv;
use crate::typing_defs::TypedefCaseTypeVariant;
use crate::typing_defs::dependent_kind;
use crate::typing_defs::empty_expand_env;
use crate::typing_defs::is_prim;
use crate::typing_defs::is_union_or_inter_type;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core::DeclTy;
use crate::typing_defs_core::Enforcement;
use crate::typing_defs_core::FunParam;
use crate::typing_defs_core::FunType;
use crate::typing_defs_core::ParamMode;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::TupleExtra;
use crate::typing_defs_core::TupleType;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_ft_support_dynamic_type;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::make_fp_flags;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::ty_equal;
use crate::typing_defs_core::with_reason;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_inference_env;
/// `module MakeType = Typing_make_type`
use crate::typing_make_type as make_type;
/// `module Reason = Typing_reason`
use crate::typing_reason;
use crate::typing_reason::T as Reason;
/// `module TySet = Typing_set`
use crate::typing_set as ty_set;

/// `S_set.t`
type SSet = im::OrdSet<String>;

/// `Typing_inference_env.on_tyvar`-style callbacks of `simplify_unions` and
/// `simplify_intersections`: `env -> Reason.t -> Tvid.t -> env * locl_ty`.
pub type OnTyvar<'a> = &'a mut dyn FnMut(&mut Env, Reason, tvid::T) -> Ty;

// ---------------------------------------------------------------------------
// Importing what is necessary
// ---------------------------------------------------------------------------

/// What OCaml puts in the references below until the module that defines
/// their function sets them. The references here start with that function
/// (see the module documentation), so this is never called.
#[allow(dead_code)]
fn not_implemented(s: &str) -> ! {
    panic!("Function {} not implemented", s)
}

/// `type sub_type`
pub type SubType = fn(
    &mut Env,
    Option<bool>, // is_dynamic_aware
    Option<bool>, // is_coeffect
    Option<bool>, // ignore_readonly
    Option<bool>, // class_sub_classname
    Ty,
    Ty,
    Option<reasons_callback::T>,
) -> Option<typing_error::T>;

/// What `Typing_subtype.set_fun_refs` puts in it: `Typing_subtype.sub_type`.
pub static SUB_TYPE_REF: SubType = crate::typing_subtype::sub_type;

pub fn sub_type(
    env: &mut Env,
    is_dynamic_aware: Option<bool>,
    is_coeffect: Option<bool>,
    ignore_readonly: Option<bool>,
    class_sub_classname: Option<bool>,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let f: SubType = SUB_TYPE_REF;
    f(
        env,
        is_dynamic_aware,
        is_coeffect,
        ignore_readonly,
        class_sub_classname,
        ty_sub,
        ty_super,
        on_error,
    )
}

/// `type expected_subtyping_result`. The environment of `Subtyping_result` is
/// the one the function leaves in `*env`; with `Ambiguous_shape_splat`, which
/// has none, the function leaves the environment it was given.
#[derive(Clone, Debug)]
pub enum ExpectedSubtypingResult {
    /// The ordinary result of asserting the subtype relation.
    SubtypingResult(Option<typing_error::T>),
    /// The normalized subtype contains multiple unresolved subtype-side
    /// shape spreads whose contributions cannot be constrained independently.
    AmbiguousShapeSplat(tvid::set::T),
}

/// `type sub_type_against_expected_type`
pub type SubTypeAgainstExpectedType = fn(
    &mut Env,
    Option<bool>, // is_dynamic_aware
    Option<bool>, // ignore_readonly
    Ty,
    Ty,
    Option<reasons_callback::T>,
) -> ExpectedSubtypingResult;

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.sub_type_against_expected_type`.
pub static SUB_TYPE_AGAINST_EXPECTED_TYPE_REF: SubTypeAgainstExpectedType =
    crate::typing_subtype::sub_type_against_expected_type;

pub fn sub_type_against_expected_type(
    env: &mut Env,
    is_dynamic_aware: Option<bool>,
    ignore_readonly: Option<bool>,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) -> ExpectedSubtypingResult {
    let f: SubTypeAgainstExpectedType = SUB_TYPE_AGAINST_EXPECTED_TYPE_REF;
    f(env, is_dynamic_aware, ignore_readonly, ty_sub, ty_super, on_error)
}

/// `type sub_type_i`
pub type SubTypeI = fn(
    &mut Env,
    Option<bool>, // is_coeffect
    Option<bool>, // class_sub_classname
    InternalType,
    InternalType,
    Option<reasons_callback::T>,
) -> Option<typing_error::T>;

/// What `Typing_subtype.set_fun_refs` puts in it: `Typing_subtype.sub_type_i`.
pub static SUB_TYPE_I_REF: SubTypeI = crate::typing_subtype::sub_type_i;

pub fn sub_type_i(
    env: &mut Env,
    is_coeffect: Option<bool>,
    class_sub_classname: Option<bool>,
    ty_sub: InternalType,
    ty_super: InternalType,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let is_coeffect = is_coeffect.unwrap_or(false);
    let f: SubTypeI = SUB_TYPE_I_REF;
    f(
        env,
        Some(is_coeffect),
        class_sub_classname,
        ty_sub,
        ty_super,
        on_error,
    )
}

/// `type is_sub_type_type`
pub type IsSubTypeType = fn(&Env, &Ty, &Ty) -> bool;

/// `type is_sub_type_opt_type`
pub type IsSubTypeOptType = fn(&Env, &Ty, &Ty) -> Option<bool>;

/// What `Typing_subtype.set_fun_refs` puts in it: `Typing_subtype.is_sub_type`.
pub static IS_SUB_TYPE_REF: IsSubTypeType = crate::typing_subtype::is_sub_type;

pub fn is_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let f: IsSubTypeType = IS_SUB_TYPE_REF;
    f(env, ty1, ty2)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.is_sub_type_for_union`.
pub static IS_SUB_TYPE_FOR_UNION_REF: fn(&Env, &Ty, &Ty) -> bool =
    crate::typing_subtype::is_sub_type_for_union;

pub fn is_sub_type_for_union(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let f: fn(&Env, &Ty, &Ty) -> bool = IS_SUB_TYPE_FOR_UNION_REF;
    f(env, ty1, ty2)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.is_sub_type_for_union_i`.
pub static IS_SUB_TYPE_FOR_UNION_I_REF: fn(&Env, &InternalType, &InternalType) -> bool =
    crate::typing_subtype::is_sub_type_for_union_i;

pub fn is_sub_type_for_union_i(env: &Env, ty1: &InternalType, ty2: &InternalType) -> bool {
    let f: fn(&Env, &InternalType, &InternalType) -> bool =
        IS_SUB_TYPE_FOR_UNION_I_REF;
    f(env, ty1, ty2)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.is_type_disjoint`.
pub static IS_TYPE_DISJOINT_REF: fn(&Env, &Ty, &Ty) -> bool =
    crate::typing_subtype::is_type_disjoint;

pub fn is_type_disjoint(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let f: fn(&Env, &Ty, &Ty) -> bool = IS_TYPE_DISJOINT_REF;
    f(env, ty1, ty2)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.is_sub_type_ignore_generic_params`.
pub static IS_SUB_TYPE_IGNORE_GENERIC_PARAMS_REF: IsSubTypeType =
    crate::typing_subtype::is_sub_type_ignore_generic_params;

pub fn is_sub_type_ignore_generic_params(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let f: IsSubTypeType = IS_SUB_TYPE_IGNORE_GENERIC_PARAMS_REF;
    f(env, ty1, ty2)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.is_sub_type_opt_ignore_generic_params`.
pub static IS_SUB_TYPE_OPT_IGNORE_GENERIC_PARAMS_REF: IsSubTypeOptType =
    crate::typing_subtype::is_sub_type_opt_ignore_generic_params;

pub fn is_sub_type_opt_ignore_generic_params(env: &Env, ty1: &Ty, ty2: &Ty) -> Option<bool> {
    let f: IsSubTypeOptType = IS_SUB_TYPE_OPT_IGNORE_GENERIC_PARAMS_REF;
    f(env, ty1, ty2)
}

/// `type add_constraint`
pub type AddConstraint =
    fn(&mut Env, ConstraintKind, Ty, Ty, Option<reasons_callback::T>);

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.add_constraint`.
pub static ADD_CONSTRAINT_REF: AddConstraint = crate::typing_subtype::add_constraint;

pub fn add_constraint(
    env: &mut Env,
    ck: ConstraintKind,
    ty_sub: Ty,
    ty_super: Ty,
    on_error: Option<reasons_callback::T>,
) {
    let f: AddConstraint = ADD_CONSTRAINT_REF;
    f(env, ck, ty_sub, ty_super, on_error)
}

/// What `Typing_subtype.set_fun_refs` puts in it:
/// `Typing_subtype.can_sub_type`.
pub static CAN_SUB_TYPE_REF: IsSubTypeType = crate::typing_subtype::can_sub_type;

pub fn can_sub_type(env: &Env, ty1: &Ty, ty2: &Ty) -> bool {
    let f: IsSubTypeType = CAN_SUB_TYPE_REF;
    f(env, ty1, ty2)
}

/// `type expand_typeconst`. As in `crate::typing_taccess`, the
/// `((env, ty_err_opt, cycles), ty)` of OCaml is `(ty_err_opt, cycles, ty)`.
pub type ExpandTypeconst = fn(
    &ExpandEnv,
    &mut Env,
    Option<bool>,        // ignore_errors
    Option<Option<Pos>>, // as_tyvar_with_cnstr
    Ty,
    PosId,
    bool, // allow_abstract_tconst
) -> (
    Option<typing_error::T>,
    Vec<type_expansions::CycleReporter>,
    Ty,
);

/// What the last line of `typing_taccess.ml` puts in it:
/// `Typing_taccess.expand_with_env`.
pub static EXPAND_TYPECONST_REF: ExpandTypeconst = crate::typing_taccess::expand_with_env;

/// Expands a type constant access like A::T to its definition.
pub fn expand_typeconst(
    ety_env: &ExpandEnv,
    env: &mut Env,
    ignore_errors: Option<bool>,
    as_tyvar_with_cnstr: Option<Option<Pos>>,
    ty: Ty,
    tconstid: PosId,
    allow_abstract_tconst: bool,
) -> (
    Option<typing_error::T>,
    Vec<type_expansions::CycleReporter>,
    Ty,
) {
    let f: ExpandTypeconst = EXPAND_TYPECONST_REF;
    f(
        ety_env,
        env,
        ignore_errors,
        as_tyvar_with_cnstr,
        ty,
        tconstid,
        allow_abstract_tconst,
    )
}

/// `type union`
pub type Union = fn(
    &mut Env,
    Option<Reason>, // reason
    Option<bool>,   // approx_cancel_neg
    Ty,
    Ty,
) -> Ty;

/// What `typing_union.ml` puts in it: `Typing_union.union`.
pub static UNION_REF: Union = crate::typing_union::union;

pub fn union(
    env: &mut Env,
    reason: Option<Reason>,
    approx_cancel_neg: Option<bool>,
    ty1: Ty,
    ty2: Ty,
) -> Ty {
    let f: Union = UNION_REF;
    f(env, reason, approx_cancel_neg, ty1, ty2)
}

/// `type make_union`
pub type MakeUnion = fn(&mut Env, Reason, &[Ty], Option<Reason>, Option<Reason>) -> Ty;

/// What `typing_union.ml` puts in it: `Typing_union.make_union`.
pub static MAKE_UNION_REF: MakeUnion = crate::typing_union::make_union;

pub fn make_union(
    env: &mut Env,
    r: Reason,
    tyl: &[Ty],
    reason_nullable_opt: Option<Reason>,
    reason_dyn_opt: Option<Reason>,
) -> Ty {
    let f: MakeUnion = MAKE_UNION_REF;
    f(env, r, tyl, reason_nullable_opt, reason_dyn_opt)
}

/// `type union_list`
pub type UnionList = fn(&mut Env, Option<bool>, Reason, &[Ty]) -> Ty;

/// What `typing_union.ml` puts in it: `Typing_union.union_list`.
pub static UNION_LIST_REF: UnionList = crate::typing_union::union_list;

pub fn union_list(env: &mut Env, approx_cancel_neg: Option<bool>, r: Reason, tyl: &[Ty]) -> Ty {
    let f: UnionList = UNION_LIST_REF;
    f(env, approx_cancel_neg, r, tyl)
}

/// `type normalize_shape_type_result`
#[derive(Clone, Debug)]
pub enum NormalizeShapeTypeResult {
    NormalizedShape(ShapeType),
    NormalizedBottom,
    NormalizedDistributed,
}

/// `type normalize_shape_type`
pub type NormalizeShapeType = fn(&mut Env, Reason, ShapeType) -> NormalizeShapeTypeResult;

/// What `typing_shape_normalize.ml` puts in it when it is initialised.
/// Errors are dropped (`~on_error:None`) since refinement is not the place to
/// report shape well-formedness.
fn typing_shape_normalize_normalize_shape_type(
    env: &mut Env,
    reason: Reason,
    shape_ty: ShapeType,
) -> NormalizeShapeTypeResult {
    use crate::typing_shape_normalize::NormalizeResult;
    let (_err, res) =
        crate::typing_shape_normalize::normalize_shape_type(None, reason, shape_ty, env);
    match res {
        NormalizeResult::NormalizedShape(shape) => NormalizeShapeTypeResult::NormalizedShape(shape),
        NormalizeResult::NormalizedBottom => NormalizeShapeTypeResult::NormalizedBottom,
        NormalizeResult::NormalizedUnion(_) | NormalizeResult::NormalizedIntersection(_) => {
            NormalizeShapeTypeResult::NormalizedDistributed
        }
    }
}

/// Normalize a shape type (rightmost-wins merge of its splat elements).
/// [`NormalizeShapeTypeResult::NormalizedDistributed`] means union or
/// intersection distribution did not produce a single shape, so callers must
/// handle the input conservatively. Implemented in `Typing_shape_normalize`
/// and exposed here via a ref to break the module cycle
/// (`Typing_shape_normalize` depends transitively on `Typing_refinement`).
pub static NORMALIZE_SHAPE_TYPE_REF: NormalizeShapeType =
    typing_shape_normalize_normalize_shape_type;

pub fn normalize_shape_type(
    env: &mut Env,
    r: Reason,
    shape_ty: ShapeType,
) -> NormalizeShapeTypeResult {
    let f: NormalizeShapeType = NORMALIZE_SHAPE_TYPE_REF;
    f(env, r, shape_ty)
}

/// `type fold_union`
pub type FoldUnion = fn(&mut Env, Option<bool>, Reason, &[Ty]) -> Ty;

/// What `typing_union.ml` puts in it: `Typing_union.fold_union`.
pub static FOLD_UNION_REF: FoldUnion = crate::typing_union::fold_union;

/// `type simplify_unions`
pub type SimplifyUnions = fn(&mut Env, Option<bool>, Option<OnTyvar<'_>>, Ty) -> Ty;

/// What `typing_union.ml` puts in it: `Typing_union.simplify_unions`.
pub static SIMPLIFY_UNIONS_REF: SimplifyUnions = crate::typing_union::simplify_unions;

pub fn simplify_unions(
    env: &mut Env,
    approx_cancel_neg: Option<bool>,
    on_tyvar: Option<OnTyvar<'_>>,
    ty: Ty,
) -> Ty {
    let f: SimplifyUnions = SIMPLIFY_UNIONS_REF;
    f(env, approx_cancel_neg, on_tyvar, ty)
}

/// `type intersect_list`
pub type IntersectList = fn(&mut Env, Reason, &[Ty]) -> Ty;

/// What `typing_intersection.ml` puts in it:
/// `Typing_intersection.intersect_list`.
pub static INTERSECT_LIST_REF: IntersectList = crate::typing_intersection::intersect_list;

pub fn intersect_list(env: &mut Env, r: Reason, tyl: &[Ty]) -> Ty {
    let f: IntersectList = INTERSECT_LIST_REF;
    f(env, r, tyl)
}

/// `type approx`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Approx {
    ApproxUp,
    ApproxDown,
}

/// `[@@deriving eq]`
pub fn equal_approx(a: Approx, b: Approx) -> bool {
    a == b
}

/// `type negate_type`
pub type NegateType = fn(&mut Env, Reason, &Ty, Approx) -> Ty;

/// What `typing_intersection.ml` puts in it:
/// `Typing_intersection.negate_type`.
pub static NEGATE_TYPE_REF: NegateType = crate::typing_intersection::negate_type;

pub fn negate_type(env: &mut Env, r: Reason, ty: &Ty, approx: Approx) -> Ty {
    let f: NegateType = NEGATE_TYPE_REF;
    f(env, r, ty, approx)
}

/// `type simplify_intersections`
pub type SimplifyIntersections = fn(&mut Env, Option<OnTyvar<'_>>, &Ty) -> Ty;

/// What `typing_intersection.ml` puts in it:
/// `Typing_intersection.simplify_intersections`.
fn typing_intersection_simplify_intersections(
    env: &mut Env,
    on_tyvar: Option<OnTyvar<'_>>,
    ty: &Ty,
) -> Ty {
    crate::typing_intersection::simplify_intersections(env, on_tyvar, ty.clone())
}

pub static SIMPLIFY_INTERSECTIONS_REF: SimplifyIntersections =
    typing_intersection_simplify_intersections;

pub fn simplify_intersections(env: &mut Env, on_tyvar: Option<OnTyvar<'_>>, ty: &Ty) -> Ty {
    let f: SimplifyIntersections = SIMPLIFY_INTERSECTIONS_REF;
    f(env, on_tyvar, ty)
}

/// `type localize_no_subst`
pub type LocalizeNoSubst = fn(&mut Env, bool, &DeclTy) -> (Option<typing_error::T>, Ty);

/// What `typing_phase.ml` puts in it: `Typing_phase.localize_no_subst`.
pub static LOCALIZE_NO_SUBST_REF: LocalizeNoSubst = crate::typing_phase::localize_no_subst;

pub fn localize_no_subst(
    env: &mut Env,
    ignore_errors: bool,
    ty: &DeclTy,
) -> (Option<typing_error::T>, Ty) {
    let f: LocalizeNoSubst = LOCALIZE_NO_SUBST_REF;
    f(env, ignore_errors, ty)
}

/// `type localize`
pub type Localize = fn(&ExpandEnv, &mut Env, &DeclTy) -> (Option<typing_error::T>, Ty);

/// What `typing_phase.ml` puts in it: `Typing_phase.localize`.
pub static LOCALIZE_REF: Localize = crate::typing_phase::localize;

pub fn localize(ety_env: &ExpandEnv, env: &mut Env, ty: &DeclTy) -> (Option<typing_error::T>, Ty) {
    let f: Localize = LOCALIZE_REF;
    f(ety_env, env, ty)
}

/// What `typing_phase.ml` puts in it: `Typing_phase.localize_disjoint_union`.
pub static LOCALIZE_DISJOINT_UNION_REF: Localize = crate::typing_phase::localize_disjoint_union;

pub fn localize_disjoint_union(
    ety_env: &ExpandEnv,
    env: &mut Env,
    ty: &DeclTy,
) -> (Option<typing_error::T>, Ty) {
    let f: Localize = LOCALIZE_DISJOINT_UNION_REF;
    f(ety_env, env, ty)
}

// ---------------------------------------------------------------------------
// What the port needs from other modules
// ---------------------------------------------------------------------------

/// `MakeType.mixed r` for a decl type: `mk (r, Toption (nonnull r))`.
/// (`crate::typing_make_type::mixed` builds localized types only.)
fn decl_mixed(r: R) -> DeclTy {
    DeclTy::new(
        r.clone(),
        d::Ty_::Toption(DeclTy::new(r, d::Ty_::Tnonnull)),
    )
}

/// `Reason.implicit_upper_bound (p, s)` for a decl reason.
fn decl_implicit_upper_bound(p: &BPos, s: &str) -> R {
    R::mk(|| {
        ReasonImpl::FromWitnessDecl(WitnessDecl::ImplicitUpperBound(p.clone(), Symbol::new(s)))
    })
}

/// `Typing_make_type.union r tyl` for decl types.
fn decl_union(r: R, mut tyl: Vec<DeclTy>) -> DeclTy {
    if tyl.len() == 1 {
        tyl.pop().unwrap()
    } else {
        DeclTy::new(r, d::Ty_::Tunion(tyl.into_boxed_slice()))
    }
}

/// `super#on_type` in a class that inherits `Type_visitor.locl_type_visitor`
/// and overrides `on_type`: the dispatch of the inherited `on_type`, which
/// calls the methods of `this` (so the overriding ones too, as `this#...`).
pub(crate) fn locl_type_visitor_on_type<A, V: LoclTypeVisitor<A> + ?Sized>(this: &mut V, acc: A, ty: &Ty) -> A {
    let r = get_reason(ty);
    match get_node(ty) {
        Ty_::Tany(_) => this.on_tany(acc, r),
        Ty_::Tnonnull => this.on_tnonnull(acc, r),
        Ty_::Tdynamic(_) => this.on_tdynamic(acc, r),
        Ty_::Toption(ty) => this.on_toption(acc, r, ty),
        Ty_::Tprim(prim) => this.on_tprim(acc, r, *prim),
        Ty_::Tvar(id) => this.on_tvar(acc, r, *id),
        Ty_::Tfun(fty) => this.on_tfun(acc, r, fty),
        Ty_::Tgeneric(x) => this.on_tgeneric(acc, r, x),
        Ty_::Tnewtype(x, tyl, ty) => this.on_tnewtype(acc, r, x, tyl, ty),
        Ty_::Tdependent(x, ty) => this.on_tdependent(acc, r, x, ty),
        Ty_::Ttuple(t) => this.on_ttuple(acc, r, t),
        Ty_::Tunion(tyl) => this.on_tunion(acc, r, tyl),
        Ty_::Tintersection(tyl) => this.on_tintersection(acc, r, tyl),
        Ty_::Tshape(s) => this.on_tshape(acc, r, s),
        Ty_::Tclass(cls, exact, tyl) => this.on_tclass(acc, r, cls, exact, tyl),
        Ty_::TvecOrDict(ty1, ty2) => this.on_tvec_or_dict(acc, r, ty1, ty2),
        Ty_::Taccess(ta) => this.on_taccess(acc, r, ta),
        Ty_::Tneg(tneg) => this.on_neg_type(acc, r, tneg),
        Ty_::Tlabel(name) => this.on_tlabel(acc, r, name),
        Ty_::TclassPtr(ty) => this.on_tclass_ptr(acc, r, ty),
    }
}

/// `super#on_type` (`parent#on_type`) in a class that inherits
/// `Type_visitor.decl_type_visitor` and overrides `on_type` (see
/// [`locl_type_visitor_on_type`]).
fn decl_type_visitor_on_type<A, V: DeclTypeVisitor<A> + ?Sized>(
    this: &mut V,
    acc: A,
    ty: &DeclTy,
) -> A {
    let r = ty.reason();
    match ty.node_ref() {
        d::Ty_::Tany => this.on_tany(acc, r),
        d::Ty_::Tmixed => this.on_tmixed(acc, r),
        d::Ty_::Twildcard => this.on_twildcard(acc, r),
        d::Ty_::Tnonnull => this.on_tnonnull(acc, r),
        d::Ty_::Tdynamic => this.on_tdynamic(acc, r),
        d::Ty_::Tthis => this.on_tthis(acc, r),
        d::Ty_::TvecOrDict(kv) => this.on_tvec_or_dict(acc, r, &kv.0, &kv.1),
        d::Ty_::Tgeneric(s) => this.on_tgeneric(acc, r, s.as_str()),
        d::Ty_::Toption(ty) => this.on_toption(acc, r, ty),
        d::Ty_::Tlike(ty) => this.on_tlike(acc, r, ty),
        d::Ty_::Tprim(prim) => this.on_tprim(acc, r, *prim),
        d::Ty_::Tfun(fty) => this.on_tfun(acc, r, fty),
        d::Ty_::Tapply(s_and_tyl) => this.on_tapply(acc, r, &s_and_tyl.0, &s_and_tyl.1),
        d::Ty_::Trefinement(tr) => this.on_trefinement(acc, r, &tr.ty, &tr.refinement),
        d::Ty_::Taccess(aty) => this.on_taccess(acc, r, aty),
        d::Ty_::Ttuple(t) => this.on_ttuple(acc, r, t),
        d::Ty_::Tunion(tyl) => this.on_tunion(acc, r, tyl),
        d::Ty_::Tintersection(tyl) => this.on_tintersection(acc, r, tyl),
        d::Ty_::Tshape(s) => this.on_tshape(acc, r, s),
        d::Ty_::TclassPtr(ty) => this.on_tclass_ptr(acc, r, ty),
    }
}

// ---------------------------------------------------------------------------
// Checking properties of types
// ---------------------------------------------------------------------------

pub fn is_class(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tclass(..) => true,
        _ => false,
    }
}

pub fn is_class_i(ty: &InternalType) -> bool {
    match ty {
        InternalType::ConstraintType(_) => false,
        InternalType::LoclType(ty) => is_class(ty),
    }
}

/// The types that the predicates below compare with, all with the reason
/// `Reason.none`: built once per thread (OCaml builds them at each call; they
/// are only read, by subtyping queries that change nothing).
#[derive(Clone, Copy)]
enum ConstantType {
    Mixed,
    Nothing,
    Null,
    Dynamic,
    SupportdynMixed,
}

fn constant_type(which: ConstantType) -> Ty {
    thread_local! {
        static TYPES: [Ty; 5] = [
            make_type::mixed(typing_reason::none()),
            make_type::nothing(typing_reason::none()),
            make_type::null(typing_reason::none()),
            make_type::dynamic(typing_reason::none()),
            make_type::supportdyn_mixed(typing_reason::none()),
        ];
    }
    TYPES.with(|types| types[which as usize].clone())
}

pub fn is_mixed_i(env: &Env, ty: &InternalType) -> bool {
    let mixed = InternalType::LoclType(constant_type(ConstantType::Mixed));
    is_sub_type_for_union_i(env, &mixed, ty)
}

pub fn is_mixed(env: &Env, ty: &Ty) -> bool {
    is_mixed_i(env, &InternalType::LoclType(ty.clone()))
}

pub fn is_nothing_i(env: &Env, ty: &InternalType) -> bool {
    let nothing = InternalType::LoclType(constant_type(ConstantType::Nothing));
    is_sub_type_for_union_i(env, ty, &nothing)
}

pub fn is_nothing(env: &Env, ty: &Ty) -> bool {
    is_nothing_i(env, &InternalType::LoclType(ty.clone()))
}

pub fn is_null(env: &Env, ty: &Ty) -> bool {
    let null = constant_type(ConstantType::Null);
    is_sub_type_for_union(env, ty, &null)
}

pub fn is_dynamic(env: &Env, ty: &Ty) -> bool {
    let dynamic = constant_type(ConstantType::Dynamic);
    (is_sub_type_for_union(env, &dynamic, ty) && !is_mixed(env, ty))
        || (is_sub_type_for_union(env, ty, &dynamic) && !is_nothing(env, ty))
}

pub fn is_any(env: &Env, ty: &Ty) -> bool {
    // The environment the expansion returns is used below but not returned.
    let mut env = env.clone();
    let ty = typing_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Tany(_) => true,
        Ty_::Tunion(tyl) => tyl.iter().all(|ty| is_any(&env, ty)),
        Ty_::Tintersection(tyl) => tyl.iter().any(|ty| is_any(&env, ty)),
        _ => false,
    }
}

pub fn is_any_and_not_nothing(env: &Env, ty: &Ty) -> bool {
    // The environment the expansion returns is used below but not returned.
    let mut env = env.clone();
    let ty = typing_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Tany(_) => true,
        Ty_::Tunion(tyl) if tyl.is_empty() => false,
        Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => {
            tyl.iter().any(|ty| is_any_and_not_nothing(&env, ty))
        }
        _ => false,
    }
}

pub fn is_tunion(env: &Env, ty: &Ty) -> bool {
    let ty = typing_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tunion(_) => true,
        _ => false,
    }
}

pub fn is_tintersection(env: &Env, ty: &Ty) -> bool {
    let ty = typing_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tintersection(_) => true,
        _ => false,
    }
}

pub fn is_tyvar(env: &Env, ty: &Ty) -> bool {
    let ty = typing_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tvar(_) => true,
        _ => false,
    }
}

pub fn is_opt_tyvar(env: &Env, ty: &Ty) -> bool {
    // The environment the expansion returns is used below but not returned.
    let mut env = env.clone();
    let ty = typing_env::expand_type(&mut env, ty.clone());
    match get_node(&ty) {
        Ty_::Toption(ty) => is_tyvar(&env, ty),
        _ => false,
    }
}

pub fn is_tyvar_error(env: &Env, ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tvar(tvid) => typing_inference_env::is_error(&env.inference_env, *tvid),
        _ => false,
    }
}

pub fn contains_unresolved_tyvars(env: &mut Env, ty: &Ty) -> bool {
    struct Finder<'a> {
        env: &'a mut Env,
        /// The type variables whose solution has been visited without finding
        /// an unresolved one (not in the OCaml, which visits the solution
        /// again at each occurrence). Expanding a variable only shortens
        /// chains of aliases, so a second visit of the same solution would
        /// find nothing either. (A few: they are looked up linearly.)
        visited: Vec<isize>,
    }
    impl LoclTypeVisitor<bool> for Finder<'_> {
        fn on_tvar(&mut self, occurs: bool, r: &Reason, v: isize) -> bool {
            if occurs {
                return occurs;
            }
            if self.visited.contains(&v) {
                return false;
            }
            let ty = typing_env::expand_var(self.env, r.clone(), v);
            if typing_defs::is_tyvar(&ty) {
                true
            } else {
                let found = self.on_type(occurs, &ty);
                if !found && self.visited.len() < 16 {
                    self.visited.push(v);
                }
                found
            }
        }

        fn on_type(&mut self, occurs: bool, ty: &Ty) -> bool {
            if occurs {
                return occurs;
            }
            // Not in the OCaml, which visits it: a type without type
            // variables has no unresolved one (see `ty_flags`).
            if !ty.may_have_tyvars() {
                return false;
            }
            locl_type_visitor_on_type(self, occurs, ty)
        }
    }
    let mut finder = Finder {
        env,
        visited: vec![],
    };
    finder.on_type(false, ty)
}

/// `hackrs` decl types have no `Tvar` (`ty::decl::Ty_`), so the visitor never
/// reaches `on_tvar` and this is always `false`.
pub fn contains_tvar_decl(t: &DeclTy) -> bool {
    struct Finder;
    impl DeclTypeVisitor<bool> for Finder {
        fn on_tvar(&mut self, _found: bool, _r: &R, _v: isize) -> bool {
            true
        }

        fn on_type(&mut self, found: bool, ty: &DeclTy) -> bool {
            if found {
                true
            } else {
                decl_type_visitor_on_type(self, found, ty)
            }
        }
    }
    Finder.on_type(false, t)
}

/// `exception FoundGeneric of Pos_or_decl.t`, raised by the visitor of
/// [`contains_generic_decl`] and caught by it: the error of the accumulator,
/// with which the visitor does nothing more.
struct FoundGeneric(PosOrDecl);

pub fn contains_generic_decl(ty: &DeclTy) -> Option<PosOrDecl> {
    struct Visitor;
    impl DeclTypeVisitor<Result<(), FoundGeneric>> for Visitor {
        fn on_type(
            &mut self,
            env: Result<(), FoundGeneric>,
            ty: &DeclTy,
        ) -> Result<(), FoundGeneric> {
            let () = env?;
            match ty.node_ref() {
                d::Ty_::Tgeneric(_) => Err(FoundGeneric(PosOrDecl::from(ty.pos().clone()))),
                _ => decl_type_visitor_on_type(self, Ok(()), ty),
            }
        }
    }
    match Visitor.on_type(Ok(()), ty) {
        Ok(()) => None,
        Err(FoundGeneric(p)) => Some(p),
    }
}

/// [wrap_union_inter_ty_in_var env r ty] wraps [ty] in a type variable
/// if [ty] is a union, intersection or option containing an unsolved type variable.
/// Wrapping in a type variable means a new type variable is created and mapped to [ty].
/// This is a way to mark [ty] as needing simplification when the unsolved type variable
/// later gets solved.
pub fn wrap_union_inter_ty_in_var(env: &mut Env, r: Reason, ty: Ty) -> Ty {
    if is_union_or_inter_type(&ty) {
        let contains_unresolved_tyvars = contains_unresolved_tyvars(env, &ty);
        if contains_unresolved_tyvars {
            typing_env::wrap_ty_in_var(env, r, ty)
        } else {
            ty
        }
    } else {
        ty
    }
}

/// The lower bound of a newtype: what it is declared [super], if anything. The
/// dual of [`get_newtype_super`]; [None] when the typedef declares no [super]
/// constraint, so callers can pick their own default.
pub fn get_newtype_sub_opt(env: &mut Env, name: &str, tyargs: &[Ty]) -> Option<Ty> {
    match typing_env::get_typedef(env, name) {
        decl_entry::T::Found(td) => match &td.super_constraint {
            None => None,
            Some(cstr) => {
                let substs = crate::decl_subst::make_locl(&td.tparams, tyargs);
                let ety_env = ExpandEnv {
                    substs,
                    ..empty_expand_env()
                };
                let (_err, bound) = localize(&ety_env, env, cstr);
                Some(bound)
            }
        },
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
    }
}

pub fn get_newtype_super(env: &mut Env, r: Reason, name: &str, tyargs: &[Ty]) -> Ty {
    // Special case for supportdyn<T>: use the localized arg directly
    // to avoid supportdynamic.hhi leaking into reasons. This applies even when
    // the typedef is unbound: under everything_sdt the unbound fallthrough
    // below returns supportdyn<mixed>, which does not reduce supportdyn itself
    // and sends subtyping into an infinite loop.
    if name == sn::classes::SUPPORT_DYN {
        match tyargs {
            [ty] => ty.clone(),
            _ => make_type::mixed(r),
        }
    } else if typing_env::is_enum(env, name) {
        match typing_env::get_enum_constraint(env, name) {
            decl_entry::T::Found(Some(ty)) => {
                let (_err, ty) = localize(&empty_expand_env(), env, &ty);
                ty
            }
            _ => match typing_env::get_enum(env, name) {
                decl_entry::T::Found(tc) => make_type::arraykey(typing_reason::implicit_upper_bound((
                    cls::pos(&tc),
                    "arraykey".to_string(),
                ))),
                _ => make_type::arraykey(typing_reason::implicit_upper_bound((
                    typing_reason::to_pos(&r),
                    "arraykey".to_string(),
                ))),
            },
        }
    } else {
        match typing_env::get_typedef(env, name) {
            decl_entry::T::Found(td)
                if !typing_reason::predicates::is_opaque_type_from_module(&r) =>
            {
                let decl_cstr = match &td.as_constraint {
                    None => decl_mixed(decl_implicit_upper_bound(&td.pos, "?nonnull")),
                    Some(cstr) => cstr.clone(),
                };
                let substs = crate::decl_subst::make_locl(&td.tparams, tyargs);
                let ety_env = ExpandEnv {
                    substs,
                    ..empty_expand_env()
                };
                let (_err, bound) = localize(&ety_env, env, &decl_cstr);
                // It's not helpful to report the trivial bound for FunctionRef. Also,
                // preserve the reason for opaque types created during localization
                if name == C_FUNCTION_REF
                    || typing_reason::predicates::is_opaque_type_from_module(&r)
                {
                    with_reason(bound, r)
                } else {
                    bound
                }
            }
            // `Decl_entry.DoesNotExist | Decl_entry.NotYetAvailable | _`
            _ => {
                if env.genv.tcopt.po.everything_sdt {
                    make_type::supportdyn_mixed(r)
                } else {
                    make_type::mixed(r)
                }
            }
        }
    }
}

/// `Concrete_supertypes_cache`: the cache of [`get_concrete_supertypes`].
pub mod concrete_supertypes_cache {
    use std::cell::RefCell;
    use std::collections::BTreeMap;

    use super::Env;
    use super::ty_set;

    /// `type entry`
    #[derive(Clone)]
    pub struct Entry {
        pub input_env: Env,
        pub expand_supportdyn: bool,
        pub include_case_types: bool,
        pub abstract_enum: bool,
        pub supertypes: ty_set::T,
    }

    /// `type t = entry list S_map.t ref`. The head of each OCaml list is the
    /// last element of its vector.
    pub struct T(RefCell<BTreeMap<String, Vec<Entry>>>);

    pub fn create() -> T {
        T(RefCell::new(BTreeMap::new()))
    }

    pub(super) fn find(
        cache: &T,
        expand_supportdyn: bool,
        include_case_types: bool,
        abstract_enum: bool,
        input_env: &Env,
        name: &str,
    ) -> Option<Entry> {
        cache.0.borrow().get(name).and_then(|entries| {
            entries
                .iter()
                .rev()
                .find(|entry| {
                    super::env_phys_equal(input_env, &entry.input_env)
                        && expand_supportdyn == entry.expand_supportdyn
                        && include_case_types == entry.include_case_types
                        && abstract_enum == entry.abstract_enum
                })
                .cloned()
        })
    }

    pub(super) fn add(cache: &T, name: String, entry: Entry) {
        cache.0.borrow_mut().entry(name).or_default().push(entry)
    }
}

/// `phys_equal env1 env2` on environments, with which the cache of
/// [`get_concrete_supertypes`] knows that an environment has not changed.
///
/// An [`Env`] is a shared handle that copies its fields on the first write
/// through a handle that is not the only one (`Rc::make_mut`): the cache
/// keeps a handle of the input environment, so a computation that writes to
/// the environment leaves it with other fields than the cached handle's,
/// and one that does not leaves it sharing them, which is what the OCaml's
/// physical equality tells (a write that changes nothing still counts as a
/// change here: the cache can only hit less often than the OCaml's).
fn env_phys_equal(env1: &Env, env2: &Env) -> bool {
    Env::ptr_eq(env1, env2)
}

/// Get the "as" constraints from an abstract type or generic parameter, or
/// return the type itself if there is no "as" constraint.
/// In the case of a generic parameter whose "as" constraint is another
/// generic parameter, repeat the process until a type is reached that is not
/// a generic parameter. Don't loop on cycles.
/// (For example, function foo<Tu as Tv, Tv as Tu>(...))
/// Also breaks apart intersections.
pub fn get_concrete_supertypes(
    cache: Option<&concrete_supertypes_cache::T>,
    expand_supportdyn: Option<bool>,
    include_case_types: Option<bool>,
    abstract_enum: bool,
    env: &mut Env,
    ty: Ty,
) -> Vec<Ty> {
    let expand_supportdyn = expand_supportdyn.unwrap_or(true);
    let include_case_types = include_case_types.unwrap_or(false);
    let default_cache;
    let cache = match cache {
        Some(cache) => cache,
        None => {
            default_cache = concrete_supertypes_cache::create();
            &default_cache
        }
    };
    struct Ctx<'a> {
        cache: &'a concrete_supertypes_cache::T,
        expand_supportdyn: bool,
        include_case_types: bool,
        abstract_enum: bool,
    }
    fn collect(ctx: &Ctx<'_>, seen: &SSet, env: &mut Env, ty: Ty) -> (ty_set::T, bool) {
        let ty = typing_env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tnewtype(cid, _, _)
                if (!ctx.expand_supportdyn) && cid == sn::classes::SUPPORT_DYN =>
            {
                (ty_set::singleton(ty.clone()), false)
            }
            Ty_::Tnewtype(cid, tyargs, _) => {
                let as_ty = get_newtype_super(env, get_reason(&ty).clone(), cid, tyargs);
                let as_ty = typing_env::expand_type(env, as_ty);
                if ctx.abstract_enum
                    && is_prim(Tprim::Tarraykey, &as_ty)
                    && typing_env::is_enum(env, cid)
                {
                    (ty_set::empty(), false)
                } else if cid == C_FUNCTION_REF {
                    collect(ctx, seen, env, as_ty)
                } else {
                    let supertypes = ty_set::singleton(as_ty);
                    let supertypes = if ctx.include_case_types {
                        ty_set::add(ty.clone(), &supertypes)
                    } else {
                        supertypes
                    };
                    (supertypes, false)
                }
            }
            Ty_::Tdependent(_, ty) => (ty_set::singleton(ty.clone()), false),
            Ty_::Tgeneric(name) => {
                if seen.contains(name) {
                    (ty_set::empty(), true)
                } else {
                    let input_env = env.clone();
                    match concrete_supertypes_cache::find(
                        ctx.cache,
                        ctx.expand_supportdyn,
                        ctx.include_case_types,
                        ctx.abstract_enum,
                        &input_env,
                        name,
                    ) {
                        Some(concrete_supertypes_cache::Entry { supertypes, .. }) => {
                            (supertypes, false)
                        }
                        None => {
                            let mut seen = seen.clone();
                            seen.insert(name.clone());
                            let bounds = ty_set::elements(&typing_env::get_upper_bounds(env, name));
                            let (supertypes, encountered_cycle) =
                                collect_list(ctx, &seen, env, &bounds);
                            if (!encountered_cycle) && env_phys_equal(env, &input_env) {
                                concrete_supertypes_cache::add(
                                    ctx.cache,
                                    name.clone(),
                                    concrete_supertypes_cache::Entry {
                                        input_env,
                                        expand_supportdyn: ctx.expand_supportdyn,
                                        include_case_types: ctx.include_case_types,
                                        abstract_enum: ctx.abstract_enum,
                                        supertypes: supertypes.clone(),
                                    },
                                );
                            }
                            (supertypes, encountered_cycle)
                        }
                    }
                }
            }
            Ty_::Tintersection(tys) => collect_list(ctx, seen, env, tys),
            _ => (ty_set::singleton(ty.clone()), false),
        }
    }
    fn collect_list(ctx: &Ctx<'_>, seen: &SSet, env: &mut Env, tys: &[Ty]) -> (ty_set::T, bool) {
        let mut acc = ty_set::empty();
        let mut encountered_cycle = false;
        for ty in tys {
            let (supertypes, ty_encountered_cycle) = collect(ctx, seen, env, ty.clone());
            acc = ty_set::union(&acc, &supertypes);
            encountered_cycle = encountered_cycle || ty_encountered_cycle;
        }
        (acc, encountered_cycle)
    }
    let ctx = Ctx {
        cache,
        expand_supportdyn,
        include_case_types,
        abstract_enum,
    };
    let (supertypes, _encountered_cycle) = collect(&ctx, &SSet::new(), env, ty);
    ty_set::elements(&supertypes)
}

/// The concrete types known to be BELOW the given type: the dual of
/// [`get_concrete_supertypes`]. Use this, not that one, when reading a lower
/// bound -- supertypes can only bound from above.
pub fn get_concrete_subtypes(env: &mut Env, ty: Ty) -> Vec<Ty> {
    let mut seen = SSet::new();
    let mut acc = ty_set::empty();
    // The OCaml list `tyl`, its head in front.
    let mut tyl: VecDeque<Ty> = VecDeque::from([ty]);
    while let Some(ty) = tyl.pop_front() {
        let ty = typing_env::expand_type(env, ty);
        match get_node(&ty) {
            Ty_::Tgeneric(n) => {
                if !seen.contains(n) {
                    seen.insert(n.clone());
                    let lower_bounds = ty_set::elements(&typing_env::get_lower_bounds(env, n));
                    for ty in lower_bounds.into_iter().rev() {
                        tyl.push_front(ty)
                    }
                }
            }
            Ty_::Tnewtype(cid, tyargs, _) => {
                let sub_ty = get_newtype_sub_opt(env, cid, tyargs);
                match sub_ty {
                    Some(sub_ty) => tyl.push_front(sub_ty),
                    None => acc = ty_set::add(ty.clone(), &acc),
                }
            }
            // Mirror of the [Tintersection] case in [get_concrete_supertypes]: every
            // member of a union is below it. An intersection is deliberately not
            // flattened here for the same reason that function leaves unions alone.
            Ty_::Tunion(tyl_) => {
                for ty in tyl_.iter().rev() {
                    tyl.push_front(ty.clone())
                }
            }
            _ => acc = ty_set::add(ty.clone(), &acc),
        }
    }
    ty_set::elements(&acc)
}

/// Over-approximate a shape splat as a flattened list of concrete shape elements
/// (each a [Shape_simple] or [nothing]) by resolving each splat-position type
/// parameter to its concrete shape supertypes, transitively. Returns [None] if
/// some element cannot be reduced to a shape.
pub fn get_shape_splat_concrete_supertypes(env: &mut Env, ty: Ty) -> Option<Vec<Ty>> {
    let concrete_supertypes_cache = concrete_supertypes_cache::create();
    fn intersect_supertypes(env: &mut Env, reason: &Reason, tys: Vec<Ty>) -> Ty {
        fn pair(env: &mut Env, reason: &Reason, tys: &[Ty]) -> Vec<Ty> {
            let mut acc = vec![];
            let mut tys = tys;
            loop {
                match tys {
                    [ty1, ty2, rest @ ..] => {
                        let ty = intersect_list(env, reason.clone(), &[ty1.clone(), ty2.clone()]);
                        acc.push(ty);
                        tys = rest;
                    }
                    [ty] => {
                        acc.push(ty.clone());
                        return acc;
                    }
                    [] => return acc,
                }
            }
        }
        fn reduce(env: &mut Env, reason: &Reason, tys: Vec<Ty>) -> Ty {
            match tys.as_slice() {
                [] => intersect_list(env, reason.clone(), &[]),
                [ty] => ty.clone(),
                _ => {
                    let tys = pair(env, reason, &tys);
                    reduce(env, reason, tys)
                }
            }
        }
        reduce(env, reason, tys)
    }
    type Memo = BTreeMap<String, Option<Vec<Ty>>>;
    fn resolve(
        cache: &concrete_supertypes_cache::T,
        visited: &SSet,
        memo: &mut Memo,
        env: &mut Env,
        ty: Ty,
    ) -> Option<Vec<Ty>> {
        let ty = typing_env::expand_type(env, ty);
        resolve_expanded(cache, visited, memo, env, ty)
    }
    fn resolve_expanded(
        cache: &concrete_supertypes_cache::T,
        visited: &SSet,
        memo: &mut Memo,
        env: &mut Env,
        ty: Ty,
    ) -> Option<Vec<Ty>> {
        match get_node(&ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(_)) => Some(vec![ty.clone()]),
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                resolve_elems(cache, visited, memo, env, ss_elems)
            }
            Ty_::Tgeneric(name) if visited.contains(name) => None,
            Ty_::Tgeneric(name) => match memo.get(name) {
                Some(result) => result.clone(),
                None => {
                    let supers = get_concrete_supertypes(Some(cache), None, None, false, env, ty.clone());
                    let result = match supers.as_slice() {
                        [] => None,
                        _ => {
                            let combined = intersect_supertypes(env, get_reason(&ty), supers);
                            let mut visited = visited.clone();
                            visited.insert(name.clone());
                            resolve(cache, &visited, memo, env, combined)
                        }
                    };
                    memo.insert(name.clone(), result.clone());
                    result
                }
            },
            _ if is_nothing(env, &ty) => Some(vec![ty.clone()]),
            _ => None,
        }
    }
    fn resolve_elems(
        cache: &concrete_supertypes_cache::T,
        visited: &SSet,
        memo: &mut Memo,
        env: &mut Env,
        tys: &[Ty],
    ) -> Option<Vec<Ty>> {
        // `acc` is the OCaml `acc` reversed (in the order of the result);
        // `pending` is the OCaml list of lists, its head last.
        let mut acc: Vec<Ty> = vec![];
        let mut pending: Vec<VecDeque<Ty>> = vec![tys.iter().cloned().collect()];
        loop {
            let next = match pending.last_mut() {
                None => return Some(acc),
                Some(tys) => tys.pop_front(),
            };
            match next {
                None => {
                    pending.pop();
                }
                Some(ty) => {
                    let ty = typing_env::expand_type(env, ty);
                    match get_node(&ty) {
                        Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                            pending.push(ss_elems.iter().cloned().collect())
                        }
                        _ => {
                            let result = resolve_expanded(cache, visited, memo, env, ty.clone());
                            match result {
                                None => return None,
                                Some(resolved) => acc.extend(resolved),
                            }
                        }
                    }
                }
            }
        }
    }
    let mut memo = Memo::new();
    resolve(&concrete_supertypes_cache, &SSet::new(), &mut memo, env, ty)
}

/// Run a function on an intersection represented by a list of types.
/// We stay liberal with errors:
/// discard the result of any run which has produced an error.
/// If all runs have produced an error, gather all errors and results and add errors.
/// Note: warnings should NOT affect which results are considered valid
pub fn run_on_intersection<E, A>(
    env: &mut E,
    mut f: impl FnMut(&mut E, &Ty) -> A,
    tyl: &[Ty],
) -> Vec<A> {
    let resl_errors: Vec<(A, diagnostics::T)> = tyl
        .iter()
        .map(|ty| {
            let (errors, result) = diagnostics::do_(None, || f(env, ty));
            (result, errors)
        })
        .collect();
    let valid: Vec<bool> = resl_errors
        .iter()
        .map(|(_, err)| diagnostics::has_no_errors(None, err))
        .collect();
    // Always merge warnings from all branches so they're not lost
    for (_, err) in &resl_errors {
        let warnings_only = diagnostics::filter(err.clone(), |_path, error| {
            match error.severity {
                Severity::Warning { .. } => true,
                Severity::Err => false,
            }
        });
        diagnostics::merge_into_current(warnings_only);
    }
    if valid.iter().any(|valid| *valid) {
        resl_errors
            .into_iter()
            .zip(valid)
            .filter_map(|((result, _), valid)| if valid { Some(result) } else { None })
            .collect()
    } else {
        for (_, err) in &resl_errors {
            diagnostics::merge_into_current(diagnostics::filter_out_warnings(
                err.clone(),
            ));
        }
        resl_errors.into_iter().map(|(result, _)| result).collect()
    }
}

pub fn run_on_intersection_with_ty_err<E, A>(
    env: &mut E,
    mut f: impl FnMut(&mut E, &Ty) -> (Option<typing_error::T>, A),
    tys: &[Ty],
) -> (Option<typing_error::T>, Vec<A>) {
    let resl: Vec<(A, Option<typing_error::T>)> = tys
        .iter()
        .map(|ty| {
            let (ty_err_opt, res) = f(env, ty);
            (res, ty_err_opt)
        })
        .collect();
    // Partition the results into those with and without errors
    let mut without_err: Vec<A> = vec![];
    let mut with_err: Vec<(A, typing_error::T)> = vec![];
    for (res, ty_err_opt) in resl {
        match ty_err_opt {
            None => without_err.push(res),
            Some(err) => with_err.push((res, err)),
        }
    }
    if without_err.is_empty() {
        // We have no element of the intersection without error
        // Take the intersection of the errors so we remember where they came from
        // when applying error suppression
        let (res, errs): (Vec<A>, Vec<typing_error::T>) = with_err.into_iter().unzip();
        (typing_error::intersect_opt(errs), res)
    } else {
        // We have at least one that is without error so return the elements without
        // error and indicate there is no error for the intersection
        (None, without_err)
    }
}

/// As above but allow functions which also return subtyping/coercion error
/// information
pub fn run_on_intersection_res<E, B, C>(
    env: &mut E,
    mut f: impl FnMut(&mut E, &Ty) -> (B, C),
    tyl: &[Ty],
) -> (Vec<B>, Vec<C>) {
    let g = |env: &mut E, ty: &Ty| {
        let (a, b) = f(env, ty);
        (a, b)
    };
    let pairs = run_on_intersection(env, g, tyl);
    pairs.into_iter().unzip()
}

pub fn run_on_intersection_key_value_res<E, B, C, D>(
    env: &mut E,
    mut f: impl FnMut(&mut E, &Ty) -> (B, C, D),
    tyl: &[Ty],
) -> (Vec<B>, Vec<C>, Vec<D>) {
    let g = |env: &mut E, ty: &Ty| {
        let (a, b, c) = f(env, ty);
        (a, b, c)
    };
    let triples = run_on_intersection(env, g, tyl);
    // `List.unzip3`
    let mut res = vec![];
    let mut key_errs = vec![];
    let mut errs = vec![];
    for (a, b, c) in triples {
        res.push(a);
        key_errs.push(b);
        errs.push(c);
    }
    (res, key_errs, errs)
}

pub fn run_on_intersection_array_key_value_res<E, B, C, D, F>(
    env: &mut E,
    mut f: impl FnMut(&mut E, &Ty) -> (B, C, D, F),
    tyl: &[Ty],
) -> (Vec<B>, Vec<C>, Vec<D>, Vec<F>) {
    let g = |env: &mut E, ty: &Ty| {
        let (a, b, c, d) = f(env, ty);
        (a, b, c, d)
    };
    let quads = run_on_intersection(env, g, tyl);
    // `List.unzip4`
    let mut res = vec![];
    let mut arr_errs = vec![];
    let mut key_errs = vec![];
    let mut val_errs = vec![];
    for (a, b, c, d) in quads {
        res.push(a);
        arr_errs.push(b);
        key_errs.push(c);
        val_errs.push(d);
    }
    (res, arr_errs, key_errs, val_errs)
}

pub fn strip_supportdyn(env: &mut Env, ty: Ty) -> (bool, Ty) {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            let (_, ty) = strip_supportdyn(env, tyargs[0].clone());
            (true, ty)
        }
        _ => (false, ty),
    }
}

/// (The function type is shared with the type, not copied.)
pub fn get_underlying_function_type(
    env: &mut Env,
    ty: Ty,
) -> Option<(Reason, std::rc::Rc<FunType>)> {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, _)
            if tyargs.len() == 1
                && (name == sn::classes::SUPPORT_DYN || name == C_FUNCTION_REF) =>
        {
            get_underlying_function_type(env, tyargs[0].clone())
        }
        Ty_::Tfun(ft) => Some((get_reason(&ty).clone(), ft.clone())),
        _ => None,
    }
}

/// The list of types should not be considered to be a bound if it is all mixed
/// or supportdyn<mixed> (when include_sd_mixed is set
pub fn no_upper_bound(include_sd_mixed: bool, env: &mut Env, tyl: &[Ty]) -> bool {
    // `List.for_all_env`, which stops at the first `false`.
    for ty in tyl {
        let holds = if is_mixed(env, ty) {
            true
        } else if include_sd_mixed {
            let (stripped, ty) = strip_supportdyn(env, ty.clone());
            stripped && is_mixed(env, &ty)
        } else {
            false
        };
        if !holds {
            return false;
        }
    }
    true
}

/// Gets the base type of an abstract type
pub fn get_base_type(expand_supportdyn: Option<bool>, env: &mut Env, ty: Ty) -> Ty {
    let expand_supportdyn = expand_supportdyn.unwrap_or(true);
    fn loop_(expand_supportdyn: bool, env: &mut Env, seen_generics: &SSet, ty: Ty) -> Ty {
        let ty = typing_env::expand_type(env, ty);
        let r = get_reason(&ty).clone();
        let default = |env: &mut Env| -> Ty {
            let tys = get_concrete_supertypes(None, Some(expand_supportdyn), None, true, env, ty.clone());
            let has_no_bounds = no_upper_bound(expand_supportdyn, env, &tys);
            match tys.as_slice() {
                [ty] if !has_no_bounds => loop_(expand_supportdyn, env, seen_generics, ty.clone()),
                _ => ty.clone(),
            }
        };
        match get_node(&ty) {
            Ty_::Tnewtype(classname, _, _)
                if classname == sn::classes::CLASS_NAME
                    || classname == sn::classes::CLASS_OR_CLASSNAME =>
            {
                ty.clone()
            }
            Ty_::Tnewtype(n, tyargs, _) if tyargs.len() == 1 && n == sn::classes::SUPPORT_DYN => {
                let ty = loop_(expand_supportdyn, env, seen_generics, tyargs[0].clone());
                if expand_supportdyn {
                    ty
                } else {
                    make_type::supportdyn(r, ty)
                }
            }
            // If we have an expression dependent type and it only has one super
            // type, we can treat it similarly to AKdependent _, Some ty
            Ty_::Tgeneric(n) if dependent_kind::is_generic_dep_ty(n) => {
                match ty_set::elements(&typing_env::get_upper_bounds(env, n)).as_slice() {
                    [ty2, ..] if ty_equal(None, &ty, ty2) => ty.clone(),
                    // If it's exactly equal, then the base ty is just this one
                    [ty, ..] => {
                        if ty_set::mem(ty, &typing_env::get_lower_bounds(env, n)) {
                            ty.clone()
                        } else if seen_generics.contains(n) {
                            ty.clone()
                        } else {
                            let mut seen_generics = seen_generics.clone();
                            seen_generics.insert(n.clone());
                            loop_(expand_supportdyn, env, &seen_generics, ty.clone())
                        }
                    }
                    [] => ty.clone(),
                }
            }
            Ty_::Tnewtype(cid, tyargs, _) if typing_env::is_enum(env, cid) => {
                let bound_ty = get_newtype_super(env, r, cid, tyargs);
                if is_prim(Tprim::Tarraykey, &bound_ty) {
                    ty.clone()
                } else {
                    default(env)
                }
            }
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) | Ty_::Tdependent(..) => default(env),
            _ => ty.clone(),
        }
    }
    loop_(expand_supportdyn, env, &SSet::new(), ty)
}

/// `Typing_defs.TShapeField.name`
pub fn get_printable_shape_field_name(x: &TshapeFieldName) -> bstr::BString {
    t_shape_field::name(x)
}

// ---------------------------------------------------------------------------
// Class types
// ---------------------------------------------------------------------------

/// `Invalid_argument`, which `unwrap_class_type` raises and
/// `try_unwrap_class_type` catches (`Option.try_with`).
struct InvalidArgument(&'static str);

/// `unwrap_class_type`, raising its exception as an error.
fn unwrap_class_type_result(
    ty: &DeclTy,
) -> Result<(R, Positioned<TypeName, BPos>, Vec<DeclTy>), InvalidArgument> {
    match ty.node_ref() {
        d::Ty_::Tapply(name_and_tparaml) => {
            let (name, tparaml) = &**name_and_tparaml;
            Ok((ty.reason().clone(), name.clone(), tparaml.to_vec()))
        }
        _ => Err(InvalidArgument("unwrap_class_type got non-class")),
    }
}

pub fn unwrap_class_type(ty: &DeclTy) -> (R, Positioned<TypeName, BPos>, Vec<DeclTy>) {
    match unwrap_class_type_result(ty) {
        Ok(res) => res,
        Err(InvalidArgument(msg)) => panic!("Invalid_argument(\"{}\")", msg),
    }
}

pub fn try_unwrap_class_type(x: &DeclTy) -> Option<(R, Positioned<TypeName, BPos>, Vec<DeclTy>)> {
    unwrap_class_type_result(x).ok()
}

pub fn class_is_final_and_invariant(class_ty: &cls::T) -> bool {
    cls::final_(class_ty)
        && cls::tparams_ref(class_ty)
            .iter()
            .all(|tp| tp.variance == oxidized::ast_defs::Variance::Invariant)
}

// ---------------------------------------------------------------------------
// Function parameters
// ---------------------------------------------------------------------------

/// The OCaml makes a `'a fun_param` of either phase; this is the localized
/// one (`ty::decl::FunParam` has its own constructors).
pub fn default_fun_param(readonly: bool, pos: Option<PosOrDecl>, ty: Ty) -> FunParam {
    let pos = pos.unwrap_or(Pos::NONE);
    FunParam {
        pos,
        name: None,
        type_: ty,
        flags: make_fp_flags(
            ParamMode::FPnormal,
            false, // accept_disposable
            false, // is_optional
            readonly,
            false, // ignore_readonly_error
            false, // splat
            false, // named
        ),
        def_value: None,
    }
}

/// `let tany = Env.tany`
fn tany(env: &Env) -> Ty_ {
    typing_env::tany(env)
}

pub fn mk_tany(env: &Env, p: Pos) -> Ty {
    let tany = tany(env);
    mk((typing_reason::witness(p), tany))
}

pub fn collect_enum_class_upper_bounds(env: &mut Env, name: &str) -> Option<Ty> {
    // the boolean ok is here to see if we find anything at all,
    // and prevents us to return the initial mixed value if nothing
    // is to be found.
    fn collect(env: &Env, seen: SSet, ok: bool, result: Ty, name: &str) -> (SSet, bool, Ty) {
        let upper_bounds = typing_env::get_upper_bounds(env, name);
        let mut acc = (seen, ok, result);
        for lty in upper_bounds.iter() {
            let (seen, ok, result) = acc;
            acc = match get_node(lty) {
                Ty_::Tclass((_, name), _, _) if typing_env::is_enum_class(env, name) => {
                    let result = {
                        // We build an intersection, but only care about the result
                        // if it is simplified to a singleton type, so the following
                        // reason is not useful. We could add a dedicated reason
                        // for more precise error reporting.
                        let r = typing_reason::none();
                        mk((r, Ty_::Tintersection(vec![result, lty.clone()])))
                    };
                    (seen, true, result)
                }
                Ty_::Tgeneric(name) if !seen.contains(name) => {
                    let mut seen = seen;
                    seen.insert(name.clone());
                    collect(env, seen, ok, result, name)
                }
                _ => (seen, ok, result),
            };
        }
        acc
    }
    let mixed = make_type::mixed(typing_reason::none());
    let (_, ok, upper_bound) = collect(env, SSet::new(), false, mixed, name);
    if ok {
        let upper_bound = simplify_intersections(env, None, &upper_bound);
        Some(upper_bound)
    } else {
        None
    }
}

pub fn make_locl_subst_for_class_tparams(
    classdef: &cls::T,
    tyl: &[Ty],
) -> crate::pmap::Map<String, Ty> {
    if tyl.is_empty() {
        crate::pmap::Map::new()
    } else {
        crate::decl_subst::make_locl(cls::tparams_ref(classdef), tyl)
    }
}

pub fn is_sub_class_refl(env: &Env, c_sub: &str, c_super: &str) -> bool {
    c_sub == c_super
        || match typing_env::get_class(env, c_sub) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
            decl_entry::T::Found(cls_sub) => cls::has_ancestor(&cls_sub, c_super),
        }
}

pub fn class_has_no_params(env: &Env, c: &str) -> bool {
    match typing_env::get_class(env, c) {
        decl_entry::T::Found(cls) => cls::tparams_ref(&cls).is_empty(),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
    }
}

/// The definitions that the ones of the `.mli` shadow (see the module
/// documentation).
mod with_visited {
    use super::*;

    /// Is super_id an ancestor of sub_id, including through requires steps?
    /// Maintain a visited set to catch cycles (these are rejected in folding but
    /// the definitions survive).
    pub fn has_ancestor_including_req(
        visited: &SSet,
        env: &Env,
        cls: &cls::T,
        super_id: &str,
    ) -> bool {
        cls::has_ancestor(cls, super_id) || {
            let kind = cls::kind(cls);
            (ast_defs::is_c_trait(kind) || ast_defs::is_c_interface(kind))
                && (cls::requires_ancestor(cls, super_id) || {
                    let mut bounds = cls::upper_bounds_on_this_iter(cls);
                    bounds.any(|ty| match ty.node_ref() {
                        d::Ty_::Tapply(name_and_args) => {
                            let (name, _) = &**name_and_args;
                            has_ancestor_including_req_refl(
                                visited,
                                env,
                                name.id_ref().as_str(),
                                super_id,
                            )
                        }
                        _ => false,
                    })
                })
        }
    }

    pub fn has_ancestor_including_req_refl(
        visited: &SSet,
        env: &Env,
        sub_id: &str,
        super_id: &str,
    ) -> bool {
        (!visited.contains(sub_id))
            && (sub_id == super_id
                || match typing_env::get_class(env, sub_id) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
                    decl_entry::T::Found(cls) => {
                        let mut visited = visited.clone();
                        visited.insert(sub_id.to_string());
                        has_ancestor_including_req(&visited, env, &cls, super_id)
                    }
                })
    }

    /// Return true if the type is known to support dynamic (i.e. is a subtype of supportdyn<mixed>)
    /// Note that we look at bounds on type variables, so vec<#0> produces true if #0 has a
    /// bound that supports dynamic
    pub fn is_supportdyn(
        visited_tyvars: &tvid::set::T,
        visited_typarams: &SSet,
        env: &Env,
        ty: &Ty,
    ) -> bool {
        // The environment the expansion returns is used below but not
        // returned.
        let mut env = env.clone();
        let ty = typing_env::expand_type(&mut env, ty.clone());
        let env = &env;
        let recurse = |ty: &Ty| is_supportdyn(visited_tyvars, visited_typarams, env, ty);
        match get_node(&ty) {
            Ty_::Tprim(_) | Ty_::Tdynamic(_) | Ty_::Tlabel(_) | Ty_::Tany(_) => true,
            Ty_::Tunion(tyl) => tyl.iter().all(recurse),
            Ty_::Tintersection(tyl) => tyl.iter().any(recurse),
            Ty_::Tnonnull => false,
            Ty_::Tfun(ft) => get_ft_support_dynamic_type(ft),
            Ty_::Toption(ty) => recurse(ty),
            Ty_::Ttuple(TupleType {
                required: t_required,
                optional: t_optional,
                extra: TupleExtra::Tvariadic(t_vs) | TupleExtra::Tsplat(t_vs),
            }) => t_required.iter().all(recurse) && t_optional.iter().all(recurse) && recurse(t_vs),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value: s_unknown_value,
                fields: s_fields,
            })) => {
                recurse(s_unknown_value)
                    && s_fields
                        .values()
                        .fold(true, |d, sft| d && recurse(&sft.ty))
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                ss_elems.iter().all(recurse)
            }
            Ty_::TvecOrDict(ty1, ty2) => recurse(ty1) && recurse(ty2),
            Ty_::Tnewtype(n, tyl, _) if tyl.len() == 1 && n == sn::classes::SUPPORT_DYN => true,
            Ty_::Tnewtype(n, tyl, _) => {
                // `let (_, bound) = get_newtype_super env ...`: its environment
                // is dropped.
                let bound = get_newtype_super(&mut env.clone(), get_reason(&ty).clone(), n, tyl);
                recurse(&bound)
            }
            Ty_::Tdependent(_, ty) => recurse(ty),
            Ty_::Tclass((_, class_id), _exact, tyargs) => {
                tyargs.iter().all(recurse) && {
                    let class_def_sub = typing_env::get_class(env, class_id);
                    match class_def_sub {
                        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => true,
                        decl_entry::T::Found(class_sub) => {
                            cls::get_support_dynamic_type(&class_sub)
                                || typing_env::is_enum(env, class_id)
                        }
                    }
                }
            }
            Ty_::Tvar(id) => {
                if visited_tyvars.contains(id) || is_tyvar_error(env, &ty) {
                    false
                } else {
                    let upper_bounds = typing_env::get_tyvar_upper_bounds(env, *id);
                    let mut visited_tyvars = visited_tyvars.clone();
                    visited_tyvars.insert(*id);
                    ity_set::exists(
                        |ty| is_supportdyn_i(&visited_tyvars, visited_typarams, env, ty),
                        &upper_bounds,
                    )
                }
            }
            Ty_::Tgeneric(name) => {
                if visited_typarams.contains(name) {
                    false
                } else {
                    let upper_bounds = typing_env::get_upper_bounds(env, name);
                    let mut visited_typarams = visited_typarams.clone();
                    visited_typarams.insert(name.clone());
                    ty_set::exists(
                        |ty| is_supportdyn(visited_tyvars, &visited_typarams, env, ty),
                        &upper_bounds,
                    )
                }
            }
            Ty_::TclassPtr(ty) => recurse(ty),
            _ => false,
        }
    }

    pub fn is_supportdyn_i(
        visited_tyvars: &tvid::set::T,
        visited_typarams: &SSet,
        env: &Env,
        ty: &InternalType,
    ) -> bool {
        match ty {
            InternalType::LoclType(ty) => is_supportdyn(visited_tyvars, visited_typarams, env, ty),
            _ => false,
        }
    }
}

pub fn has_ancestor_including_req(env: &Env, cls: &cls::T, super_id: &str) -> bool {
    // The first tests of `with_visited::has_ancestor_including_req`, which
    // decide most cases, before the empty visited set is made.
    cls::has_ancestor(cls, super_id) || {
        let kind = cls::kind(cls);
        (ast_defs::is_c_trait(kind) || ast_defs::is_c_interface(kind))
            && with_visited::has_ancestor_including_req(&crate::im_empty::ord_set(), env, cls, super_id)
    }
}

pub fn has_ancestor_including_req_refl(env: &Env, sub_id: &str, super_id: &str) -> bool {
    with_visited::has_ancestor_including_req_refl(&crate::im_empty::ord_set(), env, sub_id, super_id)
}

pub fn is_tests_bypass_visibility_context(env: &Env) -> bool {
    // (Without classes to bypass the visibility for, the answer is `false`
    // whatever the class: the copy of its name is skipped.)
    if env.genv.tcopt.tco_permits_bypassing_visibility.is_empty() {
        return false;
    }
    match typing_env::get_self_id(env) {
        None => false,
        Some(self_id) => typing_env::get_tcopt(env)
            .tco_permits_bypassing_visibility
            .iter()
            .any(|super_id| has_ancestor_including_req_refl(env, &self_id, super_id)),
    }
}

/// Alternative implementation of is_supportdyn (compare below) that makes use of tyvar
/// bounds e.g. if #0 <: supportdyn<mixed> then function will return true on vec<#0>.
/// Ideally we would have a variant of subtyping that does this, but until that's the
/// case we can use this function to get the same behaviour.
pub fn is_supportdyn_use_tyvar_bounds(env: &Env, ty: &Ty) -> bool {
    with_visited::is_supportdyn(&tvid::set::T::new(), &SSet::new(), env, ty)
}

/// Return true if type definitely is a subtype of supportdyn<mixed>
pub fn is_supportdyn(env: &Env, ty: &Ty) -> bool {
    is_sub_type_for_union(env, ty, &constant_type(ConstantType::SupportdynMixed))
}

/// Wrap supportdyn<_> around a type. Push through intersections
/// and unions, and leave type alone if it is a subtype of dynamic.
pub fn make_supportdyn(r: Reason, env: &mut Env, ty: Ty) -> Ty {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tintersection(tyl) => {
            let r_ = get_reason(&ty).clone();
            let tyl = tyl
                .iter()
                .map(|ty| make_supportdyn(r.clone(), env, ty.clone()))
                .collect();
            mk((r_, Ty_::Tintersection(tyl)))
        }
        Ty_::Tunion(tyl) => {
            let r_ = get_reason(&ty).clone();
            let tyl = tyl
                .iter()
                .map(|ty| make_supportdyn(r.clone(), env, ty.clone()))
                .collect();
            mk((r_, Ty_::Tunion(tyl)))
        }
        _ => {
            if is_supportdyn(env, &ty) {
                ty
            } else {
                make_type::supportdyn(r, ty)
            }
        }
    }
}

pub fn simple_make_supportdyn(r: Reason, env: &mut Env, ty: Ty) -> Ty {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tnewtype(n, _, _) if n == sn::classes::SUPPORT_DYN => ty,
        _ => make_type::supportdyn(r, ty),
    }
}

pub fn map_supportdyn(env: &mut Env, ty: Ty, f: impl FnOnce(&mut Env, Ty) -> Ty) -> Ty {
    let ty = typing_env::expand_type(env, ty);
    match get_node(&ty) {
        Ty_::Tnewtype(name, tyargs, _) if tyargs.len() == 1 && name == sn::classes::SUPPORT_DYN => {
            let r = get_reason(&ty).clone();
            let (_, ty) = strip_supportdyn(env, tyargs[0].clone());
            let ty = f(env, ty);
            make_supportdyn(r, env, ty)
        }
        _ => f(env, ty),
    }
}

/// `mk (r, Tapply ((p, SN.Classes.cSupportDyn), [ty]))`. The position, a
/// `Pos_or_decl.t`, becomes the position of the decl type.
pub fn make_supportdyn_decl_type(p: PosOrDecl, r: R, ty: DeclTy) -> DeclTy {
    DeclTy::apply(
        r,
        Positioned::new(BPos::from(&p), TypeName::new(sn::classes::SUPPORT_DYN)),
        Box::new([ty]),
    )
}

/// Wrap ~ around a type, unless it is already a dynamic or a like type
pub fn make_like(reason: Option<Reason>, env: &Env, ty: Ty) -> Ty {
    // `let (_env, _) = Env.expand_type env ty`: both results are dropped.
    let _ = typing_env::expand_type(&mut env.clone(), ty.clone());
    match get_node(&ty) {
        Ty_::Tdynamic(_) => ty,
        Ty_::Tunion(tyl) if tyl.iter().any(typing_defs::is_dynamic) => ty,
        _ => {
            let r = match reason {
                None => get_reason(&ty).clone(),
                Some(r) => r,
            };
            make_type::locl_like(r, ty)
        }
    }
}

/// Wrap ~ around a type if it is enforced. This is used for returns, property
/// assignment, and default expression typing
pub fn make_like_if_enforced(env: &Env, et_enforced: Enforcement, et_type: Ty) -> Ty {
    match et_enforced {
        Enforcement::Enforced if typing_env::get_support_dynamic_type(env) => {
            let reason = typing_reason::enforced_type(get_pos(&et_type));
            make_like(Some(reason), env, et_type)
        }
        _ => et_type,
    }
}

pub fn is_capability(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tclass((_, name), _, _) if name.starts_with(CAPABILITIES_PREFIX) => true,
        Ty_::Tintersection(tyl) if tyl.is_empty() => false,
        Ty_::Tintersection(tyl) => tyl.iter().all(is_capability),
        Ty_::Tgeneric(s) if coeffects::is_generated_generic(s) => true,
        _ => false,
    }
}

pub fn is_capability_i(ty: &InternalType) -> bool {
    match ty {
        InternalType::LoclType(ty) => is_capability(ty),
        InternalType::ConstraintType(_) => false,
    }
}

pub fn supports_dynamic(
    env: &mut Env,
    ty: Ty,
    on_error: Option<reasons_callback::T>,
) -> Option<typing_error::T> {
    let r = get_reason(&ty).clone();
    sub_type(
        env,
        None,
        None,
        None,
        None,
        ty,
        make_type::supportdyn_mixed(r),
        on_error,
    )
}

pub fn get_case_type_variants_as_type(
    first: &TypedefCaseTypeVariant,
    variants: &[TypedefCaseTypeVariant],
) -> DeclTy {
    // TODO T201569125 audit callers to see if they need to account for where clauses
    let first_ty = &first.hint;
    match variants.last() {
        None => first_ty.clone(),
        Some(TypedefCaseTypeVariant { hint: last_ty, .. }) => {
            let pos = crate::pos_or_decl::btw(
                &PosOrDecl::from(first_ty.reason().pos().clone()),
                &PosOrDecl::from(last_ty.reason().pos().clone()),
            );
            let mut tyl = vec![first_ty.clone()];
            tyl.extend(variants.iter().map(|variant| variant.hint.clone()));
            decl_union(R::hint(BPos::from(&pos)), tyl)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn class(name: &str, tyl: Vec<Ty>) -> Ty {
        mk((
            typing_reason::none(),
            Ty_::Tclass(
                (Pos::NONE, name.to_string()),
                crate::typing_defs_core::nonexact(),
                tyl,
            ),
        ))
    }

    #[test]
    fn capabilities() {
        let cap = class("\\HH\\Capabilities\\WriteProperty", vec![]);
        let not_cap = class("\\C", vec![]);
        assert!(is_capability(&cap));
        assert!(!is_capability(&not_cap));
        let inter = |tyl| mk((typing_reason::none(), Ty_::Tintersection(tyl)));
        assert!(!is_capability(&inter(vec![])));
        assert!(is_capability(&inter(vec![cap.clone(), cap.clone()])));
        assert!(!is_capability(&inter(vec![cap.clone(), not_cap])));
        let generated = mk((
            typing_reason::none(),
            Ty_::Tgeneric("T/[ctx $f]".to_string()),
        ));
        assert!(is_capability(&generated));
        assert!(is_capability_i(&InternalType::LoclType(cap)));
    }

    #[test]
    fn classes() {
        assert!(is_class(&class("\\C", vec![])));
        assert!(!is_class(&prim(Tprim::Tint)));
        assert!(is_class_i(&InternalType::LoclType(class("\\C", vec![]))));
    }

    #[test]
    fn unwrap_class_types() {
        let name = Positioned::new(BPos::none(), TypeName::new("\\C"));
        let int = DeclTy::prim(R::none(), Tprim::Tint);
        let ty = DeclTy::apply(R::none(), name.clone(), Box::new([int.clone()]));
        let (_, id, args) = unwrap_class_type(&ty);
        assert_eq!(id, name);
        assert_eq!(args, vec![int.clone()]);
        assert!(try_unwrap_class_type(&int).is_none());
        assert!(try_unwrap_class_type(&ty).is_some());
    }

    #[test]
    #[should_panic(expected = "unwrap_class_type got non-class")]
    fn unwrap_class_type_of_a_non_class_raises() {
        unwrap_class_type(&DeclTy::prim(R::none(), Tprim::Tint));
    }

    #[test]
    fn generics_in_decl_types() {
        let t = DeclTy::generic(R::none(), TypeName::new("T"));
        let ty = DeclTy::apply(
            R::none(),
            Positioned::new(BPos::none(), TypeName::new("\\C")),
            Box::new([DeclTy::prim(R::none(), Tprim::Tint), t]),
        );
        assert!(contains_generic_decl(&ty).is_some());
        assert!(contains_generic_decl(&DeclTy::prim(R::none(), Tprim::Tint)).is_none());
        assert!(!contains_tvar_decl(&ty));
    }

    #[test]
    fn supportdyn_decl_type() {
        let int = DeclTy::prim(R::none(), Tprim::Tint);
        let ty = make_supportdyn_decl_type(Pos::NONE, R::none(), int.clone());
        let (_, id, args) = unwrap_class_type(&ty);
        assert_eq!(id.id_ref().as_str(), sn::classes::SUPPORT_DYN);
        assert_eq!(args, vec![int]);
    }

    #[test]
    fn case_type_variants() {
        let variant = |ty| TypedefCaseTypeVariant {
            hint: ty,
            where_constraints: Box::new([]),
        };
        let int = DeclTy::prim(R::none(), Tprim::Tint);
        let float = DeclTy::prim(R::none(), Tprim::Tfloat);
        assert_eq!(get_case_type_variants_as_type(&variant(int.clone()), &[]), int);
        let union = get_case_type_variants_as_type(&variant(int.clone()), &[variant(float.clone())]);
        match union.node_ref() {
            d::Ty_::Tunion(tyl) => assert_eq!(tyl.to_vec(), vec![int, float]),
            _ => panic!("not a union"),
        }
    }

    #[test]
    fn default_fun_params() {
        let fp = default_fun_param(true, None, prim(Tprim::Tint));
        assert!(crate::typing_defs_core::get_fp_readonly(&fp));
        assert!(!crate::typing_defs_core::get_fp_is_optional(&fp));
        assert_eq!(fp.pos, Pos::NONE);
        assert!(fp.name.is_none());
    }

    #[test]
    fn approx_equality() {
        assert!(equal_approx(Approx::ApproxUp, Approx::ApproxUp));
        assert!(!equal_approx(Approx::ApproxUp, Approx::ApproxDown));
    }
}
