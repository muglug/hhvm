// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The types of the *locl* phase: `locl_ty` and what it is made of
//! (`typing_defs_core.ml`), constraint types and `internal_type`
//! (`typing_defs_constraints.ml`), with the comparison functions of both
//! files.
//!
//! **These definitions are provisional**, and only compiled without the
//! `port` feature. `oxidized::typing_defs_core` only has the decl phase: `Ty_`
//! there has no `Tvar`, `Tnewtype`, `Tdependent`, `Tclass`, `Tneg` or `Tlabel`,
//! its reasons are decl reasons, and the constraint types do not exist at all
//! (they are `[@@oxidize.exclude]`d in OCaml). The printer needs them, so they
//! were written here, named the way `oxidized` names the decl ones (same
//! constructor and field names wherever the OCaml type is shared between the
//! phases).
//!
//! The ports of `typing_defs_core.ml` and `typing_defs_constraints.ml`
//! (`crate::typing_defs_core`, `crate::typing_defs_constraints`) now define
//! the same types, with the same names; with the `port` feature,
//! `typing_print::locl` is those two modules and this file is not compiled.
//! It can be deleted when the feature is the default. The printer only relies
//! on the shape of the types (it has its own copies of the few functions of
//! `Typing_defs` that it needs), so nothing else has to change.

use std::cmp::Ordering;

use oxidized::ast_defs;
use oxidized::ast_defs::ConstraintKind;
use oxidized::ast_defs::Tprim;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::s_map::SMap;
use oxidized::t_shape_map::TShapeMap;
use oxidized::tany_sentinel::TanySentinel;
pub use oxidized::typing_defs_core::PosId;
pub use oxidized::typing_defs_core::TshapeFieldName;
pub use oxidized::typing_defs_core::TypeOrigin;
pub use oxidized::typing_defs_core::UserAttribute;
pub use oxidized::typing_defs_core::UserAttributeParam;
use oxidized::typing_defs_flags::FunParamFlags;
use oxidized::typing_defs_flags::FunTypeFlags;

use crate::typing_reason as reason;
use crate::typing_reason::ExpressionId;
use crate::typing_reason::Tvid;

/// `dependent_type`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DependentType {
    /// A reference to some expression. For example:
    ///
    ///  $x->foo()
    ///
    ///  The expression $x would have a reference ident
    ///  The expression $x->foo() would have a different one
    DTexpr(ExpressionId),
}

/// `locl_ty tparam`
#[derive(Clone, Debug)]
pub struct Tparam {
    pub variance: ast_defs::Variance,
    pub name: PosId,
    pub constraints: Vec<(ConstraintKind, Ty)>,
    pub reified: ast_defs::ReifyKind,
    pub user_attributes: Vec<UserAttribute>,
}

/// `locl_ty where_constraint`
#[derive(Clone, Debug)]
pub struct WhereConstraint(pub Ty, pub ConstraintKind, pub Ty);

/// `locl_ty capability`
#[derive(Clone, Debug)]
pub enum Capability {
    /// Should not be used for lambda inference
    CapDefaults(PosOrDecl),
    CapTy(Ty),
}

/// `locl_ty fun_implicit_params`
#[derive(Clone, Debug)]
pub struct FunImplicitParams {
    pub capability: Capability,
}

/// `locl_ty fun_param`
#[derive(Clone, Debug)]
pub struct FunParam {
    pub pos: PosOrDecl,
    pub name: Option<String>,
    pub type_: Ty,
    pub flags: FunParamFlags,
    pub def_value: Option<String>,
}

pub type FunParams = Vec<FunParam>;

/// `locl_ty fun_type`: the type of a function AND a method
#[derive(Clone, Debug)]
pub struct FunType {
    pub tparams: Vec<Tparam>,
    pub where_constraints: Vec<WhereConstraint>,
    pub params: FunParams,
    pub implicit_params: FunImplicitParams,
    pub ret: Ty,
    pub flags: FunTypeFlags,
    pub instantiated: bool,
}

/// `locl_ty`
#[derive(Clone, Debug)]
pub struct Ty(pub reason::T, pub std::rc::Rc<Ty_>);

/// `type_tag_generic`
#[derive(Clone, Debug)]
pub enum TypeTagGeneric {
    Filled(Ty),
    Wildcard(isize),
}

/// `type_tag`
#[derive(Clone, Debug)]
pub enum TypeTag {
    BoolTag,
    IntTag,
    ArraykeyTag,
    FloatTag,
    NumTag,
    ResourceTag,
    NullTag,
    ClassTag(ast_defs::Id_, Vec<TypeTagGeneric>),
    EnumTag(ast_defs::Id_),
    GenericTag { name: String, from_like: bool },
}

/// `shape_field_predicate`
#[derive(Clone, Debug)]
pub struct ShapeFieldPredicate {
    pub optional: bool,
    pub predicate: TypePredicate,
}

/// `shape_predicate`
#[derive(Clone, Debug)]
pub struct ShapePredicate {
    pub allows_unknown_fields: bool,
    pub fields: TShapeMap<ShapeFieldPredicate>,
}

/// `tuple_predicate`
#[derive(Clone, Debug)]
pub struct TuplePredicate {
    pub required: Vec<TypePredicate>,
}

/// `type_predicate_`
#[derive(Clone, Debug)]
pub enum TypePredicate_ {
    IsTag(TypeTag),
    IsTupleOf(TuplePredicate),
    IsShapeOf(ShapePredicate),
    IsUnionOf(Vec<TypePredicate>),
    IsNot(Box<TypePredicate>),
}

/// `type_predicate`
#[derive(Clone, Debug)]
pub struct TypePredicate(pub reason::T, pub TypePredicate_);

/// `locl_phase shape_field_type`
#[derive(Clone, Debug)]
pub struct ShapeFieldType {
    pub optional: bool,
    pub ty: Ty,
}

/// `locl_phase ty_`: the constructors that exist in the locl phase.
#[derive(Clone, Debug)]
pub enum Ty_ {
    Tany(TanySentinel),
    Tnonnull,
    /// The optional Tvid.t is a "shadow type variable" used for dynamic
    /// inference.
    Tdynamic(Option<Tvid>),
    /// Nullable, called "option" in the ML parlance.
    Toption(Ty),
    /// All the primitive types: int, string, void, etc.
    Tprim(Tprim),
    /// A wrapper around fun_type, which contains the full type information for a
    /// function, method, lambda, etc.
    Tfun(FunType),
    /// A wrapper around tuple_type, which contains information about tuple elements
    Ttuple(TupleType),
    Tshape(ShapeType),
    /// The type of a generic parameter. The constraints on a generic parameter
    /// are accessed through the lenv.tpenv component of the environment.
    Tgeneric(String),
    /// Union type.
    Tunion(Vec<Ty>),
    Tintersection(Vec<Ty>),
    /// Tvec_or_dict (ty1, ty2) => "vec_or_dict<ty1, ty2>"
    TvecOrDict(Ty, Ty),
    /// Name of class, name of type const, remaining names of type consts
    Taccess(TaccessType),
    /// A type of a class pointer, class<T>.
    TclassPtr(Ty),
    /// A type variable (not to be confused with a type parameter). It
    /// represents a type that we are trying to infer.
    Tvar(Tvid),
    /// The type of an opaque type or enum. Outside their defining files or
    /// when they represent enums, they are "opaque", which means that they
    /// only unify with themselves. Within a file, uses of newtypes are
    /// expanded to their definitions (unless the newtype is an enum).
    /// The last argument is the upper bound.
    Tnewtype(String, Vec<Ty>, Ty),
    /// See dependent_type
    Tdependent(DependentType, Ty),
    /// An instance of a class or interface, ty list are the arguments.
    /// If exact=Exact, then this represents instances of *exactly* this class.
    /// If exact=Nonexact, this also includes subclasses.
    Tclass(PosId, Exact, Vec<Ty>),
    /// The negation of the type predicate
    Tneg(TypePredicate),
    /// The type of the label expression #ID
    Tlabel(String),
}

/// `locl_phase taccess_type`
#[derive(Clone, Debug)]
pub struct TaccessType(pub Ty, pub PosId);

/// `exact`
#[derive(Clone, Debug)]
pub enum Exact {
    Exact,
    Nonexact(ClassRefinement),
}

/// `locl_phase class_refinement`
#[derive(Clone, Debug, Default)]
pub struct ClassRefinement {
    pub cr_consts: SMap<RefinedConst>,
}

/// `locl_phase refined_const`
#[derive(Clone, Debug)]
pub struct RefinedConst {
    pub bound: RefinedConstBound,
    pub is_ctx: bool,
}

/// `locl_phase refined_const_bound`
#[derive(Clone, Debug)]
pub enum RefinedConstBound {
    /// for `=` constraints
    TRexact(Ty),
    /// for `as` or `super` constraints
    TRloose(RefinedConstBounds),
}

/// `locl_phase refined_const_bounds`
#[derive(Clone, Debug)]
pub struct RefinedConstBounds {
    pub lower: Vec<Ty>,
    pub upper: Vec<Ty>,
}

/// `locl_phase shape_type_simple`
#[derive(Clone, Debug)]
pub struct ShapeTypeSimple {
    pub origin: TypeOrigin,
    pub unknown_value: Ty,
    pub fields: TShapeMap<ShapeFieldType>,
}

/// `locl_phase shape_type_splat`
#[derive(Clone, Debug)]
pub struct ShapeTypeSplat {
    pub ss_elems: Vec<Ty>,
}

/// `locl_phase shape_type`
#[derive(Clone, Debug)]
pub enum ShapeType {
    ShapeSimple(ShapeTypeSimple),
    ShapeSplat(ShapeTypeSplat),
}

/// `locl_phase tuple_type`
#[derive(Clone, Debug)]
pub struct TupleType {
    pub required: Vec<Ty>,
    pub optional: Vec<Ty>,
    pub extra: TupleExtra,
}

/// `locl_phase tuple_extra`
#[derive(Clone, Debug)]
pub enum TupleExtra {
    Tvariadic(Ty),
    Tsplat(Ty),
}

impl Ty {
    /// `mk`
    pub fn mk(r: reason::T, node: Ty_) -> Self {
        Ty(r, std::rc::Rc::new(node))
    }

    pub fn get_reason(&self) -> &reason::T {
        &self.0
    }

    pub fn get_node(&self) -> &Ty_ {
        &self.1
    }
}

/// `nonexact`
pub fn nonexact() -> Exact {
    Exact::Nonexact(ClassRefinement::default())
}

/// `Class_refinement.is_empty`
pub fn class_refinement_is_empty(r: &ClassRefinement) -> bool {
    r.cr_consts.is_empty()
}

/// `refined_const_kind_str`
pub fn refined_const_kind_str(is_ctx: bool) -> &'static str {
    if is_ctx { "ctx" } else { "type" }
}

// ~~ typing_defs_constraints.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `destructure_kind`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DestructureKind {
    ListDestructure,
    SplatUnpack,
}

/// `destructure`
#[derive(Clone, Debug)]
pub struct Destructure {
    pub required: Vec<Ty>,
    pub optional: Vec<Ty>,
    pub variadic: Option<Ty>,
    pub kind: DestructureKind,
}

/// `has_member_method`
#[derive(Clone, Debug)]
pub struct HasMemberMethod {
    pub explicit_targs: Vec<nast::Targ>,
    pub args_pos: Vec<Pos>,
}

/// `has_member`
#[derive(Clone, Debug)]
pub struct HasMember {
    pub name: oxidized::aast_defs::Sid,
    pub type_: Ty,
    pub class_id: nast::ClassId_,
    pub method: Option<HasMemberMethod>,
}

/// `ci_access_kind`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CiAccessKind {
    CiNormal,
    CiLhsOfNullCoalesce,
    CiDestructureOptional,
}

/// `can_index`
#[derive(Clone, Debug)]
pub struct CanIndex {
    pub key: Ty,
    pub val: Ty,
    pub index_expr: nast::Expr,
    pub access_kind: CiAccessKind,
    pub expr_pos: Pos,
    pub array_pos: Pos,
    pub index_pos: Pos,
}

/// `can_index_assign`: `$source[key] = write` update the array to type val
#[derive(Clone, Debug)]
pub struct CanIndexAssign {
    pub key: Ty,
    pub write: Ty,
    pub val: Ty,
    pub index_expr: nast::Expr,
    pub expr_pos: Pos,
    pub array_pos: Pos,
    pub index_pos: Pos,
    pub write_pos: Pos,
}

/// `can_traverse`
#[derive(Clone, Debug)]
pub struct CanTraverse {
    pub key: Option<Ty>,
    pub val: Ty,
    pub is_await: bool,
    pub reason: reason::T,
}

/// `has_type_member`
#[derive(Clone, Debug)]
pub struct HasTypeMember {
    pub id: String,
    pub lower: Ty,
    pub upper: Ty,
}

/// `constraint_type_`
#[derive(Clone, Debug)]
pub enum ConstraintType_ {
    ThasMember(HasMember),
    ThasTypeMember(HasTypeMember),
    ThasConst {
        name: String,
        ty: Ty,
    },
    TcanIndex(CanIndex),
    TcanIndexAssign(CanIndexAssign),
    TcanTraverse(CanTraverse),
    Tdestructure(Destructure),
    TtypeSwitch {
        predicate: TypePredicate,
        ty_true: Ty,
        ty_false: Ty,
    },
}

/// `constraint_type`
#[derive(Clone, Debug)]
pub struct ConstraintType(pub reason::T, pub std::rc::Rc<ConstraintType_>);

/// `internal_type`
#[derive(Clone, Debug)]
pub enum InternalType {
    LoclType(Ty),
    ConstraintType(ConstraintType),
}

// ~~ helpers of typing_defs.ml ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Typing_defs.is_nothing`
pub fn is_nothing(ty: &Ty) -> bool {
    matches!(ty.get_node(), Ty_::Tunion(tyl) if tyl.is_empty())
}

/// `Typing_defs.is_dynamic`
pub fn is_dynamic(ty: &Ty) -> bool {
    matches!(ty.get_node(), Ty_::Tdynamic(_))
}

/// `Typing_defs.DependentKind.to_string`
pub fn dependent_kind_to_string(dep: DependentType) -> String {
    match dep {
        DependentType::DTexpr(i) => reason::expression_id_display(i),
    }
}

/// `Typing_defs.DependentKind.is_generic_dep_ty`
pub fn is_generic_dep_ty(s: &str) -> bool {
    s.contains("::") || s == naming_special_names_rust::typehints::THIS
}

// ~~ comparison ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `ty_con_ordinal_` (of the constructors of the locl phase)
fn ty_con_ordinal_(ty: &Ty_) -> isize {
    use Ty_::*;
    match ty {
        Tany(_) => 0,
        Toption(t) => match t.get_node() {
            Tnonnull => 1,
            _ => 4,
        },
        Tnonnull => 2,
        Tdynamic(_) => 3,
        Tprim(_) => 5,
        Tfun(_) => 6,
        Ttuple(_) => 7,
        Tshape(_) => 8,
        Tvar(_) => 9,
        Tgeneric(_) => 11,
        Tunion(_) => 13,
        Tintersection(_) => 14,
        Taccess(_) => 24,
        TvecOrDict(..) => 25,
        TclassPtr(_) => 26,
        Tnewtype(..) => 201,
        Tdependent(..) => 202,
        Tclass(..) => 204,
        Tneg(_) => 205,
        Tlabel(_) => 206,
    }
}

/// `equal_type_origin`: the position of the alias is ignored.
fn equal_type_origin(orig1: &TypeOrigin, orig2: &TypeOrigin) -> bool {
    match (orig1, orig2) {
        (TypeOrigin::MissingOrigin, TypeOrigin::MissingOrigin) => true,
        (TypeOrigin::FromAlias(a1, _), TypeOrigin::FromAlias(a2, _)) => a1 == a2,
        _ => false,
    }
}

/// `same_type_origin`
pub fn same_type_origin(orig1: &TypeOrigin, orig2: &TypeOrigin) -> bool {
    match orig1 {
        TypeOrigin::MissingOrigin => false,
        _ => equal_type_origin(orig1, orig2),
    }
}

#[allow(non_snake_case)]
fn type_predicate__con_ordinal(p: &TypePredicate_) -> isize {
    match p {
        TypePredicate_::IsTag(_) => 0,
        TypePredicate_::IsTupleOf(_) => 1,
        TypePredicate_::IsShapeOf(_) => 2,
        TypePredicate_::IsUnionOf(_) => 3,
        TypePredicate_::IsNot(_) => 4,
    }
}

fn type_tag_con_ordinal(tag: &TypeTag) -> isize {
    match tag {
        TypeTag::BoolTag => 0,
        TypeTag::IntTag => 1,
        TypeTag::ArraykeyTag => 3,
        TypeTag::FloatTag => 4,
        TypeTag::NumTag => 5,
        TypeTag::ResourceTag => 6,
        TypeTag::NullTag => 7,
        TypeTag::ClassTag(..) => 8,
        TypeTag::EnumTag(_) => 9,
        TypeTag::GenericTag { .. } => 10,
    }
}

/// The comparison of two constructor ordinals.
fn ordinals(o1: isize, o2: isize) -> Ordering {
    (o1 - o2).cmp(&0)
}

/// `List.compare`
fn list_compare<A>(cmp: impl Fn(&A, &A) -> Ordering, l1: &[A], l2: &[A]) -> Ordering {
    let mut i1 = l1.iter();
    let mut i2 = l2.iter();
    loop {
        match (i1.next(), i2.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(x1), Some(x2)) => match cmp(x1, x2) {
                Ordering::Equal => {}
                c => return c,
            },
        }
    }
}

/// `Map.compare`: the bindings of both maps, in order, compared by key and
/// then by value.
fn map_compare<'a, K: Ord + 'a, V: 'a>(
    cmp: impl Fn(&V, &V) -> Ordering,
    m1: impl Iterator<Item = (&'a K, &'a V)>,
    m2: impl Iterator<Item = (&'a K, &'a V)>,
) -> Ordering {
    let mut i1 = m1;
    let mut i2 = m2;
    loop {
        match (i1.next(), i2.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some((k1, v1)), Some((k2, v2))) => match k1.cmp(k2).then_with(|| cmp(v1, v2)) {
                Ordering::Equal => {}
                c => return c,
            },
        }
    }
}

/// `ty__compare`.
///
/// Compare two types syntactically, ignoring reason information and other
/// small differences that do not affect type inference behaviour. This
/// comparison function can be used to construct tree-based sets of types,
/// or to compare two types for "exact" equality.
/// Note that this function does *not* expand type variables, or type
/// aliases.
/// But if ty_compare ty1 ty2 = 0, then the types must not be distinguishable
/// by any typing rules.
#[allow(non_snake_case)]
pub fn ty__compare(normalize_lists: bool, ty_1: &Ty_, ty_2: &Ty_) -> Ordering {
    use Ty_::*;
    // The functions that the OCaml defines inside `ty__compare` keep the
    // `normalize_lists` they were entered with; the ones defined outside of it
    // (`ft_params_compare`, `exact_compare`, `tyl_compare ~sort:false`) are
    // called without it, that is with `false`.
    let ty_compare = |ty1: &Ty, ty2: &Ty| ty_compare(normalize_lists, ty1, ty2);
    match (ty_1, ty_2) {
        (Tprim(ty1), Tprim(ty2)) => ty1.cmp(ty2),
        (Toption(ty), Toption(ty2)) => ty_compare(ty, ty2),
        (TvecOrDict(tk, tv), TvecOrDict(tk2, tv2)) => {
            ty_compare(tk, tk2).then_with(|| ty_compare(tv, tv2))
        }
        (Tfun(fty), Tfun(fty2)) => tfun_compare(normalize_lists, fty, fty2),
        (Tunion(tyl1), Tunion(tyl2)) | (Tintersection(tyl1), Tintersection(tyl2)) => {
            tyl_compare(normalize_lists, normalize_lists, tyl1, tyl2)
        }
        (Ttuple(t1), Ttuple(t2)) => tuple_type_compare(normalize_lists, t1, t2),
        (Tgeneric(n1), Tgeneric(n2)) => n1.cmp(n2),
        (Tnewtype(id, tyl, cstr1), Tnewtype(id2, tyl2, cstr2)) => id
            .cmp(id2)
            .then_with(|| tyl_compare(false, false, tyl, tyl2))
            .then_with(|| ty_compare(cstr1, cstr2)),
        (Tdependent(d1, cstr1), Tdependent(d2, cstr2)) => {
            d1.cmp(d2).then_with(|| ty_compare(cstr1, cstr2))
        }
        // An instance of a class or interface, ty list are the arguments
        (Tclass(id, exact, tyl), Tclass(id2, exact2, tyl2)) => (id.1)
            .cmp(&id2.1)
            .then_with(|| tyl_compare(false, false, tyl, tyl2))
            .then_with(|| exact_compare(exact, exact2)),
        (Tshape(s1), Tshape(s2)) => shape_type_compare(normalize_lists, s1, s2),
        (Tvar(v1), Tvar(v2)) => v1.cmp(v2),
        (Taccess(TaccessType(ty1, id1)), Taccess(TaccessType(ty2, id2))) => {
            ty_compare(ty1, ty2).then_with(|| (id1.1).cmp(&id2.1))
        }
        (Tneg(neg1), Tneg(neg2)) => compare_type_predicate(neg1, neg2),
        (Tnonnull, Tnonnull) => Ordering::Equal,
        (Tdynamic(_), Tdynamic(_)) => Ordering::Equal,
        (Tlabel(name1), Tlabel(name2)) => name1.cmp(name2),
        (TclassPtr(ty1), TclassPtr(ty2)) => ty_compare(ty1, ty2),
        (
            Tprim(_)
            | Toption(_)
            | TvecOrDict(..)
            | Tfun(_)
            | Tintersection(_)
            | Tunion(_)
            | Ttuple(_)
            | Tgeneric(_)
            | Tnewtype(..)
            | Tdependent(..)
            | Tclass(..)
            | Tshape(_)
            | Tvar(_)
            | Tnonnull
            | Tdynamic(_)
            | Taccess(_)
            | Tany(_)
            | Tneg(_)
            | Tlabel(_)
            | TclassPtr(_),
            _,
        ) => ordinals(ty_con_ordinal_(ty_1), ty_con_ordinal_(ty_2)),
    }
}

fn shape_field_type_compare(
    normalize_lists: bool,
    sft1: &ShapeFieldType,
    sft2: &ShapeFieldType,
) -> Ordering {
    ty_compare(normalize_lists, &sft1.ty, &sft2.ty).then_with(|| sft1.optional.cmp(&sft2.optional))
}

fn shape_type_compare(normalize_lists: bool, s1: &ShapeType, s2: &ShapeType) -> Ordering {
    match (s1, s2) {
        (ShapeType::ShapeSimple(_), ShapeType::ShapeSplat(_)) => Ordering::Less,
        (ShapeType::ShapeSplat(_), ShapeType::ShapeSimple(_)) => Ordering::Greater,
        (ShapeType::ShapeSplat(e1), ShapeType::ShapeSplat(e2)) => {
            tyl_compare(false, false, &e1.ss_elems, &e2.ss_elems)
        }
        (ShapeType::ShapeSimple(s1), ShapeType::ShapeSimple(s2)) => {
            if same_type_origin(&s1.origin, &s2.origin) {
                Ordering::Equal
            } else {
                // (The OCaml first tests physical equality of the fields and
                // of the unknown value, which only saves work.)
                ty_compare(normalize_lists, &s1.unknown_value, &s2.unknown_value).then_with(|| {
                    map_compare(
                        |f1, f2| shape_field_type_compare(normalize_lists, f1, f2),
                        s1.fields.iter(),
                        s2.fields.iter(),
                    )
                })
            }
        }
    }
}

fn tuple_extra_compare(normalize_lists: bool, t1: &TupleExtra, t2: &TupleExtra) -> Ordering {
    match (t1, t2) {
        (TupleExtra::Tvariadic(_), TupleExtra::Tsplat(_)) => Ordering::Less,
        (TupleExtra::Tsplat(_), TupleExtra::Tvariadic(_)) => Ordering::Greater,
        (TupleExtra::Tsplat(t1), TupleExtra::Tsplat(t2)) => ty_compare(normalize_lists, t1, t2),
        (TupleExtra::Tvariadic(t1), TupleExtra::Tvariadic(t2)) => {
            ty_compare(normalize_lists, t1, t2)
        }
    }
}

fn tuple_type_compare(normalize_lists: bool, t1: &TupleType, t2: &TupleType) -> Ordering {
    let ty_compare = |ty1: &Ty, ty2: &Ty| ty_compare(normalize_lists, ty1, ty2);
    list_compare(ty_compare, &t1.required, &t2.required)
        .then_with(|| list_compare(ty_compare, &t1.optional, &t2.optional))
        .then_with(|| tuple_extra_compare(normalize_lists, &t1.extra, &t2.extra))
}

fn user_attribute_param_compare(p1: &UserAttributeParam, p2: &UserAttributeParam) -> Ordering {
    fn dest_user_attribute_param(p: &UserAttributeParam) -> (isize, &[u8]) {
        match p {
            UserAttributeParam::Classname(s) => (0, s.as_bytes()),
            UserAttributeParam::EnumClassLabel(s) => (1, s.as_bytes()),
            UserAttributeParam::String(s) => (2, s.as_slice()),
            UserAttributeParam::Int(i) => (3, i.as_bytes()),
        }
    }
    let (id1, s1) = dest_user_attribute_param(p1);
    let (id2, s2) = dest_user_attribute_param(p2);
    id1.cmp(&id2).then_with(|| s1.cmp(s2))
}

fn user_attribute_compare(ua1: &UserAttribute, ua2: &UserAttribute) -> Ordering {
    (ua1.name.1)
        .cmp(&ua2.name.1)
        .then_with(|| list_compare(user_attribute_param_compare, &ua1.params, &ua2.params))
}

fn user_attributes_compare(ual1: &[UserAttribute], ual2: &[UserAttribute]) -> Ordering {
    list_compare(user_attribute_compare, ual1, ual2)
}

fn constraint_compare(
    normalize_lists: bool,
    (ck1, ty1): &(ConstraintKind, Ty),
    (ck2, ty2): &(ConstraintKind, Ty),
) -> Ordering {
    ck1.cmp(ck2)
        .then_with(|| ty_compare(normalize_lists, ty1, ty2))
}

fn tparam_compare(normalize_lists: bool, tp1: &Tparam, tp2: &Tparam) -> Ordering {
    // Type parameters on functions are always marked invariant
    (tp1.name.1)
        .cmp(&tp2.name.1)
        .then_with(|| {
            list_compare(
                |c1, c2| constraint_compare(normalize_lists, c1, c2),
                &tp1.constraints,
                &tp2.constraints,
            )
        })
        .then_with(|| user_attributes_compare(&tp1.user_attributes, &tp2.user_attributes))
        .then_with(|| tp1.reified.cmp(&tp2.reified))
}

fn where_constraint_compare(
    normalize_lists: bool,
    WhereConstraint(ty1a, ck1, ty1b): &WhereConstraint,
    WhereConstraint(ty2a, ck2, ty2b): &WhereConstraint,
) -> Ordering {
    ck1.cmp(ck2)
        .then_with(|| ty_compare(normalize_lists, ty1a, ty2a))
        .then_with(|| ty_compare(normalize_lists, ty1b, ty2b))
}

fn capability_compare(normalize_lists: bool, cap1: &Capability, cap2: &Capability) -> Ordering {
    match (cap1, cap2) {
        (Capability::CapDefaults(_), Capability::CapDefaults(_)) => Ordering::Equal,
        (Capability::CapDefaults(_), Capability::CapTy(_)) => Ordering::Less,
        (Capability::CapTy(_), Capability::CapDefaults(_)) => Ordering::Greater,
        (Capability::CapTy(ty1), Capability::CapTy(ty2)) => ty_compare(normalize_lists, ty1, ty2),
    }
}

fn tfun_compare(normalize_lists: bool, fty1: &FunType, fty2: &FunType) -> Ordering {
    ty_compare(normalize_lists, &fty1.ret, &fty2.ret)
        .then_with(|| ft_params_compare(false, &fty1.params, &fty2.params))
        .then_with(|| {
            list_compare(
                |tp1, tp2| tparam_compare(normalize_lists, tp1, tp2),
                &fty1.tparams,
                &fty2.tparams,
            )
        })
        .then_with(|| {
            list_compare(
                |c1, c2| where_constraint_compare(normalize_lists, c1, c2),
                &fty1.where_constraints,
                &fty2.where_constraints,
            )
        })
        .then_with(|| fty1.flags.cmp(&fty2.flags))
        .then_with(|| {
            capability_compare(
                normalize_lists,
                &fty1.implicit_params.capability,
                &fty2.implicit_params.capability,
            )
        })
        .then_with(|| fty1.instantiated.cmp(&fty2.instantiated))
}

/// `compare_type_predicate`
pub fn compare_type_predicate(
    TypePredicate(_, p1): &TypePredicate,
    TypePredicate(_, p2): &TypePredicate,
) -> Ordering {
    use TypePredicate_::*;
    match (p1, p2) {
        (IsTag(tag1), IsTag(tag2)) => compare_type_tag(tag1, tag2),
        (IsTupleOf(tp1), IsTupleOf(tp2)) => compare_tuple_predicate(tp1, tp2),
        (IsShapeOf(sp1), IsShapeOf(sp2)) => compare_shape_predicate(sp1, sp2),
        (IsNot(p1), IsNot(p2)) => compare_type_predicate(p1, p2),
        // (This is also where two `IsUnionOf` end up: they compare equal.)
        _ => ordinals(
            type_predicate__con_ordinal(p1),
            type_predicate__con_ordinal(p2),
        ),
    }
}

fn compare_type_tag_generic(g1: &TypeTagGeneric, g2: &TypeTagGeneric) -> Ordering {
    match (g1, g2) {
        (TypeTagGeneric::Wildcard(id1), TypeTagGeneric::Wildcard(id2)) => id1.cmp(id2),
        (TypeTagGeneric::Filled(ty1), TypeTagGeneric::Filled(ty2)) => ty_compare(false, ty1, ty2),
        (TypeTagGeneric::Wildcard(_), TypeTagGeneric::Filled(_)) => Ordering::Greater,
        (TypeTagGeneric::Filled(_), TypeTagGeneric::Wildcard(_)) => Ordering::Less,
    }
}

fn compare_type_tag(tag1: &TypeTag, tag2: &TypeTag) -> Ordering {
    use TypeTag::*;
    match (tag1, tag2) {
        (BoolTag, BoolTag)
        | (IntTag, IntTag)
        | (ArraykeyTag, ArraykeyTag)
        | (FloatTag, FloatTag)
        | (NumTag, NumTag)
        | (ResourceTag, ResourceTag)
        | (NullTag, NullTag) => Ordering::Equal,
        (ClassTag(id1, args1), ClassTag(id2, args2)) => id1
            .cmp(id2)
            .then_with(|| list_compare(compare_type_tag_generic, args1, args2)),
        (EnumTag(id1), EnumTag(id2)) => id1.cmp(id2),
        (
            GenericTag {
                name: n1,
                from_like: b1,
            },
            GenericTag {
                name: n2,
                from_like: b2,
            },
        ) => n1.cmp(n2).then_with(|| b1.cmp(b2)),
        _ => ordinals(type_tag_con_ordinal(tag1), type_tag_con_ordinal(tag2)),
    }
}

fn compare_tuple_predicate(tp1: &TuplePredicate, tp2: &TuplePredicate) -> Ordering {
    list_compare(compare_type_predicate, &tp1.required, &tp2.required)
}

fn compare_shape_predicate(sp1: &ShapePredicate, sp2: &ShapePredicate) -> Ordering {
    map_compare(
        compare_shape_field_predicate,
        sp1.fields.iter(),
        sp2.fields.iter(),
    )
    .then_with(|| sp1.allows_unknown_fields.cmp(&sp2.allows_unknown_fields))
}

fn compare_shape_field_predicate(p1: &ShapeFieldPredicate, p2: &ShapeFieldPredicate) -> Ordering {
    compare_type_predicate(&p1.predicate, &p2.predicate)
        .then_with(|| p1.optional.cmp(&p2.optional))
}

/// `ty_compare ?normalize_lists`
pub fn ty_compare(normalize_lists: bool, ty1: &Ty, ty2: &Ty) -> Ordering {
    ty__compare(normalize_lists, ty1.get_node(), ty2.get_node())
}

/// `tyl_compare ~sort ?normalize_lists`
pub fn tyl_compare(sort: bool, normalize_lists: bool, tyl1: &[Ty], tyl2: &[Ty]) -> Ordering {
    let cmp = |ty1: &&Ty, ty2: &&Ty| ty_compare(normalize_lists, ty1, ty2);
    let mut tyl1: Vec<&Ty> = tyl1.iter().collect();
    let mut tyl2: Vec<&Ty> = tyl2.iter().collect();
    if sort {
        // `List.sort ~compare:ty_compare`: a stable sort, without
        // `normalize_lists`.
        tyl1.sort_by(|ty1, ty2| ty_compare(false, ty1, ty2));
        tyl2.sort_by(|ty1, ty2| ty_compare(false, ty1, ty2));
    }
    list_compare(cmp, &tyl1, &tyl2)
}

fn ft_param_compare(normalize_lists: bool, param1: &FunParam, param2: &FunParam) -> Ordering {
    ty_compare(normalize_lists, &param1.type_, &param2.type_)
        .then_with(|| param1.flags.cmp(&param2.flags))
        .then_with(|| {
            if param1.flags.is_named() {
                // Option.compare String.compare
                param1.name.cmp(&param2.name)
            } else {
                Ordering::Equal
            }
        })
}

fn ft_params_compare(normalize_lists: bool, params1: &[FunParam], params2: &[FunParam]) -> Ordering {
    list_compare(
        |p1, p2| ft_param_compare(normalize_lists, p1, p2),
        params1,
        params2,
    )
}

fn refined_const_compare(a: &RefinedConst, b: &RefinedConst) -> Ordering {
    let rc_is_ctx_cmp = a.is_ctx.cmp(&b.is_ctx);
    if rc_is_ctx_cmp != Ordering::Equal {
        rc_is_ctx_cmp
    } else {
        match (&a.bound, &b.bound) {
            (RefinedConstBound::TRexact(_), RefinedConstBound::TRloose(_)) => Ordering::Less,
            (RefinedConstBound::TRloose(_), RefinedConstBound::TRexact(_)) => Ordering::Greater,
            (RefinedConstBound::TRloose(b1), RefinedConstBound::TRloose(b2)) => {
                tyl_compare(true, false, &b1.lower, &b2.lower)
                    .then_with(|| tyl_compare(true, false, &b1.upper, &b2.upper))
            }
            (RefinedConstBound::TRexact(ty1), RefinedConstBound::TRexact(ty2)) => {
                ty_compare(false, ty1, ty2)
            }
        }
    }
}

fn class_refinement_compare(r1: &ClassRefinement, r2: &ClassRefinement) -> Ordering {
    map_compare(
        refined_const_compare,
        r1.cr_consts.iter(),
        r2.cr_consts.iter(),
    )
}

/// `exact_compare`
pub fn exact_compare(e1: &Exact, e2: &Exact) -> Ordering {
    match (e1, e2) {
        (Exact::Exact, Exact::Exact) => Ordering::Equal,
        (Exact::Nonexact(_), Exact::Exact) => Ordering::Greater,
        (Exact::Exact, Exact::Nonexact(_)) => Ordering::Less,
        (Exact::Nonexact(r1), Exact::Nonexact(r2)) => class_refinement_compare(r1, r2),
    }
}

/// `ty_equal ?normalize_lists`
pub fn ty_equal(normalize_lists: bool, ty1: &Ty, ty2: &Ty) -> bool {
    ty_compare(normalize_lists, ty1, ty2) == Ordering::Equal
}

/// `equal_locl_ty_`
pub fn equal_locl_ty_(ty_1: &Ty_, ty_2: &Ty_) -> bool {
    ty__compare(false, ty_1, ty_2) == Ordering::Equal
}

// `compare_locl_ty`, the order of `Typing_set`.
impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Ty {}
impl PartialOrd for Ty {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Ty {
    fn cmp(&self, other: &Self) -> Ordering {
        ty_compare(false, self, other)
    }
}

/// `Typing_set.t`: a set of types ordered by `compare_locl_ty`.
pub type TySet = std::collections::BTreeSet<Ty>;
