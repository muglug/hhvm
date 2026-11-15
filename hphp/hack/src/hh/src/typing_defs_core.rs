// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_defs_core.ml`. See `hh/PORTING.md`.
//!
//! # Phases, and which Rust type is which
//!
//! OCaml has one GADT, `'phase ty`, for declared (`decl_phase`) and inferred
//! (`locl_phase`) types. In Rust the two phases are different types:
//!
//! - **locl** (`locl_ty`, `locl_phase ty_`, `locl_fun_type`, ...): [`Ty`],
//!   [`Ty_`], [`FunType`], ... *defined in this module*. `oxidized` only has
//!   the declared phase (everything the OCaml marks `[@@oxidize.exclude]` is
//!   missing there: `Tvar`, `Tnewtype`, `Tdependent`, `Tclass`, `Tneg`,
//!   `Tlabel`, `exact`, `type_predicate`, `type_tag`, `dependent_type`, ...),
//!   so the types here are the `oxidized::typing_defs_core` definitions copied
//!   field for field, without the constructors that exist only in the declared
//!   phase and with the ones that exist only in the localized phase added.
//!   Constructor and field names are the `oxidized` ones (`TvecOrDict`,
//!   `TclassPtr`, `ft.params`, `fp.type_`, `ShapeSimple`, ...), and the types
//!   that `oxidized` does not have are named the same way (constructors in
//!   camel case, the common prefix of the fields of a record removed:
//!   `ShapePredicate { allows_unknown_fields, fields }`).
//! - **decl** (`decl_ty` and friends): [`DeclTy`] = `ty::decl::Ty<BReason>`
//!   from `hackrs`, as PORTING.md prescribes. The functions of this module
//!   that are specific to the declared phase take those.
//!
//! Functions that are polymorphic in the phase in OCaml (`mk`, `get_node`,
//! `ty_compare`, the `Flags` accessors, ...) are ported for the localized
//! phase; the declared phase has the functions with `decl` in their name, and
//! otherwise the `hackrs` API (`Ty::new`, `node_ref`, `reason`, `flags`).
//!
//! The types that do not mention a phase are re-exported from `oxidized`.
//!
//! The reason of a localized type is `crate::typing_reason::T` (the reasons of
//! `oxidized` are those of the declared phase only).
//!
//! `Tvid.t` and `Expression_id.t` are `isize`, as in `oxidized`
//! (`Tdynamic(Option<isize>)`) and in `crate::typing_reason`.
//!
//! Comparison functions return [`Ordering`] where OCaml returns an `int`.

use std::rc::Rc;
use std::cmp::Ordering;
use std::collections::BTreeSet;

use bstr::BString;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::s_map::SMap;
use oxidized::tany_sentinel::TanySentinel;
pub use oxidized::typing_defs_core::CeVisibility;
pub use oxidized::typing_defs_core::ConsistentKind;
pub use oxidized::typing_defs_core::Enforcement;
pub use oxidized::typing_defs_core::ParamMode;
pub use oxidized::typing_defs_core::PosByteString;
pub use oxidized::typing_defs_core::PosId;
pub use oxidized::typing_defs_core::PosString;
pub use oxidized::typing_defs_core::TByteString;
pub use oxidized::typing_defs_core::TshapeFieldName;
/// The origin of a type is a succinct key that is unique to the type
/// containing it. Consequently, two types with the same origin are necessarily
/// identical. Any change to a type with origin needs to come with a *reset* of
/// its origin. For example, all type mappers have to reset origins to
/// [Missing_origin].
pub use oxidized::typing_defs_core::TypeOrigin;
pub use oxidized::typing_defs_core::UserAttribute;
pub use oxidized::typing_defs_core::UserAttributeParam;
pub use oxidized::typing_defs_core::ValKind;
pub use oxidized::typing_defs_core::XhpAttr;
use oxidized::typing_defs_flags::FunParamFlags;
use oxidized::typing_defs_flags::FunTypeFlags;

use self::t_shape_map::TShapeField;
use self::t_shape_map::TShapeMap;
/// `module Reason = Typing_reason`
pub use crate::typing_reason as reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;

// ---------------------------------------------------------------------------
// Types of the declared phase (hackrs)
// ---------------------------------------------------------------------------

/// `decl_ty`
pub type DeclTy = ty::decl::Ty<crate::ctx::R>;
/// `decl_ty_`
pub type DeclTy_ = ty::decl::Ty_<crate::ctx::R>;
/// `decl_tparam`
pub type DeclTparam = ty::decl::Tparam<crate::ctx::R, DeclTy>;
/// `decl_where_constraint`
pub type DeclWhereConstraint = ty::decl::WhereConstraint<DeclTy>;
/// `decl_fun_type`
pub type DeclFunType = ty::decl::FunType<crate::ctx::R, DeclTy>;
/// `decl_fun_param`
pub type DeclFunParam = ty::decl::FunParam<crate::ctx::R, DeclTy>;
/// `decl_fun_params`
pub type DeclFunParams = ty::decl::ty::FunParams<crate::ctx::R, DeclTy>;
/// `decl_class_refinement`
pub type DeclClassRefinement = ty::decl::ClassRefinement<DeclTy>;
/// `decl_refined_const`
pub type DeclRefinedConst = ty::decl::RefinedConst<DeclTy>;
/// `decl_phase refined_const_bound`
pub type DeclRefinedConstBound = ty::decl::RefinedConstBound<DeclTy>;
/// `decl_phase shape_field_type`
pub type DeclShapeFieldType = ty::decl::ShapeFieldType<crate::ctx::R>;

// ---------------------------------------------------------------------------
// Types of the localized phase
// ---------------------------------------------------------------------------

/// `locl_ty`
pub type LoclTy = Ty;
/// `locl_ty_`
pub type LoclTy_ = Ty_;
/// `locl_tparam`
pub type LoclTparam = Tparam;
/// `locl_where_constraint`
pub type LoclWhereConstraint = WhereConstraint;
/// `locl_fun_type`
pub type LoclFunType = FunType;
/// `locl_fun_param`
pub type LoclFunParam = FunParam;
/// `locl_fun_params`
pub type LoclFunParams = FunParams;
/// `locl_class_refinement`
pub type LoclClassRefinement = ClassRefinement;
/// `locl_refined_const`
pub type LoclRefinedConst = RefinedConst;

/// A reference to some expression. For example:
///
///  $x->foo()
///
///  The expression $x would have a certain ID.
///  The expression $x->foo() would have a different one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DependentType {
    /// The payload is an `Expression_id.t`.
    DTexpr(isize),
}

#[derive(Clone, Debug)]
pub struct Tparam {
    pub variance: ast_defs::Variance,
    pub name: PosId,
    pub constraints: Vec<(ast_defs::ConstraintKind, Ty)>,
    pub reified: ast_defs::ReifyKind,
    pub user_attributes: Vec<UserAttribute>,
}

#[derive(Clone, Debug)]
pub struct WhereConstraint(pub Ty, pub ast_defs::ConstraintKind, pub Ty);

/// Because Tfun is currently used as both a decl and locl ty, without this,
/// the HH\Contexts\defaults alias must be stored in shared memory for a
/// decl Tfun record. We can eliminate this if the majority of usages end up
/// explicit or if we separate decl and locl Tfuns.
#[derive(Clone, Debug)]
pub enum Capability {
    /// Should not be used for lambda inference
    CapDefaults(PosOrDecl),
    CapTy(Ty),
}

/// Companion to fun_params type, intended to consolidate checking of
/// implicit params for functions.
#[derive(Clone, Debug)]
pub struct FunImplicitParams {
    pub capability: Capability,
}

#[derive(Clone, Debug)]
pub struct FunParam {
    pub pos: PosOrDecl,
    /// Only type-relevant when
    ///  `Option.is_some (Typing_defs.Named_params.name_of_named_param fp_name)`
    /// used:
    /// - for IDE features
    /// - for named params (use accessor above)
    pub name: Option<String>,
    pub type_: Ty,
    pub flags: FunParamFlags,
    pub def_value: Option<String>,
}

pub type FunParams = Vec<FunParam>;

/// The type of a function AND a method
#[derive(Clone, Debug)]
pub struct FunType {
    pub tparams: Vec<Tparam>,
    pub where_constraints: Vec<WhereConstraint>,
    pub params: FunParams,
    pub implicit_params: FunImplicitParams,
    /// Carries through the sync/async information from the aast
    pub ret: Ty,
    pub flags: FunTypeFlags,
    pub instantiated: bool,
}

/// Private type in OCaml: use [`mk`] to construct, [`deref`]/[`get_node`]/
/// [`get_reason`] to access.
///
/// The node is reference-counted: cloning a type shares it, as OCaml shares
/// values, so cloning is cheap and the identity of a type survives a clone.
/// [`phys_equal`] is OCaml's `phys_equal` on types. To change a node, build a
/// new type with [`mk`] (or [`unwrap_node`] the node first).
///
/// `==` and `Ord` are [`ty_compare`] (they ignore reasons).
#[derive(Clone, Debug)]
pub struct Ty(pub Reason, pub Rc<TyNode>);

/// The node of a localized type: a [`Ty_`] (which it dereferences to), and
/// what is known of the types in it ([`ty_flags`]), computed the first time
/// it is asked for (not in the OCaml: a visitor that looks for type
/// variables, say, can skip a type that has none without visiting it). It
/// is immutable: to change a node, build another (with [`mk`]);
/// [`unwrap_node`] gives back the `Ty_`.
pub struct TyNode {
    node: Ty_,
    /// The flags, with [`ty_flags::KNOWN`] once they are computed.
    flags: std::cell::Cell<u8>,
    /// Not in the OCaml, not read here: the structural hash of the type that
    /// `typing_subtype::subtype_ask::memo` computes once per node from its
    /// children's (0 until then), so that the memo of `ask`/`tell` does not
    /// walk the whole type to hash it at every lookup (-3.3% instructions).
    pub memo_hash: std::cell::Cell<u64>,
    /// Not in the OCaml, not read here either: the number of this node in the
    /// per-thread memo of `subtype_ask::memo` (0 until it gets one), so that
    /// the memo's front table holds numbers instead of `Weak` references
    /// (about -6% cycles). It fits in the padding after `flags`; a copy of
    /// the node is another node, so `Clone` resets it.
    pub memo_serial: std::cell::Cell<u32>,
}

impl Clone for TyNode {
    fn clone(&self) -> TyNode {
        TyNode {
            node: self.node.clone(),
            flags: self.flags.clone(),
            // A copy is another node: what `subtype_ask::memo` keeps in a
            // node is computed again for it.
            memo_hash: std::cell::Cell::new(0),
            memo_serial: std::cell::Cell::new(0),
        }
    }
}

impl std::ops::Deref for TyNode {
    type Target = Ty_;
    fn deref(&self) -> &Ty_ {
        &self.node
    }
}

impl std::fmt::Debug for TyNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.node, f)
    }
}

impl TyNode {
    pub fn new(node: Ty_) -> TyNode {
        TyNode {
            node,
            flags: std::cell::Cell::new(0),
            memo_hash: std::cell::Cell::new(0),
            memo_serial: std::cell::Cell::new(0),
        }
    }

    /// The [`ty_flags`] of the node.
    pub fn flags(&self) -> u8 {
        let flags = self.flags.get();
        if flags & ty_flags::KNOWN != 0 {
            return flags;
        }
        let flags = ty_flags::of_node(&self.node) | ty_flags::KNOWN;
        self.flags.set(flags);
        flags
    }
}

/// The `Ty_` of `ty`'s node, to change in place, if no other type shares the
/// node (`Rc::get_mut`); the node is then another node (what is cached in it
/// is computed again). OCaml builds a new node; here an unshared one, which
/// nothing else can see, is reused.
pub fn node_mut(ty: &mut Ty) -> Option<&mut Ty_> {
    let node = Rc::get_mut(&mut ty.1)?;
    node.flags.set(0);
    node.memo_hash.set(0);
    node.memo_serial.set(0);
    Some(&mut node.node)
}

/// `Rc::unwrap_or_clone` of a node: its `Ty_`, copied if it is shared.
pub fn unwrap_node(node: Rc<TyNode>) -> Ty_ {
    match Rc::try_unwrap(node) {
        Ok(node) => node.node,
        Err(node) => node.node.clone(),
    }
}

/// What may occur in a type (not in the OCaml; see [`TyNode`]). A flag that
/// is not set means that nothing of its kind occurs anywhere in the type: in
/// none of the types of its node, of their nodes, and so on (the types of a
/// function type's parameters, constraints and capability, of a class
/// type's refinement, ...). A flag can be set when nothing of its kind
/// occurs (a negated type predicate has them all).
pub mod ty_flags {
    use super::*;

    /// A type variable (`Tvar`, or a `Tdynamic` with a shadow variable).
    pub const TVAR: u8 = 1;
    /// A generic (`Tgeneric`).
    pub const TGENERIC: u8 = 1 << 1;
    /// An expression-dependent type (`Tdependent`).
    pub const TDEPENDENT: u8 = 1 << 2;
    /// A type access (`Taccess`).
    pub const TACCESS: u8 = 1 << 3;
    /// All of them.
    pub const ALL: u8 = TVAR | TGENERIC | TDEPENDENT | TACCESS;
    /// (In a node: its flags are computed.)
    pub(super) const KNOWN: u8 = 1 << 7;

    fn of_tys<'a>(tys: impl IntoIterator<Item = &'a Ty>) -> u8 {
        tys.into_iter().fold(0, |acc, ty| acc | ty.1.flags())
    }

    fn of_exact(exact: &Exact) -> u8 {
        match exact {
            Exact::Exact => 0,
            Exact::Nonexact(cr) => cr.cr_consts.values().fold(0, |acc, rc| {
                acc | match &rc.bound {
                    RefinedConstBound::TRexact(ty) => ty.1.flags(),
                    RefinedConstBound::TRloose(bounds) => {
                        of_tys(&bounds.lower) | of_tys(&bounds.upper)
                    }
                }
            }),
        }
    }

    fn of_fun(ft: &FunType) -> u8 {
        let tparams = ft
            .tparams
            .iter()
            .fold(0, |acc, tp| acc | of_tys(tp.constraints.iter().map(|(_, ty)| ty)));
        let where_constraints = ft
            .where_constraints
            .iter()
            .fold(0, |acc, WhereConstraint(ty1, _, ty2)| acc | ty1.1.flags() | ty2.1.flags());
        let capability = match &ft.implicit_params.capability {
            Capability::CapDefaults(_) => 0,
            Capability::CapTy(ty) => ty.1.flags(),
        };
        tparams
            | where_constraints
            | of_tys(ft.params.iter().map(|fp| &fp.type_))
            | capability
            | ft.ret.1.flags()
    }

    /// The flags of a node built from `node`.
    pub(super) fn of_node(node: &Ty_) -> u8 {
        match node {
            Ty_::Tany(_) | Ty_::Tnonnull | Ty_::Tprim(_) | Ty_::Tlabel(_) | Ty_::Tdynamic(None) => 0,
            Ty_::Tdynamic(Some(_)) | Ty_::Tvar(_) => TVAR,
            Ty_::Tgeneric(_) => TGENERIC,
            Ty_::Toption(ty) | Ty_::TclassPtr(ty) => ty.1.flags(),
            Ty_::Tdependent(_, ty) => TDEPENDENT | ty.1.flags(),
            Ty_::Taccess(TaccessType(ty, _)) => TACCESS | ty.1.flags(),
            Ty_::Tfun(ft) => of_fun(ft),
            Ty_::Ttuple(TupleType {
                required,
                optional,
                extra: TupleExtra::Tvariadic(ty) | TupleExtra::Tsplat(ty),
            }) => of_tys(required) | of_tys(optional) | ty.1.flags(),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value,
                fields,
            })) => unknown_value.1.flags() | of_tys(fields.values().map(|sft| &sft.ty)),
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => of_tys(ss_elems),
            Ty_::Tunion(tyl) | Ty_::Tintersection(tyl) => of_tys(tyl),
            Ty_::TvecOrDict(ty1, ty2) => ty1.1.flags() | ty2.1.flags(),
            Ty_::Tnewtype(_, tyl, ty) => of_tys(tyl) | ty.1.flags(),
            Ty_::Tclass(_, exact, tyl) => of_exact(exact) | of_tys(tyl),
            Ty_::Tneg(_) => ALL,
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeTagGeneric {
    Filled(Ty),
    Wildcard(isize),
}

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
    /// The name of a runtime-checkable rigid type variable: a reified
    /// generic parameter (e.g. `"T"`), an enforceable abstract type
    /// constant access (e.g. `"this::TC"`), or `this` itself.
    ///
    /// `from_like` is `true` iff the predicate came from a `~this` hint
    /// (i.e. `TyPredicate.of_ty` collapsed `Tunion [dynamic; this]`
    /// back into this tag). `TyPredicate.to_ty` uses it to reconstruct
    /// the like-wrapped form.
    GenericTag {
        name: String,
        from_like: bool,
    },
}

#[derive(Clone, Debug)]
pub struct ShapeFieldPredicate {
    pub optional: bool,
    pub predicate: TypePredicate,
}

#[derive(Clone, Debug)]
pub struct ShapePredicate {
    pub allows_unknown_fields: bool,
    pub fields: TShapeMap<ShapeFieldPredicate>,
}

/// TODO optional and variadic components T201398626 T201398652
#[derive(Clone, Debug)]
pub struct TuplePredicate {
    pub required: Vec<TypePredicate>,
}

/// Represents the predicate of a type switch, i.e. in the expression
/// ```
/// if ($x is Bool) { ... } else { ... }
/// ```
///
/// The predicate would be `is Bool`
#[derive(Clone, Debug)]
pub enum TypePredicate_ {
    IsTag(TypeTag),
    IsTupleOf(TuplePredicate),
    IsShapeOf(ShapePredicate),
    IsUnionOf(Vec<TypePredicate>),
    IsNot(Box<TypePredicate>),
}

/// `type_predicate = Reason.t * type_predicate_`
#[derive(Clone, Debug)]
pub struct TypePredicate(pub Reason, pub TypePredicate_);

/// A shape may specify whether or not fields are required. For example, consider
/// this typedef:
///
/// ```
/// type ShapeWithOptionalField = shape(?'a' => ?int);
/// ```
///
/// With this definition, the field 'a' may be unprovided in a shape. In this
/// case, the field 'a' would have sf_optional set to true.
#[derive(Clone, Debug)]
pub struct ShapeFieldType {
    pub optional: bool,
    pub ty: Ty,
}

/// `locl_phase ty_`: the constructors that exist in both phases, and the ones
/// that cannot be declared in user code. (The constructors that exist only in
/// the declared phase, `Tthis`, `Tapply`, `Trefinement`, `Tmixed`, `Twildcard`
/// and `Tlike`, are in [`DeclTy_`].)
///
/// `==` and `Ord` are [`ty__compare`].
#[derive(Clone, Debug)]
pub enum Ty_ {
    /// "Any" is the type of a variable with a missing annotation, and "mixed"
    /// is the type of a variable annotated as "mixed". THESE TWO ARE VERY
    /// DIFFERENT! Any unifies with anything, i.e., it is both a supertype and
    /// subtype of any other type. You can do literally anything to it; it's
    /// the "trust me" type. Mixed, on the other hand, is only a supertype of
    /// everything. You need to do a case analysis to figure out what it is
    /// (i.e., its elimination form).
    ///
    /// Here's an example to demonstrate:
    ///
    /// ```text
    /// function f($x): int {
    ///   return $x + 1;
    /// }
    /// ```
    ///
    /// In that example, $x has type Tany. This unifies with anything, so
    /// adding one to it is allowed, and returning that as int is allowed.
    ///
    /// In contrast, if $x were annotated as mixed, adding one to that would be
    /// a type error -- mixed is not a subtype of int, and you must be a
    /// subtype of int to take part in addition. (The converse is true though
    /// -- int is a subtype of mixed.) A case analysis would need to be done on
    /// $x, via is_int or similar.
    ///
    /// mixed exists only in the decl_phase phase because it is desugared into
    /// ?nonnull during the localization phase.
    Tany(TanySentinel),
    Tnonnull,
    /// A dynamic type is a special type which sometimes behaves as if it were a
    /// top type; roughly speaking, where a specific value of a particular type is
    /// expected and that type is dynamic, anything can be given. We call this
    /// behaviour "coercion", in that the types "coerce" to dynamic. In other ways it
    /// behaves like a bottom type; it can be used in any sort of binary expression
    /// or even have object methods called from it. However, it is in fact neither.
    ///
    /// it captures dynamicism within function scope.
    /// See tests in typecheck/dynamic/ for more examples.
    ///
    /// The optional Tvid.t is a "shadow type variable" used for dynamic inference.
    /// When present (Some v), every subtype check [dynamic <: T] also records
    /// T as an upper bound on v. After type checking, v's accumulated upper bounds
    /// describe how the dynamic value was actually used, enabling use-type inference.
    /// Shadow type variables are never solved; they only collect constraints.
    /// None in all contexts where inference is disabled or for declared types.
    Tdynamic(Option<isize>),
    /// Nullable, called "option" in the ML parlance.
    Toption(Ty),
    /// All the primitive types: int, string, void, etc.
    Tprim(ast_defs::Tprim),
    /// A wrapper around fun_type, which contains the full type information for a
    /// function, method, lambda, etc.
    ///
    /// (Shared: the OCaml's `Tfun of fun_type` points to a record that copies
    /// share; the `Rc` gives the same sharing, so copying a function type,
    /// which the calls and the subtyping of function types do, copies a
    /// pointer. Change one with `Rc::make_mut`.)
    Tfun(Rc<FunType>),
    /// A wrapper around tuple_type, which contains information about tuple elements
    Ttuple(TupleType),
    Tshape(ShapeType),
    /// The type of a generic parameter. The constraints on a generic parameter
    /// are accessed through the lenv.tpenv component of the environment, which
    /// is set up when checking the body of a function or method. See uses of
    /// Typing_phase.add_generic_parameters_and_constraints.
    Tgeneric(String),
    /// Union type.
    /// The values that are members of this type are the union of the values
    /// that are members of the components of the union.
    /// Some examples (writing | for binary union)
    ///   Tunion []  is the "nothing" type, with no values
    ///   Tunion [int;float] is the same as num
    ///   Tunion [null;t] is the same as Toption t
    Tunion(Vec<Ty>),
    Tintersection(Vec<Ty>),
    /// Tvec_or_dict (ty1, ty2) => "vec_or_dict<ty1, ty2>"
    TvecOrDict(Ty, Ty),
    /// Name of class, name of type const, remaining names of type consts
    Taccess(TaccessType),
    /// A type of a class pointer, class<T>. To be compatible with classname<T>,
    /// it takes an arbitrary type. In the future, it should only take a string
    /// that is a class name, and be named Tclass. The current Tclass would be
    /// renamed to Tinstance, where a Tinstance is an instantiation of a Tclass
    TclassPtr(Ty),
    // ========== Below Are Types That Cannot Be Declared In User Code ==========
    /// The payload is a `Tvid.t`.
    Tvar(isize),
    /// The type of an opaque type or enum. Outside their defining files or
    /// when they represent enums, they are "opaque", which means that they
    /// only unify with themselves. Within a file, uses of newtypes are
    /// expanded to their definitions (unless the newtype is an enum).
    ///
    /// However, it is possible to have a constraint that allows us to relax
    /// opaqueness. For example:
    ///
    ///   newtype MyType as int = ...
    ///
    /// or
    ///
    ///   enum MyType: int as int { ... }
    ///
    /// Outside of the file where the type was defined, this translates to:
    ///
    ///   Tnewtype ((pos, "MyType"), [], Tprim Tint)
    ///
    /// which means that MyType is abstract, but is a subtype of int as well.
    /// When the constraint is omitted, the third parameter is set to mixed.
    ///
    /// The second parameter is the list of type arguments to the type.
    Tnewtype(String, Vec<Ty>, Ty),
    /// see dependent_type
    Tdependent(DependentType, Ty),
    /// An instance of a class or interface, ty list are the arguments
    /// If exact=Exact, then this represents instances of *exactly* this class
    /// If exact=Nonexact, this also includes subclasses
    /// TODO(T199606542) rename this to Tinstance
    Tclass(PosId, Exact, Vec<Ty>),
    /// The negation of the [type_predicate]
    Tneg(TypePredicate),
    /// The type of the label expression #ID
    Tlabel(String),
}

#[derive(Clone, Debug)]
pub struct TaccessType(pub Ty, pub PosId);

#[derive(Clone, Debug)]
pub enum Exact {
    Exact,
    Nonexact(ClassRefinement),
}

/// Class refinements are for type annotations like
///
/// Box with {type T = string}
#[derive(Clone, Debug)]
pub struct ClassRefinement {
    pub cr_consts: RefinedConsts,
}

/// `refined_const SMap.t`, the map of a [`ClassRefinement`]: an
/// `SMap<RefinedConst>` (which it dereferences to), that costs nothing to
/// make, copy or drop when it is empty, which nearly all are (every class
/// type that is not exact has one). (Not in the OCaml, whose empty map is a
/// constant.)
#[derive(Clone, Default)]
pub struct RefinedConsts(Option<Box<SMap<RefinedConst>>>);

/// The map that an empty [`RefinedConsts`] dereferences to.
struct EmptyRefinedConsts(SMap<RefinedConst>);

// SAFETY: the map is empty and never changed: no value (and so no `Rc`) can
// be reached through it, from any thread.
unsafe impl Sync for EmptyRefinedConsts {}

static EMPTY_REFINED_CONSTS: EmptyRefinedConsts = EmptyRefinedConsts(SMap::new());

impl RefinedConsts {
    pub fn new() -> Self {
        RefinedConsts(None)
    }
}

impl std::ops::Deref for RefinedConsts {
    type Target = SMap<RefinedConst>;
    fn deref(&self) -> &SMap<RefinedConst> {
        match &self.0 {
            Some(map) => map,
            None => &EMPTY_REFINED_CONSTS.0,
        }
    }
}

impl std::ops::DerefMut for RefinedConsts {
    fn deref_mut(&mut self) -> &mut SMap<RefinedConst> {
        self.0.get_or_insert_with(Default::default)
    }
}

impl std::fmt::Debug for RefinedConsts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl From<SMap<RefinedConst>> for RefinedConsts {
    fn from(map: SMap<RefinedConst>) -> Self {
        if map.is_empty() {
            RefinedConsts(None)
        } else {
            RefinedConsts(Some(Box::new(map)))
        }
    }
}

impl FromIterator<(String, RefinedConst)> for RefinedConsts {
    fn from_iter<I: IntoIterator<Item = (String, RefinedConst)>>(iter: I) -> Self {
        SMap::from_iter(iter).into()
    }
}

impl IntoIterator for RefinedConsts {
    type Item = (String, RefinedConst);
    type IntoIter = std::collections::btree_map::IntoIter<String, RefinedConst>;
    fn into_iter(self) -> Self::IntoIter {
        match self.0 {
            Some(map) => map.into_iter(),
            None => SMap::new().into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a RefinedConsts {
    type Item = (&'a String, &'a RefinedConst);
    type IntoIter = std::collections::btree_map::Iter<'a, String, RefinedConst>;
    fn into_iter(self) -> Self::IntoIter {
        (**self).iter()
    }
}

#[derive(Clone, Debug)]
pub struct RefinedConst {
    pub bound: RefinedConstBound,
    pub is_ctx: bool,
}

#[derive(Clone, Debug)]
pub enum RefinedConstBound {
    /// for `=` constraints
    TRexact(Ty),
    /// for `as` or `super` constraints
    TRloose(RefinedConstBounds),
}

#[derive(Clone, Debug)]
pub struct RefinedConstBounds {
    pub lower: Vec<Ty>,
    pub upper: Vec<Ty>,
}

/// Whether all fields of this shape are known, types of each of the
/// known arms.
#[derive(Clone, Debug)]
pub struct ShapeTypeSimple {
    pub origin: TypeOrigin,
    pub unknown_value: Ty,
    pub fields: TShapeMap<ShapeFieldType>,
}

#[derive(Clone, Debug)]
pub struct ShapeTypeSplat {
    pub ss_elems: Vec<Ty>,
}

#[derive(Clone, Debug)]
pub enum ShapeType {
    ShapeSimple(ShapeTypeSimple),
    ShapeSplat(ShapeTypeSplat),
}

/// Required and extra components of a tuple. Extra components
/// are either optional + variadic, or a type splat.
/// Exmaple 1:
/// (string,bool,optional float,optional bool,int...)
/// has require components string, bool, optional components float, bool
/// and variadic component int.
/// Example 2:
/// (string,float,...T)
/// has required components string, float, and splat component T.
#[derive(Clone, Debug)]
pub struct TupleType {
    pub required: Vec<Ty>,
    pub optional: Vec<Ty>,
    pub extra: TupleExtra,
}

#[derive(Clone, Debug)]
pub enum TupleExtra {
    Tvariadic(Ty),
    Tsplat(Ty),
}

// ---------------------------------------------------------------------------
// TShapeField, TShapeMap, TShapeSet
// ---------------------------------------------------------------------------

/// This is similar to Aast.ShapeField, but contains Pos_or_decl.t
/// instead of Pos.t. Aast.ShapeField is used in shape expressions,
/// while this is used in shape types.
pub mod t_shape_field {
    use super::*;

    pub type T = TshapeFieldName;

    pub fn pos(x: &T) -> PosOrDecl {
        match x {
            TshapeFieldName::TSFregexGroup(PosString(p, _))
            | TshapeFieldName::TSFlitStr(PosByteString(p, _)) => p.clone(),
            TshapeFieldName::TSFclassConst((cls_pos, _), PosString(mem_pos, _)) => {
                // Pos_or_decl.btw
                match Pos::btw(cls_pos, mem_pos) {
                    Ok(p) => p,
                    Err(msg) => panic!("{}", msg),
                }
            }
        }
    }

    /// The name is a byte string: the keys of shape literals are.
    pub fn name(x: &T) -> BString {
        match x {
            TshapeFieldName::TSFregexGroup(PosString(_, s)) => BString::from(s.as_str()),
            TshapeFieldName::TSFlitStr(PosByteString(_, s)) => s.clone(),
            TshapeFieldName::TSFclassConst((_, s1), PosString(_, s2)) => {
                BString::from(format!("{}::{}", s1, s2))
            }
        }
    }

    pub fn of_ast(convert_pos: impl Fn(&Pos) -> PosOrDecl, x: &ast_defs::ShapeFieldName) -> T {
        match x {
            ast_defs::ShapeFieldName::SFlitStr((p, s)) => {
                TshapeFieldName::TSFlitStr(PosByteString(convert_pos(p), s.clone()))
            }
            ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(p, cls)) => {
                TshapeFieldName::TSFclassConst(
                    (convert_pos(p), cls.clone()),
                    PosString(convert_pos(p), "class".to_string()),
                )
            }
            ast_defs::ShapeFieldName::SFclassConst(ast_defs::Id(pcls, cls), (pconst, const_)) => {
                TshapeFieldName::TSFclassConst(
                    (convert_pos(pcls), cls.clone()),
                    PosString(convert_pos(pconst), const_.clone()),
                )
            }
        }
    }

    /// This ignores positions!
    /// We include span information in tshape_field_name to improve error
    /// messages, but we don't want it being used in the comparison, so
    /// we have to write our own compare.
    ///
    /// (Same order as `Ord for oxidized::t_shape_map::TShapeField`.)
    pub fn compare(x: &T, y: &T) -> Ordering {
        use TshapeFieldName::*;
        match (x, y) {
            (TSFregexGroup(PosString(_, s1)), TSFregexGroup(PosString(_, s2))) => s1.cmp(s2),
            (TSFlitStr(PosByteString(_, s1)), TSFlitStr(PosByteString(_, s2))) => s1.cmp(s2),
            (
                TSFclassConst((_, s1), PosString(_, s1_)),
                TSFclassConst((_, s2), PosString(_, s2_)),
            ) => (s1, s1_).cmp(&(s2, s2_)),
            (TSFregexGroup(_), _) => Ordering::Less,
            (TSFlitStr(_), TSFregexGroup(_)) => Ordering::Greater,
            (TSFlitStr(_), _) => Ordering::Less,
            (TSFclassConst(_, _), _) => Ordering::Greater,
        }
    }

    /// This also ignores positions for the same reasons.
    pub fn equal(x: &T, y: &T) -> bool {
        compare(x, y) == Ordering::Equal
    }
}

/// This is similar to Ast_defs.ShapeMap, but contains Pos_or_decl.t
/// instead of Pos.t. Ast_defs.ShapeMap is used in shape expressions,
/// while this is used in shape types.
///
/// The map is `oxidized::t_shape_map::TShapeMap` (a `BTreeMap` whose keys,
/// [`TShapeField`], wrap a `TshapeFieldName` and are ordered by
/// `TShapeField.compare`), so the functions of `Wrapped_map.S` that `BTreeMap`
/// has are not repeated here.
pub mod t_shape_map {
    use std::cmp::Ordering;

    pub use oxidized::t_shape_map::TShapeField;
    pub use oxidized::t_shape_map::TShapeMap;

    /// `'a TShapeMap.t`
    pub type T<A> = TShapeMap<A>;
    /// `TShapeMap.key`
    pub type Key = TShapeField;

    pub fn map_and_rekey<A, B>(
        m: T<A>,
        mut f1: impl FnMut(Key) -> Key,
        mut f2: impl FnMut(A) -> B,
    ) -> T<B> {
        let mut acc = T::new();
        for (k, v) in m {
            acc.insert(f1(k), f2(v));
        }
        acc
    }

    /// `Wrapped_map.S.map_env`: maps the values in the order of the keys.
    pub fn map_env<Env, A, B>(
        mut f: impl FnMut(&mut Env, &Key, A) -> B,
        env: &mut Env,
        m: T<A>,
    ) -> T<B> {
        // The keys come in order: the map is built from them in one go
        // (`BTreeMap::from_iter` of a sorted list), not one insertion (and
        // search) at a time.
        let bindings: Vec<(Key, B)> = (m.into_iter())
            .map(|(k, v)| {
                let v = f(env, &k, v);
                (k, v)
            })
            .collect();
        bindings.into_iter().collect()
    }

    /// `Wrapped_map.S.map_env` on the fields of a shape, which keeps their
    /// keys: the values are replaced in the map that is given (in the order of
    /// the keys, as `map_env`), whose tree is kept, instead of building
    /// another, as the OCaml does. The result is the same map; no allocation
    /// or key comparison per field (-2.5% instructions with the callers in
    /// `typing_defs::shape_field_map` and `type_mapper_generic`).
    pub fn map_fields_env<Env>(
        mut f: impl FnMut(&mut Env, &Key, super::ShapeFieldType) -> super::ShapeFieldType,
        env: &mut Env,
        mut m: T<super::ShapeFieldType>,
    ) -> T<super::ShapeFieldType> {
        for (k, v) in m.iter_mut() {
            let old = std::mem::replace(v, placeholder_field());
            *v = f(env, k, old);
        }
        m
    }

    /// `Wrapped_map.S.map_env_ty_err_opt` on the fields of a shape, in place,
    /// as [`map_fields_env`] (`combine_ty_errs` gets the errors in the reverse
    /// of the order of the keys, as in [`map_env_ty_err_opt`]).
    pub fn map_fields_env_ty_err_opt<Env, TyErr, TyErrs>(
        mut f: impl FnMut(&mut Env, &Key, super::ShapeFieldType) -> (Option<TyErr>, super::ShapeFieldType),
        env: &mut Env,
        mut m: T<super::ShapeFieldType>,
        combine_ty_errs: impl FnOnce(Vec<TyErr>) -> TyErrs,
    ) -> (TyErrs, T<super::ShapeFieldType>) {
        let mut errs = Vec::new();
        for (k, v) in m.iter_mut() {
            let old = std::mem::replace(v, placeholder_field());
            let (err, new) = f(env, k, old);
            if let Some(err) = err {
                errs.push(err);
            }
            *v = new;
        }
        errs.reverse();
        (combine_ty_errs(errs), m)
    }

    /// What a field holds while it is being mapped (a shared node).
    fn placeholder_field() -> super::ShapeFieldType {
        super::ShapeFieldType {
            optional: false,
            ty: super::mk((crate::typing_reason::none(), super::Ty_::Tnonnull)),
        }
    }

    /// `Wrapped_map.S.map_env_ty_err_opt`. As in OCaml, `combine_ty_errs` gets
    /// the errors in the reverse of the order of the keys.
    pub fn map_env_ty_err_opt<Env, A, B, TyErr, TyErrs>(
        mut f: impl FnMut(&mut Env, &Key, A) -> (Option<TyErr>, B),
        env: &mut Env,
        m: T<A>,
        combine_ty_errs: impl FnOnce(Vec<TyErr>) -> TyErrs,
    ) -> (TyErrs, T<B>) {
        let mut errs = Vec::new();
        // (Built in one go, as in `map_env`.)
        let mut bindings: Vec<(Key, B)> = Vec::with_capacity(m.len());
        for (k, v) in m {
            let (err, v) = f(env, &k, v);
            if let Some(err) = err {
                errs.push(err);
            }
            bindings.push((k, v));
        }
        errs.reverse();
        (combine_ty_errs(errs), bindings.into_iter().collect())
    }

    /// `Map.S.compare`
    pub fn compare<A>(mut cmp: impl FnMut(&A, &A) -> Ordering, m1: &T<A>, m2: &T<A>) -> Ordering {
        let mut e1 = m1.iter();
        let mut e2 = m2.iter();
        loop {
            match (e1.next(), e2.next()) {
                (None, None) => return Ordering::Equal,
                (None, Some(_)) => return Ordering::Less,
                (Some(_), None) => return Ordering::Greater,
                (Some((k1, d1)), Some((k2, d2))) => {
                    let c = k1.cmp(k2);
                    if c != Ordering::Equal {
                        return c;
                    }
                    let c = cmp(d1, d2);
                    if c != Ordering::Equal {
                        return c;
                    }
                }
            }
        }
    }
}

pub mod t_shape_set {
    /// `TShapeSet.t`
    pub type T = std::collections::BTreeSet<super::TShapeField>;
}

/// `TShapeSet.t`
pub type TShapeSet = BTreeSet<TShapeField>;

pub fn user_attribute_param_to_string(p: &UserAttributeParam) -> BString {
    match p {
        UserAttributeParam::Classname(s)
        | UserAttributeParam::EnumClassLabel(s)
        | UserAttributeParam::Int(s) => BString::from(s.as_str()),
        UserAttributeParam::String(s) => s.clone(),
    }
}

pub fn nonexact() -> Exact {
    Exact::Nonexact(ClassRefinement {
        cr_consts: RefinedConsts::new(),
    })
}

pub fn is_nonexact(e: &Exact) -> bool {
    match e {
        Exact::Nonexact(_) => true,
        Exact::Exact => false,
    }
}

pub fn refined_const_kind_str(rc: &RefinedConst) -> &'static str {
    if rc.is_ctx { "ctx" } else { "type" }
}

// ---------------------------------------------------------------------------
// Flags
// ---------------------------------------------------------------------------

pub mod flags {
    use super::*;

    pub fn get_ft_return_disposable(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::RETURN_DISPOSABLE)
    }

    pub fn get_ft_returns_readonly(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::RETURNS_READONLY)
    }

    pub fn get_ft_readonly_this(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::READONLY_THIS)
    }

    pub fn get_ft_async(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::ASYNC)
    }

    pub fn get_ft_generator(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::GENERATOR)
    }

    pub fn get_ft_support_dynamic_type(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::SUPPORT_DYNAMIC_TYPE)
    }

    /// This flag is set true only if the exact method has the memoized attribute.
    pub fn get_ft_is_memoized(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::IS_MEMOIZED)
    }

    pub fn set_ft_is_function_pointer(mut ft: FunType, is_fp: bool) -> FunType {
        ft.flags.set(FunTypeFlags::IS_FUNCTION_POINTER, is_fp);
        ft
    }

    pub fn get_ft_is_function_pointer(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::IS_FUNCTION_POINTER)
    }

    pub fn set_ft_readonly_this(mut ft: FunType, readonly_this: bool) -> FunType {
        ft.flags.set(FunTypeFlags::READONLY_THIS, readonly_this);
        ft
    }

    pub fn set_ft_returns_readonly(mut ft: FunType, readonly_return: bool) -> FunType {
        ft.flags
            .set(FunTypeFlags::RETURNS_READONLY, readonly_return);
        ft
    }

    pub fn set_ft_support_dynamic_type(mut ft: FunType, readonly_return: bool) -> FunType {
        ft.flags
            .set(FunTypeFlags::SUPPORT_DYNAMIC_TYPE, readonly_return);
        ft
    }

    pub fn get_ft_variadic(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::VARIADIC)
    }

    pub fn get_ft_named_variadic(ft: &FunType) -> bool {
        ft.flags.contains(FunTypeFlags::NAMED_VARIADIC)
    }

    pub fn get_ft_fun_kind(ft: &FunType) -> ast_defs::FunKind {
        // Typing_defs_flags.Fun.fun_kind
        match (
            ft.flags.contains(FunTypeFlags::ASYNC),
            ft.flags.contains(FunTypeFlags::GENERATOR),
        ) {
            (false, false) => ast_defs::FunKind::FSync,
            (true, false) => ast_defs::FunKind::FAsync,
            (false, true) => ast_defs::FunKind::FGenerator,
            (true, true) => ast_defs::FunKind::FAsyncGenerator,
        }
    }

    pub fn get_fp_readonly(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::READONLY)
    }

    pub fn get_fp_splat(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::SPLAT)
    }

    pub fn make_fp_flags(
        mode: ParamMode,
        accept_disposable: bool,
        is_optional: bool,
        readonly: bool,
        ignore_readonly_error: bool,
        splat: bool,
        named: bool,
    ) -> FunParamFlags {
        let inout = match mode {
            ParamMode::FPinout => true,
            ParamMode::FPnormal => false,
        };
        // Typing_defs_flags.FunParam.make
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

    pub fn get_fp_accept_disposable(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::ACCEPT_DISPOSABLE)
    }

    pub fn get_fp_is_optional(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::IS_OPTIONAL)
    }

    pub fn get_fp_is_named(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::NAMED)
    }

    pub fn get_fp_ignore_readonly_error(fp: &FunParam) -> bool {
        fp.flags.contains(FunParamFlags::IGNORE_READONLY_ERROR)
    }

    pub fn get_fp_mode(fp: &FunParam) -> ParamMode {
        if fp.flags.contains(FunParamFlags::INOUT) {
            ParamMode::FPinout
        } else {
            ParamMode::FPnormal
        }
    }
}

pub use flags::*;

// ---------------------------------------------------------------------------
// Pp
// ---------------------------------------------------------------------------

/// The hand-written printers of `Typing_defs_core.Pp`. They print with OCaml's
/// `Format` boxes (`@[<2>`, `@,`, `@ `), whose line breaking has no port yet,
/// so the `pp_*` functions (which take a `Format.formatter`) are not here and
/// the `show_*` functions are `todo!`.
pub mod pp {
    use super::*;

    pub fn show_ty(_x: &Ty) -> String {
        todo!("Typing_defs_core.Pp.show_ty: needs a port of OCaml's Format (boxes and break hints)")
    }

    pub fn show_decl_ty(_x: &DeclTy) -> String {
        todo!(
            "Typing_defs_core.Pp.show_decl_ty: needs a port of OCaml's Format (boxes and break hints)"
        )
    }

    pub fn show_locl_ty(x: &Ty) -> String {
        show_ty(x)
    }

    pub fn show_type_predicate_(_predicate_: &TypePredicate_) -> String {
        todo!(
            "Typing_defs_core.Pp.show_type_predicate_: needs a port of OCaml's Format (boxes and break hints)"
        )
    }
}

pub use pp::*;

// ---------------------------------------------------------------------------
// Constructor and deconstructor functions for types and constraint types.
// Abstracting these lets us change the implementation, e.g. hash cons
// ---------------------------------------------------------------------------

pub fn mk(p: (Reason, Ty_)) -> Ty {
    let (r, ty_) = p;
    // The nodes without components (`nonnull`, `dynamic` without a shadow
    // variable, the primitive types) are shared: one of each per thread. In
    // OCaml these constructors are constants too (only the pair with the
    // reason is allocated); two such types are `phys_equal` here when their
    // reasons are equal, and only then.
    match &ty_ {
        Ty_::Tnonnull | Ty_::Tdynamic(None) | Ty_::Tprim(_) => Ty(r, shared_leaf(ty_)),
        _ => Ty(r, Rc::new(TyNode::new(ty_))),
    }
}

/// The shared node of `ty_`, a node without components.
fn shared_leaf(ty_: Ty_) -> Rc<TyNode> {
    const PRIMS: usize = 16;
    thread_local! {
        static LEAVES: [std::cell::OnceCell<Rc<TyNode>>; PRIMS + 2] =
            const { [const { std::cell::OnceCell::new() }; PRIMS + 2] };
    }
    let index = match &ty_ {
        Ty_::Tprim(p) if (*p as usize) < PRIMS => *p as usize,
        Ty_::Tnonnull => PRIMS,
        Ty_::Tdynamic(None) => PRIMS + 1,
        _ => return Rc::new(TyNode::new(ty_)),
    };
    LEAVES.with(|leaves| Rc::clone(leaves[index].get_or_init(|| Rc::new(TyNode::new(ty_)))))
}

/// OCaml's `phys_equal` on types: the same node, shared by cloning, with the
/// same reason. OCaml compares the address of the `(reason, node)` pair; here
/// two types that share a node and have equal reasons count as the same, which
/// differs from OCaml only for a type rebuilt from its own node with an equal
/// but separately constructed reason.
pub fn phys_equal(t1: &Ty, t2: &Ty) -> bool {
    Rc::ptr_eq(&t1.1, &t2.1) && t1.0 == t2.0
}

/// The reason and the node, copied. To take a type apart without copying it,
/// match on [`get_node`], or on the fields of [`Ty`].
pub fn deref(p: &Ty) -> (Reason, Ty_) {
    let Ty(r, n) = p;
    (r.clone(), Ty_::clone(n))
}

pub fn get_reason(ty: &Ty) -> &Reason {
    &ty.0
}

pub fn get_node(ty: &Ty) -> &Ty_ {
    &ty.1
}

impl Ty {
    /// [`get_reason`]
    pub fn get_reason(&self) -> &Reason {
        &self.0
    }

    /// [`get_node`]
    pub fn get_node(&self) -> &Ty_ {
        &self.1
    }

    /// Whether a type variable may occur in the type (see [`ty_flags`]):
    /// `false` means that none does.
    pub fn may_have_tyvars(&self) -> bool {
        self.1.flags() & ty_flags::TVAR != 0
    }

    /// Whether any of `flags` may occur in the type (see [`ty_flags`]).
    pub fn may_have(&self, flags: u8) -> bool {
        self.1.flags() & flags != 0
    }
}

fn ty_con_ordinal_(ty_: &Ty_) -> isize {
    match ty_ {
        // exist in both phases
        Ty_::Tany(_) => 0,
        Ty_::Toption(t) => match get_node(t) {
            Ty_::Tnonnull => 1,
            _ => 4,
        },
        Ty_::Tnonnull => 2,
        Ty_::Tdynamic(_) => 3,
        Ty_::Tprim(_) => 5,
        Ty_::Tfun(_) => 6,
        Ty_::Ttuple(_) => 7,
        Ty_::Tshape(_) => 8,
        Ty_::Tvar(_) => 9,
        Ty_::Tgeneric(_) => 11,
        Ty_::Tunion(_) => 13,
        Ty_::Tintersection(_) => 14,
        Ty_::Taccess(_) => 24,
        Ty_::TvecOrDict(_, _) => 25,
        Ty_::TclassPtr(_) => 26,
        // only locl constructors
        Ty_::Tnewtype(_, _, _) => 201,
        Ty_::Tdependent(_, _) => 202,
        Ty_::Tclass(_, _, _) => 204,
        Ty_::Tneg(_) => 205,
        Ty_::Tlabel(_) => 206,
    }
}

/// Returns `true` if both origins are available and identical.
/// If this function returns `true`, the two types that have
/// the origins provided must be identical.
pub fn same_type_origin(orig1: &TypeOrigin, orig2: &TypeOrigin) -> bool {
    match orig1 {
        TypeOrigin::MissingOrigin => false,
        _ => orig1 == orig2,
    }
}

// The OCaml name (`type_predicate_` + `_con_ordinal`), kept as it is next to
// the other `type_predicate_` functions: snake case would drop the `_` of the
// type's name.
#[allow(non_snake_case)]
fn type_predicate__con_ordinal(type_predicate_: &TypePredicate_) -> isize {
    match type_predicate_ {
        TypePredicate_::IsTag(_) => 0,
        TypePredicate_::IsTupleOf(_) => 1,
        TypePredicate_::IsShapeOf(_) => 2,
        TypePredicate_::IsUnionOf(_) => 3,
        TypePredicate_::IsNot(_) => 4,
    }
}

fn type_tag_con_ordinal(type_tag: &TypeTag) -> isize {
    match type_tag {
        TypeTag::BoolTag => 0,
        TypeTag::IntTag => 1,
        TypeTag::ArraykeyTag => 3,
        TypeTag::FloatTag => 4,
        TypeTag::NumTag => 5,
        TypeTag::ResourceTag => 6,
        TypeTag::NullTag => 7,
        TypeTag::ClassTag(_, _) => 8,
        TypeTag::EnumTag(_) => 9,
        TypeTag::GenericTag { .. } => 10,
    }
}

pub fn chain_compare(comp: Ordering, cont: impl FnOnce() -> Ordering) -> Ordering {
    match comp {
        Ordering::Equal => cont(),
        n => n,
    }
}

/// `Option.compare`
fn option_compare<T>(
    cmp: impl FnOnce(&T, &T) -> Ordering,
    o1: Option<&T>,
    o2: Option<&T>,
) -> Ordering {
    match (o1, o2) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => cmp(a, b),
    }
}

/// `S_map.compare`
fn s_map_compare<A>(
    mut cmp: impl FnMut(&A, &A) -> Ordering,
    m1: &SMap<A>,
    m2: &SMap<A>,
) -> Ordering {
    let mut e1 = m1.iter();
    let mut e2 = m2.iter();
    loop {
        match (e1.next(), e2.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some((k1, d1)), Some((k2, d2))) => {
                let c = k1.cmp(k2);
                if c != Ordering::Equal {
                    return c;
                }
                let c = cmp(d1, d2);
                if c != Ordering::Equal {
                    return c;
                }
            }
        }
    }
}

/// The functions that OCaml defines inside `ty__compare`, where they close
/// over `normalize_lists`; here it is their first parameter.
///
/// The `phys_equal` shortcuts of the OCaml inside the comparison of shapes
/// (`typing_defs_core.ml`, `ty__compare`) are not ported: they only skip
/// comparisons whose result is 0. [`ty_compare`] has one on the node instead.
mod ty_compare_impl {
    use super::*;

    #[allow(non_snake_case)]
    pub(super) fn ty__compare(normalize_lists: bool, ty_1: &Ty_, ty_2: &Ty_) -> Ordering {
        use Ty_::*;
        match (ty_1, ty_2) {
            // Both or in Localized Phase
            (Tprim(ty1), Tprim(ty2)) => ty1.cmp(ty2),
            (Toption(ty), Toption(ty2)) => ty_compare(normalize_lists, ty, ty2),
            (TvecOrDict(tk, tv), TvecOrDict(tk2, tv2)) => {
                chain_compare(ty_compare(normalize_lists, tk, tk2), || {
                    ty_compare(normalize_lists, tv, tv2)
                })
            }
            (Tfun(fty), Tfun(fty2)) => tfun_compare(normalize_lists, fty, fty2),
            (Tunion(tyl1), Tunion(tyl2)) | (Tintersection(tyl1), Tintersection(tyl2)) => {
                super::tyl_compare(normalize_lists, Some(normalize_lists), tyl1, tyl2)
            }
            (Ttuple(t1), Ttuple(t2)) => tuple_type_compare(normalize_lists, t1, t2),
            (Tgeneric(n1), Tgeneric(n2)) => n1.cmp(n2),
            (Tnewtype(id, tyl, cstr1), Tnewtype(id2, tyl2, cstr2)) => {
                chain_compare(id.cmp(id2), || {
                    chain_compare(super::tyl_compare(false, None, tyl, tyl2), || {
                        ty_compare(normalize_lists, cstr1, cstr2)
                    })
                })
            }
            (Tdependent(d1, cstr1), Tdependent(d2, cstr2)) => {
                chain_compare(d1.cmp(d2), || ty_compare(normalize_lists, cstr1, cstr2))
            }
            // An instance of a class or interface, ty list are the arguments
            (Tclass(id, exact, tyl), Tclass(id2, exact2, tyl2)) => {
                chain_compare(id.1.cmp(&id2.1), || {
                    chain_compare(super::tyl_compare(false, None, tyl, tyl2), || {
                        exact_compare(exact, exact2)
                    })
                })
            }
            (Tshape(s1), Tshape(s2)) => shape_type_compare(normalize_lists, s1, s2),
            (Tvar(v1), Tvar(v2)) => v1.cmp(v2),
            (Taccess(TaccessType(ty1, id1)), Taccess(TaccessType(ty2, id2))) => {
                chain_compare(ty_compare(normalize_lists, ty1, ty2), || id1.1.cmp(&id2.1))
            }
            (Tneg(neg1), Tneg(neg2)) => compare_type_predicate(neg1, neg2),
            (Tnonnull, Tnonnull) => Ordering::Equal,
            (Tdynamic(_), Tdynamic(_)) => Ordering::Equal,
            (Tlabel(name1), Tlabel(name2)) => name1.cmp(name2),
            (TclassPtr(ty1), TclassPtr(ty2)) => ty_compare(normalize_lists, ty1, ty2),
            (
                Tprim(_)
                | Toption(_)
                | TvecOrDict(_, _)
                | Tfun(_)
                | Tintersection(_)
                | Tunion(_)
                | Ttuple(_)
                | Tgeneric(_)
                | Tnewtype(_, _, _)
                | Tdependent(_, _)
                | Tclass(_, _, _)
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
            ) => ty_con_ordinal_(ty_1).cmp(&ty_con_ordinal_(ty_2)),
        }
    }

    fn shape_field_type_compare(
        normalize_lists: bool,
        sft1: &ShapeFieldType,
        sft2: &ShapeFieldType,
    ) -> Ordering {
        let ShapeFieldType {
            ty: ty1,
            optional: optional1,
        } = sft1;
        let ShapeFieldType {
            ty: ty2,
            optional: optional2,
        } = sft2;
        chain_compare(ty_compare(normalize_lists, ty1, ty2), || {
            optional1.cmp(optional2)
        })
    }

    fn shape_type_compare(normalize_lists: bool, s1: &ShapeType, s2: &ShapeType) -> Ordering {
        match (s1, s2) {
            (ShapeType::ShapeSimple(_), ShapeType::ShapeSplat(_)) => Ordering::Less,
            (ShapeType::ShapeSplat(_), ShapeType::ShapeSimple(_)) => Ordering::Greater,
            (
                ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems: e1 }),
                ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems: e2 }),
            ) => super::tyl_compare(false, None, e1, e2),
            (
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: shape_origin1,
                    unknown_value: unknown_fields_type1,
                    fields: fields1,
                }),
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: shape_origin2,
                    unknown_value: unknown_fields_type2,
                    fields: fields2,
                }),
            ) => {
                if same_type_origin(shape_origin1, shape_origin2) {
                    Ordering::Equal
                } else {
                    chain_compare(
                        ty_compare(normalize_lists, unknown_fields_type1, unknown_fields_type2),
                        || {
                            t_shape_map::compare(
                                |sft1, sft2| shape_field_type_compare(normalize_lists, sft1, sft2),
                                fields1,
                                fields2,
                            )
                        },
                    )
                }
            }
        }
    }

    fn tuple_extra_compare(normalize_lists: bool, t1: &TupleExtra, t2: &TupleExtra) -> Ordering {
        match (t1, t2) {
            (TupleExtra::Tvariadic(_), TupleExtra::Tsplat(_)) => Ordering::Less,
            (TupleExtra::Tsplat(_), TupleExtra::Tvariadic(_)) => Ordering::Greater,
            (TupleExtra::Tsplat(t_splat1), TupleExtra::Tsplat(t_splat2)) => {
                ty_compare(normalize_lists, t_splat1, t_splat2)
            }
            (TupleExtra::Tvariadic(t_variadic1), TupleExtra::Tvariadic(t_variadic2)) => {
                ty_compare(normalize_lists, t_variadic1, t_variadic2)
            }
        }
    }

    fn tuple_type_compare(normalize_lists: bool, t1: &TupleType, t2: &TupleType) -> Ordering {
        let TupleType {
            required: t_required1,
            optional: t_optional1,
            extra: t_extra1,
        } = t1;
        let TupleType {
            required: t_required2,
            optional: t_optional2,
            extra: t_extra2,
        } = t2;
        chain_compare(
            crate::rt::ocaml_list::compare(
                |a, b| ty_compare(normalize_lists, a, b),
                t_required1,
                t_required2,
            ),
            || {
                chain_compare(
                    crate::rt::ocaml_list::compare(
                        |a, b| ty_compare(normalize_lists, a, b),
                        t_optional1,
                        t_optional2,
                    ),
                    || tuple_extra_compare(normalize_lists, t_extra1, t_extra2),
                )
            },
        )
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
        chain_compare(id1.cmp(&id2), || s1.cmp(s2))
    }

    fn user_attribute_compare(ua1: &UserAttribute, ua2: &UserAttribute) -> Ordering {
        let UserAttribute {
            name: name1,
            params: params1,
            raw_val: _,
        } = ua1;
        let UserAttribute {
            name: name2,
            params: params2,
            raw_val: _,
        } = ua2;
        chain_compare(name1.1.cmp(&name2.1), || {
            crate::rt::ocaml_list::compare(user_attribute_param_compare, params1, params2)
        })
    }

    fn user_attributes_compare(ual1: &[UserAttribute], ual2: &[UserAttribute]) -> Ordering {
        crate::rt::ocaml_list::compare(user_attribute_compare, ual1, ual2)
    }

    fn tparam_compare(normalize_lists: bool, tp1: &Tparam, tp2: &Tparam) -> Ordering {
        let Tparam {
            // Type parameters on functions are always marked invariant
            variance: _,
            name: name1,
            constraints: constraints1,
            reified: reified1,
            user_attributes: user_attributes1,
        } = tp1;
        let Tparam {
            variance: _,
            name: name2,
            constraints: constraints2,
            reified: reified2,
            user_attributes: user_attributes2,
        } = tp2;
        chain_compare(name1.1.cmp(&name2.1), || {
            chain_compare(
                constraints_compare(normalize_lists, constraints1, constraints2),
                || {
                    chain_compare(
                        user_attributes_compare(user_attributes1, user_attributes2),
                        || reified1.cmp(reified2),
                    )
                },
            )
        })
    }

    fn tparams_compare(normalize_lists: bool, tpl1: &[Tparam], tpl2: &[Tparam]) -> Ordering {
        crate::rt::ocaml_list::compare(|a, b| tparam_compare(normalize_lists, a, b), tpl1, tpl2)
    }

    fn constraints_compare(
        normalize_lists: bool,
        cl1: &[(ast_defs::ConstraintKind, Ty)],
        cl2: &[(ast_defs::ConstraintKind, Ty)],
    ) -> Ordering {
        crate::rt::ocaml_list::compare(|a, b| constraint_compare(normalize_lists, a, b), cl1, cl2)
    }

    fn constraint_compare(
        normalize_lists: bool,
        (ck1, ty1): &(ast_defs::ConstraintKind, Ty),
        (ck2, ty2): &(ast_defs::ConstraintKind, Ty),
    ) -> Ordering {
        chain_compare(ck1.cmp(ck2), || ty_compare(normalize_lists, ty1, ty2))
    }

    fn where_constraint_compare(
        normalize_lists: bool,
        WhereConstraint(ty1a, ck1, ty1b): &WhereConstraint,
        WhereConstraint(ty2a, ck2, ty2b): &WhereConstraint,
    ) -> Ordering {
        chain_compare(ck1.cmp(ck2), || {
            chain_compare(ty_compare(normalize_lists, ty1a, ty2a), || {
                ty_compare(normalize_lists, ty1b, ty2b)
            })
        })
    }

    fn where_constraints_compare(
        normalize_lists: bool,
        cl1: &[WhereConstraint],
        cl2: &[WhereConstraint],
    ) -> Ordering {
        crate::rt::ocaml_list::compare(
            |a, b| where_constraint_compare(normalize_lists, a, b),
            cl1,
            cl2,
        )
    }

    /// We match every field rather than using field selection syntax. This guards against future additions to function type elements
    fn tfun_compare(normalize_lists: bool, fty1: &FunType, fty2: &FunType) -> Ordering {
        let FunType {
            ret: ret1,
            params: params1,
            flags: flags1,
            implicit_params: implicit_params1,
            tparams: tparams1,
            where_constraints: where_constraints1,
            instantiated: inst1,
        } = fty1;
        let FunType {
            ret: ret2,
            params: params2,
            flags: flags2,
            implicit_params: implicit_params2,
            tparams: tparams2,
            where_constraints: where_constraints2,
            instantiated: inst2,
        } = fty2;
        chain_compare(ty_compare(normalize_lists, ret1, ret2), || {
            // (the OCaml calls the toplevel ft_params_compare without ~normalize_lists)
            chain_compare(super::ft_params_compare(None, params1, params2), || {
                chain_compare(tparams_compare(normalize_lists, tparams1, tparams2), || {
                    chain_compare(
                        where_constraints_compare(
                            normalize_lists,
                            where_constraints1,
                            where_constraints2,
                        ),
                        || {
                            chain_compare(flags1.cmp(flags2), || {
                                let FunImplicitParams {
                                    capability: capability1,
                                } = implicit_params1;
                                let FunImplicitParams {
                                    capability: capability2,
                                } = implicit_params2;
                                chain_compare(
                                    capability_compare(normalize_lists, capability1, capability2),
                                    || inst1.cmp(inst2),
                                )
                            })
                        },
                    )
                })
            })
        })
    }

    fn capability_compare(normalize_lists: bool, cap1: &Capability, cap2: &Capability) -> Ordering {
        match (cap1, cap2) {
            (Capability::CapDefaults(_), Capability::CapDefaults(_)) => Ordering::Equal,
            (Capability::CapDefaults(_), Capability::CapTy(_)) => Ordering::Less,
            (Capability::CapTy(_), Capability::CapDefaults(_)) => Ordering::Greater,
            (Capability::CapTy(ty1), Capability::CapTy(ty2)) => {
                ty_compare(normalize_lists, ty1, ty2)
            }
        }
    }

    pub(super) fn ty_compare(normalize_lists: bool, ty1: &Ty, ty2: &Ty) -> Ordering {
        // A node is equal to itself (the comparison is a total order): not
        // in the OCaml, which compares the shared parts of two types again.
        if Rc::ptr_eq(&ty1.1, &ty2.1) {
            return Ordering::Equal;
        }
        ty__compare(normalize_lists, get_node(ty1), get_node(ty2))
    }
}

/// Compare two types syntactically, ignoring reason information and other
/// small differences that do not affect type inference behaviour. This
/// comparison function can be used to construct tree-based sets of types,
/// or to compare two types for "exact" equality.
/// Note that this function does *not* expand type variables, or type
/// aliases.
/// But if ty_compare ty1 ty2 = 0, then the types must not be distinguishable
/// by any typing rules.
// The OCaml name (`ty_` + `_compare`), kept: its snake case, `ty_compare`, is
// the function on `ty` below.
#[allow(non_snake_case)]
pub fn ty__compare(normalize_lists: Option<bool>, ty_1: &Ty_, ty_2: &Ty_) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    ty_compare_impl::ty__compare(normalize_lists, ty_1, ty_2)
}

pub fn compare_type_predicate(
    TypePredicate(_, p1): &TypePredicate,
    TypePredicate(_, p2): &TypePredicate,
) -> Ordering {
    match (p1, p2) {
        (TypePredicate_::IsTag(tag1), TypePredicate_::IsTag(tag2)) => compare_type_tag(tag1, tag2),
        (TypePredicate_::IsTupleOf(tp1), TypePredicate_::IsTupleOf(tp2)) => {
            compare_tuple_predicate(tp1, tp2)
        }
        (TypePredicate_::IsShapeOf(sp1), TypePredicate_::IsShapeOf(sp2)) => {
            compare_shape_predicate(sp1, sp2)
        }
        (TypePredicate_::IsNot(p1), TypePredicate_::IsNot(p2)) => compare_type_predicate(p1, p2),
        // (As in OCaml, two `IsUnionOf` end up here and compare equal.)
        _ => type_predicate__con_ordinal(p1).cmp(&type_predicate__con_ordinal(p2)),
    }
}

fn compare_type_tag_generic(g1: &TypeTagGeneric, g2: &TypeTagGeneric) -> Ordering {
    match (g1, g2) {
        (TypeTagGeneric::Wildcard(id1), TypeTagGeneric::Wildcard(id2)) => id1.cmp(id2),
        (TypeTagGeneric::Filled(ty1), TypeTagGeneric::Filled(ty2)) => ty_compare(None, ty1, ty2),
        (TypeTagGeneric::Wildcard(_), TypeTagGeneric::Filled(_)) => Ordering::Greater,
        (TypeTagGeneric::Filled(_), TypeTagGeneric::Wildcard(_)) => Ordering::Less,
    }
}

fn compare_type_tag(tag1: &TypeTag, tag2: &TypeTag) -> Ordering {
    match (tag1, tag2) {
        (TypeTag::BoolTag, TypeTag::BoolTag)
        | (TypeTag::IntTag, TypeTag::IntTag)
        | (TypeTag::ArraykeyTag, TypeTag::ArraykeyTag)
        | (TypeTag::FloatTag, TypeTag::FloatTag)
        | (TypeTag::NumTag, TypeTag::NumTag)
        | (TypeTag::ResourceTag, TypeTag::ResourceTag)
        | (TypeTag::NullTag, TypeTag::NullTag) => Ordering::Equal,
        (TypeTag::ClassTag(id1, args1), TypeTag::ClassTag(id2, args2)) => {
            chain_compare(id1.cmp(id2), || {
                crate::rt::ocaml_list::compare(compare_type_tag_generic, args1, args2)
            })
        }
        (TypeTag::EnumTag(id1), TypeTag::EnumTag(id2)) => id1.cmp(id2),
        (
            TypeTag::GenericTag {
                name: n1,
                from_like: b1,
            },
            TypeTag::GenericTag {
                name: n2,
                from_like: b2,
            },
        ) => chain_compare(n1.cmp(n2), || b1.cmp(b2)),
        _ => type_tag_con_ordinal(tag1).cmp(&type_tag_con_ordinal(tag2)),
    }
}

fn compare_tuple_predicate(tp1: &TuplePredicate, tp2: &TuplePredicate) -> Ordering {
    crate::rt::ocaml_list::compare(compare_type_predicate, &tp1.required, &tp2.required)
}

fn compare_shape_predicate(sp1: &ShapePredicate, sp2: &ShapePredicate) -> Ordering {
    let ShapePredicate {
        allows_unknown_fields: u1,
        fields: f1,
    } = sp1;
    let ShapePredicate {
        allows_unknown_fields: u2,
        fields: f2,
    } = sp2;
    chain_compare(
        t_shape_map::compare(compare_shape_field_predicate, f1, f2),
        || u1.cmp(u2),
    )
}

fn compare_shape_field_predicate(
    sfp1: &ShapeFieldPredicate,
    sfp2: &ShapeFieldPredicate,
) -> Ordering {
    let ShapeFieldPredicate {
        optional: o1,
        predicate: p1,
    } = sfp1;
    let ShapeFieldPredicate {
        optional: o2,
        predicate: p2,
    } = sfp2;
    chain_compare(compare_type_predicate(p1, p2), || o1.cmp(o2))
}

pub fn ty_compare(normalize_lists: Option<bool>, ty1: &Ty, ty2: &Ty) -> Ordering {
    // (See `ty_compare_impl::ty_compare`.)
    if Rc::ptr_eq(&ty1.1, &ty2.1) {
        return Ordering::Equal;
    }
    ty__compare(normalize_lists, get_node(ty1), get_node(ty2))
}

pub fn tyl_compare(
    sort: bool,
    normalize_lists: Option<bool>,
    tyl1: &[Ty],
    tyl2: &[Ty],
) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    if sort {
        let mut tyl1: Vec<&Ty> = tyl1.iter().collect();
        let mut tyl2: Vec<&Ty> = tyl2.iter().collect();
        tyl1.sort_by(|a, b| ty_compare(None, a, b));
        tyl2.sort_by(|a, b| ty_compare(None, a, b));
        crate::rt::ocaml_list::compare(|a, b| ty_compare(Some(normalize_lists), a, b), &tyl1, &tyl2)
    } else {
        crate::rt::ocaml_list::compare(|a, b| ty_compare(Some(normalize_lists), a, b), tyl1, tyl2)
    }
}

fn ft_param_compare(
    normalize_lists: Option<bool>,
    param1: &FunParam,
    param2: &FunParam,
) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    chain_compare(
        ty_compare(Some(normalize_lists), &param1.type_, &param2.type_),
        || {
            chain_compare(param1.flags.cmp(&param2.flags), || {
                if param1.flags.contains(FunParamFlags::NAMED) {
                    option_compare(
                        |a: &String, b: &String| a.cmp(b),
                        param1.name.as_ref(),
                        param2.name.as_ref(),
                    )
                } else {
                    Ordering::Equal
                }
            })
        },
    )
}

pub fn ft_params_compare(
    normalize_lists: Option<bool>,
    params1: &[FunParam],
    params2: &[FunParam],
) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    crate::rt::ocaml_list::compare(
        |a, b| ft_param_compare(Some(normalize_lists), a, b),
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
                chain_compare(tyl_compare(true, None, &b1.lower, &b2.lower), || {
                    tyl_compare(true, None, &b1.upper, &b2.upper)
                })
            }
            (RefinedConstBound::TRexact(ty1), RefinedConstBound::TRexact(ty2)) => {
                ty_compare(None, ty1, ty2)
            }
        }
    }
}

fn class_refinement_compare(cr1: &ClassRefinement, cr2: &ClassRefinement) -> Ordering {
    let ClassRefinement { cr_consts: rcs1 } = cr1;
    let ClassRefinement { cr_consts: rcs2 } = cr2;
    s_map_compare(refined_const_compare, rcs1, rcs2)
}

fn exact_compare(e1: &Exact, e2: &Exact) -> Ordering {
    match (e1, e2) {
        (Exact::Exact, Exact::Exact) => Ordering::Equal,
        (Exact::Nonexact(_), Exact::Exact) => Ordering::Greater,
        (Exact::Exact, Exact::Nonexact(_)) => Ordering::Less,
        (Exact::Nonexact(r1), Exact::Nonexact(r2)) => class_refinement_compare(r1, r2),
    }
}

/// Whether equal modulo reason and position info.
pub fn exact_equal(e1: &Exact, e2: &Exact) -> bool {
    exact_compare(e1, e2) == Ordering::Equal
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        ty_compare(None, self, other) == Ordering::Equal
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
        ty_compare(None, self, other)
    }
}

impl PartialEq for Ty_ {
    fn eq(&self, other: &Self) -> bool {
        ty__compare(None, self, other) == Ordering::Equal
    }
}
impl Eq for Ty_ {}
impl PartialOrd for Ty_ {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Ty_ {
    fn cmp(&self, other: &Self) -> Ordering {
        ty__compare(None, self, other)
    }
}

/// `hash_fold_ty` (`[@@deriving hash]`), written by hand so that it agrees
/// with `==` (that is, with [`ty_compare`]): everything the comparison ignores
/// (reasons, positions, the shadow type variable of `Tdynamic`, the variance of
/// type parameters, the names of parameters that are not named, the origin of
/// shapes, the contents of `IsUnionOf`, the order of the bounds of refined
/// constants) is left out.
///
/// The comparison says that two shapes with the same origin are equal without
/// looking at them, and "two types with the same origin are necessarily
/// identical" (see `type_origin`): the hash relies on that.
mod ty_hash_impl {
    use std::hash::Hash;
    use std::hash::Hasher;

    use super::*;

    pub(super) fn hash_ty<H: Hasher>(ty: &Ty, state: &mut H) {
        hash_ty_(get_node(ty), state)
    }

    fn hash_tyl<H: Hasher>(tyl: &[Ty], state: &mut H) {
        tyl.len().hash(state);
        for ty in tyl {
            hash_ty(ty, state);
        }
    }

    /// For the lists that are compared with `tyl_compare ~sort:true`.
    fn hash_tyl_sorted<H: Hasher>(tyl: &[Ty], state: &mut H) {
        let mut tyl: Vec<&Ty> = tyl.iter().collect();
        tyl.sort_by(|a, b| ty_compare(None, a, b));
        tyl.len().hash(state);
        for ty in tyl {
            hash_ty(ty, state);
        }
    }

    pub(super) fn hash_ty_<H: Hasher>(ty_: &Ty_, state: &mut H) {
        match ty_ {
            Ty_::Tany(_) => 0u8.hash(state),
            Ty_::Tnonnull => 1u8.hash(state),
            Ty_::Tdynamic(_) => 2u8.hash(state),
            Ty_::Toption(ty) => {
                3u8.hash(state);
                hash_ty(ty, state);
            }
            Ty_::Tprim(p) => {
                4u8.hash(state);
                p.hash(state);
            }
            Ty_::Tfun(ft) => {
                5u8.hash(state);
                hash_fun_type(ft, state);
            }
            Ty_::Ttuple(TupleType {
                required,
                optional,
                extra,
            }) => {
                6u8.hash(state);
                hash_tyl(required, state);
                hash_tyl(optional, state);
                match extra {
                    TupleExtra::Tvariadic(ty) => {
                        0u8.hash(state);
                        hash_ty(ty, state);
                    }
                    TupleExtra::Tsplat(ty) => {
                        1u8.hash(state);
                        hash_ty(ty, state);
                    }
                }
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                7u8.hash(state);
                hash_tyl(ss_elems, state);
            }
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: _,
                unknown_value,
                fields,
            })) => {
                8u8.hash(state);
                hash_ty(unknown_value, state);
                fields.len().hash(state);
                for (k, ShapeFieldType { optional, ty }) in fields {
                    hash_tshape_field_name(&k.0, state);
                    optional.hash(state);
                    hash_ty(ty, state);
                }
            }
            Ty_::Tgeneric(n) => {
                9u8.hash(state);
                n.hash(state);
            }
            Ty_::Tunion(tyl) => {
                10u8.hash(state);
                hash_tyl(tyl, state);
            }
            Ty_::Tintersection(tyl) => {
                11u8.hash(state);
                hash_tyl(tyl, state);
            }
            Ty_::TvecOrDict(tk, tv) => {
                12u8.hash(state);
                hash_ty(tk, state);
                hash_ty(tv, state);
            }
            Ty_::Taccess(TaccessType(ty, id)) => {
                13u8.hash(state);
                hash_ty(ty, state);
                id.1.hash(state);
            }
            Ty_::TclassPtr(ty) => {
                14u8.hash(state);
                hash_ty(ty, state);
            }
            Ty_::Tvar(v) => {
                15u8.hash(state);
                v.hash(state);
            }
            Ty_::Tnewtype(id, tyl, cstr) => {
                16u8.hash(state);
                id.hash(state);
                hash_tyl(tyl, state);
                hash_ty(cstr, state);
            }
            Ty_::Tdependent(d, cstr) => {
                17u8.hash(state);
                d.hash(state);
                hash_ty(cstr, state);
            }
            Ty_::Tclass(id, exact, tyl) => {
                18u8.hash(state);
                id.1.hash(state);
                hash_tyl(tyl, state);
                match exact {
                    Exact::Exact => 0u8.hash(state),
                    Exact::Nonexact(ClassRefinement { cr_consts }) => {
                        1u8.hash(state);
                        cr_consts.len().hash(state);
                        for (k, RefinedConst { bound, is_ctx }) in cr_consts {
                            k.hash(state);
                            is_ctx.hash(state);
                            match bound {
                                RefinedConstBound::TRexact(ty) => {
                                    0u8.hash(state);
                                    hash_ty(ty, state);
                                }
                                RefinedConstBound::TRloose(RefinedConstBounds { lower, upper }) => {
                                    1u8.hash(state);
                                    hash_tyl_sorted(lower, state);
                                    hash_tyl_sorted(upper, state);
                                }
                            }
                        }
                    }
                }
            }
            Ty_::Tneg(p) => {
                19u8.hash(state);
                hash_type_predicate(p, state);
            }
            Ty_::Tlabel(n) => {
                20u8.hash(state);
                n.hash(state);
            }
        }
    }

    fn hash_tshape_field_name<H: Hasher>(x: &TshapeFieldName, state: &mut H) {
        match x {
            TshapeFieldName::TSFregexGroup(PosString(_, s)) => {
                0u8.hash(state);
                s.hash(state);
            }
            TshapeFieldName::TSFlitStr(PosByteString(_, s)) => {
                1u8.hash(state);
                s.hash(state);
            }
            TshapeFieldName::TSFclassConst((_, s1), PosString(_, s2)) => {
                2u8.hash(state);
                s1.hash(state);
                s2.hash(state);
            }
        }
    }

    fn hash_fun_type<H: Hasher>(ft: &FunType, state: &mut H) {
        let FunType {
            tparams,
            where_constraints,
            params,
            implicit_params: FunImplicitParams { capability },
            ret,
            flags,
            instantiated,
        } = ft;
        hash_ty(ret, state);
        params.len().hash(state);
        for FunParam {
            pos: _,
            name,
            type_,
            flags,
            def_value: _,
        } in params
        {
            hash_ty(type_, state);
            flags.hash(state);
            if flags.contains(FunParamFlags::NAMED) {
                name.hash(state);
            }
        }
        tparams.len().hash(state);
        for Tparam {
            variance: _,
            name,
            constraints,
            reified,
            user_attributes,
        } in tparams
        {
            name.1.hash(state);
            constraints.len().hash(state);
            for (ck, ty) in constraints {
                ck.hash(state);
                hash_ty(ty, state);
            }
            user_attributes.len().hash(state);
            for UserAttribute {
                name,
                params,
                raw_val: _,
            } in user_attributes
            {
                name.1.hash(state);
                params.len().hash(state);
                for p in params {
                    match p {
                        UserAttributeParam::Classname(s) => {
                            0u8.hash(state);
                            s.as_bytes().hash(state);
                        }
                        UserAttributeParam::EnumClassLabel(s) => {
                            1u8.hash(state);
                            s.as_bytes().hash(state);
                        }
                        UserAttributeParam::String(s) => {
                            2u8.hash(state);
                            s.as_slice().hash(state);
                        }
                        UserAttributeParam::Int(s) => {
                            3u8.hash(state);
                            s.as_bytes().hash(state);
                        }
                    }
                }
            }
            reified.hash(state);
        }
        where_constraints.len().hash(state);
        for WhereConstraint(ty1, ck, ty2) in where_constraints {
            ck.hash(state);
            hash_ty(ty1, state);
            hash_ty(ty2, state);
        }
        flags.hash(state);
        match capability {
            Capability::CapDefaults(_) => 0u8.hash(state),
            Capability::CapTy(ty) => {
                1u8.hash(state);
                hash_ty(ty, state);
            }
        }
        instantiated.hash(state);
    }

    fn hash_type_predicate<H: Hasher>(TypePredicate(_, p): &TypePredicate, state: &mut H) {
        match p {
            TypePredicate_::IsTag(tag) => {
                0u8.hash(state);
                match tag {
                    TypeTag::BoolTag => 0u8.hash(state),
                    TypeTag::IntTag => 1u8.hash(state),
                    TypeTag::ArraykeyTag => 3u8.hash(state),
                    TypeTag::FloatTag => 4u8.hash(state),
                    TypeTag::NumTag => 5u8.hash(state),
                    TypeTag::ResourceTag => 6u8.hash(state),
                    TypeTag::NullTag => 7u8.hash(state),
                    TypeTag::ClassTag(id, args) => {
                        8u8.hash(state);
                        id.hash(state);
                        args.len().hash(state);
                        for g in args {
                            match g {
                                TypeTagGeneric::Filled(ty) => {
                                    0u8.hash(state);
                                    hash_ty(ty, state);
                                }
                                TypeTagGeneric::Wildcard(id) => {
                                    1u8.hash(state);
                                    id.hash(state);
                                }
                            }
                        }
                    }
                    TypeTag::EnumTag(id) => {
                        9u8.hash(state);
                        id.hash(state);
                    }
                    TypeTag::GenericTag { name, from_like } => {
                        10u8.hash(state);
                        name.hash(state);
                        from_like.hash(state);
                    }
                }
            }
            TypePredicate_::IsTupleOf(TuplePredicate { required }) => {
                1u8.hash(state);
                required.len().hash(state);
                for p in required {
                    hash_type_predicate(p, state);
                }
            }
            TypePredicate_::IsShapeOf(ShapePredicate {
                allows_unknown_fields,
                fields,
            }) => {
                2u8.hash(state);
                fields.len().hash(state);
                for (
                    k,
                    ShapeFieldPredicate {
                        optional,
                        predicate,
                    },
                ) in fields
                {
                    hash_tshape_field_name(&k.0, state);
                    hash_type_predicate(predicate, state);
                    optional.hash(state);
                }
                allows_unknown_fields.hash(state);
            }
            // compare_type_predicate does not look into IsUnionOf
            TypePredicate_::IsUnionOf(_) => 3u8.hash(state),
            TypePredicate_::IsNot(p) => {
                4u8.hash(state);
                hash_type_predicate(p, state);
            }
        }
    }
}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ty_hash_impl::hash_ty(self, state)
    }
}

impl std::hash::Hash for Ty_ {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ty_hash_impl::hash_ty_(self, state)
    }
}

pub fn map_reason(ty: Ty, f: impl FnOnce(Reason) -> Reason) -> Ty {
    let Ty(r, ty) = ty;
    Ty(f(r), ty)
}

pub fn map_ty(ty: Ty, f: impl FnOnce(Ty_) -> Ty_) -> Ty {
    let Ty(r, ty) = ty;
    Ty(r, Rc::new(TyNode::new(f(unwrap_node(ty)))))
}

pub fn with_reason(ty: Ty, r: Reason) -> Ty {
    map_reason(ty, |_r| r)
}

pub fn get_pos(t: &Ty) -> PosOrDecl {
    reason::to_pos(get_reason(t))
}

/// Hack keyword for this visibility
pub fn string_of_visibility(v: &CeVisibility) -> &'static str {
    match v {
        CeVisibility::Vpublic => "public",
        CeVisibility::Vprivate(_) => "private",
        CeVisibility::Vprotected(_) => "protected",
        CeVisibility::Vinternal(_) => "internal",
        CeVisibility::VprotectedInternal { .. } => "protected internal",
    }
}

/// Dedicated functions with more easily discoverable names
pub fn compare_locl_ty(normalize_lists: Option<bool>, ty1: &Ty, ty2: &Ty) -> Ordering {
    ty_compare(normalize_lists, ty1, ty2)
}

pub fn tyl_equal(tyl1: &[Ty], tyl2: &[Ty]) -> bool {
    tyl_compare(false, None, tyl1, tyl2) == Ordering::Equal
}

fn class_id_con_ordinal<Ex, En>(cid: &aast::ClassId_<Ex, En>) -> isize {
    match cid {
        aast::ClassId_::CIparent => 0,
        aast::ClassId_::CIself => 1,
        aast::ClassId_::CIstatic => 2,
        aast::ClassId_::CIexpr(_) => 3,
        aast::ClassId_::CI(_) => 4,
        aast::ClassId_::CIreified(_) => 5,
    }
}

pub fn class_id_compare<A, B, C, D>(
    cid1: &aast::ClassId_<A, B>,
    cid2: &aast::ClassId_<C, D>,
) -> Ordering {
    match (cid1, cid2) {
        (aast::ClassId_::CIexpr(_e1), aast::ClassId_::CIexpr(_e2)) => Ordering::Equal,
        (aast::ClassId_::CI(ast_defs::Id(_, id1)), aast::ClassId_::CI(ast_defs::Id(_, id2))) => {
            id1.cmp(id2)
        }
        (
            aast::ClassId_::CIreified(ast_defs::Id(_, id1)),
            aast::ClassId_::CIreified(ast_defs::Id(_, id2)),
        ) => id1.cmp(id2),
        // (cid2 first, as in OCaml)
        _ => class_id_con_ordinal(cid2).cmp(&class_id_con_ordinal(cid1)),
    }
}

pub fn class_id_equal<A, B, C, D>(
    cid1: &aast::ClassId_<A, B>,
    cid2: &aast::ClassId_<C, D>,
) -> bool {
    class_id_compare(cid1, cid2) == Ordering::Equal
}

pub fn ty_equal(normalize_lists: Option<bool>, ty1: &Ty, ty2: &Ty) -> bool {
    let normalize_lists = normalize_lists.unwrap_or(false);
    std::ptr::eq(get_node(ty1), get_node(ty2))
        || ty_compare(Some(normalize_lists), ty1, ty2) == Ordering::Equal
}

pub fn equal_locl_ty(ty1: &Ty, ty2: &Ty) -> bool {
    ty_equal(None, ty1, ty2)
}

pub fn equal_locl_ty_(ty_1: &Ty_, ty_2: &Ty_) -> bool {
    ty__compare(None, ty_1, ty_2) == Ordering::Equal
}

pub fn equal_type_predicate(p1: &TypePredicate, p2: &TypePredicate) -> bool {
    compare_type_predicate(p1, p2) == Ordering::Equal
}

// ---------------------------------------------------------------------------
// Locl_subst
// ---------------------------------------------------------------------------

pub mod locl_subst {
    use super::*;

    /// `locl_ty S_map.t`
    pub type T = im::OrdMap<String, Ty>;

    /// `combine_reasons ~src ~dest`
    pub type CombineReasons<'a> = &'a dyn Fn(Reason, Reason) -> Reason;

    fn apply_ty(ty: Ty, subst: &T, combine_reasons: CombineReasons<'_>) -> Ty {
        let Ty(r, node) = ty;
        match (r, unwrap_node(node)) {
            (reason_src, Ty_::Tgeneric(nm)) => match subst.get(&nm) {
                Some(ty_subst) => map_reason(ty_subst.clone(), |reason_dest| {
                    combine_reasons(reason_src, reason_dest)
                }),
                _ => mk((reason_src, Ty_::Tgeneric(nm))),
            },
            (r, Ty_::Toption(ty)) => mk((r, Ty_::Toption(apply_ty(ty, subst, combine_reasons)))),
            (r, Ty_::TclassPtr(ty)) => {
                mk((r, Ty_::TclassPtr(apply_ty(ty, subst, combine_reasons))))
            }
            (r, Ty_::Taccess(TaccessType(ty, pos_id))) => mk((
                r,
                Ty_::Taccess(TaccessType(apply_ty(ty, subst, combine_reasons), pos_id)),
            )),
            (r, Ty_::TvecOrDict(ty_k, ty_v)) => mk((
                r,
                Ty_::TvecOrDict(
                    apply_ty(ty_k, subst, combine_reasons),
                    apply_ty(ty_v, subst, combine_reasons),
                ),
            )),
            (r, Ty_::Ttuple(tuple_ty)) => mk((
                r,
                Ty_::Ttuple(apply_tuple(tuple_ty, subst, combine_reasons)),
            )),
            (r, Ty_::Tunion(tys)) => mk((r, Ty_::Tunion(apply_tyl(tys, subst, combine_reasons)))),
            (r, Ty_::Tintersection(tys)) => mk((
                r,
                Ty_::Tintersection(apply_tyl(tys, subst, combine_reasons)),
            )),
            (r, Ty_::Tfun(fun_ty)) => mk((r, Ty_::Tfun(std::rc::Rc::new(apply_fun(std::rc::Rc::unwrap_or_clone(fun_ty), subst, combine_reasons))))),
            (r, Ty_::Tshape(shape_ty)) => mk((
                r,
                Ty_::Tshape(apply_shape(shape_ty, subst, combine_reasons)),
            )),
            (r, Ty_::Tnewtype(nm, ty_params, ty_bound)) => mk((
                r,
                Ty_::Tnewtype(
                    nm,
                    apply_tyl(ty_params, subst, combine_reasons),
                    apply_ty(ty_bound, subst, combine_reasons),
                ),
            )),
            (r, Ty_::Tdependent(dep_ty, ty)) => mk((
                r,
                Ty_::Tdependent(dep_ty, apply_ty(ty, subst, combine_reasons)),
            )),
            (r, Ty_::Tclass(id, exact, tys)) => {
                let exact = apply_exact(exact, subst, combine_reasons);
                mk((
                    r,
                    Ty_::Tclass(id, exact, apply_tyl(tys, subst, combine_reasons)),
                ))
            }
            (
                r,
                ty_ @ (Ty_::Tvar(_)
                | Ty_::Tany(_)
                | Ty_::Tnonnull
                | Ty_::Tdynamic(_)
                | Ty_::Tprim(_)
                | Ty_::Tlabel(_)
                | Ty_::Tneg(_)),
            ) => mk((r, ty_)),
        }
    }

    /// `List.map tys ~f:(apply_ty ~subst ~combine_reasons)`
    fn apply_tyl(tys: Vec<Ty>, subst: &T, combine_reasons: CombineReasons<'_>) -> Vec<Ty> {
        tys.into_iter()
            .map(|ty| apply_ty(ty, subst, combine_reasons))
            .collect()
    }

    fn apply_tuple(t: TupleType, subst: &T, combine_reasons: CombineReasons<'_>) -> TupleType {
        let TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        } = t;
        let t_required = apply_tyl(t_required, subst, combine_reasons);
        let t_optional = apply_tyl(t_optional, subst, combine_reasons);
        let t_extra = match t_extra {
            TupleExtra::Tsplat(ty) => TupleExtra::Tsplat(apply_ty(ty, subst, combine_reasons)),
            TupleExtra::Tvariadic(ty) => {
                TupleExtra::Tvariadic(apply_ty(ty, subst, combine_reasons))
            }
        };
        TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }
    }

    pub fn apply_fun(fun_type: FunType, subst: &T, combine_reasons: CombineReasons<'_>) -> FunType {
        let FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags,
            instantiated,
        } = fun_type;
        let ft_tparams = ft_tparams
            .into_iter()
            .map(|tparam| apply_tparam(tparam, subst, combine_reasons))
            .collect();
        let ft_params = ft_params
            .into_iter()
            .map(|fun_param| apply_fun_param(fun_param, subst, combine_reasons))
            .collect();
        let ft_implicit_params =
            apply_fun_implicit_params(ft_implicit_params, subst, combine_reasons);
        let ft_where_constraints = ft_where_constraints
            .into_iter()
            .map(|cstr| apply_where_constraint(cstr, subst, combine_reasons))
            .collect();
        let ft_ret = apply_ty(ft_ret, subst, combine_reasons);
        FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags,
            instantiated,
        }
    }

    fn apply_tparam(mut tparam: Tparam, subst: &T, combine_reasons: CombineReasons<'_>) -> Tparam {
        let tp_constraints = std::mem::take(&mut tparam.constraints)
            .into_iter()
            .map(|(cstr_kind, ty)| (cstr_kind, apply_ty(ty, subst, combine_reasons)))
            .collect();
        tparam.constraints = tp_constraints;
        tparam
    }

    fn apply_fun_param(
        fun_param: FunParam,
        subst: &T,
        combine_reasons: CombineReasons<'_>,
    ) -> FunParam {
        let FunParam {
            pos,
            name,
            type_: fp_type,
            flags,
            def_value,
        } = fun_param;
        let fp_type = apply_ty(fp_type, subst, combine_reasons);
        FunParam {
            pos,
            name,
            type_: fp_type,
            flags,
            def_value,
        }
    }

    fn apply_fun_implicit_params(
        t: FunImplicitParams,
        subst: &T,
        combine_reasons: CombineReasons<'_>,
    ) -> FunImplicitParams {
        let FunImplicitParams { capability } = t;
        match capability {
            Capability::CapDefaults(_) => FunImplicitParams { capability },
            Capability::CapTy(ty) => FunImplicitParams {
                capability: Capability::CapTy(apply_ty(ty, subst, combine_reasons)),
            },
        }
    }

    fn apply_where_constraint(
        WhereConstraint(ty1, cstr_kind, ty2): WhereConstraint,
        subst: &T,
        combine_reasons: CombineReasons<'_>,
    ) -> WhereConstraint {
        let ty1 = apply_ty(ty1, subst, combine_reasons);
        let ty2 = apply_ty(ty2, subst, combine_reasons);
        WhereConstraint(ty1, cstr_kind, ty2)
    }

    fn apply_shape(st: ShapeType, subst: &T, combine_reasons: CombineReasons<'_>) -> ShapeType {
        match st {
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                ShapeType::ShapeSplat(ShapeTypeSplat {
                    ss_elems: apply_tyl(ss_elems, subst, combine_reasons),
                })
            }
            ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: s_origin,
                unknown_value: s_unknown_value,
                fields: s_fields,
            }) => {
                let s_unknown_value = apply_ty(s_unknown_value, subst, combine_reasons);
                let s_fields = s_fields
                    .into_iter()
                    .map(|(k, sft)| (k, apply_shape_field(sft, subst, combine_reasons)))
                    .collect();
                ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: s_origin,
                    unknown_value: s_unknown_value,
                    fields: s_fields,
                })
            }
        }
    }

    fn apply_shape_field(
        sft: ShapeFieldType,
        subst: &T,
        combine_reasons: CombineReasons<'_>,
    ) -> ShapeFieldType {
        let ShapeFieldType {
            optional: sft_optional,
            ty: sft_ty,
        } = sft;
        let sft_ty = apply_ty(sft_ty, subst, combine_reasons);
        ShapeFieldType {
            optional: sft_optional,
            ty: sft_ty,
        }
    }

    fn apply_exact(exact: Exact, subst: &T, combine_reasons: CombineReasons<'_>) -> Exact {
        match exact {
            Exact::Exact => exact,
            Exact::Nonexact(ClassRefinement { cr_consts }) => {
                let cr_consts = cr_consts
                    .into_iter()
                    .map(|(k, rc)| (k, apply_refined_const(rc, subst, combine_reasons)))
                    .collect();
                Exact::Nonexact(ClassRefinement { cr_consts })
            }
        }
    }

    fn apply_refined_const(
        rc: RefinedConst,
        subst: &T,
        combine_reasons: CombineReasons<'_>,
    ) -> RefinedConst {
        let RefinedConst {
            bound: rc_bound,
            is_ctx: rc_is_ctx,
        } = rc;
        let rc_bound = match rc_bound {
            RefinedConstBound::TRexact(ty) => {
                RefinedConstBound::TRexact(apply_ty(ty, subst, combine_reasons))
            }
            RefinedConstBound::TRloose(RefinedConstBounds {
                lower: tr_lower,
                upper: tr_upper,
            }) => {
                let tr_lower = apply_tyl(tr_lower, subst, combine_reasons);
                let tr_upper = apply_tyl(tr_upper, subst, combine_reasons);
                RefinedConstBound::TRloose(RefinedConstBounds {
                    lower: tr_lower,
                    upper: tr_upper,
                })
            }
        };
        RefinedConst {
            bound: rc_bound,
            is_ctx: rc_is_ctx,
        }
    }

    pub fn apply(ty: Ty, subst: &T, combine_reasons: CombineReasons<'_>) -> Ty {
        // Avoid a pointless traversal
        if subst.is_empty() {
            ty
        } else {
            apply_ty(ty, subst, combine_reasons)
        }
    }
}

// ---------------------------------------------------------------------------
// Find_locl
// ---------------------------------------------------------------------------

mod find_locl {
    use super::*;

    pub(super) type P<'a> = &'a dyn Fn(&Ty) -> bool;

    pub(super) fn find_ty<'a>(ty: &'a Ty, p: P<'_>) -> Option<&'a Ty> {
        if p(ty) {
            Some(ty)
        } else {
            match get_node(ty) {
                Ty_::Toption(ty)
                | Ty_::TclassPtr(ty)
                | Ty_::Taccess(TaccessType(ty, _))
                | Ty_::Tdependent(_, ty) => find_ty(ty, p),
                Ty_::Tunion(tys) | Ty_::Tintersection(tys) => find_first_ty(tys, p),
                Ty_::TvecOrDict(ty_k, ty_v) => match find_ty(ty_k, p) {
                    None => find_ty(ty_v, p),
                    res => res,
                },
                Ty_::Tclass(_, exact, ty_args) => match find_exact(exact, p) {
                    None => find_first_ty(ty_args, p),
                    res => res,
                },
                Ty_::Tnewtype(_, ty_args, ty_bound) => match find_first_ty(ty_args, p) {
                    None => find_ty(ty_bound, p),
                    res => res,
                },
                Ty_::Ttuple(tuple_ty) => find_tuple(tuple_ty, p),
                Ty_::Tfun(fun_ty) => find_fun(fun_ty, p),
                Ty_::Tshape(shape_ty) => find_shape(shape_ty, p),
                Ty_::Tgeneric(_)
                | Ty_::Tvar(_)
                | Ty_::Tany(_)
                | Ty_::Tnonnull
                | Ty_::Tdynamic(_)
                | Ty_::Tprim(_)
                | Ty_::Tlabel(_)
                | Ty_::Tneg(_) => None,
            }
        }
    }

    fn find_first_ty<'a>(tys: &'a [Ty], p: P<'_>) -> Option<&'a Ty> {
        match tys {
            [] => None,
            [ty, tys @ ..] => match find_ty(ty, p) {
                None => find_first_ty(tys, p),
                res => res,
            },
        }
    }

    fn find_tuple<'a>(t: &'a TupleType, p: P<'_>) -> Option<&'a Ty> {
        let TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        } = t;
        match find_first_ty(t_required, p) {
            None => match find_first_ty(t_optional, p) {
                None => match t_extra {
                    TupleExtra::Tsplat(ty) => find_ty(ty, p),
                    TupleExtra::Tvariadic(ty) => find_ty(ty, p),
                },
                res => res,
            },
            res => res,
        }
    }

    fn find_fun<'a>(ft: &'a FunType, p: P<'_>) -> Option<&'a Ty> {
        let FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags: _,
            instantiated: _,
        } = ft;
        match find_first_tparam(ft_tparams, p) {
            None => match find_first_fun_param(ft_params, p) {
                None => match find_implicit_params(ft_implicit_params, p) {
                    None => match find_first_where_constraint(ft_where_constraints, p) {
                        None => find_ty(ft_ret, p),
                        res => res,
                    },
                    res => res,
                },
                res => res,
            },
            res => res,
        }
    }

    fn find_first_tparam<'a>(tparams: &'a [Tparam], p: P<'_>) -> Option<&'a Ty> {
        match tparams {
            [] => None,
            [tparam, tparams @ ..] => match find_tparam(tparam, p) {
                None => find_first_tparam(tparams, p),
                res => res,
            },
        }
    }

    fn find_tparam<'a>(tparam: &'a Tparam, p: P<'_>) -> Option<&'a Ty> {
        find_first_constraint(&tparam.constraints, p)
    }

    fn find_first_constraint<'a>(
        cstrs: &'a [(ast_defs::ConstraintKind, Ty)],
        p: P<'_>,
    ) -> Option<&'a Ty> {
        match cstrs {
            [] => None,
            [(_, ty), cstrs @ ..] => match find_ty(ty, p) {
                None => find_first_constraint(cstrs, p),
                res => res,
            },
        }
    }

    fn find_first_fun_param<'a>(fun_params: &'a [FunParam], p: P<'_>) -> Option<&'a Ty> {
        match fun_params {
            [] => None,
            [FunParam { type_: fp_type, .. }, cstrs @ ..] => match find_ty(fp_type, p) {
                None => find_first_fun_param(cstrs, p),
                res => res,
            },
        }
    }

    fn find_implicit_params<'a>(ip: &'a FunImplicitParams, p: P<'_>) -> Option<&'a Ty> {
        match &ip.capability {
            Capability::CapDefaults(_) => None,
            Capability::CapTy(ty) => find_ty(ty, p),
        }
    }

    fn find_first_where_constraint<'a>(cstrs: &'a [WhereConstraint], p: P<'_>) -> Option<&'a Ty> {
        match cstrs {
            [] => None,
            [cstr, cstrs @ ..] => match find_where_constraint(cstr, p) {
                None => find_first_where_constraint(cstrs, p),
                res => res,
            },
        }
    }

    fn find_where_constraint<'a>(
        WhereConstraint(ty1, _, ty2): &'a WhereConstraint,
        p: P<'_>,
    ) -> Option<&'a Ty> {
        match find_ty(ty1, p) {
            None => find_ty(ty2, p),
            res => res,
        }
    }

    fn find_shape<'a>(st: &'a ShapeType, p: P<'_>) -> Option<&'a Ty> {
        match st {
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                ss_elems.iter().find_map(|ty| find_ty(ty, p))
            }
            ShapeType::ShapeSimple(ShapeTypeSimple {
                unknown_value: s_unknown_value,
                fields: s_fields,
                origin: _,
            }) => match find_ty(s_unknown_value, p) {
                // TShapeMap.bindings: in the order of the keys
                None => find_first_shape_field(s_fields.values(), p),
                res => res,
            },
        }
    }

    fn find_first_shape_field<'a>(
        mut fields: impl Iterator<Item = &'a ShapeFieldType>,
        p: P<'_>,
    ) -> Option<&'a Ty> {
        fields.find_map(|ShapeFieldType { ty: sft_ty, .. }| find_ty(sft_ty, p))
    }

    fn find_exact<'a>(exact: &'a Exact, p: P<'_>) -> Option<&'a Ty> {
        match exact {
            Exact::Exact => None,
            Exact::Nonexact(ClassRefinement { cr_consts }) => {
                // S_map.bindings: in the order of the keys
                find_first_refined_const(cr_consts.values(), p)
            }
        }
    }

    fn find_first_refined_const<'a>(
        mut cr_consts: impl Iterator<Item = &'a RefinedConst>,
        p: P<'_>,
    ) -> Option<&'a Ty> {
        cr_consts.find_map(|next| find_refined_const(next, p))
    }

    fn find_refined_const<'a>(rc: &'a RefinedConst, p: P<'_>) -> Option<&'a Ty> {
        match &rc.bound {
            RefinedConstBound::TRexact(ty) => find_ty(ty, p),
            RefinedConstBound::TRloose(RefinedConstBounds {
                lower: tr_lower,
                upper: tr_upper,
            }) => match find_first_ty(tr_lower, p) {
                None => find_first_ty(tr_upper, p),
                res => res,
            },
        }
    }
}

/// Find the first element of a [locl_ty] satisfying the predicate [p]
pub fn find_locl_ty(locl_ty: &Ty, p: &dyn Fn(&Ty) -> bool) -> Option<Ty> {
    find_locl::find_ty(locl_ty, p).cloned()
}

// ---------------------------------------------------------------------------
// The declared phase: comparison
// ---------------------------------------------------------------------------

/// `ty__compare` and the functions it defines, for the types of the declared
/// phase (`hackrs`). Where the `hackrs` definitions differ from the OCaml ones
/// (no `s_origin` in shapes, interned names), the comparison is the one OCaml
/// does on the corresponding OCaml value: names are compared as strings, and
/// maps in the order of their keys as strings.
mod decl_compare {
    use ty::decl::ty as d;

    use super::*;

    type R = crate::ctx::R;

    fn ty_con_ordinal_(ty_: &DeclTy_) -> isize {
        match ty_ {
            // only decl constructors
            d::Ty_::Tthis => 100,
            d::Ty_::Tapply(_) => 101,
            d::Ty_::Tmixed => 102,
            d::Ty_::Tlike(_) => 103,
            d::Ty_::Trefinement(_) => 104,
            d::Ty_::Twildcard => 105,
            // exist in both phases
            d::Ty_::Tany => 0,
            d::Ty_::Toption(t) => match t.node_ref() {
                d::Ty_::Tnonnull => 1,
                _ => 4,
            },
            d::Ty_::Tnonnull => 2,
            d::Ty_::Tdynamic => 3,
            d::Ty_::Tprim(_) => 5,
            d::Ty_::Tfun(_) => 6,
            d::Ty_::Ttuple(_) => 7,
            d::Ty_::Tshape(_) => 8,
            d::Ty_::Tgeneric(_) => 11,
            d::Ty_::Tunion(_) => 13,
            d::Ty_::Tintersection(_) => 14,
            d::Ty_::Taccess(_) => 24,
            d::Ty_::TvecOrDict(_) => 25,
            d::Ty_::TclassPtr(_) => 26,
        }
    }

    #[allow(non_snake_case)]
    pub(super) fn ty__compare(normalize_lists: bool, ty_1: &DeclTy_, ty_2: &DeclTy_) -> Ordering {
        use d::Ty_::*;
        match (ty_1, ty_2) {
            // Only in Declared Phase
            (Tthis, Tthis) => Ordering::Equal,
            (Tapply(a1), Tapply(a2)) => {
                let (id1, tyl1) = &**a1;
                let (id2, tyl2) = &**a2;
                chain_compare(id1.id_ref().as_str().cmp(id2.id_ref().as_str()), || {
                    tyl_compare(normalize_lists, normalize_lists, tyl1, tyl2)
                })
            }
            (Trefinement(tr1), Trefinement(tr2)) => {
                chain_compare(ty_compare(normalize_lists, &tr1.ty, &tr2.ty), || {
                    class_refinement_compare(&tr1.refinement, &tr2.refinement)
                })
            }
            (Tmixed, Tmixed) => Ordering::Equal,
            (Twildcard, Twildcard) => Ordering::Equal,
            (Tlike(ty1), Tlike(ty2)) => ty_compare(normalize_lists, ty1, ty2),
            (Tthis | Tapply(_) | Tmixed | Twildcard | Tlike(_), _)
            | (_, Tthis | Tapply(_) | Tmixed | Twildcard | Tlike(_)) => {
                ty_con_ordinal_(ty_1).cmp(&ty_con_ordinal_(ty_2))
            }
            // Both or in Localized Phase
            (Tprim(ty1), Tprim(ty2)) => ty1.cmp(ty2),
            (Toption(ty), Toption(ty2)) => ty_compare(normalize_lists, ty, ty2),
            (TvecOrDict(kv1), TvecOrDict(kv2)) => {
                let (tk, tv) = &**kv1;
                let (tk2, tv2) = &**kv2;
                chain_compare(ty_compare(normalize_lists, tk, tk2), || {
                    ty_compare(normalize_lists, tv, tv2)
                })
            }
            (Tfun(fty), Tfun(fty2)) => tfun_compare(normalize_lists, fty, fty2),
            (Tunion(tyl1), Tunion(tyl2)) | (Tintersection(tyl1), Tintersection(tyl2)) => {
                tyl_compare(normalize_lists, normalize_lists, tyl1, tyl2)
            }
            (Ttuple(t1), Ttuple(t2)) => tuple_type_compare(normalize_lists, t1, t2),
            (Tgeneric(n1), Tgeneric(n2)) => n1.as_str().cmp(n2.as_str()),
            (Tshape(s1), Tshape(s2)) => shape_type_compare(normalize_lists, s1, s2),
            (Taccess(ta1), Taccess(ta2)) => {
                chain_compare(ty_compare(normalize_lists, &ta1.ty, &ta2.ty), || {
                    ta1.type_const
                        .id_ref()
                        .as_str()
                        .cmp(ta2.type_const.id_ref().as_str())
                })
            }
            (Tnonnull, Tnonnull) => Ordering::Equal,
            (Tdynamic, Tdynamic) => Ordering::Equal,
            (TclassPtr(ty1), TclassPtr(ty2)) => ty_compare(normalize_lists, ty1, ty2),
            (
                Tprim(_) | Toption(_) | TvecOrDict(_) | Tfun(_) | Tintersection(_) | Tunion(_)
                | Ttuple(_) | Tgeneric(_) | Tshape(_) | Tnonnull | Tdynamic | Taccess(_) | Tany
                | Trefinement(_) | TclassPtr(_),
                _,
            ) => ty_con_ordinal_(ty_1).cmp(&ty_con_ordinal_(ty_2)),
        }
    }

    pub(super) fn ty_compare(normalize_lists: bool, ty1: &DeclTy, ty2: &DeclTy) -> Ordering {
        ty__compare(normalize_lists, ty1.node_ref(), ty2.node_ref())
    }

    /// The toplevel `tyl_compare ~sort ~normalize_lists`.
    fn tyl_compare(
        sort: bool,
        normalize_lists: bool,
        tyl1: &[DeclTy],
        tyl2: &[DeclTy],
    ) -> Ordering {
        if sort {
            let mut tyl1: Vec<&DeclTy> = tyl1.iter().collect();
            let mut tyl2: Vec<&DeclTy> = tyl2.iter().collect();
            tyl1.sort_by(|a, b| ty_compare(false, a, b));
            tyl2.sort_by(|a, b| ty_compare(false, a, b));
            crate::rt::ocaml_list::compare(|a, b| ty_compare(normalize_lists, a, b), &tyl1, &tyl2)
        } else {
            crate::rt::ocaml_list::compare(|a, b| ty_compare(normalize_lists, a, b), tyl1, tyl2)
        }
    }

    /// `TShapeField.compare`
    pub(super) fn tshape_field_name_compare(
        x: &d::TshapeFieldName,
        y: &d::TshapeFieldName,
    ) -> Ordering {
        use d::TshapeFieldName::*;
        match (x, y) {
            (TSFregexGroup(s1), TSFregexGroup(s2)) => s1.as_str().cmp(s2.as_str()),
            (TSFlitStr(s1), TSFlitStr(s2)) => s1.as_bytes().cmp(s2.as_bytes()),
            (TSFclassConst(s1, s1_), TSFclassConst(s2, s2_)) => {
                (s1.as_str(), s1_.as_str()).cmp(&(s2.as_str(), s2_.as_str()))
            }
            (TSFregexGroup(_), _) => Ordering::Less,
            (TSFlitStr(_), TSFregexGroup(_)) => Ordering::Greater,
            (TSFlitStr(_), _) => Ordering::Less,
            (TSFclassConst(_, _), _) => Ordering::Greater,
        }
    }

    fn shape_field_type_compare(
        normalize_lists: bool,
        sft1: &d::ShapeFieldType<R>,
        sft2: &d::ShapeFieldType<R>,
    ) -> Ordering {
        chain_compare(ty_compare(normalize_lists, &sft1.ty, &sft2.ty), || {
            sft1.optional.cmp(&sft2.optional)
        })
    }

    fn shape_type_compare(
        normalize_lists: bool,
        s1: &d::ShapeType<R>,
        s2: &d::ShapeType<R>,
    ) -> Ordering {
        match (s1, s2) {
            (d::ShapeType::Simple(_), d::ShapeType::Splat(_)) => Ordering::Less,
            (d::ShapeType::Splat(_), d::ShapeType::Simple(_)) => Ordering::Greater,
            (d::ShapeType::Splat(e1), d::ShapeType::Splat(e2)) => tyl_compare(false, false, e1, e2),
            (
                d::ShapeType::Simple(d::ShapeTypeSimple(unknown_fields_type1, fields1)),
                d::ShapeType::Simple(d::ShapeTypeSimple(unknown_fields_type2, fields2)),
            ) => {
                // (hackrs shapes have no origin: as Missing_origin)
                chain_compare(
                    ty_compare(normalize_lists, unknown_fields_type1, unknown_fields_type2),
                    || {
                        // TShapeMap.compare
                        let mut fields1: Vec<_> = fields1.iter().collect();
                        let mut fields2: Vec<_> = fields2.iter().collect();
                        fields1.sort_by(|a, b| tshape_field_name_compare(a.0, b.0));
                        fields2.sort_by(|a, b| tshape_field_name_compare(a.0, b.0));
                        crate::rt::ocaml_list::compare(
                            |(k1, d1), (k2, d2)| {
                                chain_compare(tshape_field_name_compare(k1, k2), || {
                                    shape_field_type_compare(normalize_lists, d1, d2)
                                })
                            },
                            &fields1,
                            &fields2,
                        )
                    },
                )
            }
        }
    }

    fn tuple_extra_compare(
        normalize_lists: bool,
        t1: &d::TupleExtra<R>,
        t2: &d::TupleExtra<R>,
    ) -> Ordering {
        match (t1, t2) {
            (d::TupleExtra::Tvariadic(_), d::TupleExtra::Tsplat(_)) => Ordering::Less,
            (d::TupleExtra::Tsplat(_), d::TupleExtra::Tvariadic(_)) => Ordering::Greater,
            (d::TupleExtra::Tsplat(t_splat1), d::TupleExtra::Tsplat(t_splat2)) => {
                ty_compare(normalize_lists, t_splat1, t_splat2)
            }
            (d::TupleExtra::Tvariadic(t_variadic1), d::TupleExtra::Tvariadic(t_variadic2)) => {
                ty_compare(normalize_lists, t_variadic1, t_variadic2)
            }
        }
    }

    fn tuple_type_compare(
        normalize_lists: bool,
        t1: &d::TupleType<R>,
        t2: &d::TupleType<R>,
    ) -> Ordering {
        let d::TupleType(t_required1, t_optional1, t_extra1) = t1;
        let d::TupleType(t_required2, t_optional2, t_extra2) = t2;
        chain_compare(
            crate::rt::ocaml_list::compare(
                |a, b| ty_compare(normalize_lists, a, b),
                t_required1,
                t_required2,
            ),
            || {
                chain_compare(
                    crate::rt::ocaml_list::compare(
                        |a, b| ty_compare(normalize_lists, a, b),
                        t_optional1,
                        t_optional2,
                    ),
                    || tuple_extra_compare(normalize_lists, t_extra1, t_extra2),
                )
            },
        )
    }

    fn user_attribute_param_compare(
        p1: &d::UserAttributeParam,
        p2: &d::UserAttributeParam,
    ) -> Ordering {
        fn dest_user_attribute_param(p: &d::UserAttributeParam) -> (isize, &[u8]) {
            match p {
                d::UserAttributeParam::Classname(s) => (0, s.as_str().as_bytes()),
                d::UserAttributeParam::EnumClassLabel(s) => (1, s.as_bytes()),
                d::UserAttributeParam::String(s) => (2, s.as_bytes()),
                d::UserAttributeParam::Int(i) => (3, i.as_bytes()),
            }
        }
        let (id1, s1) = dest_user_attribute_param(p1);
        let (id2, s2) = dest_user_attribute_param(p2);
        chain_compare(id1.cmp(&id2), || s1.cmp(s2))
    }

    fn user_attribute_compare<P>(ua1: &d::UserAttribute<P>, ua2: &d::UserAttribute<P>) -> Ordering {
        chain_compare(
            ua1.name.id_ref().as_str().cmp(ua2.name.id_ref().as_str()),
            || crate::rt::ocaml_list::compare(user_attribute_param_compare, &ua1.params, &ua2.params),
        )
    }

    fn tparam_compare(normalize_lists: bool, tp1: &DeclTparam, tp2: &DeclTparam) -> Ordering {
        chain_compare(
            tp1.name.id_ref().as_str().cmp(tp2.name.id_ref().as_str()),
            || {
                chain_compare(
                    crate::rt::ocaml_list::compare(
                        |(ck1, ty1), (ck2, ty2)| {
                            chain_compare(ck1.cmp(ck2), || ty_compare(normalize_lists, ty1, ty2))
                        },
                        &tp1.constraints,
                        &tp2.constraints,
                    ),
                    || {
                        chain_compare(
                            crate::rt::ocaml_list::compare(
                                user_attribute_compare,
                                &tp1.user_attributes,
                                &tp2.user_attributes,
                            ),
                            || tp1.reified.cmp(&tp2.reified),
                        )
                    },
                )
            },
        )
    }

    fn where_constraint_compare(
        normalize_lists: bool,
        d::WhereConstraint(ty1a, ck1, ty1b): &DeclWhereConstraint,
        d::WhereConstraint(ty2a, ck2, ty2b): &DeclWhereConstraint,
    ) -> Ordering {
        chain_compare(ck1.cmp(ck2), || {
            chain_compare(ty_compare(normalize_lists, ty1a, ty2a), || {
                ty_compare(normalize_lists, ty1b, ty2b)
            })
        })
    }

    /// The toplevel `ft_param_compare`.
    fn ft_param_compare(
        normalize_lists: bool,
        param1: &DeclFunParam,
        param2: &DeclFunParam,
    ) -> Ordering {
        chain_compare(ty_compare(normalize_lists, &param1.ty, &param2.ty), || {
            chain_compare(param1.flags.cmp(&param2.flags), || {
                if param1.flags.contains(FunParamFlags::NAMED) {
                    option_compare(
                        |a: &pos::Symbol, b: &pos::Symbol| a.as_str().cmp(b.as_str()),
                        param1.name.as_ref(),
                        param2.name.as_ref(),
                    )
                } else {
                    Ordering::Equal
                }
            })
        })
    }

    fn tfun_compare(normalize_lists: bool, fty1: &DeclFunType, fty2: &DeclFunType) -> Ordering {
        chain_compare(ty_compare(normalize_lists, &fty1.ret, &fty2.ret), || {
            chain_compare(
                // (the OCaml calls the toplevel ft_params_compare without ~normalize_lists)
                crate::rt::ocaml_list::compare(
                    |a, b| ft_param_compare(false, a, b),
                    &fty1.params,
                    &fty2.params,
                ),
                || {
                    chain_compare(
                        crate::rt::ocaml_list::compare(
                            |a, b| tparam_compare(normalize_lists, a, b),
                            &fty1.tparams,
                            &fty2.tparams,
                        ),
                        || {
                            chain_compare(
                                crate::rt::ocaml_list::compare(
                                    |a, b| where_constraint_compare(normalize_lists, a, b),
                                    &fty1.where_constraints,
                                    &fty2.where_constraints,
                                ),
                                || {
                                    chain_compare(fty1.flags.cmp(&fty2.flags), || {
                                        chain_compare(
                                            capability_compare(
                                                normalize_lists,
                                                &fty1.implicit_params.capability,
                                                &fty2.implicit_params.capability,
                                            ),
                                            || fty1.instantiated.cmp(&fty2.instantiated),
                                        )
                                    })
                                },
                            )
                        },
                    )
                },
            )
        })
    }

    fn capability_compare(
        normalize_lists: bool,
        cap1: &d::Capability<R, DeclTy>,
        cap2: &d::Capability<R, DeclTy>,
    ) -> Ordering {
        match (cap1, cap2) {
            (d::Capability::CapDefaults(_), d::Capability::CapDefaults(_)) => Ordering::Equal,
            (d::Capability::CapDefaults(_), d::Capability::CapTy(_)) => Ordering::Less,
            (d::Capability::CapTy(_), d::Capability::CapDefaults(_)) => Ordering::Greater,
            (d::Capability::CapTy(ty1), d::Capability::CapTy(ty2)) => {
                ty_compare(normalize_lists, ty1, ty2)
            }
        }
    }

    fn refined_const_compare(a: &DeclRefinedConst, b: &DeclRefinedConst) -> Ordering {
        let rc_is_ctx_cmp = a.is_ctx.cmp(&b.is_ctx);
        if rc_is_ctx_cmp != Ordering::Equal {
            rc_is_ctx_cmp
        } else {
            match (&a.bound, &b.bound) {
                (d::RefinedConstBound::Exact(_), d::RefinedConstBound::Loose(_)) => Ordering::Less,
                (d::RefinedConstBound::Loose(_), d::RefinedConstBound::Exact(_)) => {
                    Ordering::Greater
                }
                (d::RefinedConstBound::Loose(b1), d::RefinedConstBound::Loose(b2)) => {
                    chain_compare(tyl_compare(true, false, &b1.lower, &b2.lower), || {
                        tyl_compare(true, false, &b1.upper, &b2.upper)
                    })
                }
                (d::RefinedConstBound::Exact(ty1), d::RefinedConstBound::Exact(ty2)) => {
                    ty_compare(false, ty1, ty2)
                }
            }
        }
    }

    fn class_refinement_compare(cr1: &DeclClassRefinement, cr2: &DeclClassRefinement) -> Ordering {
        // S_map.compare
        let mut rcs1: Vec<_> = cr1.consts.iter().collect();
        let mut rcs2: Vec<_> = cr2.consts.iter().collect();
        rcs1.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
        rcs2.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
        crate::rt::ocaml_list::compare(
            |(k1, d1), (k2, d2)| {
                chain_compare(k1.as_str().cmp(k2.as_str()), || {
                    refined_const_compare(d1, d2)
                })
            },
            &rcs1,
            &rcs2,
        )
    }
}

/// `TShapeField.compare` on the names of the fields of a declared shape (the
/// order of the bindings of a `TShapeMap`; the `hackrs` map is in the order of
/// the interned names).
pub(crate) fn decl_tshape_field_name_compare(
    x: &ty::decl::ty::TshapeFieldName,
    y: &ty::decl::ty::TshapeFieldName,
) -> Ordering {
    decl_compare::tshape_field_name_compare(x, y)
}

pub fn compare_decl_ty(normalize_lists: Option<bool>, ty1: &DeclTy, ty2: &DeclTy) -> Ordering {
    let normalize_lists = normalize_lists.unwrap_or(false);
    decl_compare::ty_compare(normalize_lists, ty1, ty2)
}

pub fn equal_decl_ty_(ty1: &DeclTy_, ty2: &DeclTy_) -> bool {
    decl_compare::ty__compare(false, ty1, ty2) == Ordering::Equal
}

pub fn equal_decl_ty(ty1: &DeclTy, ty2: &DeclTy) -> bool {
    equal_decl_ty_(ty1.node_ref(), ty2.node_ref())
}

pub fn equal_shape_field_type(sft1: &DeclShapeFieldType, sft2: &DeclShapeFieldType) -> bool {
    equal_decl_ty(&sft1.ty, &sft2.ty) && sft1.optional == sft2.optional
}

pub fn equal_decl_tyl(tyl1: &[DeclTy], tyl2: &[DeclTy]) -> bool {
    // List.equal
    tyl1.len() == tyl2.len()
        && tyl1
            .iter()
            .zip(tyl2.iter())
            .all(|(ty1, ty2)| equal_decl_ty(ty1, ty2))
}

// ---------------------------------------------------------------------------
// Transform_top_down_decl
// ---------------------------------------------------------------------------

/// What `on_ty` and `on_rc_bound` answer in [`transform_top_down_decl_ty`]
/// (the polymorphic variants `` `Continue ``, `` `Stop `` and `` `Restart ``).
#[derive(Clone, Debug)]
pub enum TransformTopDown<T> {
    Continue(T),
    Stop(T),
    Restart(T),
}

mod transform_top_down_decl {
    use ty::decl::ty as d;

    use super::*;

    pub(super) type OnTy<'a, A> = &'a dyn Fn(DeclTy, &A) -> (A, TransformTopDown<DeclTy>);
    pub(super) type OnRcBound<'a, A> =
        &'a dyn Fn(DeclRefinedConstBound, &A) -> (A, TransformTopDown<DeclRefinedConstBound>);

    pub(super) fn transform<A>(
        ty: DeclTy,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclTy {
        match on_ty(ty, ctx) {
            (_, TransformTopDown::Stop(ty)) => ty,
            (ctx, TransformTopDown::Continue(ty)) => traverse(ty, on_ty, on_rc_bound, &ctx),
            (ctx, TransformTopDown::Restart(ty)) => transform(ty, on_ty, on_rc_bound, &ctx),
        }
    }

    fn transform_tyl<A>(
        tys: &[DeclTy],
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> Box<[DeclTy]> {
        tys.iter()
            .map(|ty| transform(ty.clone(), on_ty, on_rc_bound, ctx))
            .collect()
    }

    fn traverse<A>(
        ty: DeclTy,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclTy {
        let r = ty.reason().clone();
        let tr = |ty: &DeclTy| transform(ty.clone(), on_ty, on_rc_bound, ctx);
        match ty.node_ref() {
            d::Ty_::Tthis
            | d::Ty_::Tmixed
            | d::Ty_::Twildcard
            | d::Ty_::Tany
            | d::Ty_::Tnonnull
            | d::Ty_::Tdynamic
            | d::Ty_::Tprim(_)
            | d::Ty_::Tgeneric(_) => ty,
            d::Ty_::Tlike(ty) => DeclTy::new(r, d::Ty_::Tlike(tr(ty))),
            d::Ty_::Toption(ty) => DeclTy::new(r, d::Ty_::Toption(tr(ty))),
            d::Ty_::TclassPtr(ty) => DeclTy::new(r, d::Ty_::TclassPtr(tr(ty))),
            d::Ty_::Taccess(ta) => DeclTy::new(
                r,
                d::Ty_::Taccess(Box::new(d::TaccessType {
                    ty: tr(&ta.ty),
                    type_const: ta.type_const.clone(),
                })),
            ),
            d::Ty_::TvecOrDict(kv) => {
                let (ty_k, ty_v) = &**kv;
                let ty_k = tr(ty_k);
                let ty_v = tr(ty_v);
                DeclTy::new(r, d::Ty_::TvecOrDict(Box::new((ty_k, ty_v))))
            }
            d::Ty_::Tunion(tys) => DeclTy::new(
                r,
                d::Ty_::Tunion(transform_tyl(tys, on_ty, on_rc_bound, ctx)),
            ),
            d::Ty_::Tintersection(tys) => DeclTy::new(
                r,
                d::Ty_::Tintersection(transform_tyl(tys, on_ty, on_rc_bound, ctx)),
            ),
            d::Ty_::Tapply(id_and_tys) => {
                let (id, tys) = &**id_and_tys;
                DeclTy::new(
                    r,
                    d::Ty_::Tapply(Box::new((
                        id.clone(),
                        transform_tyl(tys, on_ty, on_rc_bound, ctx),
                    ))),
                )
            }
            d::Ty_::Trefinement(tr_) => {
                let ty = tr(&tr_.ty);
                let refinement =
                    traverse_class_refinement(&tr_.refinement, on_ty, on_rc_bound, ctx);
                DeclTy::new(
                    r,
                    d::Ty_::Trefinement(Box::new(d::TrefinementType { ty, refinement })),
                )
            }
            d::Ty_::Tfun(fun_ty) => DeclTy::new(
                r,
                d::Ty_::Tfun(Box::new(traverse_fun_ty(fun_ty, on_ty, on_rc_bound, ctx))),
            ),
            d::Ty_::Ttuple(tuple_ty) => DeclTy::new(
                r,
                d::Ty_::Ttuple(Box::new(traverse_tuple_ty(
                    tuple_ty,
                    on_ty,
                    on_rc_bound,
                    ctx,
                ))),
            ),
            d::Ty_::Tshape(shape_ty) => DeclTy::new(
                r,
                d::Ty_::Tshape(Box::new(traverse_shape_ty(
                    shape_ty,
                    on_ty,
                    on_rc_bound,
                    ctx,
                ))),
            ),
        }
    }

    fn traverse_class_refinement<A>(
        cr: &DeclClassRefinement,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclClassRefinement {
        // S_map.map: in the order of the names
        let mut consts: Vec<_> = cr.consts.iter().collect();
        consts.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
        d::ClassRefinement {
            consts: consts
                .into_iter()
                .map(|(k, rc)| (*k, traverse_refined_const(rc, on_ty, on_rc_bound, ctx)))
                .collect(),
        }
    }

    fn traverse_refined_const<A>(
        rc: &DeclRefinedConst,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclRefinedConst {
        let rc_bound = transform_rc_bound(rc.bound.clone(), on_ty, on_rc_bound, ctx);
        d::RefinedConst {
            bound: rc_bound,
            is_ctx: rc.is_ctx,
        }
    }

    fn transform_rc_bound<A>(
        rc_bound: DeclRefinedConstBound,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclRefinedConstBound {
        match on_rc_bound(rc_bound, ctx) {
            (_, TransformTopDown::Stop(rc_bound)) => rc_bound,
            (ctx, TransformTopDown::Continue(rc_bound)) => {
                traverse_rc_bound(rc_bound, on_ty, on_rc_bound, &ctx)
            }
            (ctx, TransformTopDown::Restart(rc_bound)) => {
                transform_rc_bound(rc_bound, on_ty, on_rc_bound, &ctx)
            }
        }
    }

    fn traverse_rc_bound<A>(
        rc_bound: DeclRefinedConstBound,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclRefinedConstBound {
        match rc_bound {
            d::RefinedConstBound::Exact(ty) => {
                d::RefinedConstBound::Exact(transform(ty, on_ty, on_rc_bound, ctx))
            }
            d::RefinedConstBound::Loose(d::RefinedConstBounds {
                lower: tr_lower,
                upper: tr_upper,
            }) => {
                let tr_lower = transform_tyl(&tr_lower, on_ty, on_rc_bound, ctx);
                let tr_upper = transform_tyl(&tr_upper, on_ty, on_rc_bound, ctx);
                d::RefinedConstBound::Loose(d::RefinedConstBounds {
                    lower: tr_lower,
                    upper: tr_upper,
                })
            }
        }
    }

    fn traverse_fun_ty<A>(
        fun_ty: &DeclFunType,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> DeclFunType {
        let tr = |ty: &DeclTy| transform(ty.clone(), on_ty, on_rc_bound, ctx);
        let ft_tparams = fun_ty
            .tparams
            .iter()
            .map(|tparam| {
                let tp_constraints = tparam
                    .constraints
                    .iter()
                    .map(|(cstr_kind, ty)| (*cstr_kind, tr(ty)))
                    .collect();
                d::Tparam {
                    variance: tparam.variance,
                    name: tparam.name.clone(),
                    constraints: tp_constraints,
                    reified: tparam.reified,
                    user_attributes: tparam.user_attributes.clone(),
                }
            })
            .collect();
        let ft_params = fun_ty
            .params
            .iter()
            .map(|fun_param| {
                let fp_type = tr(&fun_param.ty);
                d::FunParam {
                    pos: fun_param.pos.clone(),
                    name: fun_param.name,
                    ty: fp_type,
                    flags: fun_param.flags,
                    def_value: fun_param.def_value.clone(),
                }
            })
            .collect();
        let ft_implicit_params = match &fun_ty.implicit_params.capability {
            d::Capability::CapDefaults(_) => fun_ty.implicit_params.clone(),
            d::Capability::CapTy(ty) => d::FunImplicitParams {
                capability: d::Capability::CapTy(tr(ty)),
            },
        };
        let ft_where_constraints = fun_ty
            .where_constraints
            .iter()
            .map(|d::WhereConstraint(ty1, cstr_kind, ty2)| {
                let ty1 = tr(ty1);
                let ty2 = tr(ty2);
                d::WhereConstraint(ty1, *cstr_kind, ty2)
            })
            .collect();
        let ft_ret = tr(&fun_ty.ret);
        d::FunType {
            tparams: ft_tparams,
            where_constraints: ft_where_constraints,
            params: ft_params,
            implicit_params: ft_implicit_params,
            ret: ft_ret,
            flags: fun_ty.flags,
            instantiated: fun_ty.instantiated,
        }
    }

    fn traverse_tuple_ty<A>(
        t: &d::TupleType<crate::ctx::R>,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> d::TupleType<crate::ctx::R> {
        let d::TupleType(t_required, t_optional, t_extra) = t;
        let t_required = transform_tyl(t_required, on_ty, on_rc_bound, ctx);
        let t_optional = transform_tyl(t_optional, on_ty, on_rc_bound, ctx);
        let t_extra = match t_extra {
            d::TupleExtra::Tsplat(ty) => {
                d::TupleExtra::Tsplat(transform(ty.clone(), on_ty, on_rc_bound, ctx))
            }
            d::TupleExtra::Tvariadic(ty) => {
                d::TupleExtra::Tvariadic(transform(ty.clone(), on_ty, on_rc_bound, ctx))
            }
        };
        d::TupleType(t_required, t_optional, t_extra)
    }

    fn traverse_shape_ty<A>(
        st: &d::ShapeType<crate::ctx::R>,
        on_ty: OnTy<'_, A>,
        on_rc_bound: OnRcBound<'_, A>,
        ctx: &A,
    ) -> d::ShapeType<crate::ctx::R> {
        match st {
            d::ShapeType::Splat(ss_elems) => d::ShapeType::Splat(
                ss_elems
                    .iter()
                    .map(|ty| transform(ty.clone(), on_ty, on_rc_bound, ctx))
                    .collect(),
            ),
            d::ShapeType::Simple(d::ShapeTypeSimple(s_unknown_value, s_fields)) => {
                let s_unknown_value = transform(s_unknown_value.clone(), on_ty, on_rc_bound, ctx);
                let s_fields = s_fields
                    .iter()
                    .map(|(k, sft)| {
                        let sft_ty = transform(sft.ty.clone(), on_ty, on_rc_bound, ctx);
                        (
                            *k,
                            d::ShapeFieldType {
                                field_name_pos: sft.field_name_pos.clone(),
                                optional: sft.optional,
                                ty: sft_ty,
                            },
                        )
                    })
                    .collect();
                d::ShapeType::Simple(d::ShapeTypeSimple(s_unknown_value, s_fields))
            }
        }
    }
}

/// Transform a decl ty top down
pub fn transform_top_down_decl_ty<A>(
    decl_ty: DeclTy,
    on_ty: &dyn Fn(DeclTy, &A) -> (A, TransformTopDown<DeclTy>),
    on_rc_bound: &dyn Fn(DeclRefinedConstBound, &A) -> (A, TransformTopDown<DeclRefinedConstBound>),
    ctx: &A,
) -> DeclTy {
    transform_top_down_decl::transform(decl_ty, on_ty, on_rc_bound, ctx)
}

pub fn is_type_tag_generic_wildcard(generic: &TypeTagGeneric) -> bool {
    match generic {
        TypeTagGeneric::Wildcard(_) => true,
        TypeTagGeneric::Filled(_) => false,
    }
}

pub fn get_var(t: &Ty) -> Option<isize> {
    match get_node(t) {
        Ty_::Tvar(v) => Some(*v),
        _ => None,
    }
}

pub fn is_var_v(t: &Ty, v: isize) -> bool {
    match get_node(t) {
        Ty_::Tvar(v_) if v == *v_ => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;

    fn r() -> Reason {
        crate::typing_reason::none()
    }

    fn prim(p: Tprim) -> Ty {
        mk((r(), Ty_::Tprim(p)))
    }

    fn generic(n: &str) -> Ty {
        mk((r(), Ty_::Tgeneric(n.to_string())))
    }

    fn class(n: &str, tyl: Vec<Ty>) -> Ty {
        mk((
            r(),
            Ty_::Tclass((Pos::NONE, n.to_string()), nonexact(), tyl),
        ))
    }

    fn union(tyl: Vec<Ty>) -> Ty {
        mk((r(), Ty_::Tunion(tyl)))
    }

    fn pred(p: TypePredicate_) -> TypePredicate {
        TypePredicate(r(), p)
    }

    fn fun_type(params: Vec<Ty>, ret: Ty) -> FunType {
        FunType {
            tparams: vec![],
            where_constraints: vec![],
            params: params
                .into_iter()
                .map(|type_| FunParam {
                    pos: Pos::NONE,
                    name: None,
                    type_,
                    flags: FunParamFlags::empty(),
                    def_value: None,
                })
                .collect(),
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(Pos::NONE),
            },
            ret,
            flags: FunTypeFlags::empty(),
            instantiated: true,
        }
    }

    #[test]
    fn mk_and_deref() {
        let ty = prim(Tprim::Tint);
        assert!(matches!(get_node(&ty), Ty_::Tprim(Tprim::Tint)));
        assert!(matches!(&**get_reason(&ty), crate::typing_reason::T_::NoReason));
        let (r, n) = deref(&ty);
        assert!(matches!(&*r, crate::typing_reason::T_::NoReason));
        assert!(matches!(n, Ty_::Tprim(Tprim::Tint)));
        let ty = with_reason(prim(Tprim::Tint), crate::typing_reason::invalid());
        assert!(matches!(&**get_reason(&ty), crate::typing_reason::T_::Invalid));
        assert_eq!(get_pos(&ty), Pos::NONE);
        let ty = map_ty(ty, |_| Ty_::Tnonnull);
        assert!(matches!(get_node(&ty), Ty_::Tnonnull));
    }

    #[test]
    fn compare_ignores_reasons_and_tvid_of_dynamic() {
        let a = prim(Tprim::Tint);
        let b = with_reason(prim(Tprim::Tint), crate::typing_reason::invalid());
        assert_eq!(ty_compare(None, &a, &b), Ordering::Equal);
        assert!(equal_locl_ty(&a, &b));
        let d1 = mk((r(), Ty_::Tdynamic(None)));
        let d2 = mk((r(), Ty_::Tdynamic(Some(3))));
        assert!(equal_locl_ty(&d1, &d2));
        // Tany against Tany goes through the constructor ordinals
        let any = || mk((r(), Ty_::Tany(TanySentinel)));
        assert!(equal_locl_ty(&any(), &any()));
    }

    #[test]
    fn compare_constructor_ordinals() {
        let nonnull = || mk((r(), Ty_::Tnonnull));
        let mixed = mk((r(), Ty_::Toption(nonnull())));
        let opt_int = mk((r(), Ty_::Toption(prim(Tprim::Tint))));
        let dynamic = mk((r(), Ty_::Tdynamic(None)));
        // ?nonnull (1) < nonnull (2) < dynamic (3) < ?int (4) < int (5)
        assert_eq!(ty_compare(None, &mixed, &nonnull()), Ordering::Less);
        assert_eq!(ty_compare(None, &nonnull(), &dynamic), Ordering::Less);
        assert_eq!(ty_compare(None, &dynamic, &opt_int), Ordering::Less);
        assert_eq!(
            ty_compare(None, &opt_int, &prim(Tprim::Tint)),
            Ordering::Less
        );
        // Tvar (9) < Tgeneric (11) < Tclass (204) < Tlabel (206)
        let var = mk((r(), Ty_::Tvar(1)));
        let label = mk((r(), Ty_::Tlabel("A".to_string())));
        assert_eq!(ty_compare(None, &var, &generic("T")), Ordering::Less);
        assert_eq!(
            ty_compare(None, &generic("T"), &class("\\C", vec![])),
            Ordering::Less
        );
        assert_eq!(
            ty_compare(None, &class("\\C", vec![]), &label),
            Ordering::Less
        );
    }

    #[test]
    fn compare_unions_with_and_without_normalize_lists() {
        let u1 = union(vec![prim(Tprim::Tint), prim(Tprim::Tfloat)]);
        let u2 = union(vec![prim(Tprim::Tfloat), prim(Tprim::Tint)]);
        assert_ne!(ty_compare(None, &u1, &u2), Ordering::Equal);
        assert_ne!(ty_compare(Some(false), &u1, &u2), Ordering::Equal);
        assert_eq!(ty_compare(Some(true), &u1, &u2), Ordering::Equal);
        assert!(ty_equal(Some(true), &u1, &u2));
        assert!(!ty_equal(None, &u1, &u2));
        // normalize_lists reaches unions nested in options, but neither the
        // type arguments of classes nor the parameters of functions.
        let o1 = mk((r(), Ty_::Toption(u1.clone())));
        let o2 = mk((r(), Ty_::Toption(u2.clone())));
        assert_eq!(ty_compare(Some(true), &o1, &o2), Ordering::Equal);
        let c1 = class("\\C", vec![u1.clone()]);
        let c2 = class("\\C", vec![u2.clone()]);
        assert_ne!(ty_compare(Some(true), &c1, &c2), Ordering::Equal);
        let f1 = mk((
            r(),
            Ty_::Tfun(Rc::new(fun_type(vec![u1.clone()], prim(Tprim::Tvoid)))),
        ));
        let f2 = mk((
            r(),
            Ty_::Tfun(Rc::new(fun_type(vec![u2.clone()], prim(Tprim::Tvoid)))),
        ));
        assert_ne!(ty_compare(Some(true), &f1, &f2), Ordering::Equal);
        let f1 = mk((r(), Ty_::Tfun(Rc::new(fun_type(vec![], u1)))));
        let f2 = mk((r(), Ty_::Tfun(Rc::new(fun_type(vec![], u2)))));
        assert_eq!(ty_compare(Some(true), &f1, &f2), Ordering::Equal);
    }

    #[test]
    fn compare_classes() {
        let a = class("\\A", vec![prim(Tprim::Tint)]);
        let b = class("\\B", vec![]);
        assert_eq!(ty_compare(None, &a, &b), Ordering::Less);
        // shorter list first
        let a0 = class("\\A", vec![]);
        assert_eq!(ty_compare(None, &a0, &a), Ordering::Less);
        // Exact < Nonexact
        let exact = mk((
            r(),
            Ty_::Tclass((Pos::NONE, "\\A".to_string()), Exact::Exact, vec![]),
        ));
        assert_eq!(ty_compare(None, &exact, &a0), Ordering::Less);
        assert!(exact_equal(&nonexact(), &nonexact()));
        assert!(!exact_equal(&Exact::Exact, &nonexact()));
        assert!(is_nonexact(&nonexact()));
    }

    #[test]
    fn compare_fun_params() {
        let mut p1 = fun_type(vec![prim(Tprim::Tint)], prim(Tprim::Tvoid));
        let mut p2 = p1.clone();
        p1.params[0].name = Some("$a".to_string());
        p2.params[0].name = Some("$b".to_string());
        // names only matter for named parameters
        assert_eq!(
            ft_params_compare(None, &p1.params, &p2.params),
            Ordering::Equal
        );
        p1.params[0].flags =
            make_fp_flags(ParamMode::FPnormal, false, false, false, false, false, true);
        p2.params[0].flags = p1.params[0].flags;
        assert_eq!(
            ft_params_compare(None, &p1.params, &p2.params),
            Ordering::Less
        );
    }

    #[test]
    fn compare_type_predicates() {
        let is_int = || pred(TypePredicate_::IsTag(TypeTag::IntTag));
        let is_null = || pred(TypePredicate_::IsTag(TypeTag::NullTag));
        assert_eq!(
            compare_type_predicate(&is_int(), &is_null()),
            Ordering::Less
        );
        assert!(equal_type_predicate(&is_int(), &is_int()));
        // As in OCaml, any two IsUnionOf are equal.
        let u1 = pred(TypePredicate_::IsUnionOf(vec![is_int()]));
        let u2 = pred(TypePredicate_::IsUnionOf(vec![is_null(), is_int()]));
        assert!(equal_type_predicate(&u1, &u2));
        let n1 = pred(TypePredicate_::IsNot(Box::new(is_int())));
        let n2 = pred(TypePredicate_::IsNot(Box::new(is_null())));
        assert_eq!(compare_type_predicate(&n1, &n2), Ordering::Less);
        assert_eq!(compare_type_predicate(&u1, &n1), Ordering::Less);
        let c1 = pred(TypePredicate_::IsTag(TypeTag::ClassTag(
            "\\C".to_string(),
            vec![TypeTagGeneric::Filled(prim(Tprim::Tint))],
        )));
        let c2 = pred(TypePredicate_::IsTag(TypeTag::ClassTag(
            "\\C".to_string(),
            vec![TypeTagGeneric::Wildcard(0)],
        )));
        assert_eq!(compare_type_predicate(&c1, &c2), Ordering::Less);
        assert!(is_type_tag_generic_wildcard(&TypeTagGeneric::Wildcard(0)));
    }

    #[test]
    fn class_id_compare_is_reversed_on_constructors() {
        type C = aast::ClassId_<(), ()>;
        let ci = |n: &str| C::CI(ast_defs::Id(Pos::NONE, n.to_string()));
        assert_eq!(
            class_id_compare(&C::CIparent, &C::CIself),
            Ordering::Greater
        );
        assert_eq!(class_id_compare(&C::CIself, &C::CIparent), Ordering::Less);
        assert_eq!(class_id_compare(&ci("\\A"), &ci("\\B")), Ordering::Less);
        assert!(class_id_equal(&C::CIstatic, &C::CIstatic));
        assert!(!class_id_equal(&ci("\\A"), &C::CIstatic));
    }

    #[test]
    fn tshape_field() {
        let lit = |s: &str| TshapeFieldName::TSFlitStr(PosByteString(Pos::NONE, s.into()));
        let re = |s: &str| TshapeFieldName::TSFregexGroup(PosString(Pos::NONE, s.to_string()));
        let cc = |c: &str, m: &str| {
            TshapeFieldName::TSFclassConst(
                (Pos::NONE, c.to_string()),
                PosString(Pos::NONE, m.to_string()),
            )
        };
        assert_eq!(t_shape_field::compare(&re("z"), &lit("a")), Ordering::Less);
        assert_eq!(
            t_shape_field::compare(&lit("z"), &cc("A", "B")),
            Ordering::Less
        );
        assert_eq!(
            t_shape_field::compare(&cc("A", "C"), &cc("A", "B")),
            Ordering::Greater
        );
        assert!(t_shape_field::equal(&lit("a"), &lit("a")));
        assert_eq!(t_shape_field::name(&cc("A", "B")), "A::B");
        assert_eq!(t_shape_field::name(&lit("a")), "a");
        let of_ast = t_shape_field::of_ast(
            |p| p.clone(),
            &ast_defs::ShapeFieldName::SFclassname(ast_defs::Id(Pos::NONE, "\\C".to_string())),
        );
        assert_eq!(t_shape_field::name(&of_ast), "\\C::class");
    }

    #[test]
    fn shapes() {
        let field = |s: &str| {
            TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
                Pos::NONE,
                s.into(),
            )))
        };
        let shape = |fields: Vec<(&str, Ty)>, origin: TypeOrigin| {
            mk((
                r(),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin,
                    unknown_value: union(vec![]),
                    fields: fields
                        .into_iter()
                        .map(|(k, ty)| {
                            (
                                field(k),
                                ShapeFieldType {
                                    optional: false,
                                    ty,
                                },
                            )
                        })
                        .collect(),
                })),
            ))
        };
        let s1 = shape(vec![("a", prim(Tprim::Tint))], TypeOrigin::MissingOrigin);
        let s2 = shape(vec![("a", prim(Tprim::Tbool))], TypeOrigin::MissingOrigin);
        let s3 = shape(
            vec![("a", prim(Tprim::Tint)), ("b", prim(Tprim::Tint))],
            TypeOrigin::MissingOrigin,
        );
        assert_ne!(ty_compare(None, &s1, &s2), Ordering::Equal);
        assert_eq!(ty_compare(None, &s1, &s3), Ordering::Less);
        // Same origin: equal whatever the fields.
        let alias = || TypeOrigin::FromAlias("\\A".to_string(), None);
        let s1 = shape(vec![("a", prim(Tprim::Tint))], alias());
        let s2 = shape(vec![("a", prim(Tprim::Tbool))], alias());
        assert_eq!(ty_compare(None, &s1, &s2), Ordering::Equal);
        assert!(!same_type_origin(
            &TypeOrigin::MissingOrigin,
            &TypeOrigin::MissingOrigin
        ));
        // find_locl_ty visits the fields in the order of their keys
        let s = shape(
            vec![("b", generic("T2")), ("a", generic("T1"))],
            TypeOrigin::MissingOrigin,
        );
        let found = find_locl_ty(&s, &|ty| matches!(get_node(ty), Ty_::Tgeneric(_)));
        assert!(matches!(found.as_ref().map(get_node), Some(Ty_::Tgeneric(n)) if n == "T1"));
    }

    #[test]
    fn find_locl_ty_order() {
        let is_generic = |ty: &Ty| matches!(get_node(ty), Ty_::Tgeneric(_));
        let name = |ty: Option<Ty>| match ty.as_ref().map(get_node) {
            Some(Ty_::Tgeneric(n)) => Some(n.clone()),
            _ => None,
        };
        // class: type arguments in order
        let ty = class("\\C", vec![prim(Tprim::Tint), generic("A"), generic("B")]);
        assert_eq!(name(find_locl_ty(&ty, &is_generic)), Some("A".to_string()));
        // function: parameters before the return type
        let ty = mk((
            r(),
            Ty_::Tfun(Rc::new(fun_type(
                vec![prim(Tprim::Tint), generic("P")],
                generic("R"),
            ))),
        ));
        assert_eq!(name(find_locl_ty(&ty, &is_generic)), Some("P".to_string()));
        // newtype: arguments before the bound
        let ty = mk((
            r(),
            Ty_::Tnewtype("\\N".to_string(), vec![generic("A")], generic("B")),
        ));
        assert_eq!(name(find_locl_ty(&ty, &is_generic)), Some("A".to_string()));
        assert_eq!(name(find_locl_ty(&prim(Tprim::Tint), &is_generic)), None);
        // the type itself first
        assert_eq!(
            name(find_locl_ty(&generic("T"), &is_generic)),
            Some("T".to_string())
        );
    }

    #[test]
    fn locl_subst_apply() {
        let combine = |src: Reason, _dest: Reason| src;
        let mut subst = locl_subst::T::new();
        subst.insert(
            "T".to_string(),
            with_reason(prim(Tprim::Tint), crate::typing_reason::none()),
        );
        let ty = class(
            "\\C",
            vec![
                with_reason(generic("T"), crate::typing_reason::invalid()),
                generic("U"),
                mk((r(), Ty_::Toption(generic("T")))),
            ],
        );
        let res = locl_subst::apply(ty, &subst, &combine);
        match get_node(&res) {
            Ty_::Tclass(_, _, tyl) => {
                assert!(matches!(get_node(&tyl[0]), Ty_::Tprim(Tprim::Tint)));
                // the reason is the combination of the two
                assert!(matches!(&**get_reason(&tyl[0]), crate::typing_reason::T_::Invalid));
                assert!(matches!(get_node(&tyl[1]), Ty_::Tgeneric(n) if n == "U"));
                assert!(
                    matches!(get_node(&tyl[2]), Ty_::Toption(ty) if matches!(get_node(ty), Ty_::Tprim(Tprim::Tint)))
                );
            }
            _ => panic!("expected a class"),
        }
        // empty substitution: unchanged
        let res = locl_subst::apply(generic("T"), &locl_subst::T::new(), &combine);
        assert!(matches!(get_node(&res), Ty_::Tgeneric(n) if n == "T"));
    }

    #[test]
    fn fun_flags() {
        let ft = fun_type(vec![prim(Tprim::Tint)], prim(Tprim::Tvoid));
        assert!(!get_ft_is_function_pointer(&ft));
        let ft = set_ft_is_function_pointer(ft, true);
        assert!(get_ft_is_function_pointer(&ft));
        let ft = set_ft_is_function_pointer(ft, false);
        assert!(!get_ft_is_function_pointer(&ft));
        let ft = set_ft_readonly_this(set_ft_returns_readonly(ft, true), true);
        assert!(get_ft_returns_readonly(&ft) && get_ft_readonly_this(&ft));
        assert_eq!(get_ft_fun_kind(&ft), ast_defs::FunKind::FSync);
        let mut ft = ft;
        ft.flags |= FunTypeFlags::ASYNC | FunTypeFlags::GENERATOR;
        assert_eq!(get_ft_fun_kind(&ft), ast_defs::FunKind::FAsyncGenerator);
        assert!(get_ft_async(&ft) && get_ft_generator(&ft));
        let flags = make_fp_flags(ParamMode::FPinout, true, false, true, false, true, false);
        // the bits are those of Typing_defs_flags.FunParam
        assert_eq!(flags.bits(), (1 << 1) | (1 << 0) | (1 << 8) | (1 << 9));
        let mut fp = ft.params[0].clone();
        fp.flags = flags;
        assert_eq!(get_fp_mode(&fp), ParamMode::FPinout);
        assert!(get_fp_accept_disposable(&fp) && get_fp_readonly(&fp) && get_fp_splat(&fp));
        assert!(!get_fp_is_optional(&fp) && !get_fp_is_named(&fp));
        assert!(!get_fp_ignore_readonly_error(&fp));
    }

    #[test]
    fn vars_and_misc() {
        let v = mk((r(), Ty_::Tvar(7)));
        assert_eq!(get_var(&v), Some(7));
        assert!(is_var_v(&v, 7));
        assert!(!is_var_v(&v, 8));
        assert_eq!(get_var(&prim(Tprim::Tint)), None);
        assert_eq!(string_of_visibility(&CeVisibility::Vpublic), "public");
        assert_eq!(
            string_of_visibility(&CeVisibility::VprotectedInternal {
                class_id: "C".to_string(),
                module__: "m".to_string()
            }),
            "protected internal"
        );
        assert_eq!(
            user_attribute_param_to_string(&UserAttributeParam::Int("3".to_string())),
            "3"
        );
        assert!(tyl_equal(
            &[prim(Tprim::Tint), generic("T")],
            &[prim(Tprim::Tint), generic("T")]
        ));
        assert!(!tyl_equal(&[prim(Tprim::Tint)], &[]));
        assert_eq!(
            chain_compare(Ordering::Equal, || Ordering::Greater),
            Ordering::Greater
        );
        assert_eq!(
            chain_compare(Ordering::Less, || Ordering::Greater),
            Ordering::Less
        );
    }

    #[test]
    fn hash_agrees_with_equality() {
        use std::hash::Hash;
        use std::hash::Hasher;
        fn h(ty: &Ty) -> u64 {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            ty.hash(&mut s);
            s.finish()
        }
        // reasons, positions and the type variable of dynamic are ignored
        let a = class(
            "\\C",
            vec![prim(Tprim::Tint), mk((r(), Ty_::Tdynamic(None)))],
        );
        let b = with_reason(
            class(
                "\\C",
                vec![
                    with_reason(prim(Tprim::Tint), crate::typing_reason::invalid()),
                    mk((r(), Ty_::Tdynamic(Some(4)))),
                ],
            ),
            crate::typing_reason::invalid(),
        );
        assert!(a == b);
        assert_eq!(h(&a), h(&b));
        // any two IsUnionOf are equal
        let is_int = || pred(TypePredicate_::IsTag(TypeTag::IntTag));
        let u1 = mk((
            r(),
            Ty_::Tneg(pred(TypePredicate_::IsUnionOf(vec![is_int()]))),
        ));
        let u2 = mk((r(), Ty_::Tneg(pred(TypePredicate_::IsUnionOf(vec![])))));
        assert!(u1 == u2);
        assert_eq!(h(&u1), h(&u2));
        // the bounds of refined constants are compared as sets
        let refined = |lower: Vec<Ty>| {
            let mut cr_consts = SMap::new();
            cr_consts.insert(
                "T".to_string(),
                RefinedConst {
                    bound: RefinedConstBound::TRloose(RefinedConstBounds {
                        lower,
                        upper: vec![],
                    }),
                    is_ctx: false,
                },
            );
            mk((
                r(),
                Ty_::Tclass(
                    (Pos::NONE, "\\C".to_string()),
                    Exact::Nonexact(ClassRefinement {
                        cr_consts: cr_consts.into(),
                    }),
                    vec![],
                ),
            ))
        };
        let c1 = refined(vec![prim(Tprim::Tint), prim(Tprim::Tfloat)]);
        let c2 = refined(vec![prim(Tprim::Tfloat), prim(Tprim::Tint)]);
        assert!(c1 == c2);
        assert_eq!(h(&c1), h(&c2));
        assert!(a != c1);
        assert_ne!(h(&prim(Tprim::Tint)), h(&prim(Tprim::Tfloat)));
    }

    #[test]
    fn decl_types() {
        use pos::Positioned;
        use pos::TypeName;
        use ty::decl::ty as d;
        use ty::reason::Reason as _;
        type R = crate::ctx::R;
        let none = || R::none();
        let int = || DeclTy::prim(none(), Tprim::Tint);
        let float = || DeclTy::prim(none(), Tprim::Tfloat);
        let apply = |n: &str, tyl: Vec<DeclTy>| {
            DeclTy::new(
                none(),
                d::Ty_::Tapply(Box::new((
                    Positioned::new(pos::BPos::none(), TypeName::new(n)),
                    tyl.into_boxed_slice(),
                ))),
            )
        };
        assert!(equal_decl_ty(&int(), &int()));
        assert!(!equal_decl_ty(&int(), &float()));
        // names are compared as strings
        assert_eq!(
            compare_decl_ty(None, &apply("\\B", vec![]), &apply("\\A", vec![])),
            Ordering::Greater
        );
        // Tapply (101) is after the constructors that exist in both phases
        assert_eq!(
            compare_decl_ty(None, &apply("\\A", vec![]), &int()),
            Ordering::Greater
        );
        let u1 = DeclTy::new(none(), d::Ty_::Tunion(vec![int(), float()].into()));
        let u2 = DeclTy::new(none(), d::Ty_::Tunion(vec![float(), int()].into()));
        assert_ne!(compare_decl_ty(None, &u1, &u2), Ordering::Equal);
        assert_eq!(compare_decl_ty(Some(true), &u1, &u2), Ordering::Equal);
        assert!(equal_decl_tyl(&[int(), float()], &[int(), float()]));
        assert!(!equal_decl_tyl(&[int()], &[int(), float()]));

        // transform: replace int by float everywhere, do not look into C<_>
        let ty = apply(
            "\\A",
            vec![
                int(),
                apply("\\C", vec![int()]),
                DeclTy::new(none(), d::Ty_::Toption(int())),
            ],
        );
        let on_ty = |ty: DeclTy, _ctx: &()| match ty.node_ref() {
            d::Ty_::Tprim(Tprim::Tint) => ((), TransformTopDown::Stop(float())),
            d::Ty_::Tapply(a) if a.0.id_ref().as_str() == "\\C" => ((), TransformTopDown::Stop(ty)),
            _ => ((), TransformTopDown::Continue(ty)),
        };
        let on_rc_bound = |b: DeclRefinedConstBound, _ctx: &()| ((), TransformTopDown::Continue(b));
        let res = transform_top_down_decl_ty(ty, &on_ty, &on_rc_bound, &());
        let expected = apply(
            "\\A",
            vec![
                float(),
                apply("\\C", vec![int()]),
                DeclTy::new(none(), d::Ty_::Toption(float())),
            ],
        );
        assert!(equal_decl_ty(&res, &expected));
    }
}
