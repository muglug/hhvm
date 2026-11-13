// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_defs.ml`. See `hh/PORTING.md`.
//!
//! `include Typing_defs_core`: everything of `crate::typing_defs_core` is
//! re-exported, so read the header of that file for which Rust type stands for
//! `locl_ty` (here: [`Ty`]) and for `decl_ty` ([`DeclTy`], the `hackrs` type).
//!
//! # The records of declarations
//!
//! `class_elt`, `fun_elt`, `class_const`, `typeconst_type`, `typedef_type`,
//! ... are the types that the declarations of this crate are made of, under
//! the names that `oxidized::typing_defs` gives them:
//!
//! - [`ClassElt`] is `crate::folded_class::ClassElt` (`oxidized`'s has an
//!   `oxidized` type that is not lazy; `hackrs` has no element with its type);
//! - the others are the `hackrs` records, with the reason of this crate:
//!   [`TypeconstType`] is `ty::decl::TypeConst<R>`, [`ClassConst`] is
//!   `ty::decl::ClassConst<R>`, [`FunElt`], [`TypedefType`], [`EnumType`],
//!   [`ConstDecl`], [`Requirement`], [`ConstraintRequirement`],
//!   [`ClassConstRef`], [`ConstValue`], ...;
//! - what `hackrs` does not have, or takes from `oxidized` itself, is
//!   `oxidized`'s: [`PackageRequirement`], [`ClassConstKind`],
//!   [`VisibilityBehavior`], [`DeserializationError`],
//!   [`PartiallyAbstractTypeconst`].
//!
//! The functions over these records here (`get_ce_*`,
//! `class_elt_is_private_not_lsb`, `is_typeconst_type_abstract`,
//! `to_requirement`, `Const_value`, `CCR`) take those types.
//! `Attributes.mem`/`find` take the user attributes of either representation.
//!
//! The types that `oxidized` does not have (`expand_env`, `wildcard_action`,
//! `phase_ty`) are defined here and named the `oxidized` way.

use std::cmp::Ordering;
use std::sync::LazyLock;
use std::sync::atomic::AtomicBool;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::local_id::LocalId;
use oxidized::tany_sentinel::TanySentinel;
pub use oxidized::typing_defs::ClassConstKind;
pub use oxidized::typing_defs::DeserializationError;
pub use oxidized::typing_defs::PackageRequirement;
pub use oxidized::typing_defs::PartiallyAbstractTypeconst;
pub use oxidized::typing_defs::VisibilityBehavior;
use oxidized::typing_defs_flags::ClassEltFlags;
use oxidized::typing_defs_flags::ClassEltFlagsArgs;
/// `class_const_from`
pub use ty::decl::ClassConstFrom;
/// `class_const_ref`
pub use ty::decl::ClassConstRef;
/// `Const_value.t`
pub use ty::decl::ConstValue;

use crate::ctx::R;
/// `class_elt`
pub use crate::folded_class::ClassElt;
pub use crate::typing_defs_core::*;

/// `const_decl`
pub type ConstDecl = ty::decl::ConstDecl<R>;
/// `fun_elt`
pub type FunElt = ty::decl::ty::FunElt<R>;
/// `class_const`
pub type ClassConst = ty::decl::ClassConst<R>;
/// `module_def_type`
pub type ModuleDefType = ty::decl::ty::ModuleDefType<R>;
/// `requirement`
pub type Requirement = ty::decl::Requirement<R>;
/// `constraint_requirement`
pub type ConstraintRequirement = ty::decl::folded::ConstraintRequirement<R>;
/// `abstract_typeconst`
pub type AbstractTypeconst = ty::decl::AbstractTypeconst<R>;
/// `concrete_typeconst`
pub type ConcreteTypeconst = ty::decl::ConcreteTypeconst<R>;
/// `typeconst`
pub type Typeconst = ty::decl::Typeconst<R>;
/// `typeconst_type`
pub type TypeconstType = ty::decl::TypeConst<R>;
/// `enum_type`
pub type EnumType = ty::decl::EnumType<R>;
/// `typedef_case_type_variant`
pub type TypedefCaseTypeVariant = ty::decl::ty::TypedefCaseTypeVariant<R>;
/// `typedef_type_assignment`
pub type TypedefTypeAssignment = ty::decl::ty::TypedefTypeAssignment<R>;
/// `typedef_type`
pub type TypedefType = ty::decl::ty::TypedefType<R>;

/// `module CCR`
pub mod ccr {
    use super::*;

    pub type T = ClassConstRef;

    /// We're deriving the compare function by hand to sync it with the rust code.
    /// In the decl parser I need to sort these class_const_from in the same
    /// way. I used `cargo expand` to see how Cargo generated they Ord/PartialOrd
    /// functions.
    pub fn compare_class_const_from(ccf0: &ClassConstFrom, ccf1: &ClassConstFrom) -> Ordering {
        match (ccf0, ccf1) {
            (ClassConstFrom::Self_, ClassConstFrom::Self_) => Ordering::Equal,
            (ClassConstFrom::From(lhs), ClassConstFrom::From(rhs)) => {
                lhs.as_str().cmp(rhs.as_str())
            }
            (ClassConstFrom::Self_, ClassConstFrom::From(_)) => Ordering::Less,
            (ClassConstFrom::From(_), ClassConstFrom::Self_) => Ordering::Greater,
        }
    }

    pub fn compare(
        ClassConstRef(ccf0, s0): &ClassConstRef,
        ClassConstRef(ccf1, s1): &ClassConstRef,
    ) -> Ordering {
        match compare_class_const_from(ccf0, ccf1) {
            Ordering::Equal => s0.as_str().cmp(s1.as_str()),
            x => x,
        }
    }
}

/// `module CCRSet`: a set of `CCR.t`, in the order of `CCR.compare`.
/// (`ClassConstRef` has no `Ord`, and its names are interned, so the elements
/// are wrapped.)
pub mod ccr_set {
    use std::cmp::Ordering;

    use super::ClassConstRef;

    /// An element of the set: a `CCR.t` ordered by `CCR.compare`.
    #[derive(Clone, Debug)]
    pub struct Elt(pub ClassConstRef);

    impl PartialEq for Elt {
        fn eq(&self, other: &Self) -> bool {
            self.cmp(other) == Ordering::Equal
        }
    }
    impl Eq for Elt {}
    impl PartialOrd for Elt {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Elt {
        fn cmp(&self, other: &Self) -> Ordering {
            super::ccr::compare(&self.0, &other.0)
        }
    }

    pub type T = std::collections::BTreeSet<Elt>;
}

/// A recorded constant value, used to store enum-member values and
/// class-constant values used as shape keys. The representation is abstract
/// outside this module (see the .mli), so callers go through the API rather
/// than matching raw constructors.
pub mod const_value {
    use super::ConstValue;

    pub type T = ConstValue;

    /// The "no recorded value" case.
    pub fn absent() -> T {
        ConstValue::CVAbsent
    }

    /// Whether the value is `CVAbsent` (no recorded value).
    pub fn is_absent(v: &T) -> bool {
        match v {
            ConstValue::CVAbsent => true,
            _ => false,
        }
    }

    /// `Int64.of_string_opt s` is `Some n` and `Int64.to_string n = s`: whatever
    /// else `Int64.of_string` accepts (`0x`, `0u`, `_`) does not print back as
    /// itself.
    fn is_intish(s: &str) -> bool {
        match s.parse::<i64>() {
            Ok(n) => n.to_string() == s,
            Err(_) => false,
        }
    }

    /// A canonical textual rendering of the value, usable as a comparison key and
    /// a human-readable form.
    ///
    /// Values that render alike do collide as arraykeys at runtime, mirroring how
    /// Hack coerces arraykeys. An "intish" string renders as the bare int: that is
    /// a canonical integer like `"0"` or `"-5"`, within `i64` range, matching
    /// HHVM's `is_strictly_integer` -- `"00"`, `"-0"`, `"+1"`, hex and underscores
    /// are not intish and stay quoted. `CVLabel` (value equals the member name)
    /// renders like the equivalent `CVString`.
    ///
    /// The converse does not hold, so a caller cannot read differing renderings as
    /// differing values: `CVNameof` deliberately never matches the equivalent
    /// string literal, to avoid relying on name resolution here.
    ///
    /// `member_name` supplies the name for the `CVLabel` case.
    pub fn value_repr(member_name: &str, v: &T) -> String {
        match v {
            ConstValue::CVInt(n) => n.to_string(),
            ConstValue::CVLargeInt(s) => s.clone(),
            ConstValue::CVString(s) => {
                if is_intish(s) {
                    s.clone()
                } else {
                    format!("\"{}\"", s)
                }
            }
            ConstValue::CVLabel => format!("\"{}\"", member_name),
            ConstValue::CVNameof(s) => format!("nameof {}", s),
            ConstValue::CVClassPointer(s) => format!("{}::class", s),
            ConstValue::CVConstAccess(cls, member) => format!("{}::{}", cls, member),
            ConstValue::CVAbsent => "<absent>".to_string(),
        }
    }

    /// Whether the value cannot be resolved to a concrete, comparable form:
    /// absent (no recorded value), or a reference to another enum's member
    /// (`CVConstAccess`, resolvable only through the pure-alias exemption).
    pub fn is_uncheckable(v: &T) -> bool {
        match v {
            ConstValue::CVAbsent | ConstValue::CVConstAccess(_, _) => true,
            _ => false,
        }
    }

    /// For an aliasing member `X = E::A`, the accessed `(enum, member)`.
    pub fn const_access_target(v: &T) -> Option<(String, String)> {
        match v {
            ConstValue::CVConstAccess(base, target) => Some((base.clone(), target.clone())),
            _ => None,
        }
    }
}

pub fn to_requirement(cr: ConstraintRequirement) -> Requirement {
    match cr {
        ty::decl::folded::ConstraintRequirement::CREqual(r)
        | ty::decl::folded::ConstraintRequirement::CRSubtype(r) => r,
    }
}

#[derive(Clone, Debug)]
pub enum PhaseTy {
    DeclTy(DeclTy),
    LoclTy(Ty),
}

/// How should we treat the wildcard character _ when localizing?
///  1. Generate a fresh type variable, e.g. in type argument to constructor or function,
///     or in a lambda parameter or return type.
///       Example: foo<shape('a' => _)>($myshape);
///       Example: ($v : vec<_>) ==> $v[0]
///  2. As a placeholder in a formal higher-kinded type parameter
///       Example: function test<T1, T2<_>>() // T2 is HK and takes a type to a type
///  3. Generate a fresh generic (aka Skolem variable), e.g. in `is` or `as` test
///       Example: if ($x is Vector<_>) { // $x has type Vector<T#1> }
///  4. Reject, when in a type argument to a generic parameter marked <<__Explicit>>
///       Example: makeVec<_>(3)  where function makeVec<<<__Explicit>> T>(T $_): void
///  5. Reject, because the type must be explicit.
#[derive(Clone, Debug)]
pub enum WildcardAction {
    WildcardFreshTyvar,
    WildcardFreshGeneric,
    WildcardHigherKindedPlaceholder,
    /// (Shared: an expansion environment, which holds the action, is
    /// copied all the time.)
    WildcardRequireExplicit(std::rc::Rc<DeclTparam>),
    WildcardIllegal,
}

/// `show_visibility_behavior` (`[@@deriving show { with_path = false }]`).
///
/// The derived printer prints `Resolve_type_structure` in a box with a break
/// hint before its argument:
/// `(@[<2>Resolve_type_structure@ (Some "name")@])`. The break is a space as
/// long as the line fits in the margin of `Format`; when it does not, where
/// the line is broken is up to `Format`, which has no port: `todo!`.
pub fn show_visibility_behavior(v: &VisibilityBehavior) -> String {
    /// `%S`
    fn ocaml_string_literal(s: &str) -> String {
        let mut out = String::with_capacity(s.len() + 2);
        out.push('"');
        for b in s.bytes() {
            match b {
                b'"' => out.push_str("\\\""),
                b'\\' => out.push_str("\\\\"),
                b'\n' => out.push_str("\\n"),
                b'\t' => out.push_str("\\t"),
                b'\r' => out.push_str("\\r"),
                0x08 => out.push_str("\\b"),
                b' '..=b'~' => out.push(b as char),
                _ => out.push_str(&format!("\\{:03}", b)),
            }
        }
        out.push('"');
        out
    }
    match v {
        VisibilityBehavior::AlwaysExpandNewtype => "Always_expand_newtype".to_string(),
        VisibilityBehavior::ExpandVisibleNewtypeOnly => "Expand_visible_newtype_only".to_string(),
        VisibilityBehavior::NeverExpandNewtype => "Never_expand_newtype".to_string(),
        VisibilityBehavior::ResolveTypeStructure(x) => {
            let arg = match x {
                None => "None".to_string(),
                Some(x) => format!("(Some {})", ocaml_string_literal(x)),
            };
            let line = format!("(Resolve_type_structure {})", arg);
            // The margin of a formatter is 78 or 80 depending on where one
            // looks; a line of at most 78 characters fits in both.
            if line.len() > 78 {
                todo!(
                    "Typing_defs.show_visibility_behavior: needs a port of OCaml's Format to \
                     break a line that does not fit in the margin"
                )
            }
            line
        }
    }
}

pub fn is_default_visibility_behaviour(v: &VisibilityBehavior) -> bool {
    match v {
        VisibilityBehavior::ExpandVisibleNewtypeOnly => true,
        _ => false,
    }
}

pub fn default_visibility_behaviour() -> VisibilityBehavior {
    VisibilityBehavior::ExpandVisibleNewtypeOnly
}

/// Tracks information about how a type was expanded
#[derive(Clone)]
pub struct ExpandEnv {
    pub type_expansions: crate::type_expansions::T,
    /// Localize internal classes outside their module as if newtypes i.e. opaque
    pub make_internal_opaque: bool,
    pub visibility_behavior: VisibilityBehavior,
    /// (A `pmap::Map`, not an `im::OrdMap`: a substitution has a few
    /// entries, and an `im` map allocates a node of 64 slots for its first.)
    pub substs: crate::pmap::Map<String, Ty>,
    pub no_substs: im::OrdSet<String>,
    pub this_ty: Ty,
    pub on_error: Option<crate::typing_error::reasons_callback::T>,
    pub wildcard_action: WildcardAction,
    /// If true, for refinement hints (is/as), approximate E by ~E & arraykey to account
    /// for intish and stringish casts
    pub ish_weakening: bool,
    /// True when localizing a type that appears under a type constructor
    /// (e.g. the T in vec<T>, (T, int), shape('a' => T)). Recursive case
    /// type references in these positions are "guarded" by the constructor,
    /// so on cycle we preserve the Tnewtype identity instead of collapsing
    /// to mixed — this prevents unsound subtyping through the constructor's
    /// type parameters.
    pub under_type_constructor: bool,
    /// When false, skip calling Typing_intersection.intersect_list during
    /// localization of Tintersection types, and instead construct the
    /// intersection directly. This breaks the cycle
    /// localize -> intersect_list -> sub_type -> localize
    /// that can occur when localizing recursive case type upper bounds.
    pub simplify_intersections: bool,
}

/// `empty_expand_env`, a value in OCaml: every use shares one record (and so
/// one `this_ty`, physically). Here, one per thread (the types hold `Rc`s),
/// cloned out: building one allocates two `im` tree nodes and the type.
pub fn empty_expand_env() -> ExpandEnv {
    thread_local! {
        static EMPTY_EXPAND_ENV: ExpandEnv = make_empty_expand_env();
    }
    EMPTY_EXPAND_ENV.with(ExpandEnv::clone)
}

fn make_empty_expand_env() -> ExpandEnv {
    ExpandEnv {
        type_expansions: crate::type_expansions::empty(),
        visibility_behavior: default_visibility_behaviour(),
        make_internal_opaque: true,
        substs: crate::pmap::Map::new(),
        no_substs: im::OrdSet::new(),
        this_ty: mk((
            reason::none(),
            Ty_::Tgeneric(sn::typehints::THIS.to_string()),
        )),
        on_error: None,
        wildcard_action: WildcardAction::WildcardFreshTyvar,
        ish_weakening: false,
        under_type_constructor: false,
        simplify_intersections: true,
    }
}

pub fn empty_expand_env_with_on_error(
    on_error: crate::typing_error::reasons_callback::T,
) -> ExpandEnv {
    ExpandEnv {
        on_error: Some(on_error),
        ..empty_expand_env()
    }
}

/// `add_type_expansion_check_cycles ety_env expansion` adds
/// and `expansion` to `ety_env.expansions` and
/// checks that that `expansion` hasn't already been done,
/// i.e. wasn't already in ety_env.expansions.
///
/// As in OCaml, the result is a new environment: `ety_env` is still the one
/// to use for what is not under this expansion.
pub fn add_type_expansion_check_cycles(
    ety_env: &ExpandEnv,
    exp: crate::type_expansions::Expansion,
) -> Result<ExpandEnv, crate::type_expansions::CycleReporter> {
    match crate::type_expansions::add_and_check_cycles(&ety_env.type_expansions, exp) {
        Ok(type_expansions) => Ok(ExpandEnv {
            type_expansions,
            ..ety_env.clone()
        }),
        Err(cycle) => Err((cycle, ety_env.on_error.clone())),
    }
}

/// Returns whether there was an attempt at expanding a cyclic type.
pub fn cyclic_expansion(env: &ExpandEnv) -> bool {
    crate::type_expansions::cyclic_expansion(&env.type_expansions)
}

pub fn get_class_type(t: &Ty) -> Option<(PosId, Exact, Vec<Ty>)> {
    match get_node(t) {
        Ty_::Tclass(id, exact, tyl) => Some((id.clone(), exact.clone(), tyl.clone())),
        _ => None,
    }
}

pub fn is_tyvar(t: &Ty) -> bool {
    get_var(t).is_some()
}

pub fn is_generic(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tgeneric(_) => true,
        _ => false,
    }
}

pub fn is_dynamic(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tdynamic(_) => true,
        _ => false,
    }
}

pub fn is_nothing(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tunion(tyl) if tyl.is_empty() => true,
        _ => false,
    }
}

/// (`Twildcard` exists only in the declared phase.)
pub fn is_wildcard(t: &DeclTy) -> bool {
    match t.node_ref() {
        ty::decl::Ty_::Twildcard => true,
        _ => false,
    }
}

pub fn is_nonnull(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tnonnull => true,
        _ => false,
    }
}

pub fn is_fun(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tfun(_) => true,
        _ => false,
    }
}

pub fn is_any(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tany(_) => true,
        _ => false,
    }
}

pub fn is_generic_equal_to(n: &str, t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tgeneric(n_) if n == n_ => true,
        _ => false,
    }
}

pub fn is_prim(p: ast_defs::Tprim, t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tprim(p_) if p == *p_ => true,
        _ => false,
    }
}

pub fn is_union(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tunion(_) => true,
        _ => false,
    }
}

pub fn is_neg(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tneg(_) => true,
        _ => false,
    }
}

pub fn is_union_or_inter_type(ty: &Ty) -> bool {
    // do not expand type here!
    match get_node(ty) {
        Ty_::Toption(_) | Ty_::Tunion(_) | Ty_::Tintersection(_) => true,
        Ty_::Tnonnull
        | Ty_::Tneg(_)
        | Ty_::Tdynamic(_)
        | Ty_::Tany(_)
        | Ty_::Tprim(_)
        | Ty_::Tfun(_)
        | Ty_::Ttuple(_)
        | Ty_::Tshape(_)
        | Ty_::Tvar(_)
        | Ty_::Tnewtype(_, _, _)
        | Ty_::Tdependent(_, _)
        | Ty_::Tgeneric(_)
        | Ty_::Tclass(_, _, _)
        | Ty_::TvecOrDict(_, _)
        | Ty_::Tlabel(_)
        | Ty_::Taccess(_)
        | Ty_::TclassPtr(_) => false,
    }
}

pub mod named_params {
    use super::*;

    pub fn name_of_named_param(fp: &FunParam) -> Option<String> {
        if crate::typing_defs_core::get_fp_is_named(fp) {
            match &fp.name {
                Some(raw_name) => {
                    let name = raw_name.strip_prefix('$').unwrap_or(raw_name);
                    Some(name.to_string())
                }
                None => {
                    // TODO(named_params): remove runtime invariant checking,
                    // perhaps by changing fp.fp_name to `string` instead of `string option`
                    //
                    // Hack_event_logger.invariant_violation_bug
                    //   ~path:(Pos_or_decl.filename fp.fp_pos)
                    //   "named param without name"
                    // does nothing in this build (stubs/logging/hack_event_logger.ml).
                    None
                }
            }
        } else {
            None
        }
    }

    pub fn name_of_arg<Ex, En>(arg: &aast::Argument<Ex, En>) -> Option<String> {
        match arg {
            aast::Argument::Ainout(_, _) | aast::Argument::Anormal(_) => None,
            aast::Argument::Anamed(ast_defs::Id(_, name), _) => Some(name.clone()),
        }
    }
}

/// A named-variadic parameter is the last entry of `ft.ft_params`. It
/// represents "accepts any number of named args of this element type", NOT a
/// required named parameter.
pub fn ft_named_variadic_param(ft: &FunType) -> Option<&FunParam> {
    if get_ft_named_variadic(ft) {
        ft.params.last()
    } else {
        None
    }
}

/// `ft.ft_params` with the named-variadic entry (if any) stripped off.
pub fn ft_params_without_named_variadic(ft: &FunType) -> &[FunParam] {
    match ft_named_variadic_param(ft) {
        Some(_) => &ft.params[..ft.params.len() - 1],
        None => &ft.params,
    }
}

pub fn ft_has_positional_variadic(ft: &FunType) -> bool {
    get_ft_variadic(ft)
}

/// The identifier for this
///
/// `Local_id.make_scoped "$this"`, made once (it takes an identifier from the
/// counter of `Local_id` the first time it is asked for).
pub fn this() -> LocalId {
    static THIS: LazyLock<LocalId> = LazyLock::new(|| crate::local_id::make_scoped("$this"));
    THIS.clone()
}

/// This should be the ONLY way that Tany is constructed anywhere in the
/// codebase.
pub fn make_tany() -> Ty_ {
    Ty_::Tany(TanySentinel)
}

/// Required parameters (number and names). Does not include optional, variadic, or
/// type-splat parameters
pub fn arity_and_names_required(ft: &FunType) -> (isize, im::OrdSet<String>) {
    let non_splat_non_optional = ft_params_without_named_variadic(ft)
        .iter()
        .filter(|fp| !get_fp_is_optional(fp) && !get_fp_splat(fp));
    let mut names_required = Vec::new();
    let mut positional_params = Vec::new();
    for fp in non_splat_non_optional {
        match named_params::name_of_named_param(fp) {
            Some(name) => names_required.push(name),
            None => positional_params.push(fp),
        }
    }
    let arity_raw = positional_params.len() as isize;
    let arity_required = if ft_has_positional_variadic(ft) {
        arity_raw - 1
    } else {
        arity_raw
    };
    // (`SSet.of_list`; the empty set without allocating a node, as most
    // functions have no named parameters: see `crate::im_empty`.)
    let names_required = if names_required.is_empty() {
        crate::im_empty::ord_set()
    } else {
        names_required.into_iter().collect()
    };
    (arity_required, names_required)
}

pub fn get_param_mode(callconv: &ast_defs::ParamKind) -> ParamMode {
    match callconv {
        ast_defs::ParamKind::Pinout(_) => ParamMode::FPinout,
        ast_defs::ParamKind::Pnormal => ParamMode::FPnormal,
    }
}

pub mod dependent_kind {
    use super::*;

    pub fn to_string(d: &DependentType) -> String {
        match d {
            // Expression_id.display
            DependentType::DTexpr(i) => crate::typing_reason::expression_id_display(*i),
        }
    }

    pub fn is_generic_dep_ty(s: &str) -> bool {
        s.contains("::") || s == sn::typehints::THIS
    }

    /// The first match of `<expr#[0-9]+>::\(T[A-Za-z]+\)` in `str`, as
    /// `Str.search_forward` finds it: its group.
    pub fn strip_generic_dep_ty(str: &str) -> Option<String> {
        let bytes = str.as_bytes();
        let prefix = b"<expr#";
        let mut start = 0;
        while start + prefix.len() <= bytes.len() {
            if &bytes[start..start + prefix.len()] == prefix {
                let mut i = start + prefix.len();
                let digits = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                if i > digits && bytes[i..].starts_with(b">::T") {
                    let group = i + 3;
                    let mut j = group + 1;
                    while j < bytes.len() && bytes[j].is_ascii_alphabetic() {
                        j += 1;
                    }
                    if j > group + 1 {
                        return Some(str[group..j].to_string());
                    }
                }
            }
            start += 1;
        }
        None
    }

    pub fn is_expr_dep_ty(str: &str) -> bool {
        strip_generic_dep_ty(str).is_some()
    }
}

pub fn is_denotable(ty: &Ty) -> bool {
    match get_node(ty) {
        // Possible encodings of nothing
        Ty_::Tunion(tyl) if tyl.is_empty() => true,
        // Possible encodings of mixed
        Ty_::Tintersection(tyl) if tyl.is_empty() => true,
        Ty_::Tnonnull | Ty_::Tdynamic(_) | Ty_::Tprim(_) | Ty_::Tnewtype(_, _, _) => true,
        Ty_::Tunion(tyl) if tyl.len() == 2 => {
            let ty = &tyl[0];
            let ty_ = &tyl[1];
            match (get_node(ty), get_node(ty_)) {
                (Ty_::Tprim(ast_defs::Tprim::Tfloat), Ty_::Tprim(ast_defs::Tprim::Tint))
                | (Ty_::Tprim(ast_defs::Tprim::Tint), Ty_::Tprim(ast_defs::Tprim::Tfloat)) => true,
                (Ty_::Tclass((_, id), _, _), Ty_::Tprim(ast_defs::Tprim::Tint))
                | (Ty_::Tprim(ast_defs::Tprim::Tint), Ty_::Tclass((_, id), _, _))
                    if id == C_STRING =>
                {
                    true
                }
                _ => false,
            }
        }
        Ty_::Tclass(_, _, ts) => ts.iter().all(is_denotable),
        Ty_::Ttuple(TupleType {
            required: t_required,
            optional: t_optional,
            extra: t_extra,
        }) => {
            t_required.iter().all(is_denotable)
                && t_optional.iter().all(is_denotable)
                && tuple_extra_is_denotable(t_extra)
        }
        Ty_::TvecOrDict(tk, tv) => is_denotable(tk) && is_denotable(tv),
        Ty_::Taccess(TaccessType(ty, _)) => is_denotable(ty),
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: _,
            unknown_value: unknown_field_type,
            fields: sm,
        })) => {
            sm.iter()
                .all(|(_, ShapeFieldType { ty: sft_ty, .. })| is_denotable(sft_ty))
                && unknown_field_type_is_denotable(unknown_field_type)
        }
        Ty_::Tshape(ShapeType::ShapeSplat(_)) => false,
        Ty_::Tfun(ft) => {
            let FunType {
                params: ft_params,
                ret: ft_ret,
                ..
            } = &**ft;
            is_denotable(ft_ret)
                && ft_params
                    .iter()
                    .all(|FunParam { type_: fp_type, .. }| is_denotable(fp_type))
        }
        Ty_::Toption(ty) => is_denotable(ty),
        Ty_::Tgeneric(nm) => !(dependent_kind::is_generic_dep_ty(nm) || nm.contains('#')),
        Ty_::TclassPtr(ty) => is_denotable(ty),
        Ty_::Tunion(_)
        | Ty_::Tintersection(_)
        | Ty_::Tneg(_)
        | Ty_::Tany(_)
        | Ty_::Tvar(_)
        | Ty_::Tdependent(_, _)
        | Ty_::Tlabel(_) => false,
    }
}

fn tuple_extra_is_denotable(e: &TupleExtra) -> bool {
    match e {
        TupleExtra::Tsplat(t) => is_denotable(t),
        TupleExtra::Tvariadic(t) => unknown_field_type_is_denotable(t),
    }
}

fn unknown_field_type_is_denotable(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Tunion(tyl) if tyl.is_empty() => true,
        Ty_::Tintersection(tyl) if tyl.is_empty() => true,
        Ty_::Toption(ty) => match get_node(ty) {
            Ty_::Tnonnull => true,
            _ => false,
        },
        _ => false,
    }
}

/// `module ShapeFieldMap`: `include TShapeMap`, and the functions that map
/// over the types of the fields of a shape.
pub mod shape_field_map {
    use super::ShapeFieldType;
    use super::Ty;
    pub use crate::typing_defs_core::t_shape_map::*;

    pub fn map_and_rekey(
        shape_map: T<ShapeFieldType>,
        key_f: impl FnMut(Key) -> Key,
        mut value_f: impl FnMut(Ty) -> Ty,
    ) -> T<ShapeFieldType> {
        let f_over_shape_field_type = |shape_field_type: ShapeFieldType| {
            let ShapeFieldType {
                optional,
                ty: sft_ty,
            } = shape_field_type;
            ShapeFieldType {
                optional,
                ty: value_f(sft_ty),
            }
        };
        crate::typing_defs_core::t_shape_map::map_and_rekey(
            shape_map,
            key_f,
            f_over_shape_field_type,
        )
    }

    pub fn map_env<Env>(
        mut f: impl FnMut(&mut Env, Ty) -> Ty,
        env: &mut Env,
        shape_map: T<ShapeFieldType>,
    ) -> T<ShapeFieldType> {
        let f_over_shape_field_type =
            |env: &mut Env, _key: &Key, shape_field_type: ShapeFieldType| {
                let ShapeFieldType {
                    optional,
                    ty: sft_ty,
                } = shape_field_type;
                let sft_ty = f(env, sft_ty);
                ShapeFieldType {
                    optional,
                    ty: sft_ty,
                }
            };
        crate::typing_defs_core::t_shape_map::map_fields_env(f_over_shape_field_type, env, shape_map)
    }

    pub fn map_env_ty_err_opt<Env, TyErr, TyErrs>(
        mut f: impl FnMut(&mut Env, Ty) -> (Option<TyErr>, Ty),
        env: &mut Env,
        shape_map: T<ShapeFieldType>,
        combine_ty_errs: impl FnOnce(Vec<TyErr>) -> TyErrs,
    ) -> (TyErrs, T<ShapeFieldType>) {
        let f_over_shape_field_type =
            |env: &mut Env, _key: &Key, shape_field_type: ShapeFieldType| {
                let ShapeFieldType {
                    optional,
                    ty: sft_ty,
                } = shape_field_type;
                let (err, sft_ty) = f(env, sft_ty);
                (
                    err,
                    ShapeFieldType {
                        optional,
                        ty: sft_ty,
                    },
                )
            };
        crate::typing_defs_core::t_shape_map::map_fields_env_ty_err_opt(
            f_over_shape_field_type,
            env,
            shape_map,
            combine_ty_errs,
        )
    }

    pub fn map(f: impl FnMut(Ty) -> Ty, shape_map: T<ShapeFieldType>) -> T<ShapeFieldType> {
        map_and_rekey(shape_map, |x| x, f)
    }

    pub fn iter(mut f: impl FnMut(&Key, &Ty), shape_map: &T<ShapeFieldType>) {
        for (shape_map_key, ShapeFieldType { ty: sft_ty, .. }) in shape_map {
            f(shape_map_key, sft_ty)
        }
    }

    pub fn iter_values(mut f: impl FnMut(&Ty), shape_map: &T<ShapeFieldType>) {
        iter(|_, ty| f(ty), shape_map)
    }
}

/// `module ShapeFieldList` (`include Common.List` is not repeated here).
pub mod shape_field_list {
    use super::ShapeFieldType;
    use super::Ty;

    pub fn map_env<Env>(
        env: &mut Env,
        xs: Vec<ShapeFieldType>,
        mut f: impl FnMut(&mut Env, Ty) -> Ty,
    ) -> Vec<ShapeFieldType> {
        xs.into_iter()
            .map(|shape_field_type| {
                let ShapeFieldType {
                    optional,
                    ty: sft_ty,
                } = shape_field_type;
                let sft_ty = f(env, sft_ty);
                ShapeFieldType {
                    optional,
                    ty: sft_ty,
                }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Suggest mode
// ---------------------------------------------------------------------------

/// Set to true when we are trying to infer the missing type hints.
#[allow(non_upper_case_globals)]
pub static is_suggest_mode: AtomicBool = AtomicBool::new(false);

pub fn is_type_no_return(ty_: &Ty_) -> bool {
    equal_locl_ty_(&Ty_::Tprim(ast_defs::Tprim::Tnoreturn), ty_)
}

pub fn get_ce_abstract(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::ABSTRACT)
}

pub fn get_ce_final(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::FINAL)
}

pub fn get_ce_superfluous_override(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::SUPERFLUOUS_OVERRIDE)
}

pub fn get_ce_lsb(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::LSB)
}

pub fn get_ce_synthesized(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::SYNTHESIZED)
}

pub fn get_ce_const(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::CONST)
}

pub fn get_ce_lateinit(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::LATEINIT)
}

pub fn get_ce_readonly_prop_or_needs_concrete(ce: &ClassElt) -> bool {
    ce.ce_flags
        .contains(ClassEltFlags::READONLY_PROP_OR_NEEDS_CONCRETE)
}

pub fn get_ce_dynamicallycallable(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::DYNAMICALLYCALLABLE)
}

pub fn get_ce_support_dynamic_type(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::SUPPORT_DYNAMIC_TYPE)
}

pub fn get_ce_xhp_attr(ce: &ClassElt) -> Option<XhpAttr> {
    ce.ce_flags.get_xhp_attr()
}

pub fn get_ce_safe_global_variable(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::SAFE_GLOBAL_VARIABLE)
}

pub fn get_ce_no_auto_likes(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::NO_AUTO_LIKES)
}

pub fn get_ce_tests_bypass_visibility(ce: &ClassElt) -> bool {
    ce.ce_flags.contains(ClassEltFlags::TESTS_BYPASS_VISIBILITY)
}

/// `Typing_defs_flags.ClassElt.make`, which `oxidized` has as
/// `ClassEltFlags::new`.
pub fn make_ce_flags(
    xhp_attr: Option<XhpAttr>,
    abstract_: bool,
    final_: bool,
    superfluous_override: bool,
    lsb: bool,
    synthesized: bool,
    const_: bool,
    lateinit: bool,
    dynamicallycallable: bool,
    readonly_prop_or_needs_concrete: bool,
    support_dynamic_type: bool,
    needs_init: bool,
    safe_global_variable: bool,
    no_auto_likes: bool,
    tests_bypass_visibility: bool,
) -> ClassEltFlags {
    ClassEltFlags::new(ClassEltFlagsArgs {
        xhp_attr,
        is_abstract: abstract_,
        is_final: final_,
        is_superfluous_override: superfluous_override,
        is_lsb: lsb,
        is_synthesized: synthesized,
        is_const: const_,
        is_lateinit: lateinit,
        is_dynamicallycallable: dynamicallycallable,
        is_readonly_prop_or_needs_concrete: readonly_prop_or_needs_concrete,
        supports_dynamic_type: support_dynamic_type,
        needs_init,
        safe_global_variable,
        no_auto_likes,
        is_tests_bypass_visibility: tests_bypass_visibility,
    })
}

/// Return true if the element is private and not marked with the __LSB
/// attribute. Private elements are not inherited by child classes and are
/// namespaced to the containing class--if B extends A, then A may define a
/// method A::foo and B may define a method B::foo, and they both will exist in
/// the hierarchy and be callable at runtime (which method is invoked depends on
/// the caller).
///
/// The __LSB attribute can be applied to properties only. LSB properties are
/// (effectively) implicitly cloned into every subclass. This means that in the
/// typechecker, we want to avoid filtering them out in subclasses, so we treat
/// them as non-private here.
pub fn class_elt_is_private_not_lsb(elt: &ClassElt) -> bool {
    match &elt.ce_visibility {
        CeVisibility::Vprivate(_) => !get_ce_lsb(elt) && !get_ce_tests_bypass_visibility(elt),
        CeVisibility::Vprotected(_)
        | CeVisibility::Vpublic
        | CeVisibility::Vinternal(_)
        | CeVisibility::VprotectedInternal { .. } => false,
    }
}

pub fn class_elt_is_private_or_protected_not_lsb(elt: &ClassElt) -> bool {
    match &elt.ce_visibility {
        CeVisibility::Vprivate(_)
        | CeVisibility::Vprotected(_)
        | CeVisibility::VprotectedInternal { .. }
            if get_ce_lsb(elt) =>
        {
            false
        }
        CeVisibility::Vprivate(_)
        | CeVisibility::Vprotected(_)
        | CeVisibility::VprotectedInternal { .. } => true,
        CeVisibility::Vpublic | CeVisibility::Vinternal(_) => false,
    }
}

pub fn is_typeconst_type_abstract(tc: &TypeconstType) -> bool {
    match &tc.kind {
        ty::decl::Typeconst::TCConcrete(_) => false,
        ty::decl::Typeconst::TCAbstract(_) => true,
    }
}

pub fn is_arraykey(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tprim(ast_defs::Tprim::Tarraykey) => true,
        _ => false,
    }
}

/// `Naming_special_names.Classes.cString`. (`naming_special_names_rust` has it
/// as `typehints::HH_STRING` only.)
const C_STRING: &str = "\\HH\\string";

pub fn is_string(t: &Ty) -> bool {
    match get_node(t) {
        Ty_::Tclass((_, id), _, _) => id == C_STRING,
        _ => false,
    }
}

/// `module Attributes`
pub mod attributes {
    /// `user_attribute` is `oxidized::typing_defs_core::UserAttribute` in the
    /// types of this crate and in the `oxidized` declarations, and
    /// `ty::decl::UserAttribute` in the `hackrs` declarations: the functions
    /// here take either.
    pub trait UserAttribute {
        /// `snd ua_name`
        fn ua_name(&self) -> &str;
    }

    impl UserAttribute for oxidized::typing_defs_core::UserAttribute {
        fn ua_name(&self) -> &str {
            &self.name.1
        }
    }

    impl<P> UserAttribute for ty::decl::UserAttribute<P> {
        fn ua_name(&self) -> &str {
            self.name.id_ref().as_str()
        }
    }

    pub fn mem<UA: UserAttribute>(x: &str, xs: &[UA]) -> bool {
        xs.iter().any(|ua| x == ua.ua_name())
    }

    pub fn find<'a, UA: UserAttribute>(x: &str, xs: &'a [UA]) -> Option<&'a UA> {
        xs.iter().find(|ua| x == ua.ua_name())
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;
    use oxidized::pos::Pos;
    use oxidized::typing_defs_flags::FunParamFlags;
    use oxidized::typing_defs_flags::FunTypeFlags;

    use super::*;
    use crate::typing_reason::T as Reason;

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

    fn param(name: Option<&str>, flags: FunParamFlags) -> FunParam {
        FunParam {
            pos: Pos::NONE,
            name: name.map(|s| s.to_string()),
            type_: prim(Tprim::Tint),
            flags,
            def_value: None,
        }
    }

    fn fun_type(params: Vec<FunParam>, flags: FunTypeFlags) -> FunType {
        FunType {
            tparams: vec![],
            where_constraints: vec![],
            params,
            implicit_params: FunImplicitParams {
                capability: Capability::CapDefaults(Pos::NONE),
            },
            ret: prim(Tprim::Tvoid),
            flags,
            instantiated: true,
        }
    }

    #[test]
    fn predicates() {
        assert!(is_tyvar(&mk((r(), Ty_::Tvar(1)))));
        assert!(!is_tyvar(&prim(Tprim::Tint)));
        assert!(is_generic(&generic("T")));
        assert!(is_generic_equal_to("T", &generic("T")));
        assert!(!is_generic_equal_to("U", &generic("T")));
        assert!(is_dynamic(&mk((r(), Ty_::Tdynamic(None)))));
        assert!(is_nothing(&union(vec![])));
        assert!(!is_nothing(&union(vec![prim(Tprim::Tint)])));
        assert!(is_union(&union(vec![prim(Tprim::Tint)])));
        assert!(is_nonnull(&mk((r(), Ty_::Tnonnull))));
        assert!(is_any(&mk((r(), make_tany()))));
        assert!(is_prim(Tprim::Tint, &prim(Tprim::Tint)));
        assert!(!is_prim(Tprim::Tint, &prim(Tprim::Tfloat)));
        assert!(is_arraykey(&prim(Tprim::Tarraykey)));
        assert!(is_string(&class("\\HH\\string", vec![])));
        assert!(!is_string(&class("\\HH\\vec", vec![])));
        assert!(is_union_or_inter_type(&mk((
            r(),
            Ty_::Toption(prim(Tprim::Tint))
        ))));
        assert!(!is_union_or_inter_type(&prim(Tprim::Tint)));
        assert!(is_type_no_return(&Ty_::Tprim(Tprim::Tnoreturn)));
        assert!(!is_type_no_return(&Ty_::Tprim(Tprim::Tvoid)));
        let c = class("\\C", vec![prim(Tprim::Tint)]);
        let (id, exact, tyl) = get_class_type(&c).unwrap();
        assert_eq!(id.1, "\\C");
        assert!(is_nonexact(&exact));
        assert_eq!(tyl.len(), 1);
        assert!(get_class_type(&prim(Tprim::Tint)).is_none());
    }

    #[test]
    fn denotable() {
        assert!(is_denotable(&prim(Tprim::Tint)));
        assert!(is_denotable(&union(vec![])));
        // int | float and string | int only
        assert!(is_denotable(&union(vec![
            prim(Tprim::Tint),
            prim(Tprim::Tfloat)
        ])));
        assert!(is_denotable(&union(vec![
            class("\\HH\\string", vec![]),
            prim(Tprim::Tint)
        ])));
        assert!(!is_denotable(&union(vec![
            class("\\C", vec![]),
            prim(Tprim::Tint)
        ])));
        assert!(!is_denotable(&union(vec![
            prim(Tprim::Tint),
            prim(Tprim::Tbool)
        ])));
        assert!(!is_denotable(&union(vec![prim(Tprim::Tint)])));
        assert!(is_denotable(&class("\\C", vec![generic("T")])));
        assert!(!is_denotable(&class("\\C", vec![generic("T#1")])));
        assert!(!is_denotable(&generic("this")));
        assert!(!is_denotable(&generic("this::T")));
        assert!(!is_denotable(&mk((r(), Ty_::Tvar(0)))));
        // a tuple is denotable if its variadic part is nothing or mixed
        let tuple = |extra: TupleExtra| {
            mk((
                r(),
                Ty_::Ttuple(TupleType {
                    required: vec![prim(Tprim::Tint)],
                    optional: vec![],
                    extra,
                }),
            ))
        };
        assert!(is_denotable(&tuple(TupleExtra::Tvariadic(union(vec![])))));
        assert!(!is_denotable(&tuple(TupleExtra::Tvariadic(prim(
            Tprim::Tint
        )))));
        assert!(is_denotable(&tuple(TupleExtra::Tsplat(prim(Tprim::Tint)))));
    }

    #[test]
    fn dependent_kinds() {
        use dependent_kind::*;
        assert_eq!(to_string(&DependentType::DTexpr(12)), "<expr#12>");
        assert!(is_generic_dep_ty("this"));
        assert!(is_generic_dep_ty("T::TC"));
        assert!(!is_generic_dep_ty("T"));
        assert_eq!(
            strip_generic_dep_ty("<expr#1>::Tfoo"),
            Some("Tfoo".to_string())
        );
        assert_eq!(
            strip_generic_dep_ty("xx<expr#123>::TFoo::TBar"),
            Some("TFoo".to_string())
        );
        // the group stops at the first character that is not a letter
        assert_eq!(
            strip_generic_dep_ty("<expr#1>::TFoo2"),
            Some("TFoo".to_string())
        );
        // at least one digit, at least one letter after the T
        assert_eq!(strip_generic_dep_ty("<expr#>::Tfoo"), None);
        assert_eq!(strip_generic_dep_ty("<expr#1>::T"), None);
        assert_eq!(strip_generic_dep_ty("<expr#1>::Ufoo"), None);
        // a later match is found when an earlier candidate fails
        assert_eq!(
            strip_generic_dep_ty("<expr#1>::U <expr#2>::TA"),
            Some("TA".to_string())
        );
        assert!(is_expr_dep_ty("<expr#1>::TA"));
        assert!(!is_expr_dep_ty("this::TA"));
    }

    #[test]
    fn const_values() {
        use const_value::*;
        assert!(is_absent(&absent()));
        assert!(!is_absent(&ConstValue::CVLabel));
        assert_eq!(value_repr("M", &ConstValue::CVInt(-5)), "-5");
        assert_eq!(value_repr("M", &ConstValue::CVLargeInt("9".into())), "9");
        assert_eq!(value_repr("M", &ConstValue::CVString("a".into())), "\"a\"");
        // intish strings render as the bare int
        assert_eq!(value_repr("M", &ConstValue::CVString("0".into())), "0");
        assert_eq!(value_repr("M", &ConstValue::CVString("-5".into())), "-5");
        for not_intish in ["00", "-0", "+1", "0x10", "1_0", "", "9223372036854775808"] {
            assert_eq!(
                value_repr("M", &ConstValue::CVString(not_intish.into())),
                format!("\"{}\"", not_intish)
            );
        }
        assert_eq!(
            value_repr("M", &ConstValue::CVString("9223372036854775807".into())),
            "9223372036854775807"
        );
        assert_eq!(value_repr("M", &ConstValue::CVLabel), "\"M\"");
        assert_eq!(
            value_repr("M", &ConstValue::CVNameof("C".into())),
            "nameof C"
        );
        assert_eq!(
            value_repr("M", &ConstValue::CVClassPointer("C".into())),
            "C::class"
        );
        assert_eq!(
            value_repr("M", &ConstValue::CVConstAccess("E".into(), "A".into())),
            "E::A"
        );
        assert_eq!(value_repr("M", &ConstValue::CVAbsent), "<absent>");
        assert!(is_uncheckable(&ConstValue::CVAbsent));
        assert!(is_uncheckable(&ConstValue::CVConstAccess(
            "E".into(),
            "A".into()
        )));
        assert!(!is_uncheckable(&ConstValue::CVInt(1)));
        assert_eq!(
            const_access_target(&ConstValue::CVConstAccess("E".into(), "A".into())),
            Some(("E".to_string(), "A".to_string()))
        );
        assert_eq!(const_access_target(&ConstValue::CVInt(1)), None);
    }

    #[test]
    fn params_and_arity() {
        let named = FunParamFlags::NAMED;
        let optional = FunParamFlags::IS_OPTIONAL;
        let none = FunParamFlags::empty();
        assert_eq!(
            named_params::name_of_named_param(&param(Some("$x"), named)),
            Some("x".to_string())
        );
        assert_eq!(
            named_params::name_of_named_param(&param(Some("x"), named)),
            Some("x".to_string())
        );
        assert_eq!(
            named_params::name_of_named_param(&param(Some("$x"), none)),
            None
        );
        assert_eq!(named_params::name_of_named_param(&param(None, named)), None);

        // (int $a, int $b = .., named int $n, named int $o = .., int ...$rest)
        let ft = fun_type(
            vec![
                param(Some("$a"), none),
                param(Some("$b"), optional),
                param(Some("$n"), named),
                param(Some("$o"), named | optional),
                param(Some("$rest"), none),
            ],
            FunTypeFlags::VARIADIC,
        );
        assert!(ft_has_positional_variadic(&ft));
        assert!(ft_named_variadic_param(&ft).is_none());
        assert_eq!(ft_params_without_named_variadic(&ft).len(), 5);
        let (arity, names) = arity_and_names_required(&ft);
        // $a and $rest are positional and required; the variadic one is taken off
        assert_eq!(arity, 1);
        assert_eq!(names.into_iter().collect::<Vec<_>>(), vec!["n".to_string()]);

        // the named variadic parameter is the last one, and is not required
        let ft = fun_type(
            vec![param(Some("$a"), none), param(Some("$kw"), named)],
            FunTypeFlags::NAMED_VARIADIC,
        );
        assert_eq!(
            ft_named_variadic_param(&ft).and_then(|fp| fp.name.clone()),
            Some("$kw".to_string())
        );
        assert_eq!(ft_params_without_named_variadic(&ft).len(), 1);
        let (arity, names) = arity_and_names_required(&ft);
        assert_eq!(arity, 1);
        assert!(names.is_empty());

        assert_eq!(
            get_param_mode(&ast_defs::ParamKind::Pinout(Pos::NONE)),
            ParamMode::FPinout
        );
        assert_eq!(
            get_param_mode(&ast_defs::ParamKind::Pnormal),
            ParamMode::FPnormal
        );
        type Arg = aast::Argument<(), ()>;
        let e = || aast::Expr((), Pos::NONE, aast::Expr_::Null);
        assert_eq!(named_params::name_of_arg(&Arg::Anormal(e())), None);
        assert_eq!(
            named_params::name_of_arg(&Arg::Anamed(ast_defs::Id(Pos::NONE, "x".into()), e())),
            Some("x".to_string())
        );
    }

    fn class_elt(visibility: CeVisibility, flags: ClassEltFlags) -> ClassElt {
        use ty::reason::Reason as _;
        ClassElt {
            ce_visibility: visibility,
            ce_type: crate::folded_class::lazy(|| DeclTy::mixed(R::none())),
            ce_origin: "\\C".to_string(),
            ce_deprecated: None,
            ce_pos: crate::folded_class::lazy(|| Pos::NONE),
            ce_flags: flags,
            ce_sealed_allowlist: None,
            ce_overlapping_tparams: None,
            ce_package_requirement: None,
        }
    }

    #[test]
    fn class_elts() {
        let flags = |lsb: bool, bypass: bool| {
            make_ce_flags(
                None, true, false, false, lsb, false, true, false, false, false, false, false,
                false, false, bypass,
            )
        };
        let private = || CeVisibility::Vprivate("\\C".to_string());
        let protected = || CeVisibility::Vprotected("\\C".to_string());
        let ce = class_elt(private(), flags(false, false));
        assert!(get_ce_abstract(&ce) && get_ce_const(&ce));
        assert!(!get_ce_final(&ce) && !get_ce_lsb(&ce) && !get_ce_synthesized(&ce));
        assert!(get_ce_xhp_attr(&ce).is_none());
        assert!(class_elt_is_private_not_lsb(&ce));
        assert!(class_elt_is_private_or_protected_not_lsb(&ce));
        let ce = class_elt(private(), flags(true, false));
        assert!(!class_elt_is_private_not_lsb(&ce));
        assert!(!class_elt_is_private_or_protected_not_lsb(&ce));
        let ce = class_elt(private(), flags(false, true));
        assert!(get_ce_tests_bypass_visibility(&ce));
        assert!(!class_elt_is_private_not_lsb(&ce));
        assert!(class_elt_is_private_or_protected_not_lsb(&ce));
        let ce = class_elt(protected(), flags(false, false));
        assert!(!class_elt_is_private_not_lsb(&ce));
        assert!(class_elt_is_private_or_protected_not_lsb(&ce));
        let ce = class_elt(CeVisibility::Vpublic, flags(false, false));
        assert!(!class_elt_is_private_not_lsb(&ce));
        assert!(!class_elt_is_private_or_protected_not_lsb(&ce));
        // the xhp attribute is encoded in the flags
        let xa = oxidized::xhp_attribute::XhpAttribute {
            tag: Some(oxidized::xhp_attribute::Tag::Required),
            has_default: true,
        };
        let f = make_ce_flags(
            Some(xa.clone()),
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
        );
        let ce = class_elt(CeVisibility::Vpublic, f);
        assert_eq!(get_ce_xhp_attr(&ce), Some(xa));
    }

    #[test]
    fn attributes_and_ccr() {
        let ua = |n: &str| UserAttribute {
            name: (Pos::NONE, n.to_string()),
            params: vec![],
            raw_val: None,
        };
        let uas = vec![ua("__A"), ua("__B")];
        assert!(attributes::mem("__B", &uas));
        assert!(!attributes::mem("__C", &uas));
        assert_eq!(
            attributes::find("__B", &uas).map(|ua| ua.name.1.as_str()),
            Some("__B")
        );
        assert!(attributes::find("__C", &uas).is_none());

        let self_ = |s: &str| ClassConstRef(ClassConstFrom::Self_, pos::Symbol::new(s));
        let from = |c: &str, s: &str| {
            ClassConstRef(
                ClassConstFrom::From(pos::TypeName::new(c)),
                pos::Symbol::new(s),
            )
        };
        assert_eq!(ccr::compare(&self_("B"), &from("A", "A")), Ordering::Less);
        assert_eq!(
            ccr::compare(&from("A", "B"), &from("A", "A")),
            Ordering::Greater
        );
        assert_eq!(
            ccr::compare(&from("A", "B"), &from("B", "A")),
            Ordering::Less
        );
        // the set is in the order of CCR.compare
        let set: ccr_set::T = [from("B", "A"), self_("Z"), from("A", "B"), from("A", "A")]
            .into_iter()
            .map(ccr_set::Elt)
            .collect();
        let elts: Vec<String> = set
            .iter()
            .map(|ccr_set::Elt(ClassConstRef(f, s))| match f {
                ClassConstFrom::Self_ => format!("self::{}", s),
                ClassConstFrom::From(c) => format!("{}::{}", c, s),
            })
            .collect();
        assert_eq!(elts, vec!["self::Z", "A::A", "A::B", "B::A"]);
        // user attributes of the hackrs declarations
        let ua = |n: &str| ty::decl::UserAttribute {
            name: pos::Positioned::new((), pos::TypeName::new(n)),
            params: Box::new([]),
            raw_val: None,
        };
        assert!(attributes::mem("__B", &[ua("__A"), ua("__B")]));
        assert!(!attributes::mem("__C", &[ua("__A"), ua("__B")]));
    }

    #[test]
    fn shape_field_maps() {
        use oxidized::typing_defs_core::PosByteString;
        let field = |s: &str| shape_field_map::Key {
            0: TshapeFieldName::TSFlitStr(PosByteString(Pos::NONE, s.into())),
        };
        let sft = |ty: Ty| ShapeFieldType { optional: true, ty };
        let mut m = shape_field_map::T::new();
        m.insert(field("b"), sft(prim(Tprim::Tint)));
        m.insert(field("a"), sft(prim(Tprim::Tfloat)));
        // in the order of the keys, the environment is threaded through
        let mut seen = Vec::new();
        let m = shape_field_map::map_env(
            |seen: &mut Vec<Ty>, ty| {
                seen.push(ty);
                generic("T")
            },
            &mut seen,
            m,
        );
        assert!(matches!(get_node(&seen[0]), Ty_::Tprim(Tprim::Tfloat)));
        assert!(matches!(get_node(&seen[1]), Ty_::Tprim(Tprim::Tint)));
        assert!(m.values().all(|sft| sft.optional && is_generic(&sft.ty)));
        let m = shape_field_map::map(|_| prim(Tprim::Tbool), m);
        let mut n = 0;
        shape_field_map::iter_values(
            |ty| {
                assert!(is_prim(Tprim::Tbool, ty));
                n += 1
            },
            &m,
        );
        assert_eq!(n, 2);
        // errors are given to combine_ty_errs in the reverse of the order of the keys
        let (errs, _) = shape_field_map::map_env_ty_err_opt(
            |n: &mut i32, ty| {
                *n += 1;
                (Some(*n), ty)
            },
            &mut 0,
            m.clone(),
            |errs| errs,
        );
        assert_eq!(errs, vec![2, 1]);
        // rekeying
        let m = shape_field_map::map_and_rekey(m, |_| field("z"), |ty| ty);
        assert_eq!(m.len(), 1);
        let xs =
            shape_field_list::map_env(&mut (), vec![sft(prim(Tprim::Tint))], |_: &mut (), _| {
                generic("T")
            });
        assert!(xs[0].optional && is_generic(&xs[0].ty));
    }

    #[test]
    fn misc() {
        assert_eq!(
            show_visibility_behavior(&VisibilityBehavior::ExpandVisibleNewtypeOnly),
            "Expand_visible_newtype_only"
        );
        assert_eq!(
            show_visibility_behavior(&VisibilityBehavior::ResolveTypeStructure(None)),
            "(Resolve_type_structure None)"
        );
        assert_eq!(
            show_visibility_behavior(&VisibilityBehavior::ResolveTypeStructure(Some(
                "\\N\\C".to_string()
            ))),
            "(Resolve_type_structure (Some \"\\\\N\\\\C\"))"
        );
        assert!(is_default_visibility_behaviour(
            &default_visibility_behaviour()
        ));
        assert!(!is_default_visibility_behaviour(
            &VisibilityBehavior::NeverExpandNewtype
        ));
        use ty::reason::Reason as _;
        let wildcard = DeclTy::new(crate::ctx::R::none(), ty::decl::Ty_::Twildcard);
        assert!(is_wildcard(&wildcard));
        assert!(!is_wildcard(&DeclTy::mixed(crate::ctx::R::none())));
    }
}
