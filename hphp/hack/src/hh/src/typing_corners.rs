// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_corners.ml`. See `hh/PORTING.md`.
//!
//! # Ground corner subrow procedure
//!
//! Type parameters in spread position are not collapsed to a single bound;
//! instead each type parameter that is 'live' at a given label (i.e. can
//! influence its type) is enumerated over the <=4 extremal 'corners' of its
//! field interval [lower, upper] at each label, and the per-field subtyping
//! obligation is checked at every corner co-assignment.
//!
//! # Representation
//!
//! - `Typing_shape_normalize.Row` is `crate::typing_shape_normalize::row`
//!   (`srow` here). Its eliminators `fold` and `fold_normalized` take one
//!   closure per case, and in the OCaml several of them thread the same
//!   environment, which Rust closures cannot share. Every use goes through
//!   [`row_view`] / [`normalized_view`], which fold the row into owned data
//!   (the elements already mapped by `element_tys`, as every use of
//!   `~elements` here does), and the cases are matched afterwards.
//! - `Splat_elem.Map` and `Splat_elem.Set` are keyed by [`splat_elem::Key`],
//!   a type ordered by `Splat_elem.compare`. The set is `Stdlib.Set.Make`
//!   itself (`typing_set::stdlib_set`), since which of two equal elements it
//!   keeps (they can differ by their reasons, hence by the positions shown in
//!   errors) depends on the shapes of its trees; the map is an `im::OrdMap`
//!   (its keys are never read back).
//! - `TShapeSet` is `BTreeSet<TShapeField>` in the crate; the label sets
//!   built here are `Stdlib.Set.Make (TShapeField)` ([`LabelSet`]) for the
//!   same reason (the position of a label is the `decl_pos` of
//!   `Missing_field`), and are turned into a `TShapeSet` only by
//!   [`subrow_label_set`].
//! - `Cache.t` (see [`cache`]): the OCaml reuses a memoised value only for
//!   the physically identical environment, and stores one only when the
//!   computation left the environment physically unchanged. A Rust `Env` is
//!   mutated in place and has no identity, so no entry could be shown valid:
//!   `memoize` and `memoize_value` recompute. A hit in the OCaml returns what
//!   the computation returns again in that environment, so only the cost
//!   (and dependencies recorded again, which are sets) differs.
//! - Labels (`TShapeField.t option`) are `Option<&TShapeField>`; rows are
//!   passed by reference (normalized rows by value, as
//!   `typing_shape_normalize::row` takes them); the reasons the public
//!   functions store are taken by value, as `typing_subtype` calls them.
//! - What recomputing instead of hitting the cache could change: a
//!   memoised computation that creates fresh type variables in an
//!   environment it then drops advances the shared `tvar_id_provider` again
//!   where the OCaml would have reused its value (a later fresh variable
//!   then gets another number). Whether one does depends on what localizing
//!   a declared bound (`get_newtype_super`, `get_concrete_supertypes`)
//!   creates; this is where the port can differ from the OCaml. Likewise, a
//!   hit returns the physically same value, where recomputing builds an
//!   equal but new one when the computation builds a type (`intersect_list`
//!   of several bounds, `mixed r`, a localized bound): a later `phys_equal`
//!   between two such results is true in the OCaml and false here. Within
//!   one corner the two sides read the same assignment, so their fields stay
//!   shared.
//! - Functions that drop the environment they compute in (`let (_env, x) =`,
//!   `ignore env`) take `&Env` and work on a clone.

use std::cmp::Ordering;
use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::pos_or_decl::PosOrDecl;

use crate::tvid;
use crate::typing_defs;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TShapeSet;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_pos;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_intersection;
use crate::typing_make_type as make_type;
use crate::typing_reason;
use crate::typing_reason::T as Reason;
use crate::typing_set;
use crate::typing_set::stdlib_set;
use crate::typing_shape_normalize;
/// `Typing_shape_normalize.Row`
use crate::typing_shape_normalize::row as srow;
use crate::typing_shape_splat_key;
use crate::typing_union;
use crate::typing_utils;

fn element_tys(elements: &[srow::element::T]) -> Vec<Ty> {
    elements.iter().map(srow::element::ty).collect()
}

/// The cases of `Typing_shape_normalize.Row.fold`, as owned data; the
/// elements are given by their types (`element_tys elements`).
enum RowView {
    Bottom,
    Simple(ShapeTypeSimple),
    Elements(Vec<Ty>),
}

fn row_view(row: &srow::T) -> RowView {
    srow::fold(
        row,
        || RowView::Bottom,
        |shape| RowView::Simple(shape.clone()),
        |elements| RowView::Elements(element_tys(&elements[..])),
    )
}

/// The cases of `Typing_shape_normalize.Row.fold_normalized`, as owned data.
enum NormalizedView {
    Row(srow::T),
    Union(Vec<Ty>),
    Intersection(Vec<Ty>),
}

fn normalized_view(normalized: srow::Normalized) -> NormalizedView {
    srow::fold_normalized(
        normalized,
        NormalizedView::Row,
        NormalizedView::Union,
        NormalizedView::Intersection,
    )
}

/// `Typing_shape_normalize.Row.normalize ~on_error:None r shape_ty env`,
/// without its error (every caller here drops it).
fn normalize_row(env: &mut Env, r: &Reason, shape_ty: ShapeType) -> srow::Normalized {
    let (_err, normalized) = srow::normalize(None, r.clone(), shape_ty, env);
    normalized
}

/// `Naming_special_names.Classes.cSupportDyn`
fn is_supportdyn_name(n: &str) -> bool {
    n == sn::classes::SUPPORT_DYN
}

/// The key identifying a spread element. Two occurrences of the same parameter
/// are the same key, so it is compared by type rather than by name: [NT<int>] and
/// [NT<string>] are different elements.
pub mod splat_elem {
    use super::*;

    /// A localized generic or newtype used as a spread element key.
    pub type T = Ty;

    /// Compare spread elements by normalized type identity and opacity.
    pub fn compare(ty1: &Ty, ty2: &Ty) -> Ordering {
        let same_opacity = match (get_node(ty1), get_node(ty2)) {
            (Ty_::Tnewtype(..), Ty_::Tnewtype(..)) => {
                typing_reason::predicates::is_opaque_type_from_module(get_reason(ty1))
                    == typing_reason::predicates::is_opaque_type_from_module(get_reason(ty2))
            }
            _ => true,
        };
        // `phys_equal (get_node ty1) (get_node ty2)`
        if Rc::ptr_eq(&ty1.1, &ty2.1) && same_opacity {
            Ordering::Equal
        } else {
            typing_shape_splat_key::compare(
                &typing_shape_splat_key::of_ty(ty1),
                &typing_shape_splat_key::of_ty(ty2),
            )
        }
    }

    /// A spread element as the key of [`map`] and [`set`]: ordered by
    /// [`compare`].
    #[derive(Clone, Debug)]
    pub struct Key(pub Ty);

    impl PartialEq for Key {
        fn eq(&self, other: &Self) -> bool {
            compare(&self.0, &other.0) == Ordering::Equal
        }
    }

    impl Eq for Key {}

    impl PartialOrd for Key {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for Key {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(&self.0, &other.0)
        }
    }

    impl stdlib_set::OrderedType for Key {
        fn compare(a: &Self, b: &Self) -> Ordering {
            compare(&a.0, &b.0)
        }
    }

    /// Maps keyed by spread element (`Stdlib.Map.Make`; the functions
    /// used here).
    pub mod map {
        use super::*;

        pub type T<V> = im::OrdMap<Key, V>;

        pub fn empty<V: Clone>() -> T<V> {
            im::OrdMap::new()
        }

        pub fn add<V: Clone>(key: Ty, v: V, m: &T<V>) -> T<V> {
            m.update(Key(key), v)
        }

        pub fn find_opt<'a, V: Clone>(key: &Ty, m: &'a T<V>) -> Option<&'a V> {
            m.get(&Key(key.clone()))
        }

        pub fn mem<V: Clone>(key: &Ty, m: &T<V>) -> bool {
            m.contains_key(&Key(key.clone()))
        }
    }

    /// Sets of spread elements (`Stdlib.Set.Make`, tree for tree; the
    /// functions used here and by `typing_subtype`).
    pub mod set {
        use super::*;

        #[derive(Clone, Default)]
        pub struct T(stdlib_set::Set<Key>);

        impl std::fmt::Debug for T {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_set().entries(self.0.iter().map(|k| &k.0)).finish()
            }
        }

        pub fn empty() -> T {
            T(stdlib_set::empty())
        }

        pub fn is_empty(s: &T) -> bool {
            stdlib_set::is_empty(&s.0)
        }

        pub fn mem(x: &Ty, s: &T) -> bool {
            stdlib_set::mem(&Key(x.clone()), &s.0)
        }

        pub fn add(x: Ty, s: &T) -> T {
            T(stdlib_set::add(Key(x), &s.0))
        }

        pub fn singleton(x: Ty) -> T {
            T(stdlib_set::singleton(Key(x)))
        }

        pub fn remove(x: &Ty, s: &T) -> T {
            T(stdlib_set::remove(&Key(x.clone()), &s.0))
        }

        pub fn union(s1: &T, s2: &T) -> T {
            T(stdlib_set::union(&s1.0, &s2.0))
        }

        pub fn of_list(l: Vec<Ty>) -> T {
            T(stdlib_set::of_list(l.into_iter().map(Key).collect()))
        }

        /// In increasing order.
        pub fn elements(s: &T) -> Vec<Ty> {
            s.0.iter().map(|k| k.0.clone()).collect()
        }

        pub fn fold<B>(mut f: impl FnMut(&Ty, B) -> B, s: &T, accu: B) -> B {
            stdlib_set::fold(|k: &Key, b| f(&k.0, b), &s.0, accu)
        }

        pub fn iter(mut f: impl FnMut(&Ty), s: &T) {
            stdlib_set::iter(|k: &Key| f(&k.0), &s.0)
        }

        pub fn for_all(mut p: impl FnMut(&Ty) -> bool, s: &T) -> bool {
            stdlib_set::for_all(|k: &Key| p(&k.0), &s.0)
        }

        pub fn exists(mut p: impl FnMut(&Ty) -> bool, s: &T) -> bool {
            stdlib_set::exists(|k: &Key| p(&k.0), &s.0)
        }

        pub fn cardinal(s: &T) -> isize {
            stdlib_set::cardinal(&s.0)
        }

        /// `choose` (`min_elt` in `set.ml`); raises `Not_found` on the empty
        /// set.
        pub fn choose(s: &T) -> Ty {
            match stdlib_set::choose_opt(&s.0) {
                Some(k) => k.0,
                None => panic!("Not_found"),
            }
        }
    }
}

/// A single assignment of all type parameters to a ground shape field type
pub mod assignment {
    use super::*;

    /// A per-label assignment of each live spread element to a corner field.
    pub type T = splat_elem::map::T<ShapeFieldType>;
}

/// Memoized, assignment-independent inputs to one splat operation. Field
/// bounds themselves are not cached because their projections depend on the
/// current corner assignment.
///
/// `type 'a entry = { input_env: env; value: 'a }`: an entry is valid for
/// the environment, compared by physical identity, in which it was computed.
/// That identity does not exist for a Rust `Env` (see the module
/// documentation), so a table holds no entries and [`memoize`] and
/// [`memoize_value`] compute their value every time, which is what the OCaml
/// returns on a hit.
pub mod cache {
    use std::marker::PhantomData;

    use super::*;

    /// One table of `'a entry Splat_elem.Map.t ref`.
    pub struct Table<A>(PhantomData<A>);

    impl<A> Table<A> {
        fn new() -> Self {
            Table(PhantomData)
        }
    }

    /// Bound resolutions shared within one shape-splat operation.
    pub struct T {
        pub(super) upper_bounds: Table<Ty>,
        pub(super) lower_bounds: Table<Ty>,
        pub(super) concrete_supers: Table<Vec<Ty>>,
        pub(super) concrete_subs: Table<Vec<Ty>>,
        pub(super) dependencies: Table<Vec<Ty>>,
    }

    /// Create a fresh cache for one splat operation.
    pub fn create() -> T {
        T {
            upper_bounds: Table::new(),
            lower_bounds: Table::new(),
            concrete_supers: Table::new(),
            concrete_subs: Table::new(),
            dependencies: Table::new(),
        }
    }

    /// Memoize an environment-threading computation only when it returns the
    /// physically identical environment. Reusing a value that changed the
    /// environment could couple otherwise independent branches.
    ///
    /// (Here: the computation, every time; see [`cache`](self).)
    pub fn memoize<A>(
        _cache: &mut Table<A>,
        env: &mut Env,
        _key: &splat_elem::T,
        f: impl FnOnce(&mut Env) -> A,
    ) -> A {
        f(env)
    }

    /// Memoize an environment-indexed value that does not thread environment
    /// changes.
    ///
    /// (Here: the computation, every time; see [`cache`](self).)
    pub fn memoize_value<A>(
        _cache: &mut Table<A>,
        _env: &Env,
        _key: &splat_elem::T,
        f: impl FnOnce() -> A,
    ) -> A {
        f()
    }
}

/// Shape-field predicates and row-algebra operations.
pub mod field {
    use super::*;

    /// A required or optional localized shape field.
    pub type T = ShapeFieldType;

    /// Whether the field must be present.
    pub fn is_required(field: &T) -> bool {
        !field.optional
    }

    /// Whether the field may be absent.
    pub fn is_optional(field: &T) -> bool {
        field.optional
    }

    /// An optional field of [nothing] must be absent.
    pub fn is_absent(field: &T, env: &Env) -> bool {
        field.optional && typing_utils::is_nothing(env, &field.ty)
    }

    /// A subtype field must be at least as required as the supertype field.
    pub fn requiredness_lte(sub: &T, super_: &T) -> bool {
        (!sub.optional) || super_.optional
    }

    /// Rightmost-wins field merge.
    pub fn merge(left: T, right: T, env: &mut Env) -> T {
        typing_shape_normalize::merge_field_descs(left, right, env)
    }

    /// Greatest lower bound of two fields.
    pub fn meet(left: T, right: T, env: &mut Env) -> T {
        let sft_ty = typing_intersection::intersect(
            env,
            get_reason(&left.ty).clone(),
            left.ty.clone(),
            right.ty.clone(),
        );
        ShapeFieldType {
            optional: left.optional && right.optional,
            ty: sft_ty,
        }
    }

    /// Least upper bound of two fields.
    pub fn join(left: T, right: T, env: &mut Env) -> T {
        let sft_ty = typing_union::union(env, None, None, left.ty.clone(), right.ty.clone());
        ShapeFieldType {
            optional: left.optional || right.optional,
            ty: sft_ty,
        }
    }

    /// Extremal field values induced by lower and upper bounds.
    pub mod corners {
        use super::*;

        /// The field descriptor enumerated at each corner.
        pub type Field = super::T;

        /// The reachable corner fields, or an uninhabited inverted interval.
        #[derive(Clone, Debug)]
        pub enum T {
            Values(Vec<Field>),
            Inverted,
        }

        /// An inverted bound pair is uninhabited and contributes no obligations.
        pub fn of_bounds(lower: Field, upper: Field) -> T {
            match (lower.optional, upper.optional) {
                (false, true) => {
                    let lower_opt = ShapeFieldType {
                        optional: true,
                        ..lower.clone()
                    };
                    let upper_req = ShapeFieldType {
                        optional: false,
                        ..upper.clone()
                    };
                    T::Values(vec![lower, upper, lower_opt, upper_req])
                }
                (false, false) | (true, true) => T::Values(vec![lower, upper]),
                (true, false) => T::Inverted,
            }
        }
    }
}

// -- Projection ------------------------------------------------------------

/// `TShapeSet.t` as `Stdlib.Set.Make (TShapeField)` builds it (see the
/// module documentation).
#[derive(Clone, Debug)]
struct Label(TShapeField);

impl stdlib_set::OrderedType for Label {
    fn compare(a: &Self, b: &Self) -> Ordering {
        a.0.cmp(&b.0)
    }
}

type LabelSet = stdlib_set::Set<Label>;

mod row {
    use super::*;

    fn proj_simple(
        s_fields: &TShapeMap<ShapeFieldType>,
        s_unknown_value: &Ty,
        label: Option<&TShapeField>,
    ) -> ShapeFieldType {
        match label.and_then(|l| s_fields.get(l)) {
            Some(fd) => fd.clone(),
            None => ShapeFieldType {
                optional: true,
                ty: s_unknown_value.clone(),
            },
        }
    }

    fn proj_element(
        _env: &mut Env,
        ty: &Ty,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
    ) -> ShapeFieldType {
        let r = get_reason(ty);
        match get_node(ty) {
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                match splat_elem::map::find_opt(ty, assignment) {
                    Some(fd) => fd.clone(),
                    None => {
                        // Unreachable: Every live generic must have a corner value before row
                        // projection. Missing here indicates a traversal/dependency bug.
                        ShapeFieldType {
                            optional: true,
                            ty: make_type::nothing(r.clone()),
                        }
                    }
                }
            }
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            })) => proj_simple(s_fields, s_unknown_value, label),
            _ if typing_defs::is_nothing(ty) => ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            },
            _ => ShapeFieldType {
                optional: true,
                ty: make_type::nothing(r.clone()),
            },
        }
    }

    /// Right-to-left rightmost-wins fold over splat elements, short-circuiting once
    /// the accumulated field is required.
    fn proj_splat_help(
        env: &mut Env,
        rev_left: &[Ty],
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        fd_right: ShapeFieldType,
    ) -> ShapeFieldType {
        if !fd_right.optional {
            fd_right
        } else {
            match rev_left {
                [] => fd_right,
                [elem, rest @ ..] => {
                    let fd_left = proj_element(env, elem, label, assignment);
                    let fd = field::merge(fd_left, fd_right, env);
                    proj_splat_help(env, rest, label, assignment, fd)
                }
            }
        }
    }

    fn proj_splat(
        env: &mut Env,
        ss_elems: &[Ty],
        label: Option<&TShapeField>,
        assignment: &assignment::T,
    ) -> ShapeFieldType {
        let rev: Vec<Ty> = ss_elems.iter().rev().cloned().collect();
        match &rev[..] {
            [] => {
                // An empty splat is the identity, i.e. the empty closed shape. Every label
                // projects to absent (Opt nothing)
                ShapeFieldType {
                    optional: true,
                    ty: make_type::nothing(typing_reason::none()),
                }
            }
            [rightmost, rev_left @ ..] => {
                let fd = proj_element(env, rightmost, label, assignment);
                proj_splat_help(env, rev_left, label, assignment, fd)
            }
        }
    }

    /// Project a normalized splat row at a label under an [Assignment.t] of
    /// all type parameters contributing to the type.
    pub fn proj(
        env: &mut Env,
        row: &srow::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
    ) -> ShapeFieldType {
        match row_view(row) {
            RowView::Bottom => ShapeFieldType {
                optional: false,
                ty: make_type::nothing(typing_reason::none()),
            },
            RowView::Simple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            }) => proj_simple(&s_fields, &s_unknown_value, label),
            RowView::Elements(ss_elems) => proj_splat(env, &ss_elems, label, assignment),
        }
    }

    // -- Live parameters -----------------------------------------------------

    /// Type parameters to the right of any [Req] field at [label]: only these can
    /// contribute to the merged field.
    fn live_spreads_at(ss_elems: &[Ty], label: Option<&TShapeField>) -> Vec<Ty> {
        // `aux (List.rev ss_elems) []`: `acc` is consed onto, so it is built
        // here in reverse and turned around at the end.
        let mut rev_acc: Vec<Ty> = vec![];
        for ty in ss_elems.iter().rev() {
            match get_node(ty) {
                Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => rev_acc.push(ty.clone()),
                _ if typing_defs::is_nothing(ty) => {
                    // bottom row: forces [Req bottom]; everything to its left is masked
                    break;
                }
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    fields: s_fields,
                    unknown_value: s_unknown_value,
                    ..
                })) => {
                    let fd = proj_simple(s_fields, s_unknown_value, label);
                    if fd.optional {
                        continue;
                    } else {
                        break;
                    }
                }
                _ => {}
            }
        }
        rev_acc.reverse();
        rev_acc
    }

    /// Type parameters to the right of any required field at [label]: only these
    /// can contribute to the merged field.
    pub fn live_spreads(row: &srow::T, label: Option<&TShapeField>) -> Vec<Ty> {
        match row_view(row) {
            RowView::Bottom => vec![],
            RowView::Simple(_) => vec![],
            RowView::Elements(ss_elems) => live_spreads_at(&ss_elems, label),
        }
    }

    // -- Labels --------------------------------------------------------------

    /// Inline labels a row contributes, looking through inline shape spreads.
    /// Opaque splat elements contribute none.
    fn label_set_shape(row: &ShapeType) -> LabelSet {
        match row {
            ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: s_fields, ..
            }) => {
                let mut acc = stdlib_set::empty();
                for k in s_fields.keys() {
                    acc = stdlib_set::add(Label(k.clone()), &acc);
                }
                acc
            }
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                let mut acc = stdlib_set::empty();
                for ty in ss_elems {
                    acc = stdlib_set::union(&acc, &element_label_set(ty));
                }
                acc
            }
        }
    }

    fn element_label_set(ty: &Ty) -> LabelSet {
        match get_node(ty) {
            Ty_::Tshape(shape_ty) => label_set_shape(shape_ty),
            _ => stdlib_set::empty(),
        }
    }

    /// Set of all known field labels in a normalized row
    pub fn label_set(row: &srow::T) -> LabelSet {
        match row_view(row) {
            RowView::Bottom => stdlib_set::empty(),
            RowView::Simple(shape) => label_set_shape(&ShapeType::ShapeSimple(shape)),
            RowView::Elements(tys) => {
                let mut labels = stdlib_set::empty();
                for ty in tys.iter() {
                    labels = stdlib_set::union(&labels, &element_label_set(ty));
                }
                labels
            }
        }
    }

    /// Type parameters and newtypes in spread position in the normalized row.
    pub fn spread_elements(row: &srow::T) -> Vec<Ty> {
        match row_view(row) {
            RowView::Bottom => vec![],
            RowView::Simple(_) => vec![],
            RowView::Elements(tys) => tys
                .into_iter()
                .filter(|ty| matches!(get_node(ty), Ty_::Tgeneric(_) | Ty_::Tnewtype(..)))
                .collect(),
        }
    }
}

// -- Field bounds of an opaque spread element ------------------------------

mod bounds {
    use super::*;

    pub fn combined_upper_bound(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Ty {
        cache::memoize(&mut cache.upper_bounds, env, key, |env| {
            match get_node(key) {
                Ty_::Tnewtype(name, targs, _) => {
                    // A newtype's bounds are on the typedef rather than in the type
                    // parameter environment: what it is declared [as].
                    typing_utils::get_newtype_super(env, get_reason(key).clone(), name, targs)
                }
                Ty_::Tgeneric(name) => {
                    let bounds = typing_env::get_upper_bounds(env, name);
                    if typing_set::is_empty(&bounds) {
                        make_type::mixed(r.clone())
                    } else {
                        // Every upper bound holds, so the tightest is their intersection.
                        typing_intersection::intersect_list(
                            env,
                            r.clone(),
                            &typing_set::elements(&bounds),
                        )
                    }
                }
                _ => make_type::mixed(r.clone()),
            }
        })
    }

    fn combined_lower_bound(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Ty {
        cache::memoize(&mut cache.lower_bounds, env, key, |env| {
            match get_node(key) {
                Ty_::Tnewtype(name, targs, _) => {
                    let lower = typing_utils::get_newtype_sub_opt(env, name, targs);
                    lower.unwrap_or_else(|| make_type::nothing(r.clone()))
                }
                Ty_::Tgeneric(name) => {
                    let bounds = typing_env::get_lower_bounds(env, name);
                    if typing_set::is_empty(&bounds) {
                        make_type::nothing(r.clone())
                    } else {
                        // Each lower bound is below the element, so their union is too.
                        typing_union::union_list(
                            env,
                            None,
                            r.clone(),
                            &typing_set::elements(&bounds),
                        )
                    }
                }
                _ => make_type::nothing(r.clone()),
            }
        })
    }

    pub fn concrete_supertypes(cache: &mut cache::T, env: &mut Env, ty: &Ty) -> Vec<Ty> {
        cache::memoize(&mut cache.concrete_supers, env, ty, |env| {
            typing_utils::get_concrete_supertypes(None, None, None, false, env, ty.clone())
        })
    }

    fn concrete_subtypes(cache: &mut cache::T, env: &mut Env, ty: &Ty) -> Vec<Ty> {
        cache::memoize(&mut cache.concrete_subs, env, ty, |env| {
            typing_utils::get_concrete_subtypes(env, ty.clone())
        })
    }

    pub fn strip_supportdyn(env: &mut Env, ty: Ty) -> Ty {
        let (_supportdyn, ty) = typing_utils::strip_supportdyn(env, ty);
        ty
    }

    fn shape_types(env: &mut Env, tys: &[Ty]) -> Vec<ShapeType> {
        let shapes: Vec<Option<ShapeType>> = tys
            .iter()
            .map(|ty| {
                let ty = strip_supportdyn(env, ty.clone());
                match get_node(&ty) {
                    Ty_::Tshape(shape_ty) => Some(shape_ty.clone()),
                    _ => None,
                }
            })
            .collect();
        shapes.into_iter().flatten().collect()
    }

    pub mod upper {
        use super::*;

        pub enum T {
            /// All the rows the bound resolves to. The element is below every one of
            /// them, so its field is below each of their fields: combine by meet. A
            /// bound can resolve to several, an intersection being the obvious case,
            /// and keeping only one silently drops what the others say.
            Shapes(Vec<srow::T>),
            /// The bottom row: every field present, at the uninhabited type.
            Bottom,
            /// Not a shape, so it rules nothing out.
            Unconstrained,
        }
    }

    pub mod lower {
        use super::*;

        pub enum T {
            /// Likewise, but the element is ABOVE every one of them, so combine by
            /// join.
            Shapes(Vec<srow::T>),
            Bottom,
        }
    }

    /// Reading a row that is already known to be a shape, in each direction's own
    /// answer type.
    fn normalized_upper(env: &mut Env, r: &Reason, shape_ty: ShapeType) -> upper::T {
        let normalized = normalize_row(env, r, shape_ty);
        match srow::as_row(normalized) {
            Some(row) if srow::is_bottom(&row) => upper::T::Bottom,
            Some(row) => upper::T::Shapes(vec![row]),
            None => {
                // A distributed result is not one row. Ordinary subtyping retains its
                // connective; bound projection falls back conservatively.
                upper::T::Unconstrained
            }
        }
    }

    fn normalized_lower(env: &mut Env, r: &Reason, shape_ty: ShapeType) -> lower::T {
        let normalized = normalize_row(env, r, shape_ty);
        match srow::as_row(normalized) {
            Some(row) if srow::is_bottom(&row) => lower::T::Bottom,
            Some(row) => lower::T::Shapes(vec![row]),
            None => lower::T::Bottom,
        }
    }

    /// Spreading [dynamic] is an open row whose unknown fields are [dynamic]
    /// ([shape(_ => dynamic)]), matching [Typing_shape_normalize].
    fn dynamic_row(r: &Reason) -> srow::T {
        srow::of_simple(ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: make_type::dynamic(r.clone()),
            fields: TShapeMap::new(),
        })
    }

    pub fn bound_shape_upper(
        cache: &mut cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        assignment: &assignment::T,
        r: &Reason,
    ) -> upper::T {
        let bound_ty = combined_upper_bound(cache, env, name, r);
        let bound_ty = typing_env::expand_type(env, bound_ty);
        let bound_ty = strip_supportdyn(env, bound_ty);
        let is_assigned_param = || {
            splat_elem::map::mem(&bound_ty, assignment)
                && match get_node(&bound_ty) {
                    Ty_::Tnewtype(n, _, _) => !is_supportdyn_name(n),
                    _ => true,
                }
        };
        match get_node(&bound_ty) {
            Ty_::Tshape(shape_ty) => normalized_upper(env, r, shape_ty.clone()),
            Ty_::Tdynamic(_) => upper::T::Shapes(vec![dynamic_row(r)]),
            _ if typing_defs::is_nothing(&bound_ty) => upper::T::Bottom,
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) if is_assigned_param() => normalized_upper(
                env,
                r,
                ShapeType::ShapeSplat(ShapeTypeSplat {
                    ss_elems: vec![bound_ty.clone()],
                }),
            ),
            _ => {
                let supers = concrete_supertypes(cache, env, &bound_ty);
                let shapes = shape_types(env, &supers);
                if shapes.is_empty() {
                    upper::T::Unconstrained
                } else {
                    let normalized: Vec<Option<srow::T>> = shapes
                        .into_iter()
                        .map(|shape_ty| match normalized_upper(env, r, shape_ty) {
                            upper::T::Shapes(mut rows) if rows.len() == 1 => rows.pop(),
                            _ => None,
                        })
                        .collect();
                    let shapes: Vec<srow::T> = normalized.into_iter().flatten().collect();
                    if shapes.is_empty() {
                        upper::T::Bottom
                    } else {
                        upper::T::Shapes(shapes)
                    }
                }
            }
        }
    }

    pub fn bound_shape_lower(
        cache: &mut cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        assignment: &assignment::T,
        r: &Reason,
    ) -> lower::T {
        let bound_ty = combined_lower_bound(cache, env, name, r);
        let bound_ty = typing_env::expand_type(env, bound_ty);
        let bound_ty = strip_supportdyn(env, bound_ty);
        match get_node(&bound_ty) {
            Ty_::Tshape(shape_ty) => normalized_lower(env, r, shape_ty.clone()),
            Ty_::Tdynamic(_) => lower::T::Shapes(vec![dynamic_row(r)]),
            _ if typing_defs::is_nothing(&bound_ty) => lower::T::Bottom,
            // A lower bound that is a parameter, where that parameter ALREADY has a
            // value. Then it is not an approximation at all: this element is at least
            // whatever that one turned out to be, so use it.
            //
            // Unlike the upper case this creates no ordering requirement, and
            // [type_params_in_lower_bound] deliberately reports no dependency for it. An
            // edge here would make the relation symmetric and turn a single constraint
            // into a cycle. Taking the value only when it happens to be there keeps the
            // coupling without the edge, which is what [where T1 = T2] needs: the two
            // parameters constrain each other in both directions, and with only the upper
            // half enforced one could be given a value below the other.
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..)
                if splat_elem::map::mem(&bound_ty, assignment)
                    && match get_node(&bound_ty) {
                        Ty_::Tnewtype(n, _, _) => !is_supportdyn_name(n),
                        _ => true,
                    } =>
            {
                normalized_lower(
                    env,
                    r,
                    ShapeType::ShapeSplat(ShapeTypeSplat {
                        ss_elems: vec![bound_ty.clone()],
                    }),
                )
            }
            _ => {
                let subs = concrete_subtypes(cache, env, &bound_ty);
                let shapes = shape_types(env, &subs);
                if shapes.is_empty() {
                    lower::T::Bottom
                } else {
                    let normalized: Vec<Option<srow::T>> = shapes
                        .into_iter()
                        .map(|shape_ty| match normalized_lower(env, r, shape_ty) {
                            lower::T::Shapes(mut rows) if rows.len() == 1 => rows.pop(),
                            _ => None,
                        })
                        .collect();
                    let shapes: Vec<srow::T> = normalized.into_iter().flatten().collect();
                    if shapes.is_empty() {
                        lower::T::Bottom
                    } else {
                        lower::T::Shapes(shapes)
                    }
                }
            }
        }
    }

    fn proj_upper_bound(
        cache: &mut cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> ShapeFieldType {
        let view = bound_shape_upper(cache, env, name, assignment, r);
        match view {
            upper::T::Shapes(shapes) => match &shapes[..] {
                [] => ShapeFieldType {
                    optional: true,
                    ty: make_type::mixed(r.clone()),
                },
                [first, rest @ ..] => {
                    let mut acc = row::proj(env, first, label, assignment);
                    for shape_ty in rest {
                        let fd = row::proj(env, shape_ty, label, assignment);
                        acc = field::meet(acc, fd, env);
                    }
                    acc
                }
            },
            upper::T::Bottom => ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            },
            // A non-shape upper bound constrains nothing: the label may be absent and
            // its type may be anything.
            upper::T::Unconstrained => ShapeFieldType {
                optional: true,
                ty: make_type::mixed(r.clone()),
            },
        }
    }

    fn proj_lower_bound(
        cache: &mut cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> ShapeFieldType {
        let view = bound_shape_lower(cache, env, name, assignment, r);
        match view {
            lower::T::Shapes(shapes) => match &shapes[..] {
                [] => ShapeFieldType {
                    optional: false,
                    ty: make_type::nothing(r.clone()),
                },
                [first, rest @ ..] => {
                    let mut acc = row::proj(env, first, label, assignment);
                    for shape_ty in rest {
                        let fd = row::proj(env, shape_ty, label, assignment);
                        acc = field::join(acc, fd, env);
                    }
                    acc
                }
            },
            lower::T::Bottom => ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            },
        }
    }

    /// `(env, lower, upper)`: the lower bound is projected first.
    pub fn field_bounds(
        cache: &mut cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> (ShapeFieldType, ShapeFieldType) {
        let lower = proj_lower_bound(cache, env, name, label, assignment, r);
        let upper = proj_upper_bound(cache, env, name, label, assignment, r);
        (lower, upper)
    }
}

// -- Dependency graph over spread elements --------------------------------

mod dependency_graph {
    use super::*;

    pub mod dependency {
        use super::*;

        /// How evaluating a bound reaches another spread element.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Kind {
            DirectUpper,
            IndirectUpper,
            NestedUpper,
            NestedLower,
        }

        #[derive(Clone, Debug)]
        pub struct T {
            pub(in super::super) source: splat_elem::T,
            pub(in super::super) target: splat_elem::T,
            pub(in super::super) kind: Kind,
            pub(in super::super) position: PosOrDecl,
        }

        pub fn make(source: splat_elem::T, target: splat_elem::T, kind: Kind) -> T {
            let position = get_pos(&target);
            T {
                source,
                target,
                kind,
                position,
            }
        }

        pub fn source(dependency: &T) -> splat_elem::T {
            dependency.source.clone()
        }

        pub fn target(dependency: &T) -> splat_elem::T {
            dependency.target.clone()
        }

        pub fn kind(dependency: &T) -> Kind {
            dependency.kind
        }

        pub fn position(dependency: &T) -> PosOrDecl {
            dependency.position.clone()
        }
    }

    pub mod cycle_info {
        use super::*;

        #[derive(Clone, Debug)]
        pub struct T {
            members: splat_elem::set::T,
            dependencies: Vec<dependency::T>,
        }

        pub fn make(members: splat_elem::set::T, dependencies: Vec<dependency::T>) -> T {
            T {
                members,
                dependencies,
            }
        }

        pub fn members(info: &T) -> splat_elem::set::T {
            info.members.clone()
        }

        pub fn dependencies(info: &T) -> Vec<dependency::T> {
            info.dependencies.clone()
        }
    }

    pub mod component {
        use super::*;

        /// One strongly connected component. Only direct reciprocal type-parameter
        /// constraints prove equality; every other cyclic component is unsupported.
        #[derive(Clone, Debug)]
        pub enum T {
            Acyclic(splat_elem::T),
            ProvenEqual(cycle_info::T),
            UnsupportedCycle(cycle_info::T),
        }

        pub fn members(c: &T) -> splat_elem::set::T {
            match c {
                T::Acyclic(member) => splat_elem::set::singleton(member.clone()),
                T::ProvenEqual(info) | T::UnsupportedCycle(info) => cycle_info::members(info),
            }
        }
    }

    pub mod analysis {
        use super::*;

        #[derive(Clone, Debug)]
        pub struct T {
            pub(in super::super) components: Vec<component::T>,
            pub(in super::super) dependencies: Vec<dependency::T>,
            pub(in super::super) node_visits: isize,
            pub(in super::super) edge_visits: isize,
        }

        /// Strongly connected components in dependency order.
        pub fn components(analysis: &T) -> Vec<component::T> {
            analysis.components.clone()
        }

        pub fn dependencies(analysis: &T) -> Vec<dependency::T> {
            analysis.dependencies.clone()
        }

        /// Tarjan visits each reachable node and classified edge exactly once.
        pub fn node_visits(analysis: &T) -> isize {
            analysis.node_visits
        }

        pub fn edge_visits(analysis: &T) -> isize {
            analysis.edge_visits
        }
    }

    pub fn type_params_in_upper_bound(
        cache: &mut cache::T,
        env: &Env,
        name: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        // The environment is threaded through, and dropped at the end.
        let env = &mut env.clone();
        let bound_ty = bounds::combined_upper_bound(cache, env, name, r);
        let bound_ty = typing_env::expand_type(env, bound_ty);
        let bound_ty = bounds::strip_supportdyn(env, bound_ty);
        fn spread_elements_of_ty(env: &mut Env, r: &Reason, ty: &Ty) -> Vec<Ty> {
            let ty = bounds::strip_supportdyn(env, ty.clone());
            match get_node(&ty) {
                Ty_::Tgeneric(_) => vec![ty.clone()],
                Ty_::Tnewtype(n, _, _) if !is_supportdyn_name(n) => vec![ty.clone()],
                Ty_::Tshape(shape_ty) => {
                    let normalized = normalize_row(env, r, shape_ty.clone());
                    match normalized_view(normalized) {
                        NormalizedView::Row(row) => row::spread_elements(&row),
                        NormalizedView::Union(tys) => spread_elements_of_tys(env, r, &tys),
                        NormalizedView::Intersection(tys) => spread_elements_of_tys(env, r, &tys),
                    }
                }
                Ty_::Tunion(tys) | Ty_::Tintersection(tys) => spread_elements_of_tys(env, r, tys),
                _ => vec![],
            }
        }
        fn spread_elements_of_tys(env: &mut Env, r: &Reason, tys: &[Ty]) -> Vec<Ty> {
            let elements: Vec<Vec<Ty>> = tys
                .iter()
                .map(|ty| spread_elements_of_ty(env, r, ty))
                .collect();
            elements.concat()
        }
        match get_node(&bound_ty) {
            // A bound that IS a parameter: the upper view projects [shape(...T)].
            Ty_::Tgeneric(_) => vec![bound_ty.clone()],
            Ty_::Tnewtype(n, _, _) if !is_supportdyn_name(n) => vec![bound_ty.clone()],
            _ => {
                // Every shape the bound can resolve to, not only the one the view happens
                //       to pick. An intersection offers several, and a parameter spread into one
                //       that is not picked would otherwise never be found, leaving it unordered.
                //    Reporting one that turns out not to be read only adds an ordering
                //    constraint that was not needed.
                let supers = bounds::concrete_supertypes(cache, env, &bound_ty);
                spread_elements_of_tys(env, r, &supers)
            }
        }
    }

    pub fn type_params_in_lower_bound(
        cache: &mut cache::T,
        env: &Env,
        name: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        // `ignore env`
        let view = bounds::bound_shape_lower(
            cache,
            &mut env.clone(),
            name,
            &splat_elem::map::empty(),
            r,
        );
        match view {
            bounds::lower::T::Shapes(shapes) => shapes.iter().flat_map(row::spread_elements).collect(),
            bounds::lower::T::Bottom => vec![],
        }
    }

    pub fn type_params_in_bounds(
        cache: &mut cache::T,
        env: &Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        // `Cache.memoize_value cache.Cache.dependencies env key (fun () -> ...)`:
        // the table and the computation both need the cache.
        let up = type_params_in_upper_bound(cache, env, key, r);
        let lo = type_params_in_lower_bound(cache, env, key, r);
        cache::memoize_value(&mut cache.dependencies, env, key, || {
            splat_elem::set::elements(&splat_elem::set::union(
                &splat_elem::set::of_list(up),
                &splat_elem::set::of_list(lo),
            ))
        })
    }

    pub fn closure(
        cache: &mut cache::T,
        env: &Env,
        names: &splat_elem::set::T,
        r: &Reason,
    ) -> splat_elem::set::T {
        // `aux worklist acc`: the head of the worklist is the last element.
        let mut worklist: Vec<Ty> = splat_elem::set::elements(names);
        worklist.reverse();
        let mut acc = splat_elem::set::empty();
        while let Some(next) = worklist.pop() {
            if splat_elem::set::mem(&next, &acc) {
                continue;
            }
            let delta = type_params_in_bounds(cache, env, &next, r);
            // `delta @ rest`
            worklist.extend(delta.into_iter().rev());
            acc = splat_elem::set::add(next, &acc);
        }
        acc
    }

    fn upper_bounds(
        cache: &mut cache::T,
        env: &mut Env,
        source: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        // Combining upper bounds into an intersection would erase which generic
        // references were direct constraints, which is needed to prove equality.
        match get_node(source) {
            Ty_::Tgeneric(name) => {
                let bounds = typing_env::get_upper_bounds(env, name);
                if typing_set::is_empty(&bounds) {
                    vec![]
                } else {
                    typing_set::elements(&bounds)
                }
            }
            Ty_::Tnewtype(..) => {
                let bound = bounds::combined_upper_bound(cache, env, source, r);
                vec![bound]
            }
            _ => vec![],
        }
    }

    fn classified_upper_dependencies(
        cache: &mut cache::T,
        env: &Env,
        source: &splat_elem::T,
        r: &Reason,
    ) -> Vec<(Ty, dependency::Kind)> {
        fn indirect_dependencies(
            env: &mut Env,
            r: &Reason,
            ty: &Ty,
        ) -> Vec<(Ty, dependency::Kind)> {
            let ty = bounds::strip_supportdyn(env, ty.clone());
            match get_node(&ty) {
                Ty_::Tgeneric(_) => vec![(ty.clone(), dependency::Kind::IndirectUpper)],
                Ty_::Tnewtype(name, _, _) if !is_supportdyn_name(name) => {
                    vec![(ty.clone(), dependency::Kind::IndirectUpper)]
                }
                Ty_::Tshape(shape_ty) => {
                    let normalized = normalize_row(env, r, shape_ty.clone());
                    match normalized_view(normalized) {
                        NormalizedView::Row(row) => row::spread_elements(&row)
                            .into_iter()
                            .map(|target| (target, dependency::Kind::NestedUpper))
                            .collect(),
                        NormalizedView::Union(tys) => indirect_dependencies_of_tys(env, r, &tys),
                        NormalizedView::Intersection(tys) => {
                            indirect_dependencies_of_tys(env, r, &tys)
                        }
                    }
                }
                Ty_::Tunion(tys) | Ty_::Tintersection(tys) => {
                    indirect_dependencies_of_tys(env, r, tys)
                }
                _ => vec![],
            }
        }
        fn indirect_dependencies_of_tys(
            env: &mut Env,
            r: &Reason,
            tys: &[Ty],
        ) -> Vec<(Ty, dependency::Kind)> {
            let dependencies: Vec<Vec<(Ty, dependency::Kind)>> = tys
                .iter()
                .map(|ty| indirect_dependencies(env, r, ty))
                .collect();
            dependencies.concat()
        }
        let dependencies_of_bound = |cache: &mut cache::T,
                                     env: &mut Env,
                                     bound: &Ty|
         -> Vec<(Ty, dependency::Kind)> {
            let bound = typing_env::expand_type(env, bound.clone());
            match get_node(&bound) {
                Ty_::Tgeneric(_) => vec![(bound.clone(), dependency::Kind::DirectUpper)],
                Ty_::Tnewtype(name, _, _) if !is_supportdyn_name(name) => {
                    vec![(bound.clone(), dependency::Kind::DirectUpper)]
                }
                _ => {
                    let bound = bounds::strip_supportdyn(env, bound.clone());
                    let supers = bounds::concrete_supertypes(cache, env, &bound);
                    indirect_dependencies_of_tys(env, r, &supers)
                }
            }
        };
        // The environment is threaded through, and dropped at the end.
        let env = &mut env.clone();
        let bounds = upper_bounds(cache, env, source, r);
        let dependencies: Vec<Vec<(Ty, dependency::Kind)>> = bounds
            .iter()
            .map(|bound| dependencies_of_bound(cache, env, bound))
            .collect();
        dependencies.concat()
    }

    fn dependencies_from(
        cache: &mut cache::T,
        env: &Env,
        source: &splat_elem::T,
        r: &Reason,
    ) -> Vec<dependency::T> {
        let upper = classified_upper_dependencies(cache, env, source, r);
        let lower: Vec<(Ty, dependency::Kind)> =
            type_params_in_lower_bound(cache, env, source, r)
                .into_iter()
                .map(|target| (target, dependency::Kind::NestedLower))
                .collect();
        upper
            .into_iter()
            .chain(lower)
            .map(|(target, kind)| dependency::make(source.clone(), target, kind))
            .collect()
    }

    /// The `ref`s of `analyze`, and what `visit` needs.
    struct Tarjan<'a> {
        cache: &'a mut cache::T,
        env: &'a Env,
        r: &'a Reason,
        next_index: isize,
        indices: splat_elem::map::T<isize>,
        lowlinks: splat_elem::map::T<isize>,
        /// The head of the OCaml list is the last element.
        stack: Vec<Ty>,
        on_stack: splat_elem::set::T,
        /// In the order the OCaml gets after `List.rev`.
        components: Vec<splat_elem::set::T>,
        /// In the order the OCaml gets after `List.rev`.
        dependencies: Vec<dependency::T>,
        node_visits: isize,
        edge_visits: isize,
    }

    /// `find map key = Option.value_exn (Splat_elem.Map.find_opt key !map)`
    fn find(map: &splat_elem::map::T<isize>, key: &Ty) -> isize {
        match splat_elem::map::find_opt(key, map) {
            Some(v) => *v,
            None => panic!("Option.value_exn None"),
        }
    }

    fn visit(st: &mut Tarjan<'_>, source: &Ty) {
        let index = st.next_index;
        st.next_index += 1;
        st.node_visits += 1;
        st.indices = splat_elem::map::add(source.clone(), index, &st.indices);
        st.lowlinks = splat_elem::map::add(source.clone(), index, &st.lowlinks);
        st.stack.push(source.clone());
        st.on_stack = splat_elem::set::add(source.clone(), &st.on_stack);
        let outgoing = dependencies_from(st.cache, st.env, source, st.r);
        // `dependencies := List.rev_append outgoing !dependencies`
        st.dependencies.extend(outgoing.iter().cloned());
        for dependency in outgoing.iter() {
            st.edge_visits += 1;
            let target = dependency::target(dependency);
            if !splat_elem::map::mem(&target, &st.indices) {
                visit(st, &target);
                let low = std::cmp::min(find(&st.lowlinks, source), find(&st.lowlinks, &target));
                st.lowlinks = splat_elem::map::add(source.clone(), low, &st.lowlinks);
            } else if splat_elem::set::mem(&target, &st.on_stack) {
                let low = std::cmp::min(find(&st.lowlinks, source), find(&st.indices, &target));
                st.lowlinks = splat_elem::map::add(source.clone(), low, &st.lowlinks);
            }
        }
        if find(&st.lowlinks, source) == find(&st.indices, source) {
            let mut members = splat_elem::set::empty();
            loop {
                match st.stack.pop() {
                    None => panic!("empty stack while completing an SCC"),
                    Some(member) => {
                        st.on_stack = splat_elem::set::remove(&member, &st.on_stack);
                        let is_source = splat_elem::compare(&member, source) == Ordering::Equal;
                        members = splat_elem::set::add(member, &members);
                        if is_source {
                            break;
                        }
                    }
                }
            }
            st.components.push(members);
        }
    }

    pub fn analyze(
        cache: &mut cache::T,
        env: &Env,
        roots: &splat_elem::set::T,
        r: &Reason,
    ) -> analysis::T {
        let mut st = Tarjan {
            cache,
            env,
            r,
            next_index: 0,
            indices: splat_elem::map::empty(),
            lowlinks: splat_elem::map::empty(),
            stack: vec![],
            on_stack: splat_elem::set::empty(),
            components: vec![],
            dependencies: vec![],
            node_visits: 0,
            edge_visits: 0,
        };
        splat_elem::set::iter(
            |root| {
                if !splat_elem::map::mem(root, &st.indices) {
                    visit(&mut st, root)
                }
            },
            roots,
        );
        // Tarjan pops dependencies before their dependents; the accumulator
        // reverses that order.
        let components = std::mem::take(&mut st.components);
        let dependencies = std::mem::take(&mut st.dependencies);
        let mut component_by_member: splat_elem::map::T<usize> = splat_elem::map::empty();
        for (index, members) in components.iter().enumerate() {
            component_by_member = splat_elem::set::fold(
                |member, acc| splat_elem::map::add(member.clone(), index, &acc),
                members,
                component_by_member,
            );
        }
        // `Splat_elem.Map.find`, which raises `Not_found`.
        let find_component = |key: &Ty| -> usize {
            match splat_elem::map::find_opt(key, &component_by_member) {
                Some(index) => *index,
                None => panic!("Not_found"),
            }
        };
        let mut internal_dependencies: Vec<Vec<dependency::T>> = vec![vec![]; components.len()];
        for dependency in dependencies.iter() {
            let source_component = find_component(&dependency::source(dependency));
            let target_component = find_component(&dependency::target(dependency));
            if source_component == target_component {
                // Consed onto, then reversed: here in order.
                internal_dependencies[source_component].push(dependency.clone());
            }
        }
        let components: Vec<component::T> = components
            .into_iter()
            .enumerate()
            .map(|(index, members)| {
                let dependencies = std::mem::take(&mut internal_dependencies[index]);
                let is_self_dependency = |dependency: &dependency::T| {
                    splat_elem::compare(
                        &dependency::source(dependency),
                        &dependency::target(dependency),
                    ) == Ordering::Equal
                };
                if splat_elem::set::cardinal(&members) == 1
                    && !dependencies.iter().any(is_self_dependency)
                {
                    component::T::Acyclic(splat_elem::set::choose(&members))
                } else {
                    let is_ty_param = |ty: &Ty| matches!(get_node(ty), Ty_::Tgeneric(_));
                    // Strong connectivity through direct upper constraints proves
                    // mutual subtyping. Other paths merely prove dependency.
                    if splat_elem::set::for_all(is_ty_param, &members)
                        && dependencies.iter().all(|dependency| {
                            match dependency::kind(dependency) {
                                dependency::Kind::DirectUpper => true,
                                dependency::Kind::IndirectUpper
                                | dependency::Kind::NestedUpper
                                | dependency::Kind::NestedLower => false,
                            }
                        })
                    {
                        let info = cycle_info::make(members, dependencies);
                        component::T::ProvenEqual(info)
                    } else {
                        let info = cycle_info::make(members, dependencies);
                        component::T::UnsupportedCycle(info)
                    }
                }
            })
            .collect();
        analysis::T {
            components,
            dependencies,
            node_visits: st.node_visits,
            edge_visits: st.edge_visits,
        }
    }

    /// Topological sort of type parameters. A type parameter that appears in
    /// another's bound is assigned first; a cycle just skips the offending edge.
    pub fn topo(
        cache: &mut cache::T,
        env: &Env,
        roots: &splat_elem::set::T,
        r: &Reason,
    ) -> Vec<Ty> {
        fn equal(a: &Ty, b: &Ty) -> bool {
            splat_elem::compare(a, b) == Ordering::Equal
        }
        fn visit(
            cache: &mut cache::T,
            env: &Env,
            r: &Reason,
            key: &Ty,
            order: Vec<Ty>,
            stack: &[Ty],
        ) -> Vec<Ty> {
            if order.iter().any(|x| equal(key, x)) || stack.iter().any(|x| equal(key, x)) {
                order
            } else {
                // `key :: stack`
                let mut key_stack = vec![key.clone()];
                key_stack.extend(stack.iter().cloned());
                let mut order = order;
                for dep in type_params_in_bounds(cache, env, key, r).iter() {
                    order = visit(cache, env, r, dep, order, &key_stack);
                }
                if order.iter().any(|x| equal(key, x)) {
                    order
                } else {
                    order.push(key.clone());
                    order
                }
            }
        }
        splat_elem::set::fold(|key, acc| visit(cache, env, r, key, acc, &[]), roots, vec![])
    }
}

mod labels {
    use super::*;

    fn bound_labels_upper(
        cache: &mut cache::T,
        env: &Env,
        name: &splat_elem::T,
        r: &Reason,
    ) -> LabelSet {
        // `ignore env`
        let view = bounds::bound_shape_upper(
            cache,
            &mut env.clone(),
            name,
            &splat_elem::map::empty(),
            r,
        );
        match view {
            bounds::upper::T::Shapes(shapes) => {
                let mut acc = stdlib_set::empty();
                for shape_ty in shapes.iter() {
                    acc = stdlib_set::union(&acc, &row::label_set(shape_ty));
                }
                acc
            }
            bounds::upper::T::Bottom | bounds::upper::T::Unconstrained => stdlib_set::empty(),
        }
    }

    fn bound_labels_lower(
        cache: &mut cache::T,
        env: &Env,
        name: &splat_elem::T,
        r: &Reason,
    ) -> LabelSet {
        // `ignore env`
        let view = bounds::bound_shape_lower(
            cache,
            &mut env.clone(),
            name,
            &splat_elem::map::empty(),
            r,
        );
        match view {
            bounds::lower::T::Shapes(shapes) => {
                let mut acc = stdlib_set::empty();
                for shape_ty in shapes.iter() {
                    acc = stdlib_set::union(&acc, &row::label_set(shape_ty));
                }
                acc
            }
            bounds::lower::T::Bottom => stdlib_set::empty(),
        }
    }

    fn bound_label_set(
        cache: &mut cache::T,
        env: &Env,
        names: Vec<Ty>,
        r: &Reason,
    ) -> LabelSet {
        let all = dependency_graph::closure(cache, env, &splat_elem::set::of_list(names), r);
        splat_elem::set::fold(
            |name, acc: LabelSet| {
                // `let up = ... and lo = ... in`: in this order.
                let up = bound_labels_upper(cache, env, name, r);
                let lo = bound_labels_lower(cache, env, name, r);
                stdlib_set::union(&acc, &stdlib_set::union(&up, &lo))
            },
            &all,
            stdlib_set::empty(),
        )
    }

    pub fn subrow_label_set(
        cache: &mut cache::T,
        env: &Env,
        sub: &srow::T,
        super_: &srow::T,
        r: &Reason,
    ) -> LabelSet {
        let mut params = row::spread_elements(sub);
        params.extend(row::spread_elements(super_));
        // The arguments of the outer `TShapeSet.union` are evaluated right to
        // left: `bound_label_set` first (`Row.label_set` has no effect).
        let bound = bound_label_set(cache, env, params, r);
        stdlib_set::union(
            &stdlib_set::union(&row::label_set(sub), &row::label_set(super_)),
            &bound,
        )
    }

    /// The full label list a splat subrow must check: [None] (the unknown tail)
    /// and every label appearing inline and in the bounds of opaque elements.
    pub fn subrow_labels(
        cache: &mut cache::T,
        env: &Env,
        sub: &srow::T,
        super_: &srow::T,
        r: &Reason,
    ) -> Vec<Option<TShapeField>> {
        let mut labels = vec![None];
        labels.extend(
            stdlib_set::elements(&subrow_label_set(cache, env, sub, super_, r))
                .into_iter()
                .map(|Label(l)| Some(l)),
        );
        labels
    }
}

// -- Masking ---------------------------------------------------------------

mod masking {
    use super::*;

    /// Describes how a type parameter influences leftward labels when projecting
    /// at that label under rightmost-wins semantics.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum T {
        Masked,
        Unmasked,
        Unknown,
    }

    /// Whether a type parameter to the right of [key] in [row] masks it at
    /// [label]: a rightward generic masks iff its own upper bound is [Req] there;
    /// [Req] lower but [Opt] upper is [Unknown] (pessimistic).
    fn of_splat(
        cache: &mut cache::T,
        env: &Env,
        ss_elems: &[Ty],
        label: Option<&TShapeField>,
        key: &Ty,
        assignment: &assignment::T,
        r: &Reason,
    ) -> T {
        // `aux (List.rev ss_elems) Unmasked`
        let mut acc = T::Unmasked;
        for ty in ss_elems.iter().rev() {
            match get_node(ty) {
                Ty_::Tgeneric(_) | Ty_::Tnewtype(..)
                    if splat_elem::compare(ty, key) == Ordering::Equal =>
                {
                    return acc;
                }
                Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                    // `let (_env, lower, upper) = ...`: each from `env`.
                    let (lower, upper) =
                        bounds::field_bounds(cache, &mut env.clone(), ty, label, assignment, r);
                    if field::is_required(&upper) {
                        return T::Masked;
                    } else if field::is_required(&lower) {
                        acc = T::Unknown
                    }
                }
                _ => {}
            }
        }
        T::Unknown
    }

    pub fn of_row(
        cache: &mut cache::T,
        env: &Env,
        row: &srow::T,
        label: Option<&TShapeField>,
        key: &Ty,
        assignment: &assignment::T,
        r: &Reason,
    ) -> T {
        match row_view(row) {
            RowView::Bottom => T::Unknown,
            RowView::Simple(_) => T::Unknown,
            RowView::Elements(ss_elems) => {
                of_splat(cache, env, &ss_elems, label, key, assignment, r)
            }
        }
    }
}

// -- Corner search ---------------------------------------------------------

/// Enumerate corner assignments in dependency order. Bound resolution is cached
/// within one shape-splat operation, but every assignment path is traversed.
mod corner_search {
    use super::*;

    pub fn corners_for(
        cache: &mut cache::T,
        env: &mut Env,
        depended_on: &splat_elem::set::T,
        live_sub: &splat_elem::set::T,
        live_super: &splat_elem::set::T,
        sub: &srow::T,
        super_: &srow::T,
        label: Option<&TShapeField>,
        key: &Ty,
        assignment: &assignment::T,
        r: &Reason,
    ) -> field::corners::T {
        let (lower, upper) = bounds::field_bounds(cache, env, key, label, assignment, r);
        let is_free = !splat_elem::set::mem(key, depended_on);
        let in_sub = splat_elem::set::mem(key, live_sub);
        let in_super = splat_elem::set::mem(key, live_super);
        if is_free && in_sub && !in_super {
            field::corners::T::Values(vec![upper])
        } else if is_free && (!in_sub) && in_super {
            field::corners::T::Values(vec![lower])
        } else if is_free && in_sub && in_super {
            // `let m_sub = ... and m_super = ... in`: in this order.
            let m_sub = masking::of_row(cache, env, sub, label, key, assignment, r);
            let m_super = masking::of_row(cache, env, super_, label, key, assignment, r);
            match (m_sub, m_super) {
                (masking::T::Masked, _) => field::corners::T::Values(vec![lower]),
                (_, masking::T::Masked) => field::corners::T::Values(vec![upper]),
                (_, masking::T::Unmasked) if field::is_optional(&lower) => {
                    field::corners::T::Values(vec![lower])
                }
                _ => field::corners::of_bounds(lower, upper),
            }
        } else {
            field::corners::of_bounds(lower, upper)
        }
    }

    /// What `loop` closes over, apart from `init` and `conj` (which the
    /// continuations it hands to `conj` share with it).
    struct Loop<'a, A> {
        cache: &'a mut cache::T,
        depended_on: &'a splat_elem::set::T,
        live_sub: &'a splat_elem::set::T,
        live_super: &'a splat_elem::set::T,
        sub: &'a srow::T,
        super_: &'a srow::T,
        label: Option<&'a TShapeField>,
        r: &'a Reason,
        f: &'a mut dyn FnMut(&mut Env, ShapeFieldType, ShapeFieldType) -> A,
    }

    /// `let rec loop keys assignment env`
    fn loop_<A>(
        lp: &mut Loop<'_, A>,
        init: &dyn Fn(&mut Env) -> A,
        conj: &dyn Fn(&mut Env, A, &mut dyn FnMut(&mut Env) -> A) -> A,
        keys: &[Ty],
        assignment: &assignment::T,
        env: &mut Env,
    ) -> A {
        match keys {
            [key, rest @ ..] => {
                let corners = corners_for(
                    lp.cache,
                    env,
                    lp.depended_on,
                    lp.live_sub,
                    lp.live_super,
                    lp.sub,
                    lp.super_,
                    lp.label,
                    key,
                    assignment,
                    lp.r,
                );
                match corners {
                    field::corners::T::Inverted => init(env),
                    field::corners::T::Values(assignments) => {
                        let mut acc = init(env);
                        for field in assignments {
                            acc = conj(env, acc, &mut |env: &mut Env| {
                                loop_(
                                    lp,
                                    init,
                                    conj,
                                    rest,
                                    &splat_elem::map::add(key.clone(), field.clone(), assignment),
                                    env,
                                )
                            });
                        }
                        acc
                    }
                }
            }
            [] => {
                let sub = row::proj(env, lp.sub, lp.label, assignment);
                let super_ = row::proj(env, lp.super_, lp.label, assignment);
                (lp.f)(env, sub, super_)
            }
        }
    }

    pub fn check_subrow_corners<A>(
        cache: &mut cache::T,
        env: &mut Env,
        sub: &srow::T,
        super_: &srow::T,
        label: Option<&TShapeField>,
        r: &Reason,
        init: &dyn Fn(&mut Env) -> A,
        conj: &dyn Fn(&mut Env, A, &mut dyn FnMut(&mut Env) -> A) -> A,
        f: &mut dyn FnMut(&mut Env, ShapeFieldType, ShapeFieldType) -> A,
    ) -> A {
        // `let live_sub = ... and live_super = ... in` (no effect)
        let live_sub = splat_elem::set::of_list(row::live_spreads(sub, label));
        let live_super = splat_elem::set::of_list(row::live_spreads(super_, label));
        let all_live = splat_elem::set::union(&live_sub, &live_super);
        let ty_params_topo = dependency_graph::topo(cache, env, &all_live, r);
        let mut depended_on = splat_elem::set::empty();
        for key in ty_params_topo.iter() {
            depended_on = splat_elem::set::union(
                &depended_on,
                &splat_elem::set::of_list(dependency_graph::type_params_in_bounds(
                    cache, env, key, r,
                )),
            );
        }
        let mut lp = Loop {
            cache,
            depended_on: &depended_on,
            live_sub: &live_sub,
            live_super: &live_super,
            sub,
            super_,
            label,
            r,
            f,
        };
        loop_(
            &mut lp,
            init,
            conj,
            &ty_params_topo,
            &splat_elem::map::empty(),
            env,
        )
    }

    pub fn assignments(
        cache: &mut cache::T,
        env: &mut Env,
        ty_params_topo: &[Ty],
        label: Option<&TShapeField>,
        r: &Reason,
    ) -> Vec<assignment::T> {
        fn aux(
            cache: &mut cache::T,
            label: Option<&TShapeField>,
            r: &Reason,
            env: &mut Env,
            keys: &[Ty],
            assignment: &assignment::T,
        ) -> Vec<assignment::T> {
            match keys {
                [] => vec![assignment.clone()],
                [key, rest @ ..] => {
                    let (lower, upper) =
                        bounds::field_bounds(cache, env, key, label, assignment, r);
                    let corners = match field::corners::of_bounds(lower, upper) {
                        field::corners::T::Values(corners) => corners,
                        field::corners::T::Inverted => vec![],
                    };
                    // `rev_chunks`, consed onto and then reversed: here in order.
                    let mut chunks: Vec<Vec<assignment::T>> = vec![];
                    for field in corners {
                        let assignments = aux(
                            cache,
                            label,
                            r,
                            env,
                            rest,
                            &splat_elem::map::add(key.clone(), field, assignment),
                        );
                        chunks.push(assignments);
                    }
                    chunks.concat()
                }
            }
        }
        aux(
            cache,
            label,
            r,
            env,
            ty_params_topo,
            &splat_elem::map::empty(),
        )
    }
}

mod spread_var {
    use super::*;

    /// Spread type-variable ids at spread position, in source order
    pub fn ids(row: &srow::T) -> Vec<tvid::T> {
        match row_view(row) {
            RowView::Bottom => vec![],
            RowView::Simple(_) => vec![],
            RowView::Elements(tys) => tys
                .iter()
                .filter_map(|ty| match get_node(ty) {
                    Ty_::Tvar(v) => Some(*v),
                    _ => None,
                })
                .collect(),
        }
    }

    /// Split a splat's elements around the first occurrence of spread var [v]
    /// returning the elements before and after.
    pub fn partition(row: &srow::T, v: tvid::T) -> Option<(Vec<Ty>, Vec<Ty>)> {
        match row_view(row) {
            RowView::Bottom => None,
            RowView::Simple(_) => None,
            RowView::Elements(ss_elems) => {
                // `loop elems left`: `left` is consed onto, so it is built here in
                // order (`List.rev left`).
                let mut left: Vec<Ty> = vec![];
                for (i, ty) in ss_elems.iter().enumerate() {
                    match get_node(ty) {
                        Ty_::Tvar(v_) if tvid::equal(v, *v_) => {
                            return Some((left, ss_elems[i + 1..].to_vec()));
                        }
                        _ => left.push(ty.clone()),
                    }
                }
                None
            }
        }
    }

    /// Resolve a row's spread type variables to their current solutions, for the
    /// decoupled both-sides fallback: expand each spread var; keep it if it
    /// resolved to a non-var, drop it (the empty-row contribution) if still
    /// unsolved. Sound (the dropped var contributes nothing).
    ///
    /// Substituting breaks normal form three ways: dropping a var can leave a
    /// lone element, a solution can itself be a splat, and a solution can land
    /// next to another simple shape, so the rewritten row is re-normalized
    /// before it goes back to the corner.
    pub fn solve(env: &mut Env, r: &Reason, row: &srow::T) -> srow::Normalized {
        let normalize = |env: &mut Env, ss_elems: Vec<Ty>| -> srow::Normalized {
            normalize_row(env, r, ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))
        };
        match row_view(row) {
            RowView::Bottom => normalize(env, vec![srow::to_ty(r.clone(), row)]),
            RowView::Simple(_) => normalize(env, vec![srow::to_ty(r.clone(), row)]),
            RowView::Elements(ss_elems) => {
                // `rev`, consed onto and then reversed: here in order.
                let mut elems: Vec<Ty> = vec![];
                for ty in ss_elems {
                    match get_node(&ty) {
                        Ty_::Tvar(_) => {
                            let ty_ = typing_env::expand_type(env, ty.clone());
                            match get_node(&ty_) {
                                Ty_::Tvar(_) => {}
                                _ => elems.push(ty_),
                            }
                        }
                        _ => elems.push(ty),
                    }
                }
                normalize(env, elems)
            }
        }
    }
}

// -- API -------------------------------------------------------------------

/// Resolve a splat to a single simple shape for field reads; takes every live
/// type parameter to its upper bound in topological order then read each label off
/// the projected row. Reuses the corner machinery ([closure]/[topo]/[field_bounds]/
/// [proj]) so mutually-referencing bounds (e.g. [T2 as shape(...T1)]) resolve in
/// order.
pub fn resolve_for_read(env: &mut Env, r: Reason, elems: &[Ty]) -> Ty {
    let mut cache = cache::create();
    let cache = &mut cache;
    // Project a single row to a resolved simple shape (generics -> upper bound).
    let project = |cache: &mut cache::T, env: &mut Env, row: &srow::T| -> Ty {
        let mut labels: Vec<Option<TShapeField>> = vec![None];
        labels.extend(
            stdlib_set::elements(&labels::subrow_label_set(cache, env, row, row, &r))
                .into_iter()
                .map(|Label(l)| Some(l)),
        );
        let mut known: TShapeMap<ShapeFieldType> = TShapeMap::new();
        let mut unknown = make_type::nothing(r.clone());
        for label in labels.iter() {
            let label = label.as_ref();
            let live = splat_elem::set::of_list(row::live_spreads(row, label));
            let ty_params_topo = dependency_graph::topo(cache, env, &live, &r);
            // Assign each type param its upper bound, in topo order so a param's
            // bound is projected under the upper corners it depends on.
            let mut assignment: assignment::T = splat_elem::map::empty();
            for key in ty_params_topo.iter() {
                let (_lower, upper) = bounds::field_bounds(cache, env, key, label, &assignment, &r);
                assignment = splat_elem::map::add(key.clone(), upper, &assignment);
            }
            let fd = row::proj(env, row, label, &assignment);
            match label {
                Some(lbl) => {
                    known.insert(lbl.clone(), fd);
                }
                None => unknown = fd.ty,
            }
        }
        mk((
            r.clone(),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: unknown,
                fields: known,
            })),
        ))
    };
    let normalized = {
        let shape_ty = ShapeType::ShapeSplat(ShapeTypeSplat {
            ss_elems: elems.to_vec(),
        });
        let on_error = None;
        let (_err, normalized) = srow::normalize(on_error, r.clone(), shape_ty, env);
        normalized
    };
    // The cases of `union` and `intersection` read `normalized` itself.
    match normalized_view(normalized.clone()) {
        NormalizedView::Row(row) => {
            if srow::is_bottom(&row) {
                srow::to_ty(r.clone(), &row)
            } else {
                project(cache, env, &row)
            }
        }
        NormalizedView::Union(_) => srow::normalized_to_ty(env, r.clone(), normalized),
        NormalizedView::Intersection(_) => srow::normalized_to_ty(env, r.clone(), normalized),
    }
}

/// Read a row at one label under the current assignment. [None] is the label
/// standing for every field name nobody wrote down.
pub fn proj(
    env: &mut Env,
    row: &srow::T,
    label: Option<&TShapeField>,
    assignment: &assignment::T,
) -> ShapeFieldType {
    row::proj(env, row, label, assignment)
}

/// Type parameter/newtype spreads that can affect [row] at [label], excluding
/// those masked by a required field to their right; [None] selects the tail i.e.
/// the upper bound for all unknown fields.
pub fn row_live_spread_at(row: &srow::T, label: Option<&TShapeField>) -> Vec<Ty> {
    row::live_spreads(row, label)
}

/// Concrete labels contributed by either row or by bounds of their spreads.
pub fn subrow_label_set(
    cache: &mut cache::T,
    env: &Env,
    sub: &srow::T,
    super_: &srow::T,
    r: Reason,
) -> TShapeSet {
    stdlib_set::elements(&labels::subrow_label_set(cache, env, sub, super_, &r))
        .into_iter()
        .map(|Label(l)| l)
        .collect()
}

/// The unknown tail ([None]) followed by every concrete label to compare.
pub fn subrow_labels(
    cache: &mut cache::T,
    env: &Env,
    sub: &srow::T,
    super_: &srow::T,
    r: Reason,
) -> Vec<Option<TShapeField>> {
    labels::subrow_labels(cache, env, sub, super_, &r)
}

/// The order in which the given roots and everything reachable from them
/// should be given values: each after those its bounds mention. Bounds can be
/// cyclic, as [where T1 = T2] makes them, and then one dependency is dropped;
/// the result is still total and does not vary between runs.
pub fn topo(
    cache: &mut cache::T,
    env: &Env,
    roots: &splat_elem::set::T,
    r: Reason,
) -> Vec<Ty> {
    dependency_graph::topo(cache, env, roots, &r)
}

/// Check every corner assignment of the live spread elements.
///
/// `~init`, `~conj` and `~f` thread the environment: `init env`,
/// `conj (env, acc) k` (here `conj(env, acc, k)`, `k` the continuation that
/// goes on with the next spread element) and `f env ~sub ~super`.
pub fn check_subrow_corners<A>(
    cache: &mut cache::T,
    env: &mut Env,
    sub: &srow::T,
    super_: &srow::T,
    label: Option<&TShapeField>,
    r: Reason,
    init: impl Fn(&mut Env) -> A,
    conj: impl Fn(&mut Env, A, &mut dyn FnMut(&mut Env) -> A) -> A,
    mut f: impl FnMut(&mut Env, ShapeFieldType, ShapeFieldType) -> A,
) -> A {
    corner_search::check_subrow_corners(
        cache, env, sub, super_, label, &r, &init, &conj, &mut f,
    )
}

/// Every corner co-assignment of the given spread elements.
pub fn corner_assignments(
    cache: &mut cache::T,
    env: &mut Env,
    ty_params_topo: &[Ty],
    label: Option<&TShapeField>,
    r: Reason,
) -> Vec<assignment::T> {
    corner_search::assignments(cache, env, ty_params_topo, label, &r)
}

/// Type-variable IDs occurring in spread position, in source order.
pub fn spread_tyvar_ids(row: &srow::T) -> Vec<tvid::T> {
    spread_var::ids(row)
}

/// Split a splat around the first occurrence of the given spread variable.
pub fn partition_at_tyvar(row: &srow::T, v: tvid::T) -> Option<(Vec<Ty>, Vec<Ty>)> {
    spread_var::partition(row, v)
}

/// Substitute solved spread variables and drop unsolved ones as empty rows.
pub fn solve_spread_vars(env: &mut Env, r: Reason, row: &srow::T) -> srow::Normalized {
    spread_var::solve(env, &r, row)
}

/// Exported only so the tests can reach them.
///
/// Nothing outside typingCornersTest uses anything below. They are the pieces
/// whose behaviour the tests check directly rather than through a subtyping
/// decision, which is the whole reason this module was split out of
/// Typing_subtype: reached only through [is_sub_type], most of their
/// configurations cannot be produced at all.
pub mod for_test {
    use super::*;

    /// Shape interpretations of an upper bound; unconstrained means non-shape.
    pub enum UpperBoundView {
        UpperShapes(Vec<srow::T>),
        UpperBottom,
        UpperUnconstrained,
    }

    /// Shape interpretations of a lower bound, defaulting to the bottom row.
    pub enum LowerBoundView {
        LowerShapes(Vec<srow::T>),
        LowerBottom,
    }

    /// Whether rightward spreads prevent an element from affecting a label.
    pub mod masking {
        use super::*;

        /// Definite masking, definite visibility, or a bounds-dependent result.
        pub use super::super::masking::T;

        /// Determine how [key] is masked in a row under the current assignment.
        pub fn of_row(
            cache: &mut cache::T,
            env: &Env,
            row: &srow::T,
            label: Option<&TShapeField>,
            key: &Ty,
            assignment: &assignment::T,
            r: Reason,
        ) -> T {
            super::super::masking::of_row(cache, env, row, label, key, assignment, &r)
        }
    }

    pub mod dependency {
        pub use super::super::dependency_graph::dependency::Kind;
        pub use super::super::dependency_graph::dependency::T;
        pub use super::super::dependency_graph::dependency::kind;
        pub use super::super::dependency_graph::dependency::position;
        pub use super::super::dependency_graph::dependency::source;
        pub use super::super::dependency_graph::dependency::target;
    }

    pub mod cycle_info {
        pub use super::super::dependency_graph::cycle_info::T;
        pub use super::super::dependency_graph::cycle_info::dependencies;
        pub use super::super::dependency_graph::cycle_info::members;
    }

    pub mod component {
        pub use super::super::dependency_graph::component::T;
        pub use super::super::dependency_graph::component::members;
    }

    pub mod analysis {
        pub use super::super::dependency_graph::analysis::T;
        pub use super::super::dependency_graph::analysis::components;
        pub use super::super::dependency_graph::analysis::dependencies;
        pub use super::super::dependency_graph::analysis::edge_visits;
        pub use super::super::dependency_graph::analysis::node_visits;
    }

    /// Analyze reachable dependencies without changing the corner traversal.
    pub fn analyze_dependencies(
        env: &Env,
        roots: &splat_elem::set::T,
        r: Reason,
    ) -> analysis::T {
        dependency_graph::analyze(&mut cache::create(), env, roots, &r)
    }

    /// Everything reachable by following bounds from the given elements.
    pub fn closure(env: &Env, names: &splat_elem::set::T, r: Reason) -> splat_elem::set::T {
        let mut cache = cache::create();
        dependency_graph::closure(&mut cache, env, names, &r)
    }

    /// Interpret a spread element's upper bound as normalized shape rows.
    pub fn bound_shape_upper(
        env: &mut Env,
        ty: &Ty,
        assignment: &assignment::T,
        r: Reason,
    ) -> UpperBoundView {
        let mut cache = cache::create();
        let view = bounds::bound_shape_upper(&mut cache, env, ty, assignment, &r);
        match view {
            bounds::upper::T::Shapes(rows) => UpperBoundView::UpperShapes(rows),
            bounds::upper::T::Bottom => UpperBoundView::UpperBottom,
            bounds::upper::T::Unconstrained => UpperBoundView::UpperUnconstrained,
        }
    }

    /// Interpret a spread element's lower bound as normalized shape rows.
    pub fn bound_shape_lower(
        env: &mut Env,
        ty: &Ty,
        assignment: &assignment::T,
        r: Reason,
    ) -> LowerBoundView {
        let mut cache = cache::create();
        let view = bounds::bound_shape_lower(&mut cache, env, ty, assignment, &r);
        match view {
            bounds::lower::T::Shapes(rows) => LowerBoundView::LowerShapes(rows),
            bounds::lower::T::Bottom => LowerBoundView::LowerBottom,
        }
    }

    /// Project a spread element's lower and upper field bounds at one label.
    pub fn field_bounds(
        env: &mut Env,
        name: &Ty,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: Reason,
    ) -> (ShapeFieldType, ShapeFieldType) {
        bounds::field_bounds(&mut cache::create(), env, name, label, assignment, &r)
    }

    /// Spread elements mentioned by the given element's upper bound.
    pub fn type_params_in_upper_bound(env: &Env, splat_elem: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        dependency_graph::type_params_in_upper_bound(&mut cache, env, splat_elem, &r)
    }

    /// Spread elements mentioned by the given element's lower bound.
    ///
    /// (The OCaml applies it to one cache created when the module is
    /// initialised; the cache holds nothing here.)
    pub fn type_params_in_lower_bound(env: &Env, name: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        dependency_graph::type_params_in_lower_bound(&mut cache, env, name, &r)
    }

    /// Spread elements mentioned by either bound of the given element.
    ///
    /// (Likewise.)
    pub fn type_params_in_bounds(env: &Env, key: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        dependency_graph::type_params_in_bounds(&mut cache, env, key, &r)
    }

    /// Which corners to check for [key] at one label. Fewer than all of them when
    /// the element can only affect one side of the comparison.
    pub fn corners_for(
        env: &mut Env,
        depended_on: &splat_elem::set::T,
        live_sub: &splat_elem::set::T,
        live_super: &splat_elem::set::T,
        sub: &srow::T,
        super_: &srow::T,
        label: Option<&TShapeField>,
        key: &Ty,
        assignment: &assignment::T,
        r: Reason,
    ) -> field::corners::T {
        let mut cache = cache::create();
        corner_search::corners_for(
            &mut cache,
            env,
            depended_on,
            live_sub,
            live_super,
            sub,
            super_,
            label,
            key,
            assignment,
            &r,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn generic(name: &str) -> Ty {
        mk((typing_reason::none(), Ty_::Tgeneric(name.to_string())))
    }

    #[test]
    fn corners_of_bounds() {
        let nothing = make_type::nothing(typing_reason::none());
        let mixed = make_type::mixed(typing_reason::none());
        let fd = |optional: bool, ty: &Ty| ShapeFieldType {
            optional,
            ty: ty.clone(),
        };
        match field::corners::of_bounds(fd(false, &nothing), fd(true, &mixed)) {
            field::corners::T::Values(v) => {
                let opts: Vec<bool> = v.iter().map(|f| f.optional).collect();
                assert_eq!(opts, vec![false, true, true, false]);
            }
            field::corners::T::Inverted => panic!("expected values"),
        }
        match field::corners::of_bounds(fd(true, &nothing), fd(true, &mixed)) {
            field::corners::T::Values(v) => assert_eq!(v.len(), 2),
            field::corners::T::Inverted => panic!("expected values"),
        }
        assert!(matches!(
            field::corners::of_bounds(fd(true, &nothing), fd(false, &mixed)),
            field::corners::T::Inverted
        ));
    }

    #[test]
    fn field_predicates() {
        let ty = make_type::mixed(typing_reason::none());
        let req = ShapeFieldType {
            optional: false,
            ty: ty.clone(),
        };
        let opt = ShapeFieldType {
            optional: true,
            ty,
        };
        assert!(field::is_required(&req));
        assert!(field::is_optional(&opt));
        assert!(field::requiredness_lte(&req, &opt));
        assert!(field::requiredness_lte(&req, &req));
        assert!(field::requiredness_lte(&opt, &opt));
        assert!(!field::requiredness_lte(&opt, &req));
    }

    #[test]
    fn splat_elem_sets() {
        let t1 = generic("T1");
        let t2 = generic("T2");
        // The same parameter with another reason is the same element.
        let t1_again = generic("T1");
        assert_eq!(splat_elem::compare(&t1, &t1_again), Ordering::Equal);
        assert_ne!(splat_elem::compare(&t1, &t2), Ordering::Equal);
        let s = splat_elem::set::of_list(vec![t2.clone(), t1.clone(), t1_again]);
        assert_eq!(splat_elem::set::cardinal(&s), 2);
        assert!(splat_elem::set::mem(&t1, &s));
        let m = splat_elem::map::add(t1.clone(), 1, &splat_elem::map::empty());
        assert_eq!(splat_elem::map::find_opt(&t1, &m), Some(&1));
        assert!(!splat_elem::map::mem(&t2, &m));
    }
}
