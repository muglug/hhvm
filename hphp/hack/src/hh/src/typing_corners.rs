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
//! - `Env_memo` (see [`env_memo`]), which the tables of `Bound_lookup.Cache`
//!   and `Analysis.Cache` (together [`cache::T`]) are made of: the OCaml
//!   reuses a memoised value only for the physically identical environment,
//!   and stores one only when the computation left the environment physically
//!   unchanged. A Rust `Env` is mutated in place and has no identity, so no
//!   entry could be shown valid: `memoize` and `memoize_value` recompute. A
//!   hit in the OCaml returns what the computation returns again in that
//!   environment, so only the cost (and dependencies recorded again, which
//!   are sets) differs.
//! - A projection that finds no assigned field for a live spread element
//!   gives `Error Missing_assignment.t` (`Result<_, missing_assignment::T>`),
//!   and a traversal of corners gives a [`Computation`]; the environment the
//!   OCaml returns beside either is the one that is threaded.
//! - `Search.fold_plan` takes `~corners ~leaf ~empty ~combine`; here they are
//!   the methods of one value (`search::Fold`), since the closures would each
//!   borrow the cache.
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

        pub fn inter(s1: &T, s2: &T) -> T {
            T(stdlib_set::inter(&s1.0, &s2.0))
        }

        pub fn diff(s1: &T, s2: &T) -> T {
            T(stdlib_set::diff(&s1.0, &s2.0))
        }

        pub fn choose_opt(s: &T) -> Option<Ty> {
            stdlib_set::choose_opt(&s.0).map(|k| k.0.clone())
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

/// A spread element was projected without an assigned field.
pub mod missing_assignment {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct T {
        pub element: splat_elem::T,
        pub position: PosOrDecl,
    }

    pub fn make(element: Ty) -> T {
        let position = get_pos(&element);
        T { element, position }
    }

    pub fn element(missing: &T) -> &splat_elem::T {
        &missing.element
    }

    pub fn position(missing: &T) -> &PosOrDecl {
        &missing.position
    }
}

/// `type 'a entry = { input_env: env; value: 'a }`: an entry is valid for
/// the environment, compared by physical identity, in which it was computed.
/// That identity does not exist for a Rust `Env` (see the module
/// documentation), so a table holds no entries and [`memoize`] and
/// [`memoize_value`] compute their value every time, which is what the OCaml
/// returns on a hit.
pub mod env_memo {
    use std::marker::PhantomData;

    use super::*;

    /// One table of `'a entry Splat_elem.Map.t ref`.
    pub struct Table<A>(PhantomData<A>);

    impl<A> Table<A> {
        pub fn new() -> Self {
            Table(PhantomData)
        }
    }

    /// Memoize an environment-threading computation only when it returns the
    /// physically identical environment. Reusing a value that changed the
    /// environment could couple otherwise independent branches.
    ///
    /// (Here: the computation, every time; see [`env_memo`](self).)
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
    /// (Here: the computation, every time; see [`env_memo`](self).)
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

        /// The generated fields can only be duplicates when the lower and upper
        /// types are equal. Compare them at most once: [equal_locl_ty] may traverse
        /// large types, and this function runs at internal nodes of the
        /// corner traversal. Structural equality is nevertheless intentional;
        /// retaining separately allocated but equal bounds would multiply the
        /// number of branches explored afterwards.
        ///
        /// An inverted bound pair is uninhabited and contributes no obligations.
        pub fn of_bounds(lower: Field, upper: Field) -> T {
            match (lower.optional, upper.optional) {
                (false, true) => {
                    if typing_defs::equal_locl_ty(&lower.ty, &upper.ty) {
                        T::Values(vec![lower, upper])
                    } else {
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
                }
                (false, false) | (true, true) => {
                    if typing_defs::equal_locl_ty(&lower.ty, &upper.ty) {
                        T::Values(vec![lower])
                    } else {
                        T::Values(vec![lower, upper])
                    }
                }
                (true, false) => T::Inverted,
            }
        }
    }
}

// -- Projection ------------------------------------------------------------

/// `TShapeSet.t` as `Stdlib.Set.Make (TShapeField)` builds it (see the
/// module documentation).
#[derive(Clone, Debug)]
pub struct Label(TShapeField);

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
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        let r = get_reason(ty);
        match get_node(ty) {
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                match splat_elem::map::find_opt(ty, assignment) {
                    Some(fd) => Ok(fd.clone()),
                    None => Err(missing_assignment::make(ty.clone())),
                }
            }
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            })) => Ok(proj_simple(s_fields, s_unknown_value, label)),
            _ if typing_defs::is_nothing(ty) => Ok(ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            }),
            _ => Ok(ShapeFieldType {
                optional: true,
                ty: make_type::nothing(r.clone()),
            }),
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
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        if !fd_right.optional {
            Ok(fd_right)
        } else {
            match rev_left {
                [] => Ok(fd_right),
                [elem, rest @ ..] => match proj_element(env, elem, label, assignment) {
                    Err(missing) => Err(missing),
                    Ok(fd_left) => {
                        let fd = field::merge(fd_left, fd_right, env);
                        proj_splat_help(env, rest, label, assignment, fd)
                    }
                },
            }
        }
    }

    fn proj_splat(
        env: &mut Env,
        ss_elems: &[Ty],
        label: Option<&TShapeField>,
        assignment: &assignment::T,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        let rev: Vec<Ty> = ss_elems.iter().rev().cloned().collect();
        match &rev[..] {
            [] => {
                // An empty splat is the identity, i.e. the empty closed shape. Every label
                // projects to absent (Opt nothing)
                Ok(ShapeFieldType {
                    optional: true,
                    ty: make_type::nothing(typing_reason::none()),
                })
            }
            [rightmost, rev_left @ ..] => {
                match proj_element(env, rightmost, label, assignment) {
                    Err(missing) => Err(missing),
                    Ok(fd) => proj_splat_help(env, rev_left, label, assignment, fd),
                }
            }
        }
    }

    /// Project a normalized splat row at a label under an [Assignment.t] of
    /// all spread elements contributing to that label. [None] denotes the
    /// unknown tail: every label not named explicitly.
    pub fn proj(
        env: &mut Env,
        row: &srow::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        match row_view(row) {
            RowView::Bottom => Ok(ShapeFieldType {
                optional: false,
                ty: make_type::nothing(typing_reason::none()),
            }),
            RowView::Simple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            }) => Ok(proj_simple(&s_fields, &s_unknown_value, label)),
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

// -- Bound lookup ----------------------------------------------------------
// Determine the bounds of an opaque shape splat element under the typing
// environment.
// --------------------------------------------------------------------------

mod bound_lookup {
    use super::*;

    pub mod cache {
        use super::*;

        pub struct T {
            pub(in super::super) upper_bounds: env_memo::Table<Ty>,
            pub(in super::super) lower_bounds: env_memo::Table<Ty>,
            pub(in super::super) concrete_supers: env_memo::Table<Vec<Ty>>,
            pub(in super::super) concrete_subs: env_memo::Table<Vec<Ty>>,
        }

        pub fn create() -> T {
            T {
                upper_bounds: env_memo::Table::new(),
                lower_bounds: env_memo::Table::new(),
                concrete_supers: env_memo::Table::new(),
                concrete_subs: env_memo::Table::new(),
            }
        }
    }

    pub fn combined_upper_bound(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Ty {
        env_memo::memoize(&mut cache.upper_bounds, env, key, |env| {
            match get_node(key) {
                Ty_::Tnewtype(name, targs, _) => {
                    typing_utils::get_newtype_super(env, get_reason(key).clone(), name, targs)
                }
                Ty_::Tgeneric(name) => {
                    let bounds = typing_env::get_upper_bounds(env, name);
                    if typing_set::is_empty(&bounds) {
                        make_type::mixed(r.clone())
                    } else {
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

    pub fn combined_lower_bound(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Ty {
        env_memo::memoize(&mut cache.lower_bounds, env, key, |env| {
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

    pub fn upper_bounds(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        match get_node(key) {
            Ty_::Tgeneric(name) => typing_set::elements(&typing_env::get_upper_bounds(env, name)),
            Ty_::Tnewtype(..) => {
                let bound = combined_upper_bound(cache, env, key, r);
                vec![bound]
            }
            _ => vec![],
        }
    }

    pub fn lower_bounds(
        cache: &mut cache::T,
        env: &mut Env,
        key: &splat_elem::T,
        r: &Reason,
    ) -> Vec<Ty> {
        match get_node(key) {
            Ty_::Tgeneric(name) => typing_set::elements(&typing_env::get_lower_bounds(env, name)),
            Ty_::Tnewtype(..) => {
                let bound = combined_lower_bound(cache, env, key, r);
                vec![bound]
            }
            _ => vec![],
        }
    }

    pub fn concrete_supertypes(cache: &mut cache::T, env: &mut Env, ty: &Ty) -> Vec<Ty> {
        env_memo::memoize(&mut cache.concrete_supers, env, ty, |env| {
            typing_utils::get_concrete_supertypes(None, None, None, false, env, ty.clone())
        })
    }

    pub fn concrete_subtypes(cache: &mut cache::T, env: &mut Env, ty: &Ty) -> Vec<Ty> {
        env_memo::memoize(&mut cache.concrete_subs, env, ty, |env| {
            typing_utils::get_concrete_subtypes(env, ty.clone())
        })
    }

    pub fn strip_supportdyn(env: &mut Env, ty: Ty) -> Ty {
        let (_supportdyn, ty) = typing_utils::strip_supportdyn(env, ty);
        ty
    }
}

// -- Exact field-bound evaluation ----------------------------------------
//
// This is the first stage allowed to normalize bounds. By the time it runs,
// dependency analysis has produced an order in which every parameter needed
// by a projected bound already has a field in [Assignment.t]. A missing
// assignment therefore exposes a broken planning invariant.
//
// If declarations establish [L <: T <: U], T's field lies between the
// projected fields of L and U. Multiple lower possibilities are joined,
// because T must admit each of them. Multiple upper constraints are met,
// because T must satisfy all of them. For example:
//
//   required int join required string = required (int | string)
//   required mixed meet optional mixed = required mixed
//
// The view constructors distinguish facts that project to similar fields:
// [Lower.Bottom] means that no shape lower bound supplied positive
// information; [Upper.Bottom] means the parameter is uninhabited; and
// [Upper.Unconstrained] means no upper bound restricted shape fields.
// -------------------------------------------------------------------------
mod field_bounds {
    use super::*;

    // -- Bound views and normalization -------------------------------------

    fn shape_types(env: &mut Env, tys: &[Ty]) -> Vec<ShapeType> {
        let shapes: Vec<Option<ShapeType>> = tys
            .iter()
            .map(|ty| {
                let ty = bound_lookup::strip_supportdyn(env, ty.clone());
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
            /// Likewise, but the element is above every one of them, so combine by
            /// join.
            Shapes(Vec<srow::T>),
            /// No usable shape lower bound supplied positive information.
            Bottom,
        }
    }

    fn intersect_upper_views(views: Vec<upper::T>) -> upper::T {
        if views.iter().any(|view| match view {
            upper::T::Bottom => true,
            upper::T::Shapes(_) | upper::T::Unconstrained => false,
        }) {
            upper::T::Bottom
        } else {
            let rows: Vec<srow::T> = views
                .into_iter()
                .flat_map(|view| match view {
                    upper::T::Shapes(rows) => rows,
                    upper::T::Bottom | upper::T::Unconstrained => vec![],
                })
                .collect();
            if rows.is_empty() {
                upper::T::Unconstrained
            } else {
                upper::T::Shapes(rows)
            }
        }
    }

    fn union_lower_views(views: Vec<lower::T>) -> lower::T {
        let rows: Vec<srow::T> = views
            .into_iter()
            .flat_map(|view| match view {
                lower::T::Shapes(rows) => rows,
                lower::T::Bottom => vec![],
            })
            .collect();
        if rows.is_empty() {
            lower::T::Bottom
        } else {
            lower::T::Shapes(rows)
        }
    }

    /// Read a normalized shape in each direction's own answer type.
    fn normalized_upper(env: &mut Env, r: &Reason, shape_ty: ShapeType) -> upper::T {
        let normalized = normalize_row(env, r, shape_ty);
        match normalized_view(normalized) {
            NormalizedView::Row(row) => {
                if srow::is_bottom(&row) {
                    upper::T::Bottom
                } else {
                    upper::T::Shapes(vec![row])
                }
            }
            NormalizedView::Union(_) => upper::T::Unconstrained,
            NormalizedView::Intersection(tys) => {
                let views: Vec<upper::T> = tys
                    .iter()
                    .map(|ty| {
                        normalized_upper(
                            env,
                            get_reason(ty),
                            ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: vec![ty.clone()],
                            }),
                        )
                    })
                    .collect();
                intersect_upper_views(views)
            }
        }
    }

    fn normalized_lower(env: &mut Env, r: &Reason, shape_ty: ShapeType) -> lower::T {
        let normalized = normalize_row(env, r, shape_ty);
        match normalized_view(normalized) {
            NormalizedView::Row(row) => {
                if srow::is_bottom(&row) {
                    lower::T::Bottom
                } else {
                    lower::T::Shapes(vec![row])
                }
            }
            NormalizedView::Union(tys) => {
                let views: Vec<lower::T> = tys
                    .iter()
                    .map(|ty| {
                        normalized_lower(
                            env,
                            get_reason(ty),
                            ShapeType::ShapeSplat(ShapeTypeSplat {
                                ss_elems: vec![ty.clone()],
                            }),
                        )
                    })
                    .collect();
                union_lower_views(views)
            }
            NormalizedView::Intersection(_) => lower::T::Bottom,
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

    fn is_assigned_param(bound_ty: &Ty, assignment: &assignment::T) -> bool {
        splat_elem::map::mem(bound_ty, assignment)
            && match get_node(bound_ty) {
                Ty_::Tnewtype(n, _, _) => !is_supportdyn_name(n),
                _ => true,
            }
    }

    fn bound_shape_upper_of_ty(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        bound_ty: Ty,
        assignment: &assignment::T,
        r: &Reason,
    ) -> upper::T {
        let bound_ty = typing_env::expand_type(env, bound_ty);
        let bound_ty = bound_lookup::strip_supportdyn(env, bound_ty);
        match get_node(&bound_ty) {
            Ty_::Tshape(shape_ty) => normalized_upper(env, r, shape_ty.clone()),
            Ty_::Tdynamic(_) => upper::T::Shapes(vec![dynamic_row(r)]),
            _ if typing_defs::is_nothing(&bound_ty) => upper::T::Bottom,
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) if is_assigned_param(&bound_ty, assignment) => {
                normalized_upper(
                    env,
                    r,
                    ShapeType::ShapeSplat(ShapeTypeSplat {
                        ss_elems: vec![bound_ty.clone()],
                    }),
                )
            }
            _ => {
                let supers = bound_lookup::concrete_supertypes(cache, env, &bound_ty);
                let shapes = shape_types(env, &supers);
                if shapes.is_empty() {
                    upper::T::Unconstrained
                } else {
                    let row_groups: Vec<Option<Vec<srow::T>>> = shapes
                        .into_iter()
                        .map(|shape_ty| match normalized_upper(env, r, shape_ty) {
                            upper::T::Shapes(rows) => Some(rows),
                            _ => None,
                        })
                        .collect();
                    let shapes: Vec<srow::T> = row_groups.into_iter().flatten().flatten().collect();
                    if shapes.is_empty() {
                        upper::T::Bottom
                    } else {
                        upper::T::Shapes(shapes)
                    }
                }
            }
        }
    }

    pub fn bound_shape_upper(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        assignment: &assignment::T,
        r: &Reason,
    ) -> upper::T {
        let bound_ty = bound_lookup::combined_upper_bound(cache, env, name, r);
        bound_shape_upper_of_ty(cache, env, bound_ty, assignment, r)
    }

    fn bound_shape_lower_of_ty(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        bound_ty: Ty,
        assignment: &assignment::T,
        r: &Reason,
    ) -> lower::T {
        let bound_ty = typing_env::expand_type(env, bound_ty);
        let bound_ty = bound_lookup::strip_supportdyn(env, bound_ty);
        match get_node(&bound_ty) {
            Ty_::Tshape(shape_ty) => normalized_lower(env, r, shape_ty.clone()),
            Ty_::Tdynamic(_) => lower::T::Shapes(vec![dynamic_row(r)]),
            _ if typing_defs::is_nothing(&bound_ty) => lower::T::Bottom,
            // A lower bound that is a parameter, where that parameter ALREADY has a
            // value. Then it is not an approximation at all: this element is at least
            // whatever that one turned out to be, so use it.
            //
            // Unlike the upper case this creates no ordering requirement, and
            // [type_params_in_lower_bound] deliberately reports no dependency for it.
            // An edge here would make the relation symmetric and turn a single
            // constraint into a cycle. Taking the value only when it happens to be
            // there keeps the coupling without the edge, which is what
            // [where T1 = T2] needs: the two parameters constrain each other in both
            // directions, and with only the upper half enforced one could be given a
            // value below the other.
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) if is_assigned_param(&bound_ty, assignment) => {
                normalized_lower(
                    env,
                    r,
                    ShapeType::ShapeSplat(ShapeTypeSplat {
                        ss_elems: vec![bound_ty.clone()],
                    }),
                )
            }
            _ => {
                let subs = bound_lookup::concrete_subtypes(cache, env, &bound_ty);
                let shapes = shape_types(env, &subs);
                if shapes.is_empty() {
                    lower::T::Bottom
                } else {
                    let row_groups: Vec<Option<Vec<srow::T>>> = shapes
                        .into_iter()
                        .map(|shape_ty| match normalized_lower(env, r, shape_ty) {
                            lower::T::Shapes(rows) => Some(rows),
                            _ => None,
                        })
                        .collect();
                    let shapes: Vec<srow::T> = row_groups.into_iter().flatten().flatten().collect();
                    if shapes.is_empty() {
                        lower::T::Bottom
                    } else {
                        lower::T::Shapes(shapes)
                    }
                }
            }
        }
    }

    pub fn bound_shape_lower(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        assignment: &assignment::T,
        r: &Reason,
    ) -> lower::T {
        let bound_ty = bound_lookup::combined_lower_bound(cache, env, name, r);
        bound_shape_lower_of_ty(cache, env, bound_ty, assignment, r)
    }

    // -- Projecting one field interval -------------------------------------

    fn project_shapes(
        env: &mut Env,
        shapes: &[srow::T],
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        empty: ShapeFieldType,
        combine: fn(ShapeFieldType, ShapeFieldType, &mut Env) -> ShapeFieldType,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        match shapes {
            [] => Ok(empty),
            [first, rest @ ..] => {
                let mut acc = row::proj(env, first, label, assignment)?;
                for shape in rest {
                    let field = row::proj(env, shape, label, assignment)?;
                    acc = combine(acc, field, env);
                }
                Ok(acc)
            }
        }
    }

    fn proj_upper_view(
        env: &mut Env,
        view: upper::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        match view {
            upper::T::Shapes(shapes) => project_shapes(
                env,
                &shapes,
                label,
                assignment,
                ShapeFieldType {
                    optional: true,
                    ty: make_type::mixed(r.clone()),
                },
                field::meet,
            ),
            upper::T::Bottom => Ok(ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            }),
            // A non-shape upper bound constrains nothing: the label may be absent and
            // its type may be anything.
            upper::T::Unconstrained => Ok(ShapeFieldType {
                optional: true,
                ty: make_type::mixed(r.clone()),
            }),
        }
    }

    fn proj_lower_view(
        env: &mut Env,
        view: lower::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        match view {
            lower::T::Shapes(shapes) => project_shapes(
                env,
                &shapes,
                label,
                assignment,
                ShapeFieldType {
                    optional: false,
                    ty: make_type::nothing(r.clone()),
                },
                field::join,
            ),
            lower::T::Bottom => Ok(ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            }),
        }
    }

    fn proj_upper_bound(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        let view = bound_shape_upper(cache, env, name, assignment, r);
        proj_upper_view(env, view, label, assignment, r)
    }

    pub fn upper_field_bound(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        proj_upper_bound(cache, env, name, label, assignment, r)
    }

    fn proj_lower_bound(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<ShapeFieldType, missing_assignment::T> {
        let view = bound_shape_lower(cache, env, name, assignment, r);
        proj_lower_view(env, view, label, assignment, r)
    }

    /// `(lower, upper)`: the lower bound is projected first.
    pub fn field_bounds(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        name: &splat_elem::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<(ShapeFieldType, ShapeFieldType), missing_assignment::T> {
        let lower = proj_lower_bound(cache, env, name, label, assignment, r)?;
        let upper = proj_upper_bound(cache, env, name, label, assignment, r)?;
        Ok((lower, upper))
    }

    // -- Bounds for a proven-equal component -------------------------------

    /// Which bound of a member `fold_equality_bounds` reads (`~get_bounds` and
    /// `~project` in the OCaml, which are given together).
    #[derive(Clone, Copy)]
    enum Direction {
        Lower,
        Upper,
    }

    fn fold_equality_bounds(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
        direction: Direction,
        combine: fn(ShapeFieldType, ShapeFieldType, &mut Env) -> ShapeFieldType,
        init: field::T,
    ) -> Result<field::T, missing_assignment::T> {
        let preferred = splat_elem::set::inter(members, preferred_members);
        let remaining = splat_elem::set::diff(members, &preferred);
        let mut ordered = splat_elem::set::elements(&preferred);
        ordered.extend(splat_elem::set::elements(&remaining));
        let mut acc = init;
        for member in &ordered {
            let bounds = match direction {
                Direction::Lower => bound_lookup::lower_bounds(cache, env, member, r),
                Direction::Upper => bound_lookup::upper_bounds(cache, env, member, r),
            };
            for bound in bounds {
                // `is_direct_member`
                let bound = typing_env::expand_type(env, bound);
                let is_member = match get_node(&bound) {
                    Ty_::Tgeneric(_) => splat_elem::set::mem(&bound, members),
                    _ => false,
                };
                if is_member {
                    continue;
                }
                let field = match direction {
                    Direction::Lower => {
                        let view = bound_shape_lower_of_ty(cache, env, bound, assignment, r);
                        proj_lower_view(env, view, label, assignment, r)
                    }
                    Direction::Upper => {
                        let view = bound_shape_upper_of_ty(cache, env, bound, assignment, r);
                        proj_upper_view(env, view, label, assignment, r)
                    }
                }?;
                acc = combine(acc, field, env);
            }
        }
        Ok(acc)
    }

    fn lower_field_bound_for_equality(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<field::T, missing_assignment::T> {
        fold_equality_bounds(
            cache,
            env,
            preferred_members,
            members,
            label,
            assignment,
            r,
            Direction::Lower,
            field::join,
            ShapeFieldType {
                optional: false,
                ty: make_type::nothing(r.clone()),
            },
        )
    }

    pub fn upper_field_bound_for_equality(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<field::T, missing_assignment::T> {
        fold_equality_bounds(
            cache,
            env,
            preferred_members,
            members,
            label,
            assignment,
            r,
            Direction::Upper,
            field::meet,
            ShapeFieldType {
                optional: true,
                ty: make_type::mixed(r.clone()),
            },
        )
    }

    pub fn field_bounds_for_equality(
        cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<(field::T, field::T), missing_assignment::T> {
        let lower = lower_field_bound_for_equality(
            cache,
            env,
            preferred_members,
            members,
            label,
            assignment,
            r,
        )?;
        let upper = upper_field_bound_for_equality(
            cache,
            env,
            preferred_members,
            members,
            label,
            assignment,
            r,
        )?;
        Ok((lower, upper))
    }
}

// -- Structural dependency analysis -------------------------------------
//
// An edge [source -> target] means that calculating source's field bounds can
// require target's chosen field, so target must be assigned first. Analysis
// reads only cached structural summaries, then traverses each reachable node
// and edge once. Dependency kinds retain enough evidence to distinguish a
// direct mutual-subtyping cycle from a recursive field computation.
// -------------------------------------------------------------------------
pub mod analysis {
    use super::*;

    pub mod dependency {
        use super::*;

        /// Why source's field-bound evaluation can require target.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Kind {
            /// A whole upper constraint [source <: target]. Cycles containing only
            /// these edges between type parameters prove mutual subtyping.
            DirectUpper,
            /// Target was found through a compound upper bound. This proves
            /// dependency, but not whole-type equality.
            IndirectUpper,
            /// A shape in source's upper bounds spreads target.
            NestedUpper,
            /// A shape in source's lower bounds spreads target.
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

        /// Return one concrete cycle for diagnostics. Every dependency stored in a
        /// cyclic component is internal to that component, so a depth-first search
        /// from an edge's target can recover a path back to its source.
        pub fn dependency_cycle(info: &T) -> Vec<dependency::T> {
            fn same(left: &Ty, right: &Ty) -> bool {
                splat_elem::compare(left, right) == Ordering::Equal
            }
            fn path_to(
                info: &T,
                source: &Ty,
                target: &Ty,
                seen: &splat_elem::set::T,
            ) -> Option<Vec<dependency::T>> {
                if same(source, target) {
                    Some(vec![])
                } else {
                    // `outgoing source`
                    info.dependencies
                        .iter()
                        .filter(|dependency| same(source, &dependency.source))
                        .find_map(|dependency| {
                            let next = dependency::target(dependency);
                            if splat_elem::set::mem(&next, seen) {
                                None
                            } else {
                                let seen = splat_elem::set::add(next.clone(), seen);
                                path_to(info, &next, target, &seen).map(|path| {
                                    let mut cycle = vec![dependency.clone()];
                                    cycle.extend(path);
                                    cycle
                                })
                            }
                        })
                }
            }
            info.dependencies
                .iter()
                .find_map(|dependency| {
                    let source = dependency::source(dependency);
                    let target = dependency::target(dependency);
                    path_to(
                        info,
                        &target,
                        &source,
                        &splat_elem::set::singleton(target.clone()),
                    )
                    .map(|path| {
                        let mut cycle = vec![dependency.clone()];
                        cycle.extend(path);
                        cycle
                    })
                })
                .unwrap_or_default()
        }
    }

    pub mod component {
        use super::*;

        /// One strongly connected component. Only direct reciprocal
        /// type-parameter constraints prove equality; every other cyclic
        /// component is unsupported.
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

    mod bound_summary {
        use super::*;

        /// Assignment-independent facts about one element's bounds. Constructing a
        /// summary may expand types and inspect constructors, but must never
        /// normalize a shape, project a row, perform subtyping, evaluate exact
        /// field bounds, or enumerate corners.
        #[derive(Clone)]
        pub struct T {
            pub dependencies: Vec<dependency::T>,
            pub labels: LabelSet,
        }
    }

    pub mod cache {
        use super::*;

        pub struct T {
            pub(super) bound_summaries: env_memo::Table<bound_summary::T>,
        }

        pub fn create() -> T {
            T {
                bound_summaries: env_memo::Table::new(),
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub(super) components: Vec<component::T>,
        pub(super) dependencies: Vec<dependency::T>,
        pub(super) node_visits: isize,
        pub(super) edge_visits: isize,
    }

    pub fn components(analysis: &T) -> Vec<component::T> {
        analysis.components.clone()
    }

    pub fn dependencies(analysis: &T) -> Vec<dependency::T> {
        analysis.dependencies.clone()
    }

    pub fn node_visits(analysis: &T) -> isize {
        analysis.node_visits
    }

    pub fn edge_visits(analysis: &T) -> isize {
        analysis.edge_visits
    }

    // -- Structural bound summaries ---------------------------------------

    /// Shape normalization may ask whether an opaque operand is [nothing]. That
    /// invokes subtyping and can re-enter corner checking once for every
    /// dependency path. Collect only dependencies and explicit labels directly
    /// from localized type syntax.
    ///
    /// (`rev_dependencies` is consed onto in the OCaml and reversed at the
    /// end; here the dependencies are pushed, in order.)
    struct Scan {
        dependencies: Vec<dependency::T>,
        labels: LabelSet,
    }

    fn add_dependency(source: &Ty, target: Ty, kind: dependency::Kind, scan: &mut Scan) {
        scan.dependencies
            .push(dependency::make(source.clone(), target, kind))
    }

    fn add_labels(fields: &TShapeMap<ShapeFieldType>, scan: &mut Scan) {
        // `TShapeMap.fold`: in the order of the keys.
        for label in fields.keys() {
            scan.labels = stdlib_set::add(Label(label.clone()), &scan.labels);
        }
    }

    fn scan_shape(
        source: &Ty,
        kind: dependency::Kind,
        env: &mut Env,
        scan: &mut Scan,
        shape: &ShapeType,
    ) {
        match shape {
            ShapeType::ShapeSimple(ShapeTypeSimple { fields, .. }) => add_labels(fields, scan),
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => {
                scan_nested_tys(source, kind, env, scan, ss_elems)
            }
        }
    }

    fn scan_nested_ty(
        source: &Ty,
        kind: dependency::Kind,
        env: &mut Env,
        scan: &mut Scan,
        ty: &Ty,
    ) {
        let ty = typing_env::expand_type(env, ty.clone());
        let ty = bound_lookup::strip_supportdyn(env, ty);
        match get_node(&ty) {
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => add_dependency(source, ty.clone(), kind, scan),
            Ty_::Tshape(shape_ty) => scan_shape(source, kind, env, scan, shape_ty),
            Ty_::Tunion(tys) | Ty_::Tintersection(tys) => {
                scan_nested_tys(source, kind, env, scan, tys)
            }
            _ => {}
        }
    }

    fn scan_nested_tys(
        source: &Ty,
        kind: dependency::Kind,
        env: &mut Env,
        scan: &mut Scan,
        tys: &[Ty],
    ) {
        for ty in tys {
            scan_nested_ty(source, kind, env, scan, ty)
        }
    }

    fn scan_indirect_upper_ty(source: &Ty, env: &mut Env, scan: &mut Scan, ty: &Ty) {
        let ty = typing_env::expand_type(env, ty.clone());
        let ty = bound_lookup::strip_supportdyn(env, ty);
        match get_node(&ty) {
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                add_dependency(source, ty.clone(), dependency::Kind::IndirectUpper, scan)
            }
            Ty_::Tshape(shape_ty) => {
                scan_shape(source, dependency::Kind::NestedUpper, env, scan, shape_ty)
            }
            Ty_::Tunion(tys) | Ty_::Tintersection(tys) => {
                for ty in tys {
                    scan_indirect_upper_ty(source, env, scan, ty)
                }
            }
            _ => {}
        }
    }

    fn scan_upper_bound(
        bounds_cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        source: &Ty,
        scan: &mut Scan,
        bound: Ty,
    ) {
        let bound = typing_env::expand_type(env, bound);
        match get_node(&bound) {
            Ty_::Tgeneric(_) => {
                add_dependency(source, bound.clone(), dependency::Kind::DirectUpper, scan)
            }
            Ty_::Tnewtype(name, _, _) if !is_supportdyn_name(name) => {
                add_dependency(source, bound.clone(), dependency::Kind::DirectUpper, scan)
            }
            _ => {
                let bound = bound_lookup::strip_supportdyn(env, bound.clone());
                let supers = bound_lookup::concrete_supertypes(bounds_cache, env, &bound);
                for super_ in &supers {
                    scan_indirect_upper_ty(source, env, scan, super_)
                }
            }
        }
    }

    fn scan_lower_bound(
        bounds_cache: &mut bound_lookup::cache::T,
        env: &mut Env,
        source: &Ty,
        scan: &mut Scan,
        bound: Ty,
    ) {
        let bound = typing_env::expand_type(env, bound);
        let bound = bound_lookup::strip_supportdyn(env, bound);
        let subs = bound_lookup::concrete_subtypes(bounds_cache, env, &bound);
        for sub in subs {
            let sub = bound_lookup::strip_supportdyn(env, sub);
            match get_node(&sub) {
                Ty_::Tshape(shape_ty) => {
                    scan_shape(source, dependency::Kind::NestedLower, env, scan, shape_ty)
                }
                _ => {}
            }
        }
    }

    fn summary_from(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> bound_summary::T {
        env_memo::memoize_value(&mut cache.bound_summaries, env, source, || {
            // The environment is threaded through, and dropped at the end.
            let env = &mut env.clone();
            let mut scan = Scan {
                dependencies: vec![],
                labels: stdlib_set::empty(),
            };
            let upper_bounds = bound_lookup::upper_bounds(bounds_cache, env, source, r);
            for bound in upper_bounds {
                scan_upper_bound(bounds_cache, env, source, &mut scan, bound)
            }
            let lower_bounds = bound_lookup::lower_bounds(bounds_cache, env, source, r);
            for bound in lower_bounds {
                scan_lower_bound(bounds_cache, env, source, &mut scan, bound)
            }
            bound_summary::T {
                dependencies: scan.dependencies,
                labels: scan.labels,
            }
        })
    }

    /// The cached structural summary is the sole dependency representation.
    /// Graph discovery therefore cannot recursively invoke corner checking.
    fn dependencies_from(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> Vec<dependency::T> {
        summary_from(bounds_cache, cache, env, source, r).dependencies
    }

    fn labels_from(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> LabelSet {
        summary_from(bounds_cache, cache, env, source, r).labels
    }

    fn targets(dependencies: &[dependency::T], f: impl Fn(dependency::Kind) -> bool) -> Vec<Ty> {
        let mut acc = splat_elem::set::empty();
        for edge in dependencies {
            if f(dependency::kind(edge)) {
                acc = splat_elem::set::add(dependency::target(edge), &acc)
            }
        }
        splat_elem::set::elements(&acc)
    }

    pub fn type_params_in_upper_bound(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> Vec<Ty> {
        targets(
            &dependencies_from(bounds_cache, cache, env, source, r),
            |kind| match kind {
                dependency::Kind::DirectUpper
                | dependency::Kind::IndirectUpper
                | dependency::Kind::NestedUpper => true,
                dependency::Kind::NestedLower => false,
            },
        )
    }

    pub fn type_params_in_lower_bound(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> Vec<Ty> {
        targets(
            &dependencies_from(bounds_cache, cache, env, source, r),
            |kind| match kind {
                dependency::Kind::NestedLower => true,
                dependency::Kind::DirectUpper
                | dependency::Kind::IndirectUpper
                | dependency::Kind::NestedUpper => false,
            },
        )
    }

    pub fn type_params_in_bounds(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        source: &Ty,
        r: &Reason,
    ) -> Vec<Ty> {
        targets(
            &dependencies_from(bounds_cache, cache, env, source, r),
            |_| true,
        )
    }

    // -- Reachability and SCC classification -------------------------------

    /// [roots] are caller-supplied starting elements, normally the elements live
    /// in either surface row at one label. They are not graph nodes with no
    /// incoming edge.
    pub fn closure(
        bounds_cache: &mut bound_lookup::cache::T,
        cache: &mut cache::T,
        env: &Env,
        names: &splat_elem::set::T,
        r: &Reason,
    ) -> splat_elem::set::T {
        // `aux worklist acc`: the head of the worklist is the last element here.
        let mut worklist: Vec<Ty> = splat_elem::set::elements(names);
        worklist.reverse();
        let mut acc = splat_elem::set::empty();
        while let Some(next) = worklist.pop() {
            if splat_elem::set::mem(&next, &acc) {
                continue;
            }
            let delta = type_params_in_bounds(bounds_cache, cache, env, &next, r);
            // `delta @ rest`
            worklist.extend(delta.into_iter().rev());
            acc = splat_elem::set::add(next, &acc);
        }
        acc
    }

    /// The `ref`s of `analyze`, and what `visit` needs.
    struct Tarjan<'a> {
        bounds_cache: &'a mut bound_lookup::cache::T,
        analysis_cache: &'a mut cache::T,
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
        let outgoing = dependencies_from(st.bounds_cache, st.analysis_cache, st.env, source, st.r);
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

    /// Tarjan's traversal returns dependency-first strongly connected
    /// components. Since summaries cannot invoke corner checking, its work is
    /// linear in the reachable nodes and dependency edges.
    pub fn analyze(
        bounds_cache: &mut bound_lookup::cache::T,
        analysis_cache: &mut cache::T,
        env: &Env,
        roots: &splat_elem::set::T,
        r: &Reason,
    ) -> T {
        let mut st = Tarjan {
            bounds_cache,
            analysis_cache,
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
        T {
            components,
            dependencies,
            node_visits: st.node_visits,
            edge_visits: st.edge_visits,
        }
    }

    // -- Label discovery ----------------------------------------------------

    /// Label discovery cannot begin with per-label liveness: the labels must be
    /// known before liveness can be calculated. Start from every spread element
    /// written in either surface row, follow its dependency closure, and collect
    /// labels from all reachable summaries. Search later computes a smaller live
    /// root set separately for each discovered label.
    pub mod labels {
        use super::*;

        fn bound_label_set(
            bounds_cache: &mut bound_lookup::cache::T,
            analysis_cache: &mut cache::T,
            env: &Env,
            names: Vec<Ty>,
            r: &Reason,
        ) -> LabelSet {
            let all = closure(
                bounds_cache,
                analysis_cache,
                env,
                &splat_elem::set::of_list(names),
                r,
            );
            splat_elem::set::fold(
                |name, acc: LabelSet| {
                    stdlib_set::union(
                        &acc,
                        &labels_from(bounds_cache, analysis_cache, env, name, r),
                    )
                },
                &all,
                stdlib_set::empty(),
            )
        }

        pub fn subrow_label_set(
            bounds_cache: &mut bound_lookup::cache::T,
            analysis_cache: &mut cache::T,
            env: &Env,
            sub: &srow::T,
            super_: &srow::T,
            r: &Reason,
        ) -> LabelSet {
            let mut params = row::spread_elements(sub);
            params.extend(row::spread_elements(super_));
            // The arguments of the outer `TShapeSet.union` are evaluated right to
            // left: `bound_label_set` first (`Row.label_set` has no effect).
            let bound = bound_label_set(bounds_cache, analysis_cache, env, params, r);
            stdlib_set::union(
                &stdlib_set::union(&row::label_set(sub), &row::label_set(super_)),
                &bound,
            )
        }

        pub fn subrow_labels(
            bounds_cache: &mut bound_lookup::cache::T,
            analysis_cache: &mut cache::T,
            env: &Env,
            sub: &srow::T,
            super_: &srow::T,
            r: &Reason,
        ) -> Vec<Option<TShapeField>> {
            let mut labels = vec![None];
            labels.extend(
                stdlib_set::elements(&subrow_label_set(
                    bounds_cache,
                    analysis_cache,
                    env,
                    sub,
                    super_,
                    r,
                ))
                .into_iter()
                .map(|Label(l)| Some(l)),
            );
            labels
        }
    }
}

// Public compatibility aliases. The representations themselves are owned by
// dependency analysis.
pub use analysis::component;
pub use analysis::cycle_info;
pub use analysis::dependency;

/// The outcome of traversing a corner plan. [Empty] means that every branch
/// encountered an uninhabited field interval, so there is no checking
/// obligation. [Unsupported_cycle] preserves facts for the caller's error
/// construction rather than rendering a message here.
#[derive(Clone, Debug)]
pub enum Computation<A> {
    /// At least one complete assignment was evaluated.
    Computed(A),
    /// Every branch had an uninhabited field interval.
    Empty,
    /// The cycle facts needed by the caller's error construction.
    UnsupportedCycle(cycle_info::T),
}

pub mod cache {
    use super::*;

    pub struct T {
        pub(super) bounds: bound_lookup::cache::T,
        pub(super) analysis: analysis::cache::T,
    }

    /// Create a fresh cache for one splat operation.
    pub fn create() -> T {
        T {
            bounds: bound_lookup::cache::create(),
            analysis: analysis::cache::create(),
        }
    }
}

// -- Compiling an executable plan ----------------------------------------
//
// Analysis describes every reachable component, including unsupported
// cycles. A plan either rejects such a cycle or turns the analysis into
// dependency-ordered singleton and proven-equality groups. Every dependency
// between distinct groups points to an earlier group, and each element occurs
// in exactly one group.
// -------------------------------------------------------------------------
mod plan {
    use super::*;

    #[derive(Clone, Debug)]
    pub enum Group {
        One(splat_elem::T),
        Equal(cycle_info::T),
    }

    pub struct T {
        groups: Vec<Group>,
        /// Search cannot prune these parameters' corners using only their visible
        /// positions in the surface rows: another group's bounds depend on them.
        depended_on: splat_elem::set::T,
    }

    pub fn groups(plan: &T) -> &[Group] {
        &plan.groups
    }

    /// Parameters whose assigned field can affect another group's bounds.
    pub fn depended_on(plan: &T) -> &splat_elem::set::T {
        &plan.depended_on
    }

    /// Compatibility view for tests and callers which still request a flat
    /// topological order. Search consumes the component plan below.
    pub fn order(
        cache: &mut cache::T,
        env: &Env,
        roots: &splat_elem::set::T,
        r: &Reason,
    ) -> Vec<Ty> {
        let analysis = analysis::analyze(&mut cache.bounds, &mut cache.analysis, env, roots, r);
        analysis::components(&analysis)
            .iter()
            .flat_map(|component| splat_elem::set::elements(&component::members(component)))
            .collect()
    }

    /// Compile dependency analysis into the only representation consumed by
    /// search: dependency-ordered singleton or proven-equality groups.
    pub fn of_analysis(analysis: &analysis::T) -> Result<T, cycle_info::T> {
        let mut depended_on = splat_elem::set::empty();
        for dependency in analysis::dependencies(analysis).iter() {
            depended_on = splat_elem::set::add(dependency::target(dependency), &depended_on);
        }
        // `groups` is consed onto and reversed at the end: here in order.
        let mut groups = vec![];
        for component in analysis::components(analysis) {
            match component {
                component::T::Acyclic(element) => groups.push(Group::One(element)),
                component::T::ProvenEqual(info) => groups.push(Group::Equal(info)),
                component::T::UnsupportedCycle(info) => return Err(info),
            }
        }
        Ok(T {
            groups,
            depended_on,
        })
    }
}

// -- Corner search -------------------------------------------------------
//
// Search evaluates groups in plan order. Bounds for the current group may
// read fields assigned to earlier groups, so its available corners are
// calculated separately inside each partial-assignment branch.
//
// This Cartesian product is intentionally exponential when its leaves are
// observably different. It is distinct from the accidental exponential
// dependency discovery prevented by structural summaries. The pruning below
// selects one extremum only when row position and dependency information make
// it dominate every omitted corner.
// -------------------------------------------------------------------------
mod search {
    use super::*;

    // -- Dynamic masking and corner pruning --------------------------------

    pub mod masking {
        use super::*;

        /// Whether rightward spread elements definitely overwrite [key], leave it
        /// potentially relevant at every allowed corner, or vary across their own
        /// corners. [Unmasked] does not mean visible in every value; it means that
        /// [key] cannot be discarded.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum T {
            Masked,
            Unmasked,
            Unknown,
        }

        /// In [shape(...key, ...other)], [other] definitely masks [key] at [label]
        /// when its upper field is required. If both field bounds are optional,
        /// [key] remains potentially relevant. Required lower and optional upper
        /// bounds make the answer [Unknown].
        fn of_splat(
            cache: &mut cache::T,
            env: &Env,
            ss_elems: &[Ty],
            label: Option<&TShapeField>,
            key: &Ty,
            assignment: &assignment::T,
            r: &Reason,
        ) -> Result<T, missing_assignment::T> {
            // `aux (List.rev ss_elems) Unmasked`
            let mut acc = T::Unmasked;
            for ty in ss_elems.iter().rev() {
                match get_node(ty) {
                    Ty_::Tgeneric(_) | Ty_::Tnewtype(..)
                        if splat_elem::compare(ty, key) == Ordering::Equal =>
                    {
                        return Ok(acc);
                    }
                    Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                        // `let (_env, bounds) = ...`: each from `env`.
                        let (lower, upper) = field_bounds::field_bounds(
                            &mut cache.bounds,
                            &mut env.clone(),
                            ty,
                            label,
                            assignment,
                            r,
                        )?;
                        if field::is_required(&upper) {
                            return Ok(T::Masked);
                        } else if field::is_required(&lower) {
                            acc = T::Unknown
                        }
                    }
                    _ => {}
                }
            }
            Ok(T::Unknown)
        }

        pub fn of_row(
            cache: &mut cache::T,
            env: &Env,
            row: &srow::T,
            label: Option<&TShapeField>,
            key: &Ty,
            assignment: &assignment::T,
            r: &Reason,
        ) -> Result<T, missing_assignment::T> {
            match row_view(row) {
                RowView::Bottom => Ok(T::Unknown),
                RowView::Simple(_) => Ok(T::Unknown),
                RowView::Elements(ss_elems) => {
                    of_splat(cache, env, &ss_elems, label, key, assignment, r)
                }
            }
        }
    }

    /// Enumerate corner assignments in dependency order. Bound resolution is
    /// cached within one shape-splat operation, but every retained assignment
    /// path is traversed.
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
    ) -> Result<field::corners::T, missing_assignment::T> {
        let (lower, upper) =
            field_bounds::field_bounds(&mut cache.bounds, env, key, label, assignment, r)?;
        // A free parameter affects no other parameter's bounds, so its visible
        // row position alone can determine the extremal corner to check.
        let is_free = !splat_elem::set::mem(key, depended_on);
        let in_sub = splat_elem::set::mem(key, live_sub);
        let in_super = splat_elem::set::mem(key, live_super);
        if is_free && in_sub && !in_super {
            Ok(field::corners::T::Values(vec![upper]))
        } else if is_free && (!in_sub) && in_super {
            Ok(field::corners::T::Values(vec![lower]))
        } else if is_free && in_sub && in_super {
            // `let m_sub = ... and m_super = ... in`: in this order.
            let m_sub = masking::of_row(cache, env, sub, label, key, assignment, r);
            let m_super = masking::of_row(cache, env, super_, label, key, assignment, r);
            match (m_sub, m_super) {
                (Err(missing), _) | (_, Err(missing)) => Err(missing),
                (Ok(masking::T::Masked), _) => Ok(field::corners::T::Values(vec![lower])),
                (_, Ok(masking::T::Masked)) => Ok(field::corners::T::Values(vec![upper])),
                // Both occurrences use the same assignment. If the supertype
                // occurrence remains relevant and the lower field is optional, that
                // lower choice exposes every unshared subtype contribution. Raising
                // the field adds the same shared contribution to both projections, so
                // it cannot create a harder case.
                (_, Ok(masking::T::Unmasked)) if field::is_optional(&lower) => {
                    Ok(field::corners::T::Values(vec![lower]))
                }
                (Ok(_), Ok(_)) => Ok(field::corners::of_bounds(lower, upper)),
            }
        } else {
            Ok(field::corners::of_bounds(lower, upper))
        }
    }

    fn bounds_for_group(
        cache: &mut cache::T,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: &Reason,
        group: &plan::Group,
    ) -> Result<(field::T, field::T), missing_assignment::T> {
        match group {
            plan::Group::One(key) => {
                field_bounds::field_bounds(&mut cache.bounds, env, key, label, assignment, r)
            }
            plan::Group::Equal(info) => field_bounds::field_bounds_for_equality(
                &mut cache.bounds,
                env,
                preferred_members,
                &cycle_info::members(info),
                label,
                assignment,
                r,
            ),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn corners_for_group(
        cache: &mut cache::T,
        env: &mut Env,
        depended_on: &splat_elem::set::T,
        live_sub: &splat_elem::set::T,
        live_super: &splat_elem::set::T,
        sub: &srow::T,
        super_: &srow::T,
        preferred_members: &splat_elem::set::T,
        label: Option<&TShapeField>,
        group: &plan::Group,
        assignment: &assignment::T,
        r: &Reason,
    ) -> Result<field::corners::T, missing_assignment::T> {
        match group {
            plan::Group::One(key) => corners_for(
                cache,
                env,
                depended_on,
                live_sub,
                live_super,
                sub,
                super_,
                label,
                key,
                assignment,
                r,
            ),
            plan::Group::Equal(_) => {
                let (lower, upper) = bounds_for_group(
                    cache,
                    env,
                    preferred_members,
                    label,
                    assignment,
                    r,
                    group,
                )?;
                Ok(field::corners::of_bounds(lower, upper))
            }
        }
    }

    fn assign_group(
        group: &plan::Group,
        field: field::T,
        assignment: &assignment::T,
    ) -> assignment::T {
        match group {
            plan::Group::One(member) => splat_elem::map::add(member.clone(), field, assignment),
            plan::Group::Equal(info) => splat_elem::set::fold(
                |member, assignment: assignment::T| {
                    splat_elem::map::add(member.clone(), field.clone(), &assignment)
                },
                &cycle_info::members(info),
                assignment.clone(),
            ),
        }
    }

    // -- Traversing the Cartesian product ----------------------------------

    /// What `fold_plan` is given: `~corners`, `~leaf`, `~empty` and
    /// `~combine`.
    ///
    /// `combine (env, result) next` has the same shape in both of its uses: an
    /// error on the left is returned without running `next`; otherwise `next`
    /// runs from the environment of the left result, its error is returned,
    /// and its value is merged with the left one. `merge` is that last step:
    /// `env` is the environment after `next`, `env_before` the one it started
    /// from.
    trait Fold<R> {
        fn corners(
            &mut self,
            env: &mut Env,
            group: &plan::Group,
            assignment: &assignment::T,
        ) -> Result<field::corners::T, missing_assignment::T>;

        fn leaf(
            &mut self,
            assignment: &assignment::T,
            env: &mut Env,
        ) -> Result<R, missing_assignment::T>;

        fn empty(&mut self, env: &mut Env) -> Result<R, missing_assignment::T>;

        fn merge(&mut self, env_before: Env, env: &mut Env, left: R, right: R) -> R;
    }

    /// Traverse one dependency-ordered plan. [corners] chooses the candidates for
    /// a group; [leaf], [empty], and [combine] interpret the same traversal for
    /// ground checking or for collecting inference assignments.
    fn fold_plan<R>(
        folder: &mut dyn Fold<R>,
        groups: &[plan::Group],
        assignment: &assignment::T,
        env: &mut Env,
    ) -> Result<R, missing_assignment::T> {
        match groups {
            [] => folder.leaf(assignment, env),
            [group, rest @ ..] => match folder.corners(env, group, assignment)? {
                field::corners::T::Inverted => folder.empty(env),
                field::corners::T::Values(fields) => {
                    let mut fields = fields.into_iter();
                    let first = match fields.next() {
                        None => panic!("Field.Corners.Values must be nonempty"),
                        Some(first) => first,
                    };
                    let mut acc = fold_plan(
                        folder,
                        rest,
                        &assign_group(group, first, assignment),
                        env,
                    );
                    for field in fields {
                        acc = match acc {
                            Err(missing) => Err(missing),
                            Ok(left) => {
                                let env_before = env.clone();
                                match fold_plan(
                                    folder,
                                    rest,
                                    &assign_group(group, field, assignment),
                                    env,
                                ) {
                                    Err(missing) => Err(missing),
                                    Ok(right) => Ok(folder.merge(env_before, env, left, right)),
                                }
                            }
                        };
                    }
                    acc
                }
            },
        }
    }

    struct Check<'a, A> {
        cache: &'a mut cache::T,
        plan: &'a plan::T,
        live_sub: &'a splat_elem::set::T,
        live_super: &'a splat_elem::set::T,
        preferred_members: &'a splat_elem::set::T,
        sub: &'a srow::T,
        super_: &'a srow::T,
        label: Option<&'a TShapeField>,
        r: &'a Reason,
        init: &'a dyn Fn(&mut Env) -> A,
        conj: &'a dyn Fn(&mut Env, A, &mut dyn FnMut(&mut Env) -> A) -> A,
        f: &'a mut dyn FnMut(&mut Env, ShapeFieldType, ShapeFieldType) -> A,
    }

    impl<A> Fold<(A, bool)> for Check<'_, A> {
        fn corners(
            &mut self,
            env: &mut Env,
            group: &plan::Group,
            assignment: &assignment::T,
        ) -> Result<field::corners::T, missing_assignment::T> {
            corners_for_group(
                self.cache,
                env,
                plan::depended_on(self.plan),
                self.live_sub,
                self.live_super,
                self.sub,
                self.super_,
                self.preferred_members,
                self.label,
                group,
                assignment,
                self.r,
            )
        }

        /// `finish`
        fn leaf(
            &mut self,
            assignment: &assignment::T,
            env: &mut Env,
        ) -> Result<(A, bool), missing_assignment::T> {
            let sub = row::proj(env, self.sub, self.label, assignment)?;
            let super_ = row::proj(env, self.super_, self.label, assignment)?;
            let value = (self.f)(env, sub, super_);
            Ok((value, true))
        }

        fn empty(&mut self, env: &mut Env) -> Result<(A, bool), missing_assignment::T> {
            let value = (self.init)(env);
            Ok((value, false))
        }

        /// `conj (env_before, left) (fun _ -> (env_after, right))`
        fn merge(
            &mut self,
            env_before: Env,
            env: &mut Env,
            (left, left_completed): (A, bool),
            (right, right_completed): (A, bool),
        ) -> (A, bool) {
            let env_after = std::mem::replace(env, env_before);
            let mut right = Some(right);
            let value = (self.conj)(env, left, &mut |env: &mut Env| {
                *env = env_after.clone();
                right
                    .take()
                    .expect("the continuation of `conj` is called at most once")
            });
            (value, left_completed || right_completed)
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
    ) -> Result<Computation<A>, missing_assignment::T> {
        // `let live_sub = ... and live_super = ... in` (no effect)
        let live_sub = splat_elem::set::of_list(row::live_spreads(sub, label));
        let live_super = splat_elem::set::of_list(row::live_spreads(super_, label));
        let all_live = splat_elem::set::union(&live_sub, &live_super);
        let analysis =
            analysis::analyze(&mut cache.bounds, &mut cache.analysis, env, &all_live, r);
        match plan::of_analysis(&analysis) {
            Err(info) => Ok(Computation::UnsupportedCycle(info)),
            Ok(plan) => {
                let preferred_members = splat_elem::set::union(&live_sub, &live_super);
                let mut check = Check {
                    cache,
                    plan: &plan,
                    live_sub: &live_sub,
                    live_super: &live_super,
                    preferred_members: &preferred_members,
                    sub,
                    super_,
                    label,
                    r,
                    init,
                    conj,
                    f,
                };
                let (value, completed) = fold_plan(
                    &mut check,
                    plan::groups(&plan),
                    &splat_elem::map::empty(),
                    env,
                )?;
                if completed {
                    Ok(Computation::Computed(value))
                } else {
                    Ok(Computation::Empty)
                }
            }
        }
    }

    // -- Materializing assignments for inference and tests ----------------

    struct Collect<'a> {
        cache: &'a mut cache::T,
        roots: &'a splat_elem::set::T,
        label: Option<&'a TShapeField>,
        r: &'a Reason,
    }

    /// (The OCaml collects difference lists; here the assignments, in the
    /// same order.)
    impl Fold<Vec<assignment::T>> for Collect<'_> {
        fn corners(
            &mut self,
            env: &mut Env,
            group: &plan::Group,
            assignment: &assignment::T,
        ) -> Result<field::corners::T, missing_assignment::T> {
            let (lower, upper) = bounds_for_group(
                self.cache,
                env,
                self.roots,
                self.label,
                assignment,
                self.r,
                group,
            )?;
            Ok(field::corners::of_bounds(lower, upper))
        }

        fn leaf(
            &mut self,
            assignment: &assignment::T,
            _env: &mut Env,
        ) -> Result<Vec<assignment::T>, missing_assignment::T> {
            Ok(vec![assignment.clone()])
        }

        fn empty(&mut self, _env: &mut Env) -> Result<Vec<assignment::T>, missing_assignment::T> {
            Ok(vec![])
        }

        fn merge(
            &mut self,
            _env_before: Env,
            _env: &mut Env,
            mut left: Vec<assignment::T>,
            right: Vec<assignment::T>,
        ) -> Vec<assignment::T> {
            left.extend(right);
            left
        }
    }

    pub fn assignments(
        cache: &mut cache::T,
        env: &mut Env,
        roots: &splat_elem::set::T,
        label: Option<&TShapeField>,
        r: &Reason,
    ) -> Result<Computation<Vec<assignment::T>>, missing_assignment::T> {
        let analysis = analysis::analyze(&mut cache.bounds, &mut cache.analysis, env, roots, r);
        match plan::of_analysis(&analysis) {
            Err(info) => Ok(Computation::UnsupportedCycle(info)),
            Ok(plan) => {
                let mut collect = Collect {
                    cache,
                    roots,
                    label,
                    r,
                };
                let assignments = fold_plan(
                    &mut collect,
                    plan::groups(&plan),
                    &splat_elem::map::empty(),
                    env,
                )?;
                if assignments.is_empty() {
                    Ok(Computation::Empty)
                } else {
                    Ok(Computation::Computed(assignments))
                }
            }
        }
    }
}

// -- Inference helpers -----------------------------------------------------
mod inference {
    use super::*;

    /// Spread type-variable ids at spread position, in source order
    pub fn spread_tyvar_ids(row: &srow::T) -> Vec<tvid::T> {
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
    pub fn partition_at_tyvar(row: &srow::T, v: tvid::T) -> Option<(Vec<Ty>, Vec<Ty>)> {
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
    pub fn solve_spread_vars(env: &mut Env, r: &Reason, row: &srow::T) -> srow::Normalized {
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

// -- Resolve a splat to a simple shape for reads ---------------------------
// Unsupported cyclic components are assigned [Opt mixed]; projecting the
// original row afterward preserves precision from concrete fields that mask
// them on the right.
// --------------------------------------------------------------------------
mod read_resolution {
    use super::*;

    fn assign_field(
        assignment: &assignment::T,
        members: &splat_elem::set::T,
        field: &field::T,
    ) -> assignment::T {
        splat_elem::set::fold(
            |member, assignment: assignment::T| {
                splat_elem::map::add(member.clone(), field.clone(), &assignment)
            },
            members,
            assignment.clone(),
        )
    }

    fn upper_for_component(
        cache: &mut cache::T,
        r: &Reason,
        env: &mut Env,
        preferred_members: &splat_elem::set::T,
        assignment: &assignment::T,
        label: Option<&TShapeField>,
        component: &component::T,
    ) -> Result<assignment::T, missing_assignment::T> {
        match component {
            component::T::Acyclic(key) => {
                let upper = field_bounds::upper_field_bound(
                    &mut cache.bounds,
                    env,
                    key,
                    label,
                    assignment,
                    r,
                )?;
                Ok(splat_elem::map::add(key.clone(), upper, assignment))
            }
            component::T::ProvenEqual(info) => {
                let members = cycle_info::members(info);
                let upper = field_bounds::upper_field_bound_for_equality(
                    &mut cache.bounds,
                    env,
                    preferred_members,
                    &members,
                    label,
                    assignment,
                    r,
                )?;
                Ok(assign_field(assignment, &members, &upper))
            }
            component::T::UnsupportedCycle(_) => Ok(assignment.clone()),
        }
    }

    fn assignment_for_read(
        cache: &mut cache::T,
        r: &Reason,
        env: &mut Env,
        row: &srow::T,
        label: Option<&TShapeField>,
    ) -> Result<assignment::T, missing_assignment::T> {
        let live = splat_elem::set::of_list(row::live_spreads(row, label));
        let analysis = analysis::analyze(&mut cache.bounds, &mut cache.analysis, env, &live, r);
        let top = ShapeFieldType {
            optional: true,
            ty: make_type::mixed(r.clone()),
        };
        let mut assignment: assignment::T = splat_elem::map::empty();
        for component in analysis::components(&analysis).iter() {
            match component {
                component::T::UnsupportedCycle(info) => {
                    assignment = assign_field(&assignment, &cycle_info::members(info), &top)
                }
                component::T::Acyclic(_) | component::T::ProvenEqual(_) => {
                    assignment =
                        upper_for_component(cache, r, env, &live, &assignment, label, component)?
                }
            }
        }
        Ok(assignment)
    }

    /// Project one row to a resolved simple shape, replacing generics with
    /// their upper bounds.
    fn project(
        cache: &mut cache::T,
        r: &Reason,
        env: &mut Env,
        row: &srow::T,
    ) -> Result<Ty, missing_assignment::T> {
        let mut labels: Vec<Option<TShapeField>> = vec![None];
        labels.extend(
            stdlib_set::elements(&analysis::labels::subrow_label_set(
                &mut cache.bounds,
                &mut cache.analysis,
                env,
                row,
                row,
                r,
            ))
            .into_iter()
            .map(|Label(l)| Some(l)),
        );
        let mut known: TShapeMap<ShapeFieldType> = TShapeMap::new();
        let mut unknown = make_type::nothing(r.clone());
        for label in labels.iter() {
            let label = label.as_ref();
            let assignment = assignment_for_read(cache, r, env, row, label)?;
            let field = row::proj(env, row, label, &assignment)?;
            match label {
                Some(name) => {
                    known.insert(name.clone(), field);
                }
                None => unknown = field.ty,
            }
        }
        Ok(mk((
            r.clone(),
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: unknown,
                fields: known,
            })),
        )))
    }

    pub fn resolve(env: &mut Env, r: Reason, elems: &[Ty]) -> Result<Ty, missing_assignment::T> {
        let mut cache = cache::create();
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
                    Ok(srow::to_ty(r.clone(), &row))
                } else {
                    project(&mut cache, &r, env, &row)
                }
            }
            NormalizedView::Union(_) => Ok(srow::normalized_to_ty(env, r.clone(), normalized)),
            NormalizedView::Intersection(_) => {
                Ok(srow::normalized_to_ty(env, r.clone(), normalized))
            }
        }
    }
}

// -- API -------------------------------------------------------------------

/// Project a normalized row at [label], where [None] denotes all labels not
/// named explicitly. Every live spread element must have an assigned field.
pub fn proj(
    env: &mut Env,
    row: &srow::T,
    label: Option<&TShapeField>,
    assignment: &assignment::T,
) -> Result<ShapeFieldType, missing_assignment::T> {
    row::proj(env, row, label, assignment)
}

/// Type parameter/newtype spreads that can affect [row] at [label], excluding
/// those masked by a required field to their right; [None] selects the tail i.e.
/// the upper bound for all unknown fields.
pub fn row_live_spread_at(row: &srow::T, label: Option<&TShapeField>) -> Vec<Ty> {
    row::live_spreads(row, label)
}

/// Resolve a row to a simple shape for reads. Unsupported cyclic components
/// widen to optional [mixed]; normal row projection still applies rightward
/// masking.
pub fn resolve_for_read(
    env: &mut Env,
    r: Reason,
    elems: &[Ty],
) -> Result<Ty, missing_assignment::T> {
    read_resolution::resolve(env, r, elems)
}

/// Concrete labels contributed by either row or by bounds of their spreads.
pub fn subrow_label_set(
    cache: &mut cache::T,
    env: &Env,
    sub: &srow::T,
    super_: &srow::T,
    r: Reason,
) -> TShapeSet {
    stdlib_set::elements(&analysis::labels::subrow_label_set(
        &mut cache.bounds,
        &mut cache.analysis,
        env,
        sub,
        super_,
        &r,
    ))
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
    analysis::labels::subrow_labels(
        &mut cache.bounds,
        &mut cache.analysis,
        env,
        sub,
        super_,
        &r,
    )
}

/// The dependency-ordered components reachable from the given roots,
/// flattened.
pub fn topo(
    cache: &mut cache::T,
    env: &Env,
    roots: &splat_elem::set::T,
    r: Reason,
) -> Vec<Ty> {
    plan::order(cache, env, roots, &r)
}

/// Check every corner assignment of the live spread elements.
///
/// `~init`, `~conj` and `~f` thread the environment: `init env`,
/// `conj (env, acc) k` (here `conj(env, acc, k)`) and `f env ~sub ~super`.
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
) -> Result<Computation<A>, missing_assignment::T> {
    search::check_subrow_corners(cache, env, sub, super_, label, &r, &init, &conj, &mut f)
}

/// Every corner co-assignment of the spread elements reachable from the roots.
pub fn corner_assignments(
    cache: &mut cache::T,
    env: &mut Env,
    roots: &splat_elem::set::T,
    label: Option<&TShapeField>,
    r: Reason,
) -> Result<Computation<Vec<assignment::T>>, missing_assignment::T> {
    search::assignments(cache, env, roots, label, &r)
}

/// Type-variable IDs occurring in spread position, in source order.
pub fn spread_tyvar_ids(row: &srow::T) -> Vec<tvid::T> {
    inference::spread_tyvar_ids(row)
}

/// Split a splat around the first occurrence of the given spread variable.
pub fn partition_at_tyvar(row: &srow::T, v: tvid::T) -> Option<(Vec<Ty>, Vec<Ty>)> {
    inference::partition_at_tyvar(row, v)
}

/// Substitute solved spread variables and drop unsolved ones as empty rows.
pub fn solve_spread_vars(env: &mut Env, r: Reason, row: &srow::T) -> srow::Normalized {
    inference::solve_spread_vars(env, &r, row)
}

/// Exported only so the tests can reach them.
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

        /// Definitely overwritten, still potentially relevant, or
        /// bounds-dependent.
        pub use super::super::search::masking::T;

        /// Determine how [key] is masked in a row under the current assignment.
        pub fn of_row(
            cache: &mut cache::T,
            env: &Env,
            row: &srow::T,
            label: Option<&TShapeField>,
            key: &Ty,
            assignment: &assignment::T,
            r: Reason,
        ) -> Result<T, missing_assignment::T> {
            super::super::search::masking::of_row(cache, env, row, label, key, assignment, &r)
        }
    }

    pub use super::analysis;
    pub use super::analysis::component;
    pub use super::analysis::cycle_info;
    pub use super::analysis::dependency;

    /// Analyze reachable dependencies without changing the corner traversal.
    pub fn analyze_dependencies(
        env: &Env,
        roots: &splat_elem::set::T,
        r: Reason,
    ) -> analysis::T {
        let mut cache = cache::create();
        analysis::analyze(&mut cache.bounds, &mut cache.analysis, env, roots, &r)
    }

    /// Everything reachable by following bounds from the given elements.
    pub fn closure(env: &Env, names: &splat_elem::set::T, r: Reason) -> splat_elem::set::T {
        let mut cache = cache::create();
        analysis::closure(&mut cache.bounds, &mut cache.analysis, env, names, &r)
    }

    /// Interpret a spread element's upper bound as normalized shape rows.
    pub fn bound_shape_upper(
        env: &mut Env,
        ty: &Ty,
        assignment: &assignment::T,
        r: Reason,
    ) -> UpperBoundView {
        let mut cache = cache::create();
        let view = field_bounds::bound_shape_upper(&mut cache.bounds, env, ty, assignment, &r);
        match view {
            field_bounds::upper::T::Shapes(rows) => UpperBoundView::UpperShapes(rows),
            field_bounds::upper::T::Bottom => UpperBoundView::UpperBottom,
            field_bounds::upper::T::Unconstrained => UpperBoundView::UpperUnconstrained,
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
        let view = field_bounds::bound_shape_lower(&mut cache.bounds, env, ty, assignment, &r);
        match view {
            field_bounds::lower::T::Shapes(rows) => LowerBoundView::LowerShapes(rows),
            field_bounds::lower::T::Bottom => LowerBoundView::LowerBottom,
        }
    }

    /// Project a spread element's lower and upper field bounds at one label.
    pub fn field_bounds(
        env: &mut Env,
        name: &Ty,
        label: Option<&TShapeField>,
        assignment: &assignment::T,
        r: Reason,
    ) -> Result<(ShapeFieldType, ShapeFieldType), missing_assignment::T> {
        let mut cache = cache::create();
        super::field_bounds::field_bounds(&mut cache.bounds, env, name, label, assignment, &r)
    }

    /// Spread elements mentioned by the given element's upper bound.
    pub fn type_params_in_upper_bound(env: &Env, splat_elem: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        analysis::type_params_in_upper_bound(
            &mut cache.bounds,
            &mut cache.analysis,
            env,
            splat_elem,
            &r,
        )
    }

    /// Spread elements mentioned by the given element's lower bound.
    pub fn type_params_in_lower_bound(env: &Env, splat_elem: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        analysis::type_params_in_lower_bound(
            &mut cache.bounds,
            &mut cache.analysis,
            env,
            splat_elem,
            &r,
        )
    }

    /// Spread elements mentioned by either bound of the given element.
    pub fn type_params_in_bounds(env: &Env, splat_elem: &Ty, r: Reason) -> Vec<Ty> {
        let mut cache = cache::create();
        analysis::type_params_in_bounds(
            &mut cache.bounds,
            &mut cache.analysis,
            env,
            splat_elem,
            &r,
        )
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
    ) -> Result<field::corners::T, missing_assignment::T> {
        let mut cache = cache::create();
        search::corners_for(
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
