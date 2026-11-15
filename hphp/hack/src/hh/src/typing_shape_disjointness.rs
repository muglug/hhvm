// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_shape_disjointness.ml`. See `hh/PORTING.md`.
//!
//! The decision procedure behind `<<__DisjointShapeSplat>>`: every way the
//! localized elements of a splat may fail to be pairwise disjoint.
//!
//! - The sets and maps over labels are `TShapeSet` / `TShapeMap`, ordered by
//!   `TShapeField.compare`, which ignores positions; nothing here reads the
//!   position of a label out of a set made by `union`, `inter` or `diff` (only
//!   out of the sets of one shape's own fields), so which of two equal labels
//!   such a set keeps is not observable.
//! - Lists the OCaml builds reversed (`rev_sources`) are kept in order.
//! - Functions which thread an environment only to drop it take `&Env` and
//!   work on a copy.
//! - `Solver`'s cache entries hold the environment they were computed in, and
//!   are used only for a physically equal one. The environments one solver
//!   sees differ from the one `violations` is given only by what
//!   `expand_type` does to it, which changes no bound, so the entries here
//!   hold no environment: a bound found is the bound that would be computed.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use oxidized::pos_or_decl::PosOrDecl;

use crate::pos_or_decl;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TShapeSet;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::t_shape_map;
use crate::typing_defs_core::t_shape_map::TShapeField;
use crate::typing_defs_core::t_shape_map::TShapeMap;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error::primary::shape_splat::DisjointnessViolation;
use crate::typing_error::primary::shape_splat::OverlapSource;
use crate::typing_error::primary::shape_splat::OverlapSourceOrigin;
use crate::typing_make_type;
use crate::typing_reason;
use crate::typing_set;
use crate::typing_shape_splat_key;
use crate::typing_utils;
use crate::utils;

/// `TShapeSet.inter`
fn inter(s1: &TShapeSet, s2: &TShapeSet) -> TShapeSet {
    s1.intersection(s2).cloned().collect()
}

/// `TShapeSet.union`
fn union(s1: &TShapeSet, s2: &TShapeSet) -> TShapeSet {
    s1.union(s2).cloned().collect()
}

/// `TShapeSet.diff`
fn diff(s1: &TShapeSet, s2: &TShapeSet) -> TShapeSet {
    s1.difference(s2).cloned().collect()
}

/// `TShapeSet.singleton`
fn singleton(field: TShapeField) -> TShapeSet {
    let mut s = TShapeSet::new();
    s.insert(field);
    s
}

/// `TShapeField.name`
fn name(field: &TShapeField) -> String {
    t_shape_field::name(&field.0).to_string()
}

/// `TShapeField.pos`
fn pos(field: &TShapeField) -> PosOrDecl {
    t_shape_field::pos(&field.0)
}

/// `TShapeMap.add`: the binding is replaced, key included.
fn add<V>(field: TShapeField, v: V, map: &mut TShapeMap<V>) {
    map.remove(&field);
    map.insert(field, v);
}

pub mod label_bound {
    use super::*;

    /// The upper bound on the shape field labels a shape _may_ include.
    /// [Bottom_plus] describes labels coming from closed upper bounds whilst
    /// [Top_minus] describes a set including all labels except those declared
    /// as [absent] (i.e. open upper bounds)
    #[derive(Clone, Debug)]
    pub enum T {
        BottomPlus(TShapeSet),
        TopMinus(TShapeSet),
    }

    /// The [top] label bound has all fields possible present, `Top - {} = Top`
    pub fn top() -> T {
        T::TopMinus(TShapeSet::new())
    }

    /// The [bottom] label bound has no fields present, `Bot + {} = Bot`
    pub fn bottom() -> T {
        T::BottomPlus(TShapeSet::new())
    }

    pub fn equal(t1: &T, t2: &T) -> bool {
        match (t1, t2) {
            (T::BottomPlus(labels1), T::BottomPlus(labels2))
            | (T::TopMinus(labels1), T::TopMinus(labels2)) => labels1 == labels2,
            (T::BottomPlus(_), T::TopMinus(_)) | (T::TopMinus(_), T::BottomPlus(_)) => false,
        }
    }

    pub fn is_top(t: &T) -> bool {
        match t {
            T::TopMinus(absent) => absent.is_empty(),
            T::BottomPlus(_) => false,
        }
    }

    pub fn is_empty(t: &T) -> bool {
        match t {
            T::BottomPlus(present) => present.is_empty(),
            T::TopMinus(_) => false,
        }
    }

    pub fn disjoint(t1: &T, t2: &T) -> bool {
        match (t1, t2) {
            (T::BottomPlus(present1), T::BottomPlus(present2)) => {
                // Concrete case; if the intersection of the known labels is empty then
                // t1 and t2 must be disjoint
                let present_both = inter(present1, present2);
                present_both.is_empty()
            }
            (T::BottomPlus(present), T::TopMinus(absent))
            | (T::TopMinus(absent), T::BottomPlus(present)) => {
                // We have the labels known to be present in on label bound and those
                // known to be absent in the other. If the set of labels known to be
                // present in the first is contained by the set of labels known to be
                // absent in the second then t1 and t2 must be disjoint
                present.is_subset(absent)
            }
            (T::TopMinus(_), T::TopMinus(_)) => {
                // Always false - a finite set of absent labels in both t1 and t2 doesn't
                // prove there are no other labels which may not be disjoint
                false
            }
        }
    }

    pub fn join(t1: &T, t2: &T) -> T {
        match (t1, t2) {
            (T::BottomPlus(present1), T::BottomPlus(present2)) => {
                let maybe_present = union(present1, present2);
                T::BottomPlus(maybe_present)
            }
            (T::TopMinus(absent1), T::TopMinus(absent2)) => {
                let definitely_absent = inter(absent1, absent2);
                T::TopMinus(definitely_absent)
            }
            (T::BottomPlus(present), T::TopMinus(absent))
            | (T::TopMinus(absent), T::BottomPlus(present)) => T::TopMinus(diff(absent, present)),
        }
    }

    pub fn meet(t1: &T, t2: &T) -> T {
        match (t1, t2) {
            (T::BottomPlus(present1), T::BottomPlus(present2)) => {
                let definitely_present = inter(present1, present2);
                T::BottomPlus(definitely_present)
            }
            (T::TopMinus(absent1), T::TopMinus(absent2)) => {
                let maybe_absent = union(absent1, absent2);
                T::TopMinus(maybe_absent)
            }
            (T::BottomPlus(present), T::TopMinus(absent))
            | (T::TopMinus(absent), T::BottomPlus(present)) => {
                T::BottomPlus(diff(present, absent))
            }
        }
    }

    /// Equivalent to [meet b1 (Bottom_plus labels)] then extracting the labels
    /// but avoids being partial
    pub fn restrict(t: &T, labels: &TShapeSet) -> TShapeSet {
        match t {
            T::BottomPlus(s) => inter(labels, s),
            T::TopMinus(s) => diff(labels, s),
        }
    }
}

pub mod element {
    use super::*;

    /// Describes the labels which are and may be present in a given splat element
    /// [definitely_present] corresponds which are known to exist whilst
    /// [possibly_present] uses a [Label_bound] representation to encode those
    /// that may exist
    #[derive(Clone, Debug)]
    pub struct T {
        pub definitely_present: TShapeSet,
        pub possibly_present: label_bound::T,
    }

    /// A closed splat element has all undeclared labels at [nothing].
    pub fn closed_elem(definitely_present: TShapeSet, possibly_present: TShapeSet) -> T {
        T {
            definitely_present,
            possibly_present: label_bound::T::BottomPlus(possibly_present),
        }
    }

    pub fn empty() -> T {
        T {
            definitely_present: TShapeSet::new(),
            possibly_present: label_bound::T::BottomPlus(TShapeSet::new()),
        }
    }

    /// An open splat element may have any label present
    pub fn open_elem() -> T {
        T {
            definitely_present: TShapeSet::new(),
            possibly_present: label_bound::T::TopMinus(TShapeSet::new()),
        }
    }

    pub fn ty_param_source(name: &str) -> String {
        format!("type parameter `{}`", name)
    }

    pub fn newtype_source(name: &str) -> String {
        format!("newtype `{}`", utils::strip_ns(name))
    }

    pub fn demote_except(retained: &TShapeSet, t: &T) -> T {
        let T {
            definitely_present,
            possibly_present,
        } = t;
        let demoted = diff(definitely_present, retained);
        let possibly_present = match possibly_present {
            label_bound::T::BottomPlus(s) => label_bound::T::BottomPlus(union(s, &demoted)),
            label_bound::T::TopMinus(s) => label_bound::T::TopMinus(diff(s, &demoted)),
        };
        T {
            definitely_present: retained.clone(),
            possibly_present,
        }
    }

    /// Make every known-present label merely possible.
    pub fn possible(t: &T) -> T {
        demote_except(&TShapeSet::new(), t)
    }

    /// Merge two elements that both contribute: the union of what each certainly
    /// carries, and the join of what each may carry.
    pub fn join(e1: &T, e2: &T) -> T {
        let possibly_present = label_bound::join(&e1.possibly_present, &e2.possibly_present);
        let definitely_present = union(&e1.definitely_present, &e2.definitely_present);
        T {
            definitely_present,
            possibly_present,
        }
    }
}

mod positions {
    use super::*;

    /// An element of `Pos_or_decl.Set.t`, ordered by `Pos_or_decl.compare`.
    #[derive(Clone, Debug)]
    pub struct Key(pub PosOrDecl);

    impl Ord for Key {
        fn cmp(&self, other: &Self) -> Ordering {
            pos_or_decl::compare(&self.0, &other.0)
        }
    }

    impl PartialOrd for Key {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl PartialEq for Key {
        fn eq(&self, other: &Self) -> bool {
            self.cmp(other) == Ordering::Equal
        }
    }

    impl Eq for Key {}

    #[derive(Clone, Debug)]
    pub struct T {
        pub first: Option<PosOrDecl>,
        pub all: BTreeSet<Key>,
    }

    pub fn empty() -> T {
        T {
            first: None,
            all: BTreeSet::new(),
        }
    }

    pub fn singleton(pos: PosOrDecl) -> T {
        let mut all = BTreeSet::new();
        all.insert(Key(pos.clone()));
        T {
            first: Some(pos),
            all,
        }
    }

    pub fn add(positions: T, pos: PosOrDecl) -> T {
        if positions.all.contains(&Key(pos.clone())) {
            positions
        } else {
            let T { first, mut all } = positions;
            all.insert(Key(pos.clone()));
            T {
                // `Option.first_some first (Some pos)`
                first: first.or(Some(pos)),
                all,
            }
        }
    }

    pub fn add_list(positions: T, additional: Vec<PosOrDecl>) -> T {
        additional.into_iter().fold(positions, add)
    }

    pub fn union(left: T, right: &T) -> T {
        match left.first {
            None => right.clone(),
            Some(_) => right
                .all
                .iter()
                .fold(left, |positions, pos| add(positions, pos.0.clone())),
        }
    }

    pub fn elements(t: &T) -> Vec<PosOrDecl> {
        let T { first, all } = t;
        match first {
            None => vec![],
            Some(first) => {
                let mut l = vec![first.clone()];
                let first = Key(first.clone());
                l.extend(all.iter().filter(|pos| **pos != first).map(|pos| pos.0.clone()));
                l
            }
        }
    }
}

mod overlap_source {
    use super::*;

    /// `module Minimal`: `type t = Typing_error.Primary.Shape_splat.overlap_source`,
    /// ordered by `compare` (the key of `Map` and the element of `Set`).
    #[derive(Clone, Debug)]
    pub struct Minimal(pub OverlapSource);

    pub fn compare_origin(left: &OverlapSourceOrigin, right: &OverlapSourceOrigin) -> Ordering {
        match (left, right) {
            (OverlapSourceOrigin::ShapeField(left), OverlapSourceOrigin::ShapeField(right))
            | (OverlapSourceOrigin::Description(left), OverlapSourceOrigin::Description(right)) => {
                left.as_bytes().cmp(right.as_bytes())
            }
            (OverlapSourceOrigin::ShapeField(_), OverlapSourceOrigin::Description(_)) => {
                Ordering::Less
            }
            (OverlapSourceOrigin::Description(_), OverlapSourceOrigin::ShapeField(_)) => {
                Ordering::Greater
            }
        }
    }

    pub fn compare(left: &OverlapSource, right: &OverlapSource) -> Ordering {
        let result = pos_or_decl::compare(&left.pos, &right.pos);
        if result == Ordering::Equal {
            compare_origin(&left.origin, &right.origin)
        } else {
            result
        }
    }

    impl Ord for Minimal {
        fn cmp(&self, other: &Self) -> Ordering {
            compare(&self.0, &other.0)
        }
    }

    impl PartialOrd for Minimal {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl PartialEq for Minimal {
        fn eq(&self, other: &Self) -> bool {
            self.cmp(other) == Ordering::Equal
        }
    }

    impl Eq for Minimal {}

    /// `module Map = Stdlib.Map.Make (Minimal)`
    pub type Map<V> = BTreeMap<Minimal, V>;
    /// `module Set = Stdlib.Set.Make (Minimal)`
    pub type Set = BTreeSet<Minimal>;
}

mod sources {
    use super::*;

    /// (`rev_sources` is kept in order here: `sources`.)
    #[derive(Clone, Debug)]
    pub struct T {
        sources: Vec<OverlapSource>,
        source_set: overlap_source::Set,
    }

    pub fn empty() -> T {
        T {
            sources: vec![],
            source_set: overlap_source::Set::new(),
        }
    }

    pub fn add(mut sources: T, source: OverlapSource) -> T {
        if sources
            .source_set
            .contains(&overlap_source::Minimal(source.clone()))
        {
            sources
        } else {
            sources
                .source_set
                .insert(overlap_source::Minimal(source.clone()));
            sources.sources.push(source);
            sources
        }
    }

    pub fn add_list(sources: T, additional: Vec<OverlapSource>) -> T {
        additional.into_iter().fold(sources, add)
    }

    pub fn elements(t: &T) -> Vec<OverlapSource> {
        t.sources.clone()
    }
}

mod possible_source {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct T {
        pub source: OverlapSource,
        pub bound: label_bound::T,
    }
}

mod possible_sources {
    use super::*;

    /// (`rev_sources` is kept in order here: `sources`.)
    #[derive(Clone, Debug)]
    pub struct T {
        sources: Vec<OverlapSource>,
        bounds: overlap_source::Map<label_bound::T>,
        aggregate_bound: label_bound::T,
    }

    pub fn empty() -> T {
        T {
            sources: vec![],
            bounds: overlap_source::Map::new(),
            aggregate_bound: label_bound::bottom(),
        }
    }

    pub fn add(mut sources: T, possible_source: possible_source::T) -> T {
        let possible_source::T { source, bound } = possible_source;
        let aggregate_bound = label_bound::join(&sources.aggregate_bound, &bound);
        let key = overlap_source::Minimal(source.clone());
        match sources.bounds.get(&key) {
            None => {
                sources.sources.push(source);
                sources.bounds.insert(key, bound);
                sources.aggregate_bound = aggregate_bound;
                sources
            }
            Some(previous_bound) => {
                let bound = label_bound::join(previous_bound, &bound);
                sources.bounds.insert(key, bound);
                sources.aggregate_bound = aggregate_bound;
                sources
            }
        }
    }

    pub fn singleton(possible_source: possible_source::T) -> T {
        add(empty(), possible_source)
    }

    pub fn elements(t: &T) -> Vec<possible_source::T> {
        t.sources
            .iter()
            .map(|source| possible_source::T {
                source: source.clone(),
                // `Overlap_source.Map.find`
                bound: match t.bounds.get(&overlap_source::Minimal(source.clone())) {
                    Some(bound) => bound.clone(),
                    None => panic!("Not_found"),
                },
            })
            .collect()
    }

    pub fn sources(t: &T) -> Vec<OverlapSource> {
        t.sources.clone()
    }

    pub fn union(left: T, right: &T) -> T {
        elements(right).into_iter().fold(left, add)
    }

    pub fn restrict(sources: &T, restriction: &label_bound::T) -> T {
        elements(sources)
            .into_iter()
            .fold(empty(), |acc, possible_source| {
                let possible_source::T { source, bound } = possible_source;
                let bound = label_bound::meet(&bound, restriction);
                if label_bound::is_empty(&bound) {
                    acc
                } else {
                    add(acc, possible_source::T { source, bound })
                }
            })
    }

    pub fn is_empty(t: &T) -> bool {
        t.sources.is_empty()
    }

    pub fn aggregate_bound(t: &T) -> &label_bound::T {
        &t.aggregate_bound
    }
}

/// `(required, optional, absent)`
fn partition_fields(
    env: &Env,
    s_fields: &t_shape_map::T<ShapeFieldType>,
) -> (TShapeSet, TShapeSet, TShapeSet) {
    let mut required = TShapeSet::new();
    let mut optional = TShapeSet::new();
    let mut absent = TShapeSet::new();
    for (label, sft) in s_fields.iter() {
        if !sft.optional {
            required.insert(label.clone());
        } else if typing_utils::is_nothing(env, &sft.ty) {
            absent.insert(label.clone());
        } else {
            optional.insert(label.clone());
        }
    }
    (required, optional, absent)
}

fn label_bound_from_shape_disjointness(env: &Env, ty: &Ty) -> label_bound::T {
    let r = get_reason(ty);
    let top_shape = typing_make_type::shape(
        r.clone(),
        typing_make_type::mixed(r.clone()),
        t_shape_map::T::new(),
    );
    if typing_utils::is_type_disjoint(env, ty, &top_shape) {
        label_bound::bottom()
    } else {
        label_bound::top()
    }
}

/// Computes the label bounds of recursive type parameters and newtypes. Only
/// label bounds are cached; detailed elements retain use-site provenance.
mod solver {
    use super::*;

    pub mod node {
        use super::*;

        #[derive(Clone, Debug)]
        pub struct NewtypeNode {
            pub key: typing_shape_splat_key::T,
            pub bound_ty: Ty,
        }

        #[derive(Clone, Debug)]
        pub enum T {
            TyParam(String),
            Newtype(NewtypeNode),
        }

        pub fn compare(left: &T, right: &T) -> Ordering {
            match (left, right) {
                (T::TyParam(left), T::TyParam(right)) => left.as_bytes().cmp(right.as_bytes()),
                (T::Newtype(left), T::Newtype(right)) => {
                    typing_shape_splat_key::compare(&left.key, &right.key)
                }
                (T::TyParam(_), T::Newtype(_)) => Ordering::Less,
                (T::Newtype(_), T::TyParam(_)) => Ordering::Greater,
            }
        }

        pub fn of_ty(ty: &Ty) -> T {
            match get_node(ty) {
                Ty_::Tgeneric(name) => T::TyParam(name.clone()),
                Ty_::Tnewtype(_, _, bound_ty) => {
                    // The canonical key deliberately omits [bound_ty], so map comparison
                    // never traverses a recursively duplicated bound. Equal keys in the
                    // same environment denote the same localized newtype bound.
                    T::Newtype(NewtypeNode {
                        key: typing_shape_splat_key::of_ty(ty),
                        bound_ty: bound_ty.clone(),
                    })
                }
                _ => panic!("Invalid_argument: Solver expected a type parameter or newtype"),
            }
        }

        impl Ord for T {
            fn cmp(&self, other: &Self) -> Ordering {
                compare(self, other)
            }
        }

        impl PartialOrd for T {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl PartialEq for T {
            fn eq(&self, other: &Self) -> bool {
                self.cmp(other) == Ordering::Equal
            }
        }

        impl Eq for T {}

        pub type Map<V> = BTreeMap<T, V>;
        pub type Set = BTreeSet<T>;
    }

    /// (No `input_env`: see the module documentation.)
    struct Entry {
        bound: label_bound::T,
    }

    pub struct T {
        cache: node::Map<Entry>,
    }

    pub fn create() -> T {
        T {
            cache: node::Map::new(),
        }
    }

    fn find(solver: &T, _env: &Env, node: &node::T) -> Option<label_bound::T> {
        solver.cache.get(node).map(|entry| entry.bound.clone())
    }

    fn add(solver: &mut T, _env: &Env, node: node::T, bound: label_bound::T) {
        solver.cache.remove(&node);
        solver.cache.insert(node, Entry { bound });
    }

    fn simple_shape_bound(
        env: &Env,
        s_fields: &t_shape_map::T<ShapeFieldType>,
        s_unknown_value: &Ty,
    ) -> label_bound::T {
        let (required, optional, absent) = partition_fields(env, s_fields);
        if typing_utils::is_nothing(env, s_unknown_value) {
            label_bound::T::BottomPlus(union(&required, &optional))
        } else {
            label_bound::T::TopMinus(absent)
        }
    }

    fn nodes_in_ty(env: &Env, nodes: &mut node::Set, ty: &Ty) {
        let mut env = env.clone();
        let (_sd, ty) = typing_utils::strip_supportdyn(&mut env, ty.clone());
        let ty = typing_env::expand_type(&mut env, ty);
        let env = &env;
        match get_node(&ty) {
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))
            | Ty_::Tunion(ss_elems)
            | Ty_::Tintersection(ss_elems) => {
                for ty in ss_elems.iter() {
                    nodes_in_ty(env, nodes, ty)
                }
            }
            Ty_::Toption(bound_ty) | Ty_::Tdependent(_, bound_ty) => {
                nodes_in_ty(env, nodes, bound_ty)
            }
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => {
                // `Node.Set.add`: an equal node already there is kept.
                let node = node::of_ty(&ty);
                if !nodes.contains(&node) {
                    nodes.insert(node);
                }
            }
            Ty_::Tshape(ShapeType::ShapeSimple(_))
            | Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tdynamic(_)
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::TclassPtr(_)
            | Ty_::Tvar(_)
            | Ty_::Tclass(..)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_) => {}
        }
    }

    fn bound_tys(env: &Env, node: &node::T) -> Vec<Ty> {
        match node {
            node::T::TyParam(name) => {
                typing_set::elements(&typing_env::get_upper_bounds(env, name))
            }
            node::T::Newtype(node::NewtypeNode { bound_ty, .. }) => vec![bound_ty.clone()],
        }
    }

    fn dependencies(env: &Env, node: &node::T) -> node::Set {
        let mut nodes = node::Set::new();
        for ty in bound_tys(env, node).iter() {
            nodes_in_ty(env, &mut nodes, ty)
        }
        nodes
    }

    fn reachable_nodes(solver: &T, env: &Env, root: &node::T) -> Vec<node::T> {
        // (`rev_order` is consed onto and reversed at the end: here in order.)
        fn visit(
            solver: &T,
            env: &Env,
            node: &node::T,
            seen: &mut node::Set,
            order: &mut Vec<node::T>,
        ) {
            if seen.contains(node) || find(solver, env, node).is_some() {
            } else {
                seen.insert(node.clone());
                for dependency in dependencies(env, node).iter() {
                    visit(solver, env, dependency, seen, order)
                }
                order.push(node.clone());
            }
        }
        let mut seen = node::Set::new();
        let mut order = vec![];
        visit(solver, env, root, &mut seen, &mut order);
        order
    }

    fn bound_of_ty(
        lookup: &dyn Fn(&node::T) -> label_bound::T,
        env: &Env,
        ty: &Ty,
    ) -> label_bound::T {
        let mut env = env.clone();
        let (_sd, ty) = typing_utils::strip_supportdyn(&mut env, ty.clone());
        let ty = typing_env::expand_type(&mut env, ty);
        let env = &env;
        match get_node(&ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            })) => simple_shape_bound(env, s_fields, s_unknown_value),
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))
            | Ty_::Tunion(ss_elems) => join_ty_bounds(lookup, env, ss_elems),
            Ty_::Tintersection(tys) => meet_ty_bounds(lookup, env, tys),
            Ty_::Toption(bound_ty) | Ty_::Tdependent(_, bound_ty) => {
                bound_of_ty(lookup, env, bound_ty)
            }
            Ty_::Tgeneric(_) | Ty_::Tnewtype(..) => lookup(&node::of_ty(&ty)),
            Ty_::Tdynamic(_) | Ty_::Tvar(_) => label_bound::top(),
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::TclassPtr(_)
            | Ty_::Tclass(..)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_) => label_bound_from_shape_disjointness(env, &ty),
        }
    }

    fn join_ty_bounds(
        lookup: &dyn Fn(&node::T) -> label_bound::T,
        env: &Env,
        tys: &[Ty],
    ) -> label_bound::T {
        match tys {
            [] => label_bound::bottom(),
            [ty, tys @ ..] => {
                let bound = bound_of_ty(lookup, env, ty);
                if label_bound::is_top(&bound) {
                    bound
                } else {
                    label_bound::join(&bound, &join_ty_bounds(lookup, env, tys))
                }
            }
        }
    }

    fn meet_ty_bounds(
        lookup: &dyn Fn(&node::T) -> label_bound::T,
        env: &Env,
        tys: &[Ty],
    ) -> label_bound::T {
        match tys {
            [] => label_bound::top(),
            [ty, tys @ ..] => {
                let bound = bound_of_ty(lookup, env, ty);
                if label_bound::is_empty(&bound) {
                    bound
                } else {
                    label_bound::meet(&bound, &meet_ty_bounds(lookup, env, tys))
                }
            }
        }
    }

    // Recursive type-parameter and newtype bounds form monotone equations over
    // [Label_bound]. For example, [A = meet B {a}] and [B = join A {b}]
    // converge as follows:
    //
    //   [(A, B) = (top, top) -> ({a}, top) -> ({a}, {a, b})]
    //
    // Starting at top gives the greatest solution without distinguishing
    // expansion paths.
    pub fn solve(solver: &mut T, env: &Env, ty: &Ty) -> label_bound::T {
        let root = node::of_ty(ty);
        match find(solver, env, &root) {
            Some(bound) => bound,
            None => {
                let nodes = reachable_nodes(solver, env, &root);
                let initial_bounds: node::Map<label_bound::T> = nodes
                    .iter()
                    .map(|node| (node.clone(), label_bound::top()))
                    .collect();
                // `let rec converge bounds = ...`
                let mut bounds = initial_bounds;
                loop {
                    let mut changed = false;
                    let mut next_bounds: node::Map<label_bound::T> = node::Map::new();
                    for node in nodes.iter() {
                        // `Node.Map.find`
                        let previous = match bounds.get(node) {
                            Some(previous) => previous.clone(),
                            None => panic!("Not_found"),
                        };
                        let bound = {
                            let lookup = |dependency: &node::T| -> label_bound::T {
                                match find(solver, env, dependency) {
                                    Some(bound) => bound,
                                    None => match next_bounds.get(dependency) {
                                        Some(bound) => bound.clone(),
                                        None => match bounds.get(dependency) {
                                            Some(bound) => bound.clone(),
                                            None => label_bound::top(),
                                        },
                                    },
                                }
                            };
                            meet_ty_bounds(&lookup, env, &bound_tys(env, node))
                        };
                        if !label_bound::equal(&previous, &bound) {
                            changed = true
                        }
                        next_bounds.remove(node);
                        next_bounds.insert(node.clone(), bound);
                    }
                    bounds = next_bounds;
                    if !changed {
                        break;
                    }
                }
                for (node, bound) in bounds.iter() {
                    add(solver, env, node.clone(), bound.clone())
                }
                // `Node.Map.find`
                match bounds.get(&root) {
                    Some(bound) => bound.clone(),
                    None => panic!("Not_found"),
                }
            }
        }
    }
}

mod detailed_element {
    use super::*;

    /// An [Element.t] together with all the provenance that its sets intentionally
    /// discard. [TShapeField.compare] ignores positions, which is right for the
    /// lattice but not for a diagnostic.
    #[derive(Clone, Debug)]
    pub struct T {
        pub element: element::T,
        pub present_positions: TShapeMap<positions::T>,
        pub possible_sources: possible_sources::T,
    }

    fn positions_of_fields(fields: &TShapeSet) -> TShapeMap<positions::T> {
        let mut positions = TShapeMap::new();
        for field in fields.iter() {
            add(field.clone(), positions::singleton(pos(field)), &mut positions)
        }
        positions
    }

    fn merge_positions(
        left: &TShapeMap<positions::T>,
        right: &TShapeMap<positions::T>,
    ) -> TShapeMap<positions::T> {
        let mut acc = left.clone();
        for (field, positions) in right.iter() {
            let previous = match acc.get(field) {
                Some(previous) => previous.clone(),
                None => positions::empty(),
            };
            add(field.clone(), positions::union(previous, positions), &mut acc)
        }
        acc
    }

    pub fn empty() -> T {
        // `let element = ... and present_positions = ... and possible_sources = ...`
        let element = element::empty();
        let present_positions = TShapeMap::new();
        let possible_sources = possible_sources::empty();
        T {
            element,
            present_positions,
            possible_sources,
        }
    }

    fn source(pos: PosOrDecl, description: &str, bound: label_bound::T) -> possible_source::T {
        possible_source::T {
            source: OverlapSource {
                pos,
                origin: OverlapSourceOrigin::Description(description.to_string()),
            },
            bound,
        }
    }

    fn field_source(pos: PosOrDecl, label: String, bound: label_bound::T) -> possible_source::T {
        possible_source::T {
            source: OverlapSource {
                pos,
                origin: OverlapSourceOrigin::ShapeField(label),
            },
            bound,
        }
    }

    fn possible_sources_of_fields(fields: &TShapeSet) -> possible_sources::T {
        let mut sources = possible_sources::empty();
        for field in fields.iter() {
            let bound = label_bound::T::BottomPlus(singleton(field.clone()));
            sources = possible_sources::add(sources, field_source(pos(field), name(field), bound));
        }
        sources
    }

    /// Demote all fields that were definitely present to be only possibly present
    /// except those contained in [retained]; used when we have a union shape
    /// splat element
    fn demote_except(retained: &TShapeSet, t: &T) -> T {
        let mut present_positions: TShapeMap<positions::T> = TShapeMap::new();
        let mut field_sources = possible_sources::empty();
        for (field, position_set) in t.present_positions.iter() {
            if retained.contains(field) {
                add(field.clone(), position_set.clone(), &mut present_positions)
            } else {
                let label = name(field);
                let bound = label_bound::T::BottomPlus(singleton(field.clone()));
                for pos in positions::elements(position_set) {
                    field_sources = possible_sources::add(
                        field_sources,
                        field_source(pos, label.clone(), bound.clone()),
                    );
                }
            }
        }
        let element = element::demote_except(retained, &t.element);
        let possible_sources = possible_sources::union(t.possible_sources.clone(), &field_sources);
        T {
            element,
            present_positions,
            possible_sources,
        }
    }

    fn possible(t: &T) -> T {
        demote_except(&TShapeSet::new(), t)
    }

    fn unknown(source_pos: PosOrDecl, description: &str) -> T {
        let element = element::open_elem();
        let present_positions = TShapeMap::new();
        let possible_sources =
            possible_sources::singleton(source(source_pos, description, label_bound::top()));
        T {
            element,
            present_positions,
            possible_sources,
        }
    }

    // A non-shape upper bound can still admit shape inhabitants, as [nonnull]
    // and dict-compatible classes do. Only discard it when disjointness proves
    // that their intersection is empty.
    fn of_other_type(env: &Env, source_pos: PosOrDecl, ty: &Ty) -> T {
        let bound = label_bound_from_shape_disjointness(env, ty);
        if label_bound::is_empty(&bound) {
            empty()
        } else {
            unknown(source_pos, "a type which may contain a shape")
        }
    }

    pub fn join(e1: &T, e2: &T) -> T {
        T {
            element: element::join(&e1.element, &e2.element),
            present_positions: merge_positions(&e1.present_positions, &e2.present_positions),
            possible_sources: possible_sources::union(
                e1.possible_sources.clone(),
                &e2.possible_sources,
            ),
        }
    }

    fn join_alternatives(e1: &T, e2: &T) -> T {
        let retained = inter(
            &e1.element.definitely_present,
            &e2.element.definitely_present,
        );
        // (The arguments are evaluated right to left; `demote_except` has no
        // effect.)
        join(&demote_except(&retained, e1), &demote_except(&retained, e2))
    }

    /// An intersection can only supply labels allowed by every member. Concrete
    /// fields are possible rather than certain until all members are considered.
    fn intersect(e1: &T, e2: &T) -> T {
        let e1 = possible(e1);
        let e2 = possible(e2);
        let possibly_present = label_bound::meet(
            &e1.element.possibly_present,
            &e2.element.possibly_present,
        );
        let possible_sources = possible_sources::union(
            possible_sources::restrict(&e1.possible_sources, &possibly_present),
            &possible_sources::restrict(&e2.possible_sources, &possibly_present),
        );
        let element = element::T {
            definitely_present: TShapeSet::new(),
            possibly_present,
        };
        T {
            element,
            present_positions: TShapeMap::new(),
            possible_sources,
        }
    }

    fn of_ty_(solver: &mut solver::T, env: &Env, ty: &Ty) -> T {
        let source_pos = typing_reason::to_pos(get_reason(ty));
        let mut env = env.clone();
        let (_sd, ty) = typing_utils::strip_supportdyn(&mut env, ty.clone());
        let ty = typing_env::expand_type(&mut env, ty);
        let env = &env;
        match get_node(&ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                fields: s_fields,
                unknown_value: s_unknown_value,
                ..
            })) => {
                let (definitely_present, optional, absent) = partition_fields(env, s_fields);
                let optional_sources = possible_sources_of_fields(&optional);
                if typing_utils::is_nothing(env, s_unknown_value) {
                    let present_positions = positions_of_fields(&definitely_present);
                    let element = element::closed_elem(definitely_present, optional);
                    let possible_sources = optional_sources;
                    T {
                        element,
                        present_positions,
                        possible_sources,
                    }
                } else {
                    let declared = union(&definitely_present, &union(&optional, &absent));
                    let row_bound = label_bound::T::TopMinus(declared);
                    let possibly_present =
                        label_bound::join(&label_bound::T::BottomPlus(optional), &row_bound);
                    let present_positions = positions_of_fields(&definitely_present);
                    let element = element::T {
                        definitely_present,
                        possibly_present,
                    };
                    let possible_sources = possible_sources::add(
                        optional_sources,
                        source(source_pos, "an open shape", row_bound),
                    );
                    T {
                        element,
                        present_positions,
                        possible_sources,
                    }
                }
            }
            Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                // Every element of a nested splat contributes to the outer one.
                let mut acc = empty();
                for elem in ss_elems.iter() {
                    acc = join(&acc, &of_ty_(solver, env, elem));
                }
                acc
            }
            Ty_::Tunion(tys) => match tys.as_slice() {
                [] => {
                    // The bottom row is uninhabited, so it can never overlap with anything.
                    empty()
                }
                [first, rest @ ..] => {
                    // Only labels present in every member remain certainly present; demote
                    // any other labels to be only possibly present
                    let mut acc = of_ty_(solver, env, first);
                    for member in rest.iter() {
                        let e = of_ty_(solver, env, member);
                        acc = join_alternatives(&acc, &e);
                    }
                    acc
                }
            },
            Ty_::Tintersection(tys) => match tys.as_slice() {
                [] => unknown(source_pos, "`mixed`"),
                [first, rest @ ..] => {
                    let mut acc = of_ty_(solver, env, first);
                    for member in rest.iter() {
                        let e = of_ty_(solver, env, member);
                        acc = intersect(&acc, &e);
                    }
                    acc
                }
            },
            Ty_::Tnewtype(name, _, _) => {
                let description = element::newtype_source(name);
                let possibly_present = solver::solve(solver, env, &ty);
                let element = element::T {
                    definitely_present: TShapeSet::new(),
                    possibly_present: possibly_present.clone(),
                };
                let present_positions = TShapeMap::new();
                let possible_sources = possible_sources::singleton(source(
                    source_pos,
                    &description,
                    possibly_present,
                ));
                T {
                    element,
                    present_positions,
                    possible_sources,
                }
            }
            Ty_::Toption(inner) => possible(&of_ty_(solver, env, inner)),
            Ty_::Tdependent(_, bound_ty) => possible(&of_ty_(solver, env, bound_ty)),
            Ty_::Tgeneric(name) => {
                let possibly_present = solver::solve(solver, env, &ty);
                let description = element::ty_param_source(name);
                let element = element::T {
                    definitely_present: TShapeSet::new(),
                    possibly_present: possibly_present.clone(),
                };
                let present_positions = TShapeMap::new();
                let possible_sources = possible_sources::singleton(source(
                    source_pos,
                    &description,
                    possibly_present,
                ));
                T {
                    element,
                    present_positions,
                    possible_sources,
                }
            }
            Ty_::Tdynamic(_) => {
                // A dynamic splat element is the open shape where each unknown field
                // has dynamic as its upper bound
                unknown(source_pos, "`dynamic`")
            }
            Ty_::Tvar(_) => unknown(source_pos, "an unresolved type variable"),
            Ty_::Tany(_)
            | Ty_::Tnonnull
            | Ty_::Tprim(_)
            | Ty_::Tfun(_)
            | Ty_::Ttuple(_)
            | Ty_::TvecOrDict(..)
            | Ty_::Taccess(_)
            | Ty_::TclassPtr(_)
            | Ty_::Tclass(..)
            | Ty_::Tneg(_)
            | Ty_::Tlabel(_) => of_other_type(env, source_pos, &ty),
        }
    }

    pub fn of_tys(tys: &[Ty], env: &Env) -> Vec<T> {
        let mut solver = solver::create();
        tys.iter().map(|ty| of_ty_(&mut solver, env, ty)).collect()
    }
}

mod possible_overlap {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct PossibleOverlap {
        pub positions: positions::T,
        pub sources: sources::T,
    }
}

fn add_positions(
    field: &TShapeField,
    positions: Vec<PosOrDecl>,
    map: &mut TShapeMap<positions::T>,
) {
    let previous = match map.get(field) {
        Some(previous) => previous.clone(),
        None => positions::empty(),
    };
    add(field.clone(), positions::add_list(previous, positions), map)
}

fn add_possible_overlap(
    field: &TShapeField,
    positions: Vec<PosOrDecl>,
    sources: Vec<OverlapSource>,
    overlaps: &mut TShapeMap<possible_overlap::PossibleOverlap>,
) {
    let previous = match overlaps.get(field) {
        Some(previous) => previous.clone(),
        None => possible_overlap::PossibleOverlap {
            positions: positions::empty(),
            sources: sources::empty(),
        },
    };
    add(
        field.clone(),
        possible_overlap::PossibleOverlap {
            positions: positions::add_list(previous.positions, positions),
            sources: sources::add_list(previous.sources, sources),
        },
        overlaps,
    )
}

/// `possibly possible certain sources positions labels` (the map `possible`
/// is updated in place).
fn possibly(
    possible: &mut TShapeMap<possible_overlap::PossibleOverlap>,
    certain: &TShapeSet,
    sources: &possible_sources::T,
    positions: &TShapeMap<positions::T>,
    labels: &TShapeSet,
) {
    if possible_sources::is_empty(sources) || labels.is_empty() {
    } else {
        let sources = possible_sources::elements(sources);
        for field in diff(labels, certain).iter() {
            let matching_sources: Vec<OverlapSource> = sources
                .iter()
                .filter_map(|source| {
                    if label_bound::restrict(&source.bound, &singleton(field.clone()))
                        .contains(field)
                    {
                        Some(source.source.clone())
                    } else {
                        None
                    }
                })
                .collect();
            if matching_sources.is_empty() {
            } else {
                let positions = positions::elements(&match positions.get(field) {
                    Some(positions) => positions.clone(),
                    None => positions::empty(),
                });
                add_possible_overlap(field, positions, matching_sources, possible)
            }
        }
    }
}

// -- API -------------------------------------------------------------------

/// Given a list of shape splat elements, [ss_elems], ranging over simple shapes
/// newtypes and type parameters, determine all groups of elements which violate
/// disjointness.
///
/// (`.mli`) Every way the localized elements of a splat may fail to be pairwise
/// disjoint. Field violations are grouped by label and retain every contributing
/// position. Empty iff every pair is provably disjoint.
pub fn violations(ss_elems: &[Ty], env: &Env) -> Vec<DisjointnessViolation> {
    // Convert each element to a representation with which we can reason about
    // fields which are definitely present (via simple shapes) and/or possible
    // present (via type parameters, new types etc)
    let detailed_elems = detailed_element::of_tys(ss_elems, env);
    let mut all = detailed_element::empty();
    let mut overlapping: TShapeMap<positions::T> = TShapeMap::new();
    let mut possible: TShapeMap<possible_overlap::PossibleOverlap> = TShapeMap::new();
    let mut has_unresolved = false;
    for detailed_elem in detailed_elems.iter() {
        let seen = &all;
        let seen_element = &seen.element;
        let element = &detailed_elem.element;

        // Known fields overlap
        let certain = inter(&element.definitely_present, &seen_element.definitely_present);
        for field in certain.iter() {
            let positions = |element: &detailed_element::T| match element
                .present_positions
                .get(field)
            {
                Some(positions) => positions.clone(),
                None => positions::empty(),
            };
            let new_positions = positions::elements(&positions(detailed_elem));
            let positions = if overlapping.contains_key(field) {
                new_positions
            } else {
                let mut l = positions::elements(&positions(seen));
                l.extend(new_positions);
                l
            };
            add_positions(field, positions, &mut overlapping)
        }

        // Known fields of one element overlap with fields which may be present
        // in the other
        possibly(
            &mut possible,
            &certain,
            &seen.possible_sources,
            &detailed_elem.present_positions,
            &element.definitely_present,
        );
        possibly(
            &mut possible,
            &certain,
            &detailed_elem.possible_sources,
            &seen.present_positions,
            &seen_element.definitely_present,
        );

        // Overlap in fields which may be present
        let seen_possible = &seen.possible_sources;
        let element_possible = &detailed_elem.possible_sources;
        has_unresolved = has_unresolved
            || (!possible_sources::is_empty(seen_possible))
                && (!possible_sources::is_empty(element_possible))
                && !label_bound::disjoint(
                    possible_sources::aggregate_bound(seen_possible),
                    possible_sources::aggregate_bound(element_possible),
                );
        all = detailed_element::join(seen, detailed_elem);
    }
    // `rev_violations` is consed onto and reversed at the end: here in order
    // (the overlapping fields, the possibly overlapping ones, each in the order
    // of the labels, and the unresolved sources).
    let mut violations: Vec<DisjointnessViolation> = vec![];
    for (field, position_set) in overlapping.iter() {
        violations.push(DisjointnessViolation::OverlappingField {
            label: name(field),
            positions: positions::elements(position_set),
        })
    }
    for (field, overlap) in possible.iter() {
        if overlapping.contains_key(field) {
        } else {
            let possible_overlap::PossibleOverlap { positions, sources } = overlap;
            violations.push(DisjointnessViolation::PossibleOverlappingField {
                label: name(field),
                positions: positions::elements(positions),
                sources: sources::elements(sources),
            })
        }
    }
    if has_unresolved {
        violations.push(DisjointnessViolation::UnresolvedSources {
            sources: possible_sources::sources(&all.possible_sources),
        })
    }
    violations
}

pub mod for_test {
    use super::*;

    /// `type label_bound = Label_bound.t = Bottom_plus of .. | Top_minus of ..`
    pub type LabelBound = label_bound::T;

    pub fn restrict(t: &LabelBound, labels: &TShapeSet) -> TShapeSet {
        label_bound::restrict(t, labels)
    }

    pub fn disjoint(t1: &LabelBound, t2: &LabelBound) -> bool {
        label_bound::disjoint(t1, t2)
    }

    pub fn join(t1: &LabelBound, t2: &LabelBound) -> LabelBound {
        label_bound::join(t1, t2)
    }

    pub fn meet(t1: &LabelBound, t2: &LabelBound) -> LabelBound {
        label_bound::meet(t1, t2)
    }

    /// `type element = Element.t`
    pub type Element = element::T;

    pub fn make_element(present: TShapeSet, bound: LabelBound) -> Element {
        element::T {
            definitely_present: present,
            possibly_present: bound,
        }
    }

    pub fn possible(element: &Element) -> Element {
        element::possible(element)
    }

    pub fn element_bound(element: &Element) -> &LabelBound {
        &element.possibly_present
    }
}

#[cfg(test)]
mod tests {
    use oxidized::typing_defs_core::PosByteString;
    use oxidized::typing_defs_core::TshapeFieldName;

    use super::for_test::*;
    use super::*;

    fn label(s: &str) -> TShapeField {
        TShapeField(TshapeFieldName::TSFlitStr(PosByteString(
            pos_or_decl::NONE,
            s.into(),
        )))
    }

    fn set(labels: &[&str]) -> TShapeSet {
        labels.iter().map(|s| label(s)).collect()
    }

    #[test]
    fn label_bounds() {
        let ab = label_bound::T::BottomPlus(set(&["a", "b"]));
        let c = label_bound::T::BottomPlus(set(&["c"]));
        let not_a = label_bound::T::TopMinus(set(&["a"]));
        assert!(disjoint(&ab, &c));
        assert!(!disjoint(&ab, &ab));
        // `{a, b}` against "everything but `a`": `b` may be in both.
        assert!(!disjoint(&ab, &not_a));
        assert!(disjoint(&label_bound::T::BottomPlus(set(&["a"])), &not_a));
        assert!(!disjoint(&not_a, &not_a));
        assert!(label_bound::equal(
            &join(&ab, &c),
            &label_bound::T::BottomPlus(set(&["a", "b", "c"]))
        ));
        assert!(label_bound::equal(
            &join(&ab, &not_a),
            &label_bound::top()
        ));
        assert!(label_bound::equal(
            &meet(&ab, &not_a),
            &label_bound::T::BottomPlus(set(&["b"]))
        ));
        assert_eq!(restrict(&not_a, &set(&["a", "b"])), set(&["b"]));
        assert_eq!(restrict(&ab, &set(&["a", "c"])), set(&["a"]));
    }

    #[test]
    fn possible_demotes_the_present_labels() {
        let e = make_element(set(&["a"]), label_bound::T::BottomPlus(set(&["b"])));
        let e = possible(&e);
        assert!(e.definitely_present.is_empty());
        assert!(label_bound::equal(
            element_bound(&e),
            &label_bound::T::BottomPlus(set(&["a", "b"]))
        ));
        let e = make_element(set(&["a"]), label_bound::T::TopMinus(set(&["a", "b"])));
        let e = possible(&e);
        assert!(label_bound::equal(
            element_bound(&e),
            &label_bound::T::TopMinus(set(&["b"]))
        ));
    }
}
