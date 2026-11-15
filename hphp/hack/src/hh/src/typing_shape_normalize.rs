// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_shape_normalize.ml`. See `hh/PORTING.md`.
//!
//! # The `nothing` cache of `merge`
//!
//! `merge` memoizes `Typing_utils.is_nothing` on its operands
//! (`splat_is_nothing`): an entry is valid while the inference environment is
//! the one it was computed in, which OCaml tests by physical equality
//! (`inference_env == env.inference_env`). `typing_inference_env::T` has no
//! notion of identity, so the cache keeps an [`InferenceEnvId`] instead: a
//! number that `merge` changes after each step that can change the inference
//! environment (merging shapes and finishing the accumulator, which take
//! unions, a fresh error type variable, finishing a distributed branch). An
//! entry is used only when no such step happened since it was made, so the
//! answer is always the one `is_nothing` would give. (OCaml can also miss
//! where this hits, after `strip_supportdyn` shortens a path of type
//! variables, which does not change what is solved; and hit where this misses,
//! after a union that leaves the inference environment as it was.)
//!
//! # The splat as a stack
//!
//! The OCaml lists that `merge` builds by consing (`rev_elems`, `elems`,
//! `errs`) are `VecDeque`s whose front is the head of the list.
//!
//! # `TShapeMap.add`
//!
//! OCaml's `Map.add` of a new value replaces the key of an existing binding
//! too (its positions); `BTreeMap::insert` keeps the old key, so the port
//! removes the binding first ([`tshape_map_add`]). When the value is
//! physically the binding already there, `Map.add` returns the map unchanged:
//! see `Shape_acc.merge_shape`.
//!
//! # Abstract types
//!
//! The types that the `.mli` makes abstract (`Row.t`, `Row.normalized`,
//! `Row.Opaque.t`, `Row.Element.t`) wrap a representation that only this
//! module sees. `Typing_utils.normalize_shape_type_ref` is set to
//! [`normalize_shape_type`] in `typing_utils.rs` itself (Rust has no module
//! initialisation).

use std::cell::Cell;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::rc::Rc;

use crate::pos_or_decl;
use crate::typing_defs;
use crate::typing_defs_core::ShapeFieldType;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::ShapeTypeSplat;
use crate::typing_defs_core::TshapeFieldName;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_defs_core::get_reason;
use crate::typing_defs_core::mk;
use crate::typing_defs_core::t_shape_field;
use crate::typing_defs_core::t_shape_map;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_intersection;
use crate::typing_make_type as make_type;
use crate::typing_reason;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;
use crate::typing_shape_splat_key;
use crate::typing_union;
use crate::typing_utils;

type TyErr = typing_error::T;

/// `TShapeMap.t`
type TShapeMap<V> = t_shape_map::T<V>;

/// `TShapeMap.add key v m`, for a value `v` that is not the binding of `key`
/// in `m`: the binding, key included, replaces any other one for the field.
fn tshape_map_add<V>(m: &mut TShapeMap<V>, key: t_shape_map::Key, v: V) {
    m.remove(&key);
    m.insert(key, v);
}

/// The identity of the inference environment, as far as the `nothing` cache of
/// `merge` can tell (see the module documentation).
type InferenceEnvId = u64;

/// [`Typing_shape_splat_key`] memoizes every kind of splat operand using its
/// structural identity. For [Tnewtype], it omits the stored bound because
/// [is_nothing] re-fetches it from the typedef. Comparing that bound directly
/// would follow both branches of chains such as [N1 as shape(...N2, ...N2)],
/// [N2 as shape(...N3, ...N3)], and so on, taking exponential time.
///
/// (`(Typing_inference_env.t * bool) Typing_shape_splat_key.Map.t ref`; the
/// inference environment of an entry is an [`InferenceEnvId`].)
struct NothingCache {
    entries: RefCell<typing_shape_splat_key::map::T<(InferenceEnvId, bool)>>,
    /// The current inference environment.
    inference_env: Cell<InferenceEnvId>,
}

impl NothingCache {
    fn new() -> Self {
        NothingCache {
            entries: RefCell::new(typing_shape_splat_key::map::T::new()),
            inference_env: Cell::new(0),
        }
    }

    /// The inference environment may be another one from now on.
    fn inference_env_may_have_changed(&self) {
        self.inference_env.set(self.inference_env.get() + 1)
    }
}

/// A path identifies an operand in the original nested splat/distribution tree.
///
/// Union distribution reprocesses the unvisited prefix once per element, so one
/// input operand may be visited in several generated branches. Its path is a
/// merge-local identity used to reuse one recovery type variable and report one
/// error, while keeping distinct equal-looking operands separate.
mod elem_path {
    use super::*;

    pub(super) mod ord {
        use super::*;

        /// `int list`, the head first.
        #[derive(Clone, Debug)]
        pub(crate) struct T(pub(crate) Vec<isize>);

        /// `List.compare Int.compare`
        pub(crate) fn compare(p1: &T, p2: &T) -> Ordering {
            p1.0.cmp(&p2.0)
        }

        impl PartialEq for T {
            fn eq(&self, other: &Self) -> bool {
                compare(self, other) == Ordering::Equal
            }
        }

        impl Eq for T {}

        impl PartialOrd for T {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(compare(self, other))
            }
        }

        impl Ord for T {
            fn cmp(&self, other: &Self) -> Ordering {
                compare(self, other)
            }
        }
    }

    pub(super) use ord::T;

    /// `index :: path`
    pub(super) fn cons(index: usize, path: &T) -> T {
        let mut l = Vec::with_capacity(path.0.len() + 1);
        l.push(index as isize);
        l.extend(path.0.iter().copied());
        T(l)
    }

    /// `[index]`
    pub(super) fn singleton(index: usize) -> T {
        T(vec![index as isize])
    }

    pub(super) mod map {
        pub(crate) type T<V> = std::collections::BTreeMap<super::T, V>;
    }

    pub(super) mod set {
        pub(crate) type T = std::collections::BTreeSet<super::T>;
    }
}

fn splat_is_nothing(cache: &NothingCache, env: &Env, ty: &Ty) -> bool {
    let key = typing_shape_splat_key::of_ty(ty);
    // `Some (inference_env, result) when inference_env == env.inference_env`
    if let Some((inference_env, result)) = cache.entries.borrow().get(&key) {
        if *inference_env == cache.inference_env.get() {
            return *result;
        }
    }
    let result = typing_utils::is_nothing(env, ty);
    cache
        .entries
        .borrow_mut()
        .insert(key, (cache.inference_env.get(), result));
    result
}

#[derive(Clone, Debug)]
pub enum MergeResult {
    /// The merge collapsed to a single type (a merged shape, or [nothing] for
    /// the bottom row). The [bool] is the supportdyn flag.
    Full(Ty, bool),
    /// The merge collapsed to the empty closed shape [shape()] — the unit for
    /// merge (e.g. spreading only empty shapes). We cannot build the [ty] here
    /// because the merge site has no [Reason.t] to attach to it; the caller,
    /// which does have a reason in scope, constructs the [shape()] type. The
    /// [bool] is the supportdyn flag.
    EmptyShape(bool),
    /// The operands could not be fully merged (e.g. a residual type variable);
    /// the remaining element list must be kept as a splat.
    Partial(Vec<Ty>, bool),
    /// A union operand was distributed outward: one fully-finalised type per
    /// union member (supportdyn already applied per member, so no [bool]). The
    /// caller unions these with its own reason (mirrors [Empty_shape], where
    /// the caller supplies the reason).
    Union(Vec<Ty>),
    /// As [Union], for an intersection operand: a value that is every member
    /// spreads to a row that is every member's row.
    Intersection(Vec<Ty>),
}

/// Merge field descriptors: under right-most wins semantics, we have:
/// - (Req _ | Opt _) , Req t -> Req t
/// - Req t_l, Opt t_r        -> Req (t_l | t_r)
/// - Opt t_l, Opt t_r        -> Opt (t_l | t_r)
pub fn merge_field_descs(
    fd_left: ShapeFieldType,
    fd_right: ShapeFieldType,
    env: &mut Env,
) -> ShapeFieldType {
    match (fd_left.optional, fd_right.optional) {
        (_, false) => {
            // Right-hand field is not optional so it 'wins'
            fd_right
        }
        (false, true) => {
            // Right-hand field is optional, left-hand field is not so we take the union
            // of their types and the resulting field is not optional
            // TODO[mjt] Record flow for extended reason
            let sft_ty = typing_union::union(env, None, None, fd_left.ty, fd_right.ty);
            ShapeFieldType {
                optional: false,
                ty: sft_ty,
            }
        }
        (true, true) => {
            // Both fields are optional; take the union of both types with the resulting
            // field also being optional
            // TODO[mjt] Record flow for extended reason
            let sft_ty = typing_union::union(env, None, None, fd_left.ty, fd_right.ty);
            ShapeFieldType {
                optional: true,
                ty: sft_ty,
            }
        }
    }
}

/// Optimized accumulator, keeping required and optional fields separate
mod shape_acc {
    use super::*;

    /// Open-row bounds are stored newest-first in binary-sized chunks. A field's
    /// depth identifies its pending prefix, which has at most logarithmic chunks.
    pub(super) mod widenings {
        use super::*;

        #[derive(Debug)]
        pub(crate) enum Chunk {
            Leaf(Ty),
            Node {
                size: isize,
                union: Ty,
                newer: Rc<Chunk>,
                older: Rc<Chunk>,
            },
        }

        #[derive(Clone, Debug)]
        pub(crate) struct T {
            depth: isize,
            /// The head of the OCaml list first.
            chunks: Vec<Rc<Chunk>>,
        }

        fn chunk_size(chunk: &Chunk) -> isize {
            match chunk {
                Chunk::Leaf(_) => 1,
                Chunk::Node { size, .. } => *size,
            }
        }

        fn chunk_union(chunk: &Chunk) -> Ty {
            match chunk {
                Chunk::Leaf(ty) => ty.clone(),
                Chunk::Node { union, .. } => union.clone(),
            }
        }

        pub(crate) fn empty() -> T {
            T {
                depth: 0,
                chunks: vec![],
            }
        }

        pub(crate) fn singleton(ty: Ty) -> T {
            T {
                depth: 1,
                chunks: vec![Rc::new(Chunk::Leaf(ty))],
            }
        }

        pub(crate) fn depth(widenings: &T) -> isize {
            widenings.depth
        }

        pub(crate) fn add(env: &mut Env, ty: Ty, widenings: &T) -> T {
            fn carry(env: &mut Env, newer: Rc<Chunk>, chunks: &[Rc<Chunk>]) -> Vec<Rc<Chunk>> {
                match chunks {
                    [older, chunks @ ..] if chunk_size(&newer) == chunk_size(older) => {
                        let union = typing_union::union(
                            env,
                            None,
                            None,
                            chunk_union(&newer),
                            chunk_union(older),
                        );
                        let newer = Rc::new(Chunk::Node {
                            size: chunk_size(&newer) + chunk_size(older),
                            union,
                            newer,
                            older: older.clone(),
                        });
                        carry(env, newer, chunks)
                    }
                    chunks => {
                        let mut l = Vec::with_capacity(chunks.len() + 1);
                        l.push(newer);
                        l.extend(chunks.iter().cloned());
                        l
                    }
                }
            }
            let chunks = carry(env, Rc::new(Chunk::Leaf(ty)), &widenings.chunks);
            T {
                depth: widenings.depth + 1,
                chunks,
            }
        }

        fn chunk_prefix(count: isize, chunk: &Chunk) -> Vec<Ty> {
            if count == chunk_size(chunk) {
                vec![chunk_union(chunk)]
            } else {
                match chunk {
                    Chunk::Leaf(_) => panic!("invalid widening prefix"),
                    Chunk::Node { newer, older, .. } => {
                        let newer_size = chunk_size(newer);
                        if count <= newer_size {
                            chunk_prefix(count, newer)
                        } else {
                            let rest = chunk_prefix(count - newer_size, older);
                            let mut l = Vec::with_capacity(rest.len() + 1);
                            l.push(chunk_union(newer));
                            l.extend(rest);
                            l
                        }
                    }
                }
            }
        }

        fn prefix(count: isize, chunks: &[Rc<Chunk>]) -> Vec<Ty> {
            match chunks {
                _ if count == 0 => vec![],
                [] => panic!("invalid widening depth"),
                [chunk, chunks @ ..] => {
                    let size = chunk_size(chunk);
                    if count < size {
                        chunk_prefix(count, chunk)
                    } else {
                        let rest = prefix(count - size, chunks);
                        let mut l = Vec::with_capacity(rest.len() + 1);
                        l.push(chunk_union(chunk));
                        l.extend(rest);
                        l
                    }
                }
            }
        }

        /// `apply env (union :: unions) ty` is
        /// `Typing_union.union env union (apply env unions ty)`.
        fn apply(env: &mut Env, unions: &[Ty], ty: Ty) -> Ty {
            match unions {
                [] => ty,
                [union, unions @ ..] => {
                    let ty = apply(env, unions, ty);
                    typing_union::union(env, None, None, union.clone(), ty)
                }
            }
        }

        pub(crate) fn apply_since(env: &mut Env, widenings: &T, since: isize, ty: Ty) -> Ty {
            let count = widenings.depth - since;
            let unions = prefix(count, &widenings.chunks);
            apply(env, &unions, ty)
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            fn prim(p: oxidized::ast_defs::Tprim) -> Ty {
                mk((typing_reason::none(), Ty_::Tprim(p)))
            }

            fn is_prim(ty: &Ty, p: oxidized::ast_defs::Tprim) -> bool {
                matches!(get_node(ty), Ty_::Tprim(q) if *q == p)
            }

            #[test]
            fn prefixes_take_the_newest_widenings() {
                use oxidized::ast_defs::Tprim;
                // a, then b, then c were added: `[Leaf c; Node (b | a)]`; the
                // union of a chunk stands for all of its widenings.
                let (a, b, c) = (prim(Tprim::Tint), prim(Tprim::Tbool), prim(Tprim::Tfloat));
                let ab = prim(Tprim::Tnum);
                let node = Rc::new(Chunk::Node {
                    size: 2,
                    union: ab,
                    newer: Rc::new(Chunk::Leaf(b)),
                    older: Rc::new(Chunk::Leaf(a)),
                });
                let w = T {
                    depth: 3,
                    chunks: vec![Rc::new(Chunk::Leaf(c)), node],
                };
                assert!(prefix(0, &w.chunks).is_empty());
                let p1 = prefix(1, &w.chunks);
                assert!(p1.len() == 1 && is_prim(&p1[0], Tprim::Tfloat));
                let p2 = prefix(2, &w.chunks);
                assert!(
                    p2.len() == 2 && is_prim(&p2[0], Tprim::Tfloat) && is_prim(&p2[1], Tprim::Tbool)
                );
                let p3 = prefix(3, &w.chunks);
                assert!(
                    p3.len() == 2 && is_prim(&p3[0], Tprim::Tfloat) && is_prim(&p3[1], Tprim::Tnum)
                );
                assert_eq!(depth(&w), 3);
                assert_eq!(depth(&singleton(prim(Tprim::Tint))), 1);
                assert_eq!(depth(&empty()), 0);
            }

            #[test]
            #[should_panic(expected = "invalid widening depth")]
            fn prefixes_cannot_be_deeper_than_the_widenings() {
                prefix(1, &[]);
            }
        }
    }

    #[derive(Clone, Debug)]
    pub(crate) struct OptionalField {
        field: ShapeFieldType,
        widened_at: isize,
    }

    #[derive(Clone, Debug)]
    pub(crate) struct T {
        origin: TypeOrigin,
        unknown_value: Ty,
        /// The maps have disjoint keys and their values agree with the map's
        /// requiredness. An absent field from an open left row can only change
        /// optional fields.
        required_fields: TShapeMap<ShapeFieldType>,
        optional_fields: TShapeMap<OptionalField>,
        widenings: widenings::T,
    }

    fn row_is_closed(unknown_value: &Ty) -> bool {
        match get_node(unknown_value) {
            Ty_::Tunion(tyl) if tyl.is_empty() => true,
            _ => false,
        }
    }

    pub(crate) fn of_simple(shape: ShapeTypeSimple) -> T {
        let ShapeTypeSimple {
            origin: s_origin,
            unknown_value: s_unknown_value,
            fields: s_fields,
        } = shape;
        let widenings = if row_is_closed(&s_unknown_value) {
            widenings::empty()
        } else {
            widenings::singleton(s_unknown_value.clone())
        };
        let widened_at = widenings::depth(&widenings);
        // `TShapeMap.fold`, into maps that start empty.
        let mut required_fields = TShapeMap::new();
        let mut optional_fields = TShapeMap::new();
        for (key, field) in s_fields {
            if field.optional {
                optional_fields.insert(key, OptionalField { field, widened_at });
            } else {
                required_fields.insert(key, field);
            }
        }
        T {
            origin: s_origin,
            unknown_value: s_unknown_value,
            required_fields,
            optional_fields,
            widenings,
        }
    }

    /// `TShapeMap.mapi`, threading the environment (in the order of the keys).
    fn map_fields_env<A, B>(
        mut f: impl FnMut(&mut Env, &t_shape_map::Key, &A) -> B,
        env: &mut Env,
        fields: &TShapeMap<A>,
    ) -> TShapeMap<B> {
        let mut res = TShapeMap::new();
        for (key, field) in fields {
            let field = f(env, key, field);
            res.insert(key.clone(), field);
        }
        res
    }

    fn materialize_optional(
        env: &mut Env,
        widenings: &widenings::T,
        optional: &OptionalField,
    ) -> ShapeFieldType {
        let sft_ty = widenings::apply_since(
            env,
            widenings,
            optional.widened_at,
            optional.field.ty.clone(),
        );
        ShapeFieldType {
            ty: sft_ty,
            ..optional.field.clone()
        }
    }

    pub(crate) fn to_simple(env: &mut Env, acc: &T) -> ShapeTypeSimple {
        let optional_fields = map_fields_env(
            |env, _, optional| materialize_optional(env, &acc.widenings, optional),
            env,
            &acc.optional_fields,
        );
        let s_fields = if acc.required_fields.is_empty() {
            optional_fields
        } else {
            // `TShapeMap.union ~combine:(fun _ _ _ -> failwith ...)`
            let mut s_fields = acc.required_fields.clone();
            for (key, field) in optional_fields {
                if s_fields.contains_key(&key) {
                    panic!("Shape_acc: field is both required and optional")
                }
                s_fields.insert(key, field);
            }
            s_fields
        };
        ShapeTypeSimple {
            origin: acc.origin.clone(),
            unknown_value: acc.unknown_value.clone(),
            fields: s_fields,
        }
    }

    pub(crate) fn merge_shape(
        shape_left: &ShapeTypeSimple,
        shape_right: &T,
        env: &mut Env,
    ) -> T {
        let left_row_closed = row_is_closed(&shape_left.unknown_value);
        let widened_at =
            widenings::depth(&shape_right.widenings) + if left_row_closed { 0 } else { 1 };
        // `TShapeMap.fold ... shape_left.s_fields (env, shape_right.required_fields,
        // shape_right.optional_fields)`
        let mut required = shape_right.required_fields.clone();
        let mut optional = shape_right.optional_fields.clone();
        for (key, fd_left) in &shape_left.fields {
            // Whether `fd_right` is the binding of `shape_right.required_fields`
            // (and so of `required`, where only the other keys change).
            let (fd_right, fd_right_is_required_binding) =
                match shape_right.required_fields.get(key) {
                    Some(fd) => (fd.clone(), true),
                    None => match shape_right.optional_fields.get(key) {
                        Some(fd) => (
                            materialize_optional(env, &shape_right.widenings, fd),
                            false,
                        ),
                        None => (
                            ShapeFieldType {
                                optional: true,
                                ty: shape_right.unknown_value.clone(),
                            },
                            false,
                        ),
                    },
                };
            // `merge_field_descs` returns `fd_right` itself when it is required.
            let fd_is_required_binding = fd_right_is_required_binding && !fd_right.optional;
            let fd = merge_field_descs(fd_left.clone(), fd_right, env);
            if fd.optional {
                required.remove(key);
                tshape_map_add(
                    &mut optional,
                    key.clone(),
                    OptionalField {
                        field: fd,
                        widened_at,
                    },
                );
            } else {
                // `TShapeMap.add key fd required`: when `fd` is physically the
                // binding of `required`, `Map.add` returns the map unchanged,
                // and the binding keeps its key.
                if !fd_is_required_binding {
                    tshape_map_add(&mut required, key.clone(), fd);
                }
                optional.remove(key);
            }
        }
        let widenings = if left_row_closed {
            shape_right.widenings.clone()
        } else {
            widenings::add(
                env,
                shape_left.unknown_value.clone(),
                &shape_right.widenings,
            )
        };
        let unknown_value = typing_union::union(
            env,
            None,
            None,
            shape_left.unknown_value.clone(),
            shape_right.unknown_value.clone(),
        );
        T {
            origin: TypeOrigin::MissingOrigin,
            unknown_value,
            required_fields: required,
            optional_fields: optional,
            widenings,
        }
    }
}

#[derive(Clone, Debug)]
enum MergeElem {
    Empty,
    Merging(Reason, shape_acc::T),
    Bottom(Reason),
}

/// Turn the merge accumulator (once the element list is exhausted) into a
/// [merge_result].
fn finalize(env: &mut Env, merge_elem: MergeElem, elems: Vec<Ty>, sd: bool) -> MergeResult {
    match (merge_elem, elems.is_empty()) {
        (MergeElem::Bottom(reason), _) => {
            // The whole type is [nothing].
            MergeResult::Full(make_type::nothing(reason), false)
        }
        (MergeElem::Merging(reason, shape_acc), true) => {
            let shape = shape_acc::to_simple(env, &shape_acc);
            MergeResult::Full(
                mk((reason, Ty_::Tshape(ShapeType::ShapeSimple(shape)))),
                sd,
            )
        }
        (MergeElem::Merging(reason, shape_acc), false) => {
            let shape = shape_acc::to_simple(env, &shape_acc);
            let elem = mk((reason, Ty_::Tshape(ShapeType::ShapeSimple(shape))));
            let mut l = Vec::with_capacity(elems.len() + 1);
            l.push(elem);
            l.extend(elems);
            MergeResult::Partial(l, sd)
        }
        (MergeElem::Empty, true) => {
            // Everything cancelled to the unit element: the empty closed shape. The
            // caller supplies the reason with which to build [shape()].
            MergeResult::EmptyShape(sd)
        }
        (MergeElem::Empty, false) => MergeResult::Partial(elems, sd),
    }
}

/// Finalise one distributed branch to a single type, built with the member's
/// [reason]. supportdyn is applied per-branch here, so distributed results
/// carry no sd flag.
fn result_to_ty(reason: Reason, env: &mut Env, res: MergeResult) -> Ty {
    let wrap = |sd: bool, ty: Ty| {
        if sd {
            make_type::supportdyn(get_reason(&ty).clone(), ty)
        } else {
            ty
        }
    };
    match res {
        MergeResult::Full(ty, sd) => wrap(sd, ty),
        MergeResult::EmptyShape(sd) => wrap(sd, make_type::closed_shape(reason, TShapeMap::new())),
        // A splat of one element and nothing else IS that element.
        MergeResult::Partial(mut ss_elems, sd) if ss_elems.len() == 1 => {
            wrap(sd, ss_elems.pop().unwrap())
        }
        MergeResult::Partial(ss_elems, sd) => wrap(
            sd,
            mk((reason, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })))),
        ),
        MergeResult::Union(tys) => {
            // Nested union (a member itself distributed): flatten by unioning.
            typing_union::union_list(env, None, reason, &tys)
        }
        MergeResult::Intersection(tys) => typing_intersection::intersect_list(env, reason, &tys),
    }
}

/// The state that the closures of `merge` share (the OCaml `ref`s).
struct MergeState {
    on_error: Option<reasons_callback::T>,
    nothing_cache: NothingCache,
    invalid_tyvars: RefCell<elem_path::map::T<Ty>>,
    reported_invalids: RefCell<elem_path::set::T>,
}

impl MergeState {
    fn error_tyvar(&self, path: &elem_path::T, reason: &Reason, env: &mut Env) -> Ty {
        if let Some(ty) = self.invalid_tyvars.borrow().get(path) {
            return ty.clone();
        }
        let ty = typing_env::fresh_type_error(
            env,
            pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(reason)),
        );
        self.nothing_cache.inference_env_may_have_changed();
        self.invalid_tyvars
            .borrow_mut()
            .insert(path.clone(), ty.clone());
        ty
    }

    /// `errs` is the OCaml list, the head at the front.
    fn add_splat_not_a_shape_error(
        &self,
        path: &elem_path::T,
        reason: &Reason,
        errs: &mut VecDeque<TyErr>,
    ) {
        if self.reported_invalids.borrow().contains(path) {
        } else {
            self.reported_invalids.borrow_mut().insert(path.clone());
            match &self.on_error {
                None => {}
                Some(on_error) => {
                    let err = typing_error::apply_reasons(
                        secondary::T::SplatNotAShape(typing_reason::to_pos(reason)),
                        on_error.clone(),
                    );
                    errs.push_front(err)
                }
            }
        }
    }
}

fn bottom_result(ty: &Ty) -> MergeResult {
    MergeResult::Full(make_type::nothing(get_reason(ty).clone()), false)
}

fn union_result(tys: Vec<Ty>) -> MergeResult {
    match tys.split_first() {
        Some((first, rest))
            if typing_defs::is_nothing(first) && rest.iter().all(typing_defs::is_nothing) =>
        {
            bottom_result(first)
        }
        _ => MergeResult::Union(tys),
    }
}

fn intersection_result(tys: Vec<Ty>) -> MergeResult {
    match tys.iter().find(|ty| typing_defs::is_nothing(ty)) {
        Some(bottom) => bottom_result(bottom),
        None => MergeResult::Intersection(tys),
    }
}

/// `loop rev_elems (merge_elem, elems, errs, sd, env)` of `merge`. The lists
/// are the OCaml lists, the head at the front.
fn loop_(
    st: &MergeState,
    mut rev_elems: VecDeque<(elem_path::T, Ty)>,
    mut merge_elem: MergeElem,
    mut elems: VecDeque<Ty>,
    mut errs: VecDeque<TyErr>,
    mut sd: bool,
    env: &mut Env,
) -> (VecDeque<TyErr>, MergeResult) {
    loop {
        let (path, ty) = match rev_elems.pop_front() {
            None => {
                let result = finalize(env, merge_elem, elems.into_iter().collect(), sd);
                return (errs, result);
            }
            Some(elem) => elem,
        };
        // Under sound dynamic a non-enforceable splat operand (e.g. an open
        // shape, whose unknown fields are [mixed]) is localized wrapped in
        // [supportdyn<...>]. Strip it so we can see the underlying shape, and
        // remember that the normalized result must be wrapped back up in
        // [supportdyn] to stay sound. Closed shapes with enforceable fields are
        // not wrapped, so this leaves them (and the [everything_sdt=false] case)
        // untouched.
        let (sd_elem, ty) = typing_utils::strip_supportdyn(env, ty);
        let ty_reason = get_reason(&ty).clone();
        match (get_node(&ty), &merge_elem) {
            // -- Merge identity --------------------------------------------------
            (Ty_::Tshape(ShapeType::ShapeSimple(shape_left)), _)
                if shape_left.fields.is_empty()
                    && splat_is_nothing(&st.nothing_cache, env, &shape_left.unknown_value) =>
            {
                // The empty closed shape is unit for merge
                sd = sd || sd_elem;
            }
            // -- Merge with bottom on rhs ----------------------------------------
            (
                Ty_::Tshape(_)
                | Ty_::Tgeneric(_)
                | Ty_::Tnewtype(_, _, _)
                | Ty_::Tvar(_)
                | Ty_::Tdynamic(_),
                MergeElem::Bottom(_),
            ) => {
                // We don't accumulate elements since the resulting type will be
                // [nothing]
            }
            // -- Merge with bottom on both sides ---------------------------------
            (_, MergeElem::Bottom(_)) if splat_is_nothing(&st.nothing_cache, env, &ty) => {
                // Spreading [nothing] onto the bottom row stays bottom; don't fall
                // through to the error case below
            }
            // -- Start accumulating ----------------------------------------------
            (Ty_::Tshape(ShapeType::ShapeSimple(shape)), MergeElem::Empty) => {
                // Start accumulating the merged shape
                let shape = shape.clone();
                merge_elem = MergeElem::Merging(ty_reason, shape_acc::of_simple(shape));
                sd = sd || sd_elem;
            }
            // Keep both [Tshape] cases before [splat_is_nothing]: otherwise nested
            // splats are re-traversed at every depth and simple shapes are needlessly
            // cached. Canonical [nothing] still falls through to the bottom check.
            // -- Flatten nested splats -------------------------------------------
            // Any bottom element exposed by flattening is still handled by the loop.
            (
                Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })),
                MergeElem::Empty | MergeElem::Merging(_, _),
            ) => {
                sd = sd || sd_elem;
                // `List.rev (List.mapi (fun index ty -> (index :: path, ty)) ss_elems)
                // @ rev_elems`
                for (index, ty) in ss_elems.iter().enumerate() {
                    rev_elems.push_front((elem_path::cons(index, &path), ty.clone()));
                }
            }
            // -- Merge simple shapes ---------------------------------------------
            (
                Ty_::Tshape(ShapeType::ShapeSimple(shape_left)),
                MergeElem::Merging(reason, shape_right),
            ) => {
                let reason = reason.clone();
                let shape = shape_acc::merge_shape(shape_left, shape_right, env);
                st.nothing_cache.inference_env_may_have_changed();
                merge_elem = MergeElem::Merging(reason, shape);
                sd = sd || sd_elem;
            }
            // -- Merge with bottom as the left element ---------------------------
            (_, MergeElem::Empty | MergeElem::Merging(_, _))
                if splat_is_nothing(&st.nothing_cache, env, &ty) =>
            {
                // speading [nothing] gives us the bottom row: a row in which the
                // all unknown fields are required, irrespective of their type or the
                // presence of known fields. Elsewhere we don't collapse shapes with
                // known required fields with type [nothing] to bottom but we HAVE to
                // here since we have no other representation
                merge_elem = MergeElem::Bottom(ty_reason);
            }
            // -- Accumulate opaque elements --------------------------------------
            // Type variables, type parameters, and newtypes. A newtype is opaque
            // outside its defining file and behaves exactly like a rigid parameter;
            // inside, localization has already expanded it to its definition.
            (
                Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) | Ty_::Tvar(_),
                MergeElem::Merging(shape_reason, shape_acc),
            ) => {
                let shape_reason = shape_reason.clone();
                let shape = shape_acc::to_simple(env, shape_acc);
                st.nothing_cache.inference_env_may_have_changed();
                // `ty :: elem :: elems`
                let elem = mk((shape_reason, Ty_::Tshape(ShapeType::ShapeSimple(shape))));
                elems.push_front(elem);
                elems.push_front(ty.clone());
                merge_elem = MergeElem::Empty;
                sd = sd || sd_elem;
            }
            (Ty_::Tgeneric(_) | Ty_::Tnewtype(_, _, _) | Ty_::Tvar(_), MergeElem::Empty) => {
                elems.push_front(ty.clone());
                merge_elem = MergeElem::Empty;
                sd = sd || sd_elem;
            }
            // -- Spread dynamic as an open row with dynamic as upper bound -------
            (Ty_::Tdynamic(_), MergeElem::Merging(reason, shape_right)) => {
                let shape_left = ShapeTypeSimple {
                    origin: TypeOrigin::MissingOrigin,
                    unknown_value: ty.clone(),
                    fields: TShapeMap::new(),
                };
                let reason = reason.clone();
                let shape = shape_acc::merge_shape(&shape_left, shape_right, env);
                st.nothing_cache.inference_env_may_have_changed();
                merge_elem = MergeElem::Merging(reason, shape);
                sd = sd || sd_elem;
            }
            (Ty_::Tdynamic(_), MergeElem::Empty) => {
                let shape = ShapeTypeSimple {
                    origin: TypeOrigin::MissingOrigin,
                    unknown_value: ty.clone(),
                    fields: TShapeMap::new(),
                };
                merge_elem = MergeElem::Merging(ty_reason, shape_acc::of_simple(shape));
                sd = sd || sd_elem;
            }
            // -- Distribute a union operand --------------------------------------
            // [shape(...A, ...(m1 | ... | mk), ...B)] distributes to
            // [shape(...A, ...m1, ...B) | ... | shape(...A, ...mk, ...B)]
            (Ty_::Tunion(members), _) => {
                let members = members.clone();
                return distribute(
                    st,
                    &path,
                    rev_elems,
                    (merge_elem, elems, errs, sd || sd_elem),
                    env,
                    &members,
                    union_result,
                );
            }
            // -- Distribute an intersection operand -----------------------------
            // [shape(...A, ...(m1 & ... & mk), ...B)] is
            // [shape(...A, ...m1, ...B) & ... & shape(...A, ...mk, ...B)]
            (Ty_::Tintersection(members), _) if !members.is_empty() => {
                let members = members.clone();
                return distribute(
                    st,
                    &path,
                    rev_elems,
                    (merge_elem, elems, errs, sd || sd_elem),
                    env,
                    &members,
                    intersection_result,
                );
            }
            // -- Error conditions ------------------------------------------------
            (_, MergeElem::Merging(shape_reason, shape_acc)) => {
                let shape_reason = shape_reason.clone();
                let elem_err = st.error_tyvar(&path, &ty_reason, env);
                let shape = shape_acc::to_simple(env, shape_acc);
                st.nothing_cache.inference_env_may_have_changed();
                // `elem_err :: elem_shape :: elems`
                let elem_shape = mk((shape_reason, Ty_::Tshape(ShapeType::ShapeSimple(shape))));
                elems.push_front(elem_shape);
                elems.push_front(elem_err);
                st.add_splat_not_a_shape_error(&path, &ty_reason, &mut errs);
                merge_elem = MergeElem::Empty;
            }
            (_, MergeElem::Empty) => {
                let elem_err = st.error_tyvar(&path, &ty_reason, env);
                elems.push_front(elem_err);
                merge_elem = MergeElem::Empty;
                st.add_splat_not_a_shape_error(&path, &ty_reason, &mut errs);
            }
            (_, MergeElem::Bottom(_)) => {
                // Still report malformed splats despite being bottom.
                st.add_splat_not_a_shape_error(&path, &ty_reason, &mut errs);
            }
        }
    }
}

/// `distribute path rev_elems (merge_elem, elems, errs, sd, env) members
/// ~make_result` of `merge`.
fn distribute(
    st: &MergeState,
    path: &elem_path::T,
    rev_elems: VecDeque<(elem_path::T, Ty)>,
    (merge_elem, elems, errs, sd): (MergeElem, VecDeque<Ty>, VecDeque<TyErr>, bool),
    env: &mut Env,
    members: &[Ty],
    make_result: fn(Vec<Ty>) -> MergeResult,
) -> (VecDeque<TyErr>, MergeResult) {
    let members: Vec<(elem_path::T, Ty)> = members
        .iter()
        .enumerate()
        .map(|(index, member)| (elem_path::cons(index, path), member.clone()))
        .collect();
    // `List.concat error_groups`, where `error_groups` starts as `[errs]` and
    // each branch puts its errors in front.
    let mut error_groups = errs;
    let mut branch_tys = Vec::with_capacity(members.len());
    for (path, member) in members {
        // [errs] belongs to the already-processed suffix. Branch-local
        // errors start empty; the per-element cache prevents a shared
        // prefix from reporting the same malformed operand again.
        let member_reason = get_reason(&member).clone();
        let mut branch_rev_elems = rev_elems.clone();
        branch_rev_elems.push_front((path, member));
        let (branch_errs, res) = loop_(
            st,
            branch_rev_elems,
            merge_elem.clone(),
            elems.clone(),
            VecDeque::new(),
            sd,
            env,
        );
        let ty = result_to_ty(member_reason, env, res);
        st.nothing_cache.inference_env_may_have_changed();
        for err in branch_errs.into_iter().rev() {
            error_groups.push_front(err)
        }
        branch_tys.push(ty);
    }
    (error_groups, make_result(branch_tys))
}

/// Merge adjacent simple shapes in a list. Used during shape normalization in
/// localization and subtyping. If all elements are simple shapes the result
/// will be a single element list which is itself a simple shape. Otherwise,
/// the list will be simple shapes interspersed with spreads of other types.
/// If we encounter a type which cannot be spread we raise an error and replace
/// it with a fresh type variable representing the error so as to avoid
/// re-raising the error later. We don't check the bounds of type parameters
/// at this point so they may well lead to ill-formed shapes and errors will
/// be reported during subtyping
pub fn merge(
    on_error: Option<reasons_callback::T>,
    elems: Vec<Ty>,
    env: &mut Env,
) -> (Option<TyErr>, MergeResult) {
    let st = MergeState {
        on_error,
        nothing_cache: NothingCache::new(),
        invalid_tyvars: RefCell::new(BTreeMap::new()),
        reported_invalids: RefCell::new(BTreeSet::new()),
    };
    // Merge simple shape elements from right to left so reverse the list.
    // [loop] finalises via [finalize] at its base case (and via [result_to_ty]
    // per branch for a distributed union or intersection).
    let rev_elems: VecDeque<(elem_path::T, Ty)> = elems
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (elem_path::singleton(index), ty))
        .rev()
        .collect();
    let (errs, result) = loop_(
        &st,
        rev_elems,
        MergeElem::Empty,
        VecDeque::new(),
        VecDeque::new(),
        false,
        env,
    );
    (typing_error::multiple_opt(errs.into_iter().collect()), result)
}

#[derive(Clone, Debug)]
pub enum NormalizeResult {
    NormalizedShape(ShapeType),
    NormalizedUnion(Vec<Ty>),
    NormalizedIntersection(Vec<Ty>),
    /// The merge collapsed to the bottom row [nothing]: the row is
    /// uninhabited.
    NormalizedBottom,
}

/// A normalized local shape row, including the uninhabited bottom row.
///
/// A single operand is lifted to a simple shape, type parameter, inference
/// variable, or newtype case. A multi-element splat contains only those
/// operands, contains at least one opaque operand, and never contains
/// adjacent shape fragments.
pub mod row {
    use super::*;

    pub mod opaque {
        use super::*;

        /// `type t` (abstract in the `.mli`)
        #[derive(Clone, Debug)]
        pub struct T(Repr);

        #[derive(Clone, Debug)]
        enum Repr {
            TypeParameter(Ty),
            TypeVariable(Ty),
            Newtype(Ty),
        }

        #[derive(Clone, Debug)]
        pub enum View {
            TypeParameter(Ty),
            TypeVariable(Ty),
            Newtype(Ty),
        }

        pub fn view(opaque: &T) -> View {
            match &opaque.0 {
                Repr::TypeParameter(ty) => View::TypeParameter(ty.clone()),
                Repr::TypeVariable(ty) => View::TypeVariable(ty.clone()),
                Repr::Newtype(ty) => View::Newtype(ty.clone()),
            }
        }

        pub fn ty(opaque: &T) -> Ty {
            match &opaque.0 {
                Repr::TypeParameter(ty) | Repr::TypeVariable(ty) | Repr::Newtype(ty) => {
                    ty.clone()
                }
            }
        }

        pub(super) fn of_ty(ty: Ty) -> T {
            match get_node(&ty) {
                Ty_::Tgeneric(_) => T(Repr::TypeParameter(ty)),
                Ty_::Tvar(_) => T(Repr::TypeVariable(ty)),
                Ty_::Tnewtype(_, _, _) => T(Repr::Newtype(ty)),
                _ => panic!("non-opaque type in normalized shape splat"),
            }
        }
    }

    pub type Simple = (Reason, ShapeTypeSimple);

    #[derive(Clone, Debug)]
    pub enum AfterOpaque {
        End,
        NextShape(Simple, Box<AfterShape>),
        NextOpaque(opaque::T, Box<AfterOpaque>),
    }

    #[derive(Clone, Debug)]
    pub enum AfterShape {
        EndAfterShape,
        OpaqueAfterShape(opaque::T, Box<AfterOpaque>),
    }

    #[derive(Clone, Debug)]
    pub enum AfterOpaqueNonempty {
        FirstShape(Simple, AfterShape),
        FirstOpaque(opaque::T, AfterOpaque),
    }

    /// `type t` (abstract in the `.mli`)
    #[derive(Clone, Debug)]
    pub struct T(pub(super) Repr);

    #[derive(Clone, Debug)]
    pub(super) enum Repr {
        Bottom,
        Simple(ShapeTypeSimple),
        TypeParameter(Ty),
        TypeVariable(Ty),
        Newtype(Ty),
        OpaqueFirst(opaque::T, AfterOpaqueNonempty),
        ShapeFirst(Simple, opaque::T, AfterOpaque),
    }

    /// `type normalized` (abstract in the `.mli`)
    #[derive(Clone, Debug)]
    pub struct Normalized(pub(super) NormalizedRepr);

    #[derive(Clone, Debug)]
    pub(super) enum NormalizedRepr {
        NormalizedRow(T),
        NormalizedUnion(Vec<Ty>),
        NormalizedIntersection(Vec<Ty>),
    }

    pub fn as_row(normalized: Normalized) -> Option<T> {
        match normalized.0 {
            NormalizedRepr::NormalizedRow(row) => Some(row),
            NormalizedRepr::NormalizedUnion(_) | NormalizedRepr::NormalizedIntersection(_) => None,
        }
    }

    pub fn fold_normalized<A>(
        normalized: Normalized,
        row: impl FnOnce(T) -> A,
        union: impl FnOnce(Vec<Ty>) -> A,
        intersection: impl FnOnce(Vec<Ty>) -> A,
    ) -> A {
        match normalized.0 {
            NormalizedRepr::NormalizedRow(normalized) => row(normalized),
            NormalizedRepr::NormalizedUnion(tys) => union(tys),
            NormalizedRepr::NormalizedIntersection(tys) => intersection(tys),
        }
    }

    fn of_opaque(opaque: opaque::T) -> T {
        match opaque::view(&opaque) {
            opaque::View::TypeParameter(ty) => T(Repr::TypeParameter(ty)),
            opaque::View::TypeVariable(ty) => T(Repr::TypeVariable(ty)),
            opaque::View::Newtype(ty) => T(Repr::Newtype(ty)),
        }
    }

    pub mod element {
        use super::*;

        /// `type t` (abstract in the `.mli`)
        #[derive(Clone, Debug)]
        pub struct T(Repr);

        #[derive(Clone, Debug)]
        enum Repr {
            Shape(Simple),
            Opaque(opaque::T),
        }

        #[derive(Clone, Debug)]
        pub enum View {
            Shape(Simple),
            Opaque(opaque::T),
        }

        pub fn view(element: &T) -> View {
            match &element.0 {
                Repr::Shape(shape) => View::Shape(shape.clone()),
                Repr::Opaque(opaque) => View::Opaque(opaque.clone()),
            }
        }

        pub fn ty(element: &T) -> Ty {
            match &element.0 {
                Repr::Shape((reason, shape)) => mk((
                    reason.clone(),
                    Ty_::Tshape(ShapeType::ShapeSimple(shape.clone())),
                )),
                Repr::Opaque(opaque) => opaque::ty(opaque),
            }
        }

        pub(super) fn shape(shape: Simple) -> T {
            T(Repr::Shape(shape))
        }

        pub(super) fn opaque(opaque: opaque::T) -> T {
            T(Repr::Opaque(opaque))
        }
    }

    pub fn is_bottom(row: &T) -> bool {
        match &row.0 {
            Repr::Bottom => true,
            Repr::Simple(_)
            | Repr::TypeParameter(_)
            | Repr::TypeVariable(_)
            | Repr::Newtype(_)
            | Repr::OpaqueFirst(_, _)
            | Repr::ShapeFirst(_, _, _) => false,
        }
    }

    pub fn as_simple(row: &T) -> Option<ShapeTypeSimple> {
        match &row.0 {
            Repr::Simple(shape) => Some(shape.clone()),
            Repr::Bottom
            | Repr::TypeParameter(_)
            | Repr::TypeVariable(_)
            | Repr::Newtype(_)
            | Repr::OpaqueFirst(_, _)
            | Repr::ShapeFirst(_, _, _) => None,
        }
    }

    pub fn of_simple(shape: ShapeTypeSimple) -> T {
        T(Repr::Simple(shape))
    }

    fn after_opaque_elements(rest: &AfterOpaque) -> Vec<element::T> {
        match rest {
            AfterOpaque::End => vec![],
            AfterOpaque::NextShape(shape, rest) => {
                let mut l = vec![element::shape(shape.clone())];
                l.extend(after_shape_elements(rest));
                l
            }
            AfterOpaque::NextOpaque(opaque, rest) => {
                let mut l = vec![element::opaque(opaque.clone())];
                l.extend(after_opaque_elements(rest));
                l
            }
        }
    }

    fn after_shape_elements(rest: &AfterShape) -> Vec<element::T> {
        match rest {
            AfterShape::EndAfterShape => vec![],
            AfterShape::OpaqueAfterShape(opaque, rest) => {
                let mut l = vec![element::opaque(opaque.clone())];
                l.extend(after_opaque_elements(rest));
                l
            }
        }
    }

    fn elements(row: &T) -> Vec<element::T> {
        match &row.0 {
            Repr::Bottom => vec![],
            Repr::Simple(shape) => vec![element::shape((typing_reason::none(), shape.clone()))],
            Repr::TypeParameter(ty) | Repr::TypeVariable(ty) | Repr::Newtype(ty) => {
                vec![element::opaque(opaque::of_ty(ty.clone()))]
            }
            Repr::OpaqueFirst(opaque, rest) => {
                let mut l = vec![element::opaque(opaque.clone())];
                match rest {
                    AfterOpaqueNonempty::FirstShape(shape, rest) => {
                        l.push(element::shape(shape.clone()));
                        l.extend(after_shape_elements(rest))
                    }
                    AfterOpaqueNonempty::FirstOpaque(opaque, rest) => {
                        l.push(element::opaque(opaque.clone()));
                        l.extend(after_opaque_elements(rest))
                    }
                }
                l
            }
            Repr::ShapeFirst(shape, opaque, rest) => {
                let mut l = vec![
                    element::shape(shape.clone()),
                    element::opaque(opaque.clone()),
                ];
                l.extend(after_opaque_elements(rest));
                l
            }
        }
    }

    /// Eliminate a row without exposing its normalized representation.
    /// [elements] receives the spread-position sequence for every inhabited row
    /// that is not a simple shape.
    pub fn fold<A>(
        row: &T,
        bottom: impl FnOnce() -> A,
        simple: impl FnOnce(&ShapeTypeSimple) -> A,
        fold_elements: impl FnOnce(Vec<element::T>) -> A,
    ) -> A {
        match &row.0 {
            Repr::Bottom => bottom(),
            Repr::Simple(shape) => simple(shape),
            Repr::TypeParameter(_)
            | Repr::TypeVariable(_)
            | Repr::Newtype(_)
            | Repr::OpaqueFirst(_, _)
            | Repr::ShapeFirst(_, _, _) => fold_elements(elements(row)),
        }
    }

    fn shape_of_ty(ty: &Ty) -> Option<Simple> {
        match get_node(ty) {
            Ty_::Tshape(ShapeType::ShapeSimple(shape)) => {
                Some((get_reason(ty).clone(), shape.clone()))
            }
            _ => None,
        }
    }

    // (The components of the OCaml constructors are evaluated from right to
    // left: the rest of the list first.)
    fn splat_of_elems(elems: &[Ty]) -> T {
        fn after_opaque(elems: &[Ty]) -> AfterOpaque {
            match elems {
                [] => AfterOpaque::End,
                [first, rest @ ..] => match shape_of_ty(first) {
                    Some(shape) => {
                        let rest = after_shape(rest);
                        AfterOpaque::NextShape(shape, Box::new(rest))
                    }
                    None => {
                        let rest = after_opaque(rest);
                        AfterOpaque::NextOpaque(opaque::of_ty(first.clone()), Box::new(rest))
                    }
                },
            }
        }
        fn after_shape(elems: &[Ty]) -> AfterShape {
            match elems {
                [] => AfterShape::EndAfterShape,
                [first, rest @ ..] => match shape_of_ty(first) {
                    Some(_) => panic!("contiguous shapes in normalized shape splat"),
                    None => {
                        let rest = after_opaque(rest);
                        AfterShape::OpaqueAfterShape(opaque::of_ty(first.clone()), Box::new(rest))
                    }
                },
            }
        }
        match elems {
            [] => panic!("empty normalized shape splat"),
            [only] => match shape_of_ty(only) {
                Some(_) => panic!("singleton shape must normalize to a simple row"),
                None => of_opaque(opaque::of_ty(only.clone())),
            },
            [first, rest @ ..] => match shape_of_ty(first) {
                None => match rest {
                    [] => unreachable!("assert false"),
                    [second, rest @ ..] => match shape_of_ty(second) {
                        Some(shape) => {
                            let rest = after_shape(rest);
                            let rest = AfterOpaqueNonempty::FirstShape(shape, rest);
                            T(Repr::OpaqueFirst(opaque::of_ty(first.clone()), rest))
                        }
                        None => {
                            let rest = after_opaque(rest);
                            let second = opaque::of_ty(second.clone());
                            let rest = AfterOpaqueNonempty::FirstOpaque(second, rest);
                            T(Repr::OpaqueFirst(opaque::of_ty(first.clone()), rest))
                        }
                    },
                },
                Some(shape) => match rest {
                    [] => panic!("normalized shape splat contains no opaque operand"),
                    [opaque, rest @ ..] => {
                        let rest = after_opaque(rest);
                        let opaque = opaque::of_ty(opaque.clone());
                        T(Repr::ShapeFirst(shape, opaque, rest))
                    }
                },
            },
        }
    }

    #[cfg(test)]
    pub(super) fn splat_of_elems_for_test(elems: &[Ty]) -> T {
        splat_of_elems(elems)
    }

    fn of_merge_result(reason: Reason, res: MergeResult) -> T {
        match res {
            MergeResult::Full(ty, _) => match get_node(&ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(shape)) => T(Repr::Simple(shape.clone())),
                Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })) => {
                    splat_of_elems(ss_elems)
                }
                _ => T(Repr::Bottom),
            },
            MergeResult::EmptyShape(_) => T(Repr::Simple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: make_type::nothing(reason),
                fields: TShapeMap::new(),
            })),
            MergeResult::Partial(elems, _) if elems.is_empty() => T(Repr::Simple(ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                unknown_value: make_type::nothing(reason),
                fields: TShapeMap::new(),
            })),
            MergeResult::Partial(elems, _) => splat_of_elems(&elems),
            MergeResult::Union(_) | MergeResult::Intersection(_) => {
                panic!("a distributed result is not a normalized row")
            }
        }
    }

    pub fn to_ty(reason: Reason, row: &T) -> Ty {
        match &row.0 {
            Repr::Bottom => make_type::nothing(reason),
            Repr::Simple(shape) => mk((reason, Ty_::Tshape(ShapeType::ShapeSimple(shape.clone())))),
            Repr::TypeParameter(ty) | Repr::TypeVariable(ty) | Repr::Newtype(ty) => ty.clone(),
            Repr::OpaqueFirst(_, _) | Repr::ShapeFirst(_, _, _) => {
                let mut ss_elems: Vec<Ty> = elements(row).iter().map(element::ty).collect();
                if ss_elems.len() == 1 {
                    ss_elems.pop().unwrap()
                } else {
                    mk((reason, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }))))
                }
            }
        }
    }

    pub fn normalize(
        on_error: Option<reasons_callback::T>,
        reason: Reason,
        shape_ty: ShapeType,
        env: &mut Env,
    ) -> (Option<TyErr>, Normalized) {
        let elems = match shape_ty {
            ShapeType::ShapeSimple(_) => vec![mk((reason.clone(), Ty_::Tshape(shape_ty)))],
            ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems }) => ss_elems,
        };
        let (err_opt, result) = merge(on_error, elems, env);
        let normalized = match result {
            MergeResult::Union(tys) => NormalizedRepr::NormalizedUnion(tys),
            MergeResult::Intersection(tys) => NormalizedRepr::NormalizedIntersection(tys),
            result => NormalizedRepr::NormalizedRow(of_merge_result(reason, result)),
        };
        (err_opt, Normalized(normalized))
    }

    pub fn normalized_to_ty(env: &mut Env, reason: Reason, normalized: Normalized) -> Ty {
        match normalized.0 {
            NormalizedRepr::NormalizedRow(row) => to_ty(reason, &row),
            NormalizedRepr::NormalizedUnion(tys) => typing_union::union_list(env, None, reason, &tys),
            NormalizedRepr::NormalizedIntersection(tys) => {
                typing_intersection::intersect_list(env, reason, &tys)
            }
        }
    }
}

pub fn normalize_shape_type(
    on_error: Option<reasons_callback::T>,
    reason: Reason,
    shape_ty: ShapeType,
    env: &mut Env,
) -> (Option<TyErr>, NormalizeResult) {
    // [_sd] (whether an element carried [supportdyn]) is unused here: the return
    // is a bare [shape_type] which cannot hold a [supportdyn] wrapper, and
    // subtyping reasons about dynamic separately.
    let (err_opt, normalized) = row::normalize(on_error, reason.clone(), shape_ty, env);
    let distributed_to_shape = |ty: Ty| match get_node(&ty) {
        Ty_::Tunion(tys) if tys.is_empty() => NormalizeResult::NormalizedBottom,
        Ty_::Tunion(tys) => NormalizeResult::NormalizedUnion(tys.clone()),
        Ty_::Tintersection(tys) => NormalizeResult::NormalizedIntersection(tys.clone()),
        Ty_::Tshape(shape_ty) => NormalizeResult::NormalizedShape(shape_ty.clone()),
        _ => NormalizeResult::NormalizedShape(ShapeType::ShapeSplat(ShapeTypeSplat {
            ss_elems: vec![ty.clone()],
        })),
    };
    // `Row.fold_normalized normalized ~row ~union ~intersection` (the
    // callbacks of `union` and `intersection` would both need the environment).
    let res = match normalized.0 {
        row::NormalizedRepr::NormalizedRow(row) => match row.0 {
            row::Repr::Simple(shape) => NormalizeResult::NormalizedShape(ShapeType::ShapeSimple(shape)),
            row::Repr::TypeParameter(_)
            | row::Repr::TypeVariable(_)
            | row::Repr::Newtype(_)
            | row::Repr::OpaqueFirst(_, _)
            | row::Repr::ShapeFirst(_, _, _) => {
                let ty = row::to_ty(reason, &row);
                match get_node(&ty) {
                    Ty_::Tshape(shape_ty) => NormalizeResult::NormalizedShape(shape_ty.clone()),
                    _ => NormalizeResult::NormalizedShape(ShapeType::ShapeSplat(ShapeTypeSplat {
                        ss_elems: vec![ty],
                    })),
                }
            }
            row::Repr::Bottom => NormalizeResult::NormalizedBottom,
        },
        row::NormalizedRepr::NormalizedUnion(tys) => {
            let ty = typing_union::union_list(env, None, reason, &tys);
            distributed_to_shape(ty)
        }
        row::NormalizedRepr::NormalizedIntersection(tys) => {
            let ty = typing_intersection::intersect_list(env, reason, &tys);
            distributed_to_shape(ty)
        }
    };
    (err_opt, res)
}

/// Canonical constructor for a shape splat: normalize [elems] and return the
/// result in normal form. Every operation that rewrites a row must build its
/// result with this rather than assembling a [Shape_splat] by hand -- rewriting
/// can empty an element, leave a lone element, or make two simple shapes
/// adjacent, none of which are normal forms.
pub fn splat(
    on_error: Option<reasons_callback::T>,
    reason: Reason,
    elems: Vec<Ty>,
    env: &mut Env,
) -> (Option<TyErr>, Ty) {
    let (err_opt, res) = merge(on_error, elems, env);
    let ty = result_to_ty(reason, env, res);
    (err_opt, ty)
}

fn pessimize_existing_fields(
    overwritten_field: &TshapeFieldName,
    reason: &Reason,
    env: &mut Env,
    elems: &[Ty],
) -> Vec<Ty> {
    match elems {
        [] => vec![],
        [ty, rest @ ..] => {
            let ty = match get_node(ty) {
                Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
                    let r = get_reason(ty).clone();
                    let s_unknown_value =
                        typing_utils::make_supportdyn(reason.clone(), env, s.unknown_value.clone());
                    let s_fields = t_shape_map::map_env(
                        |env: &mut Env, name: &t_shape_map::Key, field_ty: ShapeFieldType| {
                            if t_shape_field::equal(&name.0, overwritten_field) {
                                field_ty
                            } else {
                                let ShapeFieldType {
                                    optional: sft_optional,
                                    ty: sft_ty,
                                } = field_ty;
                                let sft_ty = typing_utils::make_supportdyn(reason.clone(), env, sft_ty);
                                ShapeFieldType {
                                    optional: sft_optional,
                                    ty: sft_ty,
                                }
                            }
                        },
                        env,
                        s.fields.clone(),
                    );
                    mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: s_unknown_value,
                            fields: s_fields,
                        })),
                    ))
                }
                _ => ty.clone(),
            };
            let rest = pessimize_existing_fields(overwritten_field, reason, env, rest);
            let mut l = Vec::with_capacity(rest.len() + 1);
            l.push(ty);
            l.extend(rest);
            l
        }
    }
}

/// Set [field] to [field_ty] on a shape splat under rightmost-wins semantics. A
/// field write is a runtime dict write, so it may add a new field or overwrite
/// an existing one, and the written field must win over every element. It is
/// therefore set on the rightmost element: if that element is a concrete simple
/// shape the field is added or overwritten there in place; otherwise (a type
/// parameter, variable or nested splat) a new closed simple shape carrying just
/// the field is appended.
///
/// If [pessimize_existing] is set, the row came from beneath [supportdyn], so
/// every existing concrete field, including the unknown-field tail, must retain
/// that pessimization after the outer wrapper is removed. The newly written
/// field remains precise.
pub fn set_rightmost_field(
    elems: &[Ty],
    field: TshapeFieldName,
    field_ty: ShapeFieldType,
    pessimize_existing: bool,
    reason: Reason,
    env: &mut Env,
) -> (Option<TyErr>, Ty) {
    let elems = if pessimize_existing {
        pessimize_existing_fields(&field, &reason, env, elems)
    } else {
        elems.to_vec()
    };
    let field = t_shape_map::TShapeField(field);
    let append = |mut elems: Vec<Ty>, field: t_shape_map::Key, field_ty: ShapeFieldType| {
        let mut s_fields = TShapeMap::new();
        s_fields.insert(field, field_ty);
        let s = ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: make_type::nothing(reason.clone()),
            fields: s_fields,
        };
        elems.push(mk((reason.clone(), Ty_::Tshape(ShapeType::ShapeSimple(s)))));
        elems
    };
    // `match List.rev elems with last :: rev_rest -> ...`
    let last_shape = match elems.last() {
        Some(last) => match get_node(last) {
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => Some((get_reason(last).clone(), s.clone())),
            _ => None,
        },
        None => None,
    };
    let elems = match last_shape {
        Some((r, s)) => {
            let mut s_fields = s.fields;
            tshape_map_add(&mut s_fields, field, field_ty);
            let s = ShapeTypeSimple {
                origin: TypeOrigin::MissingOrigin,
                fields: s_fields,
                ..s
            };
            let mut elems = elems;
            elems.pop();
            elems.push(mk((r, Ty_::Tshape(ShapeType::ShapeSimple(s)))));
            elems
        }
        None => append(elems, field, field_ty),
    };
    splat(None, reason, elems, env)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r() -> Reason {
        typing_reason::none()
    }

    fn generic(name: &str) -> Ty {
        mk((r(), Ty_::Tgeneric(name.to_string())))
    }

    fn closed(fields: Vec<(&str, bool, Ty)>) -> ShapeTypeSimple {
        let mut m = TShapeMap::new();
        for (name, optional, ty) in fields {
            m.insert(
                t_shape_map::TShapeField(TshapeFieldName::TSFlitStr(
                    crate::typing_defs_core::PosByteString(
                        oxidized::pos::Pos::NONE,
                        bstr::BString::from(name),
                    ),
                )),
                ShapeFieldType { optional, ty },
            );
        }
        ShapeTypeSimple {
            origin: TypeOrigin::MissingOrigin,
            unknown_value: make_type::nothing(r()),
            fields: m,
        }
    }

    fn shape_ty(s: ShapeTypeSimple) -> Ty {
        mk((r(), Ty_::Tshape(ShapeType::ShapeSimple(s))))
    }

    #[test]
    fn rows_round_trip_through_elements() {
        let s = closed(vec![("a", false, make_type::int(r()))]);
        // shape('a' => int, ...T, ...U)
        let row = row::splat_of_elems_for_test(&[shape_ty(s.clone()), generic("T"), generic("U")]);
        assert!(!row::is_bottom(&row));
        assert!(row::as_simple(&row).is_none());
        let tys = row::fold(&row, || vec![], |_| vec![], |els| {
            els.iter().map(row::element::ty).collect::<Vec<_>>()
        });
        assert_eq!(tys.len(), 3);
        assert!(matches!(get_node(&tys[1]), Ty_::Tgeneric(n) if n == "T"));
        // A simple row folds to `simple`
        let simple = row::of_simple(s);
        assert!(row::fold(&simple, || false, |_| true, |_| false));
        // A lone parameter is its own type
        let t = row::splat_of_elems_for_test(&[generic("T")]);
        assert!(matches!(get_node(&row::to_ty(r(), &t)), Ty_::Tgeneric(n) if n == "T"));
    }

    #[test]
    #[should_panic(expected = "contiguous shapes in normalized shape splat")]
    fn contiguous_shapes_are_rejected() {
        let s = closed(vec![]);
        row::splat_of_elems_for_test(&[generic("T"), shape_ty(s.clone()), shape_ty(s)]);
    }

    #[test]
    fn result_shapes() {
        assert!(matches!(
            union_result(vec![make_type::nothing(r()), make_type::nothing(r())]),
            MergeResult::Full(ty, false) if typing_defs::is_nothing(&ty)
        ));
        assert!(matches!(
            union_result(vec![make_type::nothing(r()), make_type::int(r())]),
            MergeResult::Union(tys) if tys.len() == 2
        ));
        assert!(matches!(
            intersection_result(vec![make_type::int(r()), make_type::nothing(r())]),
            MergeResult::Full(ty, false) if typing_defs::is_nothing(&ty)
        ));
    }

    #[test]
    fn elem_paths_cons_at_the_head() {
        let p = elem_path::cons(2, &elem_path::singleton(1));
        assert_eq!(p.0, vec![2, 1]);
        assert!(elem_path::ord::compare(&elem_path::singleton(1), &p) == Ordering::Less);
    }
}
