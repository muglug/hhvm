// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Part of the port of `typing_subtype.ml` (lines 11229-11318): module `Subtype_ask`.
//! See `hh/PORTING.md`.
//!
//! The functions of this module answer a question and return no environment
//! (`let (_env, prop) = ...` in OCaml): they take `&Env` and simplify in a
//! copy of it.
//!
//! `Common.dispatch_constraint` is called as
//! `common::dispatch_constraint(&subtype_env, this_ty: Option<&Ty>,
//! sub_supportdyn: Option<Reason>, ity_sub: InternalType, ity_super:
//! InternalType, env: &mut Env) -> tl::SubtypeProp` (the shape of the
//! `simplify` of the prelude's `ConstraintHandler`).

use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_core;
use crate::typing_env_types::Env;
use crate::typing_logic as tl;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::common;
use crate::typing_subtype::prelude::*;

pub fn is_sub_type_alt_i(
    require_completeness: bool,
    no_top_bottom: bool,
    is_dynamic_aware: bool,
    sub_supportdyn: Option<Reason>,
    env: &Env,
    ity_sub: &InternalType,
    ity_super: &InternalType,
) -> Option<bool> {
    // Not in the OCaml, which only saves work: physically equal types, and
    // the answers remembered by `memo` (see there for why they cannot change).
    let memo_query = match (ity_sub, ity_super, &sub_supportdyn) {
        (InternalType::LoclType(sub), InternalType::LoclType(sup), None)
            if env.log_levels.is_empty() =>
        {
            // The first step of the simplifier (`simplify_` checks
            // physical equality before anything else, and the environment
            // that `dispatch_constraint` changes is dropped).
            if !env.genv.tcopt.tco_disable_physical_equality
                && typing_defs_core::phys_equal(sub, sup)
            {
                return Some(true);
            }
            let flags = memo::flags(require_completeness, no_top_bottom, is_dynamic_aware);
            match memo::lookup(env, sub, sup, flags) {
                memo::Lookup::Hit(res) if !memo::verify() => return res,
                // Checking the memo against the simplifier (whose answer is
                // returned).
                memo::Lookup::Hit(res) => Some((sub, sup, Err(res))),
                memo::Lookup::Miss(miss) => Some((sub, sup, Ok((flags, miss)))),
                memo::Lookup::Unsupported => None,
            }
        }
        _ => None,
    };
    let ids_before = memo_query.as_ref().map(|_| memo::ids(env));
    let this_ty = match ity_sub {
        InternalType::LoclType(ty1) => Some(ty1),
        InternalType::ConstraintType(_) => None,
    };
    let subtype_env = subtype_env::create(
        None,                       // require_soundness
        Some(require_completeness), // require_completeness
        None,                       // ignore_readonly
        Some(no_top_bottom),        // no_top_bottom
        Some(is_dynamic_aware),     // is_dynamic_aware
        None,                       // is_coeffect
        None,                       // in_transitive_closure
        None,                       // ignore_likes
        None,                       // has_member_arg_posl
        None,                       // report_ambiguous_shape_splat
        should_cls_sub_cn(env),     // class_sub_classname
        3,                          // log_level
        None,
    );
    // It is weird that this can cause errors, but I am wary to discard them.
    // Using the generic unify_error to maintain current behavior.
    // (The OCaml drops the environment that `dispatch_constraint` returns:
    // simplify in a copy.)
    let prop = common::dispatch_constraint(
        &subtype_env,
        this_ty,
        sub_supportdyn,
        ity_sub.clone(),
        ity_super.clone(),
        &mut env.clone(),
    );

    let res = if tl::is_valid(&prop) {
        Some(true)
    } else if tl::is_unsat(&prop) {
        Some(false)
    } else {
        None
    };
    match (memo_query, ids_before) {
        (Some((sub, sup, Ok((flags, miss)))), Some(ids_before)) => {
            // A query that made type variables or expression ids (the
            // providers are shared with the dropped copy) is not remembered:
            // answering it from the memo would not make them.
            if memo::ids(env) == ids_before {
                memo::record(miss, sub, sup, flags, res);
            }
        }
        (Some((sub, sup, Err(remembered))), _) if remembered != res => {
            eprintln!(
                "HH_ASK_MEMO_VERIFY: remembered {:?}, simplifier {:?}: {} <: {}",
                remembered,
                res,
                crate::typing_print::debug(env, sub),
                crate::typing_print::debug(env, sup)
            );
        }
        _ => {}
    }
    res
}

/// A per-thread memo of the answers of [`is_sub_type_alt_i`] for two
/// localized types. Not in the OCaml: it only saves work (the same question
/// is asked again and again: `is_mixed`/`is_nothing` on the same types, the
/// pairwise queries of the unions of the same lists of types, ...).
///
/// What is remembered, and why the answer cannot change:
///
/// - The types are compared structurally, ignoring reasons and positions
///   (which the simplifier only puts in errors, and an answer has none).
/// - Only types without type variables, generic parameters, dependent types
///   or type accesses (`Tdynamic` with a shadow type variable included): the
///   simplifier then reads nothing of the inference environment or of the
///   type parameter environment.
/// - No negation and no intersection anywhere in them: the simplifier is
///   incomplete for those, so that `t <: t` can be valid only through the
///   physical equality shortcut, and the answer for two structurally equal
///   queries could depend on which nodes they share. For the other types,
///   a structural `t <: t` is valid, so the shortcut changes no answer.
///   Likewise no shape splat, tuple splat, class refinement, or function
///   type with type parameters or where constraints.
/// - Per value of the flags of the query (the subtype environment is
///   otherwise the default one, and `sub_supportdyn` is `None`).
/// - Per context: the fields of the global environment that subtyping can
///   read (the options, the file, the module and package, `self`... of the
///   definition being checked, compared by `same_genv`) and the value of
///   `env.checked` (the dynamic assumptions). Those are the only parts of the
///   environment that the simplifier reads for such types besides the
///   declarations (fixed for the whole check; in the daemon, the memos of a
///   thread are forgotten when they change, `crate::rt::decl_epoch`). The
///   memos of the last few contexts are kept. When dependency edges are
///   recorded, the definition being checked is part of the context too
///   (`decl_epoch::Dependent`): the simplifier's lookups record the edges
///   of that definition, which a hit for another one would lose.
/// - Each node of an accepted type gets, once, the number of its class of
///   structurally equal types (`TyNode::memo_serial`): a per-thread table
///   maps the structure of a node (its constructor, names and flags, and the
///   numbers of the types in it) to a representative node and its number. A
///   number is never given to two different structures (numbers are not
///   reused, also when the table is emptied), so that two nodes with the
///   same number are structurally equal, and a query is a pair of numbers.
/// - Queries that fail these conditions only by the kinds of
///   types in them (a negation, an intersection, ...), but in which no type
///   variable, generic, dependent type or type access occurs, are remembered
///   for their very nodes only: such a node gets a number of its own, that
///   no other node of the thread has. The query is then the same input to
///   the simplifier (the same nodes, so the same sharing too), in the same
///   context, about types in which nothing of the environment that may
///   change occurs (`TyNode::flags`), so that it gives the same answer.
/// - Not when the query made a type variable or an expression id (the
///   providers are shared between copies of the environment, so that making
///   them is visible after the copy is dropped), and not when logging.
pub(crate) mod memo {
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::collections::hash_map;
    use std::hash::BuildHasherDefault;
    use std::hash::Hasher;
    use std::rc::Rc;

    use oxidized::typing_defs_core::TshapeFieldName;

    use crate::ident_provider;
    use crate::rt::decl_epoch::Dependent;
    use crate::tast::CheckStatus;
    use crate::typing_defs_core::Capability;
    use crate::typing_defs_core::Exact;
    use crate::typing_defs_core::ShapeType;
    use crate::typing_defs_core::TupleExtra;
    use crate::typing_defs_core::Ty;
    use crate::typing_defs_core::TyNode;
    use crate::typing_defs_core::Ty_;
    use crate::typing_env_types::Env;
    use crate::typing_env_types::Genv;

    /// More entries than a definition needs; the memo is emptied when it is
    /// reached.
    const MAX_ENTRIES: usize = 50_000;

    /// The table of classes is emptied when it has this many.
    const MAX_CLASSES: usize = 1 << 17;

    /// Fx-style hashing of words, with the high half folded into the low
    /// bits (hashbrown takes the bucket from the low bits).
    #[derive(Default)]
    struct WordHasher(u64);

    impl Hasher for WordHasher {
        #[inline]
        fn finish(&self) -> u64 {
            self.0 ^ (self.0 >> 32)
        }
        fn write(&mut self, _: &[u8]) {
            unreachable!()
        }
        #[inline]
        fn write_u64(&mut self, x: u64) {
            self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
        #[inline]
        fn write_u16(&mut self, x: u16) {
            self.write_u64(x as u64)
        }
    }

    type WordMap<K, V> = HashMap<K, V, BuildHasherDefault<WordHasher>>;

    /// A query: the numbers of the two nodes, and the flags.
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    struct Key(u64, u16);

    /// The answers for one global environment and value of `checked`.
    struct Memo {
        /// Names this memo (and its context) in a [`Miss`].
        id: u32,
        /// The global environment last seen in this context, held weakly:
        /// an environment that updates its own (`set_param`...) would have
        /// to copy it if the memo shared it. Its allocation is kept, so a
        /// global environment at the same address is this one, unchanged
        /// (`Rc::make_mut` moves the value of an `Rc` that has only weak
        /// references to a new allocation).
        genv: std::rc::Weak<Genv>,
        /// A copy of the global environment of the context, to compare by
        /// value with `same_genv`.
        key: Rc<Genv>,
        checked: CheckStatus,
        /// The definition the dependency edges are recorded for, when they
        /// are (see `crate::rt::decl_epoch::Dependent`): the answers of
        /// one dependent are not given to another, which would lose the
        /// edges of the lookups the simplifier made for them.
        dependent: Dependent,
        entries: WordMap<Key, Option<bool>>,
    }

    struct State {
        memos: Vec<Memo>,
        next_id: u32,
        /// The structural hash of a node -> a node with that structure and
        /// its number (another structure with the same hash gets a number
        /// of its own, not in the table).
        classes: WordMap<u64, (Rc<TyNode>, u32)>,
        /// The classes of the nodes that [`small_key`] describes in full.
        small_classes: WordMap<(u64, u64), u32>,
        /// The last number given to a node.
        last_number: u32,
    }

    /// The memos of the last few contexts, the most recently used first
    /// (checking a lambda changes the global environment, and returning
    /// from it restores the enclosing one).
    const CONTEXTS: usize = 4;

    thread_local! {
        static MEMO: RefCell<State> = RefCell::new(State {
            memos: Vec::new(),
            next_id: 0,
            classes: WordMap::default(),
            small_classes: WordMap::default(),
            last_number: 0,
        });
    }

    pub(crate) enum Lookup {
        Hit(Option<bool>),
        /// Not known: what [`record`] needs.
        Miss(Miss),
        /// Not a query the memo answers.
        Unsupported,
    }

    /// A query not found by [`lookup`].
    pub(crate) struct Miss {
        /// The memo of the context of the query.
        memo_id: u32,
    }

    /// `HH_ASK_MEMO_VERIFY` set: compare every answer found in the memo with
    /// the simplifier's, and report on stderr when they differ.
    pub(crate) fn verify() -> bool {
        static VERIFY: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *VERIFY.get_or_init(|| std::env::var_os("HH_ASK_MEMO_VERIFY").is_some())
    }

    /// The key of a query of `Subtype_tell` (see `subtype_tell::tell_memo`):
    /// the fields of the subtype environment that can change its outcome,
    /// told apart from the queries of [`super::is_sub_type_alt_i`].
    pub(crate) fn tell_flags(subtype_env: &crate::typing_subtype::prelude::subtype_env::T) -> u16 {
        let bits = [
            subtype_env.require_soundness,
            subtype_env.require_completeness,
            subtype_env.ignore_readonly,
            subtype_env.no_top_bottom,
            subtype_env.is_dynamic_aware,
            subtype_env.is_coeffect,
            subtype_env.in_transitive_closure,
            subtype_env.ignore_likes,
            subtype_env.class_sub_classname,
            subtype_env.report_ambiguous_shape_splat,
            subtype_env.on_error.is_some(),
        ];
        bits.iter().fold(0u16, |acc, &b| (acc << 1) | b as u16) | 1 << 15
    }

    pub(super) fn flags(require_completeness: bool, no_top_bottom: bool, is_dynamic_aware: bool) -> u16 {
        (require_completeness as u16) | (no_top_bottom as u16) << 1 | (is_dynamic_aware as u16) << 2
    }

    /// The next type variable and expression ids.
    pub(crate) fn ids(env: &Env) -> (isize, isize) {
        (
            ident_provider::peek(&env.tvar_id_provider),
            ident_provider::peek(&env.expression_id_provider),
        )
    }

    /// FxHash's mixing step.
    struct H(u64);

    impl H {
        #[inline]
        fn add(&mut self, x: u64) {
            self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
        fn bytes(&mut self, s: &[u8]) {
            let mut chunks = s.chunks_exact(8);
            for c in &mut chunks {
                self.add(u64::from_le_bytes(c.try_into().unwrap()));
            }
            let mut last = [0u8; 8];
            let rest = chunks.remainder();
            last[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(last) ^ (s.len() as u64) << 56);
        }
        fn opt_str(&mut self, s: &Option<String>) {
            match s {
                None => self.add(0),
                Some(s) => self.bytes(s.as_bytes()),
            }
        }
    }

    fn shape_field_name(h: &mut H, name: &TshapeFieldName) {
        match name {
            TshapeFieldName::TSFregexGroup(s) => {
                h.add(1);
                h.bytes(s.1.as_bytes())
            }
            TshapeFieldName::TSFlitStr(s) => {
                h.add(2);
                h.bytes(&s.1)
            }
            TshapeFieldName::TSFclassConst(c, s) => {
                h.add(3);
                h.bytes(c.1.as_bytes());
                h.bytes(s.1.as_bytes())
            }
        }
    }

    /// The value of `TyNode::memo_hash` for a node not accepted (0: not
    /// known yet; any other value: accepted, and `memo_serial` is the number
    /// of its class).
    const REJECTED: u64 = 1;

    /// A number not given before; 0 when there are no more (never in
    /// practice: the node is then not remembered).
    fn fresh_number(last_number: &mut u32) -> u32 {
        if *last_number == u32::MAX {
            return 0;
        }
        *last_number += 1;
        *last_number
    }

    /// The number of the class of an accepted node (see the module
    /// documentation), computed once per node; `None` if the node is not
    /// accepted (or there are no more numbers).
    fn class_number(st: &mut State, node: &Rc<TyNode>) -> Option<u32> {
        match node.memo_hash.get() {
            0 => {}
            REJECTED => return None,
            _ => return Some(node.memo_serial.get()),
        }
        if node.flags() & crate::typing_defs_core::ty_flags::ALL != 0 {
            node.memo_hash.set(REJECTED);
            return None;
        }
        if let Some(key) = small_key(st, node) {
            let Some(key) = key else {
                node.memo_hash.set(REJECTED);
                return None;
            };
            if st.small_classes.len() >= MAX_CLASSES {
                st.small_classes = WordMap::default();
            }
            let number = match st.small_classes.entry(key) {
                hash_map::Entry::Occupied(e) => *e.get(),
                hash_map::Entry::Vacant(e) => {
                    let number = fresh_number(&mut st.last_number);
                    if number == 0 {
                        return None;
                    }
                    *e.insert(number)
                }
            };
            node.memo_serial.set(number);
            // Any value but 0 and `REJECTED`.
            node.memo_hash.set(2);
            return Some(number);
        }
        let mut h = H(0x9e37_79b9_7f4a_7c15);
        if !hash_node(st, &mut h, node) {
            node.memo_hash.set(REJECTED);
            return None;
        }
        // Never 0 or `REJECTED`.
        let hash = h.0 | 2;
        if st.classes.len() >= MAX_CLASSES {
            // The nodes keep their numbers: they are not given again.
            st.classes = WordMap::default();
        }
        let number = match st.classes.entry(hash) {
            hash_map::Entry::Occupied(e) => {
                let (rep, number) = e.get();
                if shallow_equal(rep, node) {
                    *number
                } else {
                    fresh_number(&mut st.last_number)
                }
            }
            hash_map::Entry::Vacant(e) => {
                let number = fresh_number(&mut st.last_number);
                if number != 0 {
                    e.insert((Rc::clone(node), number));
                }
                number
            }
        };
        if number == 0 {
            return None;
        }
        node.memo_serial.set(number);
        node.memo_hash.set(hash);
        Some(number)
    }

    /// The number of a node for the memo: of its class if it is accepted,
    /// else its own (given now if it has none and `give`); 0 if none.
    fn node_number(st: &mut State, node: &Rc<TyNode>, give: bool) -> u32 {
        if let Some(n) = class_number(st, node) {
            return n;
        }
        let n = node.memo_serial.get();
        if n != 0 || !give {
            return n;
        }
        let n = fresh_number(&mut st.last_number);
        node.memo_serial.set(n);
        n
    }

    /// For the nodes of a few kinds made of at most two types and a small
    /// number: a key that tells the structure in full (with the numbers of
    /// the classes of the types in it), so that their classes need no
    /// representative; `Some(None)` if a type in it is not accepted, `None`
    /// for the other kinds.
    fn small_key(st: &mut State, node: &TyNode) -> Option<Option<(u64, u64)>> {
        fn kind(k: u64) -> u64 {
            k << 56
        }
        let num = |st: &mut State, ty: &Ty| class_number(st, &ty.1).map(|n| n as u64);
        Some(match &**node {
            Ty_::Tany(_) => Some((kind(1), 0)),
            Ty_::Tnonnull => Some((kind(2), 0)),
            Ty_::Tdynamic(None) => Some((kind(3), 0)),
            Ty_::Toption(ty) => num(st, ty).map(|n| (kind(4), n)),
            Ty_::Tprim(p) => Some((kind(5) | *p as u64, 0)),
            Ty_::Tunion(tyl) if tyl.len() <= 2 => {
                let mut ns = [0u64; 2];
                for (i, ty) in tyl.iter().enumerate() {
                    match num(st, ty) {
                        Some(n) => ns[i] = n,
                        None => return Some(None),
                    }
                }
                Some((kind(9) | tyl.len() as u64, ns[0] | ns[1] << 32))
            }
            Ty_::TvecOrDict(tk, tv) => match (num(st, tk), num(st, tv)) {
                (Some(k), Some(v)) => Some((kind(10), k | v << 32)),
                _ => None,
            },
            Ty_::TclassPtr(ty) => num(st, ty).map(|n| (kind(11), n)),
            _ => return None,
        })
    }

    /// Hash a type in a node into `h` by the number of its class; false if
    /// it is not accepted.
    #[inline]
    fn child(st: &mut State, h: &mut H, ty: &Ty) -> bool {
        match class_number(st, &ty.1) {
            Some(n) => {
                h.add(n as u64);
                true
            }
            None => false,
        }
    }

    /// Hash the node into `h` (the types in it by the numbers of their
    /// classes); false if it is not a type the memo answers for.
    fn hash_node(st: &mut State, h: &mut H, node: &TyNode) -> bool {
        match &**node {
            Ty_::Tany(_) => {
                h.add(1);
                true
            }
            Ty_::Tnonnull => {
                h.add(2);
                true
            }
            Ty_::Tdynamic(None) => {
                h.add(3);
                true
            }
            Ty_::Toption(ty) => {
                h.add(4);
                child(st, h, ty)
            }
            Ty_::Tprim(p) => {
                h.add(5);
                h.add(*p as u64);
                true
            }
            Ty_::Tfun(ft) => {
                if !ft.tparams.is_empty() || !ft.where_constraints.is_empty() {
                    return false;
                }
                h.add(6);
                h.add(ft.flags.bits() as u64);
                h.add(ft.instantiated as u64);
                h.add(ft.params.len() as u64);
                for p in &ft.params {
                    h.opt_str(&p.name);
                    h.add(p.flags.bits() as u64);
                    h.opt_str(&p.def_value);
                    if !child(st, h, &p.type_) {
                        return false;
                    }
                }
                match &ft.implicit_params.capability {
                    Capability::CapDefaults(_) => h.add(0),
                    Capability::CapTy(ty) => {
                        h.add(1);
                        if !child(st, h, ty) {
                            return false;
                        }
                    }
                }
                child(st, h, &ft.ret)
            }
            Ty_::Ttuple(tt) => {
                h.add(7);
                h.add(tt.required.len() as u64);
                h.add(tt.optional.len() as u64);
                tt.required.iter().all(|ty| child(st, h, ty))
                    && tt.optional.iter().all(|ty| child(st, h, ty))
                    && match &tt.extra {
                        TupleExtra::Tvariadic(ty) => child(st, h, ty),
                        TupleExtra::Tsplat(_) => false,
                    }
            }
            Ty_::Tshape(ShapeType::ShapeSimple(s)) => {
                h.add(8);
                match &s.origin {
                    crate::typing_defs_core::TypeOrigin::MissingOrigin => h.add(0),
                    crate::typing_defs_core::TypeOrigin::FromAlias(name, _) => h.bytes(name.as_bytes()),
                }
                h.add(s.fields.len() as u64);
                child(st, h, &s.unknown_value)
                    && s.fields.iter().all(|(name, f)| {
                        shape_field_name(h, &name.0);
                        h.add(f.optional as u64);
                        child(st, h, &f.ty)
                    })
            }
            Ty_::Tunion(tyl) => {
                h.add(9);
                h.add(tyl.len() as u64);
                tyl.iter().all(|ty| child(st, h, ty))
            }
            Ty_::TvecOrDict(tk, tv) => {
                h.add(10);
                child(st, h, tk) && child(st, h, tv)
            }
            Ty_::TclassPtr(ty) => {
                h.add(11);
                child(st, h, ty)
            }
            Ty_::Tnewtype(name, tyl, cstr) => {
                h.add(12);
                h.bytes(name.as_bytes());
                h.add(tyl.len() as u64);
                tyl.iter().all(|ty| child(st, h, ty)) && child(st, h, cstr)
            }
            Ty_::Tclass((_, name), exact, tyl) => {
                h.add(13);
                h.bytes(name.as_bytes());
                match exact {
                    Exact::Exact => h.add(1),
                    Exact::Nonexact(cr) if cr.cr_consts.is_empty() => h.add(2),
                    Exact::Nonexact(_) => return false,
                }
                h.add(tyl.len() as u64);
                tyl.iter().all(|ty| child(st, h, ty))
            }
            Ty_::Tlabel(name) => {
                h.add(14);
                h.bytes(name.as_bytes());
                true
            }
            Ty_::Tdynamic(Some(_))
            | Ty_::Tshape(ShapeType::ShapeSplat(_))
            | Ty_::Tgeneric(_)
            | Ty_::Tintersection(_)
            | Ty_::Taccess(_)
            | Ty_::Tvar(_)
            | Ty_::Tdependent(..)
            | Ty_::Tneg(_) => false,
        }
    }

    /// The types in two accepted nodes are of the same class (their numbers
    /// are computed: by `hash_node`, for the nodes compared).
    #[inline]
    fn same(t1: &Ty, t2: &Ty) -> bool {
        t1.1.memo_serial.get() == t2.1.memo_serial.get()
    }

    fn all_same(tyl1: &[Ty], tyl2: &[Ty]) -> bool {
        tyl1.len() == tyl2.len() && tyl1.iter().zip(tyl2).all(|(t1, t2)| same(t1, t2))
    }

    /// Structural equality of two nodes that [`hash_node`] accepted,
    /// ignoring reasons and positions, the types in them compared by the
    /// numbers of their classes.
    fn shallow_equal(n1: &TyNode, n2: &TyNode) -> bool {
        match (&**n1, &**n2) {
            (Ty_::Tany(_), Ty_::Tany(_))
            | (Ty_::Tnonnull, Ty_::Tnonnull)
            | (Ty_::Tdynamic(None), Ty_::Tdynamic(None)) => true,
            (Ty_::Toption(t1), Ty_::Toption(t2)) => same(t1, t2),
            (Ty_::Tprim(p1), Ty_::Tprim(p2)) => p1 == p2,
            (Ty_::Tfun(f1), Ty_::Tfun(f2)) => {
                f1.tparams.is_empty()
                    && f2.tparams.is_empty()
                    && f1.where_constraints.is_empty()
                    && f2.where_constraints.is_empty()
                    && f1.flags == f2.flags
                    && f1.instantiated == f2.instantiated
                    && f1.params.len() == f2.params.len()
                    && f1.params.iter().zip(&f2.params).all(|(p1, p2)| {
                        p1.name == p2.name
                            && p1.flags == p2.flags
                            && p1.def_value == p2.def_value
                            && same(&p1.type_, &p2.type_)
                    })
                    && match (&f1.implicit_params.capability, &f2.implicit_params.capability) {
                        (Capability::CapDefaults(_), Capability::CapDefaults(_)) => true,
                        (Capability::CapTy(t1), Capability::CapTy(t2)) => same(t1, t2),
                        _ => false,
                    }
                    && same(&f1.ret, &f2.ret)
            }
            (Ty_::Ttuple(t1), Ty_::Ttuple(t2)) => {
                all_same(&t1.required, &t2.required)
                    && all_same(&t1.optional, &t2.optional)
                    && match (&t1.extra, &t2.extra) {
                        (TupleExtra::Tvariadic(v1), TupleExtra::Tvariadic(v2)) => same(v1, v2),
                        _ => false,
                    }
            }
            (Ty_::Tshape(ShapeType::ShapeSimple(s1)), Ty_::Tshape(ShapeType::ShapeSimple(s2))) => {
                // The origins are compared as `same_type_origin` does
                // (positions included): the simplifier has a fast path for
                // shapes of the same origin.
                s1.origin == s2.origin
                    && same(&s1.unknown_value, &s2.unknown_value)
                    && s1.fields.len() == s2.fields.len()
                    && s1.fields.iter().zip(&s2.fields).all(|((n1, f1), (n2, f2))| {
                        n1 == n2 && f1.optional == f2.optional && same(&f1.ty, &f2.ty)
                    })
            }
            (Ty_::Tunion(l1), Ty_::Tunion(l2)) => all_same(l1, l2),
            (Ty_::TvecOrDict(k1, v1), Ty_::TvecOrDict(k2, v2)) => same(k1, k2) && same(v1, v2),
            (Ty_::TclassPtr(t1), Ty_::TclassPtr(t2)) => same(t1, t2),
            (Ty_::Tnewtype(n1, l1, c1), Ty_::Tnewtype(n2, l2, c2)) => {
                n1 == n2 && all_same(l1, l2) && same(c1, c2)
            }
            (Ty_::Tclass((_, n1), e1, l1), Ty_::Tclass((_, n2), e2, l2)) => {
                n1 == n2
                    && match (e1, e2) {
                        (Exact::Exact, Exact::Exact) => true,
                        (Exact::Nonexact(cr1), Exact::Nonexact(cr2)) => {
                            cr1.cr_consts.is_empty() && cr2.cr_consts.is_empty()
                        }
                        _ => false,
                    }
                    && all_same(l1, l2)
            }
            (Ty_::Tlabel(n1), Ty_::Tlabel(n2)) => n1 == n2,
            _ => false,
        }
    }

    /// The two global environments agree on everything the simplifier reads
    /// for the types of the memo. The fields not compared are those of the
    /// body being checked that subtyping never looks at: its positions,
    /// return information, parameters, readonly, kind (async...), value kind
    /// and whether it is a constructor.
    fn same_genv(g1: &Rc<Genv>, g2: &Rc<Genv>) -> bool {
        if Rc::ptr_eq(g1, g2) {
            return true;
        }
        let Genv {
            tcopt,
            callable_pos: _,
            function_pos: _,
            readonly: _,
            return_: _,
            params: _,
            parent,
            self_,
            static_,
            fun_kind: _,
            val_kind: _,
            fun_is_ctor: _,
            file,
            current_module,
            current_package,
            soft_package_requirement,
            this_internal,
            this_support_dynamic_type,
            no_auto_likes,
            needs_concrete,
        } = &**g1;
        (std::sync::Arc::ptr_eq(file, &g2.file) || **file == *g2.file)
            && *current_module == g2.current_module
            && *current_package == g2.current_package
            && *soft_package_requirement == g2.soft_package_requirement
            && *this_internal == g2.this_internal
            && *this_support_dynamic_type == g2.this_support_dynamic_type
            && *no_auto_likes == g2.no_auto_likes
            && *needs_concrete == g2.needs_concrete
            && *static_ == g2.static_
            && match (self_, &g2.self_) {
                (None, None) => true,
                (Some((id1, ty1)), Some((id2, ty2))) => {
                    id1 == id2 && (Rc::ptr_eq(&ty1.1, &ty2.1) || crate::typing_defs_core::ty_equal(None, ty1, ty2))
                }
                _ => false,
            }
            && match (parent, &g2.parent) {
                (None, None) => true,
                (Some((id1, ty1)), Some((id2, ty2))) => id1 == id2 && ty1 == ty2,
                _ => false,
            }
            // Last: the options are compared by value when they are not the
            // same `Arc` (the file attributes of some files make new ones).
            && (std::sync::Arc::ptr_eq(tcopt, &g2.tcopt) || **tcopt == *g2.tcopt)
    }

    /// The memo of the context of `env`, made the first.
    fn context<'a>(memos: &'a mut Vec<Memo>, next_id: &mut u32, env: &Env) -> &'a mut Memo {
        match memos
            .iter()
            .position(|m| {
                m.checked == env.checked
                    && (std::ptr::eq(m.genv.as_ptr(), Rc::as_ptr(&env.genv)) || same_genv(&m.key, &env.genv))
                    && m.dependent.is_for(env)
            }) {
            Some(i) => {
                if !std::ptr::eq(memos[i].genv.as_ptr(), Rc::as_ptr(&env.genv)) {
                    memos[i].genv = Rc::downgrade(&env.genv);
                }
                if i > 0 {
                    memos[..=i].rotate_right(1)
                }
            }
            None => {
                if *next_id == u32::MAX {
                    // Never in practice: start again with no memo, so that
                    // no id names two memos.
                    memos.clear();
                    *next_id = 0;
                }
                *next_id += 1;
                if memos.len() < CONTEXTS {
                    memos.push(Memo {
                        id: *next_id,
                        genv: Rc::downgrade(&env.genv),
                        key: Rc::new(Genv::clone(&env.genv)),
                        checked: env.checked,
                        dependent: Dependent::of_env(env),
                        entries: WordMap::default(),
                    });
                } else {
                    // Reuse the least recently used one.
                    let last = memos.last_mut().unwrap();
                    last.id = *next_id;
                    last.genv = Rc::downgrade(&env.genv);
                    last.key = Rc::new(Genv::clone(&env.genv));
                    last.checked = env.checked;
                    last.dependent = Dependent::of_env(env);
                    if last.entries.capacity() > 4 * 1024 {
                        last.entries = WordMap::default();
                    } else {
                        last.entries.clear();
                    }
                }
                memos.rotate_right(1);
            }
        }
        &mut memos[0]
    }

    fn key(sub: u32, sup: u32, flags: u16) -> Key {
        Key(sub as u64 | (sup as u64) << 32, flags)
    }

    pub(crate) fn lookup(env: &Env, sub: &Ty, sup: &Ty, flags: u16) -> Lookup {
        // Most of the types that are not accepted are told by the flags of
        // their nodes, before looking for the memo of the context.
        if (sub.1.flags() | sup.1.flags()) & crate::typing_defs_core::ty_flags::ALL != 0
            || crate::rt::decl_epoch::no_memos()
        {
            return Lookup::Unsupported;
        }
        MEMO.with_borrow_mut(|st| {
            let a = node_number(st, &sub.1, false);
            let b = node_number(st, &sup.1, false);
            let State {
                memos,
                next_id,
                classes,
                ..
            } = st;
            let id_before = *next_id;
            let memo = context(memos, next_id, env);
            if *next_id != id_before {
                // A new context (a new definition, mostly): the
                // representatives are dropped, so that they do not keep the
                // types of the definitions checked before alive (scattered
                // in memory, they hold many pages). The nodes keep their
                // numbers.
                classes.clear();
            }
            if a != 0 && b != 0 {
                if let Some(res) = memo.entries.get(&key(a, b, flags)) {
                    return Lookup::Hit(*res);
                }
            }
            Lookup::Miss(Miss { memo_id: memo.id })
        })
    }

    /// Forget the answers (the declarations they were found with may have
    /// changed: see `crate::rt::decl_epoch`), and the representatives of
    /// the classes. The numbers stay: nodes that live on keep the numbers
    /// of their structures, and a number is still never given to two
    /// structures (`last_number`, `next_id` go on).
    pub(crate) fn forget_thread_memos() {
        MEMO.with_borrow_mut(|st| {
            st.memos.clear();
            st.classes = WordMap::default();
        })
    }

    /// Remembers the answer of a query that [`lookup`] did not know, in the
    /// memo of its context (if it is still there).
    pub(crate) fn record(miss: Miss, sub: &Ty, sup: &Ty, flags: u16, res: Option<bool>) {
        MEMO.with_borrow_mut(|st| {
            let a = node_number(st, &sub.1, true);
            let b = node_number(st, &sup.1, true);
            if a == 0 || b == 0 {
                return;
            }
            // The simplifier may have looked up other contexts meanwhile.
            let Some(memo) = st.memos.iter_mut().find(|m| m.id == miss.memo_id) else {
                return;
            };
            if memo.entries.len() >= MAX_ENTRIES {
                memo.entries.clear();
            }
            memo.entries.insert(key(a, b, flags), res);
        })
    }
}

pub fn is_sub_type_for_union_i(
    env: &Env,
    is_dynamic_aware: Option<bool>,
    ty1: &InternalType,
    ty2: &InternalType,
) -> bool {
    let is_dynamic_aware = is_dynamic_aware.unwrap_or(false);
    is_sub_type_alt_i(
        false, // require_completeness
        true,  // no_top_bottom
        is_dynamic_aware,
        None, // sub_supportdyn
        env,
        ty1,
        ty2,
    ) == Some(true)
}

pub fn is_sub_type_ignore_generic_params_i(
    env: &Env,
    ty1: &InternalType,
    ty2: &InternalType,
) -> bool {
    is_sub_type_alt_i(
        // TODO(T121047839): Should this set a dedicated ignore_generic_param flag instead?
        true,  // require_completeness
        true,  // no_top_bottom
        false, // is_dynamic_aware
        None,  // sub_supportdyn
        env, ty1, ty2,
    ) == Some(true)
}
