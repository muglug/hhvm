// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_phase.ml`. See `hh/PORTING.md`.
//!
//! # Shape of the results
//!
//! The functions that return `((env, ty_err_opt, cycles), x)` in OCaml return
//! `(ty_err_opt, cycles, x)` (as in `typing_taccess.rs`), and the ones that
//! return `((env, ty_err_opt), x)` return `(ty_err_opt, x)`. A list of cycles
//! (`Type_expansions.cycle_reporter list`) is a `Vec` in the order of the OCaml
//! list.
//!
//! # Shadowed definitions
//!
//! The end of `typing_phase.ml` redefines, without the cycles, the functions of
//! the recursive group that return them (`let localize ~ety_env env ty =
//! ignore_cycles @@ localize ~ety_env env ty`, and so for `localize_ft`,
//! `localize_targ`, `check_tparams_constraints` and
//! `check_where_constraints`). Here the functions with the cycles are named
//! with `_rec`, after `localize_rec` (which the `.mli` exports, and which is
//! the first `localize`), and the code between the two definitions calls them.
//! `localize_no_subst_` and `localize_and_add_where_constraints` are also
//! defined twice: the second `localize_no_subst_` is
//! [`localize_no_subst_ignore_errors`] here, and the first
//! `localize_and_add_where_constraints` is a function of the same name in the
//! only function that calls it.
//!
//! # Declared types
//!
//! The declared types are `hackrs`'s (`crate::typing_defs_core::DeclTy`), whose
//! reasons and positions are converted to those of the localized phase where a
//! localized type is built (`localize_reason`, `decl_pos`). A declared shape
//! keeps the position of the name of a field in the field: the key of the
//! localized field is put together from the two ([`tshape_field_of_decl`]).
//!
//! # The localization cache
//!
//! `MakeTyCache` is a functor over the size settings, which `setup_cache`
//! applies once, on the first use of the cache, to the options of the
//! environment it is given. Here the instance of the functor is a value of the
//! struct [`MakeTyCache`], kept in a thread-local (OCaml has one per process,
//! and a file is checked on one thread); `cache` and `active_context` are its
//! fields. `Lru.M` (the `lru` library) is [`Lru`].
//!
//! # `Typing_utils`
//!
//! The last lines of `typing_phase.ml` set `Typing_utils.localize_no_subst_ref`,
//! `localize_ref` and `localize_disjoint_union_ref` to [`localize_no_subst`],
//! [`localize`] and [`localize_disjoint_union`]: OCaml breaks the dependency
//! cycle between the two modules with references. They have no counterpart
//! here: Rust has no module initialisation, so the references of
//! `crate::typing_utils` start with these functions.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::rc::Rc;

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::ConstraintKind;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::BPos;
use pos::Positioned;
use pos::ToOxidized;
use pos::TypeName;
use relative_path::RelativePath;
use ty::decl::ty as d;
use ty::reason::Reason as _;

use crate::aast_defs;
use crate::ast_defs;
use crate::class_refinement;
use crate::ctx::R;
use crate::decl_entry;
use crate::decl_hint;
use crate::decl_subst;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::naming_special_names::coeffects as sn_coeffects;
use crate::pos_or_decl;
use crate::positioned;
use crate::tast;
use crate::type_expansions;
use crate::type_expansions::CycleReporter;
use crate::type_parameter_env;
use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs::*;
use crate::typing_env as env;
use crate::typing_env::ClassOrTypedefResult;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error::reasons_callback;
use crate::typing_error::secondary;
use crate::typing_generic_constraint as tgen_constraint;
use crate::typing_intersection;
use crate::typing_kinding_defs as kind_defs;
use crate::typing_log;
use crate::typing_make_type as make_type;
use crate::typing_modules;
use crate::typing_packages;
use crate::typing_print;
use crate::typing_reason;
use crate::typing_reason::LazyString;
/// `Typing_reason.t`
use crate::typing_reason::T as Reason;
use crate::typing_shape_normalize;
use crate::typing_tdef;
use crate::typing_type_integrity;
use crate::typing_union;
use crate::typing_utils as t_utils;
use crate::utils;

/// `Typing_error.t option`
type TyErr = Option<typing_error::T>;

// ---------------------------------------------------------------------------
// Helpers for the declared types (`hackrs`) and OCaml's library functions
// ---------------------------------------------------------------------------

/// `Typing_reason.localize` of the reason of a declared type.
///
/// In OCaml this is a few allocations; here it converts the declared reason
/// to `oxidized` (allocating its positions and their files) and then to a
/// typing reason, for every type node localized. The result depends on the
/// declared reason alone, which is immutable and shared by every use of the
/// declaration, so it is kept per thread by the address of the declared
/// reason (the entry keeps that reason alive, so that the address is not
/// reused). Typing reasons made from declared ones hold no lazy value (which
/// is compared by identity), so sharing one is the same as building it again.
fn localize_reason(r: &R) -> Reason {
    const CAPACITY: usize = 1 << 14;
    if matches!(r.as_impl(), ty::reason::ReasonImpl::NoReason) {
        return typing_reason::none();
    }
    let key = r.as_impl() as *const _ as usize;
    if let Some(reason) =
        LOCALIZED_REASONS.with_borrow(|c| c.get(&key).map(|(_, reason)| reason.clone()))
    {
        return reason;
    }
    let reason = typing_reason::localize(&r.clone().to_oxidized());
    LOCALIZED_REASONS.with_borrow_mut(|c| {
        if c.len() >= CAPACITY {
            c.clear()
        }
        c.insert(key, (r.clone(), reason.clone()))
    });
    reason
}

thread_local! {
    /// The memo of [`localize_reason`].
    static LOCALIZED_REASONS: RefCell<hash::HashMap<usize, (R, Reason)>> =
        RefCell::new(hash::HashMap::default());
}

/// Not in the OCaml: forget what this thread keeps of the declarations (see
/// `crate::rt::decl_epoch`): the alias cache (both tiers), the `localize_`
/// memo, and the memo of [`localize_reason`] (whose entries are right for
/// as long as they exist, but keep the declarations they come from alive).
pub fn forget_thread_memos() {
    forget_locl_cache();
    localize_memo::forget();
    LOCALIZED_REASONS.with_borrow_mut(|c| *c = hash::HashMap::default());
}

/// A position of a declaration, as a `Pos_or_decl.t`.
fn decl_pos(p: &BPos) -> PosOrDecl {
    p.clone().to_oxidized()
}

/// `Typing_reason.to_pos` of the reason of a declared type.
fn decl_reason_to_pos(r: &R) -> PosOrDecl {
    decl_utils::reason_to_pos(r).to_oxidized()
}

/// `Typing_defs.get_pos` of a declared type.
fn decl_get_pos(ty: &DeclTy) -> PosOrDecl {
    decl_utils::get_pos(ty).to_oxidized()
}

/// `tp_name` of a declared type parameter.
fn tp_name(tp: &DeclTparam) -> PosId {
    pos_id(&tp.name)
}

/// A positioned name of a declaration, as a `pos_id`.
fn pos_id<S: ToOxidized<Output = String> + Clone>(id: &Positioned<S, BPos>) -> PosId {
    id.clone().to_oxidized()
}

/// The key of a localized shape field: `hackrs` keeps the position of the name
/// of a field in the field (`ShapeFieldType::field_name_pos`) and the name
/// alone in the key; the key of the localized field (and of `Typing_defs`) has
/// both. (This is how `hackrs` puts them together when it converts a declared
/// shape to `oxidized`.)
pub(crate) fn tshape_field_of_decl(
    name: &d::TshapeFieldName,
    sft: &DeclShapeFieldType,
) -> t_shape_map::TShapeField {
    use oxidized::typing_defs_core::TshapeFieldName as O;
    let name = match (name, &sft.field_name_pos) {
        (d::TshapeFieldName::TSFregexGroup(x), d::ShapeFieldNamePos::Simple(p)) => {
            O::TSFregexGroup(PosString(decl_pos(p), x.to_oxidized()))
        }
        (d::TshapeFieldName::TSFlitStr(x), d::ShapeFieldNamePos::Simple(p)) => {
            O::TSFlitStr(PosByteString(decl_pos(p), x.to_oxidized()))
        }
        (
            d::TshapeFieldName::TSFregexGroup(_) | d::TshapeFieldName::TSFlitStr(_),
            d::ShapeFieldNamePos::ClassConst(_, _),
        ) => panic!("expected ShapeFieldNamePos::Simple"),
        (d::TshapeFieldName::TSFclassConst(cls, name), d::ShapeFieldNamePos::ClassConst(p1, p2)) => {
            O::TSFclassConst(
                (decl_pos(p1), cls.to_oxidized()),
                PosString(decl_pos(p2), name.to_oxidized()),
            )
        }
        (d::TshapeFieldName::TSFclassConst(_, _), d::ShapeFieldNamePos::Simple(_)) => {
            panic!("expected ShapeFieldNamePos::ClassConst")
        }
    };
    t_shape_map::TShapeField(name)
}

/// `{ ety_env with under_type_constructor = true }`, without a copy when it
/// already is.
fn under_type_constructor(ety_env: &ExpandEnv) -> std::borrow::Cow<'_, ExpandEnv> {
    if ety_env.under_type_constructor {
        std::borrow::Cow::Borrowed(ety_env)
    } else {
        std::borrow::Cow::Owned(ExpandEnv {
            under_type_constructor: true,
            ..ety_env.clone()
        })
    }
}

/// `{ t with tp_constraints = cstrl }`, for a declared type parameter whose
/// constraints were localized.
fn tparam_with_constraints(t: &DeclTparam, constraints: Vec<(ConstraintKind, Ty)>) -> Tparam {
    Tparam {
        variance: t.variance,
        name: tp_name(t),
        constraints,
        reified: t.reified,
        user_attributes: t.user_attributes.clone().to_oxidized(),
    }
}

/// `{ param with fp_type = ty }`, for a declared parameter.
fn fun_param_with_type(param: &DeclFunParam, ty: Ty) -> FunParam {
    FunParam {
        pos: decl_pos(&param.pos),
        name: param.name.map(|name| name.to_oxidized()),
        type_: ty,
        flags: param.flags,
        def_value: param.def_value.clone(),
    }
}

/// `Option.merge e1 e2 ~f:Typing_error.both`
fn merge_errs(e1: TyErr, e2: TyErr) -> TyErr {
    match (e1, e2) {
        (Some(e1), Some(e2)) => Some(typing_error::both(e1, e2)),
        (Some(e), None) | (None, Some(e)) => Some(e),
        (None, None) => None,
    }
}

/// `l1 @ l2`
fn append<A>(mut l1: Vec<A>, l2: Vec<A>) -> Vec<A> {
    l1.extend(l2);
    l1
}

/// `List.rev_append l1 l2`
fn rev_append<A>(l1: Vec<A>, l2: Vec<A>) -> Vec<A> {
    let mut l = l1;
    l.reverse();
    l.extend(l2);
    l
}

/// `List.filter_map ~f:Fn.id`
fn filter_some<A>(l: impl IntoIterator<Item = Option<A>>) -> Vec<A> {
    l.into_iter().flatten().collect()
}

/// `Aast.is_erased`
fn is_erased(r: ast_defs::ReifyKind) -> bool {
    match r {
        ast_defs::ReifyKind::Erased => true,
        ast_defs::ReifyKind::SoftReified | ast_defs::ReifyKind::Reified => false,
    }
}

/// `List.map_env_ty_err_opt` (of `Common.List`): `f` is applied to the
/// elements from left to right, and `combine_ty_errs` gets the errors in the
/// order the OCaml builds them: the elements are taken five at a time, the
/// errors of each group in order and the groups from the last to the first
/// (after 1001 groups, the errors of the rest of the elements from the last
/// to the first, before the groups).
fn list_map_env_ty_err_opt<E: ?Sized, X, Y, Err, Errs>(
    env: &mut E,
    xs: &[X],
    mut f: impl FnMut(&mut E, &X) -> (Option<Err>, Y),
    combine_ty_errs: impl FnOnce(Vec<Err>) -> Errs,
) -> (Errs, Vec<Y>) {
    // The OCaml list of errors, last element first.
    let mut rev_errs: Vec<Err> = Vec::new();
    let mut ys = Vec::with_capacity(xs.len());
    let mut rest = xs;
    let mut counter = 0;
    loop {
        if rest.is_empty() {
            break;
        }
        let (group, tail) = rest.split_at(std::cmp::min(5, rest.len()));
        let errs: Vec<Option<Err>> = group
            .iter()
            .map(|x| {
                let (err, y) = f(env, x);
                ys.push(y);
                err
            })
            .collect();
        // `ty_err_opt1 :: ... :: ty_err_opt5 :: ty_err_opts`
        rev_errs.extend(errs.into_iter().rev().flatten());
        if tail.is_empty() {
            break;
        }
        if counter > 1000 {
            // `rev_map_env_ty_err_opt env ys ~f ~err:(...)`
            for x in tail {
                let (err, y) = f(env, x);
                ys.push(y);
                rev_errs.extend(err);
            }
            break;
        }
        counter += 1;
        rest = tail;
    }
    rev_errs.reverse();
    (combine_ty_errs(rev_errs), ys)
}

// ---------------------------------------------------------------------------
// The phase of a type
// ---------------------------------------------------------------------------

// Here is the general problem the delayed application of the phase solves.
// Let's say you have a function that you want to operate generically across
// phases. In most cases when you do this you can use the 'ty' GADT and locally
// abstract types to write code in a phase agonistic way.
//
//  let yell_any: type a. a ty -> string = fun ty ->
//    match ty with
//    | _, Tany -> "Any"
//    | _ -> ""
//
// Now let's add a function that works for all phases, but whose logic is phase
// dependent. For this we can use 'phase_ty' ADT:
//
//  let yell_locl phase_ty =
//     match phase_ty with
//     | DeclTy ty -> ""
//     | LoclTy ty -> "Locl"
//
// Let's say you want to write a function that has behavior that works across
// phases, but needs to invoke a function that is phase dependent. Our options
// are as follows.
//
//  let yell_any_or_locl phase_ty =
//    let ans = yell_locl phase_ty in
//    match phase_ty with
//    | DeclTy ty -> ans ^ (yell_any ty)
//    | LoclTy ty -> ans ^ (yell_any ty)
//
// This would lead to code duplication since we can't generically operate on the
// underlying 'ty' GADT. If we want to eliminate this code duplication there are
// two options.
//
//  let generic_ty: type a. phase_ty -> a ty = function
//    | DeclTy ty -> ty
//    | LoclTy ty -> ty
//
//  let yell_any_or_locl phase_ty =
//    let ans = yell_locl phase_ty in
//    ans ^ (yell_any (generic_ty phase_ty))
//
// generic_ty allows us to extract a generic value which we can use. This
// approach is limiting because we lose all information about what phase 'a ty
// is.
//
// The other approach is to pass in a function that goes from 'a ty -> phase_ty'
//
//  let yell_any_or_locl phase ty =
//    let ans = yell_locl (phase ty) in
//    ans ^ (yell_any ty)
//
// Here we can use 'ty' generically (without losing information about what phase
// 'a ty' is), and we rely on the caller passing in an appropriate function that
// converts into the 'phase_ty' when we need to hop into phase specific code.
pub fn decl(ty: DeclTy) -> PhaseTy {
    PhaseTy::DeclTy(ty)
}

pub fn locl(ty: Ty) -> PhaseTy {
    PhaseTy::LoclTy(ty)
}

#[derive(Clone, Debug)]
pub struct MethodInstantiation {
    pub use_pos: Pos,
    pub use_name: String,
    pub explicit_targs: Vec<tast::Targ>,
}

// ---------------------------------------------------------------------------
// Localization caching.
// ---------------------------------------------------------------------------

/// `Lru.M.Make (String) (struct type t = locl_ty let weight _ = 1 end)`, of
/// the `lru` library (0.3): a map whose weight (here its size, since every
/// binding weighs 1) is bounded by a capacity, and that drops its least
/// recently used bindings first. Only `trim` drops bindings.
struct Lru<V = Ty> {
    cap: isize,
    /// The bindings, with the time of their last use.
    bindings: HashMap<String, (u64, V)>,
    /// The keys by time of last use: the first is the least recently used.
    by_use: BTreeMap<u64, String>,
    time: u64,
}

impl<V: Clone> Lru<V> {
    /// `create cap`
    fn create(cap: isize) -> Self {
        Lru {
            cap,
            bindings: HashMap::new(),
            by_use: BTreeMap::new(),
            time: 0,
        }
    }

    fn tick(&mut self) -> u64 {
        self.time += 1;
        self.time
    }

    /// `is_empty t`
    fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// `weight t`
    fn weight(&self) -> isize {
        self.bindings.len() as isize
    }

    /// `add k v t`: binds `k` to `v` as the most recently used binding (an
    /// earlier binding of `k` is replaced). Does not drop bindings: see `trim`.
    fn add(&mut self, k: String, v: V) {
        let time = self.tick();
        if let Some((old_time, _)) = self.bindings.remove(&k) {
            self.by_use.remove(&old_time);
        }
        self.by_use.insert(time, k.clone());
        self.bindings.insert(k, (time, v));
    }

    /// `promote k t`: makes the binding of `k`, if any, the most recently used.
    fn promote(&mut self, k: &str) {
        let time = self.tick();
        if let Some((old_time, _)) = self.bindings.get(k) {
            let old_time = *old_time;
            self.by_use.remove(&old_time);
            self.by_use.insert(time, k.to_string());
            if let Some(binding) = self.bindings.get_mut(k) {
                binding.0 = time;
            }
        }
    }

    /// `find k t`: does not change how recently the binding was used.
    fn find(&self, k: &str) -> Option<V> {
        self.bindings.get(k).map(|(_, v)| v.clone())
    }

    /// `resize cap t`: does not drop bindings.
    fn resize(&mut self, cap: isize) {
        self.cap = cap
    }

    /// `trim t`: drops the least recently used bindings until the weight is
    /// within the capacity.
    fn trim(&mut self) {
        while self.weight() > self.cap {
            match self.by_use.pop_first() {
                None => break,
                Some((_, k)) => {
                    self.bindings.remove(&k);
                }
            }
        }
    }
}

/// `module type CACHESETTINGS`
#[derive(Clone, Copy, Debug)]
struct CacheSettings {
    capacity: isize,
    node_count_threshold: isize,
}

/// Not in the OCaml: the settings of `MakeTyCache.extra`.
///
/// OCaml keeps (with its default settings) 30 types of 10,000 nodes or more
/// per worker. Keeping more types of fewer nodes saves time and memory (about
/// 20% fewer instructions on Slack's code), but a type is only what
/// localizing again would give, with the same effects on the environment, if
/// its localization does not depend on the environment: see
/// `MakeTyCache::extra`.
const EXTRA_CAPACITY: isize = 2000;
const EXTRA_NODE_COUNT_THRESHOLD: isize = 20;

/// An instance of `MakeTyCache (Settings : CACHESETTINGS)`.
struct MakeTyCache {
    settings: CacheSettings,
    /// `cache`: what OCaml keeps, with the settings of the options.
    cache: Lru,
    /// Not in the OCaml: types that `cache` does not keep, and that OCaml
    /// would localize again each time. A type is kept here only if using it
    /// gives what localizing again would, with the same effects:
    ///
    /// - localizing it was error-free, without cycle, did not add type
    ///   parameters to the environment, and the type has no type parameter,
    ///   type variable or dependent type in it (a type parameter for an
    ///   abstract type constant is added to the environment when the type is
    ///   localized: a type that has one cannot be used in another function);
    /// - it is kept by the alias (or `C::T`), apart for each value of the
    ///   options of the expansion that localizing it reads (the visibility of
    ///   newtypes, `ish_weakening`, `simplify_intersections`: see
    ///   `extra_key`);
    /// - a type is used only where none of the names its localization
    ///   expanded is being expanded (see `type_expansions::recording`);
    /// - like `cache`, it is emptied when the file or the module changes.
    ///
    /// When dependency edges are recorded, an entry also keeps the
    /// dependencies its localization recorded, which a use for another
    /// definition records again (they are the same: the localization does
    /// not depend on the definition, see above).
    #[allow(clippy::type_complexity)]
    extra: HashMap<u8, Lru<(Ty, Rc<Vec<type_expansions::expandable::T>>, Rc<Vec<Dep>>)>>,
    /// Not in the OCaml: see `SizeMemo`.
    size_memo: SizeMemo,
    /// `active_context`
    active_context: (RelativePath, Option<String>),
}

impl MakeTyCache {
    fn new(settings: CacheSettings) -> Self {
        MakeTyCache {
            settings,
            cache: Lru::create(settings.capacity),
            extra: HashMap::new(),
            size_memo: HashMap::new(),
            active_context: (crate::relative_path::default, None),
        }
    }

    fn clear(&mut self) {
        // The only reliable way to empty the LRU cache.
        self.cache.resize(0);
        self.cache.trim();
        self.cache.resize(self.settings.capacity);
        assert!(self.cache.is_empty());
        self.extra.clear();
        self.size_memo.clear();
    }

    /// We invalidate the cache as soon as we are processing a new file or
    /// module because those affect how types are expanded (e.g., newtypes
    /// are unfolded only in the file that defines them).
    fn maybe_invalidate(&mut self, env: &Env) {
        let context = (
            RelativePath::clone(&env::get_file(env)),
            env::get_current_module(env),
        );
        let valid = self.active_context == context;
        if !valid {
            self.active_context = context;
            self.clear()
        }
    }

    /// `add` (if `ocaml`), and then, not in the OCaml, the addition to
    /// `extra` (if `extra` has its key and the names its localization
    /// expanded). The type is visited once for both.
    fn add(
        &mut self,
        env: &Env,
        ocaml: bool,
        extra: Option<(u8, Vec<type_expansions::expandable::T>, Vec<Dep>)>,
        alias: &str,
        lty: &Ty,
    ) {
        self.maybe_invalidate(env);
        // `should_cache_type`: whether the type has more nodes than the
        // threshold.
        let cap = self
            .settings
            .node_count_threshold
            .max(EXTRA_NODE_COUNT_THRESHOLD)
            .saturating_add(1);
        let (count, independent) =
            type_size_and_independence(&self.size_memo, lty, cap, extra.is_some());
        if extra.is_some() {
            self.size_memo.insert(
                Rc::as_ptr(&lty.1) as usize,
                (count, independent, Rc::clone(&lty.1)),
            );
        }
        if ocaml && count > self.settings.node_count_threshold {
            self.cache.add(alias.to_string(), lty.clone());
            self.cache.trim()
        }
        if let Some((key, names, deps)) = extra {
            if count > EXTRA_NODE_COUNT_THRESHOLD && independent {
                let extra = self
                    .extra
                    .entry(key)
                    .or_insert_with(|| Lru::create(EXTRA_CAPACITY));
                extra.add(alias.to_string(), (lty.clone(), Rc::new(names), Rc::new(deps)));
                extra.trim()
            }
        }
    }

    fn get(&mut self, env: &Env, alias: &str) -> Option<Ty> {
        self.maybe_invalidate(env);
        self.cache.promote(alias);
        self.cache.find(alias)
    }

    /// The type, and the dependencies its localization recorded.
    fn get_extra(
        &mut self,
        env: &Env,
        ety_env: &ExpandEnv,
        key: u8,
        alias: &str,
    ) -> Option<(Ty, Rc<Vec<Dep>>)> {
        self.maybe_invalidate(env);
        let extra = self.extra.get_mut(&key)?;
        extra.promote(alias);
        match extra.find(alias) {
            Some((lty, names, deps))
                if !names
                    .iter()
                    .any(|name| type_expansions::mentions(&ety_env.type_expansions, name)) =>
            {
                type_expansions::recording::extend(&names);
                Some((lty, deps))
            }
            _ => None,
        }
    }
}

/// What `type_size_and_independence` found for the types added to the cache,
/// by the address of their node (the entry keeps the node alive, so that the
/// address is not reused): a type that contains one is visited without
/// visiting it again.
type SizeMemo = HashMap<usize, (isize, bool, Rc<TyNode>)>;

/// The number of nodes of `lty`, up to `cap` (the size test of
/// `should_cache_type` stops the visit at the node after the threshold), and,
/// if `independence` (not in the OCaml), whether `lty` has no type parameter,
/// type variable, dependent type or type access in it (see
/// `MakeTyCache::extra`; the whole type is then visited).
fn type_size_and_independence(
    memo: &SizeMemo,
    lty: &Ty,
    cap: isize,
    independence: bool,
) -> (isize, bool) {
    struct SizeVisitor<'a> {
        memo: &'a SizeMemo,
        cap: isize,
        count: isize,
        /// Still to be found out.
        independence: bool,
        independent: bool,
    }
    impl LoclTypeVisitor<()> for SizeVisitor<'_> {
        fn on_type(&mut self, acc: (), ty: &Ty) {
            if self.count >= self.cap && !self.independence {
                return;
            }
            if let Some((count, independent, _)) = self.memo.get(&(Rc::as_ptr(&ty.1) as usize)) {
                self.count = self.count.saturating_add(*count).min(self.cap);
                if !independent {
                    self.independent = false;
                    self.independence = false;
                }
                return;
            }
            if self.count < self.cap {
                self.count += 1
            }
            if self.independence
                && matches!(
                    get_node(ty),
                    Ty_::Tgeneric(_) | Ty_::Tvar(_) | Ty_::Tdependent(_, _) | Ty_::Taccess(_)
                )
            {
                self.independent = false;
                self.independence = false;
            }
            locl_type_visitor_on_type(self, acc, ty)
        }
    }
    // Whether the type is independent is in its flags (see
    // `typing_defs_core::ty_flags`): the visit only counts the nodes, up to
    // `cap`. (A flag can be set when nothing of its kind occurs: such a type
    // is not kept, which only costs time.)
    let independent = independence
        && !lty.may_have(ty_flags::TGENERIC | ty_flags::TVAR | ty_flags::TDEPENDENT | ty_flags::TACCESS);
    let mut visitor = SizeVisitor {
        memo,
        cap,
        count: 0,
        independence: false,
        independent: true,
    };
    visitor.on_type((), lty);
    (visitor.count, independent)
}

/// `locl_type_visitor#on_type`, which a visitor that overrides `on_type` calls
/// as `super#on_type`.
fn locl_type_visitor_on_type<A, V: LoclTypeVisitor<A> + ?Sized>(v: &mut V, acc: A, ty: &Ty) -> A {
    let r = get_reason(ty);
    match get_node(ty) {
        Ty_::Tany(_) => v.on_tany(acc, r),
        Ty_::Tnonnull => v.on_tnonnull(acc, r),
        Ty_::Tdynamic(_) => v.on_tdynamic(acc, r),
        Ty_::Toption(ty) => v.on_toption(acc, r, ty),
        Ty_::Tprim(prim) => v.on_tprim(acc, r, *prim),
        Ty_::Tvar(id) => v.on_tvar(acc, r, *id),
        Ty_::Tfun(fty) => v.on_tfun(acc, r, fty),
        Ty_::Tgeneric(x) => v.on_tgeneric(acc, r, x),
        Ty_::Tnewtype(x, tyl, ty) => v.on_tnewtype(acc, r, x, tyl, ty),
        Ty_::Tdependent(x, ty) => v.on_tdependent(acc, r, x, ty),
        Ty_::Ttuple(t) => v.on_ttuple(acc, r, t),
        Ty_::Tunion(tyl) => v.on_tunion(acc, r, tyl),
        Ty_::Tintersection(tyl) => v.on_tintersection(acc, r, tyl),
        Ty_::Tshape(s) => v.on_tshape(acc, r, s),
        Ty_::Tclass(cls, exact, tyl) => v.on_tclass(acc, r, cls, exact, tyl),
        Ty_::TvecOrDict(ty1, ty2) => v.on_tvec_or_dict(acc, r, ty1, ty2),
        Ty_::Taccess(ta) => v.on_taccess(acc, r, ta),
        Ty_::Tneg(tneg) => v.on_neg_type(acc, r, tneg),
        Ty_::Tlabel(name) => v.on_tlabel(acc, r, name),
        Ty_::TclassPtr(ty) => v.on_tclass_ptr(acc, r, ty),
    }
}

/// `Typing_phase.Log`
mod log {
    use super::*;

    pub(super) fn should_log_localize(env: &Env) -> bool {
        typing_log::should_log(env, "localize", 1)
    }

    /// `f` is the localization, given the environment; the result printed is
    /// the type it returns, in the environment it leaves.
    pub(super) fn log_localize(
        env: &mut Env,
        ety_env: &ExpandEnv,
        decl_ty: &DeclTy,
        f: impl FnOnce(&mut Env) -> (TyErr, Vec<CycleReporter>, Ty),
    ) -> (TyErr, Vec<CycleReporter>, Ty) {
        // (`typing_print` prints the `oxidized` form of declared types.)
        let mut arguments = vec![(
            "decl ty".to_string(),
            typing_print::debug_decl(&*env, &decl_ty.clone().to_oxidized()),
        )];
        arguments.extend(env::log::expand_env(env, ety_env));
        // The `'a` of `Typing_log.log_function` is the environment that `f`
        // returns, with the result of `f`.
        let (_env, res) = typing_log::log_function(
            &decl_get_pos(decl_ty),
            "Typing_phase.localize",
            &arguments,
            |(env, (_, _, ty)): &(&mut Env, (TyErr, Vec<CycleReporter>, Ty))| {
                // The OCaml drops the environment that `expand_type` returns.
                let mut env = Env::clone(env);
                let ty = env::expand_type(&mut env, ty.clone());
                Some(typing_print::debug(&env, &ty))
            },
            move || {
                let res = f(env);
                (env, res)
            },
        );
        res
    }

    pub(super) fn should_log_check_tparams_constraints(env: &Env) -> bool {
        typing_log::should_log(env, "generics", 1)
    }

    /// `f` checks the constraint, given the environment, and returns the
    /// errors so far (the `(env, ty_errs)` of the OCaml).
    pub(super) fn log_check_tparams_constraints(
        env: &mut Env,
        use_pos: &Pos,
        cstr_ty: &Ty,
        ty: &Ty,
        f: impl FnOnce(&mut Env) -> Vec<typing_error::T>,
    ) -> Vec<typing_error::T> {
        let arguments = vec![
            ("cstr_ty".to_string(), typing_print::debug(env, cstr_ty)),
            ("ty".to_string(), typing_print::debug(env, ty)),
        ];
        let (_env, ty_errs) = typing_log::log_function(
            &pos_or_decl::of_raw_pos(use_pos.clone()),
            "Typing_phase.check_tparams_constraints",
            &arguments,
            |(_env, err): &(&mut Env, Vec<typing_error::T>)| {
                Some(format!("{} error(s)", err.len()))
            },
            move || {
                let ty_errs = f(env);
                (env, ty_errs)
            },
        );
        ty_errs
    }

    pub(super) fn log_tparam_instantiation(env: &Env, pos: &Pos, name: &str, ty: &Ty) {
        typing_log::log_tparam_instantiation(env, pos, name, ty)
    }
}

thread_local! {
    /// The instance of `MakeTyCache` that `setup_cache` makes on the first
    /// use of `locl_cache_add` or `locl_cache_get`.
    static LOCL_CACHE: RefCell<Option<MakeTyCache>> = const { RefCell::new(None) };
}

/// Not in the OCaml: empty the cache, and make its next use empty it again,
/// as the first use for a new file does. `check.rs` calls it before it checks
/// a file again from its start (see
/// `typing::expr::snapshots::check_without_snapshots`), so that the second
/// check starts from what the first one started from.
pub fn forget_locl_cache() {
    LOCL_CACHE.with(|cache| {
        if let Some(cache) = cache.borrow_mut().as_mut() {
            cache.active_context = (crate::relative_path::default, None);
            cache.clear()
        }
    })
}

/// Since the typechecker options defining the cache parameters will be
/// available only when we have an environment, the add/get functions are
/// stored in references initially set to stubs that update themselves
/// during their first call.
fn locl_cache_add(
    env: &Env,
    ocaml: bool,
    extra: Option<(u8, Vec<type_expansions::expandable::T>, Vec<Dep>)>,
    alias: &str,
    lty: &Ty,
) {
    LOCL_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        cache
            .get_or_insert_with(|| setup_cache(env))
            .add(env, ocaml, extra, alias, lty)
    })
}

fn locl_cache_get(env: &Env, alias: &str) -> Option<Ty> {
    LOCL_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        cache.get_or_insert_with(|| setup_cache(env)).get(env, alias)
    })
}

/// Not in the OCaml: the options of `ety_env` that localizing an alias
/// reads, as the index of the part of `MakeTyCache::extra` that keeps the
/// types localized with them, if such a type can be kept there.
///
/// The check of the hints of a definition (`Typing_type_wellformedness`)
/// localizes every hint with `Never_expand_newtype`, so it expands the
/// aliases a hint mentions, and the ones those mention, each time: about
/// 100,000 expansions for one 1,300-line file of nested shape aliases. So
/// the types localized that way are kept too (apart).
fn extra_key(ety_env: &ExpandEnv) -> Option<u8> {
    let visibility = match ety_env.visibility_behavior {
        VisibilityBehavior::ExpandVisibleNewtypeOnly => 0,
        VisibilityBehavior::NeverExpandNewtype => 1,
        _ => return None,
    };
    if !ety_env.make_internal_opaque {
        return None;
    }
    // `under_type_constructor` only changes what a cycle gives, and a type
    // whose localization meets a cycle is not kept.
    Some(
        visibility
            | (ety_env.ish_weakening as u8) << 1
            | (ety_env.simplify_intersections as u8) << 2,
    )
}

/// The lookup of the cache before localizing `alias` with `ety_env`.
/// `ocaml_lookup`: whether OCaml looks the type up there (it does for a type
/// alias, not for a type constant: it only adds those). Then, if OCaml does not
/// have it, `MakeTyCache::extra`.
fn locl_cache_get_for(
    env: &Env,
    ety_env: &ExpandEnv,
    alias: &str,
    ocaml_lookup: bool,
) -> Option<Ty> {
    if ocaml_lookup {
        if let Some(lty) = locl_cache_get(env, alias) {
            // What its localization expanded is not known.
            type_expansions::recording::taint();
            return Some(lty);
        }
    }
    // (Not with `HH_NO_MEMOS`, see `crate::rt::decl_epoch`.)
    if crate::rt::decl_epoch::no_memos() {
        return None;
    }
    let key = extra_key(ety_env)?;
    let (lty, deps) = LOCL_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        cache
            .get_or_insert_with(|| setup_cache(env))
            .get_extra(env, ety_env, key, alias)
    })?;
    // (`extra` is not keyed by the definition being checked: the dependency
    // edges that localizing the type again would record for it,
    // `Typing_env.get_typedef` and friends, are recorded.)
    if !deps.is_empty() {
        type_expansions::recording::extend_deps(&deps);
        for dep in deps.iter() {
            env::deps::add_recorded_dependency_edge(env, dep);
        }
    }
    Some(lty)
}

fn setup_cache(env: &Env) -> MakeTyCache {
    let tcopts = env::get_tcopt(env);
    let settings = CacheSettings {
        // `Typechecker_options.locl_cache_capacity`
        capacity: tcopts.tco_locl_cache_capacity,
        // `Typechecker_options.locl_cache_node_threshold`
        node_count_threshold: tcopts.tco_locl_cache_node_threshold,
    };
    MakeTyCache::new(settings)
}

// ---------------------------------------------------------------------------
// Transforms a declaration phase type into a localized type. This performs
// common operations that are necessary for this operation, specifically:
//   > Expand newtype/types
//   > Resolves the "this" type
//   > Instantiate generics
//   > ...
//
// When keep track of additional information while localizing a type such as
// what type defs were expanded to detect potentially recursive definitions..
// ---------------------------------------------------------------------------

/// `combine_ty_errs` gets the errors as `List.map_env_ty_err_opt` gives them;
/// the cycles of each element are put before those of the elements before it.
pub fn list_map_env_err_cycles<E: ?Sized, X, Err, Errs, Cycle, Res>(
    env: &mut E,
    list: &[X],
    combine_ty_errs: impl FnOnce(Vec<Err>) -> Errs,
    mut f: impl FnMut(&mut E, &X) -> (Option<Err>, Vec<Cycle>, Res),
) -> (Errs, Vec<Cycle>, Vec<Res>) {
    let mut cycles_acc: Vec<Cycle> = vec![];
    let (ty_err, list) = list_map_env_ty_err_opt(
        env,
        list,
        |env, ty| {
            let (ty_err, cycles, ty) = f(env, ty);
            cycles_acc = append(cycles, std::mem::take(&mut cycles_acc));
            (ty_err, ty)
        },
        combine_ty_errs,
    );
    (ty_err, cycles_acc, list)
}

/// The first `localize` of `typing_phase.ml`, which returns the cycles.
pub fn localize_rec(
    ety_env: &ExpandEnv,
    env: &mut Env,
    dty: &DeclTy,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    if log::should_log_localize(env) {
        log::log_localize(env, ety_env, dty, |env| localize_(ety_env, env, dty))
    } else {
        // This path should be fast, so we make sure not to create a closure unlike the other path.
        localize_(ety_env, env, dty)
    }
}

/// `find_origin` of `localize_`
fn find_origin(dty: &DeclTy) -> Option<String> {
    match dty.node_ref() {
        DeclTy_::Taccess(taccess) => {
            let id = taccess.type_const.id_ref().as_str();
            find_origin(&taccess.ty).map(|orig| format!("{}::{}", orig, id))
        }
        DeclTy_::Tapply(cid_args) if cid_args.1.is_empty() => {
            Some(cid_args.0.id_ref().as_str().to_string())
        }
        _ => None,
    }
}

/// `set_origin_and_cache` of `localize_`. `env_tpenv` is the global type
/// parameter environment of the environment that `localize_` was given (the
/// `env.tpenv` of the OCaml); the file and the module of the environment, which
/// the cache reads, do not change while localizing.
///
/// When the type resulting from the localize call originates from a
/// decl type with a succinct unambiguous form (e.g., Cls or Cls::T) we
/// store a serialized version of the decl alias in an *origin* field
/// of the locl type returned. Currently, only shape types have an
/// origin field.
fn set_origin_and_cache(
    ety_env: &ExpandEnv,
    env_tpenv: &type_parameter_env::T,
    origin_opt: Option<&str>,
    final_env: &Env,
    ty_err_opt: &TyErr,
    lty: Ty,
    decl_pos_opt: Option<PosOrDecl>,
    recorded: Option<type_expansions::recording::Recorded>,
) -> Ty {
    let cache_result = || {
        // Under the following conditions we may cache the localized
        // type:
        //
        //   1/ We did not encounter cycles during expansion,
        //   2/ localization was error-free,
        //   3/ we are expanding under regular assumptions (local
        //      newtypes are visible), and
        //   4/ the expansion has not created new global type params.
        //
        // Case 4 happens when we bogusly create type params for
        // abstract type constants.
        // Cycles are not reported systematically as errors, so we
        // track them separately with a reference in ety_env.
        let no_new_global_type_params =
            type_parameter_env::size(&final_env.tpenv) <= type_parameter_env::size(env_tpenv);
        !cyclic_expansion(ety_env)
            && ty_err_opt.is_none()
            && is_default_visibility_behaviour(&ety_env.visibility_behavior)
            && ety_env.make_internal_opaque
            && no_new_global_type_params
    };
    // Not in the OCaml: whether the type can be kept in `MakeTyCache::extra`
    // (the conditions of `cache_result` but the visibility, which is in the
    // key, and a localization that was recorded without cycle).
    let cache_result_extra = || {
        let no_new_global_type_params =
            type_parameter_env::size(&final_env.tpenv) <= type_parameter_env::size(env_tpenv);
        !cyclic_expansion(ety_env)
            && ty_err_opt.is_none()
            && no_new_global_type_params
            && recorded.as_ref().is_some_and(|recorded| !recorded.tainted)
    };
    match get_node(&lty) {
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: old_origin,
            unknown_value: shape_kind,
            fields: shape_fields,
        })) => match origin_opt {
            None => lty,
            Some(origin) => {
                let new_origin = TypeOrigin::FromAlias(origin.to_string(), decl_pos_opt);
                // A type that comes from the cache already has this origin:
                // it is the type the OCaml builds again here, so it is kept
                // as it is (the same node, without copying the fields).
                let lty = if *old_origin == new_origin {
                    lty
                } else if Rc::strong_count(&lty.1) == 1 {
                    // (`{ shape with s_origin = .. }` on a node that no other
                    // type shares: changed in place, without copying the
                    // fields.)
                    let mut lty = lty;
                    if let Some(Ty_::Tshape(ShapeType::ShapeSimple(shape))) =
                        crate::typing_defs_core::node_mut(&mut lty)
                    {
                        shape.origin = new_origin;
                    }
                    lty
                } else {
                    mk((
                        get_reason(&lty).clone(),
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: new_origin,
                            unknown_value: shape_kind.clone(),
                            fields: shape_fields.clone(),
                        })),
                    ))
                };
                let ocaml = cache_result();
                let extra = if cache_result_extra() {
                    extra_key(ety_env)
                        .zip(recorded)
                        .map(|(key, recorded)| (key, recorded.names, recorded.deps))
                } else {
                    None
                };
                if ocaml || extra.is_some() {
                    locl_cache_add(final_env, ocaml, extra, origin, &lty)
                }
                lty
            }
        },
        _ => lty,
    }
}

/// `push_supportdyn_into_shape` of `localize_`
fn push_supportdyn_into_shape(env: &mut Env, lty: Ty) -> Ty {
    let (is_supportdyn, stripped_lty) = t_utils::strip_supportdyn(env, lty.clone());
    match get_node(&stripped_lty) {
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin,
            unknown_value: ty,
            fields: shape_fields,
        })) if is_supportdyn => {
            let r = get_reason(&stripped_lty).clone();
            let ty = t_utils::make_supportdyn(r.clone(), env, ty.clone());
            let shape = mk((
                r.clone(),
                Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                    origin: origin.clone(),
                    unknown_value: ty,
                    fields: shape_fields.clone(),
                })),
            ));
            make_type::supportdyn(r, shape)
        }
        _ => lty,
    }
}

/// `allow_abstract_tconst` of the `Taccess` case of `localize_`
fn allow_abstract_tconst(ty: &DeclTy) -> bool {
    match ty.node_ref() {
        // When the root of an access is 'this', abstract type constants
        // are allowed and localized as rigid type variables (Tgeneric).
        // This happens when typing generic code in an abstract class
        // that deals with data whose type is going to be set later in
        // derived classes.
        //
        // In case the root is a generic, we also accept accesses to
        // abstract constant to type check the dangerous and ubiquitous
        // pattern:
        //
        //   function get<TBox as Box, T>(TBox $foo) : T where T = TBox::T
        //                                                         ^^^^^^^
        DeclTy_::Tthis | DeclTy_::Tgeneric(_) => true,
        DeclTy_::Taccess(taccess) => allow_abstract_tconst(&taccess.ty),
        _ => false,
    }
}

/// `null_is_subtype_of` of `union_null` in the `Toption` case of `localize_`
fn null_is_subtype_of(ty: &Ty) -> bool {
    match get_node(ty) {
        Ty_::Toption(_) | Ty_::Tprim(aast::Tprim::Tnull) => true,
        Ty_::Tunion(tyl) => tyl.iter().any(null_is_subtype_of),
        Ty_::Tintersection(tyl) => tyl.iter().all(null_is_subtype_of),
        Ty_::Tnewtype(n, args, _) if args.len() == 1 && n == sn::classes::SUPPORT_DYN => {
            null_is_subtype_of(&args[0])
        }
        _ => false,
    }
}

/// A memo of `localize_` (not in the OCaml, which localizes a declared type
/// again at every use: a function's signature at each call, a hint at each
/// check of it...).
///
/// A declared type is immutable, and hash-consed: its node and its reason
/// identify it. What localizing it gives can depend on the environment and
/// on the expansion environment, so an entry is only made, and only used,
/// when:
///
/// - the expansion environment has no expansions in progress (so no cycle
///   can be found through them), and is not resolving a type structure; the
///   flags it has that are read are in the key;
/// - the declared type mentions no `this`, no generic, no type access, no
///   wildcard, no refinement, no class pointer, no shape splat, and no
///   function type with type parameters or where constraints (the parts
///   whose localization reads the type parameters of the environment, the
///   `this` type or the substitution, or creates type variables);
/// - localizing it changed nothing in the environment (it is shared with a
///   copy before, so that any write separates them), reported no
///   diagnostic, returned no error and found no cycle.
///
/// The entries are for one context: the definition being checked (the
/// dependencies recorded while localizing are for it, and are recorded the
/// first time), its file, module, package and class (which decide what is
/// visible) and the options; the memo is emptied when the context changes.
/// The flags of the environment that its subtyping queries may read are in
/// the key. A
/// result that comes from it is the same value as the one that localizing
/// again would build, but shares its nodes with it (as OCaml's own cache of
/// aliases, `MakeTyCache`, does).
type Dep = crate::typing_deps::dep::Variant;

mod localize_memo {
    use std::sync::Arc;

    use super::*;

    const CAPACITY: usize = 1 << 13;

    #[derive(PartialEq, Eq, Hash, Clone, Copy)]
    pub(super) struct Key {
        node: usize,
        reason: usize,
        visibility: u8,
        make_internal_opaque: bool,
        ish_weakening: bool,
        under_type_constructor: bool,
        simplify_intersections: bool,
        flags: EnvFlags,
    }

    struct Context {
        /// Kept alive, so that their addresses identify them.
        genv: Rc<crate::typing_env_types::Genv>,
        decl_env: Rc<crate::decl_env::Env>,
    }

    #[derive(PartialEq, Eq, Hash, Clone, Copy)]
    struct EnvFlags {
        checked: tast::CheckStatus,
        in_expr_tree: bool,
        in_macro_splice: bool,
        allow_wildcards: bool,
        emit_string_coercion_error: bool,
    }

    fn env_flags(env: &Env) -> EnvFlags {
        EnvFlags {
            checked: env.checked,
            in_expr_tree: env.in_expr_tree.is_some(),
            in_macro_splice: env.in_macro_splice.is_some(),
            allow_wildcards: env.allow_wildcards,
            emit_string_coercion_error: env.emit_string_coercion_error,
        }
    }

    /// The fields of the global environment and of the decl environment that
    /// localizing may read, compared by value.
    fn same_definition(
        g1: &crate::typing_env_types::Genv,
        g2: &crate::typing_env_types::Genv,
        d1: &crate::decl_env::Env,
        d2: &crate::decl_env::Env,
    ) -> bool {
        Arc::ptr_eq(&g1.tcopt, &g2.tcopt)
            && g1.file == g2.file
            && g1.current_module.as_ref().map(|id| &id.1) == g2.current_module.as_ref().map(|id| &id.1)
            && g1.current_package == g2.current_package
            && g1.soft_package_requirement.as_ref().map(|id| &id.1)
                == g2.soft_package_requirement.as_ref().map(|id| &id.1)
            && g1.self_.as_ref().map(|(id, _)| id) == g2.self_.as_ref().map(|(id, _)| id)
            && g1.parent.as_ref().map(|(id, _)| id) == g2.parent.as_ref().map(|(id, _)| id)
            && g1.this_internal == g2.this_internal
            && g1.this_support_dynamic_type == g2.this_support_dynamic_type
            && g1.no_auto_likes == g2.no_auto_likes
            && g1.needs_concrete == g2.needs_concrete
            && Arc::ptr_eq(&d1.ctx, &d2.ctx)
            && d1.mode == d2.mode
            && d1.droot == d2.droot
            // (Only the fine-grained dependencies are recorded for the member.)
            && (!g1.tcopt.tco_record_fine_grained_dependencies
                || d1.droot_member == d2.droot_member)
    }

    struct Memo {
        context: Option<Context>,
        entries: hash::HashMap<Key, (DeclTy, Ty)>,
    }

    thread_local! {
        static MEMO: RefCell<Memo> = RefCell::new(Memo {
            context: None,
            entries: hash::HashMap::default(),
        });
    }

    /// The key of `dty` under `ety_env`, if the expansion environment is one
    /// the memo is for.
    pub(super) fn key(ety_env: &ExpandEnv, env: &Env, dty: &DeclTy) -> Option<Key> {
        let visibility = match ety_env.visibility_behavior {
            VisibilityBehavior::AlwaysExpandNewtype => 0,
            VisibilityBehavior::ExpandVisibleNewtypeOnly => 1,
            VisibilityBehavior::NeverExpandNewtype => 2,
            VisibilityBehavior::ResolveTypeStructure(_) => return None,
        };
        // (The substitution, the generics that are not substituted and the
        // `this` type are only read for generics and `this`, which a type
        // that has entries does not mention.)
        if !type_expansions::is_empty(&ety_env.type_expansions)
            || !env.log_levels.is_empty()
            || crate::rt::decl_epoch::no_memos()
        {
            return None;
        }
        Some(Key {
            node: dty.node_ref() as *const _ as usize,
            reason: dty.reason().as_impl() as *const _ as usize,
            visibility,
            make_internal_opaque: ety_env.make_internal_opaque,
            ish_weakening: ety_env.ish_weakening,
            under_type_constructor: ety_env.under_type_constructor,
            simplify_intersections: ety_env.simplify_intersections,
            flags: env_flags(env),
        })
    }

    /// Make the memo that of the context of `env`.
    fn use_context(memo: &mut Memo, env: &Env) {
        let same = match &memo.context {
            Some(c) => {
                (Rc::ptr_eq(&c.genv, &env.genv) && Rc::ptr_eq(&c.decl_env, &env.decl_env))
                    || same_definition(&c.genv, &env.genv, &c.decl_env, &env.decl_env)
            }
            None => false,
        };
        if !same {
            memo.entries.clear();
        }
        let up_to_date = match &memo.context {
            Some(c) => same && Rc::ptr_eq(&c.genv, &env.genv) && Rc::ptr_eq(&c.decl_env, &env.decl_env),
            None => false,
        };
        if !up_to_date {
            memo.context = Some(Context {
                genv: Rc::clone(&env.genv),
                decl_env: Rc::clone(&env.decl_env),
            });
        }
    }

    /// Empty the memo (see `forget_thread_memos`).
    pub(super) fn forget() {
        MEMO.with_borrow_mut(|memo| {
            memo.context = None;
            memo.entries = hash::HashMap::default();
        })
    }

    pub(super) fn get(env: &Env, key: &Key) -> Option<Ty> {
        MEMO.with_borrow_mut(|memo| {
            use_context(memo, env);
            memo.entries.get(key).map(|(_, ty)| ty.clone())
        })
    }

    pub(super) fn add(env: &Env, key: Key, dty: &DeclTy, ty: &Ty) {
        MEMO.with_borrow_mut(|memo| {
            use_context(memo, env);
            if memo.entries.len() >= CAPACITY {
                memo.entries.clear()
            }
            // The entry keeps the declared type alive, so that the addresses
            // of its node and reason are not reused.
            memo.entries.insert(key, (dty.clone(), ty.clone()));
        })
    }

    /// Whether localizing `dty` reads nothing but the declarations and the
    /// context (see the module documentation).
    pub(super) fn is_closed(dty: &DeclTy) -> bool {
        use d::Ty_::*;
        match dty.node_ref() {
            Tmixed | Tany | Tnonnull | Tdynamic | Tprim(_) => true,
            Tthis | Twildcard | Tgeneric(_) | Taccess(_) | Trefinement(_) | TclassPtr(_) => false,
            Tlike(ty) | Toption(ty) => is_closed(ty),
            Tapply(id_and_args) => id_and_args.1.iter().all(is_closed),
            Tunion(tyl) | Tintersection(tyl) => tyl.iter().all(is_closed),
            TvecOrDict(tk_tv) => is_closed(&tk_tv.0) && is_closed(&tk_tv.1),
            Ttuple(tuple) => {
                let d::TupleType(required, optional, extra) = &**tuple;
                required.iter().all(is_closed)
                    && optional.iter().all(is_closed)
                    && match extra {
                        d::TupleExtra::Tsplat(ty) | d::TupleExtra::Tvariadic(ty) => is_closed(ty),
                    }
            }
            Tshape(shape) => match &**shape {
                d::ShapeType::Simple(d::ShapeTypeSimple(unknown, fields)) => {
                    is_closed(unknown) && fields.values().all(|sft| is_closed(&sft.ty))
                }
                d::ShapeType::Splat(_) => false,
            },
            Tfun(ft) => {
                ft.tparams.is_empty()
                    && ft.where_constraints.is_empty()
                    && ft.params.iter().all(|p| is_closed(&p.ty))
                    && match &ft.implicit_params.capability {
                        d::Capability::CapDefaults(_) => true,
                        d::Capability::CapTy(ty) => is_closed(ty),
                    }
                    && is_closed(&ft.ret)
            }
        }
    }
}

fn localize_(ety_env: &ExpandEnv, env: &mut Env, dty: &DeclTy) -> (TyErr, Vec<CycleReporter>, Ty) {
    // (A type that is not closed is never in the memo: it is neither looked
    // up nor kept, and the environment is not shared with a copy while it is
    // localized, which would make its first write copy it.)
    match localize_memo::key(ety_env, env, dty).filter(|_| localize_memo::is_closed(dty)) {
        None => localize_uncached(ety_env, env, dty),
        Some(key) => {
            if let Some(ty) = localize_memo::get(env, &key) {
                // What localizing it expanded is not kept: a recording in
                // progress (see `type_expansions::recording`) cannot know it.
                type_expansions::recording::taint();
                return (None, vec![], ty);
            }
            let saved = env.clone();
            let diagnostics_before = crate::diagnostics_state::added_count();
            let res = localize_uncached(ety_env, env, dty);
            let (ty_err_opt, cycles, ty) = &res;
            if ty_err_opt.is_none()
                && cycles.is_empty()
                && Env::ptr_eq(&saved, env)
                && crate::diagnostics_state::added_count() == diagnostics_before
            {
                localize_memo::add(env, key, dty, ty)
            }
            res
        }
    }
}

fn localize_uncached(ety_env: &ExpandEnv, env: &mut Env, dty: &DeclTy) -> (TyErr, Vec<CycleReporter>, Ty) {
    let r = localize_reason(dty.reason());
    match dty.node_ref() {
        DeclTy_::Trefinement(refinement) => {
            let (err, cycles, ty) =
                localize_refinement(ety_env, env, r, &refinement.ty, &refinement.refinement);
            (err, cycles, ty)
        }
        // The `Tvid.t option` of a declared `Tdynamic` (which `hackrs` does
        // not keep) is `None`.
        DeclTy_::Tnonnull => (None, vec![], mk((r, Ty_::Tnonnull))),
        DeclTy_::Tprim(p) => (None, vec![], mk((r, Ty_::Tprim(*p)))),
        DeclTy_::Tdynamic => (None, vec![], mk((r, Ty_::Tdynamic(None)))),
        DeclTy_::Tany => (None, vec![], mk((r, make_tany()))),
        DeclTy_::Tmixed => (None, vec![], make_type::mixed(r)),
        DeclTy_::Tthis => {
            let ty = map_reason(ety_env.this_ty.clone(), |reason| {
                if typing_reason::predicates::is_none(&reason) {
                    r.clone()
                } else {
                    match typing_reason::predicates::unpack_expr_dep_type_opt(&reason) {
                        Some((_, pos, s)) => typing_reason::expr_dep_type((r.clone(), pos, s)),
                        None => typing_reason::instantiate(
                            reason,
                            sn::typehints::THIS.to_string(),
                            r.clone(),
                        ),
                    }
                }
            });
            // When refining `as this`, insert a like type for generic or non-final
            // classes, because generics are not checked at runtime
            let ty = if ety_env.ish_weakening {
                match env::get_self_class(env) {
                    decl_entry::T::Found(tc) => {
                        if cls::final_(&tc) && cls::tparams_ref(&tc).is_empty() {
                            ty
                        } else {
                            make_type::locl_like(
                                typing_reason::pessimised_this(typing_reason::to_pos(&r)),
                                ty,
                            )
                        }
                    }
                    _ => ty,
                }
            } else {
                ty
            };
            (None, vec![], ty)
        }
        DeclTy_::TvecOrDict(tk_tv) => {
            let (tk, tv) = &**tk_tv;
            let ety_env_targ = under_type_constructor(ety_env);
            let tk = match ety_env.wildcard_action {
                WildcardAction::WildcardFreshGeneric => {
                    DeclTy::new(tk.reason().clone(), DeclTy_::Twildcard)
                }
                _ => tk.clone(),
            };
            let (e1, cycles1, tk) = localize_rec(&ety_env_targ, env, &tk);
            let (e2, cycles2, tv) = localize_rec(&ety_env_targ, env, tv);
            let ty = Ty_::TvecOrDict(tk, tv);
            let ty_err_opt = merge_errs(e1, e2);
            (ty_err_opt, append(cycles1, cycles2), mk((r, ty)))
        }
        DeclTy_::Tgeneric(nm) if ety_env.no_substs.contains(nm.as_str()) => {
            // For polymorphic lambda we want to retain generics bound in the lambda signature
            (None, vec![], mk((r, Ty_::Tgeneric(nm.as_str().to_string()))))
        }
        DeclTy_::Tgeneric(x) => match ety_env.substs.get(x.as_str()) {
            Some(x_ty) => {
                let x_ty = env::expand_type(env, x_ty.clone());
                let r_inst = {
                    let rp = get_reason(&x_ty).clone();
                    typing_reason::instantiate(rp, x.as_str().to_string(), r)
                };
                // `mk (r_inst, get_node x_ty)`: the node is shared.
                (None, vec![], with_reason(x_ty, r_inst))
            }
            None => (None, vec![], mk((r, Ty_::Tgeneric(x.as_str().to_string())))),
        },
        DeclTy_::Toption(ty) => {
            let (ty_err_opt, cycles, ty) = localize_rec(ety_env, env, ty);
            // Calling into the union module here would cost 2% perf regression on a full init,
            // so we use this lightweight version instead.
            let union_null = |env: &mut Env, ty: Ty| -> Ty {
                if null_is_subtype_of(&ty) {
                    ty
                } else {
                    let ty = make_type::nullable(r.clone(), ty);
                    t_utils::wrap_union_inter_ty_in_var(env, r.clone(), ty)
                }
            };
            let ty = union_null(env, ty);
            (ty_err_opt, cycles, ty)
        }
        DeclTy_::Tlike(ty) => {
            let (ty_err_opt, cycles, ty) = localize_rec(ety_env, env, ty);
            let lty = make_type::locl_like(r, ty);
            (ty_err_opt, cycles, lty)
        }
        DeclTy_::Tfun(ft) => {
            let pos = typing_reason::to_pos(&r);
            let (err, cycles, ft) = localize_ft_rec(
                None,
                &under_type_constructor(ety_env),
                pos,
                env,
                ft,
            );
            (err, cycles, mk((r, Ty_::Tfun(std::rc::Rc::new(ft)))))
        }
        DeclTy_::Tapply(x_args)
            if x_args.1.len() == 1 && x_args.0.id_ref().as_str() == sn::typehints::POISON_MARKER =>
        {
            let arg = &x_args.1[0];
            let decl_ty = DeclTy::new(dty.reason().clone(), DeclTy_::Tlike(arg.clone()));
            localize_rec(ety_env, env, &decl_ty)
        }
        DeclTy_::Twildcard => {
            match &ety_env.wildcard_action {
                // Generate a fresh type variable
                WildcardAction::WildcardFreshTyvar => {
                    let ty = env::fresh_type(
                        env,
                        pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                    );
                    (None, vec![], ty)
                }
                // Produce an error: wildcard is not allowed in this position
                WildcardAction::WildcardRequireExplicit(tparam) => {
                    let (decl_pos, param_name) = tp_name(tparam);
                    let err_opt = Some(typing_error::primary(primary::T::Require_generic_explicit {
                        decl_pos,
                        param_name,
                        pos: pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                    }));
                    let ty = env::fresh_type_error(
                        env,
                        pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                    );
                    (err_opt, vec![], ty)
                }
                // All should have been dealt with already:
                // (1) Wildcard_fresh_generic and Wildcard_fresh_generic_type_argument, in localize_targ_constrain_wildcard.
                // (2) Wildcard_illegal, in the naming phase.
                // (3) Wildcard_higher_kinded_placeholder, in Typing_type_integrity.ml
                WildcardAction::WildcardFreshGeneric
                | WildcardAction::WildcardIllegal
                | WildcardAction::WildcardHigherKindedPlaceholder => {
                    let ty = env::fresh_type_error(
                        env,
                        pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                    );
                    (None, vec![], ty)
                }
            }
        }
        DeclTy_::Tapply(cls_argl) => {
            let (cls, argl) = &**cls_argl;
            let cid = cls.id_ref().as_str();
            let (ty_err_opt, cycles, lty) = match env::get_class_or_typedef(env, cid) {
                decl_entry::T::Found(ClassOrTypedefResult::ClassResult(class_info)) => {
                    localize_class_instantiation(ety_env, env, r, cls, argl, Some(&class_info))
                }
                decl_entry::T::Found(ClassOrTypedefResult::TypedefResult(typedef_info)) => {
                    let origin_opt = find_origin(dty);
                    let env_tpenv = env.tpenv.clone();
                    let (ty_err_opt, cycles, lty, recorded) = match origin_opt
                        .as_deref()
                        .and_then(|origin| locl_cache_get_for(env, ety_env, origin, true))
                    {
                        Some(lty) => (None, vec![], with_reason(lty, r.clone()), None),
                        None => {
                            // Not in the OCaml: see `MakeTyCache::extra`.
                            let recording = origin_opt
                                .is_some()
                                .then(type_expansions::recording::start);
                            let (ty_err_opt, cycles, lty) = localize_typedef_instantiation(
                                ety_env,
                                env,
                                r.clone(),
                                cid,
                                argl,
                                Some(&typedef_info),
                            );
                            let recorded = recording.map(type_expansions::recording::stop);
                            (ty_err_opt, cycles, lty, recorded)
                        }
                    };

                    let shp_def_pos = match &typedef_info.type_assignment {
                        d::TypedefTypeAssignment::SimpleTypeDef(_, hint) => {
                            decl_reason_to_pos(hint.reason())
                        }
                        d::TypedefTypeAssignment::CaseType(variant, rest) if rest.is_empty() => {
                            decl_reason_to_pos(variant.hint.reason())
                        }
                        d::TypedefTypeAssignment::CaseType(first, rest) => match rest.last() {
                            None => decl_reason_to_pos(first.hint.reason()),
                            Some(last) => {
                                let first_pos = decl_reason_to_pos(first.hint.reason());
                                let last_pos = decl_reason_to_pos(last.hint.reason());
                                pos_or_decl::btw(&first_pos, &last_pos)
                            }
                        },
                    };
                    let lty = set_origin_and_cache(
                        ety_env,
                        &env_tpenv,
                        origin_opt.as_deref(),
                        env,
                        &ty_err_opt,
                        lty,
                        Some(shp_def_pos.clone()),
                        recorded,
                    );
                    let lty = env::update_reason(env, lty, |r| {
                        typing_reason::definition(shp_def_pos, r)
                    });
                    (ty_err_opt, cycles, lty)
                }
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {
                    localize_class_instantiation(ety_env, env, r, cls, argl, None)
                }
            };
            // If we have supportdyn<t> then push supportdyn into open shape fields
            let lty = if cid == sn::classes::SUPPORT_DYN {
                push_supportdyn_into_shape(env, lty)
            } else {
                lty
            };
            (ty_err_opt, cycles, lty)
        }
        DeclTy_::Ttuple(tuple) => {
            let d::TupleType(t_required, t_optional, t_extra) = &**tuple;
            let ety_env_targ = under_type_constructor(ety_env);
            let (ty_err_opt1, cycles1, t_required) =
                list_map_env_err_cycles(env, t_required, typing_error::multiple_opt, |env, ty| {
                    localize_rec(&ety_env_targ, env, ty)
                });
            let (ty_err_opt2, cycles2, t_optional) =
                list_map_env_err_cycles(env, t_optional, typing_error::multiple_opt, |env, ty| {
                    localize_rec(&ety_env_targ, env, ty)
                });
            let (ty_err_opt3, cycles3, t_extra) = localize_tuple_extra(&ety_env_targ, env, t_extra);
            let ty_err_opt = merge_errs(merge_errs(ty_err_opt1, ty_err_opt2), ty_err_opt3);
            (
                ty_err_opt,
                append(append(cycles1, cycles2), cycles3),
                mk((
                    r,
                    Ty_::Ttuple(TupleType {
                        required: t_required,
                        optional: t_optional,
                        extra: t_extra,
                    }),
                )),
            )
        }
        DeclTy_::Tunion(tyl) => {
            let (ty_err_opt, cycles, tyl) =
                list_map_env_err_cycles(env, tyl, typing_error::union_opt, |env, ty| {
                    localize_rec(ety_env, env, ty)
                });
            let ty = typing_union::union_list(env, None, r, &tyl);
            (ty_err_opt, cycles, ty)
        }
        DeclTy_::Tintersection(tyl) => {
            let (ty_err_opt, cycles, tyl) =
                list_map_env_err_cycles(env, tyl, typing_error::multiple_opt, |env, ty| {
                    localize_rec(ety_env, env, ty)
                });
            let ty = if ety_env.simplify_intersections {
                typing_intersection::intersect_list(env, r, &tyl)
            } else {
                make_type::intersection(r, tyl)
            };
            (ty_err_opt, cycles, ty)
        }
        DeclTy_::Taccess(taccess) => {
            let root_ty = &taccess.ty;
            let id: PosId = pos_id(&taccess.type_const);
            let origin_opt = find_origin(dty);
            let allow_abstract_tconst = allow_abstract_tconst(root_ty);
            let env_tpenv = env.tpenv.clone();
            let (e1, cycles_root, root_ty) = localize_rec(
                // We don't want to put `~` on this::TC, so set ish_weakening to false
                &ExpandEnv {
                    ish_weakening: false,
                    ..ety_env.clone()
                },
                env,
                root_ty,
            );
            // Not in the OCaml, which adds the type of a type constant to the
            // cache but does not look it up there: the type that
            // `expand_typeconst` would give again, if `MakeTyCache::extra`
            // has it.
            let cached = if e1.is_none() && cycles_root.is_empty() {
                origin_opt
                    .as_deref()
                    .and_then(|origin| locl_cache_get_for(env, ety_env, origin, false))
            } else {
                None
            };
            let (e2, cycles_tconst, ty, recorded) = match cached {
                Some(ty) => (None, vec![], ty, None),
                None => {
                    let recording = origin_opt
                        .is_some()
                        .then(type_expansions::recording::start);
                    let (e2, cycles_tconst, ty) = t_utils::expand_typeconst(
                        ety_env,
                        env,
                        None,
                        None,
                        root_ty.clone(),
                        id.clone(),
                        allow_abstract_tconst,
                    );
                    let recorded = recording.map(type_expansions::recording::stop);
                    (e2, cycles_tconst, ty, recorded)
                }
            };
            // Elaborate reason with information about expression dependent types and
            // the original location of the Taccess type
            let ty_err_opt = merge_errs(e1, e2);
            let ty = set_origin_and_cache(
                ety_env,
                &env_tpenv,
                origin_opt.as_deref(),
                env,
                &ty_err_opt,
                ty,
                None,
                recorded,
            );
            let elaborate_reason = |expand_reason: Reason| -> Reason {
                // `lazy (...)`: a lazy string has to be `Send`, which
                // the environment is not; the string is the same as
                // the one OCaml computes later, from the environment it
                // captures here.
                let taccess_string = LazyString::from_val(format!(
                    "{}::{}",
                    typing_print::full_strip_ns(true, &*env, &root_ty),
                    id.1
                ));
                // If the root is an expression dependent type, change the primary
                // reason to be for the full Taccess type to preserve the position where
                // the expression dependent type was derived from.
                let reason = match typing_reason::predicates::unpack_expr_dep_type_opt(
                    get_reason(&root_ty),
                ) {
                    Some((_, p, e)) => typing_reason::expr_dep_type((r.clone(), p, e)),
                    None => r.clone(),
                };
                typing_reason::type_access((expand_reason, vec![(reason, taccess_string)]))
            };
            let ty = map_reason(ty, elaborate_reason);
            (ty_err_opt, append(cycles_root, cycles_tconst), ty)
        }
        DeclTy_::Tshape(shape) => match &**shape {
            d::ShapeType::Simple(d::ShapeTypeSimple(shape_kind, tym)) => {
                let ety_env_targ = under_type_constructor(ety_env);
                // `ShapeFieldMap.map_env_ty_err_opt`: the fields in the order of
                // their keys, and `combine_ty_errs` gets the errors in the
                // reverse order.
                let mut cycles_shape = vec![];
                let mut errs = vec![];
                // (The map is built in one go from its bindings, which
                // `BTreeMap::from_iter` sorts: the names of a declared shape
                // are distinct, and so are their localized keys.)
                let mut fields = Vec::with_capacity(tym.len());
                for (name, sft) in tym {
                    let (err, cycles, ty) = localize_rec(&ety_env_targ, env, &sft.ty);
                    cycles_shape = append(cycles, cycles_shape);
                    errs.extend(err);
                    fields.push((
                        tshape_field_of_decl(name, sft),
                        ShapeFieldType {
                            optional: sft.optional,
                            ty,
                        },
                    ));
                }
                let fields: t_shape_map::T<ShapeFieldType> = fields.into_iter().collect();
                errs.reverse();
                let ty_err_opt1 = typing_error::multiple_opt(errs);
                let (ty_err_opt2, cycles_unknown_value, shape_kind) =
                    localize_rec(&ety_env_targ, env, shape_kind);
                let ty_err_opt = merge_errs(ty_err_opt1, ty_err_opt2);
                (
                    ty_err_opt,
                    append(cycles_shape, cycles_unknown_value),
                    mk((
                        r,
                        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: shape_kind,
                            fields,
                        })),
                    )),
                )
            }
            d::ShapeType::Splat(ss_elems) => {
                let ety_env_targ = under_type_constructor(ety_env);
                let mut ty_err_opt = None;
                let mut all_cycles = vec![];
                let mut localized_elems = vec![];
                for elem in ss_elems {
                    let (ty_err_opt_, cycles, elem_ty) = localize_rec(&ety_env_targ, env, elem);
                    ty_err_opt = merge_errs(ty_err_opt, ty_err_opt_);
                    all_cycles = rev_append(cycles, all_cycles);
                    localized_elems.push(elem_ty);
                }
                let (norm_err_opt, normalized) =
                    typing_shape_normalize::merge(ety_env.on_error.clone(), localized_elems, env);
                let ty_err_opt = match (ty_err_opt, norm_err_opt) {
                    (Some(t1), Some(t2)) => Some(typing_error::both(t1, t2)),
                    (Some(t), _) | (_, Some(t)) => Some(t),
                    _ => None,
                };
                let (ty, sd) = match normalized {
                    typing_shape_normalize::MergeResult::Full(ty, sd) => (ty, sd),
                    typing_shape_normalize::MergeResult::EmptyShape(sd) => {
                        let shape = ShapeTypeSimple {
                            origin: TypeOrigin::MissingOrigin,
                            unknown_value: make_type::nothing(r.clone()),
                            fields: t_shape_map::T::new(),
                        };
                        (mk((r, Ty_::Tshape(ShapeType::ShapeSimple(shape)))), sd)
                    }
                    // A splat of one element and nothing else IS that element, so lift it out
                    // rather than leaving a singleton [Shape_splat] wrapper: `shape(...T)` is
                    // `T`. Without this the wrapper hides the element behind the splat
                    // machinery and reading a field off a `shape(...T)` parameter would go via
                    // the corner's bound projection rather than the ordinary rules for `T`.
                    typing_shape_normalize::MergeResult::Partial(mut ss_elems, sd)
                        if ss_elems.len() == 1 =>
                    {
                        (ss_elems.pop().unwrap(), sd)
                    }
                    typing_shape_normalize::MergeResult::Partial(ss_elems, sd) => (
                        mk((r, Ty_::Tshape(ShapeType::ShapeSplat(ShapeTypeSplat { ss_elems })))),
                        sd,
                    ),
                    typing_shape_normalize::MergeResult::Union(tys) => {
                        // Union operand distributed: members are already finalised (supportdyn
                        // applied per member), so union them and mark sd already-applied.
                        let ty = typing_union::union_list(env, None, r, &tys);
                        (ty, false)
                    }
                    typing_shape_normalize::MergeResult::Intersection(tys) => {
                        let ty = typing_intersection::intersect_list(env, r, &tys);
                        (ty, false)
                    }
                };
                // If any element was [supportdyn<...>] (e.g. an open shape under sound
                // dynamic), the stripped, normalized result must be re-wrapped to stay
                // sound. [supportdyn] is idempotent so this is a no-op otherwise.
                let ty = if sd {
                    make_type::supportdyn(get_reason(&ty).clone(), ty)
                } else {
                    ty
                };
                (ty_err_opt, all_cycles, ty)
            }
        },
        DeclTy_::TclassPtr(ty) => {
            let (ty_err_opt, cycles, ty) = localize_rec(
                &under_type_constructor(ety_env),
                env,
                ty,
            );
            (ty_err_opt, cycles, mk((r, Ty_::TclassPtr(ty))))
        }
    }
}

fn localize_tuple_extra(
    ety_env: &ExpandEnv,
    env: &mut Env,
    e: &d::TupleExtra<R>,
) -> (TyErr, Vec<CycleReporter>, TupleExtra) {
    match e {
        d::TupleExtra::Tvariadic(t_variadic) => {
            let (ty_err_opt, cycles, t_variadic) = localize_rec(ety_env, env, t_variadic);
            (ty_err_opt, cycles, TupleExtra::Tvariadic(t_variadic))
        }
        d::TupleExtra::Tsplat(t_splat) => {
            let (ty_err_opt, cycles, t_splat) = localize_rec(ety_env, env, t_splat);
            (ty_err_opt, cycles, TupleExtra::Tsplat(t_splat))
        }
    }
}

/// Localize type arguments using localize_targ_constrain_wildcard.
/// Discards tyargs for which we have no corresponding tparam.
/// Ignores superfluous tparams as well as superfluus tparams.
fn localize_targs_constrain_wildcards(
    ety_env: &ExpandEnv,
    env: &mut Env,
    tyargs: &[DeclTy],
    tparams: &[DeclTparam],
) -> (TyErr, Vec<CycleReporter>, Vec<Ty>) {
    let exp_len = tparams.len();
    let act_len = tyargs.len();
    let length = std::cmp::min(exp_len, act_len);
    let (tyargs, tparams) = (&tyargs[..length], &tparams[..length]);
    // `List.map2_env (env, [], ety_env, [])`: the errors (consed, so the last
    // one is the head of the OCaml list), the expansion environment and the
    // cycles are threaded through the type arguments, from left to right.
    let mut ty_errs = vec![];
    // (The expansion environment that a type argument gives, if it is not
    // the one it was given: only a wildcard changes it.)
    let mut ety_env_threaded: Option<ExpandEnv> = None;
    let mut cycles_acc = vec![];
    let mut tyl = Vec::with_capacity(length);
    for (x, y) in tyargs.iter().zip(tparams) {
        let (ety_env_, ty_err_opt, cycles, res) =
            localize_targ_constrain_wildcard(env, ety_env_threaded.as_ref().unwrap_or(ety_env), x, y);
        if let Some(ety_env_) = ety_env_ {
            ety_env_threaded = Some(ety_env_);
        }
        ty_errs.extend(ty_err_opt);
        cycles_acc = append(cycles, cycles_acc);
        tyl.push(res);
    }
    ty_errs.reverse();
    let ty_err_opt = typing_error::multiple_opt(ty_errs);
    // Note that we removed superfluous type arguments, because we don't have a kind to localize
    // them against.
    // It would also be useful to fill in Terr for missing type arguments, but this breaks some
    // checks on built-in collections that check the number of type arguments *after* localization.
    (ty_err_opt, cycles_acc, tyl)
}

/// Localizes a type argument. If it's a wildcard, turn into fresh generic with bounds according to tparam
///
/// (`(env, ety_env)` in OCaml; the expansion environment it returns comes
/// first in the result, `None` when it is the one it was given.)
fn localize_targ_constrain_wildcard(
    env: &mut Env,
    ety_env: &ExpandEnv,
    ty: &DeclTy,
    tparam: &DeclTparam,
) -> (Option<ExpandEnv>, TyErr, Vec<CycleReporter>, Ty) {
    match (ty.node_ref(), &ety_env.wildcard_action) {
        (DeclTy_::Twildcard, WildcardAction::WildcardFreshGeneric) => {
            let r = ty.reason();
            let pos = decl_get_pos(ty);
            let r = localize_reason(r);
            let name = tp_name(tparam);
            let kind_without_bounds = kind_defs::kind_of_decl_tparam_no_bounds(None, None, tparam);
            // add without bounds, because we need to substitute inside them first,
            // as done below
            let new_name =
                env::add_fresh_generic_parameter_by_kind(env, pos, &name.1, kind_without_bounds);
            let ty_fresh = mk((r, Ty_::Tgeneric(new_name)));
            // Substitute fresh type parameters for original formals in constraint
            let substs = ety_env.substs.update(name.1.clone(), ty_fresh.clone());
            let ety_env = ExpandEnv {
                substs,
                ..ety_env.clone()
            };
            // The errors are consed: the last one is the head of the OCaml list.
            let mut ty_errs = vec![];
            let mut cycles_acc = vec![];
            for (ck, ty) in tparam.constraints.iter() {
                let (ty_err_opt, cycles, ty) = localize_rec(&ety_env, env, ty);
                ty_errs.extend(ty_err_opt);
                t_utils::add_constraint(env, *ck, ty_fresh.clone(), ty, ety_env.on_error.clone());
                cycles_acc = append(cycles, cycles_acc);
            }
            ty_errs.reverse();
            let ty_err_opt = typing_error::multiple_opt(ty_errs);
            (Some(ety_env), ty_err_opt, cycles_acc, ty_fresh)
        }
        _ => {
            let (ty_err_opt, cycles, ty) = localize_rec(ety_env, env, ty);
            (None, ty_err_opt, cycles, ty)
        }
    }
}

fn localize_class_instantiation(
    ety_env: &ExpandEnv,
    env: &mut Env,
    r: Reason,
    sid: &Positioned<TypeName, BPos>,
    tyargs: &[DeclTy],
    class_info: Option<&cls::T>,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let sid: PosId = pos_id(sid);
    let (pos, name) = &sid;
    match class_info {
        None => {
            // Without class info, we don't know the kinds of the arguments.
            // We assume they are non-HK types.
            let ety_env = ExpandEnv {
                visibility_behavior: default_visibility_behaviour(),
                ..ety_env.clone()
            };
            let (err, cycles, tyl) =
                list_map_env_err_cycles(env, tyargs, typing_error::multiple_opt, |env, ty| {
                    localize_rec(&ety_env, env, ty)
                });
            (err, cycles, mk((r, Ty_::Tclass(sid, nonexact(), tyl))))
        }
        Some(class_info) => {
            if cls::enum_type(class_info).is_some() {
                match add_type_expansion_check_cycles(
                    ety_env,
                    type_expansions::Expansion {
                        name: type_expansions::expandable::T::Enum(name.clone()),
                        use_pos: pos.clone(),
                        def_pos: None,
                    },
                ) {
                    Err(cycle) => {
                        let ty = env::fresh_type_error(env, pos_or_decl::unsafe_to_raw_pos(pos.clone()));
                        (None, vec![cycle], ty)
                    }
                    Ok(ety_env) => {
                        if ast_defs::is_c_enum_class(cls::kind(class_info)) {
                            // Enum classes no longer has the ambiguity between the type of
                            // the enum set and the type of elements, so the enum class
                            // itself is seen as a Tclass
                            (None, vec![], mk((r, Ty_::Tclass(sid, nonexact(), vec![]))))
                        } else {
                            let (err, cycles, cstr) = match env::get_enum_constraint(env, name) {
                                // If not specified, default bound is arraykey
                                decl_entry::T::DoesNotExist
                                | decl_entry::T::NotYetAvailable
                                | decl_entry::T::Found(None) => (
                                    None,
                                    vec![],
                                    make_type::arraykey(typing_reason::implicit_upper_bound((
                                        pos.clone(),
                                        "arraykey".to_string(),
                                    ))),
                                ),
                                decl_entry::T::Found(Some(ty)) => localize_rec(&ety_env, env, &ty),
                            };
                            let enum_ty = mk((r.clone(), Ty_::Tnewtype(name.clone(), vec![], cstr)));
                            let r_dyn = r;
                            let enum_ty = if ety_env.ish_weakening {
                                make_type::intersection(
                                    r_dyn.clone(),
                                    vec![
                                        make_type::locl_like(r_dyn.clone(), enum_ty),
                                        make_type::arraykey(r_dyn),
                                    ],
                                )
                            } else {
                                enum_ty
                            };
                            (err, cycles, enum_ty)
                        }
                    }
                }
            } else {
                let tparams = cls::tparams_ref(class_info);
                let (err, cycles, tyl) = localize_targs_constrain_wildcards(
                    &under_type_constructor(ety_env),
                    env,
                    tyargs,
                    &tparams,
                );
                // Hide the class type if its internal and outside of the module
                if !ety_env.make_internal_opaque || typing_modules::is_class_visible(env, class_info)
                {
                    let r = typing_reason::definition(cls::pos(class_info), r);
                    (err, cycles, mk((r, Ty_::Tclass(sid, nonexact(), tyl))))
                } else {
                    let callee_module = match cls::get_module(class_info) {
                        Some(m) => m,
                        None => panic!("Internal error: module must exist for class to be not visible"),
                    };
                    let new_r =
                        typing_reason::opaque_type_from_module((cls::pos(class_info), callee_module, r));
                    let cstr = make_type::mixed(new_r.clone());
                    // If the class supports dynamic, reveal this in the newtype
                    let cstr = if cls::get_support_dynamic_type(class_info) {
                        make_type::supportdyn(new_r.clone(), cstr)
                    } else {
                        cstr
                    };
                    (err, cycles, mk((new_r, Ty_::Tnewtype(name.clone(), tyl, cstr))))
                }
            }
        }
    }
}

/// `localize_cstr` of `localize_typedef_instantiation`: localize a typedef
/// constraint. For supportdyn<T>, we use the localized arg directly to avoid
/// supportdynamic.hhi leaking into reasons.
fn localize_typedef_cstr(
    env: &mut Env,
    type_name: &str,
    tyargs_locl: &[Ty],
    ety_env_inner: &ExpandEnv,
    cstr: &DeclTy,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    if type_name == sn::classes::SUPPORT_DYN {
        (None, vec![], tyargs_locl.first().cloned().expect("List.hd_exn"))
    } else {
        // Disable intersection simplification when localizing the upper
        // bound constraint. Simplifying intersections during localization
        // calls Typing_intersection.intersect_list, which depends on
        // typing_subtype, which depends on typing_phase — creating a cycle
        // that can loop forever on recursive case type bounds.
        let ety_env_cstr = if ety_env_inner.simplify_intersections {
            std::borrow::Cow::Owned(ExpandEnv {
                simplify_intersections: false,
                ..ety_env_inner.clone()
            })
        } else {
            std::borrow::Cow::Borrowed(ety_env_inner)
        };
        localize_rec(&ety_env_cstr, env, cstr)
    }
}

fn localize_typedef_instantiation(
    ety_env: &ExpandEnv,
    env: &mut Env,
    r: Reason,
    type_name: &str,
    tyargs: &[DeclTy],
    typedef_info: Option<&TypedefType>,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    match typedef_info {
        Some(typedef_info) => {
            let tparams = &typedef_info.tparams;
            // Localize type args, handling wildcards
            // (`{ ety_env with visibility_behavior = default; under_type_constructor
            // = true }`, without a copy when it already is.)
            let ety_env_targs = if ety_env.under_type_constructor
                && matches!(
                    ety_env.visibility_behavior,
                    VisibilityBehavior::ExpandVisibleNewtypeOnly
                ) {
                std::borrow::Cow::Borrowed(ety_env)
            } else {
                std::borrow::Cow::Owned(ExpandEnv {
                    visibility_behavior: default_visibility_behaviour(),
                    under_type_constructor: true,
                    ..ety_env.clone()
                })
            };
            let (e1, cycles_tyargs, tyargs_locl) = localize_targs_constrain_wildcards(
                &ety_env_targs,
                env,
                tyargs,
                tparams,
            );
            // Expand the typedef at decl level. Substitution is handled by the
            // caller (via ety_env.substs during localization) to preserve wildcard
            // identity — decl-level substitution would duplicate Twildcard nodes.
            let typing_tdef::ExpansionResult {
                ety_env: result_ety_env,
                cycles: cycles_td,
                expansion,
            } = typing_tdef::expand_typedef(ety_env, env, &r, type_name);
            let cycles = append(cycles_td, cycles_tyargs);
            let arity_ok = |td_tparams: &[DeclTparam]| tyargs_locl.len() == td_tparams.len();
            // Build the ety_env for localizing the typedef body/constraint
            let make_ety_env_inner = |td_tparams: &[DeclTparam]| {
                let substs = decl_subst_make_locl(td_tparams, &tyargs_locl);
                ExpandEnv {
                    substs,
                    under_type_constructor: false,
                    ..result_ety_env.clone()
                }
            };
            let arity_error = |env: &mut Env, e1: TyErr, cycles: Vec<CycleReporter>| {
                let ty = env::fresh_type_error(
                    env,
                    pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)),
                );
                (e1, cycles, ty)
            };
            match expansion {
                typing_tdef::Expansion::Expanded {
                    tparams: td_tparams,
                    body,
                    cstr,
                } => {
                    if !arity_ok(&td_tparams) {
                        arity_error(env, e1, cycles)
                    } else {
                        let ety_env_inner = make_ety_env_inner(&td_tparams);
                        // TODO(T207369421): Cycle detection through constraints should be a
                        // well-formedness check in typing_type_wellformedness.ml, not a
                        // side effect of localization. We localize the constraint here even
                        // though we discard the localized value because localizing expands
                        // any typedefs referenced in the constraint, which triggers
                        // add_type_expansion_check_cycles and detects constraint cycles
                        // like `newtype A as B` / `newtype B as A`.
                        let (cstr_err, cstr_cycles, _cstr) =
                            localize_typedef_cstr(env, type_name, &tyargs_locl, &ety_env_inner, &cstr);
                        let (rhs_err, rhs_cycles, lty) = localize_rec(&ety_env_inner, env, &body);
                        let ty_err_opt = merge_errs(e1, cstr_err);
                        let ty_err_opt = merge_errs(ty_err_opt, rhs_err);
                        let lty = with_reason(lty, r.clone());
                        (
                            ty_err_opt,
                            append(append(cycles, cstr_cycles), rhs_cycles),
                            lty,
                        )
                    }
                }
                typing_tdef::Expansion::Opaque {
                    tparams: td_tparams,
                    cstr,
                } => {
                    if !arity_ok(&td_tparams) {
                        arity_error(env, e1, cycles)
                    } else {
                        let ety_env_inner = make_ety_env_inner(&td_tparams);
                        let (cstr_err, cstr_cycles, cstr) =
                            localize_typedef_cstr(env, type_name, &tyargs_locl, &ety_env_inner, &cstr);
                        let lty = mk((
                            r.clone(),
                            Ty_::Tnewtype(type_name.to_string(), tyargs_locl.clone(), cstr),
                        ));
                        let ty_err_opt = merge_errs(e1, cstr_err);
                        (ty_err_opt, append(cycles, cstr_cycles), lty)
                    }
                }
                typing_tdef::Expansion::Cyclic { td_type_assignment } => {
                    if !arity_ok(tparams) {
                        arity_error(env, e1, cycles)
                    } else {
                        // Cycle detected — produce a fallback type.
                        let cycle_r = typing_reason::illegal_recursive_type(
                            typing_reason::to_pos(&r),
                            type_name.to_string(),
                        );
                        let td_as_constraint = &typedef_info.as_constraint;
                        let mixed = match td_as_constraint {
                            Some(ty) => match ty.node_ref() {
                                DeclTy_::Tapply(sdt_args)
                                    if sdt_args.1.len() == 1
                                        && sdt_args.0.id_ref().as_str() == sn::classes::SUPPORT_DYN =>
                                {
                                    make_type::supportdyn_mixed(cycle_r.clone())
                                }
                                _ => make_type::mixed(cycle_r.clone()),
                            },
                            _ => make_type::mixed(cycle_r.clone()),
                        };
                        let lty = if ety_env.under_type_constructor {
                            match td_type_assignment {
                                d::TypedefTypeAssignment::CaseType(_, _) => mk((
                                    cycle_r,
                                    Ty_::Tnewtype(type_name.to_string(), tyargs_locl.clone(), mixed),
                                )),
                                d::TypedefTypeAssignment::SimpleTypeDef(_, _) => mixed,
                            }
                        } else {
                            match ety_env.visibility_behavior {
                                VisibilityBehavior::AlwaysExpandNewtype => mk((
                                    cycle_r,
                                    Ty_::Tnewtype(type_name.to_string(), tyargs_locl.clone(), mixed),
                                )),
                                VisibilityBehavior::ResolveTypeStructure(_)
                                | VisibilityBehavior::NeverExpandNewtype
                                | VisibilityBehavior::ExpandVisibleNewtypeOnly => mixed,
                            }
                        };
                        (e1, cycles, lty)
                    }
                }
            }
        }
        None => {
            let ty = env::fresh_type_error(env, pos_or_decl::unsafe_to_raw_pos(typing_reason::to_pos(&r)));
            (None, vec![], ty)
        }
    }
}

fn localize_cstr_ty(
    ety_env: &ExpandEnv,
    env: &mut Env,
    ty: &DeclTy,
    tp_name: &PosId,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let (err, cycles, ty) = localize_rec(ety_env, env, ty);
    let ty = map_reason(ty, |r| {
        typing_reason::cstr_on_generics((typing_reason::to_pos(&r), tp_name.clone()))
    });
    (err, cycles, ty)
}

/// `Decl_subst.make_locl`, over the localized types of this crate
/// (`crate::decl_subst::make_locl` builds a map of `oxidized` types, which
/// have the declared phase only).
pub(crate) fn decl_subst_make_locl<TP: decl_subst::TpName>(
    tparams: &[TP],
    tyl: &[Ty],
) -> crate::pmap::Map<String, Ty> {
    let mut subst = crate::pmap::Map::new();
    let mut tyl = tyl;
    for t in tparams {
        match tyl {
            [] => {}
            [ty, rl @ ..] => {
                subst.insert(t.tp_name().to_string(), ty.clone());
                tyl = rl;
            }
        }
    }
    subst
}

/// `localize_tparam` of `localize_ft`: localize the constraints for a type
/// parameter declaration. `cycles` is the list threaded with the environment.
fn localize_ft_tparam(
    ety_env: &ExpandEnv,
    env: &mut Env,
    cycles: &mut Vec<CycleReporter>,
    t: &DeclTparam,
) -> (TyErr, Tparam) {
    let t_tp_name = tp_name(t);
    let (ty_err_opt, cstrl) = list_map_env_ty_err_opt(
        env,
        &t.constraints,
        |env, (ck, ty)| {
            let (ty_err_opt, cycles_, ty) = localize_cstr_ty(ety_env, env, ty, &t_tp_name);
            let name_str = &t_tp_name.1;
            // In order to access type constants on generics on where clauses,
            // we need to add the constraints from the type parameters into the
            // environment before localizing the where clauses with them. Temporarily
            // add them to the environment here, and reset the environment later.
            match ck {
                ConstraintKind::ConstraintAs => env::add_upper_bound(None, env, name_str, ty.clone()),
                ConstraintKind::ConstraintSuper => {
                    env::add_lower_bound(None, env, name_str, ty.clone())
                }
                ConstraintKind::ConstraintEq => {
                    env::add_lower_bound(None, env, name_str, ty.clone());
                    env::add_upper_bound(None, env, name_str, ty.clone())
                }
            }
            *cycles = append(cycles_, std::mem::take(cycles));
            (ty_err_opt, (*ck, ty))
        },
        typing_error::multiple_opt,
    );
    (ty_err_opt, tparam_with_constraints(t, cstrl))
}

/// The first `localize_ft`, which returns the cycles.
///
/// For the majority of cases when we localize a function type we instantiate
/// the function's type parameters to Tvars. There are two cases where we do not do this.
///
/// 1) In Typing_subtype.subtype_method. See the comment for that function for why
///    this is necessary.
/// 2) When the type arguments are explicitly specified, in which case we instantiate
///    the type parameters to the provided types.
fn localize_ft_rec(
    instantiation: Option<MethodInstantiation>,
    ety_env: &ExpandEnv,
    def_pos: PosOrDecl,
    env: &mut Env,
    ft: &DeclFunType,
) -> (TyErr, Vec<CycleReporter>, FunType) {
    let (arity_ty_err_opt, substs) = match &instantiation {
        Some(MethodInstantiation {
            explicit_targs,
            use_name: _,
            use_pos,
        }) => {
            let ty_err_opt = if !explicit_targs.is_empty() && explicit_targs.len() != ft.tparams.len()
            {
                Some(typing_error::primary(primary::T::Expected_tparam {
                    decl_pos: def_pos.clone(),
                    pos: use_pos.clone(),
                    n: ft.tparams.len() as isize,
                }))
            } else {
                None
            };
            let tvarl: Vec<Ty> = explicit_targs
                .iter()
                .map(|aast::Targ(ty, _)| ty.clone())
                .collect();
            let ft_subst = if explicit_targs.is_empty() {
                crate::pmap::Map::new()
            } else {
                decl_subst_make_locl(&ft.tparams, &tvarl)
            };
            // `S_map.union`: the binding of the first map wins (the union
            // with an empty map is the other map; `pmap::Map::union` keeps
            // the bindings of `self`).
            // (`None`: the substitution of `ety_env`, which is then used as
            // it is, without a copy.)
            let substs = if ft_subst.is_empty() {
                None
            } else {
                Some(ft_subst.union(ety_env.substs.clone()))
            };
            (ty_err_opt, substs)
        }
        None => (None, None),
    };
    let ety_env: std::borrow::Cow<'_, ExpandEnv> = match substs {
        None => std::borrow::Cow::Borrowed(ety_env),
        Some(substs) => std::borrow::Cow::Owned(ExpandEnv {
            substs,
            ..ety_env.clone()
        }),
    };
    // Grab and store the old tpenvs
    let old_tpenv = env::get_tpenv(env);
    let old_global_tpenv = env.tpenv.clone();
    // Always localize tparams so they are available for later Tast check
    let mut cycles_tparams = vec![];
    let (tparam_ty_err_opt, tparams) = list_map_env_ty_err_opt(
        env,
        &ft.tparams,
        |env, t| localize_ft_tparam(&ety_env, env, &mut cycles_tparams, t),
        typing_error::multiple_opt,
    );
    // Localize the 'where' constraints
    let mut cycles_where_constraints = vec![];
    let (where_cstr_ty_err_opt, where_constraints) = list_map_env_ty_err_opt(
        env,
        &ft.where_constraints,
        |env, d::WhereConstraint(ty1, ck, ty2)| {
            let (e1, cycles1, ty1) = localize_rec(&ety_env, env, ty1);
            let (e2, cycles2, ty2) = localize_rec(&ety_env, env, ty2);
            let ty_err_opt = merge_errs(e1, e2);
            cycles_where_constraints = append(
                append(cycles1, cycles2),
                std::mem::take(&mut cycles_where_constraints),
            );
            (ty_err_opt, WhereConstraint(ty1, *ck, ty2))
        },
        typing_error::multiple_opt,
    );
    // Remove the constraints we added for localizing where constraints.
    // (When there was nothing to localize, nothing has run since the tpenvs
    // were read: putting them back would change nothing, and copies the
    // continuations of the environment.)
    let nothing_localized = ft.where_constraints.is_empty()
        && ft.tparams.iter().all(|tp| tp.constraints.is_empty());
    if !nothing_localized {
        env::env_with_tpenv(env, old_tpenv);
        env::env_with_global_tpenv(env, old_global_tpenv);
    }
    // If we're instantiating the generic parameters then add a deferred
    // check that constraints are satisfied under the
    // substitution [ety_env.substs].
    let (gen_param_ty_err_opt, cycles_constraints) = match &instantiation {
        Some(MethodInstantiation { use_pos, .. }) => {
            let (e1, cycles_tparams) =
                check_tparams_constraints_rec(use_pos.clone(), &ety_env, env, &ft.tparams);
            let (e2, cycles_where_constraints) = check_where_constraints_rec(
                false,
                use_pos.clone(),
                &ety_env,
                def_pos.clone(),
                env,
                &ft.where_constraints,
            );
            let ty_err_opt = merge_errs(e1, e2);
            (ty_err_opt, append(cycles_tparams, cycles_where_constraints))
        }
        None => (None, vec![]),
    };
    // (The OCaml also threads a counter of the parameters, which it drops.)
    let mut cycles_params = vec![];
    let (variadic_params_ty_err_opt, params) = list_map_env_ty_err_opt(
        env,
        &ft.params,
        |env, param| {
            let (ty_err_opt, cycles, ty) = localize_rec(&ety_env, env, &param.ty);
            cycles_params = append(cycles, std::mem::take(&mut cycles_params));
            (ty_err_opt, fun_param_with_type(param, ty))
        },
        typing_error::multiple_opt,
    );
    let (implicit_params_ty_err_opt, cycles_impl_param, implicit_params) = {
        let ((err, cycles), capability) = match &ft.implicit_params.capability {
            d::Capability::CapTy(c) => {
                let (err, cycles, ty) = localize_rec(&ety_env, env, c);
                ((err, cycles), Capability::CapTy(ty))
            }
            d::Capability::CapDefaults(p) => ((None, vec![]), Capability::CapDefaults(decl_pos(p))),
        };
        (err, cycles, FunImplicitParams { capability })
    };
    let (ret_ty_err_opt, cycles_ret, ret) = localize_rec(&ety_env, env, &ft.ret);
    let ty_err_opt = typing_error::multiple_opt(filter_some([
        arity_ty_err_opt,
        tparam_ty_err_opt,
        where_cstr_ty_err_opt,
        gen_param_ty_err_opt,
        variadic_params_ty_err_opt,
        implicit_params_ty_err_opt,
        ret_ty_err_opt,
    ]));
    let cycles = [
        cycles_tparams,
        cycles_where_constraints,
        cycles_constraints,
        cycles_params,
        cycles_impl_param,
        cycles_ret,
    ]
    .into_iter()
    .flatten()
    .collect();
    (
        ty_err_opt,
        cycles,
        FunType {
            params,
            implicit_params,
            ret,
            tparams,
            where_constraints,
            flags: ft.flags,
            instantiated: ft.instantiated,
        },
    )
}

/// `check_tparam_constraint` of `check_tparams_constraints` (the first one,
/// which the logging one calls): `ty_errs` is the OCaml list of errors, last
/// element first.
fn check_tparam_constraint_(
    env: &mut Env,
    mut ty_errs: Vec<typing_error::T>,
    use_pos: &Pos,
    (ck, cstr_ty): (ConstraintKind, Ty),
    ty: &Ty,
) -> Vec<typing_error::T> {
    let e2 = tgen_constraint::check_tparams_constraint(env, use_pos.clone(), ck, cstr_ty, ty.clone());
    ty_errs.extend(e2);
    ty_errs
}

/// The first `check_tparams_constraints`, which returns the cycles.
///
/// Given a list of generic parameters [tparams] and a substitution
/// in [ety_env.substs] whose domain is at least these generic parameters,
/// check that the types satisfy
/// the constraints on the corresponding generic parameter.
///
/// Note that the constraints may contain occurrences of the generic
/// parameters, but the subsitution will be applied to them. e.g. if tparams is
///   <Tu as MyCovariant<Tu>, Tv super Tu>
/// and ety_env.substs is
///   Tu :-> C
///   Tv :-> I
/// with
///   class C extends MyContravariant<I> implements I { ... }
/// Then the constraints are satisfied, because
///   C is a subtype of MyContravariant<C>
///   I is a supertype of C
fn check_tparams_constraints_rec(
    use_pos: Pos,
    ety_env: &ExpandEnv,
    env: &mut Env,
    tparams: &[DeclTparam],
) -> (TyErr, Vec<CycleReporter>) {
    let check_tparam_constraint =
        |env: &mut Env, ty_errs: Vec<typing_error::T>, (ck, cstr_ty): (ConstraintKind, Ty), ty: &Ty| {
            if log::should_log_check_tparams_constraints(env) {
                let cstr_ty_ = cstr_ty.clone();
                log::log_check_tparams_constraints(env, &use_pos, &cstr_ty_, ty, |env| {
                    check_tparam_constraint_(env, ty_errs, &use_pos, (ck, cstr_ty), ty)
                })
            } else {
                check_tparam_constraint_(env, ty_errs, &use_pos, (ck, cstr_ty), ty)
            }
        };
    // The errors, last one first (the OCaml list), and the cycles.
    let mut ty_errs: Vec<typing_error::T> = vec![];
    let mut cycles_acc: Vec<CycleReporter> = vec![];
    for t in tparams {
        let nm = t.name.id_ref().as_str();
        if ety_env.no_substs.contains(nm) {
            continue;
        }
        match ety_env.substs.get(nm) {
            Some(_) if t.constraints.is_empty() => {}
            Some(ty) => {
                let ty = ty.clone();
                let t_tp_name = tp_name(t);
                for (ck, cstr_ty) in t.constraints.iter() {
                    let (e1, cycles1, cstr_ty) = localize_cstr_ty(ety_env, env, cstr_ty, &t_tp_name);
                    ty_errs.extend(e1);
                    ty_errs = check_tparam_constraint(env, ty_errs, (*ck, cstr_ty), &ty);
                    cycles_acc = append(cycles1, cycles_acc);
                }
            }
            None => {}
        }
    }
    ty_errs.reverse();
    (typing_error::multiple_opt(ty_errs), cycles_acc)
}

/// The first `check_where_constraints`, which returns the cycles.
fn check_where_constraints_rec(
    in_class: bool,
    use_pos: Pos,
    ety_env: &ExpandEnv,
    definition_pos: PosOrDecl,
    env: &mut Env,
    cstrl: &[DeclWhereConstraint],
) -> (TyErr, Vec<CycleReporter>) {
    // (Nothing to check: no callback to build.)
    if cstrl.is_empty() {
        return (typing_error::multiple_opt(vec![]), vec![]);
    }
    let cycles_acc = vec![];
    let ety_env = {
        let on_error = Some(reasons_callback::explain_where_constraint(
            use_pos.clone(),
            in_class,
            definition_pos.clone(),
        ));
        ExpandEnv {
            on_error,
            ..ety_env.clone()
        }
    };
    // The errors, last one first (the OCaml list).
    let mut ty_errs = vec![];
    let mut cycles_acc = cycles_acc;
    for d::WhereConstraint(ty, ck, cstr_ty) in cstrl {
        let (e1, cycles1, ty) = localize_rec(&ety_env, env, ty);
        let (e2, cycles2, cstr_ty) = localize_rec(&ety_env, env, cstr_ty);
        let e3 = tgen_constraint::check_where_constraint(
            in_class,
            env,
            use_pos.clone(),
            definition_pos.clone(),
            *ck,
            cstr_ty,
            ty,
        );
        let ty_err_opt = typing_error::multiple_opt(filter_some([e1, e2, e3]));
        ty_errs.extend(ty_err_opt);
        cycles_acc = append(append(cycles1, cycles2), cycles_acc);
    }
    ty_errs.reverse();
    (typing_error::multiple_opt(ty_errs), cycles_acc)
}

fn localize_refinement(
    ety_env: &ExpandEnv,
    env: &mut Env,
    r: Reason,
    root: &DeclTy,
    decl_cr: &DeclClassRefinement,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let mk_unsupported_err = |r: &Reason| {
        let pos = typing_reason::to_pos(r);
        ety_env.on_error.clone().map(|on_error| {
            typing_error::apply_reasons(secondary::T::Unsupported_refinement(pos), on_error)
        })
    };
    let both_err = merge_errs;
    let (err_opt, cycles_root, root) = localize_rec(ety_env, env, root);
    let (err_refinements, cycles_refinements, ty) = match get_node(&root) {
        Ty_::Tclass(cid, Exact::Nonexact(cr), tyl) => {
            // `Class_refinement.fold_refined_consts ~f ~init:((env, None, []), cr) decl_cr`
            // (`env` is threaded by the closure; the accumulator is the rest)
            type Acc = ((TyErr, Vec<CycleReporter>), ClassRefinement);
            let f = |id: &str, rc: &DeclRefinedConst, ((ty_err_opt, cycles_acc), cr): Acc| -> Acc {
                let d::RefinedConst {
                    bound: rc_bound,
                    is_ctx: rc_is_ctx,
                } = rc;
                let (ty_err_opt_, cycles_rc_bound, rc_bound) = match rc_bound {
                    d::RefinedConstBound::Exact(ty) => {
                        let (err, cycles, ty) = localize_rec(ety_env, env, ty);
                        (err, cycles, RefinedConstBound::TRexact(ty))
                    }
                    d::RefinedConstBound::Loose(d::RefinedConstBounds {
                        lower: tr_lower,
                        upper: tr_upper,
                    }) => {
                        // `List.map_env (env, None, [])`
                        let localize_list = |env: &mut Env, tyl: &[DeclTy]| {
                            let mut ty_err_opt: TyErr = None;
                            let mut cycles_acc: Vec<CycleReporter> = vec![];
                            let mut out = Vec::with_capacity(tyl.len());
                            for ty in tyl {
                                let (ty_err_opt_, cycles, ty) = localize_rec(ety_env, env, ty);
                                ty_err_opt = both_err(ty_err_opt, ty_err_opt_);
                                cycles_acc = append(cycles, cycles_acc);
                                out.push(ty);
                            }
                            (ty_err_opt, cycles_acc, out)
                        };
                        let (ty_err_opt1, cycles_lower, tr_lower) = localize_list(env, tr_lower);
                        let (ty_err_opt2, cycles_upper, tr_upper) = localize_list(env, tr_upper);
                        (
                            both_err(ty_err_opt1, ty_err_opt2),
                            append(cycles_lower, cycles_upper),
                            RefinedConstBound::TRloose(RefinedConstBounds {
                                lower: tr_lower,
                                upper: tr_upper,
                            }),
                        )
                    }
                };
                let cr = class_refinement::add_refined_const(
                    id.to_string(),
                    RefinedConst {
                        bound: rc_bound,
                        is_ctx: *rc_is_ctx,
                    },
                    cr,
                );
                (
                    (
                        both_err(ty_err_opt, ty_err_opt_),
                        append(cycles_rc_bound, cycles_acc),
                    ),
                    cr,
                )
            };
            let ((ty_err_opt, cycles_refinements), cr) =
                class_refinement::fold_refined_consts_decl(decl_cr, ((None, vec![]), cr.clone()), f);
            (
                ty_err_opt,
                cycles_refinements,
                mk((r, Ty_::Tclass(cid.clone(), Exact::Nonexact(cr), tyl.clone()))),
            )
        }
        _ => {
            let ty = env::fresh_type_error(env, Pos::NONE);
            (mk_unsupported_err(&r), vec![], ty)
        }
    };
    let err = both_err(err_opt, err_refinements);
    let cycles = append(cycles_root, cycles_refinements);
    (err, cycles, ty)
}

/// The first `localize_targ`, which returns the cycles.
///
/// Localize an explicit type argument to a constructor or function. We
/// support the use of wildcards at the top level only
fn localize_targ_rec(
    tparam: Option<&DeclTparam>,
    check_type_integrity: bool,
    env: &mut Env,
    hint: &aast::Hint,
) -> (TyErr, Vec<CycleReporter>, tast::Targ) {
    // For explicit type arguments we support a wildcard syntax `_` for which
    // Hack will generate a fresh type variable
    match hint {
        aast::Hint(p, h) if matches!(**h, aast::Hint_::Hwildcard) => {
            let ty = env::fresh_type(env, p.clone());
            (None, vec![], aast::Targ(ty, hint.clone()))
        }
        aast::Hint(hint_pos, _) => {
            let ty = decl_hint::hint(&env.decl_env, hint);
            let in_reified = tparam.map_or(false, |tparam| !is_erased(tparam.reified));
            let should_check_package_boundary = {
                use typing_error::primary::package::TargetSymbolSpec;
                if in_reified {
                    typing_packages::CheckReason::Yes(TargetSymbolSpec::Reified_generic)
                } else if tparam.is_some() {
                    typing_packages::CheckReason::Yes(TargetSymbolSpec::Generic)
                } else {
                    typing_packages::CheckReason::No
                }
            };
            if check_type_integrity {
                typing_type_integrity::check_type_integrity(
                    false,
                    should_check_package_boundary,
                    env,
                    &ty,
                );
            }
            let ety_env = empty_expand_env_with_on_error(reasons_callback::invalid_type_hint(
                hint_pos.clone(),
            ));
            let ety_env = match tparam {
                Some(tp) if attributes::mem(sn::user_attributes::EXPLICIT, &tp.user_attributes) => {
                    ExpandEnv {
                        wildcard_action: WildcardAction::WildcardRequireExplicit(Rc::new(tp.clone())),
                        ..ety_env
                    }
                }
                _ => ety_env,
            };
            let (err, cycles, ty) = localize_rec(&ety_env, env, &ty);
            (err, cycles, aast::Targ(ty, hint.clone()))
        }
    }
}

/// Declare and localize the type arguments to a constructor or function, given
/// information about the declared type parameters in `decl_tparam list`. If no
/// explicit type arguments are given, generate fresh type variables in their
/// place; do the same for any wildcard explicit type arguments.
/// Report arity errors using `def_pos` (for the declared parameters), `use_pos`
/// (for the use-site) and `use_name` (the name of the constructor or function).
pub fn localize_targs(
    check_type_integrity: bool,
    is_method: bool,
    def_pos: PosOrDecl,
    use_pos: Pos,
    use_name: String,
    check_explicit_targs: Option<bool>,
    env: &mut Env,
    tparaml: &[DeclTparam],
    targl: Vec<aast::Hint>,
) -> (TyErr, Vec<tast::Targ>) {
    let check_explicit_targs = check_explicit_targs.unwrap_or(true);
    let targ_count = targl.len();
    let generated_tparam_count = tparaml
        .iter()
        .filter(|t| sn_coeffects::is_generated_generic(t.name.id_ref().as_str()))
        .count();
    let tparam_count = tparaml.len();
    let explicit_tparam_count = tparam_count - generated_tparam_count;

    let checking_rewritten_call = || {
        // Typing_phase expands the case of targl=[] to a list of wildcards matching the
        // length of tparaml, but some `if` condition checks retype already typed
        // expressions, so we get the generated list instead of what the user wrote
        // TODO(coeffects) attempt to remove Tast.to_nast_expr calls
        generated_tparam_count > 0
            && targ_count == tparam_count
            && targl.iter().all(aast_defs::is_wildcard_hint)
    };
    // If there are explicit type arguments but too few or too many then
    // report an error
    let arity_ty_err_opt = if !(targ_count == 0
        || targ_count == explicit_tparam_count
        || checking_rewritten_call())
    {
        if is_method {
            Some(typing_error::primary(primary::T::Expected_tparam {
                decl_pos: def_pos.clone(),
                pos: use_pos.clone(),
                n: explicit_tparam_count as isize,
            }))
        } else {
            Some(typing_error::primary(primary::T::Type_arity_mismatch {
                pos: use_pos.clone(),
                decl_pos: def_pos.clone(),
                expected: tparam_count as isize,
                actual: targ_count as isize,
            }))
        }
    } else {
        None
    };

    // Declare and localize the explicit type arguments
    // (`List.zip_with_remainder`: as many as the shorter of the two lists)
    // `List.map_env (env, [], [])`: the errors are consed (the last one is the
    // head of the OCaml list).
    let mut ty_errs = vec![];
    let mut _cycles_targs: Vec<CycleReporter> = vec![];
    let explicit_targs: Vec<tast::Targ> = targl
        .iter()
        .zip(tparaml.iter())
        .map(|(targ, tparam)| {
            let (ty_err_opt, cycles, res) =
                localize_targ_rec(Some(tparam), check_type_integrity, env, targ);
            ty_errs.extend(ty_err_opt);
            _cycles_targs = append(cycles, std::mem::take(&mut _cycles_targs));
            res
        })
        .collect();
    ty_errs.reverse();
    let explicit_targ_ty_err_opt = typing_error::multiple_opt(ty_errs);
    // Generate fresh type variables for the remainder
    let (implicit_targ_ty_err_opt, implicit_targs) = {
        let mk_implicit_targ = |env: &mut Env, tparam: &DeclTparam| {
            let wildcard_hint = aast::Hint(use_pos.clone(), Box::new(aast::Hint_::Hwildcard));
            let name = tp_name(tparam);
            let tvar = env::fresh_type_reason(None, env, use_pos.clone(), |tvid| {
                typing_reason::type_variable_generics(
                    (use_pos.clone(), name.1.clone(), use_name.clone()),
                    tvid,
                )
            });
            log::log_tparam_instantiation(env, &use_pos, &name.1, &tvar);
            (None, aast::Targ(tvar, wildcard_hint))
        };
        // `List.drop tparaml targ_count`
        let rest = tparaml.get(targ_count..).unwrap_or(&[]);
        list_map_env_ty_err_opt(env, rest, mk_implicit_targ, typing_error::multiple_opt)
    };

    let check_for_explicit_user_attribute = |tparam: &DeclTparam, targ: &tast::Targ| {
        let aast::Targ(_, hint) = targ;
        if attributes::mem(sn::user_attributes::EXPLICIT, &tparam.user_attributes)
            && aast_defs::is_wildcard_hint(hint)
        {
            let (decl_pos, param_name) = tp_name(tparam);
            Some(typing_error::primary(primary::T::Require_generic_explicit {
                decl_pos,
                param_name,
                pos: hint.0.clone(),
            }))
        } else {
            None
        }
    };

    let ua_ty_err_opt = if check_explicit_targs {
        // `List.fold2_exn tparaml (explicit_targs @ implicit_targs) ~init:[]`:
        // the errors are consed.
        let targs: Vec<&tast::Targ> = explicit_targs.iter().chain(implicit_targs.iter()).collect();
        if tparaml.len() != targs.len() {
            panic!(
                "length mismatch in fold2_exn: {} <> {}",
                tparaml.len(),
                targs.len()
            )
        }
        let mut ty_errs: Vec<typing_error::T> = tparaml
            .iter()
            .zip(targs)
            .filter_map(|(tp, targ)| check_for_explicit_user_attribute(tp, targ))
            .collect();
        ty_errs.reverse();
        typing_error::multiple_opt(ty_errs)
    } else {
        None
    };
    let ty_err_opt = typing_error::multiple_opt(filter_some([
        arity_ty_err_opt,
        explicit_targ_ty_err_opt,
        implicit_targ_ty_err_opt,
        ua_ty_err_opt,
    ]));
    let mut targs = explicit_targs;
    targs.extend(implicit_targs);
    (ty_err_opt, targs)
}

/// Localize a type that we know to be a union of disjoint types.
pub fn localize_disjoint_union(ety_env: &ExpandEnv, env: &mut Env, dty: &DeclTy) -> (TyErr, Ty) {
    let r = localize_reason(dty.reason());
    match dty.node_ref() {
        DeclTy_::Tunion(tyl) => {
            let (ty_err_opt, _cycles, tyl) =
                list_map_env_err_cycles(env, tyl, typing_error::union_opt, |env, ty| {
                    localize_rec(ety_env, env, ty)
                });
            // We know the types to be disjoint, so we don't simplify the union
            let ty = make_type::union(r, tyl);
            (ty_err_opt, ty)
        }
        _ => {
            let (err, _cycles, ty) = localize_rec(ety_env, env, dty);
            (err, ty)
        }
    }
}

/// The first `localize_no_subst_`.
///
/// Performs no substitutions of generics and initializes Tthis to
/// Env.get_self env
fn localize_no_subst_(
    env: &mut Env,
    wildcard_action: WildcardAction,
    ish_weakening: bool,
    on_error: Option<reasons_callback::T>,
    report_cycle: Option<(Pos, type_expansions::expandable::T)>,
    ty: &DeclTy,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let ety_env = ExpandEnv {
        type_expansions: type_expansions::empty_w_cycle_report(report_cycle),
        on_error,
        wildcard_action,
        ish_weakening,
        ..empty_expand_env()
    };
    localize_rec(&ety_env, env, ty)
}

fn localize_no_subst_no_cycles(
    env: &mut Env,
    wildcard_action: WildcardAction,
    ish_weakening: bool,
    on_error: Option<reasons_callback::T>,
    ty: &DeclTy,
) -> (TyErr, Ty) {
    let (err, _cycles, ty) =
        localize_no_subst_(env, wildcard_action, ish_weakening, on_error, None, ty);
    (err, ty)
}

fn localize_hint_no_subst_report_cycles_(
    env: &mut Env,
    ignore_errors: bool,
    report_cycle: Option<(Pos, type_expansions::expandable::T)>,
    h: &aast::Hint,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let aast::Hint(pos, _) = h;
    let h = decl_hint::hint(&env.decl_env, h);
    localize_no_subst_(
        env,
        WildcardAction::WildcardIllegal,
        false,
        if ignore_errors {
            None
        } else {
            Some(reasons_callback::invalid_type_hint(pos.clone()))
        },
        report_cycle,
        &h,
    )
}

pub fn localize_typedef_structure(
    env: &mut Env,
    ignore_errors: bool,
    report_cycle: (Pos, type_expansions::expandable::T),
    name: Option<String>,
    h: &aast::Hint,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    let aast::Hint(pos, _) = h;
    let ty = decl_hint::hint(&env.decl_env, h);
    let ety_env = ExpandEnv {
        visibility_behavior: VisibilityBehavior::ResolveTypeStructure(name),
        type_expansions: type_expansions::empty_w_cycle_report(Some(report_cycle)),
        on_error: if ignore_errors {
            None
        } else {
            Some(reasons_callback::invalid_type_hint(pos.clone()))
        },
        wildcard_action: WildcardAction::WildcardIllegal,
        ish_weakening: false,
        ..empty_expand_env()
    };
    localize_rec(&ety_env, env, &ty)
}

/// Transform a type hint into a localized type, with no substitution for generic
/// parameters and [this].
///
/// [ignore_errors] silences errors because those errors have already fired
/// and/or are not appropriate at the time we call localize.
pub fn localize_hint_no_subst(env: &mut Env, ignore_errors: bool, h: &aast::Hint) -> (TyErr, Ty) {
    let (err, _cycles, ty) = localize_hint_no_subst_report_cycles_(env, ignore_errors, None, h);
    (err, ty)
}

/// Transform a type hint into a localized type, with no substitution for generic
/// parameters and [this]. Report cycles on provided [report_cycle] expansion.
///
/// [ignore_errors] silences errors because those errors have already fired
/// and/or are not appropriate at the time we call localize.
pub fn localize_hint_no_subst_report_cycles(
    env: &mut Env,
    ignore_errors: bool,
    report_cycle: (Pos, type_expansions::expandable::T),
    h: &aast::Hint,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    localize_hint_no_subst_report_cycles_(env, ignore_errors, Some(report_cycle), h)
}

pub fn localize_hint_for_refinement(env: &mut Env, hint: &aast::Hint) -> (TyErr, Ty) {
    let aast::Hint(pos, _) = hint;
    let h = decl_hint::hint(&env.decl_env, hint);
    // `Typechecker_options.pessimise_builtins`, which the crate does not have.
    let ish_weakening = {
        let tcopt = env::get_tcopt(env);
        tcopt.po.everything_sdt || tcopt.tco_pessimise_builtins
    };
    localize_no_subst_no_cycles(
        env,
        WildcardAction::WildcardFreshGeneric,
        ish_weakening,
        Some(reasons_callback::invalid_type_hint(pos.clone())),
        &h,
    )
}

pub fn localize_hint_for_lambda(env: &mut Env, h: &aast::Hint) -> (TyErr, Ty) {
    let aast::Hint(pos, _) = h;
    let h = decl_hint::hint(&env.decl_env, h);
    localize_no_subst_no_cycles(
        env,
        WildcardAction::WildcardFreshTyvar,
        false,
        Some(reasons_callback::invalid_type_hint(pos.clone())),
        &h,
    )
}

/// The second `localize_no_subst_` of `typing_phase.ml`, which shadows the
/// first.
fn localize_no_subst_ignore_errors(
    env: &mut Env,
    ignore_errors: bool,
    report_cycle: Option<(Pos, type_expansions::expandable::T)>,
    ty: &DeclTy,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    localize_no_subst_(
        env,
        WildcardAction::WildcardIllegal,
        false,
        if ignore_errors {
            None
        } else {
            Some(reasons_callback::invalid_type_hint(
                pos_or_decl::unsafe_to_raw_pos(decl_get_pos(ty)),
            ))
        },
        report_cycle,
        ty,
    )
}

/// Transform a declaration phase type into a localized type, with no substitution
/// for generic parameters and [this].
///
/// [ignore_errors] silences errors because those errors have already fired
/// and/or are not appropriate at the time we call localize.
pub fn localize_no_subst(env: &mut Env, ignore_errors: bool, ty: &DeclTy) -> (TyErr, Ty) {
    let (err, _cycles, ty) = localize_no_subst_ignore_errors(env, ignore_errors, None, ty);
    (err, ty)
}

pub fn localize_fun_type_no_subst(
    fun_type: &DeclFunType,
    env: &mut Env,
    ignore_errors: bool,
) -> (TyErr, FunType) {
    let (env_err, ty) = localize_no_subst(
        env,
        ignore_errors,
        &DeclTy::new(R::none(), DeclTy_::Tfun(Box::new(fun_type.clone()))),
    );
    let Ty(_, node) = ty;
    match unwrap_node(node) {
        Ty_::Tfun(fun_type) => (env_err, std::rc::Rc::unwrap_or_clone(fun_type)),
        _ => panic!("localize_fun_type_no_subst: expected a function type"),
    }
}

pub fn localize_no_subst_report_cycles(
    env: &mut Env,
    ignore_errors: bool,
    report_cycle: (Pos, type_expansions::expandable::T),
    ty: &DeclTy,
) -> (TyErr, Vec<CycleReporter>, Ty) {
    localize_no_subst_ignore_errors(env, ignore_errors, Some(report_cycle), ty)
}

/// Same as [localize_targs] but also check constraints on type parameters
/// (though not `where` constraints)
pub fn localize_targs_and_check_constraints(
    exact: Exact,
    check_type_integrity: bool,
    def_pos: PosOrDecl,
    use_pos: Pos,
    check_explicit_targs: Option<bool>,
    env: &mut Env,
    class_id: &ast_defs::Id,
    r: Reason,
    tparaml: &[DeclTparam],
    hintl: Vec<aast::Hint>,
) -> (TyErr, Ty, Vec<tast::Targ>) {
    let check_explicit_targs = check_explicit_targs.unwrap_or(true);
    let (e1, type_argl) = localize_targs(
        check_type_integrity,
        false,
        def_pos,
        use_pos.clone(),
        utils::strip_ns(&class_id.1).to_string(),
        Some(check_explicit_targs),
        env,
        tparaml,
        hintl,
    );
    let targs_tys: Vec<Ty> = type_argl.iter().map(|aast::Targ(ty, _)| ty.clone()).collect();
    let this_ty = mk((
        r,
        Ty_::Tclass(
            positioned::of_raw_positioned((class_id.0.clone(), class_id.1.clone())),
            exact,
            targs_tys.clone(),
        ),
    ));
    let ety_env = ExpandEnv {
        this_ty: this_ty.clone(),
        substs: decl_subst_make_locl(tparaml, &targs_tys),
        on_error: Some(reasons_callback::unify_error_at(use_pos.clone())),
        ..empty_expand_env()
    };
    let (e2, _cycles) = check_tparams_constraints_rec(use_pos, &ety_env, env, tparaml);
    let ty_err_opt = merge_errs(e1, e2);
    (ty_err_opt, this_ty, type_argl)
}

/// Add generic parameters to the environment, localize their bounds, and
/// transform these into a flat list of constraints of the form (ty1,ck,ty2)
/// where ck is as, super or =
fn localize_and_add_generic_parameters_with_bounds(
    ety_env: &ExpandEnv,
    env: &mut Env,
    tparams: &[DeclTparam],
) -> (TyErr, Vec<CycleReporter>) {
    env::add_generic_parameters(env, tparams);
    let mut cycles_tparams: Vec<CycleReporter> = vec![];
    let localize_bound = |env: &mut Env, tp: &DeclTparam| {
        let (pos, name) = tp_name(tp);
        let tparam_ty = mk((typing_reason::witness_from_decl(pos), Ty_::Tgeneric(name)));
        list_map_env_ty_err_opt(
            env,
            &tp.constraints,
            |env, (ck, cstr)| {
                let (err, cycle, ty) = localize_rec(ety_env, env, cstr);
                cycles_tparams = append(cycle, std::mem::take(&mut cycles_tparams));
                (err, (tparam_ty.clone(), *ck, ty))
            },
            typing_error::multiple_opt,
        )
    };
    let (ty_err_opt, cstrss) =
        list_map_env_ty_err_opt(env, tparams, localize_bound, typing_error::multiple_opt);
    let add_constraint = |env: &mut Env, (ty1, ck, ty2): (Ty, ConstraintKind, Ty)| {
        t_utils::add_constraint(env, ck, ty1, ty2, ety_env.on_error.clone())
    };
    for cstr in cstrss.into_iter().flatten() {
        add_constraint(env, cstr)
    }
    (ty_err_opt, cycles_tparams)
}

// Helper functions

pub fn sub_type_decl(
    env: &mut Env,
    ty1: &DeclTy,
    ty2: &DeclTy,
    on_error: Option<reasons_callback::T>,
) -> TyErr {
    let (e1, ty1) = localize_no_subst(env, true, ty1);
    let (e2, ty2) = localize_no_subst(env, true, ty2);
    let e3 = t_utils::sub_type(env, None, None, None, None, ty1, ty2, on_error);
    typing_error::multiple_opt(filter_some([e1, e2, e3]))
}

/// Are two decl types definitely subtypes of each other?
///
/// (The OCaml drops the environment it threads: this works on a copy.)
pub fn is_sub_type_decl(
    is_dynamic_aware: Option<bool>,
    env: &Env,
    ty1: &DeclTy,
    ty2: &DeclTy,
) -> bool {
    let mut env = env.clone();
    let env = &mut env;
    let (e1, ty1) = localize_no_subst(env, true, ty1);
    let (e2, ty2) = localize_no_subst(env, true, ty2);
    let e3 = t_utils::sub_type(
        env,
        is_dynamic_aware,
        None,
        None,
        None,
        ty1,
        ty2,
        Some(reasons_callback::unify_error_at(Pos::NONE)),
    );
    e1.is_none() && e2.is_none() && e3.is_none()
}

/// Add generic parameters to the environment, with localized bounds,
/// and also add any consequences of `where` constraints
pub fn localize_and_add_generic_parameters_and_where_constraints(
    ety_env: &ExpandEnv,
    env: &mut Env,
    tparams: &[DeclTparam],
    where_constraints: &[DeclWhereConstraint],
) -> TyErr {
    /// The first `localize_and_add_where_constraints` of `typing_phase.ml`,
    /// which the function of the `.mli` shadows.
    fn localize_and_add_where_constraints(
        ety_env: &ExpandEnv,
        env: &mut Env,
        where_constraints: &[DeclWhereConstraint],
    ) -> (TyErr, Vec<CycleReporter>) {
        // The errors, last one first (the OCaml list).
        let mut ty_errs = vec![];
        let mut cycles_acc = vec![];
        for d::WhereConstraint(ty1, ck, ty2) in where_constraints {
            let (e1, cycles1, ty1) = localize_rec(ety_env, env, ty1);
            let (e2, cycles2, ty2) = localize_rec(ety_env, env, ty2);
            t_utils::add_constraint(env, *ck, ty1, ty2, ety_env.on_error.clone());
            ty_errs.extend(merge_errs(e1, e2));
            cycles_acc = append(append(cycles1, cycles2), cycles_acc);
        }
        ty_errs.reverse();
        (typing_error::multiple_opt(ty_errs), cycles_acc)
    }
    let (e1, _cycles) = localize_and_add_generic_parameters_with_bounds(ety_env, env, tparams);
    let (e2, _cycles) = localize_and_add_where_constraints(ety_env, env, where_constraints);
    merge_errs(e1, e2)
}

/// [localize_and_add_ast_generic_parameters_and_where_constraints env ~ignore_errors tparams where_constraints]
/// adds the type parameters [tparams] to the environment, with localized bounds,
/// and also adds any consequences of `where` constraints.
///
/// {!ignore_errors} silences errors because those errors may have already fired
/// during another localization and/or are not appropriate at the time we call localize.
pub fn localize_and_add_ast_generic_parameters_and_where_constraints(
    env: &mut Env,
    ignore_errors: bool,
    tparams: &[nast::Tparam],
    where_constraints: &[aast::WhereConstraintHint],
) -> TyErr {
    let tparams: Vec<DeclTparam> = tparams
        .iter()
        .map(|t| decl_hint::aast_tparam_to_decl_tparam(&env.decl_env, t))
        .collect();
    let where_constraints: Vec<DeclWhereConstraint> = where_constraints
        .iter()
        .map(|aast::WhereConstraintHint(h1, ck, h2)| {
            // OCaml evaluates the components of the tuple from right to left.
            let ty2 = decl_hint::hint(&env.decl_env, h2);
            let ty1 = decl_hint::hint(&env.decl_env, h1);
            d::WhereConstraint(ty1, *ck, ty2)
        })
        .collect();
    let ety_env = if ignore_errors {
        empty_expand_env()
    } else {
        empty_expand_env_with_on_error(env::invalid_type_hint_assert_primary_pos_in_current_decl(env))
    };
    localize_and_add_generic_parameters_and_where_constraints(
        &ety_env,
        env,
        &tparams,
        &where_constraints,
    )
}

/// Add consequences of `where` constraints
pub fn localize_and_add_where_constraints(
    env: &mut Env,
    ignore_errors: bool,
    where_constraints: &[aast::WhereConstraintHint],
) -> TyErr {
    localize_and_add_ast_generic_parameters_and_where_constraints(
        env,
        ignore_errors,
        &[],
        where_constraints,
    )
}

fn ignore_cycles<A>((err, _cycles, res): (TyErr, Vec<CycleReporter>, A)) -> (TyErr, A) {
    (err, res)
}

fn ignore_cycles_((err, _cycles): (TyErr, Vec<CycleReporter>)) -> TyErr {
    err
}

/// Take a declaration phase type and use [ety_env] to transform it into a localized type.
///
/// - Desugar [Tmixed], [Toption] and [Tlike] types into unions.
///
/// - Transform [Tapply] to [Tclass] (for classish types), or [Tnewtype] (for opaque
///   type defs outside their defining file), else expand aliases or opaque
///   types within their defining file.
///
/// - Replace [Tthis] by [ety_env.this_ty].
///
/// - Replace [Tgeneric] by the type specified in [ety_env.substs], if present;
///   otherwise leave as generic.
///
/// - Expand [Taccess] type constant accesses through concrete classes.
///
/// Use this function to localize types outside the body of the method being
/// type-checked whose generic parameters and [this] type must be instantiated to
/// explicit types or fresh type variables. Use [localize_no_subst] instead for types
/// whose generic parameters and [this] type should be left as is.
///
/// The following errors are detected during localization:
///
/// - Bad type constant access e.g. [AbstractClass::T]
///
/// - Cyclic types
///
/// Errors are handled using [ety_env.on_error]. If you want to ignore errors
/// during localization, set this to [Diagnostics.ignore_error].
pub fn localize(ety_env: &ExpandEnv, env: &mut Env, ty: &DeclTy) -> (TyErr, Ty) {
    ignore_cycles(localize_rec(ety_env, env, ty))
}

pub fn localize_ft(
    instantiation: Option<MethodInstantiation>,
    ety_env: &ExpandEnv,
    def_pos: PosOrDecl,
    env: &mut Env,
    ft: &DeclFunType,
) -> (TyErr, FunType) {
    ignore_cycles(localize_ft_rec(instantiation, ety_env, def_pos, env, ft))
}

/// Declare and localize a single explicit type argument
pub fn localize_targ(
    tparam: Option<&DeclTparam>,
    check_type_integrity: bool,
    env: &mut Env,
    hint: &aast::Hint,
) -> (TyErr, tast::Targ) {
    ignore_cycles(localize_targ_rec(tparam, check_type_integrity, env, hint))
}

/// Add some [as] or [super] constraint to the environment.
/// Raise an error if any inconsistency is detected.
pub fn check_tparams_constraints(
    use_pos: Pos,
    ety_env: &ExpandEnv,
    env: &mut Env,
    tparams: &[DeclTparam],
) -> TyErr {
    ignore_cycles_(check_tparams_constraints_rec(use_pos, ety_env, env, tparams))
}

/// Add some [where] constraints to the environment.
/// Raise an error if any inconsistency is detected.
pub fn check_where_constraints(
    in_class: bool,
    use_pos: Pos,
    ety_env: &ExpandEnv,
    definition_pos: PosOrDecl,
    env: &mut Env,
    cstrl: &[DeclWhereConstraint],
) -> TyErr {
    ignore_cycles_(check_where_constraints_rec(
        in_class,
        use_pos,
        ety_env,
        definition_pos,
        env,
        cstrl,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(n: isize) -> Ty {
        mk((typing_reason::none(), Ty_::Tvar(n)))
    }

    fn tvar_of(ty: &Ty) -> isize {
        match get_node(ty) {
            Ty_::Tvar(n) => *n,
            _ => panic!("expected a type variable"),
        }
    }

    #[test]
    fn lru_drops_the_least_recently_used() {
        let mut lru = Lru::create(2);
        lru.add("a".to_string(), ty(1));
        lru.add("b".to_string(), ty(2));
        // `find` does not promote; `promote` does.
        assert_eq!(lru.find("a").map(|t| tvar_of(&t)), Some(1));
        lru.promote("a");
        lru.add("c".to_string(), ty(3));
        // `add` does not drop bindings.
        assert_eq!(lru.weight(), 3);
        lru.trim();
        assert_eq!(lru.weight(), 2);
        assert!(lru.find("b").is_none());
        assert_eq!(lru.find("a").map(|t| tvar_of(&t)), Some(1));
        // Replacing a binding makes it the most recently used.
        lru.add("a".to_string(), ty(4));
        lru.add("d".to_string(), ty(5));
        lru.trim();
        assert!(lru.find("c").is_none());
        assert_eq!(lru.find("a").map(|t| tvar_of(&t)), Some(4));
        assert_eq!(lru.find("d").map(|t| tvar_of(&t)), Some(5));
        // `clear` of the cache: resize to 0, trim, resize back.
        lru.resize(0);
        lru.trim();
        assert!(lru.is_empty());
    }

    #[test]
    fn map_env_ty_err_opt_error_order() {
        // Elements 0..=11: groups [0..4], [5..9], [10, 11]; the errors of a
        // group in order, the last group first.
        let xs: Vec<isize> = (0..12).collect();
        let mut env = ();
        let (errs, ys) = list_map_env_ty_err_opt(
            &mut env,
            &xs,
            |_, x| (if x % 2 == 0 { Some(*x) } else { None }, *x * 10),
            |errs| errs,
        );
        assert_eq!(ys, (0..12).map(|x| x * 10).collect::<Vec<_>>());
        assert_eq!(errs, vec![10, 6, 8, 0, 2, 4]);
        let (errs, ys) = list_map_env_ty_err_opt(&mut env, &[] as &[isize], |_, x| (Some(*x), *x), |e| e);
        assert!(errs.is_empty() && ys.is_empty());
        // Five elements: one group.
        let (errs, _) = list_map_env_ty_err_opt(&mut env, &[1, 2, 3, 4, 5], |_, x| (Some(*x), ()), |e| e);
        assert_eq!(errs, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn map_env_ty_err_opt_long_lists() {
        // After 1001 groups of five (and the 1002nd), the errors of the rest
        // of the elements come first, from the last to the first.
        let n = 5 * 1002 + 3;
        let xs: Vec<usize> = (0..n).collect();
        let mut env = ();
        let (errs, ys) = list_map_env_ty_err_opt(&mut env, &xs, |_, x| (Some(*x), *x), |e| e);
        assert_eq!(ys, xs);
        assert_eq!(&errs[..3], &[n - 1, n - 2, n - 3]);
        // then the groups from the last to the first
        assert_eq!(&errs[3..8], &[5 * 1001, 5 * 1001 + 1, 5 * 1001 + 2, 5 * 1001 + 3, 5 * 1001 + 4]);
        assert_eq!(&errs[errs.len() - 5..], &[0, 1, 2, 3, 4]);
    }

    #[test]
    fn list_map_env_err_cycles_puts_later_cycles_first() {
        let mut env = ();
        let (errs, cycles, res) = list_map_env_err_cycles(
            &mut env,
            &[1, 2, 3],
            |errs: Vec<isize>| errs,
            |_, x| (Some(*x), vec![*x, *x * 10], *x),
        );
        assert_eq!(errs, vec![1, 2, 3]);
        assert_eq!(cycles, vec![3, 30, 2, 20, 1, 10]);
        assert_eq!(res, vec![1, 2, 3]);
    }
}
