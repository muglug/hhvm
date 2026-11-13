// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! A memo of the shape and class types that are known to be subtypes of
//! `dynamic`. Not in the OCaml: it only saves work.
//!
//! `t <: dynamic` visits every type inside `t`. For the shape that a type
//! alias expands to, that is the whole (often very large) tree of the shapes
//! it mentions, and the question is asked again every time such a value is
//! passed to something that accepts `supportdyn<mixed>`. `Typing_phase`
//! caches the types of aliases, so the same shape is the same node each time
//! it is used in a file: the answer for a node is remembered. Closed class
//! types are shared the same way (the `localize_` memo), and `C<..> <:
//! dynamic` is asked about a million times on the benchmark sample, mostly
//! for nodes asked about before.
//!
//! What is remembered, and why the answer cannot change:
//!
//! - only a shape that has an alias as its origin and contains no type
//!   variable and no generic parameter, or a class type that contains no type
//!   variable, generic, dependent type or type access (`ty_flags`): nothing
//!   in the environment (bounds, solutions) is read to answer for it;
//! - only the answer "valid", found with no goal assumed (`visited` empty, no
//!   operation in the recursion tracker, no `this` type), so it does not
//!   hold only under an assumption, and only when finding it changed nothing
//!   in the environment (the handle is shared with a copy kept from before,
//!   so any write separates them) and added no diagnostic: skipping it later
//!   changes nothing. A failure is computed again each time, since it
//!   carries an error for where it is asked;
//! - per node (the entry keeps a weak reference to the node, so that its
//!   address is not reused while the entry exists; a strong one would make
//!   the code that takes a node apart in place, when it is the only owner,
//!   copy it instead),
//!   per value of the settings of the subtype query that a class or newtype
//!   inside the type may read;
//! - until the file or the module being checked changes, like the cache of
//!   `Typing_phase` (newtypes expand differently in the file that defines
//!   them), so that each file still looks up the classes involved itself;
//!   when dependency edges are recorded, until the definition being checked
//!   changes (`crate::rt::decl_epoch::Dependent`: a hit skips the lookups
//!   that record its edges); and until the declarations change (the daemon:
//!   [`forget_thread_memos`]).

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::hash::Hasher;
use std::rc::Rc;
use std::sync::Arc;

use relative_path::RelativePath;

use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs_core::ShapeType;
use crate::typing_defs_core::ShapeTypeSimple;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::TypeOrigin;
use crate::typing_defs_core::get_node;
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_reason::T as Reason;
use crate::typing_subtype::prelude::subtype_env;

/// More entries than any file needs; the memo is emptied when it is reached.
const MAX_ENTRIES: usize = 100_000;

struct Memo {
    /// The file (the handle of the environment's, compared by address
    /// first) and the module.
    context: (Arc<RelativePath>, Option<String>),
    /// See `crate::rt::decl_epoch::Dependent`.
    dependent: crate::rt::decl_epoch::Dependent,
    /// By [`key`].
    valid: HashMap<u64, std::rc::Weak<crate::typing_defs_core::TyNode>, BuildHasherDefault<KeyHasher>>,
}

/// The address of the node and the settings, in one word (the nodes are
/// aligned to 8 bytes at least).
fn key(ty: &Ty, settings: u16) -> u64 {
    ((Rc::as_ptr(&ty.1) as usize as u64) << 16) | settings as u64
}

/// FxHash's mixing step, for the one-word keys, with the high half folded
/// into the low one (the table picks buckets by the low bits, which a
/// multiplication alone leaves as they are in the key: here the settings).
#[derive(Default)]
struct KeyHasher(u64);

impl Hasher for KeyHasher {
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 32)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64)
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

thread_local! {
    static MEMO: RefCell<Option<Memo>> = const { RefCell::new(None) };
}

/// The settings of the query, as a key. `None`: do not use the memo for this
/// query (a goal is assumed, or the query is being logged).
fn settings(subtype_env: &subtype_env::T, this_ty: Option<&Ty>, env: &Env) -> Option<u16> {
    if !subtype_env.visited.is_empty()
        || !subtype_env.visited_internal.is_empty()
        || !crate::subtype_recursion_tracker::is_empty(&subtype_env.recursion_tracker)
        || this_ty.is_some()
        || crate::typing_log::should_log(env, "sub", 1)
    {
        return None;
    }
    let bits = [
        subtype_env.require_soundness,
        subtype_env.require_completeness,
        subtype_env.ignore_readonly,
        subtype_env.no_top_bottom,
        subtype_env.is_dynamic_aware,
        subtype_env.is_coeffect,
        subtype_env.ignore_likes,
        subtype_env.class_sub_classname,
        subtype_env.report_ambiguous_shape_splat,
        subtype_env.has_member_arg_posl.is_some(),
    ];
    Some(bits.iter().fold(0u16, |acc, &b| (acc << 1) | b as u16))
}

/// The types that the memo answers for, at first sight: see [`eligible`].
fn alias_shape_or_class(ty: &Ty) -> bool {
    matches!(
        get_node(ty),
        Ty_::Tshape(ShapeType::ShapeSimple(ShapeTypeSimple {
            origin: TypeOrigin::FromAlias(..),
            ..
        })) | Ty_::Tclass(..)
    )
}

/// An alias shape without type variable or generic, a class type without
/// type variable, generic, dependent type or type access.
fn eligible(ty: &Ty) -> bool {
    use crate::typing_defs_core::ty_flags;
    match get_node(ty) {
        Ty_::Tclass(..) => !ty.may_have(ty_flags::ALL),
        _ => is_closed(ty),
    }
}

fn with_memo<A>(env: &Env, f: impl FnOnce(&mut Memo) -> A) -> A {
    MEMO.with_borrow_mut(|memo| {
        // The context of the memo, compared in place (`env::get_file env`,
        // `env::get_current_module env`), and copied only when it changes.
        let file: &Arc<RelativePath> = &env.genv.file;
        let module: Option<&str> = env.genv.current_module.as_ref().map(|id| id.1.as_str());
        match memo {
            Some(m)
                if (Arc::ptr_eq(&m.context.0, file) || *m.context.0 == **file)
                    && m.context.1.as_deref() == module
                    && m.dependent.is_for(env) =>
            {
                if !Arc::ptr_eq(&m.context.0, file) {
                    m.context.0 = Arc::clone(file);
                }
            }
            _ => {
                *memo = Some(Memo {
                    context: (Arc::clone(file), env::get_current_module(env)),
                    dependent: crate::rt::decl_epoch::Dependent::of_env(env),
                    valid: HashMap::default(),
                })
            }
        }
        f(memo.as_mut().unwrap())
    })
}

/// Forget the memo (see `crate::rt::decl_epoch`).
pub(crate) fn forget_thread_memos() {
    MEMO.with_borrow_mut(|memo| *memo = None)
}

/// What the memo knows of `ty <: dynamic` for this query.
pub(crate) enum Query {
    /// Not a query the memo answers.
    No,
    /// Found valid before.
    Valid,
    /// Not known: [`Recorder::record`] the answer once it is computed.
    Unknown(Recorder),
}

/// What [`Recorder::record`] checks: the settings, the environment and the
/// count of diagnostics before the answer was computed.
pub(crate) struct Recorder {
    settings: u16,
    env_before: Env,
    diagnostics_before: u64,
}

pub(crate) fn query(
    subtype_env: &subtype_env::T,
    this_ty: Option<&Ty>,
    env: &Env,
    ty: &Ty,
) -> Query {
    if !alias_shape_or_class(ty) || crate::rt::decl_epoch::no_memos() {
        return Query::No;
    }
    let Some(settings) = settings(subtype_env, this_ty, env) else {
        return Query::No;
    };
    if with_memo(env, |memo| memo.valid.contains_key(&key(ty, settings))) {
        Query::Valid
    } else {
        Query::Unknown(Recorder {
            settings,
            env_before: env.clone(),
            diagnostics_before: crate::diagnostics_state::added_count(),
        })
    }
}

impl Recorder {
    /// `prop` is the answer for `ty <: dynamic`, computed in `env` since the
    /// [`query`] that gave this recorder.
    pub(crate) fn record(self, env: &Env, ty: &Ty, prop: &crate::typing_logic::SubtypeProp) {
        if crate::typing_logic::is_valid(prop)
            && Env::ptr_eq(&self.env_before, env)
            && crate::diagnostics_state::added_count() == self.diagnostics_before
            && eligible(ty)
        {
            with_memo(env, |memo| {
                if memo.valid.len() >= MAX_ENTRIES {
                    memo.valid.clear();
                }
                memo.valid.insert(key(ty, self.settings), Rc::downgrade(&ty.1));
            })
        }
    }
}

/// No type variable and no generic parameter anywhere in `ty`.
fn is_closed(ty: &Ty) -> bool {
    struct Closed;
    impl LoclTypeVisitor<bool> for Closed {
        /// Stops at the first type variable or generic: `false` is the
        /// answer from there on.
        fn on_type(&mut self, acc: bool, ty: &Ty) -> bool {
            use crate::typing_defs_core::ty_flags;
            // (Not visited when the flags of the type tell that neither
            // occurs in it.)
            acc && (!ty.may_have(ty_flags::TVAR | ty_flags::TGENERIC)
                || crate::typing_utils::locl_type_visitor_on_type(self, acc, ty))
        }
        fn on_tvar(&mut self, _acc: bool, _r: &Reason, _id: isize) -> bool {
            false
        }
        fn on_tgeneric(&mut self, _acc: bool, _r: &Reason, _name: &str) -> bool {
            false
        }
    }
    Closed.on_type(true, ty)
}
