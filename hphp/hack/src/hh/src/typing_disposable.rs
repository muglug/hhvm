// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_disposable.ml`. See `hh/PORTING.md`.
//!
//! Typing code concerned with disposable types.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::ast_defs::Id;

use crate::ast_defs;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::type_visitor::LoclTypeVisitor;
use crate::typing_defs_core::Exact;
use crate::typing_defs_core::PosId;
use crate::typing_defs_core::Ty;
/// `module Env = Typing_env`
use crate::typing_env as env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_reason::T as Reason;
use crate::typing_utils;
use crate::utils;

pub fn is_disposable_class(env: &Env, cls: &cls::T) -> bool {
    let name = cls::name(cls);
    name == sn::classes::IDISPOSABLE
        || name == sn::classes::IASYNC_DISPOSABLE
        || typing_utils::has_ancestor_including_req(env, cls, sn::classes::IDISPOSABLE)
        || typing_utils::has_ancestor_including_req(env, cls, sn::classes::IASYNC_DISPOSABLE)
}

/// The object `is_disposable_visitor env`.
pub struct IsDisposableVisitor<'a> {
    env: &'a Env,
    /// Whether the answers are kept (see [`node_memo`]): when the lookups of
    /// classes record no dependency edge.
    memo: bool,
}

/// Not in the OCaml, which visits every node of the type again at each
/// call. The visit of a node gives `Some name` of the last disposable class
/// it meets in it, whatever the accumulator it is given, and the
/// accumulator otherwise (`on_tclass` drops the accumulator for a disposable
/// class and folds it through the type arguments otherwise; every other
/// method folds it through the children). So `on_type acc ty` is
/// `(on_type None ty) or acc`, and `on_type None ty` depends only on the
/// node (immutable) and on the classes of the decl store. Types share their
/// nodes (shapes and unions localized from the same type alias): the
/// answers for those nodes are kept per thread, with the node (so that its
/// address is not reused), for as long as the classes are.
mod node_memo {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;

    const SIZE: usize = 1024;

    struct Memo {
        generation: u64,
        entries: Vec<Option<(Ty, Option<String>)>>,
    }

    thread_local! {
        static MEMO: RefCell<Memo> = RefCell::new(Memo { generation: u64::MAX, entries: vec![] });
    }

    fn slot(ty: &Ty) -> usize {
        let p = Rc::as_ptr(&ty.1) as *const u8 as usize;
        (p >> 4 ^ p >> 16) & (SIZE - 1)
    }

    pub fn get(env: &Env, ty: &Ty) -> Option<Option<String>> {
        let generation = crate::decl_provider::class_cache_generation(&env.decl_env.ctx);
        MEMO.with_borrow_mut(|m| {
            if m.generation != generation {
                m.generation = generation;
                m.entries.clear();
                m.entries.resize(SIZE, None);
                return None;
            }
            match &m.entries[slot(ty)] {
                Some((node, res)) if Rc::ptr_eq(&node.1, &ty.1) => Some(res.clone()),
                _ => None,
            }
        })
    }

    /// Forget the answers (see `crate::rt::decl_epoch`; the generation of
    /// the class cache changes then too).
    pub fn forget() {
        MEMO.with_borrow_mut(|m| {
            m.generation = u64::MAX;
            m.entries = vec![];
        })
    }

    /// After [`get`] (which set the generation).
    pub fn set(ty: &Ty, res: &Option<String>) {
        MEMO.with_borrow_mut(|m| m.entries[slot(ty)] = Some((ty.clone(), res.clone())))
    }
}

impl LoclTypeVisitor<Option<String>> for IsDisposableVisitor<'_> {
    fn on_type(&mut self, acc: Option<String>, ty: &Ty) -> Option<String> {
        use crate::typing_defs_core::Ty_;
        let memoised = self.memo
            && matches!(
                crate::typing_defs_core::get_node(ty),
                Ty_::Tshape(_) | Ty_::Tunion(_) | Ty_::Tintersection(_) | Ty_::Ttuple(_)
            );
        if !memoised {
            return self.on_type_default(acc, ty);
        }
        // See [`node_memo`].
        let res = match node_memo::get(self.env, ty) {
            Some(res) => res,
            None => {
                let res = self.on_type_default(None, ty);
                node_memo::set(ty, &res);
                res
            }
        };
        res.or(acc)
    }

    // Only bother looking at classish types. Other types can spuriously
    // claim to implement these interfaces. Ideally we should check
    // constrained generics, abstract types, etc.
    fn on_tclass(
        &mut self,
        acc: Option<String>,
        _r: &Reason,
        (_, class_name): &PosId,
        _exact: &Exact,
        tyl: &[Ty],
    ) -> Option<String> {
        let default = |this: &mut Self, acc| tyl.iter().fold(acc, |acc, ty| this.on_type(acc, ty));
        // Not in the OCaml: the answer for a class that exists is kept per
        // thread (`Decl_provider.disposable_class_memo`), unless the lookups
        // of `get_class` record dependency edges.
        if self.memo {
            let env = self.env;
            let memo = crate::decl_provider::disposable_class_memo(
                &env.decl_env.ctx,
                class_name,
                || match env::get_class(env, class_name) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
                    decl_entry::T::Found(c) => Some(is_disposable_class(env, &c)),
                },
            );
            return match memo {
                Some(true) => Some(utils::strip_ns(class_name).to_string()),
                Some(false) | None => default(self, acc),
            };
        }
        match env::get_class(self.env, class_name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => default(self, acc),
            decl_entry::T::Found(c) => {
                if is_disposable_class(self.env, &c) {
                    Some(utils::strip_ns(class_name).to_string())
                } else {
                    default(self, acc)
                }
            }
        }
    }
}

impl IsDisposableVisitor<'_> {
    /// The `on_type` of `locl_type_visitor` (which [`LoclTypeVisitor::on_type`]
    /// overrides here).
    fn on_type_default(&mut self, acc: Option<String>, ty: &Ty) -> Option<String> {
        use crate::typing_defs_core::Ty_;
        let r = crate::typing_defs_core::get_reason(ty);
        match crate::typing_defs_core::get_node(ty) {
            Ty_::Tany(_) => self.on_tany(acc, r),
            Ty_::Tnonnull => self.on_tnonnull(acc, r),
            Ty_::Tdynamic(_) => self.on_tdynamic(acc, r),
            Ty_::Toption(ty) => self.on_toption(acc, r, ty),
            Ty_::Tprim(prim) => self.on_tprim(acc, r, *prim),
            Ty_::Tvar(id) => self.on_tvar(acc, r, *id),
            Ty_::Tfun(fty) => self.on_tfun(acc, r, fty),
            Ty_::Tgeneric(x) => self.on_tgeneric(acc, r, x),
            Ty_::Tnewtype(x, tyl, ty) => self.on_tnewtype(acc, r, x, tyl, ty),
            Ty_::Tdependent(x, ty) => self.on_tdependent(acc, r, x, ty),
            Ty_::Ttuple(t) => self.on_ttuple(acc, r, t),
            Ty_::Tunion(tyl) => self.on_tunion(acc, r, tyl),
            Ty_::Tintersection(tyl) => self.on_tintersection(acc, r, tyl),
            Ty_::Tshape(s) => self.on_tshape(acc, r, s),
            Ty_::Tclass(cls, exact, tyl) => self.on_tclass(acc, r, cls, exact, tyl),
            Ty_::TvecOrDict(ty1, ty2) => self.on_tvec_or_dict(acc, r, ty1, ty2),
            Ty_::Taccess(ta) => self.on_taccess(acc, r, ta),
            Ty_::Tneg(tneg) => self.on_neg_type(acc, r, tneg),
            Ty_::Tlabel(name) => self.on_tlabel(acc, r, name),
            Ty_::TclassPtr(ty) => self.on_tclass_ptr(acc, r, ty),
        }
    }
}

/// Not in the OCaml: forget the memo of the visitor (see
/// `crate::rt::decl_epoch`; the memo of the classes is in
/// `crate::decl_provider`'s cache, forgotten with it).
pub fn forget_thread_memos() {
    node_memo::forget()
}

pub fn is_disposable_visitor(env: &Env) -> IsDisposableVisitor<'_> {
    IsDisposableVisitor {
        env,
        memo: !env::deps::records_dependency_edges(env) && !crate::rt::decl_epoch::no_memos(),
    }
}

/// Does ty (or a type embedded in ty) implement IDisposable
/// or IAsyncDisposable, directly or indirectly?
/// Return Some class_name if it does, None if it doesn't.
pub fn is_disposable_type(env: &Env, ty: &Ty) -> Option<String> {
    // `match Env.expand_type env ty with (_env, ety) -> ...`: the expanded type
    // is visited with the environment it was expanded in, not the new one.
    let ety = env::expand_type(&mut env.clone(), ty.clone());
    is_disposable_visitor(env).on_type(None, &ety)
}

pub fn enforce_is_disposable(env: &Env, hint: &aast::Hint) {
    match hint {
        aast::Hint(_, h) => match &**h {
            aast::Hint_::Happly(Id(p, c), _) => match env::get_class(env, c) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(c) => {
                    if !(is_disposable_class(env, &c) || ast_defs::is_c_interface(cls::kind(&c))) {
                        typing_error_utils::add_typing_error(
                            &typing_error::primary(
                                typing_error::primary::T::Must_extend_disposable(p.clone()),
                            ),
                            env,
                        )
                    }
                }
            },
            _ => {}
        },
    }
}
