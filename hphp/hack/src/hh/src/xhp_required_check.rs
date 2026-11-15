// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/xhp_required_check.ml`. See `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast;
use oxidized::message::Message;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs;
use crate::typing_defs_core::Ty;
use crate::typing_defs_core::Ty_;
use crate::typing_defs_core::get_node;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_reason as reason;
use crate::typing_utils;
use crate::utils;
use crate::xhp_attribute;

/// `S_set.t`
type SSet = BTreeSet<String>;

/// `S_map.t`
type SMap<V> = BTreeMap<String, V>;

/// `('a, 'b) xhp_attribute` of a TAST.
type XhpAttribute = aast::XhpAttribute<tast::Ty, tast::SavedEnv>;

/// `?(include_optional = false)`; `add` adds `(name, origin)` to `bag`.
pub fn collect_attrs_from_ty_sid<B>(
    include_optional: Option<bool>,
    env: &Env,
    add: impl Fn((String, String), B) -> B,
    bag: B,
    sid: &str,
) -> B {
    let include_optional = include_optional.unwrap_or(false);
    match tast_env::get_class(env, sid) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => bag,
        decl_entry::T::Found(c) => {
            let should_collect = |ce: &cls::ClassElt| match typing_defs::get_ce_xhp_attr(ce) {
                Some(xhp_attribute::T {
                    has_default: xa_has_default,
                    tag: None,
                }) if include_optional => xa_has_default,
                Some(xhp_attribute::T {
                    tag: Some(xhp_attribute::Tag::Required),
                    ..
                }) => true,
                _ => false,
            };
            let required_attrs = cls::props(&c)
                .into_iter()
                .filter(|(_, ce)| should_collect(ce));
            let mut s = bag;
            for (n, elt) in required_attrs {
                s = add((n, elt.ce_origin), s)
            }
            s
        }
    }
}

pub fn collect_attrs_from_ty(env: &Env, set: SSet, ty: &Ty) -> SSet {
    let ty = tast_env::expand_type(&mut env.clone(), ty.clone());
    let ty = tast_env::strip_dynamic(env, ty);
    match get_node(&ty) {
        // Collect attrs from each conjunct
        Ty_::Tintersection(tys) => {
            let mut set = set;
            for ty in tys {
                set = collect_attrs_from_ty(env, set, ty)
            }
            set
        }
        Ty_::Tunion(tys) => {
            // Filter out dynamic, as we conservatively assume that anything dynamic
            // has the appropriate required attrs
            let tys: Vec<&Ty> = tys
                .iter()
                .filter(|ty| !typing_utils::is_dynamic(env, ty))
                .collect();
            match tys.split_first() {
                None => set,
                Some((ty, tys)) => {
                    let collect = |ty: &Ty| collect_attrs_from_ty(env, SSet::new(), ty);
                    // `List.fold (List.map tys ~f:collect) ~init:(collect ty)
                    // ~f:S_set.inter`: OCaml evaluates the arguments from right
                    // to left, `collect ty` first.
                    let init = collect(ty);
                    let rest: Vec<SSet> = tys.iter().map(|ty| collect(ty)).collect();
                    rest.into_iter()
                        .fold(init, |acc, s| acc.intersection(&s).cloned().collect())
                }
            }
        }
        Ty_::Tclass((_, sid), _, _) => collect_attrs_from_ty_sid(
            Some(true),
            env,
            // `compose S_set.add fst`
            |(n, _), mut s: SSet| {
                s.insert(n);
                s
            },
            set,
            sid,
        ),
        _ => set,
    }
}

pub fn collect_attrs(env: &Env, attrs: &[XhpAttribute]) -> SSet {
    let collect_attr = |mut set: SSet, attr: &XhpAttribute| match attr {
        aast::XhpAttribute::XhpSimple(aast::XhpSimple { name: (_, n), .. }) => {
            set.insert(":".to_string() + n);
            set
        }
        aast::XhpAttribute::XhpSpread(aast::Expr(ty, _, _)) => collect_attrs_from_ty(env, set, ty),
    };
    attrs.iter().fold(SSet::new(), collect_attr)
}

pub fn check_attrs(pos: &Pos, env: &Env, sid: &str, attrs: &[XhpAttribute]) {
    let collect_with_ty = |bag: SMap<String>, sid: &str| {
        collect_attrs_from_ty_sid(
            None,
            env,
            |(n, c), mut m: SMap<String>| {
                m.insert(n, c);
                m
            },
            bag,
            sid,
        )
    };
    let required_attrs = collect_with_ty(SMap::new(), sid);
    let supplied_attrs = collect_attrs(env, attrs);
    let mut missing_attrs = required_attrs;
    for attr in &supplied_attrs {
        missing_attrs.remove(attr);
    }
    if missing_attrs.is_empty() {
    } else {
        for (attr, origin_sid) in missing_attrs {
            let attr_name = utils::strip_xhp_ns(&attr).to_string();
            let ty_reason_msg = {
                let env = env.clone();
                let attr_name = attr_name.clone();
                typing_error::Lazy::new(move || match tast_env::get_class(&env, &origin_sid) {
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
                    decl_entry::T::Found(ty) => {
                        let pos = match tast_env::get_prop(&env, &ty, &attr) {
                            Some(attr_decl) => (*attr_decl.ce_pos).clone(),
                            None => cls::pos(&ty),
                        };
                        reason::to_string(
                            &("The attribute `".to_string()
                                + &attr_name
                                + "` is declared here."),
                            &reason::witness_from_decl(pos),
                        )
                        .into_iter()
                        .map(|(pos, msg)| Message(pos, msg.into()))
                        .collect()
                    }
                })
            };
            typing_error_utils::add_typing_error(
                &typing_error::xhp(primary::xhp::T::MissingXhpRequiredAttr {
                    pos: pos.clone(),
                    attr: attr_name,
                    ty_reason_msg,
                }),
                env,
            )
        }
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        match e {
            aast::Expr(_, pos, aast::Expr_::Xml(xml)) => {
                let (sid, attrs, _) = &**xml;
                check_attrs(pos, env, &sid.1, attrs)
            }
            _ => {}
        }
    }
}

pub fn create_handler<'a>(_ctx: &Arc<Ctx>) -> Option<Box<dyn tast_visitor::Handler<'a> + 'a>> {
    let handler = Handler;
    Some(Box::new(handler))
}
