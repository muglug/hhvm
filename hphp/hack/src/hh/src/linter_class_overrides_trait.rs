// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_class_overrides_trait.ml`. See `hh/PORTING.md`.
//!
//! This linter warns if a class overrides all instance/static methods
//! and properties of a trait the class uses
//!
//! (linting is not fanout-aware, so it's safe to use non-dep-aware
//! functions here)

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use oxidized::aast;
use oxidized::ast_defs::ClassishKind;
use oxidized::pos::Pos;

use crate::ctx::Ctx;
use crate::decl_entry;
use crate::decl_provider;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_defs::ClassElt;

fn has_semantic_attribute(m: &tast::Method_) -> bool {
    m.user_attributes
        .0
        .iter()
        .any(|ua| !ua.name.1.starts_with("__"))
}

fn trait_name_from_hint(th: &aast::Hint_) -> Option<&str> {
    match th {
        aast::Hint_::Happly(tid, _) => Some(&tid.1),
        _ => None,
    }
}

/// collect the names of properties and methods of a Cls.t
fn names_and_origins_defined_by_cls_t(
    cls: &cls::T,
) -> (BTreeSet<String>, BTreeMap<String, String>) {
    // static properties in decls have a $ prefix, removing it
    fn remove_trailing_dollar(s: &str) -> String {
        match s.strip_prefix('$') {
            None => s.to_string(),
            Some(s) => s.to_string(),
        }
    }
    type Accessor = fn(&cls::T) -> Vec<(String, ClassElt)>;
    type Condition = fn(&(String, ClassElt)) -> bool;
    type Sanitize = fn(&(String, ClassElt)) -> String;
    let accessors: [(Accessor, Condition, Sanitize); 4] = [
        (
            cls::methods,
            |m| !crate::typing_defs::get_ce_abstract(&m.1),
            |m| m.0.clone(),
        ),
        (
            cls::smethods,
            |m| !crate::typing_defs::get_ce_abstract(&m.1),
            |m| m.0.clone(),
        ),
        (cls::props, |_| true, |p| p.0.clone()),
        (cls::sprops, |_| true, |p| remove_trailing_dollar(&p.0)),
    ];
    let mut names = BTreeSet::new();
    let mut origins = BTreeMap::new();
    for (accessor, condition, sanitize) in accessors {
        for el in accessor(cls) {
            if condition(&el) {
                let name = sanitize(&el);
                let element = &el.1;
                names.insert(name.clone());
                origins.insert(name, element.ce_origin.clone());
            }
        }
    }
    (names, origins)
}

/// collect the names of properties and methods of a class_
fn names_and_pos_defined_by_class_(
    class_: &tast::Class_,
) -> (BTreeSet<String>, BTreeMap<String, Pos>) {
    let mut names = BTreeSet::new();
    let mut pos = BTreeMap::new();
    for m in &class_.methods {
        names.insert(m.name.1.clone());
        pos.insert(m.name.1.clone(), m.name.0);
    }
    for cv in &class_.vars {
        names.insert(cv.id.1.clone());
        pos.insert(cv.id.1.clone(), cv.id.0);
    }
    (names, pos)
}

/// Does this [trait] implement any interfaces?
///
/// This looks for traits of the form:
///
///   trait X implements I {} // true
///
/// It does not include traits with requirements.
///
///   trait X { require implements I; } // false
fn trait_implements_interfaces(ctx: &Arc<Ctx>, trait_: &cls::T) -> bool {
    let is_interface = |name: &String| -> bool {
        match decl_provider::get_class(None, ctx, name) {
            decl_entry::T::Found(decl) => match cls::kind(&decl) {
                ClassishKind::Cinterface => true,
                _ => false,
            },
            // If we can't find this type (e.g. the user hasn't finished
            // writing it), conservatively assume it's an interface.
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => true,
        }
    };
    let interface_ancestors: Vec<String> = cls::all_ancestor_names(trait_)
        .into_iter()
        .filter(|n| is_interface(n))
        .collect();
    !interface_ancestors.is_empty()
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let (pos, bid) = (c.name.0, &c.name.1);
        let ctx = tast_env::get_ctx(env);

        let (base_names, base_pos_map) = names_and_pos_defined_by_class_(c);

        let used_trait_names: Vec<&str> = c
            .uses
            .iter()
            .filter_map(|u| trait_name_from_hint(&u.1))
            .collect();

        let required_classes: Vec<&str> = c
            .reqs
            .iter()
            .filter_map(|aast::ClassReq(u, k)| match k {
                aast::RequireKind::RequireClass => trait_name_from_hint(&u.1),
                aast::RequireKind::RequireThisAs
                | aast::RequireKind::RequireExtends
                | aast::RequireKind::RequireImplements => None,
            })
            .collect();

        // if the class or trait uses a trait that does not have require class constraints,
        // and does not implement an interface, then ensure that at least one method or
        // property of the trait is not overridden by the using class.
        for tid in used_trait_names {
            match decl_provider::get_class(None, &ctx, tid) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(t_cls) => {
                    let trait_names = names_and_origins_defined_by_cls_t(&t_cls).0;
                    if cls::all_ancestor_req_class_requirements(&t_cls).is_empty()
                        && !trait_names.is_empty()
                        && trait_names.is_subset(&base_names)
                        && !trait_implements_interfaces(&ctx, &t_cls)
                    {
                        crate::lints_diagnostics::class_overrides_all_trait_methods(
                            pos,
                            bid,
                            &cls::name(&t_cls),
                        )
                    }
                }
            }
        }
        // if the trait has a require class C constraint, ensure that the class C does
        // not override any property or method of the trait
        for cid in required_classes {
            match decl_provider::get_class(None, &ctx, cid) {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(c_cls) => {
                    let (class_names, origins) = names_and_origins_defined_by_cls_t(&c_cls);
                    for n in class_names.intersection(&base_names) {
                        let origin = origins.get(n).expect("Not_found");
                        let method_ = c.methods.iter().find(|m| *n == m.name.1);
                        let has_semantic_meaning = match method_ {
                            None => false,
                            Some(m) => m.abstract_ && has_semantic_attribute(m),
                        };
                        if origin != bid && !has_semantic_meaning {
                            crate::lints_diagnostics::trait_requires_class_that_overrides_method(
                                *base_pos_map.get(n).expect("Not_found"),
                                cid,
                                bid,
                                n,
                            )
                        }
                    }
                }
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
