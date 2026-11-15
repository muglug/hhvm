// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/class_inherited_member_case_check.ml`.
//! See `hh/PORTING.md`.

use std::collections::BTreeMap;

use oxidized::aast;
use oxidized::ast_defs;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_defs::ClassElt;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;

pub fn error_inherited_base(
    env: &Env,
    member_type: &str,
    base_name: &str,
    parent_name: &str,
    base_elt: &ClassElt,
    parent_elt: &ClassElt,
) {
    // The fields of the record are evaluated from right to left: the
    // position of `parent_elt` is forced first.
    let prev_class_pos = (*parent_elt.ce_pos).clone();
    let pos = pos_or_decl::unsafe_to_raw_pos((*base_elt.ce_pos).clone());
    typing_error_utils::add_typing_error(
        &typing_error::primary(
            typing_error::primary::T::InheritedClassMemberWithDifferentCase {
                member_type: member_type.to_string(),
                name: base_name.to_string(),
                name_prev: parent_name.to_string(),
                pos,
                child_class: base_elt.ce_origin.clone(),
                prev_class: parent_elt.ce_origin.clone(),
                prev_class_pos,
            },
        ),
        env,
    )
}

pub fn check_inheritance_case(
    env: &Env,
    member_type: &str,
    class_id: &aast::Sid,
    (name, elt): &(String, ClassElt),
    mut acc: BTreeMap<String, (String, ClassElt)>,
) -> BTreeMap<String, (String, ClassElt)> {
    let ast_defs::Id(p, cls_name) = class_id;
    let canonical_name = name.to_ascii_lowercase();
    match acc.get(&canonical_name) {
        Some((prev_name, prev_elt)) if name != prev_name => {
            match (&elt.ce_origin, &prev_elt.ce_origin) {
                // If they are from the same class, there's already a parsing error
                (a, b) if a == b => {}
                // new is the current class
                (base_cls, _) if cls_name == base_cls => {
                    error_inherited_base(env, member_type, name, prev_name, elt, prev_elt)
                }
                // prev is the current class
                (_, base_cls) if cls_name == base_cls => {
                    error_inherited_base(env, member_type, prev_name, name, prev_elt, elt)
                }
                // Otherwise, this class inherited two methods that differ only by case
                (class1, class2) => {
                    // The fields of the record are evaluated from right to
                    // left: the position of `prev_elt` is forced first.
                    let class2_pos = (*prev_elt.ce_pos).clone();
                    let class1_pos = (*elt.ce_pos).clone();
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(
                            typing_error::primary::T::MultipleInheritedClassMemberWithDifferentCase {
                                member_type: member_type.to_string(),
                                name1: name.clone(),
                                name2: prev_name.clone(),
                                class1_name: class1.clone(),
                                class2_name: class2.clone(),
                                child_class_name: cls_name.clone(),
                                pos: p.clone(),
                                class1_pos,
                                class2_pos,
                            },
                        ),
                        env,
                    )
                }
            }
        }
        _ => {}
    }
    acc.insert(canonical_name, (name.clone(), elt.clone()));
    acc
}

pub fn check_inheritance_cases(
    env: &Env,
    member_type: &str,
    name: &aast::Sid,
    class_elts: &[(String, ClassElt)],
) {
    // We keep a map of canonical names for each class element
    // and iterate through the list. If we ever see two members with
    // the same canonical name, we raise an error.
    //
    // `List.fold_right`: from the last element to the first.
    let _: BTreeMap<String, (String, ClassElt)> =
        class_elts.iter().rev().fold(BTreeMap::new(), |acc, elt| {
            check_inheritance_case(env, member_type, name, elt, acc)
        });
}

/// The object `handler`.
struct ClassInheritedMemberCaseCheck;

impl<'a> tast_visitor::Handler<'a> for ClassInheritedMemberCaseCheck {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        // Check if any methods, including inherited ones, interfere via canonical name
        let ast_defs::Id(_, cls_name) = &c.name;
        let result = tast_env::get_class(env, cls_name);
        match result {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => {
                let methods = cls::methods(&cls);
                let smethods = cls::smethods(&cls);
                let mut all_methods = methods;
                all_methods.extend(smethods);
                // All methods are treated the same when it comes to inheritance
                // Member type may be useful for properties, constants, etc later
                check_inheritance_cases(env, "method", &c.name, &all_methods)
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassInheritedMemberCaseCheck)
}
