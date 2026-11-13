// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `trait_reuse_check.ml`. See `hh/PORTING.md`.
//!
//! Ban reuse of traits that have final methods.
//!
//! The lazy traces of the errors keep a copy of the environment (cheap: its
//! collections are persistent), as the OCaml closures keep `env`.

use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::ancestor_route;
use crate::ast_defs;
use crate::decl_entry;
use crate::decl_utils;
use crate::folded_class as cls;
use crate::typing_defs::ClassElt;
use crate::typing_defs::get_ce_final;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::Lazy;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::utils;

fn strip_ns(s: &str) -> &str {
    utils::strip_ns(s)
}

fn get_class(env: &Env, name: &str) -> decl_entry::T<cls::T> {
    typing_env::get_class(env, name)
}

fn is_class(env: &Env, name: &str) -> bool {
    match get_class(env, name) {
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => false,
        decl_entry::T::Found(c) => ast_defs::is_c_class(cls::kind(&c)),
    }
}

/// Return the position where class/trait [type_name] is defined.
fn classish_def_pos(env: &Env, type_name: &str) -> PosOrDecl {
    let decl = get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => cls::pos(&decl),
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => PosOrDecl::NONE,
    }
}

/// The final methods in [type_name] (excluding inherited methods),
/// both instance and static methods.
fn final_methods(env: &Env, type_name: &str) -> Vec<(String, ClassElt)> {
    let decl = get_class(env, type_name);
    match decl {
        decl_entry::T::Found(decl) => {
            let mut methods = cls::methods(&decl);
            methods.extend(cls::smethods(&decl));
            methods
                .into_iter()
                .filter(|(_, m)| m.ce_origin == type_name && get_ce_final(m))
                .collect()
        }
        decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => vec![],
    }
}

/// Return a list of positions explaining why a final method is reused.
fn relevant_positions(
    env: &Env,
    class_name: &str,
    first_using_parent_or_trait_name: &str,
    second_using_trait_name: &str,
    reused_trait: &str,
) -> (String, Vec<(PosOrDecl, String)>) {
    let route = ancestor_route::find_route(env, first_using_parent_or_trait_name, reused_trait);
    let using_cls_name = match route.iter().rev().find(|c| is_class(env, c)) {
        None => class_name.to_string(),
        Some(c) => c.clone(),
    };
    let mut result = if second_using_trait_name == reused_trait {
        vec![]
    } else {
        ancestor_route::describe_route(env, second_using_trait_name, reused_trait)
    };

    // Show the position of the ancestor class that also uses this trait.
    result.push((
        classish_def_pos(env, &using_cls_name),
        format!("`{}` is defined here", strip_ns(&using_cls_name)),
    ));

    // Since traits can use multiple other traits, show the full trait
    // path so users can see how the trait reuse occurred.
    result.extend(ancestor_route::describe_route(
        env,
        &using_cls_name,
        reused_trait,
    ));

    // Finally, show the final method in the trait.
    let (meth_name, meth) = match final_methods(env, reused_trait).into_iter().next() {
        Some(m) => m,
        None => panic!("List.hd_exn"),
    };
    result.push((
        (*meth.ce_pos).clone(),
        format!(
            "`{}` has a final method `{}`",
            strip_ns(reused_trait),
            meth_name
        ),
    ));
    (using_cls_name, result)
}

fn to_messages(l: &[(PosOrDecl, String)]) -> Vec<Message<PosOrDecl>> {
    l.iter()
        .map(|(p, s)| Message(p.clone(), s.as_str().into()))
        .collect()
}

pub fn trait_reuse_with_final_method_error(
    env: &Env,
    class_elt: &ClassElt,
    class_name: String,
    first_using_parent_or_trait: &cls::T,
    (second_using_trait_pos, second_using_trait): (Pos, &cls::T),
) -> typing_error::T {
    let trait_name = class_elt.ce_origin.clone();
    let first_using_parent_or_trait_name = cls::name(first_using_parent_or_trait);
    let second_using_trait_name = cls::name(second_using_trait);
    let trace = {
        let env = env.clone();
        let trait_name = trait_name.clone();
        Lazy::new(move || {
            relevant_positions(
                &env,
                &class_name,
                &first_using_parent_or_trait_name,
                &second_using_trait_name,
                &trait_name,
            )
        })
    };
    typing_error::primary(primary::T::Trait_reuse_with_final_method {
        pos: second_using_trait_pos,
        trait_name,
        parent_cls_name: trace.map(|(name, _)| name.clone()),
        trace: trace.map(|(_, trace)| to_messages(trace)),
    })
}

pub fn method_import_via_diamond_error(
    env: &Env,
    (class_name_pos, class_name): (Pos, String),
    (method_name, class_elt): (String, &ClassElt),
    first_using_trait: &cls::T,
    second_using_trait: &cls::T,
) -> typing_error::T {
    let trait_name = class_elt.ce_origin.clone();
    // The fields of the record, from the last to the first.
    let trace2 = {
        let env = env.clone();
        let class_name = class_name.clone();
        let trait_name = trait_name.clone();
        let via = cls::name(first_using_trait);
        Lazy::new(move || {
            to_messages(&ancestor_route::describe_route_via(
                &env,
                &class_name,
                &trait_name,
                &via,
            ))
        })
    };
    let trace1 = {
        let env = env.clone();
        let class_name = class_name.clone();
        let trait_name = trait_name.clone();
        let via = cls::name(second_using_trait);
        Lazy::new(move || {
            to_messages(&ancestor_route::describe_route_via(
                &env,
                &class_name,
                &trait_name,
                &via,
            ))
        })
    };
    let method_pos = (*class_elt.ce_pos).clone();
    typing_error::primary(primary::T::Method_import_via_diamond {
        pos: class_name_pos,
        class_name,
        method_pos,
        method_name,
        trace1,
        trace2,
    })
}

pub fn property_import_via_diamond_error(
    generic: bool,
    env: &Env,
    (class_name_pos, class_name): (Pos, String),
    (property_name, class_elt): (String, &ClassElt),
    first_using_trait: &cls::T,
    second_using_trait: &cls::T,
) {
    let trait_name = class_elt.ce_origin.clone();
    // The fields of the record, from the last to the first.
    let trace2 = {
        let env = env.clone();
        let class_name = class_name.clone();
        let trait_name = trait_name.clone();
        let via = cls::name(first_using_trait);
        Lazy::new(move || {
            to_messages(&ancestor_route::describe_route_via(
                &env,
                &class_name,
                &trait_name,
                &via,
            ))
        })
    };
    let trace1 = {
        let env = env.clone();
        let class_name = class_name.clone();
        let trait_name = trait_name.clone();
        let via = cls::name(second_using_trait);
        Lazy::new(move || {
            to_messages(&ancestor_route::describe_route_via(
                &env,
                &class_name,
                &trait_name,
                &via,
            ))
        })
    };
    // `Typing_defs.get_pos (Lazy.force class_elt.ce_type)`
    let property_pos = PosOrDecl::from(decl_utils::get_pos(&class_elt.ce_type));
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::Property_import_via_diamond {
            generic,
            pos: class_name_pos,
            class_name,
            property_pos,
            property_name,
            trace1,
            trace2,
        }),
        env,
    )
}
