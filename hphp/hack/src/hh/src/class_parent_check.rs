// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/class_parent_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::aast::RequireKind;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast_check_error::NastCheckError;
use oxidized::nast_check_error::Verb;

use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics;
use crate::folded_class as cls;
use crate::pos_or_decl;
use crate::rt::ocaml_hashtbl;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error_utils;
use crate::typing_warning;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    let diagnostic = crate::naming_phase_error::to_user_diagnostic(NamingPhaseError::NastCheck(err));
    diagnostics::add_diagnostic(diagnostic);
}

pub fn check_is_class(
    env: &tast_env::Env,
    require_constraint_check: Option<RequireKind>,
    hint: &aast::Hint,
) {
    let aast::Hint(p, h) = hint;
    let (is_req_class_check, is_req_this_as_check) = match require_constraint_check {
        Some(RequireKind::RequireClass) => (true, false),
        Some(RequireKind::RequireThisAs) => (false, true),
        _ => (false, false),
    };
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => match tast_env::get_class(env, name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) => {
                let kind = cls::kind(&cls);
                let name = cls::name(&cls);
                let is_interface = ast_defs::is_c_interface(cls::kind(&cls));
                if ast_defs::is_c_class(kind) {
                    if cls::final_(&cls) && !is_req_class_check {
                        add_nast_check_error(NastCheckError::RequiresFinalClass {
                            pos: p.clone(),
                            name,
                            is_req_this_as_check,
                        })
                    } else if cls::final_(&cls) && is_req_this_as_check {
                        add_nast_check_error(NastCheckError::RequiresFinalClass {
                            pos: p.clone(),
                            name,
                            is_req_this_as_check,
                        })
                    }
                } else {
                    add_nast_check_error(NastCheckError::RequiresNonClass {
                        pos: p.clone(),
                        name,
                        kind: ast_defs::string_of_classish_kind(kind),
                        is_interface,
                        is_req_this_as_check,
                    })
                }
            }
        },
        aast::Hint_::Habstr(name) => add_nast_check_error(NastCheckError::RequiresNonClass {
            pos: p.clone(),
            name: name.clone(),
            kind: "a generic".to_string(),
            is_interface: false,
            is_req_this_as_check,
        }),
        _ => add_nast_check_error(NastCheckError::RequiresNonClass {
            pos: p.clone(),
            name: "This".to_string(),
            kind: "an invalid type hint".to_string(),
            is_interface: false,
            is_req_this_as_check,
        }),
    }
}

pub fn check_is_interface((env, error_verb): (&tast_env::Env, Verb), hint: &aast::Hint) {
    let aast::Hint(p, h) = hint;
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => match tast_env::get_class(env, name) {
            decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
            decl_entry::T::Found(cls) if ast_defs::is_c_interface(cls::kind(&cls)) => {}
            decl_entry::T::Found(cls) => add_nast_check_error(NastCheckError::NonInterface {
                pos: p.clone(),
                name: cls::name(&cls),
                verb: error_verb,
            }),
        },
        aast::Hint_::Habstr(_) => add_nast_check_error(NastCheckError::NonInterface {
            pos: p.clone(),
            name: "generic".to_string(),
            verb: error_verb,
        }),
        _ => add_nast_check_error(NastCheckError::NonInterface {
            pos: p.clone(),
            name: "invalid type hint".to_string(),
            verb: error_verb,
        }),
    }
}

pub fn check_is_trait(env: &tast_env::Env, hint: &aast::Hint) {
    let aast::Hint(p, h) = hint;
    match &**h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => {
            let type_info = tast_env::get_class(env, name);
            match type_info {
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                decl_entry::T::Found(cls) if ast_defs::is_c_trait(cls::kind(&cls)) => {}
                decl_entry::T::Found(cls) => {
                    let name = cls::name(&cls);
                    let kind = cls::kind(&cls);
                    add_nast_check_error(NastCheckError::UsesNonTrait {
                        pos: p.clone(),
                        name,
                        kind: ast_defs::string_of_classish_kind(kind),
                    })
                }
            }
        }
        _ => panic!("assertion failure: trait isn't an Happly"),
    }
}

pub fn hint_happly_to_string(h: &aast::Hint_) -> Option<String> {
    match h {
        aast::Hint_::Happly(ast_defs::Id(_, name), _) => Some(name.clone()),
        _ => None,
    }
}

pub fn duplicated_used_traits(env: &Env, c: &tast::Class_) {
    let mut traits = ocaml_hashtbl::StringMultiTable::create();
    for aast::Hint(p, h) in &c.uses {
        match hint_happly_to_string(h) {
            Some(s) => traits.add_multi(s, p.clone()),
            None => {}
        }
    }
    traits.iteri(|key, data| {
        if data.len() > 1 {
            let ast_defs::Id(pos, class_name) = &c.name;
            typing_error_utils::add_typing_error(
                &typing_error::primary(typing_error::primary::T::TraitReuseInsideClass {
                    class_name: class_name.clone(),
                    pos: pos.clone(),
                    trait_name: key.to_string(),
                    // `List.rev_map data ~f:Pos_or_decl.of_raw_pos`
                    occurrences: data
                        .iter()
                        .rev()
                        .map(|p| pos_or_decl::of_raw_pos(p.clone()))
                        .collect(),
                }),
                env,
            )
        }
    })
}

pub fn check_redundant_require_this_as(
    env: &tast_env::Env,
    c: &tast::Class_,
    req_this_as: &[&aast::Hint],
) {
    // Only check for traits
    if !ast_defs::is_c_trait(c.kind) {
    } else {
        let ast_defs::Id(_, trait_name) = &c.name;
        for aast::Hint(p, h) in req_this_as.iter().copied() {
            match &**h {
                aast::Hint_::Happly(ast_defs::Id(_, class_name), _) => {
                    match tast_env::get_class(env, class_name) {
                        decl_entry::T::Found(cls) => {
                            // Check if the class uses this trait (directly or transitively)
                            if !cls::has_ancestor(&cls, trait_name) {
                                // Class does not use the trait, emit warning
                                tast_env::add_warning(
                                    env,
                                    (
                                        p.clone(),
                                        typing_warning::Kind::REDUNDANT_REQUIRE_THIS_AS,
                                        typing_warning::redundant_require_this_as::T {
                                            trait_name: trait_name.clone(),
                                            class_name: class_name.clone(),
                                        },
                                    ),
                                )
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
    }
}

/// The object `handler`.
struct ClassParentCheck;

impl<'a> tast_visitor::Handler<'a> for ClassParentCheck {
    fn at_class_(&mut self, env: &tast_env::Env, c: &'a tast::Class_) {
        let (req_extends, req_implements, req_class, req_this_as) = crate::aast::split_reqs(&c.reqs);
        for h in &c.uses {
            check_is_trait(env, h)
        }
        duplicated_used_traits(env, c);
        for h in req_extends {
            check_is_class(env, None, h)
        }
        for h in &c.implements {
            check_is_interface((env, Verb::Vimplement), h)
        }
        for h in req_implements {
            check_is_interface((env, Verb::VreqImplement), h)
        }
        for h in req_class {
            check_is_class(env, Some(RequireKind::RequireClass), h)
        }
        for h in req_this_as.iter().copied() {
            check_is_class(env, Some(RequireKind::RequireThisAs), h)
        }
        // Check for redundant require this as
        check_redundant_require_this_as(env, c, &req_this_as)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(ClassParentCheck)
}

