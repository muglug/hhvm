// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing_needs_concrete.ml`. See `hh/PORTING.md`.
//!
//! The polymorphic variant ``[ `Id | `Static | `Self | `Parent ]`` given to
//! `add_call_needs_concrete` is `typing_warning::call_needs_concrete::Via`;
//! the error takes the same tags as `primary::CallNeedsConcreteVia`.

use std::cell::LazyCell;

use oxidized::aast;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::naming_attributes;
use crate::naming_special_names as sn;
use crate::typing_defs::ClassElt;
use crate::typing_defs::ConsistentKind;
use crate::typing_defs::get_ce_abstract;
use crate::typing_defs::get_ce_readonly_prop_or_needs_concrete;
use crate::typing_env;
use crate::typing_env_types::Env;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;
use crate::typing_warning;
use crate::typing_warning::call_needs_concrete::Via;
use crate::typing_warning_utils;

fn error_via(via: Via) -> primary::CallNeedsConcreteVia {
    match via {
        Via::Id => primary::CallNeedsConcreteVia::Id,
        Via::Self_ => primary::CallNeedsConcreteVia::Self_,
        Via::Parent => primary::CallNeedsConcreteVia::Parent,
        Via::Static => primary::CallNeedsConcreteVia::Static,
    }
}

fn add_call_needs_concrete(
    env: &Env,
    check_level: isize,
    pos: &Pos,
    class_name: &str,
    meth_name: &str,
    decl_pos: &PosOrDecl,
    via: Via,
) {
    match check_level {
        1 => typing_warning_utils::add(
            env,
            (
                pos.clone(),
                typing_warning::Kind::Call_needs_concrete,
                typing_warning::call_needs_concrete::T {
                    call_pos: pos.clone(),
                    class_name: class_name.to_string(),
                    meth_name: meth_name.to_string(),
                    decl_pos: decl_pos.clone(),
                    via,
                },
            ),
        ),
        2 => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Call_needs_concrete {
                pos: pos.clone(),
                class_name: class_name.to_string(),
                meth_name: meth_name.to_string(),
                decl_pos: decl_pos.clone(),
                via: error_via(via),
            }),
            env,
        ),
        _ => {}
    }
}

fn add_abstract_access_via_static(
    env: &Env,
    check_level: isize,
    pos: &Pos,
    class_name: &str,
    member_name: &str,
    decl_pos: &PosOrDecl,
) {
    let containing_method_pos = Some(env.genv.function_pos.clone());
    match check_level {
        1 => typing_warning_utils::add(
            env,
            (
                pos.clone(),
                typing_warning::Kind::Abstract_access_via_static,
                typing_warning::abstract_access_via_static::T {
                    access_pos: pos.clone(),
                    class_name: class_name.to_string(),
                    member_name: member_name.to_string(),
                    decl_pos: decl_pos.clone(),
                    containing_method_pos,
                },
            ),
        ),
        2 => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Abstract_access_via_static {
                pos: pos.clone(),
                class_name: class_name.to_string(),
                member_name: member_name.to_string(),
                decl_pos: decl_pos.clone(),
                containing_method_pos,
            }),
            env,
        ),
        _ => {}
    }
}

fn add_uninstantiable_class_via_static(
    env: &Env,
    check_level: isize,
    pos: &Pos,
    class_name: String,
    decl_pos: PosOrDecl,
) {
    let containing_method_pos = Some(env.genv.function_pos.clone());
    match check_level {
        1 => typing_warning_utils::add(
            env,
            (
                pos.clone(),
                typing_warning::Kind::Uninstantiable_class_via_static,
                typing_warning::uninstantiable_class_via_static::T {
                    usage_pos: pos.clone(),
                    class_name,
                    decl_pos,
                    containing_method_pos,
                },
            ),
        ),
        2 => typing_error_utils::add_typing_error(
            &typing_error::primary(primary::T::Uninstantiable_class_via_static {
                pos: pos.clone(),
                class_name,
                decl_pos,
                containing_method_pos,
            }),
            env,
        ),
        _ => {}
    }
}

/// Produce warnings for "needs concrete" violations.
/// https://fburl.com/hack_needs_concrete
pub fn check_class_get<Ex, En>(
    env: &Env,
    class_get_pos: &Pos,
    def_pos: &PosOrDecl,
    cid: &str,
    mid: &str,
    ce: &ClassElt,
    e: &aast::ClassId_<Ex, En>,
    is_method: bool,
) {
    let tcopt = &env.genv.tcopt;
    if crate::typechecker_options::needs_concrete_body_or_call_check_enabled(tcopt) {
        let body_check_level = tcopt.needs_concrete_body_check;
        let forwarding_call_check_level = tcopt.needs_concrete_forwarding_call_check;
        let class_call_check_level = tcopt.needs_concrete_class_call_check;
        let callee_is_needs_concrete_method: bool =
            is_method && get_ce_readonly_prop_or_needs_concrete(ce);
        let check_needs_concrete_call = |via: Via| {
            // `self` and `parent` forward the referent of `static` so are just as dangerous
            if forwarding_call_check_level > 0
                && callee_is_needs_concrete_method
                && !typing_env::static_points_to_concrete_class(env)
            {
                add_call_needs_concrete(
                    env,
                    forwarding_call_check_level,
                    class_get_pos,
                    cid,
                    mid,
                    def_pos,
                    via,
                )
            }
        };
        match e {
            aast::ClassId_::CI(_)
                if class_call_check_level > 0 && callee_is_needs_concrete_method =>
            {
                if let Some(class_) = decl_entry::to_option(typing_env::get_class(env, cid)) {
                    let is_concrete: bool = {
                        let is_non_abstract: bool = !cls::abstract_(&class_);
                        let is_final_non_consistent_construct =
                            LazyCell::new(|| match typing_env::get_construct(env, &class_).1 {
                                ConsistentKind::FinalClass => true,
                                ConsistentKind::Inconsistent
                                | ConsistentKind::ConsistentConstruct => false,
                            });
                        is_non_abstract
                            || cls::final_(&class_) && *is_final_non_consistent_construct
                    };
                    if !is_concrete {
                        add_call_needs_concrete(
                            env,
                            class_call_check_level,
                            class_get_pos,
                            cid,
                            mid,
                            def_pos,
                            Via::Id,
                        )
                    }
                }
            }
            aast::ClassId_::CIself => check_needs_concrete_call(Via::Self_),
            aast::ClassId_::CIparent => check_needs_concrete_call(Via::Parent),
            aast::ClassId_::CIstatic => {
                check_needs_concrete_call(Via::Static);
                if body_check_level > 0
                    && get_ce_abstract(ce)
                    && !typing_env::static_points_to_concrete_class(env)
                {
                    // We check for abstract access via `static`
                    // as part of the "needs concrete" feature, because
                    // checking for calls to `abstract` functions for
                    // `self`/`parent`/classname, etc. is already covered by other type
                    // errors such as Primary.Self_abstract_call, Primary.Parent_abstract_call, etc.
                    add_abstract_access_via_static(
                        env,
                        body_check_level,
                        class_get_pos,
                        cid,
                        mid,
                        def_pos,
                    )
                }
            }
            aast::ClassId_::CI(_) => {}
            aast::ClassId_::CIreified(_) => {}
            aast::ClassId_::CIexpr(_) => {}
        }
    }
}

/// Produce warnings for "needs concrete" violations.
/// https://fburl.com/hack_needs_concrete
pub fn check_instantiation<Ex, En>(
    env: &Env,
    instantiation_pos: &Pos,
    cid: &aast::ClassId_<Ex, En>,
) {
    let check_level = env.genv.tcopt.needs_concrete_body_check;
    if check_level == 1 || check_level == 2 {
        match cid {
            aast::ClassId_::CIstatic if !typing_env::static_points_to_concrete_class(env) => {
                if let Some(class_) = decl_entry::to_option(typing_env::get_self_class(env)) {
                    let would_be_redundant =
                        // Elsewhere we already generate a 4002 (uninstantiable class)
                        // error for `new static(....)` in `abstract final` classes
                        // https://www.internalfb.com/code/fbsource/[0032e6cacac2bab09425384b967f12d8d4743daf]/fbcode/hphp/hack/src/typing/typing.ml?lines=4226%2C11972
                        cls::abstract_(&class_) && cls::final_(&class_);
                    if !would_be_redundant {
                        add_uninstantiable_class_via_static(
                            env,
                            check_level,
                            instantiation_pos,
                            cls::name(&class_),
                            cls::pos(&class_),
                        )
                    }
                }
            }
            aast::ClassId_::CIstatic
            | aast::ClassId_::CIself
            | aast::ClassId_::CIparent
            | aast::ClassId_::CI(_)
            | aast::ClassId_::CIreified(_)
            | aast::ClassId_::CIexpr(_) => {}
        }
    }
}

/// Validate `<<__NeedsConcrete>>` usage on class members.
///  - Errors on instance methods and constructors.
///  - Errors on static methods in final classes.
pub fn check_class_def(env: &Env, c: &nast::Class_, tc: &cls::T) {
    // Attribute validity historically followed `needs_concrete`, independently
    // of `needs_concrete_override_check`. Preserve that behavior for its three
    // fine-grained replacements.
    if crate::typechecker_options::needs_concrete_body_or_call_check_enabled(&env.genv.tcopt) {
        // Check for __NeedsConcrete on instance methods (non-static methods) and constructors
        for m in c.methods.iter() {
            if naming_attributes::mem(sn::user_attributes::NEEDS_CONCRETE, &m.user_attributes) {
                let meth_name = &m.name.1;
                if meth_name == sn::members::__CONSTRUCT {
                    // __NeedsConcrete on constructor
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Needs_concrete_on_constructor {
                            pos: m.name.0.clone(),
                            class_name: c.name.1.clone(),
                        }),
                        env,
                    )
                } else if !m.static_ {
                    // __NeedsConcrete on instance method
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Needs_concrete_on_instance_method {
                            pos: m.name.0.clone(),
                            class_name: c.name.1.clone(),
                            meth_name: meth_name.clone(),
                        }),
                        env,
                    )
                } else if
                // Check for __NeedsConcrete on static methods in final classes
                cls::final_(tc) && !cls::abstract_(tc) {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Needs_concrete_in_final_class {
                            pos: m.name.0.clone(),
                            class_name: c.name.1.clone(),
                            meth_name: meth_name.clone(),
                        }),
                        env,
                    )
                }
            }
        }
    }
}
