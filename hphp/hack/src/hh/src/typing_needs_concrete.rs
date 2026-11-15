// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_needs_concrete.ml`. See `hh/PORTING.md`.
//!
//! The polymorphic variant ``[ `Id | `Static | `Self | `Parent ]`` given to
//! `add_call_needs_concrete` is `typing_warning::call_needs_concrete::Via`;
//! the error takes the same tags as `primary::CallNeedsConcreteVia`.

use oxidized::aast;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::nast;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use pos::ToOxidized;

use crate::decl_entry;
use crate::folded_class as cls;
use crate::naming_attributes;
use crate::naming_special_names as sn;
use crate::typing_defs::ClassElt;
use crate::typing_defs::get_ce_abstract;
use crate::typing_defs::get_ce_readonly_prop_or_needs_concrete;
use crate::typing_defs_core::DeclTparam;
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
                typing_warning::Kind::CALL_NEEDS_CONCRETE,
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
            &typing_error::primary(primary::T::CallNeedsConcrete {
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
    pos: &Pos,
    class_name: &str,
    member_name: &str,
    decl_pos: &PosOrDecl,
) {
    let containing_method_pos = Some(env.genv.function_pos.clone());
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::AbstractAccessViaStatic {
            pos: pos.clone(),
            class_name: class_name.to_string(),
            member_name: member_name.to_string(),
            decl_pos: decl_pos.clone(),
            containing_method_pos,
        }),
        env,
    )
}

fn add_uninstantiable_class_via_static(
    env: &Env,
    pos: &Pos,
    class_name: String,
    decl_pos: PosOrDecl,
) {
    let containing_method_pos = Some(env.genv.function_pos.clone());
    typing_error_utils::add_typing_error(
        &typing_error::primary(primary::T::UninstantiableClassViaStatic {
            pos: pos.clone(),
            class_name,
            decl_pos,
            containing_method_pos,
        }),
        env,
    )
}

pub fn check_abstract_access_via_static<Ex, En>(
    env: &Env,
    class_get_pos: &Pos,
    def_pos: &PosOrDecl,
    cid: &str,
    mid: &str,
    e: &aast::ClassId_<Ex, En>,
) {
    match e {
        aast::ClassId_::CIstatic if !typing_env::static_points_to_concrete_class(env) => {
            add_abstract_access_via_static(env, class_get_pos, cid, mid, def_pos)
        }
        aast::ClassId_::CIstatic
        | aast::ClassId_::CIself
        | aast::ClassId_::CIparent
        | aast::ClassId_::CI(_)
        | aast::ClassId_::CIreified(_)
        | aast::ClassId_::CIexpr(_) => {}
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
    is_function_pointer: bool,
    is_method: bool,
) {
    let named_class_check_level = if is_function_pointer {
        crate::typechecker_options::needs_concrete_class_function_pointer_check(&env.genv.tcopt)
    } else {
        2
    };
    let callee_is_needs_concrete_method: bool =
        is_method && get_ce_readonly_prop_or_needs_concrete(ce);
    let check_needs_concrete_call = |via: Via| {
        // `self` and `parent` forward the referent of `static` so are just as dangerous
        if callee_is_needs_concrete_method && !typing_env::static_points_to_concrete_class(env) {
            add_call_needs_concrete(env, 2, class_get_pos, cid, mid, def_pos, via)
        }
    };
    match e {
        aast::ClassId_::CI(_) if named_class_check_level > 0 && callee_is_needs_concrete_method => {
            if let Some(class_) = decl_entry::to_option(typing_env::get_class(env, cid)) {
                if !typing_env::is_concrete_class(env, &class_) {
                    add_call_needs_concrete(
                        env,
                        named_class_check_level,
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
            if get_ce_abstract(ce) {
                // We check for abstract access via `static`
                // as part of the "needs concrete" feature, because
                // checking for calls to `abstract` functions for
                // `self`/`parent`/classname, etc. is already covered by other type
                // errors such as Primary.Self_abstract_call, Primary.Parent_abstract_call, etc.
                check_abstract_access_via_static(env, class_get_pos, def_pos, cid, mid, e)
            }
        }
        aast::ClassId_::CI(_) => {}
        aast::ClassId_::CIreified(_) => {}
        aast::ClassId_::CIexpr(_) => {}
    }
}

/// Produce warnings for "needs concrete" violations.
/// https://fburl.com/hack_needs_concrete
pub fn check_instantiation<Ex, En>(
    env: &Env,
    instantiation_pos: &Pos,
    cid: &aast::ClassId_<Ex, En>,
) {
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

pub fn check_abstract_tconst_via_static(env: &Env, pos: &Pos, tconst_name: &str) {
    if !typing_env::static_points_to_concrete_class(env) {
        if let Some(class_) = decl_entry::to_option(typing_env::get_self_class(env)) {
            match typing_env::get_typeconst(env, &class_, tconst_name) {
                Some(tc)
                    if matches!(
                        &tc.kind,
                        ty::decl::Typeconst::TCAbstract(ty::decl::AbstractTypeconst {
                            default: None,
                            ..
                        })
                    ) =>
                {
                    // Resolving an abstract type constant without a default through
                    // `static`/`this` requires a runtime value that an abstract class
                    // does not have.
                    // We treat this like abstract member access via `static`
                    // (see [check_class_get]) so the containing method must be
                    // `__NeedsConcrete`.
                    add_abstract_access_via_static(
                        env,
                        pos,
                        &cls::name(&class_),
                        tconst_name,
                        &tc.name.pos().clone().to_oxidized(),
                    )
                }
                _ => {}
            }
        }
    }
}

pub fn check_reified_targ(env: &Env, tparam: &DeclTparam, hint: &nast::Hint) {
    match tparam.reified {
        aast::ReifyKind::Erased => {}
        aast::ReifyKind::SoftReified | aast::ReifyKind::Reified => {
            struct V<'e>(&'e Env);
            impl<'ast> Visitor<'ast> for V<'_> {
                type Params = AstParams<(), ()>;

                fn object(&mut self) -> &mut dyn Visitor<'ast, Params = Self::Params> {
                    self
                }

                fn visit_hint(&mut self, c: &mut (), hint: &'ast nast::Hint) -> Result<(), ()> {
                    let aast::Hint(pos, hint_) = hint;
                    match &**hint_ {
                        aast::Hint_::Haccess(aast::Hint(_, root), ids)
                            if matches!(&**root, aast::Hint_::Hthis) && !ids.is_empty() =>
                        {
                            check_abstract_tconst_via_static(self.0, pos, &ids[0].1);
                            Ok(())
                        }
                        _ => hint.recurse(c, self.object()),
                    }
                }
            }
            let _ = V(env).visit_hint(&mut (), hint);
        }
    }
}

pub fn check_reified_targs<Ex>(env: &Env, tparams: &[DeclTparam], targs: &[aast::Targ<Ex>]) {
    if tparams.len() == targs.len() {
        for (tparam, aast::Targ(_, hint)) in tparams.iter().zip(targs.iter()) {
            check_reified_targ(env, tparam, hint)
        }
    }
}

/// Validate `<<__NeedsConcrete>>` usage on class members.
///  - Errors on instance methods and constructors.
///  - Errors on static methods in final classes.
pub fn check_class_def(env: &Env, c: &nast::Class_, tc: &cls::T) {
    // Check for __NeedsConcrete on instance methods (non-static methods) and constructors
    for m in c.methods.iter() {
        if naming_attributes::mem(sn::user_attributes::NEEDS_CONCRETE, &m.user_attributes) {
            let meth_name = &m.name.1;
            if meth_name == sn::members::__CONSTRUCT {
                // __NeedsConcrete on constructor
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::NeedsConcreteOnConstructor {
                        pos: m.name.0.clone(),
                        class_name: c.name.1.clone(),
                    }),
                    env,
                )
            } else if !m.static_ {
                // __NeedsConcrete on instance method
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::NeedsConcreteOnInstanceMethod {
                        pos: m.name.0.clone(),
                        class_name: c.name.1.clone(),
                        meth_name: meth_name.clone(),
                    }),
                    env,
                )
            } else if
            // In a final concrete class `static` is always the class itself, so
            // the attribute is redundant
            cls::final_(tc) && typing_env::is_concrete_class(env, tc) {
                typing_error_utils::add_typing_error(
                    &typing_error::primary(primary::T::NeedsConcreteInFinalClass {
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
