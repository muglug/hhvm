// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `abstract_class_check.ml`. See `hh/PORTING.md`.

use naming_special_names_rust as sn;
use oxidized::aast;
use oxidized::naming_phase_error::NamingPhaseError;
use oxidized::nast_check_error::NastCheckError;

use crate::ast_defs;
use crate::decl_entry;
use crate::diagnostics_state;
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error_utils;

/// `Diagnostics.add_diagnostic (Nast_check_error.to_user_diagnostic err)`
fn add_nast_check_error(err: NastCheckError) {
    if let Some(diagnostic) = crate::naming_errors::to_diagnostic(NamingPhaseError::NastCheck(err))
    {
        diagnostics_state::add_diagnostic(diagnostic)
    }
}

/// `Aast.split_methods`: the constructor (the last one), the static methods
/// and the other ones, each in the order of the class.
fn split_methods(
    c_methods: &[tast::Method_],
) -> (
    Option<&tast::Method_>,
    Vec<&tast::Method_>,
    Vec<&tast::Method_>,
) {
    let mut constr = None;
    let mut statics = vec![];
    let mut rest = vec![];
    for m in c_methods {
        if m.name.1 == "__construct" {
            constr = Some(m)
        } else if m.static_ {
            statics.push(m)
        } else {
            rest.push(m)
        }
    }
    (constr, statics, rest)
}

/// `Aast.split_vars`: the static properties and the other ones.
fn split_vars(c_vars: &[tast::ClassVar]) -> (Vec<&tast::ClassVar>, Vec<&tast::ClassVar>) {
    let mut statics = vec![];
    let mut rest = vec![];
    for v in c_vars {
        if v.is_static {
            statics.push(v)
        } else {
            rest.push(v)
        }
    }
    (statics, rest)
}

pub fn check_expr(env: &tast_env::Env, e: &tast::Expr) {
    let aast::Expr(_, pos, e) = e;
    match e {
        aast::Expr_::ClassConst(cc)
            if matches!(&cc.0.2, aast::ClassId_::CIparent)
                && cc.1.1 == sn::members::__CONSTRUCT =>
        {
            let construct = &cc.1.1;
            match tast_env::get_parent_class(env) {
                decl_entry::T::Found(parent_class)
                    if ast_defs::is_c_abstract(cls::kind(&parent_class)) =>
                {
                    let (parent_construct, _) = tast_env::get_construct(env, &parent_class);
                    match parent_construct {
                        None => typing_error_utils::add_typing_error(
                            &typing_error::primary(
                                typing_error::primary::T::Parent_abstract_call {
                                    meth_name: construct.clone(),
                                    pos: pos.clone(),
                                    decl_pos: cls::pos(&parent_class),
                                },
                            ),
                            env,
                        ),
                        Some(_) => {}
                    }
                }
                _ => {}
            }
        }
        _ => {}
    }
}

pub fn check_method_body(m: &tast::Method_) {
    let named_body = &m.body;
    if m.abstract_ && !named_body.fb_ast.0.is_empty() {
        add_nast_check_error(NastCheckError::AbstractWithBody(m.name.0.clone()))
    }
}

pub fn check_class(_env: &tast_env::Env, c: &tast::Class_) {
    if ast_defs::is_c_abstract(c.kind) && c.final_ {
        let err = |m: &tast::Method_| {
            add_nast_check_error(NastCheckError::NonstaticMethodInAbstractFinalClass(
                m.name.0.clone(),
            ))
        };
        let (c_constructor, _, c_methods) = split_methods(&c.methods);
        for m in c_methods {
            err(m)
        }
        if let Some(m) = c_constructor {
            err(m)
        }

        let (_, c_instance_vars) = split_vars(&c.vars);
        for var in c_instance_vars
            .into_iter()
            .filter(|var| var.xhp_attr.is_none())
        {
            add_nast_check_error(NastCheckError::InstancePropertyInAbstractFinalClass(
                var.id.0.clone(),
            ))
        }
    }
}

/// The object `handler`.
struct AbstractClassCheck;

impl<'a> tast_visitor::Handler<'a> for AbstractClassCheck {
    fn at_expr(&mut self, env: &tast_env::Env, e: &tast::Expr) {
        check_expr(env, e)
    }

    fn at_method_(&mut self, _env: &tast_env::Env, m: &tast::Method_) {
        check_method_body(m)
    }

    fn at_class_(&mut self, env: &tast_env::Env, c: &tast::Class_) {
        check_class(env, c)
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(AbstractClassCheck)
}
