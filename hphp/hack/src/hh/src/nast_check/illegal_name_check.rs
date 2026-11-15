// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/illegal_name_check.ml`.

use oxidized::ast_defs::ClassishKind;
use oxidized::naming_error::NamingError;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;
use oxidized::pos::Pos;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;
use super::sn;

fn is_magic(s: &str) -> bool {
    s != sn::members::__TO_STRING && sn::members::AS_SET.contains(s)
}

/// Class consts and typeconsts cannot be named "class".
fn error_if_is_named_class(nast::Id(pos, name): &nast::Id, errors: &mut Errors) {
    if name.to_lowercase() == "class" {
        errors.add(NamingError::IllegalMemberVariableClass(pos.clone()));
    }
}

fn magic(pos: &Pos, meth_name: &str, errors: &mut Errors) {
    errors.add(NastCheckError::Magic {
        pos: pos.clone(),
        meth_name: meth_name.to_string(),
    });
}

pub struct IllegalNameCheck;

impl<'a> Handler<'a> for IllegalNameCheck {
    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        for tc in &c.typeconsts {
            error_if_is_named_class(&tc.name, errors);
        }
        for cc in &c.consts {
            error_if_is_named_class(&cc.id, errors);
        }
    }

    fn at_expr(&mut self, env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        let func_name = env.function_name.map(|sid| sid.1.as_str());
        match &e.2 {
            nast::Expr_::Id(id) => {
                let nast::Id(pos, const_) = &**id;
                let ck = env.classish_kind;
                if !sn::pseudo_consts::is_pseudo_const(const_) {
                } else if const_ == sn::pseudo_consts::G__CLASS__ && ck.is_none() {
                    errors.add(NamingError::IllegalCLASS(pos.clone()));
                } else if const_ == sn::pseudo_consts::G__TRAIT__
                    && !matches!(ck, Some(ClassishKind::Ctrait))
                {
                    errors.add(NamingError::IllegalTRAIT(pos.clone()));
                }
            }
            nast::Expr_::ClassConst(cc) => {
                let (class_id, (pos, meth_name)) = &**cc;
                if matches!(class_id.2, nast::ClassId_::CIparent)
                    && func_name == Some(meth_name.as_str())
                {
                } else if is_magic(meth_name) && func_name != Some(meth_name.as_str()) {
                    magic(pos, meth_name, errors);
                }
            }
            nast::Expr_::ObjGet(og) => {
                if let nast::Expr(_, _, nast::Expr_::Id(s)) = &og.1 {
                    let nast::Id(pos, meth_name) = &**s;
                    if is_magic(meth_name) {
                        magic(pos, meth_name, errors);
                    }
                }
            }
            nast::Expr_::MethodCaller(mc) => {
                let (_, (pos, meth_name)) = &**mc;
                if is_magic(meth_name) {
                    magic(pos, meth_name, errors);
                }
            }
            _ => {}
        }
    }

    fn at_fun_def(&mut self, _env: &Env<'a>, fd: &'a nast::FunDef, errors: &mut Errors) {
        let nast::Id(pos, fname) = &fd.name;
        // `Utils.strip_ns`
        let fname_lower = fname.strip_prefix('\\').unwrap_or(fname).to_lowercase();
        if fname_lower == sn::members::__CONSTRUCT || fname_lower == "using" {
            errors.add(NastCheckError::IllegalFunctionName {
                pos: pos.clone(),
                name: fname.clone(),
            });
        }
    }

    fn at_method_(&mut self, env: &Env<'a>, m: &'a nast::Method_, errors: &mut Errors) {
        let nast::Id(pos, name) = &m.name;
        if name == sn::members::__DESTRUCT {
            errors.add(NastCheckError::IllegalDestructor(pos.clone()));
        }
        assert!(env.class_name.is_some());
    }
}
