// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/linter_internal_class.ml`. See `hh/PORTING.md`.
//!
//! Owned by **LINT** (plan §7.3).
//!
//! `in_sealed_attribute` is a global `ref` in OCaml (a worker is a process);
//! here it is the thread's.

use std::cell::Cell;

use naming_special_names_rust as sn;
use oxidized::aast;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;

thread_local! {
    static IN_SEALED_ATTRIBUTE: Cell<bool> = const { Cell::new(false) };
}

fn check_internal_classname(pos: oxidized::pos::Pos, ci: &aast::ClassId_<tast::Ty, tast::SavedEnv>, env: &Env) {
    let class_result = match ci {
        aast::ClassId_::CI(cls) => tast_env::get_class(env, &cls.1),
        aast::ClassId_::CIself | aast::ClassId_::CIstatic => tast_env::get_self_class(env),
        aast::ClassId_::CIparent => tast_env::get_parent_class(env),
        _ => decl_entry::T::DoesNotExist,
    };
    match class_result {
        decl_entry::T::Found(cls) if cls::internal(&cls) => {
            crate::lints_diagnostics::internal_classname(pos)
        }
        _ => {}
    }
}

/// Checks creation of a ::class from an internal class
struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_user_attribute(&mut self, _env: &Env, ua: &'a tast::UserAttribute) {
        match &ua.name.1 {
            name if name == sn::user_attributes::SEALED => IN_SEALED_ATTRIBUTE.set(true),
            _ => IN_SEALED_ATTRIBUTE.set(false),
        }
    }

    fn at_class_(&mut self, _env: &Env, _c: &'a tast::Class_) {
        IN_SEALED_ATTRIBUTE.set(false)
    }

    fn at_method_(&mut self, _env: &Env, _m: &'a tast::Method_) {
        IN_SEALED_ATTRIBUTE.set(false)
    }

    fn at_fun_def(&mut self, _env: &Env, _fd: &'a tast::FunDef) {
        IN_SEALED_ATTRIBUTE.set(false)
    }

    fn at_expr(&mut self, env: &Env, aast::Expr(_, _, expr): &'a tast::Expr) {
        match expr {
            aast::Expr_::ClassConst(cc) if cc.1.1 == "class" => {
                let (aast::ClassId(_, p, ci), _) = &**cc;
                if !IN_SEALED_ATTRIBUTE.get() {
                    check_internal_classname(*p, ci, env)
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
