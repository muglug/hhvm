// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/control_context_check.ml`.

use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::ControlContext;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

pub struct ControlContextCheck;

impl<'a> Handler<'a> for ControlContextCheck {
    fn at_stmt(&mut self, env: &Env<'a>, s: &'a nast::Stmt, errors: &mut Errors) {
        let p = &s.0;
        let err = match (&s.1, env.control_context) {
            (nast::Stmt_::Break, ControlContext::Toplevel) => {
                NastCheckError::ToplevelBreak(p.clone())
            }
            (nast::Stmt_::Continue, ControlContext::Toplevel) => {
                NastCheckError::ToplevelContinue(p.clone())
            }
            (nast::Stmt_::Continue, ControlContext::SwitchContext) => {
                NastCheckError::ContinueInSwitch(p.clone())
            }
            (nast::Stmt_::Return(_), _) if env.is_finally => {
                NastCheckError::ReturnInFinally(p.clone())
            }
            _ => return,
        };
        errors.add(err);
    }
}
