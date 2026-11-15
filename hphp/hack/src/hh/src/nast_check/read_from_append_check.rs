// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/read_from_append_check.ml`.

use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

pub struct ReadFromAppendCheck;

impl<'a> Handler<'a> for ReadFromAppendCheck {
    fn at_expr(&mut self, env: &Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        if let nast::Expr_::ArrayGet(ag) = &e.2 {
            if let (nast::Expr(_, p, _), None) = &**ag {
                if !env.array_append_allowed {
                    errors.add(NastCheckError::ReadingFromAppend(p.clone()));
                }
            }
        }
    }
}
