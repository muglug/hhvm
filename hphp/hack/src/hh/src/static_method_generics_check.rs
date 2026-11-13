// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `static_method_generics_check.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::ast_defs::ReifyKind;

use crate::aast::split_methods;
use crate::relative_path;
use crate::tast;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

/// `S_set.t`
type SSet = std::collections::BTreeSet<String>;

/// The object `visitor` of `static_method_check` (it inherits `Aast.iter`).
struct StaticMethodVisitor<'m> {
    reified_params: &'m SSet,
    m: &'m tast::Method_,
}

impl<'a, 'm> Visitor<'a> for StaticMethodVisitor<'m> {
    type Params = tast_visitor::IterParams;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_hint(&mut self, env: &mut Env, h: &'a tast::Hint) -> tast_visitor::Res {
        let aast::Hint(pos, hint) = h;
        match &**hint {
            aast::Hint_::Habstr(t) => {
                if self.reified_params.contains(t) {
                    typing_error_utils::add_typing_error(
                        &typing_error::primary(primary::T::Static_meth_with_class_reified_generic {
                            pos: self.m.span.clone(),
                            generic_pos: pos.clone(),
                        }),
                        env,
                    )
                }
                Ok(())
            }
            _ => h.recurse(env, self),
        }
    }
}

pub fn static_method_check(env: &Env, reified_params: &SSet, m: &tast::Method_) {
    let mut visitor = StaticMethodVisitor { reified_params, m };
    // The visitor does not change its environment.
    let mut env = env.clone();
    for param in &m.params {
        let _ = visitor.visit_fun_param(&mut env, param);
    }
    let _ = visitor.visit_type_hint(&mut env, &m.ret);
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_class_(&mut self, env: &Env, c: &'a tast::Class_) {
        let (_, static_methods, _) = split_methods(&c.methods);
        if !relative_path::is_hhi(relative_path::prefix(c.span.filename())) {
            let reified_params: SSet = c
                .tparams
                .iter()
                .filter_map(|tp| {
                    if !matches!(tp.reified, ReifyKind::Erased) {
                        Some(tp.name.1.clone())
                    } else {
                        None
                    }
                })
                .collect();
            for m in static_methods {
                static_method_check(env, &reified_params, m)
            }
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}
