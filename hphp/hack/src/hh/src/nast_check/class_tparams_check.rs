// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/class_tparams_check.ml`.

use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

/// The type parameters of the class, and of the function hints around the
/// hint being visited.
type State<'a> = Vec<&'a nast::Id>;

struct HintVisitor<'e> {
    errors: &'e mut Errors,
}

impl<'a, 'e> Visitor<'a> for HintVisitor<'e> {
    type Params = AstParams<State<'a>, ()>;

    fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_hint(&mut self, state: &mut State<'a>, hint: &'a nast::Hint) -> Result<(), ()> {
        let nast::Hint(pos, h) = hint;
        if let nast::Hint_::Habstr(tp_name) = &**h {
            for nast::Id(c_tp_pos, c_tp_name) in state.iter() {
                if c_tp_name == tp_name {
                    self.errors
                        .add(NastCheckError::TypeconstDependsOnExternalTparam {
                            pos: pos.clone(),
                            ext_pos: c_tp_pos.clone(),
                            ext_name: c_tp_name.clone(),
                        });
                }
            }
            hint.recurse(state, self)
        } else if let nast::Hint_::Hfun(hf) = &**h {
            let saved = state.len();
            state.extend(hf.tparams.iter().map(|tp| &tp.name));
            let result = hint.recurse(state, self);
            state.truncate(saved);
            result
        } else {
            hint.recurse(state, self)
        }
    }
}

pub struct ClassTparamsCheck;

impl<'a> Handler<'a> for ClassTparamsCheck {
    fn at_class_(&mut self, _env: &Env<'a>, c: &'a nast::Class_, errors: &mut Errors) {
        let mut state: State<'a> = c.tparams.iter().map(|tp| &tp.name).collect();
        let mut visitor = HintVisitor { errors };
        let mut on_hint = |hint: &'a nast::Hint| {
            let _ = visitor.visit_hint(&mut state, hint);
        };
        for t in &c.typeconsts {
            match &t.kind {
                nast::ClassTypeconst::TCAbstract(nast::ClassAbstractTypeconst {
                    as_constraint,
                    super_constraint,
                    default,
                }) => {
                    as_constraint.iter().for_each(&mut on_hint);
                    super_constraint.iter().for_each(&mut on_hint);
                    default.iter().for_each(&mut on_hint);
                }
                nast::ClassTypeconst::TCConcrete(nast::ClassConcreteTypeconst { c_tc_type }) => {
                    on_hint(c_tc_type)
                }
            }
        }
    }
}
