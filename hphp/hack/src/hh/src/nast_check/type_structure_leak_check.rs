// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/type_structure_leak_check.ml`.

use oxidized::aast_visitor;
use oxidized::aast_visitor::AstParams;
use oxidized::aast_visitor::Node;
use oxidized::aast_visitor::Visitor as _;
use oxidized::nast;
use oxidized::nast_check_error::NastCheckError;

use super::Errors;
use super::nast_check_env::Env;
use super::nast_visitor::Handler;

struct Visitor<'e> {
    errors: &'e mut Errors,
}

impl<'a, 'e> aast_visitor::Visitor<'a> for Visitor<'e> {
    /// The kind of thing the hint is in.
    type Params = AstParams<&'static str, ()>;

    fn object(&mut self) -> &mut dyn aast_visitor::Visitor<'a, Params = Self::Params> {
        self
    }

    fn visit_hint(&mut self, kind: &mut &'static str, hint: &'a nast::Hint) -> Result<(), ()> {
        match &*hint.1 {
            nast::Hint_::Hrefinement(_, _) => {
                self.errors.add(NastCheckError::RefinementInTypestruct {
                    pos: hint.0.clone(),
                    kind: kind.to_string(),
                });
                Ok(())
            }
            _ => hint.recurse(kind, self),
        }
    }
}

fn on_hint(mut ancestor: &'static str, hint: &nast::Hint, errors: &mut Errors) {
    let _ = Visitor { errors }.visit_hint(&mut ancestor, hint);
}

pub struct TypeStructureLeakCheck;

impl<'a> Handler<'a> for TypeStructureLeakCheck {
    // `at_expr env = visitor#on_expr (env, None)`: without an ancestor the
    // visitor reports nothing, and nothing below an expression gives it one.

    fn at_class_(&mut self, _env: &Env<'a>, class: &'a nast::Class_, errors: &mut Errors) {
        for tc in &class.typeconsts {
            match &tc.kind {
                nast::ClassTypeconst::TCAbstract(nast::ClassAbstractTypeconst {
                    default: Some(hint),
                    ..
                })
                | nast::ClassTypeconst::TCConcrete(nast::ClassConcreteTypeconst {
                    c_tc_type: hint,
                }) => {
                    let ancestor = if tc.is_ctx {
                        "a context constant"
                    } else {
                        "a type constant"
                    };
                    on_hint(ancestor, hint, errors);
                }
                nast::ClassTypeconst::TCAbstract(_) => {}
            }
        }
    }

    fn at_typedef(&mut self, _env: &Env<'a>, td: &'a nast::Typedef, errors: &mut Errors) {
        match &td.assignment {
            nast::TypedefAssignment::SimpleTypeDef(nast::TypedefVisibilityAndHint {
                vis: _,
                hint,
            }) => on_hint("a type alias", hint, errors),
            nast::TypedefAssignment::CaseType(variant, variants) => {
                for variant in std::iter::once(variant).chain(variants) {
                    on_hint("a case type", &variant.hint, errors);
                }
            }
        }
    }
}
