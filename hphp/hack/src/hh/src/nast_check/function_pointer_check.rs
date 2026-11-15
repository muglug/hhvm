// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/nast_check/function_pointer_check.ml`.

use oxidized::ast_defs::ClassishKind;
use oxidized::naming_error::NamingError;
use oxidized::nast;

use super::Errors;
use super::stateful_aast_visitor::NastVisitorWithState;

#[derive(Clone, Copy)]
pub struct Env<'a> {
    in_final_class: bool,
    class_name: Option<&'a str>,
    parent_name: Option<&'a str>,
    is_trait: bool,
}

/// `Naming_special_names.SpecialFunctions.is_special_function`
fn is_special_function(name: &str) -> bool {
    [
        "\\HH\\classname_to_class",
        "\\HH\\classname_to_class_strict_isolation_backdoor",
        "\\exit",
        "\\HH\\ReifiedGenerics\\get_class_from_type",
        "\\HH\\global_get",
        "\\HH\\global_set",
        "\\HH\\tag_provenance_here",
        "\\HH\\FIXME\\UNSAFE_CAST",
        "\\HH\\FIXME\\UNSAFE_NONNULL_CAST",
    ]
    .contains(&name)
}

pub struct FunctionPointerCheck;

impl<'a> NastVisitorWithState<'a> for FunctionPointerCheck {
    type State = Env<'a>;

    fn initial_state(&self) -> Env<'a> {
        Env {
            in_final_class: false,
            class_name: None,
            parent_name: None,
            is_trait: false,
        }
    }

    fn at_class_(&mut self, env: &mut Env<'a>, c: &'a nast::Class_, _errors: &mut Errors) {
        let parent_name = match c.extends.first() {
            Some(nast::Hint(_, h)) => match &**h {
                nast::Hint_::Happly(nast::Id(_, parent_name), _) => Some(parent_name.as_str()),
                _ => None,
            },
            None => None,
        };
        *env = Env {
            in_final_class: c.final_,
            class_name: Some(&c.name.1),
            parent_name,
            is_trait: matches!(c.kind, ClassishKind::Ctrait),
        };
    }

    fn at_expr(&mut self, env: &mut Env<'a>, e: &'a nast::Expr, errors: &mut Errors) {
        let nast::Expr_::FunctionPointer(fp) = &e.2 else {
            return;
        };
        match &fp.0 {
            nast::FunctionPtrId::FPId(nast::Id(pos, name)) => {
                if is_special_function(name) {
                    errors.add(NamingError::InvalidFunPointer {
                        pos: pos.clone(),
                        name: name.clone(),
                    });
                }
            }
            nast::FunctionPtrId::FPClassConst(class_id, (_, meth_name)) => {
                let p = &class_id.1;
                match &class_id.2 {
                    nast::ClassId_::CIself => {
                        if !env.in_final_class {
                            errors.add(NamingError::SelfInNonFinalFunctionPointer {
                                pos: p.clone(),
                                class_name: if env.is_trait {
                                    None
                                } else {
                                    env.class_name.map(str::to_string)
                                },
                                meth_name: meth_name.clone(),
                            });
                        }
                    }
                    nast::ClassId_::CIparent => {
                        errors.add(NamingError::ParentInFunctionPointer {
                            pos: p.clone(),
                            parent_name: env.parent_name.map(str::to_string),
                            meth_name: meth_name.clone(),
                        });
                    }
                    _ => {}
                }
            }
        }
    }
}
