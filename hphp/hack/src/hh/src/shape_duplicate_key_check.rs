// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/shape_duplicate_key_check.ml`. See
//! `hh/PORTING.md`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use bstr::BString;
use oxidized::aast;
use oxidized::ast_defs;
use oxidized::ast_defs::ShapeFieldName;
use oxidized::custom_error_config::CustomErrorConfig;
use oxidized::message::Message;
use oxidized::naming_error::NamingError;
use oxidized::pos::Pos;
use oxidized::shape_map::ShapeField;
use oxidized::typing_defs::ClassConstKind;

use crate::decl_entry;
use crate::diagnostics;
use crate::markdown_lite;
use crate::naming_error_utils;
use crate::pos_or_decl;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typechecker_options;
use crate::typing_defs::const_value;
use crate::utils;

/// `Runtime_value_map`
type RuntimeValueMap<V> = BTreeMap<const_value::ConcreteValue, V>;

fn symbolic_name_pos(symbolic_name: &ShapeFieldName) -> &Pos {
    match symbolic_name {
        ShapeFieldName::SFlitStr((pos, _))
        | ShapeFieldName::SFclassname(ast_defs::Id(pos, _))
        | ShapeFieldName::SFclassConst(_, (pos, _)) => pos,
    }
}

fn symbolic_name_span(symbolic_name: &ShapeFieldName) -> Pos {
    match symbolic_name {
        ShapeFieldName::SFlitStr((pos, _)) | ShapeFieldName::SFclassname(ast_defs::Id(pos, _)) => {
            pos.clone()
        }
        ShapeFieldName::SFclassConst(ast_defs::Id(class_pos, _), (member_pos, _)) => {
            crate::pos::btw(class_pos, member_pos)
        }
    }
}

// Keep in sync with hackc's [hhbc::ClassName::mangle] in [hackc/hhbc/id.rs],
// including [hhbc_string_utils::mangle] and [hhbc_string_utils::mangle_xhp_id]
// in [hackc/utils/string_utils.rs].
fn runtime_class_name(class_name: &str) -> String {
    let class_name = utils::strip_ns(class_name);
    let (namespace, name) = match class_name.rsplit_once('\\') {
        Some((namespace, name)) => (format!("{}\\", namespace), name),
        None => (String::new(), class_name),
    };
    let name = match name.strip_prefix(':') {
        Some(name) => format!("xhp_{}", name.replace(':', "__").replace('-', "_")),
        None => name.to_string(),
    };
    namespace + &name
}

fn resolve_runtime_value(
    env: &Env,
    symbolic_name: &ShapeFieldName,
) -> Option<const_value::ConcreteValue> {
    match symbolic_name {
        ShapeFieldName::SFlitStr((_, value)) => {
            Some(const_value::ConcreteValue::SKVString(value.to_string()))
        }
        ShapeFieldName::SFclassname(ast_defs::Id(_, class_name)) => {
            let _ = tast_env::get_class(env, class_name);
            Some(const_value::ConcreteValue::SKVString(runtime_class_name(
                class_name,
            )))
        }
        ShapeFieldName::SFclassConst(ast_defs::Id(_, class_name), (_, member_name)) => {
            (match tast_env::get_class(env, class_name) {
                decl_entry::T::Found(cls) => tast_env::get_const(env, &cls, member_name),
                decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => None,
            })
            .and_then(|const_| match const_.kind {
                ClassConstKind::CCAbstract(_) => None,
                ClassConstKind::CCConcrete => {
                    const_value::concrete_value(member_name, &const_.value)
                }
            })
        }
    }
}

fn report_duplicate_symbolic_name(
    _custom_err_config: &CustomErrorConfig,
    symbolic_name: &ShapeFieldName,
) {
    let diagnostic = naming_error_utils::to_user_diagnostic(NamingError::FieldNameAlreadyBound(
        symbolic_name_pos(symbolic_name).clone(),
    ));
    diagnostics::add_diagnostic(diagnostic)
}

fn report_duplicate_runtime_value(
    custom_err_config: &CustomErrorConfig,
    symbolic_name: &ShapeFieldName,
    first_symbolic_name: &ShapeFieldName,
    runtime_value: &const_value::ConcreteValue,
) {
    if ShapeField(symbolic_name.clone()) == ShapeField(first_symbolic_name.clone()) {
        report_duplicate_symbolic_name(custom_err_config, symbolic_name)
    } else {
        let runtime_value_text = match runtime_value {
            const_value::ConcreteValue::SKVInt(value)
            | const_value::ConcreteValue::SKVString(value) => value,
        };
        let mut diagnostic = naming_error_utils::to_user_diagnostic(
            NamingError::FieldNameAlreadyBound(symbolic_name_span(symbolic_name)),
        );
        diagnostic.reasons = vec![Message(
            pos_or_decl::of_raw_pos(symbolic_name_span(first_symbolic_name)),
            BString::from(format!(
                "This field has the same runtime key {}",
                markdown_lite::md_codify(runtime_value_text)
            )),
        )];
        diagnostics::add_diagnostic(diagnostic)
    }
}

fn check_duplicates(env: &Env, symbolic_names: Vec<&ShapeFieldName>) {
    let tcopt = tast_env::get_tcopt(env);
    let custom_err_config = typechecker_options::custom_error_config(tcopt);
    let check_runtime_values = typechecker_options::check_duplicate_runtime_shape_keys(tcopt);
    let mut seen_symbolic_names: BTreeSet<ShapeField> = BTreeSet::new();
    let mut seen_runtime_values: RuntimeValueMap<&ShapeFieldName> = RuntimeValueMap::new();
    for symbolic_name in symbolic_names {
        let runtime_value = if check_runtime_values {
            resolve_runtime_value(env, symbolic_name)
        } else {
            None
        };
        match runtime_value {
            None => {
                if seen_symbolic_names.contains(&ShapeField(symbolic_name.clone())) {
                    report_duplicate_symbolic_name(&custom_err_config, symbolic_name)
                }
            }
            Some(runtime_value) => match seen_runtime_values.get(&runtime_value) {
                None => {
                    seen_runtime_values.insert(runtime_value, symbolic_name);
                }
                Some(first_symbolic_name) => report_duplicate_runtime_value(
                    &custom_err_config,
                    symbolic_name,
                    first_symbolic_name,
                    &runtime_value,
                ),
            },
        }
        seen_symbolic_names.insert(ShapeField(symbolic_name.clone()));
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, expr: &'a tast::Expr) {
        match expr {
            aast::Expr(_, _, aast::Expr_::Shape(fields)) => {
                let symbolic_names = fields
                    .iter()
                    .filter_map(|field| match field {
                        aast::ShapeExprField::SFField(symbolic_name, _) => Some(symbolic_name),
                        aast::ShapeExprField::SFSplat(_) => None,
                    })
                    .collect();
                check_duplicates(env, symbolic_names)
            }
            _ => {}
        }
    }

    fn at_hint(&mut self, env: &Env, aast::Hint(_, hint): &'a tast::Hint) {
        match &**hint {
            aast::Hint_::Hshape(aast::NastShapeInfo { field_map, .. }) => {
                let symbolic_names = field_map
                    .iter()
                    .filter_map(|elem| match elem {
                        aast::ShapeElement::SEField(aast::ShapeFieldInfo { name, .. }) => {
                            Some(name)
                        }
                        aast::ShapeElement::SESplat(_) => None,
                    })
                    .collect();
                check_duplicates(env, symbolic_names)
            }
            _ => {}
        }
    }
}

/// `val handler : Tast_visitor.handler`
pub fn handler() -> Box<dyn for<'a> tast_visitor::Handler<'a>> {
    Box::new(Handler)
}
