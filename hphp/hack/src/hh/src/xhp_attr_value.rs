// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/tast_check/xhp_attr_value.ml`. See `hh/PORTING.md`.

use oxidized::aast;
use oxidized::ast_defs::XhpEnumValue;
use oxidized::pos::Pos;

use crate::decl_entry;
/// `module Cls = Folded_class`
use crate::folded_class as cls;
use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::tast;
use crate::tast_env;
use crate::tast_env::Env;
use crate::tast_visitor;
use crate::typing_error;
use crate::typing_error::primary;
use crate::typing_error_utils;

/// `('a, 'b) xhp_attribute` of a TAST.
type XhpAttribute = aast::XhpAttribute<tast::Ty, tast::SavedEnv>;

/// If `attr_name` is an enum attribute on `cls`, return the list of allowed values.
pub fn xhp_enum_attr_values(env: &Env, cls: &cls::T, attr_name: &str) -> Option<Vec<XhpEnumValue>> {
    let attr_name = ":".to_string() + attr_name;
    // `Cls.props cls |> List.find ~f:(fun (name, _) -> ..)`, the origin of
    // the property only.
    cls::prop_origin(cls, &attr_name)
        .and_then(|cls_name| decl_entry::to_option(tast_env::get_class(env, &cls_name)))
        .and_then(|cls| cls::xhp_enum_values(&cls).get(&attr_name).cloned())
}

pub fn split_attr_values(decl_values: &[XhpEnumValue]) -> (Vec<isize>, Vec<String>) {
    // `let rec aux dvs ((int_vals, string_vals) as acc)`: the values are
    // prepended, so each list is in the reverse order.
    let mut int_vals = vec![];
    let mut string_vals = vec![];
    for dv in decl_values {
        match dv {
            XhpEnumValue::XEVInt(i) => int_vals.insert(0, *i),
            XhpEnumValue::XEVString(s) => string_vals.insert(0, s.clone()),
        }
    }
    (int_vals, string_vals)
}

/// Format enum values as Hack literals.
pub fn attr_value_literals(decl_values: &[XhpEnumValue]) -> Vec<String> {
    let as_literal = |v: &XhpEnumValue| match v {
        XhpEnumValue::XEVInt(i) => i.to_string(),
        XhpEnumValue::XEVString(s) => "\"".to_string() + s + "\"",
    };
    decl_values.iter().map(as_literal).collect()
}

/// Best-effort conversion from a Hack integer literal to its integer value.
pub fn int_of_hack_literal(literal: &str) -> Option<isize> {
    let parts: Vec<&str> = literal.split('_').collect();
    let clean_literal = parts.concat();
    int_of_string_opt(&clean_literal)
}

pub fn add_error(env: &Env, pos: &Pos, attr_name: &str, attr_values: &[XhpEnumValue]) {
    typing_error_utils::add_typing_error(
        &typing_error::xhp(primary::xhp::T::AttributeValue {
            pos: pos.clone(),
            attr_name: attr_name.to_string(),
            valid_values: attr_value_literals(attr_values),
        }),
        env,
    )
}

/// If `attr` is initialized with a literal value that isn't in the
/// enum declaration, show a lint error.
pub fn check_attr_value(env: &Env, cls: &cls::T, attr: &XhpAttribute) {
    match attr {
        aast::XhpAttribute::XhpSimple(aast::XhpSimple {
            name: (_, attr_name),
            expr: aast::Expr(_, attr_val_pos, attr_val),
            ..
        }) => match xhp_enum_attr_values(env, cls, attr_name) {
            Some(attr_values) => {
                let (int_values, string_values) = split_attr_values(&attr_values);
                match attr_val {
                    aast::Expr_::Int(i) => match int_of_hack_literal(i) {
                        Some(i) => {
                            if !int_values.contains(&i) {
                                add_error(env, attr_val_pos, attr_name, &attr_values)
                            }
                        }
                        None => {}
                    },
                    aast::Expr_::String(s) => {
                        if !string_values.iter().any(|v| v.as_bytes() == s.as_slice()) {
                            add_error(env, attr_val_pos, attr_name, &attr_values)
                        }
                    }
                    _ => {}
                }
            }
            None => {}
        },
        aast::XhpAttribute::XhpSpread(_) => {}
    }
}

struct Handler;

impl<'a> tast_visitor::Handler<'a> for Handler {
    fn at_expr(&mut self, env: &Env, e: &'a tast::Expr) {
        let aast::Expr(_, _, e_) = e;
        match e_ {
            aast::Expr_::Xml(xml) => {
                let (class_name, attrs, _children) = &**xml;
                match tast_env::get_class(env, &class_name.1) {
                    decl_entry::T::Found(cls) => {
                        for attr in attrs {
                            check_attr_value(env, &cls, attr)
                        }
                    }
                    decl_entry::T::DoesNotExist | decl_entry::T::NotYetAvailable => {}
                }
            }
            _ => {}
        }
    }
}

pub fn handler<'a>() -> Box<dyn tast_visitor::Handler<'a> + 'a> {
    Box::new(Handler)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literals() {
        assert_eq!(int_of_hack_literal("1_000"), Some(1000));
        assert_eq!(int_of_hack_literal("0x1F"), Some(31));
        assert_eq!(int_of_hack_literal("0b101"), Some(5));
        // Leading zeros are decimal for `int_of_string`, not octal as in Hack.
        assert_eq!(int_of_hack_literal("017"), Some(17));
        assert_eq!(int_of_hack_literal("1.5"), None);
        // 63-bit ints: decimal literals are range-checked, the others wrap.
        assert_eq!(int_of_hack_literal("4611686018427387903"), Some((1 << 62) - 1));
        assert_eq!(int_of_hack_literal("4611686018427387904"), None);
        assert_eq!(int_of_hack_literal("-4611686018427387904"), Some(-(1 << 62)));
        assert_eq!(int_of_hack_literal("0x4000000000000000"), Some(-(1 << 62)));
        assert_eq!(int_of_hack_literal("-0x4000000000000000"), Some(-(1 << 62)));
        assert_eq!(int_of_hack_literal("0x7FFFFFFFFFFFFFFF"), Some(-1));
        assert_eq!(int_of_hack_literal("0x8000000000000000"), None);
        assert_eq!(int_of_hack_literal("-0x10"), Some(-16));
        assert_eq!(
            attr_value_literals(&[XhpEnumValue::XEVInt(3), XhpEnumValue::XEVString("a".into())]),
            vec!["3".to_string(), "\"a\"".to_string()]
        );
        let (ints, strings) = split_attr_values(&[
            XhpEnumValue::XEVInt(1),
            XhpEnumValue::XEVString("a".into()),
            XhpEnumValue::XEVInt(2),
        ]);
        assert_eq!(ints, vec![2, 1]);
        assert_eq!(strings, vec!["a".to_string()]);
    }
}
