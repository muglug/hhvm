// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `typing/typing_log_value.ml`. See `hh/PORTING.md`.
//!
//! The set and the map of a [`Value`] are those of the crate's `S_set` and
//! `S_map` (`crate::s_set::T`, `crate::s_map::T`); `Value::Map(pairs.collect())`
//! builds one from any iterator of pairs.
//!
//! The crate has two representations of `S_map.t` and of `Local_id.Set.t`
//! (`crate::s_map`, `crate::local_id::set`, on `im`, and the `BTreeMap` and
//! `BTreeSet` of `oxidized`), so [`smap_as_value`] and
//! [`local_id_set_as_value`] take anything that iterates like them.

use oxidized::pos::Pos;

use crate::internal_type_set;
use crate::local_id;
use crate::s_map;
use crate::s_set;
use crate::tvid;
use crate::typing_defs_constraints::InternalType;
use crate::typing_defs_constraints::equal_internal_type;
use crate::typing_defs_core::Ty;
use crate::typing_logic;
use crate::typing_logic::SubtypeProp;
use crate::typing_reason;

/// Universal representation of an environment, for pretty-printing and delta computation
#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Atom(String),
    List(Vec<Value>),
    Set(s_set::T),
    Map(s_map::T<Value>),
    Type(InternalType),
    SubtypeProp(SubtypeProp),
}

/// `[@@deriving eq]`: types are compared with
/// `Typing_defs_constraints.equal_internal_type` and propositions with
/// `Typing_logic.equal_subtype_prop`.
pub fn equal_value(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Atom(a), Value::Atom(b)) => a == b,
        (Value::List(a), Value::List(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| equal_value(a, b))
        }
        (Value::Set(a), Value::Set(b)) => a == b,
        (Value::Map(a), Value::Map(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|((ka, a), (kb, b))| ka == kb && equal_value(a, b))
        }
        (Value::Type(a), Value::Type(b)) => equal_internal_type(a, b),
        (Value::SubtypeProp(a), Value::SubtypeProp(b)) => typing_logic::equal_subtype_prop(a, b),
        (
            Value::Bool(_)
            | Value::Atom(_)
            | Value::List(_)
            | Value::Set(_)
            | Value::Map(_)
            | Value::Type(_)
            | Value::SubtypeProp(_),
            _,
        ) => false,
    }
}

/// [`equal_value`]
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        equal_value(self, other)
    }
}

/// When a key is given more than once, the last value wins (`S_map.of_list`).
pub fn make_map(l: Vec<(String, Value)>) -> Value {
    Value::Map(s_map::of_list(l))
}

pub fn bool_as_value(v: bool) -> Value {
    Value::Bool(v)
}

pub fn string_as_value(s: String) -> Value {
    Value::Atom(s)
}

/// `m` is an `S_map.t`: `&crate::s_map::T<A>` (`im::OrdMap<String, A>`) or
/// `&oxidized::s_map::SMap<A>`. `f` is applied in the order of the keys.
pub fn smap_as_value<'a, A: 'a>(
    mut f: impl FnMut(&'a A) -> Value,
    m: impl IntoIterator<Item = (&'a String, &'a A)>,
) -> Value {
    Value::Map(m.into_iter().map(|(k, v)| (k.clone(), f(v))).collect())
}

pub fn list_as_value(l: Vec<Value>) -> Value {
    Value::List(l)
}

/// Not exported by the `.mli`.
fn internal_type_as_value(ty: InternalType) -> Value {
    Value::Type(ty)
}

pub fn locl_type_as_value(ty: Ty) -> Value {
    internal_type_as_value(InternalType::LoclType(ty))
}

pub fn internal_type_set_as_value(tys: &internal_type_set::T) -> Value {
    list_as_value(
        internal_type_set::elements(tys)
            .into_iter()
            .map(internal_type_as_value)
            .collect(),
    )
}

pub fn subtype_prop_as_value(prop: SubtypeProp) -> Value {
    Value::SubtypeProp(prop)
}

pub fn pos_as_value(p: &Pos) -> Value {
    string_as_value(crate::pos::string(&crate::pos::to_absolute(p)))
}

pub fn reason_as_value(_r: &typing_reason::T_) -> Value {
    todo!(
        "Typing_log_value.reason_as_value: Typing_reason.pp_t_ (`[@@deriving show]` of a reason) is not ported: it needs a port of OCaml's Format (boxes and break hints)"
    )
}

pub fn local_id_as_string(id: &local_id::T) -> String {
    format!("{}[#{}]", local_id::get_name(id), local_id::to_int(id))
}

/// `s` is a `Local_id.Set.t`: `&crate::local_id::set::T`
/// (`im::OrdSet<LocalId>`) or `&oxidized::local_id::set::Set`.
pub fn local_id_set_as_value<'a>(s: impl IntoIterator<Item = &'a local_id::T>) -> Value {
    Value::Set(s.into_iter().map(local_id_as_string).collect())
}

pub fn var_as_string(v: tvid::T) -> String {
    format!("#{}", tvid::show(v))
}

pub fn varset_as_value(s: &tvid::set::T) -> Value {
    Value::Set(s.iter().map(|v| var_as_string(*v)).collect())
}

pub fn variant_as_value(name: String, v: Value) -> Value {
    make_map(vec![(name, v)])
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Tprim;

    use super::*;
    use crate::typing_defs_core::Ty_;
    use crate::typing_defs_core::mk;

    fn prim(p: Tprim) -> Ty {
        mk((typing_reason::none(), Ty_::Tprim(p)))
    }

    fn atom(s: &str) -> Value {
        string_as_value(s.to_string())
    }

    #[test]
    fn maps() {
        let m = make_map(vec![
            ("b".to_string(), atom("1")),
            ("a".to_string(), bool_as_value(true)),
            ("b".to_string(), atom("2")),
        ]);
        match &m {
            Value::Map(m) => {
                let entries: Vec<(&String, &Value)> = m.iter().collect();
                assert_eq!(entries.len(), 2);
                assert_eq!(entries[0].0, "a");
                assert!(equal_value(entries[0].1, &Value::Bool(true)));
                assert_eq!(entries[1].0, "b");
                // S_map.of_list: the last binding of a key.
                assert!(equal_value(entries[1].1, &atom("2")));
            }
            _ => panic!("expected a map"),
        }
        assert_eq!(
            variant_as_value("TVIType".to_string(), atom("x")),
            make_map(vec![("TVIType".to_string(), atom("x"))])
        );
        // Built from pairs, as the callers do.
        assert_eq!(
            Value::Map(
                [("a".to_string(), atom("1"))]
                    .into_iter()
                    .collect::<s_map::T<Value>>()
            ),
            make_map(vec![("a".to_string(), atom("1"))])
        );
        // The two representations of `S_map.t`.
        let im_map: s_map::T<isize> = [("y".to_string(), 2isize), ("x".to_string(), 1)]
            .into_iter()
            .collect();
        let btree: oxidized::s_map::SMap<isize> = im_map.clone().into_iter().collect();
        let expected = make_map(vec![
            ("x".to_string(), atom("1")),
            ("y".to_string(), atom("2")),
        ]);
        let mut seen = vec![];
        assert_eq!(
            smap_as_value(
                |n: &isize| {
                    seen.push(*n);
                    atom(&n.to_string())
                },
                &im_map
            ),
            expected
        );
        // In the order of the keys.
        assert_eq!(seen, vec![1, 2]);
        assert_eq!(
            smap_as_value(|n: &isize| atom(&n.to_string()), &btree),
            expected
        );
    }

    #[test]
    fn equality() {
        assert_eq!(atom("a"), atom("a"));
        assert_ne!(atom("a"), atom("b"));
        assert_ne!(atom("true"), bool_as_value(true));
        assert_eq!(
            list_as_value(vec![atom("a"), bool_as_value(false)]),
            list_as_value(vec![atom("a"), bool_as_value(false)])
        );
        assert_ne!(list_as_value(vec![atom("a")]), list_as_value(vec![]));
        // Types are compared modulo reasons.
        assert_eq!(
            locl_type_as_value(prim(Tprim::Tint)),
            locl_type_as_value(mk((
                typing_reason::type_variable(Pos::NONE, 3),
                Ty_::Tprim(Tprim::Tint)
            )))
        );
        assert_ne!(
            locl_type_as_value(prim(Tprim::Tint)),
            locl_type_as_value(prim(Tprim::Tfloat))
        );
        assert_eq!(
            subtype_prop_as_value(typing_logic::valid()),
            subtype_prop_as_value(typing_logic::valid())
        );
        assert_ne!(
            subtype_prop_as_value(typing_logic::valid()),
            subtype_prop_as_value(typing_logic::invalid(None))
        );
        assert_ne!(
            make_map(vec![("a".to_string(), atom("1"))]),
            make_map(vec![("b".to_string(), atom("1"))])
        );
        assert_ne!(
            make_map(vec![("a".to_string(), atom("1"))]),
            make_map(vec![("a".to_string(), atom("2"))])
        );
    }

    #[test]
    fn variables_and_locals() {
        assert_eq!(var_as_string(12), "#12");
        let mut vars = tvid::set::Set::new();
        vars.insert(10);
        vars.insert(2);
        match varset_as_value(&vars) {
            Value::Set(s) => {
                // A set of strings: "#10" comes before "#2".
                assert_eq!(
                    s.into_iter().collect::<Vec<String>>(),
                    vec!["#10".to_string(), "#2".to_string()]
                );
            }
            _ => panic!("expected a set"),
        }
        let x: local_id::T = local_id::make(3, "$x");
        assert_eq!(local_id_as_string(&x), "$x[#3]");
        let y = local_id::make_unscoped("$y");
        assert_eq!(local_id_as_string(&y), "$y[#0]");
        let im_set: local_id::set::T = [x.clone(), y.clone()].into_iter().collect();
        let btree: oxidized::local_id::set::Set = [x, y].into_iter().collect();
        let expected: s_set::T = ["$x[#3]".to_string(), "$y[#0]".to_string()]
            .into_iter()
            .collect();
        assert_eq!(local_id_set_as_value(&im_set), Value::Set(expected.clone()));
        assert_eq!(local_id_set_as_value(&btree), Value::Set(expected));
    }

    #[test]
    fn internal_type_sets_are_lists_in_the_order_of_the_set() {
        let tys: internal_type_set::T = [
            InternalType::LoclType(prim(Tprim::Tfloat)),
            InternalType::LoclType(prim(Tprim::Tint)),
        ]
        .into_iter()
        .collect();
        let expected: Vec<Value> = internal_type_set::elements(&tys)
            .into_iter()
            .map(Value::Type)
            .collect();
        match internal_type_set_as_value(&tys) {
            Value::List(l) => {
                assert_eq!(l.len(), 2);
                assert_eq!(l, expected);
            }
            _ => panic!("expected a list"),
        }
    }
}
