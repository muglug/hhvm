// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `annotated_ast/aast.ml`. See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::aast`, re-exported here. This module
//! has the functions of `aast.ml` that `oxidized` lacks and that the port has
//! needed so far (`split_methods`, `split_vars`, `split_reqs`,
//! `hint_of_type_hint`, `enum_includes_map`).
//!
//! The OCaml returns the members it splits (values are shared); here they are
//! references into the list it is given.

pub use oxidized::aast::*;

/// Splits the methods on a class into the constructor, statics, dynamics
///
/// Methods, properties, and requirements are order dependent in bytecode
/// emission, which is observable in user code via `ReflectionClass`.
pub fn split_methods<Ex, En>(
    c_methods: &[Method_<Ex, En>],
) -> (
    Option<&Method_<Ex, En>>,
    Vec<&Method_<Ex, En>>,
    Vec<&Method_<Ex, En>>,
) {
    let mut constr = None;
    let mut statics = vec![];
    let mut rest = vec![];
    for m in c_methods {
        if m.name.1 == "__construct" {
            constr = Some(m)
        } else if m.static_ {
            statics.push(m)
        } else {
            rest.push(m)
        }
    }
    (constr, statics, rest)
}

/// Splits class properties into statics, dynamics
pub fn split_vars<Ex, En>(
    c_vars: &[ClassVar<Ex, En>],
) -> (Vec<&ClassVar<Ex, En>>, Vec<&ClassVar<Ex, En>>) {
    let mut statics = vec![];
    let mut rest = vec![];
    for v in c_vars {
        if v.is_static {
            statics.push(v)
        } else {
            rest.push(v)
        }
    }
    (statics, rest)
}

/// Splits `require`s into extends, implements, class, constraint
pub fn split_reqs(c_reqs: &[ClassReq]) -> (Vec<&Hint>, Vec<&Hint>, Vec<&Hint>, Vec<&Hint>) {
    let mut extends = vec![];
    let mut implements = vec![];
    let mut class_ = vec![];
    let mut this_as = vec![];
    for ClassReq(h, require_kind) in c_reqs {
        match require_kind {
            RequireKind::RequireExtends => extends.push(h),
            RequireKind::RequireImplements => implements.push(h),
            RequireKind::RequireClass => class_.push(h),
            RequireKind::RequireThisAs => this_as.push(h),
        }
    }
    (extends, implements, class_, this_as)
}

/// extract the hint from a type annotation
pub fn hint_of_type_hint<Ex>(th: &TypeHint<Ex>) -> &TypeHint_ {
    &th.1
}

/// helper function to access the list of enums included by an enum
pub fn enum_includes_map<A>(
    default: Option<Vec<A>>,
    f: impl FnOnce(&Enum_) -> Vec<A>,
    includes: Option<&Enum_>,
) -> Vec<A> {
    let default = default.unwrap_or_default();
    match includes {
        None => default,
        Some(includes) => f(includes),
    }
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::Id;
    use oxidized::pos::Pos;

    use super::*;

    fn hint(name: &str) -> Hint {
        Hint(
            Pos::NONE,
            Box::new(Hint_::Happly(Id(Pos::NONE, name.to_string()), vec![])),
        )
    }

    fn name(h: &Hint) -> &str {
        match &*h.1 {
            Hint_::Happly(Id(_, n), _) => n,
            _ => panic!(),
        }
    }

    #[test]
    fn split_reqs_keeps_order() {
        let reqs = vec![
            ClassReq(hint("A"), RequireKind::RequireExtends),
            ClassReq(hint("I"), RequireKind::RequireImplements),
            ClassReq(hint("B"), RequireKind::RequireExtends),
            ClassReq(hint("C"), RequireKind::RequireClass),
            ClassReq(hint("T"), RequireKind::RequireThisAs),
        ];
        let (extends, implements, class_, this_as) = split_reqs(&reqs);
        assert_eq!(
            extends.iter().map(|h| name(h)).collect::<Vec<_>>(),
            ["A", "B"]
        );
        assert_eq!(
            implements.iter().map(|h| name(h)).collect::<Vec<_>>(),
            ["I"]
        );
        assert_eq!(class_.iter().map(|h| name(h)).collect::<Vec<_>>(), ["C"]);
        assert_eq!(this_as.iter().map(|h| name(h)).collect::<Vec<_>>(), ["T"]);
    }

    #[test]
    fn enum_includes_map_default() {
        let r: Vec<isize> = enum_includes_map(None, |_| vec![1], None);
        assert!(r.is_empty());
        let r: Vec<isize> = enum_includes_map(Some(vec![2]), |_| vec![1], None);
        assert_eq!(r, vec![2]);
    }
}
