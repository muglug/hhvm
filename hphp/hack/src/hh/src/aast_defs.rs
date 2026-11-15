// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `annotated_ast/aast_defs.ml`. See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::aast_defs`, re-exported here. This
//! module has the functions of `aast_defs.ml`, and the `[@@deriving]`
//! functions that the typechecker calls by name (`equal_*`, `compare_*`; the
//! types have the same constructors in the same order, so the derived
//! orders are the same).
//!
//! Not here: the `show_*` functions other than `show_class_name` and
//! `show_check_status` (`show_hint_`, `show_stmt_`: the `[@@deriving show]`
//! of AST types, laid out by OCaml's `Format`), and `compare_hint` (whose positions compare as `Pos.t` does in
//! OCaml, which `oxidized::pos::Pos` does not do for every position).

pub use oxidized::aast_defs::*;
use oxidized::ast_defs::Variance;

pub fn string_of_tprim(prim: Tprim) -> String {
    match prim {
        Tprim::Tnull => "null",
        Tprim::Tvoid => "void",
        Tprim::Tint => "int",
        Tprim::Tnum => "num",
        Tprim::Tfloat => "float",
        Tprim::Tarraykey => "arraykey",
        Tprim::Tresource => "resource",
        Tprim::Tnoreturn => "noreturn",
        Tprim::Tbool => "bool",
    }
    .to_string()
}

pub fn string_of_visibility(vis: Visibility) -> String {
    match vis {
        Visibility::Private => "private",
        Visibility::Public => "public",
        Visibility::Protected => "protected",
        Visibility::Internal => "internal",
        Visibility::ProtectedInternal => "protected internal",
    }
    .to_string()
}

pub fn is_wildcard_hint(h: &Hint) -> bool {
    match h {
        Hint(_, hint_) => matches!(**hint_, Hint_::Hwildcard),
    }
}

pub fn tparam_of_hint_tparam<Ex, En>(hint_tparam: &HintTparam) -> Tparam<Ex, En> {
    let HintTparam {
        name: htp_name,
        user_attributes: htp_user_attributes,
        constraints: htp_constraints,
    } = hint_tparam;
    Tparam {
        variance: Variance::Invariant,
        name: htp_name.clone(),
        constraints: htp_constraints.clone(),
        reified: ReifyKind::Erased,
        user_attributes: UserAttributes(
            htp_user_attributes
                .iter()
                .map(|ua_name| UserAttribute {
                    name: ua_name.clone(),
                    params: vec![],
                })
                .collect(),
        ),
    }
}

/// `[@@deriving eq]`
pub fn equal_visibility(a: Visibility, b: Visibility) -> bool {
    a == b
}

/// `[@@deriving eq]`
pub fn equal_tprim(a: Tprim, b: Tprim) -> bool {
    a == b
}

/// `[@@deriving ord]`: in the order of the constructors.
pub fn compare_tprim(a: Tprim, b: Tprim) -> std::cmp::Ordering {
    a.cmp(&b)
}

/// `[@@deriving ord]`: in the order of the constructors.
pub fn compare_reify_kind(a: ReifyKind, b: ReifyKind) -> std::cmp::Ordering {
    a.cmp(&b)
}


/// `class_name = sid = Ast_defs.id`, printed by `Ast_defs.pp_id`.
pub fn show_class_name(cls: &ClassName) -> String {
    crate::ast_defs::show_id(cls)
}

/// The `[@@deriving show]` of `check_status`, which prints the constructor
/// qualified by the module that defines it (`Tast.show_check_status` too).
pub fn show_check_status(check_status: &CheckStatus) -> String {
    match check_status {
        CheckStatus::COnce => "Aast_defs.COnce",
        CheckStatus::CUnderNormalAssumptions => "Aast_defs.CUnderNormalAssumptions",
        CheckStatus::CUnderDynamicAssumptions => "Aast_defs.CUnderDynamicAssumptions",
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use oxidized::ast_defs::ConstraintKind;
    use oxidized::ast_defs::Id;
    use oxidized::pos::Pos;

    use super::*;

    #[test]
    fn strings() {
        let all = [
            Tprim::Tnull,
            Tprim::Tvoid,
            Tprim::Tint,
            Tprim::Tbool,
            Tprim::Tfloat,
            Tprim::Tresource,
            Tprim::Tnum,
            Tprim::Tarraykey,
            Tprim::Tnoreturn,
        ];
        assert_eq!(
            all.map(string_of_tprim).join(" "),
            "null void int bool float resource num arraykey noreturn"
        );
        assert_eq!(
            string_of_visibility(Visibility::ProtectedInternal),
            "protected internal"
        );
        assert_eq!(string_of_visibility(Visibility::Internal), "internal");
        // In the order of the OCaml constructors.
        assert_eq!(
            compare_tprim(Tprim::Tbool, Tprim::Tfloat),
            std::cmp::Ordering::Less
        );
        assert_eq!(
            compare_tprim(Tprim::Tnum, Tprim::Tresource),
            std::cmp::Ordering::Greater
        );
        assert_eq!(
            compare_reify_kind(ReifyKind::Erased, ReifyKind::SoftReified),
            std::cmp::Ordering::Less
        );
        assert!(equal_tprim(Tprim::Tint, Tprim::Tint));
        assert!(!equal_visibility(Visibility::Public, Visibility::Private));
    }

    #[test]
    fn hints() {
        let hint = |h| Hint(Pos::NONE, Box::new(h));
        assert!(is_wildcard_hint(&hint(Hint_::Hwildcard)));
        assert!(!is_wildcard_hint(&hint(Hint_::Hmixed)));

        let id = |s: &str| Id(Pos::NONE, s.to_string());
        let htp = HintTparam {
            name: id("T"),
            user_attributes: vec![id("__Enforceable"), id("__Newable")],
            constraints: vec![(ConstraintKind::ConstraintAs, hint(Hint_::Hmixed))],
        };
        let tp: Tparam<(), ()> = tparam_of_hint_tparam(&htp);
        assert_eq!(tp.variance, Variance::Invariant);
        assert_eq!(tp.name, id("T"));
        assert_eq!(tp.constraints, htp.constraints);
        assert_eq!(tp.reified, ReifyKind::Erased);
        assert_eq!(
            tp.user_attributes.0,
            vec![
                UserAttribute {
                    name: id("__Enforceable"),
                    params: vec![]
                },
                UserAttribute {
                    name: id("__Newable"),
                    params: vec![]
                },
            ]
        );
    }

    #[test]
    fn shows() {
        assert_eq!(
            crate::ast_defs::show_id(&crate::ast_defs::Id(
                oxidized::pos::Pos::NONE,
                "\\M\"".to_string()
            )),
            "([Pos.none], \"\\\\M\\\"\")"
        );
        assert_eq!(
            show_check_status(&CheckStatus::CUnderDynamicAssumptions),
            "Aast_defs.CUnderDynamicAssumptions"
        );
    }
}
