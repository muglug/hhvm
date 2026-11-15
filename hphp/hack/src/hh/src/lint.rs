// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lint/lint.ml`. See `hh/PORTING.md`.
//!
//! This is `utils/lint/lint.ml`: lints reported through `Lints_core`.

use oxidized::pos::Pos;

use crate::lint_codes as codes;
use crate::lints_core::Severity::LintError;
use crate::lints_core::Severity::LintWarning;
use crate::lints_core::add;
use crate::markdown_lite::md_codify;

pub fn internal_error(pos: Pos, msg: &str) {
    add(
        None,
        None,
        None,
        0,
        LintError,
        pos,
        format!("Internal error: {}", msg),
    )
}

pub fn use_collection_literal(pos: Pos, coll: &str) {
    let coll = crate::utils::strip_ns(coll);
    add(
        None,
        None,
        None,
        codes::to_enum(codes::T::UseCollectionLiteral),
        LintWarning,
        pos,
        format!(
            "Use {} instead of {}",
            md_codify(&format!("{} {{...}}", coll)),
            md_codify(&format!("new {}(...)", coll))
        ),
    )
}

pub fn static_string(no_consts: Option<bool>, pos: Pos) {
    let no_consts = no_consts.unwrap_or(false);
    add(
        None,
        None,
        None,
        codes::to_enum(codes::T::StaticString),
        LintWarning,
        pos,
        if no_consts {
            "This should be a string literal so that lint can analyze it.".to_string()
        } else {
            format!(
                "{}{}",
                "This should be a string literal or string constant so that lint can ",
                "analyze it."
            )
        },
    )
}

pub fn shape_idx_access_required_field(field_pos: Pos, name: &str) {
    add(
        None,
        None,
        None,
        codes::to_enum(codes::T::ShapeIdxRequiredField),
        LintWarning,
        field_pos,
        format!(
            "The field {} is required to exist in the shape. Consider using a subscript-expression instead, such as {}",
            md_codify(name),
            md_codify(&format!("$myshape['{}']", name))
        ),
    )
}

pub fn option_mixed(pos: Pos) {
    add(
        None,
        None,
        None,
        codes::to_enum(codes::T::OptionMixed),
        LintWarning,
        pos,
        "`?mixed` is a redundant typehint - just use `mixed`".to_string(),
    )
}

pub fn option_null(pos: Pos) {
    add(
        None,
        None,
        None,
        codes::to_enum(codes::T::OptionNull),
        LintWarning,
        pos,
        "`?null` is a redundant typehint - just use `null`".to_string(),
    )
}

pub fn class_const_to_string(pos: Pos, cid_str: &str) {
    let cid_str = crate::utils::strip_ns(cid_str);
    let nameof = format!("nameof {}", cid_str);
    let nameof_md = md_codify(&nameof);
    let autofix = Some((nameof, pos.clone()));
    add(
        None,
        None,
        Some(autofix),
        codes::to_enum(codes::T::ClassPointerToString),
        LintWarning,
        pos,
        format!(
            "Using `{}::class` in this position will trigger an implicit runtime conversion to string, please use {}",
            cid_str, nameof_md
        ),
    )
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::lints_core;

    fn pos() -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        Pos::from_lnum_bol_offset(file, (1, 0, 3), (1, 0, 8))
    }

    #[test]
    fn messages() {
        let (lints, ()) = lints_core::do_(|| {
            option_null(pos());
            shape_idx_access_required_field(pos(), "x");
            class_const_to_string(pos(), "\\N\\C");
            use_collection_literal(pos(), "\\HH\\Vector");
        });
        let got: Vec<_> = lints
            .iter()
            .map(|l| (l.code, l.message.as_str(), l.autofix.as_ref().map(|(s, _)| s.as_str())))
            .collect();
        assert_eq!(
            got,
            vec![
                (
                    5002,
                    "Use `HH\\Vector {...}` instead of `new HH\\Vector(...)`",
                    None
                ),
                (
                    5005,
                    "The field `x` is required to exist in the shape. Consider using a subscript-expression instead, such as `$myshape['x']`",
                    None
                ),
                (
                    5009,
                    "`?null` is a redundant typehint - just use `null`",
                    None
                ),
                (
                    5010,
                    "Using `N\\C::class` in this position will trigger an implicit runtime conversion to string, please use `nameof N\\C`",
                    Some("nameof N\\C")
                ),
            ]
        );
    }
}
