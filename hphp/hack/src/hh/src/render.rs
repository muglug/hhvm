// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/render.ml`. See `hh/PORTING.md`.
//!
//! The functions that take polymorphic variants in OCaml take the enums
//! below, or anything that converts into them: the callers have their own
//! enums for the subsets of tags they use.


use crate::markdown_lite;

/// ``[ `public | `private_ | `internal | `protected ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vis {
    Public,
    Private,
    Internal,
    Protected,
}

/// ``[ `extend | `implement | `use ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verb {
    Extend,
    Implement,
    Use,
}

/// ``[ `class_constant | `static_method | `class_variable | `class_typeconst
/// | `method_ | `property ]``
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassMemberKind {
    ClassConstant,
    StaticMethod,
    ClassVariable,
    ClassTypeconst,
    Method,
    Property,
}

pub fn strip_ns(id: &str) -> &str {
    crate::hh_autoimport::strip_hh_namespace_if_autoimport(crate::utils::strip_ns(id))
}

pub fn vis_to_string(vis: impl Into<Vis>) -> String {
    match vis.into() {
        Vis::Public => "public",
        Vis::Private => "private",
        Vis::Internal => "internal",
        Vis::Protected => "protected",
    }
    .to_string()
}

pub fn verb_to_string(verb: impl Into<Verb>) -> String {
    match verb.into() {
        Verb::Extend => "extend",
        Verb::Implement => "implement",
        Verb::Use => "use",
    }
    .to_string()
}

pub fn string_of_class_member_kind(kind: impl Into<ClassMemberKind>) -> String {
    match kind.into() {
        ClassMemberKind::ClassConstant => "class constant",
        ClassMemberKind::StaticMethod => "static method",
        ClassMemberKind::ClassVariable => "class variable",
        ClassMemberKind::ClassTypeconst => "type constant",
        ClassMemberKind::Method => "method",
        ClassMemberKind::Property => "property",
    }
    .to_string()
}

/// Given two equal-length strings, highlights the characters in
/// the second that differ from the first
///
/// (Characters are bytes, as in OCaml. The callers compare names that are
/// equal up to the case of ASCII letters, so the highlighted runs are whole
/// characters.)
pub fn highlight_differences(base: &str, to_highlight: &str) -> String {
    let base = base.as_bytes();
    let bytes = to_highlight.as_bytes();
    // `List.zip`: `Unequal_lengths`
    if base.len() != bytes.len() {
        return to_highlight.to_string();
    }
    // `List.group ~break`: runs of characters that are all the same as in
    // `base`, or all different.
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut start = 0;
    while start < bytes.len() {
        let same = base[start] == bytes[start];
        let mut end = start + 1;
        while end < bytes.len() && (base[end] == bytes[end]) == same {
            end += 1;
        }
        if same {
            out.extend_from_slice(&bytes[start..end]);
        } else {
            // `Markdown_lite.md_highlight`
            out.extend_from_slice(b"~~");
            out.extend_from_slice(&bytes[start..end]);
            out.extend_from_slice(b"~~");
        }
        start = end;
    }
    match String::from_utf8(out) {
        Ok(s) => s,
        Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
    }
}

/// `modifier` defaults to `""`.
pub fn suggestion_message<P>(
    modifier: Option<&str>,
    orig: &str,
    hint: &str,
    hint_pos: P,
) -> (P, String) {
    let modifier = modifier.unwrap_or("");
    let s = if orig != hint && orig.to_ascii_lowercase() == hint.to_ascii_lowercase() {
        format!(
            "Did you mean {}{} instead (which only differs by case)?",
            modifier,
            markdown_lite::md_codify(&highlight_differences(orig, hint))
        )
    } else {
        format!(
            "Did you mean {}{} instead?",
            modifier,
            markdown_lite::md_codify(hint)
        )
    };
    (hint_pos, s)
}

pub fn pluralize_arguments(n: isize) -> String {
    format!("{}{}", n, if n == 1 { " argument" } else { " arguments" })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip() {
        assert_eq!(strip_ns("\\Foo\\Bar"), "Foo\\Bar");
        assert_eq!(strip_ns("\\HH\\vec"), "vec");
        assert_eq!(strip_ns("HH\\Traversable"), "Traversable");
        assert_eq!(strip_ns("\\HH\\Lib\\Vec"), "HH\\Lib\\Vec");
        assert_eq!(strip_ns("\\HH\\class_or_classname"), "HH\\class_or_classname");
        // One backslash, then one `HH\`.
        assert_eq!(strip_ns("\\\\HH\\vec"), "\\HH\\vec");
        assert_eq!(strip_ns("\\HH\\HH\\vec"), "HH\\HH\\vec");
        assert_eq!(strip_ns(""), "");
    }

    #[test]
    fn variants() {
        assert_eq!(vis_to_string(Vis::Private), "private");
        assert_eq!(vis_to_string(Vis::Internal), "internal");
        assert_eq!(verb_to_string(Verb::Use), "use");
        assert_eq!(verb_to_string(Verb::Implement), "implement");
        assert_eq!(
            string_of_class_member_kind(ClassMemberKind::ClassTypeconst),
            "type constant"
        );
        assert_eq!(
            string_of_class_member_kind(ClassMemberKind::ClassVariable),
            "class variable"
        );
        assert_eq!(string_of_class_member_kind(ClassMemberKind::Method), "method");
    }

    #[test]
    fn highlight() {
        // As in the expected output of hphp/hack/test/typecheck/capitalization1.php
        assert_eq!(
            highlight_differences("camelcase", "CamelCase"),
            "~~C~~amel~~C~~ase"
        );
        assert_eq!(
            highlight_differences("CAMELCASE", "CamelCase"),
            "C~~amel~~C~~ase~~"
        );
        assert_eq!(
            highlight_differences("cAMELcASE", "CamelCase"),
            "~~CamelCase~~"
        );
        assert_eq!(highlight_differences("abc", "abc"), "abc");
        assert_eq!(highlight_differences("abc", "abcd"), "abcd");
        assert_eq!(highlight_differences("", ""), "");
    }

    #[test]
    fn suggestion() {
        assert_eq!(
            suggestion_message(None, "foo", "bar", 1),
            (1, "Did you mean `bar` instead?".to_string())
        );
        assert_eq!(
            suggestion_message(None, "camelcase", "CamelCase", ()),
            (
                (),
                "Did you mean `~~C~~amel~~C~~ase` instead (which only differs by case)?"
                    .to_string()
            )
        );
        assert_eq!(
            suggestion_message(Some("instance method "), "foo", "Foo", ()).1,
            "Did you mean instance method `~~F~~oo` instead (which only differs by case)?"
        );
        assert_eq!(
            suggestion_message(Some("static method "), "foo", "bar", ()).1,
            "Did you mean static method `bar` instead?"
        );
        // The same name is not a name that differs by case.
        assert_eq!(
            suggestion_message(None, "foo", "foo", ()).1,
            "Did you mean `foo` instead?"
        );
    }

    #[test]
    fn pluralize() {
        assert_eq!(pluralize_arguments(0), "0 arguments");
        assert_eq!(pluralize_arguments(1), "1 argument");
        assert_eq!(pluralize_arguments(2), "2 arguments");
        assert_eq!(pluralize_arguments(-1), "-1 arguments");
    }
}
