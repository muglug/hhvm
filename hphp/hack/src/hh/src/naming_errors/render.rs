// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The helpers messages are built with: `Render`, `Markdown_lite` and the
//! name-stripping functions of `Utils` in `hh_server`.

use oxidized::name_context::NameContext;
use oxidized::pos::Pos;

/// `Markdown_lite.md_codify`
pub fn md_codify(s: &str) -> String {
    format!("`{}`", s)
}

/// `Markdown_lite.md_highlight`
fn md_highlight(s: &str) -> String {
    format!("~~{}~~", s)
}

/// `Utils.strip_ns`: `\A\B\C` -> `A\B\C`
pub fn utils_strip_ns(s: &str) -> &str {
    s.strip_prefix('\\').unwrap_or(s)
}

/// `Utils.strip_all_ns`: `\A\B\C` -> `C`
pub fn strip_all_ns(s: &str) -> &str {
    match s.rfind('\\') {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

/// `Hh_autoimport.is_hh_autoimport`: whether `s` is one of
/// `Hh_autoimport.types`.
///
/// The list of the `hh_autoimport_rust` crate is the one of `hh_autoimport.ml`
/// plus `class_or_classname`, which OCaml does not strip (the expected outputs
/// have `HH\class_or_classname<C>`).
fn is_hh_autoimport(s: &str) -> bool {
    hh_autoimport::is_hh_autoimport(s) && s != "class_or_classname"
}

/// `Hh_autoimport.strip_HH_namespace_if_autoimport`
fn strip_hh_namespace_if_autoimport(id: &str) -> &str {
    match id.strip_prefix("HH\\") {
        Some(stripped) if is_hh_autoimport(stripped) => stripped,
        _ => id,
    }
}

/// `Render.strip_ns`
pub fn strip_ns(id: &str) -> &str {
    strip_hh_namespace_if_autoimport(utils_strip_ns(id))
}

/// `Render.highlight_differences`: given two equal-length strings, highlight
/// the characters of the second that differ from the first.
pub(crate) fn highlight_differences(base: &str, to_highlight: &str) -> String {
    let base = base.as_bytes();
    let bytes = to_highlight.as_bytes();
    if base.len() != bytes.len() {
        return to_highlight.to_string();
    }
    // Runs of bytes that are all the same as in `base`, or all different.
    // (Bytes, as in OCaml. The only caller compares strings that are equal up
    // to the case of ASCII letters, so a run never ends inside a character.)
    let mut out = Vec::with_capacity(bytes.len());
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
            out.extend_from_slice(b"~~");
            out.extend_from_slice(&bytes[start..end]);
            out.extend_from_slice(b"~~");
        }
        start = end;
    }
    String::from_utf8(out).unwrap_or_else(|_| md_highlight(to_highlight))
}

/// `Render.suggestion_message` (without a modifier)
pub fn suggestion_message(orig: &str, hint: &str, hint_pos: Pos) -> (Pos, String) {
    let msg = if orig != hint && orig.to_ascii_lowercase() == hint.to_ascii_lowercase() {
        format!(
            "Did you mean {} instead (which only differs by case)?",
            md_codify(&highlight_differences(orig, hint))
        )
    } else {
        format!("Did you mean {} instead?", md_codify(hint))
    };
    (hint_pos, msg)
}

/// `Render.pluralize_arguments`
pub fn pluralize_arguments(n: isize) -> String {
    format!("{}{}", n, if n == 1 { " argument" } else { " arguments" })
}

/// `Name_context.to_string`
pub fn name_context_to_string(kind: NameContext) -> &'static str {
    match kind {
        NameContext::FunctionNamespace => "function",
        NameContext::ConstantNamespace => "constant",
        NameContext::TypeNamespace => "type",
        NameContext::TraitContext => "trait",
        NameContext::ClassContext => "class",
        NameContext::ModuleNamespace => "module",
        NameContext::PackageNamespace => "package",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strip() {
        assert_eq!(strip_ns("\\Foo\\Bar"), "Foo\\Bar");
        assert_eq!(strip_ns("\\HH\\vec"), "vec");
        assert_eq!(strip_ns("\\HH\\Lib\\Vec"), "HH\\Lib\\Vec");
        assert_eq!(strip_ns("HH\\Traversable"), "Traversable");
        assert_eq!(
            strip_ns("\\HH\\class_or_classname"),
            "HH\\class_or_classname"
        );
        assert_eq!(strip_all_ns("\\Foo\\Bar"), "Bar");
        assert_eq!(strip_all_ns("Bar"), "Bar");
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
        assert_eq!(highlight_differences("abc", "abcd"), "abcd");
    }
}
