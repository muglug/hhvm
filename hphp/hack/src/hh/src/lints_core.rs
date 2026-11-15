// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `lints/lints_core.ml`. See `hh/PORTING.md`.
//!
//! The lints being collected (`lint_list`) are global state in OCaml, where a
//! worker is a process; here they belong to the thread, like the errors of
//! `crate::diagnostics` (a file is checked on one thread).
//!
//! `utils/lint/lint.rs` (crate `lint_rust`) has a Rust copy of these types,
//! made by `hh_oxidize` for the parser (whose lints are `lint_rust::LintError`).
//! These are the port's own (`Severity::LintWarning` is the OCaml
//! `Lint_warning`), which `crate::typing_warning_utils` uses.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::BTreeMap;

use oxidized::pos::Pos;

use crate::tast::CheckStatus;
use crate::yojson::safe as yojson;

/// These severity levels are based on those provided by Arcanist:
/// - Error: when it fires, it will require confirmation
/// - Warning: when it fires, it shows up visibly before landing
/// - Advice: Similar to warning, but implies lesser severity
/// - Disabled: Hidden from most UI, but it is useful for telemetry
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum Severity {
    LintError,
    LintWarning,
    LintAdvice,
    LintDisabled,
}

pub fn string_of_severity(severity: Severity) -> String {
    match severity {
        Severity::LintError => "error",
        Severity::LintWarning => "warning",
        Severity::LintAdvice => "advice",
        Severity::LintDisabled => "disabled",
    }
    .to_string()
}

/// `'pos t` (serde: the result of `LINT` crosses the socket; E2)
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct T<P> {
    /// Determines ordering (1st priority)
    pub code: isize,
    pub severity: Severity,
    /// Determines ordering (2nd priority)
    pub pos: P,
    /// Determines ordering (3rd priority)
    pub message: String,
    /// Normally, lint warnings and lint advice only get shown by arcanist if the
    /// lines they are raised on overlap with lines changed in a diff. This
    /// flag bypasses that behavior
    pub bypass_changed_lines: bool,
    pub autofix: Option<(String, Pos)>,
    pub check_status: Option<CheckStatus>,
}

/// Code, position, and message imply the rest of the fields
fn compare_lint(a: &T<Pos>, b: &T<Pos>) -> Ordering {
    match a.code.cmp(&b.code) {
        Ordering::Equal => match crate::pos::compare(&a.pos, &b.pos) {
            Ordering::Equal => a.message.cmp(&b.message),
            n => n,
        },
        n => n,
    }
}

thread_local! {
    /// `lint_list`. The vector holds the OCaml list from its last element to
    /// its head: `lint :: lst` pushes `lint`. A global ref of the worker
    /// process in OCaml (`lints/lints_core.ml`); one per thread here, since a
    /// file is linted on one thread.
    static LINT_LIST: RefCell<Option<Vec<T<Pos>>>> = const { RefCell::new(None) };
}

pub fn get_code<P>(t: &T<P>) -> isize {
    t.code
}

pub fn get_pos<P: Clone>(t: &T<P>) -> P {
    t.pos.clone()
}

pub fn add(
    check_status: Option<Option<CheckStatus>>,
    bypass_changed_lines: Option<bool>,
    autofix: Option<Option<(String, Pos)>>,
    code: isize,
    severity: Severity,
    pos: Pos,
    message: String,
) {
    let check_status = check_status.unwrap_or(None);
    let bypass_changed_lines = bypass_changed_lines.unwrap_or(false);
    let autofix = autofix.unwrap_or(None);
    LINT_LIST.with_borrow_mut(|lint_list| match lint_list {
        Some(lst) => {
            let lint = T {
                code,
                severity,
                pos,
                message,
                bypass_changed_lines,
                autofix,
                check_status,
            };
            lst.push(lint)
        }
        // by default, we ignore lint errors
        None => {}
    })
}

/// `add_lint lint`: as OCaml, this does not pass on `check_status`.
pub fn add_lint(lint: T<Pos>) {
    let T {
        code,
        severity,
        pos,
        message,
        bypass_changed_lines,
        autofix,
        check_status: _,
    } = lint;
    add(
        None,
        Some(bypass_changed_lines),
        Some(autofix),
        code,
        severity,
        pos,
        message,
    )
}

pub fn to_absolute(lint: T<Pos>) -> T<crate::pos::Absolute> {
    let T {
        code,
        severity,
        pos,
        message,
        bypass_changed_lines,
        autofix,
        check_status,
    } = lint;
    T {
        code,
        severity,
        pos: crate::pos::to_absolute(&pos),
        message,
        bypass_changed_lines,
        autofix,
        check_status,
    }
}

pub fn to_string(lint: &T<crate::pos::Absolute>) -> String {
    let code = crate::user_diagnostic::error_code_to_string(lint.code);
    format!(
        "{}\n{} ({})",
        crate::pos::string(&lint.pos),
        lint.message,
        code
    )
}

/// `User_diagnostic.make_absolute (User_diagnostic.Warning { is_trusted = true })
/// lint.code [(lint.pos, lint.message)]`
#[cfg(feature = "server")]
fn make_absolute_warning(
    lint: &T<crate::pos::Absolute>,
) -> crate::user_diagnostic::T<crate::pos::Absolute, crate::pos::Absolute> {
    crate::user_diagnostic::make_absolute(
        crate::user_diagnostic::Severity::Warning { is_trusted: true },
        lint.code,
        vec![oxidized::message::Message(
            lint.pos.clone(),
            bstr::BString::from(lint.message.as_str()),
        )],
    )
}

/// The formatters (`Contextual_diagnostic_formatter`,
/// `Highlighted_diagnostic_formatter`) are compiled with the feature
/// `server` only: without it, these two are `todo!`.
pub fn to_contextual_string(lint: &T<crate::pos::Absolute>) -> String {
    let claim_color = match lint.severity {
        Severity::LintError => crate::tty::RawColor::Red,
        Severity::LintWarning => crate::tty::RawColor::Yellow,
        Severity::LintAdvice | Severity::LintDisabled => crate::tty::RawColor::Default,
    };
    #[cfg(feature = "server")]
    {
        crate::contextual_diagnostic_formatter::to_string(
            Some(claim_color),
            &make_absolute_warning(lint),
        )
    }
    #[cfg(not(feature = "server"))]
    {
        let _ = claim_color;
        todo!(
            "Lints_core.to_contextual_string: Contextual_diagnostic_formatter is compiled with the feature `server` only"
        )
    }
}

pub fn to_plain_highlighted_string(
    source: Option<String>,
    lint: &T<crate::pos::Absolute>,
) -> String {
    #[cfg(feature = "server")]
    {
        crate::plain_highlighted_diagnostic_formatter::to_string_with_source(
            source,
            &make_absolute_warning(lint),
        )
    }
    #[cfg(not(feature = "server"))]
    {
        let _ = (source, lint);
        todo!(
            "Lints_core.to_plain_highlighted_string: Plain_highlighted_diagnostic_formatter is compiled with the feature `server` only"
        )
    }
}

pub fn to_highlighted_string(lint: &T<crate::pos::Absolute>) -> String {
    #[cfg(feature = "server")]
    {
        crate::highlighted_diagnostic_formatter::to_string(&make_absolute_warning(lint))
    }
    #[cfg(not(feature = "server"))]
    {
        let _ = lint;
        todo!(
            "Lints_core.to_highlighted_string: Highlighted_diagnostic_formatter is compiled with the feature `server` only"
        )
    }
}

pub fn to_json(lint: &T<crate::pos::Absolute>) -> yojson::T {
    let T {
        pos,
        code,
        severity,
        message,
        bypass_changed_lines,
        autofix,
        ..
    } = lint;
    let (line, scol, ecol) = crate::pos::info_pos(pos);
    let (origin, replacement, start, w) = match autofix {
        Some((replacement, replacement_pos)) => {
            let path = crate::pos::filename(&crate::pos::to_absolute(replacement_pos));
            let lines = crate::diagnostics::read_lines(&path);
            let src = lines.join("\n");
            let original = crate::pos::get_text_from_pos(&src, replacement_pos);
            let (start_offset, end_offset) = crate::pos::info_raw(replacement_pos);
            let width = end_offset - start_offset;
            (
                yojson::T::String(original),
                yojson::T::String(replacement.clone()),
                yojson::T::Int(start_offset),
                yojson::T::Int(width),
            )
        }
        None => (
            yojson::T::String(String::new()),
            yojson::T::String(String::new()),
            yojson::T::Null,
            yojson::T::Null,
        ),
    };
    yojson::T::Assoc(vec![
        ("descr".to_string(), yojson::T::String(message.clone())),
        (
            "severity".to_string(),
            yojson::T::String(string_of_severity(*severity)),
        ),
        (
            "path".to_string(),
            yojson::T::String(crate::pos::filename(pos)),
        ),
        ("line".to_string(), yojson::T::Int(line)),
        ("start".to_string(), yojson::T::Int(scol)),
        ("end".to_string(), yojson::T::Int(ecol)),
        ("code".to_string(), yojson::T::Int(*code)),
        (
            "bypass_changed_lines".to_string(),
            yojson::T::Bool(*bypass_changed_lines),
        ),
        ("original".to_string(), origin),
        ("replacement".to_string(), replacement),
        ("start_offset".to_string(), start),
        ("width".to_string(), w),
    ])
}

/// `type t = int * Pos.t [@@deriving ord]`, the key of `LintMap`
/// (`Wrapped_map.Make`): by code, then by position (`Pos.compare`).
#[derive(Clone, Debug)]
struct LintMapKey(isize, Pos);

impl PartialEq for LintMapKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for LintMapKey {}

impl PartialOrd for LintMapKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LintMapKey {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Equal => crate::pos::compare(&self.1, &other.1),
            n => n,
        }
    }
}

/// `module CheckStatusParity`
mod check_status_parity {
    #[derive(Clone, Copy, Debug)]
    pub struct T {
        pub under_normal_assumptions: bool,
        pub under_dynamic_assumptions: bool,
    }

    pub const DEFAULT: T = T {
        under_normal_assumptions: false,
        under_dynamic_assumptions: false,
    };

    pub fn set_normal(parity_opt: Option<T>) -> Option<T> {
        let set = |parity: T| {
            Some(T {
                under_normal_assumptions: true,
                ..parity
            })
        };
        set(parity_opt.unwrap_or(DEFAULT))
    }

    pub fn set_dynamic(parity_opt: Option<T>) -> Option<T> {
        let set = |parity: T| {
            Some(T {
                under_dynamic_assumptions: true,
                ..parity
            })
        };
        set(parity_opt.unwrap_or(DEFAULT))
    }

    pub fn is_paired(parity: T) -> bool {
        parity.under_dynamic_assumptions && parity.under_normal_assumptions
    }
}

/// If the check_status field is available in a lint, we expect that the
/// lint is a true positive only if the same lint was produced under both
/// dynamic and normal assumptions. This helper function filters out the
/// remaining ones.
fn filter_out_unsound_lints(lints: Vec<T<Pos>>) -> Vec<T<Pos>> {
    let mut lint_parity: BTreeMap<LintMapKey, check_status_parity::T> = BTreeMap::new();
    for lint in &lints {
        // `LintMap.update (lint.code, lint.pos) f m`
        let mut update = |f: fn(Option<check_status_parity::T>) -> Option<check_status_parity::T>| {
            let key = LintMapKey(lint.code, lint.pos.clone());
            match f(lint_parity.get(&key).copied()) {
                Some(parity) => {
                    lint_parity.insert(key, parity);
                }
                None => {
                    lint_parity.remove(&key);
                }
            }
        };
        match lint.check_status {
            Some(CheckStatus::CUnderNormalAssumptions) => update(check_status_parity::set_normal),
            Some(CheckStatus::CUnderDynamicAssumptions) => {
                update(check_status_parity::set_dynamic)
            }
            _ => {}
        }
    }
    let should_keep_lint = |lint: &T<Pos>| match lint {
        T {
            check_status: Some(CheckStatus::CUnderDynamicAssumptions),
            ..
        } => {
            // There are three cases to consider:
            //   1. we are in any unsound lint rule: this cannot be the case as
            //      `check_status` is set to non-None.
            //   2. we are in a sound lint rule where the lint is only produced under
            //      dynamic assumptions: the result is not reliable, so it should be
            //      eliminated.
            //   3. we are in a sound lint rule where the lint is produced under both
            //      dynamic and normal assumptions: the lint is reliable, but it is
            //      duplicated, so we arbitrarily eliminate the one produced under
            //      dynamic assumptions and keep the one under normal assumptions.
            false
        }
        T { code, pos, .. } => {
            match lint_parity.get(&LintMapKey(*code, pos.clone())) {
                Some(parity) => check_status_parity::is_paired(*parity),
                None => {
                    // Either it was checked once and no parity is needed or is a lint that
                    // doesn't use sound linting.
                    true
                }
            }
        }
    };
    lints.into_iter().filter(|lint| should_keep_lint(lint)).collect()
}

/// `List.dedup_and_sort ~compare` of Base: a stable sort, then, of each run
/// of elements that compare equal, the last one.
fn dedup_and_sort(mut list: Vec<T<Pos>>) -> Vec<T<Pos>> {
    list.sort_by(compare_lint);
    let mut res: Vec<T<Pos>> = Vec::with_capacity(list.len());
    for lint in list {
        match res.last_mut() {
            Some(to_keep) if compare_lint(to_keep, &lint) == Ordering::Equal => *to_keep = lint,
            _ => res.push(lint),
        }
    }
    res
}

pub fn do_<A>(f: impl FnOnce() -> A) -> (Vec<T<Pos>>, A) {
    let list_copy = LINT_LIST.with_borrow_mut(|lint_list| lint_list.replace(vec![]));
    let result = f();
    let out = match LINT_LIST.with_borrow_mut(Option::take) {
        Some(mut lst) => {
            // The OCaml list, head first.
            lst.reverse();
            lst
        }
        None => panic!("Assert_failure lints/lints_core.ml"),
    };
    let out = filter_out_unsound_lints(out);
    LINT_LIST.with_borrow_mut(|lint_list| *lint_list = list_copy);
    let uniq = dedup_and_sort(out);
    (uniq, result)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn pos(line: usize) -> Pos {
        let file = Arc::new(RelativePath::make(Prefix::Root, "a.php".into()));
        let bol = line * 100;
        Pos::from_lnum_bol_offset(file, (line, bol, bol), (line, bol, bol + 4))
    }

    fn add_simple(check_status: Option<CheckStatus>, code: isize, line: usize, message: &str) {
        add(
            Some(check_status),
            None,
            None,
            code,
            Severity::LintWarning,
            pos(line),
            message.to_string(),
        )
    }

    #[test]
    fn ignored_outside_do() {
        add_simple(None, 1, 1, "dropped");
        let (lints, ()) = do_(|| ());
        assert!(lints.is_empty());
    }

    #[test]
    fn sorted_and_deduplicated() {
        let (lints, x) = do_(|| {
            add_simple(None, 2, 1, "b");
            add_simple(None, 1, 3, "a");
            add_simple(None, 1, 2, "z");
            // A duplicate (same code, position and message): the first one
            // added is the one that is kept.
            add(
                None,
                Some(true),
                None,
                1,
                Severity::LintError,
                pos(2),
                "z".to_string(),
            );
            42
        });
        assert_eq!(x, 42);
        let got: Vec<_> = lints
            .iter()
            .map(|l| (l.code, l.pos.line(), l.message.as_str(), l.severity))
            .collect();
        assert_eq!(
            got,
            vec![
                (1, 2, "z", Severity::LintWarning),
                (1, 3, "a", Severity::LintWarning),
                (2, 1, "b", Severity::LintWarning),
            ]
        );
    }

    #[test]
    fn unsound_lints_are_filtered() {
        let (lints, ()) = do_(|| {
            // Paired: the one under normal assumptions stays.
            add_simple(Some(CheckStatus::CUnderNormalAssumptions), 1, 1, "paired");
            add_simple(Some(CheckStatus::CUnderDynamicAssumptions), 1, 1, "paired");
            // Only under dynamic assumptions: dropped.
            add_simple(Some(CheckStatus::CUnderDynamicAssumptions), 2, 1, "dynamic");
            // Only under normal assumptions: not paired, dropped.
            add_simple(Some(CheckStatus::CUnderNormalAssumptions), 3, 1, "normal");
            // Checked once.
            add_simple(Some(CheckStatus::COnce), 4, 1, "once");
            add_simple(None, 5, 1, "unsound rule");
        });
        let got: Vec<_> = lints.iter().map(|l| l.message.as_str()).collect();
        assert_eq!(got, vec!["paired", "once", "unsound rule"]);
    }

    #[test]
    fn nested_do() {
        let (outer, ()) = do_(|| {
            add_simple(None, 1, 1, "outer");
            let (inner, ()) = do_(|| add_simple(None, 2, 1, "inner"));
            assert_eq!(inner.len(), 1);
            add_lint(inner.into_iter().next().unwrap());
        });
        let got: Vec<_> = outer.iter().map(|l| l.message.as_str()).collect();
        assert_eq!(got, vec!["outer", "inner"]);
    }

    #[test]
    fn severities() {
        assert_eq!(string_of_severity(Severity::LintError), "error");
        assert_eq!(string_of_severity(Severity::LintDisabled), "disabled");
    }
}
