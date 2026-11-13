// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `user_diagnostic.ml`. See `hh/PORTING.md`.
//!
//! The types are those of `oxidized::user_diagnostic`, re-exported:
//! `severity` is [`Severity`] and `('prim_pos, 'pos) t` is [`T`] (an alias
//! of `UserDiagnostic`). `Pos.absolute` is `crate::pos::Absolute`.
//!
//! # Derived functions
//!
//! The `.mli` exports what `[@@deriving ord]` gives `severity` and what
//! `[@@deriving eq, hash, ord, show]` gives `t`. The OCaml attributes make
//! these ignore the `is_trusted` of a warning and the explanation of a
//! diagnostic, so they differ from the `PartialEq`, `Ord` and `Hash` that
//! `oxidized` derives (and from the `Ord` of `oxidized::diagnostics_impl`,
//! which is `Diagnostics.compare_internal`): they are [`compare_severity`],
//! [`equal`] and [`compare`]. The derived `hash`, `pp` and `show` are not
//! ported (nothing in the typechecker uses them; saved states use
//! [`hash_diagnostic_for_saved_state`]).
//!
//! # Functions of modules that have no Rust module
//!
//! `to_absolute` and `to_absolute_for_test` need `Explanation.map`,
//! `Quickfix.to_absolute` (`Quickfix.map_positions`) and
//! `Classish_positions.map_pos`, which have no Rust function yet: they are
//! private functions at the end of this file, under their OCaml names.

use std::cmp::Ordering;

use bstr::ByteSlice;
use oxidized::classish_positions_types;
use oxidized::explanation::Elem;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;
use oxidized::pos_or_decl::PosOrDecl;
use oxidized::quickfix::Edits;
use oxidized::quickfix::HintStyle;
use oxidized::quickfix::Quickfix;
pub use oxidized::user_diagnostic::*;

use crate::pos::APos;
use crate::pos::Absolute;
use crate::yojson::safe as yojson;

/// `('prim_pos, 'pos) t`
pub type T<PrimPos, P> = UserDiagnostic<PrimPos, P>;

/// `module Severity`
pub mod severity {
    use super::Severity;

    pub fn to_string(s: &Severity) -> String {
        match s {
            Severity::Err => "error",
            Severity::Warning { .. } => "warning",
        }
        .to_string()
    }

    pub fn to_all_caps_string(s: &Severity) -> String {
        match s {
            Severity::Err => "ERROR",
            Severity::Warning { .. } => "WARN",
        }
        .to_string()
    }

    pub fn tty_color(s: &Severity) -> crate::tty::RawColor {
        match s {
            Severity::Err => crate::tty::RawColor::Red,
            Severity::Warning { .. } => crate::tty::RawColor::Yellow,
        }
    }
}

/// `equal_severity` (`[@@deriving eq]`): the `is_trusted` of a warning is
/// not compared (`[@equal (fun _ _ -> true)]`).
fn equal_severity(x: &Severity, y: &Severity) -> bool {
    match (x, y) {
        (Severity::Warning { .. }, Severity::Warning { .. }) => true,
        (Severity::Err, Severity::Err) => true,
        (Severity::Warning { .. }, Severity::Err) | (Severity::Err, Severity::Warning { .. }) => {
            false
        }
    }
}

/// `compare_severity` (`[@@deriving ord]`): by the order of the constructors,
/// `Warning` first; the `is_trusted` of a warning is not compared
/// (`[@compare (fun _ _ -> 0)]`).
pub fn compare_severity(x: &Severity, y: &Severity) -> Ordering {
    match (x, y) {
        (Severity::Warning { .. }, Severity::Warning { .. }) => Ordering::Equal,
        (Severity::Warning { .. }, Severity::Err) => Ordering::Less,
        (Severity::Err, Severity::Warning { .. }) => Ordering::Greater,
        (Severity::Err, Severity::Err) => Ordering::Equal,
    }
}

/// `equal` (`[@@deriving eq]`): field by field, in their order, except the
/// explanation (`[@equal (fun _ _ -> true)]`).
pub fn equal<PP: PartialEq, P: PartialEq>(x: &T<PP, P>, y: &T<PP, P>) -> bool {
    let UserDiagnostic {
        severity: x_severity,
        code: x_code,
        claim: x_claim,
        reasons: x_reasons,
        explanation: _,
        quickfixes: x_quickfixes,
        custom_msgs: x_custom_msgs,
        is_fixmed: x_is_fixmed,
        function_pos: x_function_pos,
    } = x;
    let UserDiagnostic {
        severity: y_severity,
        code: y_code,
        claim: y_claim,
        reasons: y_reasons,
        explanation: _,
        quickfixes: y_quickfixes,
        custom_msgs: y_custom_msgs,
        is_fixmed: y_is_fixmed,
        function_pos: y_function_pos,
    } = y;
    equal_severity(x_severity, y_severity)
        && x_code == y_code
        && x_claim == y_claim
        && x_reasons == y_reasons
        && x_quickfixes == y_quickfixes
        && x_custom_msgs == y_custom_msgs
        && x_is_fixmed == y_is_fixmed
        && x_function_pos == y_function_pos
}

/// `compare` (`[@@deriving ord]`): field by field, in their order, except the
/// explanation (`[@compare (fun _ _ -> 0)]`).
pub fn compare<PP: Ord, P: Ord>(x: &T<PP, P>, y: &T<PP, P>) -> Ordering {
    let UserDiagnostic {
        severity: x_severity,
        code: x_code,
        claim: x_claim,
        reasons: x_reasons,
        explanation: _,
        quickfixes: x_quickfixes,
        custom_msgs: x_custom_msgs,
        is_fixmed: x_is_fixmed,
        function_pos: x_function_pos,
    } = x;
    let UserDiagnostic {
        severity: y_severity,
        code: y_code,
        claim: y_claim,
        reasons: y_reasons,
        explanation: _,
        quickfixes: y_quickfixes,
        custom_msgs: y_custom_msgs,
        is_fixmed: y_is_fixmed,
        function_pos: y_function_pos,
    } = y;
    compare_severity(x_severity, y_severity)
        .then_with(|| x_code.cmp(y_code))
        .then_with(|| x_claim.cmp(y_claim))
        .then_with(|| x_reasons.cmp(y_reasons))
        .then_with(|| x_quickfixes.cmp(y_quickfixes))
        .then_with(|| x_custom_msgs.cmp(y_custom_msgs))
        .then_with(|| x_is_fixmed.cmp(y_is_fixmed))
        .then_with(|| x_function_pos.cmp(y_function_pos))
}

/// `external hash_diagnostic_for_saved_state`: the Rust function behind it is
/// `UserDiagnostic::hash_for_saved_state` (`oxidized::user_diagnostic_impl`).
pub fn hash_diagnostic_for_saved_state(d: &T<Pos, PosOrDecl>) -> isize {
    d.hash_for_saved_state()
}

#[allow(clippy::too_many_arguments)]
pub fn make<PP, P>(
    severity: Severity,
    code: isize,
    is_fixmed: Option<bool>,
    quickfixes: Option<Vec<Quickfix<PP>>>,
    custom_msgs: Option<Vec<String>>,
    function_pos: Option<PP>,
    claim: Message<PP>,
    reasons: Vec<Message<P>>,
    explanation: Explanation<P>,
) -> T<PP, P> {
    let is_fixmed = is_fixmed.unwrap_or(false);
    let quickfixes = quickfixes.unwrap_or_default();
    let custom_msgs = custom_msgs.unwrap_or_default();
    UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs,
        is_fixmed,
        function_pos,
    }
}

/// Make a User_diagnostic.t with severity Err
#[allow(clippy::too_many_arguments)]
pub fn make_err<PP, P>(
    code: isize,
    is_fixmed: Option<bool>,
    quickfixes: Option<Vec<Quickfix<PP>>>,
    custom_msgs: Option<Vec<String>>,
    function_pos: Option<PP>,
    claim: Message<PP>,
    reasons: Vec<Message<P>>,
    explanation: Explanation<P>,
) -> T<PP, P> {
    make(
        Severity::Err,
        code,
        is_fixmed,
        quickfixes,
        custom_msgs,
        function_pos,
        claim,
        reasons,
        explanation,
    )
}

/// Make a User_diagnostic.t with severity Warning.
/// [is_trusted] defaults to [true]; set to [false] for type-dependent
/// warnings that have not been verified under dynamic assumptions.
#[allow(clippy::too_many_arguments)]
pub fn make_warning<PP, P>(
    is_trusted: Option<bool>,
    code: isize,
    is_fixmed: Option<bool>,
    quickfixes: Option<Vec<Quickfix<PP>>>,
    custom_msgs: Option<Vec<String>>,
    claim: Message<PP>,
    reasons: Vec<Message<P>>,
) -> T<PP, P> {
    let is_trusted = is_trusted.unwrap_or(true);
    make(
        Severity::Warning { is_trusted },
        code,
        is_fixmed,
        quickfixes,
        custom_msgs,
        None,
        claim,
        reasons,
        Explanation::Empty,
    )
}

pub fn get_code<PP, P>(d: &T<PP, P>) -> isize {
    d.code
}

pub fn get_pos<PP: Clone, P>(d: &T<PP, P>) -> PP {
    let Message(pos, _) = &d.claim;
    pos.clone()
}

pub fn quickfixes<PP: Clone, P>(d: &T<PP, P>) -> Vec<Quickfix<PP>> {
    d.quickfixes.clone()
}

/// `claim :: reasons`
fn claim_and_reasons<A: Clone>(claim: &Message<A>, reasons: &[Message<A>]) -> Vec<Message<A>> {
    let mut l = Vec::with_capacity(reasons.len() + 1);
    l.push(claim.clone());
    l.extend_from_slice(reasons);
    l
}

pub fn to_list<A: Clone>(d: &T<A, A>) -> Vec<Message<A>> {
    claim_and_reasons(&d.claim, &d.reasons)
}

pub fn to_list_(d: &T<Pos, PosOrDecl>) -> Vec<Message<PosOrDecl>> {
    let Message(pos, claim) = &d.claim;
    let claim = Message(crate::pos_or_decl::of_raw_pos(pos.clone()), claim.clone());
    claim_and_reasons(&claim, &d.reasons)
}

pub fn get_messages<A: Clone>(d: &T<A, A>) -> Vec<Message<A>> {
    claim_and_reasons(&d.claim, &d.reasons)
}

pub fn to_absolute(d: &T<Pos, PosOrDecl>) -> T<Absolute, Absolute> {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs,
        is_fixmed,
        function_pos,
    } = d;
    let pos_or_decl_to_absolute_pos = |pos_or_decl: &PosOrDecl| {
        let pos = crate::pos_or_decl::unsafe_to_raw_pos(pos_or_decl.clone());
        crate::pos::to_absolute(&pos)
    };
    let claim = {
        let Message(pos, msg) = claim;
        Message(crate::pos::to_absolute(pos), msg.clone())
    };
    let function_pos = function_pos.as_ref().map(crate::pos::to_absolute);
    let reasons = reasons
        .iter()
        .map(|Message(p, s)| Message(pos_or_decl_to_absolute_pos(p), s.clone()))
        .collect();
    let explanation = explanation_map(explanation, pos_or_decl_to_absolute_pos);
    let quickfixes = quickfixes.iter().map(quickfix_to_absolute).collect();
    UserDiagnostic {
        severity: *severity,
        code: *code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs: custom_msgs.clone(),
        is_fixmed: *is_fixmed,
        function_pos,
    }
}

pub fn to_relative(t: T<Pos, PosOrDecl>) -> T<Pos, Pos> {
    let reasons = (t.reasons.into_iter())
        .map(|Message(p, s)| Message(crate::pos_or_decl::unsafe_to_raw_pos(p), s))
        .collect();
    let explanation = explanation_map(&t.explanation, |pos: &PosOrDecl| {
        crate::pos_or_decl::unsafe_to_raw_pos(pos.clone())
    });
    UserDiagnostic {
        reasons,
        explanation,
        ..t
    }
}

pub fn make_absolute<A>(severity: Severity, code: isize, messages: Vec<Message<A>>) -> T<A, A> {
    let mut messages = messages.into_iter();
    match messages.next() {
        None => panic!("an error must have at least one message"),
        Some(claim) => UserDiagnostic {
            severity,
            code,
            claim,
            reasons: messages.collect(),
            explanation: Explanation::Empty,
            quickfixes: vec![],
            custom_msgs: vec![],
            is_fixmed: false,
            function_pos: None,
        },
    }
}

pub fn to_absolute_for_test(d: &T<Pos, PosOrDecl>) -> T<Absolute, Absolute> {
    let UserDiagnostic {
        severity,
        code,
        claim: Message(claim_pos, claim_msg),
        reasons,
        explanation,
        quickfixes,
        custom_msgs,
        is_fixmed,
        function_pos,
    } = d;
    let f = |p: &PosOrDecl| {
        let p = crate::pos_or_decl::unsafe_to_raw_pos(p.clone());
        let path = crate::pos::filename(&p);
        let path_without_prefix = crate::relative_path::suffix(&path);
        let p = crate::pos::set_file(
            crate::relative_path::create(crate::relative_path::Prefix::Dummy, &path_without_prefix),
            &p,
        );
        crate::pos::to_absolute(&p)
    };
    let claim = Message(
        f(&crate::pos_or_decl::of_raw_pos(claim_pos.clone())),
        claim_msg.clone(),
    );
    let reasons = reasons
        .iter()
        .map(|Message(p, s)| Message(f(p), s.clone()))
        .collect();
    let explanation = explanation_map(explanation, |pos: &PosOrDecl| {
        crate::pos::to_absolute(&crate::pos_or_decl::unsafe_to_raw_pos(pos.clone()))
    });
    let quickfixes = quickfixes.iter().map(quickfix_to_absolute).collect();
    let function_pos = function_pos
        .as_ref()
        .map(|pos| f(&crate::pos_or_decl::of_raw_pos(pos.clone())));
    UserDiagnostic {
        severity: *severity,
        code: *code,
        claim,
        reasons,
        explanation,
        quickfixes,
        custom_msgs: custom_msgs.clone(),
        is_fixmed: *is_fixmed,
        function_pos,
    }
}

pub fn error_kind(error_code: isize) -> String {
    // OCaml's `/` rounds towards zero, as Rust's does.
    match error_code / 1000 {
        1 => "Parsing",
        2 => "Naming",
        3 => "NastCheck",
        4 => "Typing",
        5 => "Lint",
        8 => "Init",
        12 => "Warn",
        _ => "Other",
    }
    .to_string()
}

pub fn error_code_to_string(error_code: isize) -> String {
    let error_kind = error_kind(error_code);
    let error_number = format!("{:04}", error_code);
    format!("{}[{}]", error_kind, error_number)
}

/// The string looks like:
///
///     ERROR/WARN: path/to/file.php pos...
///     error/warning: You have a problem here (Typing4110)
///       path/to/other/file.php pos...
///       Because this is wrong
///       path/to/other/file.php pos...
///       And this too
///
/// (The messages are byte strings; bytes that are not UTF-8 are replaced
/// with U+FFFD, as `crate::diagnostics::to_plain_string` does.)
pub fn to_string(d: &T<Absolute, Absolute>) -> String {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        custom_msgs,
        ..
    } = d;
    let mut buf = String::with_capacity(50);
    let Message(pos1, msg1) = claim;
    buf.push_str(&{
        let error_code = error_code_to_string(*code);
        // /!\ WARNING!!!!!
        // Changing this might break emacs and vim.
        // These are not officially supported, but breaking will piss off users.
        // Fix Emacs at fbcode/emacs_config/emacs-packages/compile-mode-regexes.el
        // Fix Vim at fbcode/shellconfigs/rc_deprecated/vim/plugin/hack.vim, variable hack_errorformat
        format!(
            "{}: {}\n{} ({})\n",
            severity::to_all_caps_string(severity),
            crate::pos::string(pos1),
            msg1.to_str_lossy(),
            error_code
        )
    });
    for Message(p, w) in reasons {
        let msg = format!("  {}\n  {}\n", crate::pos::string(p), w.to_str_lossy());
        buf.push_str(&msg);
    }
    for w in custom_msgs {
        let msg = format!("  {}\n", w);
        buf.push_str(&msg);
    }
    buf
}

/// `to_json ~human_formatter ~filename_to_string error`, for an `'a Pos.pos`
/// of either kind (`Pos` or `Absolute`).
pub fn to_json<P: APos>(
    human_formatter: Option<&dyn Fn(&T<P, P>) -> String>,
    filename_to_string: impl Fn(P::File) -> String,
    error: &T<P, P>,
) -> yojson::T {
    let UserDiagnostic {
        severity,
        code,
        claim,
        reasons,
        custom_msgs,
        function_pos,
        ..
    } = error;
    let is_trusted = match severity {
        Severity::Warning { is_trusted } => *is_trusted,
        Severity::Err => true,
    };
    let msgl = std::iter::once(claim).chain(reasons.iter());
    let elts: Vec<yojson::T> = msgl
        .map(|Message(p, msg)| {
            let (line, scol, ecol) = crate::pos::info_pos(p);
            yojson::T::Assoc(vec![
                (
                    "descr".to_string(),
                    yojson::T::String(msg.to_str_lossy().into_owned()),
                ),
                (
                    "path".to_string(),
                    yojson::T::String(filename_to_string(crate::pos::filename(p))),
                ),
                ("line".to_string(), yojson::T::Int(line)),
                ("start".to_string(), yojson::T::Int(scol)),
                ("end".to_string(), yojson::T::Int(ecol)),
                ("code".to_string(), yojson::T::Int(*code)),
            ])
        })
        .collect();
    let custom_msgs: Vec<yojson::T> = custom_msgs
        .iter()
        .map(|msg| yojson::T::String(msg.clone()))
        .collect();
    let human_format = human_formatter.map(|f| f(error));
    let mut obj = vec![
        (
            "severity".to_string(),
            yojson::T::String(severity::to_string(severity)),
        ),
        ("is_trusted".to_string(), yojson::T::Bool(is_trusted)),
        ("message".to_string(), yojson::T::List(elts)),
        ("custom_messages".to_string(), yojson::T::List(custom_msgs)),
    ];
    // `List.filter_opt [human_format; function_pos]`
    let function_pos = function_pos.as_ref().map(|pos| {
        let (line, scol, ecol) = crate::pos::info_pos(pos);
        (
            "function_pos".to_string(),
            yojson::T::Assoc(vec![
                (
                    "path".to_string(),
                    yojson::T::String(filename_to_string(crate::pos::filename(pos))),
                ),
                ("line".to_string(), yojson::T::Int(line)),
                ("start".to_string(), yojson::T::Int(scol)),
                ("end".to_string(), yojson::T::Int(ecol)),
                ("code".to_string(), yojson::T::Int(*code)),
            ]),
        )
    });
    let human_format = human_format
        .map(|human_format| ("human_format".to_string(), yojson::T::String(human_format)));
    obj.extend(human_format);
    obj.extend(function_pos);
    yojson::T::Assoc(obj)
}

pub fn claim_message<PP: Clone, P>(d: &T<PP, P>) -> Message<PP> {
    d.claim.clone()
}

pub fn reason_messages<PP, P: Clone>(d: &T<PP, P>) -> Vec<Message<P>> {
    d.reasons.clone()
}

pub fn function_pos<PP: Clone, P>(d: &T<PP, P>) -> Option<PP> {
    d.function_pos.clone()
}

pub fn custom_errors<PP, P>(d: &T<PP, P>) -> Vec<String> {
    d.custom_msgs.clone()
}

// ~~ functions of modules that have no Rust module yet ~~~~~~~~~~~~~~~~~~~~~~

/// `Explanation.map_elem`
fn explanation_map_elem<A, B>(elem: &Elem<A>, f: &impl Fn(&A) -> B) -> Elem<B> {
    match elem {
        Elem::Witness(pos, str) => Elem::Witness(f(pos), str.clone()),
        Elem::WitnessNoPos(str) => Elem::WitnessNoPos(str.clone()),
        Elem::Rule(rule) => Elem::Rule(rule.clone()),
        Elem::Step(path, is_error) => Elem::Step(path.clone(), *is_error),
        Elem::Trans(trans) => Elem::Trans(trans.clone()),
        Elem::Prefix { prefix, sep } => Elem::Prefix {
            prefix: prefix.clone(),
            sep: sep.clone(),
        },
        Elem::Suffix { suffix, sep } => Elem::Suffix {
            suffix: suffix.clone(),
            sep: sep.clone(),
        },
    }
}

/// `Explanation.map`
fn explanation_map<A, B>(t: &Explanation<A>, f: impl Fn(&A) -> B) -> Explanation<B> {
    match t {
        Explanation::Debug(str) => Explanation::Debug(str.clone()),
        Explanation::Derivation(elems) => Explanation::Derivation(
            elems
                .iter()
                .map(|elem| explanation_map_elem(elem, &f))
                .collect(),
        ),
        Explanation::Empty => Explanation::Empty,
    }
}

/// `Classish_positions.map_pos`
fn classish_positions_map_pos<A, B>(
    f: &impl Fn(&A) -> B,
    p: &classish_positions_types::Pos<A>,
) -> classish_positions_types::Pos<B> {
    use classish_positions_types::Pos as CP;
    match p {
        CP::Precomputed(p) => CP::Precomputed(f(p)),
        CP::ClassishStartOfBody(name) => CP::ClassishStartOfBody(name.clone()),
        CP::ClassishEndOfBody(name) => CP::ClassishEndOfBody(name.clone()),
        CP::ClassishClosingBrace(name) => CP::ClassishClosingBrace(name.clone()),
    }
}

/// `Quickfix.map_positions`
fn quickfix_map_positions<A, B>(q: &Quickfix<A>, f: impl Fn(&A) -> B) -> Quickfix<B> {
    let Quickfix {
        title,
        edits,
        hint_styles,
    } = q;
    let transform_edits = |edits: &Edits<A>| match edits {
        Edits::Eager(edits) => {
            let edits = edits.iter().map(|(s, p)| (s.clone(), f(p))).collect();
            Edits::Eager(edits)
        }
        Edits::ClassishEnd { new_text, name } => Edits::ClassishEnd {
            new_text: new_text.clone(),
            name: name.clone(),
        },
        Edits::AddFunctionAttribute {
            function_pos,
            attribute_name,
        } => Edits::AddFunctionAttribute {
            function_pos: f(function_pos),
            attribute_name: attribute_name.clone(),
        },
    };
    let edits = transform_edits(edits);
    let transform_hint_style =
        |hint_style: &HintStyle<classish_positions_types::Pos<A>>| match hint_style {
            HintStyle::HintStyleSilent(p) => {
                HintStyle::HintStyleSilent(classish_positions_map_pos(&f, p))
            }
            HintStyle::HintStyleHint(p) => {
                HintStyle::HintStyleHint(classish_positions_map_pos(&f, p))
            }
        };
    let hint_styles = hint_styles.iter().map(transform_hint_style).collect();
    Quickfix {
        title: title.clone(),
        edits,
        hint_styles,
    }
}

/// `Quickfix.to_absolute`
fn quickfix_to_absolute(q: &Quickfix<Pos>) -> Quickfix<Absolute> {
    quickfix_map_positions(q, crate::pos::to_absolute)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use bstr::BString;
    use oxidized::pos_span_raw::PosSpanRaw;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;

    fn pos(file: &str) -> Pos {
        Pos::from_raw_span(
            Arc::new(RelativePath::make(Prefix::Root, PathBuf::from(file))),
            PosSpanRaw::make_dummy(),
        )
    }

    fn msg(p: &Pos, s: &str) -> Message<Pos> {
        Message(p.clone(), BString::from(s))
    }

    #[test]
    fn error_codes_to_string() {
        assert_eq!(error_code_to_string(4110), "Typing[4110]");
        assert_eq!(error_code_to_string(2049), "Naming[2049]");
        assert_eq!(error_code_to_string(12001), "Warn[12001]");
        assert_eq!(error_code_to_string(0), "Other[0000]");
        assert_eq!(error_code_to_string(5), "Other[0005]");
        assert_eq!(error_kind(8001), "Init");
        assert_eq!(error_kind(9001), "Other");
    }

    #[test]
    fn make_defaults() {
        let p = pos("a.php");
        let d: T<Pos, Pos> = make_err(
            4110,
            None,
            None,
            None,
            None,
            msg(&p, "claim"),
            vec![msg(&p, "reason")],
            Explanation::Empty,
        );
        assert_eq!(d.severity, Severity::Err);
        assert!(!d.is_fixmed);
        assert!(d.quickfixes.is_empty());
        assert!(d.custom_msgs.is_empty());
        assert_eq!(d.function_pos, None);
        assert_eq!(get_code(&d), 4110);
        assert_eq!(to_list(&d).len(), 2);
        let w: T<Pos, Pos> = make_warning(None, 12001, None, None, None, msg(&p, "w"), vec![]);
        assert_eq!(w.severity, Severity::Warning { is_trusted: true });
    }

    #[test]
    fn derived_comparisons_ignore_is_trusted_and_explanation() {
        let p = pos("a.php");
        let w1: T<Pos, Pos> =
            make_warning(Some(true), 12001, None, None, None, msg(&p, "w"), vec![]);
        let mut w2: T<Pos, Pos> =
            make_warning(Some(false), 12001, None, None, None, msg(&p, "w"), vec![]);
        w2.explanation = Explanation::Debug("x".to_string());
        assert!(equal(&w1, &w2));
        assert_eq!(compare(&w1, &w2), Ordering::Equal);
        let e: T<Pos, Pos> = make_err(
            12001,
            None,
            None,
            None,
            None,
            msg(&p, "w"),
            vec![],
            Explanation::Empty,
        );
        assert!(!equal(&w1, &e));
        assert_eq!(compare(&w1, &e), Ordering::Less);
        assert_eq!(
            compare_severity(&Severity::Err, &Severity::Warning { is_trusted: false }),
            Ordering::Greater
        );
    }

    #[test]
    #[should_panic(expected = "an error must have at least one message")]
    fn make_absolute_empty() {
        let _: T<Pos, Pos> = make_absolute(Severity::Err, 0, vec![]);
    }
}
