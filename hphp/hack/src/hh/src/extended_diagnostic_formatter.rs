// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/extended_diagnostic_formatter.ml`. See `hh/PORTING.md`.
//!
//! `Diagnostics.finalized_diagnostic` is `user_diagnostic::T<Absolute,
//! Absolute>`. Message texts are byte strings; bytes that are not UTF-8
//! become U+FFFD, as in `user_diagnostic::to_string`. The `Base.String`
//! functions that cut source lines (`prefix`, `drop_prefix`, `slice`) work on
//! bytes, as in OCaml, and raise (panic) where `Base` raises.
//!
//! `try ... with _ -> ...` around `Pos.to_relative` (in `mark_with_context`
//! and `add_span`) is [`to_relative_opt`], which returns `None` exactly where
//! `Pos.to_relative` raises (a prefix of `Relative_path` that is not set).
//!
//! The OCaml has two functions named `merge`, the second shadowing the first;
//! the first is [`merge_pair`] here.

use std::collections::BTreeMap;

use bstr::ByteSlice;
use oxidized::explanation::Elem;
use oxidized::explanation::Explanation;
use oxidized::message::Message;
use oxidized::pos::Pos;

use crate::diagnostics;
use crate::markdown_lite;
use crate::pos::APos;
use crate::pos::Absolute;
use crate::relative_path;
use crate::relative_path::Prefix;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_list;
use crate::string_utils;
use crate::tty;
use crate::tty::RawColor;
use crate::tty::Style;
use crate::user_diagnostic;
use crate::user_diagnostic::Severity;
use crate::user_diagnostic::UserDiagnostic;
use crate::user_diagnostic::severity;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// `string S_map.t`, of the spans of each file.
type Spans = BTreeMap<String, Vec<Pos>>;

const LINE_GAP: isize = 4;

const PAD_BEFORE: isize = 2;

const PAD_AFTER: isize = 3;

const CURSOR_L: &str = "»";

const CURSOR_R: &str = "«";

const HEADER_COLS: isize = 80;

const ERROR_ALERT: &str = " (here is where the error occurred)";

enum MergeResult {
    Only(Pos),
    Both(Pos, Pos),
}

/// The first `merge` of the OCaml (`merge pos0 pos1`).
///
/// Invariant: pos0.start <= pos1.start
fn merge_pair(pos0: &Pos, pos1: &Pos) -> MergeResult {
    if crate::pos::contains(pos0, pos1) {
        MergeResult::Only(pos0.clone())
    } else {
        let end_0 = crate::pos::end_line(pos0);
        let beg_1 = crate::pos::line(pos1);
        let gap = (beg_1 - end_0).abs();
        if gap >= LINE_GAP {
            MergeResult::Both(pos0.clone(), pos1.clone())
        } else {
            MergeResult::Only(crate::pos::merge(pos0, pos1))
        }
    }
}

fn merge_all(ps: Vec<Pos>, cur: Pos, acc: Vec<Pos>) -> Vec<Pos> {
    // `acc` in the order the positions were added (the OCaml list reversed).
    let mut cur = cur;
    let mut acc = acc;
    for p in ps {
        match merge_pair(&cur, &p) {
            MergeResult::Only(c) => cur = c,
            MergeResult::Both(p, q) => {
                acc.push(p);
                cur = q;
            }
        }
    }
    // `List.rev (cur :: acc)`
    acc.push(cur);
    acc
}

/// The second `merge` of the OCaml (`merge ps`).
fn merge(ps: Vec<Pos>) -> Vec<Pos> {
    let mut ps = ps.into_iter();
    match ps.next() {
        Some(p) => merge_all(ps.collect(), p, vec![]),
        None => vec![],
    }
}

// ~~ Tty helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

const STYLE_ELEM: Style = Style::Normal(RawColor::Green);

const STYLE_CURSOR: Style = Style::Dim(RawColor::Green);

const STYLE_STEP: Style = Style::BoldWithBG(RawColor::Default, RawColor::Blue);

const STYLE_ALERT: Style = Style::NormalWithBG(RawColor::Default, RawColor::Blue);

const STYLE_RULE: Style = Style::BoldItalics(RawColor::Default);

const STYLE_TRANS: Style = Style::Italics(RawColor::Default);

const STYLE_LINE_NUM: Style = Style::Dim(RawColor::Default);

const STYLE_FILEPOS: Style = Style::Dim(RawColor::Default);

const STYLE_FILENAME: Style = Style::Normal(RawColor::Magenta);

// ~~ Base.String ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// `Base.String.sub s ~pos ~len`, which raises `Invalid_argument` out of
/// bounds.
fn string_sub(s: &[u8], pos: isize, len: isize) -> &[u8] {
    if pos < 0 || len < 0 || pos + len > s.len() as isize {
        panic!(
            "Invalid_argument: String.sub: pos={} len={} length={}",
            pos,
            len,
            s.len()
        )
    }
    &s[pos as usize..(pos + len) as usize]
}

/// `Base.String.prefix s n`: the first `n` bytes, or all of `s` when it is
/// shorter; raises `Invalid_argument` when `n < 0`.
fn string_prefix(s: &[u8], n: isize) -> &[u8] {
    if n < 0 {
        panic!("Invalid_argument: prefix expecting nonnegative argument")
    }
    if n as usize > s.len() {
        s
    } else {
        &s[..n as usize]
    }
}

/// `Base.String.drop_prefix s n`: without the first `n` bytes, or `""` when
/// `s` is shorter; raises `Invalid_argument` when `n < 0`.
fn string_drop_prefix(s: &[u8], n: isize) -> &[u8] {
    if n < 0 {
        panic!("Invalid_argument: drop_prefix expecting nonnegative argument")
    }
    if n as usize > s.len() {
        b""
    } else {
        &s[n as usize..]
    }
}

/// `Base.String.slice s start stop`: a `stop` of 0 is the end of `s`, and
/// negative indices count from the end.
fn string_slice(s: &[u8], start: isize, stop: isize) -> &[u8] {
    let length = s.len() as isize;
    let normalize = |i: isize| if i < 0 { i + length } else { i };
    let stop = if stop == 0 { length } else { stop };
    let pos = normalize(start);
    let len = normalize(stop) - pos;
    string_sub(s, pos, len)
}

/// `Base.String.pad_left s ~char ~len`
fn string_pad_left(s: &str, c: char, len: isize) -> String {
    let src_len = s.len() as isize;
    if src_len >= len {
        s.to_string()
    } else {
        std::iter::repeat_n(c, (len - src_len) as usize).collect::<String>() + s
    }
}

/// `Base.String.pad_right s ~len` (padding with spaces)
fn string_pad_right(s: &str, len: isize) -> String {
    let src_len = s.len() as isize;
    if src_len >= len {
        s.to_string()
    } else {
        s.to_string() + &" ".repeat((len - src_len) as usize)
    }
}

/// `Base.String.lstrip s`: without its leading `Char.is_whitespace`.
fn string_lstrip(s: &str) -> &str {
    s.trim_start_matches([' ', '\t', '\n', '\r', '\x0b', '\x0c'])
}

fn lossy(s: &[u8]) -> std::borrow::Cow<'_, str> {
    String::from_utf8_lossy(s)
}

// ~~ Context helpers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

fn relative_path(path: &str) -> String {
    let cwd = {
        let cwd = std::env::current_dir().unwrap_or_else(|e| panic!("Sys_error: {}", e));
        ocaml_filename::concat(&cwd.to_string_lossy(), "")
    };
    string_utils::lstrip(path, &cwd).to_string()
}

/// `try Some (Pos.to_relative p) with _ -> None`: `Relative_path.create_detect_prefix`
/// raises `Invalid_argument` when it reaches a prefix that is not set
/// (it tries `Root`, `Hhi` and `Tmp` in this order, and stops at the first
/// one the path starts with).
fn to_relative_opt(p: &Absolute) -> Option<Pos> {
    let s = crate::pos::filename(p);
    let mut file_prefix = Prefix::Dummy;
    for prefix in [Prefix::Root, Prefix::Hhi, Prefix::Tmp] {
        match relative_path::path_of_prefix(prefix) {
            Err(_) => return None,
            Ok(path) => {
                if s.starts_with(&path) {
                    file_prefix = prefix;
                    break;
                }
            }
        }
    }
    Some(crate::pos::set_file(
        relative_path::create(file_prefix, &s),
        p,
    ))
}

fn render_pos(buf: &mut String, pos: &Absolute) {
    let pos_string = tty::apply_color(
        None,
        STYLE_FILEPOS,
        &crate::pos::multiline_string_no_file(pos),
    );
    let filename = {
        let fn_ = relative_path(&crate::pos::filename(pos));
        if fn_.ends_with(".hhi") {
            // (The OCaml's hhi files are in a directory of `/tmp`; the
            // port's hhi root is not, so it is recognised by its prefix.)
            let hhi_root = relative_path::path_of_prefix(relative_path::Prefix::Hhi).ok();
            let under_hhi_root = hhi_root
                .as_deref()
                .filter(|root| !root.is_empty())
                .and_then(|root| fn_.strip_prefix(root))
                .map(|rest| rest.trim_start_matches('/').to_string());
            match (under_hhi_root, fn_.split('/').collect::<Vec<_>>().as_slice()) {
                (_, [_, "tmp", _, rest @ ..]) => rest.join("/"),
                (Some(rest), _) => rest,
                _ => fn_,
            }
        } else {
            fn_
        }
    };
    let file_pos_string = format!(
        "{} {}{} {}{}",
        tty::apply_color(None, Style::Dim(RawColor::Default), "File"),
        tty::apply_color(None, STYLE_FILENAME, &filename),
        tty::apply_color(None, Style::Dim(RawColor::Default), ","),
        pos_string,
        tty::apply_color(None, Style::Dim(RawColor::Default), ":")
    );
    buf.push_str(&file_pos_string);
}

fn context_pos<P: APos>(
    ctxt_pos: &P,
    pos: &Absolute,
) -> (isize, isize, isize, isize, isize, isize) {
    let ctxt_start_ln = crate::pos::line(ctxt_pos);
    let ctxt_end_ln = crate::pos::end_line(ctxt_pos);
    let (start_ln, end_ln, start_col, end_col) = crate::pos::info_pos_extended(pos);
    (
        ctxt_start_ln - PAD_BEFORE - 1,
        ctxt_end_ln + PAD_AFTER - 1,
        start_ln - 1,
        end_ln - 1,
        start_col - 1,
        end_col - 1,
    )
}

/// Given a position and the list of all spans for each file:
/// 1) Find the relevant file and find the first span that contains the position
/// 2) Select the lines from that file corresponding to the containing span
/// 3) For each line prepend the line number and a gutter marker
/// 4) For the line(s) containing the position we want to mark, insert a cursor
///    before and after the start column on the start line and after the end
///    column on the end line
fn mark_with_context(pos: &Absolute, buf: &mut String, spans: &Spans) {
    // Find the containing span for our position
    let path = relative_path(&crate::pos::filename(pos));
    let ctxt_pos_opt = spans.get(&path).and_then(|l| {
        l.iter().find(|spos| match to_relative_opt(pos) {
            Some(p) => crate::pos::contains(spos, &p),
            None => false,
        })
    });
    let (ctxt_start_ln, ctxt_end_ln, start_ln, end_ln, start_col, end_col) = match ctxt_pos_opt {
        Some(ctxt_pos) => context_pos(ctxt_pos, pos),
        _ => context_pos(pos, pos),
    };
    // We'll use the same number of characters for each line number so find how
    // many chars the longest line number needs
    let line_num_width = 1 + (end_ln.to_string().len() as isize);
    // Write to buffer
    for (ln, str) in diagnostics::read_lines(&path).iter().enumerate() {
        let ln = ln as isize;
        if ln < ctxt_start_ln || ln > ctxt_end_ln {
            // This line isn't in our containing span so skip it
        } else if (ln == ctxt_start_ln || ln == ctxt_end_ln) && string_lstrip(str).is_empty() {
            // If the line is blank and is either the first of last line, skip it
        } else {
            // First write the line number and gutter marker
            let ln_num = string_pad_left(&(ln + 1).to_string(), ' ', line_num_width);
            buf.push_str(&tty::apply_color(None, STYLE_LINE_NUM, &ln_num));
            buf.push_str(&tty::apply_color(None, STYLE_LINE_NUM, " | "));
            let is_start = ln == start_ln;
            let is_end = ln == end_ln;
            let s = str.as_bytes();
            if is_start && is_end {
                // If our target pos starts and ends on the line..
                // - write the prefix before the start of the marked pos
                // - write the lhs cursor marker
                // - write the marked string
                // - write the rhs cursor marker
                // - write the suffix after the end of the marked pos
                buf.push_str(&lossy(string_prefix(s, start_col)));
                buf.push_str(&tty::apply_color(None, STYLE_CURSOR, CURSOR_L));
                buf.push_str(&tty::apply_color(
                    None,
                    STYLE_ELEM,
                    &lossy(string_slice(s, start_col, end_col + 1)),
                ));
                buf.push_str(&tty::apply_color(None, STYLE_CURSOR, CURSOR_R));
                buf.push_str(&lossy(string_drop_prefix(s, end_col + 1)));
            } else if is_start {
                // If this is the start line, write the prefix, the lhs cursor and
                // substring of the marked pos that is on this line
                buf.push_str(&lossy(string_prefix(s, start_col)));
                buf.push_str(&tty::apply_color(None, STYLE_CURSOR, CURSOR_L));
                buf.push_str(&tty::apply_color(
                    None,
                    STYLE_ELEM,
                    &lossy(string_drop_prefix(s, start_col)),
                ));
            } else if is_end {
                // If this is the end line, write the substring of the marked pos
                // that is on the line, the rhs cursor and the suffix
                buf.push_str(&tty::apply_color(
                    None,
                    STYLE_ELEM,
                    &lossy(string_prefix(s, end_col)),
                ));
                buf.push_str(&tty::apply_color(None, STYLE_CURSOR, CURSOR_R));
                buf.push_str(&lossy(string_drop_prefix(s, end_col)));
            } else if ln < start_ln || ln > end_ln {
                // Either the whole line is part of the target pos or the target
                // is not on the line at all; either way, write the entire line
                buf.push_str(str);
            } else {
                buf.push_str(&tty::apply_color(None, STYLE_ELEM, str));
            }
            buf.push('\n');
        }
    }
}

fn render_reason(buf: &mut String, spans: &Spans, (pos, msg): (&Absolute, &str)) {
    let pretty_msg = markdown_lite::render(None, None, msg);
    buf.push_str(&pretty_msg);
    buf.push_str("\n\n");
    render_pos(buf, pos);
    buf.push_str("\n\n");
    mark_with_context(pos, buf, spans);
    buf.push('\n');
}

fn render_elem(buf: &mut String, spans: &Spans, cols: isize, elem: &Elem<Absolute>) {
    match elem {
        Elem::Witness(pos, msg) => {
            let msg = markdown_lite::render(None, None, msg);
            render_reason(buf, spans, (pos, &msg))
        }
        Elem::WitnessNoPos(msg) => {
            let msg = markdown_lite::render(None, None, msg);
            buf.push_str(&msg);
            buf.push('\n');
        }
        Elem::Rule(msg) => {
            let msg = markdown_lite::render(None, None, msg);
            buf.push('\n');
            buf.push_str(&tty::apply_color(None, STYLE_RULE, &msg));
            buf.push_str("\n\n");
        }
        Elem::Step(msg, false) => {
            let len = cols - 2;
            let msg = string_pad_right(msg, len);
            buf.push_str(&tty::apply_color(None, STYLE_ALERT, "\n  "));
            buf.push_str(&tty::apply_color(None, STYLE_STEP, &msg));
            buf.push('\n');
        }
        Elem::Step(msg, true) => {
            let len = cols - ERROR_ALERT.len() as isize - 2;
            let msg = string_pad_right(msg, len);
            buf.push_str(&tty::apply_color(None, STYLE_ALERT, "\n  "));
            buf.push_str(&tty::apply_color(None, STYLE_STEP, &msg));
            buf.push_str(&tty::apply_color(None, STYLE_ALERT, ERROR_ALERT));
            buf.push_str(&tty::apply_color(None, STYLE_ALERT, " "));

            buf.push('\n');
        }
        Elem::Trans(msg) => {
            let msg = markdown_lite::render(None, None, msg);
            buf.push_str(&tty::apply_color(None, STYLE_TRANS, &msg));
            buf.push('\n');
        }
        Elem::Prefix { prefix, sep } => {
            let prefix = markdown_lite::render(None, None, prefix);
            buf.push_str(&prefix);
            buf.push_str(sep);
        }
        Elem::Suffix { suffix, sep: _ } => {
            let suffix = markdown_lite::render(None, None, suffix);
            buf.push_str(&suffix);
            buf.push_str("\n\n");
        }
    }
}

fn render_derivation(buf: &mut String, spans: &Spans, cols: isize, elems: &[Elem<Absolute>]) {
    buf.push_str("Here's why:\n\n");
    for elem in elems {
        render_elem(buf, spans, cols, elem)
    }
}

fn render_claim(
    buf: &mut String,
    spans: &Spans,
    code: isize,
    (pos, msg): (&Absolute, &str),
    severity: &Severity,
) {
    let colour = severity::tty_color(severity);
    let style_severity = Style::Bold(colour);
    let pretty_msg = markdown_lite::render(Some(true), Some(colour), msg);
    buf.push_str(&format!(
        "{}: {} {}\n\n",
        tty::apply_color(None, style_severity, &severity::to_string(severity)),
        tty::apply_color(
            None,
            style_severity,
            &user_diagnostic::error_code_to_string(code)
        ),
        pretty_msg
    ));
    render_pos(buf, pos);
    buf.push_str("\n\n");
    mark_with_context(pos, buf, spans);
    buf.push('\n');
}

fn add_span(acc: Spans, p: &Absolute) -> Spans {
    let file_checked = relative_path(&crate::pos::filename(p));
    match to_relative_opt(p) {
        Some(p) => {
            let mut acc = acc;
            // `Some ps -> Some (p :: ps) | None -> Some [p]`
            acc.entry(file_checked).or_default().insert(0, p);
            acc
        }
        None => acc,
    }
}

/// `S_map.map (fun ps -> merge @@ List.sort ps ~compare:(fun x y -> Pos.compare y x))`
fn merge_spans(spans: Spans) -> Spans {
    spans
        .into_iter()
        .map(|(file, ps)| {
            (
                file,
                merge(ocaml_list::stable_sort(ps, |x, y| {
                    crate::pos::compare(y, x)
                })),
            )
        })
        .collect()
}

pub fn to_string(error: &FinalizedDiagnostic) -> String {
    let UserDiagnostic {
        code,
        claim: Message(pos, msg),
        reasons,
        explanation,
        severity,
        ..
    } = error;
    let msg = msg.to_str_lossy();
    match explanation {
        Explanation::Debug(json) => {
            // Just render the json, no other info
            json.clone()
        }
        Explanation::Empty => {
            // If the explanation is empty then just render the claim and reasons;
            // only subtyping errors will have explanations at the moment
            let file_checked = relative_path(&crate::pos::filename(pos));
            let init = Spans::from([(file_checked, vec![crate::pos::to_relative(pos)])]);
            let spans = merge_spans(
                reasons
                    .iter()
                    .fold(init, |acc, Message(p, _)| add_span(acc, p)),
            );
            let mut buf = String::with_capacity(500);
            render_claim(&mut buf, &spans, *code, (pos, &msg), severity);
            for Message(p, m) in reasons {
                render_reason(&mut buf, &spans, (p, &m.to_str_lossy()))
            }
            buf
        }
        Explanation::Derivation(elems) => {
            let cols = tty::get_term_cols().unwrap_or(HEADER_COLS);
            let file_checked = relative_path(&crate::pos::filename(pos));
            let init = elems.iter().fold(
                Spans::from([(file_checked, vec![crate::pos::to_relative(pos)])]),
                |acc, elem| match elem {
                    Elem::Witness(p, _) => add_span(acc, p),
                    _ => acc,
                },
            );
            let spans = merge_spans(
                reasons
                    .iter()
                    .fold(init, |acc, Message(p, _)| add_span(acc, p)),
            );
            let mut buf = String::with_capacity(1000);
            render_claim(&mut buf, &spans, *code, (pos, &msg), severity);
            for Message(p, m) in reasons {
                render_reason(&mut buf, &spans, (p, &m.to_str_lossy()))
            }
            render_derivation(&mut buf, &spans, cols, elems);
            buf
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    const SUITE: &str = "extended_reasons";

    /// The diagnostic of `extended_reasons/fn_ret.php`, with this
    /// explanation.
    fn fn_ret(
        explanation: impl FnOnce(
            &dyn Fn((usize, usize), (usize, usize)) -> Absolute,
        ) -> Explanation<Absolute>,
    ) -> FinalizedDiagnostic {
        let p = |start, end| fx::pos("fn_ret.php", start, end);
        let mut e = fx::err(
            4110,
            fx::msg(p((8, 9), (8, 14)), "Invalid return type"),
            vec![
                fx::msg(p((7, 16), (7, 20)), "Expected `bool`"),
                fx::msg(p((3, 16), (3, 19)), "But got `int`"),
            ],
        );
        e.explanation = explanation(&p);
        e
    }

    /// `extended_reasons/fn_ret.php.exp`.
    #[test]
    fn derivation() {
        let out = fx::run_in_suite(module_path!(), "derivation", SUITE, false, || {
            let e = fn_ret(|p| {
                Explanation::Derivation(vec![
                    Elem::Step("Step 1 of 1".to_string(), true),
                    Elem::Rule("I started by checking this subtype relationship.".to_string()),
                    Elem::Witness(
                        p((3, 16), (3, 19)),
                        "The subtype comes from this hint".to_string(),
                    ),
                    Elem::Witness(
                        p((7, 16), (7, 20)),
                        "The supertype comes from this hint".to_string(),
                    ),
                ])
            });
            fx::single_type_check_output(diagnostics::Format::Extended, to_string, &[e])
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, &fx::expected(SUITE, "fn_ret.php.exp"));
        }
    }

    /// Without an explanation, the claim and the reasons: the part of
    /// `fn_ret.php.exp` before `Here's why:`.
    #[test]
    fn empty_explanation() {
        let out = fx::run_in_suite(module_path!(), "empty_explanation", SUITE, false, || {
            to_string(&fn_ret(|_| Explanation::Empty))
        });
        if let Some(out) = out {
            let exp = fx::expected(SUITE, "fn_ret.php.exp");
            fx::assert_same_text(&out, &exp[..exp.find("Here's why:").unwrap()]);
        }
    }

    #[test]
    fn debug_explanation() {
        let out = fx::run_in_suite(module_path!(), "debug_explanation", SUITE, false, || {
            to_string(&fn_ret(|_| Explanation::Debug("{\"debug\":1}".to_string())))
        });
        if let Some(out) = out {
            fx::assert_same_text(&out, "{\"debug\":1}");
        }
    }

    /// The other elements of a derivation, a step that is not the error,
    /// and a position that spans several lines (its end column is counted
    /// from the beginning of its first line, as `Pos.info_pos` does).
    #[test]
    fn other_elements() {
        let out = fx::run_in_suite(module_path!(), "other_elements", SUITE, false, || {
            let e = fn_ret(|p| {
                Explanation::Derivation(vec![
                    Elem::Step("Step 1 of 2".to_string(), false),
                    Elem::Prefix {
                        prefix: "`pre`".to_string(),
                        sep: " | ".to_string(),
                    },
                    Elem::Suffix {
                        suffix: "suf".to_string(),
                        sep: "ignored".to_string(),
                    },
                    Elem::Trans("*trans*".to_string()),
                    Elem::WitnessNoPos("no pos".to_string()),
                    Elem::Witness(p((3, 16), (4, 4)), "two lines".to_string()),
                ])
            });
            let out = to_string(&e);
            out[out.find("Here's why:").unwrap()..].to_string()
        });
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                &format!(
                    "Here's why:\n\
                     \n\
                     \n  {}\n\
                     pre | suf\n\
                     \n\
                     trans\n\
                     no pos\n\
                     two lines\n\
                     \n\
                     File fn_ret.php, line 3, character 17 - line 4, character 4:\n\
                     \n\
                     \x201 | <?hh\n\
                     \x202 | \n\
                     \x203 | function foo(): »int {{\n\
                     \x204 |   return 1;«\n\
                     \x205 | }}\n\
                     \x206 | \n\
                     \x207 | function bar(): bool {{\n\
                     \n",
                    format!("{:78}", "Step 1 of 2")
                ),
            );
        }
    }

    /// `render_pos`: the path is relative to the current directory, and an
    /// `.hhi` file under `/tmp/<dir>/` is shown without them (`_ :: "tmp" ::
    /// _ :: rest`, so `/tmp/x.hhi` has an empty name); other `.hhi` paths
    /// are kept.
    #[test]
    fn render_pos_hhi_paths() {
        let out = fx::run_in_suite(module_path!(), "render_pos_hhi_paths", SUITE, false, || {
            [
                "fn_ret.php",
                "/tmp/hhi_123/lib/string.hhi",
                "/tmp/x.hhi",
                "/var/hhi_123/string.hhi",
                "/tmp/hhi_123/string.php",
            ]
            .iter()
            .map(|file| {
                let mut buf = String::new();
                render_pos(&mut buf, &fx::pos(file, (1, 0), (1, 3)));
                buf + "\n"
            })
            .collect()
        });
        if let Some(out) = out {
            fx::assert_same_text(
                &out,
                "File fn_ret.php, line 1, character 1 - line 1, character 3:\n\
                 File lib/string.hhi, line 1, character 1 - line 1, character 3:\n\
                 File , line 1, character 1 - line 1, character 3:\n\
                 File /var/hhi_123/string.hhi, line 1, character 1 - line 1, character 3:\n\
                 File /tmp/hhi_123/string.php, line 1, character 1 - line 1, character 3:\n",
            );
        }
    }

    #[test]
    fn base_string_helpers() {
        // Pure functions of `Base.String`.
        assert_eq!(string_slice(b"abcdef", 1, 3), b"bc");
        assert_eq!(string_slice(b"abcdef", 2, 0), b"cdef");
        assert_eq!(string_slice(b"abcdef", -2, 0), b"ef");
        assert_eq!(string_prefix(b"abc", 5), b"abc");
        assert_eq!(string_drop_prefix(b"abc", 5), b"");
        assert_eq!(string_pad_left("7", ' ', 3), "  7");
        assert_eq!(string_pad_right("ab", 1), "ab");
        assert_eq!(string_lstrip(" \t "), "");
    }

    #[test]
    #[should_panic(expected = "Invalid_argument: String.sub")]
    fn slice_out_of_bounds_raises() {
        string_slice(b"abc", 1, 5);
    }
}
