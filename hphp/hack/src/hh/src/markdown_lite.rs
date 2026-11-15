// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `diagnostics/markdown_lite.ml`. See `hh/PORTING.md`.

use crate::tty;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Delimiter {
    Backtick,
    Asterisk,
    DoubleAsterisk,
    DoubleTilde,
}

/// `DelimiterSet.t`: a set of delimiters. OCaml's is `Stdlib.Set.Make
/// (DelimiterKind)`; here it is one bit per `Delimiter` (there are four, and
/// every character of the message carries a set).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DelimiterSet(u8);

impl DelimiterSet {
    const EMPTY: Self = Self(0);

    fn mem(self, d: Delimiter) -> bool {
        self.0 & (1 << d as u8) != 0
    }

    fn add(self, d: Delimiter) -> Self {
        Self(self.0 | (1 << d as u8))
    }
}

/// The characters are bytes, as in OCaml.
type TaggedChar = (DelimiterSet, u8);

struct ParseState<'a> {
    parsed: Vec<TaggedChar>,
    remaining: &'a [u8],
}

fn delimiter_to_string(d: Delimiter) -> &'static [u8] {
    match d {
        Delimiter::Backtick => b"`",
        Delimiter::Asterisk => b"*",
        Delimiter::DoubleAsterisk => b"**",
        Delimiter::DoubleTilde => b"~~",
    }
}

/// Supports a small subset of Markdown, with some caveats
/// in order to handle bolding the main message:
///
///  *foo bar* for italics
///  **foo bar** for bold
///  `foo bar` for code (underlines text)
///  ~~foo bar~~ for highlighting the text (in red by default)
///
/// The `color` parameter is only used on characters
/// tagged with DoubleTilde.
///
/// `apply_color_from_style` is `Tty.apply_color_from_style`.
fn format_markdown(
    add_bold: bool,
    color: tty::RawColor,
    parsed: &[TaggedChar],
    apply_color_from_style: impl Fn(&str, &str) -> String,
) -> String {
    let format = |delimiters: DelimiterSet, s: &[u8]| -> Vec<u8> {
        let mut styles = if delimiters.mem(Delimiter::Backtick) {
            vec![tty::StyleAttribute::Underline]
        } else {
            vec![]
        };
        // Second condition: if we're supposed to bold the message anyway
        // (e.g. in the main message), then add italics to it (and add bold
        // later below)
        if delimiters.mem(Delimiter::Asterisk)
            || (delimiters.mem(Delimiter::DoubleAsterisk) && add_bold)
        {
            styles.insert(0, tty::StyleAttribute::Italics);
        }
        if delimiters.mem(Delimiter::DoubleAsterisk) || add_bold {
            styles.insert(0, tty::StyleAttribute::Bold);
        }
        let color = if delimiters.mem(Delimiter::DoubleTilde) {
            color
        } else {
            tty::RawColor::Default
        };
        if styles.is_empty() {
            s.to_vec()
        } else {
            // A run of characters with the same delimiters never ends inside
            // a UTF-8 character: runs end where a delimiter (ASCII) was.
            let s = String::from_utf8_lossy(s);
            apply_color_from_style(&tty::style_num_from_list(color, &styles), &s).into_bytes()
        }
    };
    // `List.group ~break`: runs of characters with the same delimiters.
    let mut out: Vec<u8> = Vec::with_capacity(parsed.len());
    let mut start = 0;
    while start < parsed.len() {
        let delimiters = parsed[start].0;
        let mut end = start + 1;
        while end < parsed.len() && parsed[end].0 == delimiters {
            end += 1;
        }
        let s: Vec<u8> = parsed[start..end].iter().map(|(_, c)| *c).collect();
        out.extend(format(delimiters, &s));
        start = end;
    }
    match String::from_utf8(out) {
        Ok(s) => s,
        Err(e) => String::from_utf8_lossy(e.as_bytes()).into_owned(),
    }
}

fn eat_prefix<'a>(prefix: &[u8], state: ParseState<'a>) -> Option<ParseState<'a>> {
    let ParseState { parsed, remaining } = state;
    let remaining = remaining.strip_prefix(prefix)?;
    Some(ParseState { parsed, remaining })
}

fn parse_single_char(state: ParseState<'_>) -> Option<ParseState<'_>> {
    let ParseState {
        mut parsed,
        remaining,
    } = state;
    // `first_and_tail_exn`
    let (first, remaining) = remaining.split_first().expect("Invalid_argument: index out of bounds");
    parsed.push((DelimiterSet::EMPTY, *first));
    Some(ParseState { parsed, remaining })
}

/// `state.parsed` is the section so far, last character first.
fn parse_and_format_until(delimiter: Delimiter, state: ParseState<'_>) -> Option<ParseState<'_>> {
    // Example: "*foo bar*" is a valid section, while
    // "**", "* foo bar*", "*foo bar *", and "* foo bar *" are not.
    // The absence of a leading space is checked before entering this function.
    //
    // (The head of the section is its last character.)
    let is_valid_section =
        |section: &[TaggedChar]| !section.is_empty() && section[section.len() - 1].1 != b' ';
    // Here `parsed` is in the order of the text, and OCaml's list is
    // `parsed` reversed.
    let ParseState {
        mut parsed,
        mut remaining,
    } = state;
    loop {
        match remaining.strip_prefix(delimiter_to_string(delimiter)) {
            Some(remaining) if is_valid_section(&parsed) => {
                // Matched a delimiter over a non-empty section;
                // now try and see if there are nested delimited sections
                // in that larger section.
                //
                // OCaml parses the section as it has it: last character
                // first. The result is in that order too, as the caller
                // expects (it reverses it).
                let section: Vec<u8> = parsed.iter().rev().map(|(_, c)| *c).collect();
                let parsed: Vec<TaggedChar> = parse_markdown(&section)
                    .into_iter()
                    .flatten()
                    .map(|(delims, c)| (delims.add(delimiter), c))
                    .collect();
                return Some(ParseState { parsed, remaining });
            }
            _ => match remaining.split_first() {
                // Nothing left to try
                None => return None,
                // Haven't matched a delimiter yet (or did, but the section
                // wasn't valid), and we still have text we can try
                Some((first, rest)) => {
                    parsed.push((DelimiterSet::EMPTY, *first));
                    remaining = rest;
                }
            },
        }
    }
}

fn parse_and_format_section(delimiter: Delimiter, s: ParseState<'_>) -> Option<ParseState<'_>> {
    let s = eat_prefix(delimiter_to_string(delimiter), s)?;
    // `eat_prefix " " |> fail`: success if there is no space.
    if s.remaining.starts_with(b" ") {
        return None;
    }
    // The result is the section last character first.
    parse_and_format_until(delimiter, s)
}

/// The parsed pieces of `msg`, in order: delimited sections and single
/// characters.
fn parse_markdown(msg: &[u8]) -> Vec<Vec<TaggedChar>> {
    let mut acc: Vec<Vec<TaggedChar>> = vec![];
    let mut msg = msg;
    while !msg.is_empty() {
        let state = || ParseState {
            parsed: vec![],
            remaining: msg,
        };
        // The result of a section is last character first
        // (`List.rev parsed`).
        let section = |delimiter| {
            parse_and_format_section(delimiter, state()).map(|ParseState { parsed, remaining }| {
                ParseState {
                    parsed: parsed.into_iter().rev().collect(),
                    remaining,
                }
            })
        };
        let parsed = section(Delimiter::DoubleAsterisk)
            .or_else(|| section(Delimiter::DoubleTilde))
            .or_else(|| section(Delimiter::Asterisk))
            .or_else(|| section(Delimiter::Backtick))
            .or_else(|| parse_single_char(state()));
        match parsed {
            None => panic!("Impossible: unable to parse a single character in error message"),
            Some(ParseState { parsed, remaining }) => {
                acc.push(parsed);
                msg = remaining;
            }
        }
    }
    acc
}

fn render_with(
    add_bold: bool,
    color: tty::RawColor,
    msg: &str,
    apply_color_from_style: impl Fn(&str, &str) -> String,
) -> String {
    let parsed: Vec<TaggedChar> = parse_markdown(msg.as_bytes()).into_iter().flatten().collect();
    format_markdown(add_bold, color, &parsed, apply_color_from_style)
}

/// `add_bold` defaults to `false` and `color` to `Tty.Red`.
pub fn render(add_bold: Option<bool>, color: Option<tty::RawColor>, msg: &str) -> String {
    let add_bold = add_bold.unwrap_or(false);
    let color = color.unwrap_or(tty::RawColor::Red);
    render_with(add_bold, color, msg, |style, s| {
        tty::apply_color_from_style(None, style, s)
    })
}

pub fn md_codify(s: &str) -> String {
    format!("`{}`", s)
}

pub fn md_highlight(s: &str) -> String {
    format!("~~{}~~", s)
}

pub fn md_bold(s: &str) -> String {
    format!("**{}**", s)
}

pub fn md_italicize(s: &str) -> String {
    format!("*{}*", s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `render`, with the styles shown as `<style|text>`.
    fn show(add_bold: bool, msg: &str) -> String {
        render_with(add_bold, tty::RawColor::Red, msg, |style, s| {
            format!("<{}|{}>", style, s)
        })
    }

    #[test]
    fn delimiters() {
        assert_eq!(md_codify("x"), "`x`");
        assert_eq!(md_highlight("x"), "~~x~~");
        assert_eq!(md_bold("x"), "**x**");
        assert_eq!(md_italicize("x"), "*x*");
    }

    #[test]
    fn plain() {
        assert_eq!(show(false, ""), "");
        assert_eq!(show(false, "Hello world"), "Hello world");
        assert_eq!(show(true, "Hello world"), "<0;1|Hello world>");
    }

    #[test]
    fn sections() {
        // Code is underlined, emphasis is italics, strong is bold, and
        // highlighted text takes the color (when it has a style at all).
        assert_eq!(show(false, "a `b c` d"), "a <0;4|b c> d");
        assert_eq!(show(false, "a *b c* d"), "a <0;3|b c> d");
        assert_eq!(show(false, "a **b c** d"), "a <0;1|b c> d");
        assert_eq!(show(false, "a ~~b c~~ d"), "a b c d");
        assert_eq!(
            show(true, "a ~~b c~~ d"),
            "<0;1|a ><31;1|b c><0;1| d>"
        );
        assert_eq!(
            show(true, "a `b` *c* **d**"),
            "<0;1|a ><0;1;4|b><0;1| ><0;1;3|c><0;1| ><0;1;3|d>"
        );
    }

    #[test]
    fn invalid_sections() {
        // Not closed.
        assert_eq!(show(false, "a `b c"), "a `b c");
        assert_eq!(show(false, "2 * 3"), "2 * 3");
        // A section does not start or end with a space.
        assert_eq!(show(false, "2 * 3 * 4"), "2 * 3 * 4");
        assert_eq!(show(false, "a *b * c"), "a *b * c");
        // The closing delimiter after a space is skipped, not the section.
        assert_eq!(show(false, "a *b *c* d"), "a <0;3|b *c> d");
        // Empty sections.
        assert_eq!(show(false, "a `` b"), "a `` b");
        // `*`, an empty section, the character `*` and `*`: the delimiter
        // that closes an empty section is a character of the section.
        assert_eq!(show(false, "****"), "<0;3|*>*");
        assert_eq!(show(false, "**"), "**");
    }

    #[test]
    fn nested_sections() {
        // As in `Render.suggestion_message`.
        assert_eq!(
            show(false, "Did you mean `~~C~~amel~~C~~ase` instead?"),
            "Did you mean <31;4|C><0;4|amel><31;4|C><0;4|ase> instead?"
        );
        assert_eq!(
            show(false, "**a *b* c**"),
            "<0;1|a ><0;1;3|b><0;1| c>"
        );
        // The inside of a section is parsed last character first.
        assert_eq!(show(false, "`a *b c* d`"), "<0;4|a ><0;3;4|b c><0;4| d>");
        assert_eq!(show(false, "`a * b* c`"), "<0;4|a * b* c>");
        assert_eq!(show(false, "`a *b * c`"), "<0;4|a *b * c>");
        // Outside of a section, the first `*` closes the emphasis; inside,
        // where the text is parsed backwards, the last one opens it.
        assert_eq!(show(false, "*a* b*"), "<0;3|a> b*");
        assert_eq!(show(false, "`*a* b*`"), "<0;3;4|a* b>");
    }

    #[test]
    fn utf8() {
        assert_eq!(show(false, "é `ü` ñ"), "é <0;4|ü> ñ");
        assert_eq!(show(false, "`aé*ü*`"), "<0;4|aé><0;3;4|ü>");
    }
}
