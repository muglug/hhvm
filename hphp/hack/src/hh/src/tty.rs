// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/sys/tty.ml`. See `hh/PORTING.md`.
//!
//! The colors and styles of terminal output, and the functions that apply
//! them to a string. The functions that print or read from the terminal are
//! not here, except `print_one` and `cprint` (which write to an output
//! channel), and `eprintf` and `print_clear_line` (on stderr).

use std::io::IsTerminal;
use std::io::Write;
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawColor {
    Default,
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Style {
    Normal(RawColor),
    Bold(RawColor),
    Dim(RawColor),
    Italics(RawColor),
    Underline(RawColor),
    BoldDim(RawColor),
    BoldItalics(RawColor),
    BoldUnderline(RawColor),
    DimUnderline(RawColor),
    NormalWithBG(RawColor, RawColor),
    BoldWithBG(RawColor, RawColor),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ColorMode {
    ColorAlways,
    ColorNever,
    ColorAuto,
}

/// The styles `style_num_from_list` takes: ``[ `Bold | `Dim | `Italics |
/// `Underline ]`` (a polymorphic variant, which has no name in OCaml).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StyleAttribute {
    Bold,
    Dim,
    Italics,
    Underline,
}

pub fn text_num(c: RawColor) -> String {
    match c {
        RawColor::Default => "39",
        RawColor::Black => "30",
        RawColor::Red => "31",
        RawColor::Green => "32",
        RawColor::Yellow => "33",
        RawColor::Blue => "34",
        RawColor::Magenta => "35",
        RawColor::Cyan => "36",
        RawColor::White => "37",
    }
    .to_string()
}

pub fn background_num(c: RawColor) -> String {
    match c {
        RawColor::Default => "49",
        RawColor::Black => "40",
        RawColor::Red => "41",
        RawColor::Green => "42",
        RawColor::Yellow => "43",
        RawColor::Blue => "44",
        RawColor::Magenta => "45",
        RawColor::Cyan => "46",
        RawColor::White => "47",
    }
    .to_string()
}

pub fn color_num(c: RawColor) -> String {
    match c {
        RawColor::Default => "0".to_string(),
        x => text_num(x),
    }
}

pub fn style_num(style: Style) -> String {
    match style {
        Style::Normal(c) => color_num(c),
        Style::Bold(c) => color_num(c) + ";1",
        Style::Dim(c) => color_num(c) + ";2",
        Style::Italics(c) => color_num(c) + ";3",
        Style::Underline(c) => color_num(c) + ";4",
        Style::BoldDim(c) => color_num(c) + ";1;2",
        Style::BoldItalics(c) => color_num(c) + ";1;3",
        Style::BoldUnderline(c) => color_num(c) + ";1;4",
        Style::DimUnderline(c) => color_num(c) + ";2;4",
        Style::NormalWithBG(text, bg) => text_num(text) + ";" + &background_num(bg),
        Style::BoldWithBG(text, bg) => text_num(text) + ";" + &background_num(bg) + ";1",
    }
}

pub fn style_num_from_list(color: RawColor, styles: &[StyleAttribute]) -> String {
    let mut accum = color_num(color);
    for style in styles {
        accum.push_str(match style {
            StyleAttribute::Bold => ";1",
            StyleAttribute::Dim => ";2",
            StyleAttribute::Italics => ";3",
            StyleAttribute::Underline => ";4",
        });
    }
    accum
}

/// Whether the terminal supports color
pub fn supports_color() -> bool {
    static MEMO: OnceLock<bool> = OnceLock::new();
    *MEMO.get_or_init(|| {
        // `Sys_utils.getenv_term ()`
        match std::env::var("TERM") {
            Err(_) => false,
            Ok(term) => std::io::stdout().is_terminal() && term != "dumb",
        }
    })
}

pub fn should_color(color_mode: ColorMode) -> bool {
    let force_color = match std::env::var("FORCE_ERROR_COLOR") {
        Err(_) => false,
        Ok(s) => s == "true",
    };
    match color_mode {
        ColorMode::ColorAlways => true,
        ColorMode::ColorNever => false,
        ColorMode::ColorAuto => supports_color() || force_color,
    }
}

/// `color_mode` defaults to `ColorMode::ColorAuto`.
pub fn apply_color(color_mode: Option<ColorMode>, c: Style, s: &str) -> String {
    let color_mode = color_mode.unwrap_or(ColorMode::ColorAuto);
    if should_color(color_mode) {
        format!("\x1b[{}m{}\x1b[0m", style_num(c), s)
    } else {
        s.to_string()
    }
}

/// `color_mode` defaults to `ColorMode::ColorAuto`.
pub fn apply_color_from_style(color_mode: Option<ColorMode>, style: &str, s: &str) -> String {
    let color_mode = color_mode.unwrap_or(ColorMode::ColorAuto);
    if should_color(color_mode) {
        format!("\x1b[{}m{}\x1b[0m", style, s)
    } else {
        s.to_string()
    }
}

/// `color_mode` defaults to `ColorMode::ColorAuto`, `out_channel` to stdout. A write
/// that fails panics, as `Printf.fprintf` raises `Sys_error`.
pub fn print_one<'w>(
    color_mode: Option<ColorMode>,
    out_channel: Option<&mut (dyn std::io::Write + 'w)>,
    c: Style,
    s: &str,
) {
    let color_mode = color_mode.unwrap_or(ColorMode::ColorAuto);
    let s = apply_color(Some(color_mode), c, s);
    let res = match out_channel {
        Some(out_channel) => out_channel.write_all(s.as_bytes()),
        None => std::io::Write::write_all(&mut std::io::stdout(), s.as_bytes()),
    };
    if let Err(e) = res {
        panic!("Sys_error: {}", e)
    }
}

/// `color_mode` defaults to `ColorMode::ColorAuto`, `out_channel` to stdout.
pub fn cprint<'w>(
    color_mode: Option<ColorMode>,
    mut out_channel: Option<&mut (dyn std::io::Write + 'w)>,
    strs: &[(Style, String)],
) {
    let color_mode = color_mode.unwrap_or(ColorMode::ColorAuto);
    for (c, s) in strs {
        print_one(Some(color_mode), out_channel.as_deref_mut(), *c, s)
    }
}

/// Gets the number of columns in the current terminal window through
/// [`tput cols`][1]. If the command fails in any way then `None` will
/// be returned.
///
/// This value may change over the course of program execution if a user resizes
/// their terminal.
///
/// [1]: http://invisible-island.net/ncurses/man/tput.1.html
///
/// (As in OCaml, a failing `tput` raises (`Sys_utils.exec_read` asserts that
/// it exits with 0), and output that is not a number raises `Failure
/// "int_of_string"`: both panic.)
pub fn get_term_cols() -> Option<isize> {
    if !supports_color() {
        None
    } else {
        crate::sys_utils::exec_read("tput cols").map(|s| match s.parse::<isize>() {
            Ok(cols) => cols,
            Err(_) => panic!("Failure: int_of_string"),
        })
    }
}

/// `Tty.clear_line_seq`
pub const CLEAR_LINE_SEQ: &str = "\r\x1b[0K";

/// What is written to stderr in the tests instead (as if it were a
/// terminal).
#[cfg(test)]
pub(crate) static CAPTURE: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

/// `Tty.eprintf`: writes `s` to stderr if it is a terminal, and flushes it.
pub fn eprintf(s: &str) {
    #[cfg(test)]
    {
        if let Some(captured) = CAPTURE.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
            captured.push_str(s);
            return;
        }
    }
    let stderr = std::io::stderr();
    if stderr.is_terminal() {
        let mut stderr = stderr.lock();
        let _ = stderr.write_all(s.as_bytes());
        let _ = stderr.flush();
    }
}

/// `Tty.print_clear_line stderr` (the port prints the line only on stderr).
pub fn print_clear_line() {
    eprintf(CLEAR_LINE_SEQ)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn style_numbers() {
        assert_eq!(style_num(Style::Normal(RawColor::Default)), "0");
        assert_eq!(style_num(Style::Normal(RawColor::Red)), "31");
        assert_eq!(style_num(Style::Bold(RawColor::Default)), "0;1");
        assert_eq!(style_num(Style::BoldUnderline(RawColor::Cyan)), "36;1;4");
        assert_eq!(style_num(Style::DimUnderline(RawColor::White)), "37;2;4");
        // With a background, the default text color is 39, not 0.
        assert_eq!(
            style_num(Style::NormalWithBG(RawColor::Default, RawColor::Default)),
            "39;49"
        );
        assert_eq!(
            style_num(Style::BoldWithBG(RawColor::Black, RawColor::Yellow)),
            "30;43;1"
        );
        assert_eq!(
            style_num_from_list(
                RawColor::Red,
                &[
                    StyleAttribute::Bold,
                    StyleAttribute::Italics,
                    StyleAttribute::Underline
                ]
            ),
            "31;1;3;4"
        );
        assert_eq!(style_num_from_list(RawColor::Default, &[]), "0");
    }

    #[test]
    fn apply() {
        assert_eq!(
            apply_color(
                Some(ColorMode::ColorAlways),
                Style::Bold(RawColor::Red),
                "x"
            ),
            "\x1b[31;1mx\x1b[0m"
        );
        assert_eq!(
            apply_color(Some(ColorMode::ColorNever), Style::Bold(RawColor::Red), "x"),
            "x"
        );
        assert_eq!(
            apply_color_from_style(Some(ColorMode::ColorAlways), "0;4", "x"),
            "\x1b[0;4mx\x1b[0m"
        );
        assert_eq!(
            apply_color_from_style(Some(ColorMode::ColorNever), "0;4", "x"),
            "x"
        );
    }
}
