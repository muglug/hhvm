// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stdlib/format.ml` of OCaml 5 (the standard library's `Format`,
//! not in this tree). See `hh/PORTING.md`.
//!
//! The pretty-printing engine: text, break hints and boxes, laid out within
//! a margin, transliterated from `format.ml` (the queue of tokens, the scan
//! stack that computes the sizes of breaks and boxes, the format stack that
//! decides where lines break). With the same calls, the output is the same as
//! OCaml's, line breaks and indentation included.
//!
//! Only what the port uses so far is here: text (`pp_print_string`,
//! `pp_print_as`, `pp_print_char`), break hints (`pp_print_custom_break`,
//! `pp_print_break`, `pp_print_space`, `pp_print_cut`), boxes (`pp_open_*`,
//! `pp_close_box`), flushing, the margin, and formatters writing to a buffer
//! or to an output channel (`asprintf`, `formatter_of_buffer`,
//! `formatter_of_out_channel`), forced newlines (`@\n`, `pp_force_newline`).
//! Not here: tabulation boxes, semantic tags, `pp_print_if_newline`, the
//! setters of the maximum number of boxes and of the ellipsis, and the
//! standard formatters.
//!
//! `printf`-style format strings are not interpreted: where OCaml calls
//! `Format.fprintf ppf "..." args`, make the calls that `fprintf` makes for
//! the format string (`output_acc`): a literal is `pp_print_string` (or
//! `pp_print_char` for a single character), `%s` is `pp_print_string`, `%a`
//! calls the printer, `@ ` is `pp_print_space`, `@,` is `pp_print_cut`, `@[`
//! is `pp_open_box ppf 0`, `@]` is `pp_close_box`.
//!
//! As in OCaml, sizes are counted in bytes.

use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

/// `Size.t`: the size of a token. A size is known when it is non-negative;
/// until the size of a break or a box is known, it is minus the total width
/// of the queue when the token was enqueued.
type Size = isize;

mod size {
    use super::Size;

    pub const ZERO: Size = 0;

    pub const UNKNOWN: Size = -1;

    pub fn is_known(n: Size) -> bool {
        n >= 0
    }
}

/// The pretty-printing boxes definition:
/// a pretty-printing box is either
/// - hbox: horizontal box (no line splitting)
/// - vbox: vertical box (every break hint splits the line)
/// - hvbox: horizontal/vertical box
///   (the box behaves as an horizontal box if it fits on
///   the current line, otherwise the box behaves as a vertical box)
/// - hovbox: horizontal or vertical compacting box
///   (the box is compacting material, printing as much material as possible
///   on every lines)
/// - box: horizontal or vertical compacting box with enhanced box structure
///   (the box behaves as an horizontal or vertical box but break hints split
///   the line if splitting would move to the left)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoxType {
    PpHbox,
    PpVbox,
    PpHvbox,
    PpHovbox,
    PpBox,
    PpFits,
}

/// The pretty-printing tokens definition:
/// are either text to print or pretty printing
/// elements that drive indentation and line splitting.
#[derive(Clone, Debug)]
enum PpToken {
    /// normal text
    PpText(String),
    /// complete break
    PpBreak {
        /// line is not split
        fits: (String, isize, String),
        /// line is split
        breaks: (String, isize, String),
    },
    /// beginning of a box
    PpBegin(isize, BoxType),
    /// end of a box
    PpEnd,
    /// to force a newline inside a box
    PpNewline,
}

/// The pretty-printer queue:
/// pretty-printing material is not written in the output as soon as emitted;
/// instead, the material is simply recorded in the pretty-printer queue,
/// until the enclosing box has a known computed size and proper splitting
/// decisions can be made.
///
/// Each formatting element is a tuple (size, token, length), where
/// - length is the declared length of the token,
/// - size is effective size of the token when it is printed
///   (size is set when the size of the box is known, so that size of break
///   hints are definitive).
///
/// The element is shared between the queue and the scan stack, which sets its
/// size (a `mutable` field in OCaml).
#[derive(Debug)]
struct PpQueueElem {
    size: Cell<Size>,
    token: PpToken,
    length: isize,
}

/// The pretty-printer scanning stack: scanning element definition.
#[derive(Debug)]
struct PpScanElem {
    /// Value of pp_left_total when the element was enqueued.
    left_total: isize,
    queue_elem: Rc<PpQueueElem>,
}

/// The pretty-printer formatting stack: formatting stack element definition.
/// Each stack element describes a pretty-printing box.
#[derive(Clone, Copy, Debug)]
struct PpFormatElem {
    box_type: BoxType,
    width: isize,
}

/// Where a formatter writes: `pp_out_string` and `pp_out_flush`. (The
/// newlines, spaces and indentation are written with `pp_out_string`, as
/// `make_formatter` sets them up.)
enum Output {
    /// `formatter_of_buffer b`: `Buffer.add_substring b`; flushing does
    /// nothing.
    Buffer(String),
    /// `formatter_of_out_channel oc`: `output_substring oc`, `flush oc`.
    Channel(Box<dyn std::io::Write>),
}

/// The formatter definition.
/// Each formatter value is a pretty-printer instance with all its
/// machinery. The stacks are vectors whose top is the last element.
pub struct Formatter {
    /// The pretty-printer scanning stack.
    pp_scan_stack: Vec<PpScanElem>,
    /// The pretty-printer formatting stack.
    pp_format_stack: Vec<PpFormatElem>,
    /// Value of right margin.
    pp_margin: isize,
    /// Minimal space left before margin, when opening a box.
    pp_min_space_left: isize,
    /// Maximum value of indentation:
    /// no box can be opened further.
    pp_max_indent: isize,
    /// Space remaining on the current line.
    pp_space_left: isize,
    /// Current value of indentation.
    pp_current_indent: isize,
    /// True when the line has been broken by the pretty-printer.
    pp_is_new_line: bool,
    /// Total width of tokens already printed.
    pp_left_total: isize,
    /// Total width of tokens ever put in queue.
    pp_right_total: isize,
    /// Current number of open boxes.
    pp_curr_depth: isize,
    /// Maximum number of boxes which can be simultaneously open.
    pp_max_boxes: isize,
    /// Ellipsis string.
    pp_ellipsis: String,
    /// Output functions.
    pp_out: Output,
    /// The pretty-printer queue.
    pp_queue: VecDeque<Rc<PpQueueElem>>,
}

impl std::fmt::Debug for Formatter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<formatter>")
    }
}

// ~~ Auxiliaries and basic functions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Enter a token in the pretty-printer queue.
fn pp_enqueue(state: &mut Formatter, token: Rc<PpQueueElem>) {
    state.pp_right_total = state.pp_right_total + token.length;
    state.pp_queue.push_back(token)
}

fn pp_clear_queue(state: &mut Formatter) {
    state.pp_left_total = 1;
    state.pp_right_total = 1;
    state.pp_queue.clear()
}

/// Pp_infinity: large value for default tokens size.
const PP_INFINITY: isize = 1000000010;

/// `state.pp_out_string s 0 (String.length s)`
fn pp_out_string(state: &mut Formatter, s: &str) {
    match &mut state.pp_out {
        Output::Buffer(b) => b.push_str(s),
        Output::Channel(oc) => {
            if let Err(e) = oc.write_all(s.as_bytes()) {
                panic!("Sys_error: {}", e)
            }
        }
    }
}

fn pp_out_flush(state: &mut Formatter) {
    match &mut state.pp_out {
        Output::Buffer(_) => (),
        Output::Channel(oc) => {
            if let Err(e) = oc.flush() {
                panic!("Sys_error: {}", e)
            }
        }
    }
}

/// Output functions for the formatter.
fn pp_output_string(state: &mut Formatter, s: &str) {
    pp_out_string(state, s)
}

fn pp_output_newline(state: &mut Formatter) {
    display_newline(state)
}

fn pp_output_spaces(state: &mut Formatter, n: isize) {
    display_blanks(state, n)
}

fn pp_output_indent(state: &mut Formatter, n: isize) {
    display_indent(state, n)
}

/// Format a textual token
fn format_pp_text(state: &mut Formatter, size: isize, text: &str) {
    state.pp_space_left = state.pp_space_left - size;
    pp_output_string(state, text);
    state.pp_is_new_line = false
}

/// Format a string by its length, if not empty
fn format_string(state: &mut Formatter, s: &str) {
    if !s.is_empty() {
        format_pp_text(state, s.len() as isize, s)
    }
}

/// To format a break, indenting a new line.
fn break_new_line(state: &mut Formatter, (before, offset, after): (&str, isize, &str), width: isize) {
    format_string(state, before);
    pp_output_newline(state);
    state.pp_is_new_line = true;
    let indent = state.pp_margin - width + offset;
    // Don't indent more than pp_max_indent.
    let real_indent = std::cmp::min(state.pp_max_indent, indent);
    state.pp_current_indent = real_indent;
    state.pp_space_left = state.pp_margin - state.pp_current_indent;
    pp_output_indent(state, state.pp_current_indent);
    format_string(state, after)
}

/// To force a line break inside a box: no offset is added.
fn break_line(state: &mut Formatter, width: isize) {
    break_new_line(state, ("", 0, ""), width)
}

/// To format a break that fits on the current line.
fn break_same_line(state: &mut Formatter, (before, width, after): (&str, isize, &str)) {
    format_string(state, before);
    state.pp_space_left = state.pp_space_left - width;
    pp_output_spaces(state, width);
    format_string(state, after)
}

/// To indent no more than pp_max_indent, if one tries to open a box
/// beyond pp_max_indent, then the box is rejected on the left
/// by simulating a break.
fn pp_force_break_line(state: &mut Formatter) {
    match state.pp_format_stack.last().copied() {
        None => pp_output_newline(state),
        Some(PpFormatElem { box_type, width }) => {
            if width > state.pp_space_left {
                match box_type {
                    BoxType::PpFits | BoxType::PpHbox => (),
                    BoxType::PpVbox | BoxType::PpHvbox | BoxType::PpHovbox | BoxType::PpBox => {
                        break_line(state, width)
                    }
                }
            }
        }
    }
}

// ~~ The main pretty printing functions ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Formatting a token with a given size.
fn format_pp_token(state: &mut Formatter, size: isize, token: &PpToken) {
    match token {
        PpToken::PpText(s) => format_pp_text(state, size, s),
        PpToken::PpBegin(off, ty) => {
            let insertion_point = state.pp_margin - state.pp_space_left;
            if insertion_point > state.pp_max_indent {
                // can not open a box right there.
                pp_force_break_line(state)
            }
            let width = state.pp_space_left - off;
            let box_type = match ty {
                BoxType::PpVbox => BoxType::PpVbox,
                BoxType::PpHbox
                | BoxType::PpHvbox
                | BoxType::PpHovbox
                | BoxType::PpBox
                | BoxType::PpFits => {
                    if size > state.pp_space_left {
                        *ty
                    } else {
                        BoxType::PpFits
                    }
                }
            };
            state.pp_format_stack.push(PpFormatElem { box_type, width })
        }
        PpToken::PpEnd => {
            state.pp_format_stack.pop();
        }
        PpToken::PpNewline => match state.pp_format_stack.last().copied() {
            None => pp_output_newline(state), // No open box.
            Some(PpFormatElem { width, .. }) => break_line(state, width),
        },
        PpToken::PpBreak { fits, breaks } => {
            let (before, off, _) = breaks;
            let fits = (fits.0.as_str(), fits.1, fits.2.as_str());
            let breaks = (breaks.0.as_str(), breaks.1, breaks.2.as_str());
            match state.pp_format_stack.last().copied() {
                None => (), // No open box.
                Some(PpFormatElem { box_type, width }) => match box_type {
                    BoxType::PpHovbox => {
                        if size + before.len() as isize > state.pp_space_left {
                            break_new_line(state, breaks, width)
                        } else {
                            break_same_line(state, fits)
                        }
                    }
                    BoxType::PpBox => {
                        // Have the line just been broken here ?
                        if state.pp_is_new_line {
                            break_same_line(state, fits)
                        } else if size + before.len() as isize > state.pp_space_left {
                            break_new_line(state, breaks, width)
                        }
                        // break the line here leads to new indentation ?
                        else if state.pp_current_indent > state.pp_margin - width + off {
                            break_new_line(state, breaks, width)
                        } else {
                            break_same_line(state, fits)
                        }
                    }
                    BoxType::PpHvbox => break_new_line(state, breaks, width),
                    BoxType::PpFits => break_same_line(state, fits),
                    BoxType::PpVbox => break_new_line(state, breaks, width),
                    BoxType::PpHbox => break_same_line(state, fits),
                },
            }
        }
    }
}

/// Print if token size is known else printing is delayed.
/// Printing is delayed when the text waiting in the queue requires
/// more room to format than exists on the current line.
fn advance_left(state: &mut Formatter) {
    loop {
        match state.pp_queue.front().cloned() {
            None => return, // No tokens to print
            Some(elem) => {
                let size = elem.size.get();
                let pending_count = state.pp_right_total - state.pp_left_total;
                if size::is_known(size) || pending_count >= state.pp_space_left {
                    // Not empty: we peek into it
                    state.pp_queue.pop_front();
                    let size = if size::is_known(size) {
                        size
                    } else {
                        PP_INFINITY
                    };
                    format_pp_token(state, size, &elem.token);
                    state.pp_left_total = elem.length + state.pp_left_total;
                } else {
                    return;
                }
            }
        }
    }
}

/// To enqueue a token : try to advance.
fn enqueue_advance(state: &mut Formatter, tok: Rc<PpQueueElem>) {
    pp_enqueue(state, tok);
    advance_left(state)
}

/// To enqueue strings.
fn enqueue_string_as(state: &mut Formatter, size: Size, s: &str) {
    enqueue_advance(
        state,
        Rc::new(PpQueueElem {
            size: Cell::new(size),
            token: PpToken::PpText(s.to_string()),
            length: size,
        }),
    )
}

fn enqueue_string(state: &mut Formatter, s: &str) {
    enqueue_string_as(state, s.len() as isize, s)
}

// Routines for scan stack
// determine size of boxes.

/// The scan_stack is never empty.
fn initialize_scan_stack(stack: &mut Vec<PpScanElem>) {
    stack.clear();
    let queue_elem = Rc::new(PpQueueElem {
        size: Cell::new(size::UNKNOWN),
        token: PpToken::PpText(String::new()),
        length: 0,
    });
    stack.push(PpScanElem {
        left_total: -1,
        queue_elem,
    })
}

/// Setting the size of boxes on scan stack:
/// if ty = true then size of break is set else size of box is set;
/// in each case pp_scan_stack is popped.
fn set_size(state: &mut Formatter, ty: bool) {
    let (left_total, queue_elem) = match state.pp_scan_stack.last() {
        None => return, // scan_stack is never empty.
        Some(PpScanElem {
            left_total,
            queue_elem,
        }) => (*left_total, Rc::clone(queue_elem)),
    };
    let size = queue_elem.size.get();
    // test if scan stack contains any data that is not obsolete.
    if left_total < state.pp_left_total {
        initialize_scan_stack(&mut state.pp_scan_stack)
    } else {
        match queue_elem.token {
            PpToken::PpBreak { .. } => {
                if ty {
                    queue_elem.size.set(state.pp_right_total + size);
                    state.pp_scan_stack.pop();
                }
            }
            PpToken::PpBegin(_, _) => {
                if !ty {
                    queue_elem.size.set(state.pp_right_total + size);
                    state.pp_scan_stack.pop();
                }
            }
            // scan_push is only used for breaks and boxes.
            PpToken::PpText(_) | PpToken::PpEnd | PpToken::PpNewline => (),
        }
    }
}

/// Push a token on pretty-printer scanning stack.
/// If b is true set_size is called.
fn scan_push(state: &mut Formatter, b: bool, token: Rc<PpQueueElem>) {
    pp_enqueue(state, Rc::clone(&token));
    if b {
        set_size(state, true)
    }
    let elem = PpScanElem {
        left_total: state.pp_right_total,
        queue_elem: token,
    };
    state.pp_scan_stack.push(elem)
}

/// To open a new box :
/// the user may set the depth bound pp_max_boxes
/// any text nested deeper is printed as the ellipsis string.
pub fn pp_open_box_gen(state: &mut Formatter, indent: isize, br_ty: BoxType) {
    state.pp_curr_depth = state.pp_curr_depth + 1;
    if state.pp_curr_depth < state.pp_max_boxes {
        let size = -state.pp_right_total;
        let elem = Rc::new(PpQueueElem {
            size: Cell::new(size),
            token: PpToken::PpBegin(indent, br_ty),
            length: 0,
        });
        scan_push(state, false, elem)
    } else if state.pp_curr_depth == state.pp_max_boxes {
        let ellipsis = state.pp_ellipsis.clone();
        enqueue_string(state, &ellipsis)
    }
}

/// The box which is always open.
fn pp_open_sys_box(state: &mut Formatter) {
    pp_open_box_gen(state, 0, BoxType::PpHovbox)
}

/// Close a box, setting sizes of its sub boxes.
pub fn pp_close_box(state: &mut Formatter) {
    if state.pp_curr_depth > 1 {
        if state.pp_curr_depth < state.pp_max_boxes {
            pp_enqueue(
                state,
                Rc::new(PpQueueElem {
                    size: Cell::new(size::ZERO),
                    token: PpToken::PpEnd,
                    length: 0,
                }),
            );
            set_size(state, true);
            set_size(state, false)
        }
        state.pp_curr_depth = state.pp_curr_depth - 1;
    }
}

/// Initialize pretty-printer.
fn pp_rinit(state: &mut Formatter) {
    pp_clear_queue(state);
    initialize_scan_stack(&mut state.pp_scan_stack);
    state.pp_format_stack.clear();
    state.pp_current_indent = 0;
    state.pp_curr_depth = 0;
    state.pp_space_left = state.pp_margin;
    pp_open_sys_box(state)
}

/// Flushing pretty-printer queue. (`clear_tag_stack` closes the semantic
/// tags, which are not ported: there are none to close.)
fn pp_flush_queue(state: &mut Formatter, end_with_newline: bool) {
    while state.pp_curr_depth > 1 {
        pp_close_box(state)
    }
    state.pp_right_total = PP_INFINITY;
    advance_left(state);
    if end_with_newline {
        pp_output_newline(state)
    }
    pp_rinit(state)
}

// ~~ Procedures to format values and use boxes ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// To format a string.
fn pp_print_as_size(state: &mut Formatter, size: Size, s: &str) {
    if state.pp_curr_depth < state.pp_max_boxes {
        enqueue_string_as(state, size, s)
    }
}

pub fn pp_print_as(state: &mut Formatter, isize: isize, s: &str) {
    pp_print_as_size(state, isize, s)
}

pub fn pp_print_string(state: &mut Formatter, s: &str) {
    pp_print_as(state, s.len() as isize, s)
}

/// To format a char. (An OCaml `char` is a byte: give an ASCII character.)
pub fn pp_print_char(state: &mut Formatter, c: char) {
    pp_print_as(state, 1, &c.to_string())
}

/// Opening boxes.
pub fn pp_open_hbox(state: &mut Formatter) {
    pp_open_box_gen(state, 0, BoxType::PpHbox)
}

pub fn pp_open_vbox(state: &mut Formatter, indent: isize) {
    pp_open_box_gen(state, indent, BoxType::PpVbox)
}

pub fn pp_open_hvbox(state: &mut Formatter, indent: isize) {
    pp_open_box_gen(state, indent, BoxType::PpHvbox)
}

pub fn pp_open_hovbox(state: &mut Formatter, indent: isize) {
    pp_open_box_gen(state, indent, BoxType::PpHovbox)
}

pub fn pp_open_box(state: &mut Formatter, indent: isize) {
    pp_open_box_gen(state, indent, BoxType::PpBox)
}

/// [`pp_print_flush`] prints all pending items in the pretty-printer queue
/// and then flushes the low level output device of the formatter to actually
/// display printing material.
///
/// [`pp_print_newline`] behaves as [`pp_print_flush`] after printing an
/// additional new line.
pub fn pp_print_newline(state: &mut Formatter) {
    pp_flush_queue(state, true);
    pp_out_flush(state)
}

/// To force a line break inside a box: no box is broken, only the line
/// (`@\n`).
pub fn pp_force_newline(state: &mut Formatter) {
    if state.pp_curr_depth < state.pp_max_boxes {
        enqueue_advance(
            state,
            Rc::new(PpQueueElem {
                size: Cell::new(0),
                token: PpToken::PpNewline,
                length: 0,
            }),
        )
    }
}

pub fn pp_print_flush(state: &mut Formatter) {
    pp_flush_queue(state, false);
    pp_out_flush(state)
}

/// Generalized break hint that allows printing strings before/after
/// same-line offset (width) or new-line offset
pub fn pp_print_custom_break(
    state: &mut Formatter,
    fits: (String, isize, String),
    breaks: (String, isize, String),
) {
    let (before, width, after) = &fits;
    if state.pp_curr_depth < state.pp_max_boxes {
        let size = -state.pp_right_total;
        let length = before.len() as isize + width + after.len() as isize;
        let token = PpToken::PpBreak { fits, breaks };
        let elem = Rc::new(PpQueueElem {
            size: Cell::new(size),
            token,
            length,
        });
        scan_push(state, true, elem)
    }
}

/// Printing break hints:
/// A break hint indicates where a box may be broken.
/// If line is broken then offset is added to the indentation of the current
/// box else (the value of) width blanks are printed.
pub fn pp_print_break(state: &mut Formatter, width: isize, offset: isize) {
    pp_print_custom_break(
        state,
        (String::new(), width, String::new()),
        (String::new(), offset, String::new()),
    )
}

/// Print a space :
/// a space is a break hint that prints a single space if the break does not
/// split the line;
/// a cut is a break hint that prints nothing if the break does not split the
/// line.
pub fn pp_print_space(state: &mut Formatter) {
    pp_print_break(state, 1, 0)
}

pub fn pp_print_cut(state: &mut Formatter) {
    pp_print_break(state, 0, 0)
}

// ~~ Procedures to control the pretty-printers ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// To set the margin of pretty-printer.
fn pp_limit(n: isize) -> isize {
    if n < PP_INFINITY { n } else { PP_INFINITY - 1 }
}

/// Internal pretty-printer functions.
pub fn pp_set_min_space_left(state: &mut Formatter, n: isize) {
    if n >= 1 {
        let n = pp_limit(n);
        state.pp_min_space_left = n;
        state.pp_max_indent = state.pp_margin - state.pp_min_space_left;
        pp_rinit(state)
    }
}

/// Initially, we have :
/// pp_max_indent = pp_margin - pp_min_space_left, and
/// pp_space_left = pp_margin.
pub fn pp_set_max_indent(state: &mut Formatter, n: isize) {
    if n > 1 {
        pp_set_min_space_left(state, state.pp_margin - n)
    }
}

pub fn pp_get_max_indent(state: &Formatter) -> isize {
    state.pp_max_indent
}

pub fn pp_set_margin(state: &mut Formatter, n: isize) {
    if n >= 1 {
        let n = pp_limit(n);
        state.pp_margin = n;
        let new_max_indent =
            // Try to maintain max_indent to its actual value.
            if state.pp_max_indent <= state.pp_margin {
                state.pp_max_indent
            } else {
                // If possible maintain pp_min_space_left to its actual value,
                // if this leads to a too small max_indent, take half of the
                // new margin, if it is greater than 1.
                std::cmp::max(
                    std::cmp::max(
                        state.pp_margin - state.pp_min_space_left,
                        state.pp_margin / 2,
                    ),
                    1,
                )
            };
        // Rebuild invariants.
        pp_set_max_indent(state, new_max_indent)
    }
}

pub fn pp_get_margin(state: &Formatter) -> isize {
    state.pp_margin
}

/// The default function to output new lines.
fn display_newline(state: &mut Formatter) {
    pp_out_string(state, "\n")
}

/// The default function to output spaces.
const BLANK_LINE: &str =
    "                                                                                ";

fn display_blanks(state: &mut Formatter, n: isize) {
    if n > 0 {
        if n <= 80 {
            pp_out_string(state, &BLANK_LINE[..n as usize])
        } else {
            pp_out_string(state, BLANK_LINE);
            display_blanks(state, n - 80)
        }
    }
}

/// The default function to output indentation of new lines.
fn display_indent(state: &mut Formatter, n: isize) {
    display_blanks(state, n)
}

// ~~ Defining specific formatters ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// Building a formatter given its basic output functions.
/// Other fields get reasonable default values.
fn pp_make_formatter(out: Output) -> Formatter {
    // The initial state of the formatter contains a dummy box.
    let mut pp_queue = VecDeque::new();
    let sys_tok = Rc::new(PpQueueElem {
        size: Cell::new(size::UNKNOWN),
        token: PpToken::PpBegin(0, BoxType::PpHovbox),
        length: 0,
    });
    pp_queue.push_back(Rc::clone(&sys_tok));
    let mut scan_stack = Vec::new();
    initialize_scan_stack(&mut scan_stack);
    scan_stack.push(PpScanElem {
        left_total: 1,
        queue_elem: sys_tok,
    });
    let pp_margin = 78;
    let pp_min_space_left = 10;
    Formatter {
        pp_scan_stack: scan_stack,
        pp_format_stack: Vec::new(),
        pp_margin,
        pp_min_space_left,
        pp_max_indent: pp_margin - pp_min_space_left,
        pp_space_left: pp_margin,
        pp_current_indent: 0,
        pp_is_new_line: true,
        pp_left_total: 1,
        pp_right_total: 1,
        pp_curr_depth: 1,
        pp_max_boxes: isize::MAX,
        pp_ellipsis: ".".to_string(),
        pp_out: out,
        pp_queue,
    }
}

/// Make a formatter with default functions to output spaces,
/// indentation, and new lines.
fn make_formatter(out: Output) -> Formatter {
    pp_make_formatter(out)
}

/// Make a formatter writing to a given [`std::io::Write`] (`Stdlib.out_channel`).
pub fn formatter_of_out_channel(oc: Box<dyn std::io::Write>) -> Formatter {
    make_formatter(Output::Channel(oc))
}

/// Make a formatter writing to a given buffer (`Buffer.t`), which the
/// formatter owns: [`flush_buffer_formatter`] gives its contents.
pub fn formatter_of_buffer(b: String) -> Formatter {
    make_formatter(Output::Buffer(b))
}

/// Allocating buffer for pretty-printing purposes.
/// Default buffer size is pp_buffer_size or 512.
const PP_BUFFER_SIZE: usize = 512;

fn pp_make_buffer() -> String {
    String::with_capacity(PP_BUFFER_SIZE)
}

/// [`flush_buffer_formatter`] flushes formatter `ppf`, then returns the
/// contents of its buffer, which is reset. (In OCaml it takes the buffer as
/// well: here the formatter owns it.) For a formatter that does not write to
/// a buffer, it flushes the queue and returns the empty string.
pub fn flush_buffer_formatter(ppf: &mut Formatter) -> String {
    pp_flush_queue(ppf, false);
    match &mut ppf.pp_out {
        Output::Buffer(buf) => std::mem::take(buf),
        Output::Channel(_) => String::new(),
    }
}

/// `Format.asprintf fmt args`: `printer` makes the calls that the format
/// string makes (see the module documentation) on a fresh formatter writing
/// to a buffer, whose contents are returned. `Format.asprintf "%a" pp v` is
/// `asprintf(|ppf| pp(ppf, v))`.
pub fn asprintf(printer: impl FnOnce(&mut Formatter)) -> String {
    let b = pp_make_buffer();
    let mut ppf = formatter_of_buffer(b);
    printer(&mut ppf);
    flush_buffer_formatter(&mut ppf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(ppf: &mut Formatter, n: usize, word: &str) {
        for i in 0..n {
            if i > 0 {
                pp_print_space(ppf)
            }
            pp_print_string(ppf, word)
        }
    }

    // The expected outputs are those of OCaml 5's `Format.asprintf` for the
    // same calls.

    #[test]
    fn text_and_breaks() {
        assert_eq!(asprintf(|ppf| pp_print_string(ppf, "abc")), "abc");
        // The system box is never closed, so the size of its last break hint
        // is not known when the queue is flushed: the line breaks there.
        assert_eq!(
            asprintf(|ppf| {
                pp_print_string(ppf, "a");
                pp_print_space(ppf);
                pp_print_string(ppf, "b");
                pp_print_cut(ppf);
                pp_print_string(ppf, "c");
            }),
            "a b\nc"
        );
        assert_eq!(
            asprintf(|ppf| {
                pp_print_string(ppf, "a");
                pp_print_space(ppf);
                pp_print_string(ppf, "b");
            }),
            "a\nb"
        );
        assert_eq!(asprintf(|ppf| words(ppf, 3, "x")), "x x\nx");
        assert_eq!(
            asprintf(|ppf| {
                pp_print_string(ppf, "1");
                pp_print_string(ppf, ",");
                pp_print_space(ppf);
                pp_print_string(ppf, "2");
            }),
            "1,\n2"
        );
        assert_eq!(
            asprintf(|ppf| {
                pp_print_string(ppf, "inout");
                pp_print_space(ppf);
            }),
            "inout\n"
        );
        assert_eq!(
            asprintf(|ppf| {
                pp_print_space(ppf);
                pp_print_string(ppf, "&");
                pp_print_space(ppf);
            }),
            " &\n"
        );
        // In a box that is closed, the sizes are known.
        assert_eq!(
            asprintf(|ppf| {
                // "(@[%s,@ %S@])"
                pp_print_char(ppf, '(');
                pp_open_box(ppf, 0);
                pp_print_string(ppf, "[Pos.none]");
                pp_print_char(ppf, ',');
                pp_print_space(ppf);
                pp_print_string(ppf, "\"\\\\M\\\"\"");
                pp_close_box(ppf);
                pp_print_char(ppf, ')');
            }),
            "([Pos.none], \"\\\\M\\\"\")"
        );
        // Boxes print nothing by themselves.
        assert_eq!(
            asprintf(|ppf| {
                pp_open_box(ppf, 2);
                words(ppf, 3, "x");
                pp_close_box(ppf);
            }),
            "x x x"
        );
        // A box that is not closed is closed by the flush.
        assert_eq!(
            asprintf(|ppf| {
                pp_open_hovbox(ppf, 0);
                words(ppf, 2, "y");
            }),
            "y y"
        );
    }

    #[test]
    fn vertical_boxes_break_at_every_hint() {
        assert_eq!(
            asprintf(|ppf| {
                pp_open_vbox(ppf, 2);
                words(ppf, 3, "ab");
                pp_close_box(ppf);
            }),
            "ab\n  ab\n  ab"
        );
        // An hvbox that fits is horizontal, one that does not is vertical.
        assert_eq!(
            asprintf(|ppf| {
                pp_open_hvbox(ppf, 1);
                words(ppf, 3, "ab");
                pp_close_box(ppf);
            }),
            "ab ab ab"
        );
        assert_eq!(
            asprintf(|ppf| {
                pp_open_hvbox(ppf, 1);
                words(ppf, 3, &"w".repeat(30));
                pp_close_box(ppf);
            }),
            format!("{0}\n {0}\n {0}", "w".repeat(30))
        );
        // An hbox never breaks.
        assert_eq!(
            asprintf(|ppf| {
                pp_open_hbox(ppf);
                words(ppf, 3, &"w".repeat(30));
                pp_close_box(ppf);
            }),
            format!("{0} {0} {0}", "w".repeat(30))
        );
    }

    #[test]
    fn compacting_boxes_fill_the_margin() {
        // In 78 columns, 19 words fit on the first line (19 * 3 + 18 = 75
        // columns with the spaces in between): the 20th would end at 79.
        let printed = asprintf(|ppf| {
            pp_open_hovbox(ppf, 0);
            words(ppf, 30, "abc");
            pp_close_box(ppf);
        });
        let lines: Vec<&str> = printed.split('\n').collect();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0], vec!["abc"; 19].join(" "));
        assert_eq!(lines[1], vec!["abc"; 11].join(" "));
        // The margin can be changed.
        let printed = asprintf(|ppf| {
            pp_set_margin(ppf, 10);
            pp_open_hovbox(ppf, 2);
            words(ppf, 5, "abc");
            pp_close_box(ppf);
        });
        assert_eq!(printed, "abc abc\n  abc abc\n  abc");
        assert_eq!(pp_get_max_indent(&formatter_of_buffer(String::new())), 68);
        // A vertical box of short items.
        assert_eq!(
            asprintf(|ppf| {
                pp_open_vbox(ppf, 2);
                words(ppf, 3, "1");
                pp_close_box(ppf);
            }),
            "1\n  1\n  1"
        );
    }

    #[test]
    fn margin_200_keeps_max_indent() {
        let mut ppf = formatter_of_buffer(String::new());
        pp_set_margin(&mut ppf, 200);
        assert_eq!(pp_get_margin(&ppf), 200);
        assert_eq!(pp_get_max_indent(&ppf), 68);
    }
}
