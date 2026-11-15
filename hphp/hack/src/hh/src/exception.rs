// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/core/exception.ml`. See `hh/PORTING.md`.
//!
//! An OCaml `exn` that is caught and wrapped is one of two things here:
//!
//! - the payload of a panic that was caught (`std::panic::catch_unwind`):
//!   `failwith`, `assert false` and the exceptions nothing is meant to catch
//!   are panics in this port;
//! - the error value of a `Result`, for the exceptions the port turned into
//!   error enums.
//!
//! [`wrap`] takes either, and [`reraise`] raises it again as a panic with the
//! same payload (so a caught panic goes on unchanged).
//!
//! Backtraces are `std::backtrace::Backtrace`s, which look nothing like
//! OCaml's. As in OCaml, the backtrace of a wrapped exception is only there
//! when backtraces are enabled (`RUST_BACKTRACE`, for `OCAMLRUNPARAM=b`),
//! while [`get_current_callstack_string`] always captures one. They only ever
//! go to logs and telemetry.

use std::any::Any;
use std::backtrace::Backtrace;
use std::backtrace::BacktraceStatus;
use std::fmt::Debug;

pub struct T {
    exn: Box<dyn Any + Send>,
    /// `Printexc.to_string exn`, kept because the payload is opaque.
    ctor: String,
    backtrace: Backtrace,
    /// Where the panic was raised, when the catcher knows it (see
    /// [`wrap_with_raise_site`]).
    raised_at: Option<String>,
}

impl Debug for T {
    /// `show`
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.ctor)
    }
}

/// The message of a panic payload, when it has one (`panic!` gives a `&str`
/// or a `String`).
fn string_of_payload(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(e) = position_not_found(payload) {
        e
    } else if let Some(e) = typechecker_exception(payload) {
        e
    } else {
        "<exception>".to_string()
    }
}

/// `Printexc.to_string` of the exceptions of the typechecker that are panic
/// payloads of their own: `Decl_defs.Decl_not_found`,
/// `Typing_inference_env.InconsistentTypeVarState`, and the OCaml's own
/// exceptions raised as `rt::ocaml_exn::Uncaught` (`Stack_overflow`).
#[cfg(feature = "port")]
fn typechecker_exception(payload: &(dyn Any + Send)) -> Option<String> {
    if let Some(e) = payload.downcast_ref::<crate::rt::ocaml_exn::Uncaught>() {
        Some(e.to_string())
    } else if let Some(e) = payload.downcast_ref::<crate::decl_defs::DeclNotFound>() {
        Some(e.to_string())
    } else {
        payload
            .downcast_ref::<crate::typing_inference_env::InconsistentTypeVarState>()
            .map(|e| e.to_string())
    }
}

#[cfg(not(feature = "port"))]
fn typechecker_exception(_payload: &(dyn Any + Send)) -> Option<String> {
    None
}

/// `Line_break_map.Position_not_found(line, column, num_lines)`, a panic
/// payload of its own (see `full_fidelity_source_text`).
#[cfg(feature = "port")]
fn position_not_found(payload: &(dyn Any + Send)) -> Option<String> {
    payload
        .downcast_ref::<crate::full_fidelity_source_text::PositionNotFound>()
        .map(|p| {
            format!(
                "Line_break_map.Position_not_found({}, {}, {})",
                p.line, p.column, p.num_lines_in_file
            )
        })
}

#[cfg(not(feature = "port"))]
fn position_not_found(_payload: &(dyn Any + Send)) -> Option<String> {
    None
}

/// In ocaml, backtraces (the path that the exception bubbled up after being
/// thrown) are stored as global state and NOT with the exception itself. This
/// means the only safe place to ever read the backtrace is immediately after
/// the exception is caught.
///
/// `exn` is an error value or the payload of a caught panic.
pub fn wrap<E: Debug + Send + 'static>(exn: E) -> T {
    let backtrace = Backtrace::capture();
    let ctor = format!("{:?}", exn);
    let exn: Box<dyn Any + Send> = Box::new(exn);
    // A caught panic is already a boxed payload: keep it as it is, so that
    // `reraise` resumes the same panic.
    match exn.downcast::<Box<dyn Any + Send>>() {
        Ok(payload) => {
            let payload: Box<dyn Any + Send> = *payload;
            let ctor = string_of_payload(&*payload);
            T {
                exn: payload,
                ctor,
                backtrace,
                raised_at: None,
            }
        }
        Err(exn) => T {
            exn,
            ctor,
            backtrace,
            raised_at: None,
        },
    }
}

/// [`wrap`] of the payload of a panic that the panic hook did not print
/// (`rt::quiet_panic`), with where it was raised: the backtrace string of
/// the exception is then `panicked at FILE:LINE:COLUMN` (and the Rust
/// backtrace of that point when backtraces are enabled), where the OCaml's
/// is the backtrace it recorded when the exception was raised
/// (`Printexc.record_backtrace true`). The frames of the two languages have
/// nothing in common; what a log reader gets in both is the exception, then
/// lines that say where it was raised.
pub fn wrap_with_raise_site(
    payload: Box<dyn Any + Send>,
    site: Option<crate::rt::quiet_panic::RaiseSite>,
) -> T {
    let mut t = wrap(payload);
    if let Some(site) = site {
        t.raised_at = site.location.map(|l| format!("panicked at {}", l));
        t.backtrace = site.backtrace;
    }
    t
}

/// `Exception.unwrap`: the exception (the panic payload, or the error value
/// that was wrapped), to downcast.
pub fn unwrap(t: &T) -> &(dyn Any + Send) {
    &*t.exn
}

pub fn reraise(t: T) -> ! {
    std::panic::resume_unwind(t.exn)
}

pub fn get_ctor_string(t: &T) -> String {
    t.ctor.clone()
}

pub fn get_backtrace_string(t: &T) -> String {
    let backtrace = match t.backtrace.status() {
        BacktraceStatus::Captured => t.backtrace.to_string(),
        _ => String::new(),
    };
    match &t.raised_at {
        None => backtrace,
        Some(raised_at) if backtrace.is_empty() => raised_at.clone(),
        Some(raised_at) => format!("{}\n{}", raised_at, backtrace),
    }
}

pub fn to_string(t: &T) -> String {
    let ctor = get_ctor_string(t);
    let bt = get_backtrace_string(t);
    if bt.is_empty() {
        ctor
    } else {
        format!("{}\n{}", ctor, bt)
    }
}

/// Whether `line` starts a frame of a printed `Backtrace` (`  12: symbol`).
fn is_frame_header(line: &str) -> bool {
    let line = line.trim_start();
    let digits = line.bytes().take_while(u8::is_ascii_digit).count();
    digits > 0 && line[digits..].starts_with(": ")
}

/// The callstack at this point, at most `n` frames of it.
pub fn get_current_callstack_string(n: isize) -> String {
    let stack = Backtrace::force_capture().to_string();
    let mut res = String::new();
    let mut frames: isize = 0;
    for line in stack.split_inclusive('\n') {
        if is_frame_header(line) {
            frames += 1;
        }
        if frames > n {
            break;
        }
        res.push_str(line);
    }
    res
}

/// The rest of `stack_re` after the optional module: ` file "<file>"`, an
/// optional ` (inlined)`, `, line <line>, character` and anything. Returns
/// the file and the line.
fn stack_re_match_file_and_line(s: &str) -> Option<(&str, &str)> {
    let s = s.strip_prefix(" file \"")?;
    let quote = s.find('"')?;
    let file = &s[..quote];
    let s = &s[quote + 1..];
    let s = s.strip_prefix(" (inlined)").unwrap_or(s);
    let s = s.strip_prefix(", line ")?;
    let digits = s.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return None;
    }
    let line = &s[..digits];
    s[digits..].strip_prefix(", character")?;
    Some((file, line))
}

/// `stack_re`:
/// `^\(Called from\|Raised by primitive operation at\|Raised at\|Re-raised at\)\( \([^ ]*\) in\)? file "\([^"]*\)"\( (inlined)\)?, line \([0-9]+\), character.*$`.
/// Returns the module (group 3, `""` when it is not there), the file
/// (group 4) and the line (group 6).
fn stack_re_match(s: &str) -> Option<(&str, &str, &str)> {
    let rest = [
        "Called from",
        "Raised by primitive operation at",
        "Raised at",
        "Re-raised at",
    ]
    .iter()
    .find_map(|prefix| s.strip_prefix(prefix))?;
    // ` <module> in`, when what follows it matches too.
    let with_module = || {
        let rest = rest.strip_prefix(' ')?;
        let module_len = rest.find(' ').unwrap_or(rest.len());
        let module_ = &rest[..module_len];
        let rest = rest[module_len..].strip_prefix(" in")?;
        let (file, line) = stack_re_match_file_and_line(rest)?;
        Some((module_, file, line))
    };
    with_module().or_else(|| {
        let (file, line) = stack_re_match_file_and_line(rest)?;
        Some(("", file, line))
    })
}

/// We want to include all stack lines that come from our code, and exclude
/// ones that come from the standard library. That's easy for stack lines that
/// include a module: if the module starts "Stdlib" or "Base" then exclude it;
/// if it starts with anything else then include it. But for stack lines that
/// don't include a module then we'll use a heuristic that only works on some
/// build systems. Some build systems like buck include absolute pathnames so
/// that "/.../hack/src/hh_client.ml" implies it's our code and "src/list.ml"
/// implies it's not. Other build systems like dune are relative and there's
/// no way we can distinguish "src/hh_client.ml" from "src/list.ml". Our
/// heuristic will simply assume buck-style absolute pathnames.
///
/// (The lines of a Rust backtrace have another shape: they are kept as they
/// are, like every line the regular expression does not match.)
pub fn clean_stack(stack: &str) -> String {
    let format_one_line = |s: &str| -> Option<String> {
        match stack_re_match(s) {
            Some((module_, file, line)) => {
                // `file_re`: `^.*/hack/\(.*\)$`
                let (file, file_is_in_hack_src_tree) = match file.rfind("/hack/") {
                    Some(i) => (&file[i + "/hack/".len()..], true),
                    None => (file, false),
                };
                if module_.is_empty() {
                    if file_is_in_hack_src_tree {
                        Some(format!("{} @ {}", file, line))
                    } else {
                        None
                    }
                } else if module_.starts_with("Base")
                    || module_.starts_with("Stdlib")
                    || module_.starts_with("Lwt")
                {
                    None
                } else {
                    Some(format!("{} @ {}", file, line))
                }
            }
            None => Some(s.to_string()),
        }
    };
    crate::string_utils::split_on_newlines(stack)
        .into_iter()
        .filter_map(|line| format_one_line(&line))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_ocaml_stack() {
        let stack = [
            // No module, in the hack tree: kept.
            r#"Raised at file "/data/fbsource/hphp/hack/src/typing/typing.ml", line 12, characters 4-20"#,
            // No module, not in the hack tree: dropped.
            r#"Called from file "src/list.ml", line 110, characters 6-23"#,
            // A module of the standard library: dropped.
            r#"Called from Stdlib__List.iter in file "list.ml", line 110, characters 12-15"#,
            r#"Called from Base__List.map in file "/x/hack/src/list.ml" (inlined), line 1, characters 1-2"#,
            r#"Called from Lwt.bind in file "lwt.ml", line 1, characters 1-2"#,
            // Another module: kept, with the path below `hack/` if it has one.
            r#"Called from Typing_env.get in file "/data/hack/src/hack/typing/env.ml" (inlined), line 7, characters 1-2"#,
            r#"Re-raised at Decl.f in file "decl.ml", line 30, characters 1-2"#,
            r#"Raised by primitive operation at Foo.bar in file "foo.ml", line 3, characters 5-9"#,
            // Not a stack line: kept as it is.
            "Fatal error: exception Not_found",
            // No line number: not a stack line.
            r#"Called from file "/hack/a.ml", line x, characters 1-2"#,
            // Lines with the word `character` only.
            r#"Called from file "/hack/a.ml", line 5, character"#,
        ]
        .join("\n");
        let expected = [
            "src/typing/typing.ml @ 12",
            "typing/env.ml @ 7",
            "decl.ml @ 30",
            "foo.ml @ 3",
            "Fatal error: exception Not_found",
            r#"Called from file "/hack/a.ml", line x, characters 1-2"#,
            "a.ml @ 5",
        ]
        .join("\n");
        assert_eq!(clean_stack(&stack), expected);
        // The line after a trailing newline is not a line.
        assert_eq!(clean_stack(&format!("{}\n", stack)), expected);
        assert_eq!(clean_stack(""), "");
    }

    #[test]
    fn module_named_like_the_pattern() {
        // `\( \([^ ]*\) in\)?` first tries to match a module.
        assert_eq!(
            clean_stack(r#"Called from file in file "x.ml", line 1, characters 1-2"#),
            "x.ml @ 1"
        );
        // An empty module is no module.
        assert_eq!(
            clean_stack(r#"Called from  in file "x.ml", line 1, characters 1-2"#),
            ""
        );
        assert_eq!(
            clean_stack(r#"Called from  in file "/a/hack/x.ml", line 1, characters 1-2"#),
            "x.ml @ 1"
        );
        // The prefix has to be at the start of the line.
        let line = r#" Called from file "/a/hack/x.ml", line 1, characters 1-2"#;
        assert_eq!(clean_stack(line), line);
    }

    #[test]
    fn rust_stack_is_kept() {
        let stack = get_current_callstack_string(3);
        assert!(!stack.is_empty());
        assert!(stack.lines().filter(|l| is_frame_header(l)).count() <= 3);
        assert_eq!(clean_stack(&stack), stack.trim_end_matches('\n'));
        assert_eq!(get_current_callstack_string(0), "");
    }

    #[test]
    fn wrap_and_reraise() {
        #[derive(Debug)]
        #[allow(dead_code)]
        enum Error {
            InconsistentTypeVarState(String),
        }
        let e = wrap(Error::InconsistentTypeVarState("x".to_string()));
        assert_eq!(get_ctor_string(&e), "InconsistentTypeVarState(\"x\")");
        assert!(to_string(&e).starts_with("InconsistentTypeVarState(\"x\")"));
        let payload =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| reraise(e))).unwrap_err();
        assert!(payload.downcast_ref::<Error>().is_some());

        // A caught panic is wrapped as it is and resumed unchanged.
        let payload =
            std::panic::catch_unwind(|| std::panic::panic_any("boom".to_string())).unwrap_err();
        let e = wrap(payload);
        assert_eq!(get_ctor_string(&e), "boom");
        let payload =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| reraise(e))).unwrap_err();
        assert_eq!(payload.downcast_ref::<String>().unwrap(), "boom");
    }
}
