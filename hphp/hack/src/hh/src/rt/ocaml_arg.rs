// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `stdlib/arg.ml` (OCaml 5.2's `Stdlib.Arg`), as far as the command
//! lines of the server layer use it: the specs, [`parse_argv`] and [`parse`],
//! [`align`], [`usage_string`] and [`usage`], with `Arg`'s own messages
//! (`hh_client: unknown option '--foo'.`), padding and `-help`/`--help`
//! entries, byte for byte. See `hh/PORTING.md`, "The server layer".
//!
//! # How the OCaml maps
//!
//! - A spec's function is a boxed closure that returns `Result<(), Exn<E>>`:
//!   `raise (Arg.Bad m)` in it is `Err(Exn::Bad(m))`. The other OCaml
//!   exceptions that the functions of a spec list raise (`Exit_status.Exit_with`,
//!   ...) are `Err(Exn::Raise(e))`, of the error type `E` of the list
//!   (PORTING.md, "Exceptions"; `E` is `Infallible` when they raise none):
//!   they go through [`parse_argv`] and [`parse`] unchanged, as they go
//!   through `Arg.parse_argv` and `Arg.parse`.
//! - `bool ref`, `string ref`, ... (`Set`, `Set_string`, ...) are `&Cell` /
//!   `&RefCell`: the specs borrow the variables the caller declared, for the
//!   lifetime `'a` of the spec list.
//! - The exceptions `Bad`, `Help` and the internal `Stop` are [`Exn`];
//!   [`parse_argv`] returns `Err(Exn::Bad(..))` or `Err(Exn::Help(..))` where
//!   `Arg.parse_argv` raises them, `Err(Exn::Raise(..))` for what a spec's
//!   function raised, and never `Exn::Stop`.
//! - `Arg.current` is per thread ([`with_current`]), so that tests can run in
//!   parallel; a program has one thread that parses its command line.
//!
//! Not emulated: `Expand` and the `parse_*_dynamic` / `parse_expand` variants
//! (their spec list is a `ref` that the specs may change), `read_arg`,
//! `write_arg` (and their `0` variants). Nothing in the server layer uses
//! them.
//!
//! Strings are Rust `String`s: lengths and offsets are in bytes, as OCaml's.

use std::cell::Cell;
use std::cell::RefCell;
use std::convert::Infallible;
use std::fmt::Write as _;
use std::io::Write as _;

use crate::rt::ocaml_stdlib;

pub type Key = String;
pub type Doc = String;
pub type UsageMsg = String;

/// The result of the function of a spec: `Ok(())`, or the exception it
/// raises.
pub type Res<E = Infallible> = Result<(), Exn<E>>;

/// `Arg.spec`
pub enum Spec<'a, E = Infallible> {
    /// Call the function with unit argument
    Unit(Box<dyn FnMut() -> Res<E> + 'a>),
    /// Call the function with a bool argument
    Bool(Box<dyn FnMut(bool) -> Res<E> + 'a>),
    /// Set the reference to true
    Set(&'a Cell<bool>),
    /// Set the reference to false
    Clear(&'a Cell<bool>),
    /// Call the function with a string argument
    String(Box<dyn FnMut(String) -> Res<E> + 'a>),
    /// Set the reference to the string argument
    SetString(&'a RefCell<String>),
    /// Call the function with an int argument
    Int(Box<dyn FnMut(isize) -> Res<E> + 'a>),
    /// Set the reference to the int argument
    SetInt(&'a Cell<isize>),
    /// Call the function with a float argument
    Float(Box<dyn FnMut(f64) -> Res<E> + 'a>),
    /// Set the reference to the float argument
    SetFloat(&'a Cell<f64>),
    /// Take several arguments according to the spec list
    Tuple(Vec<Spec<'a, E>>),
    /// Take one of the symbols as argument and call the function with the
    /// symbol.
    Symbol(Vec<String>, Box<dyn FnMut(String) -> Res<E> + 'a>),
    /// Stop interpreting keywords and call the function with each remaining
    /// argument
    Rest(Box<dyn FnMut(String) -> Res<E> + 'a>),
    /// Stop interpreting keywords and call the function with all remaining
    /// arguments.
    RestAll(Box<dyn FnMut(Vec<String>) -> Res<E> + 'a>),
}

/// A spec list: `(key * spec * doc) list`.
pub type Speclist<'a, E = Infallible> = Vec<(Key, Spec<'a, E>, Doc)>;

/// `Arg.anon_fun`
pub type AnonFun<'b, E = Infallible> = dyn FnMut(String) -> Res<E> + 'b;

/// The exceptions of `Arg`: `Bad` and `Help`, which it exports, and `Stop`,
/// which it uses internally; and `Raise`, any other exception that the
/// function of a spec raises.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exn<E = Infallible> {
    /// `exception Bad of string`
    Bad(String),
    /// `exception Help of string`
    Help(String),
    /// `exception Stop of error` (used internally)
    Stop(Error),
    /// Another exception, raised by the function of a spec (or the anonymous
    /// function): `Arg` lets it through.
    Raise(E),
}

/// `Arg.error` (internal)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Unknown(String),
    /// option, actual, expected
    Wrong(String, String, String),
    Missing(String),
    Message(String),
}

/// `assoc3`: the index of the first entry with key `x` (OCaml returns its
/// spec, or raises `Not_found`).
fn assoc3<E>(x: &str, l: &Speclist<'_, E>) -> Option<usize> {
    l.iter().position(|(y1, _, _)| y1 == x)
}

/// `split`: the parts before and after the first `=` (`None` where OCaml's
/// `String.index` raises `Not_found`).
fn split(s: &str) -> Option<(String, String)> {
    let i = s.find('=')?;
    Some((s[..i].to_string(), s[i + 1..].to_string()))
}

fn make_symlist(prefix: &str, sep: &str, suffix: &str, l: &[String]) -> String {
    match l {
        [] => "<none>".to_string(),
        [h, t @ ..] => {
            let mut acc = format!("{}{}", prefix, h);
            for y in t {
                acc.push_str(sep);
                acc.push_str(y);
            }
            acc.push_str(suffix);
            acc
        }
    }
}

fn print_spec<E>(buf: &mut String, key: &str, spec: Option<&Spec<'_, E>>, doc: &str) {
    if !doc.is_empty() {
        match spec {
            Some(Spec::Symbol(l, _)) => {
                let _ = writeln!(buf, "  {} {}{}", key, make_symlist("{", "|", "}", l), doc);
            }
            _ => {
                let _ = writeln!(buf, "  {} {}", key, doc);
            }
        }
    }
}

fn help_action<E>() -> Res<E> {
    Err(Exn::Stop(Error::Unknown("-help".to_string())))
}

const HELP_DOC: &str = " Display this list of options";

/// `add_help`: `-help` and `--help`, after the others, where the list does
/// not have them.
fn add_help<'a, E: 'a>(mut speclist: Speclist<'a, E>) -> Speclist<'a, E> {
    let add1 = assoc3("-help", &speclist).is_none();
    let add2 = assoc3("--help", &speclist).is_none();
    if add1 {
        speclist.push((
            "-help".to_string(),
            Spec::Unit(Box::new(help_action::<E>)),
            HELP_DOC.to_string(),
        ));
    }
    if add2 {
        speclist.push((
            "--help".to_string(),
            Spec::Unit(Box::new(help_action::<E>)),
            HELP_DOC.to_string(),
        ));
    }
    speclist
}

/// `usage_b`: prints the entries of `add_help speclist` (without building
/// the list: the entries `add_help` would add are printed after the others).
fn usage_b<E>(buf: &mut String, speclist: &Speclist<'_, E>, errmsg: &str) {
    let _ = writeln!(buf, "{}", errmsg);
    for (key, spec, doc) in speclist {
        print_spec(buf, key, Some(spec), doc);
    }
    if assoc3("-help", speclist).is_none() {
        print_spec::<E>(buf, "-help", None, HELP_DOC);
    }
    if assoc3("--help", speclist).is_none() {
        print_spec::<E>(buf, "--help", None, HELP_DOC);
    }
}

/// `Arg.usage_string speclist usage_msg`: the message that `usage` would
/// print.
pub fn usage_string<E>(speclist: &Speclist<'_, E>, errmsg: &str) -> String {
    let mut b = String::with_capacity(200);
    usage_b(&mut b, speclist, errmsg);
    b
}

/// `Arg.usage speclist usage_msg` prints to standard error an error message
/// that includes the list of valid options.
pub fn usage<E>(speclist: &Speclist<'_, E>, errmsg: &str) {
    eprint!("{}", usage_string(speclist, errmsg));
}

thread_local! {
    /// `Arg.current` (per thread: see the module documentation).
    static CURRENT: Cell<usize> = const { Cell::new(0) };
}

/// Runs `f` with `Arg.current`, the position in `argv` of the argument being
/// processed.
pub fn with_current<A>(f: impl FnOnce(&Cell<usize>) -> A) -> A {
    CURRENT.with(f)
}

/// `bool_of_string_opt`
pub fn bool_of_string_opt(x: &str) -> Option<bool> {
    match x {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// `float_of_string_opt`: `caml_float_of_string` (`runtime/floats.c`). The
/// `_` are removed first; then a hexadecimal literal (after an optional
/// sign) is read by OCaml's own reader, and anything else by `strtod`, which
/// must read all of it.
pub fn float_of_string_opt(x: &str) -> Option<f64> {
    // Remove '_' characters before conversion
    let buf: Vec<u8> = x.bytes().filter(|c| *c != b'_').collect();
    if buf.is_empty() {
        return None;
    }
    // Check for hexadecimal FP constant
    let (sign, src) = match buf.first() {
        Some(b'-') => (-1.0, &buf[1..]),
        Some(b'+') => (1.0, &buf[1..]),
        _ => (1.0, &buf[..]),
    };
    if src.len() >= 2 && src[0] == b'0' && (src[1] == b'x' || src[1] == b'X') {
        // Convert using our hexadecimal FP parser
        let d = float_of_hex(&src[2..])?;
        return Some(if sign < 0.0 { -d } else { d });
    }
    // Convert using strtod. A NUL stops `strtod` before the end, which is
    // then an error.
    if buf.contains(&0) {
        return None;
    }
    let c = std::ffi::CString::new(buf.clone()).ok()?;
    let mut end: *mut libc::c_char = std::ptr::null_mut();
    // SAFETY: `c` is a NUL-terminated string that outlives the call, and
    // `end` is set by `strtod` to a position inside it.
    let (d, consumed) = unsafe {
        let d = libc::strtod(c.as_ptr(), &mut end);
        (d, end.offset_from(c.as_ptr()) as usize)
    };
    if consumed != buf.len() {
        return None;
    }
    Some(d)
}

/// `caml_float_of_hex`: the digits of a hexadecimal float after its `0x`
/// (with an optional `.` and an optional `p` exponent; the `_` have been
/// removed by the caller, and another character is a bad digit).
fn float_of_hex(s: &[u8]) -> Option<f64> {
    let mut m: u64 = 0; // the mantissa - top 60 bits at most
    let mut n_bits: i32 = 0; // total number of bits read
    let mut m_bits: i32 = 0; // number of bits in mantissa
    let mut x_bits: i32 = 0; // number of bits after mantissa
    let mut dec_point: i32 = -1; // bit count corresponding to decimal point
    let mut exp: i32 = 0; // exponent
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        i += 1;
        match c {
            b'.' => {
                if dec_point >= 0 {
                    return None; // multiple decimal points
                }
                dec_point = n_bits;
            }
            b'p' | b'P' => {
                if i >= s.len() {
                    return None; // nothing after exponent mark
                }
                // `strtol`: optional blanks and sign, then decimal digits,
                // which must reach the end.
                let rest = &s[i..];
                let mut j = 0;
                while j < rest.len() && (rest[j] == b' ' || (b'\t'..=b'\r').contains(&rest[j])) {
                    j += 1;
                }
                let mut neg = false;
                if j < rest.len() && (rest[j] == b'-' || rest[j] == b'+') {
                    neg = rest[j] == b'-';
                    j += 1;
                }
                let digits_start = j;
                let mut e: i128 = 0;
                while j < rest.len() && rest[j].is_ascii_digit() {
                    e = (e * 10 + (rest[j] - b'0') as i128).min(i64::MAX as i128 + 1);
                    j += 1;
                }
                if j == digits_start || j != rest.len() {
                    return None; // ill-formed exponent
                }
                let e = if neg { -e } else { e };
                // Handle exponents larger than int by returning 0/infinity
                // directly.
                if e <= i32::MIN as i128 {
                    return Some(0.0);
                } else if e >= i32::MAX as i128 {
                    return Some(if m == 0 { 0.0 } else { f64::INFINITY });
                }
                // regular exponent value
                exp = e as i32;
                i = s.len(); // stop at next loop iteration
            }
            _ => {
                // Nonzero digit
                let d = match c {
                    b'0'..=b'9' => (c - b'0') as u64,
                    b'A'..=b'F' => (c - b'A') as u64 + 10,
                    b'a'..=b'f' => (c - b'a') as u64 + 10,
                    _ => return None,
                };
                n_bits += 4;
                if d == 0 && m == 0 {
                    continue; // leading zeros are skipped
                }
                if m_bits < 60 {
                    // There is still room in m. Add this digit to the
                    // mantissa.
                    m = (m << 4) + d;
                    m_bits += 4;
                } else {
                    // We've already collected 60 significant bits in m. Now
                    // all we care about is whether there is a nonzero bit
                    // after. In this case, round m to odd so that the later
                    // rounding of m to FP precision will be correct.
                    if d != 0 {
                        m |= 1; // round to odd
                    }
                    x_bits += 4;
                }
            }
        }
    }
    if n_bits == 0 {
        return None;
    }
    // Convert mantissa to FP.
    let mut f = m as i64 as f64;
    // Adjust exponent to take decimal point and extra digits into account
    let mut adj = x_bits;
    if dec_point >= 0 {
        adj += dec_point - n_bits;
    }
    // saturated addition exp + adj
    exp = exp.saturating_add(adj);
    // Apply exponent if needed
    if exp != 0 {
        f = ldexp(f, exp);
    }
    Some(f)
}

/// `ldexp`: `f * 2^exp`, rounded once.
fn ldexp(f: f64, exp: i32) -> f64 {
    unsafe extern "C" {
        fn ldexp(x: f64, exp: libc::c_int) -> f64;
    }
    // SAFETY: `ldexp` of the C library is a pure function.
    unsafe { ldexp(f, exp) }
}

/// `parse_and_expand_argv_dynamic_aux false current argv speclist anonfun
/// errmsg` (without `Expand`, see the module documentation).
fn parse_and_expand_argv_dynamic_aux<E>(
    current: &Cell<usize>,
    argv: &[String],
    speclist: &mut Speclist<'_, E>,
    anonfun: &mut AnonFun<'_, E>,
    errmsg: &str,
) -> Res<E> {
    let initpos = current.get();
    // convert an internal error to a Bad/Help exception
    // *or* add the program name as a prefix and the usage message as a suffix
    // to an user-raised Bad exception.
    let convert_error = |speclist: &Speclist<'_, E>, error: Error| -> Exn<E> {
        let mut b = String::with_capacity(200);
        let progname = if initpos < argv.len() {
            argv[initpos].as_str()
        } else {
            "(?)"
        };
        match &error {
            Error::Unknown(s) if s == "-help" => {}
            Error::Unknown(s) if s == "--help" => {}
            Error::Unknown(s) => {
                let _ = writeln!(b, "{}: unknown option '{}'.", progname, s);
            }
            Error::Missing(s) => {
                let _ = writeln!(b, "{}: option '{}' needs an argument.", progname, s);
            }
            Error::Wrong(opt, arg, expected) => {
                let _ = writeln!(
                    b,
                    "{}: wrong argument '{}'; option '{}' expects {}.",
                    progname, arg, opt, expected
                );
            }
            Error::Message(s) => {
                // user error message
                let _ = writeln!(b, "{}: {}.", progname, s);
            }
        }
        usage_b(&mut b, speclist, errmsg);
        if error == Error::Unknown("-help".to_string())
            || error == Error::Unknown("--help".to_string())
        {
            Exn::Help(b)
        } else {
            Exn::Bad(b)
        }
    };
    current.set(current.get() + 1);
    while current.get() < argv.len() {
        let res = (|| -> Res<E> {
            let s = &argv[current.get()];
            if s.starts_with('-') {
                let (index, follow) = match assoc3(s, speclist) {
                    Some(index) => (index, None),
                    None => match split(s) {
                        Some((keyword, arg)) => match assoc3(&keyword, speclist) {
                            Some(index) => (index, Some(arg)),
                            None => return Err(Exn::Stop(Error::Unknown(s.clone()))),
                        },
                        None => return Err(Exn::Stop(Error::Unknown(s.clone()))),
                    },
                };
                let action = &mut speclist[index].1;
                treat_action(current, argv, s, &follow, action)
            } else {
                anonfun(s.clone())
            }
        })();
        match res {
            Ok(()) => {}
            Err(Exn::Bad(m)) => return Err(convert_error(speclist, Error::Message(m))),
            Err(Exn::Stop(e)) => return Err(convert_error(speclist, e)),
            Err(help @ Exn::Help(_)) => return Err(help),
            Err(raise @ Exn::Raise(_)) => return Err(raise),
        }
        current.set(current.get() + 1);
    }
    Ok(())
}

/// `treat_action` of `parse_and_expand_argv_dynamic_aux`, for the option `s`
/// (with `follow`, the argument after its `=`, if any).
fn treat_action<E>(
    current: &Cell<usize>,
    argv: &[String],
    s: &str,
    follow: &Option<String>,
    action: &mut Spec<'_, E>,
) -> Res<E> {
    let no_arg = || -> Res<E> {
        match follow {
            None => Ok(()),
            Some(arg) => Err(Exn::Stop(Error::Wrong(
                s.to_string(),
                arg.clone(),
                "no argument".to_string(),
            ))),
        }
    };
    let get_arg = || -> Result<String, Exn<E>> {
        match follow {
            None => {
                if current.get() + 1 < argv.len() {
                    Ok(argv[current.get() + 1].clone())
                } else {
                    Err(Exn::Stop(Error::Missing(s.to_string())))
                }
            }
            Some(arg) => Ok(arg.clone()),
        }
    };
    let consume_arg = || match follow {
        None => current.set(current.get() + 1),
        Some(_) => {}
    };
    let wrong = |arg: String, expected: &str| {
        Exn::Stop(Error::Wrong(s.to_string(), arg, expected.to_string()))
    };
    match action {
        Spec::Unit(f) => {
            no_arg()?;
            f()
        }
        Spec::Bool(f) => {
            let arg = get_arg()?;
            match bool_of_string_opt(&arg) {
                None => return Err(wrong(arg, "a boolean")),
                Some(s) => f(s)?,
            }
            consume_arg();
            Ok(())
        }
        Spec::Set(r) => {
            no_arg()?;
            r.set(true);
            Ok(())
        }
        Spec::Clear(r) => {
            no_arg()?;
            r.set(false);
            Ok(())
        }
        Spec::String(f) => {
            let arg = get_arg()?;
            f(arg)?;
            consume_arg();
            Ok(())
        }
        Spec::Symbol(symb, f) => {
            let arg = get_arg()?;
            if symb.contains(&arg) {
                f(arg)?;
                consume_arg();
                Ok(())
            } else {
                let expected = format!("one of: {}", make_symlist("", " ", "", symb));
                Err(wrong(arg, &expected))
            }
        }
        Spec::SetString(r) => {
            *r.borrow_mut() = get_arg()?;
            consume_arg();
            Ok(())
        }
        Spec::Int(f) => {
            let arg = get_arg()?;
            match ocaml_stdlib::int_of_string_opt(&arg) {
                None => return Err(wrong(arg, "an integer")),
                Some(x) => f(x)?,
            }
            consume_arg();
            Ok(())
        }
        Spec::SetInt(r) => {
            let arg = get_arg()?;
            match ocaml_stdlib::int_of_string_opt(&arg) {
                None => return Err(wrong(arg, "an integer")),
                Some(x) => r.set(x),
            }
            consume_arg();
            Ok(())
        }
        Spec::Float(f) => {
            let arg = get_arg()?;
            match float_of_string_opt(&arg) {
                None => return Err(wrong(arg, "a float")),
                Some(x) => f(x)?,
            }
            consume_arg();
            Ok(())
        }
        Spec::SetFloat(r) => {
            let arg = get_arg()?;
            match float_of_string_opt(&arg) {
                None => return Err(wrong(arg, "a float")),
                Some(x) => r.set(x),
            }
            consume_arg();
            Ok(())
        }
        Spec::Tuple(specs) => {
            no_arg()?;
            for spec in specs.iter_mut() {
                treat_action(current, argv, s, follow, spec)?;
            }
            Ok(())
        }
        Spec::Rest(f) => {
            no_arg()?;
            while current.get() + 1 < argv.len() {
                f(argv[current.get() + 1].clone())?;
                consume_arg();
            }
            Ok(())
        }
        Spec::RestAll(f) => {
            no_arg()?;
            let mut acc = vec![];
            while current.get() + 1 < argv.len() {
                acc.push(argv[current.get() + 1].clone());
                consume_arg();
            }
            f(acc)
        }
    }
}

/// `Arg.parse_argv ~current args speclist anon_fun usage_msg` parses the
/// array `args` as if it were the command line. It uses and updates the
/// value of `current` (`None` for `Arg.current`). Where `Arg.parse_argv`
/// raises `Arg.Bad` or `Arg.Help` (with the message `Arg.parse` would print),
/// this returns them as `Err`, as it returns what a spec's function raised
/// (`Exn::Raise`).
pub fn parse_argv<E>(
    current: Option<&Cell<usize>>,
    argv: &[String],
    speclist: &mut Speclist<'_, E>,
    anonfun: &mut AnonFun<'_, E>,
    errmsg: &str,
) -> Res<E> {
    match current {
        Some(current) => parse_and_expand_argv_dynamic_aux(current, argv, speclist, anonfun, errmsg),
        None => with_current(|current| parse_and_expand_argv_dynamic_aux(current, argv, speclist, anonfun, errmsg)),
    }
}

/// `Arg.parse speclist anon_fun usage_msg` parses the command line
/// (`argv`, which is `Sys.argv`): on `Bad` it prints the message to standard
/// error and exits with 2, on `Help` it prints it to standard output and
/// exits with 0. What a spec's function raised is returned.
pub fn parse<E>(
    argv: &[String],
    speclist: &mut Speclist<'_, E>,
    anonfun: &mut AnonFun<'_, E>,
    errmsg: &str,
) -> Result<(), E> {
    match parse_argv(None, argv, speclist, anonfun, errmsg) {
        Ok(()) => Ok(()),
        Err(Exn::Bad(msg)) => {
            eprint!("{}", msg);
            stdlib_exit(2)
        }
        Err(Exn::Help(msg)) => {
            print!("{}", msg);
            stdlib_exit(0)
        }
        Err(Exn::Stop(_)) => unreachable!("parse_argv converts Stop"),
        Err(Exn::Raise(e)) => Err(e),
    }
}

/// `Stdlib.exit code`: flush the standard channels, then exit.
pub fn stdlib_exit(code: i32) -> ! {
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    std::process::exit(code)
}

fn second_word(s: &str) -> usize {
    let s = s.as_bytes();
    let len = s.len();
    let rec_loop = |mut n: usize| {
        while n < len && s[n] == b' ' {
            n += 1;
        }
        n.min(len)
    };
    match s.iter().position(|c| *c == b'\t') {
        Some(n) => rec_loop(n + 1),
        None => match s.iter().position(|c| *c == b' ') {
            Some(n) => rec_loop(n + 1),
            None => len,
        },
    }
}

fn max_arg_len<E>(cur: usize, (kwd, spec, doc): &(Key, Spec<'_, E>, Doc)) -> usize {
    match spec {
        Spec::Symbol(..) => cur.max(kwd.len()),
        _ => cur.max(kwd.len() + second_word(doc)),
    }
}

fn replace_leading_tab(s: &str) -> String {
    let mut seen = false;
    s.chars()
        .map(|c| {
            if c == '\t' && !seen {
                seen = true;
                ' '
            } else {
                c
            }
        })
        .collect()
}

fn add_padding<'a, E>(len: usize, ksd: (Key, Spec<'a, E>, Doc)) -> (Key, Spec<'a, E>, Doc) {
    match ksd {
        (kwd, spec, msg) if msg.is_empty() => {
            // Do not pad undocumented options, so that they still don't show
            // up when run through [usage] or [parse].
            (kwd, spec, msg)
        }
        (kwd, spec @ Spec::Symbol(..), msg) => {
            let cutcol = second_word(&msg);
            let spaces = " ".repeat((len as isize - cutcol as isize).max(0) as usize + 3);
            let msg = format!("\n{}{}", spaces, replace_leading_tab(&msg));
            (kwd, spec, msg)
        }
        (kwd, spec, msg) => {
            let cutcol = second_word(&msg);
            let kwd_len = kwd.len();
            let diff = len as isize - kwd_len as isize - cutcol as isize;
            if diff <= 0 {
                let msg = replace_leading_tab(&msg);
                (kwd, spec, msg)
            } else {
                let spaces = " ".repeat(diff as usize);
                let replaced = replace_leading_tab(&msg);
                let prefix = &replaced[..cutcol];
                let suffix = &msg[cutcol..];
                let msg = format!("{}{}{}", prefix, spaces, suffix);
                (kwd, spec, msg)
            }
        }
    }
}

/// `Arg.align ?limit speclist`: aligns the documentation strings by
/// inserting spaces at the first alignment separator (tab or, if tab is not
/// found, space), according to the length of the keyword. Use an alignment
/// separator as the first character in a doc string if you want to align the
/// whole string. The doc strings corresponding to `Symbol` arguments are
/// aligned on the next line. `limit` (default: no limit) caps the alignment
/// column. It adds `-help` and `--help` where `speclist` lacks them.
pub fn align<'a, E: 'a>(speclist: Speclist<'a, E>, limit: Option<usize>) -> Speclist<'a, E> {
    let limit = limit.unwrap_or(usize::MAX);
    let completed = add_help(speclist);
    let len = completed.iter().fold(0, max_arg_len);
    let len = len.min(limit);
    completed
        .into_iter()
        .map(|ksd| add_padding(len, ksd))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn argv(args: &[&str]) -> Vec<String> {
        args.iter().map(|s| s.to_string()).collect()
    }

    fn parse_with(
        args: &[&str],
        speclist: &mut Speclist<'_>,
        anon: &RefCell<Vec<String>>,
    ) -> Res {
        let current = Cell::new(0);
        let mut anonfun = |s: String| -> Res {
            anon.borrow_mut().push(s);
            Ok(())
        };
        parse_argv(Some(&current), &argv(args), speclist, &mut anonfun, "Usage: prog")
    }

    #[test]
    fn align_pads_at_the_first_word() {
        let flag = Cell::new(false);
        let speclist: Speclist<'_> = vec![
            ("--a".to_string(), Spec::Set(&flag), " doc a".to_string()),
            (
                "--longer".to_string(),
                Spec::String(Box::new(|_| Ok(()))),
                "<path> doc b".to_string(),
            ),
            ("--hidden".to_string(), Spec::Set(&flag), "".to_string()),
            (
                "--sym".to_string(),
                Spec::Symbol(vec!["x".to_string(), "y".to_string()], Box::new(|_| Ok(()))),
                " pick one".to_string(),
            ),
        ];
        let aligned = align(speclist, None);
        // Every doc starts at column 18 (`--longer <path> ` is the longest).
        let sp = |n: usize| " ".repeat(n);
        assert_eq!(
            usage_string(&aligned, "Usage: prog"),
            format!(
                "Usage: prog\n  --a{}doc a\n  --longer <path> doc b\n  --sym {{x|y}}\n{}pick one\n  -help{}Display this list of options\n  --help{}Display this list of options\n",
                sp(13),
                sp(18),
                sp(11),
                sp(10)
            )
        );
    }

    #[test]
    fn unaligned_usage_adds_help() {
        let flag = Cell::new(false);
        let speclist: Speclist<'_> =
            vec![("-v".to_string(), Spec::Set(&flag), "\tverbose".to_string())];
        assert_eq!(
            usage_string(&speclist, "u"),
            "u\n  -v \tverbose\n  -help  Display this list of options\n  --help  Display this list of options\n"
        );
    }

    #[test]
    fn errors_have_arg_messages() {
        let n = Cell::new(0);
        let anon = RefCell::new(vec![]);
        let mk = || -> Speclist<'_> {
            vec![
                ("--n".to_string(), Spec::SetInt(&n), " int".to_string()),
                (
                    "--bad".to_string(),
                    Spec::Unit(Box::new(|| Err(Exn::Bad("custom".to_string())))),
                    " bad".to_string(),
                ),
                (
                    "--sym".to_string(),
                    Spec::Symbol(vec!["a".to_string(), "b".to_string()], Box::new(|_| Ok(()))),
                    " sym".to_string(),
                ),
            ]
        };
        let usage_tail = "Usage: prog\n  --n  int\n  --bad  bad\n  --sym {a|b} sym\n  -help  Display this list of options\n  --help  Display this list of options\n";
        let first_line = |r: Res| match r {
            Err(Exn::Bad(m)) => {
                assert!(m.ends_with(usage_tail), "{}", m);
                m.lines().next().unwrap().to_string()
            }
            r => panic!("{:?}", r),
        };
        assert_eq!(
            first_line(parse_with(&["prog", "--nope"], &mut mk(), &anon)),
            "prog: unknown option '--nope'."
        );
        assert_eq!(
            first_line(parse_with(&["prog", "--n"], &mut mk(), &anon)),
            "prog: option '--n' needs an argument."
        );
        assert_eq!(
            first_line(parse_with(&["prog", "--n", "x1"], &mut mk(), &anon)),
            "prog: wrong argument 'x1'; option '--n' expects an integer."
        );
        assert_eq!(
            first_line(parse_with(&["prog", "--bad=1"], &mut mk(), &anon)),
            "prog: wrong argument '1'; option '--bad=1' expects no argument."
        );
        assert_eq!(
            first_line(parse_with(&["prog", "--bad"], &mut mk(), &anon)),
            "prog: custom."
        );
        assert_eq!(
            first_line(parse_with(&["prog", "--sym", "c"], &mut mk(), &anon)),
            "prog: wrong argument 'c'; option '--sym' expects one of: a b."
        );
        // `--help` is not in the list: Unknown "--help" is Help.
        match parse_with(&["prog", "--help"], &mut mk(), &anon) {
            Err(Exn::Help(m)) => assert_eq!(m, usage_tail),
            r => panic!("{:?}", r),
        }
        assert!(parse_with(&["prog", "--n=0x1F", "anon"], &mut mk(), &anon).is_ok());
        assert_eq!(n.get(), 31);
        assert_eq!(*anon.borrow(), vec!["anon".to_string()]);
    }

    #[test]
    fn help_action_of_align() {
        let anon = RefCell::new(vec![]);
        let mut speclist = align(vec![], None);
        match parse_with(&["prog", "--help"], &mut speclist, &anon) {
            Err(Exn::Help(m)) => assert_eq!(
                m,
                "Usage: prog\n  -help   Display this list of options\n  --help  Display this list of options\n"
            ),
            r => panic!("{:?}", r),
        }
    }

    #[test]
    fn tuple_rest_and_current() {
        let a = RefCell::new(String::new());
        let rest = RefCell::new(vec![]);
        let anon = RefCell::new(vec![]);
        let mut speclist: Speclist<'_> = vec![
            (
                "--t".to_string(),
                Spec::Tuple(vec![
                    Spec::SetString(&a),
                    Spec::Int(Box::new(|i| {
                        rest.borrow_mut().push(i.to_string());
                        Ok(())
                    })),
                ]),
                " t".to_string(),
            ),
            (
                "--rest".to_string(),
                Spec::Rest(Box::new(|s| {
                    rest.borrow_mut().push(s);
                    Ok(())
                })),
                " r".to_string(),
            ),
        ];
        let current = Cell::new(0);
        let mut anonfun = |s: String| -> Res {
            anon.borrow_mut().push(s);
            Ok(())
        };
        let args = argv(&["p", "x", "--t", "s", "7", "y", "--rest", "--t", "z"]);
        parse_argv(Some(&current), &args, &mut speclist, &mut anonfun, "u").unwrap();
        assert_eq!(*a.borrow(), "s");
        assert_eq!(*rest.borrow(), vec!["7", "--t", "z"]);
        assert_eq!(*anon.borrow(), vec!["x", "y"]);
        assert_eq!(current.get(), args.len());
    }

    #[test]
    fn floats_as_in_ocaml() {
        assert_eq!(float_of_string_opt("5"), Some(5.0));
        assert_eq!(float_of_string_opt("1_0.5"), Some(10.5));
        assert_eq!(float_of_string_opt("1e3"), Some(1000.0));
        assert_eq!(float_of_string_opt(" 2"), Some(2.0));
        assert_eq!(float_of_string_opt("2 "), None);
        assert_eq!(float_of_string_opt(""), None);
        assert_eq!(float_of_string_opt("_"), None);
        assert_eq!(float_of_string_opt("abc"), None);
        assert_eq!(float_of_string_opt("inf"), Some(f64::INFINITY));
        assert!(float_of_string_opt("nan").unwrap().is_nan());
        assert_eq!(float_of_string_opt("0x1p3"), Some(8.0));
        assert_eq!(float_of_string_opt("-0x1.8"), Some(-1.5));
        assert_eq!(float_of_string_opt("0x"), None);
        assert_eq!(float_of_string_opt("0x1p"), None);
        assert_eq!(float_of_string_opt("0x1.2.3"), None);
        // The `_` are removed before anything else, the hexadecimal reader
        // included (OCaml 5's `caml_float_of_string`).
        assert_eq!(float_of_string_opt("0x1p3_"), Some(8.0));
        assert_eq!(float_of_string_opt("0x1p_3"), Some(8.0));
        assert_eq!(float_of_string_opt("-_0x1p3"), Some(-8.0));
        assert_eq!(float_of_string_opt("0x_"), None);
    }

    #[test]
    fn bools_as_in_ocaml() {
        assert_eq!(bool_of_string_opt("true"), Some(true));
        assert_eq!(bool_of_string_opt("false"), Some(false));
        assert_eq!(bool_of_string_opt("True"), None);
        assert_eq!(bool_of_string_opt("1"), None);
    }
}
