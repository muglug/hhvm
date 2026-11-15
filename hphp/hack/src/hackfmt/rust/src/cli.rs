// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The hackfmt command line (hackfmt.ml), with the OCaml library behaviour
//! it relies on: `Arg` option parsing, `Wwwroot` root guessing, `.hhconfig`
//! reading (`Config_file`), `Parse_diff`, `Find_utils.is_hack`, and OCaml's
//! buffered standard channels.

use std::ffi::OsStr;
use std::io::Read;
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::path::Path;

use bumpalo::Bump;

use crate::boundaries::expand_to_line_boundaries;
use crate::boundaries::get_line_boundaries;
use crate::boundaries::line_interval_to_offset_range;
use crate::config_file::ConfigFile;
use crate::debug::DebugConfig;
use crate::error;
use crate::error::Exn;
use crate::error::raise;
use crate::format_env::Env as FEnv;
use crate::hack_format;
use crate::interval::Interval;
use crate::libhackfmt;
use crate::syntax;
use crate::syntax::SyntaxTree;

// ---------------------------------------------------------------------------
// OCaml's buffered stdout and stderr

const IO_BUFFER_SIZE: usize = 65536;

#[derive(Default)]
pub struct Io {
    out: Vec<u8>,
    err: Vec<u8>,
    /// Captured output (for tests): when set, nothing is written to the
    /// process's standard channels.
    capture: Option<(Vec<u8>, Vec<u8>)>,
}

impl Io {
    pub fn new() -> Self {
        Io::default()
    }

    pub fn capturing() -> Self {
        Io {
            capture: Some((vec![], vec![])),
            ..Io::default()
        }
    }

    fn write_out(&mut self, b: &[u8]) {
        let mut b = b;
        while !b.is_empty() {
            let free = IO_BUFFER_SIZE - self.out.len();
            let n = std::cmp::min(free, b.len());
            self.out.extend_from_slice(&b[..n]);
            b = &b[n..];
            if self.out.len() == IO_BUFFER_SIZE {
                self.flush_out();
            }
        }
    }

    fn write_err(&mut self, b: &[u8]) {
        let mut b = b;
        while !b.is_empty() {
            let free = IO_BUFFER_SIZE - self.err.len();
            let n = std::cmp::min(free, b.len());
            self.err.extend_from_slice(&b[..n]);
            b = &b[n..];
            if self.err.len() == IO_BUFFER_SIZE {
                self.flush_err();
            }
        }
    }

    pub fn print(&mut self, b: impl AsRef<[u8]>) {
        self.write_out(b.as_ref());
    }

    pub fn eprint(&mut self, b: impl AsRef<[u8]>) {
        self.write_err(b.as_ref());
    }

    pub fn flush_out(&mut self) {
        let buf = std::mem::take(&mut self.out);
        match &mut self.capture {
            Some((out, _)) => out.extend_from_slice(&buf),
            None => {
                let mut stdout = std::io::stdout().lock();
                let _ = stdout.write_all(&buf);
                let _ = stdout.flush();
            }
        }
    }

    pub fn flush_err(&mut self) {
        let buf = std::mem::take(&mut self.err);
        match &mut self.capture {
            Some((_, err)) => err.extend_from_slice(&buf),
            None => {
                let mut stderr = std::io::stderr().lock();
                let _ = stderr.write_all(&buf);
                let _ = stderr.flush();
            }
        }
    }

    /// What `exit` does: flush stdout, then stderr.
    pub fn flush_all(&mut self) {
        self.flush_out();
        self.flush_err();
    }

    /// The captured (stdout, stderr), after flushing.
    pub fn captured(mut self) -> (Vec<u8>, Vec<u8>) {
        self.flush_all();
        self.capture.take().unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// OCaml library functions

fn lossy(b: &[u8]) -> std::borrow::Cow<'_, str> {
    String::from_utf8_lossy(b)
}

fn os(b: &[u8]) -> &Path {
    Path::new(OsStr::from_bytes(b))
}

/// `Sys_utils.realpath`
fn realpath(path: &[u8]) -> Option<Vec<u8>> {
    if path.is_empty() {
        return None;
    }
    std::fs::canonicalize(os(path))
        .ok()
        .map(|p| p.into_os_string().into_vec())
}

trait IntoVec {
    fn into_vec(self) -> Vec<u8>;
}

impl IntoVec for std::ffi::OsString {
    fn into_vec(self) -> Vec<u8> {
        use std::os::unix::ffi::OsStringExt;
        OsStringExt::into_vec(self)
    }
}

/// `file_exists` in hackfmt.ml: realpath succeeds.
fn file_exists(path: &[u8]) -> bool {
    realpath(path).is_some()
}

/// `Path.make`: realpath, or the path itself.
fn path_make(path: &[u8]) -> Vec<u8> {
    realpath(path).unwrap_or_else(|| path.to_vec())
}

/// `Sys.file_exists`
fn sys_file_exists(path: &[u8]) -> bool {
    !path.is_empty() && os(path).exists()
}

/// `Filename.concat`
fn filename_concat(dir: &[u8], file: &[u8]) -> Vec<u8> {
    let mut out = dir.to_vec();
    if !(dir.is_empty() || dir.ends_with(b"/")) {
        out.push(b'/');
    }
    out.extend_from_slice(file);
    out
}

/// `Path.concat`
fn path_concat(dir: &[u8], file: &[u8]) -> Vec<u8> {
    path_make(&filename_concat(dir, file))
}

/// `Filename.dirname` (Unix)
fn filename_dirname(name: &[u8]) -> Vec<u8> {
    if name.is_empty() {
        return b".".to_vec();
    }
    let is_sep = |i: usize| name[i] == b'/';
    // trailing_sep
    let mut n = name.len() as isize - 1;
    while n >= 0 && is_sep(n as usize) {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_vec();
    }
    // base
    while n >= 0 && !is_sep(n as usize) {
        n -= 1;
    }
    if n < 0 {
        return b".".to_vec();
    }
    // intermediate_sep
    while n >= 0 && is_sep(n as usize) {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_vec();
    }
    name[..(n + 1) as usize].to_vec()
}

/// `Filename.basename` (Unix)
fn filename_basename(name: &[u8]) -> Vec<u8> {
    if name.is_empty() {
        return b".".to_vec();
    }
    let is_sep = |i: usize| name[i] == b'/';
    let mut n = name.len() as isize - 1;
    while n >= 0 && is_sep(n as usize) {
        n -= 1;
    }
    if n < 0 {
        return name[..1].to_vec();
    }
    let p = (n + 1) as usize;
    while n >= 0 && !is_sep(n as usize) {
        n -= 1;
    }
    name[(n + 1) as usize..p].to_vec()
}

const HACK_EXTENSIONS: [&[u8]; 8] = [
    b".php",
    b".phpt",
    b".hack",
    b".hackpartial",
    b".hck",
    b".hh",
    b".hhi",
    b".xhp",
];

/// `Find_utils.is_hack`
pub fn is_hack(path: &[u8]) -> bool {
    let base = filename_basename(path);
    let is_dot_file = !base.is_empty() && base[0] == b'.';
    !is_dot_file && HACK_EXTENSIONS.iter().any(|e| path.ends_with(e))
}

/// `String.trim`
fn ocaml_trim(s: &[u8]) -> &[u8] {
    let is_space = |c: &u8| matches!(c, b' ' | b'\x0c' | b'\n' | b'\r' | b'\t');
    let start = s.iter().position(|c| !is_space(c)).unwrap_or(s.len());
    let end = s.iter().rposition(|c| !is_space(c)).map_or(start, |i| i + 1);
    &s[start..end]
}

/// `%S`: an OCaml string literal.
fn ocaml_quote(s: &[u8]) -> String {
    let mut out = String::from("\"");
    for &c in s {
        match c {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            8 => out.push_str("\\b"),
            32..=126 => out.push(c as char),
            _ => out.push_str(&format!("\\{:03}", c)),
        }
    }
    out.push('"');
    out
}

/// `int_of_string_opt` (63-bit OCaml ints).
pub fn ocaml_int_of_string(s: &[u8]) -> Option<isize> {
    let mut i = 0;
    let mut sign: i128 = 1;
    if s.get(i) == Some(&b'-') {
        sign = -1;
        i += 1;
    } else if s.get(i) == Some(&b'+') {
        i += 1;
    }
    let mut base: u128 = 10;
    let mut signedness = true;
    if s.get(i) == Some(&b'0') {
        match s.get(i + 1) {
            Some(b'x') | Some(b'X') => {
                base = 16;
                signedness = false;
                i += 2;
            }
            Some(b'o') | Some(b'O') => {
                base = 8;
                signedness = false;
                i += 2;
            }
            Some(b'b') | Some(b'B') => {
                base = 2;
                signedness = false;
                i += 2;
            }
            Some(b'u') | Some(b'U') => {
                signedness = false;
                i += 2;
            }
            _ => {}
        }
    }
    let digit = |c: u8| -> Option<u128> {
        let d = match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => return None,
        };
        Some(d as u128)
    };
    let first = digit(*s.get(i)?)?;
    if first >= base {
        return None;
    }
    let max: u128 = u64::MAX as u128;
    let mut res = first;
    i += 1;
    while i < s.len() {
        let c = s[i];
        i += 1;
        if c == b'_' {
            continue;
        }
        let d = digit(c).filter(|d| *d < base)?;
        res = res * base + d;
        if res > max {
            return None;
        }
    }
    let nbits = 63;
    if signedness {
        if sign >= 0 {
            if res >= 1u128 << (nbits - 1) {
                return None;
            }
        } else if res > 1u128 << (nbits - 1) {
            return None;
        }
    } else if res >= 1u128 << nbits {
        return None;
    }
    let v = (sign * res as i128) as i64;
    // Wrap to a 63-bit OCaml int.
    Some(((v << 1) >> 1) as isize)
}

// ---------------------------------------------------------------------------
// Exceptions that escape OCaml's main (printed by the runtime)

enum Fatal {
    /// Exit with this code (output already written).
    Exit(i32),
}

/// An uncaught exception: the runtime flushes the standard channels, prints
/// it, and exits with code 2.
fn uncaught(io: &mut Io, printed: &str) -> Fatal {
    io.flush_all();
    io.eprint(format!("Fatal error: exception {}\n", printed));
    io.flush_err();
    Fatal::Exit(2)
}

fn printexc_of_exn(e: &Exn) -> String {
    match e {
        Exn::InvalidSyntax => "Hackfmt_error.InvalidSyntax".into(),
        Exn::InvalidCliArg(s) => format!("Hackfmt_error.InvalidCliArg({})", ocaml_quote(s.as_bytes())),
        Exn::InvalidDiff(s) => format!("Hackfmt_error.InvalidDiff({})", ocaml_quote(s.as_bytes())),
        Exn::InvalidArgument(s) => format!("Invalid_argument({})", ocaml_quote(s.as_bytes())),
        Exn::Failure(s) => format!("Failure({})", ocaml_quote(s.as_bytes())),
        Exn::SysError(s) => format!("Sys_error({})", ocaml_quote(s.as_bytes())),
        Exn::Other(s) => s.clone(),
    }
}

/// `Sys_error` message for an I/O error on `path`.
fn sys_error(path: &[u8], e: &std::io::Error) -> Exn {
    let msg = e.to_string();
    let msg = match msg.find(" (os error ") {
        Some(i) => msg[..i].to_string(),
        None => msg,
    };
    Exn::SysError(format!("{}: {}", lossy(path), msg))
}

/// `Sys_utils.cat` (raises `Sys_error`).
fn cat(path: &[u8]) -> Vec<u8> {
    let mut f = match std::fs::File::open(os(path)) {
        Ok(f) => f,
        Err(e) => raise(sys_error(path, &e)),
    };
    let mut buf = vec![];
    if let Err(e) = f.read_to_end(&mut buf) {
        raise(Exn::SysError(
            e.to_string()
                .split(" (os error ")
                .next()
                .unwrap_or_default()
                .to_string(),
        ));
    }
    buf
}

// ---------------------------------------------------------------------------
// Root guessing (Wwwroot, repo_root.rs)

fn is_www_directory(path: &[u8]) -> bool {
    sys_file_exists(&path_concat(path, b".hhconfig"))
}

fn guess_root_ocaml(start: &[u8]) -> Option<Vec<u8>> {
    let mut start = start.to_vec();
    let mut recursion_limit = 50;
    loop {
        if !sys_file_exists(&start) {
            return None;
        }
        let dirname = filename_dirname(&start);
        if start == dirname {
            // Reached file system root
            return None;
        }
        if is_www_directory(&start) {
            return Some(start);
        }
        if recursion_limit <= 0 {
            return None;
        }
        start = dirname;
        recursion_limit -= 1;
    }
}

/// `repo_root::guess_root_from`, used through `Repo_root_ffi`.
fn guess_root_rust(start: &Path) -> Option<std::path::PathBuf> {
    let is_root = |p: &Path| p.join(".hhconfig").exists();
    let mut possible_root = start;
    let mut found = None;
    for _ in 0..=50 {
        if is_root(possible_root) {
            found = Some(possible_root.to_owned());
            break;
        }
        match possible_root.parent() {
            Some(p) => possible_root = p,
            None => break,
        }
    }
    if found.is_some() {
        return found;
    }
    let www_child = start.join("www");
    if is_root(&www_child) { Some(www_child) } else { None }
}

/// `Wwwroot.guess_root`
fn guess_root(start: &[u8]) -> Option<Vec<u8>> {
    let use_rust = std::env::var_os("HH_USE_RUST_REPO_ROOT").is_none_or(|v| v != "0");
    if !(sys_file_exists(start) && use_rust) {
        guess_root_ocaml(start)
    } else {
        match guess_root_rust(os(start)) {
            Some(root) => Some(path_make(root.as_os_str().as_bytes())),
            None => guess_root_ocaml(start),
        }
    }
}

fn get_www_root_for_diff(io: &mut Io) -> Result<Vec<u8>, Fatal> {
    io.eprint("No root specified, trying to guess one\n");
    let start_path = path_make(b".");
    let root = guess_root(&start_path).unwrap_or(start_path);
    // Wwwroot.assert_www_directory
    let message = if !(sys_file_exists(&root) && os(&root).is_dir()) {
        Some(format!("{} is not a directory", lossy(&root)))
    } else if !is_www_directory(&root) {
        Some(format!(
            "could not find a .hhconfig file in {} or any of its parent directories. Do you have a .hhconfig in your code's root directory?",
            lossy(&root)
        ))
    } else {
        None
    };
    if let Some(message) = message {
        io.eprint(format!("Error: {}\n", message));
        io.flush_err();
        io.flush_all();
        return Err(Fatal::Exit(1));
    }
    io.eprint(b"Guessed root: ");
    io.eprint(&root);
    io.eprint(b"\n");
    io.flush_err();
    Ok(root)
}

fn get_www_root_for_format(files: &[Vec<u8>]) -> Vec<u8> {
    let cur = path_make(b".");
    let start_path = match files.first() {
        None => cur.clone(),
        // just use the first file here. specifying more than one will result
        // in an error during validation
        Some(hd) => filename_dirname(&path_make(hd)),
    };
    guess_root(&start_path).unwrap_or(cur)
}

/// `Hg.hg_root`, through `Future.get`.
fn hg_root(io: &mut Io) -> Result<Result<Vec<u8>, String>, Fatal> {
    let child = std::process::Command::new("hg")
        .arg("root")
        .env("HGPLAIN", "1")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output();
    match child {
        Err(e) => {
            let code = match e.kind() {
                std::io::ErrorKind::NotFound => "ENOENT",
                std::io::ErrorKind::PermissionDenied => "EACCES",
                _ => "EUNKNOWNERR",
            };
            Err(uncaught(
                io,
                &format!("Unix.Unix_error(Unix.{}, \"create_process\", \"hg\")", code),
            ))
        }
        Ok(output) => {
            use std::os::unix::process::ExitStatusExt;
            if output.status.success() {
                Ok(Ok(ocaml_trim(&output.stdout).to_vec()))
            } else {
                let info = "(hg [root])";
                let status = match (output.status.code(), output.status.signal()) {
                    (Some(c), _) => format!("({} WEXITED {})", info, c),
                    (None, Some(s)) => format!("({} WSIGNALED {})", info, s),
                    _ => format!("({} WEXITED 255)", info),
                };
                Ok(Err(format!(
                    "Process_failure({}, stderr: {})",
                    status,
                    lossy(&output.stderr)
                )))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// .hhconfig

/// `Config_file.Getters.bool_opt` (raises `Invalid_argument`).
fn bool_opt(config: &ConfigFile, key: &str) -> Result<Option<bool>, Exn> {
    match config.get_bool(key) {
        None => Ok(None),
        Some(Ok(b)) => Ok(Some(b)),
        Some(Err(e)) => Err(Exn::InvalidArgument(e.to_string())),
    }
}

/// `Config_file.Getters.int_opt` (raises `Invalid_argument`).
fn int_opt(config: &ConfigFile, key: &str) -> Result<Option<isize>, Exn> {
    match config.get_int(key) {
        None => Ok(None),
        Some(Ok(n)) => Ok(Some(((n as i64) << 1 >> 1) as isize)),
        Some(Err(e)) => Err(Exn::InvalidArgument(e.to_string())),
    }
}

/// `read_hhconfig` in hackfmt.ml: the formatting options and
/// `enable_xhp_class_modifier`.
fn read_hhconfig(io: &mut Io, path: &[u8]) -> Result<(FEnv, bool), Fatal> {
    let contents = match std::fs::read(os(path)) {
        Ok(c) => c,
        Err(e) => {
            // Config_file.cat_hhconfig_file
            let exn = sys_error(path, &e);
            io.eprint(format!(".hhconfig deleted: {}\n", printexc_of_exn(&exn)));
            io.flush_all();
            return Err(Fatal::Exit(104));
        }
    };
    let config = ConfigFile::from_slice(&contents);
    let default = FEnv::default();
    // The tuple and the record are evaluated right to left.
    let read = || -> Result<(FEnv, bool), Exn> {
        let enable_xhp_class_modifier = bool_opt(&config, "enable_xhp_class_modifier")?.unwrap_or(false);
        let version = int_opt(&config, "hackfmt.version")?;
        let format_generated_code =
            bool_opt(&config, "hackfmt.format_generated_code")?.unwrap_or(default.format_generated_code);
        let line_width = int_opt(&config, "hackfmt.line_width")?.unwrap_or(default.line_width);
        let indent_with_tabs = bool_opt(&config, "hackfmt.tabs")?.unwrap_or(default.indent_with_tabs);
        let indent_width = int_opt(&config, "hackfmt.indent_width")?.unwrap_or(default.indent_width);
        let add_trailing_commas =
            bool_opt(&config, "hackfmt.add_trailing_commas")?.unwrap_or(default.add_trailing_commas);
        Ok((
            FEnv {
                add_trailing_commas,
                indent_width,
                indent_with_tabs,
                line_width,
                format_generated_code,
                version,
                hakana_rules: default.hakana_rules,
            },
            enable_xhp_class_modifier,
        ))
    };
    read().map_err(|e| uncaught(io, &printexc_of_exn(&e)))
}

// ---------------------------------------------------------------------------
// Options

#[derive(Clone, Copy, Debug)]
enum Range {
    /// 0-based byte offsets; half-open
    Byte(Interval),
    /// 1-based line numbers; inclusive
    Line(Interval),
}

#[derive(Clone, Debug)]
enum TextSource {
    File(Vec<u8>),
    /// Optional filename for logging.
    Stdin(Option<Vec<u8>>),
}

struct Env {
    debug: bool,
    debug_config: DebugConfig,
    diff_root: Vec<u8>,
    jobs: usize,
}

struct NormalOptions {
    /// In reverse command-line order, as hackfmt.ml accumulates them.
    files: Vec<Vec<u8>>,
    filename_for_logging: Option<Vec<u8>>,
    range: Option<Range>,
    at_char: Option<isize>,
    inplace: bool,
    diff: bool,
    diff_dry: bool,
    diff_root: Vec<u8>,
    check: bool,
    config: FEnv,
    www_root: Vec<u8>,
    enable_xhp_class_modifier: bool,
    debug: bool,
    debug_config: DebugConfig,
    jobs: usize,
    recursive: bool,
}

enum RawOptions {
    Normal(Box<NormalOptions>),
    Linttool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Opt {
    Linttool,
    LinttoolSeverity,
    Range,
    LineRange,
    AtChar,
    InPlace,
    IndentWidth,
    LineWidth,
    Tabs,
    FormatGeneratedCode,
    Version,
    Root,
    Diff,
    DiffRoot,
    DiffDryRun,
    CheckFormatting,
    Debug,
    FilenameForLogging,
    Test,
    HackfmtCompat,
    Jobs,
    Recursive,
    DebugDoc,
    DebugIds,
    DebugNesting,
    DebugRuleDeps,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgKind {
    Unit,
    String,
    Int,
    IntPair,
}

struct Spec {
    key: &'static str,
    kind: ArgKind,
    opt: Opt,
    doc: String,
}

fn spec(key: &'static str, kind: ArgKind, opt: Opt, doc: impl Into<String>) -> Spec {
    Spec {
        key,
        kind,
        opt,
        doc: doc.into(),
    }
}

fn main_specs() -> Vec<Spec> {
    use ArgKind::*;
    let d = FEnv::default();
    vec![
        spec(
            "--linttool",
            Unit,
            Opt::Linttool,
            "For use by an external tool that runs linters (https://fburl.com/wiki/g5m0d3zt)",
        ),
        spec(
            "--linttool-severity",
            String,
            Opt::LinttoolSeverity,
            "For use with --linttool. Makes us emit 'lints' with the given severity (we just give back the same severity that was passed in)",
        ),
        spec(
            "--range",
            IntPair,
            Opt::Range,
            "[start end]  Range of character positions to be formatted (1 indexed)",
        ),
        spec(
            "--line-range",
            IntPair,
            Opt::LineRange,
            "[start end]  Range of lines to be formatted (1 indexed, inclusive)",
        ),
        spec(
            "--at-char",
            Int,
            Opt::AtChar,
            "[idx]  Format a node ending at the given character (0 indexed)",
        ),
        spec("-i", Unit, Opt::InPlace, " Format file in-place"),
        spec("--in-place", Unit, Opt::InPlace, " Format file in-place"),
        spec(
            "--indent-width",
            Int,
            Opt::IndentWidth,
            format!(
                " Specify the number of spaces per indentation level. Defaults to {}",
                d.indent_width
            ),
        ),
        spec(
            "--line-width",
            Int,
            Opt::LineWidth,
            format!(" Specify the maximum length for each line. Defaults to {}", d.line_width),
        ),
        spec("--tabs", Unit, Opt::Tabs, " Indent with tabs rather than spaces"),
        spec(
            "--format-generated-code",
            Unit,
            Opt::FormatGeneratedCode,
            " Enable formatting of generated files and generated sections in partially-generated files. By default, generated code will be left untouched.",
        ),
        spec(
            "--version",
            Int,
            Opt::Version,
            " For version-gated formatter features, specify the version to use. Defaults to latest.",
        ),
        spec(
            "--root",
            String,
            Opt::Root,
            "[dir]  Specify a directory containing an .hhconfig",
        ),
        spec(
            "--diff",
            Unit,
            Opt::Diff,
            " Format the changed lines in a diff (example: hg diff | hackfmt --diff)",
        ),
        spec(
            "--diff-root",
            String,
            Opt::DiffRoot,
            "[dir]  (for use with --diff) Specify a directory paths are relative to in a diffs file.If not specified, defaults to `hg root`. If no hg root, falls back to WWW root.",
        ),
        spec(
            "--diff-dry-run",
            Unit,
            Opt::DiffDryRun,
            " Preview the files that would be overwritten by --diff mode",
        ),
        spec(
            "--check-formatting",
            Unit,
            Opt::CheckFormatting,
            " Given a list of filenames, check whether they are formatted and print the filenames which would be modified by hackfmt -i",
        ),
        spec("--debug", Unit, Opt::Debug, " Print debug statements"),
        spec(
            "--filename-for-logging",
            String,
            Opt::FilenameForLogging,
            " The filename for logging purposes, when providing file contents through stdin.",
        ),
        spec("--test", Unit, Opt::Test, " Disable logging"),
        // Extras (not in OCaml hackfmt).
        spec(
            "--hackfmt-compat",
            Unit,
            Opt::HackfmtCompat,
            " Format exactly as OCaml hackfmt, without Hakana's rules: no blank line at the start of a file, |?> laid out like other binary operators, trivia read at their own position",
        ),
        spec(
            "-j",
            Int,
            Opt::Jobs,
            "[n]  Format the files of -i and --check-formatting with n threads (default: the number of CPUs, at most 8). The output is the same for any n.",
        ),
        spec("--jobs", Int, Opt::Jobs, "[n]  Same as -j"),
        spec(
            "--recursive",
            Unit,
            Opt::Recursive,
            " With -i or --check-formatting, replace each directory argument with the Hack files under it (following symlinks, in file name order)",
        ),
    ]
}

/// `Hackfmt_debug.init_with_options`
fn debug_specs() -> Vec<Spec> {
    use ArgKind::*;
    vec![
        spec("--doc", Unit, Opt::DebugDoc, " Print out a dump of the Doc IR"),
        spec(
            "--ids",
            String,
            Opt::DebugIds,
            " Comma separate list of chunk ids to inspect (default is all)",
        ),
        spec(
            "--nesting",
            Unit,
            Opt::DebugNesting,
            " Print out a representation of the nesting graph below each chunk group",
        ),
        spec(
            "--rule-deps",
            Unit,
            Opt::DebugRuleDeps,
            " Print out a representation of the rule dependenies below each chunk group",
        ),
    ]
}

/// `Arg.usage_b`
fn usage_b(buf: &mut Vec<u8>, specs: &[Spec], errmsg: &str) {
    buf.extend_from_slice(errmsg.as_bytes());
    buf.push(b'\n');
    let mut print = |key: &str, doc: &str| {
        if !doc.is_empty() {
            buf.extend_from_slice(format!("  {} {}\n", key, doc).as_bytes());
        }
    };
    for s in specs {
        print(s.key, &s.doc);
    }
    if !specs.iter().any(|s| s.key == "-help") {
        print("-help", " Display this list of options");
    }
    if !specs.iter().any(|s| s.key == "--help") {
        print("--help", " Display this list of options");
    }
}

enum ArgError {
    Unknown(Vec<u8>),
    Missing(Vec<u8>),
    Wrong(Vec<u8>, Vec<u8>, &'static str),
}

#[derive(Default)]
struct ParsedArgs {
    linttool: bool,
    linttool_severity: Option<Vec<u8>>,
    files: Vec<Vec<u8>>,
    filename_for_logging: Option<Vec<u8>>,
    start_char: Option<isize>,
    end_char: Option<isize>,
    start_line: Option<isize>,
    end_line: Option<isize>,
    at_char: Option<isize>,
    inplace: bool,
    diff: bool,
    diff_dry: bool,
    check: bool,
    debug: bool,
    debug_config: DebugConfig,
    cli_indent_width: Option<isize>,
    cli_indent_with_tabs: bool,
    cli_line_width: Option<isize>,
    cli_root: Option<Vec<u8>>,
    diff_root_arg: Option<Vec<u8>>,
    cli_format_generated_code: bool,
    cli_version: Option<isize>,
    hackfmt_compat: bool,
    jobs: Option<isize>,
    recursive: bool,
}

/// `Str.split (Str.regexp ",")`
fn split_commas(s: &[u8]) -> Vec<&[u8]> {
    let mut start = if s.first() == Some(&b',') { 1 } else { 0 };
    let mut out = vec![];
    while start < s.len() {
        match s[start..].iter().position(|c| *c == b',') {
            None => {
                out.push(&s[start..]);
                break;
            }
            Some(i) => {
                out.push(&s[start..start + i]);
                start += i + 1;
            }
        }
    }
    out
}

/// `Arg.parse_dynamic`
fn parse_args(argv: &[Vec<u8>], io: &mut Io) -> Result<ParsedArgs, Fatal> {
    let progname = argv.first().map_or_else(|| "(?)".to_string(), |a| lossy(a).into_owned());
    let usage = format!(
        "Usage: {} [--range s e] [filename or read from stdin]\nor --linttool [filenames or @filename containing newline-separated paths]",
        progname
    );
    let mut specs = main_specs();
    let mut p = ParsedArgs::default();
    let mut current = 1;
    while current < argv.len() {
        let s = &argv[current];
        let step = (|| -> Result<Option<Fatal>, ArgError> {
            if !s.starts_with(b"-") {
                p.files.insert(0, s.clone());
                return Ok(None);
            }
            let (spec, follow) = match specs.iter().position(|sp| sp.key.as_bytes() == s.as_slice()) {
                Some(i) => (i, None),
                None => {
                    let eq = s.iter().position(|c| *c == b'=');
                    match eq.and_then(|eq| {
                        specs
                            .iter()
                            .position(|sp| sp.key.as_bytes() == &s[..eq])
                            .map(|i| (i, s[eq + 1..].to_vec()))
                    }) {
                        Some((i, arg)) => (i, Some(arg)),
                        None => return Err(ArgError::Unknown(s.clone())),
                    }
                }
            };
            let kind = specs[spec].kind;
            let opt = specs[spec].opt;
            let get_arg = |current: &mut usize| -> Result<Vec<u8>, ArgError> {
                match &follow {
                    None => {
                        if *current + 1 < argv.len() {
                            let a = argv[*current + 1].clone();
                            *current += 1;
                            Ok(a)
                        } else {
                            Err(ArgError::Missing(s.clone()))
                        }
                    }
                    Some(arg) => Ok(arg.clone()),
                }
            };
            let get_int = |arg: Vec<u8>| -> Result<isize, ArgError> {
                ocaml_int_of_string(&arg).ok_or_else(|| ArgError::Wrong(s.clone(), arg.clone(), "an integer"))
            };
            match kind {
                ArgKind::Unit => {
                    if let Some(arg) = &follow {
                        return Err(ArgError::Wrong(s.clone(), arg.clone(), "no argument"));
                    }
                    match opt {
                        Opt::Linttool => p.linttool = true,
                        Opt::InPlace => p.inplace = true,
                        Opt::Tabs => p.cli_indent_with_tabs = true,
                        Opt::FormatGeneratedCode => p.cli_format_generated_code = true,
                        Opt::Diff => p.diff = true,
                        Opt::DiffDryRun => p.diff_dry = true,
                        Opt::CheckFormatting => p.check = true,
                        Opt::Debug => {
                            p.debug = true;
                            specs = debug_specs();
                        }
                        Opt::Test => {}
                        Opt::HackfmtCompat => p.hackfmt_compat = true,
                        Opt::Recursive => p.recursive = true,
                        Opt::DebugDoc => p.debug_config.print_doc = true,
                        Opt::DebugNesting => p.debug_config.print_nesting_graph = true,
                        Opt::DebugRuleDeps => p.debug_config.print_rule_dependencies = true,
                        _ => unreachable!(),
                    }
                }
                ArgKind::String => {
                    let arg = get_arg(&mut current)?;
                    match opt {
                        Opt::LinttoolSeverity => p.linttool_severity = Some(arg),
                        Opt::Root => p.cli_root = Some(arg),
                        Opt::DiffRoot => p.diff_root_arg = Some(arg),
                        Opt::FilenameForLogging => p.filename_for_logging = Some(arg),
                        Opt::DebugIds => {
                            let mut ids = vec![];
                            for part in split_commas(&arg) {
                                match ocaml_int_of_string(part) {
                                    Some(n) => ids.push(n),
                                    None => {
                                        return Ok(Some(uncaught(
                                            io,
                                            "Failure(\"Invalid id list specification\")",
                                        )));
                                    }
                                }
                            }
                            p.debug_config.chunk_ids = Some(ids);
                        }
                        _ => unreachable!(),
                    }
                }
                ArgKind::Int => {
                    let n = get_int(get_arg(&mut current)?)?;
                    match opt {
                        Opt::AtChar => p.at_char = Some(n),
                        Opt::IndentWidth => p.cli_indent_width = Some(n),
                        Opt::LineWidth => p.cli_line_width = Some(n),
                        Opt::Version => p.cli_version = Some(n),
                        Opt::Jobs => p.jobs = Some(n),
                        _ => unreachable!(),
                    }
                }
                ArgKind::IntPair => {
                    if let Some(arg) = &follow {
                        return Err(ArgError::Wrong(s.clone(), arg.clone(), "no argument"));
                    }
                    let a = get_int(get_arg(&mut current)?)?;
                    match opt {
                        Opt::Range => p.start_char = Some(a),
                        _ => p.start_line = Some(a),
                    }
                    let b = get_int(get_arg(&mut current)?)?;
                    match opt {
                        Opt::Range => p.end_char = Some(b),
                        _ => p.end_line = Some(b),
                    }
                }
            }
            Ok(None)
        })();
        match step {
            Ok(None) => {}
            Ok(Some(fatal)) => return Err(fatal),
            Err(e) => {
                let mut b = vec![];
                let help = matches!(&e, ArgError::Unknown(s) if s == b"-help" || s == b"--help");
                match &e {
                    ArgError::Unknown(s) if s == b"-help" || s == b"--help" => {}
                    ArgError::Unknown(s) => {
                        b.extend_from_slice(format!("{}: unknown option '{}'.\n", progname, lossy(s)).as_bytes())
                    }
                    ArgError::Missing(s) => b.extend_from_slice(
                        format!("{}: option '{}' needs an argument.\n", progname, lossy(s)).as_bytes(),
                    ),
                    ArgError::Wrong(opt, arg, expected) => b.extend_from_slice(
                        format!(
                            "{}: wrong argument '{}'; option '{}' expects {}.\n",
                            progname,
                            lossy(arg),
                            lossy(opt),
                            expected
                        )
                        .as_bytes(),
                    ),
                }
                usage_b(&mut b, &specs, &usage);
                if help {
                    io.print(&b);
                    io.flush_all();
                    return Err(Fatal::Exit(0));
                } else {
                    io.eprint(&b);
                    io.flush_all();
                    return Err(Fatal::Exit(2));
                }
            }
        }
        current += 1;
    }
    Ok(p)
}

/// `parse_options` in hackfmt.ml.
fn parse_options(argv: &[Vec<u8>], io: &mut Io) -> Result<RawOptions, Fatal> {
    let p = parse_args(argv, io)?;
    if p.linttool {
        return Ok(RawOptions::Linttool);
    }
    if p.linttool_severity.is_some() {
        return Err(uncaught(
            io,
            &printexc_of_exn(&Exn::InvalidCliArg(
                "cannot use --linttool-severity without --linttool".into(),
            )),
        ));
    }
    let range = match (p.start_char, p.end_char, p.start_line, p.end_line) {
        (Some(s), Some(e), None, None) => Some(Range::Byte((s - 1, e - 1))),
        (None, None, Some(s), Some(e)) => Some(Range::Line((s, e))),
        (Some(_), Some(_), Some(_), Some(_)) => {
            return Err(uncaught(
                io,
                &printexc_of_exn(&Exn::InvalidCliArg("Cannot use --range with --line-range".into())),
            ));
        }
        _ => None,
    };
    let www_root = match &p.cli_root {
        Some(r) => path_make(r),
        None => {
            if p.diff {
                get_www_root_for_diff(io)?
            } else {
                get_www_root_for_format(&p.files)
            }
        }
    };
    let diff_root = if p.diff {
        match &p.diff_root_arg {
            Some(r) => path_make(r),
            None => match hg_root(io)? {
                Ok(hg_root) => path_make(&hg_root),
                Err(e) => {
                    io.eprint(format!(
                        "Could not find hg root:\n{}\nFalling back to WWW root {}\n",
                        e,
                        lossy(&www_root)
                    ));
                    www_root.clone()
                }
            },
        }
    } else {
        www_root.clone()
    };
    let hhconfig_path = path_concat(&www_root, b".hhconfig");
    let (config, enable_xhp_class_modifier) = if file_exists(&hhconfig_path) {
        read_hhconfig(io, &hhconfig_path)?
    } else {
        (FEnv::default(), false)
    };
    let config = FEnv {
        add_trailing_commas: config.add_trailing_commas,
        indent_width: p.cli_indent_width.unwrap_or(config.indent_width),
        indent_with_tabs: p.cli_indent_with_tabs || config.indent_with_tabs,
        line_width: p.cli_line_width.unwrap_or(config.line_width),
        format_generated_code: p.cli_format_generated_code || config.format_generated_code,
        version: if p.cli_version.is_some() { p.cli_version } else { config.version },
        hakana_rules: !p.hackfmt_compat,
    };
    Ok(RawOptions::Normal(Box::new(NormalOptions {
        files: p.files,
        filename_for_logging: p.filename_for_logging,
        range,
        at_char: p.at_char,
        inplace: p.inplace,
        diff: p.diff,
        diff_dry: p.diff_dry,
        diff_root,
        check: p.check,
        config,
        www_root,
        enable_xhp_class_modifier,
        debug: p.debug,
        debug_config: p.debug_config,
        jobs: match p.jobs {
            Some(n) if n >= 1 => n as usize,
            _ => std::thread::available_parallelism().map_or(1, usize::from).min(8),
        },
        recursive: p.recursive,
    })))
}

enum FormatOptions {
    Print {
        text_source: TextSource,
        range: Option<Range>,
        config: FEnv,
    },
    InPlace {
        files: Vec<Vec<u8>>,
        config: FEnv,
    },
    Check {
        files: Vec<Vec<u8>>,
        config: FEnv,
    },
    AtChar {
        text_source: TextSource,
        pos: isize,
        config: FEnv,
    },
    Diff {
        dry: bool,
        config: FEnv,
    },
}

fn fail(msg: impl Into<String>) -> ! {
    raise(Exn::InvalidCliArg(msg.into()))
}

/// `--recursive` (an extra): replace each directory of the (reversed) file
/// list with the Hack files under it, following symlinks, in file name order,
/// each file once. Returns the list in the same reversed order.
fn expand_directories(files: &[Vec<u8>]) -> Vec<Vec<u8>> {
    fn walk(dir: &Path, seen_dirs: &mut std::collections::HashSet<std::path::PathBuf>, out: &mut Vec<Vec<u8>>) {
        let Ok(canonical) = std::fs::canonicalize(dir) else {
            return;
        };
        if !seen_dirs.insert(canonical) {
            return;
        }
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<_> = entries.filter_map(|e| e.ok()).map(|e| e.path()).collect();
        entries.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
        for path in entries {
            if path.is_dir() {
                walk(&path, seen_dirs, out);
            } else if path.is_file() {
                let bytes = path.as_os_str().as_bytes().to_vec();
                if is_hack(&bytes) {
                    out.push(bytes);
                }
            }
        }
    }
    let mut out = vec![];
    let mut seen_files = std::collections::HashSet::new();
    for path in files.iter().rev() {
        if os(path).is_dir() {
            let mut found = vec![];
            walk(os(path), &mut std::collections::HashSet::new(), &mut found);
            for f in found {
                let key = std::fs::canonicalize(os(&f)).map_or_else(|_| f.clone(), |p| p.into_os_string().into_vec());
                if seen_files.insert(key) {
                    out.push(f);
                }
            }
        } else {
            out.push(path.clone());
        }
    }
    out.reverse();
    out
}

/// `validate_options` in hackfmt.ml (raises `InvalidCliArg`).
fn validate_options(env: &Env, o: &NormalOptions, www_root: &[u8], io: &mut Io) -> FormatOptions {
    let multifile_allowed = o.inplace || o.check;
    let filename = match o.files.as_slice() {
        [filename] => Some(filename.clone()),
        [filename, _, ..] if multifile_allowed => Some(filename.clone()),
        [] => None,
        _ => fail("More than one file given"),
    };
    let text_source = match (&filename, &o.filename_for_logging) {
        (Some(_), Some(_)) => fail("Can't supply both a filename and a filename for logging"),
        (Some(filename), None) => TextSource::File(filename.clone()),
        (None, Some(f)) => TextSource::Stdin(Some(f.clone())),
        (None, None) => TextSource::Stdin(None),
    };
    let assert_file_exists = |path: &[u8]| {
        if !file_exists(path) {
            fail(format!("No such file or directory: {}", lossy(path)))
        }
    };
    if let Some(f) = &filename {
        assert_file_exists(f);
    }
    assert_file_exists(www_root);
    let expanded;
    let input_files: &[Vec<u8>] = if multifile_allowed && o.recursive {
        expanded = expand_directories(&o.files);
        &expanded
    } else {
        &o.files
    };
    let files = if multifile_allowed {
        // List.rev_filter: in the order of the (reversed) list, then reversed.
        let mut kept = vec![];
        for path in input_files {
            if is_hack(path) {
                kept.push(path.clone());
            } else {
                io.eprint(format!(
                    "Unexpected file extension (probably not a Hack file): {}\n",
                    lossy(path)
                ));
            }
        }
        kept.reverse();
        kept
    } else {
        match &text_source {
            TextSource::File(path) | TextSource::Stdin(Some(path)) if !is_hack(path) => fail(format!(
                "Unexpected file extension (probably not a Hack file): {}",
                lossy(path)
            )),
            _ => {}
        }
        o.files.clone()
    };
    // Let --diff-dry-run imply --diff
    let diff = o.diff || o.diff_dry;
    let inplace = o.inplace;
    let check = o.check;
    let range = o.range;
    let at_char = o.at_char;
    let config = o.config.clone();
    let is_file = matches!(text_source, TextSource::File(_));
    let is_stdin = !is_file;
    let is_stdin_none = matches!(text_source, TextSource::Stdin(None));
    if env.debug && diff {
        fail("Can't format diff in debug mode")
    }
    if diff && (is_file || matches!(text_source, TextSource::Stdin(Some(_)))) {
        fail("--diff mode expects no files")
    }
    if diff && range.is_some() {
        fail("--diff mode expects no range")
    }
    if diff && at_char.is_some() {
        fail("--diff mode can't format at-char")
    }
    if diff && check {
        fail("Can't check formatting in --diff mode")
    }
    if inplace && is_stdin {
        fail("Provide a filename to format in-place")
    }
    if inplace && range.is_some() {
        fail("Can't format a range in-place")
    }
    if inplace && at_char.is_some() {
        fail("Can't format at-char in-place")
    }
    if check && is_stdin {
        fail("Provide a filename to check formatting")
    }
    if inplace && check {
        fail("Can't check formatting in-place")
    }
    if check && range.is_some() {
        fail("Can't check formatting for a range")
    }
    if check && at_char.is_some() {
        fail("Can't check formatting at-char")
    }
    if !diff && !inplace && range.is_some() && at_char.is_some() {
        fail("--at-char expects no range")
    }
    if !diff && !inplace && at_char.is_none() && !check {
        return FormatOptions::Print {
            text_source,
            range,
            config,
        };
    }
    if !diff && inplace && is_file && range.is_none() {
        return FormatOptions::InPlace { files, config };
    }
    if !diff && check && is_file && range.is_none() {
        return FormatOptions::Check { files, config };
    }
    if !diff && !inplace && range.is_none() {
        if let Some(pos) = at_char {
            return FormatOptions::AtChar {
                text_source,
                pos,
                config,
            };
        }
    }
    if diff && is_stdin_none && range.is_none() {
        return FormatOptions::Diff {
            dry: o.diff_dry,
            config,
        };
    }
    raise(Exn::Other("Match_failure(\"hackfmt.ml\", 458, 2)".into()))
}

// ---------------------------------------------------------------------------
// Reading and parsing

/// `read_stdin`: read lines (dropping a trailing '\r' from each, as Core's
/// `In_channel.input_line` does), each followed by '\n'.
fn read_stdin() -> Vec<u8> {
    let mut input = vec![];
    let _ = std::io::stdin().lock().read_to_end(&mut input);
    let mut buf = Vec::with_capacity(input.len() + 1);
    if input.is_empty() {
        return buf;
    }
    let mut lines: Vec<&[u8]> = input.split(|c| *c == b'\n').collect();
    if input.ends_with(b"\n") {
        lines.pop();
    }
    for line in lines {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        buf.extend_from_slice(line);
        buf.push(b'\n');
    }
    buf
}

/// `SourceText.offset_to_position`
fn offset_to_position(bolmap: &[usize], offset: usize) -> (usize, usize) {
    // The largest index whose line start is at or before the offset.
    let index = match bolmap.binary_search(&offset) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
    };
    (index + 1, offset - bolmap[index] + 1)
}

/// `Line_break_map.make`
fn line_break_map(text: &[u8]) -> Vec<usize> {
    let len = text.len();
    let mut result = vec![];
    for i in 1..=len {
        let prev = text[i - 1];
        if (prev == b'\r' && (i == len || text[i] != b'\n')) || prev == b'\n' {
            result.push(i);
        }
    }
    if let Some(r) = result.last() {
        if *r != len {
            result.push(len);
        }
    }
    let mut map = vec![0];
    map.extend(result);
    map
}

fn positioned_string(e: &parser_core_types::syntax_error::SyntaxError, bolmap: &[usize]) -> String {
    let child = match &e.child {
        Some(child) => format!("\n  {}", positioned_string(child, bolmap)),
        None => String::new(),
    };
    let (sl, sc) = offset_to_position(bolmap, e.start_offset);
    let (el, ec) = offset_to_position(bolmap, e.end_offset);
    format!("({},{})-({},{}) {}{}", sl, sc, el, ec, e.message, child)
}

/// `parse_text`: parse, printing the syntax errors and raising
/// `InvalidSyntax` if there are any.
fn parse_text<'a>(
    io: &mut Io,
    text: &'a [u8],
    path: &[u8],
    enable_xhp_class_modifier: bool,
    config: &FEnv,
) -> SyntaxTree<'a> {
    let tree = syntax::parse(text, &lossy(path), enable_xhp_class_modifier, config.hakana_rules);
    if tree.errors.is_empty() {
        tree
    } else {
        let bolmap = line_break_map(text);
        for e in &tree.errors {
            io.eprint(format!("{}\n", positioned_string(e, &bolmap)));
        }
        raise(Exn::InvalidSyntax)
    }
}

/// The text of a text source (`read_file` or `read_stdin`) and the path the
/// parser sees.
fn read_text_source(text_source: &TextSource) -> (Vec<u8>, Vec<u8>) {
    match text_source {
        TextSource::File(filename) => (cat(filename), filename.clone()),
        TextSource::Stdin(_) => (read_stdin(), vec![]),
    }
}

// ---------------------------------------------------------------------------
// Formatting

/// If the range is a byte range, expand it to line boundaries. If the range
/// is a line range, convert it to a byte range.
fn expand_or_convert_range(source_text: &[u8], range: Range) -> Interval {
    match range {
        Range::Byte(range) => expand_to_line_boundaries(None, source_text, range),
        Range::Line((st, ed)) => {
            let line_boundaries = get_line_boundaries(source_text);
            let st = std::cmp::max(st, 1);
            let ed = std::cmp::min(ed, line_boundaries.len() as isize);
            match error::catch(|| line_interval_to_offset_range(&line_boundaries, (st, ed))) {
                Ok(r) => r,
                Err(Exn::InvalidArgument(msg)) => raise(Exn::InvalidCliArg(msg)),
                Err(e) => error::reraise(e),
            }
        }
    }
}

/// `format` in hackfmt.ml.
fn format(config: &FEnv, range: Option<Range>, tree: &SyntaxTree<'_>) -> Vec<u8> {
    match range {
        None => libhackfmt::format_tree(Some(config), tree),
        Some(range) => {
            let range = expand_or_convert_range(tree.text, range);
            let mut formatted = libhackfmt::format_range(Some(config), range, tree);
            // This is a bit of a hack to deal with situations where a newline
            // exists in the original source in a location where hackfmt
            // refuses to split, and the range end falls at that newline. It
            // looks better to add an incorrect newline than to omit it.
            match formatted.last() {
                Some(b'\n') => {}
                Some(_) => formatted.push(b'\n'),
                None => raise(Exn::InvalidArgument("index out of bounds".into())),
            }
            formatted
        }
    }
}

/// `output`: to the file of the text source, or stdout.
fn output(io: &mut Io, text_source: Option<&TextSource>, s: &[u8]) {
    match text_source {
        Some(TextSource::File(filename)) => {
            if let Err(e) = std::fs::write(os(filename), s) {
                raise(sys_error(filename, &e));
            }
        }
        _ => {
            io.print(s);
            io.flush_out();
        }
    }
}

fn debug_print(io: &mut Io, env: &Env, range: Option<Range>, config: &FEnv, text_source: &TextSource) {
    let (text, path) = read_text_source(text_source);
    let tree = parse_text(io, &text, &path, false, config);
    let range = range.map(|r| expand_or_convert_range(&text, r));
    let fenv = libhackfmt::env_from_config(Some(config));
    let arena = Bump::new();
    let doc = hack_format::transform(&fenv, &arena, &tree.root);
    let chunk_groups = crate::chunk_builder::build(&fenv, &doc);
    let (out, err) = crate::debug::debug(&env.debug_config, &fenv, range, &text, &doc, &chunk_groups);
    if !err.is_empty() {
        io.eprint(&err);
        io.flush_err();
    }
    io.print(&out);
}

/// `Parse_diff.go`: the modified line intervals of each file of a diff.
fn parse_diff(content: &[u8]) -> Vec<(Vec<u8>, Vec<Interval>)> {
    struct E {
        file: Option<Vec<u8>>,
        /// The modified lines, in order.
        modified: Vec<isize>,
        result: Vec<(Vec<u8>, Vec<Interval>)>,
    }
    fn add_file(env: &mut E) {
        // Given a list of modified lines => returns a list of intervals,
        // merging (start1, end1), (start2, end2) when end1 + 1 >= start2.
        let mut list: std::collections::VecDeque<Interval> =
            env.modified.iter().map(|x| (*x, *x)).collect();
        let mut acc = vec![];
        while let Some(first) = list.pop_front() {
            if let Some(&second) = list.front() {
                if first.1 + 1 >= second.0 {
                    list.pop_front();
                    list.push_front((std::cmp::min(first.0, second.0), std::cmp::max(first.1, second.1)));
                    continue;
                }
            }
            acc.push(first);
        }
        if let Some(filename) = &env.file {
            env.result.push((filename.clone(), acc));
        }
    }
    fn header(env: &mut E, line: &[u8]) {
        add_file(env);
        if line.len() < 4 {
            raise(Exn::InvalidArgument("String.sub / Bytes.sub".into()));
        }
        let filename = &line[4..];
        // Getting rid of the prefix b/
        env.file = if filename == b"/dev/null" {
            None
        } else if filename.len() >= 2 && &filename[..2] == b"b/" {
            Some(filename[2..].to_vec())
        } else {
            Some(filename.to_vec())
        };
        env.modified = vec![];
    }
    let mut env = E {
        file: None,
        modified: vec![],
        result: vec![],
    };
    let lines = crate::boundaries::split_on_newlines(content);
    let mut i = 0;
    let mut entered = false;
    // Skip the text before the first +++ (to make things work with git show)
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        if line.starts_with(b"+++") {
            header(&mut env, line);
            entered = true;
            break;
        }
    }
    if !entered {
        return env.result;
    }
    let mut nbr: isize = 0;
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        if line.len() > 4 && &line[..3] == b"+++" {
            header(&mut env, line);
            nbr = 0;
        } else if line.len() > 2 && &line[..2] == b"@@" {
            // Find the position right after '+' in '@@ -line,len +line, len@@'
            let pos = (0..line.len().saturating_sub(1))
                .find(|&p| line[p] == b'+' && line[p + 1].is_ascii_digit());
            let Some(pos) = pos else {
                raise(Exn::Other("Not_found".into()))
            };
            let digits: Vec<u8> = line[pos + 1..]
                .iter()
                .take_while(|c| c.is_ascii_digit())
                .copied()
                .collect();
            nbr = match ocaml_int_of_string(&digits) {
                Some(n) => n,
                None => raise(Exn::Failure("int_of_string".into())),
            };
        } else if !line.is_empty() && line[0] == b'+' {
            // Adds the line to the list of modified lines
            env.modified.push(nbr);
            nbr += 1;
        } else if !line.is_empty() && line[0] == b'-' {
            // Skips the line (we don't care about removed code)
        } else {
            nbr += 1;
        }
    }
    add_file(&mut env);
    env.result
}

/// What formatting one file of `-i` or `--check-formatting` gives: the
/// file's text (`read_file`), the formatted text or the exception, and what
/// parsing printed to stderr.
struct FileResult {
    source: Result<Vec<u8>, Exn>,
    stderr: Vec<u8>,
    formatted: Result<Vec<u8>, Exn>,
    parallel: bool,
}

fn format_file(io: &mut Io, filename: &[u8], config: &FEnv, enable_xhp_class_modifier: bool) -> FileResult {
    let source = error::catch(|| cat(filename));
    if source.is_err() {
        return FileResult {
            source,
            stderr: vec![],
            formatted: Err(Exn::Other("unreachable".into())),
            parallel: false,
        };
    }
    let formatted = error::catch(|| {
        let text = cat(filename);
        let tree = parse_text(io, &text, filename, enable_xhp_class_modifier, config);
        format(config, None, &tree)
    });
    FileResult {
        source,
        stderr: vec![],
        formatted,
        parallel: false,
    }
}

/// Run `f` on each file in order. With more than one job, the files are
/// formatted ahead on worker threads (which neither print nor write) and `f`
/// gets the result; otherwise `f` gets `None` and formats the file itself.
/// Either way `f` sees the files in order and an exception it raises stops
/// the iteration, so the output is the same as OCaml's sequential loop.
fn for_each_file(
    io: &mut Io,
    jobs: usize,
    files: &[Vec<u8>],
    config: &FEnv,
    enable_xhp_class_modifier: bool,
    mut f: impl FnMut(&mut Io, &[u8], Option<FileResult>),
) {
    if jobs <= 1 || files.len() <= 1 {
        for filename in files {
            f(io, filename, None);
        }
        return;
    }
    use std::sync::Condvar;
    use std::sync::Mutex;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;
    let window = jobs * 4;
    let next = AtomicUsize::new(0);
    // (index of the next result to consume, results ready to consume, stop)
    let state = Mutex::new((0usize, std::collections::BTreeMap::new(), false));
    let ready = Condvar::new();
    std::thread::scope(|scope| {
        for _ in 0..jobs.min(files.len()) {
            std::thread::Builder::new()
                .stack_size(1 << 30)
                .spawn_scoped(scope, || {
                    loop {
                        let i = next.fetch_add(1, Ordering::SeqCst);
                        if i >= files.len() {
                            return;
                        }
                        // Stay within a window of the consumer.
                        {
                            let mut st = state.lock().unwrap();
                            while i >= st.0 + window && !st.2 {
                                st = ready.wait(st).unwrap();
                            }
                            if st.2 {
                                return;
                            }
                        }
                        let mut wio = Io::capturing();
                        let mut r = format_file(&mut wio, &files[i], config, enable_xhp_class_modifier);
                        let (_, err) = wio.captured();
                        r.stderr = err;
                        r.parallel = true;
                        let mut st = state.lock().unwrap();
                        st.1.insert(i, r);
                        ready.notify_all();
                    }
                })
                .expect("cannot spawn a formatter thread");
        }
        let result = error::catch(|| {
            for (i, filename) in files.iter().enumerate() {
                let r = {
                    let mut st = state.lock().unwrap();
                    loop {
                        if let Some(r) = st.1.remove(&i) {
                            st.0 = i + 1;
                            ready.notify_all();
                            break r;
                        }
                        st = ready.wait(st).unwrap();
                    }
                };
                f(io, filename, Some(r));
            }
        });
        if let Err(e) = result {
            let mut st = state.lock().unwrap();
            st.2 = true;
            ready.notify_all();
            drop(st);
            error::reraise(e);
        }
    });
}

fn run_main(io: &mut Io, env: &Env, options: FormatOptions, enable_xhp_class_modifier: bool) {
    match options {
        FormatOptions::Print {
            text_source,
            range,
            config,
        } => {
            if env.debug {
                debug_print(io, env, range, &config, &text_source);
            } else {
                let (text, path) = read_text_source(&text_source);
                let tree = parse_text(io, &text, &path, enable_xhp_class_modifier, &config);
                let formatted = format(&config, range, &tree);
                output(io, None, &formatted);
            }
        }
        FormatOptions::InPlace { files, config } => {
            for_each_file(io, env.jobs, &files, &config, enable_xhp_class_modifier, |io, filename, r| {
                let text_source = TextSource::File(filename.to_vec());
                if env.debug {
                    debug_print(io, env, None, &config, &text_source);
                }
                let r = match r {
                    Some(r) => r,
                    None => format_file(io, filename, &config, enable_xhp_class_modifier),
                };
                if let Err(e) = &r.source {
                    error::reraise(e.clone());
                }
                // An earlier file of the list may have been this one (or a
                // link to it): format what is there now, as OCaml would.
                let r = if r.parallel && r.source.as_ref().ok() != Some(&cat(filename)) {
                    format_file(io, filename, &config, enable_xhp_class_modifier)
                } else {
                    r
                };
                let source_text = r.source.unwrap();
                io.eprint(&r.stderr);
                match r.formatted {
                    Ok(formatted_text) => {
                        if source_text != formatted_text {
                            output(io, Some(&text_source), &formatted_text);
                        }
                    }
                    Err(Exn::InvalidSyntax) => {
                        io.eprint(format!("Parse error in file: {}\n", lossy(filename)));
                        io.flush_err();
                    }
                    Err(e) => error::reraise(e),
                }
            });
        }
        FormatOptions::Check { files, config } => {
            for_each_file(io, env.jobs, &files, &config, enable_xhp_class_modifier, |io, filename, r| {
                let r = match r {
                    Some(r) => r,
                    None => format_file(io, filename, &config, enable_xhp_class_modifier),
                };
                let source_text = match r.source {
                    Ok(t) => t,
                    Err(e) => error::reraise(e),
                };
                io.eprint(&r.stderr);
                match r.formatted {
                    Ok(formatted_text) => {
                        if source_text != formatted_text {
                            io.print(filename);
                            io.print(b"\n");
                        }
                    }
                    Err(Exn::InvalidSyntax) => {
                        io.eprint(format!("Parse error in file: {}\n", lossy(filename)));
                        io.flush_err();
                    }
                    Err(e) => error::reraise(e),
                }
            });
        }
        FormatOptions::AtChar {
            text_source,
            pos,
            config,
        } => {
            let (text, path) = read_text_source(&text_source);
            let tree = parse_text(io, &text, &path, enable_xhp_class_modifier, &config);
            let (range, formatted) = match error::catch(|| libhackfmt::format_at_offset(Some(&config), &tree, pos)) {
                Ok(r) => r,
                Err(Exn::InvalidArgument(s)) => raise(Exn::InvalidCliArg(s)),
                Err(e) => error::reraise(e),
            };
            if env.debug {
                debug_print(io, env, Some(Range::Byte(range)), &config, &text_source);
            }
            io.print(format!("{} {}\n", range.0, range.1));
            output(io, None, &formatted);
        }
        FormatOptions::Diff { dry, config } => {
            let input = read_stdin();
            let files = parse_diff(&input);
            let mut results = vec![];
            for (rel_path, intervals) in files {
                if !is_hack(&rel_path) {
                    continue;
                }
                // We intentionally raise an exception here instead of printing
                // a message and moving on--if a file is missing, it may be a
                // signal that this diff is out of date.
                let filename = path_concat(&env.diff_root, &rel_path);
                if !file_exists(&filename) {
                    raise(Exn::InvalidDiff(format!(
                        "No such file or directory: {}",
                        lossy(&rel_path)
                    )));
                }
                let text_source = TextSource::File(filename.clone());
                let result = error::catch(|| {
                    let (text, path) = read_text_source(&text_source);
                    let tree = parse_text(io, &text, &path, enable_xhp_class_modifier, &config);
                    match error::catch(|| libhackfmt::format_intervals(Some(&config), &intervals, &tree)) {
                        Ok(r) => r,
                        Err(Exn::InvalidArgument(s)) => raise(Exn::InvalidDiff(s)),
                        Err(e) => error::reraise(e),
                    }
                });
                match result {
                    Ok(contents) => results.push((text_source, rel_path, contents)),
                    // A parse error isn't a signal that there's something
                    // wrong with the diff--there's just something wrong with
                    // that file. We can leave that file alone and move on.
                    Err(Exn::InvalidSyntax) => {
                        io.eprint(format!("Parse error in file: {}\n", lossy(&rel_path)));
                        io.flush_err();
                    }
                    Err(e) => error::reraise(e),
                }
            }
            for (text_source, rel_path, contents) in results {
                if dry {
                    io.print(b"*** ");
                    io.print(&rel_path);
                    io.print(b"\n");
                }
                let output_text_source = if dry { TextSource::Stdin(None) } else { text_source };
                output(io, Some(&output_text_source), &contents);
            }
        }
    }
}

/// Run hackfmt with the given arguments (argv[0] first) and return the exit
/// code. Output goes to `io`.
pub fn run(argv: &[Vec<u8>], io: &mut Io) -> i32 {
    let options = match parse_options(argv, io) {
        Ok(o) => o,
        Err(Fatal::Exit(code)) => return code,
    };
    let o = match options {
        // Linttool.run is a stub in this tree.
        RawOptions::Linttool => return 0,
        RawOptions::Normal(o) => o,
    };
    let env = Env {
        debug: o.debug,
        debug_config: o.debug_config.clone(),
        diff_root: o.diff_root.clone(),
        jobs: if o.debug { 1 } else { o.jobs },
    };
    let result = error::catch(|| {
        let options = validate_options(&env, &o, &o.www_root, io);
        run_main(io, &env, options, o.enable_xhp_class_modifier)
    });
    let (err_msg, exit_code) = match result {
        Ok(()) => (None, 0),
        Err(exn) => (Some(exn.message()), exn.exit_value()),
    };
    if let Some(msg) = err_msg {
        io.eprint(format!("{}\n", msg));
    }
    exit_code
}

/// The entry point of the hackfmt binary.
pub fn main() -> i32 {
    error::install_panic_hook();
    // Like OCaml programs, die on SIGPIPE.
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }
    let argv: Vec<Vec<u8>> = std::env::args_os().map(|a| a.into_vec()).collect();
    // OCaml grows its stack on demand; run with a large one.
    let child = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let mut io = Io::new();
            let code = run(&argv, &mut io);
            io.flush_all();
            code
        })
        .expect("cannot spawn the main thread");
    child.join().unwrap_or(255)
}
