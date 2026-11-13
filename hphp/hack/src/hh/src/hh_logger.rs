// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! `Hh_logger` (`utils/core/hh_logger.ml`). See `hh/PORTING.md`.
//!
//! Lines go to stderr and, after [`set_log`], to the log file as well, each
//! filtered by its own minimum level (`level::set_min_level_file`,
//! `level::set_min_level_stderr`) and, for lines with a category, by the
//! categories that are switched on (`level::set_categories`).
//!
//! The format string and its arguments are one `&str`: the caller formats.
//! `log` takes nothing else (its `?lvl` and `?category` are [`log_with`]).

use std::io::Write;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::RwLock;

use crate::exception;

/// `dupe_log`: we might want to log to both stderr and a file.
static DUPE_LOG: Mutex<Option<std::fs::File>> = Mutex::new(None);

/// The state of `Hh_logger` (the log file, the id, the minimum levels and
/// stderr) of a thread that stands for an OCaml process of its own: the IDE
/// daemon (`clientIdeDaemon`) runs as a thread of `hh_client lsp` here
/// (plan §6 #35), and logs as its own process does (to `.client_ide_log`,
/// with its own levels; its stderr is the LSP log file, as `Daemon.spawn`
/// gives it). Not in the OCaml. (Added by G1.)
pub struct Instance {
    dupe_log: Mutex<Option<std::fs::File>>,
    id: RwLock<Option<String>>,
    min_level_file: RwLock<level::T>,
    min_level_stderr: RwLock<level::T>,
    /// The process's stderr when `None`.
    stderr: Mutex<Option<std::fs::File>>,
}

impl Instance {
    /// A fresh state (no log file, no id, the default levels), whose stderr
    /// is `stderr` (the process's when `None`).
    pub fn new(stderr: Option<std::fs::File>) -> std::sync::Arc<Self> {
        std::sync::Arc::new(Self {
            dupe_log: Mutex::new(None),
            id: RwLock::new(None),
            min_level_file: RwLock::new(level::T::Info),
            min_level_stderr: RwLock::new(level::T::Info),
            stderr: Mutex::new(stderr),
        })
    }
}

thread_local! {
    static INSTANCE: std::cell::RefCell<Option<std::sync::Arc<Instance>>> =
        const { std::cell::RefCell::new(None) };
}

/// Makes `instance` the state of `Hh_logger` for the calling thread (the
/// process-wide one again when `None`).
pub fn set_thread_instance(instance: Option<std::sync::Arc<Instance>>) {
    INSTANCE.with_borrow_mut(|i| *i = instance)
}

/// The state of the calling thread, if it has one of its own.
pub fn thread_instance() -> Option<std::sync::Arc<Instance>> {
    INSTANCE.with_borrow(|i| i.clone())
}

/// `set_log filename`: also write the log to `filename` (appending; a
/// previous log file is closed). Like `Out_channel.create`, a file that
/// cannot be opened raises (`Sys_error`).
pub fn set_log(filename: &str) {
    let instance = thread_instance();
    let mut dupe_log = match &instance {
        Some(instance) => instance.dupe_log.lock().unwrap(),
        None => DUPE_LOG.lock().unwrap(),
    };
    *dupe_log = None;
    match std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(filename)
    {
        Ok(file) => *dupe_log = Some(file),
        Err(e) => panic!("Sys_error: {}: {}", filename, e),
    }
}

static ID: RwLock<Option<String>> = RwLock::new(None);

pub fn set_id(passed_id: &str) {
    match thread_instance() {
        Some(instance) => *instance.id.write().unwrap() = Some(passed_id.to_string()),
        None => *ID.write().unwrap() = Some(passed_id.to_string()),
    }
}

pub fn get_id() -> Option<String> {
    match thread_instance() {
        Some(instance) => instance.id.read().unwrap().clone(),
        None => ID.read().unwrap().clone(),
    }
}

fn id_string() -> String {
    match get_id() {
        None => String::new(),
        Some(id) => format!("[{}] ", id),
    }
}

fn category_string(category: Option<&str>) -> String {
    match category {
        None => String::new(),
        Some(category) => format!("[{}] ", category),
    }
}

/// `passes`
#[derive(Clone, Copy, Debug)]
pub struct Passes {
    pub passes_file: bool,
    pub passes_stderr: bool,
}

/// `Unix.gettimeofday ()`
fn gettimeofday() -> f64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_secs_f64(),
        Err(e) => -e.duration().as_secs_f64(),
    }
}

fn print_with_newline_internal(
    category: Option<&str>,
    passes: Passes,
    exn: Option<&exception::T>,
    s: &str,
) {
    let exn_str = match exn {
        None => String::new(),
        Some(exn) => {
            let bt = crate::string_utils::indent(
                8,
                exception::get_backtrace_string(exn).trim(),
            );
            let bt = if bt.is_empty() {
                String::new()
            } else {
                format!("\n    Backtrace:\n{}", bt)
            };
            format!(
                "\n    Exception: {}{}",
                exception::get_ctor_string(exn),
                bt
            )
        }
    };
    let time = crate::utils::timestring(gettimeofday());
    let id_str = id_string();
    let category_str = category_string(category);
    let line = format!("{} {}{}{}{}\n", time, id_str, category_str, s, exn_str);
    let instance = thread_instance();
    if passes.passes_file {
        let mut dupe_log = match &instance {
            Some(instance) => instance.dupe_log.lock().unwrap(),
            None => DUPE_LOG.lock().unwrap(),
        };
        if let Some(dupe_log) = dupe_log.as_mut() {
            let _ = dupe_log.write_all(line.as_bytes());
            let _ = dupe_log.flush();
        }
    }
    if let Some(instance) = &instance {
        if passes.passes_stderr {
            if let Some(stderr) = instance.stderr.lock().unwrap().as_mut() {
                let _ = stderr.write_all(line.as_bytes());
                let _ = stderr.flush();
                return;
            }
        }
    }
    if passes.passes_stderr {
        let mut stderr = std::io::stderr().lock();
        let _ = stderr.write_all(line.as_bytes());
        let _ = stderr.flush();
    }
}

/// `print_with_newline ?exn`: to the file and to stderr, whatever the levels.
pub fn print_with_newline(exn: Option<&exception::T>, s: &str) {
    print_with_newline_internal(
        None,
        Passes {
            passes_file: true,
            passes_stderr: true,
        },
        exn,
        s,
    )
}

/// `print_duration name t`: logs how long since `t`; returns the time now.
pub fn print_duration(name: &str, t: f64) -> f64 {
    let t2 = gettimeofday();
    print_with_newline(None, &format!("{}: {:.6}", name, t2 - t));
    t2
}

/// `exc ?prefix ~stack e`, with `e` already printed (`Exn.to_string e`).
pub fn exc(prefix: Option<&str>, stack: &str, e: &str) {
    print_with_newline(None, &format!("{}{}\n{}", prefix.unwrap_or(""), e, stack))
}

/// `exception_ ?prefix e`: `prefix` defaults to `""`.
pub fn exception_(prefix: Option<&str>, e: &exception::T) {
    exc(
        prefix,
        &exception::get_backtrace_string(e),
        &exception::get_ctor_string(e),
    )
}

pub mod level {
    use std::sync::RwLock;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum T {
        Off,
        Fatal,
        Error,
        Warn,
        Info,
        Debug,
    }

    pub fn to_enum(level: T) -> isize {
        match level {
            T::Off => 6,
            T::Fatal => 5,
            T::Error => 4,
            T::Warn => 3,
            T::Info => 2,
            T::Debug => 1,
        }
    }

    pub fn of_enum(i: isize) -> Option<T> {
        match i {
            6 => Some(T::Off),
            5 => Some(T::Fatal),
            4 => Some(T::Error),
            3 => Some(T::Warn),
            2 => Some(T::Info),
            1 => Some(T::Debug),
            _ => None,
        }
    }

    pub fn to_enum_string(level: T) -> String {
        match level {
            T::Off => "off",
            T::Fatal => "fatal",
            T::Error => "error",
            T::Warn => "warn",
            T::Info => "info",
            T::Debug => "debug",
        }
        .to_string()
    }

    pub fn of_enum_string(s: &str) -> Option<T> {
        match s {
            "off" => Some(T::Off),
            "fatal" => Some(T::Fatal),
            "error" => Some(T::Error),
            "warn" => Some(T::Warn),
            "info" => Some(T::Info),
            "debug" => Some(T::Debug),
            _ => None,
        }
    }

    static MIN_LEVEL_FILE: RwLock<T> = RwLock::new(T::Info);

    static MIN_LEVEL_STDERR: RwLock<T> = RwLock::new(T::Info);

    /// overwrites min level for file (if enabled), but leaves stderr as is
    pub fn set_min_level_file(level: T) {
        match super::thread_instance() {
            Some(instance) => *instance.min_level_file.write().unwrap() = level,
            None => *MIN_LEVEL_FILE.write().unwrap() = level,
        }
    }

    /// overwrites min level for stderr, but leaves file (if enabled) as is
    pub fn set_min_level_stderr(level: T) {
        match super::thread_instance() {
            Some(instance) => *instance.min_level_stderr.write().unwrap() = level,
            None => *MIN_LEVEL_STDERR.write().unwrap() = level,
        }
    }

    /// overwrites min level for both stderr and file (if enabled)
    pub fn set_min_level(level: T) {
        set_min_level_file(level);
        set_min_level_stderr(level);
    }

    /// returns the min file log level
    pub fn min_level_file() -> T {
        match super::thread_instance() {
            Some(instance) => *instance.min_level_file.read().unwrap(),
            None => *MIN_LEVEL_FILE.read().unwrap(),
        }
    }

    /// returns the min stderr log level
    pub fn min_level_stderr() -> T {
        match super::thread_instance() {
            Some(instance) => *instance.min_level_stderr.read().unwrap(),
            None => *MIN_LEVEL_STDERR.read().unwrap(),
        }
    }

    /// returns true if t passes either stderr or file min level (regardless
    /// whether file is enabled)
    pub fn passes_min_level(level: T) -> bool {
        let ilevel = to_enum(level);
        let passes_file = ilevel >= to_enum(min_level_file());
        let passes_stderr = ilevel >= to_enum(min_level_stderr());
        passes_file || passes_stderr
    }

    static CATEGORIES: RwLock<Vec<String>> = RwLock::new(Vec::new());

    /// `set_categories`: the categories whose lines are logged (a line
    /// without a category always is).
    pub fn set_categories(categories: &[&str]) {
        *CATEGORIES.write().unwrap() = categories.iter().map(|c| c.to_string()).collect();
    }

    /// `passes level ~category`
    pub fn passes(level: T, category: Option<&str>) -> Option<super::Passes> {
        let passes_category = match category {
            None => true,
            Some(category) => CATEGORIES.read().unwrap().iter().any(|c| c == category),
        };
        if !passes_category {
            return None;
        }
        let ilevel = to_enum(level);
        let passes_file = ilevel >= to_enum(min_level_file());
        let passes_stderr = ilevel >= to_enum(min_level_stderr());
        if passes_file || passes_stderr {
            Some(super::Passes {
                passes_file,
                passes_stderr,
            })
        } else {
            None
        }
    }

    /// `log level ?category ?exn`
    pub fn log(
        level: T,
        category: Option<&str>,
        exn: Option<&crate::exception::T>,
        msg: &str,
    ) {
        if let Some(passes) = passes(level, category) {
            super::print_with_newline_internal(category, passes, exn, msg)
        }
    }

    /// `log_lazy level ?category ?exn s`: `s` is forced only if the line is
    /// logged.
    pub fn log_lazy(
        level: T,
        category: Option<&str>,
        exn: Option<&crate::exception::T>,
        s: impl FnOnce() -> String,
    ) {
        if let Some(passes) = passes(level, category) {
            super::print_with_newline_internal(category, passes, exn, &s())
        }
    }

    /// logs the message and how long the presumed operation took, assuming
    /// that the float argument is the start time and that the end time is
    /// now. Return said end time.
    pub fn log_duration(level: T, category: Option<&str>, name: &str, t: f64) -> f64 {
        let t2 = super::gettimeofday();
        if let Some(passes) = passes(level, category) {
            super::print_with_newline_internal(
                category,
                passes,
                None,
                &format!("{}: {:.6}", name, t2 - t),
            )
        }
        t2
    }
}

/// `log fmt`: at level `Info`, without a category.
pub fn log(msg: &str) {
    level::log(level::T::Info, None, None, msg)
}

/// `log ?lvl ?category fmt`: `lvl` defaults to `Info`.
pub fn log_with(lvl: Option<level::T>, category: Option<&str>, msg: &str) {
    level::log(lvl.unwrap_or(level::T::Info), category, None, msg)
}

/// `log_lazy ?lvl ?category str`: `lvl` defaults to `Info`; the string is
/// forced only if the line is logged.
pub fn log_lazy<F: FnOnce() -> String>(
    lvl: Option<level::T>,
    category: Option<&str>,
    str: &LazyLock<String, F>,
) {
    level::log_lazy(lvl.unwrap_or(level::T::Info), category, None, || {
        (**str).clone()
    })
}

/// `lvl` defaults to `Info`. Returns the time now.
pub fn log_duration(lvl: Option<level::T>, category: Option<&str>, name: &str, t: f64) -> f64 {
    let lvl = lvl.unwrap_or(level::T::Info);
    level::log_duration(lvl, category, name, t)
}

pub fn fatal(category: Option<&str>, exn: Option<&exception::T>, msg: &str) {
    level::log(level::T::Fatal, category, exn, msg)
}

pub fn error(category: Option<&str>, exn: Option<&exception::T>, msg: &str) {
    level::log(level::T::Error, category, exn, msg)
}

pub fn warn(category: Option<&str>, exn: Option<&exception::T>, msg: &str) {
    level::log(level::T::Warn, category, exn, msg)
}

pub fn info(category: Option<&str>, exn: Option<&exception::T>, msg: &str) {
    level::log(level::T::Info, category, exn, msg)
}

pub fn debug(category: Option<&str>, exn: Option<&exception::T>, msg: &str) {
    level::log(level::T::Debug, category, exn, msg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn levels() {
        // The default minimum is `Info`.
        assert!(level::passes_min_level(level::T::Info));
        assert!(level::passes_min_level(level::T::Error));
        assert!(!level::passes_min_level(level::T::Debug));
        for l in [
            level::T::Off,
            level::T::Fatal,
            level::T::Error,
            level::T::Warn,
            level::T::Info,
            level::T::Debug,
        ] {
            assert_eq!(level::of_enum(level::to_enum(l)), Some(l));
            assert_eq!(level::of_enum_string(&level::to_enum_string(l)), Some(l));
        }
        assert_eq!(level::of_enum(0), None);
        assert_eq!(level::of_enum_string("Info"), None);
    }

    #[test]
    fn durations() {
        // At `Debug`, below the minimum: returns the time, logs nothing (the
        // other test of the module reads the log file).
        let t = log_duration(Some(level::T::Debug), None, "x", 0.);
        assert!(t > 1.6e9);
        // Below the minimum level: not logged, not forced.
        level::log_lazy(level::T::Debug, None, None, || unreachable!());
        // A category that is not switched on: not logged.
        level::log_lazy(level::T::Error, Some("cat"), None, || unreachable!());
    }

    #[test]
    fn writes_lines_to_the_log_file() {
        let path = std::env::temp_dir().join(format!("hh_logger_test_{}.log", std::process::id()));
        let _ = std::fs::remove_file(&path);
        set_log(path.to_str().unwrap());
        level::set_categories(&["mine"]);
        warn(Some("mine"), None, "a warning");
        warn(Some("other"), None, "not logged");
        let text = std::fs::read_to_string(&path).unwrap();
        let _ = std::fs::remove_file(&path);
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 1, "{text}");
        // `[YYYY-MM-DD HH:MM:SS.mmm] [mine] a warning`
        let line = lines[0];
        assert_eq!(&line[0..1], "[");
        assert_eq!(&line[24..], "] [mine] a warning");
        assert_eq!(&line[5..6], "-");
        assert_eq!(&line[11..12], " ");
        assert_eq!(&line[20..21], ".");
    }
}
