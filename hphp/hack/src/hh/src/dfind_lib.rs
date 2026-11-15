// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `dfind/dfind_lib.ml`, with `dfind/dfind_env.ml`,
//! `dfind/dfind_server.ml` and `dfind/dfind_add_file.ml`: the native backend
//! of `Server_notifier` (`crate::server_notifier`), the default, which the
//! OCaml calls `Dfind` (over
//! `fsnotify/fsnotify.ml`), as a thread instead of a forked process. On Linux
//! it watches with inotify as dfind does (`crate::fsnotify`: a watch on each
//! directory it lists, with `Fsnotify.select_events`); on macOS with
//! FSEvents (the `notify` crate), on the roots recursively.
//!
//! What dfind reports is kept: every path an event names (files and
//! directories, Hack or not), the paths it knows to be under a directory that
//! an event names, and everything under a directory that appears. As dfind,
//! it is conservative (it can report more than what changed) and never
//! forgets a path. Events from inside `.git`, `.hg`, `.svn` and
//! `wiki/images` directories are dropped (dfind does not watch them).
//! `Find_utils.post_file_watcher_filter_from_fully_qualified_raw_updates`
//! filters the result, as it filters dfind's.
//!
//! A thread (the dfind server) first lists the roots (dfind's
//! initialisation; [`wait_until_ready`] waits for it), then processes the
//! events in the order they come. [`get_changes`] (`Dfind_lib.get_changes`)
//! syncs: it creates a cookie file in the first root and waits until the
//! thread has seen its event, so that the changes returned are all those made
//! before the call. An overflow of the kernel's queue (`IN_Q_OVERFLOW`,
//! `Flag::Rescan`) or an error of the watcher is what made dfind exit
//! ("INOTIFY OVERFLOW!!!"): the backend is then dead, and `get_changes`
//! fails, which `Server_notifier` turns into `Dfind_died`.
//!
//! The dfind log (`Server_files.dfind_log`, the file given to [`init`]) gets
//! the lines dfind wrote: `Initialization: <seconds>` and `Sending <n> file
//! updates`.
//!
//! Not kept: the time-stamped set of files of `Dfind_env` (`files`, which
//! nothing reads), `Dfind_lib.pid` (there is no process), the Scuba logging.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::sync::Arc;
use std::sync::Condvar;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::time::Duration;
use std::time::Instant;

#[cfg(not(target_os = "linux"))]
use notify::Watcher as _;
use regex::Regex;

use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_printf::sprintf_s;
use crate::rt::ocaml_unix;
use crate::s_set;

/// Why [`get_changes`] failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GetChangesError {
    /// The changes did not come in time (`Timeout.with_timeout`'s
    /// `on_timeout`).
    Timeout,
    /// The watcher stopped working (dfind exited): what happened.
    Died(String),
}

/// `Dfind_env.t`, without `files` (unread), and without `fsnotify` on macOS
/// (the watcher is `notify`'s).
pub struct DfindEnv {
    /// The fsnotify environment, used to interact with the kernel
    #[cfg(target_os = "linux")]
    pub fsnotify: crate::fsnotify::Env,
    /// The set of new files (files created during an event)
    pub new_files: s_set::T,
    /// The directories (and the files they contain)
    pub dirs: BTreeMap<String, s_set::T>,
    /// `Dfind_maybe.log`: the dfind log, standard error when `None`.
    #[cfg(target_os = "linux")]
    pub log: Option<Arc<Mutex<std::fs::File>>>,
}

/// `Dfind_env.make roots`
#[cfg(target_os = "linux")]
pub fn make(roots: &[String]) -> Result<DfindEnv, crate::fsnotify::Error> {
    Ok(DfindEnv {
        fsnotify: crate::fsnotify::init(roots)?,
        new_files: s_set::T::new(),
        dirs: BTreeMap::new(),
        log: None,
    })
}

/// `Dfind_env.make roots`
#[cfg(not(target_os = "linux"))]
pub fn make(_roots: &[String]) -> Result<DfindEnv, std::convert::Infallible> {
    Ok(DfindEnv {
        new_files: s_set::T::new(),
        dirs: BTreeMap::new(),
    })
}

// ---------------------------------------------------------------------------
// `Dfind_add_file`: adds a new file or directory to the environment
// ---------------------------------------------------------------------------

/// Gives back a set of all the files in the directory, with "full" paths
/// (`path/file1`, not `file1`). An error stops the listing.
pub fn get_files(path: &str, dir_handle: std::fs::ReadDir) -> s_set::T {
    let mut paths = s_set::T::new();
    for file in dir_handle {
        match file {
            Ok(file) => {
                let file = file.file_name().to_string_lossy().into_owned();
                if file == "." || file == ".." {
                } else {
                    paths.insert(ocaml_filename::concat(path, &file));
                }
            }
            Err(_) => break,
        }
    }
    paths
}

/// Gets rid of the '/' at the end of a directory name
pub fn normalize(path: &str) -> String {
    if path.ends_with('/') {
        path[..path.len() - 1].to_string()
    } else {
        path.to_string()
    }
}

/// This used to be an environment variable, but it is too complicated
/// for now. Hardcoding! Yay! (`Str.regexp`s, which `Str.string_match` matches
/// at the start of the path.)
static BLACKLIST: LazyLock<Vec<Regex>> = LazyLock::new(|| {
    [r".*/wiki/images/.*", r".*/\.git", r".*/\.svn", r".*/\.hg"]
        .iter()
        .map(|re| Regex::new(&format!("^(?:{})", re)).unwrap())
        .collect()
});

/// `blacklist`
pub fn blacklist() -> &'static [Regex] {
    &BLACKLIST
}

pub fn is_blacklisted(path: &str) -> bool {
    BLACKLIST.iter().any(|re| re.is_match(path))
}

/// The inodes seen on the way down (`ISet`), so that a loop of hard links is
/// not followed.
type ISet = BTreeSet<u64>;

/// `add_file links env path`: `None` when something failed (the maybe monad
/// of `Dfind_maybe`, which never raises).
pub fn add_file(links: &ISet, env: &mut DfindEnv, path: &str) -> Option<()> {
    let path = normalize(path);
    if is_blacklisted(&path) {
        Some(())
    } else if !env.new_files.contains(&path) {
        add_new_file(links, env, &path)
    } else {
        Some(())
    }
}

/// `add_watch links env path`
#[cfg(target_os = "linux")]
pub fn add_watch(links: &ISet, env: &mut DfindEnv, path: &str) -> Option<()> {
    match crate::fsnotify::add_watch(&mut env.fsnotify, path) {
        Err(e) => {
            handle_file_exn(env, path, e);
            None
        }
        Ok(None) => Some(()),
        Ok(Some(_watch)) => add_file(links, env, path),
    }
}

/// `add_watch links env path`: the watch itself is `notify`'s (it watches the
/// roots recursively); dfind's call of `add_file` on a new watch does nothing,
/// since the path is already one of the new files.
#[cfg(not(target_os = "linux"))]
pub fn add_watch(_links: &ISet, _env: &mut DfindEnv, _path: &str) -> Option<()> {
    Some(())
}

/// `Dfind_maybe.handle_file_exn path`, for the `Fsnotify.Error`s (the other
/// exceptions are not logged).
#[cfg(target_os = "linux")]
fn handle_file_exn(env: &DfindEnv, path: &str, e: crate::fsnotify::Error) {
    if e.err.raw_os_error() == Some(libc::ENOENT) {
        // The file got deleted in the mean time ... we don't care
    } else {
        // This is bad ...
        let msg = format!("Error: could not add watch to {} [{}]\n", path, e.reason);
        match &env.log {
            Some(log) => {
                let mut log = lock(log);
                let _ = log.write_all(msg.as_bytes());
                let _ = log.flush();
            }
            None => eprint!("{}", msg),
        }
    }
}

pub fn add_new_file(links: &ISet, env: &mut DfindEnv, path: &str) -> Option<()> {
    env.new_files.insert(path.to_string());
    let st = std::fs::symlink_metadata(path).ok()?;
    if links.contains(&st.ino()) {
        return Some(());
    }
    let mut links = links.clone();
    links.insert(st.ino());
    let kind = st.file_type();
    if kind.is_symlink() {
        // TODO add an option to support symlinks
        Some(())
    } else if kind.is_dir() {
        add_watch(&links, env, path)?;
        let dir_handle = std::fs::read_dir(path).ok()?;
        let files = get_files(path, dir_handle);
        for x in files.iter() {
            let _ = add_file(&links, env, x);
        }
        let prev_files = match env.dirs.get(path) {
            Some(files) => files.clone(),
            None => s_set::T::new(),
        };
        let prev_files = files.clone().union(prev_files);
        let mut all_files = prev_files;
        for file in files.iter() {
            match env.dirs.get(file) {
                Some(sub_dir) => all_files = sub_dir.clone().union(all_files),
                None => {
                    all_files.insert(file.clone());
                }
            }
        }
        env.dirs.insert(path.to_string(), all_files);
        Some(())
    } else {
        Some(())
    }
}

/// `Dfind_add_file.path env x`: the only thing `Dfind_add_file` exposes.
pub fn path(env: &mut DfindEnv, x: &str) {
    let _ = add_file(&ISet::new(), env, x);
}

// ---------------------------------------------------------------------------
// `Dfind_server`
// ---------------------------------------------------------------------------

/// `process_fsnotify_event env dirty event`, for the event of `path` in the
/// watched directory `wpath`.
pub fn process_fsnotify_event(
    env: &mut DfindEnv,
    dirty: s_set::T,
    path: &str,
    wpath: &str,
) -> s_set::T {
    // Tell everybody that this file has changed
    let mut dirty = dirty;
    dirty.insert(path.to_string());
    // Is it a directory? Be conservative, everything we know about this
    // directory is now "dirty"
    let mut dirty = if let Some(content) = env.dirs.get(path) {
        dirty.union(content.clone())
    } else {
        let mut dir_content = match env.dirs.get(wpath) {
            Some(content) => content.clone(),
            None => s_set::T::new(),
        };
        dir_content.insert(path.to_string());
        env.dirs.insert(wpath.to_string(), dir_content);
        dirty
    };
    env.new_files = s_set::T::new();
    // Add the file, plus all of the sub elements if it is a directory
    self::path(env, path);
    // Add everything new we found in this directory
    // (empty when it's a regular file)
    for f in env.new_files.iter() {
        dirty.insert(f.clone());
    }
    dirty
}

// ---------------------------------------------------------------------------
// `Dfind_lib`
// ---------------------------------------------------------------------------

/// What the dfind thread and the callers share.
struct State {
    /// The initial listing is done (`Ready`).
    ready: bool,
    /// The directory the cookies are made in (the first root), if the
    /// watcher is watching it; known once `ready`.
    cookie_dir: Option<String>,
    /// The paths changed since the last [`get_changes`] (`acc`).
    acc: s_set::T,
    /// The number of the last cookie seen.
    last_cookie: u64,
    /// Why the watcher stopped working, if it did.
    dead: Option<String>,
}

struct Shared {
    /// The roots, as given.
    roots: Vec<String>,
    /// The name of the cookies, but for their number.
    cookie_prefix: String,
    state: Mutex<State>,
    cond: Condvar,
    /// The dfind log.
    log: Arc<Mutex<std::fs::File>>,
}

fn lock<A>(m: &Mutex<A>) -> MutexGuard<'_, A> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

impl Shared {
    /// A line of the dfind log, as `Hh_logger` writes it in the dfind
    /// process: the time, then the message.
    fn log(&self, msg: &str) {
        self.log_raw(&format!(
            "{} {}\n",
            crate::utils::timestring(ocaml_unix::gettimeofday()),
            msg
        ));
    }

    /// Text written to the dfind log as it is.
    fn log_raw(&self, text: &str) {
        let mut log = lock(&self.log);
        let _ = log.write_all(text.as_bytes());
        let _ = log.flush();
    }

    /// The number of the cookie `path` is, if it is one of ours (made in
    /// `cookie_dir`).
    fn cookie_of_path(&self, cookie_dir: Option<&str>, path: &str) -> Option<u64> {
        let name = path.strip_prefix(cookie_dir?)?.strip_prefix('/')?;
        name.strip_prefix(self.cookie_prefix.as_str())?.parse().ok()
    }

    fn die(&self, why: String) {
        let mut state = lock(&self.state);
        if state.dead.is_none() {
            state.dead = Some(why);
        }
        self.cond.notify_all();
    }

    /// The paths an event made dirty, and the last cookie it named: given to
    /// the callers (`acc`).
    fn publish(&self, dirty: s_set::T, cookie: Option<u64>) {
        let mut state = lock(&self.state);
        if !dirty.is_empty() {
            let acc = std::mem::take(&mut state.acc);
            state.acc = acc.union(dirty);
        }
        if let Some(n) = cookie {
            state.last_cookie = state.last_cookie.max(n);
            self.cond.notify_all();
        }
    }
}

/// What stops the watching when dropped: the write end of the pipe the
/// thread polls on Linux, the `notify` watcher on macOS.
#[cfg(target_os = "linux")]
type Watcher = std::io::PipeWriter;
#[cfg(not(target_os = "linux"))]
type Watcher = notify::RecommendedWatcher;

/// What the dfind thread reads its events from, besides `DfindEnv`.
#[cfg(target_os = "linux")]
type Events = std::io::PipeReader;
#[cfg(not(target_os = "linux"))]
type Events = crossbeam_channel::Receiver<notify::Result<notify::Event>>;

/// `Dfind_lib.t`
pub struct T {
    shared: Arc<Shared>,
    watcher: Mutex<Option<Watcher>>,
    next_cookie: Mutex<u64>,
}

/// Marks the backend dead if the dfind thread ends for any reason but the
/// end of its events.
struct DeathGuard(Arc<Shared>);

impl Drop for DeathGuard {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.die("End_of_file".to_string());
        }
    }
}

/// `run_daemon (scuba_table, roots) (ic, oc)`: the dfind server, on the
/// events of `events`.
fn run_daemon(shared: Arc<Shared>, mut env: DfindEnv, events: Events) {
    let _guard = DeathGuard(shared.clone());
    let t = ocaml_unix::gettimeofday();
    let roots = shared.roots.clone();
    // `Dfind_maybe.set_log`
    #[cfg(target_os = "linux")]
    {
        env.log = Some(shared.log.clone());
    }
    for root in &roots {
        path(&mut env, root);
    }
    let cookie_dir = {
        let mut state = lock(&shared.state);
        #[cfg(target_os = "linux")]
        {
            state.cookie_dir = roots
                .first()
                .filter(|root| crate::fsnotify::is_watched(&env.fsnotify, root))
                .cloned();
        }
        state.ready = true;
        shared.cond.notify_all();
        state.cookie_dir.clone()
    };
    // `Hh_logger.log_duration "Initialization" t`
    shared.log(&format!(
        "Initialization: {:.6}",
        ocaml_unix::gettimeofday() - t
    ));
    process_events(&shared, &mut env, cookie_dir.as_deref(), events)
}

/// The loop of `run_daemon`: `Fsnotify.select`, and the events it reads
/// through `process_fsnotify_event`, until `stop`.
#[cfg(target_os = "linux")]
fn process_events(shared: &Shared, env: &mut DfindEnv, cookie_dir: Option<&str>, stop: Events) {
    use std::os::fd::AsFd;

    use crate::fsnotify;

    let mut buffer = vec![0u8; 64 * 1024];
    loop {
        let events = match fsnotify::select(&mut env.fsnotify, stop.as_fd(), &mut buffer) {
            Ok(fsnotify::Select::Events(events)) => events,
            Ok(fsnotify::Select::Stopped) => return,
            Err(fsnotify::ReadError::Error(e)) => {
                // `Unix.handle_unix_error read env`: dfind exits.
                shared.die(e.reason);
                return;
            }
            Err(fsnotify::ReadError::Overflow) => {
                // `Fsnotify.check_event_type` prints this (`Printf.printf`,
                // to the dfind log, with no timestamp) and dfind exits 5.
                shared.log_raw("INOTIFY OVERFLOW!!!\n");
                shared.die("INOTIFY OVERFLOW!!!".to_string());
                return;
            }
        };
        let mut dirty = s_set::T::new();
        let mut cookie = None;
        for event in &events {
            if let Some(n) = shared.cookie_of_path(cookie_dir, &event.path) {
                cookie = Some(cookie.map_or(n, |c: u64| c.max(n)));
                continue;
            }
            dirty = process_fsnotify_event(env, dirty, &event.path, &event.wpath);
        }
        shared.publish(dirty, cookie);
    }
}

/// The loop of `run_daemon`, on the events of FSEvents, until `stop` drops
/// the watcher.
#[cfg(not(target_os = "linux"))]
fn process_events(shared: &Shared, env: &mut DfindEnv, cookie_dir: Option<&str>, rx: Events) {
    let roots = &shared.roots;
    for event in rx.iter() {
        let event = match event {
            Ok(event) => event,
            Err(e) => {
                // `Fsnotify.read` raised.
                shared.die(format!("{}", e));
                return;
            }
        };
        if event.need_rescan() {
            // `Inotify.Q_overflow`: `Fsnotify.check_event_type` prints this
            // (`Printf.printf`, to the dfind log, with no timestamp) and
            // dfind exits 5.
            shared.log_raw("INOTIFY OVERFLOW!!!\n");
            shared.die("INOTIFY OVERFLOW!!!".to_string());
            return;
        }
        // Inotify's `Access`, `Open` and `Close_*` events are not among the
        // ones dfind asks for.
        if matches!(event.kind, notify::EventKind::Access(_)) {
            continue;
        }
        let mut dirty = s_set::T::new();
        let mut cookie = None;
        for p in &event.paths {
            let p = p.to_string_lossy().into_owned();
            if let Some(n) = shared.cookie_of_path(cookie_dir, &p) {
                cookie = Some(cookie.map_or(n, |c: u64| c.max(n)));
                continue;
            }
            // Events of the watched directories only (dfind's watches are on
            // the directories under the roots, and an event of a watch names
            // a child of its directory).
            let wpath = ocaml_filename::dirname(&p);
            let under_a_root = roots.iter().any(|root| {
                p != *root && (wpath == *root || wpath.starts_with(&format!("{}/", root)))
            });
            if !under_a_root || is_blacklisted(&wpath) {
                continue;
            }
            dirty = process_fsnotify_event(env, dirty, &p, &wpath);
        }
        shared.publish(dirty, cookie);
    }
}

/// Starts watching: `Dfind_env.make`, which creates the inotify instance
/// (the watches are added as the thread lists the roots), and the pipe that
/// stops the thread. `Err` when dfind died of it.
#[cfg(target_os = "linux")]
fn start(shared: &Shared) -> Result<(Watcher, Events, DfindEnv), String> {
    let env = match make(&shared.roots) {
        Ok(env) => env,
        Err(e) => {
            // `Fsnotify.init` (`Inotify.create`) raised in `Dfind_env.make`,
            // before dfind's `Ready`: the dfind process died of the uncaught
            // exception, which the runtime printed to its log.
            shared.log_raw(&format!(
                "Fatal error: exception Fsnotify.Error({}, _)\n",
                sprintf_s(&e.reason)
            ));
            return Err(e.reason);
        }
    };
    let (stop_read, stop_write) = std::io::pipe().map_err(|e| e.to_string())?;
    Ok((stop_write, stop_read, env))
}

/// Starts watching: the FSEvents stream of each root, which it watches
/// recursively. `Err` when dfind died of it.
#[cfg(not(target_os = "linux"))]
fn start(shared: &Shared) -> Result<(Watcher, Events, DfindEnv), String> {
    let roots = &shared.roots;
    let (tx, rx) = crossbeam_channel::unbounded();
    let config = notify::Config::default().with_follow_symlinks(false);
    let watcher = notify::RecommendedWatcher::new(
        move |event: notify::Result<notify::Event>| {
            let _ = tx.send(event);
        },
        config,
    );
    let mut watcher = match watcher {
        Ok(watcher) => watcher,
        Err(e) => {
            // `Fsnotify.init` (`Inotify.create`) raised in `Dfind_env.make`,
            // before dfind's `Ready`: the dfind process died of the uncaught
            // exception, which the runtime printed to its log.
            shared.log_raw(&format!(
                "Fatal error: exception Fsnotify.Error({}, _)\n",
                sprintf_s(&e.to_string())
            ));
            return Err(format!("{}", e));
        }
    };
    let mut watched = vec![];
    for root in roots {
        match watcher.watch(std::path::Path::new(root), notify::RecursiveMode::Recursive) {
            Ok(()) => watched.push(root.clone()),
            // `Dfind_maybe.handle_file_exn`: `Fsnotify.Error (_,
            // ENOENT)`, "The file got deleted in the mean time ... we
            // don't care".
            Err(notify::Error {
                kind: notify::ErrorKind::PathNotFound,
                ..
            }) => {}
            Err(notify::Error {
                kind: notify::ErrorKind::Io(e),
                ..
            }) if e.kind() == std::io::ErrorKind::NotFound => {}
            // `Dfind_maybe.handle_file_exn`: logged, and dfind carries on.
            Err(e) => shared.log_raw(&format!("Error: could not add watch to {} [{}]\n", root, e)),
        }
    }
    lock(&shared.state).cookie_dir = roots.first().filter(|root| watched.contains(root)).cloned();
    let env = match make(roots) {
        Ok(env) => env,
        Err(e) => match e {},
    };
    Ok((watcher, rx, env))
}

/// `Dfind_lib.init (in_fd, log_fd, log_fd) (scuba_table, roots)`: starts
/// watching `roots` and listing them; `log_fd` is the dfind log.
pub fn init(log_fd: std::fs::File, roots: &[path::T]) -> T {
    let roots: Vec<String> = roots.iter().map(path::to_string).collect();
    let shared = Arc::new(Shared {
        roots,
        cookie_prefix: format!(".hh_server_cookie.{}.", ocaml_unix::getpid()),
        state: Mutex::new(State {
            ready: false,
            cookie_dir: None,
            acc: s_set::T::new(),
            last_cookie: 0,
            dead: None,
        }),
        cond: Condvar::new(),
        log: Arc::new(Mutex::new(log_fd)),
    });
    let (watcher, events, env) = match start(&shared) {
        Ok(started) => started,
        Err(why) => {
            shared.die(why);
            return T {
                shared,
                watcher: Mutex::new(None),
                next_cookie: Mutex::new(0),
            };
        }
    };
    let thread_shared = shared.clone();
    let name = format!("file watching process for server {}", ocaml_unix::getpid());
    std::thread::Builder::new()
        .name(name)
        .spawn(move || run_daemon(thread_shared, env, events))
        .expect("could not start the file watching thread");
    T {
        shared,
        watcher: Mutex::new(Some(watcher)),
        next_cookie: Mutex::new(0),
    }
}

/// `Dfind_lib.wait_until_ready`: waits for the end of the initial listing.
/// Like reading dfind's `Ready` message, fails (`End_of_file`) if the
/// watcher died first.
pub fn wait_until_ready(t: &T) -> Result<(), GetChangesError> {
    let mut state = lock(&t.shared.state);
    loop {
        if state.ready {
            return Ok(());
        }
        if let Some(why) = &state.dead {
            return Err(GetChangesError::Died(why.clone()));
        }
        state = t.shared.cond.wait(state).unwrap_or_else(|e| e.into_inner());
    }
}

/// `Dfind_lib.get_changes`: the paths changed since the last call, all those
/// changed before this one included (see the module documentation), within
/// `timeout`.
pub fn get_changes(t: &T, timeout: Duration) -> Result<s_set::T, GetChangesError> {
    let deadline = Instant::now() + timeout;
    // dfind reads the request once it is `Ready`.
    let cookie_dir = {
        let mut state = lock(&t.shared.state);
        loop {
            if let Some(why) = &state.dead {
                return Err(GetChangesError::Died(why.clone()));
            }
            if state.ready {
                break state.cookie_dir.clone();
            }
            let now = Instant::now();
            if now >= deadline {
                return Err(GetChangesError::Timeout);
            }
            state = t
                .shared
                .cond
                .wait_timeout(state, deadline - now)
                .unwrap_or_else(|e| e.into_inner())
                .0;
        }
    };
    let cookie = match &cookie_dir {
        None => None,
        Some(dir) => {
            let n = {
                let mut next = lock(&t.next_cookie);
                *next += 1;
                *next
            };
            let file = ocaml_filename::concat(dir, &format!("{}{}", t.shared.cookie_prefix, n));
            match std::fs::write(&file, b"") {
                Ok(()) => Some((n, file)),
                Err(e) => {
                    // A root we cannot write to: the changes seen so far.
                    t.shared
                        .log(&format!("Could not create the cookie {}: {}", file, e));
                    None
                }
            }
        }
    };
    let mut state = lock(&t.shared.state);
    if let Some((n, file)) = &cookie {
        while state.last_cookie < *n && state.dead.is_none() {
            let now = Instant::now();
            if now >= deadline {
                drop(state);
                let _ = std::fs::remove_file(file);
                return Err(GetChangesError::Timeout);
            }
            state = t
                .shared
                .cond
                .wait_timeout(state, deadline - now)
                .unwrap_or_else(|e| e.into_inner())
                .0;
        }
        let _ = std::fs::remove_file(file);
    }
    if let Some(why) = &state.dead {
        return Err(GetChangesError::Died(why.clone()));
    }
    let acc = std::mem::take(&mut state.acc);
    drop(state);
    let count = acc.len();
    if count > 0 {
        t.shared.log(&format!("Sending {} file updates\n", count));
    }
    Ok(acc)
}

/// `Dfind_lib.stop`: stops watching.
pub fn stop(t: &T) {
    lock(&t.watcher).take();
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A temporary root (canonical, as `Server_args.root` is) and a dfind
    /// log in it.
    fn scratch(name: &str) -> (String, std::fs::File) {
        let dir = std::env::temp_dir().join(format!(
            "hh_notifier_native_{}_{}",
            name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let dir = std::fs::canonicalize(&dir)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string();
        let log_dir = format!("{}.logs", dir);
        let _ = std::fs::remove_dir_all(&log_dir);
        std::fs::create_dir_all(&log_dir).unwrap();
        let log = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("{}/dfind.log", log_dir))
            .unwrap();
        (dir, log)
    }

    fn cleanup(root: &str) {
        let _ = std::fs::remove_dir_all(root);
        let _ = std::fs::remove_dir_all(format!("{}.logs", root));
    }

    fn changes(t: &T) -> Vec<String> {
        get_changes(t, Duration::from_secs(20))
            .unwrap()
            .into_iter()
            .collect()
    }

    #[test]
    fn blacklisted_paths() {
        assert!(is_blacklisted("/a/.git"));
        assert!(is_blacklisted("/a/.git/objects"));
        // `Str.string_match` matches a prefix.
        assert!(is_blacklisted("/a/.github"));
        assert!(is_blacklisted("/a/wiki/images/x"));
        assert!(!is_blacklisted("/a/wiki/images"));
        assert!(!is_blacklisted("/a/b.php"));
        assert_eq!(normalize("/a/b/"), "/a/b");
        assert_eq!(normalize("/a/b"), "/a/b");
    }

    #[test]
    fn dfind_environment() {
        let (root, _log) = scratch("env");
        std::fs::create_dir_all(format!("{root}/d/e")).unwrap();
        std::fs::write(format!("{root}/d/e/f.php"), "").unwrap();
        std::fs::write(format!("{root}/g.php"), "").unwrap();
        let mut env = make(&[root.clone()]).unwrap();
        path(&mut env, &root);
        let d = &env.dirs[&format!("{root}/d")];
        assert!(d.contains(&format!("{root}/d/e")));
        assert!(d.contains(&format!("{root}/d/e/f.php")));
        // An event naming a directory: everything known under it.
        let dirty = process_fsnotify_event(&mut env, s_set::T::new(), &format!("{root}/d"), &root);
        assert!(dirty.contains(&format!("{root}/d")));
        assert!(dirty.contains(&format!("{root}/d/e/f.php")));
        // An event naming a file: the file.
        std::fs::write(format!("{root}/h.php"), "").unwrap();
        let dirty =
            process_fsnotify_event(&mut env, s_set::T::new(), &format!("{root}/h.php"), &root);
        assert_eq!(dirty.len(), 1);
        assert!(env.dirs[&root].contains(&format!("{root}/h.php")));
        cleanup(&root);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn watches_the_listed_directories() {
        let (root, _log) = scratch("watches");
        std::fs::create_dir_all(format!("{root}/d/e")).unwrap();
        std::fs::create_dir_all(format!("{root}/.git/objects")).unwrap();
        std::fs::write(format!("{root}/g.php"), "").unwrap();
        let mut env = make(&[root.clone()]).unwrap();
        path(&mut env, &root);
        for dir in ["", "/d", "/d/e"] {
            assert!(
                crate::fsnotify::is_watched(&env.fsnotify, &format!("{root}{dir}")),
                "{dir}"
            );
        }
        for path in ["/.git", "/.git/objects", "/g.php"] {
            assert!(
                !crate::fsnotify::is_watched(&env.fsnotify, &format!("{root}{path}")),
                "{path}"
            );
        }
        assert_eq!(crate::fsnotify::select_events().bits(), 0xfc6);
        cleanup(&root);
    }

    #[test]
    fn watches_a_directory() {
        let (root, log) = scratch("watch");
        std::fs::write(format!("{root}/a.php"), "1").unwrap();
        std::fs::write(format!("{root}/b.php"), "1").unwrap();
        std::fs::write(format!("{root}/c.php"), "1").unwrap();
        std::fs::create_dir_all(format!("{root}/.git")).unwrap();
        let t = init(log, &[root.clone()]);
        wait_until_ready(&t).unwrap();
        // FSEvents can report the writes made just before the stream
        // started (dfind would not): extra paths, which is conservative.
        // They come before the first cookie, so once they are read nothing
        // has changed.
        let _ = changes(&t);
        assert_eq!(changes(&t), Vec::<String>::new());

        // A change.
        std::fs::write(format!("{root}/a.php"), "2").unwrap();
        assert!(changes(&t).contains(&format!("{root}/a.php")));
        // Reported once.
        assert!(!changes(&t).contains(&format!("{root}/a.php")));
        // A read is not a change.
        std::fs::read(format!("{root}/a.php")).unwrap();
        assert_eq!(changes(&t), Vec::<String>::new());

        // A creation, a deletion, a rename (both names), a .hhconfig.
        std::fs::write(format!("{root}/new.php"), "").unwrap();
        std::fs::remove_file(format!("{root}/b.php")).unwrap();
        std::fs::rename(format!("{root}/c.php"), format!("{root}/c2.php")).unwrap();
        std::fs::write(format!("{root}/.hhconfig"), "").unwrap();
        let c = changes(&t);
        for p in ["new.php", "b.php", "c.php", "c2.php", ".hhconfig"] {
            assert!(c.contains(&format!("{root}/{p}")), "{p} not in {c:?}");
        }
        // The cookies are not changes.
        assert!(!c.iter().any(|p| p.contains(".hh_server_cookie")), "{c:?}");

        // A directory that appears: what is in it.
        let tmp = format!("{root}.logs/moved");
        std::fs::create_dir_all(format!("{tmp}/sub")).unwrap();
        std::fs::write(format!("{tmp}/sub/x.php"), "").unwrap();
        std::fs::rename(&tmp, format!("{root}/moved")).unwrap();
        let c = changes(&t);
        assert!(c.contains(&format!("{root}/moved")), "{c:?}");
        assert!(c.contains(&format!("{root}/moved/sub/x.php")), "{c:?}");

        // Inside .git: not reported.
        std::fs::write(format!("{root}/.git/index.php"), "").unwrap();
        std::fs::write(format!("{root}/after.php"), "").unwrap();
        let c = changes(&t);
        assert!(c.contains(&format!("{root}/after.php")), "{c:?}");
        assert!(!c.contains(&format!("{root}/.git/index.php")), "{c:?}");

        // Ignored paths are the filter's business: vendor/bin is reported here.
        std::fs::create_dir_all(format!("{root}/vendor/bin")).unwrap();
        let _ = changes(&t);
        std::fs::write(format!("{root}/vendor/bin/v.php"), "").unwrap();
        assert!(changes(&t).contains(&format!("{root}/vendor/bin/v.php")));

        stop(&t);
        let log = std::fs::read_to_string(format!("{root}.logs/dfind.log")).unwrap();
        assert!(log.contains("] Initialization: "), "{log}");
        assert!(log.contains(" file updates\n\n"), "{log}");
        cleanup(&root);
    }
}
