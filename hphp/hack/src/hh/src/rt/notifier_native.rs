// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The native backend of `Server_notifier` (`crate::server_notifier`), the
//! default: what the OCaml calls `Dfind` (`dfind/dfind_lib.ml`, the dfind
//! server of `dfind/dfind_server.ml`, `dfind/dfind_add_file.ml`, over
//! `fsnotify/fsnotify.ml`), on the `notify` crate (FSEvents on macOS, inotify
//! on Linux) instead of a forked process with its own inotify.
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
//! before the call. An overflow of the kernel's queue (`Flag::Rescan`) or an
//! error of the watcher is what made dfind exit ("INOTIFY OVERFLOW!!!"): the
//! backend is then dead, and `get_changes` fails, which `Server_notifier`
//! turns into `Dfind_died`.
//!
//! The dfind log (`Server_files.dfind_log`, the file given to [`init`]) gets
//! the lines dfind wrote: `Initialization: <seconds>` and `Sending <n> file
//! updates`.
//!
//! Not kept: the time-stamped set of files of `Dfind_env` (`files`, which
//! nothing reads), the inotify watch table of `Fsnotify` (`notify` keeps the
//! watches), `Dfind_lib.pid` (there is no process), the Scuba logging.

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

use notify::Watcher;
use regex::Regex;

use crate::path;
use crate::rt::ocaml_filename;
use crate::rt::ocaml_printf::sprintf_S;
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

/// `Dfind_env.t`, without `fsnotify` (the watcher) and `files` (unread).
#[derive(Default)]
pub struct DfindEnv {
    /// The set of new files (files created during an event)
    pub new_files: s_set::T,
    /// The directories (and the files they contain)
    pub dirs: BTreeMap<String, s_set::T>,
}

/// `Dfind_env.make roots`
pub fn make(_roots: &[String]) -> DfindEnv {
    DfindEnv::default()
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

/// `add_watch links env path`: the watch itself is `notify`'s (it watches the
/// roots recursively); dfind's call of `add_file` on a new watch does nothing,
/// since the path is already one of the new files.
pub fn add_watch(_links: &ISet, _env: &mut DfindEnv, _path: &str) -> Option<()> {
    Some(())
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
    /// The directory the cookies are made in (the first root), if the
    /// watcher is watching it.
    cookie_dir: Option<String>,
    /// The name of the cookies, but for their number.
    cookie_prefix: String,
    state: Mutex<State>,
    cond: Condvar,
    /// The dfind log.
    log: Mutex<std::fs::File>,
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

    /// The number of the cookie `path` is, if it is one of ours.
    fn cookie_of_path(&self, path: &str) -> Option<u64> {
        let dir = self.cookie_dir.as_ref()?;
        let name = path.strip_prefix(dir.as_str())?.strip_prefix('/')?;
        name.strip_prefix(self.cookie_prefix.as_str())?.parse().ok()
    }

    fn die(&self, why: String) {
        let mut state = lock(&self.state);
        if state.dead.is_none() {
            state.dead = Some(why);
        }
        self.cond.notify_all();
    }
}

/// `Dfind_lib.t`
pub struct T {
    shared: Arc<Shared>,
    watcher: Mutex<Option<notify::RecommendedWatcher>>,
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
/// events of `rx`.
fn run_daemon(shared: Arc<Shared>, rx: crossbeam_channel::Receiver<notify::Result<notify::Event>>) {
    let _guard = DeathGuard(shared.clone());
    let t = ocaml_unix::gettimeofday();
    let roots = shared.roots.clone();
    let mut env = make(&roots);
    for root in &roots {
        path(&mut env, root);
    }
    {
        let mut state = lock(&shared.state);
        state.ready = true;
        shared.cond.notify_all();
    }
    // `Hh_logger.log_duration "Initialization" t`
    shared.log(&format!(
        "Initialization: {:.6}",
        ocaml_unix::gettimeofday() - t
    ));
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
            if let Some(n) = shared.cookie_of_path(&p) {
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
            dirty = process_fsnotify_event(&mut env, dirty, &p, &wpath);
        }
        let mut state = lock(&shared.state);
        if !dirty.is_empty() {
            let acc = std::mem::take(&mut state.acc);
            state.acc = acc.union(dirty);
        }
        if let Some(n) = cookie {
            state.last_cookie = state.last_cookie.max(n);
            shared.cond.notify_all();
        }
    }
}

/// `Dfind_lib.init (in_fd, log_fd, log_fd) (scuba_table, roots)`: starts
/// watching `roots` and listing them; `log_fd` is the dfind log.
pub fn init(log_fd: std::fs::File, roots: &[path::T]) -> T {
    let roots: Vec<String> = roots.iter().map(path::to_string).collect();
    let (tx, rx) = crossbeam_channel::unbounded();
    let config = notify::Config::default().with_follow_symlinks(false);
    let watcher = notify::RecommendedWatcher::new(
        move |event: notify::Result<notify::Event>| {
            let _ = tx.send(event);
        },
        config,
    );
    let mut errors = vec![];
    let mut fatal = None;
    let watcher = match watcher {
        Ok(mut watcher) => {
            let mut watched = vec![];
            for root in &roots {
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
                    Err(e) => {
                        errors.push(format!("Error: could not add watch to {} [{}]\n", root, e))
                    }
                }
            }
            Some((watcher, watched))
        }
        Err(e) => {
            // `Fsnotify.init` (`Inotify.create`) raised in `Dfind_env.make`,
            // before dfind's `Ready`: the dfind process died of the uncaught
            // exception, which the runtime printed to its log.
            fatal = Some(format!("{}", e));
            errors.push(format!(
                "Fatal error: exception Fsnotify.Error({}, _)\n",
                sprintf_S(&e.to_string())
            ));
            None
        }
    };
    let cookie_dir = match (&watcher, roots.first()) {
        (Some((_, watched)), Some(root)) if watched.contains(root) => Some(root.clone()),
        _ => None,
    };
    let shared = Arc::new(Shared {
        roots,
        cookie_dir,
        cookie_prefix: format!(".hh_server_cookie.{}.", ocaml_unix::getpid()),
        state: Mutex::new(State {
            ready: false,
            acc: s_set::T::new(),
            last_cookie: 0,
            dead: None,
        }),
        cond: Condvar::new(),
        log: Mutex::new(log_fd),
    });
    for error in &errors {
        // `Dfind_maybe.handle_file_exn`: logged, and dfind carries on.
        shared.log_raw(error);
    }
    if let Some(why) = fatal {
        shared.die(why);
        return T {
            shared,
            watcher: Mutex::new(None),
            next_cookie: Mutex::new(0),
        };
    }
    let thread_shared = shared.clone();
    let name = format!("file watching process for server {}", ocaml_unix::getpid());
    std::thread::Builder::new()
        .name(name)
        .spawn(move || run_daemon(thread_shared, rx))
        .expect("could not start the file watching thread");
    T {
        shared,
        watcher: Mutex::new(watcher.map(|(w, _)| w)),
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
    if let Some(why) = &lock(&t.shared.state).dead {
        return Err(GetChangesError::Died(why.clone()));
    }
    let cookie = match &t.shared.cookie_dir {
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
        let mut env = make(&[root.clone()]);
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
