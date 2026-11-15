// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/cgroup/c_group.ml`: the memory of the cgroup v2 this
//! process is in, read from `/sys/fs/cgroup`. Where there is no cgroup v2
//! (macOS, cgroup v1) every reading is an error, and nothing is logged.

use std::path::Path;
use std::sync::Mutex;
use std::sync::OnceLock;

use crate::rt::ocaml_unix;

/// I've never seen cgroup mounted elsewhere, so it's probably fine to
/// hardcode this for now
pub const CGROUP_DIR: &str = "/sys/fs/cgroup";

/// `assert_is_using_cgroup_v2 ()` (memoized forever)
fn assert_is_using_cgroup_v2() -> Result<(), String> {
    static MEMOIZED_RESULT: OnceLock<Result<(), String>> = OnceLock::new();
    MEMOIZED_RESULT
        .get_or_init(|| assert_is_using_cgroup_v2_in(Path::new(CGROUP_DIR)))
        .clone()
}

/// [`assert_is_using_cgroup_v2`] on the cgroup directory `cgroup_dir`.
fn assert_is_using_cgroup_v2_in(cgroup_dir: &Path) -> Result<(), String> {
    if cgroup_dir.exists() {
        // /sys/fs/cgroup/memory exists for cgroup v1 but not v2. It's an easy
        // way to tell the difference between versions
        if cgroup_dir.join("memory").exists() {
            Err(format!("cgroup v1 is mounted at {}. We need v2", cgroup_dir.display()))
        } else {
            Ok(())
        }
    } else {
        Err(format!("{} doesn't exist", cgroup_dir.display()))
    }
}

/// `get_cgroup_name ()`: I don't really expect us to switch cgroups often,
/// but let's only cache for 5 seconds (`Memoize.until ~seconds:5.0`)
fn get_cgroup_name() -> Result<String, String> {
    static MEMOIZED_RESULT: Mutex<Option<(f64, Result<String, String>)>> = Mutex::new(None);
    let mut memoized = MEMOIZED_RESULT.lock().unwrap_or_else(|e| e.into_inner());
    match &*memoized {
        Some((good_until, result)) if ocaml_unix::gettimeofday() < *good_until => result.clone(),
        _ => {
            let result = crate::proc_fs::first_cgroup_for_pid(ocaml_unix::getpid());
            *memoized = Some((ocaml_unix::gettimeofday() + 5.0, result.clone()));
            result
        }
    }
}

/// `stats`
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Stats {
    /// cgroup/memory.current - the total physical memory for the cgroup
    pub memory_current: i64,
    /// cgroup/memory.swap.current - the total amount of anonymous memory
    /// paged out to swap.
    pub memory_swap_current: i64,
    /// sum of [memory_current] plus [memory_swap_current] - this is the best
    /// measure we have about total memory burden.
    pub total: i64,
    /// cgroup/memory.stat:anon - the amount of physical anonymous memory not
    /// used for shared memory
    pub anon: i64,
    /// cgroup/memory.stat:shmem - the amount of physical anonymous memory
    /// being used as shared memory
    pub shmem: i64,
    /// cgroup/memory.stat:file-shmem - the amount of physical memory which is
    /// not anonymous
    pub file: i64,
    /// the cgroup we queried, obtained dynamically based on our pid
    pub cgroup_name: String,
}

/// `int_of_string` of OCaml on a decimal number (with an optional sign;
/// OCaml also accepts `0x`, `0o`, `0b` prefixes and `_`, which cgroup files
/// do not have).
fn int_of_string_opt(s: &str) -> Option<i64> {
    let digits = s.strip_prefix(['-', '+']).unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit() || b == b'_') {
        return None;
    }
    s.replace('_', "").parse().ok()
}

/// `read_single_number_file path`: some cgroup files contain only a single
/// integer
fn read_single_number_file(path: &Path) -> Result<i64, String> {
    std::fs::read_to_string(path)
        .ok()
        .and_then(|contents| int_of_string_opt(contents.trim()))
        .ok_or_else(|| "Failed to parse memory.current".to_string())
}

/// `parse_stat stat_contents`: `(anon, file - shmem, shmem)` of a
/// `memory.stat`.
pub fn parse_stat(stat_contents: &str) -> Result<(i64, i64, i64), String> {
    let mut stats: std::collections::BTreeMap<&str, i64> = Default::default();
    for line in stat_contents.split('\n') {
        if let [key, raw_stat] = line.split(' ').collect::<Vec<_>>()[..] {
            if let Some(stat) = int_of_string_opt(raw_stat) {
                stats.insert(key, stat);
            }
        }
    }
    let get = |key: &str| {
        stats
            .get(key)
            .copied()
            .ok_or_else(|| format!("Failed to find {} in memory.stat", crate::rt::ocaml_printf::sprintf_s(key)))
    };
    let anon = get("anon")?;
    let file = get("file")?;
    let shmem = get("shmem")?;
    // In `memory.stat` the `file` stat includes `shmem`
    Ok((anon, file - shmem, shmem))
}

/// `get_stats_for_cgroup cgroup_name`, under the cgroup directory
/// `cgroup_dir`. cgroup_name starts with a /, like /my_cgroup
pub fn get_stats_for_cgroup_in(cgroup_dir: &Path, cgroup_name: &str) -> Result<Stats, String> {
    let dir = format!("{}{}", cgroup_dir.display(), cgroup_name);
    let dir = Path::new(&dir);
    let memory_current_result = read_single_number_file(&dir.join("memory.current"));
    let memory_swap_current_result = read_single_number_file(&dir.join("memory.swap.current"));
    let stat_contents_result = std::fs::read(dir.join("memory.stat"))
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .map_err(|_| "Failed to parse memory.stat".to_string());
    let memory_current = memory_current_result?;
    let memory_swap_current = memory_swap_current_result?;
    let stat_contents = stat_contents_result?;
    let (anon, file, shmem) = parse_stat(&stat_contents)?;
    let total = memory_current + memory_swap_current;
    Ok(Stats {
        total,
        memory_current,
        memory_swap_current,
        anon,
        file,
        shmem,
        cgroup_name: cgroup_name.to_string(),
    })
}

/// `get_stats ()`: reads the current PID, figures out which cgroup it's in
/// (if cgroups are available), and queries it.
pub fn get_stats() -> Result<Stats, String> {
    assert_is_using_cgroup_v2()?;
    let cgroup_name = get_cgroup_name()?;
    get_stats_for_cgroup_in(Path::new(CGROUP_DIR), &cgroup_name)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// A directory of its own for a test, removed when dropped.
    pub(crate) struct ScratchDir(std::path::PathBuf);

    impl ScratchDir {
        pub(crate) fn new(name: &str) -> Self {
            let dir = std::env::temp_dir().join(format!("hh_c_group_{}_{}", name, std::process::id()));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            ScratchDir(dir)
        }

        pub(crate) fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for ScratchDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// A cgroup v2 directory `<dir>/<name>` with these files (`None`: absent).
    pub(crate) fn write_cgroup(
        dir: &Path,
        name: &str,
        memory_current: Option<&str>,
        memory_swap_current: Option<&str>,
        memory_stat: Option<&str>,
    ) {
        let cgroup = dir.join(name.trim_start_matches('/'));
        std::fs::create_dir_all(&cgroup).unwrap();
        for (file, contents) in [
            ("memory.current", memory_current),
            ("memory.swap.current", memory_swap_current),
            ("memory.stat", memory_stat),
        ] {
            let path = cgroup.join(file);
            match contents {
                Some(contents) => std::fs::write(path, contents).unwrap(),
                None => {
                    let _ = std::fs::remove_file(path);
                }
            }
        }
    }

    const STAT: &str = "anon 1073741824\nfile 3221225472\nkernel 1\nshmem 1073741824\nfile_mapped 7\nnot a stat\n";

    #[test]
    fn stats_of_a_cgroup_v2_directory() {
        let dir = ScratchDir::new("stats");
        assert_eq!(assert_is_using_cgroup_v2_in(dir.path()), Ok(()));
        write_cgroup(dir.path(), "/ci.slice/job", Some("2147483648\n"), Some("1024\n"), Some(STAT));
        assert_eq!(
            get_stats_for_cgroup_in(dir.path(), "/ci.slice/job"),
            Ok(Stats {
                memory_current: 2147483648,
                memory_swap_current: 1024,
                total: 2147484672,
                anon: 1073741824,
                shmem: 1073741824,
                file: 2147483648,
                cgroup_name: "/ci.slice/job".to_string(),
            })
        );
    }

    #[test]
    fn errors_of_get_stats() {
        let dir = ScratchDir::new("errors");
        let missing = dir.path().join("none");
        assert_eq!(
            assert_is_using_cgroup_v2_in(&missing),
            Err(format!("{} doesn't exist", missing.display()))
        );
        std::fs::create_dir(dir.path().join("memory")).unwrap();
        assert_eq!(
            assert_is_using_cgroup_v2_in(dir.path()),
            Err(format!("cgroup v1 is mounted at {}. We need v2", dir.path().display()))
        );
        // No swap accounting: the reading fails.
        write_cgroup(dir.path(), "/a", Some("10"), None, Some(STAT));
        assert_eq!(
            get_stats_for_cgroup_in(dir.path(), "/a"),
            Err("Failed to parse memory.current".to_string())
        );
        write_cgroup(dir.path(), "/a", Some("10"), Some("x"), Some(STAT));
        assert_eq!(
            get_stats_for_cgroup_in(dir.path(), "/a"),
            Err("Failed to parse memory.current".to_string())
        );
        write_cgroup(dir.path(), "/a", Some("10"), Some("0"), None);
        assert_eq!(
            get_stats_for_cgroup_in(dir.path(), "/a"),
            Err("Failed to parse memory.stat".to_string())
        );
        write_cgroup(dir.path(), "/a", Some("10"), Some("0"), Some("anon 1\nfile 2\n"));
        assert_eq!(
            get_stats_for_cgroup_in(dir.path(), "/a"),
            Err("Failed to find \"shmem\" in memory.stat".to_string())
        );
    }

    #[test]
    fn no_cgroup_v2_on_this_machine_unless_linux() {
        if !Path::new(CGROUP_DIR).exists() {
            assert_eq!(get_stats(), Err("/sys/fs/cgroup doesn't exist".to_string()));
        }
    }
}
