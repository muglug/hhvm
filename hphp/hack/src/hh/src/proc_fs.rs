// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

//! Port of `utils/procfs/proc_fs.ml`: the functions that the ported modules
//! need so far (the cgroup of a process; `status_for_pid` and
//! `telemetry_for_pid` have no caller yet).

use std::sync::OnceLock;

use crate::sys_utils;

/// `read_proc_file filename pid`: the contents of `/proc/<pid>/<filename>`,
/// or the exception that reading it raised, as a string.
fn read_proc_file(filename: &str, pid: isize) -> Result<String, String> {
    let file = format!("/proc/{}/{}", pid, filename);
    match sys_utils::cat(&file) {
        Ok(bytes) => Ok(String::from_utf8_lossy(&bytes).into_owned()),
        // (`Exception.to_string` of the `Sys_error`.)
        Err(e) => Err(e.to_string()),
    }
}

/// `parse_cgroup raw_cgroup_contents`: the cgroup of the first line of a
/// `/proc/<pid>/cgroup` file (`<id>:<controllers>:<cgroup>`).
pub fn parse_cgroup(raw_cgroup_contents: &str) -> Result<String, String> {
    // (`String.split ~on:'\n'` never gives an empty list.)
    let first_line = raw_cgroup_contents.split('\n').next().unwrap_or("");
    match first_line.split(':').collect::<Vec<_>>()[..] {
        [_id, _controllers, cgroup] => Ok(cgroup.to_string()),
        _ => Err("First line of  /proc/<PID>/cgroup file was not correctly formatted".to_string()),
    }
}

/// `asset_procfs_supported ()` (memoized)
fn asset_procfs_supported() -> Result<(), String> {
    static MEMOIZED_RESULT: OnceLock<Result<(), String>> = OnceLock::new();
    MEMOIZED_RESULT
        .get_or_init(|| {
            if std::path::Path::new("/proc").exists() {
                Ok(())
            } else {
                Err("Proc filesystem not supported".to_string())
            }
        })
        .clone()
}

/// `first_cgroup_for_pid pid`. In cgroup v1 a pid can be in multiple
/// cgroups. In cgroup v2 it will only be in a single cgroup.
pub fn first_cgroup_for_pid(pid: isize) -> Result<String, String> {
    asset_procfs_supported()?;
    parse_cgroup(&read_proc_file("cgroup", pid)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_cgroup_takes_the_first_line() {
        assert_eq!(parse_cgroup("0::/user.slice/a.scope\n"), Ok("/user.slice/a.scope".to_string()));
        assert_eq!(
            parse_cgroup("12:memory:/docker/abc\n11:cpu:/docker/abc\n"),
            Ok("/docker/abc".to_string())
        );
        let err = Err("First line of  /proc/<PID>/cgroup file was not correctly formatted".to_string());
        assert_eq!(parse_cgroup(""), err);
        assert_eq!(parse_cgroup("0::/a:b\n"), err);
    }
}
