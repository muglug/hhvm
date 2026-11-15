// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The build script of the `hh` crate: it embeds the build identifiers that
//! the OCaml build generated, as environment variables of the compilation
//! (`env!`), read by `crate::build_id` and `crate::build_banner`:
//!
//! - `HH_BUILD_REVISION`, `HH_BUILD_COMMIT_TIME`: `BuildInfo_kRevision` and
//!   `BuildInfo_kRevisionCommitTimeUnix`, as `hphp/hack/scripts/gen_build_id.ml`
//!   computes them (`git rev-parse HEAD`, else `hg id -i`, else `""`; `git log
//!   -1 --pretty=tformat:%ct`, else the `hg` date, else `0`). The build mode
//!   and the package name are `""` there ("not implemented", "always empty"),
//!   so they are not passed.
//! - `HH_BUILD_TIMESTAMP`: the time of the build (`utils/core/config/dune`:
//!   `date +%s`), which `get_build_id.c` uses when the commit time is 0.
//! - `HH_BUILD_BANNER`, only when it can be computed: what
//!   `version/build_banner/dune` gave `build_banner_stubs.c`, i.e. the output
//!   of `hphp/tools/generate-build-id.sh IGNORED IGNORED hackc hphp/hack/src`
//!   (`hackc-<sha1 of the diff of hphp/hack/src and of its last commit>`)
//!   followed by `-` and `HHVM_VERSION_C_STRING_LITERALS` of
//!   `hphp/runtime/version.h`. When it cannot (no bash, openssl or version
//!   header), the OCaml build failed; here the banner is absent (the `None`
//!   of `Build_banner.banner`) and a warning says why.
//!
//! dune ran the banner rule on every build (`(deps (universe))`). Cargo can
//! only do that by recompiling the crate every time, so this script runs again
//! when the commit changes (the git `HEAD` and the ref it points to), or when
//! this script, the version header or the build-id script change: the diff
//! hashed into the banner is the one of that run.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

/// `read_process_output` of `hphp/hack/scripts/utils.ml`: the first line of
/// the output of a command that exits with 0, `None` when it is not found or
/// fails. (OCaml reads stdout and stderr from one pipe; here stdout comes
/// first.)
fn read_process_output(dir: &Path, name: &str, args: &[&str]) -> Option<String> {
    let output = Command::new(name)
        .args(args)
        .current_dir(dir)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let mut all = output.stdout;
    all.extend_from_slice(&output.stderr);
    let all = String::from_utf8(all).ok()?;
    all.lines().next().map(|line| line.to_string())
}

/// `BuildInfo_kRevision` (`gen_build_id.ml`).
fn revision(dir: &Path) -> String {
    read_process_output(dir, "git", &["rev-parse", "HEAD"])
        .or_else(|| read_process_output(dir, "hg", &["id", "-i"]))
        .unwrap_or_default()
}

/// `BuildInfo_kRevisionCommitTimeUnix` (`gen_build_id.ml`).
fn commit_time(dir: &Path) -> String {
    let time = read_process_output(dir, "git", &["log", "-1", "--pretty=tformat:%ct"])
        .or_else(|| {
            let raw = read_process_output(dir, "hg", &["log", "-r", ".", "-T", "{date|hgdate}\\n"])?;
            Some(match raw.find(' ') {
                Some(i) => raw[..i].to_string(),
                None => "0".to_string(),
            })
        })
        .unwrap_or_else(|| "0".to_string());
    // The OCaml build pasted it into C as `<time>ul`: anything other than
    // digits did not compile.
    if !time.is_empty() && time.bytes().all(|c| c.is_ascii_digit()) {
        time
    } else {
        println!("cargo:warning=hh: commit time {time:?} is not a number; using 0");
        "0".to_string()
    }
}

/// `HHVM_VERSION_C_STRING_LITERALS` of `hphp/runtime/version.h`:
/// `MAJOR.MINOR.PATCH` followed by the suffix.
fn hhvm_version(version_h: &Path) -> Option<String> {
    let text = std::fs::read_to_string(version_h).ok()?;
    let define = |name: &str| -> Option<String> {
        text.lines().find_map(|line| {
            let mut words = line.trim_start_matches(['#', ' ', '\t']).split_whitespace();
            if words.next()? != "define" || words.next()? != name {
                return None;
            }
            Some(words.collect::<Vec<_>>().join(" "))
        })
    };
    let major = define("HHVM_VERSION_MAJOR")?;
    let minor = define("HHVM_VERSION_MINOR")?;
    let patch = define("HHVM_VERSION_PATCH")?;
    let suffix = define("HHVM_VERSION_SUFFIX")?;
    let suffix = suffix.strip_prefix('"')?.strip_suffix('"')?;
    Some(format!("{major}.{minor}.{patch}{suffix}"))
}

/// `HH_BUILD_BANNER "-" HHVM_VERSION_C_STRING_LITERALS`, or why it is absent.
fn banner(repo_root: &Path, out_dir: &Path) -> Result<String, String> {
    let script = repo_root.join("hphp/tools/generate-build-id.sh");
    let status = Command::new("bash")
        .arg(&script)
        .args(["IGNORED", "IGNORED", "hackc", "hphp/hack/src"])
        .env("INSTALL_DIR", out_dir)
        .env("FBCODE_DIR", repo_root)
        .current_dir(repo_root)
        .status()
        .map_err(|e| format!("cannot run {}: {e}", script.display()))?;
    if !status.success() {
        return Err(format!("{} failed: {status}", script.display()));
    }
    let build_id = std::fs::read_to_string(out_dir.join("build-id"))
        .map_err(|e| format!("cannot read build-id: {e}"))?;
    let version = hhvm_version(&repo_root.join("hphp/runtime/version.h"))
        .ok_or_else(|| "cannot read the version in hphp/runtime/version.h".to_string())?;
    Ok(format!("{build_id}-{version}"))
}

/// The files whose change means another commit: `HEAD`, the ref it points
/// to, and the packed refs. Only those that exist (cargo runs the script
/// every time for a path that does not).
fn git_files(dir: &Path) -> Vec<PathBuf> {
    let git_path = |p: &str| -> Option<PathBuf> {
        let path = read_process_output(dir, "git", &["rev-parse", "--git-path", p])?;
        Some(dir.join(path))
    };
    let mut files = vec![];
    files.extend(git_path("HEAD"));
    if let Some(r) = read_process_output(dir, "git", &["symbolic-ref", "-q", "HEAD"]) {
        files.extend(git_path(&r));
    }
    files.extend(git_path("packed-refs"));
    files.into_iter().filter(|f| f.exists()).collect()
}

fn main() {
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    // hphp/hack/src/hh -> the root of the repository.
    let repo_root = manifest_dir.join("../../../..");
    let repo_root = repo_root.canonicalize().unwrap_or(repo_root);

    println!("cargo:rerun-if-changed=build.rs");
    for f in [
        repo_root.join("hphp/runtime/version.h"),
        repo_root.join("hphp/tools/generate-build-id.sh"),
    ] {
        if f.exists() {
            println!("cargo:rerun-if-changed={}", f.display());
        }
    }
    for f in git_files(&manifest_dir) {
        println!("cargo:rerun-if-changed={}", f.display());
    }

    let rev = revision(&manifest_dir);
    let time = commit_time(&manifest_dir);
    let build_timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    println!("cargo:rustc-env=HH_BUILD_REVISION={rev}");
    println!("cargo:rustc-env=HH_BUILD_COMMIT_TIME={time}");
    println!("cargo:rustc-env=HH_BUILD_TIMESTAMP={build_timestamp}");
    match banner(&repo_root, &out_dir) {
        Ok(banner) => println!("cargo:rustc-env=HH_BUILD_BANNER={banner}"),
        Err(why) => println!("cargo:warning=hh: no build banner ({why})"),
    }
}
