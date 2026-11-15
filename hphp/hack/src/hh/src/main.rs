// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: `hh`, the Hack typechecker's own command line (`hh
//! check` for a whole root, `hh single` and `hh single-complete` for
//! `hh_single_type_check.ml` and `hh_single_complete.ml`).
//!
//! ```text
//! hh check [--threads N] [--stats] [--quiet] [--config KEY=VALUE]...
//!          [--save-64bit DIR [--save-human-readable-64bit-dep-map DIR]] ROOT
//!     Check every Hack file under ROOT (`--save-64bit`: and write the
//!     dependency edges found, as `hh_server --check --save-64bit` does).
//!
//! hh single [FLAGS] FILE
//!     Check one file (possibly a multifile) on its own, against the hhi
//!     files. The output is that of `hh_single_type_check`, which is what the
//!     test suites under hphp/hack/test compare against.
//! ```

use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use anyhow::Context;
use anyhow::Result;
use anyhow::bail;
use hh::check;
use hh::diagnostics_helpers;
use oxidized::diagnostics::Diagnostic;
#[cfg(all(test, feature = "port"))]
use oxidized::typechecker_options::TypecheckerOptions;

// The OCaml allocates on its own GC heap. Here mimalloc replaces the system
// allocator, because the checker allocates from many threads at once, which
// the system allocator handles poorly (on macOS in particular).
#[cfg(not(feature = "dhat-heap"))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(feature = "dhat-heap")]
#[global_allocator]
static GLOBAL: dhat::Alloc = dhat::Alloc;

// `hh single`: `hh_single_type_check.ml`.
mod hh_single_cli;

fn main() -> ExitCode {
    // A worker process (of `hh check`) runs its loop on the main thread.
    #[cfg(feature = "server")]
    hh::worker::run_if_worker();
    // Run on a thread with a large stack, and make rayon's threads as large.
    hh::check::run_on_large_stack("hh", real_main).unwrap_or_else(|_| ExitCode::from(101))
}

fn real_main() -> ExitCode {
    #[cfg(feature = "dhat-heap")]
    let _profiler = dhat::Profiler::new_heap();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("check") => check_root(&args[1..]),
        Some("single") => hh_single_cli::check_single(&args[1..]),
        // `hh_single_complete`.
        #[cfg(feature = "port")]
        Some("single-complete") => hh_single_cli::complete_single(&args[1..]),
        _ => {
            eprintln!("usage: hh check [--threads N] [--stats] [--quiet] ROOT");
            eprintln!("       hh single [FLAGS] FILE");
            return ExitCode::from(2);
        }
    };
    match result {
        Ok(code) => code,
        Err(err) => {
            eprintln!("hh: {:#}", err);
            ExitCode::from(2)
        }
    }
}

/// The `--config KEY=VALUE` overrides of `hh check`, as
/// `Server_args.parse_options` makes them: `String_utils.split2_exn '='` of
/// each, put before the earlier ones.
fn cli_config_overrides(overrides: &[String]) -> Result<Vec<(String, String)>> {
    let mut cli_config_overrides = vec![];
    for kv in overrides {
        #[cfg(feature = "port")]
        let split = hh::string_utils::split2('=', kv);
        // (Without the port, as the `hh_config` crate splits them.)
        #[cfg(not(feature = "port"))]
        let split = kv.split_once('=').map(|(k, v)| (k.to_string(), v.to_string()));
        let kv = split.with_context(|| format!("--config {kv}: String_utils.Incorrect_format"))?;
        cli_config_overrides.insert(0, kv);
    }
    Ok(cli_config_overrides)
}

fn print_diagnostics(diagnostics: &[Diagnostic]) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    if diagnostics.is_empty() {
        let _ = writeln!(out, "No errors");
    }
    for d in diagnostics {
        let _ = write!(out, "{}", diagnostics_helpers::to_plain_string(d));
    }
}

fn check_root(args: &[String]) -> Result<ExitCode> {
    let mut root = None;
    let mut overrides = vec![];
    let mut threads = None;
    let mut stats_wanted = false;
    let mut quiet = false;
    let mut only: Option<PathBuf> = None;
    let mut save_64bit: Option<String> = None;
    let mut save_human_readable_64bit_dep_map: Option<String> = None;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--threads" => {
                threads = Some(
                    it.next()
                        .context("--threads needs a number")?
                        .parse::<usize>()?,
                )
            }
            "--config" => overrides.push(it.next().context("--config needs key=value")?.clone()),
            "--stats" => stats_wanted = true,
            // Check only the files listed (one root-relative path per line) in
            // this file; every file is still declared.
            "--only" => only = Some(PathBuf::from(it.next().context("--only needs a file")?)),
            "--quiet" => quiet = true,
            // As `hh_server --check`: write the dependency edges found to
            // `new-edges-worker-<n>.bin` files in this directory, and their
            // names to `human-readable-dep-map-<n>.txt` files in the other.
            "--save-64bit" => {
                save_64bit = Some(it.next().context("--save-64bit needs a directory")?.clone())
            }
            "--save-human-readable-64bit-dep-map" => {
                save_human_readable_64bit_dep_map = Some(
                    it.next()
                        .context("--save-human-readable-64bit-dep-map needs a directory")?
                        .clone(),
                )
            }
            flag if flag.starts_with("--") => bail!("unknown flag {}", flag),
            path => root = Some(PathBuf::from(path)),
        }
    }
    let root = root.context("no root given")?;
    let cli_config_overrides = cli_config_overrides(&overrides)?;
    check::build_thread_pool(threads)?;
    // As `hh_server --check`, whose code this shares: the threads check (the
    // worker processes, as many as the threads, only with `HH_RUST_WORKERS=1`;
    // see `check::start_workers`).
    #[cfg(feature = "server")]
    {
        let canonical = root.canonicalize()?;
        let config = check::sharedmem_config(&canonical, &cli_config_overrides)?;
        let trace = save_64bit.is_some() || std::env::var_os("HH_RECORD_EDGES_TO").is_some();
        let n = threads.unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get()));
        check::start_workers(&canonical, Path::new("/hhi"), n, trace, &config)?;
    }

    #[cfg_attr(not(feature = "port"), allow(unused_mut))]
    let mut root = check::discover_root(&root, &cli_config_overrides)?;
    #[cfg(feature = "port")]
    {
        root.ctx.deps_mode = check::get_deps_mode(
            save_64bit.as_deref(),
            save_human_readable_64bit_dep_map.as_deref(),
        );
    }
    #[cfg(not(feature = "port"))]
    if save_64bit.is_some() || save_human_readable_64bit_dep_map.is_some() {
        bail!("--save-64bit needs the typechecker (the `port` feature)");
    }
    let (hhi_count, discovery_time, start) = (root.hhi_count, root.discovery_time, root.start);
    // `HH_LIST_FILES=1`: print the files found, in order (to compare walkers).
    if std::env::var_os("HH_LIST_FILES").is_some() {
        for path in &root.paths[hhi_count..] {
            println!("{}", path.path().display());
        }
        return Ok(ExitCode::SUCCESS);
    }
    let checked = check::check_root(root, only.as_deref(), Path::new("/hhi"))?;
    let stats = checked.stats.clone();
    let diagnostics = checked.sorted_diagnostics();

    if !quiet {
        print_diagnostics(&diagnostics);
    }
    if stats_wanted {
        eprintln!(
            "files: {} ({:.1} MB), hhi files: {}",
            stats.files,
            stats.bytes as f64 / 1e6,
            hhi_count
        );
        eprintln!("discovery: {:>8.3}s", discovery_time.as_secs_f64());
        eprintln!("decl:      {:>8.3}s", stats.decl_time.as_secs_f64());
        eprintln!("check:     {:>8.3}s", stats.check_time.as_secs_f64());
        eprintln!("total:     {:>8.3}s", start.elapsed().as_secs_f64());
        eprintln!("errors: {}", diagnostics.len());
    }
    Ok(if diagnostics.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    })
}

#[cfg(all(test, feature = "port"))]
mod tests {
    use super::*;

    /// A fresh directory under the system's temporary directory, resolved
    /// (on macOS the temporary directory is behind a symbolic link).
    fn temp_root(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("hh_main_{}_{}", name, std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        dir.canonicalize().unwrap()
    }

    fn strings(l: &[&str]) -> Vec<String> {
        l.iter().map(|s| s.to_string()).collect()
    }

    /// The options of `hh check --config O... ROOT`.
    fn check_options(
        root: &Path,
        overrides: &[String],
    ) -> Result<(TypecheckerOptions, Vec<String>)> {
        check::check_options(root, &cli_config_overrides(overrides)?)
    }

    /// `hh check`: the keys of `.hhconfig` that the `hh_config` crate does
    /// not read reach the options, `--config` overrides them (the first
    /// `--config` of a key wins, as in `hh_server`), and the keys of hh.conf
    /// given with `--config` reach them through the local config. (One test:
    /// the root of `Relative_path` is process-wide.)
    #[test]
    fn check_options_read_hhconfig_and_overrides() {
        let root = temp_root("check_options");
        std::fs::write(
            root.join(".hhconfig"),
            r#"disallow_discarded_nullable_awaitables = true
meth_caller_only_public_visibility = false
tco_global_access_check_enabled = true
disable_physical_equality = true
typecheck_if_name_matches_regexp = ^foo
keep_user_attributes = true
auto_namespace_map = {"Vec": "HH\\Lib\\Vec"}
ignored_paths = ["^vendor/", "^gen/"]
"#,
        )
        .unwrap();
        let (tco, ignored) = check_options(&root, &[]).unwrap();
        assert!(tco.tco_disallow_discarded_nullable_awaitables);
        assert!(!tco.tco_meth_caller_only_public_visibility);
        // Not a key of `.hhconfig` for the OCaml (`hh_config` reads it):
        // the check is enabled by `enable_global_access_check` of hh.conf.
        assert!(!tco.tco_global_access_check_enabled);
        assert!(tco.tco_disable_physical_equality);
        assert_eq!(
            tco.tco_typecheck_if_name_matches_regexp.as_deref(),
            Some("^foo")
        );
        assert!(tco.po.keep_user_attributes);
        assert_eq!(
            tco.po.auto_namespace_map,
            vec![("Vec".to_string(), "HH\\Lib\\Vec".to_string())]
        );
        assert_eq!(ignored, strings(&["^vendor/", "^gen/"]));
        // What hh.conf decides, without an hh.conf (`Server_local_config_load
        // .default`): no unstable features, the warnings on.
        assert!(!tco.po.allow_unstable_features);
        assert_eq!(
            tco.hack_warnings,
            oxidized::global_options::NoneOrAllExcept::AllExcept(vec![])
        );
        assert!(!tco.tco_skip_tast_checks);

        let (tco, _) = check_options(
            &root,
            &strings(&[
                "disable_physical_equality=false",
                "disable_physical_equality=true",
                "implicit_inherit_sdt=true",
                // Keys of hh.conf.
                "skip_tast_checks=true",
                "enable_global_access_check=true",
            ]),
        )
        .unwrap();
        assert!(!tco.tco_disable_physical_equality);
        assert!(tco.tco_implicit_inherit_sdt);
        assert!(tco.tco_skip_tast_checks);
        assert!(tco.tco_global_access_check_enabled);
        assert!(tco.tco_disallow_discarded_nullable_awaitables);
        // `String_utils.split2_exn '='`.
        assert!(check_options(&root, &strings(&["a=b=c"])).is_err());
        assert!(check_options(&root, &strings(&["a"])).is_err());

        // An empty `.hhconfig` gives the defaults.
        std::fs::write(root.join(".hhconfig"), "").unwrap();
        let (tco, ignored) = check_options(&root, &[]).unwrap();
        assert!(!tco.tco_disallow_discarded_nullable_awaitables);
        assert!(tco.tco_meth_caller_only_public_visibility);
        assert!(ignored.is_empty());
        // Without one, there is no root.
        std::fs::remove_file(root.join(".hhconfig")).unwrap();
        assert!(check_options(&root, &[]).is_err());
        std::fs::remove_dir_all(&root).unwrap();
    }
}
