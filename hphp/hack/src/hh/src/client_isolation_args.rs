// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/client_isolation_args.ml`. See `hh/PORTING.md`.

use std::io::Write;

use crate::server_isolation_types;
use crate::server_isolation_types::Mode;

/// `exception Invalid of string`
#[derive(Clone, Debug, PartialEq, Eq)]
struct Invalid(String);

fn reject(message: String) -> Result<(), Invalid> {
    Err(Invalid(message))
}

fn warn(message: &str) {
    eprint!("warning: {}\n", message);
    let _ = std::io::stderr().flush();
}

/// The share of the machine's memory that must stay available for a run to
/// continue. Growth can use all of it, and the workers are processes of their
/// own, so the server checks the machine rather than itself.
// Low enough that a run that would have finished is not stopped for a few
// GiB.
pub const DEFAULT_MIN_FREE_MEMORY_PERCENT: isize = 15;

/// The share of the machine's memory that a run may take, measured from what
/// was available when it began. The floor above stops a run when the machine is
/// low whoever is to blame; this one stops a run that is taking a lot even when
/// the machine is not yet low.
pub const DEFAULT_MAX_MEMORY_PERCENT: isize = 25;

/// `check ~max_dependents_given ~mode_flags_given options`
fn check(
    max_dependents_given: bool,
    mode_flags_given: &[String],
    options: &server_isolation_types::Options,
) -> Result<(), Invalid> {
    let server_isolation_types::Options {
        mode,
        clusters_destination: _,
        seed_framework,
        seed_list,
        seed_dir,
        max_dependents,
        max_cluster_size,
        batch_size,
        min_free_memory_percent,
        max_memory_percent,
        allow_long_run: _,
        max_seeds,
        seed_offset,
    } = options;
    let grow = server_isolation_types::is_grow(mode);
    let movable = server_isolation_types::is_check_movability(mode);
    if let Some(n) = max_seeds {
        if *n < 1 {
            reject(format!(
                "--isolation-max-seeds must be at least 1, got {}",
                n
            ))?
        }
    }
    if *min_free_memory_percent < 0 || *min_free_memory_percent > 100 {
        reject(format!(
            "--isolation-min-free-memory is a percentage, from 0 to 100, got {}",
            min_free_memory_percent
        ))?
    }
    if *max_memory_percent < 0 || *max_memory_percent > 100 {
        reject(format!(
            "--isolation-max-memory is a percentage, from 0 to 100, got {}",
            max_memory_percent
        ))?
    }
    if let Some(n) = max_cluster_size {
        if *n < 2 {
            // A cap of 1 would retire every cluster before it absorbed anything.
            reject(format!(
                "--isolation-max-cluster-size must be at least 2, got {}",
                n
            ))?
        }
    }
    // One cluster per batch still works, it is just the slowest way to do it:
    // the batch exists to pool candidates into a single parallel indexing call,
    // and a batch of one leaves the worker pool idle.
    if *batch_size < 1 {
        reject(format!(
            "--isolation-batch-size must be at least 1, got {}",
            batch_size
        ))?
    }
    if *seed_offset < 0 {
        reject(format!(
            "--isolation-seed-offset cannot be negative, got {}",
            seed_offset
        ))?
    }
    // Growth needs a closure for the seed before it has a cluster, so a reach
    // under 1 admits nothing and the run silently reports none.
    if *max_dependents < 1 {
        reject(format!(
            "--isolation-max-dependents must be at least 1, got {}",
            max_dependents
        ))?
    }
    // Picking two says the caller means something the run cannot do, and
    // preferring one silently answers the wrong question.
    let seed_sources = [
        ("--isolation-seed-framework", seed_framework),
        ("--isolation-seed-list", seed_list),
        ("--isolation-seed-dir", seed_dir),
    ];
    let seed_sources_given: Vec<&str> = seed_sources
        .iter()
        .filter_map(|(flag, value)| value.as_ref().map(|_| *flag))
        .collect();
    if seed_sources_given.len() > 1 {
        reject(format!(
            "{} each name where to start; pass one",
            seed_sources_given.join(" and ")
        ))?
    }
    if mode_flags_given.len() > 1 {
        reject(format!(
            "{} each answer a different question; pass one",
            mode_flags_given.join(" and ")
        ))?
    }
    // A move is of one directory, which a list of files or a framework is not,
    // and it is said before the movability rules below because it is the flag
    // the caller spelled.
    match mode {
        Mode::MoveTo(target) if target.trim().is_empty() => {
            reject("--isolation-move-to needs the directory to move into".to_string())?
        }
        Mode::MoveTo(_) if seed_dir.is_none() => reject(
            "--isolation-move-to moves the directory named by --isolation-seed-dir; a seed list or a framework has no directory to move"
                .to_string(),
        )?,
        Mode::MoveTo(_) | Mode::Measure | Mode::Grow | Mode::CheckMovability => {}
    }
    // Movability asks about one named set of files. Everything that would
    // change which files that is, or what happens to them afterwards, asks a
    // different question — and answering a different question from the one the
    // caller spelled is worse than refusing.
    if movable {
        // The whole-repository scan collects the files nothing references, which
        // is already the answer to a different question: asking whether they can
        // collectively move would always say yes and mean nothing.
        if seed_dir.is_none() && seed_list.is_none() && seed_framework.is_none() {
            reject(
                "--isolation-movable asks about a named set of files; name it with --isolation-seed-dir, --isolation-seed-list or --isolation-seed-framework"
                    .to_string(),
            )?
        }
        // A window would answer for part of the directory, and a part of a package
        // is not a package: the files left out reference in, so the answer would
        // be no for a reason the caller created.
        if max_seeds.is_some() || *seed_offset > 0 {
            reject(
                "--isolation-max-seeds and --isolation-seed-offset take a window of the starting files, and --isolation-movable asks about all of them"
                    .to_string(),
            )?
        }
    }
    // Growth clamps the reach to the cap, so a larger one is not refused, it is
    // silently unused. Only worth saying when the caller picked the reach: the
    // default sits above most caps, and naming a flag they never passed reads as
    // an accusation rather than a hint.
    match max_cluster_size {
        Some(cap) if max_dependents_given && grow && max_dependents > cap => warn(&format!(
            "--isolation-max-dependents {} is clamped to the cluster size cap of {} for growth; a closure larger than the cluster can never be absorbed",
            max_dependents, cap
        )),
        _ => {}
    }
    // Legal, and almost always a mistake: it skips n and then runs to the end of
    // the population, which for a large family is tens of thousands.
    if *seed_offset > 0 && max_seeds.is_none() {
        warn(&format!(
            "--isolation-seed-offset {} without --isolation-max-seeds runs to the end of the seed list, not a window of it",
            seed_offset
        ))
    }
    Ok(())
}

/// `Error` on a combination of `--isolation-*` flags the run cannot honour.
/// Combinations it can honour but that almost certainly do not mean what the
/// caller intended are warned about on stderr, since they do not stop the run.
///
/// `max_dependents_given` tells the two apart for that bound: it reaches here
/// resolved to its default, and warning about a value the caller never chose
/// would report their own default back at them.
///
/// `mode_flags_given` names the flags that each select a mode: the options
/// carry one mode, so two flags given together could not be seen in them.
pub fn validate(
    max_dependents_given: bool,
    mode_flags_given: &[String],
    options: &server_isolation_types::Options,
) -> Result<(), String> {
    check(max_dependents_given, mode_flags_given, options).map_err(|Invalid(message)| message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::server_isolation_types::ClustersDestination;
    use crate::server_isolation_types::Options;

    fn options() -> Options {
        Options {
            mode: Mode::Measure,
            clusters_destination: ClustersDestination::Dropped,
            seed_framework: None,
            seed_list: None,
            seed_dir: None,
            max_dependents: 50,
            max_cluster_size: None,
            batch_size: 1,
            min_free_memory_percent: DEFAULT_MIN_FREE_MEMORY_PERCENT,
            max_memory_percent: DEFAULT_MAX_MEMORY_PERCENT,
            allow_long_run: false,
            max_seeds: None,
            seed_offset: 0,
        }
    }

    fn err(o: Options) -> String {
        validate(false, &[], &o).unwrap_err()
    }

    #[test]
    fn accepts_defaults() {
        assert_eq!(validate(false, &[], &options()), Ok(()));
    }

    #[test]
    fn bounds() {
        assert_eq!(
            err(Options {
                max_seeds: Some(0),
                ..options()
            }),
            "--isolation-max-seeds must be at least 1, got 0"
        );
        assert_eq!(
            err(Options {
                min_free_memory_percent: 101,
                ..options()
            }),
            "--isolation-min-free-memory is a percentage, from 0 to 100, got 101"
        );
        assert_eq!(
            err(Options {
                max_memory_percent: -1,
                ..options()
            }),
            "--isolation-max-memory is a percentage, from 0 to 100, got -1"
        );
        assert_eq!(
            err(Options {
                max_cluster_size: Some(1),
                ..options()
            }),
            "--isolation-max-cluster-size must be at least 2, got 1"
        );
        assert_eq!(
            err(Options {
                batch_size: 0,
                ..options()
            }),
            "--isolation-batch-size must be at least 1, got 0"
        );
        assert_eq!(
            err(Options {
                seed_offset: -2,
                ..options()
            }),
            "--isolation-seed-offset cannot be negative, got -2"
        );
        assert_eq!(
            err(Options {
                max_dependents: 0,
                ..options()
            }),
            "--isolation-max-dependents must be at least 1, got 0"
        );
    }

    #[test]
    fn one_seed_source_and_one_mode() {
        assert_eq!(
            err(Options {
                seed_list: Some("l".to_string()),
                seed_dir: Some("d".to_string()),
                ..options()
            }),
            "--isolation-seed-list and --isolation-seed-dir each name where to start; pass one"
        );
        assert_eq!(
            validate(
                false,
                &["--isolation-grow".to_string(), "--isolation-movable".to_string()],
                &options()
            ),
            Err(
                "--isolation-grow and --isolation-movable each answer a different question; pass one"
                    .to_string()
            )
        );
    }

    #[test]
    fn movability() {
        assert_eq!(
            err(Options {
                mode: Mode::MoveTo(" ".to_string()),
                ..options()
            }),
            "--isolation-move-to needs the directory to move into"
        );
        assert_eq!(
            err(Options {
                mode: Mode::MoveTo("x".to_string()),
                seed_list: Some("l".to_string()),
                ..options()
            }),
            "--isolation-move-to moves the directory named by --isolation-seed-dir; a seed list or a framework has no directory to move"
        );
        assert_eq!(
            err(Options {
                mode: Mode::CheckMovability,
                ..options()
            }),
            "--isolation-movable asks about a named set of files; name it with --isolation-seed-dir, --isolation-seed-list or --isolation-seed-framework"
        );
        assert_eq!(
            err(Options {
                mode: Mode::CheckMovability,
                seed_dir: Some("d".to_string()),
                max_seeds: Some(3),
                ..options()
            }),
            "--isolation-max-seeds and --isolation-seed-offset take a window of the starting files, and --isolation-movable asks about all of them"
        );
        assert_eq!(
            validate(
                false,
                &[],
                &Options {
                    mode: Mode::MoveTo("x".to_string()),
                    seed_dir: Some("d".to_string()),
                    ..options()
                }
            ),
            Ok(())
        );
    }
}
