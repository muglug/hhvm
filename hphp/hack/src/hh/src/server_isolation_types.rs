// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/server_isolation_types.ml`. See `hh/PORTING.md`.
//!
//! [`Options`] is the argument of `Server_command_types.FIND_ISOLATABLE_CLUSTERS`
//! and [`Result`] its result, so both cross the socket and are `serde`.

use serde::Deserialize;
use serde::Serialize;

/// A group of files that collectively form a leaf: they reference the monorepo,
/// but nothing outside the group references them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cluster {
    pub files: Vec<String>,
    /// Longest directory prefix shared by every file in the cluster.
    pub common_directory: String,
    /// Whether a size cap refused this cluster a file it would otherwise have
    /// taken, leaving it a prefix of a package rather than a package.
    pub truncated: bool,
}

/// A file outside a set of files that references into it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Blocker {
    pub file: String,
    /// The files of the set that it references, which is what it blocks.
    pub references: Vec<String>,
}

/// Whether a named set of files can move as it stands, judged from the
/// dependency graph alone. [Blocked] lists every file outside the set that
/// references into it. [Movable] does not promise that a typecheck of the
/// moved files will pass.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Movability {
    Movable,
    Blocked(Vec<Blocker>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Result {
    pub refused: Option<String>,
    /// The answer to [Check_movability]; [None] in the other modes.
    pub movability: Option<Movability>,
    /// Whether these were grown, or are each the smallest isolatable set
    /// around a starting file.
    pub grown: bool,
    pub total_seeds: isize,
    pub total_isolatable_files: isize,
    pub total_clusters: isize,
    /// A count, because the clusters themselves never come back here.
    pub total_truncated: isize,
    /// Starting files left out of the clusters because no set could be found
    /// for them: what depends on them is over the limit, or they declare
    /// nothing. Only the default mode counts them.
    pub total_refused: isize,
    pub largest_cluster: isize,
}

/// Where a run's clusters end up. They never travel in the result: a run can
/// produce hundreds of thousands, so they go to a file as they are found and
/// the result carries only the summary.
///
/// Which file depends on what the caller asked for: [--isolation-output] names
/// one, and for [--json] without it the client makes a temporary file, prints
/// it and removes it — so reaching stdout costs no more memory than reaching a
/// file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ClustersDestination {
    /// Written here as they are produced, one JSON object per line.
    ToFile(String),
    /// Counted in the summary and forgotten.
    Dropped,
}

/// What a run does with its starting files.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Mode {
    /// Report the smallest isolatable set around each starting file: its
    /// closure under reverse dependencies.
    Measure,
    /// Grow a bigger cluster around each starting file.
    Grow,
    /// Ask whether the starting files, taken together, can move as they
    /// stand, naming what blocks it if not.
    CheckMovability,
    /// Move the seed directory into this directory, under its own name, if it
    /// can move and the move introduces no errors. The client does the
    /// moving, and asks the server the [Check_movability] question.
    MoveTo(String),
}

/// Whether the mode grows clusters.
pub fn is_grow(mode: &Mode) -> bool {
    match mode {
        Mode::Grow => true,
        Mode::Measure | Mode::CheckMovability | Mode::MoveTo(_) => false,
    }
}

/// Whether the mode asks if the starting files can move.
pub fn is_check_movability(mode: &Mode) -> bool {
    match mode {
        Mode::CheckMovability | Mode::MoveTo(_) => true,
        Mode::Measure | Mode::Grow => false,
    }
}

/// Where to start growing clusters, and how far to take them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Options {
    pub mode: Mode,
    pub clusters_destination: ClustersDestination,
    /// Start from every subclass of this class.
    pub seed_framework: Option<String>,
    /// Start from the repo-relative paths in this file, one per line.
    pub seed_list: Option<String>,
    /// Start from every Hack file under this repo-relative directory.
    pub seed_dir: Option<String>,
    /// The most files that may depend on a candidate for it to be absorbed
    /// along with them — how far the closure rule may reach. At least 1.
    pub max_dependents: isize,
    /// Stop growing a cluster at this many files and never report a larger
    /// one, marking it [truncated]. [None] grows to a fixed point.
    pub max_cluster_size: Option<isize>,
    /// How many clusters to grow at once. They are all held in memory until
    /// the batch ends, so this sets the run's peak memory. It also changes
    /// what comes back: clusters in one batch are grown against the same
    /// [claimed] snapshot, so a larger batch drops more of them for
    /// overlapping. At least 1.
    pub batch_size: isize,
    /// Stop the run when less than this percentage of the machine's memory is
    /// available, whoever is using the rest. 0 turns the check off.
    pub min_free_memory_percent: isize,
    /// Stop the run when the memory available on the machine has fallen by
    /// more than this percentage of its total since the run began. 0 turns
    /// the check off.
    pub max_memory_percent: isize,
    /// Run even when the seed count says this will take hours. Without it a
    /// run that long is refused before it starts.
    pub allow_long_run: bool,
    /// [None] means every seed.
    pub max_seeds: Option<isize>,
    /// Skip this many seeds before applying [max_seeds], so a caller can walk
    /// the seed list in chunks across separate queries.
    pub seed_offset: isize,
}
