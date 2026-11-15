// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/hg/hg.ml` (`Hg_actual`), the queries the saved-state
//! loader makes (`current_mergebase_hg_rev`, `get_closest_global_ancestor`,
//! `get_hg_revision_time`). See `hh/PORTING.md`.
//!
//! `Future.t` of a process (`Future_process.make`) is
//! the process run to its end when the future is got: [`Future`] is its
//! result. Starting the process (`Process.exec`, `Unix.create_process`)
//! raises at once when `hg` cannot be run: [`ExecError`], the OCaml's
//! `Unix.Unix_error (_, "create_process", "hg")`.

/// `Hg.Rev`
pub mod rev {
    /// `Hg.Rev.t`
    pub type T = String;
}

/// `Hg.global_rev`
pub type GlobalRev = isize;

/// `Hg.rev`
#[derive(Clone, Debug)]
pub enum Rev {
    HgRev(rev::T),
    GlobalRev(GlobalRev),
}

/// The exception of `Process.exec` when the process cannot be started:
/// `Unix.Unix_error (err, "create_process", name)`.
pub struct ExecError(pub std::io::Error, pub String);

impl std::fmt::Debug for ExecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&crate::rt::ocaml_unix::unix_error_to_string(&self.0, "create_process", &self.1))
    }
}

/// `Future_process.error_mode`, of the cases that can happen here.
#[derive(Clone, Debug)]
pub enum ErrorMode {
    ProcessFailure { status: std::process::ExitStatus, stderr: String },
    TransformerRaised(String),
}

/// `Future.error` of a process: `(Process_types.invocation_info, error_mode)`.
#[derive(Clone, Debug)]
pub struct FutureError {
    pub name: String,
    pub args: Vec<String>,
    pub mode: ErrorMode,
}

/// `Future.error_to_string` (`Future_process.ProcessError.to_string`)
pub fn error_to_string(e: &FutureError) -> String {
    let info = format!("({} [{}])", e.name, e.args.join(", "));
    match &e.mode {
        ErrorMode::ProcessFailure { status, stderr } => {
            use std::os::unix::process::ExitStatusExt;
            let status_string = match (status.code(), status.signal(), status.stopped_signal()) {
                (Some(i), _, _) => format!("({} WEXITED {})", info, i),
                (None, Some(i), _) => format!("({} WSIGNALED {})", info, i),
                (None, None, Some(i)) => format!("({} WSTOPPED {})", info, i),
                (None, None, None) => format!("({} WEXITED 0)", info),
            };
            format!("Process_failure({}, stderr: {})", status_string, stderr)
        }
        ErrorMode::TransformerRaised(e) => format!("Transformer_raised({} {})", info, e),
    }
}

/// `'a Future.t`: the result of the process (an error is `Future.error`).
pub type Future<A> = Result<A, FutureError>;

/// `Hg_sig.Malformed_result`
const MALFORMED_RESULT: &str = "Hg_sig.Types.Malformed_result";

/// `exec_hg args` then `Future_process.make process transformer`: runs
/// `hg` (with `HGPLAIN=1`: "Disable user aliases or configs") to its end.
fn exec_hg<A>(
    args: &[&str],
    transformer: impl FnOnce(&str) -> Result<A, String>,
) -> Result<Future<A>, ExecError> {
    let output = std::process::Command::new("hg")
        .args(args)
        .env("HGPLAIN", "1")
        .stdin(std::process::Stdio::null())
        .output()
        .map_err(|e| ExecError(e, "hg".to_string()))?;
    let error = |mode| FutureError {
        name: "hg".to_string(),
        args: args.iter().map(|s| s.to_string()).collect(),
        mode,
    };
    if !output.status.success() {
        return Ok(Err(error(ErrorMode::ProcessFailure {
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })));
    }
    Ok(transformer(&String::from_utf8_lossy(&output.stdout)).map_err(|e| error(ErrorMode::TransformerRaised(e))))
}

/// `rev_string rev`
pub fn rev_string(rev: &Rev) -> String {
    match rev {
        Rev::HgRev(hash) => hash.clone(),
        Rev::GlobalRev(rev) => format!("r{}", rev),
    }
}

/// `int_of_string`, its `Failure` as the error of the future.
fn int_of_string(s: &str) -> Result<isize, String> {
    crate::rt::ocaml_stdlib::int_of_string_opt(s).ok_or_else(|| "Failure(\"int_of_string\")".to_string())
}

/// The globalrev of a given revision. If that revision is not public, the
/// globalrev of `parents(roots(draft() & ::<rev>))`, and if there are merge
/// conflicts, the globalrev of the mergebase.
/// (`get_closest_global_ancestor rev repo`)
pub fn get_closest_global_ancestor(rev: &str, repo: &str) -> Result<Future<GlobalRev>, ExecError> {
    let global_rev_process = |rev: &str| -> Result<Future<GlobalRev>, ExecError> {
        exec_hg(&["log", "-r", rev, "-T", "{globalrev}\n", "--cwd", repo], |s| {
            int_of_string(s.trim())
        })
    };
    // If we are on public commit, it should have global_rev field and we are done
    let q1 = global_rev_process(rev)?;
    // Otherwise, we want the closest public commit. It returns empty set when
    // we are on a public commit, hence the need to still do q1 too
    let q2 = global_rev_process(&format!("parents(roots(draft() & ::{}))", rev))?;
    // q2 can also fail in case of merge conflicts, in which case let's fall back to
    // what we always used to do, closest mergebase with master bookmark
    let q3 = global_rev_process(&format!("ancestor(master,{})", rev))?;
    let take_first = |r1: Future<GlobalRev>, r2: Future<GlobalRev>| match r1 {
        Ok(_) => r1,
        _ => r2,
    };
    let r1 = take_first(q2, q3);
    Ok(take_first(q1, r1))
}

/// `current_mergebase_hg_rev repo`
pub fn current_mergebase_hg_rev(repo: &str) -> Result<Future<rev::T>, ExecError> {
    exec_hg(
        &["log", "--rev", "ancestor(master,.)", "-T", "{node}", "--cwd", repo],
        |result| {
            let result = result.trim();
            if result.is_empty() {
                Err(MALFORMED_RESULT.to_string())
            } else {
                Ok(result.to_string())
            }
        },
    )
}

/// Return the timestamp of a specific hg revision in seconds since Unix
/// epoch. (`get_hg_revision_time rev repo`)
pub fn get_hg_revision_time(rev: &Rev, repo: &str) -> Result<Future<isize>, ExecError> {
    exec_hg(
        &["log", "-r", &rev_string(rev), "-T", "{date|hgdate}", "--cwd", repo],
        |date_string| {
            let date_string = date_string.trim();
            let first = date_string.split(' ').next().unwrap_or("");
            int_of_string(first)
        },
    )
}
