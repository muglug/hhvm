// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `procs/bucket.ml`: making buckets of jobs (`make_list`, which
//! `Server_notifier`'s Watchman indexer hands the files out with). See
//! `hh/PORTING.md`. Not ported: `type 'a bucket`, `is_done`, `of_list`,
//! `make`, `make_n_buckets`, `map`.
//!
//! When we parallelize, we need to create "buckets" of tasks for the
//! workers.
//! Given a list of files, we want to split it up into buckets such that
//! every worker is busy long enough. If the bucket is too big, it hurts
//! load balancing, if it is too small, the overhead in synchronization time
//! hurts

pub const DEFAULT_MAX_SIZE: isize = 500;

/// `calculate_bucket_size ~num_jobs ~num_workers ?max_size ()`: `max_size`
/// defaults to [`DEFAULT_MAX_SIZE`].
pub fn calculate_bucket_size(
    num_jobs: isize,
    num_workers: isize,
    max_size: Option<isize>,
) -> isize {
    let max_size = max_size.unwrap_or(DEFAULT_MAX_SIZE);
    if num_jobs < num_workers * max_size {
        std::cmp::max(1, 1 + (num_jobs / num_workers))
    } else {
        max_size
    }
}

/// The progress function of `make_list`: `~total ~start ~length`.
pub type ProgressFn = Box<dyn FnMut(isize, isize, isize) + Send>;

/// [make_ progress_fn bucket_size jobs] returns a function
/// able to provide the next bucket of jobs from [jobs]. `progress_fn`
/// receives `~start ~length`.
pub fn make_<Job: Clone + Send + 'static>(
    mut progress_fn: Box<dyn FnMut(isize, isize) + Send>,
    bucket_size: isize,
    jobs: Vec<Job>,
) -> Box<dyn FnMut() -> Vec<Job> + Send> {
    let mut i: isize = 0;
    Box::new(move || {
        let bucket_size = std::cmp::min(jobs.len() as isize - i, bucket_size);
        progress_fn(i, bucket_size);
        // `Array.sub jobs ~pos:i ~len:bucket_size`
        let result = jobs[i as usize..(i + bucket_size) as usize].to_vec();
        i += bucket_size;
        result
    })
}

/// `make_list ~num_workers ?progress_fn ?max_size jobs`: `progress_fn`
/// (`~total ~start ~length`) defaults to doing nothing.
pub fn make_list<Job: Clone + Send + 'static>(
    num_workers: isize,
    progress_fn: Option<ProgressFn>,
    max_size: Option<isize>,
    jobs: Vec<Job>,
) -> Box<dyn FnMut() -> Vec<Job> + Send> {
    let mut progress_fn: ProgressFn = progress_fn.unwrap_or_else(|| Box::new(|_, _, _| ()));
    let bucket_size = calculate_bucket_size(jobs.len() as isize, num_workers, max_size);
    let total = jobs.len() as isize;
    make_(
        Box::new(move |start, length| progress_fn(total, start, length)),
        bucket_size,
        jobs,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn buckets() {
        assert_eq!(calculate_bucket_size(10, 4, None), 3);
        assert_eq!(calculate_bucket_size(0, 4, None), 1);
        assert_eq!(calculate_bucket_size(5000, 2, None), 500);
        assert_eq!(calculate_bucket_size(5000, 0, None), 500);
        let mut next = make_list(4, None, None, (0..10).collect::<Vec<_>>());
        assert_eq!(next(), vec![0, 1, 2]);
        assert_eq!(next(), vec![3, 4, 5]);
        assert_eq!(next(), vec![6, 7, 8]);
        assert_eq!(next(), vec![9]);
        assert_eq!(next(), Vec::<i32>::new());
        assert_eq!(next(), Vec::<i32>::new());
    }
}
