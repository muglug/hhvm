// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/repo_root_ffi.ml`. See `hh/PORTING.md`.
//!
//! Its external, `hh_guess_repo_root`, was `repo_root::guess_root_from`
//! (`utils/repo_root_ffi.rs`), which this calls.

/// Find the nearest directory containing [.hhconfig], starting at the given
/// directory and searching its ancestors up to Rust's traversal limit.
/// This is a best-effort lookup: all discovery failures return [None].
///
/// (A root whose path is not UTF-8 has its other bytes replaced by U+FFFD;
/// the OCaml string had them.)
pub fn guess_root(start: &str) -> Option<String> {
    repo_root::guess_root_from(std::path::Path::new(start))
        .ok()
        .map(|root| root.to_string_lossy().into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_the_directory_with_hhconfig() {
        let dir = std::env::temp_dir().join(format!("hh_repo_root_ffi_{}", std::process::id()));
        let sub = dir.join("a/b");
        std::fs::create_dir_all(&sub).unwrap();
        std::fs::write(dir.join(".hhconfig"), b"").unwrap();
        assert_eq!(
            guess_root(sub.to_str().unwrap()),
            Some(dir.to_str().unwrap().to_string())
        );
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(guess_root("/nonexistent/hh_repo_root_ffi"), None);
    }
}
