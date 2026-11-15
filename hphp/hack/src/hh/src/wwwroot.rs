// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/wwwroot.ml`. See `hh/PORTING.md`.
//!
//! The `Sys_error` that `Path.is_directory` raises (when the path disappears
//! between the two checks of `validate_www_directory`) is the error of an
//! outer `Result` (the inner one is the OCaml `(_, string) result`).

use crate::path;
use crate::repo_root_ffi;
use crate::sys_utils::SysError;

/// Checks if x is a www directory by looking for ".hhconfig".
pub fn is_www_directory(path: &path::T) -> bool {
    let hhconfig = path::concat(path, ".hhconfig");
    path::file_exists(&hhconfig)
}

/// `Path.is_directory`, which raises `Sys_error` when `path` does not
/// exist.
fn is_directory(path: &path::T) -> Result<bool, SysError> {
    path::is_directory(path)
}

fn validate_www_directory(path: &path::T) -> Result<Result<(), String>, SysError> {
    Ok(if !(path::file_exists(path) && is_directory(path)?) {
        Err(format!("{} is not a directory", path::to_string(path)))
    } else if !is_www_directory(path) {
        Err(format!(
            "could not find a .hhconfig file in {} or any of its parent directories. Do you have a .hhconfig in your code's root directory?",
            path::to_string(path)
        ))
    } else {
        Ok(())
    })
}

/// Print a diagnostic to stderr and exit 1 if [path] is not a www directory.
pub fn assert_www_directory(path: &path::T) -> Result<(), SysError> {
    match validate_www_directory(path)? {
        Ok(()) => Ok(()),
        Err(message) => {
            use std::io::Write;
            eprint!("Error: {}\n", message);
            let _ = std::io::stderr().flush();
            // `exit` flushes the standard channels.
            let _ = std::io::stdout().flush();
            std::process::exit(1)
        }
    }
}

/// Traverse parent directories until a directory containing [.hhconfig] is found.
pub fn guess_root(start: &path::T) -> Option<path::T> {
    repo_root_ffi::guess_root(&path::to_string(start)).map(|root| path::make(&root))
}

/// Our command-line tools generally take a "root" parameter, and if none is
/// supplied then they fall back to a search based on the current directory.
/// This code implements that -- it ensures that either 0 or 1 root parameters
/// were passed (and returns an error if there were more);
/// if there were 0 parameters then it walks from CWD to find .hhconfig
/// and if there was 1 then it walks from that to find .hhconfig. If that search
/// fails, it also checks for .hhconfig in a www child of the initial directory.
/// Then it validates that .hhconfig really is there, and returns an error if it
/// wasn't.
///
/// The error is a one-line diagnostic with no "Error:" prefix and no trailing
/// newline.
///
/// CARE! Don't call this from arbitrary code in client or server, passing in
/// None in the hope that you'll pick up the root directory for your current process.
/// Doing so will mean you ignore the "root" parameter at the command-line!
pub fn interpret_command_line_root_parameter(
    paths: &[String],
) -> Result<Result<path::T, String>, SysError> {
    let path = match paths {
        [] => ".".to_string(),
        [path] => path.clone(),
        _ => return Ok(Err("please provide at most one www directory".to_string())),
    };
    let start_path = path::make(&path);
    let root = match guess_root(&start_path) {
        Some(root) => root,
        None => {
            let www_child = path::concat(&start_path, "www");
            if is_www_directory(&www_child) {
                www_child
            } else {
                start_path
            }
        }
    };
    Ok(validate_www_directory(&root)?.map(|()| root))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh directory under the temporary directory, resolved (on macOS
    /// the temporary directory is behind a symbolic link).
    fn temp_dir(name: &str) -> String {
        let dir = std::env::temp_dir().join(format!("hh_wwwroot_{}_{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        path::make(dir.to_str().unwrap())
    }

    fn interpret(paths: &[&str]) -> Result<String, String> {
        let paths: Vec<String> = paths.iter().map(|s| s.to_string()).collect();
        interpret_command_line_root_parameter(&paths).unwrap()
    }

    #[test]
    fn roots() {
        let tmp = temp_dir("roots");
        let root = format!("{}/root", tmp);
        let no_config = format!("{}/no_config", tmp);
        std::fs::create_dir_all(format!("{}/a/b/c", root)).unwrap();
        std::fs::write(format!("{}/.hhconfig", root), b"").unwrap();
        std::fs::create_dir_all(&no_config).unwrap();
        std::fs::write(format!("{}/.hginclude", no_config), b"").unwrap();

        // client_args_telemetry/root_found_in_parent
        assert_eq!(interpret(&[&format!("{}/a/b/c", root)]), Ok(root.clone()));
        assert!(is_www_directory(&root));
        assert!(!is_www_directory(&no_config));
        // client_args_telemetry/root_nonexistent_path: `Path.make` keeps a
        // path that does not exist as it is.
        assert_eq!(
            interpret(&["/nonexistent/hh_wwwroot/missing"]),
            Err("/nonexistent/hh_wwwroot/missing is not a directory".to_string())
        );
        // client_args_telemetry/root_not_a_directory
        assert_eq!(
            interpret(&[&format!("{}/.hginclude", no_config)]),
            Err(format!("{}/.hginclude is not a directory", no_config))
        );
        // client_args_telemetry/invalid_root (when no parent of the temporary
        // directory has a .hhconfig)
        if guess_root(&no_config).is_none() {
            assert_eq!(
                interpret(&[&no_config]),
                Err(format!(
                    "could not find a .hhconfig file in {} or any of its parent directories. Do you have a .hhconfig in your code's root directory?",
                    no_config
                ))
            );
        }
        assert_eq!(
            interpret(&["a", "b"]),
            Err("please provide at most one www directory".to_string())
        );
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn www_child() {
        let tmp = temp_dir("www_child");
        let www = format!("{}/www", tmp);
        std::fs::create_dir_all(&www).unwrap();
        std::fs::write(format!("{}/.hhconfig", www), b"").unwrap();
        // Only when no parent of the temporary directory has a .hhconfig.
        if guess_root(&path::dirname(&tmp)).is_none() {
            // `repo_root` checks the `www` child itself.
            assert_eq!(guess_root(&tmp), Some(www.clone()));
            assert_eq!(interpret(&[&tmp]), Ok(www.clone()));
        }
        std::fs::remove_dir_all(&tmp).unwrap();
    }

    #[test]
    fn lookup() {
        let tmp = temp_dir("lookup");
        let deep = format!("{}/x/y", tmp);
        std::fs::create_dir_all(&deep).unwrap();
        std::fs::write(format!("{}/.hhconfig", tmp), b"").unwrap();
        assert_eq!(guess_root(&deep), Some(tmp.clone()));
        std::fs::remove_dir_all(&tmp).unwrap();
    }
}
