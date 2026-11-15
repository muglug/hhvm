// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/filter_diagnostics.ml`. See `hh/PORTING.md`.
//!
//! Module to filter a list of errors in order to implement the
//! warnings CLI flags like -Wall, -Wnone, -W, -Wno, etc.
//!
//! `Str.regexp` is `crate::rt::ocaml_str::Regexp`. The cache of
//! `IsNonGenerated` (a `Hashtbl` in OCaml) is process wide.
//!
//! `Filter.t` crosses the socket in the `STATUS` command (OCaml marshals
//! it): it and `Warning_set.t` are `serde` (a regular expression as its
//! source).

use std::collections::HashMap;
use std::io::BufRead;
use std::sync::LazyLock;
use std::sync::Mutex;

use crate::diagnostics;
use crate::pos::Absolute;
use crate::rt::ocaml_str;
use crate::rt::ocaml_str::Regexp;
use crate::user_diagnostic;

/// `Diagnostics.finalized_diagnostic`
type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

/// `module Code = Error_codes.Warning`
pub mod code {
    pub use crate::error_codes::warning::*;
}

#[derive(Clone, Debug)]
pub enum Switch {
    /// -Wall
    WAll,
    /// -Wnone
    WNone,
    /// -W 12001
    CodeOn(code::T),
    /// -Wno 12001
    CodeOff(code::T),
    /// -Wignored-files <regexp>
    IgnoredFiles(Regexp),
    /// -Wgenerated
    GeneratedFilesOn,
}

mod warning_set {
    use super::code;

    /// `Error_codes.Warning_set`
    type Set = crate::error_codes::warning_set::T;

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub enum T {
        AllExcept(Set),
        NoneExcept(Set),
    }

    pub fn empty() -> T {
        T::NoneExcept(Set::new())
    }

    pub fn all() -> T {
        T::AllExcept(Set::new())
    }

    pub fn add(code: code::T, t: T) -> T {
        match t {
            T::AllExcept(mut set) => {
                set.remove(&code);
                T::AllExcept(set)
            }
            T::NoneExcept(mut set) => {
                set.insert(code);
                T::NoneExcept(set)
            }
        }
    }

    pub fn remove(code: code::T, t: T) -> T {
        match t {
            T::AllExcept(mut set) => {
                set.insert(code);
                T::AllExcept(set)
            }
            T::NoneExcept(mut set) => {
                set.remove(&code);
                T::NoneExcept(set)
            }
        }
    }

    pub fn mem(code: code::T, t: &T) -> bool {
        match t {
            T::AllExcept(set) => !set.contains(&code),
            T::NoneExcept(set) => set.contains(&code),
        }
    }
}

type Path = String;

type Code = isize;

pub mod filter {
    use super::*;

    #[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
    pub struct T {
        codes: warning_set::T,
        ignore_files: Vec<Regexp>,
        generated_files: Vec<Regexp>,
        filter_out_generated_files: bool,
    }

    fn empty() -> T {
        T {
            codes: warning_set::empty(),
            ignore_files: vec![],
            generated_files: vec![],
            filter_out_generated_files: true,
        }
    }

    fn add_code(code: code::T, filter: T) -> T {
        T {
            codes: warning_set::add(code, filter.codes),
            ..filter
        }
    }

    fn remove_code(code: code::T, filter: T) -> T {
        T {
            codes: warning_set::remove(code, filter.codes),
            ..filter
        }
    }

    fn with_all_codes(filter: T) -> T {
        T {
            codes: warning_set::all(),
            ..filter
        }
    }

    fn with_no_codes(filter: T) -> T {
        T {
            codes: warning_set::empty(),
            ..filter
        }
    }

    fn add_ignored_files(re: Regexp, filter: T) -> T {
        // `re :: filter.ignore_files`
        let mut ignore_files = filter.ignore_files;
        ignore_files.insert(0, re);
        T {
            ignore_files,
            ..filter
        }
    }

    fn apply_switch(filter: T, switch: Switch) -> T {
        match switch {
            Switch::WAll => with_all_codes(filter),
            Switch::WNone => with_no_codes(filter),
            Switch::CodeOn(code) => add_code(code, filter),
            Switch::CodeOff(code) => remove_code(code, filter),
            Switch::IgnoredFiles(re) => add_ignored_files(re, filter),
            Switch::GeneratedFilesOn => T {
                generated_files: vec![],
                filter_out_generated_files: false,
                ..filter
            },
        }
    }

    /// [default_all] controls wether an empty list of switches is equivalent to [WAll]
    /// as opposed to [WNone]
    pub fn make(default_all: bool, generated_files: Vec<Regexp>, switches: Vec<Switch>) -> T {
        let first = if default_all {
            Switch::WAll
        } else {
            Switch::WNone
        };
        let switches = std::iter::once(first).chain(switches);
        // TODO: consider reordering switches to put all the -Wall and -Wnone first
        switches.fold(
            T {
                generated_files,
                ..empty()
            },
            apply_switch,
        )
    }

    fn pass_code(codes: &warning_set::T, code: code::T) -> bool {
        warning_set::mem(code, codes)
    }

    fn match_regexp(path: &Path, regexp: &Regexp) -> bool {
        // `Str.search_forward` raises `Not_found` when nothing matches.
        match ocaml_str::search_forward(regexp, path, 0) {
            Some(_i) => true,
            None => false,
        }
    }

    fn pass_path(ignore_files: &[Regexp], file_path: &Path) -> bool {
        !ignore_files.iter().any(|re| match_regexp(file_path, re))
    }

    pub(super) mod is_non_generated {
        use super::*;

        static IS_GENERATED_CACHE: LazyLock<Mutex<HashMap<Path, bool>>> =
            LazyLock::new(|| Mutex::new(HashMap::with_capacity(1000)));

        /// `Re.str ("@" ^ "generated") |> Re.compile`, matched with
        /// `Re.execp`: the line contains this string.
        // Writing like this to prevent CI from thinking this that file is generated...
        static AT_GENERATED: LazyLock<String> = LazyLock::new(|| "@".to_string() + "generated");

        const MAX_LINES: usize = 50;

        pub(super) fn is_generated(path: &Path) -> bool {
            // `Stdlib.In_channel.with_open_text path`, then `input_line` up
            // to `max_lines` times; `Sys_error` (the file cannot be opened
            // or read) gives `false`.
            let file = match std::fs::File::open(path) {
                Ok(file) => file,
                // File not found. This could be the case for some tests.
                Err(_) => return false,
            };
            let mut ic = std::io::BufReader::new(file);
            let mut line = Vec::new();
            for _i in 0..MAX_LINES {
                line.clear();
                match ic.read_until(b'\n', &mut line) {
                    // File not found. This could be the case for some tests.
                    Err(_) => return false,
                    Ok(0) => return false,
                    Ok(_) => {
                        if line.last() == Some(&b'\n') {
                            line.pop();
                        }
                        if bstr::ByteSlice::contains_str(&line[..], AT_GENERATED.as_bytes()) {
                            return true;
                        }
                    }
                }
            }
            false
        }

        pub(super) fn pass(skip: bool, path: &Path) -> bool {
            if skip {
                true
            } else {
                let cached = IS_GENERATED_CACHE.lock().unwrap().get(path).copied();
                match cached {
                    Some(is_generated) => !is_generated,
                    None => {
                        let is_generated = is_generated(path);
                        IS_GENERATED_CACHE
                            .lock()
                            .unwrap()
                            .insert(path.clone(), is_generated);
                        !is_generated
                    }
                }
            }
        }
    }

    pub(super) fn pass(
        T {
            codes,
            ignore_files,
            generated_files,
            filter_out_generated_files,
        }: &T,
        (code, file_path): (Code, &Path),
    ) -> bool {
        match crate::error_codes::warning::of_enum(code) {
            None => {
                // This is not a warning, so don't filter out
                true
            }
            Some(code) => {
                pass_code(codes, code)
                    && pass_path(
                        &ignore_files
                            .iter()
                            .chain(generated_files.iter())
                            .cloned()
                            .collect::<Vec<_>>(),
                        file_path,
                    )
                    && is_non_generated::pass(!filter_out_generated_files, file_path)
            }
        }
    }
}

pub fn filter(
    filter: &filter::T,
    error_list: Vec<FinalizedDiagnostic>,
) -> Vec<FinalizedDiagnostic> {
    error_list
        .into_iter()
        .filter(|error| {
            filter::pass(
                filter,
                (
                    user_diagnostic::get_code(error),
                    &crate::pos::filename(&user_diagnostic::get_pos(error)),
                ),
            )
        })
        .collect()
}

pub fn filter_with_hash(
    filter: &filter::T,
    error_list: Vec<(FinalizedDiagnostic, isize)>,
) -> Vec<(FinalizedDiagnostic, isize)> {
    error_list
        .into_iter()
        .filter(|(error, _hash)| {
            filter::pass(
                filter,
                (
                    user_diagnostic::get_code(error),
                    &crate::pos::filename(&user_diagnostic::get_pos(error)),
                ),
            )
        })
        .collect()
}

pub fn filter_rel(filter: &filter::T, errors: diagnostics::T) -> diagnostics::T {
    diagnostics::filter(errors, |path, error| {
        filter::pass(
            filter,
            (
                user_diagnostic::get_code(error),
                &crate::relative_path::suffix(path),
            ),
        )
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use bstr::BString;
    use oxidized::explanation::Explanation;
    use oxidized::message::Message;
    use relative_path::Prefix;
    use relative_path::RelativePath;

    use super::*;
    use crate::rt::diagnostic_fixtures as fx;

    /// A diagnostic with this code in the file at `path` (absolute).
    fn diag(code: isize, path: &str) -> FinalizedDiagnostic {
        fx::err(code, fx::msg(fx::pos(path, (1, 0), (1, 1)), "m"), vec![])
    }

    fn codes(l: &[FinalizedDiagnostic]) -> Vec<isize> {
        l.iter().map(|e| e.code).collect()
    }

    fn re(s: &str) -> Regexp {
        ocaml_str::regexp(s).unwrap()
    }

    /// 12001 and 12004 are warnings; 4110 is not, so it always passes.
    fn errors() -> Vec<FinalizedDiagnostic> {
        vec![
            diag(12001, "/nonexistent/a.php"),
            diag(4110, "/nonexistent/a.php"),
            diag(12004, "/nonexistent/b/c.php"),
        ]
    }

    #[test]
    fn default_all_and_codes() {
        let all = filter::make(true, vec![], vec![]);
        assert_eq!(codes(&filter(&all, errors())), vec![12001, 4110, 12004]);
        let none = filter::make(false, vec![], vec![]);
        assert_eq!(codes(&filter(&none, errors())), vec![4110]);
        let one = filter::make(
            false,
            vec![],
            vec![Switch::CodeOn(code::of_enum(12004).unwrap())],
        );
        assert_eq!(codes(&filter(&one, errors())), vec![4110, 12004]);
        let all_but_one = filter::make(
            true,
            vec![],
            vec![Switch::CodeOff(code::of_enum(12004).unwrap())],
        );
        assert_eq!(codes(&filter(&all_but_one, errors())), vec![12001, 4110]);
        // The switches apply in order: a later -Wnone undoes an earlier -W.
        let reset = filter::make(
            true,
            vec![],
            vec![Switch::CodeOn(code::of_enum(12001).unwrap()), Switch::WNone],
        );
        assert_eq!(codes(&filter(&reset, errors())), vec![4110]);
        let wall_then_off = filter::make(
            false,
            vec![],
            vec![
                Switch::WAll,
                Switch::CodeOff(code::of_enum(12001).unwrap()),
                Switch::CodeOn(code::of_enum(12001).unwrap()),
            ],
        );
        assert_eq!(
            codes(&filter(&wall_then_off, errors())),
            vec![12001, 4110, 12004]
        );
    }

    #[test]
    fn ignored_and_generated_files() {
        let ignored = filter::make(true, vec![], vec![Switch::IgnoredFiles(re("/b/"))]);
        assert_eq!(codes(&filter(&ignored, errors())), vec![12001, 4110]);
        // `generated_files` filter out too, unless -Wgenerated.
        let generated = filter::make(true, vec![re("a\\.php$")], vec![]);
        assert_eq!(codes(&filter(&generated, errors())), vec![4110, 12004]);
        let generated_on = filter::make(true, vec![re("a\\.php$")], vec![Switch::GeneratedFilesOn]);
        assert_eq!(
            codes(&filter(&generated_on, errors())),
            vec![12001, 4110, 12004]
        );
        // -Wgenerated forgets the generated files, not the ignored ones.
        let both = filter::make(
            true,
            vec![re("a\\.php$")],
            vec![
                Switch::IgnoredFiles(re("c\\.php")),
                Switch::GeneratedFilesOn,
            ],
        );
        assert_eq!(codes(&filter(&both, errors())), vec![12001, 4110]);
    }

    #[test]
    fn files_marked_generated() {
        let dir =
            std::env::temp_dir().join(format!("hh_filter_diagnostics_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let write = |name: &str, content: String| {
            let path = dir.join(name);
            std::fs::write(&path, content).unwrap();
            path.to_str().unwrap().to_string()
        };
        let marker = "@".to_string() + "generated";
        let early = write("early.php", format!("<?hh\n// {marker}\n"));
        let line_50 = write("line_50.php", "\n".repeat(49) + &marker);
        let line_51 = write("line_51.php", "\n".repeat(50) + &marker);
        let plain = write("plain.php", "<?hh\n".to_string());
        let l = vec![
            diag(12001, &early),
            diag(4110, &early),
            diag(12001, &line_50),
            diag(12001, &line_51),
            diag(12001, &plain),
            diag(12001, "/nonexistent/missing.php"),
        ];
        let f = filter::make(true, vec![], vec![]);
        let kept: Vec<String> = filter(&f, l.clone())
            .iter()
            .map(|e| crate::pos::filename(&e.claim.0))
            .collect();
        assert_eq!(
            kept,
            vec![
                early.clone(),
                line_51.clone(),
                plain.clone(),
                "/nonexistent/missing.php".to_string()
            ]
        );
        let on = filter::make(true, vec![], vec![Switch::GeneratedFilesOn]);
        assert_eq!(filter(&on, l.clone()).len(), l.len());
        // filter_with_hash keeps the hashes.
        let with_hash: Vec<(FinalizedDiagnostic, isize)> = l
            .into_iter()
            .enumerate()
            .map(|(i, e)| (e, i as isize))
            .collect();
        let kept: Vec<isize> = filter_with_hash(&f, with_hash)
            .into_iter()
            .map(|(_, h)| h)
            .collect();
        assert_eq!(kept, vec![1, 3, 4, 5]);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn filter_rel_matches_the_suffix() {
        let path = RelativePath::make(Prefix::Root, "b/c.php".into());
        let pos =
            oxidized::pos::Pos::from_lnum_bol_offset(Arc::new(path.clone()), (1, 0, 0), (1, 0, 1));
        let d = |code| -> oxidized::diagnostics::Diagnostic {
            user_diagnostic::make_err(
                code,
                None,
                None,
                None,
                None,
                Message(pos.clone(), BString::from("m")),
                vec![],
                Explanation::Empty,
            )
        };
        let t = diagnostics::from_file_diagnostic_list(vec![
            (path.clone(), d(12001)),
            (path.clone(), d(4110)),
        ]);
        // The regexp is matched against the suffix, `b/c.php`.
        let f = filter::make(true, vec![], vec![Switch::IgnoredFiles(re("^b/"))]);
        let kept: Vec<isize> = diagnostics::get_diagnostic_list(None, filter_rel(&f, t))
            .iter()
            .map(|e| e.code)
            .collect();
        assert_eq!(kept, vec![4110]);
    }
}
