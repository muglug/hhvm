// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/find_refs_wire_format.ml`. See `hh/PORTING.md`.
//!
//! `CliArgs` is what the `hh_client` command line parses
//! `--ide-find-refs-by-symbol`, `--ide-find-refs-by-symbol3` and
//! `--ide-go-to-impl-by-symbol` with.
//!
//! `raise Exit_status.(Exit_with Input_error)` is `Err(ExitWith(InputError))`,
//! returned after the message is printed on standard error, as in OCaml.
//! `Yojson.Safe.Util.Type_error` (a JSON of the wrong shape) is
//! `Err(TypeError)`.

use crate::pos;
use crate::pos::Absolute;
use crate::search_types::find_refs;
use crate::yojson::safe as yojson;

/// `half_open_one_based`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HalfOpenOneBased {
    /// absolute
    pub filename: String,
    /// 1-based
    pub line: isize,
    /// 1-based
    pub char_start: isize,
    /// 1-based
    pub char_end: isize,
}

pub fn from_absolute(pos: &Absolute) -> HalfOpenOneBased {
    let (line, char_start, _line_end, char_end) = pos::destruct_range_one_based(pos);
    let filename = pos::filename(pos);
    HalfOpenOneBased {
        filename,
        line,
        char_start,
        char_end,
    }
}

pub fn pos_to_one_based_json(
    timestamp: Option<f64>,
    half_open_interval: bool,
    r: &find_refs::Absolute,
) -> yojson::T {
    let find_refs::Result { name, pos } = r;
    let HalfOpenOneBased {
        filename,
        line,
        char_start,
        char_end,
    } = if half_open_interval {
        from_absolute(pos)
    } else {
        let (line, char_start, char_end) = pos::info_pos(pos);
        HalfOpenOneBased {
            filename: pos::filename(pos),
            line,
            char_start,
            char_end,
        }
    };
    let mut fields = match timestamp {
        None => vec![],
        Some(t) => vec![("timestamp".to_string(), yojson::T::Float(t))],
    };
    fields.extend([
        ("name".to_string(), yojson::T::String(name.clone())),
        ("filename".to_string(), yojson::T::String(filename)),
        ("line".to_string(), yojson::T::Int(line)),
        ("char_start".to_string(), yojson::T::Int(char_start)),
        ("char_end".to_string(), yojson::T::Int(char_end)),
    ]);
    yojson::T::Assoc(fields)
}

/// `Yojson.Safe.Util.Type_error (msg, json)` (the message only).
#[derive(Clone, Debug, PartialEq)]
pub struct TypeError(pub String);

/// `Yojson.Safe.Util.member`: the first binding of the name (`List.assoc`),
/// `Null` when absent.
fn member<'a>(name: &str, json: &'a yojson::T) -> Result<&'a yojson::T, TypeError> {
    match json {
        yojson::T::Assoc(l) => Ok(l
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v)
            .unwrap_or(&yojson::T::Null)),
        _ => Err(TypeError(format!(
            "Can't get member '{}' of non-object type {}",
            name,
            crate::yojson::safe::util::typeof_(json)
        ))),
    }
}

fn to_string(json: &yojson::T) -> Result<String, TypeError> {
    match json {
        yojson::T::String(s) => Ok(s.clone()),
        _ => Err(TypeError(format!("Expected string, got {}", crate::yojson::safe::util::typeof_(json)))),
    }
}

fn to_int(json: &yojson::T) -> Result<isize, TypeError> {
    match json {
        yojson::T::Int(i) => Ok(*i),
        _ => Err(TypeError(format!("Expected int, got {}", crate::yojson::safe::util::typeof_(json)))),
    }
}

pub fn half_open_one_based_json_to_pos_exn(
    json: &yojson::T,
) -> Result<HalfOpenOneBased, TypeError> {
    Ok(HalfOpenOneBased {
        filename: to_string(member("filename", json)?)?,
        line: to_int(member("line", json)?)?,
        char_start: to_int(member("char_start", json)?)?,
        char_end: to_int(member("char_end", json)?)?,
    })
}

/// What `from_string_exn` and `read_from_locked_file` raise: the JSON does
/// not parse (`Yojson.Json_error`), or has the wrong shape (`Type_error`).
#[derive(Clone, Debug, PartialEq)]
pub enum ReadError {
    Json(crate::yojson::JsonError),
    Type(TypeError),
}

/// Produced by "hh --ide-find-refs-by-symbol" and parsed by clientLsp
pub mod ide_shellout {
    use super::*;

    pub fn to_string(results: &[find_refs::Absolute]) -> String {
        let entries = results
            .iter()
            .map(|r| pos_to_one_based_json(None, true, r))
            .collect();
        // unsorted: IPC wire format, parsed programmatically
        yojson::to_string(&yojson::T::List(entries))
    }

    pub fn from_string_exn(s: &str) -> Result<Vec<HalfOpenOneBased>, ReadError> {
        let json = yojson::from_string(s).map_err(ReadError::Json)?;
        let entries = match &json {
            yojson::T::List(l) => l,
            _ => {
                return Err(ReadError::Type(TypeError(format!(
                    "Expected array, got {}",
                    crate::yojson::safe::util::typeof_(&json)
                ))));
            }
        };
        entries
            .iter()
            .map(|e| half_open_one_based_json_to_pos_exn(e).map_err(ReadError::Type))
            .collect()
    }
}

/// Used by hh_server's findRefsService to write to a streaming file, read by clientLsp
pub mod ide_stream {
    use std::io;

    use super::*;
    use crate::rt::ocaml_unix;
    use crate::rt::ocaml_unix::LockCommand;
    use crate::rt::ocaml_unix::UnixError;
    use crate::sys_utils;

    /// Locks the file and appends refs to it
    pub fn lock_and_append(fd: &std::fs::File, results: &[find_refs::Absolute]) -> io::Result<()> {
        if results.is_empty() {
            Ok(())
        } else {
            let bytes: String = results
                .iter()
                .map(|find_refs::Result { name, pos }| {
                    format!(
                        "{}\n",
                        // unsorted: IPC wire format, parsed programmatically
                        yojson::to_string(&pos_to_one_based_json(
                            Some(ocaml_unix::gettimeofday()),
                            true,
                            &find_refs::Result {
                                name: name.clone(),
                                pos: pos.clone(),
                            },
                        ))
                    )
                })
                .collect();
            sys_utils::with_lock(fd, LockCommand::FLock, || {
                let _ = ocaml_unix::lseek(fd, 0, libc::SEEK_END)?;
                sys_utils::write_non_intr(fd, bytes.as_bytes())?;
                fd.sync_all().map_err(|e| UnixError(e, "fsync", String::new()))
            })
            .map_err(|UnixError(e, _, _)| e)
        }
    }

    /// The error of `read_from_locked_file`: a system call failed
    /// (`Unix_error`), or a line is not the JSON of a position.
    #[derive(Debug)]
    pub enum ReadFromLockedFileError {
        Unix(io::Error),
        Read(ReadError),
    }

    /// Reads the refs in the file that came after [pos], if any;
    /// returns a new [pos] after the last ref that was read. Caller must
    /// acquire F_RLOCK first.
    pub fn read_from_locked_file(
        fd: &std::fs::File,
        pos: i64,
    ) -> Result<(Vec<HalfOpenOneBased>, i64), ReadFromLockedFileError> {
        use ReadFromLockedFileError as E;
        let unix = |UnixError(e, _, _)| E::Unix(e);
        let end_pos = ocaml_unix::lseek(fd, 0, libc::SEEK_END).map_err(unix)?;
        if pos == end_pos {
            Ok((vec![], pos))
        } else {
            let _ = ocaml_unix::lseek(fd, pos, libc::SEEK_SET).map_err(unix)?;
            // `Sys_utils.read_non_intr fd (end_pos - pos) |> Option.value_exn`
            let buf = match sys_utils::read_non_intr(fd, (end_pos - pos) as usize).map_err(unix)? {
                Some(buf) => buf,
                None => {
                    panic!("Option.value_exn: Sys_utils.read_non_intr reached the end of the file")
                }
            };
            let text = String::from_utf8_lossy(&buf).into_owned();
            let jsons = crate::string_utils::split_on_newlines(&text)
                .iter()
                .map(|l| yojson::from_string(l).map_err(|e| E::Read(ReadError::Json(e))))
                .collect::<Result<Vec<_>, _>>()?;
            let results = jsons
                .iter()
                .map(|j| half_open_one_based_json_to_pos_exn(j).map_err(|e| E::Read(ReadError::Type(e))))
                .collect::<Result<Vec<_>, _>>()?;
            Ok((results, end_pos))
        }
    }
}

/// Used "hh --find-refs --json" and read by HackAst and other tools
pub mod hack_ast {
    use super::*;

    pub fn to_json(results: &[find_refs::Absolute]) -> yojson::T {
        let entries = results
            .iter()
            .map(|r| pos_to_one_based_json(None, false, r))
            .collect();
        yojson::T::List(entries)
    }
}

/// Used by "hh --find-refs"
pub mod cli_human_readable {
    use super::*;

    pub fn print_results(results: &[find_refs::Absolute]) {
        print!("{}", print_results_to_string(results))
    }

    /// What `print_results` prints.
    pub fn print_results_to_string(results: &[find_refs::Absolute]) -> String {
        let mut s = String::new();
        for find_refs::Result { name, pos } in results {
            s.push_str(&format!("{} {}\n", pos::string(pos), name));
        }
        s.push_str(&format!("{} total results\n", results.len()));
        s
    }
}

/// `Find_refs_wire_format.CliArgs`
pub mod cli_args {
    use crate::exit_status;
    use crate::exit_status::ExitWith;
    use crate::path;
    use crate::search_types::find_refs::Action;
    use crate::search_types::find_refs::Member;

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct T {
        pub symbol_name: String,
        pub action: Action,
        pub stream_file: Option<path::T>,
        pub hint_suffixes: Vec<String>,
    }

    fn input_error<A>() -> Result<A, ExitWith> {
        Err(ExitWith(exit_status::T::InputError))
    }

    /// Output strings in the form of
    /// SYMBOL_NAME|COMMA_SEPARATED_ACTION_STRING
    /// For example,
    /// HackTypecheckerQueryBase::getWWWDir|Member,\HackTypecheckerQueryBase,Method,getWWWDir
    /// Must be manually kept in sync with string_to_symbol_and_action_exn.
    pub fn to_string(t: &T) -> Result<String, ExitWith> {
        let T {
            symbol_name,
            action,
            ..
        } = t;
        let action_serialized = match action {
            Action::Class(str) => format!("Class,{}", str),
            Action::ExplicitClass(str) => format!("ExplicitClass,{}", str),
            Action::Function(str) => format!("Function,{}", str),
            Action::GConst(str) => format!("GConst,{}", str),
            Action::Member(str, Member::Method(s)) => format!("Member,{},{},{}", str, "Method", s),
            Action::Member(str, Member::Property(s)) => {
                format!("Member,{},{},{}", str, "Property", s)
            }
            Action::Member(str, Member::ClassConst(s)) => {
                format!("Member,{},{},{}", str, "Class_const", s)
            }
            Action::Member(str, Member::Typeconst(s)) => {
                format!("Member,{},{},{}", str, "Typeconst", s)
            }
            Action::LocalVar { .. } => {
                eprint!("Invalid action\n");
                return input_error();
            }
        };
        Ok(format!("{}|{}", symbol_name, action_serialized))
    }

    /// Expects input strings in the form of
    /// SYMBOL_NAME|COMMA_SEPARATED_ACTION_STRING
    /// For example,
    /// HackTypecheckerQueryBase::getWWWDir|Member,\HackTypecheckerQueryBase,Method,getWWWDir
    /// The implementation explicitly is tied to whatever is generated from symbol_and_action_to_string_exn
    /// and should be kept in sync manually by anybody editing.
    pub fn from_string_exn(string1: &str) -> Result<T, ExitWith> {
        let pair = crate::rt::ocaml_str::split("|", string1);
        let (symbol_name, action_arg) = match pair.as_slice() {
            [symbol_name, action_arg] => (symbol_name.clone(), action_arg.clone()),
            _ => {
                eprint!("Invalid input\n");
                return input_error();
            }
        };
        // Explicitly ignoring localvar support
        let parts = crate::rt::ocaml_str::split(",", &action_arg);
        let parts: Vec<&str> = parts.iter().map(String::as_str).collect();
        let action = match parts.as_slice() {
            ["Class", str] => Action::Class(str.to_string()),
            ["ExplicitClass", str] => Action::ExplicitClass(str.to_string()),
            ["Function", str] => Action::Function(str.to_string()),
            ["GConst", str] => Action::GConst(str.to_string()),
            ["Member", str, "Method", member_name] => {
                Action::Member(str.to_string(), Member::Method(member_name.to_string()))
            }
            ["Member", str, "Property", member_name] => {
                Action::Member(str.to_string(), Member::Property(member_name.to_string()))
            }
            ["Member", str, "Class_const", member_name] => {
                Action::Member(str.to_string(), Member::ClassConst(member_name.to_string()))
            }
            ["Member", str, "Typeconst", member_name] => {
                Action::Member(str.to_string(), Member::Typeconst(member_name.to_string()))
            }
            _ => {
                eprintln!("Invalid input for action, got {}", action_arg);
                return input_error();
            }
        };
        Ok(T {
            symbol_name,
            action,
            stream_file: None,
            hint_suffixes: vec![],
        })
    }

    pub fn to_string_triple(t: &T) -> Result<(String, String, String), ExitWith> {
        let action = to_string(t)?;
        let stream_file = match &t.stream_file {
            None => "-".to_string(),
            Some(stream_file) => path::to_string(stream_file),
        };
        let hint_suffixes = t.hint_suffixes.join("|");
        Ok((action, stream_file, hint_suffixes))
    }

    pub fn from_string_triple_exn(
        (action, stream_file, hints): (&str, &str, &str),
    ) -> Result<T, ExitWith> {
        let T {
            symbol_name,
            action,
            ..
        } = from_string_exn(action)?;
        let stream_file = if stream_file == "-" {
            None
        } else {
            Some(path::make(stream_file))
        };
        // `String.split_on_chars hints ~on:['|']`: every piece, empty ones
        // included.
        let hint_suffixes = hints.split('|').map(str::to_string).collect();
        Ok(T {
            symbol_name,
            action,
            stream_file,
            hint_suffixes,
        })
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn round_trips() {
            let t = from_string_exn(
                "HackTypecheckerQueryBase::getWWWDir|Member,\\HackTypecheckerQueryBase,Method,getWWWDir",
            )
            .unwrap();
            assert_eq!(t.symbol_name, "HackTypecheckerQueryBase::getWWWDir");
            assert_eq!(
                t.action,
                Action::Member(
                    "\\HackTypecheckerQueryBase".to_string(),
                    Member::Method("getWWWDir".to_string())
                )
            );
            assert_eq!(
                to_string(&t).unwrap(),
                "HackTypecheckerQueryBase::getWWWDir|Member,\\HackTypecheckerQueryBase,Method,getWWWDir"
            );
            let t = from_string_triple_exn(("C|Class,\\C", "-", "")).unwrap();
            assert_eq!(t.stream_file, None);
            assert_eq!(t.hint_suffixes, vec![""]);
            assert_eq!(
                to_string_triple(&t).unwrap(),
                ("C|Class,\\C".to_string(), "-".to_string(), "".to_string())
            );
        }

        #[test]
        fn bad_input_raises_input_error() {
            let ExitWith(es) = from_string_exn("bogus").unwrap_err();
            assert!(matches!(es, exit_status::T::InputError));
            let ExitWith(es) = from_string_exn("a|Nope,x").unwrap_err();
            assert!(matches!(es, exit_status::T::InputError));
        }
    }
}
