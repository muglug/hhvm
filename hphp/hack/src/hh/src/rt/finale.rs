// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: the codec of the finale file `<tmp>/<pid>.fin`
//! (`Server_files.server_finale_file`):
//! what a server leaves behind when it exits in a controlled way, read back
//! by `Exit_status.get_finale_data` so that a client can print "Hack server
//! disconnected suddenly [<status>]".
//!
//! As in OCaml (`Marshal.to_channel oc finale_data []` in the exit hook of
//! `Server_main.setup_ipc`, `Marshal.from_channel` in `get_finale_data`),
//! the file is the OCaml `Marshal` of an `Exit_status.finale_data`
//! ([`to_ocaml`], [`of_ocaml`], over `rt::ocaml_marshal`), so that a client of
//! either implementation reads the exit reason of a server of the other:
//! `{exit_status; msg; stack = Callstack s; telemetry}` is a block of tag 0;
//! `Exit_status.t`'s constant constructors are the integers 0, 1... in the
//! order of the type (the non-constant ones skipped: [`CONSTANT_CONSTRUCTORS`]),
//! `Server_hung_up_should_retry`, `Server_hung_up_should_abort` and
//! `Uncaught_exception` blocks of tags 0, 1 and 2; `Telemetry.t` the list of
//! its pairs (`Yojson.Safe.t` as polymorphic variants); `Exception.t` the
//! record `{exn; backtrace}`.
//!
//! An exception of the port has no OCaml value: `Uncaught_exception e` is
//! written as an exception constructor of no argument whose name is
//! `Exception.get_ctor_string e` (an `Object_tag` block `[name; 0]`, which
//! `Printexc.to_string` shows as the name) and an empty backtrace; one read
//! from an OCaml file is an exception whose constructor string is what
//! `Printexc.to_string` would show (its generic printer). The JSON form of
//! these values ([`yojson_of_t`] etc., `ppx_yojson_conv`'s encoding) is kept
//! for the tests that show them.

use std::fmt;

use crate::exception;
use crate::exit_status::FinaleData;
use crate::exit_status::T;
use crate::exit_status::constant_constructor_of_name;
use crate::exit_status::constructor_name;
use crate::rt::ocaml_marshal;
use crate::rt::ocaml_marshal::ConvError;
use crate::rt::ocaml_marshal::Value;
use crate::rt::ocaml_unix;
use crate::telemetry;
use crate::utils;
use crate::yojson::safe as yojson;

/// An exception recorded in a finale file: what `Printexc.to_string` showed.
struct RecordedException {
    ctor: String,
}

impl fmt::Debug for RecordedException {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.ctor)
    }
}

/// The JSON of an `Exit_status.t` (see the module documentation).
pub fn yojson_of_t(t: &T) -> yojson::T {
    let name = yojson::T::String(constructor_name(t).to_string());
    match t {
        T::ServerHungUpShouldRetry(finale_data) | T::ServerHungUpShouldAbort(finale_data) => {
            let arg = match finale_data {
                None => yojson::T::Null,
                Some(finale_data) => yojson_of_finale_data(finale_data),
            };
            yojson::T::List(vec![name, arg])
        }
        T::UncaughtException(e) => yojson::T::List(vec![
            name,
            yojson::T::Assoc(vec![
                (
                    "ctor".to_string(),
                    yojson::T::String(exception::get_ctor_string(e)),
                ),
                (
                    "backtrace".to_string(),
                    yojson::T::String(exception::get_backtrace_string(e)),
                ),
            ]),
        ]),
        _ => yojson::T::List(vec![name]),
    }
}

fn of_yojson_error<A>(what: &str, json: &yojson::T) -> Result<A, String> {
    Err(format!("{}: {}", what, yojson::to_string(json)))
}

/// An `Exit_status.t` from its JSON (see the module documentation).
pub fn t_of_yojson(json: &yojson::T) -> Result<T, String> {
    match json {
        yojson::T::List(l) => match l.as_slice() {
            [yojson::T::String(name)] => match constant_constructor_of_name(name) {
                Some(t) => Ok(t),
                None => of_yojson_error("Exit_status.t_of_yojson: unexpected variant", json),
            },
            [yojson::T::String(name), arg]
                if name == "Server_hung_up_should_retry"
                    || name == "Server_hung_up_should_abort" =>
            {
                let finale_data = match arg {
                    yojson::T::Null => None,
                    arg => Some(Box::new(finale_data_of_yojson(arg)?)),
                };
                Ok(if name == "Server_hung_up_should_retry" {
                    T::ServerHungUpShouldRetry(finale_data)
                } else {
                    T::ServerHungUpShouldAbort(finale_data)
                })
            }
            [yojson::T::String(name), yojson::T::Assoc(fields)] if name == "Uncaught_exception" => {
                match fields.iter().find(|(k, _)| k == "ctor") {
                    Some((_, yojson::T::String(ctor))) => Ok(T::UncaughtException(
                        exception::wrap(RecordedException { ctor: ctor.clone() }),
                    )),
                    _ => of_yojson_error("Exit_status.t_of_yojson: exception expected", json),
                }
            }
            _ => of_yojson_error("Exit_status.t_of_yojson: unexpected variant", json),
        },
        _ => of_yojson_error("Exit_status.t_of_yojson: list expected", json),
    }
}

/// The JSON of `finale_data` (see the module documentation).
pub fn yojson_of_finale_data(x: &FinaleData) -> yojson::T {
    let utils::Callstack(stack) = &x.stack;
    yojson::T::Assoc(vec![
        ("exit_status".to_string(), yojson_of_t(&x.exit_status)),
        (
            "msg".to_string(),
            match &x.msg {
                None => yojson::T::Null,
                Some(msg) => yojson::T::String(msg.clone()),
            },
        ),
        (
            "stack".to_string(),
            yojson::T::List(vec![
                yojson::T::String("Callstack".to_string()),
                yojson::T::String(stack.clone()),
            ]),
        ),
        (
            "telemetry".to_string(),
            match &x.telemetry {
                None => yojson::T::Null,
                Some(telemetry) => telemetry::to_yojson(telemetry),
            },
        ),
    ])
}

/// `finale_data` from its JSON (see the module documentation). As with
/// `ppx_yojson_conv`, every field must be there once, and no other.
pub fn finale_data_of_yojson(json: &yojson::T) -> Result<FinaleData, String> {
    let fields = match json {
        yojson::T::Assoc(fields) => fields,
        _ => return of_yojson_error("Exit_status.finale_data_of_yojson: object expected", json),
    };
    let mut exit_status = None;
    let mut msg = None;
    let mut stack = None;
    let mut telemetry = None;
    for (name, value) in fields {
        let duplicate = match name.as_str() {
            "exit_status" => exit_status.replace(t_of_yojson(value)?).is_some(),
            "msg" => msg
                .replace(match value {
                    yojson::T::Null => None,
                    yojson::T::String(s) => Some(s.clone()),
                    _ => return of_yojson_error("Exit_status.finale_data_of_yojson: msg", value),
                })
                .is_some(),
            "stack" => stack
                .replace(match value {
                    yojson::T::List(l) => match l.as_slice() {
                        [yojson::T::String(c), yojson::T::String(s)] if c == "Callstack" => {
                            utils::Callstack(s.clone())
                        }
                        _ => {
                            return of_yojson_error(
                                "Exit_status.finale_data_of_yojson: stack",
                                value,
                            );
                        }
                    },
                    _ => {
                        return of_yojson_error("Exit_status.finale_data_of_yojson: stack", value);
                    }
                })
                .is_some(),
            "telemetry" => telemetry
                .replace(match value {
                    yojson::T::Null => None,
                    yojson::T::Assoc(pairs) => {
                        // `telemetry::json` adds a pair as it is: the pairs
                        // come back in the order `to_yojson` gave them.
                        let mut t = telemetry::create();
                        for (key, value) in pairs {
                            t = telemetry::json(key, value.clone(), t);
                        }
                        Some(t)
                    }
                    _ => {
                        return of_yojson_error(
                            "Exit_status.finale_data_of_yojson: telemetry",
                            value,
                        );
                    }
                })
                .is_some(),
            _ => {
                return of_yojson_error("Exit_status.finale_data_of_yojson: extra field", json);
            }
        };
        if duplicate {
            return of_yojson_error("Exit_status.finale_data_of_yojson: duplicate field", json);
        }
    }
    match (exit_status, msg, stack, telemetry) {
        (Some(exit_status), Some(msg), Some(stack), Some(telemetry)) => Ok(FinaleData {
            exit_status,
            msg,
            stack,
            telemetry,
        }),
        _ => of_yojson_error("Exit_status.finale_data_of_yojson: missing field", json),
    }
}

// ~~ OCaml Marshal ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The constant constructors of `Exit_status.t`, in the order of the type:
/// the OCaml integer of each is its index.
pub const CONSTANT_CONSTRUCTORS: [&str; 71] = [
    "No_error",
    "Input_error",
    "Kill_error",
    "No_server_running_should_retry",
    "Out_of_time",
    "Out_of_retries",
    "Server_already_exists",
    "Type_error",
    "Build_id_mismatch",
    "Monitor_connection_failure",
    "Unused_server",
    "Lock_stolen",
    "Lost_parent_monitor",
    "Server_got_eof_from_monitor",
    "Interrupted",
    "Client_broken_pipe",
    "Worker_oomed",
    "Worker_busy",
    "Worker_not_found_exception",
    "Worker_failed_to_send_job",
    "Socket_error",
    "Missing_hhi",
    "Dfind_died",
    "Dfind_unresponsive",
    "EventLogger_Timeout",
    "EventLogger_restart_out_of_retries",
    "EventLogger_broken_pipe",
    "CantRunAI",
    "Watchman_failed",
    "Watchman_fresh_instance",
    "Watchman_invalid_result",
    "Edenfs_watcher_failed",
    "Edenfs_watcher_eden_shutting_down",
    "Edenfs_watcher_lost_changes",
    "Distc_failed",
    "File_provider_stale",
    "Depgraph_unavailable",
    "Hhconfig_deleted",
    "Hhconfig_changed",
    "Package_config_changed",
    "Typecheck_restarted",
    "Typecheck_abandoned",
    "Server_shutting_down_due_to_sigusr2",
    "IDE_malformed_request",
    "IDE_no_server",
    "IDE_out_of_retries",
    "Nfs_root",
    "IDE_init_failure",
    "IDE_typechecker_died",
    "Redecl_heap_overflow",
    "Out_of_shared_memory",
    "Shared_mem_assertion_failure",
    "Hash_table_full",
    "IDE_new_client_connected",
    "Lazy_decl_bug",
    "Decl_heap_elems_bug",
    "Parser_heap_build_error",
    "Heap_full",
    "Sql_assertion_failure",
    "Local_type_env_stale",
    "Sql_cantopen",
    "Sql_corrupt",
    "Sql_misuse",
    "Decl_not_found",
    "Big_rebase_detected",
    "Failed_to_load_should_retry",
    "Failed_to_load_should_abort",
    "Server_non_opt_build_mode",
    "Not_restarting_server_with_precomputed_saved_state",
    "Config_error",
    "Client_bad_args",
];

/// The OCaml value of an `Exit_status.t`.
pub fn t_to_ocaml(t: &T) -> Value {
    match t {
        T::ServerHungUpShouldRetry(finale_data) | T::ServerHungUpShouldAbort(finale_data) => {
            let tag = if matches!(t, T::ServerHungUpShouldRetry(_)) { 0 } else { 1 };
            let arg = match finale_data {
                None => Value::int(0),
                Some(finale_data) => Value::some(to_ocaml(finale_data)),
            };
            Value::block(tag, vec![arg])
        }
        T::UncaughtException(e) => {
            // `exception <ctor string>`: `[| name; id |]` (`Object_tag`); the
            // id of an unmarshalled constructor is not compared with anything.
            let exn = Value::block(
                OBJECT_TAG,
                vec![
                    Value::string(exception::get_ctor_string(e).into_bytes()),
                    Value::int(0),
                ],
            );
            // `{exn; backtrace}`, the raw backtrace an empty array.
            Value::block(2, vec![Value::block(0, vec![exn, Value::block(0, vec![])])])
        }
        _ => {
            let name = constructor_name(t);
            let i = CONSTANT_CONSTRUCTORS
                .iter()
                .position(|c| *c == name)
                .expect("a constant constructor of Exit_status.t");
            Value::int(i as i64)
        }
    }
}

/// `Obj.object_tag`: the tag of an exception constructor.
const OBJECT_TAG: u8 = 248;

/// The OCaml value of a `finale_data`.
pub fn to_ocaml(x: &FinaleData) -> Value {
    let utils::Callstack(stack) = &x.stack;
    Value::block(
        0,
        vec![
            t_to_ocaml(&x.exit_status),
            match &x.msg {
                None => Value::int(0),
                Some(msg) => Value::some(Value::string(msg.as_bytes())),
            },
            Value::block(0, vec![Value::string(stack.as_bytes())]),
            match &x.telemetry {
                None => Value::int(0),
                Some(telemetry) => Value::some(telemetry_to_ocaml(telemetry)),
            },
        ],
    )
}

type R<A> = Result<A, ConvError>;

fn string_of(v: &Value) -> R<String> {
    Ok(String::from_utf8_lossy(v.as_bytes()?).into_owned())
}

fn option_of<A>(v: &Value, f: impl FnOnce(&Value) -> R<A>) -> R<Option<A>> {
    match v {
        Value::Int(0) => Ok(None),
        _ => Ok(Some(f(&v.fields(0, 1)?[0])?)),
    }
}

/// An `Exit_status.t` from its OCaml value.
pub fn t_of_ocaml(v: &Value) -> R<T> {
    match v {
        Value::Int(i) => CONSTANT_CONSTRUCTORS
            .get(*i as usize)
            .and_then(|name| constant_constructor_of_name(name))
            .ok_or_else(|| ConvError(format!("Exit_status.t: constructor {}", i))),
        Value::Ptr(_) => {
            let (tag, fields) = v.as_block()?;
            match (tag, fields) {
                (0 | 1, [arg]) => {
                    let finale_data =
                        option_of(arg, |v| Ok(Box::new(of_ocaml(v)?)))?;
                    Ok(if tag == 0 {
                        T::ServerHungUpShouldRetry(finale_data)
                    } else {
                        T::ServerHungUpShouldAbort(finale_data)
                    })
                }
                (2, [e]) => {
                    let e = e.fields(0, 2)?;
                    Ok(T::UncaughtException(exception::wrap(RecordedException {
                        ctor: printexc_to_string(&e[0])?,
                    })))
                }
                _ => Err(ConvError(format!("Exit_status.t: block of tag {}", tag))),
            }
        }
    }
}

/// `Printexc.to_string` of an unmarshalled exception, with the generic
/// printer (`Printexc.to_string_default` without its special cases): a
/// constructor without arguments is its name, one with arguments
/// `Name(a, b)`, an integer shown with `%d`, a string with `%S`, a float with
/// `string_of_float`, anything else `_`.
fn printexc_to_string(exn: &Value) -> R<String> {
    let (tag, fields) = exn.as_block()?;
    if tag == OBJECT_TAG {
        return string_of(&fields[0]);
    }
    let constructor = match fields.first() {
        Some(c) => string_of(&c.fields(OBJECT_TAG, 2)?[0])?,
        None => return Err(ConvError("an exception".to_string())),
    };
    let field = |f: &Value| -> String {
        match f {
            Value::Int(i) => i.to_string(),
            Value::Ptr(_) => {
                if let Ok(b) = f.as_bytes() {
                    crate::rt::ocaml_printf::sprintf_s(&String::from_utf8_lossy(b))
                } else if let Ok(d) = f.as_double() {
                    let s = format!("{}", d);
                    if s.contains('.') || s.contains('e') || s.contains("inf") || s.contains("NaN") {
                        s
                    } else {
                        format!("{}.", s)
                    }
                } else {
                    "_".to_string()
                }
            }
        }
    };
    let args = &fields[1..];
    Ok(if args.is_empty() {
        constructor
    } else {
        format!(
            "{}({})",
            constructor,
            args.iter().map(field).collect::<Vec<_>>().join(", ")
        )
    })
}

/// A `finale_data` from its OCaml value.
pub fn of_ocaml(v: &Value) -> R<FinaleData> {
    let f = v.fields(0, 4)?;
    Ok(FinaleData {
        exit_status: t_of_ocaml(&f[0])?,
        msg: option_of(&f[1], string_of)?,
        stack: utils::Callstack(string_of(&f[2].fields(0, 1)?[0])?),
        telemetry: option_of(&f[3], telemetry_of_ocaml)?,
    })
}

// `Telemetry.t = (string * Yojson.Safe.t) list`, as the codec of the
// errors file has it (`server_progress::codec`, which is not built without
// the `server` feature).

fn yojson_to_ocaml(j: &yojson::T) -> Value {
    use yojson::T as J;
    let pv = |name: &str, arg: Option<Value>| Value::poly_variant(name, arg);
    let s = |s: &str| Value::string(s.as_bytes());
    match j {
        J::Null => pv("Null", None),
        J::Bool(b) => pv("Bool", Some(Value::bool(*b))),
        J::Int(i) => pv("Int", Some(Value::int(*i as i64))),
        J::Intlit(i) => pv("Intlit", Some(s(i))),
        J::Float(f) => pv("Float", Some(Value::double(*f))),
        J::String(x) => pv("String", Some(s(x))),
        J::Assoc(l) => pv(
            "Assoc",
            Some(Value::list(
                l.iter()
                    .map(|(k, v)| Value::block(0, vec![s(k), yojson_to_ocaml(v)]))
                    .collect::<Vec<_>>(),
            )),
        ),
        J::List(l) => pv(
            "List",
            Some(Value::list(l.iter().map(yojson_to_ocaml).collect::<Vec<_>>())),
        ),
    }
}

fn yojson_of_ocaml(v: &Value) -> R<yojson::T> {
    use yojson::T as J;
    let h = ocaml_marshal::hash_variant;
    match v {
        Value::Int(n) if *n == h("Null") => Ok(J::Null),
        Value::Int(_) => Err(ConvError("a Yojson.Safe.t".to_string())),
        Value::Ptr(_) => {
            let f = v.fields(0, 2)?;
            let tag = f[0].as_int()?;
            let arg = &f[1];
            if tag == h("Bool") {
                Ok(J::Bool(arg.as_int()? != 0))
            } else if tag == h("Int") {
                Ok(J::Int(arg.as_int()? as isize))
            } else if tag == h("Intlit") {
                Ok(J::Intlit(string_of(arg)?))
            } else if tag == h("Float") {
                Ok(J::Float(arg.as_double()?))
            } else if tag == h("String") {
                Ok(J::String(string_of(arg)?))
            } else if tag == h("Assoc") {
                let mut l = vec![];
                for kv in arg.list_items()? {
                    let kv = kv.fields(0, 2)?;
                    l.push((string_of(&kv[0])?, yojson_of_ocaml(&kv[1])?));
                }
                Ok(J::Assoc(l))
            } else if tag == h("List") {
                let l: R<Vec<_>> = arg.list_items()?.into_iter().map(yojson_of_ocaml).collect();
                Ok(J::List(l?))
            } else {
                Err(ConvError("a Yojson.Safe.t that the Rust Yojson has".to_string()))
            }
        }
    }
}

/// The pairs of a telemetry, head (most recent) first.
fn telemetry_to_ocaml(t: &telemetry::T) -> Value {
    let pairs = match telemetry::to_yojson(t) {
        yojson::T::Assoc(l) => l,
        _ => unreachable!("Telemetry.to_yojson is an object"),
    };
    Value::list(
        pairs
            .iter()
            .rev()
            .map(|(k, v)| Value::block(0, vec![Value::string(k.as_bytes()), yojson_to_ocaml(v)]))
            .collect::<Vec<_>>(),
    )
}

fn telemetry_of_ocaml(v: &Value) -> R<telemetry::T> {
    let mut pairs = vec![];
    for kv in v.list_items()? {
        let kv = kv.fields(0, 2)?;
        pairs.push((string_of(&kv[0])?, yojson_of_ocaml(&kv[1])?));
    }
    // `json` conses a pair onto the list: rebuild from the tail.
    let mut t = telemetry::create();
    for (k, v) in pairs.into_iter().rev() {
        t = telemetry::json(&k, v, t);
    }
    Ok(t)
}

/// Writes the finale file, as the exit hook of `Server_main.setup_ipc` does
/// (`Sys_utils.with_umask 0o000 (fun () -> let oc = open_out_bin file in
/// Marshal.to_channel oc finale_data []; close_out oc)`): mode `0o666`,
/// truncated, the `Marshal` of [`to_ocaml`]. The caller ignores the error,
/// as OCaml does.
pub fn write(server_finale_file: &str, finale_data: &FinaleData) -> std::io::Result<()> {
    use std::io::Write;
    let bytes = ocaml_marshal::to_bytes(&to_ocaml(finale_data), &[])
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e.0))?;
    let mut file = ocaml_unix::openfile_with_umask(
        server_finale_file,
        &[
            ocaml_unix::OpenFlag::OWronly,
            ocaml_unix::OpenFlag::OCreat,
            ocaml_unix::OpenFlag::OTrunc,
        ],
        0o666,
        0o000,
    )?;
    file.write_all(&bytes)?;
    file.flush()
}

/// The finale data in the file, `None` if it cannot be read or is not finale
/// data (as `get_finale_data`'s `try ... with _ -> None`).
pub fn read(server_finale_file: &str) -> Option<FinaleData> {
    let contents = std::fs::read(server_finale_file).ok()?;
    let v = ocaml_marshal::from_bytes(&contents, 0).ok()?;
    of_ocaml(&v).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exit_status::show;
    use crate::exit_status::tests::sample_finale_data;

    /// `Failure "boom"`, as `Printexc.to_string` shows it.
    #[derive(Debug)]
    #[allow(dead_code)]
    struct Failure(String);

    #[test]
    fn constructors_round_trip() {
        for t in [
            T::NoError,
            T::TypeError,
            T::ClientBadArgs,
            T::ServerHungUpShouldRetry(None),
            T::NotRestartingServerWithPrecomputedSavedState,
        ] {
            assert_eq!(show(&t_of_yojson(&yojson_of_t(&t)).unwrap()), show(&t));
        }
        assert_eq!(
            yojson::to_string(&yojson_of_t(&T::ServerHungUpShouldAbort(None))),
            r#"["Server_hung_up_should_abort",null]"#
        );
        assert!(t_of_yojson(&yojson::T::String("No_error".to_string())).is_err());
    }

    #[test]
    fn finale_file_round_trip() {
        let dir = std::env::temp_dir().join(format!("hh_finale_test_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("12345.fin");
        let file = file.to_str().unwrap();
        assert!(read(file).is_none());
        let d = sample_finale_data();
        write(file, &d).unwrap();
        {
            // `Sys_utils.with_umask 0o000 (fun () -> open_out_bin ...)`
            use std::os::unix::fs::MetadataExt;
            assert_eq!(std::fs::metadata(file).unwrap().mode() & 0o777, 0o666);
        }
        // `Marshal.to_channel oc finale_data []`
        let expected = Value::block(
            0,
            vec![
                Value::int(38),
                Value::some(Value::string("hh.conf changed")),
                Value::block(0, vec![Value::string("Raised at a.ml")]),
                Value::some(Value::list(vec![
                    Value::block(0, vec![Value::string("b"), Value::poly_variant("Int", Some(Value::int(2)))]),
                    Value::block(0, vec![Value::string("a"), Value::poly_variant("String", Some(Value::string("x")))]),
                ])),
            ],
        );
        assert_eq!(
            std::fs::read(file).unwrap(),
            ocaml_marshal::to_bytes(&expected, &[]).unwrap()
        );
        let back = read(file).unwrap();
        assert_eq!(show(&back.exit_status), "Exit_status.Hhconfig_changed");
        assert_eq!(back.msg.as_deref(), Some("hh.conf changed"));
        assert_eq!(back.stack, d.stack);
        assert_eq!(back.telemetry, d.telemetry);

        // Nested, and an exception.
        let nested = FinaleData {
            exit_status: T::ServerHungUpShouldAbort(Some(Box::new(FinaleData {
                exit_status: T::UncaughtException(exception::wrap(Failure("boom".into()))),
                msg: None,
                stack: utils::Callstack(String::new()),
                telemetry: None,
            }))),
            msg: None,
            stack: utils::Callstack("s".to_string()),
            telemetry: None,
        };
        write(file, &nested).unwrap();
        let back = read(file).unwrap();
        match back.exit_status {
            T::ServerHungUpShouldAbort(Some(inner)) => match inner.exit_status {
                T::UncaughtException(e) => {
                    assert_eq!(exception::get_ctor_string(&e), "Failure(\"boom\")")
                }
                _ => panic!("expected an exception"),
            },
            _ => panic!("expected Server_hung_up_should_abort"),
        }

        // Garbage (or a JSON finale of an older port) is no finale data.
        std::fs::write(file, "garbage").unwrap();
        assert!(read(file).is_none());
        std::fs::write(file, r#"{"exit_status":["Hhconfig_changed"],"msg":null,"stack":["Callstack",""],"telemetry":null}"#).unwrap();
        assert!(read(file).is_none());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn constant_constructors_in_the_order_of_the_type() {
        for (i, name) in CONSTANT_CONSTRUCTORS.iter().enumerate() {
            let t = constant_constructor_of_name(name).unwrap();
            assert_eq!(constructor_name(&t), *name);
            assert_eq!(t_to_ocaml(&t).as_int().unwrap(), i as i64);
        }
        // (The integers of the oracle's files.)
        assert_eq!(t_to_ocaml(&T::ServerShuttingDownDueToSigusr2).as_int().unwrap(), 42);
        assert_eq!(t_to_ocaml(&T::HhconfigChanged).as_int().unwrap(), 38);
    }

    /// Finale files written by the OCaml `hh_server` (8.1.0, macOS): `hh_client
    /// stop` (SIGUSR2), an incompatible change of `.hhconfig`, and two crashes
    /// (a `Failure` with its message, the constant exception
    /// `Watchman_restarted`). The integer of the exit status in the first
    /// two is the one of this version's `Exit_status.t`, one more than
    /// 8.1.0's (which has no `Edenfs_watcher_eden_shutting_down`).
    #[test]
    fn oracle_finale_files() {
        let decode = |bytes: &[u8]| of_ocaml(&ocaml_marshal::from_bytes(bytes, 0).unwrap()).unwrap();
        // The stack of the files is the OCaml's callstack, kept as is: so
        // writing what was read gives the oracle's bytes back.
        for bytes in [
            &include_bytes!("finale/sigusr2.fin")[..],
            &include_bytes!("finale/hhconfig_changed.fin")[..],
        ] {
            let d = decode(bytes);
            assert_eq!(ocaml_marshal::to_bytes(&to_ocaml(&d), &[]).unwrap(), bytes);
        }
        let d = decode(include_bytes!("finale/sigusr2.fin"));
        assert_eq!(show(&d.exit_status), "Exit_status.Server_shutting_down_due_to_sigusr2");
        assert_eq!(
            d.msg.as_deref(),
            Some("Hh_server received a stop signal. This can happen from a large rebase/update")
        );
        assert!(d.stack.0.starts_with("hack/src/utils/core/exception.ml @ 73\n"));
        assert!(d.telemetry.is_none());
        let d = decode(include_bytes!("finale/hhconfig_changed.fin"));
        assert_eq!(show(&d.exit_status), "Exit_status.Hhconfig_changed");
        assert_eq!(d.msg, None);

        let d = decode(include_bytes!("finale/uncaught_failure.fin"));
        match &d.exit_status {
            T::UncaughtException(e) => assert!(
                exception::get_ctor_string(e)
                    .starts_with("Failure(\"No 'cmdline' file found for PID 26885: '(Sys_error \\\"/proc/26885/cmdline")
            ),
            _ => panic!("expected Uncaught_exception"),
        }
        assert!(d.msg.as_deref().unwrap().starts_with("Failure(\"No 'cmdline' file found"));
        let d = decode(include_bytes!("finale/uncaught_watchman_restarted.fin"));
        match &d.exit_status {
            T::UncaughtException(e) => {
                assert_eq!(exception::get_ctor_string(e), "Watchman_sig.Types.Watchman_restarted")
            }
            _ => panic!("expected Uncaught_exception"),
        }
        assert_eq!(d.msg.as_deref(), Some("Watchman_sig.Types.Watchman_restarted"));
    }
}
