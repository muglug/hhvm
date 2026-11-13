// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! The finale file `<tmp>/<pid>.fin` (`Server_files.server_finale_file`):
//! what a server leaves behind when it exits in a controlled way, read back
//! by `Exit_status.get_finale_data` so that a client can print "Hack server
//! disconnected suddenly [<status>]" (design 7.3).
//!
//! OCaml writes it with `Marshal.to_channel oc finale_data []` in the exit
//! hook of `Server_main.setup_ipc` and reads it with `Marshal.from_channel`.
//! Here it is JSON, written compact by [`write`] and read by [`read`]. The
//! encoding follows `ppx_yojson_conv`: a constructor of `Exit_status.t` is
//! `["Type_error"]` or `["Server_hung_up_should_retry", <finale_data or
//! null>]`, the record an object with its fields in order, `Utils.Callstack
//! s` is `["Callstack", s]`, an absent option `null`, the telemetry its
//! `Telemetry.to_yojson`. `Exception.t` has no converter: `Uncaught_exception
//! e` is `["Uncaught_exception", {"ctor": <Exception.get_ctor_string e>,
//! "backtrace": <Exception.get_backtrace_string e>}]`; read back, it is an
//! exception whose constructor string is `ctor` (the backtrace of an
//! `exception::T` is the one captured when it is made, so the recorded one is
//! not restored; `Exit.exit` puts it in the finale's `stack` anyway).

use std::fmt;

use crate::exception;
use crate::exit_status::FinaleData;
use crate::exit_status::T;
use crate::exit_status::constant_constructor_of_name;
use crate::exit_status::constructor_name;
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

/// Writes the finale file, as the exit hook of `Server_main.setup_ipc` does
/// (`Sys_utils.with_umask 0o000 (fun () -> let oc = open_out_bin file in
/// Marshal.to_channel oc finale_data []; close_out oc)`): mode `0o666`,
/// truncated, the JSON of [`yojson_of_finale_data`]. The caller ignores the
/// error, as OCaml does.
pub fn write(server_finale_file: &str, finale_data: &FinaleData) -> std::io::Result<()> {
    use std::io::Write;
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
    file.write_all(yojson::to_string(&yojson_of_finale_data(finale_data)).as_bytes())?;
    file.flush()
}

/// The finale data in the file, `None` if it cannot be read or is not finale
/// data (as `get_finale_data`'s `try ... with _ -> None`).
pub fn read(server_finale_file: &str) -> Option<FinaleData> {
    let contents = std::fs::read_to_string(server_finale_file).ok()?;
    let json = yojson::from_string(&contents).ok()?;
    finale_data_of_yojson(&json).ok()
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
        assert_eq!(
            std::fs::read_to_string(file).unwrap(),
            r#"{"exit_status":["Hhconfig_changed"],"msg":"hh.conf changed","stack":["Callstack","Raised at a.ml"],"telemetry":{"a":"x","b":2}}"#
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

        // Garbage is no finale data.
        std::fs::write(file, "garbage").unwrap();
        assert!(read(file).is_none());
        std::fs::write(file, r#"{"exit_status":["Nope"],"msg":null,"stack":["Callstack",""],"telemetry":null}"#).unwrap();
        assert!(read(file).is_none());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
