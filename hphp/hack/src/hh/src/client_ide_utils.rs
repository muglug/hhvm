// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client/ide_service/client_ide_utils.ml`.
//!
//! The labelled optional arguments are
//! positional (`?data`, `?e`, then the others in the `.ml` order).

use crate::client_ide_message;
use crate::exception;
use crate::hh_logger;
use crate::lsp;
use crate::yojson::safe as yojson;

#[derive(Clone, Debug)]
pub struct Error {
    pub category: String,
    pub data: yojson::T,
}

/// `Exception.get_ctor_string e`, with the payloads that are not strings
/// named as `Printexc.to_string` names them.
pub fn ctor_string(e: &exception::T) -> String {
    let exn = exception::unwrap(e);
    if let Some(e) = exn.downcast_ref::<crate::decl_defs::DeclNotFound>() {
        e.to_string()
    } else if exn.downcast_ref::<crate::worker_cancel::WorkerShouldExit>().is_some() {
        crate::worker_cancel::WorkerShouldExit.to_string()
    } else if let Some(e) = exn.downcast_ref::<lsp::error::LspException>() {
        format!("{:?}", e)
    } else if let Some(e) = exn.downcast_ref::<crate::client_ide_daemon::OutfdWriteError>() {
        e.to_string()
    } else {
        exception::get_ctor_string(e)
    }
}

fn make_error_internal(
    category: &str,
    data: Option<yojson::T>,
    e: Option<&exception::T>,
) -> Error {
    let (category, stack, desc) = match e {
        None => (
            category.to_string(),
            exception::get_current_callstack_string(99),
            String::new(),
        ),
        Some(e) => {
            let backtrace = exception::get_backtrace_string(e);
            let exn = exception::unwrap(e);
            if let Some(crate::decl_defs::DeclNotFound(details)) =
                exn.downcast_ref::<crate::decl_defs::DeclNotFound>()
            {
                (
                    format!("{}: Decl_not_found", category),
                    backtrace,
                    details.clone(),
                )
            } else {
                let ctor = ctor_string(e);
                // `Decl_class.Decl_heap_elems_bug details` is a panic whose
                // message is `Decl_class.Decl_heap_elems_bug("<details>")`.
                match ctor
                    .strip_prefix("Decl_class.Decl_heap_elems_bug(\"")
                    .and_then(|rest| rest.strip_suffix("\")"))
                {
                    Some(details) => (
                        format!("{}: Decl_heap_elems_bug", category),
                        backtrace,
                        details.to_string(),
                    ),
                    None => (format!("{}: {}", category, ctor), backtrace, String::new()),
                }
            }
        }
    };
    let stack = (
        "stack".to_string(),
        yojson::T::String(exception::clean_stack(&stack)),
    );
    let desc = ("desc".to_string(), yojson::T::String(desc));
    let elems = match data {
        None => vec![stack],
        Some(yojson::T::Assoc(elems)) => {
            if elems.iter().any(|(k, _)| k == "stack") {
                elems
            } else {
                let mut all = vec![stack];
                all.extend(elems);
                all
            }
        }
        Some(data) => vec![("data".to_string(), data), stack, desc],
    };
    let data = yojson::T::Assoc(elems);
    Error { category, data }
}

/// `log_bug ?data ?e ~telemetry category`: logs, as an error, an
/// unexpected event (and sends it to telemetry: a no-op in the open-source
/// build).
pub fn log_bug(data: Option<yojson::T>, e: Option<&exception::T>, telemetry: bool, category: &str) {
    let Error { category, data } = make_error_internal(category, data, e);
    hh_logger::error(
        None,
        None,
        &format!("{}\n{}", category, crate::yojson::safe::to_string(&data)),
    );
    // `if telemetry then Hack_event_logger.serverless_ide_bug ~message:category ~data`
    let _ = telemetry;
}

/// `make_rich_error ?data ?e category`
pub fn make_rich_error(
    data: Option<yojson::T>,
    e: Option<&exception::T>,
    category: &str,
) -> client_ide_message::RichError {
    let Error { category, data } = make_error_internal(category, data, e);
    client_ide_message::RichError {
        short_user_message: "failed".to_string(),
        medium_user_message: "Hack IDE support has failed.".to_string(),
        long_user_message: "Hack IDE support has failed.\nThis is unexpected.\nPlease file a bug within your IDE, and try restarting it.".to_string(),
        is_actionable: false,
        category,
        data: Some(data),
    }
}

pub fn to_lsp_error(reason: &client_ide_message::RichError) -> lsp::error::T {
    lsp::error::T {
        code: lsp::error::UnknownErrorCode,
        message: reason.category.clone(),
        data: reason.data.clone(),
    }
}
