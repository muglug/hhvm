// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/exit.ml`. See `hh/PORTING.md`.

#![allow(non_upper_case_globals)]

use std::sync::Mutex;

use crate::exception;
use crate::exit_status;
use crate::telemetry;
use crate::utils;

type Hook = Box<dyn Fn(&exit_status::FinaleData) + Send>;

/// The hooks, the one added last first (OCaml conses them onto its list).
static hook_upon_clean_exit: Mutex<Vec<Hook>> = Mutex::new(Vec::new());

pub fn add_hook_upon_clean_exit(hook: impl Fn(&exit_status::FinaleData) + Send + 'static) {
    hook_upon_clean_exit
        .lock()
        .unwrap()
        .insert(0, Box::new(hook));
}

/// Runs the hooks with the finale data of `exit_status` (a hook that raises
/// is ignored), then exits with its code.
pub fn exit(
    msg: Option<String>,
    telemetry: Option<telemetry::T>,
    stack: Option<String>,
    exit_status: exit_status::T,
) -> ! {
    // is there additional inforamtion in exit_status to pick up?
    let (emsg, estack) = match &exit_status {
        exit_status::T::UncaughtException(e) => (
            Some(exception::get_ctor_string(e)),
            Some(exception::clean_stack(&exception::get_backtrace_string(e))),
        ),
        exit_status::T::ServerHungUpShouldAbort(Some(finale_data))
        | exit_status::T::ServerHungUpShouldRetry(Some(finale_data)) => {
            let exit_status::FinaleData {
                exit_status,
                stack: utils::Callstack(stack),
                ..
            } = &**finale_data;
            (Some(exit_status::show(exit_status)), Some(stack.clone()))
        }
        _ => (None, None),
    };
    let stack = stack
        .unwrap_or_else(|| exception::clean_stack(&exception::get_current_callstack_string(99)));
    let stack = match estack {
        None => stack,
        Some(estack) => format!("{}\n\n{}", stack, estack),
    };
    // `Option.first_some msg emsg`
    let msg = msg.or(emsg);
    let server_finale_data = exit_status::FinaleData {
        exit_status,
        msg,
        stack: utils::Callstack(stack),
        telemetry,
    };
    for hook in hook_upon_clean_exit.lock().unwrap().iter() {
        let _ =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| hook(&server_finale_data)));
    }
    let exit_code = exit_status::exit_code(&server_finale_data.exit_status);
    // `Stdlib.exit` flushes the standard channels first (and then exits even
    // if that fails).
    {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
    }
    std::process::exit(exit_code as i32)
}
