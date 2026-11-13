// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `tany_logger_file.ml`. See `hh/PORTING.md`.

use std::io::Write;

use crate::hh_logger;
use crate::tany_logger_common::should_log;
use crate::tany_logger_common::string_of_context_id;
use crate::tany_logger_common::string_of_pos;
use crate::tany_logger_types::*;
use crate::tast_env;
use crate::typing_log;

/// Flattens the structure information about Tanys and writes it out to the
/// logging channel.
fn log_info_to_file_internal(level: isize, info: &Info) {
    let tag = |tag: &str, rest: String| format!("{}[{}]", rest, tag);
    let iftag = |tag: &str, cond: bool, rest: String| {
        if cond {
            format!("{}[{}]", rest, tag)
        } else {
            rest
        }
    };
    let keyedtag = |tag: &str, value: &str, rest: String| format!("{}[{}:{}]", rest, tag, value);
    let opttag = |tag: &str, opt: &Option<String>, rest: String| match opt {
        None => rest,
        Some(value) => keyedtag(tag, value, rest),
    };
    let exp_info_tags = |exp_info: &ExpressionInfo, rest: String| {
        opttag(
            "producer",
            &exp_info.producer,
            iftag("decl_use", exp_info.declaration_usage, rest),
        )
    };
    let param_info_tags = |param_info: &ParameterInfo, rest: String| {
        iftag(
            "variadic",
            param_info.is_variadic,
            iftag("inout", param_info.is_inout, rest),
        )
    };
    let position_tags = |position: &Position, rest: String| match position {
        Position::Parameter(param_info) => param_info_tags(param_info, tag("param", rest)),
        Position::Return => tag("return", rest),
    };
    let decl_info_tags =
        |decl_info: &DeclarationInfo, rest: String| position_tags(&decl_info.position, rest);
    let context_tags = |context: &Context, rest: String| match context {
        Context::Expression(exp_info) => exp_info_tags(exp_info, tag("exp", rest)),
        Context::Declaration(decl_info) => decl_info_tags(decl_info, tag("decl", rest)),
    };
    let common_info_tags = |common_info: &CommonInfo, rest: String| {
        let rest = tag("Tany", rest);
        let rest = iftag("generated", common_info.is_generated, rest);
        let rest = iftag("test", common_info.is_test, rest);
        let rest = keyedtag(
            "context",
            &string_of_context_id(&common_info.context_id),
            rest,
        );
        keyedtag("position", &string_of_pos(&common_info.pos), rest)
    };
    let output = context_tags(
        &info.context,
        common_info_tags(&info.common_info, String::new()),
    );
    if level > 1 {
        hh_logger::log(&output)
    } else {
        let line = format!("{}\n", output);
        typing_log::out_channel.with(|oc| {
            let mut oc = oc.borrow_mut();
            if let Err(e) = oc.write_all(line.as_bytes()) {
                panic!("Sys_error: {}", e)
            }
            if let Err(e) = oc.flush() {
                panic!("Sys_error: {}", e)
            }
        })
    }
}

pub fn log_info_to_file(env: &tast_env::Env, info: &Info) {
    let log_level_opt = tast_env::get_tcopt(env).log_levels.get("tany").copied();
    match log_level_opt {
        Some(level) if should_log(level, LogMask::File) => log_info_to_file_internal(level, info),
        _ => {}
    }
}
