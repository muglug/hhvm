// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_command.ml`. See `hh/PORTING.md`.

use crate::client_decompress_zhhdg;
use crate::client_download_saved_state;
use crate::client_env;
use crate::client_lsp;
use crate::client_rage;
use crate::client_start;
use crate::client_stop;

/// Heavy commands should be run from www and provide a root.
/// They can benefit from logging and config parsing
#[derive(Clone, Debug)]
pub enum HeavyCommand {
    CCheck(client_env::ClientCheckEnv),
    CStart(client_start::Env),
    CStop(client_stop::Env),
    CRestart(client_start::Env),
    CLsp(client_lsp::Args),
    CSavedStateProjectMetadata(client_env::ClientCheckEnv),
    CDownloadSavedState(client_download_saved_state::Env),
    CRage(client_rage::Env),
}

/// Light commands should not use any of the following
/// - Hh_logger, HackEventLogger
/// - configs
/// - root or relative paths
#[derive(Clone, Debug)]
pub enum LightCommand {
    CDecompressZhhdg(client_decompress_zhhdg::Env),
}

#[derive(Clone, Debug)]
pub enum Command {
    WithConfig(HeavyCommand),
    WithoutConfig(LightCommand),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommandKeyword {
    CKCheck,
    CKStart,
    CKStop,
    CKRestart,
    CKNone,
    CKLsp,
    CKSavedStateProjectMetadata,
    CKDownloadSavedState,
    CKRage,
    CKDecompressZhhdg,
}

pub fn get_custom_telemetry_data(command: &HeavyCommand) -> Vec<(String, String)> {
    match command {
        HeavyCommand::CCheck(client_env::ClientCheckEnv {
            custom_telemetry_data,
            ..
        })
        | HeavyCommand::CStart(client_start::Env {
            custom_telemetry_data,
            ..
        })
        | HeavyCommand::CRestart(client_start::Env {
            custom_telemetry_data,
            ..
        }) => custom_telemetry_data.clone(),
        HeavyCommand::CStop(_)
        | HeavyCommand::CLsp(_)
        | HeavyCommand::CSavedStateProjectMetadata(_)
        | HeavyCommand::CDownloadSavedState(_)
        | HeavyCommand::CRage(_) => vec![],
    }
}

pub fn command_name(keyword: CommandKeyword) -> &'static str {
    match keyword {
        CommandKeyword::CKCheck => "check",
        CommandKeyword::CKStart => "start",
        CommandKeyword::CKStop => "stop",
        CommandKeyword::CKRestart => "restart",
        CommandKeyword::CKLsp => "lsp",
        CommandKeyword::CKSavedStateProjectMetadata => "saved-state-project-metadata",
        CommandKeyword::CKDownloadSavedState => "download-saved-state",
        CommandKeyword::CKRage => "rage",
        CommandKeyword::CKDecompressZhhdg => "decompress-zhhdg",
        CommandKeyword::CKNone => "",
    }
}

pub fn name_camel_case_heavy(command: &HeavyCommand) -> &'static str {
    match command {
        HeavyCommand::CCheck(_) => "Check",
        HeavyCommand::CStart(_) => "Start",
        HeavyCommand::CStop(_) => "Stop",
        HeavyCommand::CRestart(_) => "Restart",
        HeavyCommand::CLsp(_) => "Lsp",
        HeavyCommand::CSavedStateProjectMetadata(_) => "SavedStateProjectMetadata",
        HeavyCommand::CDownloadSavedState(_) => "DownloadSavedState",
        HeavyCommand::CRage(_) => "Rage",
    }
}

pub fn name_camel_case_light(command: &LightCommand) -> &'static str {
    match command {
        LightCommand::CDecompressZhhdg(_) => "DecompressZhhdg",
    }
}
