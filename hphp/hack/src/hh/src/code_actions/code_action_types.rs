// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_action_types/code_action_types.ml`.
//! See `hh/PORTING.md`.
//!
//! Internal representations for code actions for refactoring.
//!
//! `edits Lazy.t` is a [`LazyEdits`]: a closure that computes the edits,
//! called at most once (when the code action is resolved). JSON is
//! `Yojson.Safe.t` (`crate::yojson::safe::T`).

use std::collections::BTreeMap;

use crate::pos::Absolute;
use crate::pos::Pos;
use crate::relative_path::RelativePath;
use crate::tast_env;
use crate::typing_defs::Ty;
use crate::yojson::safe as yojson;

type Json = yojson::T;

#[derive(Clone, Debug, PartialEq)]
pub struct Edit {
    pub pos: Pos,
    pub text: String,
}

/// `edit list Relative_path.Map.t`
pub type Edits = BTreeMap<RelativePath, Vec<Edit>>;

/// `Relative_path.Map.singleton path edits`
pub fn singleton(path: RelativePath, edits: Vec<Edit>) -> Edits {
    let mut m = BTreeMap::new();
    m.insert(path, edits);
    m
}

/// `edits Lazy.t`
pub type LazyEdits<'a> = Box<dyn FnOnce() -> Edits + 'a>;

/// Data common to [Refactor] and [Quickfix] kind code actions
pub struct EditData<'a> {
    /// Title of the code action, as displayed by VSCode
    pub title: String,
    /// Series of edits that will be applied
    pub edits: LazyEdits<'a>,
    /// Text that will be selected after the edits are applied. If [None]
    /// the cursor is not updated after applying the edits.
    pub selection: Option<Pos>,
    /// Whether or not to trigger the inline-suggest functionality in VSCode
    /// after inserting the edits and (optionally) changing the selection.
    pub trigger_inline_suggest: bool,
}

/// `type refactor = Refactor of edit_data [@@ocaml.unboxed]`
pub struct Refactor<'a>(pub EditData<'a>);

/// `type quickfix = Quickfix of edit_data [@@ocaml.unboxed]`
pub struct Quickfix<'a>(pub EditData<'a>);

/// `List.filter_opt` of the optional fields of an object
fn assoc_opt(fields: Vec<Option<(&str, Json)>>) -> Json {
    Json::Assoc(
        fields
            .into_iter()
            .flatten()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}

fn string(s: &str) -> Json {
    Json::String(s.to_string())
}

pub mod show_sidebar_chat_command_args {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct MessageAttachment {
        pub title: String,
        pub value: String,
    }

    pub fn message_attachment_to_json(MessageAttachment { title, value }: &MessageAttachment) -> Json {
        Json::Assoc(vec![
            ("title".to_string(), string(title)),
            ("value".to_string(), string(value)),
        ])
    }

    #[derive(Clone, Copy, Debug)]
    pub enum MessageModel {
        Gpt4,
        Illama,
        IcodellamaTest,
        Icodellama405b,
        Claude37Sonnet,
    }

    pub fn message_model_to_json(m: &MessageModel) -> Json {
        string(match m {
            MessageModel::Gpt4 => "GPT4",
            MessageModel::Illama => "ILLAMA",
            MessageModel::IcodellamaTest => "ICODELLAMA_TEST",
            MessageModel::Icodellama405b => "ICODELLAMA_405B",
            MessageModel::Claude37Sonnet => "CLAUDE_37_SONNET",
        })
    }

    #[derive(Clone, Copy, Debug)]
    pub enum Action {
        /// Chat (user triggered)
        Chat,
        /// Code action
        Code,
        /// Devmate
        Devmate,
        /// An example prompt
        Example,
    }

    pub fn action_to_json(a: &Action) -> Json {
        string(match a {
            Action::Chat => "CHAT",
            Action::Code => "CODE",
            Action::Devmate => "DEVMATE",
            Action::Example => "EXAMPLE",
        })
    }

    #[derive(Clone, Copy, Debug)]
    pub enum ActionTriggerType {
        CodeAction,
        ContextMenu,
        ExamplePrompt,
        DiagnosticHover,
        SlashCommand,
        CodeLens,
    }

    pub fn action_trigger_type_to_json(t: &ActionTriggerType) -> Json {
        string(match t {
            ActionTriggerType::CodeAction => "CodeAction",
            ActionTriggerType::ContextMenu => "ContextMenu",
            ActionTriggerType::ExamplePrompt => "ExamplePrompt",
            ActionTriggerType::DiagnosticHover => "DiagnosticHover",
            ActionTriggerType::SlashCommand => "SlashCommand",
            ActionTriggerType::CodeLens => "CodeLens",
        })
    }

    #[derive(Clone, Copy, Debug)]
    pub enum LlmConfigModel {
        G4,
        IcodellamaTest,
        Icodellama405b,
        Claude37Sonnet,
    }

    pub fn llm_config_model_to_json(m: &LlmConfigModel) -> Json {
        string(match m {
            LlmConfigModel::G4 => "g4",
            LlmConfigModel::IcodellamaTest => "icodellama-test",
            LlmConfigModel::Icodellama405b => "icodellama-405b",
            LlmConfigModel::Claude37Sonnet => "claude3.7-sonnet",
        })
    }

    #[derive(Clone, Debug)]
    pub struct ToolCallResultsType {
        pub tool_call_id: String,
        pub tool_name: String,
        pub arguments: String,
        pub output: String,
    }

    pub fn tool_call_results_type_to_json(t: &ToolCallResultsType) -> Json {
        Json::Assoc(vec![
            ("tool_call_id".to_string(), string(&t.tool_call_id)),
            ("tool_name".to_string(), string(&t.tool_name)),
            ("arguments".to_string(), string(&t.arguments)),
            ("output".to_string(), string(&t.output)),
        ])
    }

    #[derive(Clone, Debug)]
    pub struct ModelParams {
        pub model: Option<LlmConfigModel>,
        pub max_tokens: Option<isize>,
        pub temperature: Option<f64>,
        pub top_p: Option<f64>,
        pub stop: Option<Vec<String>>,
        pub repetition_penalty: Option<f64>,
    }

    pub fn model_params_to_json(p: &ModelParams) -> Json {
        assoc_opt(vec![
            p.model.as_ref().map(|m| ("model", llm_config_model_to_json(m))),
            p.max_tokens.map(|n| ("max_tokens", Json::Int(n))),
            p.temperature.map(|t| ("temperature", Json::Float(t))),
            p.top_p.map(|t| ("top_p", Json::Float(t))),
            p.stop
                .as_ref()
                .map(|stop| ("stop", Json::List(stop.iter().map(|s| string(s)).collect()))),
            p.repetition_penalty
                .map(|r| ("repetition_penalty", Json::Float(r))),
        ])
    }

    #[derive(Clone, Debug)]
    pub struct LlmConfig {
        pub pipeline: Option<String>,
        pub label: Option<String>,
        pub model_params: Option<ModelParams>,
        pub max_input_token: Option<isize>,
    }

    pub fn llm_config_to_json(c: &LlmConfig) -> Json {
        assoc_opt(vec![
            c.pipeline.as_ref().map(|p| ("pipeline", string(p))),
            c.label.as_ref().map(|l| ("label", string(l))),
            c.model_params
                .as_ref()
                .map(|p| ("model_params", model_params_to_json(p))),
            c.max_input_token.map(|n| ("max_input_token", Json::Int(n))),
        ])
    }

    #[derive(Clone, Debug)]
    pub struct T {
        /// The prompt written by/to be displayed to the user.
        pub display_prompt: String,
        /// The actual prompt that will be sent to the LLM.
        pub model_prompt: Option<String>,
        /// Override the default LLM config for this prompt.
        pub llm_config: Option<LlmConfig>,
        pub model: Option<MessageModel>,
        pub attachments: Option<Vec<MessageAttachment>>,
        /// The action that triggered this prompt.
        pub action: Action,
        /// Where this prompt was triggered from.
        pub trigger: Option<String>,
        /// The type of action that triggered this prompt.
        pub trigger_type: Option<ActionTriggerType>,
        /// The results of the local tool calls run.
        pub local_tool_results: Option<ToolCallResultsType>,
        /// The unique identifier for this request provided from the calling language server
        pub correlation_id: Option<String>,
    }

    pub fn to_json(t: &T) -> Json {
        assoc_opt(vec![
            Some(("displayPrompt", string(&t.display_prompt))),
            t.model_prompt.as_ref().map(|p| ("modelPrompt", string(p))),
            t.llm_config
                .as_ref()
                .map(|c| ("llmConfig", llm_config_to_json(c))),
            t.model.as_ref().map(|m| ("model", message_model_to_json(m))),
            t.attachments.as_ref().map(|a| {
                (
                    "attachments",
                    Json::List(a.iter().map(message_attachment_to_json).collect()),
                )
            }),
            Some(("action", action_to_json(&t.action))),
            t.trigger.as_ref().map(|s| ("trigger", string(s))),
            t.trigger_type
                .as_ref()
                .map(|tt| ("triggerType", action_trigger_type_to_json(tt))),
            t.local_tool_results
                .as_ref()
                .map(|r| ("localToolResults", tool_call_results_type_to_json(r))),
            t.correlation_id
                .as_ref()
                .map(|c| ("correlationId", string(c))),
        ])
    }
}

pub mod show_inline_chat_command_args {
    use super::*;

    #[derive(Clone, Copy, Debug)]
    pub enum Model {
        Gpt4o,
        Sonnet37,
        Code31,
        Llama405b,
    }

    pub fn model_to_json(m: &Model) -> Json {
        string(match m {
            Model::Gpt4o => "GPT-4o",
            Model::Sonnet37 => "Claude 3.7 Sonnet",
            Model::Code31 => "iCodeLlama 3.1 70B",
            Model::Llama405b => "iCodeLlama 3.1 405B",
        })
    }

    #[derive(Clone, Debug)]
    pub struct PredefinedPrompt {
        pub command: String,
        pub display_prompt: String,
        pub user_prompt: String,
        pub description: Option<String>,
        pub rules: Option<String>,
        pub task: Option<String>,
        pub prompt_template: Option<String>,
        pub model: Option<Model>,
        pub add_diagnostics: Option<bool>,
    }

    pub fn predefined_prompt_to_json(p: &PredefinedPrompt) -> Json {
        let field_opt = |name: &str, s: &Option<String>| s.as_ref().map(|s| (name.to_string(), string(s)));
        let mut fields = vec![
            ("command".to_string(), string(&p.command)),
            ("displayPrompt".to_string(), string(&p.display_prompt)),
            ("userPrompt".to_string(), string(&p.user_prompt)),
        ];
        fields.extend(
            vec![
                field_opt("description", &p.description),
                field_opt("rules", &p.rules),
                field_opt("task", &p.task),
                field_opt("promptTemplate", &p.prompt_template),
                p.model.as_ref().map(|m| ("model".to_string(), model_to_json(m))),
                p.add_diagnostics
                    .map(|b| ("addDiagnostics".to_string(), Json::Bool(b))),
            ]
            .into_iter()
            .flatten(),
        );
        Json::Assoc(fields)
    }

    #[derive(Clone, Debug)]
    pub struct T {
        pub entrypoint: String,
        pub predefined_prompt: PredefinedPrompt,
        pub override_selection: Absolute,
        pub webview_start_line: isize,
        pub extras: Json,
    }

    pub fn to_json(t: &T) -> Json {
        Json::Assoc(vec![
            ("entrypoint".to_string(), string(&t.entrypoint)),
            (
                "predefinedPrompt".to_string(),
                predefined_prompt_to_json(&t.predefined_prompt),
            ),
            (
                "overrideSelection".to_string(),
                crate::lsp_fmt::print_range(&crate::lsp_helpers::hack_pos_to_lsp_range(
                    |a: &String, b: &String| a == b,
                    &t.override_selection,
                )),
            ),
            ("webviewStartLine".to_string(), Json::Int(t.webview_start_line)),
            ("extras".to_string(), t.extras.clone()),
        ])
    }
}

pub enum CommandArgs {
    ShowInlineChat(show_inline_chat_command_args::T),
    ShowSidebarChat(show_sidebar_chat_command_args::T),
}

pub struct Command {
    pub title: String,
    pub command_args: CommandArgs,
}

/// Internal representation for code actions in our language server,
/// distinct from Lsp.CodeAction and from quickfixes in Quickfixes.ml
pub enum T<'a> {
    RefactorAction(EditData<'a>),
    QuickfixAction(EditData<'a>),
    CommandAction(Command),
}

/// `type find_refactor = entry:Provider_context.entry -> Pos.t -> Provider_context.t -> refactor list`
pub type FindRefactor = for<'a> fn(
    &'a std::sync::Arc<crate::provider_context::Entry>,
    &Pos,
    &'a crate::provider_context::T,
) -> Vec<Refactor<'a>>;

/// `type find_quickfix`
pub type FindQuickfix = for<'a> fn(
    &'a std::sync::Arc<crate::provider_context::Entry>,
    &Pos,
    &'a crate::provider_context::T,
    &crate::tast_provider::ErrorFilter,
) -> Vec<Quickfix<'a>>;

/// A representation of a type for use in code generated by code actions.
/// `to_string` produces "as useful as possible" Hack source code:
///     - fully expand types
///     - avoid truncating types (especially important for nested shapes)
///     - *do* emit non-denotable types like unions. Then we can at least give the user a starting-point for
///     writing source code: a single union in a shape type shouldn't prevent us from providing most of the shape type for the user.
pub mod type_string {
    use std::cell::OnceCell;

    use super::*;
    use crate::type_mapper_generic::DeepTypeMapper;
    use crate::typing_defs_core;
    use crate::typing_defs_core::Ty_;
    use crate::typing_reason::T as Reason;

    /// `string Lazy.t`
    pub struct T {
        value: OnceCell<String>,
        thunk: std::cell::Cell<Option<(tast_env::Env, Ty)>>,
    }

    /// 'like types' are encoded as the union of a static type with [Tdynamic]
    /// so we can remove them by filtering out [Tdynamic] from the types contained
    /// in such a [Tunion]. We _shouldn't_ encounter the degenerate union cases
    /// [Tunion [Tdynamic]] or [Tunion [Tdynamic, ..., Tdynamic]] since they
    /// should have been simplified but we check for this just in case
    ///
    /// (`transform_ty_ty` with a top-down `on_ctor_ty__Tunion` that
    /// continues: every union, at every depth.)
    fn deep_strip_like_types(ty: Ty) -> Ty {
        struct Strip;
        impl DeepTypeMapper<()> for Strip {
            fn on_tunion(&mut self, env: &mut (), r: Reason, tys: Vec<Ty>) -> Ty {
                let is_not_dynamic = |ty: &Ty| !matches!(typing_defs_core::get_node(ty), Ty_::Tdynamic(_));
                let filtered: Vec<Ty> = tys.iter().filter(|ty| is_not_dynamic(ty)).cloned().collect();
                let tys = if filtered.is_empty() { tys } else { filtered };
                let tys = tys.into_iter().map(|ty| self.on_type(env, ty)).collect();
                typing_defs_core::mk((r, Ty_::Tunion(tys)))
            }
        }
        Strip.on_type(&mut (), ty)
    }

    /// Don't truncate types in printing unless they are really big,
    /// so we almost always generate valid code.
    /// The number is somewhat arbitrary: it's the smallest power of 2
    /// that could print without truncation for
    /// extract_shape_type_13.php in our test suite.
    /// We *do* want to truncate at some finite number so editors can
    /// handle that much text.
    const LOTS_OF_TYPING_PRINT_FUEL: isize = 2048;

    pub fn of_locl_ty(tast_env: &tast_env::Env, locl_ty: Ty) -> T {
        T {
            value: OnceCell::new(),
            thunk: std::cell::Cell::new(Some((tast_env.clone(), locl_ty))),
        }
    }

    fn compute(tast_env: tast_env::Env, locl_ty: Ty) -> String {
        let mut typing_env = tast_env.clone();
        crate::typing_env::map_tcopt(&mut typing_env, |mut tcopt| {
            tcopt.tco_type_printer_fuel = LOTS_OF_TYPING_PRINT_FUEL;
            tcopt
        });
        let ty = tast_env::fully_expand(&tast_env, locl_ty);
        let ty = deep_strip_like_types(ty);
        crate::typing_print::full_strip_ns(true, &typing_env, &ty)
    }

    /// `Lazy.force`
    pub fn to_string(t: &T) -> String {
        t.value
            .get_or_init(|| {
                let (env, ty) = t.thunk.take().expect("Lazy.force: forced twice");
                compute(env, ty)
            })
            .clone()
    }
}

#[cfg(test)]
mod tests {
    use super::show_inline_chat_command_args as inline;
    use super::show_sidebar_chat_command_args as sidebar;
    use super::*;

    /// The JSON of the code-action commands spells the models and actions
    /// as the OCaml does, not as the Rust variants.
    #[test]
    fn model_and_action_json() {
        let s = |j: Json| match j {
            Json::String(s) => s,
            j => panic!("{:?}", j),
        };
        use sidebar::MessageModel as M;
        for (m, name) in [
            (M::Gpt4, "GPT4"),
            (M::Illama, "ILLAMA"),
            (M::IcodellamaTest, "ICODELLAMA_TEST"),
            (M::Icodellama405b, "ICODELLAMA_405B"),
            (M::Claude37Sonnet, "CLAUDE_37_SONNET"),
        ] {
            assert_eq!(s(sidebar::message_model_to_json(&m)), name);
        }
        use sidebar::LlmConfigModel as L;
        for (m, name) in [
            (L::G4, "g4"),
            (L::IcodellamaTest, "icodellama-test"),
            (L::Icodellama405b, "icodellama-405b"),
            (L::Claude37Sonnet, "claude3.7-sonnet"),
        ] {
            assert_eq!(s(sidebar::llm_config_model_to_json(&m)), name);
        }
        use sidebar::Action as A;
        for (a, name) in [
            (A::Chat, "CHAT"),
            (A::Code, "CODE"),
            (A::Devmate, "DEVMATE"),
            (A::Example, "EXAMPLE"),
        ] {
            assert_eq!(s(sidebar::action_to_json(&a)), name);
        }
        use inline::Model as I;
        for (m, name) in [
            (I::Gpt4o, "GPT-4o"),
            (I::Sonnet37, "Claude 3.7 Sonnet"),
            (I::Code31, "iCodeLlama 3.1 70B"),
            (I::Llama405b, "iCodeLlama 3.1 405B"),
        ] {
            assert_eq!(s(inline::model_to_json(&m)), name);
        }
    }
}
