// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of
//! `client/ide_service/code_actions_services/code_actions_commands.ml`.
//!
//! Owned by **F8** (plan §7.3). Created empty by W0b.
//!
//! Ported by F7 (the commands of the diagnostics under the selection are
//! listed by every `--ide-code-actions` test with an error), with
//! `Simplihack_prompt.find` (no Rust module yet) as a private module.

use std::sync::Arc;

use bstr::BString;

use super::code_action_types as cat;
use super::code_action_types::show_inline_chat_command_args as sic;
use super::code_action_types::show_sidebar_chat_command_args as ssc;
use crate::diagnostics_state;
use crate::extended_diagnostic_formatter;
use crate::pos::Absolute;
use crate::pos::Pos;
use crate::provider_context;
use crate::tast;
use crate::tast_provider;
use crate::tast_with_dynamic;
use crate::user_diagnostic;
use crate::yojson::safe as yojson;

type FinalizedDiagnostic = user_diagnostic::T<Absolute, Absolute>;

// -- Context helpers -------------------------------------------------------
fn is_subtyping_error(code: isize) -> bool {
    (4000..5000).contains(&code)
}

const MAX_FILE_CONTENT_LINES: isize = 400;

const CURSOR_L: &str = "[DIAGNOSTIC_START]";

const CURSOR_R: &str = "[DIAGNOSTIC_END]";

/// `String.prefix s n`
fn prefix(s: &[u8], n: isize) -> &[u8] {
    let n = n.clamp(0, s.len() as isize) as usize;
    &s[..n]
}

/// `String.drop_prefix s n`
fn drop_prefix(s: &[u8], n: isize) -> &[u8] {
    let n = n.clamp(0, s.len() as isize) as usize;
    &s[n..]
}

/// `String.slice s start stop` (Core: a `stop` of 0 is the length, negative
/// indices count from the end; out of bounds raises).
fn slice(s: &[u8], start: isize, stop: isize) -> &[u8] {
    let len = s.len() as isize;
    let norm = |i: isize| if i < 0 { len + i } else { i };
    let start = norm(start);
    let stop = if stop == 0 { len } else { norm(stop) };
    if start < 0 || stop > len || start > stop {
        panic!("Invalid_argument(\"String.sub / Bytes.sub\")")
    }
    &s[start as usize..stop as usize]
}

/// `Char.is_whitespace` of Core
fn is_whitespace(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | b'\x0b' | b'\x0c' | b'\r')
}

fn extract_prompt_context(buf: &mut Vec<u8>, ctxt_pos: &Absolute, claim_pos: &Absolute) {
    let path = crate::pos::filename(ctxt_pos);
    let ctxt_start_ln = crate::pos::line(ctxt_pos) - 1;
    let ctxt_end_ln = crate::pos::end_line(ctxt_pos) - 1;
    let (start_ln, end_ln, start_col, end_col) = {
        let (start_ln, end_ln, start_col, end_col) = crate::pos::info_pos_extended(claim_pos);
        (start_ln - 1, end_ln - 1, start_col - 1, end_col - 1)
    };
    let line_num_width = 1 + end_ln.to_string().len();
    for (ln, str) in diagnostics_state::read_lines(&path).iter().enumerate() {
        let ln = ln as isize;
        let str = str.as_bytes();
        if ln < ctxt_start_ln || ln > ctxt_end_ln {
            // This line isn't in our containing span so skip it
        } else if (ln == ctxt_start_ln || ln == ctxt_end_ln) && str.iter().all(|c| is_whitespace(*c)) {
            // If the line is blank and is either the first of last line, skip it
        } else {
            // First write the line number and gutter marker
            let ln_num = format!("{:>width$}", (ln + 1).to_string(), width = line_num_width);
            buf.extend_from_slice(ln_num.as_bytes());
            buf.extend_from_slice(b" | ");
            let is_start = ln == start_ln;
            let is_end = ln == end_ln;
            if is_start && is_end {
                // If our target pos starts and ends on the line..
                //   - write the prefix before the start of the marked pos
                //   - write the lhs cursor marker
                //   - write the marked string
                //   - write the rhs cursor marker
                //   - write the suffix after the end of the marked pos
                buf.extend_from_slice(prefix(str, start_col));
                buf.extend_from_slice(CURSOR_L.as_bytes());
                buf.extend_from_slice(slice(str, start_col, end_col + 1));
                buf.extend_from_slice(CURSOR_R.as_bytes());
                buf.extend_from_slice(drop_prefix(str, end_col + 1));
            } else if is_start {
                // If this is the start line, write the prefix, the lhs cursor and
                // substring of the marked pos that is on this line
                buf.extend_from_slice(prefix(str, start_col));
                buf.extend_from_slice(CURSOR_L.as_bytes());
                buf.extend_from_slice(drop_prefix(str, start_col));
            } else if is_end {
                // If this is the end line, write the substring of the marked pos
                // that is on the line, the rhs cursor and the suffix
                buf.extend_from_slice(prefix(str, end_col));
                buf.extend_from_slice(CURSOR_R.as_bytes());
                buf.extend_from_slice(drop_prefix(str, end_col));
            } else {
                // Either the whole line is part of the target pos or the target
                // is not on the line at all; either way, write the entire line
                buf.extend_from_slice(str)
            }
            buf.extend_from_slice(b"\n");
        }
    }
}

fn user_prompt_prefix(buf: &mut Vec<u8>, ctxt_pos: &Absolute, user_error: &FinalizedDiagnostic) {
    let claim_pos = user_diagnostic::claim_message(user_error).0;
    buf.extend_from_slice(
        b"The following snippet of Hack code contains a subtyping error. Line numbers have been inlucded for your reference.",
    );
    buf.extend_from_slice(
        b"You should focus on this code when suggesting a fix and ignore what the user has selected:\n<SNIPPET>\n```hack\n",
    );
    extract_prompt_context(buf, ctxt_pos, &claim_pos);
    buf.extend_from_slice(b"```\n</SNIPPET>\n")
}

fn user_prompt_suffix(buf: &mut Vec<u8>) {
    buf.extend_from_slice(
        b"Edit the code contained in the <SNIPPET> in a way that would fix the error. The suggested edit should be valid Hack code and shouldn't contain line numbers shown in the diagnostic message.\n",
    );
    buf.extend_from_slice(
        b"If there are multiple ways to fix this issue, please return in the code section the most strightforward one that is part of <SNIPPET>, any further suggestions can be added in the explanation section.",
    )
}

fn extended_diagnostics(buf: &mut Vec<u8>, user_error: &FinalizedDiagnostic) {
    buf.extend_from_slice(
        b"The following diagnostic contains a detailed description of how the typechecker discovered the error.\n",
    );
    buf.extend_from_slice(
        b"Each step describes how a type flowed from hints to expressions or how the subtype error was discovered when checking two types.\n",
    );
    buf.extend_from_slice(
        "The contained code fragments highlight relevant hints, statements and expression using the characters '\u{bb}' and '\u{ab}' to indicate the code element .\n"
            .as_bytes(),
    );
    buf.extend_from_slice(
        b"The code fragments are given with line numbers to help you understand the context of the error. You should never use those line numbers in suggested edits.\n",
    );
    buf.extend_from_slice(b"<DIAGNOSTIC>\n\n```hack\n");
    buf.extend_from_slice(extended_diagnostic_formatter::to_string(user_error).as_bytes());
    buf.extend_from_slice(b"\n```\n\n</DIAGNOSTIC>\n\n");
    for str in user_diagnostic::custom_errors(user_error) {
        buf.extend_from_slice(format!("<HINT>\n{}\n</HINT>\n", str).as_bytes())
    }
}

fn legacy_diagnostics(buf: &mut Vec<u8>, user_error: &FinalizedDiagnostic) {
    buf.extend_from_slice(b"<DIAGNOSTIC>\n");
    buf.extend_from_slice(&user_diagnostic::claim_message(user_error).1);
    buf.extend_from_slice(b"\n</DIAGNOSTIC>\n");
    for oxidized::message::Message(pos, str) in user_diagnostic::reason_messages(user_error) {
        buf.extend_from_slice(b"<HINT>\n");
        buf.extend_from_slice(&str);
        buf.extend_from_slice(b"\nlocation uri:");
        buf.extend_from_slice(crate::pos::filename(&pos).as_bytes());
        buf.extend_from_slice(b"\n</HINT>\n");
    }
}

fn bytes_to_string(buf: Vec<u8>) -> String {
    super::code_actions_utils::to_string(BString::from(buf))
}

/// Generates the prompt used for inline fixes for subtyping errors
fn create_user_prompt(selection: &Absolute, user_error: &FinalizedDiagnostic) -> String {
    let mut buf = Vec::with_capacity(500);
    user_prompt_prefix(&mut buf, selection, user_error);
    extended_diagnostics(&mut buf, user_error);
    user_prompt_suffix(&mut buf);
    bytes_to_string(buf)
}

/// Generates the prompt used for inline fixes for non-subtyping errors
fn create_legacy_user_prompt(selection: &Absolute, user_error: &FinalizedDiagnostic) -> String {
    let mut buf = Vec::with_capacity(500);
    user_prompt_prefix(&mut buf, selection, user_error);
    legacy_diagnostics(&mut buf, user_error);
    user_prompt_suffix(&mut buf);
    bytes_to_string(buf)
}

const AGENTIC_PREFIX: &str = "You will be given a Hack code snippet and a detailed diagnostic explaining a problem with the code and all the names and locations of all related expressions, hints, statements and definitions.";

const AGENTIC_SUFFIX: &str = "Your task is to help the user to understand and fix the error by using any tool you think is appropriate and following these steps:

1. Read the diagnostic and understand how the type type error was discovered and the role of each type definition, hint, expression and statement; you may open and read any file mentioned in the diagnostic and search for the names of the definitions, hints, expressions and statements mentioned in the diagnostic. DO NOT focus solely on the position the error was found - the cause of the error may be several steps earlier in the diagnostic and occur in another part of the code mentioned in the diagnostic. The diagnostic will help you think about making changes to various parts of the code may affect the error.

2. Explain the complete diagnostic to the user in your own words, using the names of the definitions, hints, expressions and statements mentioned in the diagnostic;

3. Based on your explanation and the context of the problem, consider which declarations, hints, expressions and statements contained in the diagnostic could be changed to fix the problem.

4. Create edits for the changes you wish to make in order to fix the problem and explain your reasoning; these changes may be in any file mentioned in the diagnostic;

5. Ensure the proposed solution is syntactically correct and does not introduce new errors or warnings;

6. Evaluate the proposed solution and explain why it is the best solution to the problem. Whilst evaluating, please consider the following:
- Does the solution introduce type errors (BAD)
- Does the solution reduce code quality by circumventing the typechecker (e.g. using `as` instead of `is`, using `UNSAFE_CAST` etc) (BAD)
- Does the solution change the behavior of the program (BAD)

7. If your proposed solution is good, generate an edit that will fix the problem and return it in the code section of the response. If your proposed solution is not good, go back to step 1 and try again.
";

fn create_agentic_user_prompt(ctxt_pos: &Absolute, user_error: &FinalizedDiagnostic) -> String {
    let claim_pos = user_diagnostic::claim_message(user_error).0;
    let mut buf = Vec::with_capacity(5000);
    buf.extend_from_slice(AGENTIC_PREFIX.as_bytes());
    buf.extend_from_slice(b"\n\n```hack\n");
    extract_prompt_context(&mut buf, ctxt_pos, &claim_pos);
    if is_subtyping_error(user_diagnostic::get_code(user_error)) {
        extended_diagnostics(&mut buf, user_error)
    } else {
        legacy_diagnostics(&mut buf, user_error)
    }
    buf.extend_from_slice(AGENTIC_SUFFIX.as_bytes());
    bytes_to_string(buf)
}

// -- Generate code actions from errors -------------------------------------

/// `Printf.sprintf "%x"` of an OCaml int (63 bits, printed unsigned).
fn ocaml_hex(n: isize) -> String {
    format!("{:x}", (n as u64) & (u64::MAX >> 1))
}

fn override_selection_of(user_error: &FinalizedDiagnostic) -> Absolute {
    let claim = user_diagnostic::claim_message(user_error);
    let default = claim.0;
    match user_diagnostic::function_pos(user_error) {
        None => default,
        Some(pos) => {
            let start_line = crate::pos::line(&pos);
            let end_line = crate::pos::end_line(&pos);
            // If we aren't in a function the env contains Pos.none - use the diagnostic position in this case
            if end_line == 0 {
                default
            // If size of snippet is greater than our max just use the diagnostic position
            } else if end_line - start_line >= MAX_FILE_CONTENT_LINES {
                default
            } else {
                pos
            }
        }
    }
}

fn error_to_show_inline_chat_command(user_error: &FinalizedDiagnostic, line_agnostic_hash: isize) -> cat::Command {
    let claim = user_diagnostic::claim_message(user_error);
    let claim_msg = super::code_actions_utils::to_string(claim.1.clone());
    let override_selection = override_selection_of(user_error);
    // LSP uses 0-based line numbers
    let webview_start_line = crate::pos::line(&override_selection) - 1;
    let display_prompt = format!("Devmate Quick Fix - {}", claim_msg);
    // Only use extended reasons for subtyping errors
    let user_prompt = if is_subtyping_error(user_diagnostic::get_code(user_error)) {
        create_user_prompt(&override_selection, user_error)
    } else {
        create_legacy_user_prompt(&override_selection, user_error)
    };
    let predefined_prompt = sic::PredefinedPrompt {
        command: "Devmate Quick Fix".to_string(),
        description: Some("Devmate Quick Fix".to_string()),
        display_prompt,
        user_prompt,
        model: Some(sic::Model::CODE_31),
        rules: None,
        task: None,
        prompt_template: None,
        add_diagnostics: None,
    };
    let extras = yojson::T::Assoc(vec![(
        "lineAgnosticHash".to_string(),
        yojson::T::String(ocaml_hex(line_agnostic_hash)),
    )]);
    let command_args = cat::CommandArgs::ShowInlineChat(sic::T {
        entrypoint: "FixLintErrorCodeAction".to_string(),
        predefined_prompt,
        override_selection,
        webview_start_line,
        extras,
    });
    let title = format!("Devmate Quick Fix - {}", claim_msg);
    cat::Command { title, command_args }
}

fn error_to_show_sidebar_chat_command(user_error: &FinalizedDiagnostic, line_agnostic_hash: isize) -> cat::Command {
    let claim = user_diagnostic::claim_message(user_error);
    let claim_msg = super::code_actions_utils::to_string(claim.1.clone());
    let override_selection = override_selection_of(user_error);
    let command_args = cat::CommandArgs::ShowSidebarChat(ssc::T {
        display_prompt: format!("Devmate Agent Fix - {}", claim_msg),
        model_prompt: Some(create_agentic_user_prompt(&override_selection, user_error)),
        llm_config: None,
        model: Some(ssc::MessageModel::CLAUDE_37_SONNET),
        attachments: None,
        action: ssc::Action::DEVMATE,
        trigger: Some("FixLintErrorCodeAction".to_string()),
        trigger_type: Some(ssc::ActionTriggerType::CodeAction),
        local_tool_results: None,
        correlation_id: Some(ocaml_hex(line_agnostic_hash)),
    });
    let title = format!("Devmate Agent Fix - {}", claim_msg);
    cat::Command { title, command_args }
}

fn errors_to_commands(errors: diagnostics_state::T, selection: &Pos) -> Vec<cat::Command> {
    diagnostics_state::get_diagnostic_list(Some(false), errors)
        .iter()
        .flat_map(|user_error| {
            if crate::pos::contains(&user_diagnostic::get_pos(user_error), selection) {
                let line_agnostic_hash = user_diagnostic::hash_diagnostic_for_saved_state(user_error);
                let finalized_error = user_diagnostic::to_absolute(user_error);
                vec![
                    error_to_show_inline_chat_command(&finalized_error, line_agnostic_hash),
                    error_to_show_sidebar_chat_command(&finalized_error, line_agnostic_hash),
                ]
            } else {
                vec![]
            }
        })
        .collect()
}

/// `Simplihack_prompt` (`simplihack/simplihack_prompt.ml`), which has no
/// Rust module yet.
mod simplihack_prompt {
    use naming_special_names_rust as sn;
    use oxidized::aast;
    use oxidized::aast_visitor::Node;
    use oxidized::aast_visitor::Visitor;

    use super::*;
    use crate::tast_env::Env;
    use crate::tast_visitor;
    use crate::tast_visitor::IterParams;
    use crate::tast_visitor::Reduce;

    pub struct T<'a> {
        pub param_pos: Pos,
        /// `derive_prompt: unit -> string option`: the environment and the
        /// argument it evaluates.
        derive: (Env, &'a tast::Expr),
        #[allow(dead_code)]
        pub edit_span: Pos,
    }

    impl T<'_> {
        /// `derive_prompt ()`
        pub fn derive_prompt(&self) -> Option<BString> {
            crate::simplihack_interpreter::eval(&self.derive.0, self.derive.1).ok()
        }
    }

    struct V<'a> {
        acc: Vec<T<'a>>,
    }

    /// `user_attribute env edit_span acc ua`
    fn user_attribute<'a>(env: &Env, edit_span: &Pos, mut acc: Vec<T<'a>>, ua: &'a tast::UserAttribute) -> Vec<T<'a>> {
        let attribute_name = &ua.name.1;
        if attribute_name == sn::user_attributes::SIMPLIHACK {
            match &ua.params[..] {
                [arg] => {
                    let param_pos = crate::pos::btw(&ua.name.0, &arg.1);
                    acc.insert(
                        0,
                        T {
                            param_pos,
                            edit_span: edit_span.clone(),
                            derive: (env.clone(), arg),
                        },
                    );
                    acc
                }
                [arg1, arg2] => {
                    let param_pos = crate::pos::btw(&ua.name.0, &arg2.1);
                    acc.insert(
                        0,
                        T {
                            param_pos,
                            edit_span: edit_span.clone(),
                            derive: (env.clone(), arg1),
                        },
                    );
                    acc
                }
                _ => acc,
            }
        } else {
            acc
        }
    }

    impl<'a> V<'a> {
        /// `let acc = super#on_x env x in List.fold ~init:acc ~f:(user_attribute env span) uas`
        fn with_attributes(
            &mut self,
            env: &mut Env,
            span: &Pos,
            uas: &'a [tast::UserAttribute],
            super_: impl FnOnce(&mut Self, &mut Env) -> Result<(), ()>,
        ) -> Result<(), ()> {
            let outer_env = env.clone();
            let (res, acc) = tast_visitor::reduce::result(self, |v| super_(v, env));
            res?;
            let acc = uas
                .iter()
                .fold(acc, |acc, ua| user_attribute(&outer_env, span, acc, ua));
            tast_visitor::reduce::add(self, acc);
            Ok(())
        }
    }

    impl<'a> Reduce<'a> for V<'a> {
        type Acc = Vec<T<'a>>;
        fn zero(&self) -> Self::Acc {
            vec![]
        }
        fn plus(&self, mut a: Self::Acc, b: Self::Acc) -> Self::Acc {
            a.extend(b);
            a
        }
        fn acc(&mut self) -> &mut Self::Acc {
            &mut self.acc
        }
    }

    impl<'a> Visitor<'a> for V<'a> {
        type Params = IterParams;
        fn object(&mut self) -> &mut dyn Visitor<'a, Params = Self::Params> {
            self
        }
        crate::tast_visitor::reduce_methods!('a; expr_, expression_tree);

        fn visit_class_(&mut self, env: &mut Env, cls: &'a tast::Class_) -> Result<(), ()> {
            self.with_attributes(env, &cls.span, &cls.user_attributes, |v, env| cls.recurse(env, v))
        }

        fn visit_method_(&mut self, env: &mut Env, meth: &'a tast::Method_) -> Result<(), ()> {
            self.with_attributes(env, &meth.span, &meth.user_attributes, |v, env| {
                tast_visitor::reduce::on_method_(v, env, meth)
            })
        }

        fn visit_fun_(&mut self, env: &mut Env, func: &'a tast::Fun_) -> Result<(), ()> {
            self.with_attributes(env, &func.span, &func.user_attributes, |v, env| {
                tast_visitor::reduce::on_fun_(v, env, func)
            })
        }

        fn visit_class_var(&mut self, env: &mut Env, cv: &'a tast::ClassVar) -> Result<(), ()> {
            self.with_attributes(env, &cv.span, &cv.user_attributes, |v, env| {
                tast_visitor::reduce::on_class_var(v, env, cv)
            })
        }

        fn visit_typedef(&mut self, env: &mut Env, x: &'a tast::Typedef) -> Result<(), ()> {
            self.with_attributes(env, &x.span, &x.user_attributes, |v, env| x.recurse(env, v))
        }

        fn visit_class_const(&mut self, env: &mut Env, x: &'a tast::ClassConst) -> Result<(), ()> {
            self.with_attributes(env, &x.span, &x.user_attributes, |v, env| x.recurse(env, v))
        }

        fn visit_fun_param(&mut self, env: &mut Env, x: &'a tast::FunParam) -> Result<(), ()> {
            match x.visibility {
                None => x.recurse(env, self),
                Some(_) => self.with_attributes(env, &x.pos, &x.user_attributes, |v, env| x.recurse(env, v)),
            }
        }

        fn visit_file_attribute(&mut self, env: &mut Env, x: &'a tast::FileAttribute) -> Result<(), ()> {
            self.with_attributes(env, &Pos::NONE, &x.user_attributes, |v, env| x.recurse(env, v))
        }

        fn visit_tparam(&mut self, env: &mut Env, x: &'a tast::Tparam) -> Result<(), ()> {
            let span = x.name.0.clone();
            self.with_attributes(env, &span, &x.user_attributes, |v, env| x.recurse(env, v))
        }

        fn visit_class_typeconst_def(&mut self, env: &mut Env, x: &'a tast::ClassTypeconstDef) -> Result<(), ()> {
            self.with_attributes(env, &x.span, &x.user_attributes, |v, env| x.recurse(env, v))
        }

        fn visit_module_def(&mut self, env: &mut Env, x: &'a tast::ModuleDef) -> Result<(), ()> {
            self.with_attributes(env, &x.span, &x.user_attributes, |v, env| x.recurse(env, v))
        }
    }

    pub fn find<'a>(ctx: &provider_context::T, tast: &'a [tast::Def]) -> Vec<T<'a>> {
        let mut v = V { acc: vec![] };
        tast_visitor::reduce::go(&mut v, ctx, tast)
    }

    #[allow(dead_code)]
    fn _unused(_: &aast::Program<(), ()>) {}
}

fn generate_simplihack_commands(
    ctx: &provider_context::T,
    tast: &tast_with_dynamic::T<tast::Program>,
    pos: &Pos,
) -> Vec<cat::Command> {
    let prompts = simplihack_prompt::find(ctx, &tast.under_normal_assumptions);
    let create_code_action = |prompt: &simplihack_prompt::T<'_>| -> Option<cat::Command> {
        // Convert the relative position to an absolute position, but we don't use it for sidebar chat
        let _param_pos = crate::pos::to_absolute(&prompt.param_pos);
        let derived_prompt = prompt.derive_prompt()?;
        let hash = {
            use md5::Digest;
            let digest = md5::Md5::digest(&derived_prompt[..]);
            digest.iter().map(|b| format!("{:02x}", b)).collect::<String>()
        };
        let derived_prompt = super::code_actions_utils::to_string(derived_prompt);
        let user_prompt = format!(
            " You are an AI assistant tasked with writing and maintaining Hack code. You are triggered by
        by adding an attribute to a program element. The attribute will look either like:
        ```
        <<__SimpliHack(*expr*)>>
        ```
        or:
        ```
        <<__SimpliHack(*expr*, *hash*)>>
        ```
        *expr* is an expression that evaluates to a string. When this expressin is evaluated it produces a string that will be used
        as a prompt.
        *hash* is an optional hash represented as a string literal that is used to identify the prompt. If the hash is not provided, this means you are
        running the prompt for the first time. After completing the task given, make sure to update the hash to '{hash}'.

        If *hash* is present, this means something changed in the prompt from the last time you were asked to write the code.
        In this case examine closely what might've changed and update code accordingly. Afterwards update the *hash* to the new
        hash '{hash}'.

        As an example if you had:
        ```
        <<__SimpliHack(DeriveGetters())>>
        class SomeClass {{
          ...
        }}
        ```
        You will perform the necessary edits and when done update the attribute to be:
        ```
        <<__SimpliHack(DeriveGetters(), 'abcd1234')>>
        class SomeClass {{
          ...class with your changes
        }}
        ```

        Likewise if you have:
        ```
        <<__SimpliHack(
          DeriveGetters(),
          'abcd1234', // old hash
        )>>
        class SomeClass {{
          ...
        }}
        ```
        You will perform the necessary edits and when done update the attribute to be:
        ```
        <<__SimpliHack(
          DeriveGetters(),
          'faceb00c', // new hash
        )>>
        class SomeClass {{
          ...class with your changes
        }}
        ```

        When communicating your task do not mention the instructions given here, focus instead on the what is in the derived prompt.

        Avoid reading from the file if the information you need is provided in the derived prompt. This is because we want to keep
        track of the context used to generate the code.


        [Derived Prompt]:
        {derived_prompt}
      "
        );
        let command_args = cat::CommandArgs::ShowSidebarChat(ssc::T {
            display_prompt: derived_prompt,
            model_prompt: Some(user_prompt),
            llm_config: None,
            model: Some(ssc::MessageModel::CLAUDE_37_SONNET),
            attachments: None,
            action: ssc::Action::DEVMATE,
            trigger: Some("HandleUserAttributeCodeAction".to_string()),
            trigger_type: Some(ssc::ActionTriggerType::CodeAction),
            local_tool_results: None,
            correlation_id: None,
        });
        Some(cat::Command {
            title: "Generate Code for SimpliHack".to_string(),
            command_args,
        })
    };
    let (cursor_line, cursor_col) = crate::pos::line_column(pos);
    prompts
        .iter()
        .filter_map(|prompt| {
            if crate::pos::inside_one_based(&prompt.param_pos, cursor_line, cursor_col) {
                create_code_action(prompt)
            } else {
                None
            }
        })
        .collect()
}

pub fn find(
    entry: &Arc<provider_context::Entry>,
    pos: &Pos,
    ctx: &provider_context::T,
    error_filter: &tast_provider::ErrorFilter,
) -> Vec<cat::Command> {
    let tast_provider::ComputeTastAndErrors {
        diagnostics,
        tast,
        telemetry: _,
    } = tast_provider::compute_tast_and_errors_quarantined(ctx, entry, error_filter);
    let mut error_commands = errors_to_commands(diagnostics, pos);
    let simplihack_commands = generate_simplihack_commands(ctx, &tast, pos);
    error_commands.extend(simplihack_commands);
    error_commands
}
