// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `utils/lsp/lsp_fmt.ml`. See `hh/PORTING.md`.
//!
//! JSON is `Yojson.Safe.t` (`crate::yojson::safe::T`): the keys of an object
//! are printed in the order they are given here, which is the OCaml's.
//!
//! A `Yojson.Safe.t option` is an `Option<&yojson::T>` (the "json option" of
//! `Jget`). The parsers raise as the OCaml does: `Jget.Parse` (a missing or
//! malformed field), `Lsp.Error.LspException` (with `ParseError`) and the
//! `Of_yojson_error` of a `[@@deriving of_yojson]` converter are the
//! [`LspFmtError`] of their `Result` (PORTING.md, "Exceptions"), passed on
//! with `?` to the handlers of the callers (the main loop of `Client_lsp`,
//! `Lsp_extra_commands`); `failwith` is a panic with the message. OCaml
//! evaluates the fields of a record from the last to the first: where more
//! than one of them can raise, they are evaluated in that order here too, so
//! that the same error is raised.

use crate::hh_json_helpers::jget;
use crate::hh_json_helpers::jprint;
use crate::lsp::*;
use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::rt::yojson_conv::OfYojsonError;
use crate::yojson::safe as yojson;

type Json = yojson::T;

/// The exceptions that the parsers raise.
#[derive(Clone, PartialEq)]
pub enum LspFmtError {
    /// `Hh_json_helpers.Jget.Parse`
    Parse(jget::Parse),
    /// `Lsp.Error.LspException`
    LspException(error::LspException),
    /// `Ppx_yojson_conv_lib.Yojson_conv.Of_yojson_error`
    OfYojsonError(OfYojsonError),
}

impl std::fmt::Debug for LspFmtError {
    /// `Printexc.to_string` of the exception.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LspFmtError::Parse(e) => e.fmt(f),
            LspFmtError::LspException(e) => e.fmt(f),
            LspFmtError::OfYojsonError(e) => e.fmt(f),
        }
    }
}

impl From<jget::Parse> for LspFmtError {
    fn from(e: jget::Parse) -> Self {
        LspFmtError::Parse(e)
    }
}

impl From<error::LspException> for LspFmtError {
    fn from(e: error::LspException) -> Self {
        LspFmtError::LspException(e)
    }
}

impl From<OfYojsonError> for LspFmtError {
    fn from(e: OfYojsonError) -> Self {
        LspFmtError::OfYojsonError(e)
    }
}

fn s(x: &str) -> Json {
    Json::String(x.to_string())
}

fn assoc(fields: Vec<(&str, Json)>) -> Json {
    Json::Assoc(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

/// `List.filter_opt` of the fields of an object.
fn assoc_opt(fields: Vec<Option<(&str, Json)>>) -> Json {
    Json::Assoc(
        fields
            .into_iter()
            .flatten()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}

/// `raise (Error.LspException { code = Error.ParseError; message; data = None })`
fn raise_parse_error<A>(message: String) -> Result<A, LspFmtError> {
    Err(error::LspException(error::T {
        code: error::ParseError,
        message,
        data: None,
    })
    .into())
}

// ~~ Miscellaneous LSP structures ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_id(json: &Json) -> Result<LspId, LspFmtError> {
    Ok(match json {
        Json::Int(n) => NumberId(*n),
        Json::Intlit(s) => match int_of_string_opt(s) {
            Some(n) => NumberId(n),
            None => raise_parse_error(format!("float ids not allowed: {}", s))?,
        },
        Json::String(s) => StringId(s.clone()),
        Json::Float(f) => {
            raise_parse_error(format!("float ids not allowed: {}", crate::rt::ocaml_stdlib::string_of_float(*f)))?
        }
        _ => raise_parse_error(format!("not an id: {}", yojson::to_string(json)))?,
    })
}

pub fn parse_id_opt(json: Option<&Json>) -> Result<Option<LspId>, LspFmtError> {
    json.map(parse_id).transpose()
}

pub fn print_id(id: &LspId) -> Json {
    match id {
        NumberId(n) => Json::Intlit(n.to_string()),
        StringId(s) => Json::String(s.clone()),
    }
}

pub fn id_to_string(id: &LspId) -> String {
    match id {
        NumberId(n) => n.to_string(),
        StringId(s) => format!("\"{}\"", s),
    }
}

pub fn parse_position(json: Option<&Json>) -> Result<Position, LspFmtError> {
    let character = jget::int_exn(json, "character")?;
    let line = jget::int_exn(json, "line")?;
    Ok(Position { line, character })
}

pub fn print_position(position: &Position) -> Json {
    assoc(vec![
        ("line", Json::Int(position.line)),
        ("character", Json::Int(position.character)),
    ])
}

pub fn print_range(range: &Range) -> Json {
    assoc(vec![
        ("start", print_position(&range.start)),
        ("end", print_position(&range.end_)),
    ])
}

pub fn print_location(location: &location::T) -> Json {
    assoc(vec![
        ("uri", Json::String(string_of_uri(&location.uri))),
        ("range", print_range(&location.range)),
    ])
}

pub fn print_locations(r: &[location::T]) -> Json {
    Json::List(r.iter().map(print_location).collect())
}

pub fn print_definition_location(definition_location: &definition_location::T) -> Json {
    let location = &definition_location.location;
    let fields = vec![
        Some(("uri", Json::String(string_of_uri(&location.uri)))),
        Some(("range", print_range(&location.range))),
        definition_location
            .title
            .as_ref()
            .map(|t| ("title", Json::String(t.clone()))),
    ];
    assoc_opt(fields)
}

pub fn print_definition_locations(r: &[definition_location::T]) -> Json {
    Json::List(r.iter().map(print_definition_location).collect())
}

pub fn parse_range_exn(json: Option<&Json>) -> Result<Range, LspFmtError> {
    let end_ = parse_position(jget::obj_exn(json, "end")?)?;
    let start = parse_position(jget::obj_exn(json, "start")?)?;
    Ok(Range { start, end_ })
}

pub fn parse_location(j: Option<&Json>) -> Result<location::T, LspFmtError> {
    let range = parse_range_exn(jget::obj_exn(j, "range")?)?;
    let uri = uri_of_string(&jget::string_exn(j, "uri")?);
    Ok(location::T { uri, range })
}

pub fn parse_range_opt(json: Option<&Json>) -> Result<Option<Range>, LspFmtError> {
    Ok(if json.is_none() {
        None
    } else {
        Some(parse_range_exn(json)?)
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_error(e: &error::T) -> Json {
    let data = match &e.data {
        None => vec![],
        Some(data) => vec![("data", data.clone())],
    };
    let mut entries = vec![
        ("code", Json::Int(error::code_to_enum(e.code))),
        ("message", Json::String(e.message.clone())),
    ];
    entries.extend(data);
    assoc(entries)
}

pub fn error_to_log_string(e: &error::T) -> String {
    let data = match &e.data {
        Some(d) => crate::yojson::safe::pretty_to_string(d),
        None => String::new(),
    };
    format!("{} [{}]\n{}", e.message, error::show_code(e.code), data)
}

pub fn parse_error(error: &Json) -> Result<error::T, LspFmtError> {
    let json = Some(error);
    let code = error::code_of_enum(jget::int_exn(json, "code")?).unwrap_or(error::UnknownErrorCode);
    let message = jget::string_exn(json, "message")?;
    let data = jget::val_opt(json, "data").cloned();
    Ok(error::T {
        code,
        message,
        data,
    })
}

pub fn parse_text_document_identifier(
    json: Option<&Json>,
) -> Result<text_document_identifier::T, LspFmtError> {
    Ok(text_document_identifier::T {
        uri: uri_of_string(&jget::string_exn(json, "uri")?),
    })
}

pub fn parse_versioned_text_document_identifier(
    json: Option<&Json>,
) -> Result<versioned_text_document_identifier::T, LspFmtError> {
    let version = jget::int_d(json, "version", 0)?;
    let uri = uri_of_string(&jget::string_exn(json, "uri")?);
    Ok(versioned_text_document_identifier::T { uri, version })
}

pub fn parse_text_document_item(json: Option<&Json>) -> Result<text_document_item::T, LspFmtError> {
    let text = jget::string_exn(json, "text")?;
    let version = jget::int_d(json, "version", 0)?;
    let language_id = jget::string_d(json, "languageId", "".to_string());
    let uri = uri_of_string(&jget::string_exn(json, "uri")?);
    Ok(text_document_item::T {
        uri,
        language_id,
        version,
        text,
    })
}

pub fn print_text_document_item(item: &text_document_item::T) -> Json {
    assoc(vec![
        ("uri", Json::String(string_of_uri(&item.uri))),
        ("languageId", Json::String(item.language_id.clone())),
        ("version", Json::Intlit(item.version.to_string())),
        ("text", Json::String(item.text.clone())),
    ])
}

pub fn print_marked_item(item: &MarkedString) -> Json {
    match item {
        MarkedString::MarkedString(s) => Json::String(s.clone()),
        MarkedString::MarkedCode(language, value) => assoc(vec![
            ("language", Json::String(language.clone())),
            ("value", Json::String(value.clone())),
        ]),
    }
}

pub fn parse_text_document_position_params(
    params: Option<&Json>,
) -> Result<text_document_position_params::T, LspFmtError> {
    let position = parse_position(jget::obj_exn(params, "position")?)?;
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(text_document_position_params::T {
        text_document,
        position,
    })
}

pub fn parse_text_edit(params: Option<&Json>) -> Result<Option<text_edit::T>, LspFmtError> {
    Ok(match params {
        None => None,
        _ => {
            let new_text = jget::string_exn(params, "newText")?;
            let range = parse_range_exn(jget::obj_exn(params, "range")?)?;
            Some(text_edit::T { range, new_text })
        }
    })
}

pub fn print_text_edit(edit: &text_edit::T) -> Json {
    assoc(vec![
        ("range", print_range(&edit.range)),
        ("newText", Json::String(edit.new_text.clone())),
    ])
}

pub fn print_text_edits(r: &[text_edit::T]) -> Json {
    Json::List(r.iter().map(print_text_edit).collect())
}

pub fn print_workspace_edit(r: &workspace_edit::T) -> Json {
    let print_workspace_edit_changes =
        |(document_uri::Uri(uri), text_edits): (DocumentUri, Vec<text_edit::T>)| {
            (uri, print_text_edits(&text_edits))
        };
    assoc(vec![(
        "changes",
        // (`elements` is in decreasing order of the URIs.)
        Json::Assoc(
            document_uri::map::elements(&r.changes)
                .into_iter()
                .map(print_workspace_edit_changes)
                .collect(),
        ),
    )])
}

pub fn print_command(command: &command::T) -> Json {
    assoc(vec![
        ("title", Json::String(command.title.clone())),
        ("command", Json::String(command.command.clone())),
        ("arguments", Json::List(command.arguments.clone())),
    ])
}

pub fn parse_command(json: Option<&Json>) -> command::T {
    let arguments = jget::array_d(json, "arguments", vec![])
        .into_iter()
        .flatten()
        .cloned()
        .collect();
    let command = jget::string_d(json, "command", "".to_string());
    let title = jget::string_d(json, "title", "".to_string());
    command::T {
        title,
        command,
        arguments,
    }
}

pub fn parse_formatting_options(
    json: Option<&Json>,
) -> Result<document_formatting::FormattingOptions, LspFmtError> {
    let insert_spaces = jget::bool_d(json, "insertSpaces", true);
    let tab_size = jget::int_d(json, "tabSize", 2)?;
    Ok(document_formatting::FormattingOptions {
        tab_size,
        insert_spaces,
    })
}

pub fn print_symbol_information(info: &symbol_information::T) -> Json {
    jprint::object_opt(vec![
        ("name".to_string(), Some(Json::String(info.name.clone()))),
        (
            "kind".to_string(),
            Some(Json::Int(symbol_information::symbol_kind_to_enum(info.kind))),
        ),
        ("location".to_string(), Some(print_location(&info.location))),
        ("detail".to_string(), info.detail.as_ref().map(|d| s(d))),
        (
            "containerName".to_string(),
            info.container_name.as_ref().map(|d| s(d)),
        ),
    ])
}

pub fn parse_code_lens(json: Option<&Json>) -> Result<code_lens::T, LspFmtError> {
    let data = jget::obj_exn(json, "data")?.cloned();
    let command = parse_command(jget::obj_exn(json, "command")?);
    let range = parse_range_exn(jget::obj_exn(json, "range")?)?;
    Ok(code_lens::T {
        range,
        command,
        data,
    })
}

pub fn print_code_lens(code_lens: &code_lens::T) -> Json {
    assoc(vec![
        ("range", print_range(&code_lens.range)),
        ("command", print_command(&code_lens.command)),
        (
            "data",
            match &code_lens.data {
                None => Json::Null,
                Some(json) => json.clone(),
            },
        ),
    ])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_shutdown() -> Json {
    Json::Null
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_cancel_request(params: Option<&Json>) -> Result<cancel_request::Params, LspFmtError> {
    Ok(cancel_request::CancelParams {
        id: parse_id(jget::val_exn(params, "id")?)?,
    })
}

pub fn print_cancel_request(p: &cancel_request::Params) -> Json {
    assoc(vec![("id", print_id(&p.id))])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_set_trace_notification(params: Option<&Json>) -> set_trace_notification::Params {
    match jget::string_opt(params, "value").as_deref() {
        Some("verbose") => set_trace_notification::Params::Verbose,
        _ => set_trace_notification::Params::Off,
    }
}

pub fn parse_set_trace(params: Option<&Json>) -> set_trace_notification::Params {
    parse_set_trace_notification(params)
}

pub fn print_set_trace_notification(p: &set_trace_notification::Params) -> Json {
    let s = match p {
        set_trace_notification::Params::Verbose => "verbose",
        set_trace_notification::Params::Off => "off",
    };
    assoc(vec![("value", Json::String(s.to_string()))])
}

pub fn print_set_trace(p: &set_trace_notification::Params) -> Json {
    print_set_trace_notification(p)
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_rage(r: &rage_fb::Result) -> Json {
    let print_item = |item: &rage_fb::RageItem| -> Json {
        assoc(vec![
            ("data", Json::String(item.data.clone())),
            (
                "title",
                match &item.title {
                    None => Json::Null,
                    Some(s) => Json::String(s.clone()),
                },
            ),
        ])
    };
    Json::List(r.iter().map(print_item).collect())
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_did_open(params: Option<&Json>) -> Result<did_open::Params, LspFmtError> {
    Ok(did_open::DidOpenTextDocumentParams {
        text_document: parse_text_document_item(jget::obj_exn(params, "textDocument")?)?,
    })
}

pub fn print_did_open(params: &did_open::Params) -> Json {
    assoc(vec![(
        "textDocument",
        print_text_document_item(&params.text_document),
    )])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_did_close(params: Option<&Json>) -> Result<did_close::Params, LspFmtError> {
    Ok(did_close::DidCloseTextDocumentParams {
        text_document: parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?,
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_did_save(params: Option<&Json>) -> Result<did_save::Params, LspFmtError> {
    let text = jget::string_opt(params, "text");
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(did_save::DidSaveTextDocumentParams { text_document, text })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_did_change(params: Option<&Json>) -> Result<did_change::Params, LspFmtError> {
    let parse_text_document_content_change_event =
        |json: Option<&Json>| -> Result<did_change::TextDocumentContentChangeEvent, LspFmtError> {
            let text = jget::string_exn(json, "text")?;
            let range_length = jget::int_opt(json, "rangeLength")?;
            let range = parse_range_opt(jget::obj_opt(json, "range"))?;
            Ok(did_change::TextDocumentContentChangeEvent {
                range,
                range_length,
                text,
            })
        };
    let content_changes = jget::array_d(params, "contentChanges", vec![])
        .into_iter()
        .map(parse_text_document_content_change_event)
        .collect::<Result<_, _>>()?;
    let text_document =
        parse_versioned_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(did_change::DidChangeTextDocumentParams {
        text_document,
        content_changes,
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_signature_help(params: Option<&Json>) -> Result<signature_help::Params, LspFmtError> {
    parse_text_document_position_params(params)
}

pub fn print_signature_help(r: &signature_help::Result) -> Json {
    let print_par_info = |par_info: &signature_help::ParameterInformation| {
        assoc_opt(vec![
            Some(("label", Json::String(par_info.label.clone()))),
            par_info
                .documentation
                .as_ref()
                .map(|d| ("documentation", Json::String(d.clone()))),
        ])
    };
    let print_sig_info = |sig_info: &signature_help::SignatureInformation| {
        assoc_opt(vec![
            Some(("label", Json::String(sig_info.siginfo_label.clone()))),
            sig_info
                .siginfo_documentation
                .as_ref()
                .map(|d| ("documentation", Json::String(d.clone()))),
            Some((
                "parameters",
                Json::List(sig_info.parameters.iter().map(print_par_info).collect()),
            )),
        ])
    };
    match r {
        None => Json::Null,
        Some(r) => assoc(vec![
            (
                "signatures",
                Json::List(r.signatures.iter().map(print_sig_info).collect()),
            ),
            ("activeSignature", Json::Int(r.active_signature)),
            ("activeParameter", Json::Int(r.active_parameter)),
        ]),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_auto_close(params: Option<&Json>) -> Result<auto_close_jsx::Params, LspFmtError> {
    parse_text_document_position_params(params)
}

pub fn print_auto_close(r: &auto_close_jsx::Result) -> Json {
    match r {
        None => Json::Null,
        Some(r) => Json::String(r.clone()),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_code_lens_resolve(
    params: Option<&Json>,
) -> Result<code_lens_resolve::Params, LspFmtError> {
    parse_code_lens(params)
}

pub fn print_code_lens_resolve(r: &code_lens_resolve::Result) -> Json {
    print_code_lens(r)
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_document_rename(params: Option<&Json>) -> Result<rename::Params, LspFmtError> {
    let new_name = jget::string_exn(params, "newName")?;
    let position = parse_position(jget::obj_exn(params, "position")?)?;
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(rename::RenameParams {
        text_document,
        position,
        new_name,
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_document_code_lens(
    params: Option<&Json>,
) -> Result<document_code_lens::Params, LspFmtError> {
    Ok(document_code_lens::CodelensParams {
        text_document: parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?,
    })
}

pub fn print_document_code_lens(r: &document_code_lens::Result) -> Json {
    Json::List(r.iter().map(print_code_lens).collect())
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_diagnostic(diagnostic: &publish_diagnostics::Diagnostic) -> Json {
    use publish_diagnostics::*;
    let print_diagnostic_severity = |s: DiagnosticSeverity| Json::Int(diagnostic_severity_to_enum(s));
    let print_diagnostic_code = |c: &DiagnosticCode| match c {
        DiagnosticCode::IntCode(i) => Some(Json::Int(*i)),
        DiagnosticCode::StringCode(s) => Some(Json::String(s.clone())),
        DiagnosticCode::NoCode => None,
    };
    let print_related = |related: &RelatedLocation| -> Json {
        assoc(vec![
            ("location", print_location(&related.related_location)),
            ("message", Json::String(related.related_message.clone())),
        ])
    };
    let fields = vec![
        Some(("range", print_range(&diagnostic.range))),
        diagnostic
            .severity
            .map(|s| ("severity", print_diagnostic_severity(s))),
        match print_diagnostic_code(&diagnostic.code) {
            Some(v) => Some(("code", v)),
            None => None,
        },
        diagnostic
            .source
            .as_ref()
            .map(|s| ("source", Json::String(s.clone()))),
        Some(("message", Json::String(diagnostic.message.clone()))),
        Some((
            "relatedInformation",
            Json::List(
                diagnostic
                    .related_information
                    .iter()
                    .map(print_related)
                    .collect(),
            ),
        )),
        Some((
            "relatedLocations",
            Json::List(
                diagnostic
                    .related_locations
                    .iter()
                    .map(print_related)
                    .collect(),
            ),
        )),
        diagnostic.data.as_ref().map(|d| ("data", d.clone())),
    ];
    assoc_opt(fields)
}

pub fn print_diagnostic_list(ds: &[publish_diagnostics::Diagnostic]) -> Json {
    Json::List(ds.iter().map(print_diagnostic).collect())
}

pub fn print_diagnostics(r: &publish_diagnostics::Params) -> Json {
    let fields = vec![
        Some(("uri", Json::String(string_of_uri(&r.uri)))),
        Some(("diagnostics", print_diagnostic_list(&r.diagnostics))),
        if r.is_status_fb {
            Some(("isStatusFB", Json::Bool(true)))
        } else {
            None
        },
    ];
    assoc_opt(fields)
}

pub fn parse_diagnostic(j: Option<&Json>) -> Result<publish_diagnostics::Diagnostic, LspFmtError> {
    use publish_diagnostics::*;
    let parse_code = |c: Option<&Json>| -> Result<DiagnosticCode, LspFmtError> {
        Ok(match c {
            None => DiagnosticCode::NoCode,
            Some(Json::String(s)) => DiagnosticCode::StringCode(s.clone()),
            Some(Json::Int(i)) => DiagnosticCode::IntCode(*i),
            Some(Json::Intlit(s)) => match int_of_string_opt(s) {
                Some(i) => DiagnosticCode::IntCode(i),
                None => raise_parse_error(format!("Diagnostic code expected to be an int: {}", s))?,
            },
            _ => raise_parse_error("Diagnostic code expected to be an int or string".to_string())?,
        })
    };
    let parse_info = |j: Option<&Json>| -> Result<DiagnosticRelatedInformation, LspFmtError> {
        let related_message = jget::string_exn(j, "message")?;
        let related_location = parse_location(jget::obj_exn(j, "location")?)?;
        Ok(DiagnosticRelatedInformation {
            related_location,
            related_message,
        })
    };
    let data = jget::val_opt(j, "data").cloned();
    let related_locations = jget::array_d(j, "relatedLocations", vec![])
        .into_iter()
        .map(parse_info)
        .collect::<Result<_, _>>()?;
    let related_information = jget::array_d(j, "relatedInformation", vec![])
        .into_iter()
        .map(parse_info)
        .collect::<Result<_, _>>()?;
    let message = jget::string_exn(j, "message")?;
    let source = jget::string_opt(j, "source");
    let code = parse_code(jget::val_opt(j, "code"))?;
    let severity = jget::int_opt(j, "severity")?.and_then(diagnostic_severity_of_enum);
    let range = parse_range_exn(jget::obj_exn(j, "range")?)?;
    Ok(Diagnostic {
        range,
        severity,
        code,
        source,
        message,
        related_information,
        related_locations,
        data,
    })
}

pub fn parse_kind(json: Option<&Json>) -> Option<code_action_kind::T> {
    match json {
        Some(Json::String(s)) => Some(code_action_kind::kind_of_string(s)),
        _ => None,
    }
}

pub fn parse_kinds(jsons: &[Option<&Json>]) -> Vec<code_action_kind::T> {
    jsons.iter().filter_map(|j| parse_kind(*j)).collect()
}

pub fn parse_code_action_request(
    j: Option<&Json>,
) -> Result<code_action_request::Params, LspFmtError> {
    let parse_context =
        |c: Option<&Json>| -> Result<code_action_request::CodeActionContext, LspFmtError> {
            let only = jget::array_opt(c, "only").map(|l| parse_kinds(&l));
            let diagnostics = jget::array_exn(c, "diagnostics")?
                .into_iter()
                .map(parse_diagnostic)
                .collect::<Result<_, _>>()?;
            Ok(code_action_request::CodeActionContext { diagnostics, only })
        };
    let context = parse_context(jget::obj_exn(j, "context")?)?;
    let range = parse_range_exn(jget::obj_exn(j, "range")?)?;
    let text_document = parse_text_document_identifier(jget::obj_exn(j, "textDocument")?)?;
    Ok(code_action_request::Params {
        text_document,
        range,
        context,
    })
}

pub fn parse_code_action_resolve_request(
    j: Option<&Json>,
) -> Result<code_action_resolve_request::Params, LspFmtError> {
    let data = {
        let all = jget::obj_exn(j, "data")?;
        let request = jget::obj_opt(all, "originalRequest");
        parse_code_action_request(request)?
    };
    let title = jget::string_exn(j, "title")?;
    Ok(code_action_resolve_request::Params { data, title })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_code_action<A>(
    c: &code_action::T<A>,
    unresolved_to_code_action_request: impl Fn(&A) -> code_action_request::Params,
) -> Json {
    use code_action::*;
    let T {
        title,
        kind,
        diagnostics,
        action,
        is_ai,
    } = c;
    let (edit, command, params_opt) = match action {
        EditAndOrCommand::EditOnly(e) => (Some(e), None, None),
        EditAndOrCommand::CommandOnly(c) => (None, Some(c), None),
        EditAndOrCommand::BothEditThenCommand((e, c)) => (Some(e), Some(c), None),
        EditAndOrCommand::UnresolvedEdit(e) => {
            (None, None, Some(unresolved_to_code_action_request(e)))
        }
    };
    let print_params = |code_action_request::Params {
                            text_document,
                            range,
                            context,
                        }: &code_action_request::Params| {
        assoc(vec![
            (
                "textDocument",
                assoc(vec![("uri", Json::String(string_of_uri(&text_document.uri)))]),
            ),
            ("range", print_range(range)),
            (
                "context",
                assoc(vec![(
                    "diagnostics",
                    print_diagnostic_list(&context.diagnostics),
                )]),
            ),
        ])
    };
    let data_opt = {
        let fields: Vec<(&str, Json)> = vec![
            params_opt
                .as_ref()
                .map(|params| ("originalRequest", print_params(params))),
            is_ai.map(|is_ai| ("isAI", Json::Bool(is_ai))),
        ]
        .into_iter()
        .flatten()
        .collect();
        match fields[..] {
            [] => None,
            _ => Some(assoc(fields)),
        }
    };
    let result_fields = vec![
        Some(("title", Json::String(title.clone()))),
        Some((
            "kind",
            Json::String(code_action_kind::string_of_kind(kind)),
        )),
        Some(("diagnostics", print_diagnostic_list(diagnostics))),
        edit.map(|e| ("edit", print_workspace_edit(e))),
        command.map(|c| ("command", print_command(c))),
        data_opt.map(|d| ("data", d)),
    ];
    assoc_opt(result_fields)
}

pub fn print_code_action_result(c: &code_action::Result, p: &code_action_request::Params) -> Json {
    let print_command_or_action = |x: &code_action::CommandOrAction| match x {
        code_action::CommandOrAction_::Command(c) => print_command(c),
        code_action::CommandOrAction_::Action(c) => print_code_action(c, |_: &()| p.clone()),
    };
    Json::List(c.iter().map(print_command_or_action).collect())
}

pub fn print_code_action_resolve_result(c: &code_action_resolve::Result) -> Json {
    let print_command_or_action = |x: &code_action::ResolvedCommandOrAction| match x {
        code_action::CommandOrAction_::Command(c) => print_command(c),
        code_action::CommandOrAction_::Action(c) => {
            let unresolved_to_code_action_request =
                |m: &code_action::ResolvedMarker| -> code_action_request::Params { match *m {} };
            print_code_action(c, unresolved_to_code_action_request)
        }
    };
    match c {
        Ok(command_or_action) => print_command_or_action(command_or_action),
        Err(err) => print_error(err),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_log_message(type_: message_type::T, message: &str) -> Json {
    assoc(vec![
        ("type", Json::Int(message_type::to_enum(type_))),
        ("message", Json::String(message.to_string())),
    ])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_telemetry_notification(r: &log_message::Params, extras: &[(String, Json)]) -> Json {
    // LSP allows "any" for the format of telemetry notifications. It's up to us!
    let mut fields = vec![
        ("type".to_string(), Json::Int(message_type::to_enum(r.type_))),
        ("message".to_string(), Json::String(r.message.clone())),
    ];
    fields.extend(extras.iter().cloned());
    Json::Assoc(fields)
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_show_message(type_: message_type::T, message: &str) -> Json {
    let r = show_message::ShowMessageParams {
        type_,
        message: message.to_string(),
    };
    assoc(vec![
        ("type", Json::Int(message_type::to_enum(r.type_))),
        ("message", Json::String(r.message)),
    ])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_show_message_request(r: &show_message_request::ShowMessageRequestParams) -> Json {
    let print_action = |action: &show_message_request::MessageActionItem| -> Json {
        assoc(vec![("title", Json::String(action.title.clone()))])
    };
    let fields = vec![
        Some(("type", Json::Int(message_type::to_enum(r.type_)))),
        Some(("message", Json::String(r.message.clone()))),
        Some((
            "actions",
            Json::List(r.actions.iter().map(print_action).collect()),
        )),
    ];
    assoc_opt(fields)
}

pub fn parse_result_show_message_request(result: Option<&Json>) -> show_message_request::Result {
    let title = jget::string_opt(result, "title");
    title.map(|title| show_message_request::MessageActionItem { title })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_show_status(r: &show_status_fb::ShowStatusParams) -> Json {
    let rr = &r.request;
    let fields = vec![
        Some(("type", Json::Int(message_type::to_enum(rr.type_)))),
        Some(("message", Json::String(rr.message.clone()))),
        r.short_message
            .as_ref()
            .map(|s| ("shortMessage", Json::String(s.clone()))),
        r.telemetry.as_ref().map(|t| ("telemetry", t.clone())),
        r.progress.map(|progress| {
            let progress_fields = vec![
                Some(("numerator", Json::Int(progress))),
                r.total.map(|t| ("denominator", Json::Int(t))),
            ];
            ("progress", assoc_opt(progress_fields))
        }),
    ];
    assoc_opt(fields)
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_connection_status(p: &connection_status_fb::Params) -> Json {
    assoc(vec![("isConnected", Json::Bool(p.is_connected))])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_hover(params: Option<&Json>) -> Result<hover::Params, LspFmtError> {
    parse_text_document_position_params(params)
}

pub fn print_hover(r: &hover::Result) -> Json {
    match r {
        None => Json::Null,
        Some(r) => {
            let fields = vec![
                Some((
                    "contents",
                    Json::List(r.contents.iter().map(print_marked_item).collect()),
                )),
                r.range.as_ref().map(|rng| ("range", print_range(rng))),
            ];
            assoc_opt(fields)
        }
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_completion_item(
    params: Option<&Json>,
) -> Result<completion_item_resolve::Params, LspFmtError> {
    use completion::*;
    let text_edit = parse_text_edit(jget::obj_opt(params, "textEdit"))?;
    let additional_text_edits = jget::array_d(params, "additionalTextEdits", vec![])
        .into_iter()
        .map(parse_text_edit)
        .filter_map(std::result::Result::transpose)
        .collect::<std::result::Result<_, _>>()?;
    let command = match jget::obj_opt(params, "command") {
        None => None,
        c => Some(parse_command(c)),
    };
    let documentation = match jget::obj_opt(params, "documentation") {
        None => None,
        Some(json) => Some(CompletionDocumentation::UnparsedDocumentation(json.clone())),
    };
    let data = jget::obj_opt(params, "data").cloned();
    let insert_text_format =
        jget::int_opt(params, "insertTextFormat")?.and_then(insert_text_format_of_enum);
    let insert_text = jget::string_opt(params, "insertText");
    let filter_text = jget::string_opt(params, "filterText");
    let sort_text = jget::string_opt(params, "sortText");
    let detail = jget::string_opt(params, "detail");
    let kind = jget::int_opt(params, "kind")?.and_then(completion_item_kind_of_enum);
    let label = jget::string_exn(params, "label")?;
    Ok(CompletionItem {
        label,
        kind,
        detail,
        documentation,
        sort_text,
        filter_text,
        insert_text,
        insert_text_format,
        text_edit,
        additional_text_edits,
        command,
        data,
    })
}

pub fn string_of_marked_string(acc: String, marked: &MarkedString) -> String {
    match marked {
        MarkedString::MarkedCode(lang, code) => acc + "```" + lang + "\n" + code + "\n" + "```\n",
        MarkedString::MarkedString(str) => acc + str + "\n",
    }
}

/// `Base.String.strip`
fn strip(s: &str) -> &str {
    s.trim_matches(|c| matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r'))
}

pub fn print_completion_item(item: &completion::CompletionItem) -> Json {
    use completion::*;
    let fields = vec![
        Some(("label", Json::String(item.label.clone()))),
        item.kind
            .map(|x| ("kind", Json::Int(completion_item_kind_to_enum(x)))),
        item.detail
            .as_ref()
            .map(|d| ("detail", Json::String(d.clone()))),
        match &item.documentation {
            None => None,
            Some(CompletionDocumentation::UnparsedDocumentation(json)) => {
                Some(("documentation", json.clone()))
            }
            Some(CompletionDocumentation::MarkedStringsDocumentation(doc)) => Some((
                "documentation",
                assoc(vec![
                    ("kind", Json::String("markdown".to_string())),
                    (
                        "value",
                        Json::String(
                            strip(&doc.iter().fold(String::new(), string_of_marked_string))
                                .to_string(),
                        ),
                    ),
                ]),
            )),
        },
        item.sort_text
            .as_ref()
            .map(|s| ("sortText", Json::String(s.clone()))),
        item.filter_text
            .as_ref()
            .map(|s| ("filterText", Json::String(s.clone()))),
        item.insert_text
            .as_ref()
            .map(|s| ("insertText", Json::String(s.clone()))),
        item.insert_text_format
            .map(|x| ("insertTextFormat", Json::Int(insert_text_format_to_enum(x)))),
        item.text_edit
            .as_ref()
            .map(|te| ("textEdit", print_text_edit(te))),
        match &item.additional_text_edits[..] {
            [] => None,
            text_edits => Some(("additionalTextEdits", print_text_edits(text_edits))),
        },
        item.command
            .as_ref()
            .map(|c| ("command", print_command(c))),
        item.data.as_ref().map(|d| ("data", d.clone())),
    ];
    assoc_opt(fields)
}

pub fn parse_completion(params: Option<&Json>) -> Result<completion::Params, LspFmtError> {
    use completion::*;
    let context = jget::obj_opt(params, "context");
    let context_ = match context {
        Some(_) => {
            let tk = jget::int_exn(context, "triggerKind")?;
            let trigger_character = jget::string_opt(context, "triggerCharacter");
            let trigger_kind = match completion_trigger_kind_of_enum(tk) {
                Some(k) => k,
                // `Option.value_exn ~message`
                None => panic!("Unsupported trigger kind: {}", tk),
            };
            Some(CompletionContext {
                trigger_kind,
                trigger_character,
            })
        }
        None => None,
    };
    let loc = parse_text_document_position_params(params)?;
    Ok(CompletionParams {
        loc,
        context: context_,
    })
}

pub fn print_completion(r: &completion::Result) -> Json {
    assoc(vec![
        ("isIncomplete", Json::Bool(r.is_incomplete)),
        (
            "items",
            Json::List(r.items.iter().map(print_completion_item).collect()),
        ),
    ])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_workspace_symbol(
    params: Option<&Json>,
) -> Result<workspace_symbol::Params, LspFmtError> {
    Ok(workspace_symbol::WorkspaceSymbolParams {
        query: jget::string_exn(params, "query")?,
    })
}

pub fn print_workspace_symbol(r: &workspace_symbol::Result) -> Json {
    Json::List(r.iter().map(print_symbol_information).collect())
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_document_symbol(params: Option<&Json>) -> Result<document_symbol::Params, LspFmtError> {
    Ok(document_symbol::DocumentSymbolParams {
        text_document: parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?,
    })
}

pub fn print_document_symbol(r: &document_symbol::Result) -> Json {
    Json::List(r.iter().map(print_symbol_information).collect())
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_find_references(params: Option<&Json>) -> Result<find_references::Params, LspFmtError> {
    let partial_result_token = jget::string_opt(params, "partialResultToken").map(PartialResultToken);
    let context = jget::obj_opt(params, "context");
    let context_ = {
        let include_indirect_references = jget::bool_d(context, "includeIndirectReferences", false);
        let include_declaration = jget::bool_d(context, "includeDeclaration", true);
        find_references::ReferenceContext {
            include_declaration,
            include_indirect_references,
        }
    };
    let loc = parse_text_document_position_params(params)?;
    Ok(find_references::ReferenceParams {
        loc,
        partial_result_token,
        context: context_,
    })
}

pub fn print_find_references_partial_result(
    PartialResultToken(token): &PartialResultToken,
    refs: &[location::T],
) -> Json {
    assoc(vec![
        ("token", Json::String(token.clone())),
        ("value", print_locations(refs)),
    ])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_call_item(params: Option<&Json>) -> Result<call_hierarchy_item::T, LspFmtError> {
    let range_obj = jget::obj_exn(params, "range")?;
    let selection_range_obj = jget::obj_exn(params, "selectionRange")?;
    let selection_range = parse_range_exn(selection_range_obj)?;
    let range = parse_range_exn(range_obj)?;
    let uri = uri_of_string(&jget::string_exn(params, "uri")?);
    let detail = jget::string_opt(params, "detail");
    let kind = match symbol_information::symbol_kind_of_enum(jget::int_exn(params, "kind")?) {
        None => Err(jget::Parse("invalid symbol kind".to_string()))?,
        Some(s) => s,
    };
    let name = jget::string_exn(params, "name")?;
    Ok(call_hierarchy_item::T {
        name,
        kind,
        detail,
        uri,
        range,
        selection_range,
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_call_item(item: &call_hierarchy_item::T) -> Json {
    let fields = vec![
        Some(("name", Json::String(item.name.clone()))),
        Some((
            "kind",
            Json::Int(symbol_information::symbol_kind_to_enum(item.kind)),
        )),
        item.detail
            .as_ref()
            .map(|d| ("detail", Json::String(d.clone()))),
        Some(("uri", Json::String(string_of_uri(&item.uri)))),
        Some(("range", print_range(&item.range))),
        Some(("selectionRange", print_range(&item.selection_range))),
    ];
    assoc_opt(fields)
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_call_hierarchy_calls(
    params: Option<&Json>,
) -> Result<call_hierarchy_calls_request_param::T, LspFmtError> {
    let json_item = jget::obj_opt(params, "item");
    let parsed_item = parse_call_item(json_item)?;
    Ok(call_hierarchy_calls_request_param::T { item: parsed_item })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_prepare_call_hierarchy_result(r: &prepare_call_hierarchy::Result) -> Json {
    match r {
        None => Json::Null,
        Some(list) => Json::List(list.iter().map(print_call_item).collect()),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_call_hierarchy_incoming_calls_result(r: &call_hierarchy_incoming_calls::Result) -> Json {
    let print_call_hierarchy_incoming_call =
        |call: &call_hierarchy_incoming_calls::CallHierarchyIncomingCall| -> Json {
            assoc(vec![
                ("from", print_call_item(&call.from)),
                (
                    "fromRanges",
                    Json::List(call.from_ranges.iter().map(print_range).collect()),
                ),
            ])
        };
    match r {
        None => Json::Null,
        Some(list) => Json::List(list.iter().map(print_call_hierarchy_incoming_call).collect()),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_call_hierarchy_outgoing_calls_result(r: &call_hierarchy_outgoing_calls::Result) -> Json {
    let print_call_hierarchy_outgoing_call =
        |call: &call_hierarchy_outgoing_calls::CallHierarchyOutgoingCall| -> Json {
            assoc(vec![
                ("to", print_call_item(&call.call_to)),
                (
                    "fromRanges",
                    Json::List(call.from_ranges.iter().map(print_range).collect()),
                ),
            ])
        };
    match r {
        None => Json::Null,
        Some(list) => Json::List(list.iter().map(print_call_hierarchy_outgoing_call).collect()),
    }
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_document_highlight(
    params: Option<&Json>,
) -> Result<document_highlight::Params, LspFmtError> {
    parse_text_document_position_params(params)
}

pub fn print_document_highlight(r: &document_highlight::Result) -> Json {
    let print_highlight = |highlight: &document_highlight::DocumentHighlight| {
        let fields = vec![
            Some(("range", print_range(&highlight.range))),
            highlight.kind.map(|k| {
                (
                    "kind",
                    Json::Int(document_highlight::document_highlight_kind_to_enum(k)),
                )
            }),
        ];
        assoc_opt(fields)
    };
    Json::List(r.iter().map(print_highlight).collect())
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_document_formatting(
    params: Option<&Json>,
) -> Result<document_formatting::Params, LspFmtError> {
    let options = parse_formatting_options(jget::obj_opt(params, "options"))?;
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(document_formatting::DocumentFormattingParams {
        text_document,
        options,
    })
}

pub fn print_document_formatting(r: &document_formatting::Result) -> Json {
    print_text_edits(r)
}

pub fn parse_document_range_formatting(
    params: Option<&Json>,
) -> Result<document_range_formatting::Params, LspFmtError> {
    let options = parse_formatting_options(jget::obj_opt(params, "options"))?;
    let range = parse_range_exn(jget::obj_exn(params, "range")?)?;
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(document_range_formatting::DocumentRangeFormattingParams {
        text_document,
        range,
        options,
    })
}

pub fn print_document_range_formatting(r: &document_range_formatting::Result) -> Json {
    print_text_edits(r)
}

pub fn parse_document_on_type_formatting(
    params: Option<&Json>,
) -> Result<document_on_type_formatting::Params, LspFmtError> {
    let options = parse_formatting_options(jget::obj_opt(params, "options"))?;
    let ch = jget::string_exn(params, "ch")?;
    let position = parse_position(jget::obj_exn(params, "position")?)?;
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(document_on_type_formatting::DocumentOnTypeFormattingParams {
        text_document,
        position,
        ch,
        options,
    })
}

pub fn print_document_on_type_formatting(r: &document_on_type_formatting::Result) -> Json {
    print_text_edits(r)
}

pub fn parse_will_save_wait_until(
    params: Option<&Json>,
) -> Result<will_save_wait_until::Params, LspFmtError> {
    let reason = text_document_save_reason_of_enum(jget::int_exn(params, "reason")?)
        .unwrap_or(TextDocumentSaveReason::Manual);
    let text_document = parse_text_document_identifier(jget::obj_exn(params, "textDocument")?)?;
    Ok(will_save_wait_until::WillSaveWaitUntilTextDocumentParams {
        text_document,
        reason,
    })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn parse_initialize(params: Option<&Json>) -> Result<initialize::Params, LspFmtError> {
    use initialize::*;
    fn parse_initialize(json: Option<&Json>) -> std::result::Result<Params, LspFmtError> {
        let trace = parse_trace(jget::string_opt(json, "trace").as_deref());
        let client_capabilities = parse_capabilities(jget::obj_opt(json, "capabilities"));
        let initialization_options =
            parse_initialization_options(jget::obj_opt(json, "initializationOptions"))?;
        let root_uri = jget::string_opt(json, "rootUri").map(|s| uri_of_string(&s));
        let root_path = jget::string_opt(json, "rootPath");
        let process_id = jget::int_opt(json, "processId")?;
        Ok(Params {
            process_id,
            root_path,
            root_uri,
            initialization_options,
            client_capabilities,
            trace,
        })
    }
    fn parse_trace(s: Option<&str>) -> Trace {
        match s {
            Some("messages") => Trace::Messages,
            Some("verbose") => Trace::Verbose,
            _ => Trace::Off,
        }
    }
    fn parse_initialization_options(
        json: Option<&Json>,
    ) -> std::result::Result<InitializationOptions, LspFmtError> {
        let skip_lsp_server_on_type_formatting =
            jget::bool_d(json, "skipLspServerOnTypeFormatting", false);
        let delay_until_done_init = jget::bool_d(json, "delayUntilDoneInit", false);
        let naming_table_saved_state_test_delay =
            jget::float_d(json, "namingTableSavedStateTestDelay", 0.0)?;
        let naming_table_saved_state_path = jget::string_opt(json, "namingTableSavedStatePath");
        Ok(InitializationOptions {
            naming_table_saved_state_path,
            naming_table_saved_state_test_delay,
            delay_until_done_init,
            skip_lsp_server_on_type_formatting,
        })
    }
    fn parse_capabilities(json: Option<&Json>) -> ClientCapabilities {
        let client_experimental = parse_client_experimental(jget::obj_opt(json, "experimental"));
        let telemetry = parse_telemetry(jget::obj_opt(json, "telemetry"));
        let window = parse_window(jget::obj_opt(json, "window"));
        let text_document = parse_text_document(jget::obj_opt(json, "textDocument"));
        let workspace = parse_workspace(jget::obj_opt(json, "workspace"));
        ClientCapabilities {
            workspace,
            text_document,
            window,
            telemetry,
            client_experimental,
        }
    }
    fn parse_workspace(json: Option<&Json>) -> WorkspaceClientCapabilities {
        let did_change_watched_files =
            parse_dynamic_registration(jget::obj_opt(json, "didChangeWatchedFiles"));
        let workspace_edit = parse_workspace_edit(jget::obj_opt(json, "workspaceEdit"));
        let apply_edit = jget::bool_d(json, "applyEdit", false);
        WorkspaceClientCapabilities {
            apply_edit,
            workspace_edit,
            did_change_watched_files,
        }
    }
    fn parse_dynamic_registration(json: Option<&Json>) -> DynamicRegistration {
        DynamicRegistration {
            dynamic_registration: jget::bool_d(json, "dynamicRegistration", false),
        }
    }
    fn parse_workspace_edit(json: Option<&Json>) -> WorkspaceEdit {
        WorkspaceEdit {
            document_changes: jget::bool_d(json, "documentChanges", false),
        }
    }
    fn parse_text_document(json: Option<&Json>) -> TextDocumentClientCapabilities {
        let implementation = parse_implementation(jget::obj_opt(json, "implementation"));
        let declaration = parse_declaration(jget::obj_opt(json, "declaration"));
        let type_definition = parse_type_definition(jget::obj_opt(json, "typeDefinition"));
        let definition = parse_definition(jget::obj_opt(json, "definition"));
        let code_action = parse_code_action(jget::obj_opt(json, "codeAction"));
        let completion = parse_completion(jget::obj_opt(json, "completion"));
        let synchronization = parse_synchronization(jget::obj_opt(json, "synchronization"));
        TextDocumentClientCapabilities {
            synchronization,
            completion,
            code_action,
            definition,
            type_definition,
            declaration,
            implementation,
        }
    }
    fn parse_synchronization(json: Option<&Json>) -> Synchronization {
        let did_save = jget::bool_d(json, "didSave", false);
        let will_save_wait_until = jget::bool_d(json, "willSaveWaitUntil", false);
        let will_save = jget::bool_d(json, "willSave", false);
        Synchronization {
            will_save,
            will_save_wait_until,
            did_save,
        }
    }
    fn parse_completion(json: Option<&Json>) -> Completion {
        Completion {
            completion_item: parse_completion_item(jget::obj_opt(json, "completionItem")),
        }
    }
    fn parse_completion_item(json: Option<&Json>) -> CompletionItem {
        CompletionItem {
            snippet_support: jget::bool_d(json, "snippetSupport", false),
        }
    }
    fn parse_code_action(json: Option<&Json>) -> CodeAction {
        let code_action_literal_support =
            parse_code_action_literal_support(jget::obj_opt(json, "codeActionLiteralSupport"));
        let code_action_dynamic_registration = jget::bool_d(json, "dynamicRegistration", false);
        CodeAction {
            code_action_dynamic_registration,
            code_action_literal_support,
        }
    }
    fn parse_code_action_literal_support(json: Option<&Json>) -> Option<CodeActionliteralSupport> {
        jget::array_opt(json, "valueSet").map(|ls| CodeActionliteralSupport {
            code_action_value_set: parse_kinds(&ls),
        })
    }
    fn parse_definition(json: Option<&Json>) -> Definition {
        Definition {
            definition_link_support: jget::bool_d(json, "linkSupport", false),
        }
    }
    fn parse_type_definition(json: Option<&Json>) -> TypeDefinition {
        TypeDefinition {
            type_definition_link_support: jget::bool_d(json, "linkSupport", false),
        }
    }
    fn parse_implementation(json: Option<&Json>) -> Implementation {
        Implementation {
            implementation_link_support: jget::bool_d(json, "linkSupport", false),
        }
    }
    fn parse_declaration(json: Option<&Json>) -> Declaration {
        Declaration {
            declaration_link_support: jget::bool_d(json, "linkSupport", false),
        }
    }
    fn parse_window(json: Option<&Json>) -> WindowClientCapabilities {
        WindowClientCapabilities {
            status: jget::obj_opt(json, "status").is_some(),
        }
    }
    fn parse_telemetry(json: Option<&Json>) -> TelemetryClientCapabilities {
        TelemetryClientCapabilities {
            connection_status: jget::obj_opt(json, "connectionStatus").is_some(),
        }
    }
    fn parse_client_experimental(json: Option<&Json>) -> client_experimental_capabilities::T {
        let auto_close_jsx = jget::bool_d(json, "autoCloseJsx", false);
        let snippet_text_edit = jget::bool_d(json, "snippetTextEdit", false);
        client_experimental_capabilities::T {
            snippet_text_edit,
            auto_close_jsx,
        }
    }
    parse_initialize(params)
}

pub fn print_initialize_error(r: &initialize::ErrorData) -> Json {
    assoc(vec![("retry", Json::Bool(r.retry))])
}

pub fn print_initialize(r: &initialize::Result) -> Json {
    use initialize::*;
    let cap = &r.server_capabilities;
    let sync = &cap.text_document_sync;
    assoc(vec![(
        "capabilities",
        {
            let fields = vec![
                Some((
                    "textDocumentSync",
                    {
                        let sync_fields = vec![
                            Some(("openClose", Json::Bool(sync.open_close))),
                            Some((
                                "change",
                                Json::Int(text_document_sync_kind_to_enum(sync.change)),
                            )),
                            Some(("willSave", Json::Bool(sync.will_save))),
                            Some(("willSaveWaitUntil", Json::Bool(sync.will_save_wait_until))),
                            sync.did_save.as_ref().map(|save| {
                                (
                                    "save",
                                    assoc(vec![("includeText", Json::Bool(save.include_text))]),
                                )
                            }),
                        ];
                        assoc_opt(sync_fields)
                    },
                )),
                Some(("hoverProvider", Json::Bool(cap.hover_provider))),
                cap.completion_provider.as_ref().map(|comp| {
                    (
                        "completionProvider",
                        assoc(vec![
                            ("resolveProvider", Json::Bool(comp.resolve_provider)),
                            (
                                "triggerCharacters",
                                jprint::string_array(&comp.completion_trigger_characters),
                            ),
                        ]),
                    )
                }),
                cap.signature_help_provider.as_ref().map(|shp| {
                    (
                        "signatureHelpProvider",
                        assoc(vec![(
                            "triggerCharacters",
                            jprint::string_array(&shp.sighelp_trigger_characters),
                        )]),
                    )
                }),
                Some(("definitionProvider", Json::Bool(cap.definition_provider))),
                Some((
                    "typeDefinitionProvider",
                    Json::Bool(cap.type_definition_provider),
                )),
                Some(("referencesProvider", Json::Bool(cap.references_provider))),
                Some((
                    "documentHighlightProvider",
                    Json::Bool(cap.document_highlight_provider),
                )),
                Some((
                    "documentSymbolProvider",
                    Json::Bool(cap.document_symbol_provider),
                )),
                Some((
                    "workspaceSymbolProvider",
                    Json::Bool(cap.workspace_symbol_provider),
                )),
                cap.code_action_provider.as_ref().map(|provider| {
                    (
                        "codeActionProvider",
                        assoc(vec![(
                            "resolveProvider",
                            Json::Bool(provider.resolve_provider),
                        )]),
                    )
                }),
                cap.code_lens_provider.as_ref().map(|codelens| {
                    (
                        "codeLensProvider",
                        assoc(vec![(
                            "resolveProvider",
                            Json::Bool(codelens.codelens_resolve_provider),
                        )]),
                    )
                }),
                Some((
                    "documentFormattingProvider",
                    Json::Bool(cap.document_formatting_provider),
                )),
                Some((
                    "documentRangeFormattingProvider",
                    Json::Bool(cap.document_range_formatting_provider),
                )),
                cap.document_on_type_formatting_provider.as_ref().map(|o| {
                    (
                        "documentOnTypeFormattingProvider",
                        assoc(vec![
                            (
                                "firstTriggerCharacter",
                                Json::String(o.first_trigger_character.clone()),
                            ),
                            (
                                "moreTriggerCharacter",
                                jprint::string_array(&o.more_trigger_character),
                            ),
                        ]),
                    )
                }),
                Some(("renameProvider", Json::Bool(cap.rename_provider))),
                cap.document_link_provider.as_ref().map(|dlp| {
                    (
                        "documentLinkProvider",
                        assoc(vec![(
                            "resolveProvider",
                            Json::Bool(dlp.doclink_resolve_provider),
                        )]),
                    )
                }),
                cap.execute_command_provider.as_ref().map(|p| {
                    (
                        "executeCommandProvider",
                        assoc(vec![("commands", jprint::string_array(&p.commands))]),
                    )
                }),
                Some((
                    "implementationProvider",
                    Json::Bool(cap.implementation_provider),
                )),
                Some(("rageProvider", Json::Bool(cap.rage_provider_fb))),
                cap.server_experimental
                    .as_ref()
                    .map(|experimental_capabilities| {
                        (
                            "experimental",
                            assoc(vec![
                                (
                                    "snippetTextEdit",
                                    Json::Bool(experimental_capabilities.snippet_text_edit),
                                ),
                                (
                                    "autoCloseJsx",
                                    Json::Bool(experimental_capabilities.auto_close_jsx),
                                ),
                            ]),
                        )
                    }),
            ];
            assoc_opt(fields)
        },
    )])
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn print_registration_options(register_options: &LspRegistrationOptions) -> Json {
    match register_options {
        LspRegistrationOptions::DidChangeWatchedFilesRegistrationOptions(register_options) => {
            assoc(vec![(
                "watchers",
                Json::List(
                    register_options
                        .watchers
                        .iter()
                        .map(|watcher| {
                            assoc(vec![
                                ("globPattern", Json::String(watcher.glob_pattern.clone())),
                                // all events: create, change, and delete
                                ("kind", Json::Int(7)),
                            ])
                        })
                        .collect(),
                ),
            )])
        }
    }
}

pub fn print_register_capability(params: &register_capability::Params) -> Json {
    assoc(vec![(
        "registrations",
        Json::List(
            params
                .registrations
                .iter()
                .map(|registration| {
                    assoc(vec![
                        ("id", Json::String(registration.id.clone())),
                        ("method", Json::String(registration.method_.clone())),
                        (
                            "registerOptions",
                            print_registration_options(&registration.register_options),
                        ),
                    ])
                })
                .collect(),
        ),
    )])
}

pub fn parse_did_change_watched_files(
    json: Option<&Json>,
) -> Result<did_change_watched_files::Params, LspFmtError> {
    let changes = jget::array_exn(json, "changes")?
        .into_iter()
        .map(|change| -> Result<_, LspFmtError> {
            let uri = uri_of_string(&jget::string_exn(change, "uri")?);
            let type_ = jget::int_exn(change, "type")?;
            let type_ = match did_change_watched_files::file_change_type_of_enum(type_) {
                Some(type_) => type_,
                None => panic!("Invalid file change type {}", type_),
            };
            Ok(did_change_watched_files::FileEvent { uri, type_ })
        })
        .collect::<Result<_, _>>()?;
    Ok(did_change_watched_files::Params { changes })
}

// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// universal parser+printer
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

pub fn get_uri_opt(m: &LspMessage) -> Option<DocumentUri> {
    use LspMessage::*;
    use LspNotification::*;
    use LspRequest::*;
    match m {
        RequestMessage(_, DocumentCodeLensRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, HoverRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, DefinitionRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, TypeDefinitionRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, CodeActionRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, CodeActionResolveRequest(p)) => Some(p.data.text_document.uri.clone()),
        RequestMessage(_, CompletionRequest(p)) => Some(p.loc.text_document.uri.clone()),
        RequestMessage(_, DocumentSymbolRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, FindReferencesRequest(p)) => Some(p.loc.text_document.uri.clone()),
        RequestMessage(_, PrepareCallHierarchyRequest(p)) => Some(p.text_document.uri.clone()),
        // Implement for CallHierarchy
        RequestMessage(_, CallHierarchyIncomingCallsRequest(p)) => Some(p.item.uri.clone()),
        RequestMessage(_, CallHierarchyOutgoingCallsRequest(p)) => Some(p.item.uri.clone()),
        RequestMessage(_, ImplementationRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, DocumentHighlightRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, DocumentFormattingRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, DocumentRangeFormattingRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, DocumentOnTypeFormattingRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, RenameRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, SignatureHelpRequest(p)) => Some(p.text_document.uri.clone()),
        RequestMessage(_, AutoCloseRequest(p)) => Some(p.text_document.uri.clone()),
        NotificationMessage(PublishDiagnosticsNotification(p)) => Some(p.uri.clone()),
        NotificationMessage(DidOpenNotification(p)) => Some(p.text_document.uri.clone()),
        NotificationMessage(DidCloseNotification(p)) => Some(p.text_document.uri.clone()),
        NotificationMessage(DidSaveNotification(p)) => Some(p.text_document.uri.clone()),
        NotificationMessage(DidChangeNotification(p)) => Some(p.text_document.uri.clone()),
        NotificationMessage(DidChangeWatchedFilesNotification(p)) => match &p.changes[..] {
            [] => None,
            [did_change_watched_files::FileEvent { uri, .. }, ..] => Some(uri.clone()),
        },
        RequestMessage(
            _,
            HackTestStartServerRequestFB
            | HackTestStopServerRequestFB
            | HackTestShutdownServerlessRequestFB
            | UnknownRequest(_, _)
            | InitializeRequest(_)
            | RegisterCapabilityRequest(_)
            | ShutdownRequest
            | CodeLensResolveRequest(_)
            | CompletionItemResolveRequest(_)
            | WorkspaceSymbolRequest(_)
            | ShowMessageRequestRequest(_)
            | ShowStatusRequestFB(_)
            | RageRequestFB
            | WillSaveWaitUntilRequest(_)
            | TopLevelDefNameAtPosRequest(_),
        )
        | NotificationMessage(
            ExitNotification
            | CancelRequestNotification(_)
            | LogMessageNotification(_)
            | TelemetryNotification(_, _)
            | ShowMessageNotification(_)
            | ConnectionStatusNotificationFB(_)
            | InitializedNotification
            | FindReferencesPartialResultNotification(_, _)
            | SetTraceNotification(_)
            | SetTrace(_)
            | LogTraceNotification
            | UnknownNotification(_, _),
        )
        | ResponseMessage(_, _) => None,
    }
}

pub fn request_name_to_string(request: &LspRequest) -> String {
    use LspRequest::*;
    match request {
        ShowMessageRequestRequest(_) => "window/showMessageRequest",
        ShowStatusRequestFB(_) => "window/showStatus",
        InitializeRequest(_) => "initialize",
        RegisterCapabilityRequest(_) => "client/registerCapability",
        ShutdownRequest => "shutdown",
        CodeLensResolveRequest(_) => "codeLens/resolve",
        HoverRequest(_) => "textDocument/hover",
        CodeActionRequest(_) => "textDocument/codeAction",
        CodeActionResolveRequest(_) => "codeAction/resolve",
        CompletionRequest(_) => "textDocument/completion",
        CompletionItemResolveRequest(_) => "completionItem/resolve",
        DefinitionRequest(_) => "textDocument/definition",
        TypeDefinitionRequest(_) => "textDocument/typeDefinition",
        ImplementationRequest(_) => "textDocument/implementation",
        WorkspaceSymbolRequest(_) => "workspace/symbol",
        DocumentSymbolRequest(_) => "textDocument/documentSymbol",
        FindReferencesRequest(_) => "textDocument/references",
        PrepareCallHierarchyRequest(_) => "textDocument/prepareCallHierarchy",
        CallHierarchyIncomingCallsRequest(_) => "callHierarchy/incomingCalls",
        CallHierarchyOutgoingCallsRequest(_) => "callHierarchy/outgoingCalls",
        DocumentHighlightRequest(_) => "textDocument/documentHighlight",
        DocumentFormattingRequest(_) => "textDocument/formatting",
        DocumentRangeFormattingRequest(_) => "textDocument/rangeFormatting",
        DocumentOnTypeFormattingRequest(_) => "textDocument/onTypeFormatting",
        RageRequestFB => "telemetry/rage",
        RenameRequest(_) => "textDocument/rename",
        DocumentCodeLensRequest(_) => "textDocument/codeLens",
        SignatureHelpRequest(_) => "textDocument/signatureHelp",
        AutoCloseRequest(_) => "flow/autoCloseJsx",
        HackTestStartServerRequestFB => "$test/startHhServer",
        HackTestStopServerRequestFB => "$test/stopHhServer",
        HackTestShutdownServerlessRequestFB => "$test/shutdownServerlessIde",
        WillSaveWaitUntilRequest(_) => "textDocument/willSaveWaitUntil",
        TopLevelDefNameAtPosRequest(_) => "custom/topLevelDefNameAtPos",
        UnknownRequest(method_, _params) => return method_.clone(),
    }
    .to_string()
}

pub fn result_name_to_string(result: &LspResult) -> String {
    use LspResult::*;
    match result {
        ShowMessageRequestResult(_) => "window/showMessageRequest",
        ShowStatusResultFB(_) => "window/showStatus",
        InitializeResult(_) => "initialize",
        ShutdownResult => "shutdown",
        CodeLensResolveResult(_) => "codeLens/resolve",
        HoverResult(_) => "textDocument/hover",
        CodeActionResult(_, _) => "textDocument/codeAction",
        CodeActionResolveResult(_) => "codeAction/resolve",
        CompletionResult(_) => "textDocument/completion",
        CompletionItemResolveResult(_) => "completionItem/resolve",
        DefinitionResult(_) => "textDocument/definition",
        TypeDefinitionResult(_) => "textDocument/typeDefinition",
        ImplementationResult(_) => "textDocument/implementation",
        WorkspaceSymbolResult(_) => "workspace/symbol",
        DocumentSymbolResult(_) => "textDocument/documentSymbol",
        FindReferencesResult(_) => "textDocument/references",
        PrepareCallHierarchyResult(_) => "textDocument/prepareCallHierarchy",
        CallHierarchyIncomingCallsResult(_) => "callHierarchy/incomingCalls",
        CallHierarchyOutgoingCallsResult(_) => "callHierarchy/outgoingCalls",
        DocumentHighlightResult(_) => "textDocument/documentHighlight",
        DocumentFormattingResult(_) => "textDocument/formatting",
        DocumentRangeFormattingResult(_) => "textDocument/rangeFormatting",
        DocumentOnTypeFormattingResult(_) => "textDocument/onTypeFormatting",
        RageResultFB(_) => "telemetry/rage",
        RenameResult(_) => "textDocument/rename",
        DocumentCodeLensResult(_) => "textDocument/codeLens",
        SignatureHelpResult(_) => "textDocument/signatureHelp",
        AutoCloseResult(_) => "flow/autoCloseJsx",
        HackTestStartServerResultFB => "$test/startHhServer",
        HackTestStopServerResultFB => "$test/stopHhServer",
        HackTestShutdownServerlessResultFB => "$test/shutdownServerlessIde",
        RegisterCapabilityRequestResult => "client/registerCapability",
        WillSaveWaitUntilResult(_) => "textDocument/willSaveWaitUntil",
        TopLevelDefNameAtPosResult(_) => "custom/topLevelDefNameAtPos",
        ErrorResult(e) => return format!("ERROR/{}", e.message),
    }
    .to_string()
}

pub fn notification_name_to_string(notification: &LspNotification) -> String {
    use LspNotification::*;
    match notification {
        ExitNotification => "exit",
        CancelRequestNotification(_) => "$/cancelRequest",
        PublishDiagnosticsNotification(_) => "textDocument/publishDiagnostics",
        DidOpenNotification(_) => "textDocument/didOpen",
        DidCloseNotification(_) => "textDocument/didClose",
        DidSaveNotification(_) => "textDocument/didSave",
        DidChangeNotification(_) => "textDocument/didChange",
        DidChangeWatchedFilesNotification(_) => "workspace/didChangeWatchedFiles",
        TelemetryNotification(_, _) => "telemetry/event",
        LogMessageNotification(_) => "window/logMessage",
        ShowMessageNotification(_) => "window/showMessage",
        ConnectionStatusNotificationFB(_) => "telemetry/connectionStatus",
        InitializedNotification => "initialized",
        FindReferencesPartialResultNotification(_, _) => "$/progress",
        SetTraceNotification(_) => "$/setTraceNotification",
        SetTrace(_) => "$/setTrace",
        LogTraceNotification => "$/logTraceNotification",
        UnknownNotification(method_, _params) => return method_.clone(),
    }
    .to_string()
}

pub fn message_name_to_string(message: &LspMessage) -> String {
    match message {
        LspMessage::RequestMessage(_, r) => request_name_to_string(r),
        LspMessage::NotificationMessage(n) => notification_name_to_string(n),
        LspMessage::ResponseMessage(_, r) => result_name_to_string(r),
    }
}

pub fn denorm_message_to_string(message: &LspMessage) -> String {
    let uri = match get_uri_opt(message) {
        Some(document_uri::Uri(uri)) => format!("({})", uri),
        None => "".to_string(),
    };
    match message {
        LspMessage::RequestMessage(id, r) => format!(
            "request {} {}{}",
            id_to_string(id),
            request_name_to_string(r),
            uri
        ),
        LspMessage::NotificationMessage(n) => {
            format!("notification {}{}", notification_name_to_string(n), uri)
        }
        LspMessage::ResponseMessage(id, LspResult::ErrorResult(e)) => {
            format!("error {} {} {}", id_to_string(id), e.message, uri)
        }
        LspMessage::ResponseMessage(id, r) => format!(
            "result {} {}{}",
            id_to_string(id),
            result_name_to_string(r),
            uri
        ),
    }
}

pub fn parse_lsp_request(method_: &str, params: Option<&Json>) -> Result<LspRequest, LspFmtError> {
    use LspRequest::*;
    Ok(match method_ {
        "initialize" => InitializeRequest(parse_initialize(params)?),
        "shutdown" => ShutdownRequest,
        "codeLens/resolve" => CodeLensResolveRequest(parse_code_lens_resolve(params)?),
        "textDocument/hover" => HoverRequest(parse_hover(params)?),
        "textDocument/codeAction" => CodeActionRequest(parse_code_action_request(params)?),
        "codeAction/resolve" => CodeActionResolveRequest(parse_code_action_resolve_request(params)?),
        "textDocument/completion" => CompletionRequest(parse_completion(params)?),
        "completionItem/resolve" => CompletionItemResolveRequest(parse_completion_item(params)?),
        "textDocument/definition" => DefinitionRequest(parse_text_document_position_params(params)?),
        "textDocument/typeDefinition" => {
            TypeDefinitionRequest(parse_text_document_position_params(params)?)
        }
        "textDocument/implementation" => {
            ImplementationRequest(parse_text_document_position_params(params)?)
        }
        "workspace/symbol" => WorkspaceSymbolRequest(parse_workspace_symbol(params)?),
        "textDocument/documentSymbol" => DocumentSymbolRequest(parse_document_symbol(params)?),
        "textDocument/references" => FindReferencesRequest(parse_find_references(params)?),
        "textDocument/prepareCallHierarchy" => {
            PrepareCallHierarchyRequest(parse_text_document_position_params(params)?)
        }
        "callHierarchy/incomingCalls" => {
            CallHierarchyIncomingCallsRequest(parse_call_hierarchy_calls(params)?)
        }
        "callHierarchy/outgoingCalls" => {
            CallHierarchyOutgoingCallsRequest(parse_call_hierarchy_calls(params)?)
        }
        "textDocument/rename" => RenameRequest(parse_document_rename(params)?),
        "textDocument/documentHighlight" => {
            DocumentHighlightRequest(parse_document_highlight(params)?)
        }
        "textDocument/formatting" => DocumentFormattingRequest(parse_document_formatting(params)?),
        "textDocument/rangeFormatting" => {
            DocumentRangeFormattingRequest(parse_document_range_formatting(params)?)
        }
        "textDocument/onTypeFormatting" => {
            DocumentOnTypeFormattingRequest(parse_document_on_type_formatting(params)?)
        }
        "textDocument/signatureHelp" => SignatureHelpRequest(parse_signature_help(params)?),
        "flow/autoCloseJsx" => AutoCloseRequest(parse_auto_close(params)?),
        "textDocument/codeLens" => DocumentCodeLensRequest(parse_document_code_lens(params)?),
        "telemetry/rage" => RageRequestFB,
        "$test/startHhServer" => HackTestStartServerRequestFB,
        "$test/stopHhServer" => HackTestStopServerRequestFB,
        "$test/shutdownServerlessIde" => HackTestShutdownServerlessRequestFB,
        "textDocument/willSaveWaitUntil" => {
            WillSaveWaitUntilRequest(parse_will_save_wait_until(params)?)
        }
        "custom/topLevelDefNameAtPos" => TopLevelDefNameAtPosRequest(
            top_level_def_name_at_pos::params_of_yojson(match params {
                Some(params) => params,
                // `Option.value_exn`
                None => panic!("Option.value_exn None"),
            })?,
        ),
        "window/showMessageRequest" | "window/showStatus" | _ => {
            UnknownRequest(method_.to_string(), params.cloned())
        }
    })
}

pub fn parse_lsp_notification(
    method_: &str, params: Option<&Json>,
) -> Result<LspNotification, LspFmtError> {
    use LspNotification::*;
    Ok(match method_ {
        "$/cancelRequest" => CancelRequestNotification(parse_cancel_request(params)?),
        "$/setTraceNotification" => SetTraceNotification(parse_set_trace_notification(params)),
        "$/setTrace" => SetTrace(parse_set_trace(params)),
        "$/logTraceNotification" => LogTraceNotification,
        "initialized" => InitializedNotification,
        "exit" => ExitNotification,
        "textDocument/didOpen" => DidOpenNotification(parse_did_open(params)?),
        "textDocument/didClose" => DidCloseNotification(parse_did_close(params)?),
        "textDocument/didSave" => DidSaveNotification(parse_did_save(params)?),
        "textDocument/didChange" => DidChangeNotification(parse_did_change(params)?),
        "workspace/didChangeWatchedFiles" => {
            DidChangeWatchedFilesNotification(parse_did_change_watched_files(params)?)
        }
        "textDocument/publishDiagnostics"
        | "window/logMessage"
        | "window/showMessage"
        | "window/progress"
        | "window/actionRequired"
        | "telemetry/connectionStatus"
        | _ => UnknownNotification(method_.to_string(), params.cloned()),
    })
}

pub fn parse_lsp_result(request: &LspRequest, result: &Json) -> Result<LspResult, LspFmtError> {
    use LspRequest::*;
    let method_ = request_name_to_string(request);
    Ok(match request {
        ShowMessageRequestRequest(_) => {
            LspResult::ShowMessageRequestResult(parse_result_show_message_request(Some(result)))
        }
        ShowStatusRequestFB(_) => LspResult::ShowStatusResultFB(()),
        RegisterCapabilityRequest(_) => LspResult::RegisterCapabilityRequestResult,
        InitializeRequest(_)
        | ShutdownRequest
        | CodeLensResolveRequest(_)
        | HoverRequest(_)
        | CodeActionRequest(_)
        | CodeActionResolveRequest(_)
        | CompletionRequest(_)
        | CompletionItemResolveRequest(_)
        | DefinitionRequest(_)
        | TypeDefinitionRequest(_)
        | ImplementationRequest(_)
        | WorkspaceSymbolRequest(_)
        | DocumentSymbolRequest(_)
        | FindReferencesRequest(_)
        | PrepareCallHierarchyRequest(_)
        | CallHierarchyIncomingCallsRequest(_)
        | CallHierarchyOutgoingCallsRequest(_)
        | DocumentHighlightRequest(_)
        | DocumentFormattingRequest(_)
        | DocumentRangeFormattingRequest(_)
        | DocumentOnTypeFormattingRequest(_)
        | RageRequestFB
        | RenameRequest(_)
        | DocumentCodeLensRequest(_)
        | SignatureHelpRequest(_)
        | AutoCloseRequest(_)
        | HackTestStartServerRequestFB
        | HackTestStopServerRequestFB
        | HackTestShutdownServerlessRequestFB
        | WillSaveWaitUntilRequest(_)
        | TopLevelDefNameAtPosRequest(_)
        | UnknownRequest(_, _) => {
            raise_parse_error(format!("Don't know how to parse LSP response {}", method_))?
        }
    })
}

/// parse_lsp: non-jsonrpc inputs - will raise an exception
/// requests and notifications - will raise an exception if they're malformed,
///   otherwise return Some
/// responses - will raise an exception if they're malformed, will return None
///   if they're absent from the "outstanding" map, otherwise return Some.
pub fn parse_lsp(
    json: &Json, outstanding: impl Fn(&LspId) -> LspRequest,
) -> Result<LspMessage, LspFmtError> {
    let json = Some(json);
    let id = parse_id_opt(jget::val_opt(json, "id"))?;
    let method_opt = jget::string_opt(json, "method");
    let params = jget::val_opt(json, "params");
    let result = jget::val_opt(json, "result");
    let error = jget::val_opt(json, "error");
    Ok(match (id, method_opt, result, error) {
        (None, Some(method_), _, _) => {
            LspMessage::NotificationMessage(parse_lsp_notification(&method_, params)?)
        }
        (Some(id), Some(method_), _, _) => {
            let request = parse_lsp_request(&method_, params)?;
            LspMessage::RequestMessage(id, request)
        }
        (Some(id), _, Some(result), _) => {
            let request = outstanding(&id);
            let result = parse_lsp_result(&request, result)?;
            LspMessage::ResponseMessage(id, result)
        }
        (Some(id), _, _, Some(error)) => {
            let error = parse_error(error)?;
            LspMessage::ResponseMessage(id, LspResult::ErrorResult(error))
        }
        (_, _, _, _) => raise_parse_error("Not JsonRPC".to_string())?,
    })
}

pub fn print_lsp_request(id: &LspId, request: &LspRequest) -> Json {
    use LspRequest::*;
    let method_ = request_name_to_string(request);
    let params = match request {
        ShowMessageRequestRequest(r) => print_show_message_request(r),
        ShowStatusRequestFB(r) => print_show_status(r),
        RegisterCapabilityRequest(r) => print_register_capability(r),
        InitializeRequest(_)
        | ShutdownRequest
        | HoverRequest(_)
        | CodeActionRequest(_)
        | CodeActionResolveRequest(_)
        | CodeLensResolveRequest(_)
        | CompletionRequest(_)
        | CompletionItemResolveRequest(_)
        | DefinitionRequest(_)
        | TypeDefinitionRequest(_)
        | ImplementationRequest(_)
        | WorkspaceSymbolRequest(_)
        | DocumentSymbolRequest(_)
        | FindReferencesRequest(_)
        | PrepareCallHierarchyRequest(_)
        | CallHierarchyIncomingCallsRequest(_)
        | CallHierarchyOutgoingCallsRequest(_)
        | DocumentHighlightRequest(_)
        | DocumentFormattingRequest(_)
        | DocumentRangeFormattingRequest(_)
        | DocumentOnTypeFormattingRequest(_)
        | RageRequestFB
        | RenameRequest(_)
        | DocumentCodeLensRequest(_)
        | SignatureHelpRequest(_)
        | AutoCloseRequest(_)
        | HackTestStartServerRequestFB
        | HackTestStopServerRequestFB
        | HackTestShutdownServerlessRequestFB
        | WillSaveWaitUntilRequest(_)
        | TopLevelDefNameAtPosRequest(_)
        | UnknownRequest(_, _) => panic!("Don't know how to print request {}", method_),
    };
    assoc(vec![
        ("jsonrpc", Json::String("2.0".to_string())),
        ("id", print_id(id)),
        ("method", Json::String(method_)),
        ("params", params),
    ])
}

pub fn print_lsp_response(id: &LspId, result: &LspResult) -> Json {
    use LspResult::*;
    let method_ = result_name_to_string(result);
    let json = match result {
        InitializeResult(r) => print_initialize(r),
        ShutdownResult => print_shutdown(),
        CodeLensResolveResult(r) => print_code_lens_resolve(r),
        HoverResult(r) => print_hover(r),
        CodeActionResult(r, p) => print_code_action_result(r, p),
        CodeActionResolveResult(r) => print_code_action_resolve_result(r),
        CompletionResult(r) => print_completion(r),
        CompletionItemResolveResult(r) => print_completion_item(r),
        DefinitionResult(r) => print_definition_locations(r),
        TypeDefinitionResult(r) => print_definition_locations(r),
        ImplementationResult(r) => print_locations(r),
        WorkspaceSymbolResult(r) => print_workspace_symbol(r),
        DocumentSymbolResult(r) => print_document_symbol(r),
        FindReferencesResult(r) => print_locations(r),
        PrepareCallHierarchyResult(r) => print_prepare_call_hierarchy_result(r),
        CallHierarchyIncomingCallsResult(r) => print_call_hierarchy_incoming_calls_result(r),
        CallHierarchyOutgoingCallsResult(r) => print_call_hierarchy_outgoing_calls_result(r),
        DocumentHighlightResult(r) => print_document_highlight(r),
        DocumentFormattingResult(r) => print_document_formatting(r),
        DocumentRangeFormattingResult(r) => print_document_range_formatting(r),
        DocumentOnTypeFormattingResult(r) => print_document_on_type_formatting(r),
        RageResultFB(r) => print_rage(r),
        RenameResult(r) => print_workspace_edit(r),
        DocumentCodeLensResult(r) => print_document_code_lens(r),
        SignatureHelpResult(r) => print_signature_help(r),
        AutoCloseResult(r) => print_auto_close(r),
        HackTestStartServerResultFB => Json::Null,
        HackTestStopServerResultFB => Json::Null,
        HackTestShutdownServerlessResultFB => Json::Null,
        ShowMessageRequestResult(_) | ShowStatusResultFB(_) | RegisterCapabilityRequestResult => {
            panic!("Don't know how to print result {}", method_)
        }
        WillSaveWaitUntilResult(r) => print_text_edits(r),
        TopLevelDefNameAtPosResult(r) => top_level_def_name_at_pos::yojson_of_result(r),
        ErrorResult(e) => print_error(e),
    };
    match result {
        ErrorResult(_) => assoc(vec![
            ("jsonrpc", Json::String("2.0".to_string())),
            ("id", print_id(id)),
            ("error", json),
        ]),
        _ => assoc(vec![
            ("jsonrpc", Json::String("2.0".to_string())),
            ("id", print_id(id)),
            ("result", json),
        ]),
    }
}

pub fn print_lsp_notification(notification: &LspNotification) -> Json {
    use LspNotification::*;
    let method_ = notification_name_to_string(notification);
    let params = match notification {
        CancelRequestNotification(r) => print_cancel_request(r),
        SetTraceNotification(r) => print_set_trace_notification(r),
        SetTrace(r) => print_set_trace(r),
        PublishDiagnosticsNotification(r) => print_diagnostics(r),
        FindReferencesPartialResultNotification(token, r) => {
            print_find_references_partial_result(token, r)
        }
        TelemetryNotification(r, extras) => print_telemetry_notification(r, extras),
        LogMessageNotification(r) => print_log_message(r.type_, &r.message),
        ShowMessageNotification(r) => print_show_message(r.type_, &r.message),
        ConnectionStatusNotificationFB(r) => print_connection_status(r),
        ExitNotification
        | InitializedNotification
        | LogTraceNotification
        | DidOpenNotification(_)
        | DidCloseNotification(_)
        | DidSaveNotification(_)
        | DidChangeNotification(_)
        | DidChangeWatchedFilesNotification(_)
        | UnknownNotification(_, _) => panic!("Don't know how to print notification {}", method_),
    };
    assoc(vec![
        ("jsonrpc", Json::String("2.0".to_string())),
        ("method", Json::String(method_)),
        ("params", params),
    ])
}

pub fn print_lsp(message: &LspMessage) -> Json {
    match message {
        LspMessage::RequestMessage(id, request) => print_lsp_request(id, request),
        LspMessage::ResponseMessage(id, result) => print_lsp_response(id, result),
        LspMessage::NotificationMessage(notification) => print_lsp_notification(notification),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn json(s: &str) -> Json {
        yojson::from_string(s).unwrap()
    }

    fn no_outstanding(id: &LspId) -> LspRequest {
        panic!("no outstanding request {:?}", id)
    }

    /// The `Jget.Parse` or `LspException` that `f` raises, or the
    /// `failwith` (a panic).
    fn raised<A>(f: impl FnOnce() -> Result<A, LspFmtError>) -> String {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
            Ok(Ok(_)) => panic!("no exception"),
            Ok(Err(LspFmtError::Parse(p))) => format!("Parse {}", p.0),
            Ok(Err(LspFmtError::LspException(e))) => {
                format!("LspException {:?} {}", e.0.code, e.0.message)
            }
            Ok(Err(LspFmtError::OfYojsonError(e))) => format!("OfYojsonError {}", e.0),
            Err(payload) => match payload.downcast::<String>() {
                Ok(s) => format!("Failure {}", s),
                Err(_) => "<exception>".to_string(),
            },
        }
    }

    #[test]
    fn ids() {
        assert_eq!(parse_id(&json("3")).unwrap(), NumberId(3));
        assert_eq!(parse_id(&json("\"x\"")).unwrap(), StringId("x".to_string()));
        assert_eq!(
            raised(|| parse_id(&json("1.5"))),
            "LspException ParseError float ids not allowed: 1.5"
        );
        assert_eq!(
            raised(|| parse_id(&json("2.0"))),
            "LspException ParseError float ids not allowed: 2."
        );
        assert_eq!(
            raised(|| parse_id(&json("99999999999999999999"))),
            "LspException ParseError float ids not allowed: 99999999999999999999"
        );
        assert_eq!(
            raised(|| parse_id(&json("null"))),
            "LspException ParseError not an id: null"
        );
        assert_eq!(yojson::to_string(&print_id(&NumberId(7))), "7");
        assert_eq!(id_to_string(&StringId("a".to_string())), "\"a\"");
    }

    #[test]
    fn evaluation_order_of_errors() {
        // The last field of the record is evaluated first.
        assert_eq!(raised(|| parse_position(Some(&json("{}")))), "Parse character");
        assert_eq!(raised(|| parse_range_exn(Some(&json("{}")))), "Parse end");
        assert_eq!(
            raised(|| parse_text_document_position_params(Some(&json(r#"{"textDocument": {}}"#)))),
            "Parse position"
        );
        assert_eq!(
            raised(|| parse_text_document_item(Some(&json(r#"{"version": 99999999999999999999}"#)))),
            "Parse text"
        );
        assert_eq!(
            raised(|| parse_text_document_item(Some(&json(
                r#"{"text": "", "version": 99999999999999999999}"#
            )))),
            "Parse not an int: 99999999999999999999"
        );
        assert_eq!(
            raised(|| parse_lsp(&json("{}"), no_outstanding)),
            "LspException ParseError Not JsonRPC"
        );
        assert_eq!(
            raised(|| parse_lsp(&json(r#"{"id": 1, "result": 3}"#), |_| LspRequest::ShutdownRequest)),
            "LspException ParseError Don't know how to parse LSP response shutdown"
        );
        assert_eq!(
            raised(|| parse_lsp(
                &json(r#"{"method": "workspace/didChangeWatchedFiles", "params": {"changes": [{"uri": "a", "type": 9}]}}"#),
                no_outstanding
            )),
            "Failure Invalid file change type 9"
        );
    }

    #[test]
    fn requests_and_notifications() {
        let m = parse_lsp(
            &json(
                r#"{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
                    "processId": 12, "rootUri": "file:///r", "trace": "verbose",
                    "initializationOptions": {"namingTableSavedStateTestDelay": 2, "delayUntilDoneInit": true},
                    "capabilities": {
                        "window": {"status": {}},
                        "textDocument": {
                            "synchronization": {"willSaveWaitUntil": true},
                            "completion": {"completionItem": {"snippetSupport": true}},
                            "codeAction": {"codeActionLiteralSupport": {"valueSet": ["quickfix", 3, "refactor.inline"]}}
                        },
                        "experimental": {"autoCloseJsx": true}
                    }}}"#,
            ),
            no_outstanding,
        ).unwrap();
        let p = match &m {
            LspMessage::RequestMessage(NumberId(1), LspRequest::InitializeRequest(p)) => p,
            m => panic!("{:?}", m),
        };
        assert_eq!(p.process_id, Some(12));
        assert_eq!(p.root_uri, Some(uri_of_string("file:///r")));
        assert_eq!(p.trace, initialize::Trace::Verbose);
        assert_eq!(p.initialization_options.naming_table_saved_state_test_delay, 2.0);
        assert!(p.initialization_options.delay_until_done_init);
        assert!(p.client_capabilities.window.status);
        assert!(!p.client_capabilities.telemetry.connection_status);
        let td = &p.client_capabilities.text_document;
        assert!(td.synchronization.will_save_wait_until && !td.synchronization.did_save);
        assert!(td.completion.completion_item.snippet_support);
        assert_eq!(
            td.code_action
                .code_action_literal_support
                .as_ref()
                .unwrap()
                .code_action_value_set,
            vec![
                code_action_kind::quickfix(),
                code_action_kind::refactor_inline()
            ]
        );
        assert!(p.client_capabilities.client_experimental.auto_close_jsx);
        assert_eq!(denorm_message_to_string(&m), "request 1 initialize");

        let m = parse_lsp(
            &json(
                r#"{"method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": "file:///a", "version": 3},
                    "contentChanges": [{"text": "x"}, {"range": {"start": {"line": 0, "character": 1}, "end": {"line": 0, "character": 2}}, "rangeLength": 1, "text": "y"}]}}"#,
            ),
            no_outstanding,
        ).unwrap();
        match &m {
            LspMessage::NotificationMessage(LspNotification::DidChangeNotification(p)) => {
                assert_eq!(p.text_document.version, 3);
                assert_eq!(p.content_changes.len(), 2);
                assert_eq!(p.content_changes[0].range, None);
                assert_eq!(p.content_changes[1].range_length, Some(1));
            }
            m => panic!("{:?}", m),
        }
        assert_eq!(
            denorm_message_to_string(&m),
            "notification textDocument/didChange(file:///a)"
        );

        let m = parse_lsp(
            &json(
                r#"{"id": "s", "method": "textDocument/completion", "params": {
                    "textDocument": {"uri": "file:///a"}, "position": {"line": 1, "character": 2},
                    "context": {"triggerKind": 2, "triggerCharacter": ">"}}}"#,
            ),
            no_outstanding,
        ).unwrap();
        match &m {
            LspMessage::RequestMessage(StringId(_), LspRequest::CompletionRequest(p)) => {
                assert_eq!(
                    p.context,
                    Some(completion::CompletionContext {
                        trigger_kind: completion::CompletionTriggerKind::TriggerCharacter,
                        trigger_character: Some(">".to_string())
                    })
                )
            }
            m => panic!("{:?}", m),
        }
        assert_eq!(
            raised(|| parse_completion(Some(&json(
                r#"{"textDocument": {"uri": "a"}, "position": {"line": 1, "character": 2}, "context": {"triggerKind": 7}}"#
            )))),
            "Failure Unsupported trigger kind: 7"
        );

        // Requests and notifications that are not handled.
        let m = parse_lsp(&json(r#"{"id": 2, "method": "window/showStatus"}"#), no_outstanding).unwrap();
        assert_eq!(
            m,
            LspMessage::RequestMessage(
                NumberId(2),
                LspRequest::UnknownRequest("window/showStatus".to_string(), None)
            )
        );
        let m = parse_lsp(
            &json(r#"{"method": "$test/x", "params": {"a": 1}}"#),
            no_outstanding,
        ).unwrap();
        assert_eq!(message_name_to_string(&m), "$test/x");

        // Responses to our requests.
        let request = LspRequest::ShowMessageRequestRequest(show_message_request::ShowMessageRequestParams {
            type_: message_type::InfoMessage,
            message: "m".to_string(),
            actions: vec![],
        });
        let m = parse_lsp(&json(r#"{"id": 5, "result": {"title": "OK"}}"#), |_| request.clone()).unwrap();
        assert_eq!(
            m,
            LspMessage::ResponseMessage(
                NumberId(5),
                LspResult::ShowMessageRequestResult(Some(show_message_request::MessageActionItem {
                    title: "OK".to_string()
                }))
            )
        );
        let m = parse_lsp(
            &json(r#"{"id": 6, "error": {"code": -1, "message": "no", "data": [1]}}"#),
            no_outstanding,
        ).unwrap();
        assert_eq!(
            denorm_message_to_string(&m),
            "error 6 no "
        );
        match &m {
            LspMessage::ResponseMessage(_, LspResult::ErrorResult(e)) => {
                assert_eq!(e.code, error::UnknownErrorCode);
                assert_eq!(error_to_log_string(e), "no [UnknownErrorCode]\n[ 1 ]");
            }
            m => panic!("{:?}", m),
        }
    }

    #[test]
    fn code_actions() {
        let params = parse_code_action_request(Some(&json(
            r#"{"textDocument": {"uri": "file:///a"},
                "range": {"start": {"line": 1, "character": 2}, "end": {"line": 1, "character": 3}},
                "context": {"diagnostics": [{"range": {"start": {"line": 1, "character": 2}, "end": {"line": 1, "character": 3}}, "severity": 1, "code": 4110, "message": "bad", "data": {"x": 1}}], "only": ["refactor"]}}"#,
        ))).unwrap();
        assert_eq!(params.context.only, Some(vec![code_action_kind::refactor()]));
        let diagnostic = &params.context.diagnostics[0];
        assert_eq!(diagnostic.code, publish_diagnostics::DiagnosticCode::IntCode(4110));
        let action = |action| {
            code_action::CommandOrAction_::Action(code_action::T {
                title: "Extract".to_string(),
                kind: code_action_kind::refactor_extract(),
                diagnostics: vec![],
                action,
                is_ai: None,
            })
        };
        let result = vec![
            action(code_action::EditAndOrCommand::UnresolvedEdit(())),
            code_action::CommandOrAction_::Command(command::T {
                title: "c".to_string(),
                command: "cmd".to_string(),
                arguments: vec![Json::Int(1)],
            }),
        ];
        assert_eq!(
            yojson::to_string(&print_lsp_response(
                &NumberId(4),
                &LspResult::CodeActionResult(result, params.clone())
            )),
            concat!(
                r#"{"jsonrpc":"2.0","id":4,"result":[{"title":"Extract","kind":"refactor.extract","diagnostics":[],"#,
                r#""data":{"originalRequest":{"textDocument":{"uri":"file:///a"},"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":3}},"#,
                r#""context":{"diagnostics":[{"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":3}},"severity":1,"code":4110,"message":"bad","relatedInformation":[],"relatedLocations":[],"data":{"x":1}}]}}}},"#,
                r#"{"title":"c","command":"cmd","arguments":[1]}]}"#
            )
        );
        let resolve = parse_code_action_resolve_request(Some(&json(&format!(
            r#"{{"title": "Extract", "data": {{"originalRequest": {}}}}}"#,
            yojson::to_string(&assoc(vec![
                ("textDocument", assoc(vec![("uri", s("file:///a"))])),
                ("range", print_range(&params.range)),
                ("context", assoc(vec![("diagnostics", Json::List(vec![]))])),
            ]))
        )))).unwrap();
        assert_eq!(resolve.title, "Extract");
        assert_eq!(resolve.data.range, params.range);
        let edit = workspace_edit::T {
            changes: document_uri::map::T::unit(uri_of_string("file:///a"), vec![]),
        };
        let resolved: code_action_resolve::Result = Ok(code_action::CommandOrAction_::Action(code_action::T {
            title: "Extract".to_string(),
            kind: code_action_kind::refactor_extract(),
            diagnostics: vec![],
            action: code_action::EditAndOrCommand::EditOnly(edit),
            is_ai: Some(true),
        }));
        assert_eq!(
            yojson::to_string(&print_code_action_resolve_result(&resolved)),
            r#"{"title":"Extract","kind":"refactor.extract","diagnostics":[],"edit":{"changes":{"file:///a":[]}},"data":{"isAI":true}}"#
        );
    }

    #[test]
    fn printers() {
        let item = completion::CompletionItem {
            label: "f".to_string(),
            kind: Some(completion::CompletionItemKind::Function),
            detail: None,
            documentation: Some(completion::CompletionDocumentation::MarkedStringsDocumentation(vec![
                MarkedString::MarkedCode("hack".to_string(), "function f(): void".to_string()),
                MarkedString::MarkedString("  Docs  ".to_string()),
            ])),
            sort_text: None,
            filter_text: None,
            insert_text: Some("f()".to_string()),
            insert_text_format: Some(completion::InsertTextFormat::SnippetFormat),
            text_edit: None,
            additional_text_edits: vec![],
            command: None,
            data: Some(json(r#"{"k":1}"#)),
        };
        assert_eq!(
            yojson::to_string(&print_completion_item(&item)),
            r#"{"label":"f","kind":3,"documentation":{"kind":"markdown","value":"```hack\nfunction f(): void\n```\n  Docs"},"insertText":"f()","insertTextFormat":2,"data":{"k":1}}"#
        );
        // `parse_completionItem` keeps the documentation as it is.
        let parsed = parse_completion_item(Some(&print_completion_item(&item))).unwrap();
        assert_eq!(parsed.label, "f");
        assert!(matches!(
            parsed.documentation,
            Some(completion::CompletionDocumentation::UnparsedDocumentation(_))
        ));
        let diagnostics = publish_diagnostics::PublishDiagnosticsParams {
            uri: uri_of_string("file:///a"),
            diagnostics: vec![],
            is_status_fb: true,
        };
        assert_eq!(
            yojson::to_string(&print_lsp_notification(
                &LspNotification::PublishDiagnosticsNotification(diagnostics)
            )),
            r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///a","diagnostics":[],"isStatusFB":true}}"#
        );
        let status = show_status_fb::ShowStatusParams {
            request: show_status_fb::ShowStatusRequestParams {
                type_: message_type::InfoMessage,
                message: "m".to_string(),
            },
            progress: Some(3),
            total: None,
            short_message: Some("s".to_string()),
            telemetry: None,
        };
        assert_eq!(
            yojson::to_string(&print_lsp_request(
                &NumberId(1),
                &LspRequest::ShowStatusRequestFB(status)
            )),
            r#"{"jsonrpc":"2.0","id":1,"method":"window/showStatus","params":{"type":3,"message":"m","shortMessage":"s","progress":{"numerator":3}}}"#
        );
        let registration = register_capability::make_registration(
            LspRegistrationOptions::DidChangeWatchedFilesRegistrationOptions(
                did_change_watched_files::RegisterOptions {
                    watchers: vec![did_change_watched_files::FileSystemWatcher {
                        glob_pattern: "**/*.php".to_string(),
                    }],
                },
            ),
        );
        assert_eq!(
            yojson::to_string(&print_lsp_request(
                &NumberId(2),
                &LspRequest::RegisterCapabilityRequest(register_capability::Params {
                    registrations: vec![registration]
                })
            )),
            r#"{"jsonrpc":"2.0","id":2,"method":"client/registerCapability","params":{"registrations":[{"id":"did-change-watched-files","method":"workspace/didChangeWatchedFiles","registerOptions":{"watchers":[{"globPattern":"**/*.php","kind":7}]}}]}}"#
        );
        assert_eq!(
            raised(|| Ok(print_lsp_request(&NumberId(3), &LspRequest::ShutdownRequest))),
            "Failure Don't know how to print request shutdown"
        );
        assert_eq!(
            raised(|| Ok(print_lsp_notification(&LspNotification::ExitNotification))),
            "Failure Don't know how to print notification exit"
        );
        // The changes of a workspace edit are printed in decreasing order of
        // their URIs (`Wrapped_map.elements`).
        let mut changes = document_uri::map::T::new();
        changes.insert(uri_of_string("a"), vec![]);
        changes.insert(uri_of_string("b"), vec![]);
        assert_eq!(
            yojson::to_string(&print_workspace_edit(&workspace_edit::T { changes })),
            r#"{"changes":{"b":[],"a":[]}}"#
        );
        assert_eq!(
            yojson::to_string(&print_lsp_response(
                &StringId("x".to_string()),
                &LspResult::TopLevelDefNameAtPosResult(None)
            )),
            r#"{"jsonrpc":"2.0","id":"x","result":null}"#
        );
    }
}

/// Round trips of the LSP exchanges recorded for `test/integration`
/// (`test/integration/data/lsp_exchanges`): every message parses, and every
/// response and notification of the server, parsed back to its `Lsp` value,
/// is printed again as it was recorded (in the order of its keys).
///
/// `Lsp_fmt` has no parsers for the results of requests (only the client
/// sends requests), so the results are parsed with the small parsers below,
/// built on those of `Lsp_fmt`. `powered_by`, which `Client_lsp` adds to some
/// messages, is not part of what `Lsp_fmt` prints, and is left out.
#[cfg(test)]
mod exchange_tests {
    use std::collections::HashMap;
    use std::path::PathBuf;

    use super::*;

    fn data_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../test/integration/data/lsp_exchanges")
    }

    fn read_messages(path: &std::path::Path) -> Vec<Json> {
        let text = std::fs::read_to_string(path).unwrap();
        match yojson::from_string(&text).unwrap() {
            Json::List(l) => l,
            j => panic!("{}: not a list: {}", path.display(), yojson::to_string(&j)),
        }
    }

    fn without_powered_by(json: &Json) -> Json {
        match json {
            Json::Assoc(fields) => Json::Assoc(
                fields
                    .iter()
                    .filter(|(k, _)| k != "powered_by")
                    .cloned()
                    .collect(),
            ),
            _ => json.clone(),
        }
    }

    fn parse_definition_location(j: Option<&Json>) -> definition_location::T {
        let title = jget::string_opt(j, "title");
        let location = parse_location(j).unwrap();
        definition_location::T { location, title }
    }

    fn parse_locations(j: &Json) -> Vec<location::T> {
        match j {
            Json::List(l) => l.iter().map(|j| parse_location(Some(j)).unwrap()).collect(),
            _ => panic!("not a list of locations"),
        }
    }

    fn parse_workspace_edit(j: Option<&Json>) -> workspace_edit::T {
        let mut changes = document_uri::map::T::new();
        match jget::obj_exn(j, "changes").unwrap() {
            Some(Json::Assoc(fields)) => {
                for (uri, edits) in fields {
                    let edits = match edits {
                        Json::List(l) => {
                            l.iter().map(|e| parse_text_edit(Some(e)).unwrap().unwrap()).collect()
                        }
                        _ => panic!("not a list of edits"),
                    };
                    changes.insert(uri_of_string(uri), edits);
                }
            }
            _ => unreachable!(),
        }
        workspace_edit::T { changes }
    }

    fn strings(j: Option<&Json>, key: &str) -> Vec<String> {
        jget::string_array_exn(j, key).unwrap()
    }

    fn parse_server_capabilities(j: Option<&Json>) -> initialize::ServerCapabilities {
        use initialize::*;
        let sync = jget::obj_exn(j, "textDocumentSync").unwrap();
        let resolve_provider = |key: &str| {
            jget::obj_opt(j, key).map(|o| jget::bool_exn(Some(o), "resolveProvider").unwrap())
        };
        ServerCapabilities {
            text_document_sync: TextDocumentSyncOptions {
                open_close: jget::bool_exn(sync, "openClose").unwrap(),
                change: text_document_sync_kind_of_enum(jget::int_exn(sync, "change").unwrap()).unwrap(),
                will_save: jget::bool_exn(sync, "willSave").unwrap(),
                will_save_wait_until: jget::bool_exn(sync, "willSaveWaitUntil").unwrap(),
                did_save: jget::obj_opt(sync, "save").map(|o| SaveOptions {
                    include_text: jget::bool_exn(Some(o), "includeText").unwrap(),
                }),
            },
            hover_provider: jget::bool_exn(j, "hoverProvider").unwrap(),
            completion_provider: jget::obj_opt(j, "completionProvider").map(|o| {
                completion_options::T {
                    resolve_provider: jget::bool_exn(Some(o), "resolveProvider").unwrap(),
                    completion_trigger_characters: strings(Some(o), "triggerCharacters"),
                }
            }),
            signature_help_provider: jget::obj_opt(j, "signatureHelpProvider").map(|o| {
                SignatureHelpOptions {
                    sighelp_trigger_characters: strings(Some(o), "triggerCharacters"),
                }
            }),
            definition_provider: jget::bool_exn(j, "definitionProvider").unwrap(),
            type_definition_provider: jget::bool_exn(j, "typeDefinitionProvider").unwrap(),
            references_provider: jget::bool_exn(j, "referencesProvider").unwrap(),
            // Not printed.
            call_hierarchy_provider: true,
            document_highlight_provider: jget::bool_exn(j, "documentHighlightProvider").unwrap(),
            document_symbol_provider: jget::bool_exn(j, "documentSymbolProvider").unwrap(),
            workspace_symbol_provider: jget::bool_exn(j, "workspaceSymbolProvider").unwrap(),
            code_action_provider: resolve_provider("codeActionProvider")
                .map(|resolve_provider| code_action_options::T { resolve_provider }),
            code_lens_provider: resolve_provider("codeLensProvider").map(|codelens_resolve_provider| {
                CodeLensOptions {
                    codelens_resolve_provider,
                }
            }),
            document_formatting_provider: jget::bool_exn(j, "documentFormattingProvider").unwrap(),
            document_range_formatting_provider: jget::bool_exn(j, "documentRangeFormattingProvider").unwrap(),
            document_on_type_formatting_provider: jget::obj_opt(j, "documentOnTypeFormattingProvider")
                .map(|o| DocumentOnTypeFormattingOptions {
                    first_trigger_character: jget::string_exn(Some(o), "firstTriggerCharacter").unwrap(),
                    more_trigger_character: strings(Some(o), "moreTriggerCharacter"),
                }),
            rename_provider: jget::bool_exn(j, "renameProvider").unwrap(),
            document_link_provider: resolve_provider("documentLinkProvider").map(
                |doclink_resolve_provider| DocumentLinkOptions {
                    doclink_resolve_provider,
                },
            ),
            execute_command_provider: jget::obj_opt(j, "executeCommandProvider").map(|o| {
                ExecuteCommandOptions {
                    commands: strings(Some(o), "commands"),
                }
            }),
            implementation_provider: jget::bool_exn(j, "implementationProvider").unwrap(),
            rage_provider_fb: jget::bool_exn(j, "rageProvider").unwrap(),
            server_experimental: jget::obj_opt(j, "experimental").map(|o| {
                server_experimental_capabilities::T {
                    snippet_text_edit: jget::bool_exn(Some(o), "snippetTextEdit").unwrap(),
                    auto_close_jsx: jget::bool_exn(Some(o), "autoCloseJsx").unwrap(),
                }
            }),
        }
    }

    /// The result of a request, from its JSON.
    fn parse_result(request: &LspRequest, result: &Json) -> LspResult {
        use LspRequest::*;
        match request {
            InitializeRequest(_) => LspResult::InitializeResult(initialize::Result {
                server_capabilities: parse_server_capabilities(jget::obj_opt(
                    Some(result),
                    "capabilities",
                )),
            }),
            ShutdownRequest => {
                assert_eq!(*result, Json::Null);
                LspResult::ShutdownResult
            }
            DefinitionRequest(_) => match result {
                Json::List(l) => LspResult::DefinitionResult(
                    l.iter().map(|j| parse_definition_location(Some(j))).collect(),
                ),
                _ => panic!("not a list"),
            },
            FindReferencesRequest(_) => LspResult::FindReferencesResult(parse_locations(result)),
            RenameRequest(_) => LspResult::RenameResult(parse_workspace_edit(Some(result))),
            r => panic!("no parser for the result of {}", request_name_to_string(r)),
        }
    }

    #[test]
    fn round_trip_recorded_exchanges() {
        let mut files: Vec<PathBuf> = std::fs::read_dir(data_dir())
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "json"))
            .collect();
        files.sort();
        let mut client_messages = 0;
        let mut server_messages = 0;
        for json_file in &files {
            let expected_file = json_file.with_extension("expected");
            let name = json_file.display().to_string();
            // What the client sends.
            let mut requests: HashMap<LspId, LspRequest> = HashMap::new();
            for message in read_messages(json_file) {
                let method_ = jget::string_opt(Some(&message), "method");
                let parsed = parse_lsp(&message, |id| panic!("{}: a response to {:?}", name, id)).unwrap();
                assert_eq!(
                    Some(message_name_to_string(&parsed)),
                    method_,
                    "{}: {}",
                    name,
                    yojson::to_string(&message)
                );
                match &parsed {
                    LspMessage::RequestMessage(id, request) => {
                        requests.insert(id.clone(), request.clone());
                    }
                    LspMessage::NotificationMessage(LspNotification::CancelRequestNotification(_)) => {
                        // A notification that Lsp_fmt prints, as it came.
                        assert_eq!(
                            yojson::to_string(&print_lsp(&parsed)),
                            yojson::to_string(&message),
                            "{}",
                            name
                        );
                    }
                    _ => {}
                }
                client_messages += 1;
            }
            // What the server answered.
            for message in read_messages(&expected_file) {
                let message = without_powered_by(&message);
                let reprinted = if jget::string_opt(Some(&message), "method").as_deref()
                    == Some("$/progress")
                {
                    let params = jget::obj_exn(Some(&message), "params").unwrap();
                    let token = PartialResultToken(jget::string_exn(params, "token").unwrap());
                    let value = parse_locations(jget::val_exn(params, "value").unwrap());
                    print_lsp_notification(&LspNotification::FindReferencesPartialResultNotification(
                        token, value,
                    ))
                } else if jget::val_opt(Some(&message), "error").is_some() {
                    print_lsp(&parse_lsp(&message, |id| panic!("{}: {:?}", name, id)).unwrap())
                } else {
                    let id = parse_id(jget::val_exn(Some(&message), "id").unwrap()).unwrap();
                    let request = requests
                        .get(&id)
                        .unwrap_or_else(|| panic!("{}: no request {:?}", name, id));
                    let result = parse_result(request, jget::val_exn(Some(&message), "result").unwrap());
                    print_lsp_response(&id, &result)
                };
                assert_eq!(
                    yojson::to_string(&reprinted),
                    yojson::to_string(&message),
                    "{}",
                    expected_file.display()
                );
                server_messages += 1;
            }
        }
        eprintln!(
            "{} files: {} client messages parsed, {} server messages round-tripped",
            files.len(),
            client_messages,
            server_messages
        );
        assert_eq!(files.len(), 14);
        assert!(client_messages >= 130, "{}", client_messages);
        assert!(server_messages >= 70, "{}", server_messages);
    }
}
