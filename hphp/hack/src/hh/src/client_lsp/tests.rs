// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! No OCaml counterpart: unit tests of `client_lsp.rs`.

use super::*;

fn initialize_params(json: &str) -> initialize::Params {
    lsp_fmt::parse_initialize(Some(&yojson::from_string(json).unwrap())).unwrap()
}

/// The bytes of the OCaml's initialize response (recorded from the oracle
/// `hh_client lsp`, a root whose hh.conf leaves `go_to_implementation` on).
#[test]
fn initialize_response_is_the_ocamls() {
    let ocaml = r##"{"jsonrpc":"2.0","id":1,"result":{"capabilities":{"textDocumentSync":{"openClose":true,"change":2,"willSave":false,"willSaveWaitUntil":true,"save":{"includeText":false}},"hoverProvider":true,"completionProvider":{"resolveProvider":true,"triggerCharacters":["$",">","\\",":","<","[","'","\"","{","#"]},"signatureHelpProvider":{"triggerCharacters":["(",","]},"definitionProvider":true,"typeDefinitionProvider":true,"referencesProvider":true,"documentHighlightProvider":true,"documentSymbolProvider":true,"workspaceSymbolProvider":true,"codeActionProvider":{"resolveProvider":true},"documentFormattingProvider":true,"documentRangeFormattingProvider":true,"documentOnTypeFormattingProvider":{"firstTriggerCharacter":";","moreTriggerCharacter":["}"]},"renameProvider":true,"implementationProvider":true,"rageProvider":true,"experimental":{"snippetTextEdit":true,"autoCloseJsx":true}}}}"##;
    let params = initialize_params(
        r#"{"processId":null,"rootPath":"/r","capabilities":{"window":{"status":{}}},"initializationOptions":{}}"#,
    );
    let mut local_config = crate::server_local_config_load::default();
    local_config.go_to_implementation = true;
    set_env(Env {
        local_config,
        ..(*env()).clone()
    });
    let result = do_initialize(&params);
    let json = lsp_fmt::print_lsp_response(&lsp::NumberId(1), &LspResult::InitializeResult(result));
    assert_eq!(yojson::to_string(&json), ocaml);
    // skipLspServerOnTypeFormatting drops the on-type provider.
    let params = initialize_params(
        r#"{"processId":null,"rootPath":"/r","capabilities":{},"initializationOptions":{"skipLspServerOnTypeFormatting":true}}"#,
    );
    let s = yojson::to_string(&lsp_fmt::print_initialize(&do_initialize(&params)));
    assert!(!s.contains("documentOnTypeFormattingProvider"), "{}", s);
}

#[test]
fn register_capability_is_the_ocamls() {
    let ocaml = r#"{"jsonrpc":"2.0","id":1,"method":"client/registerCapability","params":{"registrations":[{"id":"did-change-watched-files","method":"workspace/didChangeWatchedFiles","registerOptions":{"watchers":[{"globPattern":"**/*.{php,phpt,hack,hackpartial,hck,hh,hhi,xhp}","kind":7}]}}]}}"#;
    let json = lsp_fmt::print_lsp_request(&lsp::NumberId(1), &do_did_change_watched_files_register_capability());
    assert_eq!(yojson::to_string(&json), ocaml);
}

#[test]
fn powered_by_goes_first() {
    let json = add_powered_by(
        PoweredBy::ServerlessIde,
        lsp_fmt::print_lsp_response(&lsp::NumberId(3), &LspResult::ShutdownResult),
    );
    assert_eq!(
        yojson::to_string(&json),
        r#"{"powered_by":"serverless_ide","jsonrpc":"2.0","id":3,"result":null}"#
    );
    let json = add_powered_by(
        PoweredBy::HhServer,
        lsp_fmt::print_lsp_response(&lsp::NumberId(3), &LspResult::ShutdownResult),
    );
    assert_eq!(yojson::to_string(&json), r#"{"jsonrpc":"2.0","id":3,"result":null}"#);
}

#[test]
fn lsp_error_data_order() {
    // current_stack, then stack, then the data's own fields.
    let e = make_lsp_error(
        Some(yojson::T::Assoc(vec![("x".to_string(), yojson::T::Int(1))])),
        Some("st"),
        None,
        Some(error::RequestCancelled),
        "m",
    );
    match e.data {
        Some(yojson::T::Assoc(elems)) => {
            let keys: Vec<&str> = elems.iter().map(|(k, _)| k.as_str()).collect();
            assert_eq!(keys, vec!["current_stack", "stack", "x"]);
        }
        d => panic!("{:?}", d),
    }
    // A non-object datum is kept under "data"; no current stack when asked.
    let e = make_lsp_error(Some(yojson::T::Int(2)), None, Some(false), None, "m");
    assert_eq!(e.code, error::UnknownErrorCode);
    assert_eq!(
        e.data,
        Some(yojson::T::Assoc(vec![("data".to_string(), yojson::T::Int(2))]))
    );
}

#[test]
fn ocaml_hex_is_63_bits() {
    assert_eq!(ocaml_hex(0xa674b2c021f1ea3), "a674b2c021f1ea3");
    assert_eq!(ocaml_hex(-1), "7fffffffffffffff");
}

#[test]
fn cancellation_predicate() {
    let request = LspMessage::RequestMessage(lsp::NumberId(7), LspRequest::ShutdownRequest);
    let tj = |s: &str| jsonrpc::TimestampedJson {
        json: yojson::from_string(s).unwrap(),
        timestamp: 0.,
    };
    let yes = tj(r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":7}}"#);
    let other = tj(r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":8}}"#);
    let response = tj(r#"{"jsonrpc":"2.0","id":7,"result":null}"#);
    assert!(is_cancellation_of_request(&request, &yes).unwrap());
    assert!(!is_cancellation_of_request(&request, &other).unwrap());
    // a response: `Is_response`, so no
    assert!(!is_cancellation_of_request(&request, &response).unwrap());
    // a notification is never cancelled
    let n = LspMessage::NotificationMessage(LspNotification::InitializedNotification);
    assert!(!is_cancellation_of_request(&n, &yes).unwrap());
}
