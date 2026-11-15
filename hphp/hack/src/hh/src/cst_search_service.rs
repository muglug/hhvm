// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! Port of `client_and_server/cst_search_service.ml`. See `hh/PORTING.md`.
//!
//! `go` (the `CST_SEARCH` command over the files of the server, through
//! `Multi_worker`) is in [`server`] (feature `server`); `compile_pattern`,
//! `search` and `result_to_json` serve `hh single --cst-search` too.
//!
//! The environment of a search (`env` in OCaml, threaded through the
//! functions) is mutated in place: it only caches the types of the file,
//! computed the first time a `type_pattern` needs them.

use std::sync::Arc;

use parser_core_types::indexed_source_text::IndexedSourceText;
use parser_core_types::positioned_syntax::PositionedSyntax;
use parser_core_types::syntax::SyntaxVariant;
use parser_core_types::syntax_kind::SyntaxKind;
use parser_core_types::syntax_trait::SyntaxTrait;

use crate::full_fidelity_source_text;
use crate::hh_json_helpers;
use crate::hh_json_helpers::access;
use crate::provider_context;
use crate::rt::ocaml_stdlib::int_of_string_opt;
use crate::schema_definition;
use crate::tast_type_collector;
use crate::typing_defs;
use crate::yojson::safe::T as Json;

/// A `SyntaxKind.t`. We can generate a string from a kind, but not the other
/// way around, so we store the string value given to us in the input
/// directly. Then, when examining a node to see if it's a match, we'll
/// convert the node's kind to a string and simply use string comparison.
///
/// (Note that multiple syntax kinds map to the same string anyways, so it
/// would be hard to reverse the mapping.)
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct NodeKind(pub String);

/// An identifier in the pattern used to identify the this node when
/// returning the results of a match to the caller. This identifier may not
/// be unique in the list of returned results.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct MatchName(pub String);

/// The name of a child of a node (`binary_left_operand`: the prefix of the
/// kind in the schema and the name of the field).
#[derive(Clone, Debug)]
pub struct ChildType(pub String);

/// A query that can be run on the syntax tree. It will return the matched
/// nodes of any matched `MatchPattern`s.
#[derive(Clone, Debug)]
pub enum Pattern {
    /// Match any node with the given kind, and whose children match the
    /// given patterns (children may be omitted; none is given twice).
    NodePattern {
        kind: NodeKind,
        children: Vec<(ChildType, Pattern)>,
    },
    /// Match any missing node.
    MissingNodePattern,
    /// Return the given node in the result list, assuming that the pattern
    /// overall matches. (This pattern by itself always matches; it's often
    /// used with `AndPattern`).
    MatchPattern { match_name: MatchName },
    /// Matches a given node if there is descendant node matching the given
    /// pattern anywhere in the subtree underneath the parent node.
    DescendantPattern { pattern: Box<Pattern> },
    /// Matches a list node (such as a statement list) only if all the
    /// children at the given indexes match their respective patterns.
    ListPattern {
        children: Vec<(isize, Pattern)>,
        max_length: Option<isize>,
    },
    /// Matches a given node if its raw text is exactly the specified string.
    /// The "raw" text doesn't include trivia.
    RawTextPattern { raw_text: String },
    /// Matches a given expression node if its type is a subtype of the given
    /// type.
    TypePattern { subtype_of: typing_defs::Ty },
    /// Matches if all of the children patterns match.
    AndPattern { patterns: Vec<Pattern> },
    /// Matches if any of the children patterns match (short-circuits).
    OrPattern { patterns: Vec<Pattern> },
    /// Matches only if the given pattern does not match. The matches of the
    /// child pattern are thrown away.
    NotPattern { pattern: Box<Pattern> },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct MatchedNode {
    pub match_name: MatchName,
    pub kind: NodeKind,
    pub start_offset: isize,
    pub end_offset: isize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct Result {
    /// The list of nodes for which a `MatchPattern` matched.
    pub matched_nodes: Vec<MatchedNode>,
}

/// The job of the search on the workers: the pattern (as JSON text, compiled
/// again in the clone, as the OCaml's closure compiles it in the worker)
/// over a bucket of files.
#[cfg(feature = "server")]
pub struct CstSearchJob;

#[cfg(feature = "server")]
impl crate::multi_worker::ServiceJob for CstSearchJob {
    const NAME: &'static str = "Cst_search_service.search";
    type Params = String;
    type Item = crate::relative_path::T;
    type Output = Vec<RelPathResult>;
    fn run(ctx: &provider_context::T, input: &String, inputs: Vec<crate::relative_path::T>) -> Self::Output {
        let input = crate::yojson::safe::from_string(input).expect("Cst_search_service: the pattern");
        let pattern = compile_pattern(ctx, &input).expect("compiled in the master");
        let mut acc = vec![];
        for path in inputs {
            search_path(ctx, &pattern, path, &mut acc)
        }
        acc
    }
}

/// The body of `job` in `go` for one `(path, pattern)` input: `(path, result)
/// :: acc` when the file matches; an exception is logged, with the path, and
/// re-raised.
#[cfg(feature = "server")]
fn search_path(
    ctx: &provider_context::T,
    pattern: &Pattern,
    path: crate::relative_path::T,
    acc: &mut Vec<RelPathResult>,
) {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let (ctx, entry) = provider_context::add_entry_if_missing(ctx, path.clone());
        search(&ctx, &entry, pattern)
    }));
    match r {
        Ok(Some(result)) => acc.insert(0, (path, result)),
        Ok(None) => {}
        Err(payload) => {
            let e = crate::exception::wrap(payload);
            let prefix = format!(
                "Error while running CST search on path {}:\n",
                crate::relative_path::to_absolute(&path)
            );
            crate::hh_logger::exception_(Some(&prefix), &e);
            crate::exception::reraise(e)
        }
    }
}

/// `rel_path_result` (with its derived `compare`)
pub type RelPathResult = (crate::relative_path::T, Result);

type CollectedTypeMap = tast_type_collector::CollectedTypes;

/// The environment used in searching a single file.
struct Env<'a> {
    ctx: &'a provider_context::T,
    entry: &'a Arc<provider_context::Entry>,
    collected_types: Option<CollectedTypeMap>,
    source_text: &'a full_fidelity_source_text::T,
    indexed: IndexedSourceText<'a>,
}

fn empty_result() -> Option<Result> {
    Some(Result {
        matched_nodes: vec![],
    })
}

fn merge_results(lhs: Option<Result>, rhs: Option<Result>) -> Option<Result> {
    match (lhs, rhs) {
        (Some(mut lhs), Some(rhs)) => {
            lhs.matched_nodes.extend(rhs.matched_nodes);
            Some(lhs)
        }
        (Some(x), None) | (None, Some(x)) => Some(x),
        (None, None) => None,
    }
}

/// `Syntax.children_names node` (generated from the schema in OCaml: the
/// prefix of the kind and the name of each field).
fn children_names(node: &PositionedSyntax) -> Vec<String> {
    match &node.syntax {
        SyntaxVariant::Missing | SyntaxVariant::Token(_) | SyntaxVariant::SyntaxList(_) => vec![],
        _ => {
            let kind_name = format!("{:?}", node.kind());
            match schema_definition::SCHEMA
                .iter()
                .find(|n| n.kind_name == kind_name)
            {
                Some(n) => n
                    .fields
                    .iter()
                    .map(|(f, _)| format!("{}_{}", n.prefix, f))
                    .collect(),
                None => panic!("children_names: no schema for {}", kind_name),
            }
        }
    }
}

fn find_child_with_type<'n>(node: &'n PositionedSyntax, child_type: &ChildType) -> Option<&'n PositionedSyntax> {
    let ChildType(expected_child_type) = child_type;
    let child_index = children_names(node)
        .iter()
        .position(|actual_child_type| expected_child_type == actual_child_type)?;
    node.iter_children().nth(child_index)
}

fn collect_types<'e>(env: &'e mut Env<'_>) -> &'e CollectedTypeMap {
    if env.collected_types.is_none() {
        let crate::tast_provider::ComputeTast { tast, .. } =
            crate::tast_provider::compute_tast_unquarantined(env.ctx, env.entry);
        let collected_types =
            tast_type_collector::collect_types(env.ctx, &tast.under_normal_assumptions);
        env.collected_types = Some(collected_types);
    }
    env.collected_types.as_ref().unwrap()
}

fn kind_to_string(node: &PositionedSyntax) -> String {
    node.kind().to_string().to_string()
}

fn search_node(env: &mut Env<'_>, pattern: &Pattern, node: &PositionedSyntax) -> Option<Result> {
    match pattern {
        Pattern::NodePattern { kind, children } => {
            let NodeKind(kind) = kind;
            if kind_to_string(node) != *kind {
                None
            } else {
                let patterns: Vec<(&PositionedSyntax, &Pattern)> = children
                    .iter()
                    .map(|(child_type, pattern)| {
                        let child_node = find_child_with_type(node, child_type);
                        let child_node = child_node.expect("Option.value_exn");
                        (child_node, pattern)
                    })
                    .collect();
                search_and(env, &patterns)
            }
        }
        Pattern::MissingNodePattern => match node.kind() {
            SyntaxKind::Missing => empty_result(),
            _ => None,
        },
        Pattern::MatchPattern { match_name } => Some(Result {
            matched_nodes: vec![MatchedNode {
                match_name: match_name.clone(),
                kind: NodeKind(kind_to_string(node)),
                start_offset: node.start_offset() as isize,
                end_offset: node.end_offset() as isize,
            }],
        }),
        Pattern::DescendantPattern { pattern } => search_descendants(env, pattern, node),
        Pattern::ListPattern {
            children,
            max_length,
        } => {
            let syntax_list = match &node.syntax {
                SyntaxVariant::SyntaxList(syntax_list) => match max_length {
                    None => Some(syntax_list),
                    Some(max_length) => {
                        if syntax_list.len() as isize <= *max_length {
                            Some(syntax_list)
                        } else {
                            None
                        }
                    }
                },
                _ => None,
            };
            match syntax_list {
                None => None,
                Some(syntax_list) => {
                    let patterns: Option<Vec<(&PositionedSyntax, &Pattern)>> = children
                        .iter()
                        .map(|(index, pattern)| {
                            // `List.nth` of a negative index is `None`.
                            usize::try_from(*index)
                                .ok()
                                .and_then(|i| syntax_list.get(i))
                                .map(|child_node| (child_node, pattern))
                        })
                        .collect();
                    match patterns {
                        Some(patterns) => search_and(env, &patterns),
                        // We tried to match a pattern for the child at at index N, but the syntax
                        // list didn't have an Nth element.
                        None => None,
                    }
                }
            }
        }
        Pattern::RawTextPattern { raw_text } => {
            let st = full_fidelity_source_text::source_text(env.source_text);
            if st.sub(node.start_offset(), node.width()) == raw_text.as_bytes() {
                empty_result()
            } else {
                None
            }
        }
        Pattern::TypePattern { subtype_of } => {
            // (`Line_break_map.reset_global_state ()`: no global state here.)
            // `Syntax.position env.entry.path node`
            let pos = {
                let p = env.indexed.relative_pos(node.start_offset(), node.end_offset());
                oxidized::pos::Pos::from_lnum_bol_offset(
                    Arc::new(env.entry.path.clone()),
                    p.start,
                    p.end,
                )
            };
            let collected_types = collect_types(env);
            let pos = crate::pos::to_absolute(&pos);
            let tys = tast_type_collector::get_from_pos_map(&pos, collected_types);
            let is_subtype_of = |(tast_env, ty): &tast_type_collector::CollectedType| match ty {
                typing_defs::PhaseTy::LoclTy(ty) => crate::tast_env::can_subtype(tast_env, ty, subtype_of),
                typing_defs::PhaseTy::DeclTy(_ty) => false,
            };
            match tys {
                Some(tys) if tys.iter().any(is_subtype_of) => empty_result(),
                Some(_) | None => None,
            }
        }
        Pattern::AndPattern { patterns } => {
            let patterns: Vec<(&PositionedSyntax, &Pattern)> =
                patterns.iter().map(|pattern| (node, pattern)).collect();
            search_and(env, &patterns)
        }
        Pattern::OrPattern { patterns } => {
            let patterns: Vec<(&PositionedSyntax, &Pattern)> =
                patterns.iter().map(|pattern| (node, pattern)).collect();
            search_or(env, &patterns)
        }
        Pattern::NotPattern { pattern } => match search_node(env, pattern, node) {
            Some(_) => None,
            None => empty_result(),
        },
    }
}

// TODO: this will likely have to become more intelligent
fn search_descendants(env: &mut Env<'_>, pattern: &Pattern, node: &PositionedSyntax) -> Option<Result> {
    let mut acc_result = None;
    for child in node.iter_children() {
        let child_result = search_node(env, pattern, child);
        let descendants_result = search_descendants(env, pattern, child);
        let result = merge_results(child_result, descendants_result);
        acc_result = merge_results(result, acc_result);
    }
    acc_result
}

fn search_and(env: &mut Env<'_>, patterns: &[(&PositionedSyntax, &Pattern)]) -> Option<Result> {
    let mut result = empty_result();
    for (node, pattern) in patterns {
        match result {
            // Short-circuit.
            None => {}
            Some(_) => {
                let pattern_result = search_node(env, pattern, node);
                result = match pattern_result {
                    None => None,
                    Some(_) => merge_results(result, pattern_result),
                }
            }
        }
    }
    result
}

fn search_or(env: &mut Env<'_>, patterns: &[(&PositionedSyntax, &Pattern)]) -> Option<Result> {
    let mut result = None;
    for (node, pattern) in patterns {
        match result {
            // Short-circuit.
            Some(_) => {}
            None => result = search_node(env, pattern, node),
        }
    }
    result
}

fn wrap_json_accessor<A>(r: access::M<A>) -> std::result::Result<(A, access::Keytrace), String> {
    r.map_err(|e| access::access_failure_to_string(&e))
}

fn error_at_keytrace<A>(keytrace: &access::Keytrace, error_message: String) -> std::result::Result<A, String> {
    Err(error_message + &access::keytrace_to_string(keytrace))
}

/// Compile JSON input into a pattern that can be searched for.
pub fn compile_pattern(ctx: &provider_context::T, json: &Json) -> std::result::Result<Pattern, String> {
    compile_pattern_inner(ctx, json, &vec![])
}

fn compile_pattern_inner(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> std::result::Result<Pattern, String> {
    let (pattern_type, pattern_type_keytrace) = wrap_json_accessor(access::get_string("pattern_type", (json, keytrace)))?;
    match pattern_type.as_str() {
        "node_pattern" => compile_node_pattern(ctx, json, keytrace),
        "missing_node_pattern" => Ok(Pattern::MissingNodePattern),
        "match_pattern" => {
            let (match_name, _) = wrap_json_accessor(access::get_string("match_name", (json, keytrace)))?;
            Ok(Pattern::MatchPattern {
                match_name: MatchName(match_name),
            })
        }
        "descendant_pattern" => {
            let (pattern, pattern_keytrace) = wrap_json_accessor(access::get_obj("pattern", (json, keytrace)))?;
            let pattern = compile_pattern_inner(ctx, &pattern, &pattern_keytrace)?;
            Ok(Pattern::DescendantPattern {
                pattern: Box::new(pattern),
            })
        }
        "list_pattern" => compile_list_pattern(ctx, json, keytrace),
        "raw_text_pattern" => {
            let (raw_text, _) = wrap_json_accessor(access::get_string("raw_text", (json, keytrace)))?;
            Ok(Pattern::RawTextPattern { raw_text })
        }
        "type_pattern" => {
            let (subtype_of_json, subtype_of_keytrace) =
                wrap_json_accessor(access::get_obj("subtype_of", (json, keytrace)))?;
            let locl_ty = crate::tast_env::json_to_locl_ty(Some(subtype_of_keytrace), ctx, &subtype_of_json);
            match locl_ty {
                Ok(locl_ty) => Ok(Pattern::TypePattern {
                    subtype_of: locl_ty,
                }),
                Err(typing_defs::DeserializationError::WrongPhase(message))
                | Err(typing_defs::DeserializationError::NotSupported(message))
                | Err(typing_defs::DeserializationError::DeserializationError(message)) => Err(message),
            }
        }
        "and_pattern" => Ok(Pattern::AndPattern {
            patterns: compile_child_patterns_helper(ctx, json, keytrace)?,
        }),
        "or_pattern" => Ok(Pattern::OrPattern {
            patterns: compile_child_patterns_helper(ctx, json, keytrace)?,
        }),
        "not_pattern" => {
            let (json, keytrace) = wrap_json_accessor(access::get_obj("pattern", (json, keytrace)))?;
            let pattern = compile_pattern_inner(ctx, &json, &keytrace)?;
            Ok(Pattern::NotPattern {
                pattern: Box::new(pattern),
            })
        }
        pattern_type => error_at_keytrace(
            &pattern_type_keytrace,
            format!("Unknown pattern type '{}'", pattern_type),
        ),
    }
}

fn compile_node_pattern(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> std::result::Result<Pattern, String> {
    let (kind, kind_keytrace) = wrap_json_accessor(access::get_string("kind", (json, keytrace)))?;
    let kind_info = schema_definition::SCHEMA
        .iter()
        .find(|schema_node| schema_node.description == kind);
    match kind_info {
        None => error_at_keytrace(&kind_keytrace, format!("Kind '{}' doesn't exist", kind)),
        Some(kind_info) => {
            let (children_json, children_keytrace) = wrap_json_accessor(access::get_obj("children", (json, keytrace)))?;
            // This has already been verified to be an object above.
            let children = hh_json_helpers::get_object_exn(&children_json).expect("get_object_exn");
            // We're given a field name like `binary_right_operand`, but the field
            // names in the schema are things like `right_operand`, and you have to
            // affix the prefix yourself. For consistency with other tooling, we want
            // to use `binary_right_operand` instead of just `right_operand`.
            let get_prefixed_field_name = |field_name: &str| format!("{}_{}", kind_info.prefix, field_name);
            let get_child_type = |child_keytrace: &access::Keytrace, child_name: &str| -> std::result::Result<ChildType, String> {
                let field = kind_info
                    .fields
                    .iter()
                    .find(|(field_name, _)| get_prefixed_field_name(field_name) == child_name);
                match field {
                    None => {
                        let valid_types: Vec<String> = kind_info
                            .fields
                            .iter()
                            .map(|(field_name, _)| get_prefixed_field_name(field_name))
                            .collect();
                        error_at_keytrace(
                            child_keytrace,
                            format!(
                                "Unknown child type '{}'; valid child types for a node of kind '{}' are: {}",
                                child_name,
                                kind,
                                valid_types.join(", ")
                            ),
                        )
                    }
                    Some(_) => Ok(ChildType(child_name.to_string())),
                }
            };
            // `all children_patterns`: every child is compiled (in order),
            // and the first error is returned.
            let children_patterns: Vec<std::result::Result<(ChildType, Pattern), String>> = children
                .iter()
                .enumerate()
                .map(|(index, (child_name, pattern_json))| {
                    let mut child_keytrace = vec![index.to_string()];
                    child_keytrace.extend(children_keytrace.iter().cloned());
                    let child_name = get_child_type(&child_keytrace, child_name)?;
                    let pattern = compile_pattern_inner(ctx, pattern_json, &child_keytrace)?;
                    Ok((child_name, pattern))
                })
                .collect();
            let children = children_patterns.into_iter().collect::<std::result::Result<Vec<_>, _>>()?;
            Ok(Pattern::NodePattern {
                kind: NodeKind(kind),
                children,
            })
        }
    }
}

fn compile_list_pattern(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> std::result::Result<Pattern, String> {
    // `Hh_json_helpers.get_field_opt (Access.get_number_int "max_length") json`
    let max_length = match access::get_number_int("max_length", (json, &vec![])) {
        Ok((r, _)) => Some(r),
        Err(_) => None,
    };
    let (children_json, children_keytrace) = wrap_json_accessor(access::get_obj("children", (json, keytrace)))?;
    // This has already been verified to be an object above.
    let children = hh_json_helpers::get_object_exn(&children_json).expect("get_object_exn");
    let children_patterns: Vec<std::result::Result<(isize, Pattern), String>> = children
        .iter()
        .map(|(index_str, pattern_json)| {
            let mut child_keytrace = vec![index_str.clone()];
            child_keytrace.extend(children_keytrace.iter().cloned());
            let index = match int_of_string_opt(index_str) {
                Some(index) => index,
                None => {
                    return error_at_keytrace(&child_keytrace, format!("Invalid integer key: {}", index_str));
                }
            };
            if index < 0 {
                return error_at_keytrace(&child_keytrace, "Integer key must be non-negative".to_string());
            }
            let pattern = compile_pattern_inner(ctx, pattern_json, &child_keytrace)?;
            Ok((index, pattern))
        })
        .collect();
    let children = children_patterns.into_iter().collect::<std::result::Result<Vec<_>, _>>()?;
    Ok(Pattern::ListPattern {
        children,
        max_length,
    })
}

fn compile_child_patterns_helper(
    ctx: &provider_context::T,
    json: &Json,
    keytrace: &access::Keytrace,
) -> std::result::Result<Vec<Pattern>, String> {
    let (pattern_list, pattern_list_keytrace) = wrap_json_accessor(access::get_array("patterns", (json, keytrace)))?;
    let compiled_patterns: Vec<std::result::Result<Pattern, String>> = pattern_list
        .iter()
        .enumerate()
        .map(|(i, json)| {
            let mut keytrace = vec![i.to_string()];
            keytrace.extend(pattern_list_keytrace.iter().cloned());
            compile_pattern_inner(ctx, json, &keytrace)
        })
        .collect();
    compiled_patterns.into_iter().collect()
}

/// Convert the result of a search into JSON output that can be sent back to the
/// user.
pub fn result_to_json(sort_results: bool, result: Option<&Result>) -> Json {
    match result {
        None => Json::Null,
        Some(result) => {
            let mut matched_nodes = result.matched_nodes.clone();
            if sort_results {
                // `List.sort` is stable
                matched_nodes.sort();
            }
            let matched_nodes = matched_nodes
                .into_iter()
                .map(|matched_node| {
                    let MatchName(match_name) = matched_node.match_name;
                    let NodeKind(kind) = matched_node.kind;
                    Json::Assoc(vec![
                        ("match_name".to_string(), Json::String(match_name)),
                        ("kind".to_string(), Json::String(kind)),
                        ("start_offset".to_string(), Json::Int(matched_node.start_offset)),
                        ("end_offset".to_string(), Json::Int(matched_node.end_offset)),
                    ])
                })
                .collect();
            Json::Assoc(vec![("matched_nodes".to_string(), Json::List(matched_nodes))])
        }
    }
}

/// Execute a search on a single syntax tree. This is most useful in debugging
/// utilities like `hh_single_type_check`.
pub fn search(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pattern: &Pattern,
) -> Option<Result> {
    let (source_text, root) = crate::ast_provider::compute_cst(entry);
    let st = full_fidelity_source_text::source_text(&source_text);
    let mut env = Env {
        ctx,
        entry,
        collected_types: None,
        source_text: &source_text,
        indexed: IndexedSourceText::new(st),
    };
    search_node(&mut env, pattern, &root)
}

/// `go` (the `CST_SEARCH` command).
#[cfg(feature = "server")]
pub mod server {
    use super::*;

    /// Search for the given pattern across the given set of files.
    ///
    /// `go genv env ~sort_results ~files_to_search input`. The progress
    /// messages are written as the OCaml's `Multi_worker.next` writes them,
    /// one call per bucket (then the empty one), before the search runs.
    pub fn go(
        genv: &crate::server_env::Genv,
        env: &crate::server_env::Env,
        sort_results: bool,
        files_to_search: Option<&[String]>,
        input: &Json,
    ) -> std::result::Result<Json, String> {
        let ctx = crate::provider_utils::ctx_from_server_env(env);
        // (A pattern holds types, which are not shared between threads: each
        // bucket compiles its own copy, as each OCaml worker gets one.)
        compile_pattern(&ctx, input)?;
        let mut num_files_searched = 0usize;
        let mut last_printed_num_files_searched = 0usize;
        let mut done_searching = false;
        let mut progress_fn = |length: usize| {
            let is_bucket_empty = length == 0;
            if !done_searching {
                num_files_searched += length;
                if num_files_searched - last_printed_num_files_searched >= 10000 || is_bucket_empty {
                    crate::server_progress::write(
                        None,
                        None,
                        &format!("CST search: searched {} files...", num_files_searched),
                    );
                    last_printed_num_files_searched = num_files_searched;
                }
            }
            if is_bucket_empty {
                done_searching = true
            }
        };
        let get_job_info = |path: &str| -> Option<crate::relative_path::T> {
            let path = crate::relative_path::create_detect_prefix(path);
            if crate::naming_table::has_file(&env.naming_table, &path) {
                Some(path)
            } else {
                // We may not have the file information for a file such as one that we
                // ignore in `.hhconfig`.
                None
            }
        };
        let buckets: Vec<Vec<crate::relative_path::T>> = match files_to_search {
            Some(files_to_search) => {
                let files: Vec<_> = crate::sys_utils::parse_path_list(files_to_search)
                    .iter()
                    .filter_map(|p| get_job_info(p))
                    .collect();
                crate::find_refs_service::multi_worker_buckets(genv.num_workers as usize, &files)
            }
            None => {
                let mut next = crate::server_notifier::indexer(&genv.notifier, Box::new(crate::find_utils::is_hack))
                    .unwrap_or_else(|e| panic!("{:?}", e));
                let mut buckets = vec![];
                loop {
                    let files: Vec<_> = next().iter().filter_map(|p| get_job_info(p)).collect();
                    if files.is_empty() {
                        break;
                    }
                    buckets.push(files);
                }
                buckets
            }
        };
        for b in &buckets {
            progress_fn(b.len())
        }
        progress_fn(0);
        let jobs: Vec<crate::relative_path::T> = buckets.into_iter().flatten().collect();
        let job = |acc: Vec<RelPathResult>, inputs: Vec<crate::relative_path::T>| -> Vec<RelPathResult> {
            let mut acc = acc;
            let pattern = compile_pattern(&ctx, input).expect("compiled above");
            for path in inputs {
                search_path(&ctx, &pattern, path, &mut acc)
            }
            acc
        };
        let rev_append = |b: Vec<RelPathResult>, c: Vec<RelPathResult>| {
            let mut r: Vec<RelPathResult> = b.into_iter().rev().collect();
            r.extend(c);
            r
        };
        let mut results = crate::multi_worker::call_service::<CstSearchJob, _>(
            &ctx,
            crate::yojson::safe::to_string(input),
            &jobs,
            rev_append,
            vec![],
            || false,
            |_| crate::find_refs_service::multi_worker_call(
            Some(genv.num_workers as usize),
            &jobs,
            job,
            Vec::new,
            // `List.rev_append`
            |b: Vec<RelPathResult>, c: Vec<RelPathResult>| {
                let mut r: Vec<RelPathResult> = b.into_iter().rev().collect();
                r.extend(c);
                r
            },
            || false,
        ));
        if sort_results {
            results.sort_by(|(p1, r1), (p2, r2)| crate::relative_path::compare(p1, p2).then_with(|| r1.cmp(r2)));
        }
        Ok(Json::Assoc(
            results
                .iter()
                .map(|(path, result)| (crate::relative_path::to_absolute(path), result_to_json(sort_results, Some(result))))
                .collect(),
        ))
    }
}
