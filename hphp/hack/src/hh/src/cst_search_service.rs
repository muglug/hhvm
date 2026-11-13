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
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeKind(pub String);

/// An identifier in the pattern used to identify the this node when
/// returning the results of a match to the caller. This identifier may not
/// be unique in the list of returned results.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MatchedNode {
    pub match_name: MatchName,
    pub kind: NodeKind,
    pub start_offset: isize,
    pub end_offset: isize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Result_ {
    /// The list of nodes for which a `MatchPattern` matched.
    pub matched_nodes: Vec<MatchedNode>,
}

/// `rel_path_result` (with its derived `compare`)
pub type RelPathResult = (crate::relative_path::T, Result_);

type CollectedTypeMap = tast_type_collector::CollectedTypes;

/// The environment used in searching a single file.
struct Env<'a> {
    ctx: &'a provider_context::T,
    entry: &'a Arc<provider_context::Entry>,
    collected_types: Option<CollectedTypeMap>,
    source_text: &'a full_fidelity_source_text::T,
    indexed: IndexedSourceText<'a>,
}

fn empty_result() -> Option<Result_> {
    Some(Result_ {
        matched_nodes: vec![],
    })
}

fn merge_results(lhs: Option<Result_>, rhs: Option<Result_>) -> Option<Result_> {
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
            match schema_definition::schema
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
        let crate::tast_provider::ComputeTastResult { tast, .. } =
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

fn search_node(env: &mut Env<'_>, pattern: &Pattern, node: &PositionedSyntax) -> Option<Result_> {
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
        Pattern::MatchPattern { match_name } => Some(Result_ {
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

fn search_descendants(env: &mut Env<'_>, pattern: &Pattern, node: &PositionedSyntax) -> Option<Result_> {
    let mut acc_result = None;
    for child in node.iter_children() {
        let child_result = search_node(env, pattern, child);
        let descendants_result = search_descendants(env, pattern, child);
        let result = merge_results(child_result, descendants_result);
        acc_result = merge_results(result, acc_result);
    }
    acc_result
}

fn search_and(env: &mut Env<'_>, patterns: &[(&PositionedSyntax, &Pattern)]) -> Option<Result_> {
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

fn search_or(env: &mut Env<'_>, patterns: &[(&PositionedSyntax, &Pattern)]) -> Option<Result_> {
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

fn wrap<A>(r: access::M<A>) -> Result<(A, access::Keytrace), String> {
    r.map_err(|e| access::access_failure_to_string(&e))
}

/// `Hh_json_helpers.Access.get_number_int` (not in `hh_json_helpers` yet):
/// an `Int`, or an `Intlit` that `int_of_string` reads.
fn get_number_int(k: &str, v_keytrace: (&Json, &access::Keytrace)) -> access::M<isize> {
    access::bind(access::get_val(k, v_keytrace), |(v, keytrace)| match &v {
        Json::Int(i) => Ok((*i, keytrace)),
        Json::Intlit(s) => match int_of_string_opt(s) {
            Some(i) => Ok((i, keytrace)),
            None => Err(access::AccessFailure::WrongTypeError(
                keytrace,
                hh_json_helpers::JsonType::IntegerT,
            )),
        },
        _ => Err(access::AccessFailure::WrongTypeError(
            keytrace,
            hh_json_helpers::JsonType::IntegerT,
        )),
    })
}

/// `int_of_string_opt` (a copy of the private one of `typing_array_access`): an OCaml integer literal (a sign, `0x`, `0o`, `0b`
/// or `0u`, digits and `_`), within the range of an OCaml `int` (63 bits).
fn int_of_string_opt(s: &str) -> Option<isize> {
    const MAX: i128 = (1 << 62) - 1;
    let (negative, s) = match s.strip_prefix('-') {
        Some(s) => (true, s),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let lower = s.to_ascii_lowercase();
    let (radix, digits, decimal) = if let Some(d) = lower.strip_prefix("0x") {
        (16, d, false)
    } else if let Some(d) = lower.strip_prefix("0o") {
        (8, d, false)
    } else if let Some(d) = lower.strip_prefix("0b") {
        (2, d, false)
    } else if let Some(d) = lower.strip_prefix("0u") {
        (10, d, false)
    } else {
        (10, lower.as_str(), true)
    };
    // The first character is a digit; `_` can follow.
    if !digits.chars().next()?.is_digit(radix) {
        return None;
    }
    let mut n: i128 = 0;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        n = n * radix as i128 + c.to_digit(radix)? as i128;
        // Unsigned literals can use all the 63 bits; they wrap around.
        if n > 2 * MAX + 1 {
            return None;
        }
    }
    if decimal {
        // Decimal literals are signed: up to `max_int`, or `-min_int`.
        if n > MAX + (negative as i128) {
            return None;
        }
    } else if n > MAX {
        n -= 2 * (MAX + 1);
    }
    Some((if negative { -n } else { n }) as isize)
}

fn error_at_keytrace<A>(keytrace: &access::Keytrace, error_message: String) -> Result<A, String> {
    Err(error_message + &access::keytrace_to_string(keytrace))
}

pub fn compile_pattern(ctx: &provider_context::T, json: &Json) -> Result<Pattern, String> {
    compile_pattern_(ctx, json, &vec![])
}

fn compile_pattern_(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> Result<Pattern, String> {
    let (pattern_type, pattern_type_keytrace) = wrap(access::get_string("pattern_type", (json, keytrace)))?;
    match pattern_type.as_str() {
        "node_pattern" => compile_node_pattern(ctx, json, keytrace),
        "missing_node_pattern" => Ok(Pattern::MissingNodePattern),
        "match_pattern" => {
            let (match_name, _) = wrap(access::get_string("match_name", (json, keytrace)))?;
            Ok(Pattern::MatchPattern {
                match_name: MatchName(match_name),
            })
        }
        "descendant_pattern" => {
            let (pattern, pattern_keytrace) = wrap(access::get_obj("pattern", (json, keytrace)))?;
            let pattern = compile_pattern_(ctx, &pattern, &pattern_keytrace)?;
            Ok(Pattern::DescendantPattern {
                pattern: Box::new(pattern),
            })
        }
        "list_pattern" => compile_list_pattern(ctx, json, keytrace),
        "raw_text_pattern" => {
            let (raw_text, _) = wrap(access::get_string("raw_text", (json, keytrace)))?;
            Ok(Pattern::RawTextPattern { raw_text })
        }
        "type_pattern" => {
            let (subtype_of_json, subtype_of_keytrace) =
                wrap(access::get_obj("subtype_of", (json, keytrace)))?;
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
            let (json, keytrace) = wrap(access::get_obj("pattern", (json, keytrace)))?;
            let pattern = compile_pattern_(ctx, &json, &keytrace)?;
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

fn compile_node_pattern(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> Result<Pattern, String> {
    let (kind, kind_keytrace) = wrap(access::get_string("kind", (json, keytrace)))?;
    let kind_info = schema_definition::schema
        .iter()
        .find(|schema_node| schema_node.description == kind);
    match kind_info {
        None => error_at_keytrace(&kind_keytrace, format!("Kind '{}' doesn't exist", kind)),
        Some(kind_info) => {
            let (children_json, children_keytrace) = wrap(access::get_obj("children", (json, keytrace)))?;
            // This has already been verified to be an object above.
            let children = hh_json_helpers::get_object_exn(&children_json).expect("get_object_exn");
            // We're given a field name like `binary_right_operand`, but the field
            // names in the schema are things like `right_operand`, and you have to
            // affix the prefix yourself. For consistency with other tooling, we want
            // to use `binary_right_operand` instead of just `right_operand`.
            let get_prefixed_field_name = |field_name: &str| format!("{}_{}", kind_info.prefix, field_name);
            let get_child_type = |child_keytrace: &access::Keytrace, child_name: &str| -> Result<ChildType, String> {
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
            let children_patterns: Vec<Result<(ChildType, Pattern), String>> = children
                .iter()
                .enumerate()
                .map(|(index, (child_name, pattern_json))| {
                    let mut child_keytrace = vec![index.to_string()];
                    child_keytrace.extend(children_keytrace.iter().cloned());
                    let child_name = get_child_type(&child_keytrace, child_name)?;
                    let pattern = compile_pattern_(ctx, pattern_json, &child_keytrace)?;
                    Ok((child_name, pattern))
                })
                .collect();
            let children = children_patterns.into_iter().collect::<Result<Vec<_>, _>>()?;
            Ok(Pattern::NodePattern {
                kind: NodeKind(kind),
                children,
            })
        }
    }
}

fn compile_list_pattern(ctx: &provider_context::T, json: &Json, keytrace: &access::Keytrace) -> Result<Pattern, String> {
    // `Hh_json_helpers.get_field_opt (Access.get_number_int "max_length") json`
    let max_length = match get_number_int("max_length", (json, &vec![])) {
        Ok((r, _)) => Some(r),
        Err(_) => None,
    };
    let (children_json, children_keytrace) = wrap(access::get_obj("children", (json, keytrace)))?;
    // This has already been verified to be an object above.
    let children = hh_json_helpers::get_object_exn(&children_json).expect("get_object_exn");
    let children_patterns: Vec<Result<(isize, Pattern), String>> = children
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
            let pattern = compile_pattern_(ctx, pattern_json, &child_keytrace)?;
            Ok((index, pattern))
        })
        .collect();
    let children = children_patterns.into_iter().collect::<Result<Vec<_>, _>>()?;
    Ok(Pattern::ListPattern {
        children,
        max_length,
    })
}

fn compile_child_patterns_helper(
    ctx: &provider_context::T,
    json: &Json,
    keytrace: &access::Keytrace,
) -> Result<Vec<Pattern>, String> {
    let (pattern_list, pattern_list_keytrace) = wrap(access::get_array("patterns", (json, keytrace)))?;
    let compiled_patterns: Vec<Result<Pattern, String>> = pattern_list
        .iter()
        .enumerate()
        .map(|(i, json)| {
            let mut keytrace = vec![i.to_string()];
            keytrace.extend(pattern_list_keytrace.iter().cloned());
            compile_pattern_(ctx, json, &keytrace)
        })
        .collect();
    compiled_patterns.into_iter().collect()
}

pub fn result_to_json(sort_results: bool, result: Option<&Result_>) -> Json {
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

pub fn search(
    ctx: &provider_context::T,
    entry: &Arc<provider_context::Entry>,
    pattern: &Pattern,
) -> Option<Result_> {
    let (source_text, root) = crate::identify_symbol_service::compute_cst(entry);
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
