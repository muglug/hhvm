// Copyright (c) Meta Platforms, Inc. and affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

//! hack_format.ml: the transform from the full-fidelity CST to the Doc IR.
//!
//! This follows hack_format.ml function by function and case by case.

use std::rc::Rc;

use bumpalo::Bump;
use operator::Operator;
use parser_core_types::parser_env::ParserEnv;
use parser_core_types::syntax_kind::SyntaxKind as SK;
use parser_core_types::token_kind::TokenKind as TK;
use parser_core_types::trivia_kind::TriviaKind;

use crate::doc::Cost;
use crate::doc::Doc;
use crate::doc::Doc::*;
use crate::doc::RuleKind;
use crate::doc::newline;
use crate::doc::space;
use crate::doc::space_split;
use crate::doc::split;
use crate::error::Exn;
use crate::error::raise;
use crate::format_env::Env;
use crate::syntax::Node;
use crate::syntax::Trivia;
use crate::syntax_fields as sf;

type Elem<'f, 'a> = &'f dyn Fn(&Node<'a>) -> Doc<'a>;

/// The optional arguments of `handle_list`.
#[derive(Default)]
struct ListOpts<'f, 'a> {
    before_each: Option<&'f dyn Fn() -> Doc<'a>>,
    after_each: Option<&'f dyn Fn(bool) -> Doc<'a>>,
    handle_element: Option<Elem<'f, 'a>>,
    handle_last: Option<Elem<'f, 'a>>,
}

fn failwith(msg: &str) -> ! {
    raise(Exn::Failure(msg.to_string()))
}

fn cat(docs: Vec<Doc<'_>>) -> Doc<'_> {
    Concat(docs)
}

fn rule<'a>(kind: RuleKind, body: Doc<'a>) -> Doc<'a> {
    Doc::with_rule(kind, body)
}

fn lazy_rule<'a>(kind: RuleKind, before: Doc<'a>, body: Doc<'a>) -> Doc<'a> {
    Doc::with_lazy_rule(kind, before, body)
}

const PARENTAL: RuleKind = RuleKind::Parental;
const SIMPLE_BASE: RuleKind = RuleKind::Simple(Cost::Base);

fn is_trivia_kind_fallthrough(k: TriviaKind) -> bool {
    k == TriviaKind::FallThrough
}

fn is_trivia_kind_end_of_line(k: TriviaKind) -> bool {
    k == TriviaKind::EndOfLine
}

fn is_trivia_kind_white_space(k: TriviaKind) -> bool {
    k == TriviaKind::WhiteSpace
}

/// True if the trivia list contains WhiteSpace trivia (spaces and tabs, but
/// not newlines).
fn has_whitespace(trivia: &[&Trivia<'_>]) -> bool {
    trivia.iter().any(|t| is_trivia_kind_white_space(t.kind))
}

/// True if the trivia list contains EndOfLine trivia.
fn has_newline(trivia: &[&Trivia<'_>]) -> bool {
    trivia.iter().any(|t| is_trivia_kind_end_of_line(t.kind))
}

fn has_newline_s(trivia: &[Trivia<'_>]) -> bool {
    trivia.iter().any(|t| is_trivia_kind_end_of_line(t.kind))
}

fn has_whitespace_s(trivia: &[Trivia<'_>]) -> bool {
    trivia.iter().any(|t| is_trivia_kind_white_space(t.kind))
}

fn is_invisible(trivia: &Trivia<'_>) -> bool {
    matches!(trivia.kind, TriviaKind::WhiteSpace | TriviaKind::EndOfLine)
}

fn refs<'t, 'a>(trivia: &'t [Trivia<'a>]) -> Vec<&'t Trivia<'a>> {
    trivia.iter().collect()
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    crate::noformat::contains(haystack, needle)
}

/// We don't format the node after a comment containing "hackfmt-ignore".
fn is_ignore_comment(trivia: &Trivia<'_>) -> bool {
    match trivia.kind {
        TriviaKind::DelimitedComment | TriviaKind::SingleLineComment => {
            contains(trivia.text, b"hackfmt-ignore")
        }
        _ => false,
    }
}

/// `Str.split_delim (Str.regexp "\n")`
fn split_delim_newline(text: &[u8]) -> Vec<&[u8]> {
    if text.is_empty() {
        vec![]
    } else {
        text.split(|c| *c == b'\n').collect()
    }
}

/// `Str.split (Str.regexp "\n")`: one delimiter at the very start is
/// skipped, and no empty string follows a final delimiter.
fn split_newline(text: &[u8]) -> Vec<&[u8]> {
    let len = text.len();
    let mut pos = if text.first() == Some(&b'\n') { 1 } else { 0 };
    let mut result = vec![];
    while pos < len {
        match text[pos..].iter().position(|c| *c == b'\n') {
            None => {
                result.push(&text[pos..]);
                break;
            }
            Some(i) => {
                result.push(&text[pos..pos + i]);
                pos = pos + i + 1;
            }
        }
    }
    result
}

fn make_string<'a>(text: &'a [u8], width: usize) -> Doc<'a> {
    let split_text = split_delim_newline(text);
    if split_text.len() == 1 {
        Text(text, width)
    } else {
        MultilineString(split_text, width)
    }
}

fn transform_leading_trivia<'a>(t: &[&Trivia<'a>]) -> Doc<'a> {
    transform_trivia(true, t)
}

fn transform_trailing_trivia<'a>(t: &[&Trivia<'a>]) -> Doc<'a> {
    transform_trivia(false, t)
}

fn transform_leading_trivia_s<'a>(t: &[Trivia<'a>]) -> Doc<'a> {
    transform_trivia(true, &refs(t))
}

fn transform_trailing_trivia_s<'a>(t: &[Trivia<'a>]) -> Doc<'a> {
    transform_trivia(false, &refs(t))
}

const MAX_CONSECUTIVE_BLANK_LINES: usize = 1;

fn transform_leading_invisibles<'a>(triv: &[&Trivia<'a>]) -> Doc<'a> {
    let mut newlines = 0;
    Concat(
        triv.iter()
            .map(|t| {
                let ignored = Ignore(t.width());
                match t.kind {
                    TriviaKind::EndOfLine => {
                        newlines += 1;
                        Concat(vec![
                            ignored,
                            if newlines <= MAX_CONSECUTIVE_BLANK_LINES {
                                BlankLine
                            } else {
                                Nothing
                            },
                        ])
                    }
                    _ => ignored,
                }
            })
            .collect(),
    )
}

fn ignore_trailing_invisibles<'a>(triv: &[&Trivia<'a>]) -> Doc<'a> {
    Concat(triv.iter().map(|t| Ignore(t.width())).collect())
}

fn transform_xhp_leading_trivia<'a>(triv: &[&Trivia<'a>]) -> Doc<'a> {
    let mut up_to_first_newline = vec![];
    let mut after_newline = vec![];
    let mut seen = false;
    for t in triv {
        if seen {
            after_newline.push(*t);
        } else {
            up_to_first_newline.push(*t);
            seen = is_trivia_kind_end_of_line(t.kind);
        }
    }
    Concat(vec![
        ignore_trailing_invisibles(&up_to_first_newline),
        transform_leading_invisibles(&after_newline),
    ])
}

fn transform_trivia<'a>(is_leading: bool, trivia: &[&Trivia<'a>]) -> Doc<'a> {
    struct State<'t, 'a> {
        leading_invisibles: Vec<&'t Trivia<'a>>,
        last_comment: Option<Doc<'a>>,
        last_comment_was_delimited: bool,
        newline_followed_last_comment: bool,
        whitespace_followed_last_comment: bool,
        trailing_invisibles: Vec<&'t Trivia<'a>>,
        comments: Vec<Doc<'a>>,
    }
    impl<'t, 'a> State<'t, 'a> {
        fn make_comment(&mut self) {
            if self.last_comment.is_some() {
                self.newline_followed_last_comment = has_newline(&self.trailing_invisibles);
                self.whitespace_followed_last_comment = has_whitespace(&self.trailing_invisibles);
            }
            let doc = Concat(vec![
                transform_leading_invisibles(&self.leading_invisibles),
                self.last_comment.take().unwrap_or(Nothing),
                ignore_trailing_invisibles(&self.trailing_invisibles),
                if self.last_comment_was_delimited && self.whitespace_followed_last_comment {
                    Space
                } else if self.newline_followed_last_comment {
                    Newline
                } else {
                    Nothing
                },
            ]);
            self.comments.push(doc);
            self.leading_invisibles.clear();
            self.trailing_invisibles.clear();
        }
    }
    let mut indent: usize = 0;
    let mut currently_leading = is_leading;
    let mut st = State {
        leading_invisibles: vec![],
        last_comment: None,
        last_comment_was_delimited: false,
        newline_followed_last_comment: false,
        whitespace_followed_last_comment: false,
        trailing_invisibles: vec![],
        comments: vec![],
    };
    for triv in trivia {
        match triv.kind {
            TriviaKind::ExtraTokenError
            | TriviaKind::FixMe
            | TriviaKind::Ignore
            | TriviaKind::IgnoreError
            | TriviaKind::DelimitedComment => {
                let preceded_by_whitespace = if currently_leading {
                    has_whitespace(&st.leading_invisibles)
                } else {
                    has_whitespace(&st.trailing_invisibles)
                };
                st.make_comment();
                let delimited_lines = split_newline(triv.text);
                let map_tail = |s: &'a [u8]| {
                    let prefix_space_count = s.iter().take_while(|c| **c == b' ' || **c == b'\t').count();
                    // If we're dealing with trailing trivia, then we don't
                    // have a good signal for the indent level, so we just cut
                    // all leading spaces. Otherwise, we cut a number of
                    // spaces equal to the indent before the delimited comment
                    // opener.
                    let start_index = if is_leading {
                        std::cmp::min(indent, prefix_space_count)
                    } else {
                        prefix_space_count
                    };
                    let dc = &s[start_index..];
                    Concat(vec![
                        Ignore(1),
                        Newline,
                        Ignore(start_index),
                        Comment(dc, dc.len()),
                    ])
                };
                let Some((hd, tl)) = delimited_lines.split_first() else {
                    failwith("hd")
                };
                let hd = Comment(hd, hd.len());
                let should_break = match triv.kind {
                    TriviaKind::FixMe | TriviaKind::Ignore | TriviaKind::IgnoreError => false,
                    _ => currently_leading,
                };
                let mut lines = vec![hd];
                lines.extend(tl.iter().map(|s| map_tail(s)));
                st.last_comment = Some(Concat(vec![
                    if should_break {
                        Newline
                    } else if preceded_by_whitespace {
                        Space
                    } else {
                        Nothing
                    },
                    Concat(lines),
                ]));
                st.last_comment_was_delimited = true;
                currently_leading = false;
            }
            TriviaKind::FallThrough | TriviaKind::SingleLineComment => {
                st.make_comment();
                st.last_comment = Some(Concat(vec![
                    if currently_leading { Newline } else { Space },
                    SingleLineComment(triv.text, triv.width()),
                ]));
                st.last_comment_was_delimited = false;
                currently_leading = false;
            }
            TriviaKind::EndOfLine => {
                indent = 0;
                if currently_leading {
                    st.leading_invisibles.push(triv);
                } else {
                    st.trailing_invisibles.push(triv);
                    st.make_comment();
                }
                currently_leading = true;
            }
            TriviaKind::WhiteSpace => {
                if currently_leading {
                    indent = triv.width();
                    st.leading_invisibles.push(triv);
                } else {
                    st.trailing_invisibles.push(triv);
                }
            }
        }
    }
    if st.comments.is_empty() {
        if is_leading {
            transform_leading_invisibles(trivia)
        } else {
            ignore_trailing_invisibles(trivia)
        }
    } else {
        st.make_comment();
        Concat(st.comments)
    }
}

fn node_has_trailing_newline(node: &Node<'_>) -> bool {
    has_newline_s(node.trailing_trivia())
}

fn get_operator_type(op: &Node<'_>) -> Operator {
    match op.token_kind() {
        Some(k) => Operator::trailing_from_token(k),
        None => failwith("Operator should always be a token"),
    }
}

fn is_concat(op: &Node<'_>) -> bool {
    matches!(get_operator_type(op), Operator::ConcatenationOperator)
}

fn list_length(node: &Node<'_>) -> usize {
    match node.kind {
        SK::Missing => 0,
        SK::SyntaxList => node.children.len(),
        _ => 1,
    }
}

fn after_each_argument<'a>(is_last: bool) -> Doc<'a> {
    if is_last { Split } else { space_split() }
}

fn separate_with_space_split<'a>(is_last: bool) -> Doc<'a> {
    if is_last { Nothing } else { space_split() }
}

/// Sometimes, we want to use a non-Parental rule for function call argument
/// lists and other similar constructs when not breaking around the argument
/// list looks reasonable. This function blacklists the constructs that don't
/// look so great when we do this.
fn looks_bad_in_non_parental_braces(item: &Node<'_>) -> bool {
    let item = if item.kind == SK::ListItem {
        sf::list_item(item).item
    } else {
        item
    };
    match item.kind {
        SK::LambdaExpression if sf::lambda_expression(item).body.kind == SK::CompoundStatement => {
            false
        }
        SK::FunctionCallExpression => {
            sf::function_call_expression(item).receiver.kind == SK::MemberSelectionExpression
        }
        SK::ConditionalExpression
        | SK::BinaryExpression
        | SK::MemberSelectionExpression
        | SK::FieldSpecifier
        | SK::FieldInitializer
        | SK::ElementInitializer
        | SK::LambdaExpression
        | SK::XHPExpression
        | SK::IsExpression
        | SK::AsExpression
        | SK::NullableAsExpression => true,
        _ => false,
    }
}

/// Check the leading trivia of the node's leading token: split it before the
/// first hackfmt-ignore comment.
fn leading_ignore_comment<'t, 'a>(trivia: &'t [Trivia<'a>]) -> (&'t [Trivia<'a>], &'t [Trivia<'a>]) {
    let n = trivia
        .iter()
        .position(is_ignore_comment)
        .unwrap_or(trivia.len());
    trivia.split_at(n)
}

pub struct Fmt<'e, 'a> {
    env: &'e Env,
    arena: &'a Bump,
}

/// `Hack_format.transform`
pub fn transform<'a>(env: &Env, arena: &'a Bump, node: &Node<'a>) -> Doc<'a> {
    Fmt { env, arena }.t(node)
}

impl<'e, 'a> Fmt<'e, 'a> {
    /// Main transform function, which takes a full-fidelity CST node and
    /// produces a Doc.t node.
    pub fn t(&self, node: &Node<'a>) -> Doc<'a> {
        // Leave this node as it was in the original source if it is preceded
        // by a hackfmt-ignore comment.
        if let Some(doc) = self.transform_node_if_ignored(node) {
            return doc;
        }
        let env = self.env;
        match node.kind {
            SK::Missing => Nothing,
            SK::Token(token_kind) => {
                let x = node.token.as_ref().unwrap();
                Concat(vec![
                    match token_kind {
                        TK::EndOfFile => {
                            let leading = &x.leading;
                            let mut end = leading.len();
                            while end > 0 && is_invisible(&leading[end - 1]) {
                                end -= 1;
                            }
                            transform_leading_trivia_s(&leading[..end])
                        }
                        _ => transform_leading_trivia_s(&x.leading),
                    },
                    match token_kind {
                        TK::EndOfFile => Nothing,
                        TK::SingleQuotedStringLiteral
                        | TK::DoubleQuotedStringLiteral
                        | TK::DoubleQuotedStringLiteralHead
                        | TK::StringLiteralBody
                        | TK::DoubleQuotedStringLiteralTail
                        | TK::HeredocStringLiteral
                        | TK::HeredocStringLiteralHead
                        | TK::HeredocStringLiteralTail
                        | TK::NowdocStringLiteral => make_string(x.text, x.width()),
                        TK::XHPStringLiteral if env.version_gte(2) => make_string(x.text, x.width()),
                        _ => Text(x.text, x.width()),
                    },
                    transform_trailing_trivia_s(&x.trailing),
                ])
            }
            SK::SyntaxList => {
                let text = node.text();
                failwith(&format!(
                    "Error: SyntaxList should never be handled directly;\n      offending text is '{}'.",
                    String::from_utf8_lossy(&text)
                ))
            }
            SK::EndOfFile => self.t(sf::end_of_file(node).token),
            SK::Script => cat(vec![self.handle_possible_list(sf::script(node).declarations, ListOpts::default())]),
            SK::LiteralExpression => {
                let literal_expression = sf::literal_expression(node).expression;
                // Double quoted string literals can create a list
                let wrap_with_literal_type = |kind: TK, transformed: Doc<'a>| match kind {
                    TK::HeredocStringLiteral
                    | TK::HeredocStringLiteralHead
                    | TK::HeredocStringLiteralTail
                    | TK::NowdocStringLiteral => DocLiteral(Box::new(transformed)),
                    TK::DecimalLiteral
                    | TK::OctalLiteral
                    | TK::HexadecimalLiteral
                    | TK::BinaryLiteral
                    | TK::FloatingLiteral => NumericLiteral(Box::new(transformed)),
                    _ => transformed,
                };
                match literal_expression.kind {
                    SK::Token(kind) => wrap_with_literal_type(kind, self.t(literal_expression)),
                    SK::SyntaxList => match literal_expression.trailing_token() {
                        Some(tok) => wrap_with_literal_type(
                            tok.kind,
                            Concat(literal_expression.children.iter().map(|c| self.t(c)).collect()),
                        ),
                        None => failwith("Expected Token"),
                    },
                    _ => failwith("Expected Token or SyntaxList"),
                }
            }
            SK::PrefixedStringExpression => {
                let x = sf::prefixed_string_expression(node);
                cat(vec![self.t(x.name), self.t(x.str)])
            }
            SK::MarkupSection => {
                let x = sf::markup_section(node);
                if x.hashbang.is_missing() {
                    self.t(x.suffix)
                } else {
                    cat(vec![self.t(x.hashbang), Newline, self.t(x.suffix)])
                }
            }
            SK::MarkupSuffix => self.transform_simple_statement(node),
            SK::SimpleTypeSpecifier
            | SK::VariableExpression
            | SK::PipeVariableExpression
            | SK::PropertyDeclarator
            | SK::ConstantDeclarator
            | SK::ScopeResolutionExpression
            | SK::EmbeddedMemberSelectionExpression
            | SK::EmbeddedSubscriptExpression
            | SK::PostfixUnaryExpression
            | SK::XHPRequired
            | SK::XHPLateinit
            | SK::XHPSimpleClassAttribute
            | SK::XHPClose
            | SK::TypeConstant
            | SK::GenericTypeSpecifier
            | SK::NullableTypeSpecifier
            | SK::LikeTypeSpecifier
            | SK::VariablePattern
            | SK::ShapeSplatSpecifier
            | SK::ShapeSplatExpression
            | SK::ListItem => self.transform_simple(node),
            SK::ReifiedTypeArgument => {
                let x = sf::reified_type_argument(node);
                cat(vec![self.t(x.reified), Space, self.t(x.type_)])
            }
            SK::QualifiedName => self.handle_possible_list(sf::qualified_name(node).parts, ListOpts::default()),
            SK::ModuleName => self.handle_possible_list(sf::module_name(node).parts, ListOpts::default()),
            SK::ExpressionStatement => self.transform_simple_statement(node),
            SK::EnumDeclaration => {
                let x = sf::enum_declaration(node);
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.colon),
                    Space,
                    SplitWith(Cost::Base),
                    Nest(vec![Space, self.t(x.base), Space, self.t(x.type_), Space]),
                    self.braced_block_nest(x.left_brace, x.right_brace, vec![
                        self.handle_possible_list(x.use_clauses, ListOpts::default()),
                        self.handle_possible_list(x.enumerators, ListOpts::default()),
                    ], true),
                    Newline,
                ])
            }
            SK::Enumerator => {
                let x = sf::enumerator(node);
                let value = self.t(x.value);
                cat(vec![
                    self.t(x.name),
                    Space,
                    self.t(x.equal),
                    Space,
                    if value.has_split() { SplitWith(Cost::Base) } else { Nothing },
                    Nest(vec![value]),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::EnumUse => {
                let x = sf::enum_use(node);
                cat(vec![
                    self.t(x.keyword),
                    match x.names.list_elements() {
                        Some(l) if l.len() == 1 => cat(vec![Space, self.t(l[0])]),
                        Some(_) => rule(PARENTAL, Nest(vec![self.handle_possible_list(x.names, ListOpts {
                            before_each: Some(&space_split),
                            ..Default::default()
                        })])),
                        None => cat(vec![Space, self.t(x.names)]),
                    },
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::AliasDeclaration => {
                let x = sf::alias_declaration(node);
                // TODO: revisit this for long names
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.module_kw_opt),
                    when_present(x.module_kw_opt, space),
                    self.t(x.keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.generic_parameter),
                    Space,
                    self.handle_possible_list(x.constraint, ListOpts::default()),
                    when_present(x.equal, || {
                        cat(vec![
                            Space,
                            self.t(x.equal),
                            Space,
                            SplitWith(Cost::Base),
                            Nest(vec![self.t(x.type_)]),
                        ])
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ContextAliasDeclaration => {
                let x = sf::context_alias_declaration(node);
                // TODO: revisit this for long names
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.t(x.keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.generic_parameter),
                    Space,
                    self.handle_possible_list(x.as_constraint, ListOpts::default()),
                    when_present(x.equal, || {
                        cat(vec![
                            Space,
                            self.t(x.equal),
                            Space,
                            SplitWith(Cost::Base),
                            Nest(vec![self.t(x.context)]),
                        ])
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::CaseTypeDeclaration => {
                let x = sf::case_type_declaration(node);
                let has_leading_bar = match x.variants.list_elements() {
                    Some(l) if !l.is_empty() => {
                        l[0].kind == SK::CaseTypeVariant && !sf::case_type_variant(l[0]).bar.is_missing()
                    }
                    _ => false,
                };
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.case_keyword),
                    Space,
                    self.t(x.type_keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.generic_parameter),
                    when_present(x.as_, space),
                    self.t(x.as_),
                    when_present(x.as_, space),
                    self.handle_possible_list(x.bounds, ListOpts::default()),
                    when_present(x.equal, || {
                        cat(vec![
                            Space,
                            self.t(x.equal),
                            if has_leading_bar { Newline } else { Space },
                            rule(
                                if has_leading_bar { RuleKind::Always } else { PARENTAL },
                                Nest(vec![self.handle_possible_list(x.variants, ListOpts {
                                    after_each: Some(&|is_last| if is_last { Nothing } else { space_split() }),
                                    ..Default::default()
                                })]),
                            ),
                        ])
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::CaseTypeVariant => {
                let x = sf::case_type_variant(node);
                Span(vec![
                    self.t(x.bar),
                    when_present(x.bar, space),
                    self.t(x.type_),
                    when_present(x.where_clause, space),
                    self.t(x.where_clause),
                ])
            }
            SK::PropertyDeclaration => {
                let x = sf::property_declaration(node);
                let declaration = cat(vec![
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.type_),
                    self.handle_declarator_list(x.declarators),
                    self.t(x.semicolon),
                    Newline,
                ]);
                if x.attribute_spec.is_missing() {
                    declaration
                } else {
                    lazy_rule(
                        PARENTAL,
                        self.handle_attribute_spec(x.attribute_spec),
                        cat(vec![Space, Split, declaration]),
                    )
                }
            }
            SK::NamespaceDeclaration => {
                let x = sf::namespace_declaration(node);
                cat(vec![self.t(x.header), self.t(x.body), Newline])
            }
            SK::NamespaceDeclarationHeader => {
                let x = sf::namespace_declaration_header(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.name)])
            }
            SK::NamespaceBody => {
                let x = sf::namespace_body(node);
                cat(vec![
                    Space,
                    self.braced_block_nest(x.left_brace, x.right_brace, vec![
                        self.handle_possible_list(x.declarations, ListOpts::default()),
                    ], true),
                ])
            }
            SK::NamespaceEmptyBody => {
                let x = sf::namespace_empty_body(node);
                cat(vec![self.t(x.semicolon)])
            }
            SK::NamespaceUseDeclaration => {
                let x = sf::namespace_use_declaration(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.kind),
                    when_present(x.kind, space),
                    rule(PARENTAL, Nest(vec![self.handle_possible_list(x.clauses, ListOpts {
                        after_each: Some(&after_each_argument),
                        ..Default::default()
                    })])),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::NamespaceGroupUseDeclaration => {
                let x = sf::namespace_group_use_declaration(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.kind),
                    when_present(x.kind, space),
                    self.t(x.prefix),
                    self.transform_argish(x.left_brace, x.clauses, x.right_brace, true, false, false),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::NamespaceUseClause => {
                let x = sf::namespace_use_clause(node);
                cat(vec![
                    self.t(x.clause_kind),
                    when_present(x.clause_kind, space),
                    self.t(x.name),
                    when_present(x.as_, space),
                    self.t(x.as_),
                    when_present(x.alias, space),
                    self.t(x.alias),
                ])
            }
            SK::FunctionDeclaration => {
                let x = sf::function_declaration(node);
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.t(x.declaration_header),
                    self.handle_possible_compound_statement(x.body, true, true),
                    Newline,
                ])
            }
            SK::FunctionDeclarationHeader => {
                let x = sf::function_declaration_header(node);
                cat(vec![
                    Span(self.transform_fn_decl_name(
                        x.modifiers,
                        x.keyword,
                        x.name,
                        x.type_parameter_list,
                        x.left_paren,
                    )),
                    self.transform_fn_decl_args(x.parameter_list, x.right_paren),
                    self.t(x.contexts),
                    self.t(x.colon),
                    when_present(x.colon, space),
                    self.t(x.readonly_return),
                    when_present(x.readonly_return, space),
                    self.t(x.type_),
                    when_present(x.where_clause, space),
                    self.t(x.where_clause),
                ])
            }
            SK::WhereClause => {
                let x = sf::where_clause(node);
                let last = |n: &Node<'a>| self.transform_last_arg(n, false);
                let elem = |n: &Node<'a>| self.transform_argish_item(n);
                cat(vec![rule(
                    PARENTAL,
                    cat(vec![
                        Space,
                        Split,
                        self.t(x.keyword),
                        Nest(vec![self.handle_possible_list(x.constraints, ListOpts {
                            before_each: Some(&space_split),
                            handle_last: Some(&last),
                            handle_element: Some(&elem),
                            ..Default::default()
                        })]),
                    ]),
                )])
            }
            SK::WhereConstraint => {
                let x = sf::where_constraint(node);
                cat(vec![
                    self.t(x.left_type),
                    Space,
                    self.t(x.operator),
                    Space,
                    self.t(x.right_type),
                ])
            }
            SK::TypeRefinement => {
                let x = sf::type_refinement(node);
                let members = x.members;
                let before = || {
                    cat(vec![
                        if list_length(members) > 1 { Newline } else { Space },
                        SplitWith(Cost::Moderate),
                    ])
                };
                let after = |last: bool| {
                    if last {
                        if list_length(members) > 1 { Newline } else { Space }
                    } else {
                        Nothing
                    }
                };
                cat(vec![
                    self.t(x.type_),
                    Space,
                    self.t(x.keyword),
                    Space,
                    self.t(x.left_brace),
                    space_split(),
                    Nest(vec![Span(vec![self.handle_possible_list(members, ListOpts {
                        before_each: Some(&before),
                        after_each: Some(&after),
                        ..Default::default()
                    })])]),
                    self.t(x.right_brace),
                ])
            }
            SK::TypeInRefinement | SK::CtxInRefinement => {
                let (kw, name, type_params, constraints, eq, eq_bound) = if node.kind == SK::TypeInRefinement {
                    let x = sf::type_in_refinement(node);
                    (x.keyword, x.name, x.type_parameters, x.constraints, x.equal, x.type_)
                } else {
                    let x = sf::ctx_in_refinement(node);
                    (x.keyword, x.name, x.type_parameters, x.constraints, x.equal, x.ctx_list)
                };
                Span(vec![
                    self.t(kw),
                    Space,
                    self.t(name),
                    self.t(type_params),
                    self.handle_possible_list(constraints, ListOpts {
                        before_each: Some(&space),
                        ..Default::default()
                    }),
                    when_present(eq, space),
                    self.t(eq),
                    when_present(eq_bound, || {
                        cat(vec![Space, SplitWith(Cost::High), Nest(vec![self.t(eq_bound)])])
                    }),
                ])
            }
            SK::Contexts => {
                let x = sf::contexts(node);
                self.transform_argish(x.left_bracket, x.types, x.right_bracket, true, false, false)
            }
            SK::FunctionCtxTypeSpecifier => {
                let x = sf::function_ctx_type_specifier(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.variable)])
            }
            SK::MethodishDeclaration => {
                let x = sf::methodish_declaration(node);
                cat(vec![
                    self.t(x.attribute),
                    when_present(x.attribute, newline),
                    self.t(x.function_decl_header),
                    when_present(x.function_body, || {
                        self.handle_possible_compound_statement(x.function_body, true, true)
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::MethodishTraitResolution => {
                let x = sf::methodish_trait_resolution(node);
                cat(vec![
                    self.t(x.attribute),
                    when_present(x.attribute, newline),
                    self.t(x.function_decl_header),
                    self.t(x.equal),
                    self.t(x.name),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ClassAliasDeclaration => {
                let x = sf::class_alias_declaration(node);
                cat(vec![
                    self.t(x.attribute),
                    when_present(x.attribute, newline),
                    self.handle_possible_list(x.modifiers, ListOpts::default()),
                    self.t(x.xhp),
                    self.t(x.keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.type_parameters),
                    Space,
                    self.t(x.equal),
                    Space,
                    self.t(x.original_name),
                    self.t(x.original_type_parameters),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ClassishDeclaration => {
                let x = sf::classish_declaration(node);
                let after_each_ancestor = |is_last: bool| if is_last { Nothing } else { space_split() };
                cat(vec![
                    self.t(x.attribute),
                    when_present(x.attribute, newline),
                    Span(vec![
                        self.handle_possible_list(x.modifiers, ListOpts {
                            after_each: Some(&|_| Space),
                            ..Default::default()
                        }),
                        self.t(x.xhp),
                        when_present(x.xhp, space),
                        self.t(x.keyword),
                        Space,
                        self.t(x.name),
                        self.t(x.type_parameters),
                    ]),
                    rule(
                        PARENTAL,
                        cat(vec![
                            when_present(x.extends_keyword, || {
                                Nest(vec![
                                    Space,
                                    Split,
                                    self.t(x.extends_keyword),
                                    rule(
                                        PARENTAL,
                                        Nest(vec![Span(vec![
                                            Space,
                                            if list_length(x.extends_list) == 1 {
                                                SplitWith(Cost::Base)
                                            } else {
                                                Split
                                            },
                                            Nest(vec![self.handle_possible_list(x.extends_list, ListOpts {
                                                after_each: Some(&after_each_ancestor),
                                                ..Default::default()
                                            })]),
                                        ])]),
                                    ),
                                ])
                            }),
                            when_present(x.implements_keyword, || {
                                Nest(vec![
                                    Space,
                                    Split,
                                    self.t(x.implements_keyword),
                                    rule(
                                        PARENTAL,
                                        Nest(vec![Span(vec![
                                            Space,
                                            if list_length(x.implements_list) == 1 {
                                                SplitWith(Cost::Base)
                                            } else {
                                                Split
                                            },
                                            Nest(vec![self.handle_possible_list(x.implements_list, ListOpts {
                                                after_each: Some(&after_each_ancestor),
                                                ..Default::default()
                                            })]),
                                        ])]),
                                    ),
                                ])
                            }),
                        ]),
                    ),
                    self.t(x.body),
                ])
            }
            SK::ClassishBody => {
                let x = sf::classish_body(node);
                cat(vec![
                    Space,
                    self.braced_block_nest(x.left_brace, x.right_brace, vec![
                        self.handle_possible_list(x.elements, ListOpts::default()),
                    ], true),
                    Newline,
                ])
            }
            SK::TraitUse => {
                let x = sf::trait_use(node);
                cat(vec![
                    self.t(x.keyword),
                    match x.names.list_elements() {
                        Some(l) if l.len() == 1 => cat(vec![Space, self.t(l[0])]),
                        Some(_) => rule(PARENTAL, Nest(vec![self.handle_possible_list(x.names, ListOpts {
                            before_each: Some(&space_split),
                            ..Default::default()
                        })])),
                        None => cat(vec![Space, self.t(x.names)]),
                    },
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::RequireClause => {
                let x = sf::require_clause(node);
                let name = self.t(x.name);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.kind),
                    Space,
                    if name.has_split() { SplitWith(Cost::High) } else { Nothing },
                    Nest(vec![name, self.t(x.semicolon)]),
                    Newline,
                ])
            }
            SK::RequireClauseConstraint => {
                let x = sf::require_clause_constraint(node);
                let name = self.t(x.name);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.this),
                    Space,
                    self.t(x.operator),
                    Space,
                    if name.has_split() { SplitWith(Cost::High) } else { Nothing },
                    Nest(vec![name, self.t(x.semicolon)]),
                    Newline,
                ])
            }
            SK::ConstDeclaration => {
                let x = sf::const_declaration(node);
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.keyword),
                    when_present(x.type_specifier, space),
                    self.t(x.type_specifier),
                    self.handle_declarator_list(x.declarators),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::TypeConstDeclaration => {
                let x = sf::type_const_declaration(node);
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    Space,
                    self.t(x.keyword),
                    Space,
                    self.t(x.type_keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.type_parameters),
                    self.handle_possible_list(x.type_constraints, ListOpts {
                        before_each: Some(&space),
                        ..Default::default()
                    }),
                    when_present(x.equal, space),
                    self.t(x.equal),
                    when_present(x.type_specifier, || {
                        cat(vec![Space, SplitWith(Cost::Base), Nest(vec![self.t(x.type_specifier)])])
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ContextConstDeclaration => {
                let x = sf::context_const_declaration(node);
                cat(vec![
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    Space,
                    self.t(x.const_keyword),
                    Space,
                    self.t(x.ctx_keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.type_parameters),
                    when_present(x.constraint, space),
                    self.handle_possible_list(x.constraint, ListOpts {
                        after_each: Some(&|is_last| if is_last { Nothing } else { Space }),
                        ..Default::default()
                    }),
                    when_present(x.equal, space),
                    self.t(x.equal),
                    when_present(x.ctx_list, || {
                        cat(vec![Space, SplitWith(Cost::Base), Nest(vec![self.t(x.ctx_list)])])
                    }),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ParameterDeclaration => {
                let x = sf::parameter_declaration(node);
                cat(vec![
                    self.handle_attribute_spec(x.attribute),
                    when_present(x.attribute, || cat(vec![Space, SplitWith(Cost::Base)])),
                    self.t(x.visibility),
                    when_present(x.visibility, space),
                    self.t(x.optional),
                    when_present(x.optional, space),
                    self.t(x.call_convention),
                    when_present(x.call_convention, space),
                    self.t(x.named),
                    when_present(x.named, space),
                    self.t(x.readonly),
                    when_present(x.readonly, space),
                    self.t(x.pre_ellipsis),
                    when_present(x.pre_ellipsis, space),
                    self.t(x.type_),
                    // A variadic named parameter has no name, e.g. `named arraykey...`
                    if x.name.is_missing() {
                        self.t(x.ellipsis)
                    } else {
                        let no_prefix = x.visibility.is_missing()
                            && x.call_convention.is_missing()
                            && x.type_.is_missing();
                        if no_prefix {
                            cat(vec![self.t(x.ellipsis), self.t(x.name)])
                        } else {
                            cat(vec![
                                Space,
                                SplitWith(Cost::Moderate),
                                Nest(vec![self.t(x.ellipsis), self.t(x.name)]),
                            ])
                        }
                    },
                    self.t(x.default_value),
                ])
            }
            SK::FileAttributeSpecification => {
                let x = sf::file_attribute_specification(node);
                cat(vec![
                    self.t(x.left_double_angle),
                    self.t(x.keyword),
                    self.t(x.colon),
                    when_present(x.colon, space),
                    self.transform_possible_comma_list(x.attributes, x.right_double_angle, false),
                    Newline,
                ])
            }
            SK::OldAttributeSpecification => self.handle_attribute_spec(node),
            SK::AttributizedSpecifier => {
                let x = sf::attributized_specifier(node);
                cat(vec![self.handle_attribute_spec(x.attribute_spec), Space, self.t(x.type_)])
            }
            SK::InclusionExpression => {
                let x = sf::inclusion_expression(node);
                cat(vec![
                    self.t(x.require),
                    match x.filename.kind {
                        SK::ParenthesizedExpression => Nothing,
                        _ => Space,
                    },
                    SplitWith(Cost::Base),
                    self.t(x.filename),
                ])
            }
            SK::InclusionDirective => {
                let x = sf::inclusion_directive(node);
                cat(vec![self.t(x.expression), self.t(x.semicolon), Newline])
            }
            SK::CompoundStatement => {
                let x = sf::compound_statement(node);
                cat(vec![
                    self.handle_compound_statement(x.left_brace, x.statements, x.right_brace, false, true),
                    Newline,
                ])
            }
            SK::UnsetStatement => {
                let x = sf::unset_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_paren, x.variables, x.right_paren, false, false, false),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::WhileStatement => {
                let x = sf::while_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.left_paren),
                    Split,
                    rule(
                        PARENTAL,
                        cat(vec![Nest(vec![self.t(x.condition)]), Split, self.t(x.right_paren)]),
                    ),
                    self.handle_possible_compound_statement(x.body, true, false),
                    Newline,
                ])
            }
            SK::UsingStatementBlockScoped => {
                let x = sf::using_statement_block_scoped(node);
                cat(vec![
                    self.t(x.await_keyword),
                    when_present(x.await_keyword, space),
                    self.t(x.using_keyword),
                    Space,
                    self.t(x.left_paren),
                    Split,
                    rule(
                        PARENTAL,
                        cat(vec![
                            Nest(vec![self.handle_possible_list(x.expressions, ListOpts {
                                after_each: Some(&separate_with_space_split),
                                ..Default::default()
                            })]),
                            Split,
                            self.t(x.right_paren),
                        ]),
                    ),
                    self.handle_possible_compound_statement(x.body, true, false),
                    Newline,
                ])
            }
            SK::UsingStatementFunctionScoped => {
                let x = sf::using_statement_function_scoped(node);
                cat(vec![
                    self.t(x.await_keyword),
                    when_present(x.await_keyword, space),
                    self.t(x.using_keyword),
                    Space,
                    self.t(x.expression),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::IfStatement => {
                let x = sf::if_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.transform_condition(x.left_paren, x.condition, x.right_paren),
                    self.transform_consequence(x.statement, x.right_paren),
                    self.t(x.else_clause),
                    Newline,
                ])
            }
            SK::ElseClause => {
                let x = sf::else_clause(node);
                cat(vec![
                    self.t(x.keyword),
                    match x.statement.kind {
                        SK::IfStatement => cat(vec![Space, self.t(x.statement), Space]),
                        _ => self.transform_consequence(x.statement, x.keyword),
                    },
                ])
            }
            SK::TryStatement => {
                let x = sf::try_statement(node);
                // TODO: revisit
                cat(vec![
                    self.t(x.keyword),
                    self.handle_possible_compound_statement(x.compound_statement, true, false),
                    self.handle_possible_list(x.catch_clauses, ListOpts::default()),
                    self.t(x.finally_clause),
                    Newline,
                ])
            }
            SK::CatchClause => {
                let x = sf::catch_clause(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.delimited_nest(x.left_paren, x.right_paren, vec![
                        self.t(x.type_),
                        Space,
                        SplitWith(Cost::Base),
                        Nest(vec![self.t(x.variable)]),
                    ], true, false),
                    self.handle_possible_compound_statement(x.body, true, false),
                ])
            }
            SK::FinallyClause => {
                let x = sf::finally_clause(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.handle_possible_compound_statement(x.body, true, false),
                ])
            }
            SK::DoStatement => {
                let x = sf::do_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.handle_possible_compound_statement(x.body, true, false),
                    self.t(x.while_keyword),
                    Space,
                    self.transform_condition(x.left_paren, x.condition, x.right_paren),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::ForStatement => {
                let x = sf::for_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.t(x.left_paren),
                    rule(
                        PARENTAL,
                        cat(vec![
                            Split,
                            Nest(vec![
                                self.handle_possible_list(x.initializer, ListOpts {
                                    after_each: Some(&separate_with_space_split),
                                    ..Default::default()
                                }),
                                self.t(x.first_semicolon),
                                Space,
                                Split,
                                self.handle_possible_list(x.control, ListOpts {
                                    after_each: Some(&separate_with_space_split),
                                    ..Default::default()
                                }),
                                self.t(x.second_semicolon),
                                Space,
                                Split,
                                self.handle_possible_list(x.end_of_loop, ListOpts {
                                    after_each: Some(&separate_with_space_split),
                                    ..Default::default()
                                }),
                            ]),
                            Split,
                            self.t(x.right_paren),
                        ]),
                    ),
                    self.handle_possible_compound_statement(x.body, true, false),
                    Newline,
                ])
            }
            SK::ForeachStatement => {
                let x = sf::foreach_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.delimited_nest(x.left_paren, x.right_paren, vec![
                        self.t(x.collection),
                        Space,
                        self.t(x.await_keyword),
                        Space,
                        self.t(x.as_),
                        Space,
                        SplitWith(Cost::Base),
                        Nest(vec![Span(vec![
                            self.t(x.key),
                            Space,
                            self.t(x.arrow),
                            Space,
                            SplitWith(Cost::Base),
                            Nest(vec![self.t(x.value)]),
                        ])]),
                    ], true, false),
                    self.handle_possible_compound_statement(x.body, true, false),
                    Newline,
                ])
            }
            SK::SwitchStatement => {
                let x = sf::switch_statement(node);
                let sections = x.sections.syntax_node_to_list();
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.delimited_nest(x.left_paren, x.right_paren, vec![self.t(x.expression)], true, false),
                    Space,
                    self.braced_block_nest(
                        x.left_brace,
                        x.right_brace,
                        sections.iter().map(|s| self.t(s)).collect(),
                        true,
                    ),
                    Newline,
                ])
            }
            SK::SwitchSection => {
                let x = sf::switch_section(node);
                // If there is FallThrough trivia leading the first case label,
                // handle it in a BlockNest so that it is indented to the same
                // level as the previous SwitchSection's statements.
                let (labels_leading, labels) = x.labels.remove_leading_trivia();
                // List.split_while (List.rev labels_leading) ~f:(not fallthrough)
                let n = labels_leading.len();
                let k = labels_leading
                    .iter()
                    .rev()
                    .take_while(|t| !is_trivia_kind_fallthrough(t.kind))
                    .count();
                let upto_fallthrough = refs(&labels_leading[..n - k]);
                let after_fallthrough = refs(&labels_leading[n - k..]);
                let labels = labels.syntax_node_to_list();
                let statements = x.statements.syntax_node_to_list();
                // When the statements in the SwitchSection are wrapped in a
                // single CompoundStatement, special-case the opening curly
                // brace to appear on the same line as the case label.
                let is_scoped_section =
                    statements.len() == 1 && statements[0].kind == SK::CompoundStatement;
                cat(vec![
                    if upto_fallthrough.is_empty() {
                        transform_leading_trivia(&after_fallthrough)
                    } else {
                        cat(vec![
                            BlockNest(vec![transform_leading_trivia(&upto_fallthrough), Newline]),
                            transform_trailing_trivia(&after_fallthrough),
                        ])
                    },
                    self.handle_list(&labels, ListOpts {
                        after_each: Some(&|is_last_label| {
                            if is_last_label && is_scoped_section { Nothing } else { Newline }
                        }),
                        ..Default::default()
                    }),
                    if is_scoped_section {
                        self.handle_list(&statements, ListOpts::default())
                    } else {
                        BlockNest(vec![self.handle_list(&statements, ListOpts::default())])
                    },
                    self.t(x.fallthrough),
                ])
            }
            SK::CaseLabel => {
                let x = sf::case_label(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.expression), self.t(x.colon)])
            }
            SK::DefaultLabel => {
                let x = sf::default_label(node);
                cat(vec![self.t(x.keyword), self.t(x.colon)])
            }
            SK::SwitchFallthrough => {
                let x = sf::switch_fallthrough(node);
                cat(vec![self.t(x.keyword), self.t(x.semicolon)])
            }
            SK::MatchStatement => {
                let x = sf::match_statement(node);
                let arms = x.arms.syntax_node_to_list();
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.delimited_nest(x.left_paren, x.right_paren, vec![self.t(x.expression)], true, false),
                    Space,
                    self.braced_block_nest(
                        x.left_brace,
                        x.right_brace,
                        arms.iter().map(|a| self.t(a)).collect(),
                        true,
                    ),
                    Newline,
                ])
            }
            SK::MatchStatementArm => {
                let x = sf::match_statement_arm(node);
                cat(vec![
                    self.t(x.pattern),
                    Space,
                    self.t(x.arrow),
                    Space,
                    match x.body.kind {
                        SK::CompoundStatement => {
                            let c = sf::compound_statement(x.body);
                            self.handle_compound_statement(c.left_brace, c.statements, c.right_brace, true, true)
                        }
                        _ => cat(vec![SplitWith(Cost::Base), Nest(vec![self.t(x.body)])]),
                    },
                    Newline,
                ])
            }
            SK::ReturnStatement => {
                let x = sf::return_statement(node);
                self.transform_keyword_expression_statement(x.keyword, x.expression, x.semicolon)
            }
            SK::YieldBreakStatement => {
                let x = sf::yield_break_statement(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.break_), self.t(x.semicolon)])
            }
            SK::ThrowStatement => {
                let x = sf::throw_statement(node);
                self.transform_keyword_expression_statement(x.keyword, x.expression, x.semicolon)
            }
            SK::BreakStatement => {
                let x = sf::break_statement(node);
                cat(vec![self.t(x.keyword), self.t(x.semicolon), Newline])
            }
            SK::ContinueStatement => {
                let x = sf::continue_statement(node);
                cat(vec![self.t(x.keyword), self.t(x.semicolon), Newline])
            }
            SK::EchoStatement => {
                let x = sf::echo_statement(node);
                match x.expressions.list_elements() {
                    Some(l)
                        if l.len() == 1
                            && l[0].kind == SK::ListItem
                            && sf::list_item(l[0]).item.kind == SK::ParenthesizedExpression =>
                    {
                        let expr = sf::list_item(l[0]).item;
                        cat(vec![self.t(x.keyword), self.t(expr), self.t(x.semicolon), Newline])
                    }
                    _ => self.transform_keyword_expr_list_statement(x.keyword, x.expressions, x.semicolon),
                }
            }
            SK::ConcurrentStatement => {
                let x = sf::concurrent_statement(node);
                cat(vec![
                    self.t(x.keyword),
                    Space,
                    self.handle_possible_compound_statement(x.statement, true, false),
                    Newline,
                ])
            }
            SK::SimpleInitializer => {
                let x = sf::simple_initializer(node);
                cat(vec![Space, self.t(x.equal), Space, SplitWith(Cost::Base), Nest(vec![self.t(x.value)])])
            }
            SK::AnonymousFunction => {
                let x = sf::anonymous_function(node);
                cat(vec![
                    self.handle_attribute_spec(x.attribute_spec),
                    when_present(x.attribute_spec, space),
                    self.t(x.async_keyword),
                    when_present(x.async_keyword, space),
                    self.t(x.function_keyword),
                    self.t(x.type_parameters),
                    self.transform_argish_with_return_type(
                        x.left_paren,
                        x.parameters,
                        x.right_paren,
                        x.ctx_list,
                        x.colon,
                        x.readonly_return,
                        x.type_,
                    ),
                    self.t(x.use_),
                    self.handle_possible_compound_statement(x.body, false, true),
                ])
            }
            SK::AnonymousFunctionUseClause => {
                let x = sf::anonymous_function_use_clause(node);
                // TODO: Revisit
                cat(vec![
                    Space,
                    self.t(x.keyword),
                    Space,
                    self.transform_argish(x.left_paren, x.variables, x.right_paren, true, false, false),
                ])
            }
            SK::ConstructorPattern => {
                let x = sf::constructor_pattern(node);
                if x.left_paren.is_missing() && x.members.is_missing() && x.right_paren.is_missing() {
                    self.t(x.constructor)
                } else {
                    self.transform_container_literal(
                        x.constructor,
                        x.left_paren,
                        x.members,
                        x.right_paren,
                        false,
                        None,
                        None,
                        None,
                    )
                }
            }
            SK::RefinementPattern => {
                let x = sf::refinement_pattern(node);
                cat(vec![self.t(x.variable), self.t(x.colon), Space, self.t(x.specifier)])
            }
            SK::LambdaExpression => {
                let x = sf::lambda_expression(node);
                cat(vec![
                    self.handle_attribute_spec(x.attribute_spec),
                    when_present(x.attribute_spec, space),
                    self.t(x.async_),
                    when_present(x.async_, space),
                    self.t(x.signature),
                    Space,
                    self.t(x.arrow),
                    self.handle_lambda_body(x.body),
                ])
            }
            SK::LambdaSignature => {
                let x = sf::lambda_signature(node);
                cat(vec![
                    self.t(x.function_keyword),
                    self.t(x.type_parameters),
                    self.t(x.left_paren),
                    when_present(x.parameters, split),
                    self.transform_fn_decl_args(x.parameters, x.right_paren),
                    self.t(x.contexts),
                    self.t(x.colon),
                    when_present(x.colon, space),
                    self.t(x.readonly_return),
                    when_present(x.readonly_return, space),
                    self.t(x.type_),
                ])
            }
            SK::CastExpression => Span(node.children.iter().map(|c| self.t(c)).collect()),
            SK::MemberSelectionExpression | SK::SafeMemberSelectionExpression => {
                self.handle_possible_chaining(node)
            }
            SK::YieldExpression => {
                let x = sf::yield_expression(node);
                cat(vec![self.t(x.keyword), Space, SplitWith(Cost::Base), Nest(vec![self.t(x.operand)])])
            }
            SK::PrefixUnaryExpression => {
                let x = sf::prefix_unary_expression(node);
                cat(vec![
                    self.t(x.operator),
                    match x.operator.token_kind() {
                        Some(k) => {
                            let is_parenthesized = x.operand.kind == SK::ParenthesizedExpression;
                            match k {
                                TK::Await | TK::Delay | TK::Readonly | TK::Clone => Space,
                                TK::Print => {
                                    if is_parenthesized { Nothing } else { Space }
                                }
                                _ => Nothing,
                            }
                        }
                        None => Nothing,
                    },
                    self.t(x.operand),
                ])
            }
            SK::BinaryExpression => {
                let x = sf::binary_expression(node);
                self.transform_binary_expression(false, x.left_operand, x.operator, x.right_operand)
            }
            SK::IsExpression | SK::AsExpression | SK::NullableAsExpression | SK::UpcastExpression => {
                // All four have (left_operand, operator, right_operand).
                let c = &node.children;
                let (left, kw, right) = (&*c[0], &*c[1], &*c[2]);
                cat(vec![
                    self.t(left),
                    Space,
                    SplitWith(Cost::Base),
                    Nest(vec![self.t(kw), Space, self.t(right)]),
                ])
            }
            SK::ConditionalExpression => {
                let x = sf::conditional_expression(node);
                lazy_rule(
                    PARENTAL,
                    self.t(x.test),
                    Nest(vec![
                        Space,
                        Split,
                        self.t(x.question),
                        when_present(x.consequence, || {
                            cat(vec![
                                Space,
                                if env.indent_width == 2 {
                                    Nest(vec![self.t(x.consequence)])
                                } else {
                                    self.t(x.consequence)
                                },
                                Space,
                                Split,
                            ])
                        }),
                        self.t(x.colon),
                        Space,
                        if !x.consequence.is_missing() && env.indent_width == 2 {
                            Nest(vec![self.t(x.alternative)])
                        } else {
                            self.t(x.alternative)
                        },
                    ]),
                )
            }
            SK::FunctionCallExpression => self.handle_possible_chaining(node),
            SK::FunctionPointerExpression => self.transform_simple(node),
            SK::EvalExpression => {
                let x = sf::eval_expression(node);
                cat(vec![self.t(x.keyword), self.transform_braced_item(x.left_paren, x.argument, x.right_paren)])
            }
            SK::IssetExpression => {
                let x = sf::isset_expression(node);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_paren, x.argument_list, x.right_paren, false, false, false),
                ])
            }
            SK::ParenthesizedExpression => {
                let x = sf::parenthesized_expression(node);
                cat(vec![
                    self.t(x.left_paren),
                    Split,
                    rule(PARENTAL, cat(vec![Nest(vec![self.t(x.expression)]), Split, self.t(x.right_paren)])),
                ])
            }
            SK::NameofExpression => {
                let x = sf::nameof_expression(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.target)])
            }
            SK::ETSpliceExpression => {
                let x = sf::et_splice_expression(node);
                cat(vec![
                    self.t(x.dollar),
                    self.t(x.left_brace),
                    Split,
                    rule(PARENTAL, cat(vec![Nest(vec![self.t(x.expression)]), Split, self.t(x.right_brace)])),
                ])
            }
            SK::BracedExpression => {
                let x = sf::braced_expression(node);
                // TODO: revisit this
                let kind = if x.left_brace.trailing_trivia().is_empty()
                    && x.expression.trailing_trivia().is_empty()
                {
                    SIMPLE_BASE
                } else {
                    PARENTAL
                };
                cat(vec![
                    self.t(x.left_brace),
                    Split,
                    rule(kind, cat(vec![Nest(vec![self.t(x.expression)]), Split, self.t(x.right_brace)])),
                ])
            }
            SK::EmbeddedBracedExpression => {
                let x = sf::embedded_braced_expression(node);
                cat(vec![self.t(x.left_brace), Nest(vec![self.t(x.expression)]), self.t(x.right_brace)])
            }
            SK::ListExpression => {
                let x = sf::list_expression(node);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_paren, x.members, x.right_paren, true, false, false),
                ])
            }
            SK::CollectionLiteralExpression => {
                let x = sf::collection_literal_expression(node);
                self.transform_container_literal(
                    x.name,
                    x.left_brace,
                    x.initializers,
                    x.right_brace,
                    true,
                    None,
                    None,
                    None,
                )
            }
            SK::ObjectCreationExpression => {
                let x = sf::object_creation_expression(node);
                cat(vec![self.t(x.new_keyword), Space, self.t(x.object)])
            }
            SK::ConstructorCall => {
                let x = sf::constructor_call(node);
                cat(vec![
                    self.t(x.type_),
                    self.transform_argish(x.left_paren, x.argument_list, x.right_paren, true, false, false),
                ])
            }
            SK::AnonymousClass => {
                let x = sf::anonymous_class(node);
                let after_each_ancestor = |is_last: bool| if is_last { Nothing } else { space_split() };
                cat(vec![
                    self.t(x.class_keyword),
                    self.transform_argish(x.left_paren, x.argument_list, x.right_paren, true, false, false),
                    when_present(x.extends_keyword, || {
                        cat(vec![
                            Space,
                            Split,
                            rule(
                                PARENTAL,
                                Nest(vec![Span(vec![
                                    self.t(x.extends_keyword),
                                    Space,
                                    Split,
                                    rule(PARENTAL, Nest(vec![self.handle_possible_list(x.extends_list, ListOpts {
                                        after_each: Some(&after_each_ancestor),
                                        ..Default::default()
                                    })])),
                                ])]),
                            ),
                        ])
                    }),
                    when_present(x.implements_keyword, || {
                        cat(vec![
                            Space,
                            Split,
                            rule(
                                PARENTAL,
                                Nest(vec![Span(vec![
                                    self.t(x.implements_keyword),
                                    Space,
                                    Split,
                                    rule(PARENTAL, Nest(vec![self.handle_possible_list(x.implements_list, ListOpts {
                                        after_each: Some(&after_each_ancestor),
                                        ..Default::default()
                                    })])),
                                ])]),
                            ),
                        ])
                    }),
                    self.t(x.body),
                ])
            }
            SK::DarrayIntrinsicExpression
            | SK::DictionaryIntrinsicExpression
            | SK::KeysetIntrinsicExpression
            | SK::VarrayIntrinsicExpression
            | SK::VectorIntrinsicExpression => {
                // All five have (keyword, explicit_type, left_bracket,
                // members, right_bracket).
                let c = &node.children;
                let (kw, explicit_type, left_p, members, right_p) = (&*c[0], &*c[1], &*c[2], &*c[3], &*c[4]);
                self.transform_container_literal(kw, left_p, members, right_p, false, None, Some(explicit_type), None)
            }
            SK::ElementInitializer => {
                let x = sf::element_initializer(node);
                self.transform_mapish_entry(x.key, x.arrow, x.value)
            }
            SK::SubscriptExpression => {
                let x = sf::subscript_expression(node);
                cat(vec![
                    self.t(x.receiver),
                    self.transform_braced_item(x.left_bracket, x.index, x.right_bracket),
                ])
            }
            SK::AwaitableCreationExpression => {
                let x = sf::awaitable_creation_expression(node);
                cat(vec![
                    self.handle_attribute_spec(x.attribute_spec),
                    when_present(x.attribute_spec, space),
                    self.t(x.async_),
                    when_present(x.async_, space),
                    // TODO: rethink possible one line bodies
                    // TODO: correctly handle spacing after the closing brace
                    self.handle_possible_compound_statement(x.compound_statement, false, false),
                ])
            }
            SK::XHPChildrenDeclaration => {
                let x = sf::xhp_children_declaration(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.expression), self.t(x.semicolon), Newline])
            }
            SK::XHPChildrenParenthesizedList => {
                let x = sf::xhp_children_parenthesized_list(node);
                cat(vec![self.transform_argish(x.left_paren, x.xhp_children, x.right_paren, false, false, false)])
            }
            SK::XHPCategoryDeclaration => {
                let x = sf::xhp_category_declaration(node);
                cat(vec![
                    self.t(x.keyword),
                    // TODO: Eliminate code duplication
                    rule(PARENTAL, Nest(vec![self.handle_possible_list(x.categories, ListOpts {
                        before_each: Some(&space_split),
                        ..Default::default()
                    })])),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::XHPEnumType => {
                let x = sf::xhp_enum_type(node);
                cat(vec![
                    self.t(x.like),
                    self.t(x.keyword),
                    Space,
                    self.transform_argish(x.left_brace, x.values, x.right_brace, true, false, false),
                ])
            }
            SK::XHPClassAttributeDeclaration => {
                let x = sf::xhp_class_attribute_declaration(node);
                cat(vec![
                    self.t(x.keyword),
                    match x.attributes.kind {
                        SK::Missing => Nothing,
                        SK::SyntaxList => {
                            let attrs = x.attributes.syntax_node_to_list();
                            if attrs.len() == 1 {
                                rule(PARENTAL, Nest(vec![Space, Split, self.t(attrs[0])]))
                            } else {
                                Nest(vec![self.handle_list(&attrs, ListOpts {
                                    before_each: Some(&newline),
                                    ..Default::default()
                                })])
                            }
                        }
                        _ => failwith("Expected SyntaxList"),
                    },
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::XHPClassAttribute => {
                let x = sf::xhp_class_attribute(node);
                // TODO: figure out nesting here
                cat(vec![
                    self.t(x.type_),
                    Space,
                    self.t(x.name),
                    when_present(x.initializer, space),
                    self.t(x.initializer),
                    when_present(x.required, space),
                    self.t(x.required),
                ])
            }
            SK::XHPSimpleAttribute => {
                let x = sf::xhp_simple_attribute(node);
                Span(vec![self.t(x.name), self.t(x.equal), SplitWith(Cost::Base), Nest(vec![self.t(x.expression)])])
            }
            SK::XHPSpreadAttribute => {
                let x = sf::xhp_spread_attribute(node);
                Span(vec![
                    self.t(x.left_brace),
                    self.t(x.spread_operator),
                    SplitWith(Cost::Base),
                    Nest(vec![self.t(x.expression)]),
                    self.t(x.right_brace),
                ])
            }
            SK::XHPOpen => {
                let x = sf::xhp_open(node);
                cat(vec![
                    self.t(x.left_angle),
                    self.t(x.name),
                    match x.attributes.kind {
                        SK::Missing => self.handle_xhp_open_right_angle_token(x.attributes, x.right_angle),
                        _ => cat(vec![
                            Space,
                            Split,
                            rule(
                                PARENTAL,
                                cat(vec![
                                    Nest(vec![self.handle_possible_list(x.attributes, ListOpts {
                                        after_each: Some(&|is_last| if !is_last { space_split() } else { Nothing }),
                                        ..Default::default()
                                    })]),
                                    self.handle_xhp_open_right_angle_token(x.attributes, x.right_angle),
                                ]),
                            ),
                        ]),
                    },
                ])
            }
            SK::XHPExpression => self.transform_xhp_expression(node),
            SK::VarrayTypeSpecifier | SK::VectorTypeSpecifier | SK::KeysetTypeSpecifier => {
                // All three have (keyword, left_angle, type, trailing_comma,
                // right_angle).
                let c = &node.children;
                let (kw, left_a, ty, trailing_comma, right_a) = (&*c[0], &*c[1], &*c[2], &*c[3], &*c[4]);
                cat(vec![
                    self.t(kw),
                    self.transform_braced_item_with_trailer(left_a, ty, trailing_comma, right_a),
                ])
            }
            SK::TypeParameter => {
                let x = sf::type_parameter(node);
                cat(vec![
                    self.handle_attribute_spec(x.attribute_spec),
                    when_present(x.attribute_spec, space),
                    self.t(x.reified),
                    when_present(x.reified, space),
                    self.t(x.variance),
                    self.t(x.name),
                    when_present(x.constraints, space),
                    self.handle_possible_list(x.constraints, ListOpts {
                        after_each: Some(&|is_last| if is_last { Nothing } else { Space }),
                        ..Default::default()
                    }),
                ])
            }
            SK::TypeConstraint => {
                let x = sf::type_constraint(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.type_)])
            }
            SK::ContextConstraint => {
                let x = sf::context_constraint(node);
                cat(vec![Space, self.t(x.keyword), Space, self.t(x.ctx_list)])
            }
            SK::DarrayTypeSpecifier => {
                let x = sf::darray_type_specifier(node);
                let key_list_item = Node::make_list_item(rc(x.key), rc(x.comma));
                let val_list_item = Node::make_list_item(rc(x.value), rc(x.trailing_comma));
                let args = Node::make_list(vec![Rc::new(key_list_item), Rc::new(val_list_item)]);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_angle, &args, x.right_angle, true, false, false),
                ])
            }
            SK::DictionaryTypeSpecifier => {
                let x = sf::dictionary_type_specifier(node);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_angle, x.members, x.right_angle, true, false, false),
                ])
            }
            SK::ClosureTypeSpecifier => {
                let x = sf::closure_type_specifier(node);
                cat(vec![
                    self.t(x.outer_left_paren),
                    self.t(x.readonly_keyword),
                    when_present(x.readonly_keyword, space),
                    self.t(x.function_keyword),
                    self.t(x.type_parameters),
                    self.t(x.inner_left_paren),
                    when_present(x.parameter_list, split),
                    self.transform_fn_decl_args(x.parameter_list, x.inner_right_paren),
                    self.t(x.contexts),
                    self.t(x.colon),
                    when_present(x.colon, space),
                    self.t(x.readonly_return),
                    when_present(x.readonly_return, space),
                    self.t(x.return_type),
                    self.t(x.outer_right_paren),
                ])
            }
            SK::ClosureParameterTypeSpecifier => {
                let x = sf::closure_parameter_type_specifier(node);
                cat(vec![
                    self.t(x.optional),
                    when_present(x.optional, space),
                    self.t(x.call_convention),
                    when_present(x.call_convention, space),
                    self.t(x.named),
                    when_present(x.named, space),
                    self.t(x.readonly),
                    when_present(x.readonly, space),
                    self.t(x.pre_ellipsis),
                    self.t(x.type_),
                    when_present(x.name, space),
                    self.t(x.name),
                    self.t(x.ellipsis),
                ])
            }
            SK::TupleOrUnionOrIntersectionElementTypeSpecifier => {
                let x = sf::tuple_or_union_or_intersection_element_type_specifier(node);
                cat(vec![
                    self.t(x.optional),
                    when_present(x.optional, space),
                    self.t(x.pre_ellipsis),
                    self.t(x.type_),
                    self.t(x.ellipsis),
                ])
            }
            SK::ClassPtrTypeSpecifier | SK::ClassnameTypeSpecifier => {
                // Both have (keyword, left_angle, type, trailing_comma,
                // right_angle).
                let c = &node.children;
                let (kw, left_a, class_type, trailing_comma, right_a) = (&*c[0], &*c[1], &*c[2], &*c[3], &*c[4]);
                cat(vec![
                    self.t(kw),
                    self.transform_braced_item_with_trailer(left_a, class_type, trailing_comma, right_a),
                ])
            }
            SK::FieldSpecifier => {
                let x = sf::field_specifier(node);
                cat(vec![self.t(x.question), self.transform_mapish_entry(x.name, x.arrow, x.type_)])
            }
            SK::AbsentFieldSpecifier => {
                let x = sf::absent_field_specifier(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.name)])
            }
            SK::FieldInitializer => {
                let x = sf::field_initializer(node);
                self.transform_mapish_entry(x.name, x.arrow, x.value)
            }
            SK::ShapeTypeSpecifier => {
                let x = sf::shape_type_specifier(node);
                let has_ellipsis = !(x.ellipsis.is_missing() && x.ellipsis_type.is_missing());
                let trailing_item = if has_ellipsis {
                    Some(cat(vec![self.t(x.ellipsis_type), self.t(x.ellipsis)]))
                } else {
                    None
                };
                self.transform_container_literal(
                    x.keyword,
                    x.left_paren,
                    x.fields,
                    x.right_paren,
                    false,
                    Some(!has_ellipsis),
                    None,
                    trailing_item,
                )
            }
            SK::ShapeExpression => {
                let x = sf::shape_expression(node);
                let fields_owned;
                let fields = if x.ellipsis.is_missing() {
                    x.fields
                } else {
                    let missing_separator = Rc::new(Node::make_missing());
                    let ellipsis_item = Rc::new(Node::make_list_item(rc(x.ellipsis), missing_separator));
                    let mut items: Vec<Rc<Node<'a>>> = x.fields.children.clone();
                    items.push(ellipsis_item);
                    fields_owned = Node::make_list(items);
                    &fields_owned
                };
                self.transform_container_literal(
                    x.keyword,
                    x.left_paren,
                    fields,
                    x.right_paren,
                    false,
                    Some(x.ellipsis.is_missing()),
                    None,
                    None,
                )
            }
            SK::TupleExpression => {
                let x = sf::tuple_expression(node);
                let items_owned;
                let items = if x.ellipsis.is_missing() {
                    x.items
                } else {
                    let missing_separator = Rc::new(Node::make_missing());
                    let ellipsis_item = Rc::new(Node::make_list_item(rc(x.ellipsis), missing_separator));
                    let mut items: Vec<Rc<Node<'a>>> = x.items.children.clone();
                    items.push(ellipsis_item);
                    items_owned = Node::make_list(items);
                    &items_owned
                };
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_paren, items, x.right_paren, x.ellipsis.is_missing(), false, false),
                ])
            }
            SK::TypeArguments => {
                let x = sf::type_arguments(node);
                self.transform_argish(x.left_angle, x.types, x.right_angle, true, false, false)
            }
            SK::TypeParameters => {
                let x = sf::type_parameters(node);
                self.transform_argish(x.left_angle, x.parameters, x.right_angle, true, false, false)
            }
            SK::TupleTypeSpecifier => {
                let x = sf::tuple_type_specifier(node);
                self.transform_argish(x.left_paren, x.types, x.right_paren, true, false, false)
            }
            SK::UnionTypeSpecifier | SK::IntersectionTypeSpecifier => {
                // Both have (left_paren, types, right_paren).
                let c = &node.children;
                let (left_p, types, right_p) = (&*c[0], &*c[1], &*c[2]);
                let elem = |n: &Node<'a>| match n.kind {
                    SK::ListItem => {
                        let li = sf::list_item(n);
                        cat(vec![
                            self.t(li.item),
                            when_present(li.separator, space),
                            self.t(li.separator),
                        ])
                    }
                    _ => self.t(n),
                };
                self.delimited_nest(left_p, right_p, vec![self.handle_possible_list(types, ListOpts {
                    after_each: Some(&|is_last| if is_last { Split } else { space_split() }),
                    handle_element: Some(&elem),
                    ..Default::default()
                })], true, false)
            }
            SK::TupleTypeExplicitSpecifier => {
                let x = sf::tuple_type_explicit_specifier(node);
                cat(vec![
                    self.t(x.keyword),
                    self.transform_argish(x.left_angle, x.types, x.right_angle, true, false, false),
                ])
            }
            SK::PrefixedCodeExpression => {
                let x = sf::prefixed_code_expression(node);
                match x.body.kind {
                    SK::CompoundStatement => {
                        let c = sf::compound_statement(x.body);
                        cat(vec![
                            self.t(x.prefix),
                            self.t(x.left_backtick),
                            self.handle_compound_statement(c.left_brace, c.statements, c.right_brace, true, false),
                            self.t(x.right_backtick),
                        ])
                    }
                    _ => cat(vec![
                        self.t(x.prefix),
                        self.transform_braced_item(x.left_backtick, x.body, x.right_backtick),
                    ]),
                }
            }
            SK::DecoratedExpression => {
                let x = sf::decorated_expression(node);
                cat(vec![
                    self.t(x.decorator),
                    match x.decorator.token_kind() {
                        Some(TK::Inout) => Space,
                        _ => Nothing,
                    },
                    self.t(x.expression),
                ])
            }
            SK::NamedArgument => {
                let x = sf::named_argument(node);
                cat(vec![self.t(x.name), self.t(x.equal), self.t(x.expression)])
            }
            SK::ErrorSyntax => raise(Exn::InvalidSyntax),
            SK::EnumClassDeclaration => {
                let x = sf::enum_class_declaration(node);
                let after_each_ancestor = |is_last: bool| if is_last { Nothing } else { space_split() };
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.enum_keyword),
                    Space,
                    self.t(x.class_keyword),
                    Space,
                    self.t(x.name),
                    self.t(x.colon),
                    Space,
                    SplitWith(Cost::Base),
                    Nest(vec![Space, self.t(x.base), Space]),
                    when_present(x.extends, || {
                        Nest(vec![
                            Space,
                            Split,
                            self.t(x.extends),
                            rule(
                                PARENTAL,
                                Nest(vec![Span(vec![
                                    Space,
                                    if list_length(x.extends_list) == 1 { SplitWith(Cost::Base) } else { Split },
                                    Nest(vec![self.handle_possible_list(x.extends_list, ListOpts {
                                        after_each: Some(&after_each_ancestor),
                                        ..Default::default()
                                    })]),
                                ])]),
                            ),
                        ])
                    }),
                    Space,
                    self.braced_block_nest(x.left_brace, x.right_brace, vec![
                        self.handle_possible_list(x.elements, ListOpts::default()),
                    ], true),
                    Newline,
                ])
            }
            SK::EnumClassEnumerator => {
                let x = sf::enum_class_enumerator(node);
                cat(vec![
                    self.handle_possible_list(x.modifiers, ListOpts {
                        after_each: Some(&|_| Space),
                        ..Default::default()
                    }),
                    self.t(x.type_),
                    when_present(x.type_, space),
                    self.t(x.name),
                    self.t(x.initializer),
                    self.t(x.semicolon),
                    Newline,
                ])
            }
            SK::EnumClassLabelExpression => self.transform_simple(node),
            SK::ModuleDeclaration => {
                let x = sf::module_declaration(node);
                cat(vec![
                    self.t(x.attribute_spec),
                    when_present(x.attribute_spec, newline),
                    self.t(x.new_keyword),
                    Space,
                    self.t(x.module_keyword),
                    Space,
                    self.t(x.name),
                    Space,
                    self.braced_block_nest(x.left_brace, x.right_brace, vec![], true),
                    Newline,
                ])
            }
            SK::ModuleMembershipDeclaration => {
                let x = sf::module_membership_declaration(node);
                cat(vec![self.t(x.module_keyword), Space, self.t(x.name), self.t(x.semicolon), Newline])
            }
            SK::PackageExpression => {
                let x = sf::package_expression(node);
                cat(vec![self.t(x.keyword), Space, self.t(x.name)])
            }
        }
    }

    fn transform_xhp_expression(&self, node: &Node<'a>) -> Doc<'a> {
        let x = sf::xhp_expression(node);
        let (xhp_open, body, close) = (x.open, x.body, x.close);
        let handle_xhp_body = |body: &Node<'a>| -> Doc<'a> {
            match body.kind {
                SK::Missing => when_present(close, split),
                SK::SyntaxList => {
                    // Trivia is lexed differently within an XHP body because
                    // whitespace is semantically significant in an XHP body
                    // when it is adjacent to an XHPBody token. To deal with
                    // this, we keep track of whether the last token we
                    // transformed was one that trailing trivia is scanned
                    // for. If it wasn't, we handle the next token's leading
                    // trivia list using transform_xhp_leading_trivia, which
                    // treats all trivia up to the first newline as trailing
                    // trivia.
                    let mut prev_token_was_xhpbody = false;
                    let mut transformed_body = vec![];
                    for node in &body.children {
                        let node_is_xhpbody = node.token_kind() == Some(TK::XHPBody);
                        // Here, we preserve newlines after XHPBody tokens and
                        // don't otherwise add splits between them. This means
                        // that we don't reflow paragraphs in XHP to fit in the
                        // desired line length.
                        let preserve_xhpbody_whitespace = |trivia: &[Trivia<'a>]| {
                            if node_is_xhpbody {
                                if has_newline_s(trivia) {
                                    Newline
                                } else if has_whitespace_s(trivia) {
                                    Space
                                } else {
                                    Nothing
                                }
                            } else {
                                Nothing
                            }
                        };
                        let (leading, node) = node.remove_leading_trivia();
                        let trailing = node.trailing_trivia();
                        let leading_whitespace = cat(vec![
                            // Whitespace in an XHP body is *only* significant
                            // when adjacent to an XHPBody token, so we are free
                            // to add splits between other nodes (like
                            // XHPExpressions and BracedExpressions).
                            if !prev_token_was_xhpbody && !node_is_xhpbody {
                                Split
                            } else {
                                Nothing
                            },
                            // If the previous token was an XHPBody token, the
                            // lexer will have scanned trailing trivia for it,
                            // so we can handle the leading trivia for this node
                            // normally. Otherwise, handle the trivia up to the
                            // first newline as trailing trivia.
                            if prev_token_was_xhpbody {
                                transform_leading_trivia_s(&leading)
                            } else {
                                transform_xhp_leading_trivia(&refs(&leading))
                            },
                        ]);
                        prev_token_was_xhpbody = node_is_xhpbody;
                        transformed_body.push(cat(vec![
                            leading_whitespace,
                            preserve_xhpbody_whitespace(&leading),
                            self.t(&node),
                            preserve_xhpbody_whitespace(trailing),
                        ]));
                    }
                    cat(vec![
                        Concat(transformed_body),
                        if prev_token_was_xhpbody {
                            Nothing
                        } else if has_newline_s(body.leading_trivia()) {
                            // Don't collapse XHPExpressions onto a single line
                            // if they were intentionally split across multiple
                            // lines in the original source.
                            Newline
                        } else {
                            Split
                        },
                    ])
                }
                _ => failwith("Expected SyntaxList"),
            }
        };
        Doc::WithOverridingParentalRule(Box::new(cat(vec![
            self.t(xhp_open),
            Nest(vec![handle_xhp_body(body)]),
            when_present(close, || {
                let (leading, close) = close.remove_leading_trivia();
                cat(vec![
                    // Ignore extra newlines by treating this as trailing trivia
                    ignore_trailing_invisibles(&refs(&leading)),
                    self.t(&close),
                ])
            }),
        ])))
    }

    fn transform_simple(&self, node: &Node<'a>) -> Doc<'a> {
        Concat(node.children.iter().map(|c| self.t(c)).collect())
    }

    fn transform_simple_statement(&self, node: &Node<'a>) -> Doc<'a> {
        let mut docs: Vec<Doc<'a>> = node.children.iter().map(|c| self.t(c)).collect();
        docs.push(Newline);
        Concat(docs)
    }

    fn braced_block_nest(&self, open_b: &Node<'a>, close_b: &Node<'a>, nodes: Vec<Doc<'a>>, allow_collapse: bool) -> Doc<'a> {
        let nodes = Concat(nodes);
        let collapse = allow_collapse
            && !nodes.has_printable_content()
            && match open_b.kind {
                SK::Token(_) => open_b
                    .token
                    .as_ref()
                    .unwrap()
                    .trailing
                    .iter()
                    .all(|t| !is_trivia_kind_end_of_line(t.kind)),
                SK::Missing => true,
                _ => false,
            };
        if collapse {
            cat(vec![self.t(open_b), self.t(close_b)])
        } else {
            // Remove the closing brace's leading trivia and handle it inside
            // the BlockNest, so that comments will be indented correctly.
            let (leading, close_b) = close_b.remove_leading_trivia();
            cat(vec![
                self.t(open_b),
                Newline,
                BlockNest(vec![nodes, transform_leading_trivia_s(&leading), Newline]),
                self.t(&close_b),
            ])
        }
    }

    fn delimited_nest(
        &self,
        left_delim: &Node<'a>,
        right_delim: &Node<'a>,
        nodes: Vec<Doc<'a>>,
        split_when_children_split: bool,
        force_newlines: bool,
    ) -> Doc<'a> {
        let kind = if force_newlines {
            RuleKind::Always
        } else if split_when_children_split {
            PARENTAL
        } else {
            SIMPLE_BASE
        };
        Span(vec![self.t(left_delim), rule(kind, self.nest(right_delim, nodes, false))])
    }

    fn nest(&self, right_delim: &Node<'a>, nodes: Vec<Doc<'a>>, spaces: bool) -> Doc<'a> {
        // Remove the right delimiter's leading trivia and handle it inside the
        // Nest, so that comments will be indented correctly.
        let (leading, right_delim) = right_delim.remove_leading_trivia();
        let nested_contents = Nest(vec![Concat(nodes), transform_leading_trivia_s(&leading)]);
        let content_present = nested_contents.has_printable_content();
        let maybe_split = match (content_present, spaces) {
            (false, _) => Nothing,
            (true, false) => Split,
            (true, true) => space_split(),
        };
        cat(vec![maybe_split.clone(), nested_contents, maybe_split, self.t(&right_delim)])
    }

    fn handle_attribute_spec(&self, node: &Node<'a>) -> Doc<'a> {
        match node.kind {
            SK::OldAttributeSpecification => {
                let x = sf::old_attribute_specification(node);
                self.transform_argish(x.left_double_angle, x.attributes, x.right_double_angle, true, false, false)
            }
            SK::Missing => Nothing,
            _ => failwith("Attribute specification expected"),
        }
    }

    fn handle_lambda_body(&self, node: &Node<'a>) -> Doc<'a> {
        match node.kind {
            SK::CompoundStatement => {
                let x = sf::compound_statement(node);
                self.handle_compound_statement(x.left_brace, x.statements, x.right_brace, true, true)
            }
            SK::XHPExpression => rule(PARENTAL, cat(vec![Space, Split, Nest(vec![self.t(node)])])),
            _ => cat(vec![Space, SplitWith(Cost::Base), Nest(vec![self.t(node)])]),
        }
    }

    fn handle_possible_compound_statement(&self, node: &Node<'a>, space: bool, allow_collapse: bool) -> Doc<'a> {
        match node.kind {
            SK::CompoundStatement => {
                let x = sf::compound_statement(node);
                cat(vec![
                    self.handle_compound_statement(x.left_brace, x.statements, x.right_brace, allow_collapse, true),
                    if space { Space } else { Nothing },
                ])
            }
            SK::Token(_) => self.t(node),
            _ => cat(vec![Newline, BlockNest(vec![self.t(node)])]),
        }
    }

    fn handle_compound_statement(
        &self,
        left_b: &Node<'a>,
        statements: &Node<'a>,
        right_b: &Node<'a>,
        allow_collapse: bool,
        prepend_space: bool,
    ) -> Doc<'a> {
        cat(vec![
            if prepend_space { Space } else { Nothing },
            self.braced_block_nest(left_b, right_b, vec![
                self.handle_possible_list(statements, ListOpts::default()),
            ], allow_collapse),
        ])
    }

    /// Special-case handling for lists of declarators, where we want the
    /// splits between declarators to break if their children break, but we
    /// want a single declarator to stay joined with the line preceding it if
    /// it fits, even when its children break.
    fn handle_declarator_list(&self, declarators: &Node<'a>) -> Doc<'a> {
        match declarators.kind {
            SK::Missing => Nothing,
            SK::SyntaxList if declarators.children.len() == 1 => {
                Nest(vec![
                    Space,
                    // Use an independent split, so we don't break just because
                    // a line break occurs in the declarator.
                    SplitWith(Cost::Base),
                    self.t(&declarators.children[0]),
                ])
            }
            SK::SyntaxList => {
                // Use Rule.Parental to break each declarator onto its own line
                // if any line break occurs in a declarator, or if they can't
                // all fit onto one line.
                rule(
                    PARENTAL,
                    Nest(
                        declarators
                            .children
                            .iter()
                            .map(|d| cat(vec![Space, Split, self.t(d)]))
                            .collect(),
                    ),
                )
            }
            _ => failwith("SyntaxList expected"),
        }
    }

    fn handle_list(&self, list: &[&Node<'a>], opts: ListOpts<'_, 'a>) -> Doc<'a> {
        let default_elem = |n: &Node<'a>| self.t(n);
        let handle_element: Elem<'_, 'a> = opts.handle_element.unwrap_or(&default_elem);
        let handle_last: Elem<'_, 'a> = opts.handle_last.unwrap_or(handle_element);
        let mut docs = Vec::with_capacity(list.len() * 3);
        for (i, hd) in list.iter().enumerate() {
            docs.push(opts.before_each.map_or(Nothing, |f| f()));
            if i + 1 == list.len() {
                docs.push(handle_last(hd));
                docs.push(opts.after_each.map_or(Nothing, |f| f(true)));
            } else {
                docs.push(handle_element(hd));
                docs.push(opts.after_each.map_or(Nothing, |f| f(false)));
            }
        }
        if docs.is_empty() { Nothing } else { Concat(docs) }
    }

    fn handle_possible_list(&self, node: &Node<'a>, opts: ListOpts<'_, 'a>) -> Doc<'a> {
        match node.kind {
            SK::Missing => Nothing,
            SK::SyntaxList => {
                let l: Vec<&Node<'a>> = node.children.iter().map(|c| &**c).collect();
                self.handle_list(&l, opts)
            }
            _ => self.handle_list(&[node], opts),
        }
    }

    fn handle_xhp_open_right_angle_token(&self, attrs: &Node<'a>, node: &Node<'a>) -> Doc<'a> {
        match &node.token {
            Some(token) => cat(vec![
                if token.text == b"/>" {
                    cat(vec![Space, when_present(attrs, split)])
                } else {
                    Nothing
                },
                self.t(node),
            ]),
            None => failwith("expected xhp_open right_angle token"),
        }
    }

    fn handle_possible_chaining(&self, node: &Node<'a>) -> Doc<'a> {
        type Link<'n, 'a> = (
            &'n Node<'a>,
            &'n Node<'a>,
            Option<&'n Node<'a>>,
            Option<(&'n Node<'a>, &'n Node<'a>, &'n Node<'a>)>,
        );
        fn member_selection_parts<'n, 'a>(n: &'n Node<'a>) -> Option<(&'n Node<'a>, &'n Node<'a>, &'n Node<'a>)> {
            match n.kind {
                SK::MemberSelectionExpression => {
                    let x = sf::member_selection_expression(n);
                    Some((x.object, x.operator, x.name))
                }
                SK::SafeMemberSelectionExpression => {
                    let x = sf::safe_member_selection_expression(n);
                    Some((x.object, x.operator, x.name))
                }
                _ => None,
            }
        }
        // Flatten nested member selection expressions into the first receiver
        // and a list of member selections. E.g., transform $x->a->b->c into
        // ($x, [->a; ->b; ->c])
        fn handle_chaining<'n, 'a>(node: &'n Node<'a>, acc: &mut Vec<Link<'n, 'a>>) -> &'n Node<'a> {
            match node.kind {
                SK::FunctionCallExpression => {
                    let x = sf::function_call_expression(node);
                    match member_selection_parts(x.receiver) {
                        Some((obj, arrow, member)) => {
                            let targs = if x.type_args.is_missing() { None } else { Some(x.type_args) };
                            let first = handle_chaining(obj, acc);
                            acc.push((arrow, member, targs, Some((x.left_paren, x.argument_list, x.right_paren))));
                            first
                        }
                        None => node,
                    }
                }
                SK::MemberSelectionExpression | SK::SafeMemberSelectionExpression => {
                    let (obj, arrow, member) = member_selection_parts(node).unwrap();
                    let first = handle_chaining(obj, acc);
                    acc.push((arrow, member, None, None));
                    first
                }
                _ => node,
            }
        }
        // It's easy to end up with an infinite loop by passing an unexpected
        // node kind here, so confirm that we have an expected kind in hand.
        match node.kind {
            SK::FunctionCallExpression | SK::MemberSelectionExpression | SK::SafeMemberSelectionExpression => {}
            kind => failwith(&format!("Unexpected SyntaxKind in handle_possible_chaining: {:?}", kind)),
        }
        let mut chain_list = vec![];
        let first_receiver = handle_chaining(node, &mut chain_list);
        let transform_chain = |(arrow, member, targs, argish): &Link<'_, 'a>| {
            cat(vec![
                self.t(arrow),
                self.t(member),
                targs.map_or(Nothing, |t| self.t(t)),
                argish.map_or(Nothing, |(lp, args, rp)| self.transform_argish(lp, args, rp, true, false, false)),
            ])
        };
        // The actual transform for function call expressions (the default
        // transform just calls into [handle_possible_chaining]).
        let transform_first_receiver = |node: &Node<'a>| match node.kind {
            SK::FunctionCallExpression => {
                let x = sf::function_call_expression(node);
                cat(vec![
                    self.t(x.receiver),
                    self.t(x.type_args),
                    self.transform_argish(x.left_paren, x.argument_list, x.right_paren, true, false, false),
                ])
            }
            SK::MemberSelectionExpression | SK::SafeMemberSelectionExpression => failwith(
                "Should not be possible for a member selection expression to be considered first_receiver",
            ),
            _ => self.t(node),
        };
        let first_receiver_has_trailing_newline = node_has_trailing_newline(first_receiver);
        match chain_list.as_slice() {
            [] => transform_first_receiver(first_receiver),
            [hd] => cat(vec![
                Span(vec![transform_first_receiver(first_receiver)]),
                if first_receiver_has_trailing_newline {
                    Newline
                } else {
                    SplitWith(Cost::High)
                },
                Nest(vec![transform_chain(hd)]),
            ]),
            [hd, tl @ ..] => {
                let transformed_hd = transform_chain(hd);
                let tl: Vec<Doc<'a>> = tl.iter().map(transform_chain).collect();
                let rule_type = {
                    let trailing = match hd {
                        (_, trailing, None, None) => *trailing,
                        (_, _, Some(trailing), None) => *trailing,
                        (_, _, _, Some((_, _, trailing))) => *trailing,
                    };
                    if node_has_trailing_newline(trailing) {
                        RuleKind::Always
                    } else if first_receiver_has_trailing_newline {
                        PARENTAL
                    } else {
                        // If we have a chain where only the final item
                        // contains internal splits, use a Simple rule instead
                        // of a Parental one.
                        let rev_tl_except_last = &tl[..tl.len() - 1];
                        if transformed_hd.has_split() || rev_tl_except_last.iter().any(|d| d.has_split()) {
                            PARENTAL
                        } else {
                            RuleKind::Simple(Cost::NoCost)
                        }
                    }
                };
                Span(vec![lazy_rule(
                    rule_type,
                    cat(vec![
                        transform_first_receiver(first_receiver),
                        if first_receiver_has_trailing_newline {
                            Newline
                        } else {
                            SplitWith(Cost::Base)
                        },
                    ]),
                    cat(vec![
                        // This needs to be nested separately due to the above
                        // SplitWith
                        Nest(vec![transformed_hd]),
                        Nest(tl.into_iter().map(|x| cat(vec![Split, x])).collect()),
                    ]),
                )])
            }
        }
    }

    fn transform_fn_decl_name(
        &self,
        modifiers: &Node<'a>,
        kw: &Node<'a>,
        name: &Node<'a>,
        type_params: &Node<'a>,
        leftp: &Node<'a>,
    ) -> Vec<Doc<'a>> {
        let mods = self.handle_possible_list(modifiers, ListOpts {
            after_each: Some(&|_| Space),
            ..Default::default()
        });
        vec![mods, self.t(kw), Space, self.t(name), self.t(type_params), self.t(leftp), Split]
    }

    fn transform_fn_decl_args(&self, params: &Node<'a>, rightp: &Node<'a>) -> Doc<'a> {
        // It is a syntax error to follow a variadic parameter with a trailing
        // comma, so suppress trailing commas in that case.
        let allow_trailing = match params.kind {
            SK::SyntaxList => {
                let last = params.children.last().unwrap();
                let last_param = match last.kind {
                    SK::ListItem => sf::list_item(last).item,
                    _ => failwith("Expected ListItem"),
                };
                match last_param.kind {
                    SK::ParameterDeclaration
                        if sf::parameter_declaration(last_param).ellipsis.token_kind() == Some(TK::DotDotDot) =>
                    {
                        false
                    }
                    SK::ClosureParameterTypeSpecifier
                        if sf::closure_parameter_type_specifier(last_param).ellipsis.token_kind()
                            == Some(TK::DotDotDot) =>
                    {
                        false
                    }
                    _ => true,
                }
            }
            _ => true,
        };
        rule(PARENTAL, cat(vec![self.transform_possible_comma_list(params, rightp, allow_trailing)]))
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_argish_with_return_type(
        &self,
        left_p: &Node<'a>,
        params: &Node<'a>,
        right_p: &Node<'a>,
        ctx_list: &Node<'a>,
        colon: &Node<'a>,
        readonly_ret: &Node<'a>,
        ret_type: &Node<'a>,
    ) -> Doc<'a> {
        cat(vec![
            self.t(left_p),
            when_present(params, split),
            self.transform_fn_decl_args(params, right_p),
            self.t(ctx_list),
            self.t(colon),
            when_present(colon, space),
            self.t(readonly_ret),
            when_present(readonly_ret, space),
            self.t(ret_type),
        ])
    }

    fn transform_argish(
        &self,
        left_p: &Node<'a>,
        arg_list: &Node<'a>,
        right_p: &Node<'a>,
        allow_trailing: bool,
        force_newlines: bool,
        spaces: bool,
    ) -> Doc<'a> {
        // It is a syntax error to follow a splat argument with a trailing
        // comma, so suppress trailing commas in that case.
        let allow_trailing = match arg_list.kind {
            SK::SyntaxList => {
                let last = arg_list.children.last().unwrap();
                let last_arg = match last.kind {
                    SK::ListItem => sf::list_item(last).item,
                    _ => failwith("Expected ListItem"),
                };
                match last_arg.kind {
                    SK::DecoratedExpression
                        if sf::decorated_expression(last_arg).decorator.token_kind() == Some(TK::DotDotDot) =>
                    {
                        false
                    }
                    _ => allow_trailing,
                }
            }
            _ => allow_trailing,
        };
        // When the last argument breaks across multiple lines, we want to
        // allow the arg list rule to stay unbroken even though the last
        // argument contains splits that may be broken on.
        let split_when_children_split = if spaces {
            true
        } else {
            fn unwrap_list_item<'n, 'a>(x: &'n Node<'a>) -> &'n Node<'a> {
                if x.kind == SK::ListItem { sf::list_item(x).item } else { x }
            }
            let is_doc_string_literal = |x: &Node<'a>| {
                let x = unwrap_list_item(x);
                match x.kind {
                    SK::LiteralExpression => {
                        let literal_expression = sf::literal_expression(x).expression;
                        match literal_expression.kind {
                            SK::Token(k) => matches!(k, TK::HeredocStringLiteral | TK::NowdocStringLiteral),
                            SK::SyntaxList => match literal_expression.children.first() {
                                Some(first) => first.token_kind() == Some(TK::HeredocStringLiteralHead),
                                None => false,
                            },
                            _ => false,
                        }
                    }
                    _ => false,
                }
            };
            let leading_trivia_is_all_whitespace =
                |x: &Node<'a>| x.leading_trivia().iter().all(|t| t.kind == TriviaKind::WhiteSpace);
            match arg_list.kind {
                SK::SyntaxList if arg_list.children.is_empty() => true,
                SK::SyntaxList if arg_list.children.len() == 1 => {
                    let x = &*arg_list.children[0];
                    let has_surrounding_whitespace = !(left_p.trailing_trivia().is_empty()
                        && (arg_list.trailing_trivia().is_empty()
                            || self.env.version_gte(3)
                                && is_doc_string_literal(x)
                                && leading_trivia_is_all_whitespace(right_p)));
                    if has_surrounding_whitespace {
                        true
                    } else {
                        looks_bad_in_non_parental_braces(x)
                    }
                }
                SK::SyntaxList => {
                    let items = &arg_list.children;
                    let last = &**items.last().unwrap();
                    let has_surrounding_whitespace = !(last.leading_trivia().is_empty()
                        && (arg_list.trailing_trivia().is_empty()
                            || self.env.version_gte(3)
                                && is_doc_string_literal(last)
                                && leading_trivia_is_all_whitespace(right_p)));
                    if has_surrounding_whitespace {
                        true
                    } else {
                        // When there are multiple arguments, opt into this
                        // behavior only when we have no splits in any of the
                        // arguments except the last.
                        let rest = &items[..items.len() - 1];
                        let prev_args_may_split = rest.iter().any(|a| self.t(a).has_split());
                        if prev_args_may_split {
                            true
                        } else {
                            looks_bad_in_non_parental_braces(last)
                        }
                    }
                }
                _ => true,
            }
        };
        self.delimited_nest(
            left_p,
            right_p,
            vec![self.transform_arg_list(arg_list, allow_trailing)],
            split_when_children_split,
            force_newlines,
        )
    }

    fn transform_braced_item(&self, left_p: &Node<'a>, item: &Node<'a>, right_p: &Node<'a>) -> Doc<'a> {
        let has_no_surrounding_trivia = left_p.trailing_trivia().is_empty()
            && item.leading_trivia().is_empty()
            && item.trailing_trivia().is_empty()
            && right_p.leading_trivia().is_empty();
        if has_no_surrounding_trivia && !looks_bad_in_non_parental_braces(item) {
            Concat(vec![self.t(left_p), self.t(item), self.t(right_p)])
        } else {
            self.delimited_nest(left_p, right_p, vec![self.t(item)], true, false)
        }
    }

    fn transform_argish_item(&self, x: &Node<'a>) -> Doc<'a> {
        match x.kind {
            SK::ListItem => {
                let li = sf::list_item(x);
                cat(vec![self.transform_argish_item(li.item), self.t(li.separator)])
            }
            SK::BinaryExpression if !is_concat(sf::binary_expression(x).operator) => {
                let b = sf::binary_expression(x);
                self.transform_binary_expression(true, b.left_operand, b.operator, b.right_operand)
            }
            _ => self.t(x),
        }
    }

    fn transform_trailing_comma(&self, item: &Node<'a>, comma: &Node<'a>, allow_trailing: bool) -> Doc<'a> {
        // PHP does not permit trailing commas in function calls. Rather than
        // try to account for where PHP's parser permits trailing commas, we
        // just never add them in PHP files.
        let allow_trailing = allow_trailing && self.env.add_trailing_commas;
        match comma.kind {
            SK::Token(_) => {
                let tok = comma.token.as_ref().unwrap();
                cat(vec![
                    self.transform_argish_item(item),
                    transform_leading_trivia_s(&tok.leading),
                    if allow_trailing { TrailingComma(true) } else { Nothing },
                    Ignore(tok.width()),
                    transform_trailing_trivia_s(&tok.trailing),
                ])
            }
            SK::Missing => {
                let (item, item_trailing) = item.remove_trailing_trivia();
                cat(vec![
                    self.transform_argish_item(&item),
                    if allow_trailing { TrailingComma(false) } else { Nothing },
                    transform_trailing_trivia_s(&item_trailing),
                ])
            }
            _ => failwith("Expected Token"),
        }
    }

    fn transform_braced_item_with_trailer(
        &self,
        left_p: &Node<'a>,
        item: &Node<'a>,
        comma: &Node<'a>,
        right_p: &Node<'a>,
    ) -> Doc<'a> {
        let has_no_surrounding_trivia = left_p.trailing_trivia().is_empty()
            && item.leading_trivia().is_empty()
            && item.trailing_trivia().is_empty()
            && comma.leading_trivia().is_empty()
            && comma.trailing_trivia().is_empty()
            && right_p.leading_trivia().is_empty();
        // TODO: turn allow_trailing:true when HHVM versions that don't support
        // trailing commas in all these places reach end-of-life.
        let item_and_comma = self.transform_trailing_comma(item, comma, false);
        if has_no_surrounding_trivia && !looks_bad_in_non_parental_braces(item) {
            cat(vec![self.t(left_p), item_and_comma, self.t(right_p)])
        } else {
            self.delimited_nest(left_p, right_p, vec![item_and_comma], true, false)
        }
    }

    fn transform_arg_list(&self, items: &Node<'a>, allow_trailing: bool) -> Doc<'a> {
        let last = |n: &Node<'a>| self.transform_last_arg(n, allow_trailing);
        let elem = |n: &Node<'a>| self.transform_argish_item(n);
        self.handle_possible_list(items, ListOpts {
            after_each: Some(&after_each_argument),
            handle_last: Some(&last),
            handle_element: Some(&elem),
            ..Default::default()
        })
    }

    fn transform_possible_comma_list(&self, items: &Node<'a>, right_p: &Node<'a>, allow_trailing: bool) -> Doc<'a> {
        self.nest(right_p, vec![self.transform_arg_list(items, allow_trailing)], false)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_container_literal(
        &self,
        kw: &Node<'a>,
        left_p: &Node<'a>,
        members: &Node<'a>,
        right_p: &Node<'a>,
        space: bool,
        allow_trailing: Option<bool>,
        explicit_type: Option<&Node<'a>>,
        trailing_item: Option<Doc<'a>>,
    ) -> Doc<'a> {
        let force_newlines = node_has_trailing_newline(left_p)
            && !(members.is_missing() && trailing_item.is_none());
        let ty = match explicit_type {
            Some(ex_ty) => self.t(ex_ty),
            None => Nothing,
        };
        cat(vec![
            self.t(kw),
            ty,
            if space { Space } else { Nothing },
            match trailing_item {
                None => self.transform_argish(
                    left_p,
                    members,
                    right_p,
                    allow_trailing.unwrap_or(true),
                    force_newlines,
                    false,
                ),
                Some(trailing_item) => {
                    let elem = |n: &Node<'a>| self.transform_argish_item(n);
                    self.delimited_nest(left_p, right_p, vec![
                        self.handle_possible_list(members, ListOpts {
                            after_each: Some(&|_| space_split()),
                            handle_element: Some(&elem),
                            handle_last: Some(&elem),
                            ..Default::default()
                        }),
                        trailing_item,
                    ], true, force_newlines)
                }
            },
        ])
    }

    fn transform_last_arg(&self, node: &Node<'a>, allow_trailing: bool) -> Doc<'a> {
        match node.kind {
            SK::ListItem => {
                let li = sf::list_item(node);
                self.transform_trailing_comma(li.item, li.separator, allow_trailing)
            }
            _ => failwith("Expected ListItem"),
        }
    }

    fn transform_mapish_entry(&self, key: &Node<'a>, arrow: &Node<'a>, value: &Node<'a>) -> Doc<'a> {
        cat(vec![
            self.t(key),
            Space,
            self.t(arrow),
            Space,
            SplitWith(Cost::Base),
            Nest(vec![self.t(value)]),
        ])
    }

    fn transform_keyword_expression_statement(&self, kw: &Node<'a>, expr: &Node<'a>, semi: &Node<'a>) -> Doc<'a> {
        cat(vec![
            self.t(kw),
            when_present(expr, || {
                cat(vec![
                    Space,
                    SplitWith(if self.env.version_gte(1) { Cost::Base } else { Cost::Moderate }),
                    Nest(vec![self.t(expr)]),
                ])
            }),
            self.t(semi),
            Newline,
        ])
    }

    fn transform_keyword_expr_list_statement(&self, kw: &Node<'a>, expr_list: &Node<'a>, semi: &Node<'a>) -> Doc<'a> {
        cat(vec![self.t(kw), self.handle_declarator_list(expr_list), self.t(semi), Newline])
    }

    fn transform_condition(&self, left_p: &Node<'a>, condition: &Node<'a>, right_p: &Node<'a>) -> Doc<'a> {
        cat(vec![
            self.t(left_p),
            Split,
            rule(PARENTAL, cat(vec![Nest(vec![self.t(condition)]), Split, self.t(right_p)])),
        ])
    }

    fn transform_binary_expression(
        &self,
        is_nested: bool,
        left: &Node<'a>,
        operator: &Node<'a>,
        right: &Node<'a>,
    ) -> Doc<'a> {
        let operator_has_surrounding_spaces = |op: &Node<'a>| !is_concat(op);
        // OCaml: `|>` and `|?>` (PipeOperator). Hakana: only `|>`.
        let is_pipe = |op: &Node<'a>| {
            if self.env.hakana_rules {
                op.token_kind() == Some(TK::BarGreaterThan)
            } else {
                matches!(get_operator_type(op), Operator::PipeOperator)
            }
        };
        let operator_is_leading = |op: &Node<'a>| is_pipe(op);
        let operator_preserves_newlines = |op: &Node<'a>| is_pipe(op);
        let operator_t = get_operator_type(operator);
        if operator_t.is_comparison() {
            lazy_rule(
                PARENTAL,
                cat(vec![self.t(left), Space, self.t(operator)]),
                cat(vec![Space, Split, Nest(vec![self.t(right)])]),
            )
        } else if operator_t.is_assignment() {
            cat(vec![
                self.t(left),
                Space,
                self.t(operator),
                Space,
                SplitWith(if self.env.version_gte(1) { Cost::Base } else { Cost::Moderate }),
                Nest(vec![self.t(right)]),
            ])
        } else {
            let penv = ParserEnv::default();
            let precedence = operator_t.precedence(&penv);
            fn flatten_expression<'a>(expr: Rc<Node<'a>>, precedence: usize, penv: &ParserEnv, out: &mut Vec<Rc<Node<'a>>>) {
                if expr.kind == SK::BinaryExpression {
                    let x = sf::binary_expression(&expr);
                    let op_precedence = get_operator_type(x.operator).precedence(penv);
                    if op_precedence == precedence {
                        let (l, o, r) = (expr.children[0].clone(), expr.children[1].clone(), expr.children[2].clone());
                        flatten_expression(l, precedence, penv, out);
                        out.push(o);
                        flatten_expression(r, precedence, penv, out);
                        return;
                    }
                }
                out.push(expr);
            }
            let transform_operand = |operand: &Node<'a>| match operand.kind {
                SK::BinaryExpression => {
                    let b = sf::binary_expression(operand);
                    self.transform_binary_expression(true, b.left_operand, b.operator, b.right_operand)
                }
                _ => self.t(operand),
            };
            let binary_expression = Rc::new(Node::make_binary_expression(rc(left), rc(operator), rc(right)));
            let mut binary_expression_syntax_list = vec![];
            flatten_expression(binary_expression, precedence, &penv, &mut binary_expression_syntax_list);
            let Some((hd, tl)) = binary_expression_syntax_list.split_first() else {
                failwith("Expected non empty list of binary expression pieces")
            };
            let mut last_operand: &Node<'a> = hd;
            let mut last_op: &Node<'a> = match tl.first() {
                Some(op) => op,
                None => failwith("hd"),
            };
            let mut expression = vec![];
            for (i, x) in tl.iter().enumerate() {
                if i % 2 == 0 {
                    let op: &Node<'a> = x;
                    last_op = op;
                    let op_has_spaces = operator_has_surrounding_spaces(op);
                    let op_is_leading = operator_is_leading(op);
                    let newline_before_op = operator_preserves_newlines(op) && node_has_trailing_newline(last_operand);
                    expression.push(cat(vec![
                        if newline_before_op {
                            Newline
                        } else if op_is_leading {
                            if op_has_spaces { space_split() } else { Split }
                        } else if op_has_spaces {
                            Space
                        } else {
                            Nothing
                        },
                        if is_concat(op) {
                            ConcatOperator(Box::new(self.t(op)))
                        } else {
                            self.t(op)
                        },
                    ]));
                } else {
                    let operand: &Node<'a> = x;
                    last_operand = x;
                    let op_has_spaces = operator_has_surrounding_spaces(last_op);
                    let op_is_leading = operator_is_leading(last_op);
                    expression.push(cat(vec![
                        if op_is_leading {
                            if op_has_spaces { Space } else { Nothing }
                        } else if op_has_spaces {
                            space_split()
                        } else {
                            Split
                        },
                        transform_operand(operand),
                    ]));
                }
            }
            cat(vec![lazy_rule(
                PARENTAL,
                transform_operand(hd),
                if is_nested {
                    Nest(expression)
                } else {
                    ConditionalNest(expression)
                },
            )])
        }
    }

    /// Check the leading trivia of the node's leading token. Treat the node's
    /// text as a multiline string if the leading trivia contains an ignore
    /// comment.
    fn transform_node_if_ignored(&self, node: &Node<'a>) -> Option<Doc<'a>> {
        let (leading_before, leading_including_and_after) = leading_ignore_comment(node.leading_trivia());
        if leading_including_and_after.is_empty() {
            return None;
        }
        let is_fixme = matches!(
            leading_including_and_after[0].kind,
            TriviaKind::FixMe | TriviaKind::Ignore | TriviaKind::IgnoreError
        );
        let leading_before: Vec<Trivia<'a>> = leading_before.to_vec();
        let node = node.replace_leading_trivia(leading_including_and_after.to_vec());
        let (node, trailing_trivia) = node.remove_trailing_trivia();
        let text: &'a [u8] = self.arena.alloc_slice_copy(&node.text());
        Some(cat(vec![
            transform_leading_trivia_s(&leading_before),
            // If we have a non-error-suppression comment here, then we want to
            // ensure that we don't join it up onto the preceding line. Since we
            // only scan leading trivia for hackfmt-ignore comments, and joining
            // the comment onto the preceding line would make it trailing
            // trivia, we would make the ignore comment useless if we joined it
            // with the preceding line (breaking idempotence of hackfmt).
            // Adding [Newline] here ensures a line break.
            //
            // Error-suppression comments are different--they are specially
            // handled by the lexer to ensure that they always appear in leading
            // trivia.
            if is_fixme { Nothing } else { Newline },
            make_string(text, node.width()),
            transform_trailing_trivia_s(&trailing_trivia),
            if has_newline_s(&trailing_trivia) { Newline } else { Nothing },
        ]))
    }

    fn transform_consequence(&self, node_body: &Node<'a>, node_newline: &Node<'a>) -> Doc<'a> {
        match node_body.kind {
            SK::CompoundStatement => self.handle_possible_compound_statement(node_body, true, false),
            _ => cat(vec![
                Space,
                if has_newline_s(node_newline.trailing_trivia()) {
                    cat(vec![Newline, Nest(vec![self.t(node_body)])])
                } else {
                    rule(PARENTAL, Nest(vec![Span(vec![Space, Split, self.t(node_body)])]))
                },
            ]),
        }
    }
}

fn when_present<'a>(node: &Node<'a>, f: impl FnOnce() -> Doc<'a>) -> Doc<'a> {
    match node.kind {
        SK::Missing => Nothing,
        _ => f(),
    }
}

fn rc<'a>(node: &Node<'a>) -> Rc<Node<'a>> {
    Rc::new(node.clone())
}
