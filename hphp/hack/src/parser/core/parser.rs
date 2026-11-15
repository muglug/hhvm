// Copyright (c) 2019, Facebook, Inc.
// All rights reserved.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the "hack" directory of this source tree.

use parser_core_types::source_text::SourceText;
use parser_core_types::syntax_error::SyntaxError;

use crate::declaration_parser::DeclarationParser;
use crate::lexer::Lexer;
use crate::parser_env::ParserEnv;
use crate::parser_trait::Context;
use crate::parser_trait::ParserTrait;
use crate::smart_constructors::NodeType;
use crate::smart_constructors::SmartConstructors;

pub struct Parser<'a, S>
where
    S: SmartConstructors,
    S::Output: NodeType,
{
    lexer: Lexer<'a, S::Factory>,
    errors: Vec<SyntaxError>,
    env: ParserEnv,
    sc: S,
}

impl<'a, S> Parser<'a, S>
where
    S: SmartConstructors,
    S::Output: NodeType,
{
    pub fn new(source: &SourceText<'a>, env: ParserEnv, mut sc: S) -> Self {
        let source = source.clone();
        Self {
            lexer: Lexer::make(&source, sc.token_factory_mut().clone()),
            errors: vec![],
            env,
            sc,
        }
    }

    pub fn into_parts(self) -> (Lexer<'a, S::Factory>, Vec<SyntaxError>, ParserEnv, S) {
        (self.lexer, self.errors, self.env, self.sc)
    }

    pub fn parse_header_only(
        env: ParserEnv,
        text: &'a SourceText<'a>,
        sc: S,
    ) -> Option<<S::Output as NodeType>::Output> {
        let (lexer, errors, env, sc) = Self::new(text, env, sc).into_parts();
        let mut decl_parser: DeclarationParser<'_, S> =
            DeclarationParser::make(lexer, env, Context::empty(), errors, sc);
        decl_parser
            .parse_leading_markup_section()
            .map(|r| r.extract())
    }

    pub fn parse_script(&mut self) -> <S::Output as NodeType>::Output {
        let mut decl_parser: DeclarationParser<'_, S> = DeclarationParser::make(
            self.lexer.clone(),
            self.env.clone(),
            Context::empty(),
            vec![],
            self.sc.clone(),
        );
        let root = decl_parser.parse_script().extract();
        let (lexer, _context, errors, sc) = decl_parser.into_parts();
        self.errors = errors;
        self.sc = sc;
        self.lexer = lexer;
        root
    }

    /// `parse_script` followed by `errors` and `into_sc_state`, for a parser
    /// that is not used afterwards: the lexer and the smart constructors move
    /// into the declaration parser instead of being cloned (a clone of smart
    /// constructors may share their state, which their first change would
    /// then copy).
    pub fn parse_script_into_errors_and_sc_state(
        self,
    ) -> (<S::Output as NodeType>::Output, Vec<SyntaxError>, S::State) {
        let mut decl_parser: DeclarationParser<'_, S> =
            DeclarationParser::make(self.lexer, self.env, Context::empty(), vec![], self.sc);
        let root = decl_parser.parse_script().extract();
        let (lexer, _context, mut errors, sc) = decl_parser.into_parts();
        // As `errors`: the lexer's errors, then the parser's, reversed.
        let mut res = lexer.errors().to_vec();
        res.append(&mut errors);
        res.reverse();
        (root, res, sc.into_state())
    }

    pub fn errors(&self) -> Vec<SyntaxError> {
        let mut res = vec![];
        res.extend_from_slice(self.lexer.errors());
        res.extend(self.errors.clone());
        res.reverse();
        res
    }

    pub fn sc_state(&mut self) -> &S::State {
        self.sc.state_mut()
    }

    pub fn into_sc_state(self) -> S::State {
        self.sc.into_state()
    }
}
