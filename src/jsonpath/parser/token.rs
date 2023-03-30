// Copyright 2023 Datafuse Labs.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use logos::Lexer;
use logos::Logos;
use strum_macros::EnumIter;

use crate::jsonpath::exception::ErrorCode;
use crate::jsonpath::exception::Range;
use crate::jsonpath::exception::Result;

pub use self::TokenKind::*;

#[derive(Clone, PartialEq, Eq)]
pub struct Token<'a> {
    pub source: &'a str,
    pub kind: TokenKind,
    pub span: Range,
}

impl<'a> Token<'a> {
    pub fn new_eoi(source: &'a str) -> Self {
        Token {
            source,
            kind: TokenKind::Eoi,
            span: (source.len()..source.len()).into(),
        }
    }

    pub fn text(&self) -> &'a str {
        &self.source[std::ops::Range::from(self.span)]
    }
}

impl<'a> std::fmt::Debug for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}({:?})", self.kind, self.span)
    }
}

pub struct Tokenizer<'a> {
    source: &'a str,
    lexer: Lexer<'a, TokenKind>,
    eoi: bool,
}

impl<'a> Tokenizer<'a> {
    pub fn new(source: &'a str) -> Self {
        Tokenizer {
            source,
            lexer: TokenKind::lexer(source),
            eoi: false,
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Result<Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.lexer.next() {
            Some(kind) if kind == TokenKind::Error => Some(Err(ErrorCode::SyntaxException(
                "unable to recognize the rest tokens".to_string(),
            )
            .set_span(Some((self.lexer.span().start..self.source.len()).into())))),
            Some(kind) if kind == TokenKind::Error => todo!(),
            Some(kind) => Some(Ok(Token {
                source: self.source,
                kind,
                span: self.lexer.span().into(),
            })),
            None if !self.eoi => {
                self.eoi = true;
                Some(Ok(Token::new_eoi(self.source)))
            }
            None => None,
        }
    }
}

//#[allow(non_camel_case_types)]
#[derive(Logos, EnumIter, Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    #[error]
    Error,

    Eoi,

    #[regex(r"[ \t\r\n\f]+", logos::skip)]
    Whitespace,

    //#[regex(r"--[^\t\n\f]*", logos::skip)]
    //Comment,

    //#[regex(r"/\*([^\*]|(\*[^/]))*\*/", logos::skip)]
    //CommentBlock,
    #[regex(r#"[_a-zA-Z][_$a-zA-Z0-9]*"#)]
    Ident,

    #[regex(r#"`[^`]*`"#)]
    #[regex(r#""([^"\\]|\\.|"")*""#)]
    #[regex(r#"'([^'\\]|\\.|'')*'"#)]
    QuotedString,

    #[regex(r"-?[0-9]+")]
    LiteralInteger,

    #[regex(r"[0-9]+[eE][+-]?[0-9]+")]
    #[regex(r"([0-9]*\.[0-9]+([eE][+-]?[0-9]+)?)|([0-9]+\.[0-9]*([eE][+-]?[0-9]+)?)")]
    LiteralFloat,

    // Symbols
    #[token("$")]
    Dollar,

    #[token("==")]
    DoubleEq,
    #[token("=")]
    Eq,
    #[token("<>")]
    #[token("!=")]
    NotEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    Lte,
    #[token(">=")]
    Gte,
    #[token("<=>")]
    Spaceship,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Multiply,
    #[token("/")]
    Divide,
    #[token("%")]
    Modulo,
    #[token("||")]
    StringConcat,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(",")]
    Comma,
    #[token(".")]
    Period,
    #[token("..")]
    DoublePeriod,
    #[token(":")]
    Colon,
    #[token("::")]
    DoubleColon,
    #[token(";")]
    SemiColon,
    #[token("\\")]
    Backslash,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("^")]
    Caret,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("@")]
    AtSign,
    #[token("?")]
    Placeholder,

    // Keywords
    //
    // Steps to add keyword:
    // 1. Add the keyword to token kind variants by alphabetical order.
    // 2. Search in this file to see if the new keyword is a commented
    //    out reserved keyword. If so, uncomment the keyword in the
    //    reserved list.
    #[token("AND", ignore(ascii_case))]
    And,
    #[token("CONTAINS", ignore(ascii_case))]
    Contains,
    #[token("EMPTY", ignore(ascii_case))]
    Empty,
    #[token("FALSE", ignore(ascii_case))]
    False,
    #[token("IN", ignore(ascii_case))]
    In,
    #[token("NIN", ignore(ascii_case))]
    Nin,
    #[token("NOT", ignore(ascii_case))]
    Not,
    #[token("NULL", ignore(ascii_case))]
    Null,
    #[token("OR", ignore(ascii_case))]
    Or,
    #[token("SIZE", ignore(ascii_case))]
    Size,
    #[token("SUBSETOF", ignore(ascii_case))]
    Subsetof,
    #[token("TRUE", ignore(ascii_case))]
    True,
}

impl TokenKind {
    pub fn is_keyword(&self) -> bool {
        !matches!(
            self,
            Ident
                | Dollar
                | QuotedString
                | LiteralInteger
                | LiteralFloat
                | DoubleEq
                | Eq
                | NotEq
                | Lt
                | Gt
                | Lte
                | Gte
                | Spaceship
                | Plus
                | Minus
                | Multiply
                | Divide
                | Modulo
                | StringConcat
                | LParen
                | RParen
                | Comma
                | Period
                | DoublePeriod
                | Colon
                | DoubleColon
                | SemiColon
                | Backslash
                | LBracket
                | RBracket
                | Caret
                | LBrace
                | RBrace
                | AtSign
                | Eoi
        )
    }

    pub fn is_reserved_ident(&self) -> bool {
        matches!(self, |TokenKind::And| TokenKind::Contains
            | TokenKind::Empty
            | TokenKind::False
            | TokenKind::In
            | TokenKind::Nin
            | TokenKind::Not
            | TokenKind::Null
            | TokenKind::Or
            | TokenKind::Size
            | TokenKind::Subsetof
            | TokenKind::True)
    }
}
