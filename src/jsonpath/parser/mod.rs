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

pub mod expr;
pub mod json_path;
pub mod token;
pub mod unescape;

use crate::jsonpath::ast::JsonPath;
use crate::jsonpath::error::display_parser_error;
use crate::jsonpath::error::Backtrace;
use crate::jsonpath::exception::ErrorCode;
use crate::jsonpath::exception::Result;
use crate::jsonpath::input::Input;
use crate::jsonpath::parser::json_path::json_path;
use crate::jsonpath::parser::token::Token;
use crate::jsonpath::parser::token::TokenKind;
use crate::jsonpath::parser::token::Tokenizer;
use crate::jsonpath::util::transform_span;

pub fn tokenize(json_path: &str) -> Result<Vec<Token>> {
    Tokenizer::new(json_path).collect::<Result<Vec<_>>>()
}

/// Parse a json path string into `JsonPath`.
pub fn parse_json_path<'a>(tokens: &'a [Token<'a>]) -> Result<JsonPath> {
    let backtrace = Backtrace::new();
    match json_path(Input(tokens, &backtrace)) {
        Ok((rest, json_path)) if rest[0].kind == TokenKind::EOI => Ok(json_path),
        Ok((rest, _)) => Err(ErrorCode::SyntaxException(
            "unable to parse rest of the json path".to_string(),
        )
        .set_span(transform_span(&rest[..1]))),
        Err(nom::Err::Error(err) | nom::Err::Failure(err)) => {
            let source = tokens[0].source;
            Err(ErrorCode::SyntaxException(display_parser_error(
                err, source,
            )))
        }
        Err(nom::Err::Incomplete(_)) => unreachable!(),
    }
}
