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

use crate::jsonpath::exception::Range;
use crate::jsonpath::exception::Span;
use nom::branch::alt;
use nom::combinator::map;
use nom::Offset;
use nom::Slice;
use pratt::PrattError;
use pratt::PrattParser;
use pratt::Precedence;

use crate::jsonpath::ast::Identifier;
use crate::jsonpath::error::Error;
use crate::jsonpath::error::ErrorKind;
use crate::jsonpath::input::Input;
use crate::jsonpath::input::WithSpan;
use crate::jsonpath::parser::token::*;
use crate::rule;

pub(crate) type IResult<'a, Output> = nom::IResult<Input<'a>, Output, Error<'a>>;

#[macro_export]
macro_rules! rule {
    ($($tt:tt)*) => { nom_rule::rule!(
        $crate::jsonpath::util::match_text,
        $crate::jsonpath::util::match_token,
        $($tt)*)
    }
}

pub(crate) fn match_text(text: &'static str) -> impl FnMut(Input) -> IResult<&Token> {
    move |i| match i.0.get(0).filter(|token| token.text() == text) {
        Some(token) => Ok((i.slice(1..), token)),
        _ => Err(nom::Err::Error(Error::from_error_kind(
            i,
            ErrorKind::ExpectText(text),
        ))),
    }
}

pub(crate) fn match_token(kind: TokenKind) -> impl FnMut(Input) -> IResult<&Token> {
    move |i| match i.0.get(0).filter(|token| token.kind == kind) {
        Some(token) => Ok((i.slice(1..), token)),
        _ => Err(nom::Err::Error(Error::from_error_kind(
            i,
            ErrorKind::ExpectToken(kind),
        ))),
    }
}

pub(crate) fn ident(i: Input) -> IResult<Identifier> {
    non_reserved_identifier(|token| token.is_reserved_ident())(i)
}

fn non_reserved_identifier(
    is_reserved_keyword: fn(&TokenKind) -> bool,
) -> impl FnMut(Input) -> IResult<Identifier> {
    move |i| {
        alt((
            map(
                alt((rule! { Ident }, non_reserved_keyword(is_reserved_keyword))),
                |token| Identifier {
                    span: transform_span(&[token.clone()]),
                    name: token.text().to_string(),
                    quote: None,
                },
            ),
            move |i| {
                match_token(QuotedString)(i).and_then(|(i2, token)| {
                    if token
                        .text()
                        .chars()
                        .next()
                        .filter(|c| is_ident_quote(*c))
                        .is_some()
                    {
                        Ok((
                            i2,
                            Identifier {
                                span: transform_span(&[token.clone()]),
                                name: token.text()[1..token.text().len() - 1].to_string(),
                                quote: Some(token.text().chars().next().unwrap()),
                            },
                        ))
                    } else {
                        Err(nom::Err::Error(Error::from_error_kind(
                            i,
                            ErrorKind::ExpectToken(Ident),
                        )))
                    }
                })
            },
        ))(i)
    }
}

fn non_reserved_keyword(
    is_reserved_keyword: fn(&TokenKind) -> bool,
) -> impl FnMut(Input) -> IResult<&Token> {
    move |i: Input| match i
        .0
        .get(0)
        .filter(|token| token.kind.is_keyword() && !is_reserved_keyword(&token.kind))
    {
        Some(token) => Ok((i.slice(1..), token)),
        _ => Err(nom::Err::Error(Error::from_error_kind(
            i,
            ErrorKind::ExpectToken(Ident),
        ))),
    }
}

pub fn comma_separated_list1<'a, T>(
    item: impl FnMut(Input<'a>) -> IResult<'a, T>,
) -> impl FnMut(Input<'a>) -> IResult<'a, Vec<T>> {
    separated_list1(match_text(","), item)
}

/// A fork of `separated_list1` from nom, but never forgive parser error
/// after a separator is encountered.
pub(crate) fn separated_list1<I, O, O2, E, F, G>(
    mut sep: G,
    mut f: F,
) -> impl FnMut(I) -> nom::IResult<I, Vec<O>, E>
where
    I: Clone + nom::InputLength,
    F: nom::Parser<I, O, E>,
    G: nom::Parser<I, O2, E>,
    E: nom::error::ParseError<I>,
{
    move |mut i: I| {
        let mut res = Vec::new();

        // Parse the first element
        match f.parse(i.clone()) {
            Err(e) => return Err(e),
            Ok((i1, o)) => {
                res.push(o);
                i = i1;
            }
        }

        loop {
            let len = i.input_len();
            match sep.parse(i.clone()) {
                Err(nom::Err::Error(_)) => return Ok((i, res)),
                Err(e) => return Err(e),
                Ok((i1, _)) => {
                    // infinite loop check: the parser must always consume
                    if i1.input_len() == len {
                        return Err(nom::Err::Error(E::from_error_kind(
                            i1,
                            nom::error::ErrorKind::SeparatedList,
                        )));
                    }

                    match f.parse(i1.clone()) {
                        Err(e) => return Err(e),
                        Ok((i2, o)) => {
                            res.push(o);
                            i = i2;
                        }
                    }
                }
            }
        }
    }
}

pub(crate) fn continue_list1<'a, T>(
    item: impl FnMut(Input<'a>) -> IResult<'a, T>,
) -> impl FnMut(Input<'a>) -> IResult<'a, Vec<T>> {
    continue_without_separate_list1(item)
}

/// A fork of `separated_list0` from nom, but never forgive parser error
/// after a separator is encountered, and always forgive the first element
/// failure.
pub(crate) fn continue_without_separate_list1<I, O, E, F>(
    mut f: F,
) -> impl FnMut(I) -> nom::IResult<I, Vec<O>, E>
where
    I: Clone + nom::InputLength,
    F: nom::Parser<I, O, E>,
    E: nom::error::ParseError<I>,
{
    move |mut i: I| {
        let mut res = Vec::new();

        // Parse the first element
        match f.parse(i.clone()) {
            Err(e) => return Err(e),
            Ok((i1, o)) => {
                res.push(o);
                i = i1;
            }
        }

        loop {
            match f.parse(i.clone()) {
                Err(_e) => return Ok((i, res)),
                Ok((i1, o)) => {
                    res.push(o);
                    i = i1;
                }
            }
        }
    }
}

/// A fork of `map_res` from nom, but doesn't require `FromExternalError`.
pub(crate) fn map_res<'a, O1, O2, F, G>(
    mut parser: F,
    mut f: G,
) -> impl FnMut(Input<'a>) -> IResult<'a, O2>
where
    F: nom::Parser<Input<'a>, O1, Error<'a>>,
    G: FnMut(O1) -> Result<O2, ErrorKind>,
{
    move |input: Input| {
        let i = input;
        let (input, o1) = parser.parse(input)?;
        match f(o1) {
            Ok(o2) => Ok((input, o2)),
            Err(e) => Err(nom::Err::Error(Error::from_error_kind(i, e))),
        }
    }
}

pub(crate) fn transform_span(tokens: &[Token]) -> Span {
    Some(Range {
        start: tokens.first().unwrap().span.start,
        end: tokens.last().unwrap().span.end,
    })
}

pub(crate) fn run_pratt_parser<'a, I, P, E>(
    mut parser: P,
    iter: &I,
    rest: Input<'a>,
    input: Input<'a>,
) -> IResult<'a, P::Output>
where
    E: std::fmt::Debug,
    P: PrattParser<I, Input = WithSpan<'a, E>, Error = &'static str>,
    I: Iterator<Item = P::Input> + ExactSizeIterator + Clone,
{
    let mut iter_cloned = iter.clone();
    let mut iter = iter.clone().peekable();
    let len = iter.len();
    let expr = parser
        .parse_input(&mut iter, Precedence(0))
        .map_err(|err| {
            // Rollback parsing footprint on unused expr elements.
            input.1.clear();

            let err_kind = match err {
                PrattError::EmptyInput => ErrorKind::Other("expecting more subsequent tokens"),
                PrattError::UnexpectedNilfix(_) => ErrorKind::Other("unable to parse the element"),
                PrattError::UnexpectedPrefix(_) => {
                    ErrorKind::Other("unable to parse the prefix operator")
                }
                PrattError::UnexpectedInfix(_) => {
                    ErrorKind::Other("missing lhs or rhs for the binary operator")
                }
                PrattError::UnexpectedPostfix(_) => {
                    ErrorKind::Other("unable to parse the postfix operator")
                }
                PrattError::UserError(err) => ErrorKind::Other(err),
            };

            let span = iter_cloned
                .nth(len - iter.len() - 1)
                .map(|elem| elem.span)
                // It's safe to slice one more token because input must contain EOI.
                .unwrap_or_else(|| rest.slice(..1));

            nom::Err::Error(Error::from_error_kind(span, err_kind))
        })?;
    if let Some(elem) = iter.peek() {
        // Rollback parsing footprint on unused expr elements.
        input.1.clear();
        Ok((input.slice(input.offset(&elem.span)..), expr))
    } else {
        Ok((rest, expr))
    }
}

pub(crate) fn is_ident_quote(c: char) -> bool {
    c == '"' || c == '`'
}

pub(crate) fn is_string_quote(c: char) -> bool {
    c == '\'' || c == '"'
}
