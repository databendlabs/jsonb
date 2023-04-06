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

use nom::{
    branch::alt,
    bytes::complete::{escaped, tag, tag_no_case},
    character::complete::{alphanumeric1, char, i32, i64, multispace0, one_of, u64},
    combinator::{map, opt, value},
    multi::{many0, separated_list1},
    number::complete::double,
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    IResult,
};

use crate::error::Error;
use crate::jsonpath::path::*;
use crate::number::Number;
use std::borrow::Cow;

/// Parsing the input string to JSON Path.
pub fn parse_json_path(input: &[u8]) -> Result<JsonPath<'_>, Error> {
    match json_path(input) {
        Ok((rest, json_path)) => {
            if !rest.is_empty() {
                return Err(Error::InvalidJsonPath);
            }
            Ok(json_path)
        }
        Err(nom::Err::Error(_err) | nom::Err::Failure(_err)) => Err(Error::InvalidJsonb),
        Err(nom::Err::Incomplete(_)) => unreachable!(),
    }
}

fn json_path(input: &[u8]) -> IResult<&[u8], JsonPath<'_>> {
    map(delimited(multispace0, paths, multispace0), |paths| {
        JsonPath { paths }
    })(input)
}

fn raw_string(input: &[u8]) -> IResult<&[u8], &[u8]> {
    escaped(alphanumeric1, '\\', one_of("\"n\\"))(input)
}

fn string(input: &[u8]) -> IResult<&[u8], &[u8]> {
    // TODO: support special characters and unicode characters.
    delimited(char('"'), raw_string, char('"'))(input)
}

fn bracket_wildcard(input: &[u8]) -> IResult<&[u8], ()> {
    value(
        (),
        delimited(
            char('['),
            delimited(multispace0, char('*'), multispace0),
            char(']'),
        ),
    )(input)
}

fn colon_field(input: &[u8]) -> IResult<&[u8], &[u8]> {
    preceded(char(':'), alphanumeric1)(input)
}

fn dot_field(input: &[u8]) -> IResult<&[u8], &[u8]> {
    alt((
        preceded(char('.'), alphanumeric1),
        preceded(char('.'), string),
    ))(input)
}

fn object_field(input: &[u8]) -> IResult<&[u8], &[u8]> {
    delimited(
        terminated(char('['), multispace0),
        string,
        preceded(multispace0, char(']')),
    )(input)
}

fn index(input: &[u8]) -> IResult<&[u8], Index> {
    alt((
        map(i32, Index::Index),
        map(
            preceded(
                tuple((tag_no_case("last"), multispace0, char('-'), multispace0)),
                i32,
            ),
            |v| Index::LastIndex(v.saturating_neg()),
        ),
        map(
            preceded(
                tuple((tag_no_case("last"), multispace0, char('+'), multispace0)),
                i32,
            ),
            Index::LastIndex,
        ),
        map(tag_no_case("last"), |_| Index::LastIndex(0)),
    ))(input)
}

fn array_index(input: &[u8]) -> IResult<&[u8], ArrayIndex> {
    alt((
        map(
            separated_pair(
                index,
                delimited(multispace0, tag_no_case("to"), multispace0),
                index,
            ),
            |(s, e)| ArrayIndex::Slice((s, e)),
        ),
        map(index, ArrayIndex::Index),
    ))(input)
}

fn array_indices(input: &[u8]) -> IResult<&[u8], Vec<ArrayIndex>> {
    delimited(
        terminated(char('['), multispace0),
        separated_list1(delimited(multispace0, char(','), multispace0), array_index),
        preceded(multispace0, char(']')),
    )(input)
}

fn inner_path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        value(Path::DotWildcard, tag(".*")),
        value(Path::BracketWildcard, bracket_wildcard),
        map(colon_field, |v| {
            Path::ColonField(Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(v) }))
        }),
        map(dot_field, |v| {
            Path::DotField(Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(v) }))
        }),
        map(object_field, |v| {
            Path::ObjectField(Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(v) }))
        }),
        map(array_indices, Path::ArrayIndices),
    ))(input)
}

// Compatible with Snowflake query syntax, the first field name does not require the leading period
fn pre_path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        value(Path::Root, char('$')),
        map(delimited(multispace0, alphanumeric1, multispace0), |v| {
            Path::DotField(Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(v) }))
        }),
    ))(input)
}

fn path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        map(delimited(multispace0, inner_path, multispace0), |v| v),
        map(delimited(multispace0, filter_expr, multispace0), |v| {
            Path::FilterExpr(Box::new(v))
        }),
    ))(input)
}

fn paths(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    map(
        pair(opt(pre_path), many0(path)),
        |(opt_pre_path, mut paths)| {
            if let Some(pre_path) = opt_pre_path {
                paths.insert(0, pre_path);
            }
            paths
        },
    )(input)
}

fn expr_paths(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    map(
        pair(
            alt((
                value(Path::Root, char('$')),
                value(Path::Current, char('@')),
            )),
            many0(delimited(multispace0, inner_path, multispace0)),
        ),
        |(pre_path, mut paths)| {
            paths.insert(0, pre_path);
            paths
        },
    )(input)
}

fn filter_expr(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    map(
        delimited(
            delimited(char('?'), multispace0, char('(')),
            delimited(multispace0, expr_or, multispace0),
            char(')'),
        ),
        |v| v,
    )(input)
}

fn op(input: &[u8]) -> IResult<&[u8], BinaryOperator> {
    alt((
        value(BinaryOperator::Eq, tag("==")),
        value(BinaryOperator::NotEq, tag("!=")),
        value(BinaryOperator::NotEq, tag("<>")),
        value(BinaryOperator::Lt, char('<')),
        value(BinaryOperator::Lte, tag("<=")),
        value(BinaryOperator::Gt, char('>')),
        value(BinaryOperator::Gte, tag(">=")),
    ))(input)
}

fn path_value(input: &[u8]) -> IResult<&[u8], PathValue<'_>> {
    alt((
        value(PathValue::Null, tag("null")),
        value(PathValue::Boolean(true), tag("true")),
        value(PathValue::Boolean(false), tag("false")),
        map(u64, |v| PathValue::Number(Number::UInt64(v))),
        map(i64, |v| PathValue::Number(Number::Int64(v))),
        map(double, |v| PathValue::Number(Number::Float64(v))),
        map(string, |v| {
            PathValue::String(Cow::Borrowed(unsafe { std::str::from_utf8_unchecked(v) }))
        }),
    ))(input)
}

fn inner_expr(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    alt((
        map(expr_paths, Expr::Paths),
        map(path_value, |v| Expr::Value(Box::new(v))),
    ))(input)
}

fn expr_atom(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    // TODO, support arithmetic expressions.
    alt((
        map(
            tuple((
                delimited(multispace0, inner_expr, multispace0),
                op,
                delimited(multispace0, inner_expr, multispace0),
            )),
            |(left, op, right)| Expr::BinaryOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        ),
        map(
            delimited(
                terminated(char('('), multispace0),
                expr_or,
                preceded(multispace0, char(')')),
            ),
            |expr| expr,
        ),
    ))(input)
}

fn expr_and(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    map(
        separated_list1(delimited(multispace0, tag("&&"), multispace0), expr_atom),
        |exprs| {
            let mut expr = exprs[0].clone();
            for right in exprs.iter().skip(1) {
                expr = Expr::BinaryOp {
                    op: BinaryOperator::And,
                    left: Box::new(expr),
                    right: Box::new(right.clone()),
                };
            }
            expr
        },
    )(input)
}

fn expr_or(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    map(
        separated_list1(delimited(multispace0, tag("||"), multispace0), expr_and),
        |exprs| {
            let mut expr = exprs[0].clone();
            for right in exprs.iter().skip(1) {
                expr = Expr::BinaryOp {
                    op: BinaryOperator::Or,
                    left: Box::new(expr),
                    right: Box::new(right.clone()),
                };
            }
            expr
        },
    )(input)
}
