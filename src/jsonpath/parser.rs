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

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashSet;

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::bytes::complete::tag_no_case;
use nom::character::complete::char;
use nom::character::complete::digit1;
use nom::character::complete::i32;
use nom::character::complete::multispace0;
use nom::character::complete::one_of;
use nom::character::complete::u8;
use nom::combinator::cond;
use nom::combinator::map;
use nom::combinator::map_res;
use nom::combinator::opt;
use nom::combinator::recognize;
use nom::combinator::value;
use nom::error::Error as NomError;
use nom::error::ErrorKind;
use nom::multi::many0;
use nom::multi::separated_list1;
use nom::sequence::delimited;
use nom::sequence::pair;
use nom::sequence::preceded;
use nom::sequence::separated_pair;
use nom::sequence::terminated;
use nom::IResult;
use nom::Parser;

use crate::constants::MAX_JSON_PATH_DEPTH;
use crate::constants::MAX_JSON_PATH_LOGICAL_OPERATORS;
use crate::constants::UNICODE_LEN;
use crate::error::Error;
use crate::jsonpath::path::*;
use crate::number::Number;
use crate::util::parse_string;

/// Parsing the input string to JSON Path.
pub fn parse_json_path(input: &[u8]) -> Result<JsonPath<'_>, Error> {
    check_paren_depth(input)?;
    let (result, too_many_operators) = count_logical_operators(|| json_path(input));
    if too_many_operators {
        return Err(Error::RecursionLimitExceeded);
    }
    match result {
        Ok((rest, json_path)) => {
            if !rest.is_empty() {
                return Err(Error::InvalidJsonPath);
            }
            Ok(json_path)
        }
        Err(nom::Err::Error(_) | nom::Err::Failure(_)) => Err(Error::InvalidJsonPath),
        Err(nom::Err::Incomplete(_)) => unreachable!(),
    }
}

/// Rejects input whose parentheses nest deeper than [`MAX_JSON_PATH_DEPTH`].
///
/// Every recursive rule of the grammar (`(expr)`, `? (expr)`, `exists(...)`)
/// consumes a `(`, so this bounds the parser's recursion. Characters inside
/// double-quoted string literals are ignored. A backslash escapes the next byte
/// both inside strings and in unquoted field names, as in the parser.
///
/// `&&` and `||` chains are bounded in the parser instead, by
/// [`logical_chain`]: `&` does not end an unquoted field name, so only the
/// parser can tell an operator from part of a name such as `$.a&&b`.
///
/// # Errors
///
/// Returns `Error::RecursionLimitExceeded` if the bound is exceeded.
fn check_paren_depth(input: &[u8]) -> Result<(), Error> {
    let mut depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    for &c in input {
        if escaped {
            escaped = false;
            continue;
        }
        match c {
            b'\\' => escaped = true,
            b'"' => in_string = !in_string,
            _ if in_string => {}
            b'(' => {
                depth += 1;
                if depth > MAX_JSON_PATH_DEPTH {
                    return Err(Error::RecursionLimitExceeded);
                }
            }
            b')' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    Ok(())
}

thread_local! {
    /// Positions in the input of the `&&` and `||` operators that the current
    /// `parse_json_path` call has folded into expression trees.
    static LOGICAL_OPERATORS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
}

/// Runs `parse` with no logical operators recorded, and returns its result and
/// whether it saw more than [`MAX_JSON_PATH_LOGICAL_OPERATORS`].
fn count_logical_operators<T>(parse: impl FnOnce() -> T) -> (T, bool) {
    LOGICAL_OPERATORS.with(|operators| operators.borrow_mut().clear());
    let result = parse();
    let too_many = LOGICAL_OPERATORS.with(|operators| {
        let mut operators = operators.borrow_mut();
        let too_many = operators.len() > MAX_JSON_PATH_LOGICAL_OPERATORS;
        operators.clear();
        too_many
    });
    (result, too_many)
}

fn json_path(input: &[u8]) -> IResult<&[u8], JsonPath<'_>> {
    map(
        delimited(multispace0, expr_or_paths, multispace0),
        |paths| JsonPath { paths },
    )
    .parse(input)
}

fn check_escaped(input: &[u8], i: &mut usize) -> bool {
    if *i + 1 >= input.len() {
        return false;
    }
    if input[*i + 1] == b'u' {
        if *i + 5 >= input.len() {
            return false;
        }
        if input[*i + 2] == b'{' {
            if *i + 7 >= input.len() {
                return false;
            }
            *i += UNICODE_LEN + 4;
        } else {
            *i += UNICODE_LEN + 2;
        }
    } else {
        *i += 2;
    }
    true
}

pub(crate) fn raw_string(input: &[u8]) -> IResult<&[u8], Cow<'_, str>> {
    let mut i = 0;
    let mut escapes = 0;
    while i < input.len() {
        let c = input[i];
        match c {
            b'\\' => {
                escapes += 1;
                if !check_escaped(input, &mut i) {
                    return Err(nom::Err::Error(NomError::new(input, ErrorKind::Char)));
                }
            }
            b' ' | b',' | b'.' | b':' | b'{' | b'}' | b'[' | b']' | b'(' | b')' | b'?' | b'@'
            | b'$' | b'|' | b'<' | b'>' | b'!' | b'=' | b'+' | b'-' | b'*' | b'/' | b'%' | b'"'
            | b'\'' => {
                break;
            }
            _ => {
                i += 1;
            }
        }
    }
    if i > 0 {
        if escapes == 0 {
            if let Ok(s) = std::str::from_utf8(&input[..i]) {
                return Ok((&input[i..], Cow::Borrowed(s)));
            }
        } else {
            let data = &input[..i];
            let len = i - escapes;
            let mut idx = 0;
            let s = parse_string(data, len, &mut idx)
                .map_err(|_| nom::Err::Error(NomError::new(input, ErrorKind::Char)))?;
            return Ok((&input[i..], Cow::Owned(s)));
        }
    }
    Err(nom::Err::Error(NomError::new(input, ErrorKind::Char)))
}

pub(crate) fn string(input: &[u8]) -> IResult<&[u8], Cow<'_, str>> {
    if input.is_empty() || input[0] != b'"' {
        return Err(nom::Err::Error(NomError::new(input, ErrorKind::Char)));
    }
    let mut i = 1;
    let mut escapes = 0;
    while i < input.len() {
        let c = input[i];
        match c {
            b'\\' => {
                escapes += 1;
                if !check_escaped(input, &mut i) {
                    return Err(nom::Err::Error(NomError::new(input, ErrorKind::Char)));
                }
            }
            b'"' => {
                break;
            }
            _ => {
                i += 1;
            }
        }
    }
    // `i == input.len()` means the closing quote is missing. `i == 1` is the
    // empty string `""`, a valid key and string literal.
    if i < input.len() {
        if escapes == 0 {
            if let Ok(s) = std::str::from_utf8(&input[1..i]) {
                return Ok((&input[i + 1..], Cow::Borrowed(s)));
            }
        } else {
            let data = &input[1..i];
            let len = i - 1 - escapes;
            let mut idx = 1;
            let s = parse_string(data, len, &mut idx)
                .map_err(|_| nom::Err::Error(NomError::new(input, ErrorKind::Char)))?;
            return Ok((&input[i + 1..], Cow::Owned(s)));
        }
    }
    Err(nom::Err::Error(NomError::new(input, ErrorKind::Char)))
}

fn bracket_wildcard(input: &[u8]) -> IResult<&[u8], ()> {
    value(
        (),
        delimited(
            char('['),
            delimited(multispace0, char('*'), multispace0),
            char(']'),
        ),
    )
    .parse(input)
}

fn recursive_dot_wildcard(input: &[u8]) -> IResult<&[u8], Option<RecursiveLevel>> {
    preceded(tag(".**"), opt(recursive_level)).parse(input)
}

fn recursive_level(input: &[u8]) -> IResult<&[u8], RecursiveLevel> {
    alt((
        delimited(
            char('{'),
            delimited(multispace0, recursive_level_range, multispace0),
            char('}'),
        ),
        map(
            delimited(
                char('{'),
                delimited(multispace0, u8, multispace0),
                char('}'),
            ),
            |s| RecursiveLevel {
                start: s,
                end: None,
            },
        ),
    ))
    .parse(input)
}

fn recursive_level_range(input: &[u8]) -> IResult<&[u8], RecursiveLevel> {
    alt((
        map(
            separated_pair(
                u8,
                delimited(multispace0, tag_no_case("to"), multispace0),
                u8,
            ),
            |(s, e)| RecursiveLevel {
                start: s,
                end: Some(RecursiveLevelEnd::Index(e)),
            },
        ),
        map(
            separated_pair(
                u8,
                delimited(multispace0, tag_no_case("to"), multispace0),
                tag_no_case("last"),
            ),
            |(s, _)| RecursiveLevel {
                start: s,
                end: Some(RecursiveLevelEnd::Last),
            },
        ),
    ))
    .parse(input)
}

fn colon_field(input: &[u8]) -> IResult<&[u8], Cow<'_, str>> {
    alt((preceded(char(':'), string), preceded(char(':'), raw_string))).parse(input)
}

fn dot_field(input: &[u8]) -> IResult<&[u8], Cow<'_, str>> {
    alt((preceded(char('.'), string), preceded(char('.'), raw_string))).parse(input)
}

fn object_field(input: &[u8]) -> IResult<&[u8], Cow<'_, str>> {
    delimited(
        terminated(char('['), multispace0),
        string,
        preceded(multispace0, char(']')),
    )
    .parse(input)
}

fn index(input: &[u8]) -> IResult<&[u8], Index> {
    alt((
        map(i32, Index::Index),
        map(
            preceded(
                separated_pair(tag_no_case("last"), multispace0, char('-')),
                preceded(multispace0, i32),
            ),
            |v| Index::LastIndex(v.saturating_neg()),
        ),
        map(
            preceded(
                separated_pair(tag_no_case("last"), multispace0, char('+')),
                preceded(multispace0, i32),
            ),
            Index::LastIndex,
        ),
        map(tag_no_case("last"), |_| Index::LastIndex(0)),
    ))
    .parse(input)
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
    ))
    .parse(input)
}

fn array_indices(input: &[u8]) -> IResult<&[u8], Vec<ArrayIndex>> {
    delimited(
        char('['),
        separated_list1(char(','), delimited(multispace0, array_index, multispace0)),
        char(']'),
    )
    .parse(input)
}

fn inner_path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        map(recursive_dot_wildcard, Path::RecursiveDotWildcard),
        value(Path::DotWildcard, tag(".*")),
        value(Path::BracketWildcard, bracket_wildcard),
        map(colon_field, Path::ColonField),
        map(dot_field, Path::DotField),
        map(array_indices, Path::ArrayIndices),
        map(object_field, Path::ObjectField),
    ))
    .parse(input)
}

// Compatible with Snowflake query syntax, the first field name does not require the leading period
fn pre_path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        value(Path::Root, char('$')),
        map(delimited(multispace0, raw_string, multispace0), |v| {
            Path::DotField(v)
        }),
    ))
    .parse(input)
}

fn path(input: &[u8]) -> IResult<&[u8], Path<'_>> {
    alt((
        map(delimited(multispace0, inner_path, multispace0), |v| v),
        map(delimited(multispace0, filter_expr, multispace0), |v| {
            Path::FilterExpr(Box::new(v))
        }),
    ))
    .parse(input)
}

fn expr_or_paths(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    alt((root_expr, paths)).parse(input)
}

fn root_expr(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    map(
        delimited(multispace0, |i| expr_or(i, true), multispace0),
        |v| vec![Path::Expr(Box::new(v))],
    )
    .parse(input)
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
    )
    .parse(input)
}

fn expr_paths(input: &[u8], is_root_expr: bool) -> IResult<&[u8], Vec<Path<'_>>> {
    let parse_current = map_res(
        cond(!is_root_expr, value(Path::Current, char('@'))),
        |res| match res {
            Some(v) => Ok(v),
            None => Err(NomError::new(input, ErrorKind::Char)),
        },
    );
    map(
        pair(
            alt((value(Path::Root, char('$')), parse_current)),
            many0(delimited(multispace0, inner_path, multispace0)),
        ),
        |(pre_path, mut paths)| {
            paths.insert(0, pre_path);
            paths
        },
    )
    .parse(input)
}

fn filter_expr(input: &[u8]) -> IResult<&[u8], Expr<'_>> {
    map(
        delimited(
            delimited(char('?'), multispace0, char('(')),
            delimited(multispace0, |i| expr_or(i, false), multispace0),
            char(')'),
        ),
        |v| v,
    )
    .parse(input)
}

fn op(input: &[u8]) -> IResult<&[u8], BinaryOperator> {
    alt((
        value(BinaryOperator::Eq, tag("==")),
        value(BinaryOperator::NotEq, tag("!=")),
        value(BinaryOperator::NotEq, tag("<>")),
        value(BinaryOperator::Lte, tag("<=")),
        value(BinaryOperator::Lt, char('<')),
        value(BinaryOperator::Gte, tag(">=")),
        value(BinaryOperator::Gt, char('>')),
        value(BinaryOperator::StartsWith, tag("starts with")),
        value(BinaryOperator::Add, char('+')),
        value(BinaryOperator::Subtract, char('-')),
        value(BinaryOperator::Multiply, char('*')),
        value(BinaryOperator::Divide, char('/')),
        value(BinaryOperator::Modulo, char('%')),
    ))
    .parse(input)
}

fn unary_arith_op(input: &[u8]) -> IResult<&[u8], UnaryOperator> {
    alt((
        value(UnaryOperator::Add, char('+')),
        value(UnaryOperator::Subtract, char('-')),
    ))
    .parse(input)
}

fn path_value(input: &[u8]) -> IResult<&[u8], PathValue<'_>> {
    alt((
        value(PathValue::Null, tag("null")),
        value(PathValue::Boolean(true), tag("true")),
        value(PathValue::Boolean(false), tag("false")),
        map(number, PathValue::Number),
        map(string, PathValue::String),
    ))
    .parse(input)
}

/// Parses a number literal.
///
/// The whole literal is recognized before its type is chosen. Trying the
/// integer parsers first would take `1` from `1.5` and leave `.5`, which no
/// rule accepts, so literals with a fraction or exponent never parsed.
fn number(input: &[u8]) -> IResult<&[u8], Number> {
    alt((
        map_res(number_literal, |literal: &[u8]| {
            // `number_literal` only matches ASCII.
            let literal = std::str::from_utf8(literal).map_err(|_| ErrorKind::Float)?;
            if !literal.contains(['.', 'e', 'E']) {
                if let Ok(v) = literal.parse::<u64>() {
                    return Ok(Number::UInt64(v));
                }
                if let Ok(v) = literal.parse::<i64>() {
                    return Ok(Number::Int64(v));
                }
            }
            literal
                .parse::<f64>()
                .map(Number::Float64)
                .map_err(|_| ErrorKind::Float)
        }),
        // `inf`, `infinity` and `nan`, with an optional sign. `Display`
        // writes negative infinity as `-inf`, so the sign must be accepted
        // for formatted paths to parse again.
        map_res(
            recognize((
                opt(one_of("+-")),
                alt((
                    tag_no_case("infinity"),
                    tag_no_case("inf"),
                    tag_no_case("nan"),
                )),
            )),
            |literal: &[u8]| {
                std::str::from_utf8(literal)
                    .ok()
                    .and_then(|literal| literal.parse::<f64>().ok())
                    .map(Number::Float64)
                    .ok_or(ErrorKind::Float)
            },
        ),
    ))
    .parse(input)
}

/// Recognizes `[+-]digits[.digits][e[+-]digits]` or `[+-].digits[e[+-]digits]`.
///
/// Unlike `nom::number::complete::recognize_float`, an `e` without exponent
/// digits ends the literal instead of failing the whole parse, so `1e` can
/// still be read as a field name.
fn number_literal(input: &[u8]) -> IResult<&[u8], &[u8]> {
    recognize((
        opt(one_of("+-")),
        alt((
            recognize((digit1, opt((char('.'), opt(digit1))))),
            recognize((char('.'), digit1)),
        )),
        opt((one_of("eE"), opt(one_of("+-")), digit1)),
    ))
    .parse(input)
}

fn inner_expr(input: &[u8], is_root_expr: bool) -> IResult<&[u8], Expr<'_>> {
    alt((
        map(|i| expr_paths(i, is_root_expr), Expr::Paths),
        map(path_value, |v| Expr::Value(Box::new(v))),
    ))
    .parse(input)
}

fn expr_atom(input: &[u8], is_root_expr: bool) -> IResult<&[u8], Expr<'_>> {
    alt((
        map(
            pair(
                unary_arith_op,
                delimited(multispace0, |i| inner_expr(i, is_root_expr), multispace0),
            ),
            |(op, operand)| Expr::UnaryOp {
                op,
                operand: Box::new(operand),
            },
        ),
        map(
            pair(
                pair(
                    delimited(multispace0, |i| inner_expr(i, is_root_expr), multispace0),
                    op,
                ),
                delimited(multispace0, |i| inner_expr(i, is_root_expr), multispace0),
            ),
            |((left, op), right)| Expr::BinaryOp {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        ),
        map(
            delimited(
                terminated(char('('), multispace0),
                |i| expr_or(i, is_root_expr),
                preceded(multispace0, char(')')),
            ),
            |expr| expr,
        ),
        map(exists_func, Expr::ExistsFunc),
    ))
    .parse(input)
}

fn exists_func(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    preceded(
        tag("exists"),
        preceded(
            multispace0,
            delimited(
                terminated(char('('), multispace0),
                exists_paths,
                preceded(multispace0, char(')')),
            ),
        ),
    )
    .parse(input)
}

fn exists_paths(input: &[u8]) -> IResult<&[u8], Vec<Path<'_>>> {
    map(
        pair(
            alt((
                value(Path::Root, char('$')),
                value(Path::Current, char('@')),
            )),
            many0(path),
        ),
        |(pre, mut paths)| {
            paths.insert(0, pre);
            paths
        },
    )
    .parse(input)
}

fn expr_and(input: &[u8], is_root_expr: bool) -> IResult<&[u8], Expr<'_>> {
    logical_chain(input, "&&", BinaryOperator::And, |i| {
        expr_atom(i, is_root_expr)
    })
}

fn expr_or(input: &[u8], is_root_expr: bool) -> IResult<&[u8], Expr<'_>> {
    logical_chain(input, "||", BinaryOperator::Or, |i| {
        expr_and(i, is_root_expr)
    })
}

/// Parses `operand`s separated by `operator` and folds them left into
/// `op` nodes.
///
/// The fold builds a tree as deep as the chain is long, and formatting,
/// evaluating, cloning, comparing and dropping it recurse once per level. So
/// the chain fails before folding once the whole path has more than
/// [`MAX_JSON_PATH_LOGICAL_OPERATORS`] operators. Operators are recorded by
/// position, so a chain that backtracking parses again is counted once.
fn logical_chain<'a>(
    input: &'a [u8],
    operator: &'static str,
    op: BinaryOperator,
    operand: impl FnMut(&'a [u8]) -> IResult<&'a [u8], Expr<'a>>,
) -> IResult<&'a [u8], Expr<'a>> {
    let mut positions = Vec::new();
    let separator = |i: &'a [u8]| {
        let (i, _) = multispace0(i)?;
        let position = i.as_ptr() as usize;
        let (i, _) = tag(operator).parse(i)?;
        let (i, _) = multispace0(i)?;
        positions.push(position);
        Ok((i, ()))
    };
    let (rest, exprs) = separated_list1(separator, operand).parse(input)?;
    // A separator can match before an operand that fails, ending the list.
    positions.truncate(exprs.len() - 1);
    let too_many = LOGICAL_OPERATORS.with(|operators| {
        let mut operators = operators.borrow_mut();
        operators.extend(positions);
        operators.len() > MAX_JSON_PATH_LOGICAL_OPERATORS
    });
    if too_many {
        // `Failure` keeps alternatives from parsing the chain again.
        return Err(nom::Err::Failure(NomError::new(input, ErrorKind::TooLarge)));
    }
    // Fold left, moving the operands instead of cloning their subtrees.
    let mut exprs = exprs.into_iter();
    let first = exprs.next().expect("separated_list1 yields an operand");
    let expr = exprs.fold(first, |left, right| Expr::BinaryOp {
        op: op.clone(),
        left: Box::new(left),
        right: Box::new(right),
    });
    Ok((rest, expr))
}
