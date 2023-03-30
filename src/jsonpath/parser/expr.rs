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

use crate::jsonpath::parser::json_path::path;
use itertools::Itertools;
use nom::branch::alt;
use nom::combinator::consumed;
use nom::combinator::map;
use nom::combinator::value;
use nom::error::context;
use pratt::Affix;
use pratt::Associativity;
use pratt::PrattParser;
use pratt::Precedence;

use crate::jsonpath::ast::*;
use crate::jsonpath::error::Error;
use crate::jsonpath::error::ErrorKind;
use crate::jsonpath::input::is_string_quote;
use crate::jsonpath::input::Input;
use crate::jsonpath::input::WithSpan;
use crate::jsonpath::parser::token::*;
use crate::jsonpath::parser::unescape::unescape;
use crate::jsonpath::util::*;
use crate::rule;

pub fn expr(i: Input) -> IResult<Expr> {
    context("expression", subexpr(0))(i)
}

pub fn subexpr(min_precedence: u32) -> impl FnMut(Input) -> IResult<Expr> {
    move |i| {
        let higher_prec_expr_element =
            |i| {
                expr_element(i).and_then(|(rest, elem)| {
                    match PrattParser::<std::iter::Once<_>>::query(&mut ExprParser, &elem).unwrap()
                    {
                        Affix::Infix(prec, _) | Affix::Prefix(prec) | Affix::Postfix(prec)
                            if prec <= Precedence(min_precedence) =>
                        {
                            Err(nom::Err::Error(Error::from_error_kind(
                                i,
                                ErrorKind::Other("expected more tokens for expression"),
                            )))
                        }
                        _ => Ok((rest, elem)),
                    }
                })
            };

        let (rest, mut expr_elements) = rule! { #higher_prec_expr_element+ }(i)?;

        for (prev, curr) in (-1..(expr_elements.len() as isize)).tuple_windows() {
            // Replace binary Plus and Minus to the unary one, if it's following another op
            // or it's the first element.
            if prev == -1
                || matches!(
                    expr_elements[prev as usize].elem,
                    ExprElement::UnaryOp { .. } | ExprElement::BinaryOp { .. }
                )
            {
                match &mut expr_elements[curr as usize].elem {
                    elem @ ExprElement::BinaryOp {
                        op: BinaryOperator::Plus,
                    } => {
                        *elem = ExprElement::UnaryOp {
                            op: UnaryOperator::Plus,
                        };
                    }
                    elem @ ExprElement::BinaryOp {
                        op: BinaryOperator::Minus,
                    } => {
                        *elem = ExprElement::UnaryOp {
                            op: UnaryOperator::Minus,
                        };
                    }
                    _ => {}
                }
            }

            // If it's following a prefix or infix element or it's the first element, ...
            if prev == -1
                || matches!(
                    PrattParser::<std::iter::Once<_>>::query(
                        &mut ExprParser,
                        &expr_elements[prev as usize]
                    )
                    .unwrap(),
                    Affix::Prefix(_) | Affix::Infix(_, _)
                )
            {
                // replace bracket map access to an array, ...
            }

            if prev != -1 {
                if let (
                    ExprElement::UnaryOp {
                        op: UnaryOperator::Minus,
                    },
                    ExprElement::Literal { lit },
                ) = (
                    &expr_elements[prev as usize].elem,
                    &expr_elements[curr as usize].elem,
                ) {
                    if matches!(lit, Literal::Float(_) | Literal::UInt64(_)) {
                        let span = expr_elements[curr as usize].span;
                        expr_elements[curr as usize] = WithSpan {
                            span,
                            elem: ExprElement::Literal { lit: lit.neg() },
                        };
                        let span = expr_elements[prev as usize].span;
                        expr_elements[prev as usize] = WithSpan {
                            span,
                            elem: ExprElement::Skip,
                        };
                    }
                }
            }
        }
        let iter = &mut expr_elements
            .into_iter()
            .filter(|x| x.elem != ExprElement::Skip)
            .collect::<Vec<_>>()
            .into_iter();
        run_pratt_parser(ExprParser, iter, rest, i)
    }
}

/// A 'flattened' AST of expressions.
///
/// This is used to parse expressions in Pratt parser.
/// The Pratt parser is not able to parse expressions by grammar. So we need to extract
/// the expression operands and operators to be the input of Pratt parser, by running a
/// nom parser in advance.
///
/// For example, `a + b AND c is null` is parsed as `[col(a), PLUS, col(b), AND, col(c), ISNULL]` by nom parsers.
/// Then the Pratt parser is able to parse the expression into `AND(PLUS(col(a), col(b)), ISNULL(col(c)))`.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprElement {
    /// Json paths like `$.price`
    Paths {
        paths: Vec<Path>,
    },
    /// A literal value, such as string, number, bool or NULL
    Literal {
        lit: Literal,
    },
    /// Binary operation
    BinaryOp {
        op: BinaryOperator,
    },
    /// Unary operation
    UnaryOp {
        op: UnaryOperator,
    },
    Skip,
}

struct ExprParser;

impl<'a, I: Iterator<Item = WithSpan<'a, ExprElement>>> PrattParser<I> for ExprParser {
    type Error = &'static str;
    type Input = WithSpan<'a, ExprElement>;
    type Output = Expr;

    fn query(&mut self, elem: &WithSpan<ExprElement>) -> Result<Affix, &'static str> {
        let affix = match &elem.elem {
            ExprElement::UnaryOp { op } => match op {
                UnaryOperator::Not => Affix::Prefix(Precedence(15)),

                UnaryOperator::Plus => Affix::Prefix(Precedence(50)),
                UnaryOperator::Minus => Affix::Prefix(Precedence(50)),
            },
            ExprElement::BinaryOp { op } => match op {
                BinaryOperator::Or => Affix::Infix(Precedence(5), Associativity::Left),

                BinaryOperator::And => Affix::Infix(Precedence(10), Associativity::Left),

                BinaryOperator::Eq => Affix::Infix(Precedence(20), Associativity::Right),
                BinaryOperator::NotEq => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Gt => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Lt => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Gte => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Lte => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::In => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Nin => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Subsetof => Affix::Infix(Precedence(20), Associativity::Left),
                BinaryOperator::Contains => Affix::Infix(Precedence(20), Associativity::Left),

                BinaryOperator::Plus => Affix::Infix(Precedence(30), Associativity::Left),
                BinaryOperator::Minus => Affix::Infix(Precedence(30), Associativity::Left),

                BinaryOperator::Multiply => Affix::Infix(Precedence(40), Associativity::Left),
                BinaryOperator::Divide => Affix::Infix(Precedence(40), Associativity::Left),
                BinaryOperator::Modulo => Affix::Infix(Precedence(40), Associativity::Left),
            },
            _ => Affix::Nilfix,
        };
        Ok(affix)
    }

    fn primary(&mut self, elem: WithSpan<'a, ExprElement>) -> Result<Expr, &'static str> {
        let expr = match elem.elem {
            ExprElement::Literal { lit } => Expr::Literal {
                span: transform_span(elem.span.0),
                lit,
            },
            ExprElement::Paths { paths } => Expr::Paths {
                span: transform_span(elem.span.0),
                paths,
            },
            _ => unreachable!(),
        };

        Ok(expr)
    }

    fn infix(
        &mut self,
        lhs: Expr,
        elem: WithSpan<'a, ExprElement>,
        rhs: Expr,
    ) -> Result<Expr, &'static str> {
        let expr = match elem.elem {
            ExprElement::BinaryOp { op } => Expr::BinaryOp {
                span: transform_span(elem.span.0),
                left: Box::new(lhs),
                right: Box::new(rhs),
                op,
            },
            _ => unreachable!(),
        };
        Ok(expr)
    }

    fn prefix(&mut self, elem: WithSpan<'a, ExprElement>, rhs: Expr) -> Result<Expr, &'static str> {
        let expr = match elem.elem {
            ExprElement::UnaryOp { op } => Expr::UnaryOp {
                span: transform_span(elem.span.0),
                op,
                expr: Box::new(rhs),
            },
            _ => unreachable!(),
        };
        Ok(expr)
    }

    fn postfix(
        &mut self,
        lhs: Expr,
        elem: WithSpan<'a, ExprElement>,
    ) -> Result<Expr, &'static str> {
        let expr = match elem.elem {
            ExprElement::UnaryOp { op } => Expr::UnaryOp {
                span: transform_span(elem.span.0),
                op,
                expr: Box::new(lhs),
            },
            _ => unreachable!(),
        };
        Ok(expr)
    }
}

pub fn expr_element(i: Input) -> IResult<WithSpan<ExprElement>> {
    let binary_op = map(binary_op, |op| ExprElement::BinaryOp { op });
    let unary_op = map(unary_op, |op| ExprElement::UnaryOp { op });
    let literal = map(literal, |lit| ExprElement::Literal { lit });
    let paths = map(
        rule! {
            #continue_list1(path)
        },
        |paths| ExprElement::Paths { paths },
    );

    let (rest, (span, elem)) = consumed(alt((rule!(
        #literal : "<literal>"
        | #binary_op : "<binary_op>"
        | #unary_op : "<unary_op>"
        | #paths : "<paths>"
    ),)))(i)?;

    Ok((rest, WithSpan { span, elem }))
}

pub fn unary_op(i: Input) -> IResult<UnaryOperator> {
    // Plus and Minus are parsed as binary op at first.
    alt((value(UnaryOperator::Not, rule! { NOT }),))(i)
}

pub fn binary_op(i: Input) -> IResult<BinaryOperator> {
    alt((
        alt((
            value(BinaryOperator::Plus, rule! { "+" }),
            value(BinaryOperator::Minus, rule! { "-" }),
            value(BinaryOperator::Multiply, rule! { "*" }),
            value(BinaryOperator::Divide, rule! { "/" }),
            value(BinaryOperator::Modulo, rule! { "%" }),
            value(BinaryOperator::Gt, rule! { ">" }),
            value(BinaryOperator::Lt, rule! { "<" }),
            value(BinaryOperator::Gte, rule! { ">=" }),
            value(BinaryOperator::Lte, rule! { "<=" }),
            value(BinaryOperator::Eq, rule! { "=" }),
            value(BinaryOperator::NotEq, rule! { "<>" | "!=" }),
        )),
        alt((
            value(BinaryOperator::And, rule! { AND }),
            value(BinaryOperator::Or, rule! { OR }),
            value(BinaryOperator::In, rule! { IN }),
            value(BinaryOperator::Nin, rule! { NIN }),
            value(BinaryOperator::Subsetof, rule! { SUBSETOF }),
            value(BinaryOperator::Contains, rule! { CONTAINS }),
        )),
    ))(i)
}

pub fn literal(i: Input) -> IResult<Literal> {
    let string = map(literal_string, Literal::String);
    let boolean = alt((
        value(Literal::Boolean(true), rule! { TRUE }),
        value(Literal::Boolean(false), rule! { FALSE }),
    ));
    let null = value(Literal::Null, rule! { NULL });
    let int = map(literal_i64, Literal::Int64);

    rule!(
        #string
        | #int
        | #boolean
        | #null
    )(i)
}

#[allow(clippy::from_str_radix_10)]
pub fn literal_u64(i: Input) -> IResult<u64> {
    map_res(
        rule! {
            LiteralInteger
        },
        |token| Ok(u64::from_str_radix(token.text(), 10)?),
    )(i)
}

pub fn literal_i64(i: Input) -> IResult<i64> {
    map_res(
        rule! {
            LiteralInteger
        },
        |token| Ok(token.text().parse::<i64>()?),
    )(i)
}

pub fn literal_f64(i: Input) -> IResult<f64> {
    map_res(
        rule! {
            LiteralFloat
        },
        |token| Ok(fast_float::parse(token.text())?),
    )(i)
}

pub fn literal_bool(i: Input) -> IResult<bool> {
    alt((value(true, rule! { TRUE }), value(false, rule! { FALSE })))(i)
}

pub fn literal_string(i: Input) -> IResult<String> {
    map_res(
        rule! {
            QuotedString
        },
        |token| {
            if token
                .text()
                .chars()
                .next()
                .filter(|c| is_string_quote(*c))
                .is_some()
            {
                let str = &token.text()[1..token.text().len() - 1];
                //let unescaped =
                //    unescape(str, '\'').ok_or(ErrorKind::Other("invalid escape or unicode"))?;
                let unescaped = unescape(str, '\'').unwrap();
                Ok(unescaped)
            } else {
                Err(ErrorKind::ExpectToken(QuotedString))
            }
        },
    )(i)
}
