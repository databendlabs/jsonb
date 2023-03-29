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

use std::cmp::Ordering;
use std::fmt::Display;
use std::fmt::Formatter;

use crate::jsonpath::ast::Path;
use crate::jsonpath::exception::Span;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Json paths like `$.price`
    Paths { span: Span, paths: Vec<Path> },
    /// A literal value, such as string, number, bool or NULL
    Literal { span: Span, lit: Literal },
    /// Binary operation
    BinaryOp {
        span: Span,
        op: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// Unary operation
    UnaryOp {
        span: Span,
        op: UnaryOperator,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    UInt64(u64),
    Int64(i64),
    Float(f64),
    // Quoted string literal value
    String(String),
    Boolean(bool),
    Null,
}

impl Literal {
    pub(crate) fn neg(&self) -> Self {
        match self {
            Literal::UInt64(u) => match u.cmp(&(i64::MAX as u64 + 1)) {
                Ordering::Greater => todo!(),
                Ordering::Less => Literal::Int64(-(*u as i64)),
                Ordering::Equal => Literal::Int64(i64::MIN),
            },
            Literal::Float(f) => Literal::Float(-*f),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    Gt,
    Lt,
    Gte,
    Lte,
    Eq,
    NotEq,
    And,
    Or,
    In,
    Nin,
    Subsetof,
    Contains,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOperator {
    Plus,
    Minus,
    Not,
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Literal { span, .. } | Expr::BinaryOp { span, .. } => *span,
            Expr::UnaryOp { span, .. } => *span,
            Expr::Paths { span, .. } => *span,
        }
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Plus => {
                write!(f, "+")
            }
            UnaryOperator::Minus => {
                write!(f, "-")
            }
            UnaryOperator::Not => {
                write!(f, "NOT")
            }
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Plus => {
                write!(f, " + ")
            }
            BinaryOperator::Minus => {
                write!(f, " - ")
            }
            BinaryOperator::Multiply => {
                write!(f, " * ")
            }
            BinaryOperator::Divide => {
                write!(f, " / ")
            }
            BinaryOperator::Modulo => {
                write!(f, " % ")
            }
            BinaryOperator::Gt => {
                write!(f, " > ")
            }
            BinaryOperator::Lt => {
                write!(f, " < ")
            }
            BinaryOperator::Gte => {
                write!(f, " >= ")
            }
            BinaryOperator::Lte => {
                write!(f, " <= ")
            }
            BinaryOperator::Eq => {
                write!(f, " = ")
            }
            BinaryOperator::NotEq => {
                write!(f, " <> ")
            }
            BinaryOperator::And => {
                write!(f, " AND ")
            }
            BinaryOperator::Or => {
                write!(f, " OR ")
            }
            BinaryOperator::In => {
                write!(f, " IN ")
            }
            BinaryOperator::Nin => {
                write!(f, " NIN ")
            }
            BinaryOperator::Subsetof => {
                write!(f, " SUBSETOF ")
            }
            BinaryOperator::Contains => {
                write!(f, " CONTAINS ")
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::UInt64(val) => {
                write!(f, "{val}")
            }
            Literal::Int64(val) => {
                write!(f, "{val}")
            }
            Literal::Float(val) => {
                write!(f, "{val}")
            }
            Literal::String(val) => {
                write!(f, "\'{val}\'")
            }
            Literal::Boolean(val) => {
                if *val {
                    write!(f, "TRUE")
                } else {
                    write!(f, "FALSE")
                }
            }
            Literal::Null => {
                write!(f, "NULL")
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Literal { lit, .. } => {
                write!(f, "{lit}")?;
            }
            Expr::Paths { paths, .. } => {
                for path in paths {
                    write!(f, "{path}")?;
                }
            }
            Expr::BinaryOp {
                op, left, right, ..
            } => {
                write!(f, "{}", left)?;
                write!(f, "{}", op)?;
                write!(f, "{}", right)?;
            }
            Expr::UnaryOp { op, expr, .. } => {
                write!(f, "{}", op)?;
                write!(f, "{}", expr)?;
            }
        }

        Ok(())
    }
}
