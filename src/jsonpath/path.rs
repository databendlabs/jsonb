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

use std::fmt::Display;
use std::fmt::Formatter;

/// Represents a set of JSON Path chains.
#[derive(Debug, Clone, PartialEq)]
pub struct JsonPath {
    pub paths: Vec<Path>,
}

/// Represents a valid JSON Path.
#[derive(Debug, Clone, PartialEq)]
pub enum Path {
    /// `$` represents the root node or element.
    Root,
    /// `@` represents the current node or element being processed in the filter expression.
    Current,
    /// `.*` represents selecting all elements in an Array or Object.
    DotWildcard,
    /// `..*` represents recursive selecting all elements in an Array or Object.
    DescentWildcard,
    /// `[*]` represents selecting all elements in an Array or Object.
    BracketWildcard,
    /// `.<name> represents selecting element that matched the name in an Object, like `$.event`.
    DotField(String),
    /// `..<name> represents recursive selecting all elements that matched the name, like `$..event`.
    DescentField(String),
    /// `['<name>'] represents selecting element that matched the name in an Object, like `$['event']`.
    ObjectField(String),
    /// `['<name1>','<name2>',..] represents selecting elements that matched one of the names in an Object, like `$['event', 'author']`.
    ObjectFields(Vec<String>),
    /// `[<index>] represents selecting element specified by the index in an Array, like `$[1]`. Index is 0-based.
    ArrayIndex(i32),
    /// `[<index1>,<index2>,..] represents selecting elements specified by the indices in an Array, like `$[1,2]`.
    ArrayIndices(Vec<i32>),
    /// `[<start>:<end>:<step>] represents selecting elements indexed between start and end with a step in an Array, like `$[0:4:2]`.
    /// If start is omitted, selecting from the first element of the Array, like `$[:3]`.
    /// If end is omitted, selecting from start until the last element of the Array, like `$[1:]`.
    /// If step is not specified, the default value of 1 is used.
    ArraySlice {
        start: Option<i32>,
        end: Option<i32>,
        step: Option<u32>,
    },
    /// `[?(<expression>)]` represents selecting all elements in an object or array that match the filter expression, like `$.book[?(@.price < 10)]`.
    FilterExpr(Box<Expr>),
}

/// Represents a literal value used in filter expression.
#[derive(Debug, Clone, PartialEq)]
pub enum PathValue {
    /// Null value.
    Null,
    /// Boolean value.
    Boolean(bool),
    /// 64-bit unsigned integer.
    UInt64(u64),
    /// 64-bit signed integer.
    Int64(i64),
    /// 64-bit floating point.
    Float64(f64),
    /// UTF-8 string.
    String(String),
}

/// Represents the operators used in filter expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    /// `==` represents left is equal to right.
    Eq,
    /// `!=` represents left is not equal to right.
    NotEq,
    /// `<` represents left is less than right.
    Lt,
    /// `<=` represents left is less or equal to right.
    Lte,
    /// `>` represents left is greater than right.
    Gt,
    /// `>=` represents left is greater than or equal to right.
    Gte,
    /// `=~` represents left matches regular expression, like `[?(@.name =~ /foo.*?/i)]`.
    Match,
    /// `in` represents left exists in right, like `[?(@.size in ['S', 'M'])]`.
    In,
    /// `nin` represents left does not exists in right.
    Nin,
    /// `subsetof` represents left is a subset of right, like `[?(@.sizes subsetof ['S', 'M', 'L'])]`.
    Subsetof,
    /// `anyof` represents left has an intersection with right, like `[?(@.sizes anyof ['M', 'L'])]`.
    Anyof,
    /// `noneof` represents left has no intersection with right, like `[?(@.sizes noneof ['M', 'L'])]`.
    Noneof,
    /// `size` represents size of left (Array or String) should match right.
    Size,
    /// `empty` represents left (Array or String) should be empty or not empty.
    Empty,
}

/// Represents a filter expression used to filter Array or Object.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// JSON Path chains.
    Paths(Vec<Path>),
    /// Literal value.
    Value(Box<PathValue>),
    /// Filter expression that performs a binary operation, returns a boolean value.
    BinaryOp {
        op: BinaryOperator,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}

impl Display for JsonPath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for path in &self.paths {
            write!(f, "{path}")?;
        }
        Ok(())
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Path::Root => {
                write!(f, "$")?;
            }
            Path::Current => {
                write!(f, "@")?;
            }
            Path::DotWildcard => {
                write!(f, ".*")?;
            }
            Path::DescentWildcard => {
                write!(f, "..*")?;
            }
            Path::BracketWildcard => {
                write!(f, "[*]")?;
            }
            Path::DotField(field) => {
                write!(f, ".{field}")?;
            }
            Path::DescentField(field) => {
                write!(f, "..{field}")?;
            }
            Path::ObjectField(field) => {
                write!(f, "['{field}']")?;
            }
            Path::ObjectFields(fields) => {
                write!(f, "[")?;
                for (i, field) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "'{field}'")?;
                }
                write!(f, "]")?;
            }
            Path::ArrayIndex(index) => {
                write!(f, "[{index}]")?;
            }
            Path::ArrayIndices(indices) => {
                write!(f, "[")?;
                for (i, index) in indices.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{index}")?;
                }
                write!(f, "]")?;
            }
            Path::ArraySlice { start, end, step } => {
                write!(f, "[")?;
                if let Some(start) = start {
                    write!(f, "{start}")?;
                }
                write!(f, ":")?;
                if let Some(end) = end {
                    write!(f, "{end}")?;
                }
                if let Some(step) = step {
                    write!(f, ":")?;
                    write!(f, "{step}")?;
                }
                write!(f, "]")?;
            }
            Path::FilterExpr(expr) => {
                write!(f, "[?({expr})]")?;
            }
        }
        Ok(())
    }
}

impl Display for PathValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PathValue::Null => {
                write!(f, "null")
            }
            PathValue::Boolean(v) => {
                if *v {
                    write!(f, "true")
                } else {
                    write!(f, "false")
                }
            }
            PathValue::UInt64(v) => {
                write!(f, "{v}")
            }
            PathValue::Int64(v) => {
                write!(f, "{v}")
            }
            PathValue::Float64(v) => {
                write!(f, "{v}")
            }
            PathValue::String(v) => {
                write!(f, "\'{v}\'")
            }
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Eq => {
                write!(f, "==")
            }
            BinaryOperator::NotEq => {
                write!(f, "!=")
            }
            BinaryOperator::Lt => {
                write!(f, "<")
            }
            BinaryOperator::Lte => {
                write!(f, "<=")
            }
            BinaryOperator::Gt => {
                write!(f, ">")
            }
            BinaryOperator::Gte => {
                write!(f, ">=")
            }
            BinaryOperator::Match => {
                write!(f, "=~")
            }
            BinaryOperator::In => {
                write!(f, "in")
            }
            BinaryOperator::Nin => {
                write!(f, "nin")
            }
            BinaryOperator::Subsetof => {
                write!(f, "subsetOf")
            }
            BinaryOperator::Anyof => {
                write!(f, "anyOf")
            }
            BinaryOperator::Noneof => {
                write!(f, "noneOf")
            }
            BinaryOperator::Size => {
                write!(f, "size")
            }
            BinaryOperator::Empty => {
                write!(f, "empty")
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Paths(paths) => {
                for path in paths {
                    write!(f, "{path}")?;
                }
            }
            Expr::Value(v) => {
                write!(f, "{v}")?;
            }
            Expr::BinaryOp { op, left, right } => {
                write!(f, "{left} {op} {right}")?;
            }
        }
        Ok(())
    }
}
