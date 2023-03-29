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

use crate::jsonpath::ast::write_comma_separated_list;
use crate::jsonpath::ast::write_quoted_comma_separated_list;
use crate::jsonpath::ast::Expr;
use std::fmt::Display;
use std::fmt::Formatter;

#[derive(Debug, Clone, PartialEq)]
pub enum Path {
    /// The $ Path
    Root,
    /// The @ Path
    Current,
    /// The .* Path
    DotWildcard,
    /// The ..* Path
    DescentWildcard,
    /// The [*] Path
    BracketWildcard,
    /// The . Field, like `.key`
    DotField(String),
    /// The .. Field, like `..key`
    DescentField(String),
    /// The Object Fields, like `['a','b']`
    ObjectFields(Vec<String>),
    /// The Array Indices, like `[0,1,2]`
    ArrayIndices(Vec<i64>),
    /// The Array Slice, like `[0:1]`, `[-1:]`, `[:2]`, `[0:4:2]`
    ArraySlice {
        start: Option<i64>,
        end: Option<i64>,
        step: Option<i64>,
    },
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
                write!(f, ".")?;
                write!(f, "{field}")?;
            }
            Path::DescentField(field) => {
                write!(f, "..")?;
                write!(f, "{field}")?;
            }
            Path::ObjectFields(fields) => {
                write!(f, "[")?;
                write_quoted_comma_separated_list(f, fields)?;
                write!(f, "]")?;
            }
            Path::ArrayIndices(indices) => {
                write!(f, "[")?;
                write_comma_separated_list(f, indices)?;
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
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PathItem {
    /// The Path
    Path { path: Box<Path> },
    /// The Filter Expression
    FilterExpr { expr: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct JsonPath {
    pub items: Vec<PathItem>,
}

impl Display for JsonPath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for item in &self.items {
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}

impl Display for PathItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PathItem::Path { path } => {
                write!(f, "{path}")?;
            }
            PathItem::FilterExpr { expr } => {
                write!(f, "[?({expr})]")?;
            }
        }
        Ok(())
    }
}
