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

use crate::RawJsonb;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt::Display;
use std::fmt::Formatter;
use std::fmt::Write;

use crate::number::Number;

/// Represents a set of JSON Path chains.
#[derive(Debug, Clone, PartialEq)]
pub struct JsonPath<'a> {
    pub paths: Vec<Path<'a>>,
}

impl JsonPath<'_> {
    pub fn is_predicate(&self) -> bool {
        self.paths.len() == 1 && matches!(self.paths[0], Path::Expr(_))
    }
}

/// Represents a valid JSON Path.
#[derive(Debug, Clone, PartialEq)]
pub enum Path<'a> {
    /// `$` represents the root node or element.
    Root,
    /// `@` represents the current node or element being processed in the filter expression.
    Current,
    /// `.*` represents selecting all elements in an Object.
    DotWildcard,
    /// `.**` represents recursive selecting all elements in Array and Object.
    /// The optional `RecursiveLevel` indicates the seleted levels.
    RecursiveDotWildcard(Option<RecursiveLevel>),
    /// `[*]` represents selecting all elements in an Array.
    BracketWildcard,
    /// `.<name>` represents selecting element that matched the name in an Object, like `$.event`.
    /// The name can also be written as a string literal, allowing the name to contain special characters, like `$." $price"`.
    DotField(Cow<'a, str>),
    /// `:<name>` represents selecting element that matched the name in an Object, like `$:event`.
    ColonField(Cow<'a, str>),
    /// `["<name>"]` represents selecting element that matched the name in an Object, like `$["event"]`.
    ObjectField(Cow<'a, str>),
    /// `[<index1>,<index2>,..]` represents selecting elements specified by the indices in an Array.
    /// There are several forms of index.
    /// 1. A single number representing the 0-based `n-th` element in the Array.
    ///    e.g. `$[0]` represents the first element in an Array.
    /// 2. The keyword `last` represents the last element in the Array,
    ///    and last minus a number represents the n-th element before the last element,
    ///    e.g. `$[last-1]` represents the penultimate element.
    /// 3. The keyword `to` between two numbers represent all elements of a range in an Array,
    ///    e.g. `$[1 to last]` represents all the elements in the Array from the second to the last.
    ///
    /// There can be more than one index, e.g. `$[0, last-1 to last, 5]` represents the first,
    /// the last two, and the sixth element in an Array.
    ArrayIndices(Vec<ArrayIndex>),
    /// `?(<expression>)` represents selecting all elements in an object or array that match the filter expression, like `$.book[?(@.price < 10)]`.
    FilterExpr(Box<Expr<'a>>),
    /// `<expression>` standalone filter expression, like `$.book[*].price > 10`,
    /// and arithmetic expression, like `-$.a[*]` or `$.a + 3`
    Expr(Box<Expr<'a>>),
}

/// Represents the single index in an Array.
#[derive(Debug, Clone, PartialEq)]
pub enum Index {
    /// The 0-based index in an Array.
    Index(i32),
    /// The last n-th index in an Array.
    LastIndex(i32),
}

/// Represents the index in an Array.
#[derive(Debug, Clone, PartialEq)]
pub enum ArrayIndex {
    /// The single number index.
    Index(Index),
    /// The range index between two number.
    Slice((Index, Index)),
}

impl ArrayIndex {
    /// Converts an `ArrayIndex` to a `HashSet` of indices that should be selected from an Array.
    ///
    /// # Arguments
    ///
    /// * `length` - The length of the array.
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` containing the indices to select.
    pub fn to_indices(&self, length: usize) -> HashSet<usize> {
        // `i64` arithmetic avoids overflow for extreme `i32` indices.
        let length = length as i64;

        let mut indices = HashSet::new();
        match self {
            ArrayIndex::Index(idx) => {
                let idx = Self::convert_index(idx, length);
                if (0..length).contains(&idx) {
                    indices.insert(idx as usize);
                }
            }
            ArrayIndex::Slice((start, end)) => {
                // Clamp to the array bounds; an empty range selects nothing.
                let start_idx = Self::convert_index(start, length).max(0);
                let end_idx = Self::convert_index(end, length).min(length - 1);
                for idx in start_idx..=end_idx {
                    indices.insert(idx as usize);
                }
            }
        }
        indices
    }

    fn convert_index(index: &Index, length: i64) -> i64 {
        match index {
            Index::Index(idx) => i64::from(*idx),
            Index::LastIndex(idx) => length + i64::from(*idx) - 1,
        }
    }
}

/// Represents the end level in hierarchical structure.
#[derive(Debug, Clone, PartialEq)]
pub enum RecursiveLevelEnd {
    /// Specifies the end of the recursive level.
    Index(u8),
    /// Specifies that the recursion should continue to the last level.
    Last,
}

/// Represents the selected levels in hierarchical structure.
#[derive(Debug, Clone, PartialEq)]
pub struct RecursiveLevel {
    /// The starting level of the recursive level.
    pub start: u8,
    /// The optional end of the recursive level. If None, the level applies only to the start level.
    pub end: Option<RecursiveLevelEnd>,
}

impl RecursiveLevel {
    /// Checks if the current level matches the recursive level.
    ///
    /// # Arguments
    ///
    /// * `level` - The current level in hierarchical structure.
    ///
    /// # Returns
    ///
    /// A tuple (is_match, should_continue):
    /// - is_match: Indicates whether the current level matches the level criteria.
    /// - should_continue: Indicates whether to continue processing data at the next level.
    pub fn check_recursive_level(&self, level: u8) -> (bool, bool) {
        if let Some(end) = &self.end {
            match end {
                RecursiveLevelEnd::Index(end) => {
                    if level < self.start && self.start <= *end {
                        (false, true)
                    } else if level >= self.start && level <= *end {
                        (true, true)
                    } else {
                        (false, false)
                    }
                }
                RecursiveLevelEnd::Last => {
                    if level < self.start {
                        (false, true)
                    } else {
                        (true, true)
                    }
                }
            }
        } else if level < self.start {
            (false, true)
        } else if level == self.start {
            (true, false)
        } else {
            (false, false)
        }
    }
}

/// Represents a literal value used in filter expression.
#[derive(Debug, Clone)]
pub enum PathValue<'a> {
    /// Null value.
    Null,
    /// Boolean value.
    Boolean(bool),
    /// Number value.
    Number(Number),
    /// UTF-8 string.
    String(Cow<'a, str>),
    /// RawJsonb (Array or Object) value, can't be used for calculation.
    Raw(RawJsonb<'a>),
}

impl PartialOrd for PathValue<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (PathValue::Null, PathValue::Null) => Some(Ordering::Equal),
            (PathValue::Boolean(l), PathValue::Boolean(r)) => l.partial_cmp(r),
            (PathValue::Number(l), PathValue::Number(r)) => l.partial_cmp(r),
            (PathValue::String(l), PathValue::String(r)) => l.partial_cmp(r),
            (_, _) => None,
        }
    }
}

impl PartialEq for PathValue<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

/// Represents the operators used in filter expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    /// `&&` represents logical And operation.
    And,
    /// `||` represents logical Or operation.
    Or,
    /// `==` represents left is equal to right.
    Eq,
    /// `!=` and `<>` represents left is not equal to right.
    NotEq,
    /// `<` represents left is less than right.
    Lt,
    /// `<=` represents left is less or equal to right.
    Lte,
    /// `>` represents left is greater than right.
    Gt,
    /// `>=` represents left is greater than or equal to right.
    Gte,
    /// `starts with` represents right is an initial substring of left.
    StartsWith,
    /// `Add` represents binary arithmetic + operation.
    Add,
    /// `Subtract` represents binary arithmetic - operation.
    Subtract,
    /// `Multiply` represents binary arithmetic * operation.
    Multiply,
    /// `Divide` represents binary arithmetic / operation.
    Divide,
    /// `Modulo` represents binary arithmetic % operation.
    Modulo,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    /// `Add` represents unary arithmetic + operation.
    Add,
    /// `Subtract` represents unary arithmetic - operation.
    Subtract,
}

/// Represents a filter expression used to filter Array or Object.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<'a> {
    /// JSON Path chains.
    Paths(Vec<Path<'a>>),
    /// Literal value.
    Value(Box<PathValue<'a>>),
    /// Filter expression that performs a binary operation, returns a boolean value,
    /// Or arithmetic expression that performs an arithmetic operation, returns a number value.
    BinaryOp {
        op: BinaryOperator,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
    },
    /// Unary expression that performs an arithmetic operation.
    UnaryOp {
        op: UnaryOperator,
        operand: Box<Expr<'a>>,
    },
    /// Filter function, returns a boolean value.
    ExistsFunc(Vec<Path<'a>>),
}

impl Display for JsonPath<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for path in &self.paths {
            write!(f, "{path}")?;
        }
        Ok(())
    }
}

impl Display for Index {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Index::Index(idx) => {
                write!(f, "{idx}")?;
            }
            Index::LastIndex(idx) => {
                write!(f, "last")?;
                match idx.cmp(&0) {
                    Ordering::Greater => {
                        write!(f, "+{idx}")?;
                    }
                    Ordering::Less => {
                        write!(f, "{idx}")?;
                    }
                    Ordering::Equal => {}
                }
            }
        }
        Ok(())
    }
}

impl Display for ArrayIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ArrayIndex::Index(idx) => {
                write!(f, "{idx}")?;
            }
            ArrayIndex::Slice((start, end)) => {
                write!(f, "{start} to {end}")?;
            }
        }
        Ok(())
    }
}

impl Display for RecursiveLevel {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(end_index) = &self.end {
            match end_index {
                RecursiveLevelEnd::Index(end) => {
                    write!(f, "{} to {}", self.start, end)?;
                }
                RecursiveLevelEnd::Last => {
                    write!(f, "{} to last", self.start)?;
                }
            }
        } else {
            write!(f, "{}", self.start)?;
        }
        Ok(())
    }
}

impl Display for Path<'_> {
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
            Path::RecursiveDotWildcard(level_opt) => {
                write!(f, ".**")?;
                if let Some(level) = level_opt {
                    write!(f, "{{")?;
                    write!(f, "{level}")?;
                    write!(f, "}}")?;
                }
            }
            Path::BracketWildcard => {
                write!(f, "[*]")?;
            }
            Path::ColonField(field) => {
                f.write_char(':')?;
                write_name(f, field, false)?;
            }
            Path::DotField(field) => {
                f.write_char('.')?;
                write_name(f, field, false)?;
            }
            Path::ObjectField(field) => {
                f.write_char('[')?;
                write_quoted_str(f, field)?;
                f.write_char(']')?;
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
            Path::FilterExpr(expr) => {
                write!(f, "?({expr})")?;
            }
            Path::Expr(expr) => {
                write!(f, "{expr}")?;
            }
        }
        Ok(())
    }
}

impl Display for PathValue<'_> {
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
            PathValue::Number(v) => {
                write!(f, "{v}")
            }
            PathValue::String(v) => write_quoted_str(f, v),
            PathValue::Raw(v) => {
                write!(f, "{}", v.to_string())
            }
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::And => {
                write!(f, "&&")
            }
            BinaryOperator::Or => {
                write!(f, "||")
            }
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
            BinaryOperator::StartsWith => {
                write!(f, "starts with")
            }
            BinaryOperator::Add => {
                write!(f, "+")
            }
            BinaryOperator::Subtract => {
                write!(f, "-")
            }
            BinaryOperator::Multiply => {
                write!(f, "*")
            }
            BinaryOperator::Divide => {
                write!(f, "/")
            }
            BinaryOperator::Modulo => {
                write!(f, "%")
            }
        }
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Add => {
                write!(f, "+")
            }
            UnaryOperator::Subtract => {
                write!(f, "-")
            }
        }
    }
}

impl Display for Expr<'_> {
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
                if left.needs_parens(op, false) {
                    write!(f, "({left})")?;
                } else {
                    write!(f, "{left}")?;
                }
                write!(f, " {op} ")?;
                if right.needs_parens(op, true) {
                    write!(f, "({right})")?;
                } else {
                    write!(f, "{right}")?;
                }
            }
            Expr::UnaryOp { op, operand } => {
                write!(f, "{}{}", op, operand)?;
            }
            Expr::ExistsFunc(paths) => {
                f.write_str("exists(")?;
                for path in paths {
                    write!(f, "{path}")?;
                }
                f.write_str(")")?;
            }
        }
        Ok(())
    }
}

impl Expr<'_> {
    /// Returns whether this expression, an operand of `parent`, must be
    /// parenthesized for the formatted text to parse back to the same tree.
    ///
    /// The parser gives `&&` higher precedence than `||` and reads both left to
    /// right, so `a || b || c` is `(a || b) || c`. Parenthesizing only where the
    /// tree differs from that keeps long chains flat; wrapping every logical
    /// operand turned a chain of 100 `||` into 100 nested parentheses, past the
    /// parser's nesting limit.
    fn needs_parens(&self, parent: &BinaryOperator, is_right: bool) -> bool {
        let Expr::BinaryOp { op: child, .. } = self else {
            return false;
        };
        let is_logical =
            |op: &BinaryOperator| matches!(op, BinaryOperator::And | BinaryOperator::Or);
        if !is_logical(child) {
            return false;
        }
        match parent {
            // `&&` binds tighter, so it never needs parentheses under `||`.
            BinaryOperator::Or => child == &BinaryOperator::Or && is_right,
            BinaryOperator::And => child == &BinaryOperator::Or || is_right,
            // Comparison and arithmetic operands are never logical expressions
            // when parsed, so keep the parentheses that mark such a tree.
            _ => true,
        }
    }
}

/// Characters that end an unquoted name in the JSONPath and key-path grammars.
const RAW_NAME_DELIMITERS: &str = " ,.:{}[]()?@$|<>!=+-*/%\"'";

/// Writes `s` as a double-quoted string literal that the path parsers read back
/// as the same string.
pub(crate) fn write_quoted_str(f: &mut impl Write, s: &str) -> std::fmt::Result {
    f.write_char('"')?;
    for c in s.chars() {
        match c {
            '"' => f.write_str("\\\"")?,
            '\\' => f.write_str("\\\\")?,
            c if c.is_control() => write!(f, "\\u{:04X}", u32::from(c))?,
            c => f.write_char(c)?,
        }
    }
    f.write_char('"')
}

/// Returns whether `name` cannot be written as an unquoted name as is.
///
/// Such characters would end the name, be skipped as whitespace, or start a
/// different token. With `leading_digit_is_index`, a leading digit also counts,
/// so that a key-path name is not read back as an array index.
fn needs_escaping(c: char, first: bool, leading_digit_is_index: bool) -> bool {
    c == '\\'
        || c.is_whitespace()
        || c.is_control()
        || RAW_NAME_DELIMITERS.contains(c)
        || (leading_digit_is_index && first && c.is_ascii_digit())
}

/// Writes `name` unquoted, escaping as `\uXXXX` any character that would not
/// read back unchanged.
pub(crate) fn write_raw_name(
    f: &mut impl Write,
    name: &str,
    leading_digit_is_index: bool,
) -> std::fmt::Result {
    for (i, c) in name.chars().enumerate() {
        if needs_escaping(c, i == 0, leading_digit_is_index) {
            write!(f, "\\u{:04X}", u32::from(c))?;
        } else {
            f.write_char(c)?;
        }
    }
    Ok(())
}

/// Writes `name` unquoted when it reads back unchanged, and quoted otherwise.
pub(crate) fn write_name(
    f: &mut impl Write,
    name: &str,
    leading_digit_is_index: bool,
) -> std::fmt::Result {
    let plain = !name.is_empty()
        && !name
            .chars()
            .enumerate()
            .any(|(i, c)| needs_escaping(c, i == 0, leading_digit_is_index));
    if plain {
        f.write_str(name)
    } else {
        write_quoted_str(f, name)
    }
}
