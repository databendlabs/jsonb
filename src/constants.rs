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

// JSON text constants
pub(crate) const UNICODE_LEN: usize = 4;

/// Maximum nesting depth of arrays and objects when parsing JSON text or
/// walking JSONB recursively. A level takes up to about 1.5 KiB of stack in
/// release builds, so 512 levels fit in tokio's default 2 MiB thread stack.
pub(crate) const MAX_NESTING_DEPTH: usize = 512;

/// Maximum parenthesis depth in a JSONPath expression. The JSONPath parser
/// uses much more stack per level than data traversal.
pub(crate) const MAX_JSON_PATH_DEPTH: usize = 64;

/// Maximum number of `&&` and `||` operators in a JSONPath expression. Each
/// one adds a level to the parsed tree, which is processed recursively.
/// The parser counts them because unquoted field names may contain `&&`.
pub(crate) const MAX_JSON_PATH_LOGICAL_OPERATORS: usize = 256;

/// Maximum work units for one JSONPath evaluation. Each selected item, filter
/// value, node visited by `.**` and compared pair costs one unit; without a
/// limit, chained `.**` steps grow combinatorially with the nesting depth.
pub(crate) const MAX_JSON_PATH_ITEMS: usize = 1_000_000;

/// Bytes one JSONPath evaluation may copy beyond the document size. A value
/// is copied once per selected ancestor, so `$.**.**` on 500 nested arrays
/// around a 1 KiB string copies about 300 MB. The budget is this plus the
/// document size, so any single value can be copied at least once.
pub(crate) const MAX_JSON_PATH_EXTRA_COPY_BYTES: usize = 32 * 1024 * 1024;

/// Returns the nesting depth after entering one more array or object.
///
/// # Errors
///
/// Returns `Error::RecursionLimitExceeded` if the new depth would exceed
/// [`MAX_NESTING_DEPTH`].
#[inline]
pub(crate) fn enter_container(depth: usize) -> crate::error::Result<usize> {
    if depth >= MAX_NESTING_DEPTH {
        Err(crate::Error::RecursionLimitExceeded)
    } else {
        Ok(depth + 1)
    }
}

// JSON text escape characters constants
pub(crate) const BS: char = '\x5C'; // \\ Backslash
pub(crate) const QU: char = '\x22'; // \" Double quotation mark
pub(crate) const SD: char = '\x2F'; // \/ Slash or divide
pub(crate) const BB: char = '\x08'; // \b Backspace
pub(crate) const FF: char = '\x0C'; // \f Formfeed Page Break
pub(crate) const NN: char = '\x0A'; // \n Newline
pub(crate) const RR: char = '\x0D'; // \r Carriage Return
pub(crate) const TT: char = '\x09'; // \t Horizontal Tab

// JSONB value compare level
pub(crate) const NULL_LEVEL: u8 = 8;
pub(crate) const ARRAY_LEVEL: u8 = 7;
pub(crate) const OBJECT_LEVEL: u8 = 6;
pub(crate) const STRING_LEVEL: u8 = 5;
pub(crate) const NUMBER_LEVEL: u8 = 4;
pub(crate) const TRUE_LEVEL: u8 = 3;
pub(crate) const FALSE_LEVEL: u8 = 2;
pub(crate) const EXTENSION_LEVEL: u8 = 1;

pub(crate) const TYPE_STRING: &str = "STRING";
pub(crate) const TYPE_NULL: &str = "NULL_VALUE";
pub(crate) const TYPE_BOOLEAN: &str = "BOOLEAN";
pub(crate) const TYPE_INTEGER: &str = "INTEGER";
pub(crate) const TYPE_ARRAY: &str = "ARRAY";
pub(crate) const TYPE_OBJECT: &str = "OBJECT";
pub(crate) const TYPE_DECIMAL: &str = "DECIMAL";
pub(crate) const TYPE_DOUBLE: &str = "DOUBLE";
pub(crate) const TYPE_BINARY: &str = "BINARY";
pub(crate) const TYPE_DATE: &str = "DATE";
pub(crate) const TYPE_TIMESTAMP: &str = "TIMESTAMP";
pub(crate) const TYPE_TIMESTAMP_TZ: &str = "TIMESTAMP_TZ";
pub(crate) const TYPE_INTERVAL: &str = "INTERVAL";

pub(crate) const MAX_DECIMAL64_PRECISION: usize = 18;
pub(crate) const MAX_DECIMAL128_PRECISION: usize = 38;
pub(crate) const MAX_DECIMAL256_PRECISION: usize = 76;

pub(crate) const UINT64_MIN: i128 = 0i128;
pub(crate) const UINT64_MAX: i128 = 18_446_744_073_709_551_615i128;
pub(crate) const INT64_MIN: i128 = -9_223_372_036_854_775_808i128;
pub(crate) const INT64_MAX: i128 = 9_223_372_036_854_775_807i128;
pub(crate) const DECIMAL64_MIN: i128 = -999_999_999_999_999_999i128;
pub(crate) const DECIMAL64_MAX: i128 = 999_999_999_999_999_999i128;
pub(crate) const DECIMAL128_MIN: i128 = -99_999_999_999_999_999_999_999_999_999_999_999_999i128;
pub(crate) const DECIMAL128_MAX: i128 = 99_999_999_999_999_999_999_999_999_999_999_999_999i128;

pub(crate) const NUMBER_STRUCT_TOKEN: &str = "$jsonb::private::Number";
pub(crate) const NUMBER_STRUCT_FIELD_SCALE: &str = "$jsonb::private::Number::Scale";
pub(crate) const NUMBER_STRUCT_FIELD_VALUE: &str = "$jsonb::private::Number::Value";
pub(crate) const NUMBER_STRUCT_FIELD_HIGH_VALUE: &str = "$jsonb::private::Number::High_Value";
pub(crate) const NUMBER_STRUCT_FIELD_LOW_VALUE: &str = "$jsonb::private::Number::Low_Value";
