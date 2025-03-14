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
pub(crate) const NULL_LEVEL: u8 = 7;
pub(crate) const ARRAY_LEVEL: u8 = 6;
pub(crate) const OBJECT_LEVEL: u8 = 5;
pub(crate) const STRING_LEVEL: u8 = 4;
pub(crate) const NUMBER_LEVEL: u8 = 3;
pub(crate) const TRUE_LEVEL: u8 = 2;
pub(crate) const FALSE_LEVEL: u8 = 1;

pub(crate) const TYPE_STRING: &str = "string";
pub(crate) const TYPE_NULL: &str = "null";
pub(crate) const TYPE_BOOLEAN: &str = "boolean";
pub(crate) const TYPE_NUMBER: &str = "number";
pub(crate) const TYPE_ARRAY: &str = "array";
pub(crate) const TYPE_OBJECT: &str = "object";
