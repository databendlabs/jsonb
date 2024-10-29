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
use std::fmt::Debug;

use crate::array_length;
use crate::ser::Encoder;
use crate::Value;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LazyValue<'a> {
    Value(Value<'a>),
    // Raw JSONB bytes
    Raw(Cow<'a, [u8]>),
}

impl<'a> LazyValue<'a> {
    /// Serialize the JSONB Value into a byte stream.
    pub fn write_to_vec(&self, buf: &mut Vec<u8>) {
        match self {
            LazyValue::Value(v) => {
                let mut encoder = Encoder::new(buf);
                encoder.encode(v)
            }
            LazyValue::Raw(v) => buf.extend_from_slice(v),
        };
    }

    /// Serialize the JSONB Value into a byte stream.
    pub fn to_vec(&self) -> Vec<u8> {
        match self {
            LazyValue::Value(value) => {
                let mut buf = Vec::new();
                value.write_to_vec(&mut buf);
                buf
            }
            LazyValue::Raw(cow) => cow.to_vec(),
        }
    }

    // TODO migrate more functions to be methods of LazyValue
    pub fn array_length(&self) -> Option<usize> {
        match self {
            LazyValue::Value(Value::Array(arr)) => Some(arr.len()),
            LazyValue::Raw(cow) => array_length(cow.as_ref()),
            _ => None,
        }
    }

    pub fn to_value(&'a self) -> Cow<Value<'a>> {
        match self {
            LazyValue::Value(v) => Cow::Borrowed(v),
            LazyValue::Raw(v) => Cow::Owned(crate::from_slice(v.as_ref()).unwrap()),
        }
    }
}

impl<'a> From<Value<'a>> for LazyValue<'a> {
    fn from(value: Value<'a>) -> Self {
        LazyValue::Value(value)
    }
}
