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
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::mem::discriminant;

use rand::distr::Alphanumeric;
use rand::distr::SampleString;
use rand::rng;
use rand::Rng;

use super::extension::Date;
use super::extension::Interval;
use super::extension::Timestamp;
use super::extension::TimestampTz;
use super::number::Number;
use crate::core::Encoder;

pub type Object<'a> = BTreeMap<String, Value<'a>>;

// JSONB value
#[derive(Clone, PartialEq, Default, Eq)]
pub enum Value<'a> {
    #[default]
    Null,
    Bool(bool),
    String(Cow<'a, str>),
    Number(Number),
    Binary(&'a [u8]),
    Date(Date),
    Timestamp(Timestamp),
    TimestampTz(TimestampTz),
    Interval(Interval),
    Array(Vec<Value<'a>>),
    Object(Object<'a>),
}

impl Debug for Value<'_> {
    fn fmt(&self, formatter: &mut Formatter) -> std::fmt::Result {
        match *self {
            Value::Null => formatter.debug_tuple("Null").finish(),
            Value::Bool(v) => formatter.debug_tuple("Bool").field(&v).finish(),
            Value::Number(ref v) => Debug::fmt(v, formatter),
            Value::String(ref v) => formatter.debug_tuple("String").field(v).finish(),
            Value::Binary(ref v) => formatter.debug_tuple("Binary").field(v).finish(),
            Value::Date(ref v) => formatter.debug_tuple("Date").field(v).finish(),
            Value::Timestamp(ref v) => formatter.debug_tuple("Timestamp").field(v).finish(),
            Value::TimestampTz(ref v) => formatter.debug_tuple("TimestampTz").field(v).finish(),
            Value::Interval(ref v) => formatter.debug_tuple("Interval").field(v).finish(),
            Value::Array(ref v) => {
                formatter.write_str("Array(")?;
                Debug::fmt(v, formatter)?;
                formatter.write_str(")")
            }
            Value::Object(ref v) => {
                formatter.write_str("Object(")?;
                Debug::fmt(v, formatter)?;
                formatter.write_str(")")
            }
        }
    }
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Null => write!(f, "null"),
            Value::Bool(v) => {
                if *v {
                    write!(f, "true")
                } else {
                    write!(f, "false")
                }
            }
            Value::Number(ref v) => write!(f, "{}", v),
            Value::String(ref v) => {
                write!(f, "{:?}", v)
            }
            Value::Binary(v) => {
                write!(f, "\"")?;
                for c in *v {
                    write!(f, "{c:02X}")?;
                }
                write!(f, "\"")?;
                Ok(())
            }
            Value::Date(v) => {
                write!(f, "\"{}\"", v)
            }
            Value::Timestamp(v) => {
                write!(f, "\"{}\"", v)
            }
            Value::TimestampTz(v) => {
                write!(f, "\"{}\"", v)
            }
            Value::Interval(v) => {
                write!(f, "\"{}\"", v)
            }
            Value::Array(ref vs) => {
                write!(f, "[")?;
                for (i, v) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Value::Object(ref vs) => {
                write!(f, "{{")?;
                for (i, (k, v)) in vs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "\"")?;
                    write!(f, "{k}")?;
                    write!(f, "\"")?;
                    write!(f, ":")?;
                    write!(f, "{v}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl<'a> Value<'a> {
    pub fn is_scalar(&self) -> bool {
        !self.is_array() && !self.is_object()
    }

    pub fn is_object(&self) -> bool {
        matches!(self, Value::Object(_v))
    }

    pub fn as_object(&self) -> Option<&Object<'a>> {
        match self {
            Value::Object(ref obj) => Some(obj),
            _ => None,
        }
    }

    pub fn is_array(&self) -> bool {
        matches!(self, Value::Array(_v))
    }

    pub fn as_array(&self) -> Option<&Vec<Value<'a>>> {
        match self {
            Value::Array(ref array) => Some(array),
            _ => None,
        }
    }

    pub fn is_string(&self) -> bool {
        self.as_str().is_some()
    }

    pub fn as_str(&self) -> Option<&Cow<'_, str>> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_number(&self) -> bool {
        matches!(self, Value::Number(_))
    }

    pub fn as_number(&self) -> Option<&Number> {
        match self {
            Value::Number(n) => Some(n),
            _ => None,
        }
    }

    pub fn is_i64(&self) -> bool {
        self.as_i64().is_some()
    }

    pub fn is_u64(&self) -> bool {
        self.as_u64().is_some()
    }

    pub fn is_f64(&self) -> bool {
        self.as_f64().is_some()
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::Number(n) => n.as_i64(),
            _ => None,
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Value::Number(n) => n.as_u64(),
            _ => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::Number(n) => n.as_f64(),
            _ => None,
        }
    }

    pub fn is_boolean(&self) -> bool {
        matches!(self, Value::Bool(_v))
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(v) => Some(*v),
            _ => None,
        }
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn as_null(&self) -> Option<()> {
        match self {
            Value::Null => Some(()),
            _ => None,
        }
    }

    pub fn is_binary(&self) -> bool {
        matches!(self, Value::Binary(_v))
    }

    pub fn as_binary(&self) -> Option<&[u8]> {
        match self {
            Value::Binary(v) => Some(v),
            _ => None,
        }
    }

    pub fn is_date(&self) -> bool {
        matches!(self, Value::Date(_v))
    }

    pub fn as_date(&self) -> Option<&Date> {
        match self {
            Value::Date(v) => Some(v),
            _ => None,
        }
    }

    pub fn is_timestamp(&self) -> bool {
        matches!(self, Value::Timestamp(_v))
    }

    pub fn as_timestamp(&self) -> Option<&Timestamp> {
        match self {
            Value::Timestamp(v) => Some(v),
            _ => None,
        }
    }

    pub fn is_timestamp_tz(&self) -> bool {
        matches!(self, Value::TimestampTz(_v))
    }

    pub fn as_timestamp_tz(&self) -> Option<&TimestampTz> {
        match self {
            Value::TimestampTz(v) => Some(v),
            _ => None,
        }
    }

    pub fn is_interval(&self) -> bool {
        matches!(self, Value::Interval(_v))
    }

    pub fn as_interval(&self) -> Option<&Interval> {
        match self {
            Value::Interval(v) => Some(v),
            _ => None,
        }
    }

    /// Serialize the JSONB Value into a byte stream.
    pub fn write_to_vec(&self, buf: &mut Vec<u8>) {
        let mut encoder = Encoder::new(buf);
        encoder.encode(self);
    }

    /// Serialize the JSONB Value into a byte stream.
    pub fn to_vec(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write_to_vec(&mut buf);
        buf
    }

    pub fn get_by_name_ignore_case(&self, name: &str) -> Option<&Value<'a>> {
        match self {
            Value::Object(obj) => match obj.get(name) {
                Some(val) => Some(val),
                None => {
                    for key in obj.keys() {
                        if name.eq_ignore_ascii_case(key) {
                            return obj.get(key);
                        }
                    }
                    None
                }
            },
            _ => None,
        }
    }

    pub fn array_length(&self) -> Option<usize> {
        match self {
            Value::Array(arr) => Some(arr.len()),
            _ => None,
        }
    }

    pub fn object_keys(&self) -> Option<Value<'a>> {
        match self {
            Value::Object(obj) => {
                let mut keys = Vec::with_capacity(obj.len());
                for k in obj.keys() {
                    keys.push(k.clone().into());
                }
                Some(Value::Array(keys))
            }
            _ => None,
        }
    }

    pub fn eq_variant(&self, other: &Value) -> bool {
        discriminant(self) == discriminant(other)
    }

    /// generate random JSONB value
    pub fn rand_value() -> Value<'static> {
        let mut rng = rng();
        let val = match rng.random_range(0..=2) {
            0 => {
                let len = rng.random_range(0..=5);
                let mut values = Vec::with_capacity(len);
                for _ in 0..len {
                    values.push(Self::rand_scalar_value());
                }
                Value::Array(values)
            }
            1 => {
                let len = rng.random_range(0..=5);
                let mut obj = Object::new();
                for _ in 0..len {
                    let k = Alphanumeric.sample_string(&mut rng, 5);
                    let v = Self::rand_scalar_value();
                    obj.insert(k, v);
                }
                Value::Object(obj)
            }
            _ => Self::rand_scalar_value(),
        };
        val
    }

    fn rand_scalar_value() -> Value<'static> {
        let mut rng = rng();
        let val = match rng.random_range(0..=3) {
            0 => {
                let v = rng.random_bool(0.5);
                Value::Bool(v)
            }
            1 => {
                let s = Alphanumeric.sample_string(&mut rng, 5);
                Value::String(Cow::from(s))
            }
            2 => match rng.random_range(0..=2) {
                0 => {
                    let n: u64 = rng.random_range(0..=100000);
                    Value::Number(Number::UInt64(n))
                }
                1 => {
                    let n: i64 = rng.random_range(-100000..=100000);
                    Value::Number(Number::Int64(n))
                }
                _ => {
                    let n: f64 = rng.random_range(-4000.0..1.3e5);
                    Value::Number(Number::Float64(n))
                }
            },
            _ => Value::Null,
        };
        val
    }
}
