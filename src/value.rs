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

use crate::core::JsonbItemType;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::mem::discriminant;

use crate::ExtensionValue;
use rand::distr::Alphanumeric;
use rand::distr::SampleString;
use rand::rng;
use rand::Rng;

use crate::core::Encoder;
use crate::Date;
use crate::Decimal128;
use crate::Decimal256;
use crate::Decimal64;
use crate::Interval;
use crate::Number;
use crate::Timestamp;
use crate::TimestampTz;

pub type Object<'a> = BTreeMap<String, Value<'a>>;

/// Represents a JSON or extended JSON value.
///
/// This enum supports both standard JSON types (Null, Bool, String, Number, Array, Object)
/// and extended types for specialized data representation (Binary, Date, Timestamp, etc.).
/// The extended types provide additional functionality beyond the JSON specification,
/// making this implementation more suitable for database applications and other
/// systems requiring richer data type support.
#[derive(Clone, Default)]
pub enum Value<'a> {
    /// Represents a JSON null value
    #[default]
    Null,
    /// Represents a JSON boolean value (true or false)
    Bool(bool),
    /// Represents a JSON string value
    String(Cow<'a, str>),
    /// Represents a JSON number value with various internal representations
    Number(Number),
    /// Extended type: Represents binary data not supported in standard JSON
    /// Useful for storing raw bytes, images, or other binary content
    Binary(&'a [u8]),
    /// Extended type: Represents a calendar date (year, month, day)
    /// Stored as days since epoch for efficient comparison and manipulation
    Date(Date),
    /// Extended type: Represents a timestamp without timezone information
    /// Stored as microseconds since epoch
    Timestamp(Timestamp),
    /// Extended type: Represents a timestamp with timezone information
    /// Includes both timestamp and timezone offset
    TimestampTz(TimestampTz),
    /// Extended type: Represents a time interval or duration
    /// Useful for time difference calculations and scheduling
    Interval(Interval),
    /// Represents a JSON array of values
    Array(Vec<Value<'a>>),
    /// Represents a JSON object as key-value pairs
    Object(Object<'a>),
}

impl Eq for Value<'_> {}

impl PartialEq for Value<'_> {
    fn eq(&self, other: &Self) -> bool {
        let result = self.cmp(other);
        result == Ordering::Equal
    }
}

impl PartialOrd for Value<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_type = self.jsonb_item_type();
        let other_type = other.jsonb_item_type();

        if let Some(ord) = self_type.partial_cmp(&other_type) {
            return ord;
        }

        match (self, other) {
            (Value::Null, Value::Null) => Ordering::Equal,
            (Value::Bool(v1), Value::Bool(v2)) => v1.cmp(v2),
            (Value::Number(v1), Value::Number(v2)) => v1.cmp(v2),
            (Value::String(v1), Value::String(v2)) => v1.cmp(v2),
            (Value::Array(arr1), Value::Array(arr2)) => {
                for (v1, v2) in arr1.iter().zip(arr2.iter()) {
                    let ord = v1.cmp(v2);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                arr1.len().cmp(&arr2.len())
            }
            (Value::Object(obj1), Value::Object(obj2)) => {
                for ((k1, v1), (k2, v2)) in obj1.iter().zip(obj2.iter()) {
                    let ord = k1.cmp(k2);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                    let ord = v1.cmp(v2);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                obj1.len().cmp(&obj2.len())
            }
            (_, _) => match (self.as_extension_value(), other.as_extension_value()) {
                (Some(self_ext), Some(other_ext)) => {
                    if let Some(ord) = self_ext.partial_cmp(&other_ext) {
                        return ord;
                    }
                    Ordering::Equal
                }
                (_, _) => Ordering::Equal,
            },
        }
    }
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
            Value::Number(n) => Some(n.as_f64()),
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
            2 => match rng.random_range(0..=20) {
                0..=5 => {
                    let n: u64 = rng.random_range(0..=100000);
                    Value::Number(Number::UInt64(n))
                }
                6..=10 => {
                    let n: i64 = rng.random_range(-100000..=100000);
                    Value::Number(Number::Int64(n))
                }
                11..=15 => {
                    let n: f64 = rng.random_range(-4000.0..1.3e5);
                    Value::Number(Number::Float64(n))
                }
                16..=17 => {
                    let scale: u8 = rng.random_range(0..=18);
                    let value: i64 = rng.random_range(-999999999999999999..=999999999999999999);
                    Value::Number(Number::Decimal64(Decimal64 { scale, value }))
                }
                18..=19 => {
                    let scale: u8 = rng.random_range(0..=38);
                    let value: i128 = rng.random_range(
                        -99999999999999999999999999999999999999i128
                            ..=99999999999999999999999999999999999999i128,
                    );
                    Value::Number(Number::Decimal128(Decimal128 { scale, value }))
                }
                _ => {
                    let scale: u8 = rng.random_range(0..=76);
                    let lo: i128 =
                        rng.random_range(0i128..=99999999999999999999999999999999999999i128);
                    let hi: i128 = rng.random_range(
                        -999999999999999999999999999999999999i128
                            ..=999999999999999999999999999999999999i128,
                    );
                    let value = ethnum::i256::from_words(hi, lo);
                    Value::Number(Number::Decimal256(Decimal256 { scale, value }))
                }
            },
            _ => Value::Null,
        };
        val
    }

    fn jsonb_item_type(&self) -> JsonbItemType {
        match self {
            Value::Null => JsonbItemType::Null,
            Value::Bool(_) => JsonbItemType::Boolean,
            Value::Number(_) => JsonbItemType::Number,
            Value::String(_) => JsonbItemType::String,
            Value::Binary(_) => JsonbItemType::Extension,
            Value::Date(_) => JsonbItemType::Extension,
            Value::Timestamp(_) => JsonbItemType::Extension,
            Value::TimestampTz(_) => JsonbItemType::Extension,
            Value::Interval(_) => JsonbItemType::Extension,
            Value::Array(arr) => JsonbItemType::Array(arr.len()),
            Value::Object(obj) => JsonbItemType::Object(obj.len()),
        }
    }

    fn as_extension_value(&self) -> Option<ExtensionValue<'_>> {
        match self {
            Value::Binary(v) => Some(ExtensionValue::Binary(v)),
            Value::Date(v) => Some(ExtensionValue::Date(v.clone())),
            Value::Timestamp(v) => Some(ExtensionValue::Timestamp(v.clone())),
            Value::TimestampTz(v) => Some(ExtensionValue::TimestampTz(v.clone())),
            Value::Interval(v) => Some(ExtensionValue::Interval(v.clone())),
            _ => None,
        }
    }
}
