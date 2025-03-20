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

use rand::distributions::Alphanumeric;
use rand::distributions::DistString;
use rand::thread_rng;
use rand::Rng;

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
            Value::Array(ref vs) => {
                let mut first = true;
                write!(f, "[")?;
                for v in vs.iter() {
                    if !first {
                        write!(f, ",")?;
                    }
                    first = false;
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Value::Object(ref vs) => {
                let mut first = true;
                write!(f, "{{")?;
                for (k, v) in vs.iter() {
                    if !first {
                        write!(f, ",")?;
                    }
                    first = false;
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
        self.as_object().is_some()
    }

    pub fn as_object(&self) -> Option<&Object<'a>> {
        match self {
            Value::Object(ref obj) => Some(obj),
            _ => None,
        }
    }

    pub fn is_array(&self) -> bool {
        self.as_array().is_some()
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
        self.as_bool().is_some()
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(v) => Some(*v),
            _ => None,
        }
    }

    pub fn is_null(&self) -> bool {
        self.as_null().is_some()
    }

    pub fn as_null(&self) -> Option<()> {
        match self {
            Value::Null => Some(()),
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
        let mut rng = thread_rng();
        let val = match rng.gen_range(0..=2) {
            0 => {
                let len = rng.gen_range(0..=5);
                let mut values = Vec::with_capacity(len);
                for _ in 0..len {
                    values.push(Self::rand_scalar_value());
                }
                Value::Array(values)
            }
            1 => {
                let len = rng.gen_range(0..=5);
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
        let mut rng = thread_rng();
        let val = match rng.gen_range(0..=3) {
            0 => {
                let v = rng.gen_bool(0.5);
                Value::Bool(v)
            }
            1 => {
                let s = Alphanumeric.sample_string(&mut rng, 5);
                Value::String(Cow::from(s))
            }
            2 => match rng.gen_range(0..=2) {
                0 => {
                    let n: u64 = rng.gen_range(0..=100000);
                    Value::Number(Number::UInt64(n))
                }
                1 => {
                    let n: i64 = rng.gen_range(-100000..=100000);
                    Value::Number(Number::Int64(n))
                }
                _ => {
                    let n: f64 = rng.gen_range(-4000.0..1.3e5);
                    Value::Number(Number::Float64(n))
                }
            },
            _ => Value::Null,
        };
        val
    }
}
