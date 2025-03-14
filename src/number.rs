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
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;

use ordered_float::OrderedFloat;
use serde::de;
use serde::de::Deserialize;
use serde::de::Deserializer;
use serde::de::Visitor;
use serde::ser::Serialize;
use serde::ser::Serializer;

#[derive(Debug, Clone)]
pub enum Number {
    Int64(i64),
    UInt64(u64),
    Float64(f64),
}

impl<'de> Deserialize<'de> for Number {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct NumberVisitor;

        impl Visitor<'_> for NumberVisitor {
            type Value = Number;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a number (int64, uint64, or float64)")
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::Int64(v))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::UInt64(v))
            }

            fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::Float64(v))
            }
        }
        deserializer.deserialize_any(NumberVisitor)
    }
}

impl Serialize for Number {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Number::Int64(v) => serializer.serialize_i64(*v),
            Number::UInt64(v) => serializer.serialize_u64(*v),
            Number::Float64(v) => serializer.serialize_f64(*v),
        }
    }
}

impl Number {
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Number::Int64(v) => Some(*v),
            Number::UInt64(v) => {
                if *v <= i64::MAX.try_into().unwrap() {
                    Some(*v as i64)
                } else {
                    None
                }
            }
            Number::Float64(_) => None,
        }
    }

    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Number::Int64(v) => {
                if *v >= 0 {
                    Some(*v as u64)
                } else {
                    None
                }
            }
            Number::UInt64(v) => Some(*v),
            Number::Float64(_) => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Number::Int64(v) => Some(*v as f64),
            Number::UInt64(v) => Some(*v as f64),
            Number::Float64(v) => Some(*v),
        }
    }
}

impl Default for Number {
    #[inline]
    fn default() -> Self {
        Number::UInt64(0)
    }
}

impl PartialEq for Number {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialEq<&Number> for Number {
    #[inline]
    fn eq(&self, other: &&Number) -> bool {
        self.eq(*other)
    }
}

impl PartialEq<Number> for &Number {
    #[inline]
    fn eq(&self, other: &Number) -> bool {
        (*self).eq(other)
    }
}

impl Eq for Number {}

impl PartialOrd for Number {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<&Number> for Number {
    #[inline]
    fn partial_cmp(&self, other: &&Number) -> Option<Ordering> {
        self.partial_cmp(*other)
    }
}

impl PartialOrd<Number> for &Number {
    #[inline]
    fn partial_cmp(&self, other: &Number) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl Ord for Number {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Number::Int64(l), Number::Int64(r)) => l.cmp(r),
            (Number::UInt64(l), Number::UInt64(r)) => l.cmp(r),
            (Number::Int64(l), Number::UInt64(r)) => {
                if *l < 0 {
                    Ordering::Less
                } else {
                    (*l as u64).cmp(r)
                }
            }
            (Number::UInt64(l), Number::Int64(r)) => {
                if *r < 0 {
                    Ordering::Greater
                } else {
                    l.cmp(&(*r as u64))
                }
            }
            (_, _) => {
                let l = OrderedFloat(self.as_f64().unwrap());
                let r = OrderedFloat(other.as_f64().unwrap());
                l.cmp(&r)
            }
        }
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Number::Int64(v) => {
                let mut buffer = itoa::Buffer::new();
                let s = buffer.format(*v);
                write!(f, "{}", s)
            }
            Number::UInt64(v) => {
                let mut buffer = itoa::Buffer::new();
                let s = buffer.format(*v);
                write!(f, "{}", s)
            }
            Number::Float64(v) => {
                let mut buffer = ryu::Buffer::new();
                let s = buffer.format(*v);
                write!(f, "{}", s)
            }
        }
    }
}
