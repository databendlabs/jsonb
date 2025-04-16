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
use std::convert::TryFrom;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;

use crate::error::Result;
use crate::Error;

use ethnum::i256;
use ordered_float::OrderedFloat;
use serde::de;
use serde::de::Deserialize;
use serde::de::Deserializer;
use serde::de::Visitor;
use serde::ser::Serialize;
use serde::ser::Serializer;

#[derive(Debug, Clone)]
pub struct Decimal128 {
    pub precision: u8,
    pub scale: u8,
    pub value: i128,
}

impl Decimal128 {
    pub fn to_float64(&self) -> f64 {
        let div = 10_f64.powi(self.scale as i32);
        self.value as f64 / div
    }
}

#[derive(Debug, Clone)]
pub struct Decimal256 {
    pub precision: u8,
    pub scale: u8,
    pub value: i256,
}

impl Decimal256 {
    pub fn to_float64(&self) -> f64 {
        let div = 10_f64.powi(self.scale as i32);
        self.value.as_f64() / div
    }
}

#[derive(Debug, Clone)]
pub enum Number {
    Int64(i64),
    UInt64(u64),
    Float64(f64),
    Decimal128(Decimal128),
    Decimal256(Decimal256),
}

impl<'de> Deserialize<'de> for Number {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct NumberVisitor;

        impl Visitor<'_> for NumberVisitor {
            type Value = Number;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a number (int64, uint64, or float64)")
            }

            fn visit_i64<E>(self, v: i64) -> std::result::Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::Int64(v))
            }

            fn visit_u64<E>(self, v: u64) -> std::result::Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::UInt64(v))
            }

            fn visit_f64<E>(self, v: f64) -> std::result::Result<Self::Value, E>
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
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Number::Int64(v) => serializer.serialize_i64(*v),
            Number::UInt64(v) => serializer.serialize_u64(*v),
            Number::Float64(v) => serializer.serialize_f64(*v),
            Number::Decimal128(v) => {
                let val = v.to_float64();
                serializer.serialize_f64(val)
            }
            Number::Decimal256(v) => {
                let val = v.to_float64();
                serializer.serialize_f64(val)
            }
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
            Number::Float64(_) | Number::Decimal128(_) | Number::Decimal256(_) => None,
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
            Number::Float64(_) | Number::Decimal128(_) | Number::Decimal256(_) => None,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Number::Int64(v) => Some(*v as f64),
            Number::UInt64(v) => Some(*v as f64),
            Number::Float64(v) => Some(*v),
            Number::Decimal128(v) => {
                let val = v.to_float64();
                Some(val)
            }
            Number::Decimal256(v) => {
                let val = v.to_float64();
                Some(val)
            }
        }
    }

    pub fn neg(&self) -> Result<Number> {
        match self {
            Number::Int64(v) => v
                .checked_neg()
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            Number::UInt64(v) => {
                if let Ok(v) = i64::try_from(*v) {
                    v.checked_neg()
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    Err(Error::Message("Int64 overflow".to_string()))
                }
            }
            Number::Float64(v) => Ok(Number::Float64(*v * -1.0)),
            Number::Decimal128(v) => {
                let neg_dec = Decimal128 {
                    precision: v.precision,
                    scale: v.scale,
                    value: -v.value,
                };
                Ok(Number::Decimal128(neg_dec))
            }
            Number::Decimal256(v) => {
                let Some(neg_value) = v.value.checked_neg() else {
                    return Err(Error::Message("Decimal256 overflow".to_string()));
                };
                let neg_dec = Decimal256 {
                    precision: v.precision,
                    scale: v.scale,
                    value: neg_value,
                };
                Ok(Number::Decimal256(neg_dec))
            }
        }
    }

    pub fn add(&self, other: Number) -> Result<Number> {
        match (self, other) {
            (Number::Int64(a), Number::Int64(b)) => a
                .checked_add(b)
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            (Number::UInt64(a), Number::UInt64(b)) => a
                .checked_add(b)
                .map(Number::UInt64)
                .ok_or(Error::Message("UInt64 overflow".to_string())),
            (Number::Int64(a), Number::UInt64(b)) => {
                if *a < 0 {
                    a.checked_add(b as i64)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    (*a as u64)
                        .checked_add(b)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::UInt64(a), Number::Int64(b)) => {
                if b < 0 {
                    (*a as i64)
                        .checked_add(b)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    a.checked_add(b as u64)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::Float64(a), Number::Float64(b)) => Ok(Number::Float64(a + b)),
            (a, b) => {
                let a_float = a.as_f64().unwrap();
                let b_float = b.as_f64().unwrap();
                Ok(Number::Float64(a_float + b_float))
            }
        }
    }

    pub fn sub(&self, other: Number) -> Result<Number> {
        match (self, other) {
            (Number::Int64(a), Number::Int64(b)) => a
                .checked_sub(b)
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            (Number::UInt64(a), Number::UInt64(b)) => (*a as i64)
                .checked_sub(b as i64)
                .map(Number::Int64)
                .ok_or(Error::Message("UInt64 overflow".to_string())),
            (Number::Int64(a), Number::UInt64(b)) => a
                .checked_sub(b as i64)
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            (Number::UInt64(a), Number::Int64(b)) => (*a as i64)
                .checked_sub(b)
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            (Number::Float64(a), Number::Float64(b)) => Ok(Number::Float64(a - b)),
            (a, b) => {
                let a_float = a.as_f64().unwrap();
                let b_float = b.as_f64().unwrap();
                Ok(Number::Float64(a_float - b_float))
            }
        }
    }

    pub fn mul(&self, other: Number) -> Result<Number> {
        match (self, other) {
            (Number::Int64(a), Number::Int64(b)) => a
                .checked_mul(b)
                .map(Number::Int64)
                .ok_or(Error::Message("Int64 overflow".to_string())),
            (Number::UInt64(a), Number::UInt64(b)) => a
                .checked_mul(b)
                .map(Number::UInt64)
                .ok_or(Error::Message("UInt64 overflow".to_string())),
            (Number::Int64(a), Number::UInt64(b)) => {
                if *a < 0 {
                    a.checked_mul(b as i64)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    (*a as u64)
                        .checked_mul(b)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::UInt64(a), Number::Int64(b)) => {
                if b < 0 {
                    (*a as i64)
                        .checked_mul(b)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    a.checked_mul(b as u64)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::Float64(a), Number::Float64(b)) => Ok(Number::Float64(a * b)),
            (a, b) => {
                let a_float = a.as_f64().unwrap();
                let b_float = b.as_f64().unwrap();
                Ok(Number::Float64(a_float * b_float))
            }
        }
    }

    pub fn div(&self, other: Number) -> Result<Number> {
        let a_float = self.as_f64().unwrap();
        let b_float = other.as_f64().unwrap();
        if b_float == 0.0 {
            return Err(Error::Message("Division by zero".to_string()));
        }
        Ok(Number::Float64(a_float / b_float))
    }

    pub fn rem(&self, other: Number) -> Result<Number> {
        match (self, other) {
            (Number::Int64(a), Number::Int64(b)) => {
                if b == 0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                a.checked_rem(b)
                    .map(Number::Int64)
                    .ok_or(Error::Message("Int64 overflow".to_string()))
            }
            (Number::UInt64(a), Number::UInt64(b)) => {
                if b == 0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                a.checked_rem(b)
                    .map(Number::UInt64)
                    .ok_or(Error::Message("UInt64 overflow".to_string()))
            }
            (Number::Int64(a), Number::UInt64(b)) => {
                if b == 0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                if *a < 0 {
                    a.checked_rem(b as i64)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    (*a as u64)
                        .checked_rem(b)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::UInt64(a), Number::Int64(b)) => {
                if b == 0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                if b < 0 {
                    (*a as i64)
                        .checked_rem(b)
                        .map(Number::Int64)
                        .ok_or(Error::Message("Int64 overflow".to_string()))
                } else {
                    a.checked_rem(b as u64)
                        .map(Number::UInt64)
                        .ok_or(Error::Message("UInt64 overflow".to_string()))
                }
            }
            (Number::Float64(a), Number::Float64(b)) => {
                if b == 0.0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                Ok(Number::Float64(a % b))
            }
            (a, b) => {
                let a_float = a.as_f64().unwrap();
                let b_float = b.as_f64().unwrap();
                if b_float == 0.0 {
                    return Err(Error::Message("Division by zero".to_string()));
                }
                Ok(Number::Float64(a_float % b_float))
            }
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
            Number::Decimal128(v) => {
                if v.scale == 0 {
                    write!(f, "{}", v.value)
                } else {
                    let pow_scale = 10_i128.pow(v.scale as u32);
                    if v.value >= 0 {
                        write!(
                            f,
                            "{}.{:0>width$}",
                            v.value / pow_scale,
                            (v.value % pow_scale).abs(),
                            width = v.scale as usize
                        )
                    } else {
                        write!(
                            f,
                            "-{}.{:0>width$}",
                            -v.value / pow_scale,
                            (v.value % pow_scale).abs(),
                            width = v.scale as usize
                        )
                    }
                }
            }
            Number::Decimal256(v) => {
                if v.scale == 0 {
                    write!(f, "{}", v.value)
                } else {
                    let pow_scale = i256::from(10).pow(v.scale as u32);
                    // -1/10 = 0
                    if v.value >= i256::from(0) {
                        write!(
                            f,
                            "{}.{:0>width$}",
                            v.value / pow_scale,
                            (v.value % pow_scale).abs(),
                            width = v.scale as usize
                        )
                    } else {
                        write!(
                            f,
                            "-{}.{:0>width$}",
                            -v.value / pow_scale,
                            (v.value % pow_scale).abs(),
                            width = v.scale as usize
                        )
                    }
                }
            }
        }
    }
}
