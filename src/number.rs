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
use serde::ser::SerializeStruct;
use serde::ser::Serializer;

const NUMBER_TOKEN: &str = "$serde_json::private::Number";

/// Represents a decimal number with 64-bit precision.
///
/// This structure stores a decimal value as an integer with a scale factor,
/// allowing for precise representation of decimal numbers without floating-point errors.
/// The scale indicates how many decimal places the value has (e.g., scale=2 means 2 decimal places).
#[derive(Debug, Clone)]
pub struct Decimal64 {
    /// Number of decimal places (e.g., 2 for values like 123.45)
    pub scale: u8,
    /// The actual value, scaled by 10^scale (e.g., 12345 for 123.45 with scale=2)
    pub value: i64,
}

impl Decimal64 {
    /// Converts the decimal value to a floating-point representation.
    ///
    /// This is useful when you need to perform floating-point operations,
    /// but note that it may introduce precision loss inherent to floating-point arithmetic.
    pub fn to_float64(&self) -> f64 {
        let div = 10_f64.powi(self.scale as i32);
        self.value as f64 / div
    }
}

/// Represents a decimal number with 128-bit precision.
///
/// Similar to Decimal64 but with a larger range, this structure can represent
/// very large decimal numbers with high precision, suitable for financial calculations
/// and other domains requiring exact decimal arithmetic beyond 64-bit limits.
#[derive(Debug, Clone)]
pub struct Decimal128 {
    /// Number of decimal places
    pub scale: u8,
    /// The actual value, scaled by 10^scale
    pub value: i128,
}

impl Decimal128 {
    /// Converts the decimal value to a floating-point representation.
    ///
    /// Note that for very large values, this conversion may lose precision
    /// as f64 has limited precision compared to i128.
    pub fn to_float64(&self) -> f64 {
        let div = 10_f64.powi(self.scale as i32);
        self.value as f64 / div
    }
}

/// Represents a decimal number with 256-bit precision.
///
/// This structure provides the highest level of precision for decimal numbers,
/// capable of representing extremely large values with exact decimal precision.
/// Useful for cryptographic applications, high-precision scientific calculations,
/// or any domain requiring arithmetic beyond 128-bit precision.
#[derive(Debug, Clone)]
pub struct Decimal256 {
    /// Number of decimal places
    pub scale: u8,
    /// The actual value, scaled by 10^scale
    pub value: i256,
}

impl Decimal256 {
    /// Converts the decimal value to a floating-point representation.
    ///
    /// For extremely large values, significant precision loss may occur
    /// as f64 has much lower precision than i256.
    pub fn to_float64(&self) -> f64 {
        let div = 10_f64.powi(self.scale as i32);
        self.value.as_f64() / div
    }
}

/// Represents a JSON number with multiple possible internal representations.
///
/// This enum provides a unified type for JSON numbers while supporting various
/// internal representations to optimize for different use cases:
/// - Integer types (signed/unsigned) for whole numbers
/// - Floating-point for scientific notation or fractional values
/// - Decimal types for exact decimal representation with different precision levels
///
/// The parser automatically selects the most appropriate representation based on
/// the input value's characteristics, allowing for both performance and precision.
#[derive(Debug, Clone)]
pub enum Number {
    /// 64-bit signed integer, suitable for most whole numbers
    Int64(i64),
    /// 64-bit unsigned integer, for large positive whole numbers
    UInt64(u64),
    /// 64-bit floating-point, for scientific notation and approximate decimals
    Float64(f64),
    /// 64-bit decimal with exact precision, for financial calculations
    Decimal64(Decimal64),
    /// 128-bit decimal with extended precision, for larger exact decimals
    Decimal128(Decimal128),
    /// 256-bit decimal with maximum precision, for extremely large exact decimals
    Decimal256(Decimal256),
}

impl<'de> Deserialize<'de> for Number {
    /// Deserializes a JSON number into the Number enum.
    ///
    /// This implementation supports deserialization from JSON integers and floats.
    /// It automatically selects the most suitable internal representation based on the input value.
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct NumberVisitor;

        impl Visitor<'_> for NumberVisitor {
            type Value = Number;

            /// Returns a string describing the expected input format.
            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a number (int64, uint64, or float64)")
            }

            /// Visits an i64 value and returns a Number::Int64 variant.
            fn visit_i64<E>(self, v: i64) -> std::result::Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::Int64(v))
            }

            /// Visits a u64 value and returns a Number::UInt64 variant.
            fn visit_u64<E>(self, v: u64) -> std::result::Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(Number::UInt64(v))
            }

            /// Visits an f64 value and returns a Number::Float64 variant.
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
    /// Serializes the Number enum into a JSON number.
    ///
    /// This implementation supports serialization to JSON integers and floats.
    /// It automatically selects the most suitable output format based on the internal representation.
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Number::Int64(v) => serializer.serialize_i64(*v),
            Number::UInt64(v) => serializer.serialize_u64(*v),
            Number::Float64(v) => serializer.serialize_f64(*v),
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                let mut serialize_struct = serializer.serialize_struct(NUMBER_TOKEN, 0)?;
                let val = format!("{}", self);
                serialize_struct.serialize_field(NUMBER_TOKEN, val.as_str())?;
                serialize_struct.end()
            }
        }
    }
}

impl Number {
    /// Returns the i64 representation of the number, if possible.
    ///
    /// This method returns None if the number cannot be represented as an i64.
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
            Number::Float64(_)
            | Number::Decimal64(_)
            | Number::Decimal128(_)
            | Number::Decimal256(_) => None,
        }
    }

    /// Returns the u64 representation of the number, if possible.
    ///
    /// This method returns None if the number cannot be represented as a u64.
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
            Number::Float64(_)
            | Number::Decimal64(_)
            | Number::Decimal128(_)
            | Number::Decimal256(_) => None,
        }
    }

    /// Returns the f64 representation of the number.
    ///
    /// This method always returns a value, but may lose precision for very large numbers.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Number::Int64(v) => Some(*v as f64),
            Number::UInt64(v) => Some(*v as f64),
            Number::Float64(v) => Some(*v),
            Number::Decimal64(v) => {
                let val = v.to_float64();
                Some(val)
            }
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

    /// Returns the negation of the number.
    ///
    /// This method returns an error if the negation would overflow.
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
            Number::Decimal64(v) => {
                let neg_dec = Decimal64 {
                    scale: v.scale,
                    value: -v.value,
                };
                Ok(Number::Decimal64(neg_dec))
            }
            Number::Decimal128(v) => {
                let neg_dec = Decimal128 {
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
                    scale: v.scale,
                    value: neg_value,
                };
                Ok(Number::Decimal256(neg_dec))
            }
        }
    }

    /// Returns the sum of the number and another number.
    ///
    /// This method returns an error if the sum would overflow.
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

    /// Returns the difference of the number and another number.
    ///
    /// This method returns an error if the difference would overflow.
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

    /// Returns the product of the number and another number.
    ///
    /// This method returns an error if the product would overflow.
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

    /// Returns the quotient of the number and another number.
    ///
    /// This method returns an error if the divisor is zero.
    pub fn div(&self, other: Number) -> Result<Number> {
        let a_float = self.as_f64().unwrap();
        let b_float = other.as_f64().unwrap();
        if b_float == 0.0 {
            return Err(Error::Message("Division by zero".to_string()));
        }
        Ok(Number::Float64(a_float / b_float))
    }

    /// Returns the remainder of the number divided by another number.
    ///
    /// This method returns an error if the divisor is zero.
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
    /// Returns the default value for the Number enum.
    ///
    /// The default value is Number::UInt64(0).
    #[inline]
    fn default() -> Self {
        Number::UInt64(0)
    }
}

impl PartialEq for Number {
    /// Returns true if the number is equal to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialEq<&Number> for Number {
    /// Returns true if the number is equal to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn eq(&self, other: &&Number) -> bool {
        self.eq(*other)
    }
}

impl PartialEq<Number> for &Number {
    /// Returns true if the number is equal to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn eq(&self, other: &Number) -> bool {
        (*self).eq(other)
    }
}

impl Eq for Number {}

impl PartialOrd for Number {
    /// Returns the ordering of the number compared to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<&Number> for Number {
    /// Returns the ordering of the number compared to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn partial_cmp(&self, other: &&Number) -> Option<Ordering> {
        self.partial_cmp(*other)
    }
}

impl PartialOrd<Number> for &Number {
    /// Returns the ordering of the number compared to another number.
    ///
    /// This method compares the numbers using their internal representations.
    #[inline]
    fn partial_cmp(&self, other: &Number) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl Ord for Number {
    /// Returns the ordering of the number compared to another number.
    ///
    /// This method implements precise comparison between different number types:
    /// - When comparing decimal types with other types, it converts the non-decimal type
    ///   to a decimal representation to preserve precision
    /// - When comparing between decimal types of different precision, it upgrades the lower
    ///   precision decimal to match the higher precision one
    /// - Only falls back to floating-point comparison as a last resort
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            // Same type comparisons - use native comparison
            (Number::Int64(l), Number::Int64(r)) => l.cmp(r),
            (Number::UInt64(l), Number::UInt64(r)) => l.cmp(r),
            (Number::Float64(l), Number::Float64(r)) => OrderedFloat(*l).cmp(&OrderedFloat(*r)),
            (Number::Decimal64(l), Number::Decimal64(r)) => {
                // Compare decimal values with the same scale
                if l.scale == r.scale {
                    l.value.cmp(&r.value)
                } else {
                    // Adjust scales to match for proper comparison
                    if let Some((l_val, r_val)) =
                        adjust_decimal_scales(l.value as i128, l.scale, r.value as i128, r.scale)
                    {
                        l_val.cmp(&r_val)
                    } else {
                        let l = OrderedFloat(self.as_f64().unwrap());
                        let r = OrderedFloat(other.as_f64().unwrap());
                        l.cmp(&r)
                    }
                }
            }
            (Number::Decimal128(l), Number::Decimal128(r)) => {
                // Compare decimal values with the same scale
                if l.scale == r.scale {
                    l.value.cmp(&r.value)
                } else {
                    // Adjust scales to match for proper comparison
                    if let Some((l_val, r_val)) =
                        adjust_decimal_scales(l.value, l.scale, r.value, r.scale)
                    {
                        l_val.cmp(&r_val)
                    } else {
                        let l = OrderedFloat(self.as_f64().unwrap());
                        let r = OrderedFloat(other.as_f64().unwrap());
                        l.cmp(&r)
                    }
                }
            }
            (Number::Decimal256(l), Number::Decimal256(r)) => {
                // Compare decimal values with the same scale
                if l.scale == r.scale {
                    l.value.cmp(&r.value)
                } else {
                    // For i256 comparison with different scales, we need to adjust manually
                    let scale_diff = l.scale as i32 - r.scale as i32;
                    if scale_diff > 0 {
                        // l has more decimal places, scale up r
                        let scale_factor = i256::from(10).pow(scale_diff as u32);
                        if let Some(r_val) = r.value.checked_mul(scale_factor) {
                            return l.value.cmp(&r_val);
                        }
                    } else {
                        // r has more decimal places, scale up l
                        let scale_factor = i256::from(10).pow((-scale_diff) as u32);
                        if let Some(l_val) = l.value.checked_mul(scale_factor) {
                            return l_val.cmp(&r.value);
                        }
                    }
                    // multiply overflow, fallback to used float compare
                    let l = OrderedFloat(self.as_f64().unwrap());
                    let r = OrderedFloat(other.as_f64().unwrap());
                    l.cmp(&r)
                }
            }

            // Integer to integer comparisons
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

            // Decimal64 comparisons with other types
            (Number::Decimal64(_), Number::Int64(r)) => {
                // Convert Int64 to Decimal64 with scale 0
                let r_decimal = Decimal64 {
                    scale: 0,
                    value: *r,
                };
                self.cmp(&Number::Decimal64(r_decimal))
            }
            (Number::Int64(l), Number::Decimal64(_)) => {
                // Convert Int64 to Decimal64 with scale 0
                let l_decimal = Decimal64 {
                    scale: 0,
                    value: *l,
                };
                Number::Decimal64(l_decimal).cmp(other)
            }
            (Number::Decimal64(_), Number::UInt64(r)) => {
                // Check if the value fits in i64
                if *r <= i64::MAX as u64 {
                    // Convert UInt64 to Decimal64 with scale 0
                    let r_decimal = Decimal64 {
                        scale: 0,
                        value: *r as i64,
                    };
                    self.cmp(&Number::Decimal64(r_decimal))
                } else {
                    // If it doesn't fit, Convert UInt64 to Decimal128 with scale 0
                    let r_decimal = Decimal128 {
                        scale: 0,
                        value: *r as i128,
                    };
                    self.cmp(&Number::Decimal128(r_decimal))
                }
            }
            (Number::UInt64(l), Number::Decimal64(_)) => {
                // Check if the value fits in i64
                if *l <= i64::MAX as u64 {
                    // Convert UInt64 to Decimal64 with scale 0
                    let l_decimal = Decimal64 {
                        scale: 0,
                        value: *l as i64,
                    };
                    Number::Decimal64(l_decimal).cmp(other)
                } else {
                    // If it doesn't fit, Convert UInt64 to Decimal128 with scale 0
                    let l_decimal = Decimal128 {
                        scale: 0,
                        value: *l as i128,
                    };
                    Number::Decimal128(l_decimal).cmp(other)
                }
            }

            // Decimal128 comparisons with other types
            (Number::Decimal128(_), Number::Int64(r)) => {
                // Convert Int64 to Decimal128 with scale 0
                let r_decimal = Decimal128 {
                    scale: 0,
                    value: *r as i128,
                };
                self.cmp(&Number::Decimal128(r_decimal))
            }
            (Number::Int64(l), Number::Decimal128(_)) => {
                // Convert Int64 to Decimal128 with scale 0
                let l_decimal = Decimal128 {
                    scale: 0,
                    value: *l as i128,
                };
                Number::Decimal128(l_decimal).cmp(other)
            }
            (Number::Decimal128(_), Number::UInt64(r)) => {
                // Convert UInt64 to Decimal128 with scale 0
                let r_decimal = Decimal128 {
                    scale: 0,
                    value: *r as i128,
                };
                self.cmp(&Number::Decimal128(r_decimal))
            }
            (Number::UInt64(l), Number::Decimal128(_)) => {
                // Convert UInt64 to Decimal128 with scale 0
                let l_decimal = Decimal128 {
                    scale: 0,
                    value: *l as i128,
                };
                Number::Decimal128(l_decimal).cmp(other)
            }

            // Decimal256 comparisons with other types
            (Number::Decimal256(_), Number::Int64(r)) => {
                // Convert Int64 to Decimal256 with scale 0
                let r_decimal = Decimal256 {
                    scale: 0,
                    value: i256::from(*r),
                };
                self.cmp(&Number::Decimal256(r_decimal))
            }
            (Number::Int64(l), Number::Decimal256(_)) => {
                // Convert Int64 to Decimal256 with scale 0
                let l_decimal = Decimal256 {
                    scale: 0,
                    value: i256::from(*l),
                };
                Number::Decimal256(l_decimal).cmp(other)
            }
            (Number::Decimal256(_), Number::UInt64(r)) => {
                // Convert UInt64 to Decimal256 with scale 0
                let r_decimal = Decimal256 {
                    scale: 0,
                    value: i256::from(*r),
                };
                self.cmp(&Number::Decimal256(r_decimal))
            }
            (Number::UInt64(l), Number::Decimal256(_)) => {
                // Convert UInt64 to Decimal256 with scale 0
                let l_decimal = Decimal256 {
                    scale: 0,
                    value: i256::from(*l),
                };
                Number::Decimal256(l_decimal).cmp(other)
            }

            // Cross-decimal comparisons - upgrade to the higher precision
            (Number::Decimal64(l), Number::Decimal128(_)) => {
                // Upgrade Decimal64 to Decimal128
                let l_decimal = Decimal128 {
                    scale: l.scale,
                    value: l.value as i128,
                };
                Number::Decimal128(l_decimal).cmp(other)
            }
            (Number::Decimal128(_), Number::Decimal64(r)) => {
                // Upgrade Decimal64 to Decimal128
                let r_decimal = Decimal128 {
                    scale: r.scale,
                    value: r.value as i128,
                };
                self.cmp(&Number::Decimal128(r_decimal))
            }
            (Number::Decimal64(l), Number::Decimal256(_)) => {
                // Upgrade Decimal64 to Decimal256
                let l_decimal = Decimal256 {
                    scale: l.scale,
                    value: i256::from(l.value),
                };
                Number::Decimal256(l_decimal).cmp(other)
            }
            (Number::Decimal256(_), Number::Decimal64(r)) => {
                // Upgrade Decimal64 to Decimal256
                let r_decimal = Decimal256 {
                    scale: r.scale,
                    value: i256::from(r.value),
                };
                self.cmp(&Number::Decimal256(r_decimal))
            }
            (Number::Decimal128(l), Number::Decimal256(_)) => {
                // Upgrade Decimal128 to Decimal256
                let l_decimal = Decimal256 {
                    scale: l.scale,
                    value: i256::from(l.value),
                };
                Number::Decimal256(l_decimal).cmp(other)
            }
            (Number::Decimal256(_), Number::Decimal128(r)) => {
                // Upgrade Decimal128 to Decimal256
                let r_decimal = Decimal256 {
                    scale: r.scale,
                    value: i256::from(r.value),
                };
                self.cmp(&Number::Decimal256(r_decimal))
            }

            // Fall back to float comparison for any other combinations
            (_, _) => {
                let l = OrderedFloat(self.as_f64().unwrap());
                let r = OrderedFloat(other.as_f64().unwrap());
                l.cmp(&r)
            }
        }
    }
}

/// Helper function to adjust decimal scales for comparison
///
/// Given two decimal values with potentially different scales,
/// this function adjusts them to have the same scale for accurate comparison.
fn adjust_decimal_scales(
    l_val: i128,
    l_scale: u8,
    r_val: i128,
    r_scale: u8,
) -> Option<(i128, i128)> {
    let scale_diff = l_scale as i32 - r_scale as i32;

    match scale_diff.cmp(&0) {
        Ordering::Greater => {
            // l has more decimal places, scale up r
            let scale_factor = 10_i128.pow(scale_diff as u32);
            let r_val = r_val.checked_mul(scale_factor)?;
            Some((l_val, r_val))
        }
        Ordering::Less => {
            // r has more decimal places, scale up l
            let scale_factor = 10_i128.pow((-scale_diff) as u32);
            let l_val = l_val.checked_mul(scale_factor)?;
            Some((l_val, r_val))
        }
        Ordering::Equal => {
            // Same scale, no adjustment needed
            Some((l_val, r_val))
        }
    }
}

impl Display for Number {
    /// Formats the number as a string.
    ///
    /// This method returns a string representation of the number in its internal format.
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
            Number::Decimal64(v) => {
                if v.scale == 0 {
                    write!(f, "{}", v.value)
                } else {
                    let pow_scale = 10_i64.pow(v.scale as u32);
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    #[test]
    fn test_number_comparison() {
        // Test same type comparisons
        assert_eq!(Number::Int64(10).cmp(&Number::Int64(5)), Ordering::Greater);
        assert_eq!(Number::Int64(5).cmp(&Number::Int64(10)), Ordering::Less);
        assert_eq!(Number::Int64(5).cmp(&Number::Int64(5)), Ordering::Equal);

        assert_eq!(
            Number::UInt64(10).cmp(&Number::UInt64(5)),
            Ordering::Greater
        );
        assert_eq!(Number::UInt64(5).cmp(&Number::UInt64(10)), Ordering::Less);
        assert_eq!(Number::UInt64(5).cmp(&Number::UInt64(5)), Ordering::Equal);

        assert_eq!(
            Number::Float64(10.0).cmp(&Number::Float64(5.0)),
            Ordering::Greater
        );
        assert_eq!(
            Number::Float64(5.0).cmp(&Number::Float64(10.0)),
            Ordering::Less
        );
        assert_eq!(
            Number::Float64(5.0).cmp(&Number::Float64(5.0)),
            Ordering::Equal
        );

        // Test int64 and uint64 comparisons
        assert_eq!(Number::Int64(10).cmp(&Number::UInt64(5)), Ordering::Greater);
        assert_eq!(Number::Int64(5).cmp(&Number::UInt64(10)), Ordering::Less);
        assert_eq!(Number::Int64(5).cmp(&Number::UInt64(5)), Ordering::Equal);
        assert_eq!(Number::Int64(-5).cmp(&Number::UInt64(5)), Ordering::Less);

        assert_eq!(Number::UInt64(10).cmp(&Number::Int64(5)), Ordering::Greater);
        assert_eq!(Number::UInt64(5).cmp(&Number::Int64(10)), Ordering::Less);
        assert_eq!(Number::UInt64(5).cmp(&Number::Int64(5)), Ordering::Equal);
        assert_eq!(Number::UInt64(5).cmp(&Number::Int64(-5)), Ordering::Greater);

        // Test decimal64 comparisons with same scale
        let d1 = Decimal64 {
            scale: 2,
            value: 1234,
        }; // 12.34
        let d2 = Decimal64 {
            scale: 2,
            value: 5678,
        }; // 56.78
        assert_eq!(
            Number::Decimal64(d1.clone()).cmp(&Number::Decimal64(d2.clone())),
            Ordering::Less
        );
        assert_eq!(
            Number::Decimal64(d2.clone()).cmp(&Number::Decimal64(d1.clone())),
            Ordering::Greater
        );
        assert_eq!(
            Number::Decimal64(d1.clone()).cmp(&Number::Decimal64(d1.clone())),
            Ordering::Equal
        );

        // Test decimal64 comparisons with different scales
        let d3 = Decimal64 {
            scale: 3,
            value: 12340,
        }; // 12.340
        assert_eq!(
            Number::Decimal64(d1.clone()).cmp(&Number::Decimal64(d3.clone())),
            Ordering::Equal
        );

        let d4 = Decimal64 {
            scale: 1,
            value: 123,
        }; // 12.3
        assert_eq!(
            Number::Decimal64(d1.clone()).cmp(&Number::Decimal64(d4.clone())),
            Ordering::Greater
        );

        // Test decimal128 comparisons
        let d5 = Decimal128 {
            scale: 2,
            value: 1234,
        }; // 12.34
        let d6 = Decimal128 {
            scale: 2,
            value: 5678,
        }; // 56.78
        assert_eq!(
            Number::Decimal128(d5.clone()).cmp(&Number::Decimal128(d6.clone())),
            Ordering::Less
        );

        // Test decimal256 comparisons
        let d7 = Decimal256 {
            scale: 2,
            value: i256::from(1234),
        }; // 12.34
        let d8 = Decimal256 {
            scale: 2,
            value: i256::from(5678),
        }; // 56.78
        assert_eq!(
            Number::Decimal256(d7.clone()).cmp(&Number::Decimal256(d8.clone())),
            Ordering::Less
        );

        // Test int64 to decimal64 comparisons
        assert_eq!(
            Number::Int64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 0,
                value: 12
            })),
            Ordering::Equal
        );
        assert_eq!(
            Number::Int64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 1,
                value: 120
            })),
            Ordering::Equal
        );
        assert_eq!(
            Number::Int64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 1,
                value: 121
            })),
            Ordering::Less
        );
        assert_eq!(
            Number::Int64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 1,
                value: 119
            })),
            Ordering::Greater
        );

        // Test uint64 to decimal64 comparisons
        assert_eq!(
            Number::UInt64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 0,
                value: 12
            })),
            Ordering::Equal
        );
        assert_eq!(
            Number::UInt64(12).cmp(&Number::Decimal64(Decimal64 {
                scale: 1,
                value: 120
            })),
            Ordering::Equal
        );

        // Test float64 to decimal64 comparisons
        assert_eq!(
            Number::Float64(12.34).cmp(&Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1234
            })),
            Ordering::Equal
        );
        assert_eq!(
            Number::Float64(12.34).cmp(&Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1235
            })),
            Ordering::Less
        );

        // Test cross-decimal comparisons
        // Decimal64 vs Decimal128
        assert_eq!(
            Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1234
            })
            .cmp(&Number::Decimal128(Decimal128 {
                scale: 2,
                value: 1234
            })),
            Ordering::Equal
        );
        assert_eq!(
            Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1234
            })
            .cmp(&Number::Decimal128(Decimal128 {
                scale: 2,
                value: 5678
            })),
            Ordering::Less
        );

        // Decimal64 vs Decimal256
        assert_eq!(
            Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1234
            })
            .cmp(&Number::Decimal256(Decimal256 {
                scale: 2,
                value: i256::from(1234)
            })),
            Ordering::Equal
        );

        // Decimal128 vs Decimal256
        assert_eq!(
            Number::Decimal128(Decimal128 {
                scale: 2,
                value: 1234
            })
            .cmp(&Number::Decimal256(Decimal256 {
                scale: 2,
                value: i256::from(1234)
            })),
            Ordering::Equal
        );

        // Test with different scales across decimal types
        assert_eq!(
            Number::Decimal64(Decimal64 {
                scale: 2,
                value: 1234
            })
            .cmp(&Number::Decimal128(Decimal128 {
                scale: 3,
                value: 12340
            })),
            Ordering::Equal
        );

        // Test edge cases
        // Very large numbers
        let large_int = i64::MAX;
        let large_uint = u64::MAX;
        let large_decimal = Decimal128 {
            scale: 0,
            value: i128::from(large_int),
        };

        assert_eq!(
            Number::Int64(large_int).cmp(&Number::Decimal128(large_decimal.clone())),
            Ordering::Equal
        );
        assert_eq!(
            Number::Decimal128(large_decimal.clone()).cmp(&Number::Int64(large_int)),
            Ordering::Equal
        );

        assert_eq!(
            Number::UInt64(large_uint).cmp(&Number::Decimal128(large_decimal.clone())),
            Ordering::Greater
        );
        assert_eq!(
            Number::Decimal128(large_decimal).cmp(&Number::UInt64(large_uint)),
            Ordering::Less
        );

        // Negative numbers
        let neg_int = -100;
        let neg_decimal = Decimal64 {
            scale: 0,
            value: -100,
        };

        assert_eq!(
            Number::Int64(neg_int).cmp(&Number::Decimal64(neg_decimal.clone())),
            Ordering::Equal
        );
        assert_eq!(
            Number::Decimal64(neg_decimal).cmp(&Number::UInt64(100)),
            Ordering::Less
        );

        // Zero values
        assert_eq!(Number::Int64(0).cmp(&Number::UInt64(0)), Ordering::Equal);
        assert_eq!(
            Number::Int64(0).cmp(&Number::Decimal64(Decimal64 { scale: 0, value: 0 })),
            Ordering::Equal
        );
        assert_eq!(
            Number::Int64(0).cmp(&Number::Decimal64(Decimal64 { scale: 5, value: 0 })),
            Ordering::Equal
        );
    }
}
