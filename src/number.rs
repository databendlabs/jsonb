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

use crate::constants::DECIMAL128_MAX;
use crate::constants::DECIMAL256_MAX;
use crate::constants::DECIMAL256_MIN;
use crate::constants::DECIMAL64_MAX;
use crate::constants::MAX_DECIMAL128_PRECISION;
use crate::constants::MAX_DECIMAL256_PRECISION;
use crate::constants::MAX_DECIMAL64_PRECISION;
use crate::eisel_lemire;
use crate::error::Result;
use crate::Error;

use ethnum::i256;
use ethnum::U256;
use ordered_float::OrderedFloat;
use serde::de;
use serde::de::Deserialize;
use serde::de::Deserializer;
use serde::de::Visitor;
use serde::ser::Serialize;
use serde::ser::Serializer;

/// `10^i` for each `i` whose power fits an `i128`, computed at compile time.
const I128_POWERS_OF_10: [i128; 39] = {
    let mut powers = [1; 39];
    let mut i = 1;
    while i < powers.len() {
        powers[i] = powers[i - 1] * 10;
        i += 1;
    }
    powers
};

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
    /// Creates a decimal of `value / 10^scale`.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonbNumber` if `scale` or the digits of `value`
    /// exceed precision 18.
    pub fn new(scale: u8, value: i64) -> Result<Self> {
        if usize::from(scale) <= MAX_DECIMAL64_PRECISION
            && value.unsigned_abs() <= DECIMAL64_MAX as u64
        {
            Ok(Self { scale, value })
        } else {
            Err(Error::InvalidJsonbNumber)
        }
    }

    /// Converts the decimal value to a floating-point representation.
    ///
    /// This is useful when you need to perform floating-point operations,
    /// but note that it may introduce precision loss inherent to floating-point arithmetic.
    pub fn to_float64(&self) -> f64 {
        decimal_to_f64(self.value.into(), self.scale)
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
    /// Creates a decimal of `value / 10^scale`.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonbNumber` if `scale` or the digits of `value`
    /// exceed precision 38.
    pub fn new(scale: u8, value: i128) -> Result<Self> {
        if usize::from(scale) <= MAX_DECIMAL128_PRECISION
            && value.unsigned_abs() <= DECIMAL128_MAX as u128
        {
            Ok(Self { scale, value })
        } else {
            Err(Error::InvalidJsonbNumber)
        }
    }

    /// Converts the decimal value to a floating-point representation.
    ///
    /// Note that for very large values, this conversion may lose precision
    /// as f64 has limited precision compared to i128.
    pub fn to_float64(&self) -> f64 {
        decimal_to_f64(self.value, self.scale)
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
    /// Creates a decimal of `value / 10^scale`.
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonbNumber` if `scale` or the digits of `value`
    /// exceed precision 76.
    pub fn new(scale: u8, value: i256) -> Result<Self> {
        if usize::from(scale) <= MAX_DECIMAL256_PRECISION
            && (DECIMAL256_MIN..=DECIMAL256_MAX).contains(&value)
        {
            Ok(Self { scale, value })
        } else {
            Err(Error::InvalidJsonbNumber)
        }
    }

    /// Converts the decimal value to a floating-point representation.
    ///
    /// For extremely large values, significant precision loss may occur
    /// as f64 has much lower precision than i256.
    pub fn to_float64(&self) -> f64 {
        if let Ok(value) = i128::try_from(self.value) {
            return decimal_to_f64(value, self.scale);
        }
        // `itoa` stops at `i128`, so wider values parse `<digits>e-<scale>`:
        // a sign, at most 78 digits, `e-` and a three-digit scale.
        use std::fmt::Write;
        let mut digits = DigitBuf::new();
        let digits = digits.format_u256(self.value.unsigned_abs());
        let sign = if self.value < i256::ZERO { "-" } else { "" };
        let mut text = StackBuf::<84>::new();
        write!(text, "{sign}{digits}e-{}", self.scale).expect("84 bytes fit every i256");
        fast_float2::parse(text.as_bytes()).unwrap_or(f64::NAN)
    }
}

/// Largest power of ten that `f64` represents exactly.
const MAX_EXACT_F64_POWER_OF_10: u8 = 22;

/// Longest `<digits>e-<scale>` text: a sign, the 39 digits of an `i128`,
/// `e-`, and a three-digit `u8` scale.
const SCIENTIFIC_TEXT_CAPACITY: usize = 1 + 39 + 2 + 3;

/// Returns the `f64` nearest to `value / 10^scale`.
///
/// When `|value| <= 2^53` and `10^scale` are both exact in `f64`, one IEEE
/// division rounds correctly. Converting a larger value first and dividing
/// after rounds twice, which can land on the neighboring `f64`:
/// 12345678901239047 / 100 gave 123456789012390.48 instead of
/// 123456789012390.47, so equal decimal and float values compared unequal.
/// Other values go through Eisel-Lemire, or failing that parse
/// `<digits>e-<scale>`; both round once.
fn decimal_to_f64(value: i128, scale: u8) -> f64 {
    if value.unsigned_abs() <= 1 << f64::MANTISSA_DIGITS && scale <= MAX_EXACT_F64_POWER_OF_10 {
        // Converting through `i64` avoids the slower `i128` to `f64` routine;
        // the value is exact in both.
        return value as i64 as f64 / 10_f64.powi(i32::from(scale));
    }
    // Eisel-Lemire computes the rounding from the integers directly; it gives
    // up on rare near-halfway products, and does not take mantissas above
    // `u64`, which then parse their text.
    if let Ok(mantissa) = u64::try_from(value.unsigned_abs()) {
        if let Some(float) = eisel_lemire::decimal_to_f64(value < 0, mantissa, scale) {
            return float;
        }
    }
    // Fallback: parse `<digits>e-<scale>`. Exponent notation needs no decimal
    // point or leading zeros, so only two integers are written.
    let mut digits = itoa::Buffer::new();
    let digits = digits.format(value).as_bytes();
    let mut exponent = itoa::Buffer::new();
    let exponent = exponent.format(scale).as_bytes();
    let mut text = [0; SCIENTIFIC_TEXT_CAPACITY];
    let (mantissa, rest) = text.split_at_mut(digits.len());
    mantissa.copy_from_slice(digits);
    rest[..2].copy_from_slice(b"e-");
    rest[2..2 + exponent.len()].copy_from_slice(exponent);
    let len = digits.len() + 2 + exponent.len();
    fast_float2::parse(&text[..len]).unwrap_or(f64::NAN)
}

/// Longest decimal text that serialization writes. Decimals with a longer
/// text, which need a scale above about 125, fail to serialize; the text
/// parser never produces them.
#[cfg(feature = "arbitrary_precision")]
const DECIMAL_JSON_CAPACITY: usize = 128;

/// Writes a float as serde_json's `Serializer::serialize_f64` does.
fn write_json_f64(v: f64, buf: &mut Vec<u8>) {
    if v.is_finite() {
        buf.extend_from_slice(zmij::Buffer::new().format_finite(v).as_bytes());
    } else {
        buf.extend_from_slice(b"null");
    }
}

/// A fixed-capacity buffer that formatting writes into without allocating.
/// Writing more than `N` bytes fails.
struct StackBuf<const N: usize> {
    buf: [u8; N],
    len: usize,
}

impl<const N: usize> StackBuf<N> {
    fn new() -> Self {
        Self {
            buf: [0; N],
            len: 0,
        }
    }

    fn as_bytes(&self) -> &[u8] {
        &self.buf[..self.len]
    }
}

impl<const N: usize> std::fmt::Write for StackBuf<N> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        let end = self.len + s.len();
        let dest = self.buf.get_mut(self.len..end).ok_or(std::fmt::Error)?;
        dest.copy_from_slice(s.as_bytes());
        self.len = end;
        Ok(())
    }
}

/// Stack space for the decimal digits of an integer or decimal magnitude.
struct DigitBuf {
    itoa: itoa::Buffer,
    /// Digits of magnitudes beyond `u128`, right-aligned; `U256::MAX` has 78.
    /// Set only when needed, so creating the buffer does not clear 78 bytes.
    wide: Option<[u8; 78]>,
}

impl DigitBuf {
    #[inline]
    fn new() -> Self {
        Self {
            itoa: itoa::Buffer::new(),
            wide: None,
        }
    }

    #[inline]
    fn format_u64(&mut self, value: u64) -> &str {
        self.itoa.format(value)
    }

    #[inline]
    fn format_u128(&mut self, value: u128) -> &str {
        self.itoa.format(value)
    }

    /// Writes magnitudes beyond `u128` as base-10^38 chunks, each a `u128`,
    /// instead of using `ethnum`'s `Display`, whose raw-pointer code Miri's
    /// Stacked Borrows model rejects.
    fn format_u256(&mut self, value: U256) -> &str {
        if let Ok(value) = u128::try_from(value) {
            return self.format_u128(value);
        }
        const CHUNK_DIGITS: usize = I128_POWERS_OF_10.len() - 1;
        let base = U256::from(I128_POWERS_OF_10[CHUNK_DIGITS] as u128);
        let wide = self.wide.insert([0; 78]);
        let mut value = value;
        let mut end = wide.len();
        // Every chunk but the most significant has exactly 38 digits.
        while value >= base {
            let chunk = self.itoa.format((value % base).as_u128()).as_bytes();
            let start = end - CHUNK_DIGITS;
            wide[start..end - chunk.len()].fill(b'0');
            wide[end - chunk.len()..end].copy_from_slice(chunk);
            end = start;
            value /= base;
        }
        let first = self.itoa.format(value.as_u128()).as_bytes();
        let start = end - first.len();
        wide[start..end].copy_from_slice(first);
        std::str::from_utf8(&wide[start..]).expect("digits are ASCII")
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
    ///
    /// When the `arbitrary_precision` feature is enabled, decimal types are serialized with full precision
    /// using the optimized formatting functions. When disabled, decimal types are converted to f64.
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Number::Int64(v) => serializer.serialize_i64(*v),
            Number::UInt64(v) => serializer.serialize_u64(*v),
            Number::Float64(v) => serializer.serialize_f64(*v),
            #[cfg(feature = "arbitrary_precision")]
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                use serde::ser::SerializeStruct;
                const NUMBER_TOKEN: &str = "$serde_json::private::Number";

                if serializer.is_human_readable() {
                    let text = self.format_decimal_json().map_err(|e| {
                        serde::ser::Error::custom(format!("Format decimal error: {e}"))
                    })?;
                    let num_str = std::str::from_utf8(text.as_bytes()).map_err(|e| {
                        serde::ser::Error::custom(format!("Invalid decimal number: {e}"))
                    })?;

                    let mut serialize_struct = serializer.serialize_struct(NUMBER_TOKEN, 1)?;
                    serialize_struct.serialize_field(NUMBER_TOKEN, num_str)?;
                    serialize_struct.end()
                } else {
                    use crate::constants::NUMBER_STRUCT_FIELD_HIGH_VALUE;
                    use crate::constants::NUMBER_STRUCT_FIELD_LOW_VALUE;
                    use crate::constants::NUMBER_STRUCT_FIELD_SCALE;
                    use crate::constants::NUMBER_STRUCT_FIELD_VALUE;
                    use crate::constants::NUMBER_STRUCT_TOKEN;

                    let mut serialize_struct =
                        serializer.serialize_struct(NUMBER_STRUCT_TOKEN, 2)?;
                    match self {
                        Number::Decimal64(v) => {
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_SCALE, &v.scale)?;
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_VALUE, &v.value)?;
                        }
                        Number::Decimal128(v) => {
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_SCALE, &v.scale)?;
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_VALUE, &v.value)?;
                        }
                        Number::Decimal256(v) => {
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_SCALE, &v.scale)?;
                            let (high_value, low_value) = v.value.into_words();
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_HIGH_VALUE, &high_value)?;
                            serialize_struct
                                .serialize_field(NUMBER_STRUCT_FIELD_LOW_VALUE, &low_value)?;
                        }
                        _ => unreachable!(),
                    }
                    serialize_struct.end()
                }
            }
            // Without arbitrary_precision, decimals serialize as the nearest
            // `f64`. Converting the unscaled value first and dividing after
            // rounded twice, so a decimal could serialize as a neighboring
            // float of the one `as_f64` returns.
            #[cfg(not(feature = "arbitrary_precision"))]
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                serializer.serialize_f64(self.as_f64())
            }
        }
    }
}

/// The first byte of a number in the comparable encoding, in ascending order.
const COMPARABLE_NEG_INFINITY: u8 = 0x01;
const COMPARABLE_NEGATIVE: u8 = 0x02;
const COMPARABLE_ZERO: u8 = 0x03;
const COMPARABLE_POSITIVE: u8 = 0x04;
const COMPARABLE_POS_INFINITY: u8 = 0x05;
const COMPARABLE_NAN: u8 = 0x06;

impl Number {
    /// Returns the i128 representation of the number, if possible.
    ///
    /// Decimal values are converted only when their fractional part is zero.
    /// Floating-point values are converted only when they already represent an
    /// integer value. This method returns `None` if the value cannot be
    /// represented as an `i128`.
    pub fn as_i128(&self) -> Option<i128> {
        match self {
            Number::Int64(v) => Some(*v as i128),
            Number::UInt64(v) => Some(*v as i128),
            Number::Float64(v) => integral_float_in(*v, I128_FLOAT_RANGE).map(|v| v as i128),
            Number::Decimal64(v) => exact_decimal_i128(v.value as i128, v.scale),
            Number::Decimal128(v) => exact_decimal_i128(v.value, v.scale),
            Number::Decimal256(v) => {
                exact_decimal_i256(v.value, v.scale).and_then(|value| i128::try_from(value).ok())
            }
        }
    }

    /// Returns the i64 representation of the number, if possible.
    ///
    /// Decimal values are converted only when their fractional part is zero.
    /// Floating-point values are converted only when they already represent an
    /// integer value. This method returns `None` if the value cannot be
    /// represented as an `i64`.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Number::Int64(v) => Some(*v),
            Number::UInt64(v) => i64::try_from(*v).ok(),
            Number::Float64(v) => integral_float_in(*v, I64_FLOAT_RANGE).map(|v| v as i64),
            _ => self.as_i128().and_then(|v| i64::try_from(v).ok()),
        }
    }

    /// Returns the u64 representation of the number, if possible.
    ///
    /// Decimal values are converted only when their fractional part is zero.
    /// Floating-point values are converted only when they already represent an
    /// integer value. This method returns `None` if the value is negative or
    /// cannot be represented as a `u64`.
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Number::Int64(v) => u64::try_from(*v).ok(),
            Number::UInt64(v) => Some(*v),
            Number::Float64(v) => integral_float_in(*v, U64_FLOAT_RANGE).map(|v| v as u64),
            _ => self.as_i128().and_then(|v| u64::try_from(v).ok()),
        }
    }

    /// Returns the i128 representation of the number after rounding if needed.
    ///
    /// Decimal and floating-point values are rounded to the nearest integer
    /// before conversion. This method returns `None` if the rounded value
    /// cannot be represented as an `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match self {
            Number::Int64(v) => Some(*v as i128),
            Number::UInt64(v) => Some(*v as i128),
            Number::Float64(v) => integral_float_in(v.round(), I128_FLOAT_RANGE).map(|v| v as i128),
            Number::Decimal64(v) => round_decimal_i128(v.value as i128, v.scale),
            Number::Decimal128(v) => round_decimal_i128(v.value, v.scale),
            Number::Decimal256(v) => {
                round_decimal_i256(v.value, v.scale).and_then(|value| i128::try_from(value).ok())
            }
        }
    }

    /// Returns the i64 representation of the number after rounding if needed.
    ///
    /// Decimal and floating-point values are rounded to the nearest integer
    /// before conversion. This method returns `None` if the rounded value
    /// cannot be represented as an `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        self.to_i128().and_then(|value| i64::try_from(value).ok())
    }

    /// Returns the u64 representation of the number after rounding if needed.
    ///
    /// Decimal and floating-point values are rounded to the nearest integer
    /// before conversion. This method returns `None` if the rounded value
    /// is negative or cannot be represented as a `u64`.
    pub fn to_u64(&self) -> Option<u64> {
        self.to_i128().and_then(|value| u64::try_from(value).ok())
    }

    /// Returns the f64 representation of the number.
    ///
    /// This method always returns a value, but may lose precision for very large numbers.
    #[inline]
    pub fn as_f64(&self) -> f64 {
        match self {
            Number::Int64(v) => *v as f64,
            Number::UInt64(v) => *v as f64,
            Number::Float64(v) => *v,
            Number::Decimal64(v) => v.to_float64(),
            Number::Decimal128(v) => v.to_float64(),
            Number::Decimal256(v) => v.to_float64(),
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
            // `-2^63` is the one negated `u64` above `i64::MAX` that fits.
            Number::UInt64(v) => Self::from_integer_result(Some(-i128::from(*v)), false),
            Number::Float64(v) => Ok(Number::Float64(*v * -1.0)),
            Number::Decimal64(v) => {
                let Some(neg_value) = v.value.checked_neg() else {
                    return Err(Error::Message("Decimal64 overflow".to_string()));
                };
                let neg_dec = Decimal64 {
                    scale: v.scale,
                    value: neg_value,
                };
                Ok(Number::Decimal64(neg_dec))
            }
            Number::Decimal128(v) => {
                let Some(neg_value) = v.value.checked_neg() else {
                    return Err(Error::Message("Decimal128 overflow".to_string()));
                };
                let neg_dec = Decimal128 {
                    scale: v.scale,
                    value: neg_value,
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
        if let Some((a, b, both_signed)) = self.integer_operands(&other) {
            return Self::from_integer_result(a.checked_add(b), both_signed);
        }
        Ok(Number::Float64(self.as_f64() + other.as_f64()))
    }

    /// Returns the difference of the number and another number.
    ///
    /// This method returns an error if the difference would overflow.
    pub fn sub(&self, other: Number) -> Result<Number> {
        if let Some((a, b, both_signed)) = self.integer_operands(&other) {
            return Self::from_integer_result(a.checked_sub(b), both_signed);
        }
        Ok(Number::Float64(self.as_f64() - other.as_f64()))
    }

    /// Returns the product of the number and another number.
    ///
    /// This method returns an error if the product would overflow.
    pub fn mul(&self, other: Number) -> Result<Number> {
        if let Some((a, b, both_signed)) = self.integer_operands(&other) {
            return Self::from_integer_result(a.checked_mul(b), both_signed);
        }
        Ok(Number::Float64(self.as_f64() * other.as_f64()))
    }

    /// Returns the quotient of the number and another number.
    ///
    /// This method returns an error if the divisor is zero.
    pub fn div(&self, other: Number) -> Result<Number> {
        let a_float = self.as_f64();
        let b_float = other.as_f64();
        if b_float == 0.0 {
            return Err(Error::Message("Division by zero".to_string()));
        }
        Ok(Number::Float64(a_float / b_float))
    }

    /// Returns the remainder of the number divided by another number.
    ///
    /// This method returns an error if the divisor is zero.
    pub fn rem(&self, other: Number) -> Result<Number> {
        if let Some((a, b, both_signed)) = self.integer_operands(&other) {
            if b == 0 {
                return Err(Error::Message("Division by zero".to_string()));
            }
            return Self::from_integer_result(a.checked_rem(b), both_signed);
        }
        let divisor = other.as_f64();
        if divisor == 0.0 {
            return Err(Error::Message("Division by zero".to_string()));
        }
        Ok(Number::Float64(self.as_f64() % divisor))
    }

    /// Returns the exact values of this number and `other` if both are
    /// integers, and whether both are `Int64`.
    fn integer_operands(&self, other: &Number) -> Option<(i128, i128, bool)> {
        let value = |n: &Number| match n {
            Number::Int64(v) => Some(i128::from(*v)),
            Number::UInt64(v) => Some(i128::from(*v)),
            _ => None,
        };
        let both_signed = matches!((self, other), (Number::Int64(_), Number::Int64(_)));
        Some((value(self)?, value(other)?, both_signed))
    }

    /// Builds the result of integer arithmetic from its exact value.
    ///
    /// Two `Int64` operands give an `Int64` result. Otherwise a non-negative
    /// result is a `UInt64` and a negative one an `Int64`. A value outside
    /// those ranges, or no value at all, is an overflow. Computing in `i128`
    /// first keeps mixed `Int64`/`UInt64` operands from being cast to the
    /// wrong type, which made `u64::MAX + (-1)` return `-2`.
    fn from_integer_result(value: Option<i128>, both_signed: bool) -> Result<Number> {
        let overflow = || {
            let ty = if both_signed { "Int64" } else { "UInt64" };
            Error::Message(format!("{ty} overflow"))
        };
        let value = value.ok_or_else(overflow)?;
        if both_signed {
            return i64::try_from(value)
                .map(Number::Int64)
                .map_err(|_| overflow());
        }
        match u64::try_from(value) {
            Ok(v) => Ok(Number::UInt64(v)),
            Err(_) => i64::try_from(value)
                .map(Number::Int64)
                .map_err(|_| overflow()),
        }
    }

    /// Returns an integer or a decimal narrower than `Decimal256` as
    /// `(value, scale)`, its value being `value / 10^scale`.
    fn as_scaled_i128(&self) -> Option<(i128, u8)> {
        match self {
            Number::Int64(v) => Some((i128::from(*v), 0)),
            Number::UInt64(v) => Some((i128::from(*v), 0)),
            Number::Decimal64(d) => Some((i128::from(d.value), d.scale)),
            Number::Decimal128(d) => Some((d.value, d.scale)),
            Number::Float64(_) | Number::Decimal256(_) => None,
        }
    }

    /// Returns an integer or a decimal as `(value, scale)`, its value being
    /// `value / 10^scale`.
    fn as_scaled_i256(&self) -> Option<(i256, u8)> {
        match self {
            Number::Decimal256(d) => Some((d.value, d.scale)),
            Number::Float64(_) => None,
            _ => self
                .as_scaled_i128()
                .map(|(value, scale)| (i256::from(value), scale)),
        }
    }

    /// Compares this integer or decimal with `float`.
    ///
    /// `as_f64` rounds to the nearest float. If that is not `float`, the exact
    /// value and `float`'s shortest decimal round to different floats, so they
    /// order like those floats. Only numbers that round to `float` itself
    /// need the exact comparison.
    fn cmp_with_float(&self, float: f64) -> Ordering {
        if float.is_nan() {
            return Ordering::Less;
        }
        match self.as_f64().partial_cmp(&float) {
            Some(Ordering::Equal) | None => self.cmp_exact(&Number::Float64(float)),
            Some(order) => order,
        }
    }

    /// Compares two numbers by their exact values, taking a float as its
    /// shortest decimal.
    ///
    /// This is slower than the comparisons in `cmp`, which use it only where
    /// they cannot decide: decimals whose rescaled values overflow, and
    /// numbers that round to the float they are compared with. Two floats
    /// compare as floats, which orders them the same way.
    fn cmp_exact(&self, other: &Number) -> Ordering {
        if let (Number::Float64(l), Number::Float64(r)) = (self, other) {
            return OrderedFloat(*l).cmp(&OrderedFloat(*r));
        }
        match (ExactDecimal::new(self), ExactDecimal::new(other)) {
            (Some(l), Some(r)) => l.cmp(&r),
            // Only non-finite floats have no decimal, and `cmp_with_float`
            // orders those without coming here.
            _ => OrderedFloat(self.as_f64()).cmp(&OrderedFloat(other.as_f64())),
        }
    }

    /// Appends the number as JSON text to `buf`, exactly as `Serialize`
    /// writes it through serde_json, whose integer and float formatting
    /// (itoa and zmij) this mirrors. Non-finite floats are written as `null`.
    pub(crate) fn write_json(&self, buf: &mut Vec<u8>) -> Result<()> {
        match self {
            Number::Int64(v) => buf.extend_from_slice(itoa::Buffer::new().format(*v).as_bytes()),
            Number::UInt64(v) => buf.extend_from_slice(itoa::Buffer::new().format(*v).as_bytes()),
            Number::Float64(v) => write_json_f64(*v, buf),
            #[cfg(feature = "arbitrary_precision")]
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                let text = self
                    .format_decimal_json()
                    .map_err(|_| Error::InvalidJsonbNumber)?;
                buf.extend_from_slice(text.as_bytes());
            }
            #[cfg(not(feature = "arbitrary_precision"))]
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                write_json_f64(self.as_f64(), buf)
            }
        }
        Ok(())
    }

    /// Formats a decimal as the JSON text that `Serialize` and
    /// [`Number::write_json`] write with `arbitrary_precision`.
    ///
    /// Fails if the text is longer than [`DECIMAL_JSON_CAPACITY`] bytes.
    ///
    /// # Panics
    ///
    /// Panics if the number is not a decimal.
    #[cfg(feature = "arbitrary_precision")]
    fn format_decimal_json(
        &self,
    ) -> std::result::Result<StackBuf<DECIMAL_JSON_CAPACITY>, std::fmt::Error> {
        let mut text = StackBuf::new();
        self.write_decimal(&mut text)?;
        Ok(text)
    }

    /// Returns the sign, the decimal digits of the magnitude and the scale of
    /// an integer or decimal, whose value is `±digits / 10^scale`, or `None`
    /// for a float.
    #[inline]
    fn digits<'a>(&self, buf: &'a mut DigitBuf) -> Option<(bool, &'a str, u8)> {
        Some(match self {
            Number::Int64(v) => (*v < 0, buf.format_u64(v.unsigned_abs()), 0),
            Number::UInt64(v) => (false, buf.format_u64(*v), 0),
            Number::Decimal64(d) => (d.value < 0, buf.format_u64(d.value.unsigned_abs()), d.scale),
            Number::Decimal128(d) => (
                d.value < 0,
                buf.format_u128(d.value.unsigned_abs()),
                d.scale,
            ),
            Number::Decimal256(d) => (
                d.value < i256::ZERO,
                buf.format_u256(d.value.unsigned_abs()),
                d.scale,
            ),
            Number::Float64(_) => return None,
        })
    }

    /// Writes an integer or decimal as plain decimal text: a `-` for a
    /// negative value, the integer digits, and for a nonzero scale a `.` and
    /// exactly `scale` fractional digits, so `Decimal64 { scale: 3, value: -5 }`
    /// writes `-0.005`. Any scale is written, even one beyond the precision.
    ///
    /// # Panics
    ///
    /// Panics if the number is a float.
    fn write_decimal(&self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
        const ZEROS: &str = "0000000000000000000000000000000000000000000000000000000000000000";
        let mut buf = DigitBuf::new();
        let (negative, digits, scale) = self.digits(&mut buf).expect("not a float");
        let scale = usize::from(scale);
        if negative {
            f.write_char('-')?;
        }
        if scale == 0 {
            return f.write_str(digits);
        }
        if digits.len() > scale {
            let (integer, fraction) = digits.split_at(digits.len() - scale);
            f.write_str(integer)?;
            f.write_char('.')?;
            return f.write_str(fraction);
        }
        f.write_str("0.")?;
        let mut zeros = scale - digits.len();
        while zeros > 0 {
            let n = zeros.min(ZEROS.len());
            f.write_str(&ZEROS[..n])?;
            zeros -= n;
        }
        f.write_str(digits)
    }

    /// Appends bytes that order byte-wise like `Number::cmp`, for
    /// `RawJsonb::convert_to_comparable`.
    ///
    /// A finite nonzero number is written as its exact value
    /// `±0.d1d2...dn × 10^e`, with `d1` and `dn` nonzero, so numbers of
    /// different types order by value. A float is written as its shortest
    /// decimal, the value `cmp` compares it by: the float `0.1` and the
    /// decimal `0.1` write the same bytes. Zero, `-0.0` included, the
    /// infinities and `NaN` write one marker byte each.
    ///
    /// A nonzero value is a sign marker, `e` as a big-endian `u16` biased by
    /// `0x8000`, the digits two to a byte as `1 + 10 * d + d'` (an odd last
    /// digit pairs with 0), and a 0 terminator. A larger exponent, or a larger
    /// digit at the first difference, means a larger magnitude, and a digit
    /// byte is above the terminator, so a longer digit string with the same
    /// prefix is larger. For a negative value every byte after the marker is
    /// inverted, which reverses that order.
    ///
    /// No encoding is a prefix of another, so two different numbers differ
    /// before either ends, and the bytes that follow them never decide.
    /// Writing numbers as `f64` used to give different numbers the same bytes,
    /// e.g. `2^53` and `2^53 + 1`; inside an array or object the following
    /// bytes then decided, which could reverse the order of the two containers
    /// (found by fuzzing).
    pub(crate) fn write_comparable(&self, buf: &mut Vec<u8>) {
        let mut digit_buf = DigitBuf::new();
        let (negative, digits, scale) = match self {
            Number::Float64(v) => {
                let Some(decimal) = ExactDecimal::from_f64(*v) else {
                    return buf.push(if v.is_nan() {
                        COMPARABLE_NAN
                    } else if *v > 0.0 {
                        COMPARABLE_POS_INFINITY
                    } else {
                        COMPARABLE_NEG_INFINITY
                    });
                };
                // A float's shortest decimal has at most 17 digits.
                let magnitude = u64::try_from(decimal.magnitude).expect("at most 17 digits");
                (
                    decimal.negative,
                    digit_buf.format_u64(magnitude),
                    decimal.scale,
                )
            }
            Number::Int64(v) => (*v < 0, digit_buf.format_u64(v.unsigned_abs()), 0),
            Number::UInt64(v) => (false, digit_buf.format_u64(*v), 0),
            Number::Decimal64(d) => (
                d.value < 0,
                digit_buf.format_u64(d.value.unsigned_abs()),
                i32::from(d.scale),
            ),
            Number::Decimal128(d) => (
                d.value < 0,
                digit_buf.format_u128(d.value.unsigned_abs()),
                i32::from(d.scale),
            ),
            Number::Decimal256(d) => (
                d.value < i256::ZERO,
                digit_buf.format_u256(d.value.unsigned_abs()),
                i32::from(d.scale),
            ),
        };
        let digits = digits.as_bytes();
        let Some(last) = digits.iter().rposition(|&d| d != b'0') else {
            return buf.push(COMPARABLE_ZERO);
        };
        // Decimals have at most 78 digits and scales up to 255; floats have
        // exponents from -323 to 309.
        let exponent =
            i16::try_from(digits.len() as i32 - scale).expect("decimal exponents fit an i16");
        let start = buf.len();
        buf.push(if negative {
            COMPARABLE_NEGATIVE
        } else {
            COMPARABLE_POSITIVE
        });
        buf.extend_from_slice(&((exponent as u16) ^ 0x8000).to_be_bytes());
        for pair in digits[..=last].chunks(2) {
            let high = pair[0] - b'0';
            let low = pair.get(1).map_or(0, |d| d - b'0');
            buf.push(1 + 10 * high + low);
        }
        buf.push(0);
        if negative {
            for byte in &mut buf[start + 1..] {
                *byte = !*byte;
            }
        }
    }
}

/// `[-2^63, 2^63)`, the floats that `as i64` converts exactly. The bounds
/// are exact floats; `i64::MAX as f64` rounds up to `2^63`.
const I64_FLOAT_RANGE: std::ops::Range<f64> = (i64::MIN as f64)..-(i64::MIN as f64);

/// `[0, 2^64)`, the floats that `as u64` converts exactly.
const U64_FLOAT_RANGE: std::ops::Range<f64> = 0.0..-2.0 * (i64::MIN as f64);

/// `[-2^127, 2^127)`, the floats that `as i128` converts exactly.
const I128_FLOAT_RANGE: std::ops::Range<f64> = (i128::MIN as f64)..-(i128::MIN as f64);

/// Returns `value` if it is an integer within `range`, so the caller's `as`
/// cast to the matching integer type is exact. `NaN` and the infinities have
/// a `NaN` fraction and return `None`; `-0.0` counts as 0.
#[inline]
fn integral_float_in(value: f64, range: std::ops::Range<f64>) -> Option<f64> {
    (value.fract() == 0.0 && range.contains(&value)).then_some(value)
}

fn exact_decimal_i128(value: i128, scale: u8) -> Option<i128> {
    if scale == 0 {
        return Some(value);
    }

    let Some(divisor) = I128_POWERS_OF_10.get(scale as usize) else {
        return if value == 0 { Some(0) } else { None };
    };

    if value % divisor == 0 {
        Some(value / divisor)
    } else {
        None
    }
}

fn round_decimal_i128(value: i128, scale: u8) -> Option<i128> {
    if scale == 0 {
        return Some(value);
    }

    let Some(divisor) = I128_POWERS_OF_10.get(scale as usize) else {
        // 10^scale no longer fits in i128, so any i128-backed decimal rounds to 0.
        return Some(0);
    };

    let quotient = value / divisor;
    let remainder = value % divisor;
    let abs_remainder = remainder.unsigned_abs();
    let divisor = *divisor as u128;
    let round_up = abs_remainder >= divisor - abs_remainder;

    if !round_up {
        Some(quotient)
    } else if value >= 0 {
        quotient.checked_add(1)
    } else {
        quotient.checked_sub(1)
    }
}

#[inline]
fn signed_i256_from_abs(abs: U256, negative: bool) -> Option<i256> {
    let value = i256::try_from(abs).ok()?;
    if negative {
        i256::ZERO.checked_sub(value)
    } else {
        Some(value)
    }
}

fn exact_decimal_i256(value: i256, scale: u8) -> Option<i256> {
    if scale == 0 {
        return Some(value);
    }

    let Some(divisor) = U256::new(10).checked_pow(scale as u32) else {
        return if value == i256::ZERO {
            Some(i256::ZERO)
        } else {
            None
        };
    };

    let negative = value < i256::ZERO;
    let abs_value = value.unsigned_abs();
    let quotient = abs_value / divisor;
    let remainder = abs_value % divisor;
    if remainder != U256::ZERO {
        return None;
    }

    signed_i256_from_abs(quotient, negative)
}

fn round_decimal_i256(value: i256, scale: u8) -> Option<i256> {
    if scale == 0 {
        return Some(value);
    }

    let Some(divisor) = U256::new(10).checked_pow(scale as u32) else {
        // 10^scale exceeds the i256 range by enough that the rounded result is always 0.
        return Some(i256::ZERO);
    };

    let negative = value < i256::ZERO;
    let abs_value = value.unsigned_abs();
    let quotient = abs_value / divisor;
    let remainder = abs_value % divisor;
    let round_up = remainder >= divisor - remainder;
    let rounded = if round_up {
        quotient.checked_add(U256::new(1))?
    } else {
        quotient
    };

    signed_i256_from_abs(rounded, negative)
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
    /// Integers and decimals compare by their exact values. A float compares
    /// as the shortest decimal that parses back to it, so the float `0.1`
    /// equals the decimal `0.1`. `NaN` is greater than every other number and
    /// equal to itself, as in `OrderedFloat`.
    ///
    /// Each number thus orders by one exact value, which keeps the order
    /// transitive. Converting integers and decimals to `f64` to compare them
    /// with floats did not: `2^53 + 1` equaled the float `2^53`, which equals
    /// `2^53`, though `2^53 + 1 > 2^53`.
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Number::Int64(l), Number::Int64(r)) => l.cmp(r),
            (Number::UInt64(l), Number::UInt64(r)) => l.cmp(r),
            (Number::Int64(l), Number::UInt64(r)) => match u64::try_from(*l) {
                Ok(l) => l.cmp(r),
                Err(_) => Ordering::Less,
            },
            (Number::UInt64(l), Number::Int64(r)) => match u64::try_from(*r) {
                Ok(r) => l.cmp(&r),
                Err(_) => Ordering::Greater,
            },
            (Number::Decimal64(l), Number::Decimal64(r)) if l.scale == r.scale => {
                l.value.cmp(&r.value)
            }
            (Number::Decimal128(l), Number::Decimal128(r)) if l.scale == r.scale => {
                l.value.cmp(&r.value)
            }
            (Number::Decimal256(l), Number::Decimal256(r)) if l.scale == r.scale => {
                l.value.cmp(&r.value)
            }
            (Number::Float64(l), Number::Float64(r)) => OrderedFloat(*l).cmp(&OrderedFloat(*r)),
            (Number::Float64(l), _) => other.cmp_with_float(*l).reverse(),
            (_, Number::Float64(r)) => self.cmp_with_float(*r),
            // Integers and decimals compare as `value / 10^scale` in the
            // narrowest type that holds both, or exactly if rescaling
            // overflows.
            _ => match (self.as_scaled_i128(), other.as_scaled_i128()) {
                (Some((l, l_scale)), Some((r, r_scale))) => {
                    match adjust_decimal_scales(l, l_scale, r, r_scale) {
                        Some((l, r)) => l.cmp(&r),
                        None => self.cmp_exact(other),
                    }
                }
                _ => match (self.as_scaled_i256(), other.as_scaled_i256()) {
                    (Some((l, l_scale)), Some((r, r_scale))) => {
                        match adjust_decimal256_scales(l, l_scale, r, r_scale) {
                            Some((l, r)) => l.cmp(&r),
                            None => self.cmp_exact(other),
                        }
                    }
                    _ => unreachable!("floats are compared above"),
                },
            },
        }
    }
}

/// A finite number as its exact value `(-1)^negative * magnitude / 10^scale`.
struct ExactDecimal {
    negative: bool,
    magnitude: U256,
    /// 0 to 255 for decimals. Floats range from -292, for
    /// `1.7976931348623157e308`, to under 340, for the smallest floats.
    scale: i32,
}

impl ExactDecimal {
    /// Returns the exact value of `number`, or `None` for `NaN` and the
    /// infinities.
    fn new(number: &Number) -> Option<Self> {
        let (negative, magnitude, scale) = match number {
            Number::Int64(v) => (*v < 0, U256::from(v.unsigned_abs()), 0),
            Number::UInt64(v) => (false, U256::from(*v), 0),
            Number::Decimal64(d) => (d.value < 0, U256::from(d.value.unsigned_abs()), d.scale),
            Number::Decimal128(d) => (d.value < 0, U256::from(d.value.unsigned_abs()), d.scale),
            Number::Decimal256(d) => (d.value < i256::ZERO, d.value.unsigned_abs(), d.scale),
            Number::Float64(v) => return Self::from_f64(*v),
        };
        Some(Self {
            negative,
            magnitude,
            scale: i32::from(scale),
        })
    }

    /// Returns the shortest decimal that parses back to `value`, which is
    /// the text `zmij` writes, or `None` for `NaN` and the infinities.
    fn from_f64(value: f64) -> Option<Self> {
        if !value.is_finite() {
            return None;
        }
        // Below 2^53 an integral float is an exact integer, which is its own
        // shortest decimal; `zmij` would write the same digits.
        if value.fract() == 0.0 && value.abs() < (1u64 << f64::MANTISSA_DIGITS) as f64 {
            return Some(Self {
                negative: value.is_sign_negative(),
                magnitude: U256::from(value.abs() as u64),
                scale: 0,
            });
        }
        let mut buf = zmij::Buffer::new();
        // An optional `-`, digits with an optional `.` fraction, and an
        // optional exponent: `0.1`, `123.0`, `1e+300`, `-5e-324`. There are
        // at most 17 significant digits, so the mantissa fits a `u128`.
        let text = buf.format_finite(value).as_bytes();
        let (negative, text) = match text.split_first() {
            Some((b'-', rest)) => (true, rest),
            _ => (false, text),
        };
        let (digits, exponent) = match text.iter().position(|&b| b == b'e') {
            Some(e) => (&text[..e], &text[e + 1..]),
            None => (text, &[][..]),
        };
        let mut mantissa = 0u128;
        let mut scale = 0i32;
        let mut in_fraction = false;
        for &b in digits {
            if b == b'.' {
                in_fraction = true;
            } else {
                mantissa = mantissa * 10 + u128::from(b - b'0');
                scale += i32::from(in_fraction);
            }
        }
        let (exponent_negative, exponent_digits) = match exponent.split_first() {
            Some((b'-', rest)) => (true, rest),
            Some((b'+', rest)) => (false, rest),
            _ => (false, exponent),
        };
        let exponent = exponent_digits
            .iter()
            .fold(0i32, |e, &b| e * 10 + i32::from(b - b'0'));
        if exponent_negative {
            scale += exponent;
        } else {
            scale -= exponent;
        }
        Some(Self {
            negative,
            magnitude: U256::from(mantissa),
            scale,
        })
    }
}

impl Ord for ExactDecimal {
    fn cmp(&self, other: &Self) -> Ordering {
        // -1, 0 or 1; zero has either sign, as for `-0.0`.
        let sign = |d: &Self| match (d.magnitude == U256::ZERO, d.negative) {
            (true, _) => 0,
            (false, true) => -1,
            (false, false) => 1,
        };
        let (l, r) = (sign(self), sign(other));
        if l != r || l == 0 {
            return l.cmp(&r);
        }
        let order = self.cmp_magnitude(other);
        if l < 0 {
            order.reverse()
        } else {
            order
        }
    }
}

impl PartialOrd for ExactDecimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ExactDecimal {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for ExactDecimal {}

impl ExactDecimal {
    /// Compares the magnitudes by bringing both to the larger scale.
    fn cmp_magnitude(&self, other: &Self) -> Ordering {
        if self.scale == other.scale {
            return self.magnitude.cmp(&other.magnitude);
        }
        let scale = self.scale.max(other.scale);
        let rescale = |d: &Self| {
            let mut wide = WideUint::new(d.magnitude);
            wide.mul_pow10(scale.abs_diff(d.scale));
            wide
        };
        rescale(self).cmp(&rescale(other))
    }
}

/// A 2048-bit unsigned integer, in 64-bit limbs stored most significant
/// first, so the derived `Ord` compares by value.
///
/// That fits every rescaled magnitude in `ExactDecimal::cmp_magnitude`, which
/// compares a float with an integer or decimal, or two decimals, but never two
/// floats. The largest is a float mantissa below 2^57 times 10^547, between
/// scales -292 and 255, which is below 2^1875. Decimal magnitudes are below
/// 2^256 and need at most 10^340, which gives below 2^1386.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct WideUint([u64; 32]);

impl WideUint {
    fn new(value: U256) -> Self {
        let (high, low) = value.into_words();
        let mut limbs = [0; 32];
        limbs[28..].copy_from_slice(&[
            (high >> 64) as u64,
            high as u64,
            (low >> 64) as u64,
            low as u64,
        ]);
        Self(limbs)
    }

    fn mul_small(&mut self, factor: u64) {
        let mut carry = 0u128;
        for limb in self.0.iter_mut().rev() {
            let product = u128::from(*limb) * u128::from(factor) + carry;
            *limb = product as u64;
            carry = product >> 64;
        }
        debug_assert_eq!(carry, 0, "WideUint overflow");
    }

    fn mul_pow10(&mut self, mut exponent: u32) {
        const POW10_19: u64 = 10_000_000_000_000_000_000;
        while exponent >= 19 {
            self.mul_small(POW10_19);
            exponent -= 19;
        }
        if exponent > 0 {
            self.mul_small(10_u64.pow(exponent));
        }
    }
}

/// Brings two `i128` decimals to the larger scale, or returns `None` if that
/// overflows.
fn adjust_decimal_scales(
    l_val: i128,
    l_scale: u8,
    r_val: i128,
    r_scale: u8,
) -> Option<(i128, i128)> {
    // `10^diff` fits an `i128` up to 38, the end of the table.
    let rescale = |value: i128, diff: u8| {
        I128_POWERS_OF_10
            .get(usize::from(diff))
            .and_then(|factor| value.checked_mul(*factor))
    };
    match l_scale.cmp(&r_scale) {
        Ordering::Greater => Some((l_val, rescale(r_val, l_scale - r_scale)?)),
        Ordering::Less => Some((rescale(l_val, r_scale - l_scale)?, r_val)),
        Ordering::Equal => Some((l_val, r_val)),
    }
}

/// Brings two `i256` decimals to the larger scale, or returns `None` if that
/// overflows.
fn adjust_decimal256_scales(
    l_val: i256,
    l_scale: u8,
    r_val: i256,
    r_scale: u8,
) -> Option<(i256, i256)> {
    let rescale = |value: i256, diff: u8| value.checked_mul(pow10_i256(diff)?);
    match l_scale.cmp(&r_scale) {
        Ordering::Greater => Some((l_val, rescale(r_val, l_scale - r_scale)?)),
        Ordering::Less => Some((rescale(l_val, r_scale - l_scale)?, r_val)),
        Ordering::Equal => Some((l_val, r_val)),
    }
}

/// Returns `10^exponent` if it fits an `i256`, which holds up to `10^76`.
///
/// Powers up to `10^38` come from `I128_POWERS_OF_10`, and larger ones take a
/// single multiplication by `10^38`; `checked_pow` multiplies once per bit of
/// the exponent.
fn pow10_i256(exponent: u8) -> Option<i256> {
    let exponent = usize::from(exponent);
    let max = I128_POWERS_OF_10.len() - 1;
    match exponent.checked_sub(max) {
        None | Some(0) => Some(i256::from(I128_POWERS_OF_10[exponent])),
        Some(rest) => {
            let rest = *I128_POWERS_OF_10.get(rest)?;
            Some(i256::from(I128_POWERS_OF_10[max]) * i256::from(rest))
        }
    }
}

impl Display for Number {
    /// Formats the number as a string.
    ///
    /// This method returns a string representation of the number in its internal format.
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Number::Int64(v) => f.write_str(itoa::Buffer::new().format(*v)),
            Number::UInt64(v) => f.write_str(itoa::Buffer::new().format(*v)),
            Number::Float64(v) => f.write_str(zmij::Buffer::new().format(*v)),
            Number::Decimal64(_) | Number::Decimal128(_) | Number::Decimal256(_) => {
                self.write_decimal(f)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cmp::Ordering;

    #[test]
    fn pow10_i256_covers_every_power_that_fits() {
        for exponent in 0..=76u8 {
            let expected = i256::from(10).pow(u32::from(exponent));
            assert_eq!(pow10_i256(exponent), Some(expected), "10^{exponent}");
        }
        assert_eq!(pow10_i256(77), None);
        assert_eq!(pow10_i256(u8::MAX), None);
    }

    #[test]
    fn decimal256_bounds_have_76_digits() {
        assert_eq!(DECIMAL256_MAX, i256::from(10).pow(76) - 1);
        assert_eq!(DECIMAL256_MIN, -DECIMAL256_MAX);
    }

    #[test]
    fn test_number_comparison() {
        use Ordering::*;
        let int = Number::Int64;
        let uint = Number::UInt64;
        let float = Number::Float64;
        let d64 = |value: i64, scale: u8| Number::Decimal64(Decimal64 { scale, value });
        let d128 = |value: i128, scale: u8| Number::Decimal128(Decimal128 { scale, value });
        let d256 = |value: i128, scale: u8| {
            Number::Decimal256(Decimal256 {
                scale,
                value: i256::from(value),
            })
        };
        // Each case is checked in both directions.
        let cases = [
            // Same types.
            (int(10), int(5), Greater),
            (int(5), int(5), Equal),
            (uint(10), uint(5), Greater),
            (uint(5), uint(5), Equal),
            (float(10.0), float(5.0), Greater),
            (float(5.0), float(5.0), Equal),
            (d64(1234, 2), d64(5678, 2), Less),
            (d64(1234, 2), d64(1234, 2), Equal),
            (d128(1234, 2), d128(5678, 2), Less),
            (d256(1234, 2), d256(5678, 2), Less),
            // Same type, different scales: 12.34 vs 12.340 and 12.3.
            (d64(1234, 2), d64(12340, 3), Equal),
            (d64(1234, 2), d64(123, 1), Greater),
            // Signed and unsigned integers.
            (int(10), uint(5), Greater),
            (int(5), uint(10), Less),
            (int(5), uint(5), Equal),
            (int(-5), uint(5), Less),
            (int(0), uint(0), Equal),
            // Integers and decimals.
            (int(12), d64(12, 0), Equal),
            (int(12), d64(120, 1), Equal),
            (int(12), d64(121, 1), Less),
            (int(12), d64(119, 1), Greater),
            (uint(12), d64(12, 0), Equal),
            (uint(12), d64(120, 1), Equal),
            (int(-100), d64(-100, 0), Equal),
            (d64(-100, 0), uint(100), Less),
            (int(0), d64(0, 0), Equal),
            (int(0), d64(0, 5), Equal),
            (int(i64::MAX), d128(i64::MAX.into(), 0), Equal),
            (uint(u64::MAX), d128(i64::MAX.into(), 0), Greater),
            // Floats and decimals.
            (float(12.34), d64(1234, 2), Equal),
            (float(12.34), d64(1235, 2), Less),
            // Decimals of different widths.
            (d64(1234, 2), d128(1234, 2), Equal),
            (d64(1234, 2), d128(5678, 2), Less),
            (d64(1234, 2), d128(12340, 3), Equal),
            (d64(1234, 2), d256(1234, 2), Equal),
            (d128(1234, 2), d256(1234, 2), Equal),
        ];
        for (l, r, order) in &cases {
            assert_eq!(l.cmp(r), *order, "{l:?} vs {r:?}");
            assert_eq!(r.cmp(l), order.reverse(), "{r:?} vs {l:?}");
        }
    }

    #[test]
    fn test_exact_integer_casts() {
        let decimal64 = Number::Decimal64(Decimal64 {
            scale: 1,
            value: 1230,
        });
        assert_eq!(decimal64.as_i128(), Some(123));
        assert_eq!(decimal64.as_i64(), Some(123));
        assert_eq!(decimal64.as_u64(), Some(123));

        let decimal128 = Number::Decimal128(Decimal128 {
            scale: 1,
            value: 1230,
        });
        assert_eq!(decimal128.as_i128(), Some(123));
        assert_eq!(decimal128.as_i64(), Some(123));
        assert_eq!(decimal128.as_u64(), Some(123));

        let negative_decimal128 = Number::Decimal128(Decimal128 {
            scale: 1,
            value: -1230,
        });
        assert_eq!(negative_decimal128.as_i128(), Some(-123));
        assert_eq!(negative_decimal128.as_i64(), Some(-123));
        assert_eq!(negative_decimal128.as_u64(), None);

        let non_integer_decimal64 = Number::Decimal64(Decimal64 {
            scale: 1,
            value: 1234,
        });
        assert_eq!(non_integer_decimal64.as_i128(), None);
        assert_eq!(non_integer_decimal64.as_i64(), None);
        assert_eq!(non_integer_decimal64.as_u64(), None);

        let decimal256 = Number::Decimal256(Decimal256 {
            scale: 1,
            value: i256::from(1230),
        });
        assert_eq!(decimal256.as_i128(), Some(123));
        assert_eq!(decimal256.as_i64(), Some(123));
        assert_eq!(decimal256.as_u64(), Some(123));

        let float = Number::Float64(123.0);
        assert_eq!(float.as_i128(), Some(123));
        assert_eq!(float.as_i64(), Some(123));
        assert_eq!(float.as_u64(), Some(123));

        let non_integer_float = Number::Float64(123.1);
        assert_eq!(non_integer_float.as_i128(), None);
        assert_eq!(non_integer_float.as_i64(), None);
        assert_eq!(non_integer_float.as_u64(), None);

        let u64_upper_bound = Number::Float64((u64::MAX as f64) + 1.0);
        assert_eq!(u64_upper_bound.as_u64(), None);

        // Range bounds of each target type; `2^63`, `2^64` and `2^127` are
        // exact floats one past the maximum.
        let float = Number::Float64;
        assert_eq!(float(-(2f64.powi(63))).as_i64(), Some(i64::MIN));
        assert_eq!(float(2f64.powi(63)).as_i64(), None);
        assert_eq!(
            float(2f64.powi(64) - 2048.0).as_u64(),
            Some(u64::MAX - 2047)
        );
        assert_eq!(float(-0.0).as_u64(), Some(0));
        assert_eq!(float(-1.0).as_u64(), None);
        assert_eq!(float(-(2f64.powi(127))).as_i128(), Some(i128::MIN));
        assert_eq!(float(2f64.powi(127)).as_i128(), None);
        assert_eq!(float(f64::NAN).as_i64(), None);
        assert_eq!(float(f64::INFINITY).as_u64(), None);
        // The largest float below `2^127`.
        let below = 2f64.powi(127) - 2f64.powi(74);
        assert_eq!(float(below).to_i128(), Some(i128::MAX - (1 << 74) + 1));
    }

    #[test]
    fn test_rounded_integer_casts() {
        let decimal128 = Number::Decimal128(Decimal128 {
            scale: 1,
            value: 1235,
        });
        assert_eq!(decimal128.to_i128(), Some(124));
        assert_eq!(decimal128.to_i64(), Some(124));
        assert_eq!(decimal128.to_u64(), Some(124));

        let negative_decimal128 = Number::Decimal128(Decimal128 {
            scale: 1,
            value: -1235,
        });
        assert_eq!(negative_decimal128.to_i128(), Some(-124));
        assert_eq!(negative_decimal128.to_i64(), Some(-124));
        assert_eq!(negative_decimal128.to_u64(), None);

        let small_negative_decimal64 = Number::Decimal64(Decimal64 {
            scale: 1,
            value: -4,
        });
        assert_eq!(small_negative_decimal64.to_i64(), Some(0));
        assert_eq!(small_negative_decimal64.to_u64(), Some(0));

        let decimal256 = Number::Decimal256(Decimal256 {
            scale: 1,
            value: i256::from(1234),
        });
        assert_eq!(decimal256.to_i128(), Some(123));
        assert_eq!(decimal256.to_i64(), Some(123));
        assert_eq!(decimal256.to_u64(), Some(123));

        let float = Number::Float64(123.4);
        assert_eq!(float.to_i128(), Some(123));
        assert_eq!(float.to_i64(), Some(123));
        assert_eq!(float.to_u64(), Some(123));

        let half_up = Number::Float64(123.5);
        assert_eq!(half_up.to_i128(), Some(124));
        assert_eq!(half_up.to_i64(), Some(124));
        assert_eq!(half_up.to_u64(), Some(124));

        let negative_half_up = Number::Float64(-123.5);
        assert_eq!(negative_half_up.to_i128(), Some(-124));
        assert_eq!(negative_half_up.to_i64(), Some(-124));
        assert_eq!(negative_half_up.to_u64(), None);

        let small_negative = Number::Float64(-0.4);
        assert_eq!(small_negative.to_i64(), Some(0));
        assert_eq!(small_negative.to_u64(), Some(0));

        let nan = Number::Float64(f64::NAN);
        assert_eq!(nan.to_i128(), None);
        assert_eq!(nan.to_i64(), None);
        assert_eq!(nan.to_u64(), None);

        let inf = Number::Float64(f64::INFINITY);
        assert_eq!(inf.to_i128(), None);
        assert_eq!(inf.to_i64(), None);
        assert_eq!(inf.to_u64(), None);

        let large = Number::Float64(1e100);
        assert_eq!(large.to_i128(), None);
        assert_eq!(large.to_i64(), None);
        assert_eq!(large.to_u64(), None);

        let i64_upper_bound = Number::Float64(-(i64::MIN as f64));
        assert_eq!(i64_upper_bound.to_i64(), None);
        let u64_upper_bound = Number::Float64((u64::MAX as f64) + 1.0);
        assert_eq!(u64_upper_bound.to_u64(), None);

        let overflowing_decimal128 = Number::Decimal128(Decimal128 {
            scale: 1,
            value: i128::from(i64::MAX) * 10 + 5,
        });
        assert_eq!(overflowing_decimal128.to_i64(), None);
    }
}
