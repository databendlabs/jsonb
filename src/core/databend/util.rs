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

use core::ops::Range;
use std::borrow::Cow;
use std::io::Write;

use byteorder::BigEndian;
use byteorder::WriteBytesExt;
use ethnum::i256;

use super::constants::*;
use super::jentry::JEntry;
use crate::constants::enter_container;
use crate::core::Entries;
use crate::core::ExtensionItem;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::core::NumberItem;
use crate::core::RawEntry;
use crate::error::*;
use crate::extension::Date;
use crate::extension::ExtensionValue;
use crate::extension::Interval;
use crate::extension::Timestamp;
use crate::extension::TimestampTz;
use crate::number::Decimal128;
use crate::number::Decimal256;
use crate::number::Decimal64;
use crate::Number;
use crate::Object;
use crate::OwnedJsonb;
use crate::RawJsonb;
use crate::Value;

impl<'a> JsonbItem<'a> {
    pub(crate) fn from_raw_jsonb(raw_jsonb: RawJsonb<'a>) -> Result<JsonbItem<'a>> {
        // A container decodes to itself, as `JsonbItem::Raw`.
        RawEntry::from_jsonb(raw_jsonb)?.into_item()
    }
}

impl<'a> RawJsonb<'a> {
    /// Returns the type information of a JSONB data item
    ///
    /// # Returns
    ///
    /// Returns `Result<JsonbItemType>`, where `JsonbItemType` can be one of:
    /// - `JsonbItemType::Null` - represents a null value
    /// - `JsonbItemType::Boolean` - represents a boolean value (true or false)
    /// - `JsonbItemType::Number` - represents a numeric type
    /// - `JsonbItemType::String` - represents a string type
    /// - `JsonbItemType::Extension` - represents an extension type
    /// - `JsonbItemType::Array(n)` - represents an array type, where n is the number of array elements
    /// - `JsonbItemType::Object(n)` - represents an object type, where n is the number of key-value pairs
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonb` if the JSONB data format is invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, core::JsonbItemType};
    ///
    /// // Create a JSONB containing an array
    /// let jsonb = "[1, 2, 3]".parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb.as_raw();
    ///
    /// // Get type information
    /// let item_type = raw_jsonb.jsonb_item_type().unwrap();
    /// assert!(matches!(item_type, JsonbItemType::Array(3)));
    ///
    /// // Create a JSONB containing an object
    /// let jsonb = r#"{"name": "Alice", "age": 30}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb.as_raw();
    ///
    /// // Get type information
    /// let item_type = raw_jsonb.jsonb_item_type().unwrap();
    /// assert!(matches!(item_type, JsonbItemType::Object(2)));
    /// ```
    pub fn jsonb_item_type(&self) -> Result<JsonbItemType> {
        let (header_type, header_len) = self.read_header(0)?;
        match header_type {
            SCALAR_CONTAINER_TAG => match self.read_jentry(4)?.type_code {
                NULL_TAG => Ok(JsonbItemType::Null),
                TRUE_TAG | FALSE_TAG => Ok(JsonbItemType::Boolean),
                NUMBER_TAG => Ok(JsonbItemType::Number),
                STRING_TAG => Ok(JsonbItemType::String),
                EXTENSION_TAG => Ok(JsonbItemType::Extension),
                // Including a container entry, which no encoder writes here.
                _ => Err(Error::InvalidJsonb),
            },
            ARRAY_CONTAINER_TAG => Ok(JsonbItemType::Array(header_len)),
            OBJECT_CONTAINER_TAG => Ok(JsonbItemType::Object(header_len)),
            _ => Err(Error::InvalidJsonb),
        }
    }

    /// Converts JSONB binary data to a `Value` type
    ///
    /// This function recursively parses JSONB binary data and converts it into
    /// an in-memory `Value` structure, making it convenient to access and
    /// manipulate JSON data.
    ///
    /// # Returns
    ///
    /// Returns `Result<Value<'a>>`, where `Value` can be one of:
    /// - `Value::Null` - represents a null value
    /// - `Value::Bool(bool)` - represents a boolean value
    /// - `Value::Number(Number)` - represents a numeric value
    /// - `Value::String(Cow<'a, str>)` - represents a string
    /// - `Value::Binary(&'a [u8])` - represents binary data
    /// - `Value::Date(Date)` - represents a date
    /// - `Value::Timestamp(Timestamp)` - represents a timestamp
    /// - `Value::TimestampTz(TimestampTz)` - represents a timestamp with timezone
    /// - `Value::Interval(Interval)` - represents a time interval
    /// - `Value::Array(Vec<Value<'a>>)` - represents an array
    /// - `Value::Object(Object)` - represents an object
    ///
    /// # Errors
    ///
    /// Returns `Error::InvalidJsonb` if the JSONB data format is invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use jsonb::{OwnedJsonb, Value};
    ///
    /// // Parse a simple JSON object
    /// let jsonb = r#"{"name": "Alice", "age": 30, "is_student": false}"#.parse::<OwnedJsonb>().unwrap();
    /// let raw_jsonb = jsonb.as_raw();
    ///
    /// // Convert to Value type
    /// let value = raw_jsonb.to_value().unwrap();
    /// assert!(matches!(value, Value::Object(_)));
    ///
    /// // Access object properties
    /// if let Value::Object(obj) = value {
    ///     assert_eq!(obj.get("name").unwrap().as_str().unwrap(), "Alice");
    ///     assert_eq!(obj.get("age").unwrap().as_i64().unwrap(), 30);
    ///     assert_eq!(obj.get("is_student").unwrap().as_bool().unwrap(), false);
    /// }
    /// ```
    pub fn to_value(&self) -> Result<Value<'a>> {
        self.value_with_depth(0)
    }

    /// Converts to a `Value`, where `depth` is the number of enclosing containers.
    fn value_with_depth(&self, depth: usize) -> Result<Value<'a>> {
        let (header_type, header_len) = self.read_header(0)?;
        match header_type {
            // `RawEntry::from_jsonb` rejects a container under a scalar header.
            // Encoders never write one, and unwrapping it would recurse without
            // counting depth, so nested wrappers could overflow the stack.
            SCALAR_CONTAINER_TAG => RawEntry::from_jsonb(*self)?.into_value(depth),
            ARRAY_CONTAINER_TAG => {
                let depth = enter_container(depth)?;
                let mut values = Vec::with_capacity(header_len);
                for item in Entries::new(*self, header_len) {
                    values.push(item?.into_value(depth)?);
                }
                Ok(Value::Array(values))
            }
            OBJECT_CONTAINER_TAG => {
                let depth = enter_container(depth)?;
                let (keys, values) = Entries::object(*self, header_len)?;
                // Decode every key before any value, as the keys come first.
                let mut key_strings = Vec::with_capacity(header_len);
                for key in keys {
                    let key = key?;
                    if key.type_code != STRING_TAG {
                        return Err(Error::InvalidJsonb);
                    }
                    key_strings.push(decode_str(key.payload)?.to_owned());
                }
                let mut obj = Object::new();
                for (key, value) in key_strings.into_iter().zip(values) {
                    obj.insert(key, value?.into_value(depth)?);
                }
                Ok(Value::Object(obj))
            }
            _ => Err(Error::InvalidJsonb),
        }
    }

    pub(crate) fn get_object_value_by_key_name(
        &self,
        key_name: &Cow<'a, str>,
        eq_func: impl Fn(&[u8], &[u8]) -> bool,
    ) -> Result<Option<JsonbItem<'a>>> {
        let (header_type, length) = self.read_header(0)?;
        if header_type != OBJECT_CONTAINER_TAG || length == 0 {
            return Ok(None);
        }
        let mut index = 0;
        let mut jentry_offset = 4;
        let mut item_offset = 4 + 8 * length;

        let mut key_matched = false;
        let name_len = key_name.len();
        let name_bytes = key_name.as_bytes();
        while index < length {
            let key_jentry = self.read_jentry(jentry_offset)?;
            let key_len = key_jentry.length as usize;

            index += 1;
            jentry_offset += 4;
            item_offset += key_len;

            // check if key match the name.
            if name_len == key_len {
                let key_range = Range {
                    start: item_offset - key_len,
                    end: item_offset,
                };
                let key_data = self.slice(key_range)?;
                if eq_func(name_bytes, key_data) {
                    key_matched = true;
                    break;
                }
            }
        }

        if !key_matched {
            return Ok(None);
        }
        let val_index = index - 1;
        // skip unmatched keys and values.
        while index < length + val_index {
            let jentry = self.read_jentry(jentry_offset)?;
            index += 1;
            jentry_offset += 4;
            item_offset += jentry.length as usize;
        }

        // read value item data
        let value_jentry = self.read_jentry(jentry_offset)?;
        let value_len = value_jentry.length as usize;

        let value_range = Range {
            start: item_offset,
            end: item_offset + value_len,
        };
        let value_data = self.slice(value_range)?;
        let value_item = RawEntry {
            type_code: value_jentry.type_code,
            payload: value_data,
        }
        .into_item()?;
        Ok(Some(value_item))
    }

    pub(super) fn read_header(&self, index: usize) -> Result<(u32, usize)> {
        let header = self.read_u32(index)?;
        let header_type = header & CONTAINER_HEADER_TYPE_MASK;
        let header_len = (header & CONTAINER_HEADER_LEN_MASK) as usize;
        // The JEntries follow the header directly. Rejecting a length that cannot
        // fit keeps every allocation sized from `header_len` bounded by the input.
        let jentries_per_item = match header_type {
            // A scalar header is always exactly `SCALAR_CONTAINER_TAG`. JSON text
            // whose first byte maps to the scalar type never has zero length bits,
            // so this rejects it before a JEntry read from text bytes can pass the
            // payload bounds check.
            SCALAR_CONTAINER_TAG if header_len != 0 => return Err(Error::InvalidJsonb),
            SCALAR_CONTAINER_TAG => return Ok((header_type, header_len)),
            ARRAY_CONTAINER_TAG => 1,
            OBJECT_CONTAINER_TAG => 2,
            _ => return Err(Error::InvalidJsonb),
        };
        let available = self.len().saturating_sub(index + 4) / 4;
        if header_len > available / jentries_per_item {
            return Err(Error::InvalidEOF);
        }
        Ok((header_type, header_len))
    }

    pub(super) fn read_jentry(&self, index: usize) -> Result<JEntry> {
        let jentry_encoded = self.read_u32(index)?;
        JEntry::decode_jentry(jentry_encoded)
    }

    pub(super) fn read_u32(&self, idx: usize) -> Result<u32> {
        let bytes: [u8; 4] = self
            .data
            .get(idx..idx + 4)
            .ok_or(Error::InvalidEOF)?
            .try_into()
            .unwrap();
        Ok(u32::from_be_bytes(bytes))
    }

    pub(super) fn slice(&self, range: Range<usize>) -> Result<&'a [u8]> {
        self.data.get(range).ok_or(Error::InvalidJsonb)
    }
}

impl OwnedJsonb {
    pub(crate) fn from_item(item: JsonbItem<'_>) -> Result<OwnedJsonb> {
        match item {
            JsonbItem::Raw(raw_jsonb) => Ok(raw_jsonb.to_owned()),
            JsonbItem::Owned(owned_jsonb) => Ok(owned_jsonb),
            _ => {
                let mut len = match item {
                    JsonbItem::Null => 0,
                    JsonbItem::Boolean(_) => 0,
                    JsonbItem::Number(NumberItem::Raw(data)) => data.len(),
                    JsonbItem::String(ref s) => s.len(),
                    JsonbItem::Extension(ExtensionItem::Raw(data)) => data.len(),
                    // The estimated lengths for number and extension.
                    _ => 10,
                };

                // add the length of header and jentry.
                len += 8;
                let mut buf = Vec::with_capacity(len);
                let header = SCALAR_CONTAINER_TAG;
                buf.write_u32::<BigEndian>(header)?;

                match item {
                    JsonbItem::Null => {
                        let jentry = JEntry::make_null_jentry();
                        buf.write_u32::<BigEndian>(jentry.encoded())?;
                    }
                    JsonbItem::Boolean(v) => {
                        let jentry = if v {
                            JEntry::make_true_jentry()
                        } else {
                            JEntry::make_false_jentry()
                        };
                        buf.write_u32::<BigEndian>(jentry.encoded())?;
                    }
                    JsonbItem::Number(num) => match num {
                        NumberItem::Raw(data) => {
                            let jentry = JEntry::make_number_jentry(data.len())?;
                            buf.write_u32::<BigEndian>(jentry.encoded())?;
                            buf.extend_from_slice(data);
                        }
                        NumberItem::Number(num) => {
                            let mut data = vec![];
                            let len = num.compact_encode(&mut data)?;
                            let jentry = JEntry::make_number_jentry(len)?;
                            buf.write_u32::<BigEndian>(jentry.encoded())?;
                            buf.extend_from_slice(&data);
                        }
                    },
                    JsonbItem::String(s) => {
                        let jentry = JEntry::make_string_jentry(s.len())?;
                        buf.write_u32::<BigEndian>(jentry.encoded())?;
                        buf.extend_from_slice(s.as_bytes());
                    }
                    JsonbItem::Extension(ext) => match ext {
                        ExtensionItem::Raw(data) => {
                            let jentry = JEntry::make_extension_jentry(data.len())?;
                            buf.write_u32::<BigEndian>(jentry.encoded())?;
                            buf.extend_from_slice(data);
                        }
                        ExtensionItem::Extension(ext) => {
                            let mut data = vec![];
                            let len = ext.compact_encode(&mut data)?;
                            let jentry = JEntry::make_extension_jentry(len)?;
                            buf.write_u32::<BigEndian>(jentry.encoded())?;
                            buf.extend_from_slice(&data);
                        }
                    },
                    _ => unreachable!(),
                }
                Ok(OwnedJsonb::new(buf))
            }
        }
    }
}

impl Number {
    #[inline]
    pub(crate) fn compact_encode<W: Write>(&self, mut writer: W) -> Result<usize> {
        match self {
            Self::Int64(v) => {
                if *v == 0 {
                    writer.write_all(&[NUMBER_ZERO])?;
                    return Ok(1);
                }
                writer.write_all(&[NUMBER_INT])?;
                if *v >= i8::MIN.into() && *v <= i8::MAX.into() {
                    writer.write_all(&(*v as i8).to_be_bytes())?;
                    Ok(2)
                } else if *v >= i16::MIN.into() && *v <= i16::MAX.into() {
                    writer.write_all(&(*v as i16).to_be_bytes())?;
                    Ok(3)
                } else if *v >= i32::MIN.into() && *v <= i32::MAX.into() {
                    writer.write_all(&(*v as i32).to_be_bytes())?;
                    Ok(5)
                } else {
                    writer.write_all(&v.to_be_bytes())?;
                    Ok(9)
                }
            }
            Self::UInt64(v) => {
                if *v == 0 {
                    writer.write_all(&[NUMBER_ZERO])?;
                    return Ok(1);
                }
                writer.write_all(&[NUMBER_UINT])?;
                if *v <= u8::MAX.into() {
                    writer.write_all(&(*v as u8).to_be_bytes())?;
                    Ok(2)
                } else if *v <= u16::MAX.into() {
                    writer.write_all(&(*v as u16).to_be_bytes())?;
                    Ok(3)
                } else if *v <= u32::MAX.into() {
                    writer.write_all(&(*v as u32).to_be_bytes())?;
                    Ok(5)
                } else {
                    writer.write_all(&v.to_be_bytes())?;
                    Ok(9)
                }
            }
            Self::Float64(v) => {
                if v.is_nan() {
                    writer.write_all(&[NUMBER_NAN])?;
                    return Ok(1);
                } else if v.is_infinite() {
                    if v.is_sign_negative() {
                        writer.write_all(&[NUMBER_NEG_INF])?;
                    } else {
                        writer.write_all(&[NUMBER_INF])?;
                    }
                    return Ok(1);
                }
                writer.write_all(&[NUMBER_FLOAT])?;
                writer.write_all(&v.to_be_bytes())?;
                Ok(9)
            }
            Self::Decimal64(v) => {
                writer.write_all(&[NUMBER_DECIMAL])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.scale.to_be_bytes())?;
                Ok(10)
            }
            Self::Decimal128(v) => {
                writer.write_all(&[NUMBER_DECIMAL])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.scale.to_be_bytes())?;
                Ok(18)
            }
            Self::Decimal256(v) => {
                writer.write_all(&[NUMBER_DECIMAL])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.scale.to_be_bytes())?;
                Ok(34)
            }
        }
    }

    #[inline]
    pub(crate) fn decode(bytes: &[u8]) -> Result<Number> {
        let Some((&ty, payload)) = bytes.split_first() else {
            return Err(Error::InvalidJsonbNumber);
        };
        let len = payload.len();
        let num = match ty {
            NUMBER_ZERO => Number::UInt64(0),
            NUMBER_NAN => Number::Float64(f64::NAN),
            NUMBER_INF => Number::Float64(f64::INFINITY),
            NUMBER_NEG_INF => Number::Float64(f64::NEG_INFINITY),
            NUMBER_INT => match len {
                1 => Number::Int64(i8::from_be_bytes(bytes[1..].try_into().unwrap()) as i64),
                2 => Number::Int64(i16::from_be_bytes(bytes[1..].try_into().unwrap()) as i64),
                4 => Number::Int64(i32::from_be_bytes(bytes[1..].try_into().unwrap()) as i64),
                8 => Number::Int64(i64::from_be_bytes(bytes[1..].try_into().unwrap())),
                _ => {
                    return Err(Error::InvalidJsonbNumber);
                }
            },
            NUMBER_UINT => match len {
                1 => Number::UInt64(u8::from_be_bytes(bytes[1..].try_into().unwrap()) as u64),
                2 => Number::UInt64(u16::from_be_bytes(bytes[1..].try_into().unwrap()) as u64),
                4 => Number::UInt64(u32::from_be_bytes(bytes[1..].try_into().unwrap()) as u64),
                8 => Number::UInt64(u64::from_be_bytes(bytes[1..].try_into().unwrap())),
                _ => {
                    return Err(Error::InvalidJsonbNumber);
                }
            },
            NUMBER_FLOAT => match payload.try_into() {
                Ok(bytes) => Number::Float64(f64::from_be_bytes(bytes)),
                Err(_) => return Err(Error::InvalidJsonbNumber),
            },
            NUMBER_DECIMAL => match len {
                9 => {
                    let value = i64::from_be_bytes(bytes[1..9].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[9..10].try_into().unwrap());
                    let dec = Decimal64 { scale, value };
                    Number::Decimal64(dec)
                }
                17 => {
                    let value = i128::from_be_bytes(bytes[1..17].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[17..18].try_into().unwrap());
                    let dec = Decimal128 { scale, value };
                    Number::Decimal128(dec)
                }
                18 => {
                    // Compatible with deprecated Decimal128 formats, including precision
                    let value = i128::from_be_bytes(bytes[1..17].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[18..19].try_into().unwrap());
                    let dec = Decimal128 { scale, value };
                    Number::Decimal128(dec)
                }
                33 => {
                    let value = i256::from_be_bytes(bytes[1..33].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[33..34].try_into().unwrap());
                    let dec = Decimal256 { scale, value };
                    Number::Decimal256(dec)
                }
                34 => {
                    // Compatible with deprecated Decimal256 formats, including precision
                    let value = i256::from_be_bytes(bytes[1..33].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[34..35].try_into().unwrap());
                    let dec = Decimal256 { scale, value };
                    Number::Decimal256(dec)
                }
                _ => {
                    return Err(Error::InvalidJsonbNumber);
                }
            },
            _ => {
                return Err(Error::InvalidJsonbNumber);
            }
        };
        Ok(num)
    }
}

impl ExtensionValue<'_> {
    #[inline]
    pub(crate) fn compact_encode<W: Write>(&self, mut writer: W) -> Result<usize> {
        match self {
            ExtensionValue::Binary(v) => {
                writer.write_all(&[EXTENSION_BINARY])?;
                let len = v.len() + 1;
                writer.write_all(v)?;
                Ok(len)
            }
            ExtensionValue::Date(v) => {
                writer.write_all(&[EXTENSION_DATE])?;
                writer.write_all(&v.value.to_be_bytes())?;
                Ok(5)
            }
            ExtensionValue::Timestamp(v) => {
                writer.write_all(&[EXTENSION_TIMESTAMP])?;
                writer.write_all(&v.value.to_be_bytes())?;
                Ok(9)
            }
            ExtensionValue::TimestampTz(v) => {
                writer.write_all(&[EXTENSION_TIMESTAMP_TZ])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.offset.to_be_bytes())?;
                Ok(13)
            }
            ExtensionValue::Interval(v) => {
                writer.write_all(&[EXTENSION_INTERVAL])?;
                writer.write_all(&v.months.to_be_bytes())?;
                writer.write_all(&v.days.to_be_bytes())?;
                writer.write_all(&v.micros.to_be_bytes())?;
                Ok(17)
            }
        }
    }

    #[inline]
    pub(crate) fn decode(bytes: &[u8]) -> Result<ExtensionValue<'_>> {
        let Some((&ty, payload)) = bytes.split_first() else {
            return Err(Error::InvalidJsonbExtension);
        };
        let len = payload.len();
        let val = match ty {
            EXTENSION_BINARY => ExtensionValue::Binary(payload),
            EXTENSION_DATE => {
                if len != 4 {
                    return Err(Error::InvalidJsonbNumber);
                }
                let value = i32::from_be_bytes(bytes[1..5].try_into().unwrap());

                ExtensionValue::Date(Date { value })
            }
            EXTENSION_TIMESTAMP => {
                if len != 8 {
                    return Err(Error::InvalidJsonbNumber);
                }
                let value = i64::from_be_bytes(bytes[1..9].try_into().unwrap());

                ExtensionValue::Timestamp(Timestamp { value })
            }
            EXTENSION_TIMESTAMP_TZ => {
                if len != 9 && len != 12 {
                    return Err(Error::InvalidJsonbNumber);
                }
                let value = i64::from_be_bytes(bytes[1..9].try_into().unwrap());
                let offset = if len == 9 {
                    let hours = i8::from_be_bytes(bytes[9..10].try_into().unwrap());
                    (hours as i32) * 3_600
                } else {
                    i32::from_be_bytes(bytes[9..13].try_into().unwrap())
                };

                ExtensionValue::TimestampTz(TimestampTz { offset, value })
            }
            EXTENSION_INTERVAL => {
                if len != 16 {
                    return Err(Error::InvalidJsonbNumber);
                }
                let months = i32::from_be_bytes(bytes[1..5].try_into().unwrap());
                let days = i32::from_be_bytes(bytes[5..9].try_into().unwrap());
                let micros = i64::from_be_bytes(bytes[9..17].try_into().unwrap());
                ExtensionValue::Interval(Interval {
                    months,
                    days,
                    micros,
                })
            }
            _ => {
                return Err(Error::InvalidJsonbExtension);
            }
        };
        Ok(val)
    }
}

/// Decodes a JSONB string payload.
///
/// `RawJsonb` can wrap arbitrary bytes through safe constructors, so string
/// payloads are untrusted and must be validated before being exposed as `str`.
///
/// # Errors
///
/// Returns `Error::InvalidUtf8` if `data` is not valid UTF-8.
#[inline]
pub(super) fn decode_str(data: &[u8]) -> Result<&str> {
    // Most strings are short and ASCII. `is_ascii` is inlined and checks a
    // word at a time, which saves the call into `simdutf8` for each of them.
    if data.is_ascii() {
        // SAFETY: ASCII is valid UTF-8.
        return Ok(unsafe { std::str::from_utf8_unchecked(data) });
    }
    // `simdutf8` validates long strings several times faster than `std`, and
    // falls back to `std` below 64 bytes.
    simdutf8::basic::from_utf8(data).map_err(|_| Error::InvalidUtf8)
}

impl<'a> RawEntry<'a> {
    /// Converts this entry into a `Value`, decoding nested containers.
    ///
    /// `depth` is the number of containers enclosing this entry.
    fn into_value(self, depth: usize) -> Result<Value<'a>> {
        let data = self.payload;
        match self.type_code {
            NULL_TAG => Ok(Value::Null),
            TRUE_TAG => Ok(Value::Bool(true)),
            FALSE_TAG => Ok(Value::Bool(false)),
            NUMBER_TAG => Ok(Value::Number(Number::decode(data)?)),
            STRING_TAG => Ok(Value::String(Cow::Borrowed(decode_str(data)?))),
            EXTENSION_TAG => Ok(match ExtensionValue::decode(data)? {
                ExtensionValue::Binary(v) => Value::Binary(v),
                ExtensionValue::Date(v) => Value::Date(v),
                ExtensionValue::Timestamp(v) => Value::Timestamp(v),
                ExtensionValue::TimestampTz(v) => Value::TimestampTz(v),
                ExtensionValue::Interval(v) => Value::Interval(v),
            }),
            CONTAINER_TAG => self.container().value_with_depth(depth),
            _ => Err(Error::InvalidJsonb),
        }
    }
}
