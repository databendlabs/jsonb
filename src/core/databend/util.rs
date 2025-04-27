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
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::error::*;
use crate::extension::Date;
use crate::extension::ExtensionValue;
use crate::extension::Interval;
use crate::extension::Timestamp;
use crate::extension::TimestampTz;
use crate::number::Decimal128;
use crate::number::Decimal256;
use crate::Number;
use crate::OwnedJsonb;
use crate::RawJsonb;

impl<'a> JsonbItem<'a> {
    pub(crate) fn from_raw_jsonb(raw_jsonb: RawJsonb<'a>) -> Result<JsonbItem<'a>> {
        let (header_type, _) = raw_jsonb.read_header(0)?;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = raw_jsonb.read_jentry(4)?;
                let range = Range {
                    start: 8,
                    end: raw_jsonb.len(),
                };
                let data = raw_jsonb.slice(range)?;
                let item = match jentry.type_code {
                    NULL_TAG => JsonbItem::Null,
                    TRUE_TAG => JsonbItem::Boolean(true),
                    FALSE_TAG => JsonbItem::Boolean(false),
                    NUMBER_TAG => JsonbItem::Number(data),
                    STRING_TAG => JsonbItem::String(data),
                    EXTENSION_TAG => JsonbItem::Extension(data),
                    _ => {
                        return Err(Error::InvalidJsonb);
                    }
                };
                Ok(item)
            }
            OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => Ok(JsonbItem::Raw(raw_jsonb)),
            _ => Err(Error::InvalidJsonb),
        }
    }
}

impl<'a> RawJsonb<'a> {
    pub(crate) fn jsonb_item_type(&self) -> Result<JsonbItemType> {
        let mut index = 0;
        let (header_type, header_len) = self.read_header(index)?;
        index += 4;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = self.read_jentry(index)?;

                match jentry.type_code {
                    NULL_TAG => Ok(JsonbItemType::Null),
                    TRUE_TAG => Ok(JsonbItemType::Boolean),
                    FALSE_TAG => Ok(JsonbItemType::Boolean),
                    NUMBER_TAG => Ok(JsonbItemType::Number),
                    STRING_TAG => Ok(JsonbItemType::String),
                    EXTENSION_TAG => Ok(JsonbItemType::Extension),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            ARRAY_CONTAINER_TAG => Ok(JsonbItemType::Array(header_len as usize)),
            OBJECT_CONTAINER_TAG => Ok(JsonbItemType::Object(header_len as usize)),
            _ => Err(Error::InvalidJsonb),
        }
    }

    pub(crate) fn get_object_value_by_key_name(
        &self,
        key_name: &Cow<'a, str>,
        eq_func: impl Fn(&[u8], &[u8]) -> bool,
    ) -> Result<Option<JsonbItem<'a>>> {
        let (header_type, header_len) = self.read_header(0)?;
        if header_type != OBJECT_CONTAINER_TAG || header_len == 0 {
            return Ok(None);
        }
        let length = header_len as usize;
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
        let value_item = jentry_to_jsonb_item(value_jentry, value_data);
        Ok(Some(value_item))
    }

    pub(super) fn read_header(&self, index: usize) -> Result<(u32, u32)> {
        let header = self.read_u32(index)?;
        let header_type = header & CONTAINER_HEADER_TYPE_MASK;
        match header_type {
            SCALAR_CONTAINER_TAG | OBJECT_CONTAINER_TAG | ARRAY_CONTAINER_TAG => {}
            _ => {
                return Err(Error::InvalidJsonb);
            }
        }
        let header_len = header & CONTAINER_HEADER_LEN_MASK;
        Ok((header_type, header_len))
    }

    pub(super) fn read_jentry(&self, index: usize) -> Result<JEntry> {
        let jentry_encoded = self.read_u32(index)?;
        let jentry = JEntry::decode_jentry(jentry_encoded);
        Ok(jentry)
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
        // Check for potential out-of-bounds access before creating item
        if range.end > self.len() {
            return Err(Error::InvalidJsonb);
        }
        Ok(&self.data[range])
    }
}

impl OwnedJsonb {
    pub(crate) fn from_item(item: JsonbItem<'_>) -> Result<OwnedJsonb> {
        let (jentry, data) = match item {
            JsonbItem::Null => {
                let jentry = JEntry::make_null_jentry();
                (jentry, None)
            }
            JsonbItem::Boolean(v) => {
                let jentry = if v {
                    JEntry::make_true_jentry()
                } else {
                    JEntry::make_false_jentry()
                };
                (jentry, None)
            }
            JsonbItem::Number(data) => {
                let jentry = JEntry::make_number_jentry(data.len());
                (jentry, Some(data))
            }
            JsonbItem::String(data) => {
                let jentry = JEntry::make_string_jentry(data.len());
                (jentry, Some(data))
            }
            JsonbItem::Extension(data) => {
                let jentry = JEntry::make_extension_jentry(data.len());
                (jentry, Some(data))
            }
            JsonbItem::Raw(raw_jsonb) => {
                return Ok(raw_jsonb.to_owned());
            }
            JsonbItem::Owned(owned_jsonb) => {
                return Ok(owned_jsonb.clone());
            }
        };

        let len = if let Some(data) = data {
            data.len() + 8
        } else {
            8
        };
        let mut buf = Vec::with_capacity(len);
        let header = SCALAR_CONTAINER_TAG;
        buf.write_u32::<BigEndian>(header)?;
        buf.write_u32::<BigEndian>(jentry.encoded())?;
        if let Some(data) = data {
            buf.extend_from_slice(data);
        }
        Ok(OwnedJsonb::new(buf))
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
            Self::Decimal128(v) => {
                writer.write_all(&[NUMBER_DECIMAL])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.precision.to_be_bytes())?;
                writer.write_all(&v.scale.to_be_bytes())?;
                Ok(19)
            }
            Self::Decimal256(v) => {
                writer.write_all(&[NUMBER_DECIMAL])?;
                writer.write_all(&v.value.to_be_bytes())?;
                writer.write_all(&v.precision.to_be_bytes())?;
                writer.write_all(&v.scale.to_be_bytes())?;
                Ok(35)
            }
        }
    }

    #[inline]
    pub(crate) fn decode(bytes: &[u8]) -> Result<Number> {
        let mut len = bytes.len();
        assert!(len > 0);
        len -= 1;

        let ty = bytes[0];
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
            NUMBER_FLOAT => Number::Float64(f64::from_be_bytes(bytes[1..].try_into().unwrap())),
            NUMBER_DECIMAL => match len {
                18 => {
                    let value = i128::from_be_bytes(bytes[1..17].try_into().unwrap());
                    let precision = u8::from_be_bytes(bytes[17..18].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[18..19].try_into().unwrap());
                    let dec = Decimal128 {
                        precision,
                        scale,
                        value,
                    };
                    Number::Decimal128(dec)
                }
                34 => {
                    let value = i256::from_be_bytes(bytes[1..33].try_into().unwrap());
                    let precision = u8::from_be_bytes(bytes[33..34].try_into().unwrap());
                    let scale = u8::from_be_bytes(bytes[34..35].try_into().unwrap());
                    let dec = Decimal256 {
                        precision,
                        scale,
                        value,
                    };
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
                Ok(10)
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
    pub(crate) fn decode(bytes: &[u8]) -> Result<ExtensionValue> {
        let mut len = bytes.len();
        assert!(len > 0);
        len -= 1;

        let ty = bytes[0];
        let val = match ty {
            EXTENSION_BINARY => {
                let v = &bytes[1..len + 1];
                ExtensionValue::Binary(v)
            }
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
                if len != 9 {
                    return Err(Error::InvalidJsonbNumber);
                }
                let value = i64::from_be_bytes(bytes[1..9].try_into().unwrap());
                let offset = i8::from_be_bytes(bytes[9..10].try_into().unwrap());

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

pub(super) fn jentry_to_jsonb_item(jentry: JEntry, data: &[u8]) -> JsonbItem<'_> {
    match jentry.type_code {
        NULL_TAG => JsonbItem::Null,
        TRUE_TAG => JsonbItem::Boolean(true),
        FALSE_TAG => JsonbItem::Boolean(false),
        NUMBER_TAG => JsonbItem::Number(data),
        STRING_TAG => JsonbItem::String(data),
        EXTENSION_TAG => JsonbItem::Extension(data),
        CONTAINER_TAG => JsonbItem::Raw(RawJsonb::new(data)),
        _ => unreachable!(),
    }
}
