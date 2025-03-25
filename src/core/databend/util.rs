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

use byteorder::BigEndian;
use byteorder::WriteBytesExt;
use core::ops::Range;
use std::borrow::Cow;
use std::io::Write;
use std::simd::cmp::SimdPartialEq;
use std::simd::u32x8;

use super::constants::*;
use super::jentry::JEntry;
use crate::core::JsonbItem;
use crate::core::JsonbItemType;
use crate::error::*;
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
                    _ => Err(Error::InvalidJsonb),
                }
            }
            ARRAY_CONTAINER_TAG => Ok(JsonbItemType::Array(header_len as usize)),
            OBJECT_CONTAINER_TAG => Ok(JsonbItemType::Object(header_len as usize)),
            _ => Err(Error::InvalidJsonb),
        }
    }

    #[inline]
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn get_object_value_by_key_name_simd(
        &self,
        length: usize,
        key_name: &Cow<'a, str>,
        ignore_ascii_case: bool,
    ) -> Result<Option<JsonbItem<'a>>> {
        let mut item_offset = 4 + 8 * length;

        let name_bytes = key_name.as_bytes();
        let mut index = None;

        for i in 0..length / 8 {
            if index.is_some() {
                break;
            }
            index =
                self.find_matched_pos_simd_x8(i, name_bytes, &mut item_offset, ignore_ascii_case)?;
        }
        for i in length - length % 8..length {
            if index.is_some() {
                break;
            }
            let jentry = self.read_jentry((i + 1) * 4)?;
            let key_len = jentry.length as usize;
            item_offset += key_len;

            if name_bytes.len() == key_len {
                let key_range = Range {
                    start: item_offset - key_len,
                    end: item_offset,
                };
                let data = self.slice(key_range)?;
                if Self::compare(data, name_bytes, ignore_ascii_case) {
                    index = Some(i);
                    break;
                }
            }
        }
        let Some(mut index) = index else {
            return Ok(None);
        };
        let val_index = index;
        index += 1;
        // skip rest keys and values.
        for i in index..(length + val_index) {
            let jentry = self.read_jentry((i + 1) * 4)?;
            item_offset += jentry.length as usize;
        }
        let jentry = self.read_jentry((length + val_index + 1) * 4)?;
        let value_len = jentry.length as usize;

        let value_range = Range {
            start: item_offset,
            end: item_offset + value_len,
        };
        let data = self.slice(value_range)?;
        let value_item = jentry_to_jsonb_item(jentry, data);
        Ok(Some(value_item))
    }

    #[cfg(target_arch = "x86_64")]
    fn find_matched_pos_simd_x8(
        &self,
        group_i: usize,
        target: &[u8],
        offset: &mut usize,
        ignore_ascii_case: bool,
    ) -> Result<Option<usize>> {
        let len_x8 = self.load_jentry_lens((group_i * 8 + 1) * 4)?;
        let target_len = u32x8::splat(target.len() as u32);
        let mask = len_x8.simd_eq(target_len);

        for i in 0..8 {
            let key_len = len_x8[i] as usize;
            *offset += key_len;

            if mask.test(i) {
                let key_range = Range {
                    start: *offset - key_len,
                    end: *offset,
                };
                let data = self.slice(key_range)?;
                if Self::compare(data, target, ignore_ascii_case) {
                    return Ok(Some(i + group_i * 8));
                }
            }
        }
        Ok(None)
    }

    #[cfg(target_arch = "x86_64")]
    #[inline]
    fn load_jentry_lens(&self, start: usize) -> Result<u32x8> {
        let mut array = [0u32; 8];
        for (i, len) in array.iter_mut().enumerate() {
            *len = self.read_u32(start + i * 4)? & JENTRY_OFF_LEN_MASK;
        }
        Ok(u32x8::from(array))
    }

    #[inline]
    fn compare(a: &[u8], b: &[u8], ignore_ascii_case: bool) -> bool {
        if ignore_ascii_case {
            a.eq_ignore_ascii_case(b)
        } else {
            a.eq(b)
        }
    }

    pub(crate) fn get_object_value_by_key_name(
        &self,
        key_name: &Cow<'a, str>,
        ignore_ascii_case: bool,
    ) -> Result<Option<JsonbItem<'a>>> {
        let (header_type, header_len) = self.read_header(0)?;
        if header_type != OBJECT_CONTAINER_TAG || header_len == 0 {
            return Ok(None);
        }
        let length = header_len as usize;

        #[cfg(target_arch = "x86_64")]
        return self.get_object_value_by_key_name_simd(length, key_name, ignore_ascii_case);
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
                if Self::compare(name_bytes, key_data, ignore_ascii_case) {
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
            _ => {
                return Err(Error::InvalidJsonbNumber);
            }
        };
        Ok(num)
    }
}

pub(super) fn jentry_to_jsonb_item(jentry: JEntry, data: &[u8]) -> JsonbItem<'_> {
    match jentry.type_code {
        NULL_TAG => JsonbItem::Null,
        TRUE_TAG => JsonbItem::Boolean(true),
        FALSE_TAG => JsonbItem::Boolean(false),
        NUMBER_TAG => JsonbItem::Number(data),
        STRING_TAG => JsonbItem::String(data),
        CONTAINER_TAG => JsonbItem::Raw(RawJsonb::new(data)),
        _ => unreachable!(),
    }
}
