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

mod builder;
mod de;
mod iterator;
mod ser;

pub(crate) use builder::*;
pub use de::*;
pub(crate) use iterator::*;
pub use ser::*;

use crate::constants::*;
use crate::jentry::JEntry;
use crate::raw::JsonbItem;
use core::ops::Range;

use crate::error::*;
use crate::RawJsonb;
use crate::ValueType;

use crate::OwnedJsonb;
use byteorder::BigEndian;
use byteorder::WriteBytesExt;

impl RawJsonb<'_> {
    pub fn value_type(&self) -> Result<ValueType> {
        let mut index = 0;
        let (header_type, header_len) = self.read_header(index)?;
        index += 4;
        match header_type {
            SCALAR_CONTAINER_TAG => {
                let jentry = self.read_jentry(index)?;

                match jentry.type_code {
                    NULL_TAG => Ok(ValueType::Null),
                    TRUE_TAG => Ok(ValueType::Boolean),
                    FALSE_TAG => Ok(ValueType::Boolean),
                    NUMBER_TAG => Ok(ValueType::Number),
                    STRING_TAG => Ok(ValueType::String),
                    _ => Err(Error::InvalidJsonb),
                }
            }
            ARRAY_CONTAINER_TAG => Ok(ValueType::Array(header_len as usize)),
            OBJECT_CONTAINER_TAG => Ok(ValueType::Object(header_len as usize)),
            _ => Err(Error::InvalidJsonb),
        }
    }

    pub(crate) fn read_header(&self, index: usize) -> Result<(u32, u32)> {
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

    pub(crate) fn read_jentry(&self, index: usize) -> Result<JEntry> {
        let jentry_encoded = self.read_u32(index)?;
        let jentry = JEntry::decode_jentry(jentry_encoded);
        Ok(jentry)
    }
}

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
