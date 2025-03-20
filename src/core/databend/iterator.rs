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

use std::collections::VecDeque;
use std::ops::Range;

use super::constants::*;
use super::jentry::JEntry;
use crate::core::JsonbItem;
use crate::error::Result;
use crate::RawJsonb;

pub(crate) struct ArrayIterator<'a> {
    raw_jsonb: RawJsonb<'a>,
    jentry_offset: usize,
    item_offset: usize,
    length: usize,
    index: usize,
}

impl<'a> ArrayIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == ARRAY_CONTAINER_TAG {
            let jentry_offset = 4;
            let item_offset = 4 + 4 * header_len as usize;
            Ok(Some(Self {
                raw_jsonb,
                jentry_offset,
                item_offset,
                length: header_len as usize,
                index: 0,
            }))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }
}

impl<'a> Iterator for ArrayIterator<'a> {
    type Item = Result<JsonbItem<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length {
            return None;
        }
        let jentry = match self.raw_jsonb.read_jentry(self.jentry_offset) {
            Ok(jentry) => jentry,
            Err(err) => return Some(Err(err)),
        };

        let item_length = jentry.length as usize;
        let item_range = Range {
            start: self.item_offset,
            end: self.item_offset + item_length,
        };
        let data = match self.raw_jsonb.slice(item_range) {
            Ok(data) => data,
            Err(err) => return Some(Err(err)),
        };
        let item = jentry_to_jsonb_item(jentry, data);

        self.index += 1;
        self.jentry_offset += 4;
        self.item_offset += item_length;

        Some(Ok(item))
    }
}

pub(crate) struct ObjectKeyIterator<'a> {
    raw_jsonb: RawJsonb<'a>,
    jentry_offset: usize,
    key_offset: usize,
    length: usize,
    index: usize,
}

impl<'a> ObjectKeyIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == OBJECT_CONTAINER_TAG {
            let jentry_offset = 4;
            let key_offset = 4 + 8 * header_len as usize;
            Ok(Some(Self {
                raw_jsonb,
                jentry_offset,
                key_offset,
                length: header_len as usize,
                index: 0,
            }))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }
}

impl<'a> Iterator for ObjectKeyIterator<'a> {
    type Item = Result<JsonbItem<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.length {
            return None;
        }
        let jentry = match self.raw_jsonb.read_jentry(self.jentry_offset) {
            Ok(jentry) => jentry,
            Err(err) => return Some(Err(err)),
        };

        let key_length = jentry.length as usize;
        let key_range = Range {
            start: self.key_offset,
            end: self.key_offset + key_length,
        };
        let data = match self.raw_jsonb.slice(key_range) {
            Ok(data) => data,
            Err(err) => return Some(Err(err)),
        };
        let key_item = jentry_to_jsonb_item(jentry, data);

        self.index += 1;
        self.jentry_offset += 4;
        self.key_offset += key_length;

        Some(Ok(key_item))
    }
}

pub(crate) struct ObjectIterator<'a> {
    raw_jsonb: RawJsonb<'a>,
    key_jentries: VecDeque<JEntry>,
    jentry_offset: usize,
    key_offset: usize,
    val_offset: usize,
    length: usize,
}

impl<'a> ObjectIterator<'a> {
    pub(crate) fn new(raw_jsonb: RawJsonb<'a>) -> Result<Option<Self>> {
        let (header_type, header_len) = raw_jsonb.read_header(0)?;
        if header_type == OBJECT_CONTAINER_TAG {
            let mut jentry_offset = 4;
            let mut key_jentries = VecDeque::with_capacity(header_len as usize);
            for _ in 0..header_len {
                let key_jentry = raw_jsonb.read_jentry(jentry_offset)?;
                jentry_offset += 4;
                key_jentries.push_back(key_jentry);
            }
            let key_length: usize = key_jentries.iter().map(|j| j.length as usize).sum();
            let key_offset = 4 + 8 * header_len as usize;
            let val_offset = key_offset + key_length;

            Ok(Some(Self {
                raw_jsonb,
                key_jentries,
                jentry_offset,
                key_offset,
                val_offset,
                length: header_len as usize,
            }))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.length
    }
}

impl<'a> Iterator for ObjectIterator<'a> {
    type Item = Result<(&'a str, JsonbItem<'a>)>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.key_jentries.pop_front() {
            Some(key_jentry) => {
                let val_jentry = match self.raw_jsonb.read_jentry(self.jentry_offset) {
                    Ok(jentry) => jentry,
                    Err(err) => return Some(Err(err)),
                };
                let key_length = key_jentry.length as usize;
                let val_length = val_jentry.length as usize;

                let key_range = Range {
                    start: self.key_offset,
                    end: self.key_offset + key_length,
                };
                let key_data = match self.raw_jsonb.slice(key_range) {
                    Ok(data) => data,
                    Err(err) => return Some(Err(err)),
                };
                let key = unsafe { std::str::from_utf8_unchecked(key_data) };

                let val_range = Range {
                    start: self.val_offset,
                    end: self.val_offset + val_length,
                };
                let val_data = match self.raw_jsonb.slice(val_range) {
                    Ok(data) => data,
                    Err(err) => return Some(Err(err)),
                };
                let val_item = jentry_to_jsonb_item(val_jentry, val_data);

                self.jentry_offset += 4;
                self.key_offset += key_length;
                self.val_offset += val_length;

                Some(Ok((key, val_item)))
            }
            None => None,
        }
    }
}

fn jentry_to_jsonb_item(jentry: JEntry, data: &[u8]) -> JsonbItem<'_> {
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
