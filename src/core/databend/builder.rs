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
use std::collections::BTreeMap;

use byteorder::BigEndian;
use byteorder::WriteBytesExt;

use super::constants::*;
use super::jentry::JEntry;
use crate::core::JsonbItem;
use crate::error::Error;
use crate::error::Result;
use crate::OwnedJsonb;
use crate::RawJsonb;

pub(crate) struct ArrayBuilder<'a> {
    items: Vec<JsonbItem<'a>>,
}

impl<'a> ArrayBuilder<'a> {
    pub(crate) fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, item: JsonbItem<'a>) {
        self.items.push(item);
    }

    pub(crate) fn push_raw_jsonb(&mut self, raw: RawJsonb<'a>) {
        let item = JsonbItem::Raw(raw);
        self.items.push(item);
    }

    pub(crate) fn push_owned_jsonb(&mut self, owned: OwnedJsonb) {
        let item = JsonbItem::Owned(owned);
        self.push_jsonb_item(item)
    }

    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        let mut buf = Vec::new();
        let header = ARRAY_CONTAINER_TAG | self.items.len() as u32;
        buf.write_u32::<BigEndian>(header)?;

        let mut jentry_index = reserve_jentries(&mut buf, self.items.len() * 4);
        for item in self.items.into_iter() {
            append_jsonb_item(&mut buf, &mut jentry_index, item)?;
        }
        Ok(OwnedJsonb::new(buf))
    }
}

pub(crate) struct ArrayDistinctBuilder<'a> {
    items: Vec<JsonbItem<'a>>,
    item_map: BTreeMap<JsonbItem<'a>, usize>,
}

impl<'a> ArrayDistinctBuilder<'a> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            items: Vec::with_capacity(capacity),
            item_map: BTreeMap::new(),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, item: JsonbItem<'a>) {
        if let Some(cnt) = self.item_map.get_mut(&item) {
            *cnt += 1;
        } else {
            self.item_map.insert(item.clone(), 1);
            self.items.push(item);
        }
    }

    pub(crate) fn push_raw_jsonb(&mut self, raw: RawJsonb<'a>) {
        let item = JsonbItem::Raw(raw);
        self.push_jsonb_item(item);
    }

    pub(crate) fn pop_jsonb_item(&mut self, item: JsonbItem<'a>) -> Option<()> {
        if let Some(cnt) = self.item_map.get_mut(&item) {
            if *cnt > 0 {
                *cnt -= 1;
                return Some(());
            }
        }
        None
    }

    pub(crate) fn pop_raw_jsonb(&mut self, raw: RawJsonb<'a>) -> Option<()> {
        let item = JsonbItem::Raw(raw);
        self.pop_jsonb_item(item)
    }

    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        let mut buf = Vec::new();
        let header = ARRAY_CONTAINER_TAG | self.items.len() as u32;
        buf.write_u32::<BigEndian>(header)?;

        let mut jentry_index = reserve_jentries(&mut buf, self.items.len() * 4);
        for item in self.items.into_iter() {
            append_jsonb_item(&mut buf, &mut jentry_index, item)?;
        }
        Ok(OwnedJsonb::new(buf))
    }
}

pub(crate) struct ObjectBuilder<'a> {
    entries: BTreeMap<&'a str, JsonbItem<'a>>,
}

impl<'a> ObjectBuilder<'a> {
    pub(crate) fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    pub(crate) fn push_jsonb_item(&mut self, key: &'a str, val_item: JsonbItem<'a>) -> Result<()> {
        if self.entries.contains_key(key) {
            return Err(Error::ObjectDuplicateKey);
        }
        self.entries.insert(key, val_item);
        Ok(())
    }

    pub(crate) fn push_raw_jsonb(&mut self, key: &'a str, raw: RawJsonb<'a>) -> Result<()> {
        let item = JsonbItem::Raw(raw);
        self.push_jsonb_item(key, item)
    }

    pub(crate) fn push_owned_jsonb(&mut self, key: &'a str, owned: OwnedJsonb) -> Result<()> {
        let item = JsonbItem::Owned(owned);
        self.push_jsonb_item(key, item)
    }

    pub(crate) fn contains_key(&self, key: &'a str) -> bool {
        self.entries.contains_key(key)
    }

    pub(crate) fn build(self) -> Result<OwnedJsonb> {
        let mut buf = Vec::new();
        let header = OBJECT_CONTAINER_TAG | self.entries.len() as u32;
        buf.write_u32::<BigEndian>(header)?;

        let mut jentry_index = reserve_jentries(&mut buf, self.entries.len() * 8);
        for (key, _) in self.entries.iter() {
            let key_len = key.len();
            buf.extend_from_slice(key.as_bytes());
            let jentry = JEntry::make_string_jentry(key_len);
            replace_jentry(&mut buf, jentry, &mut jentry_index)
        }
        for (_, item) in self.entries.into_iter() {
            append_jsonb_item(&mut buf, &mut jentry_index, item)?;
        }
        Ok(OwnedJsonb::new(buf))
    }
}

fn append_jsonb_item(buf: &mut Vec<u8>, jentry_index: &mut usize, item: JsonbItem) -> Result<()> {
    match item {
        JsonbItem::Null => {
            let jentry = JEntry::make_null_jentry();
            replace_jentry(buf, jentry, jentry_index);
        }
        JsonbItem::Boolean(v) => {
            let jentry = if v {
                JEntry::make_true_jentry()
            } else {
                JEntry::make_false_jentry()
            };
            replace_jentry(buf, jentry, jentry_index);
        }
        JsonbItem::Number(data) => {
            let jentry = JEntry::make_number_jentry(data.len());
            replace_jentry(buf, jentry, jentry_index);
            buf.extend_from_slice(data);
        }
        JsonbItem::String(data) => {
            let jentry = JEntry::make_string_jentry(data.len());
            replace_jentry(buf, jentry, jentry_index);
            buf.extend_from_slice(data);
        }
        JsonbItem::Raw(raw_jsonb) => {
            append_raw_jsonb_data(buf, jentry_index, raw_jsonb)?;
        }
        JsonbItem::Owned(owned_jsonb) => {
            let raw_jsonb = owned_jsonb.as_raw();
            append_raw_jsonb_data(buf, jentry_index, raw_jsonb)?;
        }
    }
    Ok(())
}

fn append_raw_jsonb_data(
    buf: &mut Vec<u8>,
    jentry_index: &mut usize,
    raw_jsonb: RawJsonb,
) -> Result<()> {
    let (header_type, _) = raw_jsonb.read_header(0)?;
    if header_type == SCALAR_CONTAINER_TAG {
        let scalar_jentry = raw_jsonb.read_jentry(4)?;
        let range = Range {
            start: 8,
            end: raw_jsonb.len(),
        };
        let data = raw_jsonb.slice(range)?;
        replace_jentry(buf, scalar_jentry, jentry_index);
        buf.extend_from_slice(data);
    } else {
        let jentry = JEntry::make_container_jentry(raw_jsonb.len());
        replace_jentry(buf, jentry, jentry_index);
        buf.extend_from_slice(raw_jsonb.data);
    }
    Ok(())
}

fn reserve_jentries(buf: &mut Vec<u8>, len: usize) -> usize {
    let old_len = buf.len();
    let new_len = old_len + len;
    buf.resize(new_len, 0);
    old_len
}

fn replace_jentry(buf: &mut [u8], jentry: JEntry, jentry_index: &mut usize) {
    let jentry_bytes = jentry.encoded().to_be_bytes();
    for (i, b) in jentry_bytes.iter().enumerate() {
        buf[*jentry_index + i] = *b;
    }
    *jentry_index += 4;
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::ArrayBuilder;
    use super::ObjectBuilder;
    use crate::to_owned_jsonb;
    use crate::Value;

    #[test]
    fn test_build_with_inner_array() {
        let from_builder = {
            let mut builder = ObjectBuilder::new();
            let mut inner_array_builder = ArrayBuilder::with_capacity(1);

            let val = to_owned_jsonb(&false).unwrap();
            inner_array_builder.push_owned_jsonb(val);
            let array = inner_array_builder.build().unwrap();

            builder.push_owned_jsonb("arr", array).unwrap();
            let object = builder.build().unwrap();
            object.to_vec()
        };
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![("arr", Value::Array(vec![Value::Bool(false)]))]);
            value.write_to_vec(&mut from_encoder);
        }
        assert_eq!(from_builder, from_encoder);
    }

    #[test]
    fn test_build_with_inner_object() {
        let from_builder = {
            let mut builder = ObjectBuilder::new();
            let mut inner_obj_builder = ObjectBuilder::new();

            let val = to_owned_jsonb(&true).unwrap();
            inner_obj_builder.push_owned_jsonb("field", val).unwrap();
            let inner_obj = inner_obj_builder.build().unwrap();

            builder.push_owned_jsonb("obj", inner_obj).unwrap();
            let object = builder.build().unwrap();
            object.to_vec()
        };
        let mut from_encoder = Vec::new();
        {
            let value = init_object(vec![(
                "obj",
                init_object(vec![("field", Value::Bool(true))]),
            )]);
            value.write_to_vec(&mut from_encoder);
        }
        assert_eq!(from_builder, from_encoder);
    }

    fn init_object<'a>(entries: Vec<(&str, Value<'a>)>) -> Value<'a> {
        let mut map = BTreeMap::new();
        for (key, val) in entries {
            map.insert(key.to_string(), val);
        }
        Value::Object(map)
    }
}
